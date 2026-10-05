package com.example.myapp

import android.app.Activity
import android.app.AlertDialog
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.ContentResolver
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.content.pm.ServiceInfo
import android.graphics.Color
import android.graphics.Typeface
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.IBinder
import android.os.Looper
import android.os.PowerManager
import android.provider.DocumentsContract
import android.view.KeyEvent
import android.view.ViewGroup
import android.widget.Button
import android.widget.LinearLayout
import android.widget.ProgressBar
import android.widget.ScrollView
import android.widget.TextView
import java.io.IOException
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CountDownLatch
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.RejectedExecutionException
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicIntegerArray
import java.util.concurrent.atomic.AtomicLong

private const val REQ_SRC = 1001
private const val REQ_DST = 1002
private const val REQ_NOTIF = 1003
private const val ACTION_STOP = "com.example.myapp.STOP"
private const val CHANNEL_ID = "transfer"
private const val NOTIF_ID = 1
private const val NOTIF_DONE_ID = 2
private const val SCAN_THREADS = 8
private const val COPY_THREADS = 4
private const val INF: Long = Long.MAX_VALUE

// ======================= shared state (service <-> UI) =======================
object TS {
    @Volatile
    var running: Boolean = false
    val jobActive: AtomicBoolean = AtomicBoolean(false)

    @Volatile
    var stop: Boolean = false

    @Volatile
    var phase: Int = 0 // 1 scan, 2 sort, 3 copy, 4 finished

    @Volatile
    var message: String = ""

    @Volatile
    var total: Int = 0

    @Volatile
    var startIndex: Int = 0

    @Volatile
    var copyStartMs: Long = 0L

    @Volatile
    var logVersion: Int = 0

    val scannedDirs: AtomicLong = AtomicLong(0L)
    val foundImages: AtomicLong = AtomicLong(0L)
    val copied: AtomicInteger = AtomicInteger(0)
    val failed: AtomicInteger = AtomicInteger(0)

    private val lines: java.util.ArrayDeque<String> = java.util.ArrayDeque<String>()

    fun reset() {
        phase = 1
        message = ""
        total = 0
        startIndex = 0
        copyStartMs = 0L
        stop = false
        scannedDirs.set(0L)
        foundImages.set(0L)
        copied.set(0)
        failed.set(0)
        synchronized(lines) {
            lines.clear()
            logVersion = logVersion + 1
        }
    }

    fun log(s: String) {
        synchronized(lines) {
            lines.addLast(s)
            while (lines.size > 200) {
                lines.removeFirst()
            }
            logVersion = logVersion + 1
        }
    }

    fun logText(): String {
        return synchronized(lines) { lines.joinToString("\n") }
    }
}

// ======================= data classes =======================
class DirInfo(val docId: String, val folderNum: Long, val path: IntArray)

class ImgItem(
    val dir: DirInfo,
    val name: String,
    val prefix: Long,
    val slice: Long,
    val ownDocId: String?
) {
    fun docId(): String {
        return ownDocId ?: (dir.docId + "/" + name)
    }
}

class SubDir(val docId: String, val name: String, val num: Long)

class ScanCtx(
    val pool: ExecutorService,
    val pending: AtomicInteger,
    val latch: CountDownLatch,
    val all: ArrayList<ImgItem>
)

private fun cmpLong(a: Long, b: Long): Int {
    return if (a < b) -1 else if (a > b) 1 else 0
}

private fun comparePath(a: IntArray, b: IntArray): Int {
    val n = if (a.size < b.size) a.size else b.size
    for (i in 0 until n) {
        val c = cmpLong(a[i].toLong(), b[i].toLong())
        if (c != 0) return c
    }
    return cmpLong(a.size.toLong(), b.size.toLong())
}

private fun fmtNum(v: Long): String {
    return if (v == INF) "inf" else v.toString()
}

// ======================= the transfer engine =======================
class TransferJob(
    private val ctx: Context,
    private val src: Uri,
    private val dst: Uri,
    private val resume: Boolean,
    private val progress: (String, Int, Int) -> Unit
) {
    private val resolver: ContentResolver = ctx.contentResolver
    private val prefs: SharedPreferences =
        ctx.getSharedPreferences("image_transfer", Context.MODE_PRIVATE)
    private val imageExts: Set<String> =
        setOf(".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tiff", ".webp")
    private var lastNotify: Long = 0L

    fun run(): String {
        TS.phase = 1
        val items: ArrayList<ImgItem> = scan()
        if (TS.stop) return "Stopped."
        val total = items.size
        if (total == 0) {
            prefs.edit().putBoolean("r_active", false).apply()
            TS.log("No images found in the source folder.")
            return "No images found in the source folder."
        }
        TS.total = total
        TS.phase = 2
        TS.log("Found $total images. Sorting...")
        progress("Sorting $total images...", 0, 0)

        // folder number, prefix number, slice number, filename (then walk order for exact ties)
        items.sortWith(Comparator<ImgItem> { a, b -> compareItems(a, b) })
        if (TS.stop) return "Stopped."

        var startIdx = 0
        if (resume) {
            val savedTotal = prefs.getInt("r_total", -1)
            val savedDone = prefs.getInt("r_done", 0)
            if (savedTotal == total && savedDone >= 0 && savedDone <= total) {
                startIdx = savedDone
            } else {
                TS.log("Source changed since the interrupted run - starting over from 1.")
            }
        }
        TS.startIndex = startIdx

        val dstId: String = DocumentsContract.getTreeDocumentId(dst)
        val dstParent: Uri = DocumentsContract.buildDocumentUriUsingTree(dst, dstId)
        val existing = ConcurrentHashMap<String, String>()
        loadExisting(dstId, (startIdx + 1).toLong(), total.toLong(), existing)

        prefs.edit()
            .putString("r_src", src.toString())
            .putString("r_dst", dst.toString())
            .putInt("r_total", total)
            .putInt("r_done", startIdx)
            .putBoolean("r_active", true)
            .apply()

        TS.log("Copying from #${startIdx + 1} to #$total ...")
        TS.phase = 3
        TS.copyStartMs = System.currentTimeMillis()

        val flags = AtomicIntegerArray(total)
        val next = AtomicInteger(startIdx)
        val latch = CountDownLatch(COPY_THREADS)
        for (w in 0 until COPY_THREADS) {
            Thread {
                try {
                    worker(items, dstId, dstParent, existing, flags, next, total)
                } catch (t: Throwable) {
                    TS.log("Worker error: " + (t.message ?: t.toString()))
                } finally {
                    latch.countDown()
                }
            }.start()
        }

        var wm = startIdx
        var lastSave = 0L
        while (!latch.await(500L, TimeUnit.MILLISECONDS)) {
            wm = advance(flags, wm, total)
            val done = TS.startIndex + TS.copied.get() + TS.failed.get()
            tick("Copied $done of $total", done, total)
            val now = System.currentTimeMillis()
            if (now - lastSave > 2000L) {
                lastSave = now
                prefs.edit().putInt("r_done", wm).apply()
            }
        }
        wm = advance(flags, wm, total)
        val failed = TS.failed.get()

        if (TS.stop && wm < total) {
            prefs.edit().putInt("r_done", wm).putBoolean("r_active", true).apply()
            TS.log("Stopped by user.")
            return "Stopped. $wm of $total done. Press Start to resume."
        }

        prefs.edit().putBoolean("r_active", false).putInt("r_done", total).apply()
        val ok = total - failed
        TS.log("\nDone. Total images copied: $ok")
        return if (failed > 0) {
            "Done. Total images copied: $ok ($failed failed)"
        } else {
            "Done. Total images copied: $ok"
        }
    }

    private fun tick(text: String, cur: Int, max: Int) {
        val now = System.currentTimeMillis()
        if (now - lastNotify >= 1000L) {
            lastNotify = now
            progress(text, cur, max)
        }
    }

    private fun advance(flags: AtomicIntegerArray, from: Int, total: Int): Int {
        var w = from
        while (w < total && flags.get(w) != 0) {
            w++
        }
        return w
    }

    // ---------- copy workers ----------
    private fun worker(
        items: ArrayList<ImgItem>,
        dstId: String,
        dstParent: Uri,
        existing: ConcurrentHashMap<String, String>,
        flags: AtomicIntegerArray,
        next: AtomicInteger,
        total: Int
    ) {
        val buf = ByteArray(256 * 1024)
        while (!TS.stop) {
            val i = next.getAndIncrement()
            if (i >= total) break
            val item: ImgItem = items[i]
            val ext: String = splitExt(item.name).lowercase()
            val newName: String = (i + 1).toString() + ext

            // shutil.copy2 overwrites an existing file with the same name
            val old: String? = existing.remove(newName)
            if (old != null) {
                val oldId: String = if (old.isEmpty()) dstId + "/" + newName else old
                try {
                    DocumentsContract.deleteDocument(
                        resolver,
                        DocumentsContract.buildDocumentUriUsingTree(dst, oldId)
                    )
                } catch (e: Exception) {
                    // ignore
                }
            }

            var err: String? = copyOne(item, newName, ext, dstParent, buf)
            if (err != null && !TS.stop) {
                err = copyOne(item, newName, ext, dstParent, buf) // one retry
            }
            if (err != null) {
                TS.failed.incrementAndGet()
                flags.set(i, 2)
                TS.log("ERROR: ${item.name} -> $newName : $err")
            } else {
                TS.copied.incrementAndGet()
                flags.set(i, 1)
                TS.log(
                    "Copied: ${item.name} " +
                            "(folder:${fmtNum(item.dir.folderNum)}, prefix:${fmtNum(item.prefix)}, slice:${fmtNum(item.slice)}) " +
                            "\u2192 $newName"
                )
            }
        }
    }

    // Returns null on success, or an error message.
    private fun copyOne(
        item: ImgItem,
        newName: String,
        ext: String,
        dstParent: Uri,
        buf: ByteArray
    ): String? {
        val created: Uri? = try {
            DocumentsContract.createDocument(resolver, dstParent, mimeFor(ext), newName)
        } catch (e: Exception) {
            null
        }
        if (created == null) return "Cannot create $newName"
        try {
            val srcUri: Uri = DocumentsContract.buildDocumentUriUsingTree(src, item.docId())
            val ins = resolver.openInputStream(srcUri)
                ?: throw IOException("Cannot open source file")
            try {
                val outs = resolver.openOutputStream(created, "wt")
                    ?: throw IOException("Cannot open destination file")
                try {
                    while (true) {
                        val n = ins.read(buf)
                        if (n < 0) break
                        outs.write(buf, 0, n)
                    }
                } finally {
                    outs.close()
                }
            } finally {
                ins.close()
            }
        } catch (e: Exception) {
            try {
                DocumentsContract.deleteDocument(resolver, created)
            } catch (e2: Exception) {
                // ignore
            }
            return e.message ?: e.toString()
        }
        return null
    }

    private fun loadExisting(
        dstId: String,
        lo: Long,
        hi: Long,
        out: ConcurrentHashMap<String, String>
    ) {
        forEachChild(dst, dstId) { id, name, isDir ->
            if (!isDir) {
                val e = digitEnd(name, 0)
                if (e > 0 && e < name.length && name[e] == '.') {
                    val n = parseDigits(name, 0, e)
                    if (n >= lo && n <= hi) {
                        out.put(name, if (id == dstId + "/" + name) "" else id)
                    }
                }
            }
        }
    }

    // ---------- parallel scan ----------
    private fun scan(): ArrayList<ImgItem> {
        val all = ArrayList<ImgItem>()
        val rootId: String = DocumentsContract.getTreeDocumentId(src)
        val rootDir = DirInfo(rootId, leadingNum(rootName()), IntArray(0))
        val pool: ExecutorService = Executors.newFixedThreadPool(SCAN_THREADS)
        val c = ScanCtx(pool, AtomicInteger(0), CountDownLatch(1), all)
        submitDir(c, rootDir)
        while (!c.latch.await(300L, TimeUnit.MILLISECONDS)) {
            if (TS.stop) break
            tick(
                "Scanning: ${TS.scannedDirs.get()} folders, ${TS.foundImages.get()} images",
                0,
                0
            )
        }
        pool.shutdownNow()
        try {
            pool.awaitTermination(3L, TimeUnit.SECONDS)
        } catch (e: InterruptedException) {
            // ignore
        }
        return all
    }

    private fun submitDir(c: ScanCtx, d: DirInfo) {
        c.pending.incrementAndGet()
        try {
            c.pool.execute {
                try {
                    if (!TS.stop) scanOne(c, d)
                } catch (t: Throwable) {
                    TS.log("Skipped a folder: " + (t.message ?: t.toString()))
                } finally {
                    if (c.pending.decrementAndGet() == 0) c.latch.countDown()
                }
            }
        } catch (e: RejectedExecutionException) {
            if (c.pending.decrementAndGet() == 0) c.latch.countDown()
        }
    }

    private fun scanOne(c: ScanCtx, d: DirInfo) {
        val local = ArrayList<ImgItem>()
        val subdirs = ArrayList<SubDir>()
        forEachChild(src, d.docId) { id, name, isDir ->
            if (isDir) {
                subdirs.add(SubDir(id, name, leadingNum(name)))
            } else {
                val ext: String = splitExt(name).lowercase()
                if (imageExts.contains(ext)) {
                    local.add(makeItem(d, id, name))
                }
            }
        }
        TS.scannedDirs.incrementAndGet()
        if (local.isNotEmpty()) {
            TS.foundImages.addAndGet(local.size.toLong())
            synchronized(c.all) {
                c.all.addAll(local)
            }
        }
        subdirs.sortWith(Comparator<SubDir> { a, b -> compareSubDirs(a, b) })
        for (k in 0 until subdirs.size) {
            val sd: SubDir = subdirs[k]
            val p = IntArray(d.path.size + 1)
            System.arraycopy(d.path, 0, p, 0, d.path.size)
            p[d.path.size] = k
            submitDir(c, DirInfo(sd.docId, sd.num, p))
        }
    }

    private fun makeItem(d: DirInfo, id: String, name: String): ImgItem {
        val n1 = digitEnd(name, 0)
        val prefix: Long
        val slice: Long
        if (n1 == 0) {
            // Pattern 3: no leading number -> end of its folder group
            prefix = INF
            slice = 0L
        } else {
            prefix = parseDigits(name, 0, n1)
            var s = 0L
            if (name.startsWith("_slice_", n1)) {
                // Pattern 1: 0042_slice_007.jpg
                val a = n1 + 7
                val n2 = digitEnd(name, a)
                if (n2 > a) {
                    s = parseDigits(name, a, n2)
                }
            }
            // Pattern 2 (0042_something.jpg) keeps slice = 0
            slice = s
        }
        val own: String? = if (id == d.docId + "/" + name) null else id
        return ImgItem(d, name, prefix, slice, own)
    }

    private fun compareItems(a: ImgItem, b: ImgItem): Int {
        var c = cmpLong(a.dir.folderNum, b.dir.folderNum)
        if (c != 0) return c
        c = cmpLong(a.prefix, b.prefix)
        if (c != 0) return c
        c = cmpLong(a.slice, b.slice)
        if (c != 0) return c
        c = a.name.compareTo(b.name)
        if (c != 0) return c
        return comparePath(a.dir.path, b.dir.path)
    }

    private fun compareSubDirs(a: SubDir, b: SubDir): Int {
        val c = cmpLong(a.num, b.num)
        if (c != 0) return c
        return a.name.compareTo(b.name)
    }

    private fun digitEnd(s: String, from: Int): Int {
        var i = from
        while (i < s.length && Character.isDigit(s[i])) {
            i++
        }
        return i
    }

    private fun parseDigits(s: String, a0: Int, b: Int): Long {
        var a = a0
        while (a < b - 1 && Character.digit(s[a], 10) == 0) {
            a++
        }
        if (b - a > 18) return Long.MAX_VALUE - 1L
        var v = 0L
        for (i in a until b) {
            v = v * 10L + Character.digit(s[i], 10).toLong()
        }
        return v
    }

    private fun leadingNum(s: String): Long {
        val e = digitEnd(s, 0)
        if (e == 0) return INF
        return parseDigits(s, 0, e)
    }

    // Same as Python os.path.splitext(name)[1]
    private fun splitExt(name: String): String {
        var lead = 0
        while (lead < name.length && name[lead] == '.') {
            lead++
        }
        val dot = name.lastIndexOf('.')
        return if (dot >= lead && dot >= 0) name.substring(dot) else ""
    }

    private fun mimeFor(ext: String): String {
        return when (ext) {
            ".jpg", ".jpeg" -> "image/jpeg"
            ".png" -> "image/png"
            ".gif" -> "image/gif"
            ".bmp" -> "image/bmp"
            ".tiff" -> "image/tiff"
            ".webp" -> "image/webp"
            else -> "application/octet-stream"
        }
    }

    private fun forEachChild(tree: Uri, parentId: String, cb: (String, String, Boolean) -> Unit) {
        val childrenUri: Uri = DocumentsContract.buildChildDocumentsUriUsingTree(tree, parentId)
        val cols = arrayOf(
            DocumentsContract.Document.COLUMN_DOCUMENT_ID,
            DocumentsContract.Document.COLUMN_DISPLAY_NAME,
            DocumentsContract.Document.COLUMN_MIME_TYPE
        )
        val cursor = resolver.query(childrenUri, cols, null, null, null) ?: return
        try {
            while (cursor.moveToNext()) {
                val id: String = cursor.getString(0) ?: continue
                val nm: String = cursor.getString(1) ?: ""
                val mime: String = cursor.getString(2) ?: ""
                cb(id, nm, mime == DocumentsContract.Document.MIME_TYPE_DIR)
            }
        } finally {
            cursor.close()
        }
    }

    private fun rootName(): String {
        val docId: String = DocumentsContract.getTreeDocumentId(src)
        val docUri: Uri = DocumentsContract.buildDocumentUriUsingTree(src, docId)
        var name: String? = null
        try {
            val cursor = resolver.query(
                docUri,
                arrayOf(DocumentsContract.Document.COLUMN_DISPLAY_NAME),
                null,
                null,
                null
            )
            if (cursor != null) {
                try {
                    if (cursor.moveToFirst()) {
                        name = cursor.getString(0)
                    }
                } finally {
                    cursor.close()
                }
            }
        } catch (e: Exception) {
            name = null
        }
        if (name != null) return name
        val cut = docId.lastIndexOfAny(charArrayOf(':', '/'))
        return if (cut >= 0) docId.substring(cut + 1) else docId
    }
}

// ======================= foreground service =======================
class TransferService : Service() {

    private var wakeLock: PowerManager.WakeLock? = null

    override fun onBind(intent: Intent?): IBinder? {
        return null
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        if (intent != null && intent.action == ACTION_STOP) {
            TS.stop = true
            if (!TS.jobActive.get()) {
                stopSelf()
            }
            return START_NOT_STICKY
        }

        createChannel()
        try {
            val n: Notification = baseBuilder()
                .setContentText("Preparing...")
                .setProgress(0, 0, true)
                .build()
            startForeground(NOTIF_ID, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_DATA_SYNC)
        } catch (e: Exception) {
            TS.message = "Cannot start background service: " + (e.message ?: e.toString())
            TS.running = false
            stopSelf()
            return START_NOT_STICKY
        }

        val srcS: String = intent?.getStringExtra("src") ?: ""
        val dstS: String = intent?.getStringExtra("dst") ?: ""
        val resume: Boolean = intent?.getBooleanExtra("resume", false) ?: false
        if (srcS.isEmpty() || dstS.isEmpty()) {
            TS.running = false
            stopForeground(Service.STOP_FOREGROUND_REMOVE)
            stopSelf()
            return START_NOT_STICKY
        }
        if (!TS.jobActive.compareAndSet(false, true)) {
            return START_NOT_STICKY
        }

        try {
            val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
            val wl = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "myapp:transfer")
            wl.setReferenceCounted(false)
            wl.acquire(24L * 60L * 60L * 1000L)
            wakeLock = wl
        } catch (e: Exception) {
            // continue without wake lock
        }

        val appCtx: Context = applicationContext
        Thread {
            var msg: String
            try {
                val job = TransferJob(appCtx, Uri.parse(srcS), Uri.parse(dstS), resume) { text, cur, max ->
                    updateNotification(text, cur, max)
                }
                msg = job.run()
            } catch (t: Throwable) {
                msg = "Error: " + (t.message ?: t.toString())
                TS.log(msg)
            }
            finishUp(msg)
        }.start()
        return START_NOT_STICKY
    }

    private fun finishUp(msg: String) {
        TS.message = msg
        TS.phase = 4
        TS.running = false
        TS.jobActive.set(false)
        releaseWakeLock()
        try {
            val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            val open = Intent(this, MainActivity::class.java)
            open.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK or Intent.FLAG_ACTIVITY_SINGLE_TOP)
            val openPi = PendingIntent.getActivity(this, 0, open, PendingIntent.FLAG_IMMUTABLE)
            val done: Notification = Notification.Builder(this, CHANNEL_ID)
                .setSmallIcon(android.R.drawable.stat_sys_download_done)
                .setContentTitle("Image Transfer")
                .setContentText(msg)
                .setAutoCancel(true)
                .setContentIntent(openPi)
                .build()
            nm.notify(NOTIF_DONE_ID, done)
        } catch (e: Exception) {
            // ignore
        }
        Handler(Looper.getMainLooper()).post {
            stopForeground(Service.STOP_FOREGROUND_REMOVE)
            stopSelf()
        }
    }

    private fun releaseWakeLock() {
        try {
            val wl = wakeLock
            if (wl != null && wl.isHeld) {
                wl.release()
            }
        } catch (e: Exception) {
            // ignore
        }
        wakeLock = null
    }

    override fun onDestroy() {
        releaseWakeLock()
        super.onDestroy()
    }

    private fun createChannel() {
        val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        val ch = NotificationChannel(CHANNEL_ID, "Image transfer", NotificationManager.IMPORTANCE_LOW)
        nm.createNotificationChannel(ch)
    }

    private fun baseBuilder(): Notification.Builder {
        val open = Intent(this, MainActivity::class.java)
        open.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK or Intent.FLAG_ACTIVITY_SINGLE_TOP)
        val openPi = PendingIntent.getActivity(this, 0, open, PendingIntent.FLAG_IMMUTABLE)
        val stop = Intent(this, TransferService::class.java)
        stop.action = ACTION_STOP
        val stopPi = PendingIntent.getService(this, 1, stop, PendingIntent.FLAG_IMMUTABLE)
        val action: Notification.Action = Notification.Action.Builder(0, "Stop", stopPi).build()
        return Notification.Builder(this, CHANNEL_ID)
            .setSmallIcon(android.R.drawable.stat_sys_download)
            .setContentTitle("Image Transfer")
            .setOngoing(true)
            .setOnlyAlertOnce(true)
            .setContentIntent(openPi)
            .addAction(action)
    }

    private fun updateNotification(text: String, cur: Int, max: Int) {
        try {
            val b: Notification.Builder = baseBuilder().setContentText(text)
            if (max > 0) {
                b.setProgress(max, cur, false)
            } else {
                b.setProgress(0, 0, true)
            }
            val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            nm.notify(NOTIF_ID, b.build())
        } catch (e: Exception) {
            // ignore
        }
    }
}

// ======================= UI =======================
class MainActivity : Activity() {

    private val ui: Handler = Handler(Looper.getMainLooper())

    private lateinit var prefs: SharedPreferences
    private lateinit var srcLabel: TextView
    private lateinit var dstLabel: TextView
    private lateinit var statusView: TextView
    private lateinit var logView: TextView
    private lateinit var scroll: ScrollView
    private lateinit var progressBar: ProgressBar
    private lateinit var btnSrc: Button
    private lateinit var btnDst: Button
    private lateinit var btnStart: Button
    private lateinit var btnStop: Button

    private var srcUri: Uri? = null
    private var dstUri: Uri? = null
    private var lastLogVersion: Int = -1
    private var lastRunning: Boolean = false
    private var lastStatus: String = ""
    private var pbMode: Int = -1

    private val poller: Runnable = object : Runnable {
        override fun run() {
            refreshUi()
            ui.postDelayed(this, 250L)
        }
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        prefs = getSharedPreferences("image_transfer", Context.MODE_PRIVATE)
        val s: String? = prefs.getString("src", null)
        val d: String? = prefs.getString("dst", null)
        if (s != null) srcUri = Uri.parse(s)
        if (d != null) dstUri = Uri.parse(d)
        buildUi()
        updateLabels()
    }

    override fun onResume() {
        super.onResume()
        updateLabels()
        lastRunning = TS.running
        setButtons(!TS.running)
        lastLogVersion = -1
        lastStatus = ""
        pbMode = -1
        ui.post(poller)
    }

    override fun onPause() {
        super.onPause()
        ui.removeCallbacks(poller)
        saveState()
    }

    private fun saveState() {
        prefs.edit()
            .putString("src", srcUri?.toString())
            .putString("dst", dstUri?.toString())
            .apply()
    }

    private fun dp(v: Int): Int {
        return (v * resources.displayMetrics.density).toInt()
    }

    private fun rowParams(): LinearLayout.LayoutParams {
        val p = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        p.setMargins(dp(2), dp(2), dp(2), dp(2))
        return p
    }

    private fun makeButton(text: String, action: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.isAllCaps = false
        b.isFocusable = false
        b.isFocusableInTouchMode = false
        b.setOnClickListener { action() }
        return b
    }

    private fun makeLabel(size: Float): TextView {
        val t = TextView(this)
        t.textSize = size
        t.setTextColor(Color.BLACK)
        t.setPadding(dp(4), dp(2), dp(4), dp(2))
        return t
    }

    private fun buildUi() {
        val root = LinearLayout(this)
        root.orientation = LinearLayout.VERTICAL
        root.setBackgroundColor(Color.WHITE)
        root.setPadding(dp(8), dp(8), dp(8), dp(8))

        val row1 = LinearLayout(this)
        row1.orientation = LinearLayout.HORIZONTAL
        btnSrc = makeButton("Source folder (S)") { pickFolder(REQ_SRC) }
        btnDst = makeButton("Destination folder (D)") { pickFolder(REQ_DST) }
        row1.addView(btnSrc, rowParams())
        row1.addView(btnDst, rowParams())
        root.addView(
            row1,
            LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
            )
        )

        val row2 = LinearLayout(this)
        row2.orientation = LinearLayout.HORIZONTAL
        btnStart = makeButton("Start (Enter)") { startTransfer() }
        btnStop = makeButton("Stop (Esc)") { TS.stop = true }
        btnStop.isEnabled = false
        row2.addView(btnStart, rowParams())
        row2.addView(btnStop, rowParams())
        root.addView(
            row2,
            LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
            )
        )

        srcLabel = makeLabel(13f)
        dstLabel = makeLabel(13f)
        statusView = makeLabel(15f)
        statusView.setTypeface(Typeface.DEFAULT, Typeface.BOLD)
        root.addView(srcLabel)
        root.addView(dstLabel)
        root.addView(statusView)

        progressBar = ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal)
        progressBar.max = 1000
        root.addView(
            progressBar,
            LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
            )
        )

        scroll = ScrollView(this)
        logView = TextView(this)
        logView.textSize = 11f
        logView.typeface = Typeface.MONOSPACE
        logView.setTextColor(Color.BLACK)
        logView.setPadding(dp(4), dp(4), dp(4), dp(4))
        scroll.addView(
            logView,
            ViewGroup.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
            )
        )
        scroll.setBackgroundColor(Color.rgb(240, 240, 240))
        root.addView(
            scroll,
            LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f)
        )

        setContentView(root)
    }

    private fun updateLabels() {
        srcLabel.text = "Source: " + (srcUri?.lastPathSegment ?: "(not selected)")
        dstLabel.text = "Destination: " + (dstUri?.lastPathSegment ?: "(not selected)")
    }

    private fun setButtons(enabled: Boolean) {
        btnSrc.isEnabled = enabled
        btnDst.isEnabled = enabled
        btnStart.isEnabled = enabled
        btnStop.isEnabled = !enabled
    }

    // ---------- periodic UI refresh (cheap, throttled) ----------
    private fun refreshUi() {
        val r: Boolean = TS.running
        if (r != lastRunning) {
            lastRunning = r
            setButtons(!r)
        }
        val st: String = statusLine()
        if (st != lastStatus) {
            lastStatus = st
            statusView.text = st
        }
        val v: Int = TS.logVersion
        if (v != lastLogVersion) {
            lastLogVersion = v
            logView.text = TS.logText()
            scroll.post { scroll.scrollTo(0, logView.height) }
        }
        val mode: Int = if (!r) 0 else if (TS.phase == 3 && TS.total > 0) 2 else 1
        if (mode != pbMode) {
            pbMode = mode
            progressBar.isIndeterminate = (mode == 1)
            if (mode != 2) {
                progressBar.progress = 0
            }
        }
        if (mode == 2) {
            val done: Long = TS.startIndex.toLong() + TS.copied.get() + TS.failed.get()
            progressBar.progress = ((done * 1000L) / TS.total.toLong()).toInt()
        }
    }

    private fun statusLine(): String {
        if (!TS.running) {
            return if (TS.message.isEmpty()) "Ready." else TS.message
        }
        return when (TS.phase) {
            1 -> "Scanning... ${TS.scannedDirs.get()} folders, ${TS.foundImages.get()} images found"
            2 -> "Sorting ${TS.total} images..."
            3 -> copyLine()
            else -> "Working..."
        }
    }

    private fun copyLine(): String {
        val c: Int = TS.copied.get() + TS.failed.get()
        val done: Int = TS.startIndex + c
        var s = "Copying $done / ${TS.total}"
        val el: Double = (System.currentTimeMillis() - TS.copyStartMs) / 1000.0
        if (el > 2.0 && c > 0) {
            val rate: Double = c / el
            val rem: Int = TS.total - done
            val eta: Long = (rem / rate).toLong()
            s += "   " + String.format("%.1f", rate) + "/s   ETA " + fmtTime(eta)
        }
        return s
    }

    private fun fmtTime(sec: Long): String {
        val h = sec / 3600L
        val m = (sec % 3600L) / 60L
        val s = sec % 60L
        return if (h > 0L) String.format("%d:%02d:%02d", h, m, s) else String.format("%d:%02d", m, s)
    }

    // ---------- keyboard shortcuts ----------
    override fun dispatchKeyEvent(event: KeyEvent): Boolean {
        if (event.action == KeyEvent.ACTION_DOWN && event.repeatCount == 0) {
            if (!TS.running) {
                when (event.keyCode) {
                    KeyEvent.KEYCODE_S -> {
                        pickFolder(REQ_SRC)
                        return true
                    }
                    KeyEvent.KEYCODE_D -> {
                        pickFolder(REQ_DST)
                        return true
                    }
                    KeyEvent.KEYCODE_ENTER -> {
                        startTransfer()
                        return true
                    }
                }
            } else if (event.keyCode == KeyEvent.KEYCODE_ESCAPE) {
                TS.stop = true
                return true
            }
        }
        return super.dispatchKeyEvent(event)
    }

    // ---------- folder selection ----------
    private fun pickFolder(req: Int) {
        if (TS.running) return
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        var flags = Intent.FLAG_GRANT_READ_URI_PERMISSION or
                Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION
        if (req == REQ_DST) {
            flags = flags or Intent.FLAG_GRANT_WRITE_URI_PERMISSION
        }
        i.addFlags(flags)
        startActivityForResult(i, req)
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (requestCode != REQ_SRC && requestCode != REQ_DST) return
        if (resultCode != Activity.RESULT_OK || data == null) return
        val uri: Uri = data.data ?: return
        try {
            var f = Intent.FLAG_GRANT_READ_URI_PERMISSION
            if (requestCode == REQ_DST) {
                f = f or Intent.FLAG_GRANT_WRITE_URI_PERMISSION
            }
            contentResolver.takePersistableUriPermission(uri, f)
        } catch (e: Exception) {
            // ignore; permission may still be valid for this session
        }
        if (requestCode == REQ_SRC) {
            srcUri = uri
        } else {
            dstUri = uri
        }
        saveState()
        updateLabels()
    }

    // ---------- start / resume ----------
    private fun startTransfer() {
        if (TS.running) return
        val src: Uri? = srcUri
        val dst: Uri? = dstUri
        if (src == null || dst == null) {
            statusView.text = "Folder selection cancelled. Select both folders first."
            return
        }
        val active: Boolean = prefs.getBoolean("r_active", false)
        val done: Int = prefs.getInt("r_done", 0)
        val sameJob: Boolean = active && done > 0 &&
                prefs.getString("r_src", "") == src.toString() &&
                prefs.getString("r_dst", "") == dst.toString()
        if (sameJob) {
            AlertDialog.Builder(this)
                .setTitle("Unfinished transfer")
                .setMessage("$done files were already copied. Resume from file #${done + 1}, or start over from 1?")
                .setPositiveButton("Resume") { _, _ -> launchJob(src, dst, true) }
                .setNegativeButton("Start over") { _, _ -> launchJob(src, dst, false) }
                .setNeutralButton("Cancel", null)
                .show()
        } else {
            launchJob(src, dst, false)
        }
    }

    private fun launchJob(src: Uri, dst: Uri, resume: Boolean) {
        if (TS.running) return
        TS.reset()
        TS.running = true
        setButtons(false)
        lastRunning = true
        if (Build.VERSION.SDK_INT >= 33 &&
            checkSelfPermission("android.permission.POST_NOTIFICATIONS") != PackageManager.PERMISSION_GRANTED
        ) {
            requestPermissions(arrayOf("android.permission.POST_NOTIFICATIONS"), REQ_NOTIF)
        }
        val i = Intent(this, TransferService::class.java)
        i.putExtra("src", src.toString())
        i.putExtra("dst", dst.toString())
        i.putExtra("resume", resume)
        try {
            startForegroundService(i)
        } catch (e: Exception) {
            TS.running = false
            TS.message = "Cannot start service: " + (e.message ?: e.toString())
            setButtons(true)
            lastRunning = false
        }
    }
}
