package leanvmsidecar;

import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.VarHandle;
import java.nio.ByteOrder;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.ArrayDeque;

/**
 * Client of the leanvm-sidecar service: {@link #send} a request, {@link #tryRecv} its response.
 *
 * <p>Payloads and response bodies are raw bytes in the encodings of PROTOCOL.md. It mirrors the Rust
 * client in crates/leanvm_sidecar_client. Java 17 or later; the channel file must be smaller than 2 GiB.
 *
 * <p>One Client per channel, used from one thread at a time. Open it while no request of an earlier
 * client is outstanding: the server would write that request's response into arena space this client
 * hands out again. The mapping lives until the Client is garbage collected.
 */
public final class Client {
    public static final int OP_AGGREGATE = 1;
    public static final int OP_RECURSE = 2;
    public static final int OP_VERIFY = 3;
    public static final int OP_VERIFY_NARROW = 4;
    public static final int OP_EXTEND = 5;

    /** {@link #OP_RECURSE}, {@link #OP_EXTEND}: verify every child natively before proving. */
    public static final int FLAG_VERIFY_CHILDREN = 1;
    /** A proving op: the server keeps the proof it returns, in place of any it held. */
    public static final int FLAG_KEEP_PROOF = 2;
    /** {@link #OP_RECURSE}, {@link #OP_EXTEND}: the kept proof is one more child, and is no longer kept. */
    public static final int FLAG_USE_KEPT = 4;

    public static final int ST_OK = 0;
    public static final int ST_BAD_REQUEST = 1;
    public static final int ST_RESP_TOO_SMALL = 2;
    public static final int ST_INVALID_PROOF = 3;
    public static final int ST_AGGREGATION_FAILED = 4;

    /**
     * @param id what {@link #send} returned for the request
     * @param respLen the body's length, or under {@link #ST_RESP_TOO_SMALL} the response capacity the request needed
     * @param body the op's response under {@link #ST_OK}, UTF-8 text for a human on a failure, empty under
     *     {@link #ST_RESP_TOO_SMALL}
     */
    public record Response(long id, int status, int detail, long respLen, byte[] body) {}

    private static final long MAGIC = 0x48534d564e41454cL; // "LEANVMSH"
    private static final long VERSION = 1;
    private static final int MSG_SIZE = 64;

    private static final int H_MAGIC = 0;
    private static final int H_VERSION = 8;
    private static final int H_EPOCH = 16;
    private static final int H_RING_CAP = 24;
    private static final int H_TOTAL = 32;
    private static final int H_REQ_RING = 40;
    private static final int H_RESP_RING = 48;
    private static final int H_ARENA_OFF = 56;
    private static final int H_ARENA_LEN = 64;
    private static final int H_PUB_KEY_SIZE = 72;
    private static final int H_MESSAGE_LEN = 80;
    private static final int H_SIG_SIZE = 88;
    private static final int HEADER_SIZE = 96;

    private static final int R_HEAD = 0;
    private static final int R_TAIL = 64;
    private static final int R_SLOTS = 128;

    /** Atomic access to the u64 at an 8-aligned offset; the mapping is page-aligned. */
    private static final VarHandle WORD =
            MethodHandles.byteBufferViewVarHandle(long[].class, ByteOrder.LITTLE_ENDIAN);

    /** A request's arena block: its payload, then its response region. Offsets from the arena's start. */
    private record Block(long id, int off, int payloadLen, int respCap) {
        int end() {
            return off + payloadLen + respCap;
        }
    }

    private final MappedByteBuffer buf;
    private final int ringCap;
    private final int reqRing;
    private final int respRing;
    private final int arenaOff;
    private final int arenaLen;
    private long nextId;
    /**
     * Blocks of requests not yet answered, oldest first. The server answers in order, so the arena is a
     * circular buffer of them: allocated at the back, freed at the front.
     */
    private final ArrayDeque<Block> live = new ArrayDeque<>();

    private Client(MappedByteBuffer buf, int ringCap, int reqRing, int respRing, int arenaOff, int arenaLen) {
        this.buf = buf;
        this.ringCap = ringCap;
        this.reqRing = reqRing;
        this.respRing = respRing;
        this.arenaOff = arenaOff;
        this.arenaLen = arenaLen;
    }

    /** Map the channel the server created at {@code path}. Responses left by an earlier client are discarded. */
    public static Client open(Path path) throws IOException {
        MappedByteBuffer buf;
        long total;
        try (FileChannel file = FileChannel.open(path, StandardOpenOption.READ, StandardOpenOption.WRITE)) {
            total = file.size();
            if (total < HEADER_SIZE || total > Integer.MAX_VALUE) {
                throw new IOException("not a leanvm-sidecar channel, or 2 GiB or larger");
            }
            buf = file.map(FileChannel.MapMode.READ_WRITE, 0, total);
        }
        // Map every page now, so no request takes this process's first-touch faults on the arena.
        buf.load();
        buf.order(ByteOrder.LITTLE_ENDIAN);
        long ringCap = buf.getLong(H_RING_CAP);
        long reqRing = buf.getLong(H_REQ_RING);
        long respRing = buf.getLong(H_RESP_RING);
        long arenaOff = buf.getLong(H_ARENA_OFF);
        long arenaLen = buf.getLong(H_ARENA_LEN);
        // Every later access is in bounds given these: the rings sit below the arena, the arena inside the file.
        boolean ok = buf.getLong(H_MAGIC) == MAGIC
                && buf.getLong(H_VERSION) == VERSION
                && buf.getLong(H_TOTAL) == total
                && ringCap > 0
                && Long.bitCount(ringCap) == 1
                && arenaOff >= 0
                && arenaOff <= total
                && arenaLen == total - arenaOff
                && ringFits(reqRing, ringCap, arenaOff)
                && ringFits(respRing, ringCap, arenaOff);
        if (!ok) {
            throw new IOException("not a leanvm-sidecar channel of this version");
        }
        Client client = new Client(buf, (int) ringCap, (int) reqRing, (int) respRing, (int) arenaOff, (int) arenaLen);
        WORD.setVolatile(buf, client.respRing + R_HEAD, (long) WORD.getVolatile(buf, client.respRing + R_TAIL));
        return client;
    }

    private static boolean ringFits(long ring, long ringCap, long arenaOff) {
        return ring >= 0 && ring % 8 == 0 && ring + R_SLOTS <= arenaOff && ringCap <= (arenaOff - ring - R_SLOTS) / MSG_SIZE;
    }

    private int slot(int ring, long index) {
        return ring + R_SLOTS + (int) (index & (ringCap - 1)) * MSG_SIZE;
    }

    /** Incremented each time the server starts. A request in flight across a restart gets no response. */
    public long epoch() {
        return (long) WORD.getVolatile(buf, H_EPOCH);
    }

    public int pubKeySize() {
        return (int) buf.getLong(H_PUB_KEY_SIZE);
    }

    public int messageLen() {
        return (int) buf.getLong(H_MESSAGE_LEN);
    }

    public int sigSize() {
        return (int) buf.getLong(H_SIG_SIZE);
    }

    /** Where a block of {@code len} bytes goes, from the arena's start, given the blocks still held; -1 if nowhere. */
    static int place(ArrayDeque<Block> live, int arenaLen, long len) {
        if (live.isEmpty()) {
            return len <= arenaLen ? 0 : -1;
        }
        Block first = live.peekFirst();
        Block last = live.peekLast();
        int end = last.end();
        if (last.off() < first.off()) {
            // Wrapped: the gap up to the oldest block.
            return len <= first.off() - end ? end : -1;
        }
        if (len <= arenaLen - end) {
            return end;
        }
        // Wrap into the space before the oldest block. first.off > 0 keeps last.off < first.off meaning wrapped.
        return first.off() > 0 && len <= first.off() ? 0 : -1;
    }

    /**
     * Queue a request. {@code respCap} bytes of arena are reserved for the response: a proof that does not
     * fit is discarded by the server ({@link #ST_RESP_TOO_SMALL}).
     *
     * @return the request's id, at least 1, or 0 if the request ring or the arena has no room: receive a
     *     response and retry
     */
    public long send(int op, int flags, int logInvRate, byte[] payload, int respCap) {
        long tail = (long) WORD.getVolatile(buf, reqRing + R_TAIL);
        if (tail - (long) WORD.getVolatile(buf, reqRing + R_HEAD) >= ringCap || respCap < 0) {
            return 0;
        }
        int off = place(live, arenaLen, (long) payload.length + respCap);
        if (off < 0) {
            return 0;
        }
        long id = ++nextId;
        int reqOff = arenaOff + off;
        buf.put(reqOff, payload, 0, payload.length);

        int msg = slot(reqRing, tail);
        buf.putLong(msg, id);
        buf.putInt(msg + 8, op);
        buf.putInt(msg + 12, flags);
        buf.putLong(msg + 16, reqOff);
        buf.putLong(msg + 24, payload.length);
        buf.putLong(msg + 32, reqOff + payload.length);
        buf.putLong(msg + 40, respCap);
        buf.putInt(msg + 48, logInvRate);
        buf.putInt(msg + 52, 0);
        buf.putLong(msg + 56, 0);
        WORD.setVolatile(buf, reqRing + R_TAIL, tail + 1);
        live.addLast(new Block(id, off, payload.length, respCap));
        return id;
    }

    /**
     * The next response, or null if the server has produced none. Frees the request's arena block, and
     * those of earlier requests that a server restart left unanswered.
     */
    public Response tryRecv() {
        long head = (long) WORD.getVolatile(buf, respRing + R_HEAD);
        if ((long) WORD.getVolatile(buf, respRing + R_TAIL) == head) {
            return null;
        }
        int msg = slot(respRing, head);
        long id = buf.getLong(msg);
        int status = buf.getInt(msg + 8);
        int detail = buf.getInt(msg + 12);
        long respLen = buf.getLong(msg + 16);
        WORD.setVolatile(buf, respRing + R_HEAD, head + 1);

        byte[] body = new byte[0];
        while (!live.isEmpty() && live.peekFirst().id() < id) {
            live.removeFirst();
        }
        if (!live.isEmpty() && live.peekFirst().id() == id) {
            Block block = live.removeFirst();
            if (status != ST_RESP_TOO_SMALL && respLen >= 0 && respLen <= block.respCap()) {
                body = new byte[(int) respLen];
                buf.get(arenaOff + block.off() + block.payloadLen(), body, 0, body.length);
            }
        }
        return new Response(id, status, detail, respLen, body);
    }
}
