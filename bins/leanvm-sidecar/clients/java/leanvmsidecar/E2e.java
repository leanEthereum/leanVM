package leanvmsidecar;

import java.io.ByteArrayOutputStream;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * The run e2e.sh drives: E2e &lt;channel&gt; &lt;signatures-file&gt; &lt;aggregate-rate&gt; &lt;recurse-rate&gt;
 *
 * <p>Sixteen AGGREGATE requests of 1500 signatures each, one after the other, then one RECURSE over the
 * sixteen proofs. The file is records of pubkey | message | signature.
 */
public final class E2e {
    private static final int BATCHES = 16;
    private static final int PER_BATCH = 1500;
    private static final int RESP_CAP = 16 << 20;

    private static long elapsedNanos;

    /** Send one request and wait for its response; the time taken is left in {@link #elapsedNanos}. */
    private static Client.Response call(Client client, int op, int flags, int rate, byte[] payload)
            throws InterruptedException {
        long started = System.nanoTime();
        long id = client.send(op, flags, rate, payload, RESP_CAP);
        if (id == 0) {
            throw new IllegalStateException("no room in the channel");
        }
        Client.Response response;
        while ((response = client.tryRecv()) == null) {
            Thread.sleep(0, 100_000);
        }
        if (response.id() != id) {
            throw new IllegalStateException("response " + response.id() + " to request " + id);
        }
        elapsedNanos = System.nanoTime() - started;
        return response;
    }

    /** The length of the proof, prefix included, at the start of a proof | claims body. */
    private static int proofEnd(Client.Response response) {
        if (response.status() != Client.ST_OK) {
            String text = new String(response.body(), StandardCharsets.UTF_8);
            System.out.printf("  FAILED: status %d detail %d: %s%n", response.status(), response.detail(), text);
            System.exit(1);
        }
        return 8 + (int) le(response.body()).getLong(0);
    }

    private static ByteBuffer le(byte[] bytes) {
        return ByteBuffer.wrap(bytes).order(ByteOrder.LITTLE_ENDIAN);
    }

    private static byte[] u32(int value) {
        return ByteBuffer.allocate(4).order(ByteOrder.LITTLE_ENDIAN).putInt(value).array();
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 4) {
            System.err.println("usage: E2e <channel> <signatures-file> <aggregate-rate> <recurse-rate>");
            System.exit(2);
        }
        int aggregateRate = Integer.parseInt(args[2]);
        int recurseRate = Integer.parseInt(args[3]);
        Client client = Client.open(Path.of(args[0]));
        int record = client.pubKeySize() + client.messageLen() + client.sigSize();
        byte[] signatures = Files.readAllBytes(Path.of(args[1]));
        if (signatures.length < BATCHES * PER_BATCH * record) {
            throw new IllegalArgumentException("signature file too short");
        }

        long total = System.nanoTime();
        ByteArrayOutputStream recurse = new ByteArrayOutputStream();
        recurse.write(u32(BATCHES));
        for (int batch = 0; batch < BATCHES; batch++) {
            ByteArrayOutputStream payload = new ByteArrayOutputStream();
            payload.write(u32(PER_BATCH));
            payload.write(signatures, batch * PER_BATCH * record, PER_BATCH * record);
            Client.Response response = call(client, Client.OP_AGGREGATE, 0, aggregateRate, payload.toByteArray());
            int proofEnd = proofEnd(response);
            byte[] body = response.body();
            System.out.printf(
                    "aggregate %2d/%d: %d signatures, %d bytes, rate %d -> proof %d bytes, %d claims, %.3f s%n",
                    batch + 1, BATCHES, PER_BATCH, payload.size(), aggregateRate, proofEnd - 8,
                    le(body).getInt(proofEnd), elapsedNanos / 1e9);
            recurse.write(body, proofEnd, body.length - proofEnd);
            recurse.write(body, 0, proofEnd);
        }
        Client.Response response =
                call(client, Client.OP_RECURSE, 0, recurseRate, recurse.toByteArray());
        int proofEnd = proofEnd(response);
        System.out.printf(
                "recurse %d -> 1: %d proofs, %d bytes, rate %d -> proof %d bytes, %d claims, %.3f s%n",
                BATCHES, BATCHES, recurse.size(), recurseRate, proofEnd - 8,
                le(response.body()).getInt(proofEnd), elapsedNanos / 1e9);
        System.out.printf("total: %.3f s%n", (System.nanoTime() - total) / 1e9);
    }
}
