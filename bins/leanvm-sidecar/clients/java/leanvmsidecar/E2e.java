package leanvmsidecar;

import java.io.ByteArrayOutputStream;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * The run e2e.sh drives: E2e &lt;channel&gt; &lt;signatures-file&gt; &lt;aggregate-rate&gt; &lt;recurse-rate&gt;
 * &lt;signatures-per-batch&gt; &lt;sub-batch&gt;
 *
 * <p>Sixteen AGGREGATE requests of signatures-per-batch signatures each, one after the other, then one RECURSE over the
 * sixteen proofs and one VERIFY of the result. With sub-batch below signatures-per-batch, each batch is
 * instead built up in parts of sub-batch signatures: an AGGREGATE, then one EXTEND per part of the proof so
 * far, which the server keeps. Parts run at rate 1, except the last at aggregate-rate. The file is records of pubkey | message | signature.
 */
public final class E2e {
    private static final int BATCHES = 16;
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

    private static void check(Client.Response response) {
        if (response.status() != Client.ST_OK) {
            String text = new String(response.body(), StandardCharsets.UTF_8);
            System.out.printf("  FAILED: status %d detail %d: %s%n", response.status(), response.detail(), text);
            System.exit(1);
        }
    }

    /** The length of the proof, prefix included, at the start of a proof | claims body. */
    private static int proofEnd(Client.Response response) {
        check(response);
        return 8 + (int) le(response.body()).getLong(0);
    }

    private static ByteBuffer le(byte[] bytes) {
        return ByteBuffer.wrap(bytes).order(ByteOrder.LITTLE_ENDIAN);
    }

    private static byte[] u32(int value) {
        return ByteBuffer.allocate(4).order(ByteOrder.LITTLE_ENDIAN).putInt(value).array();
    }

    /**
     * One proving request: prints the step, with the time since the nanoTime since if not null, and returns the
     * response's proof | claims body.
     */
    private static byte[] step(
            Client client, int op, int flags, int rate, byte[] payload, String label, String what, Long since)
            throws InterruptedException {
        Client.Response response = call(client, op, flags, rate, payload);
        String batch = since == null ? "" : String.format(", batch total %.3f s", (System.nanoTime() - since) / 1e9);
        int proofEnd = proofEnd(response);
        System.out.printf(
                "%s: %s, %d bytes, rate %d -> proof %d bytes, %d claims, %.3f s%s%n",
                label, what, payload.length, rate, proofEnd - 8, le(response.body()).getInt(proofEnd),
                elapsedNanos / 1e9, batch);
        return response.body();
    }

    /**
     * AGGREGATE over count records of record bytes each, starting at record from; under FLAG_USE_KEPT, EXTEND
     * of the proof the server kept with them.
     */
    private static byte[] aggregate(
            Client client, int flags, byte[] signatures, int from, int count, int record, int rate, String label,
            Long since)
            throws InterruptedException {
        boolean extend = (flags & Client.FLAG_USE_KEPT) != 0;
        ByteArrayOutputStream payload = new ByteArrayOutputStream();
        if (extend) {
            // No child in the payload.
            payload.writeBytes(u32(0));
        }
        payload.writeBytes(u32(count));
        payload.write(signatures, from * record, count * record);
        int op = extend ? Client.OP_EXTEND : Client.OP_AGGREGATE;
        String what = (extend ? "kept proof + " : "") + count + " signatures";
        return step(client, op, flags, rate, payload.toByteArray(), label, what, since);
    }

    /** Append a proof | claims body as claims | proof. */
    private static void child(ByteArrayOutputStream out, byte[] body) {
        int proofEnd = 8 + (int) le(body).getLong(0);
        out.write(body, proofEnd, body.length - proofEnd);
        out.write(body, 0, proofEnd);
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 6) {
            System.err.println("usage: E2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>");
            System.exit(2);
        }
        int aggregateRate = Integer.parseInt(args[2]);
        int recurseRate = Integer.parseInt(args[3]);
        int perBatch = Integer.parseInt(args[4]);
        int subBatch = Integer.parseInt(args[5]);
        Client client = Client.open(Path.of(args[0]));
        int record = client.pubKeySize() + client.messageLen() + client.sigSize();
        byte[] signatures = Files.readAllBytes(Path.of(args[1]));
        if (signatures.length < BATCHES * perBatch * record) {
            throw new IllegalArgumentException("signature file too short");
        }

        long total = System.nanoTime();
        int parts = (perBatch + subBatch - 1) / subBatch;
        ByteArrayOutputStream recurse = new ByteArrayOutputStream();
        recurse.writeBytes(u32(BATCHES));
        for (int batch = 0; batch < BATCHES; batch++) {
            byte[] body = null;
            long started = System.nanoTime();
            for (int part = 0; part < parts; part++) {
                boolean first = part == 0;
                boolean last = part + 1 == parts;
                int count = Math.min(subBatch, perBatch - part * subBatch);
                String label = String.format("%s %2d/%d", first ? "aggregate" : "extend   ", batch + 1, BATCHES);
                if (parts > 1) {
                    label += String.format(" part %2d/%d", part + 1, parts);
                }
                // Every part but the first extends the proof the server kept; every part but the last has it
                // keep the new one. The last part's proof is the batch's.
                int flags = (first ? 0 : Client.FLAG_USE_KEPT) | (last ? 0 : Client.FLAG_KEEP_PROOF);
                int rate = last ? aggregateRate : 1;
                Long since = parts > 1 && last ? started : null;
                int from = batch * perBatch + part * subBatch;
                body = aggregate(client, flags, signatures, from, count, record, rate, label, since);
            }
            child(recurse, body);
        }
        byte[] body = step(client, Client.OP_RECURSE, 0, recurseRate, recurse.toByteArray(),
                "recurse " + BATCHES + " -> 1", BATCHES + " proofs", null);
        int proofEnd = 8 + (int) le(body).getLong(0);
        ByteArrayOutputStream verify = new ByteArrayOutputStream();
        child(verify, body);
        check(call(client, Client.OP_VERIFY, 0, 0, verify.toByteArray()));
        System.out.printf(
                "verify: proof %d bytes, %d claims, %d bytes -> valid, %.3f s%n",
                proofEnd - 8, le(body).getInt(proofEnd), verify.size(), elapsedNanos / 1e9);
        System.out.printf("total: %.3f s%n", (System.nanoTime() - total) / 1e9);
    }
}
