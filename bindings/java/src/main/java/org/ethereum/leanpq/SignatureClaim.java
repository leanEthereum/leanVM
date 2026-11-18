package org.ethereum.leanpq;

import java.util.Arrays;
import java.util.HexFormat;

/** A claim proven by an {@link Aggregate}: the 32-byte public key signed the 32-byte message. */
public final class SignatureClaim {
    private final byte[] publicKey;
    private final byte[] message;

    public SignatureClaim(byte[] publicKey, byte[] message) {
        this.publicKey = Native.requireLength(publicKey, Native.PUBLIC_KEY_LENGTH, "publicKey").clone();
        this.message = Native.requireLength(message, Native.MESSAGE_LENGTH, "message").clone();
    }

    public byte[] publicKey() {
        return publicKey.clone();
    }

    public byte[] message() {
        return message.clone();
    }

    /** Writes this claim's 64-byte {@code pk|msg} record at {@code offset}. */
    void writeRecord(byte[] records, int offset) {
        System.arraycopy(publicKey, 0, records, offset, publicKey.length);
        System.arraycopy(message, 0, records, offset + publicKey.length, message.length);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof SignatureClaim that
            && Arrays.equals(publicKey, that.publicKey)
            && Arrays.equals(message, that.message);
    }

    @Override
    public int hashCode() {
        return 31 * Arrays.hashCode(publicKey) + Arrays.hashCode(message);
    }

    @Override
    public String toString() {
        HexFormat hex = HexFormat.of();
        return "SignatureClaim[publicKey=" + hex.formatHex(publicKey) + ", message=" + hex.formatHex(message) + "]";
    }
}
