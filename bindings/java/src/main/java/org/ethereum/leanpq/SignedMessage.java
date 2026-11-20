package org.ethereum.leanpq;

import java.util.Arrays;
import java.util.HexFormat;
import java.util.Objects;

/** A raw signature with the 32-byte public key and 32-byte message it signs. */
public final class SignedMessage {
    private final byte[] publicKey;
    private final byte[] message;
    private final byte[] signature;

    public SignedMessage(byte[] publicKey, byte[] message, byte[] signature) {
        this.publicKey = Native.requireLength(publicKey, Native.PUBLIC_KEY_LENGTH, "publicKey").clone();
        this.message = Native.requireLength(message, Native.MESSAGE_LENGTH, "message").clone();
        this.signature = Objects.requireNonNull(signature, "signature").clone();
    }

    public byte[] publicKey() {
        return publicKey.clone();
    }

    public byte[] message() {
        return message.clone();
    }

    public byte[] signature() {
        return signature.clone();
    }

    /** Appends this entry's {@code pk|msg|sig} record, requiring a {@code signatureLength}-byte signature. */
    void writeRecord(byte[] records, int offset, int signatureLength, String scheme) {
        if (signature.length != signatureLength) {
            throw new IllegalArgumentException(scheme + " signature must be exactly " + signatureLength + " bytes, got " + signature.length);
        }
        System.arraycopy(publicKey, 0, records, offset, publicKey.length);
        System.arraycopy(message, 0, records, offset + publicKey.length, message.length);
        System.arraycopy(signature, 0, records, offset + publicKey.length + message.length, signature.length);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof SignedMessage that
            && Arrays.equals(publicKey, that.publicKey)
            && Arrays.equals(message, that.message)
            && Arrays.equals(signature, that.signature);
    }

    @Override
    public int hashCode() {
        return 31 * (31 * Arrays.hashCode(publicKey) + Arrays.hashCode(message)) + Arrays.hashCode(signature);
    }

    @Override
    public String toString() {
        HexFormat hex = HexFormat.of();
        return "SignedMessage[publicKey=" + hex.formatHex(publicKey) + ", message=" + hex.formatHex(message) + "]";
    }
}
