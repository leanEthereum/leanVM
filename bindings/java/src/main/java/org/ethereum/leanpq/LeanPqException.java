package org.ethereum.leanpq;

/** A checked native validation or cryptographic error from lean-pq. */
public final class LeanPqException extends RuntimeException {
    LeanPqException(String message) {
        super(message);
    }
}
