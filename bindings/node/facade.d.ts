/** A `(publicKey, message)` pair an aggregate proves. Both are 32 bytes. */
export interface Claim {
  publicKey: Buffer
  message: Buffer
}

/** A raw signature to aggregate: a 32-byte public key, a 32-byte message, and its signature. */
export interface SignedMessage {
  publicKey: Buffer
  message: Buffer
  signature: Buffer
}

/**
 * A stateful leanXMSS secret key with `2^32` leaf indices. Never sign two different messages at
 * the same leaf index.
 */
export declare class XmssSecretKey {
  private constructor()
  static generate(): Promise<XmssSecretKey>
  static fromSeed(seed: Buffer): Promise<XmssSecretKey>
  static fromBytes(data: Buffer): Promise<XmssSecretKey>
  /** SECRET KEY MATERIAL: the 32-byte seed. */
  toBytes(): Buffer
  get publicKey(): Buffer
  /** Builds the bottom tree `leafIndex` falls in ahead of signing there. */
  prepare(leafIndex: number): Promise<void>
  /** Resolves to a 2404-byte signature. */
  sign(message: Buffer, leafIndex: number): Promise<Buffer>
}

/** Throws if `signature` is not a valid leanXMSS signature of `message` under `publicKey`. */
export declare function xmssVerify(publicKey: Buffer, message: Buffer, signature: Buffer): void

/** A stateless leanSPHINCS secret key. It signs at most `2^30` messages, deterministically. */
export declare class SphincsSecretKey {
  private constructor()
  static generate(): Promise<SphincsSecretKey>
  static fromSeed(seed: Buffer): Promise<SphincsSecretKey>
  static fromBytes(data: Buffer): Promise<SphincsSecretKey>
  /** SECRET KEY MATERIAL: the 32-byte seed. */
  toBytes(): Buffer
  get publicKey(): Buffer
  /** Resolves to a 7740-byte signature. */
  sign(message: Buffer): Promise<Buffer>
}

/** Throws if `signature` is not a valid leanSPHINCS signature of `message` under `publicKey`. */
export declare function sphincsVerify(publicKey: Buffer, message: Buffer, signature: Buffer): void

/**
 * A recursive proof that each listed public key signed its message. Every instance has been
 * proven by `Sidecar.aggregate` or verified by `Sidecar.verify`. Its encoding is the proof alone:
 * send the claims alongside it, or let the receiver rebuild them.
 */
export declare class Aggregate {
  private constructor()
  /** The proof alone, without its claims. */
  toBytes(): Buffer
  /** Strictly sorted. */
  get xmssClaims(): Array<Claim>
  /** Strictly sorted. */
  get sphincsClaims(): Array<Claim>
}

/**
 * A connection to a leanVM sidecar, a separate process that proves and verifies aggregates (Linux
 * and macOS). Its calls run one at a time; a broken connection is reopened on the next call.
 */
export declare class Sidecar {
  private constructor()
  /** Connects to the sidecar listening on the Unix socket at `socket`. */
  static connect(socket: string): Promise<Sidecar>
  /**
   * Launches the leanvm-sidecar executable at `binary` on `socket`, waits until it listens, and
   * connects. `close` stops it. Its log goes to the socket path plus `.log`.
   */
  static start(binary: string, socket: string): Promise<Sidecar>
  /**
   * Proves every raw signature and every child's claims in one aggregate whose claims are their
   * union. Raw signatures are verified first; at most 16 children; empty input is rejected.
   */
  aggregate(input?: {
    children?: Array<Aggregate>
    xmss?: Array<SignedMessage>
    sphincs?: Array<SignedMessage>
  }): Promise<Aggregate>
  /**
   * Verifies that a proof proves exactly the given claims, which may come in any order; a repeated
   * claim counts once. An omitted list means no claims of that scheme. Rejects when the bytes are
   * not a proof of exactly these claims.
   */
  verify(data: Buffer, claims?: { xmss?: Array<Claim>; sphincs?: Array<Claim> }): Promise<Aggregate>
  /** Closes the connection, and stops a sidecar `start` launched. */
  close(): Promise<void>
}
