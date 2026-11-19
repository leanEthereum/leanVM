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

/** Builds the aggregation guest ahead of the first proof. Optional and idempotent. */
export declare function setup(): Promise<void>

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
 * The consensus `pq` VRF tree of a seed, pruned to the slots `[start, end)`, with about `sqrt(R)`
 * of its nodes cached for a range of `R` slots. The seed and the range fix the root, so keep both.
 */
export declare class VrfKey {
  private constructor()
  /**
   * Hashes every leaf of the range once. Rejects when the seed is not 32 bytes, or the range is
   * empty or ends past `2^31`.
   */
  static fromSeed(seed: Buffer, start: number, end: number): Promise<VrfKey>
  /**
   * Loads a key from its 32-byte seed and the bytes of `cacheToBytes()`, hashing about `sqrt(R)`
   * nodes. Rejects when the bytes do not encode a range and its cached nodes. The cache is not
   * checked, and a wrong one gives a wrong root: compare `root()` with the registered root.
   */
  static fromCacheBytes(seed: Buffer, cache: Buffer): Promise<VrfKey>
  /** The 32-byte root: the validator's VRF root. */
  root(): Buffer
  /** The range and the cached nodes, about `32 sqrt(R)` bytes, without any secret. */
  cacheToBytes(): Buffer
  /**
   * The 1024-byte proof a block at `slot` reveals: its leaf, then its 31 siblings. Hashes about
   * `3 sqrt(R)` nodes. Throws when the slot is outside the key's range.
   */
  proof(slot: number): Buffer
}

/**
 * Throws if `proof` does not open the leaf of `slot` under `root`. Only the 31 low bits of `slot`
 * count, which must be an integer up to `Number.MAX_SAFE_INTEGER`.
 */
export declare function vrfVerify(root: Buffer, slot: number, proof: Buffer): void

/**
 * A recursive proof that each listed public key signed its message. Every instance has been
 * proven by `aggregate` or verified by `Aggregate.fromBytes`. Its encoding is the proof alone:
 * send the claims alongside it, or let the receiver rebuild them.
 */
export declare class Aggregate {
  private constructor()
  /**
   * Decodes a proof and verifies that it proves exactly the given claims, which may come in any
   * order; a repeated claim counts once. An omitted list means no claims of that scheme. Rejects
   * when the bytes are not an aggregate proof or the proof does not prove exactly these claims.
   */
  static fromBytes(data: Buffer, claims?: { xmss?: Array<Claim>; sphincs?: Array<Claim> }): Promise<Aggregate>
  /** The proof alone, without its claims. */
  toBytes(): Buffer
  /** Strictly sorted. */
  get xmssClaims(): Array<Claim>
  /** Strictly sorted. */
  get sphincsClaims(): Array<Claim>
}

/**
 * Proves every raw signature and every child's claims in one aggregate whose claims are their
 * union. Raw signatures are verified first; at most 16 children; empty input is rejected.
 */
export declare function aggregate(input?: {
  children?: Array<Aggregate>
  xmss?: Array<SignedMessage>
  sphincs?: Array<SignedMessage>
}): Promise<Aggregate>
