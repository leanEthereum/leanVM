// Client of the leanvm-sidecar service: send a request, tryRecv its response.
//
// Payloads and response bodies are raw bytes in the encodings of PROTOCOL.md. It mirrors the Rust
// client in crates/leanvm_sidecar_client. Node has no mmap, so the mapping comes from the small
// addon in mmap.c; everything else is here.
//
// One Client per channel. Open it while no request of an earlier client is outstanding: the server
// would write that request's response into arena space this client hands out again.
//
// Little-endian hosts only: the ring counters are read as native words.

import { join } from "node:path";

// eslint-disable-next-line @typescript-eslint/no-var-requires
const native: { map(path: string): ArrayBuffer } = require(join(__dirname, "mmap.node"));

export const OP_AGGREGATE = 1;
export const OP_RECURSE = 2;
export const OP_VERIFY = 3;
export const OP_VERIFY_NARROW = 4;
export const OP_EXTEND = 5;

/** OP_RECURSE, OP_EXTEND: verify every child natively before proving. */
export const FLAG_VERIFY_CHILDREN = 1;
/** A proving op: the server keeps the proof it returns, in place of any it held. */
export const FLAG_KEEP_PROOF = 2;
/** OP_RECURSE, OP_EXTEND: the kept proof is one more child, and is no longer kept. */
export const FLAG_USE_KEPT = 4;

export const ST_OK = 0;
export const ST_BAD_REQUEST = 1;
export const ST_RESP_TOO_SMALL = 2;
export const ST_INVALID_PROOF = 3;
export const ST_AGGREGATION_FAILED = 4;

const MAGIC = 0x48534d564e41454cn; // "LEANVMSH"
const VERSION = 1n;
const MSG_SIZE = 64;

const H_MAGIC = 0;
const H_VERSION = 8;
const H_EPOCH = 16;
const H_RING_CAP = 24;
const H_TOTAL = 32;
const H_REQ_RING = 40;
const H_RESP_RING = 48;
const H_ARENA_OFF = 56;
const H_ARENA_LEN = 64;
const H_PUB_KEY_SIZE = 72;
const H_MESSAGE_LEN = 80;
const H_SIG_SIZE = 88;
const HEADER_SIZE = 96;

const R_HEAD = 0;
const R_TAIL = 64;
const R_SLOTS = 128;

const U64_MASK = (1n << 64n) - 1n;

export interface Response {
  /** What send returned for the request. */
  id: bigint;
  status: number;
  detail: number;
  /** The body's length, or under ST_RESP_TOO_SMALL the response capacity the request needed. */
  respLen: bigint;
  /** The op's response under ST_OK, UTF-8 text for a human on a failure, empty under ST_RESP_TOO_SMALL. */
  body: Uint8Array;
}

/** A request's arena block: its payload, then its response region. Offsets from the arena's start. */
export interface Block {
  id: bigint;
  off: number;
  payloadLen: number;
  respCap: number;
}

const end = (block: Block): number => block.off + block.payloadLen + block.respCap;

/** Where a block of len bytes goes, from the arena's start, given the blocks still held; null if nowhere. */
export function place(live: readonly Block[], arenaLen: number, len: number): number | null {
  if (live.length === 0) {
    return len <= arenaLen ? 0 : null;
  }
  const first = live[0];
  const last = live[live.length - 1];
  const lastEnd = end(last);
  if (last.off < first.off) {
    // Wrapped: the gap up to the oldest block.
    return len <= first.off - lastEnd ? lastEnd : null;
  }
  if (len <= arenaLen - lastEnd) {
    return lastEnd;
  }
  // Wrap into the space before the oldest block. first.off > 0 keeps last.off < first.off meaning wrapped.
  return first.off > 0 && len <= first.off ? 0 : null;
}

export class Client {
  private readonly bytes: Uint8Array;
  private readonly view: DataView;
  /** The file as u64 words, for atomic access to the ring counters: word i is at offset 8 * i. */
  private readonly words: BigUint64Array;
  private readonly ringCap: bigint;
  private readonly reqRing: number;
  private readonly respRing: number;
  private readonly arenaOff: number;
  private readonly arenaLen: number;
  private nextId = 0n;
  /**
   * Blocks of requests not yet answered, oldest first. The server answers in order, so the arena is a
   * circular buffer of them: allocated at the back, freed at the front.
   */
  private live: Block[] = [];

  /** Map the channel the server created at path. Responses left by an earlier client are discarded. */
  static open(path: string): Client {
    return new Client(native.map(path));
  }

  private constructor(buffer: ArrayBuffer) {
    const total = buffer.byteLength;
    if (total < HEADER_SIZE) {
      throw new Error("not a leanvm-sidecar channel");
    }
    this.bytes = new Uint8Array(buffer);
    this.view = new DataView(buffer);
    this.words = new BigUint64Array(buffer, 0, Math.floor(total / 8));
    const field = (at: number): bigint => this.view.getBigUint64(at, true);
    const ringCap = field(H_RING_CAP);
    const arenaOff = field(H_ARENA_OFF);
    // Every later access is in bounds given these: the rings sit below the arena, the arena inside the file.
    const ringFits = (ring: bigint): boolean =>
      ring % 8n === 0n && ring + BigInt(R_SLOTS) + ringCap * BigInt(MSG_SIZE) <= arenaOff;
    const ok =
      field(H_MAGIC) === MAGIC &&
      field(H_VERSION) === VERSION &&
      field(H_TOTAL) === BigInt(total) &&
      ringCap > 0n &&
      ringCap <= BigInt(total) &&
      (ringCap & (ringCap - 1n)) === 0n &&
      arenaOff <= BigInt(total) &&
      field(H_ARENA_LEN) === BigInt(total) - arenaOff &&
      ringFits(field(H_REQ_RING)) &&
      ringFits(field(H_RESP_RING));
    if (!ok) {
      throw new Error("not a leanvm-sidecar channel of this version");
    }
    this.ringCap = ringCap;
    this.reqRing = Number(field(H_REQ_RING));
    this.respRing = Number(field(H_RESP_RING));
    this.arenaOff = Number(arenaOff);
    this.arenaLen = total - this.arenaOff;
    this.store(this.respRing + R_HEAD, this.load(this.respRing + R_TAIL));
  }

  /** Atomic load of the u64 at an 8-aligned offset. */
  private load(at: number): bigint {
    return Atomics.load(this.words, at / 8);
  }

  private store(at: number, value: bigint): void {
    Atomics.store(this.words, at / 8, value);
  }

  private slot(ring: number, index: bigint): number {
    return ring + R_SLOTS + Number(index & (this.ringCap - 1n)) * MSG_SIZE;
  }

  /** Incremented each time the server starts. A request in flight across a restart gets no response. */
  epoch(): bigint {
    return this.load(H_EPOCH);
  }

  pubKeySize(): number {
    return Number(this.view.getBigUint64(H_PUB_KEY_SIZE, true));
  }

  messageLen(): number {
    return Number(this.view.getBigUint64(H_MESSAGE_LEN, true));
  }

  sigSize(): number {
    return Number(this.view.getBigUint64(H_SIG_SIZE, true));
  }

  /**
   * Queue a request. respCap bytes of arena are reserved for the response: a proof that does not fit
   * is discarded by the server (ST_RESP_TOO_SMALL).
   *
   * Returns the request's id, or null if the request ring or the arena has no room: receive a
   * response and retry.
   */
  send(op: number, flags: number, logInvRate: number, payload: Uint8Array, respCap: number): bigint | null {
    const tail = this.load(this.reqRing + R_TAIL);
    if (((tail - this.load(this.reqRing + R_HEAD)) & U64_MASK) >= this.ringCap) {
      return null;
    }
    if (!Number.isSafeInteger(respCap) || respCap < 0) {
      return null;
    }
    const off = place(this.live, this.arenaLen, payload.length + respCap);
    if (off === null) {
      return null;
    }
    const id = ++this.nextId;
    const reqOff = this.arenaOff + off;
    this.bytes.set(payload, reqOff);

    const msg = this.slot(this.reqRing, tail);
    this.view.setBigUint64(msg, id, true);
    this.view.setUint32(msg + 8, op, true);
    this.view.setUint32(msg + 12, flags, true);
    this.view.setBigUint64(msg + 16, BigInt(reqOff), true);
    this.view.setBigUint64(msg + 24, BigInt(payload.length), true);
    this.view.setBigUint64(msg + 32, BigInt(reqOff + payload.length), true);
    this.view.setBigUint64(msg + 40, BigInt(respCap), true);
    this.view.setUint32(msg + 48, logInvRate, true);
    this.bytes.fill(0, msg + 52, msg + MSG_SIZE);
    this.store(this.reqRing + R_TAIL, (tail + 1n) & U64_MASK);
    this.live.push({ id, off, payloadLen: payload.length, respCap });
    return id;
  }

  /**
   * The next response, or null if the server has produced none. Frees the request's arena block, and
   * those of earlier requests that a server restart left unanswered.
   */
  tryRecv(): Response | null {
    const head = this.load(this.respRing + R_HEAD);
    if (this.load(this.respRing + R_TAIL) === head) {
      return null;
    }
    const msg = this.slot(this.respRing, head);
    const response: Response = {
      id: this.view.getBigUint64(msg, true),
      status: this.view.getUint32(msg + 8, true),
      detail: this.view.getUint32(msg + 12, true),
      respLen: this.view.getBigUint64(msg + 16, true),
      body: new Uint8Array(0),
    };
    this.store(this.respRing + R_HEAD, (head + 1n) & U64_MASK);

    while (this.live.length > 0 && this.live[0].id < response.id) {
      this.live.shift();
    }
    if (this.live.length > 0 && this.live[0].id === response.id) {
      const block = this.live.shift()!;
      if (response.status !== ST_RESP_TOO_SMALL && response.respLen <= BigInt(block.respCap)) {
        const respOff = this.arenaOff + block.off + block.payloadLen;
        // slice copies: the body outlives the arena block.
        response.body = this.bytes.slice(respOff, respOff + Number(response.respLen));
      }
    }
    return response;
  }
}
