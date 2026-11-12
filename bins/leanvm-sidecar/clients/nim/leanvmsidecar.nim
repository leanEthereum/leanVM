## Client of the leanvm-sidecar service: `send` a request, `tryRecv` its response.
##
## Payloads and response bodies are raw bytes in the encodings of PROTOCOL.md. It mirrors the Rust
## client in crates/leanvm_sidecar_client.
##
## One Client per channel, used from one thread at a time. Open it while no request of an earlier
## client is outstanding: the server would write that request's response into arena space this
## client hands out again.
##
## Little-endian hosts only: counters and message fields are read as native words. The atomics are
## the GCC and Clang builtins.

import std/[deques, options, oserrors, posix]

const
  OpAggregate* = 1'u32
  OpRecurse* = 2'u32
  OpVerify* = 3'u32
  OpVerifyNarrow* = 4'u32

  ## Makes OpRecurse verify every child natively before proving.
  FlagVerifyChildren* = 1'u32

  StOk* = 0'u32
  StBadRequest* = 1'u32
  StRespTooSmall* = 2'u32
  StInvalidProof* = 3'u32
  StAggregationFailed* = 4'u32

const
  magic = 0x48534d564e41454c'u64 # "LEANVMSH"
  version = 1'u64
  msgSize = 64'u64

  hMagic = 0'u64
  hVersion = 8'u64
  hEpoch = 16'u64
  hRingCap = 24'u64
  hTotal = 32'u64
  hReqRing = 40'u64
  hRespRing = 48'u64
  hArenaOff = 56'u64
  hArenaLen = 64'u64
  hPubKeySize = 72'u64
  hMessageLen = 80'u64
  hSigSize = 88'u64
  headerSize = 96'u64

  rHead = 0'u64
  rTail = 64'u64
  rSlots = 128'u64

  mapPopulate = when defined(linux): MAP_POPULATE else: 0.cint

type
  Response* = object
    id*: uint64 ## What `send` returned for the request.
    status*: uint32
    detail*: uint32
    respLen*: uint64 ## The body's length, or under StRespTooSmall the response capacity the request needed.
    body*: seq[byte] ## The op's response under StOk, UTF-8 text for a human on a failure, empty under StRespTooSmall.

  # A request's arena region: its payload, then its response region. Offsets from the arena's start.
  Block = object
    id, off, payloadLen, respCap: uint64

  Client* = object
    base: pointer
    total, ringCap, reqRing, respRing, arenaOff, arenaLen, nextId: uint64
    # Blocks of requests not yet answered, oldest first. The server answers in order, so the arena
    # is a circular buffer of them: allocated at the back, freed at the front.
    live: Deque[Block]

func stop(b: Block): uint64 = b.off + b.payloadLen + b.respCap

func at(c: Client, off: uint64): pointer = cast[pointer](cast[uint](c.base) + uint(off))

# `off` is 8-aligned; the mapping is page-aligned.
proc load(c: Client, off: uint64): uint64 = atomicLoadN(cast[ptr uint64](c.at(off)), ATOMIC_ACQUIRE)

proc store(c: Client, off, value: uint64) = atomicStoreN(cast[ptr uint64](c.at(off)), value, ATOMIC_RELEASE)

func slot(c: Client, ring, index: uint64): pointer = c.at(ring + rSlots + (index and (c.ringCap - 1)) * msgSize)

proc put[T](msg: pointer, off: uint, value: T) =
  var v = value
  copyMem(cast[pointer](cast[uint](msg) + off), addr v, sizeof(T))

proc get[T](msg: pointer, off: uint): T = copyMem(addr result, cast[pointer](cast[uint](msg) + off), sizeof(T))

proc openClient*(path: string): Client =
  ## Maps the channel the server created at `path`. Responses left by an earlier client are discarded.
  let fd = posix.open(path.cstring, O_RDWR)
  if fd < 0: raiseOSError(osLastError(), path)
  var st: Stat
  if fstat(fd, st) != 0:
    let err = osLastError()
    discard posix.close(fd)
    raiseOSError(err, path)
  let total = uint64(st.st_size)
  if total < headerSize:
    discard posix.close(fd)
    raise newException(IOError, "not a leanvm-sidecar channel of this version")
  let base = mmap(nil, int(total), PROT_READ or PROT_WRITE, MAP_SHARED or mapPopulate, fd, 0)
  let err = osLastError()
  discard posix.close(fd)
  if base == MAP_FAILED: raiseOSError(err, path)

  var c = Client(base: base, total: total)
  c.ringCap = c.load(hRingCap)
  c.reqRing = c.load(hReqRing)
  c.respRing = c.load(hRespRing)
  c.arenaOff = c.load(hArenaOff)
  c.arenaLen = c.load(hArenaLen)
  # Every later access is in bounds given these: the rings sit below the arena, the arena inside the file.
  proc ringFits(ring: uint64): bool =
    ring mod 8 == 0 and ring + rSlots <= c.arenaOff and c.ringCap <= (c.arenaOff - ring - rSlots) div msgSize
  let ok = c.load(hMagic) == magic and c.load(hVersion) == version and c.load(hTotal) == total and
    c.ringCap != 0 and (c.ringCap and (c.ringCap - 1)) == 0 and
    c.arenaOff <= total and c.arenaLen == total - c.arenaOff and
    ringFits(c.reqRing) and ringFits(c.respRing)
  if not ok:
    discard munmap(base, int(total))
    raise newException(IOError, "not a leanvm-sidecar channel of this version")
  c.store(c.respRing + rHead, c.load(c.respRing + rTail))
  c

proc close*(c: var Client) =
  ## Unmaps the channel. The Client must not be used afterwards.
  discard munmap(c.base, int(c.total))
  c.base = nil

proc epoch*(c: Client): uint64 =
  ## Incremented each time the server starts. A request in flight across a restart gets no response.
  c.load(hEpoch)

proc pubKeySize*(c: Client): int = int(c.load(hPubKeySize))
proc messageLen*(c: Client): int = int(c.load(hMessageLen))
proc sigSize*(c: Client): int = int(c.load(hSigSize))

# Where a block of `n` bytes goes, from the arena's start, given the blocks still held.
func place(live: Deque[Block], arenaLen, n: uint64): Option[uint64] =
  if live.len == 0:
    return if n <= arenaLen: some(0'u64) else: none(uint64)
  let
    first = live.peekFirst
    last = live.peekLast
    stop = last.stop
  if last.off < first.off:
    # Wrapped: the gap up to the oldest block.
    if n <= first.off - stop: some(stop) else: none(uint64)
  elif n <= arenaLen - stop:
    some(stop)
  # Wrap into the space before the oldest block. first.off > 0 keeps last.off < first.off meaning wrapped.
  elif first.off > 0 and n <= first.off:
    some(0'u64)
  else:
    none(uint64)

proc send*(c: var Client, op, flags, logInvRate: uint32, payload: openArray[byte], respCap: uint64): Option[uint64] =
  ## Queues a request and returns its id, or none if the request ring or the arena has no room:
  ## receive a response and retry. `respCap` bytes of arena are reserved for the response: a proof
  ## that does not fit is discarded by the server (StRespTooSmall).
  let tail = c.load(c.reqRing + rTail)
  if tail - c.load(c.reqRing + rHead) >= c.ringCap: return none(uint64)
  let payloadLen = uint64(payload.len)
  if respCap > c.arenaLen or payloadLen > c.arenaLen: return none(uint64)
  let off = place(c.live, c.arenaLen, payloadLen + respCap)
  if off.isNone: return none(uint64)
  inc c.nextId
  let
    b = Block(id: c.nextId, off: off.get, payloadLen: payloadLen, respCap: respCap)
    reqOff = c.arenaOff + b.off
  if payload.len > 0: copyMem(c.at(reqOff), addr payload[0], payload.len)

  let msg = c.slot(c.reqRing, tail)
  put(msg, 0, b.id)
  put(msg, 8, op)
  put(msg, 12, flags)
  put(msg, 16, reqOff)
  put(msg, 24, payloadLen)
  put(msg, 32, reqOff + payloadLen)
  put(msg, 40, respCap)
  put(msg, 48, logInvRate)
  zeroMem(cast[pointer](cast[uint](msg) + 52), 12)
  c.store(c.reqRing + rTail, tail + 1)
  c.live.addLast(b)
  some(b.id)

proc tryRecv*(c: var Client): Option[Response] =
  ## The next response, if the server has produced one. Frees the request's arena block, and those
  ## of earlier requests that a server restart left unanswered.
  let head = c.load(c.respRing + rHead)
  if c.load(c.respRing + rTail) == head: return none(Response)
  let msg = c.slot(c.respRing, head)
  var r = Response(
    id: get[uint64](msg, 0),
    status: get[uint32](msg, 8),
    detail: get[uint32](msg, 12),
    respLen: get[uint64](msg, 16),
  )
  c.store(c.respRing + rHead, head + 1)

  while c.live.len > 0 and c.live.peekFirst.id < r.id: c.live.popFirst()
  if c.live.len > 0 and c.live.peekFirst.id == r.id:
    let b = c.live.popFirst()
    if r.status != StRespTooSmall and r.respLen <= b.respCap and r.respLen > 0:
      r.body = newSeq[byte](r.respLen)
      copyMem(addr r.body[0], c.at(c.arenaOff + b.off + b.payloadLen), r.respLen)
  some(r)

when isMainModule:
  # Random sends and in-order frees: a placed block is inside the arena and overlaps no live one.
  const arenaLen = 100'u64
  var
    live: Deque[Block]
    state = 1'u64
    placed = 0
  for id in 0'u64 ..< 10000'u64:
    state = state * 6364136223846793005'u64 + 1442695040888963407'u64
    let
      n = (state shr 33) mod 40
      off = place(live, arenaLen, n)
    if off.isSome:
      doAssert off.get + n <= arenaLen, "block outside the arena"
      for b in live: doAssert not (off.get + n > b.off and b.stop > off.get), "blocks overlap"
      live.addLast(Block(id: id, off: off.get, payloadLen: n))
      inc placed
    else:
      live.popFirst()
    if (state shr 63) == 1 and live.len > 0: live.popFirst()
  doAssert placed > 1000, "too few blocks placed"
  echo "ok"
