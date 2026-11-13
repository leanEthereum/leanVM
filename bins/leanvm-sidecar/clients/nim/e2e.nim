## The run e2e.sh drives: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>
##
## Sixteen AGGREGATE requests of signatures-per-batch signatures each, one after the other, then one RECURSE over
## the sixteen proofs and one VERIFY of the result. With sub-batch below signatures-per-batch, each
## batch is instead built up in parts of sub-batch signatures: an AGGREGATE, then one EXTEND per part
## of the proof so far, which the server keeps. Parts run at rate 1, except the last at aggregate-rate. The file is records of pubkey | message | signature.

import std/[monotimes, options, os, strformat, strutils, times]
from std/posix import usleep
import leanvmsidecar

const
  batches = 16
  respCap = 16'u64 shl 20

proc fatal(text: string) {.noreturn.} =
  stderr.writeLine(text)
  quit(1)

proc seconds(since: MonoTime): float = float((getMonoTime() - since).inMicroseconds) / 1e6

proc putU32(buf: var seq[byte], value: uint32) =
  for shift in [0, 8, 16, 24]: buf.add(byte((value shr shift) and 0xff))

func u32(buf: openArray[byte], at: int): uint32 =
  for i in 0 ..< 4: result = result or (uint32(buf[at + i]) shl (8 * i))

func u64(buf: openArray[byte], at: int): uint64 =
  for i in 0 ..< 8: result = result or (uint64(buf[at + i]) shl (8 * i))

# Sends one request and waits for its response.
proc call(client: var Client, op, flags, rate: uint32, payload: openArray[byte]): (Response, float) =
  let
    started = getMonoTime()
    id = client.send(op, flags, rate, payload, respCap)
  if id.isNone: fatal("no room in the request ring or the arena")
  while true:
    let response = client.tryRecv()
    if response.isNone:
      discard usleep(100)
      continue
    if response.get.id != id.get: fatal(&"response {response.get.id} to request {id.get}")
    return (response.get, seconds(started))

proc check(response: Response) =
  if response.status != StOk:
    let text = cast[string](response.body)
    fatal(&"  FAILED: status {response.status} detail {response.detail}: {text}")

# Cuts a proof | claims body into the two, each with its length prefix.
proc split(response: Response): (seq[byte], seq[byte]) =
  check(response)
  let cut = 8 + int(u64(response.body, 0))
  (response.body[0 ..< cut], response.body[cut .. ^1])

# One proving request: prints the step, with the time since `since` if given, and returns the
# response's (proof, claims).
proc step(client: var Client, op, flags, rate: uint32, payload: openArray[byte], label, what: string,
          since = none(MonoTime)): (seq[byte], seq[byte]) =
  let
    (response, elapsed) = client.call(op, flags, rate, payload)
    batch = if since.isSome: &", batch total {seconds(since.get):.3f} s" else: ""
  result = split(response)
  echo &"{label}: {what}, {payload.len} bytes, rate {rate}",
    &" -> proof {result[0].len - 8} bytes, {u32(result[1], 0)} claims, {elapsed:.3f} s{batch}"

# AGGREGATE over `count` records of `record` bytes each, starting at record `first`; under
# FlagUseKept, EXTEND of the proof the server kept with them.
proc aggregate(client: var Client, flags: uint32, signatures: string, first, count, record: int, rate: uint32,
               label: string, since: Option[MonoTime]): (seq[byte], seq[byte]) =
  let extend = (flags and FlagUseKept) != 0
  var payload: seq[byte]
  # No child in the payload.
  if extend: payload.putU32(0)
  payload.putU32(uint32(count))
  let at = payload.len
  payload.setLen(at + count * record)
  copyMem(addr payload[at], addr signatures[first * record], count * record)
  if extend: client.step(OpExtend, flags, rate, payload, label, &"kept proof + {count} signatures", since)
  else: client.step(OpAggregate, flags, rate, payload, label, &"{count} signatures", since)

proc main() =
  if paramCount() != 6:
    stderr.writeLine("usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>")
    quit(2)
  let
    aggregateRate = uint32(parseUInt(paramStr(3)))
    recurseRate = uint32(parseUInt(paramStr(4)))
    perBatch = parseInt(paramStr(5))
    subBatch = parseInt(paramStr(6))
  var client = openClient(paramStr(1))
  let
    record = client.pubKeySize + client.messageLen + client.sigSize
    signatures = readFile(paramStr(2))
    parts = (perBatch + subBatch - 1) div subBatch
  if signatures.len < batches * perBatch * record: fatal("signature file too short")

  let total = getMonoTime()
  var recurse: seq[byte]
  recurse.putU32(batches)
  for batch in 0 ..< batches:
    var proved: (seq[byte], seq[byte])
    let started = getMonoTime()
    for part in 0 ..< parts:
      let
        first = part == 0
        last = part + 1 == parts
        name = if first: "aggregate" else: "extend   "
      var label = &"{name} {batch + 1:2}/{batches}"
      if parts > 1: label &= &" part {part + 1:2}/{parts}"
      let
        count = min(subBatch, perBatch - part * subBatch)
        # Every part but the first extends the proof the server kept; every part but the last has
        # it keep the new one. The last part's proof is the batch's.
        flags = (if first: 0'u32 else: FlagUseKept) or (if last: 0'u32 else: FlagKeepProof)
        rate = if last: aggregateRate else: 1'u32
        since = if parts > 1 and last: some(started) else: none(MonoTime)
      proved = client.aggregate(flags, signatures, batch * perBatch + part * subBatch, count, record, rate, label,
                                since)
    recurse.add(proved[1])
    recurse.add(proved[0])
  let
    (proof, claims) = client.step(OpRecurse, 0, recurseRate, recurse, &"recurse {batches} -> 1", &"{batches} proofs")
    verify = claims & proof
    (verdict, verifyElapsed) = client.call(OpVerify, 0, 0, verify)
  check(verdict)
  echo &"verify: proof {proof.len - 8} bytes, {u32(claims, 0)} claims, {verify.len} bytes -> valid, {verifyElapsed:.3f} s"
  echo &"total: {seconds(total):.3f} s"
  client.close()

main()
