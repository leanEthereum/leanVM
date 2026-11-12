## The run e2e.sh drives: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate>
##
## Sixteen AGGREGATE requests of 1500 signatures each, one after the other, then one RECURSE over
## the sixteen proofs. The file is records of pubkey | message | signature.

import std/[monotimes, options, os, strformat, strutils, times]
from std/posix import usleep
import leanvmsidecar

const
  batches = 16
  perBatch = 1500
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

# Cuts a proof | claims body into the two, each with its length prefix.
proc split(response: Response): (seq[byte], seq[byte]) =
  if response.status != StOk:
    let text = cast[string](response.body)
    fatal(&"  FAILED: status {response.status} detail {response.detail}: {text}")
  let cut = 8 + int(u64(response.body, 0))
  (response.body[0 ..< cut], response.body[cut .. ^1])

proc main() =
  if paramCount() != 4:
    stderr.writeLine("usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate>")
    quit(2)
  let
    aggregateRate = uint32(parseUInt(paramStr(3)))
    recurseRate = uint32(parseUInt(paramStr(4)))
  var client = openClient(paramStr(1))
  let
    record = client.pubKeySize + client.messageLen + client.sigSize
    signatures = readFile(paramStr(2))
    batchLen = perBatch * record
  if signatures.len < batches * batchLen: fatal("signature file too short")

  let total = getMonoTime()
  var recurse: seq[byte]
  recurse.putU32(batches)
  for batch in 0 ..< batches:
    var payload = newSeqOfCap[byte](4 + batchLen)
    payload.putU32(perBatch)
    payload.setLen(4 + batchLen)
    copyMem(addr payload[4], addr signatures[batch * batchLen], batchLen)
    let
      (response, elapsed) = client.call(OpAggregate, 0, aggregateRate, payload)
      (proof, claims) = split(response)
    echo &"aggregate {batch + 1:2}/{batches}: {perBatch} signatures, {payload.len} bytes, rate {aggregateRate}",
      &" -> proof {proof.len - 8} bytes, {u32(claims, 0)} claims, {elapsed:.3f} s"
    recurse.add(claims)
    recurse.add(proof)
  let
    (response, elapsed) = client.call(OpRecurse, 0, recurseRate, recurse)
    (proof, claims) = split(response)
  echo &"recurse {batches} -> 1: {batches} proofs, {recurse.len} bytes, rate {recurseRate}",
    &" -> proof {proof.len - 8} bytes, {u32(claims, 0)} claims, {elapsed:.3f} s"
  echo &"total: {seconds(total):.3f} s"
  client.close()

main()
