// The run e2e.sh drives: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch>
//
// Sixteen AGGREGATE requests of signatures-per-batch signatures each, one after the other, then one RECURSE over
// the sixteen proofs and one VERIFY of the result. The file is records of pubkey | message | signature.

import { readFileSync } from "node:fs";
import { Client, OP_AGGREGATE, OP_RECURSE, OP_VERIFY, Response, ST_OK } from "./client";

const BATCHES = 16;
const RESP_CAP = 16 << 20;

const sleeper = new Int32Array(new SharedArrayBuffer(4));

/** Send one request and wait for its response; also the seconds it took. */
function call(client: Client, op: number, rate: number, payload: Uint8Array): [Response, number] {
  const started = process.hrtime.bigint();
  const id = client.send(op, 0, rate, payload, RESP_CAP);
  if (id === null) {
    throw new Error("no room in the channel");
  }
  for (;;) {
    const response = client.tryRecv();
    if (response === null) {
      // A 100 microsecond sleep; nothing ever notifies.
      Atomics.wait(sleeper, 0, 0, 0.1);
      continue;
    }
    if (response.id !== id) {
      throw new Error(`response ${response.id} to request ${id}`);
    }
    return [response, Number(process.hrtime.bigint() - started) / 1e9];
  }
}

/** The body of a response that succeeded. */
function check(response: Response): Buffer {
  const body = Buffer.from(response.body.buffer, response.body.byteOffset, response.body.length);
  if (response.status !== ST_OK) {
    console.log(`  FAILED: status ${response.status} detail ${response.detail}: ${body.toString("utf8")}`);
    process.exit(1);
  }
  return body;
}

/** A proof | claims body cut into the two, each with its length prefix. */
function split(response: Response): [Buffer, Buffer] {
  const body = check(response);
  const proofEnd = 8 + Number(body.readBigUInt64LE(0));
  return [body.subarray(0, proofEnd), body.subarray(proofEnd)];
}

function u32(value: number): Buffer {
  const out = Buffer.alloc(4);
  out.writeUInt32LE(value);
  return out;
}

function main(): void {
  const args = process.argv.slice(2);
  if (args.length !== 5) {
    console.error("usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch>");
    process.exit(2);
  }
  const aggregateRate = Number.parseInt(args[2], 10);
  const recurseRate = Number.parseInt(args[3], 10);
  const perBatch = Number.parseInt(args[4], 10);
  const client = Client.open(args[0]);
  const record = client.pubKeySize() + client.messageLen() + client.sigSize();
  const signatures = readFileSync(args[1]);
  if (signatures.length < BATCHES * perBatch * record) {
    throw new Error("signature file too short");
  }

  const total = process.hrtime.bigint();
  const recurse: Buffer[] = [u32(BATCHES)];
  for (let batch = 0; batch < BATCHES; batch++) {
    const records = signatures.subarray(batch * perBatch * record, (batch + 1) * perBatch * record);
    const payload = Buffer.concat([u32(perBatch), records]);
    const [response, seconds] = call(client, OP_AGGREGATE, aggregateRate, payload);
    const [proof, claims] = split(response);
    console.log(
      `aggregate ${String(batch + 1).padStart(2)}/${BATCHES}: ${perBatch} signatures, ${payload.length} bytes, ` +
        `rate ${aggregateRate} -> proof ${proof.length - 8} bytes, ${claims.readUInt32LE(0)} claims, ` +
        `${seconds.toFixed(3)} s`,
    );
    recurse.push(claims, proof);
  }
  const payload = Buffer.concat(recurse);
  const [response, seconds] = call(client, OP_RECURSE, recurseRate, payload);
  const [proof, claims] = split(response);
  console.log(
    `recurse ${BATCHES} -> 1: ${BATCHES} proofs, ${payload.length} bytes, rate ${recurseRate} -> ` +
      `proof ${proof.length - 8} bytes, ${claims.readUInt32LE(0)} claims, ${seconds.toFixed(3)} s`,
  );
  const verify = Buffer.concat([claims, proof]);
  const [verdict, verifySeconds] = call(client, OP_VERIFY, 0, verify);
  check(verdict);
  console.log(
    `verify: proof ${proof.length - 8} bytes, ${claims.readUInt32LE(0)} claims, ${verify.length} bytes -> valid, ` +
      `${verifySeconds.toFixed(3)} s`,
  );
  console.log(`total: ${(Number(process.hrtime.bigint() - total) / 1e9).toFixed(3)} s`);
}

main();
