// The run e2e.sh drives: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate>
//
// Sixteen AGGREGATE requests of 1500 signatures each, one after the other, then one RECURSE over
// the sixteen proofs. The file is records of pubkey | message | signature.

import { readFileSync } from "node:fs";
import { Client, OP_AGGREGATE, OP_RECURSE, Response, ST_OK } from "./client";

const BATCHES = 16;
const PER_BATCH = 1500;
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

/** A proof | claims body cut into the two, each with its length prefix. */
function split(response: Response): [Buffer, Buffer] {
  const body = Buffer.from(response.body.buffer, response.body.byteOffset, response.body.length);
  if (response.status !== ST_OK) {
    console.log(`  FAILED: status ${response.status} detail ${response.detail}: ${body.toString("utf8")}`);
    process.exit(1);
  }
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
  if (args.length !== 4) {
    console.error("usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate>");
    process.exit(2);
  }
  const aggregateRate = Number.parseInt(args[2], 10);
  const recurseRate = Number.parseInt(args[3], 10);
  const client = Client.open(args[0]);
  const record = client.pubKeySize() + client.messageLen() + client.sigSize();
  const signatures = readFileSync(args[1]);
  if (signatures.length < BATCHES * PER_BATCH * record) {
    throw new Error("signature file too short");
  }

  const total = process.hrtime.bigint();
  const recurse: Buffer[] = [u32(BATCHES)];
  for (let batch = 0; batch < BATCHES; batch++) {
    const records = signatures.subarray(batch * PER_BATCH * record, (batch + 1) * PER_BATCH * record);
    const payload = Buffer.concat([u32(PER_BATCH), records]);
    const [response, seconds] = call(client, OP_AGGREGATE, aggregateRate, payload);
    const [proof, claims] = split(response);
    console.log(
      `aggregate ${String(batch + 1).padStart(2)}/${BATCHES}: ${PER_BATCH} signatures, ${payload.length} bytes, ` +
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
  console.log(`total: ${(Number(process.hrtime.bigint() - total) / 1e9).toFixed(3)} s`);
}

main();
