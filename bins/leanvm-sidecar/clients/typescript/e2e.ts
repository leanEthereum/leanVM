// The run e2e.sh drives: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>
//
// Sixteen AGGREGATE requests of signatures-per-batch signatures each, one after the other, then one RECURSE over
// the sixteen proofs and one VERIFY of the result. With sub-batch below signatures-per-batch, each
// batch is instead built up in parts of sub-batch signatures: an AGGREGATE, then one EXTEND per part
// of the proof so far, which the server keeps. Parts run at rate 1, except the last at aggregate-rate. The file is records of pubkey | message | signature.

import { readFileSync } from "node:fs";
import {
  Client,
  FLAG_KEEP_PROOF,
  FLAG_USE_KEPT,
  OP_AGGREGATE,
  OP_EXTEND,
  OP_RECURSE,
  OP_VERIFY,
  Response,
  ST_OK,
} from "./client";

const BATCHES = 16;
const RESP_CAP = 16 << 20;

const sleeper = new Int32Array(new SharedArrayBuffer(4));

/** Send one request and wait for its response; also the seconds it took. */
function call(client: Client, op: number, flags: number, rate: number, payload: Uint8Array): [Response, number] {
  const started = process.hrtime.bigint();
  const id = client.send(op, flags, rate, payload, RESP_CAP);
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

/** One proving request: prints the step, with the time since `since` if given, and returns the response's [proof, claims]. */
function step(
  client: Client,
  op: number,
  flags: number,
  rate: number,
  payload: Buffer,
  label: string,
  what: string,
  since: bigint | null,
): [Buffer, Buffer] {
  const [response, seconds] = call(client, op, flags, rate, payload);
  const batch =
    since === null ? "" : `, batch total ${(Number(process.hrtime.bigint() - since) / 1e9).toFixed(3)} s`;
  const [proof, claims] = split(response);
  console.log(
    `${label}: ${what}, ${payload.length} bytes, rate ${rate} -> proof ${proof.length - 8} bytes, ` +
      `${claims.readUInt32LE(0)} claims, ${seconds.toFixed(3)} s${batch}`,
  );
  return [proof, claims];
}

/** AGGREGATE over records, each `record` bytes; under FLAG_USE_KEPT, EXTEND of the proof the server kept with them. */
function aggregate(
  client: Client,
  flags: number,
  records: Buffer,
  record: number,
  rate: number,
  label: string,
  since: bigint | null,
): [Buffer, Buffer] {
  const count = records.length / record;
  const signatures = [u32(count), records];
  if ((flags & FLAG_USE_KEPT) === 0) {
    return step(client, OP_AGGREGATE, flags, rate, Buffer.concat(signatures), label, `${count} signatures`, since);
  }
  // No child in the payload.
  const payload = Buffer.concat([u32(0), ...signatures]);
  return step(client, OP_EXTEND, flags, rate, payload, label, `kept proof + ${count} signatures`, since);
}

function main(): void {
  const args = process.argv.slice(2);
  if (args.length !== 6) {
    console.error("usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>");
    process.exit(2);
  }
  const aggregateRate = Number.parseInt(args[2], 10);
  const recurseRate = Number.parseInt(args[3], 10);
  const perBatch = Number.parseInt(args[4], 10);
  const subBatch = Number.parseInt(args[5], 10);
  const client = Client.open(args[0]);
  const record = client.pubKeySize() + client.messageLen() + client.sigSize();
  const signatures = readFileSync(args[1]);
  if (signatures.length < BATCHES * perBatch * record) {
    throw new Error("signature file too short");
  }

  const total = process.hrtime.bigint();
  const parts = Math.ceil(perBatch / subBatch);
  const recurse: Buffer[] = [u32(BATCHES)];
  for (let batch = 0; batch < BATCHES; batch++) {
    const records = signatures.subarray(batch * perBatch * record, (batch + 1) * perBatch * record);
    let proved: [Buffer, Buffer] | null = null;
    const started = process.hrtime.bigint();
    for (let part = 0; part < parts; part++) {
      const first = part === 0;
      const last = part + 1 === parts;
      // subarray clamps the last part to the batch.
      const sub = records.subarray(part * subBatch * record, (part + 1) * subBatch * record);
      let label = `${first ? "aggregate" : "extend   "} ${String(batch + 1).padStart(2)}/${BATCHES}`;
      if (parts > 1) {
        label += ` part ${String(part + 1).padStart(2)}/${parts}`;
      }
      // Every part but the first extends the proof the server kept; every part but the last has it
      // keep the new one. The last part's proof is the batch's.
      const flags = (first ? 0 : FLAG_USE_KEPT) | (last ? 0 : FLAG_KEEP_PROOF);
      const rate = last ? aggregateRate : 1;
      const since = parts > 1 && last ? started : null;
      proved = aggregate(client, flags, sub, record, rate, label, since);
    }
    recurse.push(proved![1], proved![0]);
  }
  const [proof, claims] = step(
    client, OP_RECURSE, 0, recurseRate, Buffer.concat(recurse), `recurse ${BATCHES} -> 1`, `${BATCHES} proofs`, null,
  );
  const verify = Buffer.concat([claims, proof]);
  const [verdict, verifySeconds] = call(client, OP_VERIFY, 0, 0, verify);
  check(verdict);
  console.log(
    `verify: proof ${proof.length - 8} bytes, ${claims.readUInt32LE(0)} claims, ${verify.length} bytes -> valid, ` +
      `${verifySeconds.toFixed(3)} s`,
  );
  console.log(`total: ${(Number(process.hrtime.bigint() - total) / 1e9).toFixed(3)} s`);
}

main();
