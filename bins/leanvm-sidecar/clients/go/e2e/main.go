// The run e2e.sh drives: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>
//
// Sixteen AGGREGATE requests of signatures-per-batch signatures each, one after the other, then one RECURSE over
// the sixteen proofs and one VERIFY of the result. With sub-batch below signatures-per-batch, each
// batch is instead built up in parts of sub-batch signatures: an AGGREGATE, then one EXTEND per part
// of the proof so far, which the server keeps. Parts run at rate 1, except the last at aggregate-rate. The file is records of pubkey | message | signature.
package main

import (
	"encoding/binary"
	"fmt"
	"os"
	"strconv"
	"time"

	leanvmsidecar "github.com/leanEthereum/leanVM/bins/leanvm-sidecar/clients/go"
)

const (
	batches = 16
	respCap = 16 << 20
)

func fatal(err error) {
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

// call sends one request and waits for its response.
func call(client *leanvmsidecar.Client, op, flags, rate uint32, payload []byte) (leanvmsidecar.Response, time.Duration) {
	started := time.Now()
	id, err := client.Send(op, flags, rate, payload, respCap)
	fatal(err)
	for {
		response, ok := client.TryRecv()
		if !ok {
			time.Sleep(100 * time.Microsecond)
			continue
		}
		if response.ID != id {
			fatal(fmt.Errorf("response %d to request %d", response.ID, id))
		}
		return response, time.Since(started)
	}
}

func check(response leanvmsidecar.Response) {
	if response.Status != leanvmsidecar.StOK {
		fmt.Printf("  FAILED: status %d detail %d: %s\n", response.Status, response.Detail, response.Body)
		os.Exit(1)
	}
}

// split cuts a proof | claims body into the two, each with its length prefix.
func split(response leanvmsidecar.Response) (proof, claims []byte) {
	check(response)
	proofLen := binary.LittleEndian.Uint64(response.Body)
	return response.Body[:8+proofLen], response.Body[8+proofLen:]
}

// step makes one proving request, prints it, with the time since a non-zero since, and returns the
// response's proof and claims.
func step(client *leanvmsidecar.Client, op, flags, rate uint32, payload []byte, label, what string, since time.Time) (proof, claims []byte) {
	response, elapsed := call(client, op, flags, rate, payload)
	batch := ""
	if !since.IsZero() {
		batch = fmt.Sprintf(", batch total %.3f s", time.Since(since).Seconds())
	}
	proof, claims = split(response)
	fmt.Printf("%s: %s, %d bytes, rate %d -> proof %d bytes, %d claims, %.3f s%s\n",
		label, what, len(payload), rate, len(proof)-8, binary.LittleEndian.Uint32(claims), elapsed.Seconds(), batch)
	return proof, claims
}

// aggregate is an AGGREGATE over records, each record bytes; under FlagUseKept, an EXTEND of the proof
// the server kept with them.
func aggregate(client *leanvmsidecar.Client, flags uint32, records []byte, record int, rate uint32, label string, since time.Time) ([]byte, []byte) {
	le := binary.LittleEndian
	count := len(records) / record
	op, what := leanvmsidecar.OpAggregate, fmt.Sprintf("%d signatures", count)
	var payload []byte
	if flags&leanvmsidecar.FlagUseKept != 0 {
		op, what = leanvmsidecar.OpExtend, fmt.Sprintf("kept proof + %d signatures", count)
		// No child in the payload.
		payload = le.AppendUint32(payload, 0)
	}
	payload = append(le.AppendUint32(payload, uint32(count)), records...)
	return step(client, op, flags, rate, payload, label, what, since)
}

func main() {
	if len(os.Args) != 7 {
		fmt.Fprintln(os.Stderr, "usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>")
		os.Exit(2)
	}
	aggregateRate, err := strconv.ParseUint(os.Args[3], 10, 32)
	fatal(err)
	recurseRate, err := strconv.ParseUint(os.Args[4], 10, 32)
	fatal(err)
	perBatch, err := strconv.Atoi(os.Args[5])
	fatal(err)
	subBatch, err := strconv.Atoi(os.Args[6])
	fatal(err)
	client, err := leanvmsidecar.Open(os.Args[1])
	fatal(err)
	defer client.Close()
	record := client.PubKeySize() + client.MessageLen() + client.SigSize()
	signatures, err := os.ReadFile(os.Args[2])
	fatal(err)
	if len(signatures) < batches*perBatch*record {
		fatal(fmt.Errorf("signature file too short"))
	}

	total := time.Now()
	le := binary.LittleEndian
	parts := (perBatch + subBatch - 1) / subBatch
	recurse := le.AppendUint32(nil, batches)
	for batch := 0; batch < batches; batch++ {
		records := signatures[batch*perBatch*record : (batch+1)*perBatch*record]
		var proof, claims []byte
		started := time.Now()
		for part := 0; part < parts; part++ {
			sub := records[part*subBatch*record : min((part+1)*subBatch*record, len(records))]
			// Every part but the first extends the proof the server kept; every part but the last
			// has it keep the new one. The last part's proof is the batch's.
			name, flags, rate := "aggregate", leanvmsidecar.FlagKeepProof, uint32(1)
			if part > 0 {
				name, flags = "extend   ", flags|leanvmsidecar.FlagUseKept
			}
			var since time.Time
			if part+1 == parts {
				flags, rate = flags&^leanvmsidecar.FlagKeepProof, uint32(aggregateRate)
				if parts > 1 {
					since = started
				}
			}
			label := fmt.Sprintf("%s %2d/%d", name, batch+1, batches)
			if parts > 1 {
				label += fmt.Sprintf(" part %2d/%d", part+1, parts)
			}
			proof, claims = aggregate(client, flags, sub, record, rate, label, since)
		}
		recurse = append(append(recurse, claims...), proof...)
	}
	proof, claims := step(client, leanvmsidecar.OpRecurse, 0, uint32(recurseRate), recurse,
		fmt.Sprintf("recurse %d -> 1", batches), fmt.Sprintf("%d proofs", batches), time.Time{})
	verify := append(append([]byte(nil), claims...), proof...)
	verdict, elapsed := call(client, leanvmsidecar.OpVerify, 0, 0, verify)
	check(verdict)
	fmt.Printf("verify: proof %d bytes, %d claims, %d bytes -> valid, %.3f s\n",
		len(proof)-8, le.Uint32(claims), len(verify), elapsed.Seconds())
	fmt.Printf("total: %.3f s\n", time.Since(total).Seconds())
}
