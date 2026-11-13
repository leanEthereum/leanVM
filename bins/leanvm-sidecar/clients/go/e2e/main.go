// The run e2e.sh drives: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch>
//
// Sixteen AGGREGATE requests of signatures-per-batch signatures each, one after the other, then one RECURSE over
// the sixteen proofs and one VERIFY of the result. The file is records of pubkey | message | signature.
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

func main() {
	if len(os.Args) != 6 {
		fmt.Fprintln(os.Stderr, "usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch>")
		os.Exit(2)
	}
	aggregateRate, err := strconv.ParseUint(os.Args[3], 10, 32)
	fatal(err)
	recurseRate, err := strconv.ParseUint(os.Args[4], 10, 32)
	fatal(err)
	perBatch, err := strconv.Atoi(os.Args[5])
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
	recurse := le.AppendUint32(nil, batches)
	for batch := 0; batch < batches; batch++ {
		payload := le.AppendUint32(nil, uint32(perBatch))
		payload = append(payload, signatures[batch*perBatch*record:(batch+1)*perBatch*record]...)
		response, elapsed := call(client, leanvmsidecar.OpAggregate, 0, uint32(aggregateRate), payload)
		proof, claims := split(response)
		fmt.Printf("aggregate %2d/%d: %d signatures, %d bytes, rate %d -> proof %d bytes, %d claims, %.3f s\n",
			batch+1, batches, perBatch, len(payload), aggregateRate, len(proof)-8, le.Uint32(claims), elapsed.Seconds())
		recurse = append(recurse, claims...)
		recurse = append(recurse, proof...)
	}
	response, elapsed := call(client, leanvmsidecar.OpRecurse, 0, uint32(recurseRate), recurse)
	proof, claims := split(response)
	fmt.Printf("recurse %d -> 1: %d proofs, %d bytes, rate %d -> proof %d bytes, %d claims, %.3f s\n",
		batches, batches, len(recurse), recurseRate, len(proof)-8, le.Uint32(claims), elapsed.Seconds())
	verify := append(append([]byte(nil), claims...), proof...)
	verdict, elapsed := call(client, leanvmsidecar.OpVerify, 0, 0, verify)
	check(verdict)
	fmt.Printf("verify: proof %d bytes, %d claims, %d bytes -> valid, %.3f s\n",
		len(proof)-8, le.Uint32(claims), len(verify), elapsed.Seconds())
	fmt.Printf("total: %.3f s\n", time.Since(total).Seconds())
}
