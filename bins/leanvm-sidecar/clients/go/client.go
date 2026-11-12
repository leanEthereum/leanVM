// Package leanvmsidecar is a client of the leanvm-sidecar service: Send a request, TryRecv its response.
//
// Payloads and response bodies are raw bytes in the encodings of PROTOCOL.md. It mirrors the Rust
// client in crates/leanvm_sidecar_client.
//
// One Client per channel, used from one goroutine at a time. Open it while no request of an earlier
// client is outstanding: the server would write that request's response into arena space this
// client hands out again.
//
// Little-endian hosts only: the ring counters are read as native words.
package leanvmsidecar

import (
	"encoding/binary"
	"errors"
	"os"
	"sync/atomic"
	"syscall"
	"unsafe"
)

const (
	OpAggregate    uint32 = 1
	OpRecurse      uint32 = 2
	OpVerify       uint32 = 3
	OpVerifyNarrow uint32 = 4

	// FlagVerifyChildren makes OpRecurse verify every child natively before proving.
	FlagVerifyChildren uint32 = 1

	StOK                uint32 = 0
	StBadRequest        uint32 = 1
	StRespTooSmall      uint32 = 2
	StInvalidProof      uint32 = 3
	StAggregationFailed uint32 = 4
)

const (
	magic   = 0x48534d564e41454c // "LEANVMSH"
	version = 1
	msgSize = 64

	hMagic      = 0
	hVersion    = 8
	hEpoch      = 16
	hRingCap    = 24
	hTotal      = 32
	hReqRing    = 40
	hRespRing   = 48
	hArenaOff   = 56
	hArenaLen   = 64
	hPubKeySize = 72
	hMessageLen = 80
	hSigSize    = 88
	headerSize  = 96

	rHead  = 0
	rTail  = 64
	rSlots = 128
)

// ErrFull: the request ring or the arena has no room. Receive a response and retry.
var ErrFull = errors.New("leanvmsidecar: no room in the request ring or the arena")

var errHeader = errors.New("leanvmsidecar: not a leanvm-sidecar channel of this version")

type Response struct {
	// ID is what Send returned for the request.
	ID     uint64
	Status uint32
	Detail uint32
	// RespLen is the body's length, or under StRespTooSmall the response capacity the request needed.
	RespLen uint64
	// Body is the op's response under StOK, UTF-8 text for a human on a failure, empty under StRespTooSmall.
	Body []byte
}

// block is a request's arena region: its payload, then its response region. Offsets from the arena's start.
type block struct {
	id         uint64
	off        uint64
	payloadLen uint64
	respCap    uint64
}

func (b block) end() uint64 { return b.off + b.payloadLen + b.respCap }

type Client struct {
	data     []byte
	ringCap  uint64
	reqRing  uint64
	respRing uint64
	arenaOff uint64
	arenaLen uint64
	nextID   uint64
	// Blocks of requests not yet answered, oldest first. The server answers in order, so the arena
	// is a circular buffer of them: allocated at the back, freed at the front.
	live []block
}

// Open maps the channel the server created at path. Responses left by an earlier client are discarded.
func Open(path string) (*Client, error) {
	file, err := os.OpenFile(path, os.O_RDWR, 0)
	if err != nil {
		return nil, err
	}
	defer file.Close()
	info, err := file.Stat()
	if err != nil {
		return nil, err
	}
	total := uint64(info.Size())
	if total < headerSize {
		return nil, errHeader
	}
	data, err := syscall.Mmap(int(file.Fd()), 0, int(total), syscall.PROT_READ|syscall.PROT_WRITE, syscall.MAP_SHARED|mapPopulate)
	if err != nil {
		return nil, err
	}
	c := &Client{data: data}
	field := func(at uint64) uint64 { return atomic.LoadUint64(c.word(at)) }
	c.ringCap, c.reqRing, c.respRing = field(hRingCap), field(hReqRing), field(hRespRing)
	c.arenaOff, c.arenaLen = field(hArenaOff), field(hArenaLen)
	// Every later access is in bounds given these: the rings sit below the arena, the arena inside the file.
	ringFits := func(ring uint64) bool {
		return ring%8 == 0 && ring+rSlots <= c.arenaOff && c.ringCap <= (c.arenaOff-ring-rSlots)/msgSize
	}
	ok := field(hMagic) == magic && field(hVersion) == version && field(hTotal) == total &&
		c.ringCap != 0 && c.ringCap&(c.ringCap-1) == 0 &&
		c.arenaOff <= total && c.arenaLen == total-c.arenaOff &&
		ringFits(c.reqRing) && ringFits(c.respRing)
	if !ok {
		syscall.Munmap(data)
		return nil, errHeader
	}
	atomic.StoreUint64(c.word(c.respRing+rHead), atomic.LoadUint64(c.word(c.respRing+rTail)))
	return c, nil
}

// Close unmaps the channel. The Client must not be used afterwards.
func (c *Client) Close() error {
	data := c.data
	c.data = nil
	return syscall.Munmap(data)
}

// word is the u64 at an 8-aligned offset; the mapping is page-aligned.
func (c *Client) word(at uint64) *uint64 {
	return (*uint64)(unsafe.Pointer(&c.data[at : at+8][0]))
}

func (c *Client) slot(ring, index uint64) []byte {
	at := ring + rSlots + (index&(c.ringCap-1))*msgSize
	return c.data[at : at+msgSize]
}

// Epoch is incremented each time the server starts. A request in flight across a restart gets no response.
func (c *Client) Epoch() uint64 { return atomic.LoadUint64(c.word(hEpoch)) }

func (c *Client) PubKeySize() int { return int(atomic.LoadUint64(c.word(hPubKeySize))) }
func (c *Client) MessageLen() int { return int(atomic.LoadUint64(c.word(hMessageLen))) }
func (c *Client) SigSize() int    { return int(atomic.LoadUint64(c.word(hSigSize))) }

// place says where a block of n bytes goes, from the arena's start, given the blocks still held.
func place(live []block, arenaLen, n uint64) (uint64, bool) {
	if len(live) == 0 {
		return 0, n <= arenaLen
	}
	first, last := live[0], live[len(live)-1]
	end := last.end()
	switch {
	case last.off < first.off:
		// Wrapped: the gap up to the oldest block.
		return end, n <= first.off-end
	case n <= arenaLen-end:
		return end, true
	default:
		// Wrap into the space before the oldest block. first.off > 0 keeps last.off < first.off meaning wrapped.
		return 0, first.off > 0 && n <= first.off
	}
}

// Send queues a request and returns its id. respCap bytes of arena are reserved for the response:
// a proof that does not fit is discarded by the server (StRespTooSmall).
func (c *Client) Send(op, flags, logInvRate uint32, payload []byte, respCap int) (uint64, error) {
	tail := atomic.LoadUint64(c.word(c.reqRing + rTail))
	if tail-atomic.LoadUint64(c.word(c.reqRing+rHead)) >= c.ringCap {
		return 0, ErrFull
	}
	if respCap < 0 || uint64(respCap) > c.arenaLen || uint64(len(payload)) > c.arenaLen {
		return 0, ErrFull
	}
	b := block{payloadLen: uint64(len(payload)), respCap: uint64(respCap)}
	off, ok := place(c.live, c.arenaLen, b.payloadLen+b.respCap)
	if !ok {
		return 0, ErrFull
	}
	c.nextID++
	b.id, b.off = c.nextID, off
	reqOff := c.arenaOff + off
	copy(c.data[reqOff:reqOff+b.payloadLen], payload)

	msg := c.slot(c.reqRing, tail)
	le := binary.LittleEndian
	le.PutUint64(msg[0:], b.id)
	le.PutUint32(msg[8:], op)
	le.PutUint32(msg[12:], flags)
	le.PutUint64(msg[16:], reqOff)
	le.PutUint64(msg[24:], b.payloadLen)
	le.PutUint64(msg[32:], reqOff+b.payloadLen)
	le.PutUint64(msg[40:], b.respCap)
	le.PutUint32(msg[48:], logInvRate)
	clear(msg[52:])
	atomic.StoreUint64(c.word(c.reqRing+rTail), tail+1)
	c.live = append(c.live, b)
	return b.id, nil
}

// TryRecv returns the next response, if the server has produced one. It frees the request's arena
// block, and those of earlier requests that a server restart left unanswered.
func (c *Client) TryRecv() (Response, bool) {
	head := atomic.LoadUint64(c.word(c.respRing + rHead))
	if atomic.LoadUint64(c.word(c.respRing+rTail)) == head {
		return Response{}, false
	}
	msg := c.slot(c.respRing, head)
	le := binary.LittleEndian
	r := Response{ID: le.Uint64(msg[0:]), Status: le.Uint32(msg[8:]), Detail: le.Uint32(msg[12:]), RespLen: le.Uint64(msg[16:])}
	atomic.StoreUint64(c.word(c.respRing+rHead), head+1)

	for len(c.live) > 0 && c.live[0].id < r.ID {
		c.live = c.live[1:]
	}
	if len(c.live) > 0 && c.live[0].id == r.ID {
		b := c.live[0]
		c.live = c.live[1:]
		if r.Status != StRespTooSmall && r.RespLen <= b.respCap {
			respOff := c.arenaOff + b.off + b.payloadLen
			r.Body = append([]byte(nil), c.data[respOff:respOff+r.RespLen]...)
		}
	}
	return r, true
}
