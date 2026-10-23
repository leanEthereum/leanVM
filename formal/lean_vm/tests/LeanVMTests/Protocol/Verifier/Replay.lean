import LeanVM.Protocol.Verifier

/-!
# The verifier program, replayed against the Python verifier

An end-to-end differential test of `leanVmProgram` in its interactive reading. A mock run of the
Python's `verify_execution` (`python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, imported as a module) replaces the transcript by a
scripted one: the `j`-th challenge is `fe(2^20 + j)`, the committed matrices are the words
`rowWord i p j` (a function of the commitment, the position and the column, so every opening is
consistent), and the prover's `k`-th scalar is `fe(k)`, except for the announced sizes and one
scalar per check, which the driver fixed so that every `require` holds (each check is affine in
the last scalar read before it). The Python run accepts; the driver recorded its events.

`replay` runs the program on the same script: reads from the stream (the root halves, which the
program reads as commitments, removed), challenges by the same formula, openings from the same
words. It must accept, consume every scalar and challenge, and produce the Python's event trace
(`r` a scalar, `s` a challenge, `g` a proof of work, `c` a commitment with its height and width,
`q` an opening with its commitment and positions): the same operations in the same order with
the same shapes and query positions, and the same arithmetic, since every check passes on
values the Python computed. Mutations of a prover message, of the bytecode, of the public input,
and of a committed word are rejected.

The run is at memory `2^16`, stack `2^19` and rate exponent `4`. The driver announced the
tables' log-heights `2, 1, 1, 2, 2, 3`; the script announces the row counts `4, 2, 2, 4, 4, 8`,
which give those heights and leave no padding row, so the program's run is the recorded one.
-/

namespace LeanVMTests.Protocol.Verifier.Replay

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash

/-! ## The script -/

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its three limbs. -/
def e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)

/-- The driver's `fe(k)`. -/
def fe (i : ℕ) : E := e (fw i 0) (fw i 1) (fw i 2)

/-- Word `j` of row `p` of commitment `i`. -/
def rowWord (i p j : ℕ) : K := K.ofBits (fw (i * 2 ^ 40 + p * 2 ^ 12 + j + 2 ^ 30) 3)

/-- The bytecode: 32 words. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The public input: the 32 bytes `fw(i, 10) mod 256`. -/
def samplePublicInput : Digest :=
  let b := fun i ↦ (fw i 10 % 256).toUInt8
  Vector.ofFn fun j : Fin 8 ↦ leWord (b (4 * j)) (b (4 * j + 1)) (b (4 * j + 2)) (b (4 * j + 3))

/-! ## The replay -/

/-- A replay's script and state: the scalars left, the next challenge's index, the shapes
committed, the words committed (as a function of commitment, position and column), and the
trace. -/
structure Script where
  /-- The scalars left. -/
  reads : List E
  /-- The next challenge's index. -/
  samples : ℕ
  /-- The shapes committed so far. -/
  shapes : List (ℕ × ℕ)
  /-- The committed words. -/
  word : ℕ → ℕ → ℕ → K
  /-- The events so far. -/
  trace : String

/-- Run a program on the script: the interactive reading with scripted challenges and words. -/
def replay {α : Type} : Prog α → Script → Option (α × Script)
  | .ret a, s => some (a, s)
  | .fail, _ => none
  | .read k, s => match s.reads with
    | [] => none
    | x :: xs => replay (k x) { s with reads := xs, trace := s.trace.push 'r' }
  | .sample k, s =>
    replay (k (fe (2 ^ 20 + s.samples)))
      { s with samples := s.samples + 1, trace := s.trace.push 's' }
  | .grind b k, s => replay k { s with trace := s.trace ++ s!"g{b};" }
  | .commit h w k, s =>
    replay k { s with shapes := s.shapes ++ [(h, w)], trace := s.trace ++ s!"c{h},{w};" }
  | .query i ps k, s => match s.shapes[i]? with
    | none => none
    | some (h, w) =>
      replay (k (ps.map fun p ↦ (List.range w).map fun j ↦ s.word i (p % 2 ^ h) j))
        { s with trace := s.trace ++ s!"q{i}:" ++ ",".intercalate (ps.map toString) ++ ";" }

/-- Replay up to the first opening: the program there and the state. -/
def replayToQuery {α : Type} : Prog α → Script → Option (Prog α × Script)
  | .ret a, s => some (.ret a, s)
  | .fail, _ => none
  | .read k, s => match s.reads with
    | [] => none
    | x :: xs => replayToQuery (k x) { s with reads := xs, trace := s.trace.push 'r' }
  | .sample k, s =>
    replayToQuery (k (fe (2 ^ 20 + s.samples)))
      { s with samples := s.samples + 1, trace := s.trace.push 's' }
  | .grind b k, s => replayToQuery k { s with trace := s.trace ++ s!"g{b};" }
  | .commit h w k, s =>
    replayToQuery k { s with shapes := s.shapes ++ [(h, w)], trace := s.trace ++ s!"c{h},{w};" }
  | .query i ps k, s => some (.query i ps k, s)

/-! ## The Python's run -/

/-- The prover messages the mock prover fixed (stream index, value). -/
def rate4Overrides : List (ℕ × E) :=
  [(0, (e 0x10 0x0 0x0)), (1, (e 0x4 0x0 0x0)), (2, (e 0x2 0x0 0x0)), (3, (e 0x2 0x0 0x0)),
   (4, (e 0x4 0x0 0x0)), (5, (e 0x4 0x0 0x0)), (6, (e 0x8 0x0 0x0)), (7, (e 0x4 0x0 0x0)),
   (17, (e 0x4cc9bc95018ab843 0xe49f82eb12a0b9da 0x449f7a773e19fee8)),
   (33, (e 0x177cdc0d56abd95b 0xa1abc88d45768960 0x78458064b5757945)),
   (57, (e 0x68abf01c4c82c636 0x337f3743ae34f5a8 0x74fa11f729a09a09)),
   (89, (e 0x11e11744b395dc3b 0xf31484b25bd85738 0xcef65cc70a5c9d4b)),
   (129, (e 0xf1cb9fcde1e19915 0x630a6d718389e0c4 0x7c6f4379d0c7438f)),
   (177, (e 0xfbff93d06721930c 0x14a8a78b2192ebe1 0xd7a4f998bd2c0849)),
   (233, (e 0x473bb5b5f8fbe367 0x3a93da820caeb481 0x9a725556b9243fa1)),
   (297, (e 0x59db02be27a3c6df 0x364b6388157eeb71 0x38466d1c976b2c26)),
   (369, (e 0x7d4fa5bc403e93f0 0x13e42ac66d7d74cb 0x79c9f051351b0691)),
   (487, (e 0xce6fd443ffe4fa04 0x806c97f9849c887 0x61eeaa52f8095601)),
   (655, (e 0xc1bc8b522f68e85e 0xe49dc9ca0ebfd323 0x8c23fef085d8c71b)),
   (741, (e 0xf8f922e6b237e38 0xa6bf155cf50bc7a4 0xa36c6f955fa74391))]

/-- The stream indices of the root halves, which are commitments here. -/
def rate4Roots : List ℕ := [8, 9, 670, 671, 685, 686]

/-- The number of scalars the Python read, root halves included. -/
def rate4Reads : ℕ := 742

/-- The number of challenges the Python drew. -/
def rate4Samples : ℕ := 187

/-- The Python's run, event by event. -/
def rate4Trace : String :=
  "rrrrrrrrc17,64;sssssrrsrrrrrrssrrrrsrrrrrrrrrrrrsssrrrrsrrrrsrrrrsrrrrrrrrrrrrsssrrrrsrr" ++
  "rrsrrrrsrrrrsrrrrsrrrrrrrrrrrrsssrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrrrrrrrrrsssrrrrs" ++
  "rrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrrrrrrrrrsssrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrr" ++
  "rsrrrrsrrrrsrrrrsrrrrsrrrrrrrrrrrrsssrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsr" ++
  "rrrsrrrrsrrrrsrrrrrrrrrrrrsssrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrrsrrrr" ++
  "srrrrsrrrrsrrrrsrrrrrrrrrrrrssrrrrrsrrrsrrrsrrrsrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr" ++
  "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsssssrrrrrrrrrrrrrrrrrrr" ++
  "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrsrrsrrsrrsrrsrrsrrsrrsrrsrrsrrsrrsrrsrrsrrs" ++
  "rrsrrsrrsrrsrrsrrsrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrssssss" ++
  "srrsrrsrrsrrsrrsrrsrrc16,48;sssssssssssssrrrg17;sssssssq0:35985,104351,67609,40438,71577" ++
  ",53254,107946,77698,25702,26217,51117,67750,22340,59016,78269,114522,39936,33681,88255,1" ++
  "10306,82728,21899,99515,71401,50422,116100,26395,26619,90488,99323,63838,8168,123754,208" ++
  ",120463,41828,31051,69341,13301,16223,109880,17370,64680,94536,31973,38452,33235,68882,1" ++
  "12286,131055,73029,120436,101974,121191,65318,63738;rrsrrsrrsrrsrrc15,48;sssssssssrrrg17" ++
  ";ssssq1:15925,8464,41701,19465,11064,62115,60695,7614,6203,50230,14154,61300,47690,41050" ++
  ",7326,59969,42829,29165,26321,48118,37968,17280,45316,36267,13919,8101,38488,34936,9058," ++
  "61752,57482,23085;rrsrrsrrsrrsrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrg17;sssq2:7901,14024,170" ++
  "92,28203,15875,7905,14587,15709,25359,5105,23290,40,6898,13661,10666,24551,32605,2096,10" ++
  "075,22810,30893,10473,16631;rrsrrsrrsrrsrrs"

/-- The scalars of the Python's stream, the root halves removed, with `overrides` in place. -/
def script (overrides : List (ℕ × E)) : List E :=
  ((List.range rate4Reads).filter (· ∉ rate4Roots)).map fun k ↦ (overrides.lookup k).getD (fe k)

/-- The replay of the program on the script. -/
def run (bytecode : List K) (publicInput : Digest) (overrides : List (ℕ × E)) :
    Option (Bool × Script) :=
  replay (leanVmProgram bytecode publicInput) ⟨script overrides, 0, [], rowWord, ""⟩

/-- The replay accepts, consumes the script, and retraces the Python's run. -/
def accepts (r : Option (Bool × Script)) : Bool :=
  match r with
  | some (true, s) => s.reads.isEmpty && s.samples == rate4Samples && s.trace == rate4Trace
  | _ => false

/-- The committed words with WHIR's last level changed. -/
def wrongWord (i p j : ℕ) : K := if i = 2 then rowWord i p j + 1 else rowWord i p j

/-- The run up to WHIR's first opening (the bus, table, public-input and Flock phases, which
dominate the cost), then the rest twice: with the committed words, which must accept and
retrace the Python's run, and with a word changed at WHIR's last level, whose opened rows move
the enforced sum, so that the terminal check rejects. One evaluation shares the prefix. -/
def acceptsAndRejectsWrongWord : Bool :=
  match replayToQuery (leanVmProgram sampleBytecode samplePublicInput)
      ⟨script rate4Overrides, 0, [], rowWord, ""⟩ with
  | some (p, s) => accepts (replay p s) && (replay p { s with word := wrongWord }).isNone
  | none => false

#guard acceptsAndRejectsWrongWord

/-! ## Mutations -/

/-- `overrides` with the `n`-th fixed scalar moved by one. -/
def nudge (n : ℕ) : List (ℕ × E) :=
  rate4Overrides.modify n fun (k, v) ↦ (k, v + 1)

/- The scalar that closes the last GKR layer, and the one that closes the table sumcheck's
terminal check: each is the unique value passing its check. -/
#guard run sampleBytecode samplePublicInput (nudge 16) |>.isNone
#guard run sampleBytecode samplePublicInput (nudge 17) |>.isNone

/- Another bytecode: its fingerprint moves the bus totals, and the table sumcheck rejects. -/
#guard run (sampleBytecode.set 3 0) samplePublicInput rate4Overrides |>.isNone

/- Another public input: the memory claims the verifier computes from it are false of the
committed words, and the opening rejects. -/
#guard run sampleBytecode (samplePublicInput.set 0 0) rate4Overrides |>.isNone

end LeanVMTests.Protocol.Verifier.Replay
