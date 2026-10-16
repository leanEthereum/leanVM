module

public import LeanVMCircuits.Rec.Verdict
public import LeanVMCircuits.Rec.Dump
public import LeanVMCircuits.Rec.TableResid

@[expose] public section

/-!
Transcript binding of a recursion circuit.

A challenge is a squeezed word of a transcript in rows: the output of a `leaf_block` at the duplex's output tag,
whose chaining value is the end of a run of absorb blocks from a constant seed. A wire is *bound* by a squeeze when
it is determined by the words absorbed before it: it is one of them or a constant, or a determination rule makes it
from bound wires. Each rule carries its justification (`Just`): a row's forms, a split, a constant mux bit, a
compression at a constant final word, an equality that is not a test, an inverse, collision resistance of the
compression and of the output window, or a marked union product (`Bind.unionsValid`).

A *test* is an equality made from outside the builder's methods (`eq_e`, `eq_k`, `eq_e_const`, `eq_k_const`) that
reads a wire depending on a challenge. Tests do not bind. The check: every test's wires are bound by one transcript,
so the test is a function of the words that transcript absorbs. The worklist records its firings per transcript, and
the verdict is `Cert.accepts` of that record (`checkbind_sound`), not the worklist's own. A hinted wire a test reads
that no transcript absorbs, and no rule determines from absorbed words, fails the check: the prover may choose it
after the challenge.
-/

namespace LeanVMCircuits.Rec.Bind

open Model

/-- How an equality counts. -/
inductive EqKind where
  /-- `eq_d`: two digests, binding. -/
  | digest
  /-- From outside the methods, between field elements: a test when it reads a challenge. -/
  | field
  /-- Inside a method (`inv`'s product held to one). -/
  | method
  deriving Repr, DecidableEq, Inhabited

/-- A marked block being replayed: a pool or a product, its calls from its start. -/
inductive Pending where
  | pool (pc : PoolCert)
  | product (qc : ProdCert)

/-- A replay of a dump's calls through the model, with what the analysis needs of each call. -/
structure Replay where
  state : State := {}
  calls : Array Call := #[]
  outs : Array (List ℕ) := #[]
  /-- The call that made each wire. -/
  maker : Array ℕ := #[]
  /-- Each equality's kind, in `State.unions` order. -/
  eqKind : Array EqKind := #[]
  /-- The call that made each equality. -/
  eqCall : Array ℕ := #[]
  pending : Option Pending := none
  pools : Array PoolCert := #[]
  prods : Array ProdCert := #[]
  /-- Each `inv` call's `EMUL` row and equality. -/
  invs : Array (ℕ × ℕ) := #[]

/-- A pool's chunk and item cursors and closing check, by `pool_rows`' call counts from its start: where
`PoolCert.ok` checks its calls. -/
def PoolCert.layout (pc : PoolCert) : PoolCert := Id.run do
  let runs := pc.digests.length
  let mut pos := pc.start + 9 + runs
  let mut chunkAt := #[]
  let mut itemAt := #[]
  for j in [0:pc.chunks] do
    chunkAt := chunkAt.push pos
    pos := pos + (if pc.begins j then 1 + 2 * runs else 0) + (if 1 < runs then 2 * runs else 0)
    for k in [0:chunk] do
      itemAt := itemAt.push pos
      let st : Start := if j * chunk + k = 0 then .yes else if k = 0 ∧ 1 < runs then .ifBit 0 else .no
      pos := pos + 13 + sLen st + 6 + hLen st + 16 + (if pc.selecting then 2 else 0)
  return { pc with chunkAt, itemAt, endAt := pos }

/-- A product's item cursors, by `product`'s call counts from its start. -/
def ProdCert.layout (qc : ProdCert) (pc : PoolCert) : ProdCert := Id.run do
  let len := if pc.selecting then 8 else 7
  let mut pos := qc.start + 2
  let mut itemAt := #[]
  for i in [0:pc.n] do
    itemAt := itemAt.push pos
    pos := pos + (if i ≠ 0 ∧ i % chunk = 0 ∧ 1 < pc.runs then 1 else 0) + 8 + 2 * len
  return { qc with itemAt }

/-- Open or close a marked block: a pool's or a product's certificate, its cursors laid out from its first call. -/
def Replay.mark (r : Replay) (line : Dump.Line) : Except String Replay :=
  match line, r.pending with
  | .call _, _ => .ok r
  | .pool chunks selecting digests, none =>
    .ok { r with
      pending := some (.pool { start := r.calls.size, chunks, selecting, digests, chunkAt := #[], itemAt := #[],
                               endAt := 0, packs := [] }) }
  | .product first x1 weights, none =>
    match r.pools.findIdx? fun pc => o r.outs (pc.blk r.outs 0) = first with
    | none => .error s!"a product of no pool marked before it: {first}"
    | some i =>
      .ok { r with pending := some (.product { pool := i, start := r.calls.size, x1, weights, itemAt := #[] }) }
  | .stop, some (.pool pc) =>
    -- The pool's `pack` calls follow its end mark.
    .ok { r with pending := none, pools := r.pools.push { pc.layout with packs := [r.calls.size] } }
  | .stop, some (.product qc) =>
    .ok { r with pending := none, prods := r.prods.push (qc.layout (r.pools.getD qc.pool default)) }
  | .stop, none => .error "an end mark without a start"
  | _, some _ => .error "a mark inside a marked block"

def eqKindOf : Call → EqKind
  | .eqD .. => .digest
  | .eqE .. | .eqK .. | .eqConstE .. | .eqConstK .. => .field
  | _ => .method

def Replay.step (r : Replay) (c : Call) : Replay := Id.run do
  -- Take the fields apart first, so that each array is updated in place.
  let { state, calls, outs, maker, eqKind, eqCall, pending, pools, prods, invs } := r
  let (n0, u0) := (state.next, state.unions.size)
  let (out, s') := c.exec.run state
  let i := calls.size
  let mut maker := maker
  for _ in [n0:s'.next] do
    maker := maker.push i
  let mut eqKind := eqKind
  let mut eqCall := eqCall
  for _ in [u0:s'.unions.size] do
    eqKind := eqKind.push (eqKindOf c)
    eqCall := eqCall.push i
  let invs := match c with
    | .inv _ => if s'.emul.size = state.emul.size + 1 ∧ s'.unions.size = u0 + 1 then invs.push (state.emul.size, u0)
      else invs
    | _ => invs
  return ⟨s', calls.push c, outs.push out, maker, eqKind, eqCall, pending, pools, prods, invs⟩

/-- The counter word's role, its top byte. -/
def role (t : ℕ) : ℕ := t / 2 ^ 56

/-- A transcript block: an absorb block's chaining values and words, or a squeeze, by call. -/
structure Block where
  call : ℕ
  cvIn : ℕ
  cvOut : ℕ
  words : List ℕ
  squeeze : Bool
  deriving Repr, Inhabited

def blocks (r : Replay) : Array Block := Id.run do
  let mut out := #[]
  for i in [0:r.calls.size] do
    match r.calls.getD i .freeE, r.outs.getD i [] with
    | Call.leafBlock h m t _, [o] =>
      if role t = 6 then out := out.push { call := i, cvIn := h, cvOut := o, words := [], squeeze := true }
      else if 2 ≤ role t ∧ role t ≤ 5 then out := out.push { call := i, cvIn := h, cvOut := o, words := m, squeeze := false }
    | _, _ => pure ()
  return out

/-- Every transcript: its path of blocks from a seed to a chaining value no absorb block extends. -/
def transcripts (bs : Array Block) : Array (Array Block) := Id.run do
  let mut absorbOf : Std.HashMap ℕ ℕ := {}
  let mut extended : Std.HashSet ℕ := {}
  let mut squeezesAt : Std.HashMap ℕ (Array Block) := {}
  for i in [0:bs.size] do
    let b := bs[i]!
    if b.squeeze then
      squeezesAt := squeezesAt.insert b.cvIn ((squeezesAt.getD b.cvIn #[]).push b)
    else
      absorbOf := absorbOf.insert b.cvOut i
      extended := extended.insert b.cvIn
  -- The ends: chaining values of absorb outputs or squeeze inputs that nothing extends.
  let mut ends : Array ℕ := #[]
  let mut seen : Std.HashSet ℕ := {}
  for b in bs do
    let cv := if b.squeeze then b.cvIn else b.cvOut
    if !extended.contains cv && !seen.contains cv then
      ends := ends.push cv
      seen := seen.insert cv
  let mut out := #[]
  for e in ends do
    -- Walk back to the seed, collecting chaining values.
    let mut cvs : Array ℕ := #[e]
    let mut cv := e
    let mut fuel := bs.size + 1
    while fuel > 0 do
      fuel := fuel - 1
      match absorbOf[cv]? with
      | some j => cv := bs[j]!.cvIn; cvs := cvs.push cv
      | none => fuel := 0
    let mut path : Array Block := #[]
    for c in cvs.reverse do
      match absorbOf[c]? with
      | some j => path := path.push bs[j]!
      | none => pure ()
      for sq in squeezesAt.getD c #[] do
        path := path.push sq
    if path.any (·.squeeze) then out := out.push path
  return out

/-- The rules of a replayed circuit, and the rows' form rules' count. -/
structure Analysis where
  nodes : ℕ
  rules : Rules Just
  /-- Rules up to here are the rows' forms, splits, muxes and compressions; the hint search walks back through
  them. -/
  nFunction : ℕ

/-- A wire's four limb nodes, as an array. -/
def limbsA (w : ℕ) : Array ℕ := (limbs4 w).toArray

/-- A table's form rules, the same for each row: each conclusion slot limb with the slot limbs it is read off. A
slot limb that is a column gives every other limb that is the same column, and is given by it; any other limb is its
form of the columns it reads, each read off the first slot limb that is that column. -/
def formPlan (t : Table) : Array (ℕ × ℕ × List (ℕ × ℕ)) := Id.run do
  let forms := formsOf t
  let mut first : Std.HashMap ℕ (ℕ × ℕ) := {}
  let mut plan := #[]
  for (slot, s) in forms.zipIdx do
    for (f, i) in slot.zipIdx do
      match f.colOf with
      | some j =>
        match first[j]? with
        | none => first := first.insert j (s, i)
        | some src => plan := (plan.push (s, i, [src])).push (src.1, src.2, [(s, i)])
      | none => pure ()
  for (slot, s) in forms.zipIdx do
    for (f, i) in slot.zipIdx do
      if f.colOf.isNone then
        let srcs := f.cols.filterMap (first[·]?)
        if srcs.length = f.cols.length then plan := plan.push (s, i, srcs)
  return plan

/-- The rows' rules, each with its justification, then collision resistance. `invs` are the `EMUL` rows and
equalities of `inv` calls. No rule reads a hash row `drop` names: the random-oracle view drops the squeeze rows, whose
outputs are the oracle's answers, seeds of the transcript at their times (`chalSeeds`). -/
def rowRules (s : State) (invs : Array (ℕ × ℕ)) (drop : List ℕ → Bool) : Analysis := Id.run do
  let mut r : Rules Just := {}
  let dropped := s.hash.map drop
  for t in [Table.emul, .exk, .cast, .split, .hash] do
    let plan := formPlan t
    let rows := rowsOf s t
    for k in [0:rows.size] do
      let row := rows[k]!
      if liveRow drop t row then
        for (sl, i, srcs) in plan do
          r := r.push (.form t k sl i srcs) (srcs.map (colNode row)).toArray #[limb (row.getD sl 0) i]
  -- Constants by wire: their public row and value.
  let mut consts : Std.HashMap ℕ (ℕ × Limbs) := {}
  for p in [0:s.pub.size] do
    match s.pub[p]! with
    | (w, .const v) =>
      consts := consts.insert w (p, v)
      for i in [0:4] do
        r := r.push (.pubConst p i) #[] #[limb w i]
    | _ => pure ()
  -- The word column is the sum of its bit columns' monomials, each bit 0 or 1: either side gives the other.
  for k in [0:s.split.size] do
    let row := s.split[k]!
    let bits := (splitBitNodes row).toArray
    r := (r.push (.splitWord k) bits #[limb (row.getD 0 0) 0]).push (.splitBits k) #[limb (row.getD 0 0) 0] bits
  -- Output blocks by chaining value and block counter, for the windows of the output stream.
  let mut outputs : Std.HashMap (ℕ × ℕ) ℕ := {}
  for k in [0:s.hash.size] do
    let row := s.hash[k]!
    if dropped[k]! then continue
    -- At a constant bit the mux is one half of the message.
    match consts[row.getD 3 0]? with
    | some (p, v) =>
      if v == [0, 0, 0, 0] || v == [1, 0, 0, 0] then
        let base := if v == [0, 0, 0, 0] then 6 else 10
        for i in [0:4] do
          r := r.push (.mux k i p) #[limb (row.getD 2 0) i] #[colNode row (hashSrc (base + i))]
    | none => pure ()
    -- At a constant final word the output is the compression of the inputs.
    match consts[row.getD 1 0]? with
    | some (p, v) =>
      if finalOk (v.getD 1 0) then r := r.push (.compress k p) (hashIn row).toArray (hashOut row).toArray
      match v, consts[row.getD 8 0]? with
      | t :: _, some (_, n :: _) => if role t = 6 then outputs := outputs.insert (row.getD 0 0, n) k
      | _, _ => pure ()
    | none => pure ()
  let nFunction := r.size
  for k in [0:s.hash.size] do
    if !dropped[k]! then
      r := r.push (.collision k) (hashOut s.hash[k]!).toArray (hashIn s.hash[k]!).toArray
  -- Four consecutive words of the output stream that straddle two blocks bind the chaining value, with the blocks'
  -- other input words (their counter, finalization and message, constants).
  for ((h, n), ka) in outputs.toList do
    match outputs[(h, n + 1)]? with
    | some kb =>
      for j in [1:4] do
        r := r.push (.window ka kb j)
          (windowIn s.hash[ka]! s.hash[kb]! j ++ hashRest s.hash[ka]! ++ hashRest s.hash[kb]!).toArray
          (hashH s.hash[ka]!).toArray
    | none => pure ()
  -- `inv`: the inverse and its argument determine each other.
  for (k, u) in invs do
    let row := s.emul[k]!
    match consts[row.getD 2 0]?, consts[(s.unions[u]!).2]? with
    | some (pz, _), some (po, _) =>
      let (a, x) := (row.getD 0 0, row.getD 1 0)
      r := (r.push (.inv k u pz po true) (limbs3 a).toArray (limbs3 x).toArray).push (.inv k u pz po false)
        (limbs3 x).toArray (limbs3 a).toArray
    | _, _ => pure ()
  return { nodes := 4 * s.next, rules := r, nFunction }

/-- Each node's rules as a premise, among the first `n` rules. -/
def premiseIndex (r : Rules Just) (nodes n : ℕ) : Array (Array ℕ) := Id.run do
  let mut idx : Array (Array ℕ) := Array.replicate nodes #[]
  for i in [0:n] do
    for j in [r.premOff[i]!:r.premOff[i + 1]!] do
      let p := r.prems[j]!
      idx := idx.modify p (·.push i)
  return idx

/-- The worklist's state: each node's binding time, each rule's unbound premises, and the rules fired in order. -/
structure BindState where
  bound : Array (Option ℕ)
  left : Array ℕ
  firings : Array ℕ

/-- Fire every rule the nodes on the stack complete, at time `t`. -/
def propagate (r : Rules Just) (idx : Array (Array ℕ)) (t : ℕ) (st : BindState) (stack : Array ℕ) : BindState :=
  Id.run do
    let { bound, left, firings } := st
    let mut bound := bound
    let mut left := left
    let mut firings := firings
    let mut stack := stack
    while !stack.isEmpty do
      let v := stack.back!
      stack := stack.pop
      for ri in idx[v]! do
        let k := left[ri]! - 1
        left := left.set! ri k
        if k = 0 then
          firings := firings.push ri
          for j in [r.conclOff[ri]!:r.conclOff[ri + 1]!] do
            let c := r.concls[j]!
            if bound[c]!.isNone then
              bound := bound.set! c (some t)
              stack := stack.push c
    return { bound, left, firings }

/-- Each node's binding time in one transcript, by squeeze call (`0` for constants), and the firings that bind
them: the rules without premises, then the seeds in time order, each firing every rule whose premises it
completes. -/
def bind (r : Rules Just) (nodes : ℕ) (idx : Array (Array ℕ)) (seeds : Array (ℕ × ℕ)) :
    Array (Option ℕ) × Array ℕ := Id.run do
  let mut st : BindState := {
    bound := Array.replicate nodes none
    left := (Array.range r.size).map fun i => r.premOff[i + 1]! - r.premOff[i]!
    firings := #[] }
  for ri in [0:r.size] do
    if st.left[ri]! = 0 then
      let mut stack := #[]
      let mut bound := st.bound
      for j in [r.conclOff[ri]!:r.conclOff[ri + 1]!] do
        let c := r.concls[j]!
        if bound[c]!.isNone then
          bound := bound.set! c (some 0)
          stack := stack.push c
      st := propagate r idx 0 { st with bound, firings := st.firings.push ri } stack
  for (t, w) in seeds do
    if st.bound[w]!.isNone then
      st := propagate r idx t { st with bound := st.bound.set! w (some t) } #[w]
  return (st.bound, st.firings)

/-- A test that failed, and the hinted wires behind it that no transcript binds. -/
structure Failure where
  call : ℕ
  pair : ℕ × ℕ
  /-- The calls that made the unbound hinted wires. -/
  hints : List ℕ
  /-- Each transcript's binding times of the pair. -/
  perTranscript : List (Option ℕ × Option ℕ) := []
  deriving Repr

structure Report where
  /-- The verdict, `Cert.accepts` of the certificate the worklist records. -/
  accepted : Bool
  transcripts : ℕ
  squeezes : ℕ
  /-- Union products whose rows the certificate reads. -/
  products : ℕ
  tests : ℕ
  /-- Tests no transcript binds. -/
  unbound : Array Failure
  /-- Tests bound only after the latest challenge they read. -/
  late : Array Failure
  /-- Tests bound only with the statement's words: claims the next verifier checks. -/
  deferred : Array Failure := #[]
  /-- Statement words that read a challenge, and those no transcript binds. -/
  exposed : ℕ
  exposedUnbound : Array ℕ
  /-- Each probed node's binding time per transcript. -/
  probes : List (ℕ × List (Option ℕ)) := []
  /-- The tests the certificate names as sumchecks' last checks, and their rounds; those of a residual. -/
  sumchecks : ℕ := 0
  rounds : ℕ := 0
  residuals : ℕ := 0
  /-- The hints the certified sumchecks' input claims read. -/
  hints : List ℕ := []
  /-- The table sumchecks the certificate names (`TableCert`), one per residual, and whether each passes its check. -/
  tables : ℕ := 0
  tablesOk : Bool := true
  /-- The table sumchecks whose bus GKR the certificate names from root to totals (`GkrCert`), their layers past the
  first, and whether each passes its check. -/
  gkrs : ℕ := 0
  gkrLayers : ℕ := 0
  gkrsOk : Bool := true
  /-- The table sumchecks whose residual the certificate names term by term (`ResidCert`), and whether each passes its
  check. -/
  resids : ℕ := 0
  residsOk : Bool := true
  /-- Each table sumcheck with its bus GKR and residual named, and the certificate's parts their checks read. -/
  named : List (TableCert × GkrCert × ResidCert) := []
  outs : Array (List ℕ) := #[]
  relax : Array Bool := #[]
  scs : Array SumcheckCert := #[]
  topCerts : Array TopCert := #[]
  oddCerts : Array OddCert := #[]
  /-- The certificate's transcripts. -/
  ts : List Transcript := []
  /-- The proof-of-work checks the certificate names, and their tests. -/
  pows : ℕ := 0
  powTests : ℕ := 0
  /-- The GKR odd layers and radix-four top layers the certificate names. -/
  odds : ℕ := 0
  tops : ℕ := 0
  /-- The WHIR sumchecks the certificate names, and their rounds. -/
  whirs : ℕ := 0
  whirRounds : ℕ := 0
  /-- Their batch rounds, and the WHIR sumchecks not certified from the opening's first claim (whose first round does
  not fold a quadratic received against it). -/
  whirBatches : ℕ := 0
  whirPartial : ℕ := 0
  /-- The claim splits the certificate names. -/
  splits : ℕ := 0
  /-- Whether every certified check's challenges are drawn in order from the oracle's words (`Cert.chalsOk`). -/
  chalsOk : Bool := true
  /-- The calls of the `eq_e` tests that close nothing certified and no union. -/
  others : Array ℕ := #[]

/-- The hinted wires behind an unbound node: back through the function rules concluding it, the unbound limbs of
wires that `isHint` marks (made by `free_*`), else the first unbound limbs visited. -/
def hintsOf (an : Analysis) (byConcl : Array (Array ℕ)) (bound : Array Bool) (isHint : ℕ → Bool)
    (start : List ℕ) (limit : ℕ) : List ℕ := Id.run do
  let r := an.rules
  let mut seen : Std.HashSet ℕ := {}
  let mut stack := start.toArray
  let mut hints := #[]
  let mut visited := #[]
  while !stack.isEmpty && hints.size < limit do
    let v := stack.back!
    stack := stack.pop
    if seen.contains v || bound[v]! then continue
    seen := seen.insert v
    if isHint v then hints := hints.push v
    if visited.size < limit then visited := visited.push v
    for ri in byConcl[v]! do
      for j in [r.premOff[ri]!:r.premOff[ri + 1]!] do
        stack := stack.push r.prems[j]!
  return (if hints.isEmpty then visited else hints).toList

/-- A wire's binding time: its last limb's, none if a limb is unbound. -/
def wireTime (bd : Array (Option ℕ)) (w : ℕ) : Option ℕ :=
  (limbs4 w).foldl (fun acc n => match acc, bd[n]! with
    | some t, some u => some (max t u)
    | _, _ => none) (some 0)

/-- The latest squeeze each wire depends on, by call, none for a wire no challenge reaches. A wire depends on what
the call that made it reads, and a squeeze's on that squeeze: dependence follows how wires are made, not every
relation a row states (a Merkle row's mux slot is an earlier wire, which the row does not make). Constants depend on
nothing, though a method makes one the first time it needs it. -/
def latestByCalls (rp : Replay) : Array (Option ℕ) := Id.run do
  let mut isConst : Array Bool := Array.replicate rp.state.next false
  for (w, src) in rp.state.pub do
    match src with
    | .const _ => isConst := isConst.set! w true
    | .statement _ => pure ()
  let mut gamma : Array (Option ℕ) := Array.replicate rp.state.next none
  let mut w := 0
  for i in [0:rp.calls.size] do
    let c := rp.calls.getD i .zero
    let squeeze : Bool := match c with
      | .leafBlock _ _ t _ => role t == 6
      | _ => false
    let g := if squeeze then some i else c.args.foldl (fun acc a => match acc, gamma[a]! with
      | some x, some y => some (max x y)
      | none, y => y
      | x, none => x) none
    while w < rp.state.next && rp.maker[w]! = i do
      if !isConst[w]! then gamma := gamma.set! w g
      w := w + 1
  return gamma

/-! The sumchecks behind the late tests, found by their calls. -/

/-- Each wire's making calls, with the output's place. -/
def outIndex (rp : Replay) : Std.HashMap ℕ (Array (ℕ × ℕ)) := Id.run do
  let mut idx : Std.HashMap ℕ (Array (ℕ × ℕ)) := {}
  for j in [0:rp.outs.size] do
    let os := rp.outs[j]!
    for p in [0:os.length] do
      idx := idx.insert (os.getD p 0) ((idx.getD (os.getD p 0) #[]).push (j, p))
  return idx

/-- A call making `w` as its first output that `f` takes. -/
def makerBy {α : Type} (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) (f : ℕ → Call → Option α) :
    Option α :=
  (idx.getD w #[]).findSome? fun (j, p) => if p = 0 then f j (rp.calls.getD j .zero) else none

/-- A `zero` call making `w`. -/
def zeroAt (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) : Option ℕ :=
  makerBy rp idx w fun j c => match c with
    | .zero => some j
    | _ => none

/-- Horner's calls ending at `w`: its point, the coefficients constant first, the `zero` call, the `mul_add` calls in
order. -/
def hornerOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) :
    Option (ℕ × List ℕ × ℕ × List ℕ) := Id.run do
  let some (x, c, acc, j) := makerBy rp idx w (fun j c => match c with
    | .mulAdd acc x c => some (x, c, acc, j)
    | _ => none)
    | return none
  let mut coeffs := [c]
  let mut calls := [j]
  let mut cur := acc
  for _ in [0:64] do
    if let some z := zeroAt rp idx cur then
      return some (x, coeffs, z, calls)
    match makerBy rp idx cur (fun j c => match c with
      | .mulAdd acc x' c => if x' = x then some (c, acc, j) else none
      | _ => none) with
    | some (c, acc, j) => coeffs := coeffs ++ [c]; calls := j :: calls; cur := acc
    | none => return none
  return none

/-- The `add` fold over `ws` ending at `w`: its `zero` call and its calls in order. -/
def foldOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) (ws : List ℕ) : Option (ℕ × List ℕ) := Id.run do
  let mut cur := w
  let mut calls := []
  for c in ws.reverse do
    match makerBy rp idx cur (fun j call => match call with
      | .add acc c' => if c' = c then some (acc, j) else none
      | _ => none) with
    | some (acc, j) => calls := j :: calls; cur := acc
    | none => return none
  return (zeroAt rp idx cur).map (·, calls)

/-- The challenge `x`: three squeezed words. -/
def chalOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (x : ℕ) : Option ChalCert := do
  let (chalAt, w0, w1, w2) ← makerBy rp idx x (fun j c => match c with
    | .kToE a b d => some (j, a, b, d)
    | _ => none)
  let words ← [w0, w1, w2].mapM fun wk => (idx.getD wk #[]).findSome? fun (dk, p) =>
    match rp.calls.getD dk .zero with
    | .dToK d => makerBy rp idx d (fun lb c => match c with
      | .leafBlock _ _ t _ => if t / 2 ^ 56 = 6 then some (dk, p, lb) else none
      | _ => none)
    | _ => none
  return { chal := x, chalAt, words, time := 0 }

/-- A challenge's time in a transcript: one more than the place of the block whose output its squeeze reads. -/
def chalTime (rp : Replay) (s : State) (t : Transcript) (cc : ChalCert) : Option ℕ := do
  let (_, _, lb) ← cc.words.head?
  let .leafBlock h _ _ _ := rp.calls.getD lb .zero | none
  let k ← t.blocks.findIdx? fun b => (s.hash.getD b []).getD 6 0 == h
  return k + 1

/-- The GKR odd layer a test closes: one side the values at `λ` by Horner, the other the products of children at `λ`,
then each value's line through its children at the next challenge, made after the test. -/
def oddOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (s : State) (ts : List Transcript)
    (u call a b : ℕ) : Option OddCert := Id.run do
  for (cw, ew) in [(a, b), (b, a)] do
    let some (lam, values, claimZero, claimAt) := hornerOf rp idx cw | continue
    let some (lam', prods, expZero, expAt) := hornerOf rp idx ew | continue
    if lam' ≠ lam ∨ prods.length ≠ values.length then continue
    let some kids := prods.mapM (fun p => makerBy rp idx p (fun j c => match c with
      | .mul l r => some (j, l, r)
      | _ => none)) | continue
    -- Each value's line: `add(l, r)`, then `mul_add(r', sum, l)`, after the test.
    let mut sums := #[]
    let mut outs := #[]
    let mut rr : Option ℕ := none
    for (_, l, r) in kids do
      let some j := (List.range 400).findSome? (fun d => match rp.calls.getD (call + d) .zero with
        | .add l' r' => if l' = l ∧ r' = r then some (call + d) else none
        | _ => none) | break
      let sw := o rp.outs j
      let some (j', x) := (List.range 400).findSome? (fun d => match rp.calls.getD (j + d) .zero with
        | .mulAdd x sw' l' => if sw' = sw ∧ l' = l then some (j + d, x) else none
        | _ => none) | break
      if rr.any (· ≠ x) then break
      rr := some x
      sums := sums.push j
      outs := outs.push j'
    let some x := rr | continue
    if outs.size ≠ kids.length then continue
    let some lamC := chalOf rp idx lam | continue
    let some nextC := chalOf rp idx x | continue
    let some k := (List.range ts.length).find? fun k => (chalTime rp s (ts.getD k default) nextC).isSome | continue
    let t := ts.getD k default
    let some lt := chalTime rp s t lamC | continue
    let some nt := chalTime rp s t nextC | continue
    let oc : OddCert := {
      values, lam := { lamC with time := lt }, claimZero, claimAt, lefts := kids.map (·.2.1),
      rights := kids.map (·.2.2), prodAt := kids.map (·.1), expZero, expAt, test := u, next := { nextC with time := nt },
      sumAt := sums.toList, outAt := outs.toList, transcript := k }
    return some oc
  return none

/-- The round whose next claim is `w`, with the claim it reads. -/
def roundOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) : Option (RoundCert × ℕ) := do
  let (x, coeffs, hornerZero, hornerAt) ← hornerOf rp idx w
  guard (2 ≤ coeffs.length)
  -- With an eq weight the constant coefficient is `claim + e · tail`, else the linear one is `claim + tail`.
  let weighted := makerBy rp idx (coeffs.getD 0 0) (fun j c => match c with
    | .mulAdd e t cl => (foldOf rp idx t (coeffs.drop 1)).map fun (z, ts) => (e, t, cl, j, z, ts)
    | _ => none)
  let (weight, claim, fixedAt, tailZero, tailAt) ← match weighted with
    | some (e, _, cl, j, z, ts) => some (some e, cl, j, z, ts)
    | none => makerBy rp idx (coeffs.getD 1 0) (fun j c => match c with
      | .add cl t => (foldOf rp idx t (coeffs.drop 2)).map fun (z, ts) => (none, cl, j, z, ts)
      | _ => none)
  let cc ← chalOf rp idx x
  let rc : RoundCert := { coeffs, weight, tailZero, tailAt, fixedAt, chal := x, hornerZero, hornerAt,
                          chalAt := cc.chalAt, words := cc.words, time := 0 }
  return (rc, claim)

/-- A round's time in a transcript: one more than the place of the block whose output its challenge's squeeze reads. -/
def roundTime (rp : Replay) (s : State) (t : Transcript) (rc : RoundCert) : Option ℕ := do
  let (_, _, lb) ← rc.words.head?
  let .leafBlock h _ _ _ := rp.calls.getD lb .zero | none
  let k ← t.blocks.findIdx? fun b => (s.hash.getD b []).getD 6 0 == h
  return k + 1

/-- The rounds whose last next claim is `last`, back to the first claim no round makes, and that claim. -/
def roundsBack (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (last : ℕ) : List RoundCert × ℕ := Id.run do
  let mut rounds : List RoundCert := []
  let mut cur := last
  for _ in [0:256] do
    match roundOf rp idx cur with
    | some (rc, cl) =>
      if rounds.all (·.coeffs.length == rc.coeffs.length) then rounds := rc :: rounds; cur := cl else break
    | none => break
  return (rounds, cur)

/-- The sumcheck a test closes, if one of its wires is a last claim, or a residual chain from one
(`mul_add(weight, summand, residual)`): its rounds back to the first claim no round makes, in the transcript drawing
the last round's challenge. -/
def sumcheckOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (s : State) (ts : List Transcript)
    (u a b : ℕ) : Option SumcheckCert := Id.run do
  for (side, final) in [(a, b), (b, a)] do
    let mut resid : List (ℕ × ℕ × ℕ) := []
    let mut last := side
    for _ in [0:64] do
      let (rounds, claim0) := roundsBack rp idx last
      if let some lastRound := rounds.getLast? then
        if let some k := (List.range ts.length).find? fun k => (roundTime rp s (ts.getD k default) lastRound).isSome then
          let t := ts.getD k default
          let timed := rounds.filterMap fun rc => (roundTime rp s t rc).map fun time => { rc with time }
          if timed.length = rounds.length then
            return some { claim0, rounds := timed, deg := lastRound.coeffs.length - 1, test := u, final,
                          transcript := k, resid }
      -- A residual is tested against `zero`.
      if (zeroAt rp idx final).isNone then break
      match makerBy rp idx last (fun j c => match c with
        | .mulAdd w x acc => some (w, x, acc, j)
        | _ => none) with
      | some (w, x, acc, j) => resid := (w, x, j) :: resid; last := acc
      | none => break
  return none

/-- The hints behind `w` that a transcript's marks `bd` do not bind by `time`: back through the calls making the
unbound wires, the outputs of `free_*` calls. -/
def hintsBehind (rp : Replay) (bd : Array (Option ℕ)) (time w : ℕ) : List ℕ := Id.run do
  let bound := fun v => (limbs3 v).all fun n => match bd.getD n none with
    | some k => decide (k ≤ time)
    | none => false
  let mut seen : Std.HashSet ℕ := {}
  let mut stack := #[w]
  let mut hints := #[]
  while !stack.isEmpty do
    let v := stack.back!
    stack := stack.pop
    if seen.contains v || bound v then continue
    seen := seen.insert v
    let c := rp.calls.getD (rp.maker.getD v 0) .zero
    match c with
    | .freeE | .freeK | .freeD => hints := hints.push v
    | _ => for a in c.args do stack := stack.push a
  return hints.toList

/-- A call among the 400 from `start` that `f` takes. -/
def findFrom {α : Type} (rp : Replay) (start : ℕ) (f : Call → Option α) : Option (ℕ × α) :=
  (List.range 400).findSome? fun d => (f (rp.calls.getD (start + d) .zero)).map (start + d, ·)

/-- The product of four children from a `one` making `w` (`Arith::product`): the `one` and `mul` calls, and the
children. -/
def prod4Of (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) : Option (List ℕ × List ℕ) := do
  let mulOf := fun v => makerBy rp idx v fun j c => match c with
    | .mul x y => some (j, x, y)
    | _ => none
  let (j4, p3, d) ← mulOf w
  let (j3, p2, c) ← mulOf p3
  let (j2, p1, b) ← mulOf p2
  let (j1, p0, a) ← mulOf p1
  let j0 ← makerBy rp idx p0 fun j c => match c with
    | .one => some j
    | _ => none
  return ([j0, j1, j2, j3, j4], [a, b, c, d])

/-- The GKR radix-four top layer a test closes: one side the values at `λ` by Horner, the other the products of four
children at `λ`, then each value's children's interpolation at the next two challenges, made after the test. -/
def topOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (s : State) (ts : List Transcript)
    (u call a b : ℕ) : Option TopCert := Id.run do
  for (cw, ew) in [(a, b), (b, a)] do
    let some (lam, values, claimZero, claimAt) := hornerOf rp idx cw | continue
    let some (lam', prods, expZero, expAt) := hornerOf rp idx ew | continue
    if lam' ≠ lam ∨ prods.length ≠ values.length then continue
    let some ps := prods.mapM (prod4Of rp idx) | continue
    let mut lines : Array (List ℕ) := #[]
    let mut chals : Option (ℕ × ℕ) := none
    let addOf := fun (st x y : ℕ) => findFrom rp st fun c => match c with
      | .add x' y' => if x' = x ∧ y' = y then some () else none
      | _ => none
    let lineOf := fun (st d x : ℕ) => findFrom rp st fun c => match c with
      | .mulAdd t d' x' => if d' = d ∧ x' = x then some t else none
      | _ => none
    for (_, ks) in ps do
      let k := fun i => ks.getD i 0
      let some (l0, _) := addOf call (k 0) (k 1) | break
      let some (l1, lo) := lineOf l0 (o rp.outs l0) (k 0) | break
      let some (l2, _) := addOf l1 (k 2) (k 3) | break
      let some (l3, lo') := lineOf l2 (o rp.outs l2) (k 2) | break
      let some (l4, _) := addOf l3 (o rp.outs l1) (o rp.outs l3) | break
      let some (l5, hi) := lineOf l4 (o rp.outs l4) (o rp.outs l1) | break
      if lo' ≠ lo ∨ chals.any (· ≠ (lo, hi)) then break
      chals := some (lo, hi)
      lines := lines.push [l0, l1, l2, l3, l4, l5]
    let some (lo, hi) := chals | continue
    if lines.size ≠ ps.length then continue
    let some lamC := chalOf rp idx lam | continue
    let some loC := chalOf rp idx lo | continue
    let some hiC := chalOf rp idx hi | continue
    let some k := (List.range ts.length).find? fun k => (chalTime rp s (ts.getD k default) hiC).isSome | continue
    let t := ts.getD k default
    let some lt := chalTime rp s t lamC | continue
    let some ot := chalTime rp s t loC | continue
    let some ht := chalTime rp s t hiC | continue
    return some { values, lam := { lamC with time := lt }, claimZero, claimAt, kids := ps.map (·.2),
                  prodAt := ps.map (·.1), expZero, expAt, test := u, low := { loC with time := ot },
                  high := { hiC with time := ht }, lineAt := lines.toList, transcript := k }
  return none

/-- A WHIR quadratic with coefficients `c`, `b`, `a`: received (`b = claim + (0 + a)`), else folded, each coefficient
`mul_add(s, intro's, base's)`, its claim the running claim's `mul_add` among the next calls. -/
def quadOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) : ℕ → ℕ → ℕ → ℕ → Option QuadCert
  | 0, _, _, _ => none
  | fuel + 1, c, b, a =>
    let recv := makerBy rp idx b fun j call => match call with
      | .add cl t => (foldOf rp idx t [a]).bind fun (z, ts) => match ts with
        | [tAt] => some (QuadCert.recv cl c a z tAt j)
        | _ => none
      | _ => none
    match recv with
    | some q => some q
    | none => do
      let mulAddOf := fun v => makerBy rp idx v fun j call => match call with
        | .mulAdd s x y => some (j, s, x, y)
        | _ => none
      let (cAt, s, ci, cb) ← mulAddOf c
      let (bAt, s', bi, bb) ← mulAddOf b
      let (aAt, s'', ai, ab) ← mulAddOf a
      guard (s' = s ∧ s'' = s)
      let base ← quadOf rp idx fuel cb bb ab
      let intro ← quadOf rp idx fuel ci bi ai
      let (clAt, _) ← findFrom rp (aAt + 1) fun call => match call with
        | .mulAdd s₁ y t =>
          if s₁ = s ∧ y = intro.claim rp.outs ∧ t = base.claim rp.outs then some () else none
        | _ => none
      return .fold base intro s cAt bAt aAt clAt

/-- A folded quadratic's first fold: its power of `λ` and the claim of the quadratic it folds into. -/
def QuadCert.inner : QuadCert → ℕ × ℕ
  | .recv cl .. => (0, cl)
  | .fold q _ s .. => match q with
    | .recv cl .. => (s, cl)
    | _ => q.inner

/-- `RoundQuad::eval` making `w`: `mul_add(mul_add(a, x, b), x, c)`, its calls, `x` and the coefficients. -/
def quadEvalOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w : ℕ) :
    Option (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := do
  let (tAt, u, x, c) ← makerBy rp idx w fun j call => match call with
    | .mulAdd u x c => some (j, u, x, c)
    | _ => none
  let (uAt, a, b) ← makerBy rp idx u fun j call => match call with
    | .mulAdd a x' b => if x' = x then some (j, a, b) else none
    | _ => none
  return (tAt, uAt, x, c, b, a)

/-- `w` as an expression in `x`: the claim `claim` and the wires `bound` takes are atoms, `x` the variable, and any
other wire a call's output through its arguments. -/
def pexprOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (bound : ℕ → Bool) (x claim : ℕ) :
    ℕ → ℕ → Option PExpr
  | 0, _ => none
  | fuel + 1, w =>
    if w = claim then some (.atom w)
    else if w = x then some .var
    else if bound w then some (.atom w)
    else
      let go := pexprOf rp idx bound x claim fuel
      (idx.getD w #[]).findSome? fun (j, p) => if p ≠ 0 then none else
        match rp.calls.getD j .zero with
        | .add a d => do return .add j (← go a) (← go d)
        | .mul a b => do return .mul j (← go a) (← go b)
        | .mulAdd a b d => do return .mulAdd j (← go a) (← go b) (← go d)
        | .square a => do return .square j (← go a)
        | .mulConstAdd a c0 c1 c2 d => do return .mulConstAdd j c0 c1 c2 (← go a) (← go d)
        | _ => none

/-- The WHIR sumcheck a test closes: one side a `RoundQuad::eval`, back through fold rounds and the batch rounds before
folded quadratics to the first quadratic's claim, in the transcript drawing the last round's challenge. A batch
round's expression treats as atoms the wires the transcript's random-oracle view binds by `λ`'s time with the words
squeezed with `λ` but its own (its query positions) as seeds: the transcript's seeds up to `λ`'s last squeeze but
`λ`'s words, bound again (`seedsAt`, by the premise index `idxAt`) for the firings the verdict replays. -/
def whirOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (s : State) (cert : Cert) (os : Array (List ℕ))
    (ms : List (Transcript × Array (Option ℕ))) (seedsAt : ℕ → Array (ℕ × ℕ)) (idxAt : ℕ → Array (Array ℕ))
    (u a b : ℕ) : Option WhirCert := Id.run do
  for (side, final) in [(a, b), (b, a)] do
    let some (_, _, x0, _, _, _) := quadEvalOf rp idx side | continue
    let some c0 := chalOf rp idx x0 | continue
    let some k := (List.range ms.length).find? fun k => (chalTime rp s (ms.getD k default).1 c0).isSome | continue
    let (t, _) := ms.getD k default
    let timed := fun (cc : ChalCert) => (chalTime rp s t cc).map fun time => { cc with time }
    let mut rounds : List WhirRound := []
    let mut cur := side
    for _ in [0:4096] do
      let some (tAt, uAt, x, c, b, a) := quadEvalOf rp idx cur | break
      let some q := quadOf rp idx 64 c b a | break
      let some cc := (chalOf rp idx x).bind timed | break
      rounds := .fold q cc uAt tAt :: rounds
      cur := q.claim rp.outs
      if let .fold .. := q then
        let (s1, claim) := q.inner
        -- `λ` is the first power, or the factor of `mul(one, λ)` making it.
        let lam := if (chalOf rp idx s1).isSome then s1 else
          (makerBy rp idx s1 fun _ call => match call with
            | .mul _ y => some y
            | _ => none).getD s1
        let some lc := (chalOf rp idx lam).bind timed | break
        let own := lc.own os
        let lamCall := (lc.words.map (·.2.2)).foldl max 0
        let (_, fs) := bind t.rulesRO cert.nodes (idxAt k)
          ((seedsAt k).filter fun (tm, n) => tm ≤ lamCall && !own.contains n)
        let bx := cert.timesX s t ((sibSeeds s t lc.time own).map (lc.time, ·)) fs
        let bound := fun w => (limbs3 w).all fun n => match bx.getD n none with
          | some j => decide (j ≤ lc.time)
          | none => false
        let some e := pexprOf rp idx bound lam claim 100000 cur | break
        rounds := .batch lc e own fs :: rounds
        cur := claim
    if !rounds.isEmpty then
      return some { claim0 := cur, rounds, test := u, final, transcript := k }
  return none

/-- The table sumcheck's residual certificate (`ResidCert`), its terms read back from the residual's
`mul_add(weight, summand, residual)`s: each weight through its rounds to a `one`, each summand through its table's
identities and its forms' `mul_add(ξ, pull, push)` to its push and pull forms, each form forward from its constant (the
first of its calls after the rounds) over the table's columns and then its products. -/
def residOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (os : Array (List ℕ)) (scIdx : ℕ)
    (sc : SumcheckCert) (xi : ℕ) : Option ResidCert := Id.run do
  let n := sc.rounds.length
  let r := sc.rounds.map (·.chal)
  let callAt := fun (j : ℕ) => rp.calls.getD j .zero
  let out := fun (j : ℕ) => o os j
  -- The calls whose first output is `w`.
  let makers := fun (w : ℕ) => ((idx.getD w #[]).filterMap fun (j, p) => if p == 0 then some j else none).toList
  let some lastChal := r.getLast? | return none
  let start := rp.maker.getD lastChal 0
  -- Weights, back through the rounds.
  let mut sAt : Array ℕ := Array.replicate n 0
  let mut zeta : Array ℕ := Array.replicate n 0
  let mut wts : List (ℕ × ℕ × List ℕ) := []
  for (w, _, _) in sc.resid do
    let mut cur := w
    let mut wAt : List ℕ := []
    let mut tau := 0
    for jj in (List.range n).reverse do
      let rj := r.getD jj 0
      let found := (makers cur).findSome? fun j => match callAt j with
        | .mulAdd a b d => if a != d then none else match callAt (rp.maker.getD b 0) with
          | .add z x => if x == rj then some (j, a, some (rp.maker.getD b 0, z)) else none
          | _ => none
        | .mul a b => if b == rj then some (j, a, none) else none
        | _ => none
      let some (j, a, act) := found | return none
      wAt := j :: wAt
      cur := a
      if let some (sj, z) := act then
        tau := tau + 1
        sAt := sAt.set! jj sj
        zeta := zeta.set! (n - 1 - jj) z
    let some oneAt := (makers cur).find? fun j => callAt j == .one | return none
    wts := wts ++ [(tau, oneAt, wAt)]
  -- The powers of `ξ`: a `one`, then `mul(p, ξ)`.
  let mut byMul : Std.HashMap ℕ ℕ := {}
  for j in [rp.maker.getD xi 0:rp.calls.size] do
    if let .mul a b := callAt j then
      if b == xi && !byMul.contains a then byMul := byMul.insert a j
  let some (_, one0, _) := wts.head? | return none
  let mut pows : Array ℕ := #[one0]
  for _ in [0:AirLink.allIds.length + 1] do
    let some j := byMul.get? (out pows.back!) | return none
    pows := pows.push j
  -- A form forward from its constant `c` over `nc` columns from call `from`: its terms, its columns, its output and
  -- the call after its last.
  let formFrom := fun (c nc pos0 : ℕ) => Id.run do
    let mut cur := c
    let mut pos := pos0
    let mut lin : List (ℕ × ℕ × ℕ) := []
    let mut cols : List ℕ := []
    for i in [0:nc] do
      let some j := ((List.range (rp.calls.size - pos)).findSome? fun d => match callAt (pos + d) with
        | .mulAdd _ _ acc => if acc == cur then some (pos + d) else none
        | _ => none) | return none
      let .mulAdd a v _ := callAt j | return none
      lin := lin ++ [(i, a, j)]
      cols := cols ++ [v]
      cur := out j
      pos := j + 1
    let mut prods : List (ℕ × ℕ × ℕ × ℕ × ℕ) := []
    for _ in [0:4096] do
      let some j := ((List.range (rp.calls.size - pos)).find? fun d => match callAt (pos + d) with
        | .mulAdd .. => true
        | _ => false) | break
      let .mulAdd a p acc := callAt (pos + j) | break
      if acc != cur then break
      let m := rp.maker.getD p 0
      let .mul x y := callAt m | break
      if m < start then break
      let some ia := cols.idxOf? x | break
      let some ib := cols.idxOf? y | break
      prods := prods ++ [(ia, ib, a, m, pos + j)]
      cur := out (pos + j)
      pos := pos + j + 1
    return some (({ const := c, lin, prods } : FormCert), cols, cur, pos)
  -- The constant a form's wire `w` reaches back through its calls after the rounds.
  let constOf := fun (w : ℕ) => Id.run do
    let mut cur := w
    for _ in [0:4096] do
      let step := (makers cur).findSome? fun j => if j ≤ start then none else match callAt j with
        | .mulAdd _ _ acc => if acc != cur then some acc else none
        | _ => none
      match step with
      | some acc => cur := acc
      | none => break
    return cur
  let mut terms : List TermCert := []
  for k in [0:5] do
    let (_, s, _) := sc.resid.getD k default
    let T := ownedList.getD k .emul
    let (tau, oneAt, wAt) := wts.getD k default
    -- The identities, back from the summand.
    let mut cur := s
    let mut back : List (ℕ × ℕ × ℕ) := []
    for g in (idsOf T).reverse do
      let p := out (pows.getD (2 + g) 0)
      let some (j, v, acc) := ((makers cur).findSome? fun j => match callAt j with
        | .mulAdd a v acc => if a == p then some (j, v, acc) else none
        | _ => none) | return none
      back := (g, v, j) :: back
      cur := acc
    let formsOut := cur
    let some formsAt := ((makers formsOut).find? fun j => match callAt j with
      | .mulAdd a _ _ => a == xi
      | _ => false) | return none
    let .mulAdd _ pullW pushW := callAt formsAt | return none
    let some (push, cols, pushO, pos) := formFrom (constOf pushW) (nCols T) (start + 1) | return none
    let some (pull, cols', pullO, _) := formFrom (constOf pullW) (nCols T) pos | return none
    if cols != cols' || pushO != pushW || pullO != pullW then return none
    -- Each identity's calls, back from its value.
    let mut ids : List IdCert := []
    for (g, v, accAt) in back do
      let id := idAt g
      let mut here := v
      let mut prodCalls : List (ℕ × ℕ) := []
      for (a, b, w) in id.prods.reverse do
        let some (mj, j, acc) := ((makers here).findSome? fun j => match callAt j with
          | .mulConstAdd m w' 0 0 acc => if w' != w then none else
            ((makers m).find? fun mj => callAt mj == .mul (cols.getD a 0) (cols.getD b 0)).map (·, j, acc)
          | _ => none) | return none
        prodCalls := (mj, j) :: prodCalls
        here := acc
      let mut linCalls : List ℕ := []
      for (c, w) in id.linear.reverse do
        let some (j, acc) := ((makers here).findSome? fun j => match callAt j with
          | .mulConstAdd x w' 0 0 acc => if x == cols.getD c 0 && w' == w then some (j, acc) else none
          | _ => none) | return none
        linCalls := j :: linCalls
        here := acc
      let some st := (makers here).find? fun j => callAt j == .eConst 0 0 0 | return none
      ids := ids ++ [{ g, start := st, lin := linCalls, prods := prodCalls, accAt }]
    terms := terms ++ [{ tau, oneAt, wAt, cols, push, pull, formsAt, ids }]
  return some { sc := scIdx, xi, zeta := zeta.toList, sAt := sAt.toList, pows := pows.toList, terms }

/-- A claim split a test closes (`design::program_claims`): one side a chain of `mul_add(c, h^(2^e), acc)` from a
`zero`, the other the claim's value. -/
def splitOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (u a b : ℕ) : Option SplitCert := Id.run do
  for (tw, value) in [(a, b), (b, a)] do
    let mut terms : List (ℕ × ℕ × List ℕ × ℕ) := []
    let mut cur := tw
    for _ in [0:256] do
      if let some z := zeroAt rp idx cur then
        if !terms.isEmpty then return some { zeroAt := z, terms, test := u, value }
        break
      let some (j, c, p, acc) := makerBy rp idx cur (fun j call => match call with
        | .mulAdd c p acc => some (j, c, p, acc)
        | _ => none) | break
      let mut h := p
      let mut sq : List ℕ := []
      for _ in [0:64] do
        match makerBy rp idx h (fun jj call => match call with
          | .square y => some (jj, y)
          | _ => none) with
        | some (jj, y) => sq := jj :: sq; h := y
        | none => break
      terms := (c, h, sq, j) :: terms
      cur := acc
  return none

/-- The proof-of-work checks among the test calls: `eq_k_const` tests of bits of a `split` of a trial compression's
first word, by split. -/
def powsOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (testCalls : Array ℕ) : Array PowCert := Id.run do
  let mut bySplit : Std.HashMap ℕ (Array (ℕ × ℕ)) := {}
  for j in testCalls do
    if let .eqConstK a 0 := rp.calls.getD j .zero then
      for (sp, k) in idx.getD a #[] do
        if let .split _ := rp.calls.getD sp .zero then
          bySplit := bySplit.insert sp ((bySplit.getD sp #[]).push (k, j))
  let mut out := #[]
  for (sp, ts) in bySplit.toList do
    let .split w := rp.calls.getD sp .zero | continue
    let some dk := (idx.getD w #[]).findSome? (fun (j, p) => match rp.calls.getD j .zero with
      | .dToK _ => if p = 0 then some j else none
      | _ => none) | continue
    let .dToK d := rp.calls.getD dk .zero | continue
    let some cp := makerBy rp idx d (fun j c => match c with
      | .compress .. => some j
      | _ => none) | continue
    let sorted := ts.qsort (·.1 < ·.1)
    out := out.push { compressAt := cp, dkAt := dk, splitAt := sp, bits := sorted.size,
                      testAt := (sorted.map (·.2)).toList }
  return out

def analyse (rp : Replay) (probe : List ℕ := []) : Report := Id.run do
  let s := rp.state
  let an0 := rowRules s rp.invs fun _ => false
  let bs := blocks rp
  let squeezes := bs.filter (·.squeeze)
  let gamma := latestByCalls rp
  let tainted := fun w => (gamma[w]!).isSome
  let latestOf := fun w => (gamma[w]!).getD 0
  -- Equalities that bind: digests, methods', and field equalities reading no challenge.
  let mut rules := an0.rules
  -- The rules besides the rows', which each transcript's random-oracle view keeps too.
  let mut extra : Array (Just × Array ℕ × Array ℕ) := #[]
  let mut tests : Array (ℕ × ℕ × ℕ) := #[]
  let mut isTest : Array Bool := Array.replicate s.unions.size false
  for u in [0:s.unions.size] do
    let (a, b) := s.unions[u]!
    if rp.eqKind[u]! = .field ∧ (tainted a ∨ tainted b) then
      tests := tests.push (u, a, b)
      isTest := isTest.set! u true
    else
      for j in [0:4] do
        extra := (extra.push (.eq u j true, #[limb a j], #[limb b j])).push (.eq u j false, #[limb b j], #[limb a j])
  -- A union product: bound once its pool's digests, begin bits, selection bits and the point are. A pool's `pack`
  -- calls are the run of them after its end mark.
  let pools := rp.pools.map fun pc => Id.run do
    let mut packs := #[]
    let mut j := pc.packs.headD 0
    while j < rp.calls.size && (match rp.calls.getD j .zero with | .pack _ => true | _ => false) do
      packs := packs.push j
      j := j + 1
    return { pc with packs := packs.toList }
  let mut claims : Array UnionClaim := #[]
  for qc in rp.prods do
    let uc := qc.claim rp.outs (pools.getD qc.pool default)
    extra := extra.push (.union claims.size, (uc.inputs.flatMap limbs4).toArray, (limbs3 uc.out).toArray)
    claims := claims.push uc
  -- The calls whose equality is a test, relaxed when the certificate replays the unions' rows.
  let mut relax : Array Bool := Array.replicate rp.calls.size false
  for (u, _, _) in tests do
    relax := relax.set! (rp.eqCall[u]!) true
  for (j, ps, cs) in extra do
    rules := rules.push j ps cs
  let an := { an0 with rules }
  let idx := premiseIndex rules an.nodes rules.size
  let ts := transcripts bs
  -- Each absorb block's `HASH` row, by its output wire.
  let mut rowOfOut : Std.HashMap ℕ ℕ := {}
  for k in [0:s.hash.size] do
    rowOfOut := rowOfOut.insert ((s.hash[k]!).getD 6 0) k
  let stmt := statementNodes s
  let mut binds : Array (Array (Option ℕ)) := #[]
  let mut certs : Array Transcript := #[]
  -- Each transcript's seeds and its random-oracle rules' premise index, which WHIR's batch rounds bind again with.
  let mut seedsOfT : Array (Array (ℕ × ℕ)) := #[]
  let mut idxRO : Array (Array (Array ℕ)) := #[]
  for path in ts do
    -- Absorbed words are bound at the next squeeze on the path; the blocks absorbed before a squeeze seed it. A
    -- squeeze reading an absorb block's output is a challenge, the oracle's answer: a seed at its own squeeze.
    let mut words : Array (ℕ × ℕ) := #[]
    let mut blocksRev : Array ℕ := #[]
    let mut squeezes : Array ℕ := #[]
    let mut nextSq : Option ℕ := none
    let absorbOuts : Std.HashSet ℕ := path.foldl (fun acc b => if b.squeeze then acc else acc.insert b.cvOut) {}
    for b in path.reverse do
      if b.squeeze then
        nextSq := some (match nextSq with | some t => min t b.call | none => b.call)
        if absorbOuts.contains b.cvIn then
          let k := rowOfOut.getD b.cvOut 0
          if isSqueezeRow s (s.hash.getD k []) then
            squeezes := squeezes.push k
            for n in hashOut (s.hash.getD k []) do words := words.push (b.call, n)
      else match nextSq with
        | some t =>
          for w in b.words do words := words.push (t, limb w 0)
          blocksRev := blocksRev.push (rowOfOut.getD b.cvOut 0)
        | none => pure ()
    -- The statement's words are claims the verifier of this circuit's proof checks: bound last, at the end.
    let seeds := (words.qsort (·.1 < ·.1)) ++ (stmt.map (rp.calls.size, ·)).toArray
    let (bd, firings) := bind rules an.nodes idx seeds
    -- The transcript's random-oracle view: no rule reads a row writing its own blocks' or squeezes' outputs
    -- (`dropOf`).
    let own : Std.HashSet ℕ := (blocksRev ++ squeezes).foldl (fun acc k => acc.insert ((s.hash.getD k []).getD 6 0)) {}
    let rulesRO := extra.foldl (fun r (j, ps, cs) => r.push j ps cs)
      (rowRules s rp.invs fun row => own.contains (row.getD 6 0)).rules
    let idxR := premiseIndex rulesRO an.nodes rulesRO.size
    let (_, firingsRO) := bind rulesRO an.nodes idxR seeds
    binds := binds.push bd
    seedsOfT := seedsOfT.push seeds
    idxRO := idxRO.push idxR
    certs := certs.push { blocks := blocksRev.reverse.toList, firings, squeezes := squeezes.reverse.toList, firingsRO,
                          rulesRO }
  -- Each product's point: `X + 1` is made by the call after the point's first.
  let points := rp.prods.map fun qc =>
    let start := rp.maker.getD qc.x1 0 - 1
    let pt : PointCert := { start, x := 0, a := [] }
    let x := match rp.calls.getD (start + 1) .zero with | .add x _ => x | _ => 0
    let a := (List.range 4).map fun j => match rp.calls.getD (pt.round j) .zero with | .add aj _ => aj | _ => 0
    { pt with x, a }
  -- Each union's coverage test: the test of its two products' outputs, and a transcript binding what both pools
  -- commit to.
  let outOf := fun (i : ℕ) => let qc := rp.prods.getD i default; ProdCert.out rp.outs (pools.getD qc.pool default) qc
  let committedOf := fun (i : ℕ) => (pools.getD (rp.prods.getD i default).pool default).committed rp.outs
  let prodIdx := List.range rp.prods.size
  let covers := tests.filterMap fun (u, a, b) =>
    match prodIdx.find? (outOf · == a), prodIdx.find? (outOf · == b) with
    | some i, some j =>
      let ls := (committedOf i ++ committedOf j).flatMap limbs4
      let k := (List.range binds.size).find? (fun k => ls.all fun n => ((binds.getD k #[])[n]?.join).isSome)
      some { test := u, sel := i, decl := j, transcript := k.getD 0 }
    | _, _ => none
  let cert : Cert := {
    rules, nodes := an.nodes, isTest, claims, transcripts := certs.toList, calls := rp.calls, relax, pools
    prods := rp.prods, points, covers }
  -- The tests closing a sumcheck whose rounds the verdict certifies.
  let idxO := outIndex rp
  let ms := cert.marksRO s
  let os := cert.outs
  -- A sumcheck closed by a residual (the table sumcheck) has an input claim reading hinted fixed-column evaluations:
  -- the certificate names them and binds the claim with them as seeds.
  let withHints := fun (sc : SumcheckCert) =>
    if sc.resid.isEmpty then sc else
      let t := ms.getD sc.transcript default
      let hints := hintsBehind rp t.2 (sc.rounds.getD 0 default).time sc.claim0
      let (_, hintFirings) := bind t.1.rulesRO cert.nodes (idxRO.getD sc.transcript #[])
        ((hints.flatMap limbs3).toArray.map (0, ·) ++ seedsOfT.getD sc.transcript #[])
      { sc with hints, hintFirings }
  let sumchecks := (tests.filterMap fun (u, a, b) => (sumcheckOf rp idxO s certs.toList u a b).map withHints).filter
    fun sc => ({ cert with sumchecks := #[sc] }).sumchecksOk s os ms
  let pows := (powsOf rp idxO (tests.map fun (u, _, _) => rp.eqCall[u]!)).filter (·.ok os cert.calls cert.relax)
  let odds := (tests.filterMap fun (u, a, b) =>
      if sumchecks.any (·.test == u) then none else oddOf rp idxO s certs.toList u (rp.eqCall[u]!) a b).filter fun oc =>
    ({ cert with odds := #[oc] }).oddsOk s os ms
  -- The other late tests: GKR's radix-four top layers, WHIR's sumchecks, and claim splits.
  let isEqE := fun (u : ℕ) => match rp.calls.getD (rp.eqCall[u]!) .zero with
    | .eqE .. => true
    | _ => false
  let named := fun (u : ℕ) => sumchecks.any (·.test == u) || odds.any (·.test == u) || covers.any (·.test == u)
  let tops := (tests.filterMap fun (u, a, b) =>
      if named u || !isEqE u then none else topOf rp idxO s certs.toList u (rp.eqCall[u]!) a b).filter fun tc =>
    ({ cert with tops := #[tc] }).topsOk s os ms
  let whirs := (tests.filterMap fun (u, a, b) =>
      if named u || !isEqE u || tops.any (·.test == u) then none
      else whirOf rp idxO s cert os ms (seedsOfT.getD · #[]) (idxRO.getD · #[]) u a b).filter fun wc =>
    ({ cert with whirs := #[wc] }).whirsOk s os ms
  let splits := (tests.filterMap fun (u, a, b) =>
      if named u || !isEqE u || tops.any (·.test == u) || whirs.any (·.test == u) then none
      else splitOf rp idxO u a b).filter fun pc => ({ cert with splits := #[pc] }).splitsOk s os
  let cert := { cert with sumchecks, pows, odds, tops, whirs, splits }
  -- Each residual sumcheck's table certificate: its input claim's `mul_add` of the bus totals, and the latest GKR first
  -- layer reading one root for both trees before it.
  let firstLayers : List (ℕ × ℕ) :=
    (tops.toList.filterMap fun t => match t.values with
      | [a, b] => if a == b then some (t.claimZero, a) else none
      | _ => none) ++
    (odds.toList.filterMap fun t => match t.values with
      | [a, b] => if a == b then some (t.claimZero, a) else none
      | _ => none)
  let tables0 := (List.range sumchecks.size).filterMap fun i =>
    let sc := sumchecks[i]!
    if sc.resid.isEmpty then none else
      let j := rp.maker.getD sc.claim0 0
      match rp.calls.getD j .zero with
      | .mulAdd xi t1 t0 =>
        let root := ((firstLayers.filter (·.1 < j)).foldl (fun acc p => if acc.1 < p.1 then p else acc) (0, 0)).2
        some ({ sc := i, target := j, xi, tot0 := t0, tot1 := t1, root } : TableCert)
      | _ => none
  -- Each table sumcheck's bus GKR: from a first layer reading one root for both trees before it, the certified
  -- sumchecks whose input claim is a radix-four layer's claim over the last layer's next claims, then the totals'
  -- `add`s; the table's root is the first layer's from which the chain reaches its totals, the latest such.
  let layerCands := (List.range sumchecks.size).filterMap fun i =>
    let sc := sumchecks[i]!
    if !sc.resid.isEmpty then none else
      (topOf rp idxO s certs.toList sc.test (rp.eqCall[sc.test]!) sc.claim0 sc.final).map fun t => (i, sc, t)
  let addOf := fun (w v : ℕ) => match rp.calls.getD (rp.maker.getD w 0) .zero with
    | .add x y => if y == v then some (rp.maker.getD w 0, x) else none
    | _ => none
  let chainFrom := fun (tc : TableCert) (odd : Bool) (first : ℕ) => Id.run do
    let g0 : GkrCert := { odd, first, layers := [], totAt := (0, 0), fw := (0, 0) }
    let mut outs := (g0.start tops odds os).2.1
    let mut layers : Array LayerCert := #[]
    for _ in [0:64] do
      let cur := outs
      let some (i, _, t) := layerCands.find? (fun (_, _, t) => t.values == cur) | break
      -- The values bound by `λ`'s time with the words squeezed with `λ` but its own as seeds, as a WHIR batch round's.
      let k := t.transcript
      let own := t.lam.own os
      let lamCall := (t.lam.words.map (·.2.2)).foldl max 0
      let (_, fs) := bind (certs.getD k default).rulesRO cert.nodes (idxRO.getD k #[])
        ((seedsOfT.getD k #[]).filter fun (tm, n) => tm ≤ lamCall && !own.contains n)
      layers := layers.push { sc := i, layer := t, fs }
      outs := (List.range 2).map (t.out os)
    let some (j0, f0) := addOf tc.tot0 (outs.getD 0 0) | return none
    let some (j1, f1) := addOf tc.tot1 (outs.getD 1 0) | return none
    return some { g0 with layers := layers.toList, totAt := (j0, j1), fw := (f0, f1) }
  let gkrOf := fun (tc : TableCert) =>
    let firsts := ((List.range tops.size).filterMap fun i =>
        let t := tops[i]!
        match t.values with
        | [a, b] => if a == b && t.claimZero < tc.target then some (t.claimZero, a, false, i) else none
        | _ => none) ++
      ((List.range odds.size).filterMap fun i =>
        let t := odds[i]!
        match t.values with
        | [a, b] => if a == b && t.claimZero < tc.target then some (t.claimZero, a, true, i) else none
        | _ => none)
    ((firsts.mergeSort fun p q => p.1 ≥ q.1).findSome? fun (_, a, odd, first) =>
      (chainFrom tc odd first).map fun g => (a, g))
  let found := tables0.map fun tc => match gkrOf tc with
    | some (a, g) => ({ tc with root := a }, some g)
    | none => (tc, none)
  let tables := found.map (·.1)
  let tablesOk := tables.all (·.ok cert os)
  let gkrs := found.filterMap fun (tc, g) => g.map (tc, ·)
  let gkrsOk := gkrs.all fun (tc, g) => g.ok tc cert os && g.layersOk cert s os
  let gkrLayers := gkrs.foldl (fun n (_, g) => n + g.layers.length) 0
  -- Each table sumcheck's residual, term by term.
  let resids := tables.filterMap fun tc => sumchecks[tc.sc]?.bind fun sc => residOf rp idxO os tc.sc sc tc.xi
  let residsOk := resids.all (·.okIn os sumchecks cert.calls cert.relax)
  let accepted := cert.accepts s
  let mut anyBound : Array Bool := Array.replicate an.nodes false
  for bd in binds do
    for v in [0:an.nodes] do
      if bd[v]!.isSome then anyBound := anyBound.set! v true
  let mut byConcl : Array (Array ℕ) := Array.replicate an.nodes #[]
  for i in [0:an0.nFunction] do
    for j in [rules.conclOff[i]!:rules.conclOff[i + 1]!] do
      byConcl := byConcl.modify rules.concls[j]! (·.push i)
  let mut unbound := #[]
  let mut late := #[]
  let mut deferred := #[]
  let callOf := fun (i : ℕ) => rp.eqCall[i]!
  for (i, a, b) in tests do
    let g := max (latestOf a) (latestOf b)
    let mut best : Option ℕ := none
    for bd in binds do
      match wireTime bd a, wireTime bd b with
      | some ta, some tb => best := some (match best with | some x => min x (max ta tb) | none => max ta tb)
      | _, _ => pure ()
    match best with
    | none =>
      -- The hinted wires behind it in the transcript that binds most of its limbs.
      let ls := limbs4 a ++ limbs4 b
      let score := fun (bd : Array (Option ℕ)) => (ls.filter fun n => (bd[n]!).isSome).length
      let most := binds.foldl (fun acc bd => if score bd ≥ score acc then bd else acc) (binds[0]?.getD #[])
      let isHint := fun v => v < 4 * s.next && match rp.calls.getD (rp.maker[v / 4]!) .zero with
        | .freeE | .freeK | .freeD => true
        | _ => false
      let hs := hintsOf an byConcl ((Array.range an.nodes).map fun v => (most[v]?.join).isSome) isHint ls 8
      let hs := (if hs.isEmpty then [limb a 0, limb b 0] else hs).filter (· < 4 * s.next)
      let perT := binds.toList.map fun bd => (wireTime bd a, wireTime bd b)
      unbound := unbound.push ⟨callOf i, (a, b), hs.map (rp.maker[· / 4]!), perT⟩
    | some t =>
      if t = rp.calls.size then deferred := deferred.push { call := callOf i, pair := (a, b), hints := [] }
      else if t > g then late := late.push { call := callOf i, pair := (a, b), hints := [t, g] }
  let mut exposed := 0
  let mut exposedUnbound := #[]
  for (w, src) in s.pub do
    match src with
    | .statement j =>
      if tainted w then
        exposed := exposed + 1
        if !(limbs4 w).all (anyBound[·]!) then exposedUnbound := exposedUnbound.push j
    | .const _ => pure ()
  -- A probe's per-transcript binding, then its latest challenge as a last entry.
  let probes := probe.map fun w => (w, binds.toList.map (wireTime · w) ++ [if tainted w then some (latestOf w) else none])
  return {
    accepted, transcripts := ts.size, squeezes := squeezes.size, products := rp.prods.size, tests := tests.size, unbound,
    late, deferred,
    exposed, exposedUnbound, probes, sumchecks := sumchecks.size, tables := tables.length, tablesOk,
    gkrs := gkrs.length, gkrLayers, gkrsOk,
    resids := resids.length, residsOk,
    named := gkrs.filterMap (fun (tc, g) => (resids.find? (·.sc == tc.sc)).map (tc, g, ·)), outs := os,
    relax := cert.relax, scs := sumchecks, topCerts := tops, oddCerts := odds, ts := cert.transcripts,
    rounds := sumchecks.foldl (fun n sc => n + sc.rounds.length) 0,
    residuals := (sumchecks.filter (!·.resid.isEmpty)).size,
    hints := sumchecks.toList.flatMap (·.hints),
    pows := pows.size, powTests := pows.foldl (fun n pc => n + pc.bits) 0, odds := odds.size, tops := tops.size,
    whirs := whirs.size, whirRounds := whirs.foldl (fun n wc => n + wc.rounds.length) 0, splits := splits.size,
    whirBatches := whirs.foldl (fun n wc => n + (wc.rounds.filter fun | .batch .. => true | _ => false).length) 0,
    whirPartial := (whirs.filter fun wc => match wc.rounds.head? with
      | some (.fold (.recv ..) ..) => false
      | _ => true).size, chalsOk := cert.chalsOk s os,
    others := tests.filterMap fun (u, _, _) =>
      if !isEqE u || named u || tops.any (·.test == u) || whirs.any (·.test == u) || splits.any (·.test == u) then none
      else some (rp.eqCall[u]!) }

end LeanVMCircuits.Rec.Bind
