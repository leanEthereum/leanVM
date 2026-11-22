module

public import Statement.LeanVmGuest
public import Statement.Prover.Execute
public import Statement.Prover.Prove
public import Statement.Data.AdviceHints

/-!
# The guest's prover, from a node's statement and witness

`guestProve π guest s w ρ fuel` proves the guest program's run on the statement `s` from the
witness `w`: it makes the run's advice (`guestAdvice`), runs the guest on it with the executor
(`guestExecution`, `Prover/Execute.lean`), then proves the execution with the honest prover
(`LeanVM.Prover.prove`). `guest` is the guest program, `guestProgram`; it is an argument so that a
run may pass an equal program whose instructions read faster.

It is the Rust's `aggregate` (`crates/aggregation/src/node.rs`) on its normal form, not all of it.
What `aggregate` computes from its inputs is given here: the statement `s` (the claims it publishes
and its deferred claim), the children's fresh claims (`c.freshClaim`, which `aggregate` reads off
its replay of the child's proof, `verifier::replay_unchecked`, and which this checks in its own
replay, `childQueries`: a child whose fresh claim or proof the deferring verifier rejects gets no
query hints), each child's carried claim (`child_defer`: `c.statement.deferredClaim`, which
`aggregate` rebuilds from the child proof's `bytecode_point` and its `bytecode_sums`), the batching's
hints (`w.batchingHints`, `aggregate_deferred_claims`), a leaf's deferred value
(`DeferredBytecodeClaim::leaf`), a blob matrix's membership challenge (`da_challenge`: the
`DaClaim`'s `membershipChallenge`, which `aggregate` computes from the matrix's commitment) and the
slot of the DA digest the node publishes (`da_pick`: `daPick`, from the statement's DA digest, which
`aggregate` derives from the requested `OutputClaims`, its blobs and its children's claims). The raw
signatures are taken in the witness's order, repeats included, where `aggregate` sorts them on
their claims and keeps the first of each (`sorted_claims`). On the statement and witness an `aggregate` run builds, its raw signatures so
sorted and deduplicated, and of children whose proofs the deferring verifier accepts (the Rust's
replay checks nothing), the streams are the Rust's, entry for entry (`guest-diff` checks it on real
aggregations).

The advice is `main`'s frame size and the compiler's hints by `pc`, generated data
(`Statement/Data/AdviceHints*.lean`, the compiler's `CompiledProgram::export_hints`,
`crates/isa/src/export_hints.rs`), and the witness streams (`guestStreams`): what the guest pops with `hint_witness`, each stream's entries in the order it pops
them. They are the pushes of `aggregate` (`crates/aggregation/src/`:
`node.rs`, `hints.rs`, `child.rs`, `deferred.rs`), grouped by stream as `Hints::push` does
(`honestPushes`, in the order the Rust makes them). Where the Rust replays a child's proof
(`verifier::replay_unchecked`), this runs the deferring verifier (`deferringVerifierProgram`) and
records its queries. A signature's hints are its scheme's own definitions over Keccak-f[1600].

Nothing about the advice is trusted: an execution the executor returns is valid whatever the
advice. Choices the witness does not fix are made as the Rust makes them:

* **Coverage slots** (`coverage.rs`, `take_slot`): each claim a node makes, its raw signatures'
  first, in the witness's order, then every child's, child by child, takes its declared slot if
  it is still free, else the next duplicate slot.
* **A leaf's deferred value** (`leaf_defer`) is the statement's, which the guest does not check.
-/

@[expose] public section

namespace LeanVM.Guest.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-! ## Streams -/

/-- One `hint_witness` entry. -/
abbrev Entry : Type := List E

/-- Streams by name, each its entries in the order the guest pops them. -/
abbrev Streams : Type := List (String × List Entry)

/-- The pushes grouped by stream, the streams in the order of their first push (`Hints::push`). -/
def group (pushes : List (String × Entry)) : Streams :=
  let names := pushes.foldl (fun ns p ↦ if ns.contains p.1 then ns else ns ++ [p.1]) []
  names.map fun n ↦ (n, (pushes.filter (·.1 == n)).map (·.2))

/-! ## The guest's constants -/

/-- `CLAIM_GROUP` (`statement.rs`): the claims a claim list's digest absorbs per group. -/
def claimGroup : ℕ := 17

/-- `CLAIM_BIG` (`statement.rs`): the claims the main list loop absorbs per frame, `8` groups. -/
def claimBig : ℕ := claimGroup * 8

/-- `DIGIT_GROUP` (`hints.rs`): the leanSPHINCS codeword digits the guest dispatches on at a time. -/
def digitGroup : ℕ := 3

/-- `LX_DIGIT_GROUP` (`hints.rs`): the leanXMSS codeword digits the guest dispatches on at a time. -/
def lxDigitGroup : ℕ := 4

/-- `LX_WINDOW` (`hints.rs`): the leaf index bits a leanXMSS path dispatch covers. -/
def lxWindow : ℕ := 8

/-- `STREAM_CAP` (`child.rs`): a child's proof stream is zero-padded to it. -/
def streamCap : ℕ := 8192

/-- `QUERY_WINDOW_BITS` (`child.rs`): the bits of a query position the guest reads per window. -/
def queryWindowBits : ℕ := 6

/-! ## Encodings (`cells.rs`, `statement.rs`) -/

/-- `count(n)`: `g^n`. -/
def count (n : ℕ) : E := gpow n

/-- 16 bytes as a cell, limb `0` the first 8 (`pack_16_bytes`). -/
def cellOfBytes (b : List UInt8) : E :=
  E.ofLimbs (K.ofLane (littleEndianLane b 0)) (K.ofLane (littleEndianLane b 1))

/-- A byte string's 16-byte cells. -/
def cellsOfBytes (b : List UInt8) : List E :=
  (List.range (b.length / 16)).map fun i ↦ cellOfBytes (b.drop (16 * i))

/-- A 128-bit value as its cell. -/
def cell128 (v : BitVec 128) : E := cellOfBytes (HashSig.littleEndianBytes 16 v)

/-- A digest's two cells (`hash_to_scalars`). -/
def digestCells (d : Digest) : Entry := [(digestHalves d).1, (digestHalves d).2]

/-- Bytes, each in the exponent (`exponent_bytes`). -/
def exponentBytes (bytes : List UInt8) : Entry :=
  bytes.map fun b ↦ count b.toNat

/-- How a list of `n` claims splits into whole frames of `claimBig`, then whole groups of
`claimGroup`, then the rest (`list_split`). -/
def listSplit (n : ℕ) : Entry :=
  [count (n / claimBig), count (n % claimBig / claimGroup), count (n % claimBig % claimGroup)]

/-- A list's split (`signers_split`), if it is not empty, then one push per item. -/
def listPushes (item : String) (entries : List Entry) : List (String × Entry) :=
  (if entries = [] then [] else [("signers_split", listSplit entries.length)]) ++
    entries.map (item, ·)

/-- A codeword's digits as the guest dispatches on them: `size` at a time, then the rest, each
group's index little endian in base 4, in the exponent (`digit_hints`). -/
def digitHints (size : ℕ) (digits : List ℕ) : List Entry :=
  (List.range ((digits.length + size - 1) / size)).map fun i ↦
    [count (((digits.drop (size * i)).take size).foldr (· + 4 * ·) 0)]

/-- The leanSPHINCS digits' pushes (`digits`): `digitGroup` at a time, one push each. -/
def digitGroups (digits : List ℕ) : List (String × Entry) :=
  (digitHints digitGroup digits).map ("digits", ·)

/-- The ordered children of a node and its sibling: the sibling first when `right`. -/
def ordered (right : Bool) (node sibling : BitVec 128) : Entry :=
  if right then [cell128 sibling, cell128 node] else [cell128 node, cell128 sibling]

/-! ## Coverage (`coverage.rs`) -/

/-- A claim takes its declared slot if it is free, else the next duplicate slot (`take_slot`).
The state is which declared slots are taken, and the duplicates so far. -/
def takeSlot {α : Type} [BEq α] (declared : List α) (slotState : List Bool × List α) (claim : α) :
    ℕ × (List Bool × List α) :=
  match (List.range declared.length).find? fun j ↦
      declared[j]? == some claim && !(slotState.1.getD j true) with
  | some j => (j, (slotState.1.set j true, slotState.2))
  | none => (declared.length + slotState.2.length, (slotState.1, slotState.2 ++ [claim]))

/-- The slots of claims taken in order. -/
def takeSlots {α : Type} [BEq α] (declared : List α) :
    List Bool × List α → List α → List ℕ × (List Bool × List α)
  | slotState, [] => ([], slotState)
  | slotState, claim :: claims =>
    let (slot, slotState) := takeSlot declared slotState claim
    let (slots, slotState) := takeSlots declared slotState claims
    (slot :: slots, slotState)

/-- The slots of lists of claims taken in order. -/
def takeSlotsAll {α : Type} [BEq α] (declared : List α) :
    List Bool × List α → List (List α) → List (List ℕ) × (List Bool × List α)
  | slotState, [] => ([], slotState)
  | slotState, claims :: claimLists =>
    let (slots, slotState) := takeSlots declared slotState claims
    let (slotLists, slotState) := takeSlotsAll declared slotState claimLists
    (slots :: slotLists, slotState)

/-- One scheme's region of the coverage table. -/
structure CoverageRegion (α : Type) where
  /-- The duplicate claims, in slot order. -/
  duplicates : List α
  /-- The slot of each raw signature's claim. -/
  directSlots : List ℕ
  /-- The slots of each child's claims. -/
  childSlots : List (List ℕ)

/-- The region of the declared claims `declared` (`Region::plan`): the raw signatures' claims take
their slots, then the children's. -/
def coveragePlan {α : Type} [BEq α] (declared raw : List α) (children : List (List α)) :
    CoverageRegion α :=
  let (raw, slotState) := takeSlots declared (declared.map fun _ ↦ false, []) raw
  let (children, slotState) := takeSlotsAll declared slotState children
  ⟨slotState.2, raw, children⟩

/-! ## A leanXMSS signature (`lean_xmss_hints`, `hints.rs`) -/

/-- One layer's hints: the sibling of every node on the path (`lx_path`), the randomizer, the
codeword's digits (`lx_digits`, `lxDigitGroup` at a time, one push) and the chain values
(`chain_starts`); and the root the layer reaches. -/
def xmssLayer (parameter : HashSig.PublicParameter) (lay : LeanXmss.Layer)
    (key : LeanXmss.KeyIndex) (message : List UInt8) (part : LeanXmss.LayerSignature) :
    List (String × Entry) × HashSig.Digest :=
  let digest := Id.run (LeanXmss.Verification.messageDigest (m := Id) keccakF1600 parameter lay key
    message part.randomizer)
  let leaf := (Id.run (LeanXmss.Verification.otsLeaf (m := Id) keccakF1600 parameter lay key message
    part.randomizer part.chainValues)).getD 0
  let fold := fun levels ↦ Id.run (LeanXmss.Verification.treeFold (m := Id) keccakF1600
      parameter lay
    key part.authenticationPath levels leaf)
  let siblings := (List.finRange LeanXmss.layerHeight).map fun l ↦
    ("lx_path", [cell128 (part.authenticationPath l)])
  let digits := (List.finRange LeanXmss.chainCount).map fun i ↦
    (HashSig.digestDigits digest i).val
  let starts := (List.finRange LeanXmss.chainCount).map fun i ↦
    ("chain_starts", [cell128 (part.chainValues i)])
  (siblings ++ [("randomizer", [cell128 part.randomizer]),
      ("lx_digits", (digitHints lxDigitGroup digits).flatten)] ++ starts,
    fold LeanXmss.layerHeight)

/-- A leanXMSS signature's hints: its leaf index shifted by each multiple of `lxWindow`
(`lx_index`), those windows in the exponent (`lx_windows`), then each layer's, bottom first. -/
def xmssHints (pk : HashSig.PublicKey) (message : HashSig.Message) (σ : LeanXmss.Signature) :
    List (String × Entry) :=
  let index := σ.leafIndex
  let shifts := (List.range (LeanXmss.layerCount * LeanXmss.layerHeight / lxWindow)).map fun v ↦
    index.val / 2 ^ (lxWindow * v)
  let (bottom, root) := xmssLayer pk.parameter LeanXmss.bottomLayer
    (LeanXmss.keyIndexOnLayer index LeanXmss.bottomLayer) (HashSig.littleEndianBytes 32 message)
    (σ.layers LeanXmss.bottomLayer)
  let (top, _) := xmssLayer pk.parameter LeanXmss.topLayer (LeanXmss.keyIndexOnLayer index
      LeanXmss.topLayer)
    (HashSig.littleEndianBytes 16 root) (σ.layers LeanXmss.topLayer)
  ("lx_index", shifts.map fun x ↦ E.ofLimbs (K.ofBits x) (K.ofBits 0)) ::
    ("lx_windows", shifts.map fun x ↦ count (x % 2 ^ lxWindow)) :: bottom ++ top

/-! ## A leanSPHINCS signature (`lean_sphincs_hints`, `hints.rs`) -/

/-- The bytes of `H_msg`'s two calls past its `34` (the second call's bytes `2` to `7`), each in the
exponent, one entry (`sp_unused`). -/
def sphincsUnusedEntry (outputs : Sphincs.DigestCall → HashSig.HashOutput) : Entry :=
  (List.range 6).map fun k ↦ count (Sphincs.digestValue outputs / 2 ^ (8 * (34 + k)) % 256)

/-- A counter's four bytes, most significant first, each in the exponent, one entry
(`sp_counter`). -/
def sphincsCounterEntry (counter : Sphincs.EncodingCounter) : Entry :=
  exponentBytes (Sphincs.bigEndianBytes 4 counter)

/-- One FORS tree's hints: the ordered children of every node on its climb, from the leaf up
(`sp_fors_nodes`). -/
def sphincsForsNodes (publicSeed : HashSig.PublicParameter) (index : Sphincs.Index)
    (tree : Sphincs.ForsTreeIndex) (leaf : Sphincs.ForsLeafIndex)
    (opening : Sphincs.ForsTreeOpening) : List (String × Entry) :=
  let path := fun level ↦
    if h : level < Sphincs.forsTreeHeight then opening.path ⟨level, h⟩ else 0
  let value := Id.run (Sphincs.Verification.forsLeafHash (m := Id) keccakF1600 publicSeed index
    tree leaf opening.secret)
  let fold := fun levels ↦ Id.run (HashSig.OverPermutation.foldPath (m := Id)
    (fun level node ↦ Sphincs.Verification.tweakableHash keccakF1600 publicSeed
      (.forsNode index tree (level + 1) node))
    leaf.val path levels value)
  (List.range Sphincs.forsTreeHeight).map fun l ↦
    ("sp_fors_nodes", ordered (leaf.val.testBit l) (fold l) (path l))

/-- One layer's hints: the counter's bytes, the codeword's digits, the chain values
(`chain_starts`) and the ordered children of every node on the key's path (`siblings`); and the
root the layer reaches, which the layer above signs. -/
def sphincsLayer (publicSeed : HashSig.PublicParameter) (index : Sphincs.Index)
    (σ : Sphincs.Signature) (layer : Sphincs.Layer) (signed : HashSig.Digest) :
    List (String × Entry) × HashSig.Digest :=
  let tree := Sphincs.treeOfIndex layer index
  let leaf := Sphincs.leafOfIndex layer index
  let part := σ.layers layer
  let encoding := Id.run (Sphincs.Verification.encode (m := Id) keccakF1600 publicSeed layer tree
    leaf signed part.counter)
  let digits := (List.finRange Sphincs.chainCount).map fun i ↦ (encoding.map (· i |>.val)).getD 0
  let starts := (List.finRange Sphincs.chainCount).map fun i ↦
    ("chain_starts", [cell128 (part.chainValues i)])
  let value := (Id.run (Sphincs.Verification.otsLeaf (m := Id) keccakF1600 publicSeed layer tree
    leaf signed part.counter part.chainValues)).getD 0
  let fold := fun levels ↦ Id.run (Sphincs.Verification.treeFold (m := Id) keccakF1600 publicSeed
    layer tree leaf (Sphincs.Verification.layerPath σ layer) levels value)
  let siblings := (List.range (Sphincs.layerHeight layer)).map fun l ↦
    ("siblings", ordered (leaf.val.testBit l) (fold l) (Sphincs.Verification.layerPath σ layer l))
  ([("sp_counter", sphincsCounterEntry part.counter)] ++ digitGroups digits ++ starts ++ siblings,
    fold (Sphincs.layerHeight layer))

/-- A leanSPHINCS signature's hints: the randomizer (`sp_rand`), `H_msg`'s bytes past its `34`,
every FORS tree's secret (`sp_fors_secrets`), every tree's climb, then each layer's, bottom first,
the bottom one-time key signing the FORS key and each above the root below. -/
def sphincsHints (pk : Sphincs.PublicKey) (message : HashSig.Message) (σ : Sphincs.Signature) :
    List (String × Entry) :=
  let publicSeed := pk.publicSeed
  let outputs := fun call ↦ Id.run (Sphincs.Verification.messageDigestCall (m := Id) keccakF1600
    σ.randomizer publicSeed pk.root message call)
  let digest := Sphincs.truncateMessageDigest outputs
  let index := Sphincs.digestIndex digest
  let leaves := Sphincs.digestForsLeaves digest
  let trees := List.finRange Sphincs.forsTreeCount
  let secrets := trees.map fun c ↦ ("sp_fors_secrets", [cell128 (σ.forsOpening c).secret])
  let climbs := trees.flatMap fun c ↦
    sphincsForsNodes publicSeed index c (leaves c) (σ.forsOpening c)
  let forsKey := Id.run (Sphincs.Verification.forsRecover (m := Id) keccakF1600 publicSeed index
    leaves σ.forsOpening)
  let (bottom, rootB) := sphincsLayer publicSeed index σ 0 forsKey
  let (middle, rootM) := sphincsLayer publicSeed index σ 1 rootB
  let (top, _) := sphincsLayer publicSeed index σ 2 rootM
  [("sp_rand", [cell128 σ.randomizer]), ("sp_unused", sphincsUnusedEntry outputs)] ++ secrets ++
    climbs ++ bottom ++ middle ++ top

/-! ## LeanDA (`node.rs`) -/

/-- A blob matrix's hints: the claim's membership challenge (`da_challenge`), the blob count
(`da_n_blobs`), and every blob's cells, blob by blob (`da_symbols`). -/
def daHints (c : DaClaim) (w : Da.MatrixWitness) : List (String × Entry) :=
  [("da_challenge", [c.membershipChallenge]), ("da_n_blobs", [count w.rows.length])] ++
    w.rows.flatMap fun row ↦
      (List.range LeanDa.cellsPerRow).map fun j ↦
        ("da_symbols", (row.drop (j * LeanDa.cellSymbols)).take LeanDa.cellSymbols)

/-! ## A child (`gen_verify`, `child.rs`) -/

/-- The program returning, beside its value, every query it makes: the commitment opened and the
positions, in order. -/
def recordQueries {α : Type} : VerifierProgram α → VerifierProgram (α × List (ℕ × List ℕ))
  | .ret a => .ret (a, [])
  | .fail => .fail
  | .read k => .read fun x ↦ recordQueries (k x)
  | .sample k => .sample fun x ↦ recordQueries (k x)
  | .grind b k => .grind b (recordQueries k)
  | .commit h w k => .commit h w (recordQueries k)
  | .query i ps k => .query i ps fun rows ↦
      (recordQueries (k rows)).bind fun r ↦ .ret (r.1, (i, ps) :: r.2)

/-- The queries the deferring verifier makes on a child's proof (`verifyDeferred` over the bytecode
`bytecode` and the seed `seed`), each with the height of the commitment it opens. -/
def childQueries (bytecode : List K) (seed : Digest) (c : Child) : List (ℕ × List ℕ) :=
  match Id.run (Compile.run (m := Id) keccakF1600
      (recordQueries (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed
          c.statement)))
      ⟨⟨keccakF1600 (seedInput seed (statementDigest seed c.statement)), [], none⟩,
        c.proof.stream, c.proof.openings, []⟩) with
  | some ((_, queries), st) => queries.map fun (i, ps) ↦ ((st.roots[i]?.map (·.2.1)).getD 0, ps)
  | none => []

/-- An opening's climb from tree index `index` (the root `1`, a leaf of a depth-`d` tree at
`2^d` plus its position): per level, the node's index, the node and its sibling; and the root. -/
def climbSteps : ℕ → Digest → List Digest → List (ℕ × Digest × Digest) × Digest
  | _, node, [] => ([], node)
  | index, node, s :: ss =>
    let parent := if index % 2 = 0 then keccak256 (digestBytes node ++ digestBytes s)
      else keccak256 (digestBytes s ++ digestBytes node)
    let (steps, root) := climbSteps (index / 2) parent ss
    ((index, node, s) :: steps, root)

/-- The two children of a step in order. -/
def stepChildren (step : ℕ × Digest × Digest) : Entry :=
  if step.1 % 2 = 0 then digestCells step.2.1 ++ digestCells step.2.2
  else digestCells step.2.2 ++ digestCells step.2.1

/-- A leaf's words as the guest's cells: level `0`'s a `K` word each, a deeper level's an `E` word
of two `K` words each. -/
def leafCells (first : Bool) (leaf : List K) : Entry :=
  if first then leaf.map ofK
  else (List.range (leaf.length / 2)).map fun i ↦
    E.ofLimbs (leaf.getD (2 * i) 0) (leaf.getD (2 * i + 1) 0)

/-- A level's cap depth (`merkle_cap_depth`): whole windows below the root, the last ending from
`log2 count - 5` to five levels below that, and at least two levels deep. -/
def capDepthOf (count depth : ℕ) : ℕ :=
  let near := min (max (log2Ceil count - (queryWindowBits - 1)) 2) depth
  depth - (depth - near) / queryWindowBits * queryWindowBits

/-- One level's Merkle hints, from whether it is level `0`, its commitment's height, its query
count and its phase of openings: per opening its leaf's cells (`merkle_leaf_rows`) and the ordered
children below the cap, climbing from its leaf (`merkle_children`), then the level's cap nodes
(`merkle_caps`) and their parents' activity flags (`merkle_cap_active`). -/
def levelHints (first : Bool) (depth count : ℕ) (phase : List Opening) : List (String × Entry) :=
  let capDepth := capDepthOf count depth
  let pathDepth := depth - capDepth
  let climbs := phase.map fun o ↦
    (o, climbSteps (2 ^ depth + o.leafIndex) (keccak256 (o.leaf.flatMap K.toBytes)) o.path)
  let pushes := climbs.flatMap fun (o, steps, _) ↦
    [("merkle_leaf_rows", leafCells first o.leaf),
      ("merkle_children", (steps.take pathDepth).flatMap stepChildren)]
  let capSteps := climbs.flatMap fun (_, steps, _) ↦ steps.drop pathDepth
  let nodes := capSteps.foldl (fun (a : Array Digest) step ↦
      (a.set! step.1 step.2.1).set! (step.1 ^^^ 1) step.2.2)
    (Array.replicate (2 * 2 ^ capDepth) (Vector.replicate 4 0))
  let nodes := climbs.foldl (fun (a : Array Digest) (_, _, root) ↦ a.set! 1 root) nodes
  let active := capSteps.foldl (fun (a : Array E) step ↦ a.set! (step.1 / 2) 1)
    (Array.replicate (2 ^ capDepth) 0)
  pushes ++ [("merkle_caps", nodes.toList.flatMap digestCells), ("merkle_cap_active", active.toList)]

/-- Every level's Merkle hints, each level with its phase of the proof's openings, the first
`first`. -/
def merkleHints (first : Bool) : List (ℕ × List ℕ) → List (List Opening) → List (String × Entry)
  | (depth, positions) :: rest, phase :: phases =>
    levelHints first depth positions.length phase ++ merkleHints false rest phases
  | _, _ => []

/-- A side's blocks in the order the stacked leaf cube lays them out, by offset. -/
def blockOrder (sizes : List ℕ) : List ℕ :=
  let offsets := (stackOffsets sizes).1
  (List.range sizes.length).mergeSort fun i j ↦ offsets.getD i 0 ≤ offsets.getD j 0

/-- A list with each run of equal neighbours kept once. -/
def runHeads : List ℕ → List ℕ
  | a :: b :: l => if a = b then runHeads (b :: l) else a :: runHeads (b :: l)
  | l => l

/-- The group of each key of a run, numbered from `next`: a group is a maximal run of one key
(`block_groups`, `col_groups`). -/
def runGroups : ℕ → Option ℕ → List ℕ → List ℕ
  | _, _, [] => []
  | next, prev, k :: ks =>
      if prev = some k then (next - 1) :: runGroups next prev ks
      else next :: runGroups (next + 1) (some k) ks

/-- A bus block's kappa source, as a key (`block_kappa_sources`, `layout.rs`): the framework's
three blocks `0` to `2`, a table's block its table. -/
def blockKey (b : BusBlock) : ℕ := 3 + b.owner

/-- Every side's block groups in layout order, each as `g` to its index over the three sides,
once per group, whose blocks are consecutive (`block_group_order`): push and pull after the
framework's three blocks, then count; a group is a maximal run of blocks of one kappa source
within a side. -/
def blockGroupOrder (layout : Layout) : Entry :=
  let framework := [0, layout.logMemory, layout.logBytecode]
  let sides := [(framework ++ layout.push.map (·.logRows), [0, 1, 2] ++ layout.push.map blockKey),
    (framework ++ layout.pull.map (·.logRows), [0, 1, 2] ++ layout.pull.map blockKey),
    (layout.count.map (·.logRows), layout.count.map blockKey)]
  (sides.foldl (fun (acc : Entry × ℕ) side ↦
    let groups := runGroups acc.2 none side.2
    (acc.1 ++ (runHeads ((blockOrder side.1).map (groups.getD · 0))).map count,
      acc.2 + (runHeads groups).length)) ([], 0)).1

/-- The committed columns: every global column but the `KECCAK` value lanes. -/
def committedColumns (layout : Layout) : List ℕ :=
  (List.range layout.placements.length).filter fun c ↦
    (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns

/-- A global column's kappa source, as a key (`col_kappa_sources`, `layout.rs`): the memory's two
columns and `MFCNT` `0`, `BFCNT` `1`, `QKECCAK` `2`, a table's columns their table. -/
def colKey (c : ℕ) : ℕ :=
  if c < 3 then 0 else if c < 5 then c - 2 else 3 + (globalColumnBases.filter (· ≤ c)).length

/-- The committed columns' groups in stack order, each as `g` to its index, once per group,
whose columns are consecutive (`col_group_order`): a group is a maximal run of committed columns,
in their order, of one kappa source. -/
def colGroupOrder (layout : Layout) : Entry :=
  let columns := committedColumns layout
  let groups := runGroups 0 none (columns.map colKey)
  let offset := fun i ↦ (layout.placement (columns.getD i 0)).index
  (runHeads (((List.range columns.length).mergeSort fun i j ↦ offset i ≤ offset j).map
    (groups.getD · 0))).map count

/-- A child's hints (`gen_verify`): its proof stream zero-padded to `streamCap` (`stream`); the
tables' rounds (`zc_tau_max`) and log heights (`table_logs`); the two layout orders; and every
query's leaf and path. Nothing for a proof whose sizes do not read. -/
def childHints (bytecode : List K) (seed : Digest) (c : Child) : List (String × Entry) :=
  match announcedLayoutAndRate bytecode c.proof.stream with
  | none => []
  | some (layout, _) =>
    let queries := merkleHints true (childQueries bytecode seed c) c.proof.openings
    let rounds := layout.tableLogHeights.foldl max 0
    [("stream", c.proof.stream ++ List.replicate (streamCap - c.proof.stream.length) 0),
      ("zc_tau_max", [count rounds]),
      ("table_logs", layout.tableLogHeights.map count),
      ("col_group_order", colGroupOrder layout), ("block_group_order", blockGroupOrder layout)] ++
      queries

/-! ## The node (`aggregate`, `node.rs`) -/

/-- Whether a list is strictly increasing (`is_sorted_by(a < b)`). -/
def increasing : List ℕ → Bool
  | a :: b :: l => a < b && increasing (b :: l)
  | _ => true

/-- The gaps between strictly increasing slots, each from the slot after the previous one. -/
def slotGaps : ℕ → List ℕ → List ℕ
  | _, [] => []
  | next, o :: os => (o - next) :: slotGaps (o + 1) os

/-- A child's slots in one scheme's region, if any: the split, then, strictly increasing, the
flag `1` (`child_mono`) and the gaps (`child_claim_gap`), else the flag `0` and the slots
(`child_claim_index`). -/
def childSlotPushes (offsets : List ℕ) : List (String × Entry) :=
  if offsets = [] then [] else
    ("signers_split", listSplit offsets.length) ::
      if increasing offsets then
        ("child_mono", [count 1]) :: (slotGaps 0 offsets).map fun d ↦ ("child_claim_gap", [count d])
      else ("child_mono", [count 0]) :: offsets.map fun o ↦ ("child_claim_index", [count o])

/-- The batching's hints: the proof of work's nonce, if it grinds, and the sumcheck's rounds
(`bc_sumcheck_msgs`, as `aggregate_deferred_claims` writes them: `Batch.lambdaGrindNonceCells`,
`Batch.sumcheckRoundCells`), and the bytecode's value at its end (`bc_star_hint`). -/
def batchPushes (h : BatchingHints) : List (String × Entry) :=
  [("bc_sumcheck_msgs", Guest.Batch.lambdaGrindNonceCells h ++
      h.sumcheckMessages.flatMap Guest.Batch.sumcheckRoundCells),
    ("bc_star_hint", [h.finalBytecodeValue])]

/-- The DA digest the node publishes, as the slot of `da_digests` it picks (`da_pick`): its own
(`n`, the children's count) when it checks a matrix or publishes zeros, else the first child whose
DA digest it publishes. -/
def daPick (s : NodeStatement) (w : NodeWitness) : ℕ :=
  if w.daMatrix.isSome || s.claims.daDigest == zeroDigest then w.children.length
  else (w.children.findIdx? fun c ↦ c.statement.claims.daDigest == s.claims.daDigest).getD w.children.length

/-- **Every push of an honest run**, in the order `aggregate` makes them: the node's
sizes (`meta`) and seed (`fs_seed`), the claim lists (`claims`) and the
duplicates (`dup_claims`), each raw signature's slot (`raw_index`, `sp_raw_index`) and hints, each
child's sizes (`child_meta`), slots, carried claim (`child_defer`), DA digest (`child_da`) and
hints, the batching's hints or a leaf's deferred value (`leaf_defer`), the blob matrix's hints and
the DA digest's pick. -/
def honestPushes (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    List (String × Entry) :=
  let rawX := w.xmssSignatures
  let rawS := w.sphincsSignatures
  let xr := coveragePlan s.claims.xmss (rawX.map (·.1)) (w.children.map (·.statement.claims.xmss))
  let sr := coveragePlan s.claims.sphincs (rawS.map (·.1))
    (w.children.map (·.statement.claims.sphincs))
  let xCells := fun (c : LeanXmssClaim) ↦ cellsOfBytes (claimBytes xmssPublicKeyBytes c)
  let sCells := fun (c : LeanSphincsClaim) ↦ cellsOfBytes (claimBytes Sphincs.PublicKey.toBytes c)
  [("meta", [count s.claims.xmss.length, count xr.duplicates.length, count rawX.length,
      count s.claims.sphincs.length, count sr.duplicates.length, count rawS.length,
      count w.children.length, count ((w.daMatrix.map fun _ ↦ 1).getD 0)]),
    ("fs_seed", digestCells seed)] ++
  listPushes "claims" (s.claims.xmss.map xCells) ++
  listPushes "claims" (s.claims.sphincs.map sCells) ++
  (xr.duplicates.map xCells ++ sr.duplicates.map sCells).map ("dup_claims", ·) ++
  (rawX.zip xr.directSlots).flatMap (fun (c, slot) ↦ ("raw_index", [count slot]) :: xmssHints c.1.1 c.1.2 c.2) ++
  (rawS.zip sr.directSlots).flatMap (fun (c, slot) ↦
    ("sp_raw_index", [count slot]) :: sphincsHints c.1.1 c.1.2 c.2) ++
  ((w.children.zip xr.childSlots).zip sr.childSlots).flatMap (fun ((c, xs), ss) ↦
    ("child_meta", [count c.statement.claims.xmss.length, count c.statement.claims.sphincs.length]) ::
      childSlotPushes xs ++ childSlotPushes ss ++
      [("child_defer", c.statement.deferredClaim.cells), ("child_da", digestCells c.statement.claims.daDigest)] ++
      childHints bytecode seed c) ++
  (if w.children = [] then [("leaf_defer", [s.deferredClaim.bytecodeValue])] else batchPushes w.batchingHints) ++
  (w.daMatrix.map (fun c ↦ daHints c.1 c.2)).getD [] ++
  [("da_pick", [count (daPick s w)])]

end LeanVM.Guest.Prover

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Prover

/-- **The witness streams** on the statement `s`, from the witness `w`, under the seed `seed`: the
honest pushes, by stream. Of the bytecode `bytecode`, the deferring verifier reads only the length. -/
def guestStreams (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Prover.Streams :=
  Prover.group (Prover.honestPushes bytecode seed s w)

/-- **The guest's advice** on a node: `main`'s frame size and the compiler's hints, generated
(`Statement/Data/AdviceHints*.lean`), and the witness streams. -/
def guestAdvice (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Exec.Advice :=
  ⟨Data.adviceMainFrame, Data.adviceHints, guestStreams bytecode seed s w⟩

/-- **The guest's execution on a node**: the executor's run of the guest program `guest` on the
statement's digest under `guest`'s seed, with the guest's advice; the execution, or the `pc` and
fault it stops at. `guest` is `guestProgram`, an argument so that a run may pass an equal program
whose instructions read faster. -/
def guestExecution (guest : LeanIsaProgram) (s : NodeStatement) (w : NodeWitness) :
    Except (ℕ × Exec.Fault) (Execution guest) :=
  let seed := deployedSeed guest
  Exec.execute guest (PublicInput.ofDigest (statementDigest seed s))
    (guestAdvice (bytecodeWords guest) seed s w)

/-- **The guest's prover**: the honest prover's (`prove`, over `π`, at the rate `2^-ρ`, `fuel`
nonces per proof of work) proof of the guest's execution on the node; `none` if the executor
stops. -/
def guestProve {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (guest : LeanIsaProgram) (s : NodeStatement) (w : NodeWitness) (ρ fuel : ℕ) :
    m (Option Proof) :=
  match guestExecution guest s w with
  | .ok t => prove π guest (PublicInput.ofDigest (statementDigest (deployedSeed guest) s)) t ρ fuel
  | .error _ => pure none

end LeanVM.Guest

end
