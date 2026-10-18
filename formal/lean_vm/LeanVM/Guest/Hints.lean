/-
  LeanVM.Guest.Hints

  The honest hint generator of the aggregation guest: the witness streams and the initial memory
  of a run on a node's statement, as functions of a `NodeRel` witness.
-/

module

public import LeanVM.Spec.Node
public import LeanVM.Protocol.Verifier
public import LeanVM.Guest.Word

/-!
# The honest hint generator

`honestStreams bytecode seed s w` is every stream the guest pops with `hint_witness`, each a list
of entries in the order the guest pops them, for a run on the statement `s` under the seed
`seed` held by the witness `w`; `publicInput seed s` is the initial memory, the statement's digest
at cells `g^0` and `g^1`. They mirror the Rust producers of
`crates/rec_aggregation/src/aggregation.rs` push for push (`honestPushes`, grouped by stream as
`Hints::push` does): the node's streams (`aggregate_with_stats`), a raw signature's
(`lean_xmss_hints`, `push_lean_sphincs_hints`), a child's (`gen_verify`), the batching's and
LeanDA's.

Where the Rust reads a child's proof (`verifier::replay_unchecked`), this replays the Spec's
deferring verifier (`verifyDeferredWith`): the layout is `readSizes`'s (`announced`), and the
query positions are those of the compiled run itself, recorded by `recordQueries`, which rewrites
a program to return its queries and changes nothing else. The bytecode enters only through its
length, as in `verifyDeferred`. A signature's hints are its scheme's own definitions, at BLAKE2s.

Choices the witness does not fix, made as the Rust makes them:

* **Coverage slots** (`plan`, `take_slot`): the raw signatures first, in the statement's order,
  then every child's claims, child by child; a claim takes its declared slot if it is still
  free, else the next duplicate slot. The deployed lists are strictly sorted, where the first
  free match is the slot `binary_search` finds. A DA claim is matched on its root and its vector
  digest: the guest rebuilds a child's DA list from the slots, so the pair is what has to agree.
* **Holders**: the raw signatures are the claims held `.direct`; a claim held through a child
  takes the slot of the first child making it, whichever child its holder names.
* **A leaf's deferred values** (`leaf_defer`) are the statement's, which the guest does not check.

What the bump allocator hands out is not a hint: the interpreter's allocator chooses it.
-/

namespace LeanVM.Guest.Hints

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## Streams -/

/-- One `hint_witness` entry. -/
abbrev Entry : Type := List E

/-- Streams by name, each its entries in the order the guest pops them. -/
abbrev Streams : Type := List (String × List Entry)

/-- The pushes grouped by stream, the streams in the order of their first push (`Hints::push`). -/
def group (pushes : List (String × Entry)) : Streams :=
  let names := pushes.foldl (fun ns p ↦ if ns.contains p.1 then ns else ns ++ [p.1]) []
  names.map fun n ↦ (n, (pushes.filter (·.1 == n)).map (·.2))

/-! ## The deployed constants -/

/-- `STREAM_CAP`: a child's proof stream is zero-padded to it. -/
def streamCap : ℕ := 8192

/-- `SIGNERS_WINDOW`: the blocks a claim list's digest absorbs per window. -/
def signersWindow : ℕ := 32

/-- `DIGIT_GROUP`: the codeword digits the guest dispatches on at a time. -/
def digitGroup : ℕ := 3

/-! ## Encodings -/

/-- `count(n)`: `g^n`. -/
def count (n : ℕ) : E := gpowE n

/-- A bit as a word. -/
def bit (b : Bool) : E := if b then 1 else 0

/-- 16 bytes as a canonical cell, limb `0` the first 8 (`pack_16_bytes`). -/
def cellOfBytes (b : List UInt8) : E := E.ofLimbs (kOfBytes b) (kOfBytes (b.drop 8)) 0

/-- A byte string's 16-byte cells. -/
def cellsOfBytes (b : List UInt8) : List E :=
  (List.range (b.length / 16)).map fun i ↦ cellOfBytes (b.drop (16 * i))

/-- A 128-bit value as its cell. -/
def cell128 (v : BitVec 128) : E := cellOfBytes (bytes16 v)

/-- A digest's two cells (`pack_hash_state`). -/
def digestCells (d : Digest) : Entry := [(digestScalars d).1, (digestScalars d).2]

/-- A claim's four cells: the key's root and parameter, the message (`claim_cells`). -/
def claimCells (root parameter : BitVec 128) (message : BitVec 256) : Entry :=
  cellsOfBytes (claimBytes root parameter message)

/-- How a list's `n - 1` non-final blocks split into windows and a tail (`signers_split`). -/
def signersSplit (n : ℕ) : Entry := [count ((n - 1) / signersWindow), count ((n - 1) % signersWindow)]

/-- A list's split, if it is not empty, then one push per item. -/
def listPushes (item : String) (entries : List Entry) : List (String × Entry) :=
  (if entries = [] then [] else [("signers_split", signersSplit entries.length)]) ++
    entries.map (item, ·)

/-- A codeword's digits as the guest dispatches on them: `digitGroup` at a time, then the last
alone, each group's index little endian in base 4, in the exponent (`digit_hints`). -/
def digitGroups (digits : List ℕ) : List (String × Entry) :=
  (List.range ((digits.length + digitGroup - 1) / digitGroup)).map fun i ↦
    ("digits", [count (((digits.drop (digitGroup * i)).take digitGroup).foldr (· + 4 * ·) 0)])

/-- The ordered children of a node and its sibling: the sibling first when `right`. -/
def ordered (right : Bool) (node sibling : BitVec 128) : Entry :=
  if right then [cell128 sibling, cell128 node] else [cell128 node, cell128 sibling]

/-! ## Coverage (`Region::plan`, `take_slot`) -/

/-- A claim takes its declared slot if it is free, else the next duplicate slot (`take_slot`).
The state is which declared slots are taken, and the duplicates so far. -/
def takeSlot {α : Type} [BEq α] (declared : List α) (st : List Bool × List α) (claim : α) :
    ℕ × (List Bool × List α) :=
  match (List.range declared.length).find? fun j ↦
      declared[j]? == some claim && !(st.1.getD j true) with
  | some j => (j, (st.1.set j true, st.2))
  | none => (declared.length + st.2.length, (st.1, st.2 ++ [claim]))

/-- The slots of claims taken in order. -/
def takeSlots {α : Type} [BEq α] (declared : List α) :
    List Bool × List α → List α → List ℕ × (List Bool × List α)
  | st, [] => ([], st)
  | st, c :: cs =>
    let (i, st) := takeSlot declared st c
    let (is, st) := takeSlots declared st cs
    (i :: is, st)

/-- The slots of lists of claims taken in order. -/
def takeSlotsAll {α : Type} [BEq α] (declared : List α) :
    List Bool × List α → List (List α) → List (List ℕ) × (List Bool × List α)
  | st, [] => ([], st)
  | st, c :: cs =>
    let (i, st) := takeSlots declared st c
    let (is, st) := takeSlotsAll declared st cs
    (i :: is, st)

/-- One region of the coverage table: its duplicate claims, and the slot of every raw claim and
of every child's claims. -/
structure Region (α : Type) where
  /-- The duplicate claims, in slot order. -/
  dups : List α
  /-- The raw claims' slots. -/
  raw : List ℕ
  /-- Per child, its claims' slots. -/
  children : List (List ℕ)

/-- The region of the declared claims: the raw claims take their slots, then the children's. -/
def plan {α : Type} [BEq α] (declared raw : List α) (children : List (List α)) : Region α :=
  let (raw, st) := takeSlots declared (declared.map fun _ ↦ false, []) raw
  let (children, st) := takeSlotsAll declared st children
  ⟨st.2, raw, children⟩

/-- The claims held directly, with their witnesses, in the statement's order. -/
def direct {α W : Type} : List α → List (Holder W) → List (α × W)
  | c :: cs, .direct w :: hs => (c, w) :: direct cs hs
  | _ :: cs, .child _ :: hs => direct cs hs
  | _, _ => []

/-- DA claims are equal when their roots and their vector digests are. -/
instance : BEq DaClaim := ⟨fun a b ↦ a.1.toList == b.1.toList && a.2.toList == b.2.toList⟩

/-! ## A leanXMSS signature (`lean_xmss_hints`) -/

/-- One layer's hints: the ordered children of every node on the path, the randomizer, the
codeword's digits and the chain values; and the root the layer reaches. -/
def xmssLayer (parameter : LeanXmss.PublicParameter) (lay : LeanXmss.Layer)
    (key : LeanXmss.KeyIndex) (message : List UInt8) (part : LeanXmss.LayerSignature) :
    List (String × Entry) × LeanXmss.Digest :=
  letI : HasQuery LeanXmss.HashSpec Id := ⟨blake2sBits⟩
  let digest := Id.run (LeanXmss.Concrete.messageDigest parameter lay key message part.randomness)
  let leaf := (Id.run (LeanXmss.Concrete.otsLeaf parameter lay key message part.randomness
    part.chainValues)).getD 0
  let fold := fun levels ↦ Id.run (LeanXmss.Concrete.treeFold parameter lay key part.path levels leaf)
  let siblings := (List.finRange LeanXmss.layerHeight).map fun l ↦
    ("siblings", ordered (key.val.testBit l.val) (fold l.val) (part.path l))
  let digits := (List.finRange LeanXmss.numChains).map fun i ↦
    (LeanXmss.Codeword.encoding digest i).val
  let starts := (List.finRange LeanXmss.numChains).map fun i ↦
    ("chain_starts", [cell128 (part.chainValues i)])
  (siblings ++ [("randomizer", [cell128 part.randomness])] ++ digitGroups digits ++ starts,
    fold LeanXmss.layerHeight)

/-- A leanXMSS signature's hints: its leaf index's bits, then each layer's, bottom first. -/
def xmssHints (pk : LeanXmss.PublicKey) (message : LeanXmss.Message) (σ : LeanXmss.Signature) :
    List (String × Entry) :=
  let index := σ.leafIndex
  let bits := (List.range (LeanXmss.numLayers * LeanXmss.layerHeight)).map fun b ↦
    bit (index.val.testBit b)
  let (bottom, root) := xmssLayer pk.parameter LeanXmss.bottomLayer
    (LeanXmss.keyAt index LeanXmss.bottomLayer) (LeanXmss.bytesLE 32 message)
    (σ.layers LeanXmss.bottomLayer)
  let (top, _) := xmssLayer pk.parameter LeanXmss.topLayer (LeanXmss.keyAt index LeanXmss.topLayer)
    (LeanXmss.bytesLE 16 root) (σ.layers LeanXmss.topLayer)
  ("leaf_index_bits", bits) :: bottom ++ top

/-! ## A leanSPHINCS signature (`push_lean_sphincs_hints`) -/

/-- A field the guest dispatches on: in the exponent, and as the address cell whose `hi` it is. -/
def markEntry (index field : ℕ) : Entry :=
  [count index, cellOfBytes (Sphincs.fieldBytes (Sphincs.tweakFields 0 0 field 0))]

/-- A leanSPHINCS signature's hints: the randomizer, the forest's chain values, the digest's
codeword indices, each tree's leaf, each subtree's key and the forest's path nodes in signature
order, the counter, the codeword's digits, the chain values, and the ordered children of every
node on the tree's path. -/
def sphincsHints (pk : Sphincs.PublicKey) (message : Sphincs.Message) (σ : Sphincs.Signature) :
    List (String × Entry) :=
  letI : HasQuery Sphincs.HashSpec Id := ⟨blake2sBits⟩
  let parameter := pk.parameter
  let digest := Id.run (Sphincs.Concrete.messageDigest parameter pk.root message σ.randomness)
  let index := Sphincs.Concrete.digestIndex digest
  let marks := Sphincs.Concrete.digestMarks digest
  let coords := List.finRange Sphincs.forestCoords
  let subtrees := List.finRange 2
  let values := coords.flatMap fun c ↦ subtrees.flatMap fun j ↦
    (List.finRange Sphincs.childChains).map fun i ↦
      ("sp_forest_values", [cell128 (((σ.forest c).sub j).values i)])
  let words := coords.flatMap fun c ↦ subtrees.map fun j ↦
    ("sp_words", [count ((marks c).word j).val])
  let trees := coords.flatMap fun c ↦
    ("sp_leaves", markEntry (marks c).super.val (8 * (marks c).super.val)) ::
      (subtrees.flatMap fun j ↦
        ("sp_keys", markEntry ((marks c).child j).val (256 * ((marks c).child j).val)) ::
          (List.finRange Sphincs.subHeight).map fun l ↦
            ("sp_forest_nodes", [cell128 (((σ.forest c).sub j).path l)])) ++
      (List.finRange Sphincs.topHeight).map fun l ↦ ("sp_forest_nodes", [cell128 ((σ.forest c).top l)])
  let forestKey := Id.run (Sphincs.Concrete.forestRecover parameter index marks σ.forest)
  let lay := Sphincs.topLayer
  let tree := Sphincs.Concrete.treeIndexAt index lay
  let leaf := Sphincs.Concrete.leafIndexAt index lay
  let part := σ.layers lay
  let encoding := Id.run (Sphincs.Concrete.encode parameter lay tree leaf forestKey part.counter)
  let digits := (List.finRange Sphincs.numChains).map fun i ↦ (encoding.map (· i |>.val)).getD 0
  let starts := (List.finRange Sphincs.numChains).map fun i ↦
    ("chain_starts", [cell128 (part.chainValues i)])
  let wotsLeaf := (Id.run (Sphincs.Concrete.otsLeaf parameter lay tree leaf forestKey part.counter
    part.chainValues)).getD 0
  let path := Sphincs.Concrete.signaturePath σ lay
  let siblings := (List.range (Sphincs.layerHeight lay)).map fun l ↦
    ("siblings", ordered (leaf.val.testBit l)
      (Id.run (Sphincs.Concrete.treeFold parameter lay tree leaf path l wotsLeaf)) (path l))
  [("sp_rand", [cell128 σ.randomness])] ++ values ++ words ++ trees ++
    [("sp_counter", [ofK (K.ofBits part.counter.toNat)])] ++ digitGroups digits ++ starts ++ siblings

/-! ## LeanDA -/

/-- A blob matrix's hints: the vector a cell at a time, the row count and its padded log, and
every row's cells, column by column. -/
def daHints (w : Da.Witness) : List (String × Entry) :=
  (List.range LeanDa.cellsPerRow).map (fun j ↦
      ("da_weights", (w.vector.drop (LeanDa.cellSymbols * j)).take LeanDa.cellSymbols)) ++
    [("da_shape", [count w.rows.length, count (LeanDa.logPad w.rows.length)])] ++
    (List.range LeanDa.cellsPerRow).flatMap fun j ↦
      w.rows.map fun row ↦ ("da_symbols", (LeanDa.listCell row j).map ofK)

/-! ## A child (`gen_verify`) -/

/-- The program returning, beside its value, every query it makes: the commitment opened and the
positions, in order. -/
def recordQueries {α : Type} : Prog α → Prog (α × List (ℕ × List ℕ))
  | .ret a => .ret (a, [])
  | .fail => .fail
  | .read k => .read fun x ↦ recordQueries (k x)
  | .sample k => .sample fun x ↦ recordQueries (k x)
  | .grind b k => .grind b (recordQueries k)
  | .commit h w k => .commit h w (recordQueries k)
  | .query i ps k => .query i ps fun rows ↦
      (recordQueries (k rows)).bind fun r ↦ .ret (r.1, (i, ps) :: r.2)

/-- The queries the deferring verifier makes on a child's proof (`verifyDeferredWith`), each with
the height of the commitment it opens. -/
def childQueries (bytecode : List K) (seed : Digest) (c : Child) : List (ℕ × List ℕ) :=
  let publicInput := statementDigest seed c.statement
  let start := blake2sBytes (digestBytes seed ++ digestBytes publicInput)
  match Id.run (Compile.run blake2sBytes
      (recordQueries (deferredProgram c.fresh bytecode publicInput))
      ⟨start, c.proof.stream, c.proof.openings, []⟩) with
  | some ((_, queries), st) => queries.map fun (i, ps) ↦ ((st.roots[i]?.map (·.2.1)).getD 0, ps)
  | none => []

/-- An opening's climb from tree index `index` (the root `1`, a leaf of a depth-`d` tree at
`2^d` plus its position): per level, the node's index, the node and its sibling; and the root. -/
def climbSteps : ℕ → Digest → List Digest → List (ℕ × Digest × Digest) × Digest
  | _, node, [] => ([], node)
  | index, node, s :: ss =>
    let parent := if index % 2 = 0 then hashPair node s else hashPair s node
    let (steps, root) := climbSteps (index / 2) parent ss
    ((index, node, s) :: steps, root)

/-- The two children of a step in order. -/
def stepChildren (step : ℕ × Digest × Digest) : Entry :=
  if step.1 % 2 = 0 then digestCells step.2.1 ++ digestCells step.2.2
  else digestCells step.2.2 ++ digestCells step.2.1

/-- One level's Merkle hints, from its commitment's height, its positions and their openings:
per query its leaf's words and the ordered children below the cap (`merkle_leaf_rows`,
`merkle_children`), and the level's cap nodes and their parents' activity flags. -/
def levelHints (depth : ℕ) (positions : List ℕ) (openings : List Opening) :
    List (String × Entry) × Entry × Entry :=
  let capDepth := min (log2Ceil positions.length) depth
  let pathDepth := depth - capDepth
  let climbs := (positions.zip openings).map fun (q, o) ↦
    (o, climbSteps (2 ^ depth + q) (hashWords o.leaf) o.path)
  let pushes := climbs.flatMap fun (o, steps, _) ↦
    [("merkle_leaf_rows", o.leaf.map ofK),
      ("merkle_children", (steps.take pathDepth).flatMap stepChildren)]
  let capSteps := climbs.flatMap fun (_, steps, _) ↦ steps.drop pathDepth
  let nodes := capSteps.foldl (fun (a : Array Digest) step ↦
      (a.set! step.1 step.2.1).set! (step.1 ^^^ 1) step.2.2)
    (Array.replicate (2 * 2 ^ capDepth) (Vector.replicate 8 0))
  let nodes := climbs.foldl (fun (a : Array Digest) (_, _, root) ↦ a.set! 1 root) nodes
  let active := capSteps.foldl (fun (a : Array E) step ↦ a.set! (step.1 / 2) 1)
    (Array.replicate (2 ^ capDepth) 0)
  (pushes, nodes.toList.flatMap digestCells, active.toList)

/-- Every level's Merkle hints, the openings consumed in order; the caps and the flags of all
levels each make one entry. -/
def merkleHints : List (ℕ × List ℕ) → List Opening → List (String × Entry) × Entry × Entry
  | [], _ => ([], [], [])
  | (depth, positions) :: rest, openings =>
    let (pushes, caps, active) := levelHints depth positions (openings.take positions.length)
    let (pushes', caps', active') := merkleHints rest (openings.drop positions.length)
    (pushes ++ pushes', caps ++ caps', active ++ active')

/-- A side's blocks in the order the stacked leaf cube lays them out, by offset. -/
def blockOrder (sizes : List ℕ) : List ℕ :=
  let offsets := (stackOffsets sizes).1
  (List.range sizes.length).mergeSort fun i j ↦ offsets.getD i 0 ≤ offsets.getD j 0

/-- Every side's blocks in layout order, each block as `g` to its index over the three sides
(`sort_order`): push and pull after the framework's three blocks, then count. -/
def sortOrder (layout : Layout) : Entry :=
  let framework := [0, layout.logMemory, layout.logBytecode]
  let sides := [framework ++ layout.push.map (·.logRows), framework ++ layout.pull.map (·.logRows),
    layout.count.map (·.logRows)]
  (sides.foldl (fun (acc : Entry × ℕ) sizes ↦
    (acc.1 ++ (blockOrder sizes).map (count <| acc.2 + ·), acc.2 + sizes.length)) ([], 0)).1

/-- The committed columns in stack order, each as `g` to its index among them
(`col_sort_order`). -/
def colSortOrder (layout : Layout) : Entry :=
  let columns := (List.range layout.placements.length).filter fun c ↦ (limbSlot c).isNone
  let offset := fun i ↦ (layout.placements.getD (columns.getD i 0) default).index
  ((List.range columns.length).mergeSort fun i j ↦ offset i ≤ offset j).map count

/-- A child's hints (`gen_verify`): its proof stream, padded; its claims' values; the Merkle
caps; the tables' log heights; the two layout orders; and every query's leaf and path. -/
def childHints (bytecode : List K) (seed : Digest) (c : Child) : List (String × Entry) :=
  match announced bytecode c.proof.stream with
  | none => []
  | some (layout, _) =>
    let (queries, caps, active) := merkleHints (childQueries bytecode seed c) c.proof.openings
    [("stream", c.proof.stream ++ List.replicate (streamCap - c.proof.stream.length) 0),
      ("bytecode_val", [c.fresh.bytecodeValue]), ("matpart", [c.fresh.matrixValue]),
      ("merkle_caps", caps), ("merkle_cap_active", active),
      ("zc_tau_max", [count (layout.tableLogHeights.foldl max 0)]),
      ("table_logs", layout.tableLogHeights.map count), ("col_sort_order", colSortOrder layout),
      ("sort_order", sortOrder layout)] ++ queries

/-! ## The node (`aggregate_with_stats`) -/

/-- The batching's hints: both sumchecks' rounds and the values at their ends. -/
def batchPushes (h : BatchHints) : List (String × Entry) :=
  [("bc_sumcheck_msgs", h.bytecodeRounds.flatMap fun r ↦ [r.1, r.2]),
    ("mat_sumcheck_msgs", h.matrixRounds.flatMap fun r ↦ [r.1, r.2]),
    ("bc_star_hint", [h.bytecodeValue]), ("mat_stars_hint", [h.matrixA, h.matrixB])]

/-- **Every push of an honest run**, in the order `aggregate_with_stats` makes them. -/
def honestPushes (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    List (String × Entry) :=
  let rawX := direct s.claims.xmss w.xmss
  let rawS := direct s.claims.sphincs w.sphincs
  let rawD := direct s.claims.da w.da
  let xr := plan s.claims.xmss (rawX.map (·.1)) (w.children.map (·.statement.claims.xmss))
  let sr := plan s.claims.sphincs (rawS.map (·.1)) (w.children.map (·.statement.claims.sphincs))
  let dr := plan s.claims.da (rawD.map (·.1)) (w.children.map (·.statement.claims.da))
  let xCells := fun (c : XmssClaim) ↦ claimCells c.1.root c.1.parameter c.2
  let sCells := fun (c : SphincsClaim) ↦ claimCells c.1.root c.1.parameter c.2
  let slots := fun (offsets : List ℕ) ↦ listPushes "child_claim_index" (offsets.map ([count ·]))
  [("meta", [count s.claims.xmss.length, count xr.dups.length, count rawX.length,
      count s.claims.sphincs.length, count sr.dups.length, count rawS.length,
      count w.children.length, count rawD.length]),
    ("fs_seed", digestCells seed)] ++
  listPushes "claims" (s.claims.xmss.map xCells) ++
  listPushes "claims" (s.claims.sphincs.map sCells) ++
  (xr.dups.map xCells ++ sr.dups.map sCells).map ("dup_claims", ·) ++
  (rawX.zip xr.raw).flatMap (fun (c, slot) ↦ ("raw_index", [count slot]) :: xmssHints c.1.1 c.1.2 c.2) ++
  (rawS.zip sr.raw).flatMap (fun (c, slot) ↦
    ("sp_raw_index", [count slot]) :: sphincsHints c.1.1 c.1.2 c.2) ++
  ((w.children.zip xr.children).zip sr.children).flatMap (fun ((c, xs), ss) ↦
    ("child_meta", [count c.statement.claims.xmss.length, count c.statement.claims.sphincs.length]) ::
      slots xs ++ slots ss ++
      [("child_defer", c.statement.defer.cells), ("child_da_count", [count c.statement.claims.da.length])] ++
      childHints bytecode seed c) ++
  (if w.children = [] then [("leaf_defer", [s.defer.bytecodeValue, s.defer.matrixA, s.defer.matrixB])]
    else batchPushes w.hints) ++
  rawD.flatMap (fun c ↦ daHints c.2) ++
  (dr.raw ++ dr.children.flatten).map (fun slot ↦ ("da_index", [count slot])) ++
  [("da_meta", [count s.claims.da.length, count dr.dups.length])] ++
  (s.claims.da ++ dr.dups).map fun c ↦ ("da_roots", digestCells c.1 ++ digestCells c.2)

/-- **The honest streams**: `honestPushes`, by stream. -/
def honestStreams (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Streams :=
  group (honestPushes bytecode seed s w)

/-- **The public input**, the initial memory at `g^0` and `g^1`: the statement's digest. -/
def publicInput (seed : Digest) (s : NodeStatement) : List E :=
  [(digestScalars (statementDigest seed s)).1, (digestScalars (statementDigest seed s)).2]

end
end LeanVM.Guest.Hints
