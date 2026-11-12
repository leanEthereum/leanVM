/-
  LeanVM.Guest.Hints

  The honest hint generator of the aggregation guest: the witness streams and the initial memory
  of a run on a node's statement, as functions of a `NodeRelation` witness.
-/

module

public import Statement.LeanVmGuest
public import LeanVM.Facts.ClaimBytes
public import LeanVM.Guest.Batch.Def
public import LeanXmss.Scheme
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Protocol.Verifier
public import LeanVM.Guest.Word
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Protocol.KeccakHash

/-!
# The honest hint generator

`honestStreams bytecode seed s w` is every stream the guest pops with `hint_witness`, each a list
of entries in the order the guest pops them, for a run on the statement `s` under the seed
`seed` held by the witness `w`; `publicInput seed s` is the initial memory, the statement's digest
at cells `g^0` and `g^1`. They mirror the Rust producers of
`crates/rec_aggregation/src/aggregation/` (leanVM main `40f877dc`) push for push (`honestPushes`,
grouped by stream as `Hints::push` does, `aggregation/hints.rs:62-67`): the node's streams
(`aggregate_with_stats`, `aggregation/node.rs:62-348`), a raw signature's (`lean_xmss_hints`,
`aggregation/hints.rs:100-135`; `lean_sphincs_hints`, `aggregation/hints.rs:147-183`), a child's
(`gen_verify`, `aggregation/child.rs:75-260`), the batching's (`aggregate_deferred_claims`,
`aggregation/deferred.rs:245-354`) and LeanDA's.

Where the Rust reads a child's proof (`verifier::replay_unchecked`), this replays the Spec's
deferring verifier (`verifyDeferredWith` over Keccak-f[1600], from
`keccakF (seedInput seed publicInput)`): the layout is `readAnnouncedSizes`'s
(`Verifier.announcedLayoutAndRate`), and the query positions are those of the compiled run itself,
recorded by `recordQueries`, which rewrites a program to return its queries and changes nothing
else. The bytecode enters only through its length, as in `verifyDeferred`. A signature's hints are
its scheme's own definitions, over Keccak-f[1600] (as `LeanXmss.verifyWithKeccak` and
`Sphincs.verifyWithKeccak` take them).

Choices the witness does not fix, made as the Rust makes them:

* **Coverage slots** (`plan`, `take_slot`, `aggregation/coverage.rs:49-116`): the raw signatures
  first, in the witness's order (`NodeWitness.xmssSignatures`, `sphincsSignatures`; the Rust's
  sorted and deduplicated, `aggregation/node.rs:107-114`), then every child's claims, child by
  child; a claim takes its declared slot if it is still free, else the next duplicate slot. The
  deployed lists are strictly sorted, where the first free match is the slot `binary_search`
  finds.
* **A leaf's deferred value** (`leaf_defer`) is the statement's, which the guest does not check.

What the bump allocator hands out is not a hint: the interpreter's allocator chooses it.
-/

namespace LeanVM.Guest.Hints

open LeanVM.Guest.Coverage

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
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

/-- `CLAIM_GROUP` (`aggregation/statement.rs:11`): the claims a claim list's digest absorbs per
group. -/
def claimGroup : ℕ := 17

/-- `CLAIM_BIG` (`aggregation/statement.rs:14-15`): the claims the main list loop absorbs per frame,
`BIG_GROUPS = 8` groups. -/
def claimBig : ℕ := claimGroup * 8

/-- `DIGIT_GROUP` (`aggregation/hints.rs:15`): the leanSPHINCS codeword digits the guest dispatches
on at a time. -/
def digitGroup : ℕ := 3

/-- `LX_DIGIT_GROUP` (`aggregation/hints.rs:17`): the leanXMSS codeword digits the guest
dispatches on at a time. -/
def lxDigitGroup : ℕ := 4

/-- `LX_WINDOW` (`aggregation/hints.rs:19`): the leaf index bits a leanXMSS path dispatch covers. -/
def lxWindow : ℕ := 8

/-! ## Encodings -/

/-- `count(n)`: `g^n` (`aggregation/cells.rs:6-8`). -/
def count (n : ℕ) : E := gpowE n

/-- A bit as a word. -/
def bit (b : Bool) : E := if b then 1 else 0

/-- 16 bytes as a cell, limb `0` the first 8 (`pack_16_bytes`). -/
def cellOfBytes (b : List UInt8) : E := E.ofLimbs (kOfBytes b) (kOfBytes (b.drop 8))

/-- A byte string's 16-byte cells. -/
def cellsOfBytes (b : List UInt8) : List E :=
  (List.range (b.length / 16)).map fun i ↦ cellOfBytes (b.drop (16 * i))

/-- A 128-bit value as its cell. -/
def cell128 (v : BitVec 128) : E := cellOfBytes (HashSig.littleEndianBytes 16 v)

/-- A digest's two cells (`pack_hash_state`). -/
def digestCells (d : Digest) : Entry := [(digestHalves d).1, (digestHalves d).2]

/-- A claim's four cells: the key's two halves (leanXMSS: root, parameter; leanSPHINCS: `PK.seed`,
`PK.root`), the message (`claim_cells`, `aggregation/statement.rs:38-55`). -/
def claimCells (root parameter : BitVec 128) (message : BitVec 256) : Entry :=
  cellsOfBytes (claimBytesOf root parameter message)

/-- Bytes, each in the exponent (`exponent_bytes`, `aggregation/cells.rs:12-14`). -/
def exponentBytes (bytes : List UInt8) : Entry :=
  bytes.map fun b ↦ count b.toNat

/-- How a list of `n` claims splits into whole frames of `claimBig`, then whole groups of
`claimGroup`, then the rest (`list_split`, `aggregation/statement.rs:22-30`). -/
def listSplit (n : ℕ) : Entry :=
  [count (n / claimBig), count (n % claimBig / claimGroup), count (n % claimBig % claimGroup)]

/-- A list's split, if it is not empty, then one push per item. -/
def listPushes (item : String) (entries : List Entry) : List (String × Entry) :=
  (if entries = [] then [] else [("signers_split", listSplit entries.length)]) ++
    entries.map (item, ·)

/-- A codeword's digits as the guest dispatches on them: `size` at a time, then the rest, each
group's index little endian in base 4, in the exponent (`digit_hints`,
`aggregation/hints.rs:86-94`). -/
def digitHints (size : ℕ) (digits : List ℕ) : List Entry :=
  (List.range ((digits.length + size - 1) / size)).map fun i ↦
    [count (((digits.drop (size * i)).take size).foldr (· + 4 * ·) 0)]

/-- The leanSPHINCS digits' pushes: `digitGroup` at a time, one push each. -/
def digitGroups (digits : List ℕ) : List (String × Entry) :=
  (digitHints digitGroup digits).map ("digits", ·)

/-- The ordered children of a node and its sibling: the sibling first when `right`. -/
def ordered (right : Bool) (node sibling : BitVec 128) : Entry :=
  if right then [cell128 sibling, cell128 node] else [cell128 node, cell128 sibling]

/-! ## Coverage (`Region::plan`, `take_slot`) -/

/-! ## A leanXMSS signature (`lean_xmss_hints`) -/

/-- One layer's hints: the sibling of every node on the path, the randomizer, the codeword's
digits (`lxDigitGroup` at a time, one push) and the chain values; and the root the layer
reaches. -/
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
  -- `pair[index >> level & 1 == 0]` of the ordered children is the sibling.
  let siblings := (List.finRange LeanXmss.layerHeight).map fun l ↦
    ("lx_path", [cell128 (part.authenticationPath l)])
  let digits := (List.finRange LeanXmss.chainCount).map fun i ↦
    (HashSig.digestDigits digest i).val
  let starts := (List.finRange LeanXmss.chainCount).map fun i ↦
    ("chain_starts", [cell128 (part.chainValues i)])
  (siblings ++ [("randomizer", [cell128 part.randomizer]),
      ("lx_digits", (digitHints lxDigitGroup digits).flatten)] ++ starts,
    fold LeanXmss.layerHeight)

/-- A leanXMSS signature's hints: its leaf index shifted by each multiple of `lxWindow`, those
windows in the exponent, then each layer's, bottom first. -/
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
  ("lx_index", shifts.map fun x ↦ word x 0) ::
    ("lx_windows", shifts.map fun x ↦ count (x % 2 ^ lxWindow)) :: bottom ++ top

/-! ## A leanSPHINCS signature (`lean_sphincs_hints`) -/

/-- The bytes of `H_msg`'s two calls past its `34` (the second call's bytes `2` to `7`), each in the
exponent, one entry (`exponent_bytes(&digest[DIGEST_BYTES..SP_LANE_END])`, `SP_LANE_END = 40`,
`aggregation/hints.rs:40, 156-159`). -/
def sphincsUnusedEntry (outputs : Sphincs.DigestCall → HashSig.HashOutput) : Entry :=
  (List.range 6).map fun k ↦ count (Sphincs.digestValue outputs / 2 ^ (8 * (34 + k)) % 256)

/-- A counter's four bytes, most significant first, each in the exponent, one entry
(`exponent_bytes(&counter.to_be_bytes())`, `aggregation/hints.rs:173`). -/
def sphincsCounterEntry (counter : Sphincs.EncodingCounter) : Entry :=
  exponentBytes (Sphincs.bigEndianBytes 4 counter)

/-- One FORS tree's hints: the ordered children of every node on its climb, from the leaf up
(`fors_recover`'s visits, `fors.rs:94-102`). -/
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

/-- One layer's hints: the counter's bytes, the codeword's digits, the chain values and the
ordered children of every node on the key's path; and the root the layer reaches, which the layer
above signs. -/
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

/-- A leanSPHINCS signature's hints (`lean_sphincs_hints`, `aggregation/hints.rs:147-183`): the
randomizer, `H_msg`'s bytes past its `34`, every FORS tree's secret, every
tree's climb, then each layer's, bottom first, the bottom one-time key signing the FORS key and
each above the root below. -/
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

/-! ## LeanDA -/

/-- A blob matrix's hints: the claim's membership challenge, the row count and its padded log, and
every row's cells, column by column (`aggregation/node.rs:292-317`). The Rust pushes the root's
challenge (`membership_challenge`, `crates/verifier/src/da.rs:14-17`), the claim's on an honest
node. -/
def daHints (c : DaClaim) (w : Da.MatrixWitness) : List (String × Entry) :=
  [("da_challenge", [c.membershipChallenge]),
    ("da_shape", [count w.rows.length, count (LeanDa.logPaddedRowCount w.rows.length)])] ++
    (List.range LeanDa.cellsPerRow).flatMap fun j ↦
      w.rows.map fun row ↦ ("da_symbols", (LeanDa.listCell row j).map ofK)

/-! ## A child (`gen_verify`) -/

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

/-- The queries the deferring verifier makes on a child's proof (`verifyDeferredWith`), each with
the height of the commitment it opens. -/
def childQueries (bytecode : List K) (seed : Digest) (c : Child) : List (ℕ × List ℕ) :=
  match Id.run (Compile.run (m := Id) keccakF1600
      (recordQueries (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed
          c.statement)))
      (childVerifierStart seed c)) with
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

/-- A leaf's lanes as the guest's cells: level `0`'s a `K` lane each, a deeper level's an `E` word
of two lanes each (`aggregation/child.rs:193-204`). -/
def leafCells (first : Bool) (leaf : List K) : Entry :=
  if first then leaf.map ofK
  else (List.range (leaf.length / 2)).map fun i ↦
    E.ofLimbs (leaf.getD (2 * i) 0) (leaf.getD (2 * i + 1) 0)

/-- The bits of a query position the guest reads per window (`QUERY_WINDOW_BITS`). -/
def queryWindowBits : ℕ := 6

/-- A level's cap depth (`merkle_cap_depth`): whole windows below the root, the last ending from
`log2 count - 5` to five levels below that, and at least two levels deep. -/
def capDepthOf (count depth : ℕ) : ℕ :=
  let near := min (max (log2Ceil count - (queryWindowBits - 1)) 2) depth
  depth - (depth - near) / queryWindowBits * queryWindowBits

/-- One level's Merkle hints, from whether it is level `0`, its commitment's height, its query
count and its phase of openings: per opening its leaf's cells and the ordered children below the
cap, climbing from its leaf index (`merkle_leaf_rows`, `merkle_children`), then the level's cap
nodes and their parents' activity flags (`merkle_caps`, `merkle_cap_active`;
`aggregation/child.rs:184-232`). -/
def levelHints (first : Bool) (depth count : ℕ) (phase : List Opening) : List (String × Entry) :=
  let capDepth := capDepthOf count depth
  let pathDepth := depth - capDepth
  let climbs := phase.map fun o ↦
    (o, climbSteps (2 ^ depth + o.leafIndex) (merkleLeafDigest o.leaf) o.path)
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

/-- Every level's Merkle hints, each level with its phase of the proof's openings (the levels
zipped with `proof.merkle`), the first `first`. -/
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
(`block_groups`, `col_groups`, `aggregation/child.rs:57-74`). -/
def runGroups : ℕ → Option ℕ → List ℕ → List ℕ
  | _, _, [] => []
  | next, prev, k :: ks =>
      if prev = some k then (next - 1) :: runGroups next prev ks
      else next :: runGroups (next + 1) (some k) ks

/-- A bus block's kappa source, as a key (`block_kappa_sources`, `layout.rs:255-272`): the
framework's three blocks `(0, 0)`, `(1, 0)`, `(0, log_bytecode)`, a table's block its table. -/
def blockKey (b : BusBlock) : ℕ := 3 + b.owner

/-- Every side's block groups in layout order, each as `g` to its index over the three sides,
once per group, whose blocks are consecutive (`block_group_order`, `aggregation/child.rs:111-145`):
push and pull after the framework's three blocks, then count; a group is a maximal run of blocks
of one kappa source within a side. -/
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

/-- A global column's kappa source, as a key (`col_kappa_sources`, `layout.rs:211-238`): the
memory's two columns and `MFCNT` `(1, 0)`, `BFCNT` `(0, log_bytecode)`, `QKECCAK` its own, a
table's columns their table. -/
def colKey (c : ℕ) : ℕ :=
  if c < 3 then 0 else if c < 5 then c - 2 else 3 + (globalColumnBases.filter (· ≤ c)).length

/-- The committed columns' groups in stack order, each as `g` to its index, once per group,
whose columns are consecutive (`col_group_order`, `aggregation/child.rs:147-179`): a group is a
maximal run of committed columns, in their order, of one kappa source. -/
def colGroupOrder (layout : Layout) : Entry :=
  let columns := committedColumns layout
  let groups := runGroups 0 none (columns.map colKey)
  let offset := fun i ↦ (layout.placement (columns.getD i 0)).index
  (runHeads (((List.range columns.length).mergeSort fun i j ↦ offset i ≤ offset j).map
    (groups.getD · 0))).map count

/-- A child's hints (`gen_verify`): its proof stream, padded; the Merkle caps;
the tables' log heights; the two layout orders; and every query's leaf and path. -/
def childHints (bytecode : List K) (seed : Digest) (c : Child) : List (String × Entry) :=
  match announcedLayoutAndRate bytecode c.proof.stream with
  | none => []
  | some (layout, _) =>
    let queries := merkleHints true (childQueries bytecode seed c) c.proof.openings
    [("stream", c.proof.stream ++ List.replicate (childStreamCap - c.proof.stream.length) 0),
      ("zc_tau_max", [count (layout.tableLogHeights.foldl max 0)]),
      ("table_logs", layout.tableLogHeights.map count),
      ("col_group_order", colGroupOrder layout), ("block_group_order", blockGroupOrder layout)] ++
      queries

/-! ## The node (`aggregate_with_stats`) -/

/-- Whether a list is strictly increasing (`is_sorted_by(a < b)`). -/
def increasing : List ℕ → Bool
  | a :: b :: l => a < b && increasing (b :: l)
  | _ => true

/-- The gaps between strictly increasing slots, each from the slot after the previous one. -/
def slotGaps : ℕ → List ℕ → List ℕ
  | _, [] => []
  | next, o :: os => (o - next) :: slotGaps (o + 1) os

/-- A child's slots in one scheme's region, if any: the split, then, strictly increasing, the
flag `1` and the gaps (`child_claim_list_mono`), else the flag `0` and the slots
(`aggregation/node.rs:245-264`). -/
def childSlotPushes (offsets : List ℕ) : List (String × Entry) :=
  if offsets = [] then [] else
    ("signers_split", listSplit offsets.length) ::
      if increasing offsets then
        ("child_mono", [count 1]) :: (slotGaps 0 offsets).map fun d ↦ ("child_claim_gap", [count d])
      else ("child_mono", [count 0]) :: offsets.map fun o ↦ ("child_claim_index", [count o])

/-- The batching's hints: the proof of work's nonce, the sumcheck's rounds and the bytecode's value at
its end. -/
def batchPushes (h : BatchingHints) : List (String × Entry) :=
  [("bc_sumcheck_msgs", h.lambdaGrindNonce :: h.sumcheckMessages.flatMap fun r ↦ [r.1, r.2]),
    ("bc_star_hint", [h.finalBytecodeValue])]

/-- The DA digest the node publishes, as the slot of `da_digests` it picks (`da_pick`,
`aggregation/node.rs:88-104`): its own (`n`, the children's count) when it checks a matrix or
publishes zeros, else the first child whose DA digest it publishes. -/
def daPick (s : NodeStatement) (w : NodeWitness) : ℕ :=
  if w.daMatrix.isSome || s.claims.daDigest == zeroDigest then w.children.length
  else (w.children.findIdx? fun c ↦ c.statement.claims.daDigest == s.claims.daDigest).getD w.children.length

/-- **Every push of an honest run**, in the order `aggregate_with_stats` makes them. -/
def honestPushes (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    List (String × Entry) :=
  let rawX := w.xmssSignatures
  let rawS := w.sphincsSignatures
  let xr := coveragePlan s.claims.xmss (rawX.map (·.1)) (w.children.map (·.statement.claims.xmss))
  let sr := coveragePlan s.claims.sphincs (rawS.map (·.1)) (w.children.map (·.statement.claims.sphincs))
  let xCells := fun (c : LeanXmssClaim) ↦ claimCells c.1.root c.1.parameter c.2
  let sCells := fun (c : LeanSphincsClaim) ↦ claimCells c.1.publicSeed c.1.root c.2
  let slots := fun (offsets : List ℕ) ↦ childSlotPushes offsets
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
      slots xs ++ slots ss ++
      [("child_defer", c.statement.deferredClaim.cells), ("child_da", digestCells c.statement.claims.daDigest)] ++
      childHints bytecode seed c) ++
  (if w.children = [] then [("leaf_defer", [s.deferredClaim.bytecodeValue])] else batchPushes w.batchingHints) ++
  (w.daMatrix.map (fun c ↦ daHints c.1 c.2)).getD [] ++
  [("da_pick", [count (daPick s w)])]

/-- **The honest streams**: `honestPushes`, by stream. -/
def honestStreams (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Streams :=
  group (honestPushes bytecode seed s w)

/-- **The public input**, the initial memory at `g^0` and `g^1`: the statement's digest. -/
def publicInput (seed : Digest) (s : NodeStatement) : List E :=
  [(digestHalves (statementDigest seed s)).1, (digestHalves (statementDigest seed s)).2]

end
end LeanVM.Guest.Hints
