module

public import LeanVMCircuits.Rec.HashPorts

@[expose] public section

/-!
One-block BLAKE2s-256 hash rows, and Merkle paths of them.

A hash row whose chaining value is the public parameter IV and whose counter and finalization columns are the
public `(64, 0xFFFFFFFF)` hashes its message with BLAKE2s-256 as RFC 7693 section 3.3 defines it, the message one
64-byte block. A Merkle node is such a row whose message is its two children, the accumulated one placed by the
row's Boolean bit; a path of them, each node's output the next one's accumulated child, computes the root of the
leaf and the siblings the rows hold.
-/

namespace LeanVMCircuits.Rec

open LeanVMCircuits.Blake2s Rfc7693

attribute [local irreducible] program

/-- RFC 7693 section 3.3: the parameter block of an unkeyed 32-byte digest, XORed into `h0`. -/
def paramIV : Vector (BitVec 32) 8 := IV.set 0 (IV[0] ^^^ 0x01010020)

/-- RFC 7693 section 3.3 with `kk = 0` and `nn = 32`: BLAKE2s-256 of a message of one 64-byte block. -/
def hash64 (block : Vector (BitVec 32) 16) : Vector (BitVec 32) 8 := F paramIV block 64 true

/-- A digest as four 64-bit words, word `k` holding 32-bit words `2k` (low) and `2k + 1`. -/
def digest (h : Vector (BitVec 32) 8) (k : Fin 4) : BitVec 64 :=
  h[2 * k.val + 1]'(by omega) ++ h[2 * k.val]'(by omega)

theorem half_digest (h : Vector (BitVec 32) 8) (k : Fin 4) (s : ℕ) (hs : s < 2) :
    half (digest h k) s = h[2 * k.val + s]'(by omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · simp only [half, digest, Nat.mul_zero, BitVec.ushiftRight_zero]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
    simp [hi]
  · simp only [half, digest, Nat.mul_one]
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    simp [hi, show ¬ (32 + i < 32) by omega]

/-- The 16 message words of two digests, `left` first. -/
def pair (left right : Fin 4 → BitVec 64) : Vector (BitVec 32) 16 :=
  Vector.ofFn fun r => half (if h : r.val < 8 then left ⟨r.val / 2, by omega⟩ else right ⟨r.val / 2 - 4, by omega⟩)
    (r.val % 2)

/-- RFC 7693's hash of a Merkle node: BLAKE2s-256 of its two children. -/
def node (left right : Fin 4 → BitVec 64) : Fin 4 → BitVec 64 := digest (hash64 (pair left right))

theorem eq_of_halves (a b : BitVec 64) (h0 : half a 0 = half b 0) (h1 : half a 1 = half b 1) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlow : i < 32
  · have := congrArg (·.getLsbD i) h0
    simpa [half, BitVec.getLsbD_setWidth, hlow] using this
  · have := congrArg (·.getLsbD (i - 32)) h1
    simp only [half, Nat.mul_one, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show i - 32 < 32 by omega, decide_true, Bool.true_and, show 32 + (i - 32) = i by omega] at this
    exact this

theorem eq_digest (O : Fin 4 → BitVec 64) (h : Vector (BitVec 32) 8)
    (hhalf : ∀ r : Fin 8, half (O ⟨r.val / 2, by omega⟩) (r.val % 2) = h[r]) (k : Fin 4) : O k = digest h k := by
  apply eq_of_halves
  · rw [half_digest h k 0 (by omega)]
    have := hhalf ⟨2 * k.val, by omega⟩
    simp only [Fin.getElem_fin] at this
    rw [show (⟨(2 * k.val) / 2, by omega⟩ : Fin 4) = k by ext; simp, show 2 * k.val % 2 = 0 by omega] at this
    simpa using this
  · rw [half_digest h k 1 (by omega)]
    have := hhalf ⟨2 * k.val + 1, by omega⟩
    simp only [Fin.getElem_fin] at this
    rw [show (⟨(2 * k.val + 1) / 2, by omega⟩ : Fin 4) = k by ext; simp; omega,
      show (2 * k.val + 1) % 2 = 1 by omega] at this
    exact this

/-- The four 64-bit words of four `K` limbs. -/
noncomputable def words4 (acc : Fin 4 → K) (k : Fin 4) : BitVec 64 := BitVec.ofNat 64 (toWord (acc k))

/-- A hash row's output words. -/
noncomputable def outWords (row : ℕ → K) : Fin 4 → BitVec 64 := words4 fun k => row (hashO + k)

/-- A hash row's message words. -/
noncomputable def msg (row : ℕ → K) : Vector (BitVec 32) 16 := mWords fun j => columnWord row j

/-- The finalization word's low half: all ones on a final block. -/
def finalWord (f : Bool) : BitVec 32 := if f then BitVec.allOnes 32 else 0

/-- A hash row: its identities hold, and a packed witness satisfying the exported BLAKE2s artifact has its columns'
words as ports. -/
structure HashRow (row : ℕ → K) : Prop where
  witness : ∃ a, Compress.artifact.Holds a ∧ Export.ports a = (portsOf fun j => columnWord row j) ∧
    Export.result a = resultOf fun k => columnWord row (hashO + k)
  identities : ∀ id ∈ hashIdentities, id.eval row = 0

theorem hWords_digest (row : ℕ → K) (h : Vector (BitVec 32) 8)
    (hh : ∀ k : Fin 4, columnWord row (hashH + k) = digest h k) : hWords (fun j => columnWord row j) = h := by
  apply Vector.ext
  intro i hi
  simp only [hWords, Vector.getElem_ofFn]
  have := hh ⟨i / 2, by omega⟩
  simp only [hashH] at this
  rw [show (2 : ℕ) + i / 2 = 2 + (⟨i / 2, by omega⟩ : Fin 4).val from rfl, this,
    half_digest h ⟨i / 2, by omega⟩ (i % 2) (Nat.mod_lt _ (by norm_num))]
  congr 1
  simp only
  omega

/-- A hash row outputs RFC 7693's compression of the chaining value its columns hold and its message columns, at its
counter column and finalization. -/
theorem hash_row_digest (row : ℕ → K) (hr : HashRow row) (h : Vector (BitVec 32) 8)
    (hh : ∀ k : Fin 4, columnWord row (hashH + k) = digest h k) (f : Bool)
    (hf : (columnWord row hashF).setWidth 32 = finalWord f) :
    outWords row = digest (F h (msg row) (columnWord row hashT) f) := by
  obtain ⟨a, hholds, hin, hout⟩ := hr.witness
  funext k
  apply eq_digest (fun k => columnWord row (hashO + k)) _ _ k
  intro r
  have := hash_row_compress row a hholds hin hout f hf r
  rw [hWords_digest row h hh] at this
  exact this

/-- RFC 7693 section 3.3 from chaining value `h` with `i` blocks absorbed: block `m` and then `rest`, the last at
byte count `ll` and final, each before it at its own end's byte count. -/
def blocksFrom (ll : BitVec 64) : Vector (BitVec 32) 8 → ℕ → Vector (BitVec 32) 16 →
    List (Vector (BitVec 32) 16) → Vector (BitVec 32) 8
  | h, _, m, [] => F h m ll true
  | h, i, m, m' :: rest => blocksFrom ll (F h m (BitVec.ofNat 64 (64 * (i + 1))) false) (i + 1) m' rest

/-- RFC 7693 section 3.3 with `kk = 0`, `nn = 32`: BLAKE2s-256 of the `ll`-byte message whose zero-padded blocks are
`m` and then `rest`. -/
def blake2s256 (ll : BitVec 64) (m : Vector (BitVec 32) 16) (rest : List (Vector (BitVec 32) 16)) :
    Vector (BitVec 32) 8 :=
  blocksFrom ll paramIV 0 m rest

theorem hash64_eq (m : Vector (BitVec 32) 16) : hash64 m = blake2s256 64 m [] := rfl

/-- The non-final compressions of `blocksFrom`. -/
def absorb : Vector (BitVec 32) 8 → ℕ → List (Vector (BitVec 32) 16) → Vector (BitVec 32) 8
  | h, _, [] => h
  | h, i, m :: rest => absorb (F h m (BitVec.ofNat 64 (64 * (i + 1))) false) (i + 1) rest

/-- A message's leading blocks fold into the chaining value its later blocks start from. -/
theorem blocksFrom_append (ll : BitVec 64) (pre : List (Vector (BitVec 32) 16)) (h : Vector (BitVec 32) 8) (i : ℕ)
    (m : Vector (BitVec 32) 16) (rest : List (Vector (BitVec 32) 16)) :
    blocksFrom ll h i (pre.headD m) (pre.tail ++ (if pre = [] then rest else m :: rest)) =
      blocksFrom ll (absorb h i pre) (i + pre.length) m rest := by
  induction pre generalizing h i with
  | nil => simp [absorb]
  | cons p ps ih =>
    cases ps with
    | nil => simp [blocksFrom, absorb]
    | cons q qs =>
      simp only [List.headD_cons, List.tail_cons, List.cons_append, reduceCtorEq, if_false, blocksFrom] at ih ⊢
      rw [ih]
      simp only [absorb, List.length_cons]
      congr 1
      omega

/-- The rows of one message's blocks: each a hash row at its byte count, the last final, and each one's chaining
value the previous one's output. -/
def ChainFrom (ll : BitVec 64) : ℕ → (ℕ → K) → List (ℕ → K) → Prop
  | _, row, [] => HashRow row ∧ columnWord row hashT = ll ∧ (columnWord row hashF).setWidth 32 = finalWord true
  | i, row, next :: rest => HashRow row ∧ columnWord row hashT = BitVec.ofNat 64 (64 * (i + 1)) ∧
      (columnWord row hashF).setWidth 32 = finalWord false ∧ (∀ k : Fin 4, next (hashH + k) = row (hashO + k)) ∧
      ChainFrom ll (i + 1) next rest

/-- The last of a row and those after it. -/
def lastRow : (ℕ → K) → List (ℕ → K) → ℕ → K
  | row, [] => row
  | _, next :: rest => lastRow next rest

/-- A chain of hash rows outputs RFC 7693's hash of its message columns. -/
theorem chain_digest (ll : BitVec 64) (i : ℕ) (row : ℕ → K) (rest : List (ℕ → K)) (h : Vector (BitVec 32) 8)
    (hc : ChainFrom ll i row rest) (hh : ∀ k : Fin 4, columnWord row (hashH + k) = digest h k) :
    outWords (lastRow row rest) = digest (blocksFrom ll h i (msg row) (rest.map msg)) := by
  induction rest generalizing i row h with
  | nil =>
    obtain ⟨hr, ht, hf⟩ := hc
    rw [lastRow, List.map_nil, blocksFrom, hash_row_digest row hr h hh true hf, ht]
  | cons next rest ih =>
    obtain ⟨hr, ht, hf, hlink, hc⟩ := hc
    rw [lastRow, List.map_cons, blocksFrom]
    apply ih (i + 1) next _ hc
    intro k
    have := congrFun (hash_row_digest row hr h hh false hf) k
    rw [ht] at this
    simp only [columnWord, hlink k]
    exact this

/-- The message a Merkle row hashes: `acc` and the row's other half, `acc` first at bit 0. -/
theorem node_message (row : ℕ → K) (hid : ∀ id ∈ hashIdentities, id.eval row = 0) (acc : Fin 4 → K)
    (hmux : ∀ i : Fin 4, limbs hash hashSlotMux row i = acc i) :
    (row hashSel = 0 ∧ mWords (fun j => columnWord row j) =
        pair (words4 acc) fun i => columnWord row (hashM + 4 + i)) ∨
      (row hashSel = 1 ∧ mWords (fun j => columnWord row j) =
        pair (fun i => columnWord row (hashM + i)) (words4 acc)) := by
  rcases node_row row hid acc hmux with ⟨h0, hacc⟩ | ⟨h1, hacc⟩
  · refine Or.inl ⟨h0, ?_⟩
    apply Vector.ext
    intro r hr
    simp only [mWords, pair, Vector.getElem_ofFn]
    split
    · rename_i hlt
      have := hacc ⟨r / 2, by omega⟩
      simp only [words4, columnWord, ← this, hashM]
    · rename_i hge
      simp only [columnWord, hashM]
      congr 3
      congr 1
      omega
  · refine Or.inr ⟨h1, ?_⟩
    apply Vector.ext
    intro r hr
    simp only [mWords, pair, Vector.getElem_ofFn]
    split
    · simp only [columnWord, hashM]
    · rename_i hge
      have := hacc ⟨r / 2 - 4, by omega⟩
      simp only [words4, columnWord, ← this, hashM]
      congr 3
      congr 1
      omega

/-- RFC 7693's root of a Merkle path: each step hashes the accumulated digest with its sibling, the sibling first
when the step's bit is set. -/
def pathRoot (leaf : Fin 4 → BitVec 64) : List (Bool × (Fin 4 → BitVec 64)) → Fin 4 → BitVec 64
  | [] => leaf
  | p :: rest => pathRoot (if p.1 then node p.2 leaf else node leaf p.2) rest

/-- A Merkle node's row: a satisfying packed witness whose ports are its columns, the public parameter IV, counter
64 and final word in its head, and its mux slot held to `acc`. -/
structure NodeRow (row : ℕ → K) (acc : Fin 4 → K) : Prop where
  hashRow : HashRow row
  iv : ∀ k : Fin 4, columnWord row (hashH + k) = digest paramIV k
  counter : columnWord row hashT = 64
  final : (columnWord row hashF).setWidth 32 = finalWord true
  mux : ∀ i : Fin 4, limbs hash hashSlotMux row i = acc i

/-- The bit and sibling a node's row holds: the mux bit, and the message half `acc` is not in. -/
noncomputable def step (row : ℕ → K) : Bool × (Fin 4 → BitVec 64) :=
  if row hashSel = 1 then (true, fun i => columnWord row (hashM + i)) else (false, fun i => columnWord row (hashM + 4 + i))

/-- A node's row outputs the node of `acc` and its sibling, in the order its bit gives. -/
theorem node_row_digest (row : ℕ → K) (acc : Fin 4 → K) (h : NodeRow row acc) :
    outWords row = if (step row).1 then node (step row).2 (words4 acc) else node (words4 acc) (step row).2 := by
  rw [hash_row_digest row h.hashRow paramIV h.iv true h.final, h.counter]
  rcases node_message row h.hashRow.identities acc h.mux with ⟨h0, hm⟩ | ⟨h1, hm⟩
  · have : row hashSel ≠ 1 := by rw [h0]; exact zero_ne_one
    rw [step, if_neg this]
    simp only [node, hm, Bool.false_eq_true, if_false, hash64, msg]
  · rw [step, if_pos h1]
    simp only [node, hm, if_true, hash64, msg]

/-- The digest a chain of node rows ends on. -/
def pathEnd (acc : Fin 4 → K) : List (ℕ → K) → Fin 4 → K
  | [] => acc
  | row :: rest => pathEnd (fun k => row (hashO + k)) rest

/-- Node rows each taking the one before's output as its accumulated child. -/
def Chained (acc : Fin 4 → K) : List (ℕ → K) → Prop
  | [] => True
  | row :: rest => NodeRow row acc ∧ Chained (fun k => row (hashO + k)) rest

/-- A Merkle path in rows ends on the root RFC 7693 gives for its leaf and the steps its rows hold. -/
theorem path_root (leaf : Fin 4 → K) (rows : List (ℕ → K)) (h : Chained leaf rows) :
    words4 (pathEnd leaf rows) = pathRoot (words4 leaf) (rows.map step) := by
  induction rows generalizing leaf with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨hrow, hrest⟩ := h
    rw [pathEnd, List.map_cons, pathRoot, ih _ hrest, ← node_row_digest row leaf hrow]
    rfl

/-- An opened leaf hashed in rows and then up a path in rows reaches the node RFC 7693 gives for the leaf's
message columns and the path's steps. -/
theorem opening_node (ll : BitVec 64) (i : ℕ) (row : ℕ → K) (rest : List (ℕ → K)) (h : Vector (BitVec 32) 8)
    (hc : ChainFrom ll i row rest) (hh : ∀ k : Fin 4, columnWord row (hashH + k) = digest h k) (nodes : List (ℕ → K))
    (hp : Chained (fun k => lastRow row rest (hashO + k)) nodes) :
    words4 (pathEnd (fun k => lastRow row rest (hashO + k)) nodes) =
      pathRoot (digest (blocksFrom ll h i (msg row) (rest.map msg))) (nodes.map step) := by
  rw [path_root _ _ hp, ← chain_digest ll i row rest h hc hh]
  rfl

/-- `parent`: a node's row whose bit is zero and whose message's second half is `right`. -/
structure ParentRow (row : ℕ → K) (left right : Fin 4 → K) : Prop where
  nodeRow : NodeRow row left
  bit : row hashSel = 0
  right : ∀ i : Fin 4, row (hashM + 4 + i) = right i

/-- A parent's row outputs RFC 7693's node of its two children. -/
theorem parent_row_digest (row : ℕ → K) (left right : Fin 4 → K) (h : ParentRow row left right) :
    outWords row = node (words4 left) (words4 right) := by
  have hs : step row = (false, words4 right) := by
    have : row hashSel ≠ 1 := by rw [h.bit]; exact zero_ne_one
    rw [step, if_neg this]
    refine Prod.ext rfl (funext fun i => ?_)
    simp only [words4, columnWord, h.right i]
  rw [node_row_digest row left h.nodeRow, hs]
  rfl

/-- A parent's second child through a `CAST` row: the hash row's `x` and `ds` slots held to the cast row's element
and last word, its digest slot to `right`. -/
theorem parent_right (row crow : ℕ → K) (right : Fin 4 → K)
    (hx : ∀ i : Fin 3, limbs hash hashSlotX row i = limbs cast castElement crow i) (hds : limbs hash hashSlotDs row 0 = limbs cast (castWords + 3) crow 0)
    (hd : ∀ i : Fin 4, limbs cast castDigest crow i = right i) : ∀ i : Fin 4, row (hashM + 4 + i) = right i := by
  intro i
  fin_cases i
  · exact (hx 0).trans (hd 0)
  · exact (hx 1).trans (hd 1)
  · exact (hx 2).trans (hd 2)
  · exact hds.trans (hd 3)

/-- The node `d` levels above leaves `leaf`, `j`-th from the left. -/
def treeNode (leaf : ℕ → Fin 4 → BitVec 64) : ℕ → ℕ → Fin 4 → BitVec 64
  | 0, j => leaf j
  | d + 1, j => node (treeNode leaf d (2 * j)) (treeNode leaf d (2 * j + 1))

/-- Parent rows over the levels of a subtree of height `top`, node `j` of level `s` (the root's level `0`) the output
of the parent row of nodes `2j` and `2j + 1` of level `s + 1`, compute the subtree RFC 7693 gives for its bottom
level. -/
theorem tree_nodes (top : ℕ) (nodes : ℕ → ℕ → Fin 4 → K) (rows : ℕ → ℕ → ℕ → K)
    (hrows : ∀ s j, s < top → j < 2 ^ s →
      ParentRow (rows s j) (nodes (s + 1) (2 * j)) (nodes (s + 1) (2 * j + 1)) ∧
        ∀ k : Fin 4, rows s j (hashO + k) = nodes s j k) :
    ∀ d ≤ top, ∀ j < 2 ^ (top - d), words4 (nodes (top - d) j) = treeNode (fun j => words4 (nodes top j)) d j := by
  intro d
  induction d with
  | zero => intro _ j _; rfl
  | succ d ih =>
    intro hd j hj
    obtain ⟨hp, hout⟩ := hrows (top - (d + 1)) j (by omega) hj
    have hs : top - (d + 1) + 1 = top - d := by omega
    rw [hs] at hp
    have hpow : 2 ^ (top - d) = 2 * 2 ^ (top - (d + 1)) := by rw [← hs, pow_succ]; ring
    rw [treeNode, ← ih (by omega) (2 * j) (by omega), ← ih (by omega) (2 * j + 1) (by omega),
      ← parent_row_digest _ _ _ hp]
    funext k
    simp only [outWords, words4, hout k]

/-- The root of parent rows over a subtree of height `top`. -/
theorem tree_root (top : ℕ) (nodes : ℕ → ℕ → Fin 4 → K) (rows : ℕ → ℕ → ℕ → K)
    (hrows : ∀ s j, s < top → j < 2 ^ s →
      ParentRow (rows s j) (nodes (s + 1) (2 * j)) (nodes (s + 1) (2 * j + 1)) ∧
        ∀ k : Fin 4, rows s j (hashO + k) = nodes s j k) :
    words4 (nodes 0 0) = treeNode (fun j => words4 (nodes top j)) top 0 := by
  have := tree_nodes top nodes rows hrows top le_rfl 0 (by simp)
  rwa [Nat.sub_self] at this

end LeanVMCircuits.Rec
