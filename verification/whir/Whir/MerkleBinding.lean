import Whir.Soundness

/-! Commitment-time query-table extraction, not an assumption that an arbitrary
root has a known full tree. `Bytes` is the actual hash-input type: leaves and
pairs need not be domain separated. The two codec injectivity obligations are
separate from cryptographic security. The Rust octopus decoder must still be
shown to produce the authenticated paths modeled here. -/
namespace Whir.MerkleBinding

variable {Row Digest Bytes : Type*}

structure Hashing (Row Digest Bytes : Type*) where
  hash : Bytes → Digest
  leaf : Row → Bytes
  pair : Digest × Digest → Bytes
  leaf_injective : Function.Injective leaf
  pair_injective : Function.Injective pair

inductive Opening (Row Digest : Type*) : List Bool → Type _ where
  | leaf (row : Row) : Opening Row Digest []
  | node (right : Bool) (sibling : Digest) {address : List Bool}
      (child : Opening Row Digest address) : Opening Row Digest (right :: address)

namespace Opening

def row {q : List Bool} : Opening Row Digest q → Row
  | .leaf r => r
  | .node _ _ p => p.row

def digest (H : Hashing Row Digest Bytes) {q : List Bool} : Opening Row Digest q → Digest
  | .leaf r => H.hash (H.leaf r)
  | .node b s p => H.hash (H.pair (if b then (s, p.digest H) else (p.digest H, s)))

def inputs [DecidableEq Bytes] (H : Hashing Row Digest Bytes) {q : List Bool} :
    Opening Row Digest q → Finset Bytes
  | .leaf r => {H.leaf r}
  | .node b s p => insert (H.pair (if b then (s, p.digest H) else (p.digest H, s))) (p.inputs H)

end Opening

/-- Semantic pruned multiproof: opaque sibling subtrees have only a digest, not
a fictitious known preimage. Shared internal nodes are represented once. Rust's
flat sorted-unique octopus still needs a decoding refinement to this datatype. -/
inductive Pruned (Stored Digest : Type*) where
  | hidden (digest : Digest)
  | leaf (stored : Stored)
  | branch (left right : Pruned Stored Digest)

namespace Pruned
variable {Stored : Type*}

def digest (H : Hashing Row Digest Bytes) (image : Stored → Row) :
    Pruned Stored Digest → Digest
  | .hidden d => d
  | .leaf r => H.hash (H.leaf (image r))
  | .branch l r => H.hash (H.pair (l.digest H image, r.digest H image))

/-- The returned opening contains the full leaf image. Prefix restoration
therefore occurs before hashing, and every duplicate query follows the same
shared tree rather than consuming another sibling from the transport. -/
def openPath (H : Hashing Row Digest Bytes) (image : Stored → Row) :
    (tree : Pruned Stored Digest) → (q : List Bool) → Option (Opening Row Digest q)
  | .hidden _, _ => none
  | .leaf r, [] => some (.leaf (image r))
  | .leaf _, _ :: _ => none
  | .branch _ _, [] => none
  | .branch l r, false :: q =>
    (l.openPath H image q).map (fun p => .node false (r.digest H image) p)
  | .branch l r, true :: q =>
    (r.openPath H image q).map (fun p => .node true (l.digest H image) p)

theorem openPath_authenticated (H : Hashing Row Digest Bytes) (image : Stored → Row)
    (tree : Pruned Stored Digest) (q : List Bool) (p : Opening Row Digest q)
    (opened : tree.openPath H image q = some p) : p.digest H = tree.digest H image := by
  induction tree generalizing q with
  | hidden d => simp [openPath] at opened
  | leaf r =>
    cases q with
    | nil =>
      simp only [openPath, Option.some.injEq] at opened
      subst p
      rfl
    | cons b q => simp [openPath] at opened
  | branch l r ihl ihr =>
    cases q with
    | nil => simp [openPath] at opened
    | cons b q =>
      cases b
      · simp only [openPath, Option.map_eq_some_iff] at opened
        obtain ⟨child, hc, he⟩ := opened
        subst p
        simp [Opening.digest, digest, ihl q child hc]
      · simp only [openPath, Option.map_eq_some_iff] at opened
        obtain ⟨child, hc, he⟩ := opened
        subst p
        simp [Opening.digest, digest, ihr q child hc]

end Pruned

/-- A real collision witness among inputs actually present in the table. -/
def Collision (H : Hashing Row Digest Bytes) (table : Finset Bytes) : Prop :=
  ∃ x ∈ table, ∃ y ∈ table, x ≠ y ∧ H.hash x = H.hash y

/-- Targets fixed at commitment: the root and the children of recorded pair
preimages. Pair-codec injectivity ensures there are at most `2 * table.card + 1`
such targets. No claim of a known full tree is made. -/
def Target (H : Hashing Row Digest Bytes) (table : Finset Bytes) (root d : Digest) : Prop :=
  d = root ∨ ∃ l r, H.pair (l, r) ∈ table ∧ (d = l ∨ d = r)

/-- A fresh query hitting a commitment-fixed target. This is a preimage game,
not collision resistance. Its ROM bound must charge the target count and all
post-commitment primitive queries, including verification. -/
def FreshHit (H : Hashing Row Digest Bytes) (table : Finset Bytes) (root : Digest)
    (queries : Finset Bytes) : Prop :=
  ∃ x ∈ queries, x ∉ table ∧ Target H table root (H.hash x)

variable [DecidableEq Bytes]

 theorem recorded_unique (H : Hashing Row Digest Bytes) (table : Finset Bytes)
    (safe : ¬ Collision H table) {q : List Bool} (a b : Opening Row Digest q)
    (ha : a.inputs H ⊆ table) (hb : b.inputs H ⊆ table)
    (same : a.digest H = b.digest H) : a.row = b.row := by
  have inj : ∀ x ∈ table, ∀ y ∈ table, H.hash x = H.hash y → x = y := by
    intro x hx y hy he
    by_contra hn
    exact safe ⟨x, hx, y, hy, hn, he⟩
  induction a with
  | leaf r =>
    cases b with
    | leaf s =>
      change r = s
      apply H.leaf_injective
      exact inj _ (ha (by simp [Opening.inputs])) _ (hb (by simp [Opening.inputs])) same
  | node d s a ih =>
    cases b with
    | node _ t b =>
      have hp := H.pair_injective (inj _ (ha (by simp [Opening.inputs]))
        _ (hb (by simp [Opening.inputs])) same)
      apply ih b
      · intro x hx; exact ha (by simp [Opening.inputs, hx])
      · intro x hx; exact hb (by simp [Opening.inputs, hx])
      · cases d
        · exact congrArg Prod.fst hp
        · exact congrArg Prod.snd hp

 theorem recorded_or_fresh (H : Hashing Row Digest Bytes) (table : Finset Bytes)
    (root : Digest) {q : List Bool} (p : Opening Row Digest q)
    (target : Target H table root (p.digest H)) :
    p.inputs H ⊆ table ∨ FreshHit H table root (p.inputs H) := by
  induction p with
  | leaf r =>
    by_cases h : H.leaf r ∈ table
    · left; simpa [Opening.inputs] using h
    · right; exact ⟨H.leaf r, by simp [Opening.inputs], h, target⟩
  | node b s p ih =>
    let x := H.pair (if b then (s, p.digest H) else (p.digest H, s))
    by_cases hx : x ∈ table
    · have childTarget : Target H table root (p.digest H) := by
        right
        cases b
        · exact ⟨p.digest H, s, hx, Or.inl rfl⟩
        · exact ⟨s, p.digest H, hx, Or.inr rfl⟩
      rcases ih childTarget with hc | ⟨y, hy, hn, ht⟩
      · left; simpa [Opening.inputs, x] using Finset.insert_subset hx hc
      · right; exact ⟨y, by simp [Opening.inputs, hy], hn, ht⟩
    · right; exact ⟨x, by simp [Opening.inputs, x], hx, target⟩

/-- The extractor sees only the commitment-time table, root, and address. It
chooses a fully recorded path if one exists, otherwise a fixed default row.
This is a mathematical extraction game; computational search cost is not hidden
in a claimed polynomial-time extraction theorem. -/
noncomputable def idealRow (H : Hashing Row Digest Bytes) (table : Finset Bytes)
    (root : Digest) (fallback : Row) (q : List Bool) : Row := by
  classical
  exact if h : ∃ p : Opening Row Digest q, p.inputs H ⊆ table ∧ p.digest H = root
    then h.choose.row else fallback

 theorem opening_to_ideal (H : Hashing Row Digest Bytes) (table : Finset Bytes)
    (root : Digest) (fallback : Row) {q : List Bool} (p : Opening Row Digest q)
    (accepted : p.digest H = root) :
    p.row = idealRow H table root fallback q ∨ Collision H table ∨
      FreshHit H table root (p.inputs H) := by
  classical
  by_cases hc : Collision H table
  · exact Or.inr (Or.inl hc)
  rcases recorded_or_fresh H table root p (Or.inl accepted) with hp | hf
  · left
    have hex : ∃ a : Opening Row Digest q, a.inputs H ⊆ table ∧ a.digest H = root := ⟨p, hp, accepted⟩
    simp only [idealRow, dite_eq_left hex]
    exact recorded_unique H table hc p hex.choose hp hex.choose_spec.1
      (accepted.trans hex.choose_spec.2.symm)
  · exact Or.inr (Or.inr hf)

/-- The same commitment-fixed oracle explains an entire batch, including
duplicate addresses. The reduction does not select a different oracle per row. -/
theorem batch_to_ideal (H : Hashing Row Digest Bytes) (table : Finset Bytes)
    (root : Digest) (fallback : Row) {I : Type*} (address : I → List Bool)
    (paths : ∀ i, Opening Row Digest (address i))
    (accepted : ∀ i, (paths i).digest H = root) :
    (∀ i, (paths i).row = idealRow H table root fallback (address i)) ∨
      Collision H table ∨ ∃ i, FreshHit H table root ((paths i).inputs H) := by
  classical
  by_cases hc : Collision H table
  · exact Or.inr (Or.inl hc)
  by_cases hf : ∃ i, FreshHit H table root ((paths i).inputs H)
  · exact Or.inr (Or.inr hf)
  left
  intro i
  rcases opening_to_ideal H table root fallback (paths i) (accepted i) with h | h | h
  · exact h
  · exact (hc h).elim
  · exact (hf ⟨i, h⟩).elim

/-- Decode pair inputs in the *commitment-time* table. This definition does not
enumerate or assume a full Merkle tree. -/
noncomputable def children (H : Hashing Row Digest Bytes) (x : Bytes) : Finset Digest := by
  classical
  exact if h : ∃ pair, H.pair pair = x then {h.choose.1, h.choose.2} else ∅

noncomputable def targets (H : Hashing Row Digest Bytes) (table : Finset Bytes)
    (root : Digest) : Finset Digest := by
  classical
  exact insert root (table.biUnion (children H))

omit [DecidableEq Bytes] in
theorem target_mem (H : Hashing Row Digest Bytes) (table : Finset Bytes)
    (root d : Digest) : Target H table root d ↔ d ∈ targets H table root := by
  classical
  simp only [Target, targets, Finset.mem_insert, Finset.mem_biUnion]
  constructor
  · rintro (h | ⟨l, r, hp, hd⟩)
    · exact Or.inl h
    · right
      refine ⟨H.pair (l, r), hp, ?_⟩
      have hex : ∃ pair, H.pair pair = H.pair (l, r) := ⟨(l, r), rfl⟩
      have he := H.pair_injective hex.choose_spec
      simpa [children, dite_eq_left hex, he] using hd
  · rintro (h | ⟨x, hx, hd⟩)
    · exact Or.inl h
    · right
      unfold children at hd
      split at hd
      next h =>
        refine ⟨h.choose.1, h.choose.2, ?_, ?_⟩
        · simpa only [h.choose_spec] using hx
        · simpa using hd
      next h => simp at hd

omit [DecidableEq Bytes] in
theorem targets_card (H : Hashing Row Digest Bytes) (table : Finset Bytes)
    (root : Digest) : (targets H table root).card ≤ 2 * table.card + 1 := by
  classical
  have hc : ∀ x, (children H x).card ≤ 2 := by
    intro x
    unfold children
    split
    · exact Finset.card_le_two
    · simp
  calc
    _ ≤ (table.biUnion (children H)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (∑ x ∈ table, (children H x).card) + 1 :=
      Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ _x ∈ table, 2) + 1 := Nat.add_le_add_right (Finset.sum_le_sum fun x _ => hc x) 1
    _ = _ := by simp [Nat.mul_comm]

omit [DecidableEq Bytes] in
/-- Conditional on an exposed commitment-time table, a fresh random-oracle
answer is uniform. This is the single-query multi-target preimage loss; a
resource-capped adaptive game accumulates it, not a collision-only assumption. -/
theorem fresh_target_probability [Fintype Digest] (H : Hashing Row Digest Bytes)
    (table : Finset Bytes) (root : Digest) :
    Soundness.uniformProb (targets H table root) ≤
      (2 * table.card + 1 : Nat) / (Fintype.card Digest : ℚ) := by
  unfold Soundness.uniformProb
  exact div_le_div_of_nonneg_right (by exact_mod_cast targets_card H table root) (by positivity)

/-- Leading absent lanes belong to the hashed image, not to the stored row. -/
def leafImage {Word : Type*} (zero : Word) (leafWords : Nat) (stored : List Word) : List Word :=
  List.replicate (leafWords - stored.length) zero ++ stored

 theorem leafImage_length {Word : Type*} (zero : Word) (n : Nat) (r : List Word)
    (fits : r.length ≤ n) : (leafImage zero n r).length = n := by
  simp [leafImage]; omega

 theorem leafImage_injective {Word : Type*} (zero : Word) (n width : Nat)
    {a b : List Word} (ha : a.length = width) (hb : b.length = width)
    (same : leafImage zero n a = leafImage zero n b) : a = b := by
  simp only [leafImage, ha, hb] at same
  exact List.append_cancel_left same

/-- Sorted-unique transport is only an optimization. Refan-out reads one fixed
entry at each occurrence and therefore preserves multiplicity and query order. -/
def refan {Address Value : Type*} (rows : Address → Value) (queries : List Address) : List Value :=
  queries.map rows

 theorem refan_ideal {Address Value : Type*} (rows ideal : Address → Value)
    (queries : List Address) (auth : ∀ q ∈ queries, rows q = ideal q) :
    refan rows queries = refan ideal queries := by
  exact List.map_congr_left auth

 theorem refan_repeat {Address Value : Type*} (rows : Address → Value) (q : Address) :
    refan rows [q, q] = [rows q, rows q] := rfl

/-- End-to-end semantic pruned-opening reduction, with the zero prefix inside
the hashed image. `I` indexes occurrences, not distinct addresses, so repeated
queries share the same commitment-fixed ideal answer. There is no assumption
that opaque sibling digests possess known preimages. -/
theorem padded_pruned_batch_to_ideal {Word I : Type*}
    (H : Hashing (List Word) Digest Bytes) (zero : Word) (leafWords : Nat)
    (table : Finset Bytes) (root : Digest) (fallback : List Word)
    (tree : Pruned (List Word) Digest) (address : I → List Bool)
    (paths : ∀ i, Opening (List Word) Digest (address i))
    (opened : ∀ i, tree.openPath H (leafImage zero leafWords) (address i) = some (paths i))
    (accepted : tree.digest H (leafImage zero leafWords) = root) :
    (∀ i, (paths i).row = idealRow H table root fallback (address i)) ∨
      Collision H table ∨ ∃ i, FreshHit H table root ((paths i).inputs H) := by
  apply batch_to_ideal H table root fallback address paths
  intro i
  exact (Pruned.openPath_authenticated H (leafImage zero leafWords) tree
    (address i) (paths i) (opened i)).trans accepted

/-! Security and refinement obligations:

The commitment-time table must record all primitive inputs exposed before the
commitment is fixed. The global real hash has no assumed injectivity. Failure is
an actual table collision or a fresh targeted preimage, with at most
`2 * table.card + 1` targets. In a lazy ROM, charge every later primitive call,
including honest verification; `fresh_target_probability` is the conditional
single-call bound. Concrete collision/preimage security is a separate game.

The ideal oracle is commitment-fixed, even for a malicious root with no known
full preimage. It uses arbitrary defaults only where the recorded table contains
no authenticated path; accessing such a default with a different accepted leaf
forces one of the explicit bad games. Efficient extraction requires efficient
leaf/pair decoding and bounded table/path resources.

The flat Rust octopus parser (width/range checks, exact sibling consumption,
sorted-unique reconstruction, and little-endian leaf/pair codecs) must be refined
to `Pruned`; this module does not claim that a handwritten tree model establishes
source correspondence. `leafImage` and `refan` fix the semantic padding and
duplicate-query conventions at that boundary.
-/

end Whir.MerkleBinding
