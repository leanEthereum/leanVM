import Rv64Verifier.Model.Whir
import Rv64Verifier.Model.Hash

/-!
# The opening's Merkle checks, as the image runs them

`Transcript::merkle`, inlined into `verify_stacked_opening`, on the bytes it hashes: a leaf's words
copied into a byte buffer and hashed (`hash_leaf`), then one `hash_pair` per sibling, the node left
or right by the leaf index's bit at that level (`MerklePath::root`), and the top compared with the
root by `memcmp`. `merkleRust` is the whole check on one phase of decoded openings, and
`merkleRust_run` says that wherever it returns, `TM.merkleLeaves` (the mirror's) returns the same
leaves, on a transcript whose root `i` is the root and shape the Rust uses.
-/

namespace Rv64Verifier.Model.Pcs
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash

/-! ## Bytes -/

/-- A digest's 32 bytes as the Rust holds them. -/
def digestBits (d : Digest) : List (BitVec 8) := byteBits (digestBytes d)

/-- `hash_pair`. -/
def hashPairBytes (l r : List (BitVec 8)) : List (BitVec 8) := keccakHashRust (l ++ r)

/-- One level of `MerklePath::root`: the node is the left child when the index's bit `j` is
clear. -/
def climbStep (index : BitVec 64) (j : ℕ) (node sib : List (BitVec 8)) : List (BitVec 8) :=
  if (index >>> (j % 64)) &&& 1#64 = 0#64 then hashPairBytes node sib else hashPairBytes sib node

/-- `MerklePath::root`'s climb, from level `j`. -/
def climbBytes (index : BitVec 64) : ℕ → List (BitVec 8) → List (List (BitVec 8)) →
    List (BitVec 8)
  | _, node, [] => node
  | j, node, sib :: sibs => climbBytes index (j + 1) (climbStep index j node sib) sibs

theorem climbBytes_snoc (index : BitVec 64) (sib : List (BitVec 8)) :
    ∀ (sibs : List (List (BitVec 8))) (j : ℕ) (node : List (BitVec 8)),
      climbBytes index j node (sibs ++ [sib]) =
        climbStep index (j + sibs.length) (climbBytes index j node sibs) sib
  | [], j, node => rfl
  | x :: xs, j, node => by
    simp only [List.cons_append, climbBytes, List.length_cons]
    rw [climbBytes_snoc index sib xs (j + 1)]
    congr 1
    omega

/-- The root of one path: the leaf's words hashed as bytes, then climbed. -/
def pathRootBytes (index : BitVec 64) (leaf : List K) (path : List (List (BitVec 8))) :
    List (BitVec 8) :=
  climbBytes index 0 (keccakHashRust (byteBits (leaf.flatMap K.toBytes))) path

theorem byteBits_append (a b : List UInt8) : byteBits (a ++ b) = byteBits a ++ byteBits b :=
  List.map_append

theorem bit_clear_iff {q j : ℕ} (hq : q < 2 ^ 64) (hj : j < 64) :
    (BitVec.ofNat 64 q >>> (j % 64)) &&& 1#64 = 0#64 ↔ q / 2 ^ j % 2 = 0 := by
  rw [Nat.mod_eq_of_lt hj, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.zero_mod]
  rw [show (1 % 18446744073709551616 : ℕ) = 1 from rfl, Nat.and_one_is_mod,
    Nat.mod_eq_of_lt (show q < 18446744073709551616 from hq)]

theorem climbBytes_digest {q : ℕ} (hq : q < 2 ^ 64) :
    ∀ (path : List Digest) (j : ℕ) (d : Digest), j + path.length ≤ 64 →
      climbBytes (BitVec.ofNat 64 q) j (digestBits d) (path.map digestBits) =
        digestBits (Id.run (climb (m := Id) keccakF1600 d (q / 2 ^ j) path))
  | [], _, _, _ => rfl
  | x :: xs, j, d, hl => by
    simp only [List.length_cons] at hl
    simp only [List.map_cons, climbBytes]
    have hstep : climbStep (BitVec.ofNat 64 q) j (digestBits d) (digestBits x) =
        digestBits (Id.run (keccak256With (m := Id) keccakF1600
          (if q / 2 ^ j % 2 = 0 then digestBytes d ++ digestBytes x
            else digestBytes x ++ digestBytes d))) := by
      unfold climbStep
      by_cases h : q / 2 ^ j % 2 = 0
      · rw [ite_eq_left ((bit_clear_iff hq (by omega)).mpr h), ite_eq_left h]
        simp only [hashPairBytes, digestBits, ← byteBits_append, keccakHashRust_eq]
        rfl
      · rw [ite_eq_right (fun h' ↦ h ((bit_clear_iff hq (by omega)).mp h')), ite_eq_right h]
        simp only [hashPairBytes, digestBits, ← byteBits_append, keccakHashRust_eq]
        rfl
    have hclimb : Id.run (climb (m := Id) keccakF1600 d (q / 2 ^ j) (x :: xs)) =
        Id.run (climb (m := Id) keccakF1600 (Id.run (keccak256With (m := Id) keccakF1600
          (if q / 2 ^ j % 2 = 0 then digestBytes d ++ digestBytes x
            else digestBytes x ++ digestBytes d))) (q / 2 ^ (j + 1)) xs) := by
      rw [show q / 2 ^ (j + 1) = q / 2 ^ j / 2 by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]]
      simp only [climb]
      split <;> rfl
    rw [hclimb, hstep, climbBytes_digest hq xs (j + 1) _ (by omega)]

/-- The bytes of a digest determine it. -/
theorem digestBits_inj {a b : Digest} (h : digestBits a = digestBits b) : a.toList = b.toList := by
  have ha := digestWordsRust_digestBytes a
  have hb := digestWordsRust_digestBytes b
  simp only [digestBits] at h
  rw [h] at ha
  rw [ha] at hb
  exact List.map_injective_iff.mpr (fun x y hxy ↦ UInt64.toBitVec_inj.mp hxy) hb

theorem pathRootBytes_eq {q : ℕ} (hq : q < 2 ^ 64) (leaf : List K) (path : List Digest)
    (hl : path.length ≤ 64) :
    pathRootBytes (BitVec.ofNat 64 q) leaf (path.map digestBits) =
      digestBits (Id.run (do
        let l ← keccak256With (m := Id) keccakF1600 (leaf.flatMap K.toBytes)
        climb (m := Id) keccakF1600 l q path)) := by
  unfold pathRootBytes
  rw [keccakHashRust_eq]
  have := climbBytes_digest hq path 0 (keccak256With (m := Id) keccakF1600 (leaf.flatMap K.toBytes))
    (by omega)
  simp only [Nat.pow_zero, Nat.div_one] at this
  exact this

/-! ## One phase -/

/-- `Transcript::merkle` in checked mode on one phase of openings, the root and the shape the Rust
passes: every leaf `leafWords` words and every path `log2_strict(block_length)` siblings, the leaf
indices the queries, every path climbing to the root. The leaves. -/
def merkleRust (root : Digest) (blockLength : BitVec 64) (queries : List (BitVec 64))
    (leafWords : ℕ) (phase : List Opening) : Option (List (List K)) :=
  match log2StrictRust blockLength with
  | none => none
  | some height =>
    if (∀ o ∈ phase, o.leaf.length = leafWords ∧ o.path.length = height) ∧
        phase.map (fun o ↦ BitVec.ofNat 64 o.leafIndex) = queries ∧
        ∀ o ∈ phase, pathRootBytes (BitVec.ofNat 64 o.leafIndex) o.leaf (o.path.map digestBits) =
          digestBits root
    then some (phase.map (·.leaf)) else none

theorem openAll_eq (root : Digest) (height width : ℕ) :
    ∀ phase : List Opening, (∀ o ∈ phase,
      Id.run (openOne (m := Id) keccakF1600 root height width o.leafIndex o) = true) →
      Id.run (openAll (m := Id) keccakF1600 root height width (phase.map (·.leafIndex)) phase) =
        some (phase.map (·.leaf), [])
  | [], _ => rfl
  | o :: os, h => by
    have h1 := h o (List.mem_cons_self ..)
    have h2 := openAll_eq root height width os fun o' ho' ↦ h o' (List.mem_cons_of_mem _ ho')
    simp only [Id.run] at h1 h2
    simp only [List.map_cons, openAll, Id.run, h1, h2]
    rfl

theorem log2StrictRust_lt {b : BitVec 64} {h : ℕ} (hb : log2StrictRust b = some h) : h < 64 := by
  unfold log2StrictRust at hb
  split at hb
  · cases hb
    have := BitVec.ctz_lt_iff_ne_zero.mpr (by tauto)
    exact this
  · cases hb

theorem leafIndex_eq {o : Opening} (ho : o.leafIndex < 2 ^ 64) {q : BitVec 64}
    (h : BitVec.ofNat 64 o.leafIndex = q) : o.leafIndex = q.toNat := by
  rw [← h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem map_leafIndex {phase : List Opening} (hb : ∀ o ∈ phase, o.leafIndex < 2 ^ 64) :
    ∀ {queries : List (BitVec 64)}, phase.map (fun o ↦ BitVec.ofNat 64 o.leafIndex) = queries →
      phase.map (·.leafIndex) = queries.map BitVec.toNat := by
  induction phase with
  | nil => intro queries h; subst h; rfl
  | cons o os ih =>
    intro queries h
    cases queries with
    | nil => cases h
    | cons q qs =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨leafIndex_eq (hb o (List.mem_cons_self ..)) h.1,
        ih (fun o' ho' ↦ hb o' (List.mem_cons_of_mem _ ho')) h.2⟩

/-- **Where the Rust's checks pass, the mirror's `merkle` returns the same leaves**, on commitment
`i` recorded with the root and the shape the Rust checks against. -/
theorem merkleRust_run {T : TState} {i : ℕ} {root : Digest} {blockLength : BitVec 64}
    {queries : List (BitVec 64)} {leafWords height : ℕ} {phase : List Opening}
    {rows : List (List K)}
    (hroot : T.roots[i]? = some (root, height, leafWords))
    (hheight : log2StrictRust blockLength = some height)
    (hphase : T.proof.openings[T.openingOffset]? = some phase)
    (hidx : ∀ o ∈ phase, o.leafIndex < 2 ^ 64)
    (h : merkleRust root blockLength queries leafWords phase = some rows) :
    (TM.merkleLeaves i queries leafWords).run T =
      some (rows, { T with openingOffset := T.openingOffset + 1 }) := by
  unfold merkleRust at h
  rw [hheight] at h
  simp only at h
  split at h
  swap
  · cases h
  rename_i hc
  obtain ⟨hshape, hpos, hroots⟩ := hc
  cases h
  have h64 := log2StrictRust_lt hheight
  have hpos' := map_leafIndex hidx hpos
  have hone : ∀ o ∈ phase,
      Id.run (openOne (m := Id) keccakF1600 root height leafWords o.leafIndex o) = true := by
    intro o ho
    obtain ⟨hw, hh⟩ := hshape o ho
    have hr := hroots o ho
    rw [pathRootBytes_eq (hidx o ho) o.leaf o.path (by omega)] at hr
    simp only [openOne, hw, hh, and_self, ite_true, Id.run]
    exact decide_eq_true (digestBits_inj hr)
  have hopen : Id.run (openPhase (m := Id) keccakF1600 root height leafWords
      (queries.map BitVec.toNat) phase) = some (phase.map (·.leaf)) := by
    unfold openPhase
    rw [ite_eq_left ⟨fun o ho ↦ hshape o ho, hpos'⟩, ← hpos']
    simp only [Id.run] at hone ⊢
    rw [show openAll (m := Id) keccakF1600 root height leafWords (List.map (·.leafIndex) phase) phase
      = some (phase.map (·.leaf), []) from openAll_eq root height leafWords phase hone]
    rfl
  simp only [TM.merkleLeaves, TM.merkle, StateT.run, bind, StateT.bind, hroot, hphase, hopen,
    TM.require, pure, StateT.pure]
  have hlen : ∀ row ∈ phase.map (·.leaf), row.length = leafWords := by
    intro row hrow
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hrow
    exact (hshape o ho).1
  simp only [Option.bind_some]
  rw [ite_eq_left hlen]
  rfl

end Rv64Verifier.Model.Pcs
