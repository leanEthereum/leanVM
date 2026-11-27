import Keccak256Proofs.Common

/-!
# The Merkle fold

`keccak256::path_root` folds a leaf and its path into a root with any node function: the
statement's `foldPath` (`path_root_fold`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)

namespace Keccak256Proofs

theorem ite_ok {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then ok a else ok b : RustM α) = ok (if c then a else b) := by
  split <;> rfl

theorem range_next_spec (i e : Std.Usize) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } ⦃ r =>
      (i.val < e.val ∧ ∃ s : Std.Usize, s.val = i.val + 1 ∧ r = (some i, { start := s, «end» := e })) ∨
      (e.val ≤ i.val ∧ r = (none, { start := i, «end» := e })) ⦄ := by
  have t := Hax.IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun r => ⌜(i.val < e.val ∧ ∃ s : Std.Usize, s.val = i.val + 1 ∧
      r = (some i, { start := s, «end» := e })) ∨ (e.val ≤ i.val ∧ r = (none, { start := i, «end» := e }))⌝)
    (fun h s hs => Or.inl ⟨h, s, hs, rfl⟩) (fun h => Or.inr ⟨h, rfl⟩)
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok t
  have hp := Hax.triple_noThrow_elim t hv
  exact spec_of_exists ⟨v, hv, hp⟩

/-- The statement's `foldPath` with a pure node function. -/
def foldId (nodeS : ℕ → ℕ → HashInput → Digest) (e : ℕ) (sib : ℕ → Digest) (n : ℕ) (v : Digest) :
    Digest :=
  Id.run (foldPath (m := Id) (fun l j p => pure (nodeS l j p)) e sib n v)

theorem foldId_zero (nodeS : ℕ → ℕ → HashInput → Digest) (e : ℕ) (sib : ℕ → Digest) (v : Digest) :
    foldId nodeS e sib 0 v = v := rfl

theorem foldId_succ (nodeS : ℕ → ℕ → HashInput → Digest) (e : ℕ) (sib : ℕ → Digest) (l : ℕ)
    (v : Digest) :
    foldId nodeS e sib (l + 1) v =
      nodeS l (e / 2 ^ (l + 1))
        (if e.testBit l then nodePayload (sib l) (foldId nodeS e sib l v)
        else nodePayload (foldId nodeS e sib l v) (sib l)) :=
  rfl

/-- `keccak256::path_root` with any node function: the statement's `foldPath`. -/
theorem path_root_fold {T1 : Type}
    (inst : core.ops.function.Fn T1 (Std.Usize × Std.Usize × Array (Array Std.U8 16#usize) 2#usize)
      (Array Std.U8 16#usize)) (nd : T1) (nodeS : ℕ → ℕ → HashInput → Digest)
    (leaf : Array Std.U8 16#usize) (e : Std.Usize) (path : Slice (Array Std.U8 16#usize))
    (hcall : ∀ (z j : Std.Usize) (ch : Array (Array Std.U8 16#usize) 2#usize), 1 ≤ z.val →
      z.val ≤ path.length → j.val ≤ e.val → ∃ r, inst.call nd (z, j, ch) = ok r ∧
        toDigest r = nodeS (z.val - 1) j.val (bytes ((ch.val.map Array.val).flatten)))
    (hlen : path.length ≤ 16) :
    ∃ r, keccak256.path_root inst leaf e path nd = ok r ∧
      toDigest r = foldId nodeS e.val (fun z => toDigest path.val[z]!) path.length (toDigest leaf) := by
  apply WP.spec_imp_exists
  unfold keccak256.path_root
  have hl : core.slice.Slice.len path = ok path.len := by
    simp [core.slice.Slice.len, rust_primitives.slice.slice_length]
  rw [hl]
  simp only [Aeneas.Std.bind_ok]
  unfold keccak256.path_root_loop
  apply loop.spec_decr_nat (fun x => x.1.«end».val - x.1.start.val)
    (fun x => x.1.«end» = path.len ∧ x.1.start.val ≤ path.length ∧
      toDigest x.2 = foldId nodeS e.val (fun z => toDigest path.val[z]!) x.1.start.val (toDigest leaf))
  · rintro ⟨⟨i, en⟩, cur⟩ ⟨hen, hi, hcur⟩
    simp only at hen hi hcur
    subst hen
    unfold keccak256.path_root_loop.body
    have hplen : path.len.val = path.length := Slice.len_val path
    step with range_next_spec as ⟨r, it, hnext⟩
    rcases hnext with ⟨hlt, s, hs, rfl, rfl⟩ | ⟨hge, rfl, rfl⟩
    · simp only
      have hil : i.val < path.length := by omega
      step as ⟨sib, hsib⟩
      step as ⟨i0, hi0⟩
      · have := numBits_ge; omega
      simp only [lift, ite_ok, Aeneas.Std.bind_ok]
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      · have := numBits_ge; omega
      obtain ⟨r, hr, hv⟩ := hcall i2 i3
        (if i0 &&& 1#usize = 0#usize then Array.make 2#usize [cur, sib] (by rfl)
          else Array.make 2#usize [sib, cur] (by rfl)) (by omega) (by omega)
        (by rw [hi3]; exact Nat.shiftRight_le _ _)
      rw [hr]
      simp only [Aeneas.Std.bind_ok, WP.spec_ok]
      refine ⟨trivial, by omega, ?_, by omega⟩
      rw [hv, hs, foldId_succ, ← hcur]
      have h1 : i2.val - 1 = i.val := by omega
      have h3 : i3.val = e.val / 2 ^ (i.val + 1) := by rw [hi3, hi2, Nat.shiftRight_eq_div_pow]
      have hsibv : toDigest (path.val[i.val]!) = toDigest sib := by
        rw [getElem!_pos path.val i.val hil]; subst sib; rfl
      rw [h1, h3, hsibv]
      congr 1
      have hbit : (i0 &&& 1#usize = 0#usize) ↔ e.val.testBit i.val = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, ← hi0]
        constructor
        · intro h
          have := congrArg UScalar.val h
          simp only [UScalar.val_and] at this
          simp at this
          simp [this]
        · intro h
          apply UScalar.eq_of_val_eq
          simp only [UScalar.val_and]
          simp at h ⊢
          omega
      by_cases hb : i0 &&& 1#usize = 0#usize
      · simp [hb, hbit.mp hb, nodePayload, littleEndianBytes_toDigest, bytes]
      · have : e.val.testBit i.val = true := by
          cases h : e.val.testBit i.val
          · exact absurd (hbit.mpr h) hb
          · rfl
        simp [hb, this, nodePayload, littleEndianBytes_toDigest, bytes]
    · simp only [WP.spec_ok]
      have : i.val = path.length := by omega
      rw [hcur, this]
  · exact ⟨rfl, by simp, by simp [foldId_zero]⟩

theorem foldId_congr (nodeS : ℕ → ℕ → HashInput → Digest) (e : ℕ) (sib sib' : ℕ → Digest) (n : ℕ)
    (v : Digest) (h : ∀ z, z < n → sib z = sib' z) : foldId nodeS e sib n v = foldId nodeS e sib' n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldId_succ, foldId_succ, ih (fun z hz => h z (by omega)), h n (by omega)]

theorem foldId_eq_foldPath (node : ℕ → ℕ → HashInput → Id Digest) (e : ℕ) (sib : ℕ → Digest) (n : ℕ)
    (v : Digest) :
    foldId (fun l j p => Id.run (node l j p)) e sib n v = Id.run (foldPath node e sib n v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [foldId_succ, ih]; rfl

end Keccak256Proofs
