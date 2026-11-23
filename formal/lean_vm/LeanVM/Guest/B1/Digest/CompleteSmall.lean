/-
  LeanVM.Guest.B1.Digest.CompleteSmall

  Completeness of the small digest functions: a meaning (and the memory an honest run reads) gives
  the core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.Range
public import LeanVM.Guest.B1.Sig.CwComplete

/-!
# Small functions, completely

* `memOK_of_image`: a memory image of `2^κ` words is defined at every `g^i`, `i < 2^κ`.
  (B1-e's `MemOK`), so a range check of `g^k` against `g^(K-1)`, `K ≤ 2^16`, reads defined words
  (`rc_holds`);
* `list_split_complete : list_split_complete_Spec`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem memOK_of_image {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) : Sig.MemOK L.read (2 ^ κ) := by
  intro i hi
  exact Option.isSome_iff_exists.mpr ⟨L ⟨i, hi⟩, (read_some_iff (by omega) L _ _).mpr ⟨⟨i, hi⟩, rfl, rfl⟩⟩

/-- **A range check of `g^k` against `g^K` holds** on a memory defined below `2^16`, `k ≤ K < 2^16`,
its witness `g^(K - k)`. -/
theorem rc_holds' (hm : Sig.MemOK rd (2 ^ 16)) {k K : ℕ} (hk : k ≤ K) (hK : K < 2 ^ 16) :
    ∃ t1 t2, LoadHolds rd (gen ^ k) 0 t1 ∧ gen ^ K = gen ^ k * gen ^ (K - k) ∧
      LoadHolds rd (gen ^ (K - k)) 0 t2 := by
  obtain ⟨t1, h1⟩ : ∃ w, LoadHolds rd (gen ^ k) 0 w := by
    rw [gen_pow_eq_ofK]; exact Sig.load_gpow hm (show k < 2 ^ 16 by omega)
  obtain ⟨t2, h2⟩ : ∃ w, LoadHolds rd (gen ^ (K - k)) 0 w := by
    rw [gen_pow_eq_ofK]; exact Sig.load_gpow hm (show K - k < 2 ^ 16 by omega)
  exact ⟨t1, t2, h1, by rw [← pow_add]; congr 1; omega, h2⟩

/-- **`list_split` is complete** on a memory defined below `2^20`. -/
theorem list_split_complete' (rd : Reader) (hm : Sig.MemOK rd (2 ^ 20)) (args rets : List E)
    (h : MeaningListSplitC args rets) : coreProgram.Rel rd "list_split" args rets := by
  match args, h with
  | [ng], h =>
    obtain ⟨a, ha, b, hb, c, hc, hng, rfl⟩ := h
    simp only [bigFramesCap, bigGroups, claimGroup, claimBig] at ha hb hc hng
    have hm16 : Sig.MemOK rd (2 ^ 16) := fun i hi => hm i (lt_of_lt_of_le hi (by norm_num))
    obtain ⟨t1, t2, h1, e1, h2⟩ := rc_holds' hm16 (k := c) (K := 16) (by omega) (by norm_num)
    obtain ⟨t3, t4, h3, e2, h4⟩ := rc_holds' hm16 (k := b) (K := 7) (by omega) (by norm_num)
    obtain ⟨t5, h5⟩ : ∃ w, LoadHolds rd (gen ^ a) 0 w := by
      rw [gen_pow_eq_ofK]; exact Sig.load_gpow hm (show a < 2 ^ 20 by omega)
    refine (list_split_iff rd _ _).mpr ⟨ng, rfl, _, _, t1, h1, e1, t2, h2, _, _, t3, h3, e2, t4, h4,
      _, t5, h5, e_add_eq_zero_iff.mpr ?_, rfl⟩
    rw [hng, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  | [], h => exact h.elim
  | _ :: _ :: _, h => exact h.elim

/-- **`list_split` is complete**, on a memory image. -/
theorem list_split_complete : list_split_complete_Spec := fun rd hm =>
  list_split_complete' rd hm

end
end LeanVM.Guest.B1.Digest
