/-
  LeanVM.Guest.B1.VerifySub.Stream

  The stream words `verify_sub` consumes before `open_stacked`, as the decoder reads them.
-/

module

public import LeanVM.Guest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.Proof
public import LeanVM.Guest.B1.VerifySub.Tail

/-!
# The stream before the opening

`vs_stream`: the words at `stream` (`σ 25`) up to the cursor handed to `open_stacked` (`σ 656`),
read by `wordsAt` for `cursorLen` of them, are the announced words, the root's two words, the
bus's GKR words, the tables' words and `verify_keccak`'s. The cursor is `stream·g^n` for their
count `n`, which the memory bounds by `2^κ ≤ 2^32` (`mem_size_le`), so `cursorLen` finds it.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `mem_size` up to `2^33` words. -/
theorem mem_size_big {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {p : E} {n : ℕ} (hn : n ≤ 2 ^ 33)
    (h : ∀ j < n, ∃ v, LoadHolds L.read p j v) : n ≤ 2 ^ κ := by
  have hκ64 : κ < 64 := by omega
  have hidx : ∀ j : Fin n, ∃ i : Fin (2 ^ κ), p.limb 0 * Parameters.addressOfIndex j =
      Parameters.addressOfIndex i := by
    intro j
    obtain ⟨v, -, hv⟩ := h j j.isLt
    obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp hv
    exact ⟨i, hi⟩
  choose f hf using hidx
  have hinj : Function.Injective f := by
    intro a b hab
    have ea := hf a
    have eb := hf b
    rw [hab, ← eb] at ea
    have hp : p.limb 0 ≠ 0 := by
      intro h0
      have := hf a
      rw [h0, zero_mul] at this
      exact Parameters.gpow_ne_zero _ this.symm
    have := mul_left_cancel₀ hp ea
    have hlt : ∀ x : Fin n, (x : ℕ) < 2 ^ 64 - 1 := fun x ↦ by have := x.isLt; omega
    exact Fin.ext (gpow_injOn (hlt a) (hlt b) this)
  simpa using Fintype.card_le_of_injective f hinj

/-- A run of words read at one pointer is at most `2^32` long. -/
theorem mem_size_le {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {p : E} {xs : List E}
    (h : ReadsAt L.read p xs) : xs.length ≤ 2 ^ 32 := by
  by_contra hlt
  have hb := mem_size_big hκ L (n := 2 ^ 32 + 1) (by norm_num)
    (fun j hj ↦ ⟨xs[j]'(by omega), h j (by omega)⟩)
  have : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hκ
  omega

/-- **The stream before the opening** (the decoder's words). -/
theorem vs_stream {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {bytecode : List K} {C : CallRel}
    {σ : Val} (F : VsFront bytecode C L.read σ) {xsK : List E}
    (hxsK : ReadsAt L.read (σ (.n 641)) xsK) (e868 : σ (.n 656) = σ (.n 641) * gen ^ xsK.length) :
    wordsAt L.read (σ (.n 25)) (cursorLen (σ (.n 25)) (σ (.n 656))) =
      vsWords σ ++ [σ (.n 324), σ (.n 334)] ++ F.xsG ++ F.xsT ++ xsK := by
  -- the cursor after the bus's GKR
  have e844 : σ (.n 631) = σ (.n 25) * gen ^ 10 * gen ^ F.xsG.length := by
    have hr := F.hretG
    rw [show [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 632),
      σ (.n 633), σ (.n 634)] = ([σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630)] ++
        [σ (.n 631)]) ++ [σ (.n 632), σ (.n 633), σ (.n 634)] from rfl] at hr
    obtain ⟨h1, -⟩ := List.append_inj' hr (by rw [F.hvL]; rfl)
    obtain ⟨-, h2⟩ := List.append_inj' h1 rfl
    simpa using h2
  -- the words
  have h10 : ReadsAt L.read (σ (.n 25)) (vsWords σ ++ [σ (.n 324), σ (.n 334)]) := by
    intro k hk
    simp only [vsWords, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hk
    have hw := F.hw
    interval_cases k
    · exact (hw 0 (by norm_num)).1
    · exact (hw 1 (by norm_num)).1
    · exact (hw 2 (by norm_num)).1
    · exact (hw 3 (by norm_num)).1
    · exact (hw 4 (by norm_num)).1
    · exact (hw 5 (by norm_num)).1
    · exact (hw 6 (by norm_num)).1
    · exact (hw 7 (by norm_num)).1
    · exact F.w8.1
    · exact F.w9.1
  have hlen10 : (vsWords σ ++ [σ (.n 324), σ (.n 334)]).length = 10 := rfl
  have hall : ReadsAt L.read (σ (.n 25))
      (vsWords σ ++ [σ (.n 324), σ (.n 334)] ++ F.xsG ++ F.xsT ++ xsK) := by
    rw [readsAt_append, readsAt_append, readsAt_append]
    refine ⟨⟨⟨h10, ?_⟩, ?_⟩, ?_⟩
    · rw [hlen10]; exact F.hxsG
    · rw [List.length_append, hlen10, pow_add, ← mul_assoc, ← e844]; exact F.hxsT
    · rw [List.length_append, List.length_append, hlen10, pow_add, pow_add, ← mul_assoc,
        ← mul_assoc, ← e844, ← F.e854]
      exact hxsK
  have hq : σ (.n 656) = σ (.n 25) *
      gen ^ (vsWords σ ++ [σ (.n 324), σ (.n 334)] ++ F.xsG ++ F.xsT ++ xsK).length := by
    rw [e868, F.e854, e844]
    simp only [List.length_append, hlen10, pow_add]
    ring
  rw [cursorLen_eq (ne_zero_of_load (by omega) L F.w8.1) hq (mem_size_le hκ L hall),
    wordsAt_eq hall]

end
end LeanVM.Guest.B1.VerifySub
