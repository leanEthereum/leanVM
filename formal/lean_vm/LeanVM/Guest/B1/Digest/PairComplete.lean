/-
  LeanVM.Guest.B1.Digest.PairComplete

  `pack_pair`, completely: on an evaluated valuation, the 27 atoms of a deferred pair hold once its
  two words are read.
-/

module

public import LeanVM.Guest.B1.Digest.Basic
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `pack_pair`, completely

`pair_holds`: the equations of `pairAtoms ptr o b` (`Fwd.Good`), and the two words `s`, `t` read
through `ptr` at `o`, `o + 1`, make all 27 atoms hold: the hinted limbs are the words' limbs, so
the three `assert_in_k` checks see `K` words (`split3_top`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

theorem rdAt_of_load {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) : rdAt rd p k = v := by
  unfold rdAt; rw [h.2]; rfl

theorem limbAt_zero (x : E) : limbAt x 0 = ofK (x.limb 0) := rfl

theorem limbAt_one (x : E) : limbAt x 1 = ofK (x.limb 1) := rfl

theorem top_eq (x : E) : ((x + ofK (x.limb 0)) * wYi + ofK (x.limb 1)) * wYi = ofK (x.limb 2) := by
  rw [wYi_eq, split3_top]

/-- **A deferred pair holds** on an evaluated valuation, its two words read. -/
theorem pair_holds {S : List Atom} {w : ℕ → E} {σ : Val} {ptr : V} {o b : ℕ}
    (hg : ∀ a ∈ pairAtoms ptr o b, Good rd S w σ a) (hS : ∀ a ∈ S, a ∉ pairAtoms ptr o b)
    {s t : E} (hs : LoadHolds rd (σ ptr) o s) (ht : LoadHolds rd (σ ptr) (o + 1) t) :
    ∀ a ∈ pairAtoms ptr o b, a.Holds rd σ := by
  have hm : ∀ a ∈ pairAtoms ptr o b, a ∉ S := fun a ha h => hS a h ha
  have g := hg
  simp only [pairAtoms, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, Nat.add_zero] at g hm
  obtain ⟨l0, l1, h2, h3, -, c6, m7, a8, a9, c10, m11, a12, c13, m14, -, c15, m16, a17, a18, c19,
    m20, a21, c22, m23, -, c24, m25, a26⟩ := g
  simp only [Good] at l0 l1 c6 a8 a9 c10 a12 c13 c15 a17 a18 c19 a21 c22 c24 a26
  have e0 : σ (.n b) = s := by
    rcases l0 with h | h
    · exact absurd h hm.1
    · rw [h, rdAt_of_load hs]
  have e1 : σ (.n (b + 1)) = t := by
    rcases l1 with h | h
    · exact absurd h hm.2.1
    · rw [h, rdAt_of_load ht]
  have mul_eq : ∀ {d x y : ℕ}, x < d → y < d → Good rd S w σ (.mul (.n d) (.n x) (.n y)) →
      σ (.n d) = σ (.n x) * σ (.n y) := by
    intro d x y hx hy h
    simp only [Good] at h
    rwa [ite_pos' ⟨hx, hy⟩] at h
  have e7 := mul_eq (by omega) (by omega) m7
  have e11 := mul_eq (by omega) (by omega) m11
  have e14 := mul_eq (by omega) (by omega) m14
  have e16 := mul_eq (by omega) (by omega) m16
  have e20 := mul_eq (by omega) (by omega) m20
  have e23 := mul_eq (by omega) (by omega) m23
  have e25 := mul_eq (by omega) (by omega) m25
  simp only [Good] at h2 h3
  have v2 : σ (.n (b + 2)) = ofK (s.limb 0) := by
    have := h2 0 (by simp); simpa [e0, limbAt_zero] using this
  have v3 : σ (.n (b + 3)) = ofK (s.limb 1) := by
    have := h2 1 (by simp); simpa [e0, limbAt_one] using this
  have v4 : σ (.n (b + 4)) = ofK (t.limb 0) := by
    have := h3 0 (by simp); simpa [e1, limbAt_zero] using this
  have v5 : σ (.n (b + 5)) = ofK (t.limb 1) := by
    have := h3 1 (by simp); simpa [e1, limbAt_one] using this
  have v14 : σ (.n (b + 14)) = ofK (s.limb 2) := by
    rw [e14, a12, e11, a9, c10, c13, e0, v2, v3, top_eq]
  have v23 : σ (.n (b + 23)) = ofK (t.limb 2) := by
    rw [e23, a21, e20, a18, c19, c22, e1, v4, v5, top_eq]
  simp only [pairAtoms, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, Nat.add_zero]
  exact ⟨by rw [e0]; exact hs, by rw [e1]; exact ht, trivial, trivial,
    ⟨by rw [v2]; exact ofK_isInK _, by rw [v3]; exact ofK_isInK _⟩,
    c6, e7, a8, a9, c10, e11, a12, c13, e14, ⟨by rw [v14]; exact ofK_isInK _,
    by rw [v4]; exact ofK_isInK _⟩, c15, e16, a17, a18, c19, e20, a21, c22, e23,
    ⟨by rw [v5]; exact ofK_isInK _, by rw [v23]; exact ofK_isInK _⟩, c24, e25, a26⟩

end
end LeanVM.Guest.B1.Digest
