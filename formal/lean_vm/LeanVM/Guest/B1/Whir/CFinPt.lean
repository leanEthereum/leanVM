/-
  LeanVM.Guest.B1.Whir.CFinPt

  The point's buffers, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CTail
public import LeanVM.Guest.B1.Whir.Point

/-!
# The point's buffers, honestly

`osPtBlk_complete`: one entry of the point (its source's word `v` loaded, stored at `pt[i]`, `1 + v`
stored at `pt1[i]`; zero and one past the point). `osPtBlks_complete`: the entries `i ..`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- An entry's values. -/
def ptVals (src : Option (ℕ × ℕ)) (v : E) : List E :=
  match src with
  | some _ => [v, word 1 0 0, v, word 1 0 0 + v]
  | none => [word 0 0 0, word 1 0 0]

theorem osPtBlk_k (pt pt1 i k : ℕ) (src : Option (ℕ × ℕ)) :
    (osPtBlk pt pt1 i k src).2 = k + (ptVals src 0).length := by
  rcases src with _ | _ <;> rfl

/-- **One entry, honestly.** -/
theorem osPtBlk_complete {pt pt1 i k : ℕ} {src : Option (ℕ × ℕ)} {v : E} (σ : Val)
    (hpt : pt < k) (hpt1 : pt1 < k) (hsrc : ∀ b o, src = some (b, o) → b < k)
    (hv : PtSrcOk rd σ src v) (hs : LoadHolds rd (σ (.n pt)) i v)
    (hs1 : LoadHolds rd (σ (.n pt1)) i (1 + v)) :
    BlkF C rd σ k (osPtBlk pt pt1 i k src).2 (fun j ↦ (ptVals src v).getD (j - k) 0)
      (osPtBlk pt pt1 i k src).1 (fun σ' ↦ AgreeBelow k σ σ') := by
  intro σ' ha hr
  have ep := ha pt hpt; have ep1 := ha pt1 hpt1
  refine ⟨?_, ha⟩
  rcases src with _ | ⟨b, o⟩
  · simp only [PtSrcOk] at hv
    subst hv
    have v0 := hr k le_rfl (by simp [osPtBlk])
    have v1 := hr (k + 1) (by omega) (by simp [osPtBlk])
    simp [ptVals] at v0 v1
    simp only [osPtBlk, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    refine ⟨v0, by rw [v0, ep, word_zero]; exact hs, v1, by rw [v1, ep1, word_one]; simpa using hs1⟩
  · simp only [PtSrcOk] at hv
    have eb := ha b (hsrc b o rfl)
    have v0 := hr k le_rfl (by simp [osPtBlk])
    have v1 := hr (k + 1) (by omega) (by simp [osPtBlk])
    have v2 := hr (k + 2) (by omega) (by simp [osPtBlk])
    have v3 := hr (k + 3) (by omega) (by simp [osPtBlk])
    simp [ptVals] at v0 v1 v2 v3
    simp only [osPtBlk, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    refine ⟨by rw [v0, eb]; exact hv, by rw [v0, ep]; exact hs, v1, by rw [v2, eb]; exact hv,
      by rw [v3, v1, v2], by rw [v3, ep1, word_one]; exact hs1⟩

theorem osPtSrc_base {c : OsCfg} {tch i b o : ℕ} (h : osPtSrc c tch i = some (b, o)) :
    b = osFch ∨ b = tch := by
  unfold osPtSrc at h
  dsimp only at h
  split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
    first | exact Or.inl h.1.symm | exact Or.inr h.1.symm

/-- The values of the entries `i ..`. -/
def ptsF (c : OsCfg) (pt pt1 tch : ℕ) (P : ℕ → E) : ℕ → ℕ → ℕ → Val → ℕ → E
  | _, 0, _, _ => fun _ ↦ 0
  | i, n + 1, k, σ =>
    seqF σ k (osPtBlk pt pt1 i k (osPtSrc c tch i)).2
      (fun j ↦ (ptVals (osPtSrc c tch i) (P i)).getD (j - k) 0)
      fun σ1 ↦ ptsF c pt pt1 tch P (i + 1) n (osPtBlk pt pt1 i k (osPtSrc c tch i)).2 σ1

theorem osPtBlks_k (c : OsCfg) (pt pt1 tch : ℕ) :
    ∀ (i n k : ℕ), k ≤ (osPtBlks c pt pt1 tch i n k).2
  | _, 0, _ => le_rfl
  | i, n + 1, k => by
    simp only [osPtBlks]
    have := osPtBlks_k c pt pt1 tch (i + 1) n (osPtBlk pt pt1 i k (osPtSrc c tch i)).2
    have h2 := osPtBlk_k pt pt1 i k (osPtSrc c tch i)
    omega

/-- **The entries `i ..`, honestly.** -/
theorem osPtBlks_complete {c : OsCfg} {pt pt1 tch : ℕ} (P : ℕ → E) :
    ∀ (i n k : ℕ) (σ : Val), pt < k → pt1 < k → tch < k → osFch < k →
      (∀ j, i ≤ j → j < i + n → PtSrcOk rd σ (osPtSrc c tch j) (P j) ∧
        LoadHolds rd (σ (.n pt)) j (P j) ∧ LoadHolds rd (σ (.n pt1)) j (1 + P j)) →
      BlkF C rd σ k (osPtBlks c pt pt1 tch i n k).2 (ptsF c pt pt1 tch P i n k σ)
        (osPtBlks c pt pt1 tch i n k).1 (fun σ' ↦ AgreeBelow k σ σ')
  | _, 0, k, σ, _, _, _, _, _ => BlkF.nil fun _ h ↦ h
  | i, n + 1, k, σ, hpt, hpt1, htch, hfch, h => by
    have hsrc : ∀ b o, osPtSrc c tch i = some (b, o) → b < k := fun b o hb ↦ by
      rcases osPtSrc_base hb with rfl | rfl <;> assumption
    obtain ⟨h1, h2, h3⟩ := h i le_rfl (by omega)
    have hA := osPtBlk_complete (C := C) (rd := rd) (pt := pt) (pt1 := pt1) (i := i) (k := k)
      (src := osPtSrc c tch i) σ hpt hpt1 hsrc h1 h2 h3
    have e : osPtBlks c pt pt1 tch i (n + 1) k = ((osPtBlk pt pt1 i k (osPtSrc c tch i)).1 ++
        (osPtBlks c pt pt1 tch (i + 1) n (osPtBlk pt pt1 i k (osPtSrc c tch i)).2).1,
        (osPtBlks c pt pt1 tch (i + 1) n (osPtBlk pt pt1 i k (osPtSrc c tch i)).2).2) := rfl
    rw [e]
    have hk1 := osPtBlk_k pt pt1 i k (osPtSrc c tch i)
    have hk2 := osPtBlks_k c pt pt1 tch (i + 1) n (osPtBlk pt pt1 i k (osPtSrc c tch i)).2
    refine BlkF.then (k1 := (osPtBlk pt pt1 i k (osPtSrc c tch i)).2) (by omega) hk2 hA
      fun σ1 _ ha1 ↦ ?_
    refine BlkF.mono (osPtBlks_complete P (i + 1) n _ σ1 (by omega) (by omega) (by omega) (by omega)
      fun j hj1 hj2 ↦ ?_) fun σ' ha2 i' hi' ↦ (ha2 i' (by omega)).trans (ha1 i' hi')
    obtain ⟨g1, g2, g3⟩ := h j (by omega) (by omega)
    refine ⟨?_, by rw [ha1 pt hpt]; exact g2, by rw [ha1 pt1 hpt1]; exact g3⟩
    unfold PtSrcOk at g1 ⊢
    split
    · next b o hb =>
      rw [hb] at g1
      have : b < k := by
        rcases osPtSrc_base hb with rfl | rfl <;> omega
      rw [ha1 b this]; exact g1
    · next hb => rw [hb] at g1; exact g1

end
end LeanVM.Guest.B1.Whir
