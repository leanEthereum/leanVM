/-
  LeanVM.Guest.B1.Whir.CFinPt

  The finish's call of fold_final_msg, its point buffers and the heap buffers it allocates,
  honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinEval
public import LeanVM.Guest.B1.Whir.Point

/-!
# The point, honestly (G:1733-1757)

`osPtBlks_complete`: the point's entries, each loaded from its source (`osPtSrc`) and stored in
`point` and, plus one, in `point1`, on memory holding the honest words there.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- What memory holds of a point entry `i` of value `v` from the source `src`: the source's word,
`v` in `point`, `1 + v` in `point1`. -/
def PtMem (rd : Reader) (σ : Val) (pt pt1 i : ℕ) (src : Option (ℕ × ℕ)) (v : E) : Prop :=
  PtSrcOk rd σ src v ∧ LoadHolds rd (σ (.n pt)) i v ∧ LoadHolds rd (σ (.n pt1)) i (1 + v)

theorem osPtBlk_next (pt pt1 i k : ℕ) (src : Option (ℕ × ℕ)) :
    k + 2 ≤ (osPtBlk pt pt1 i k src).2 := by
  unfold osPtBlk; split <;> simp

/-- **One point entry, honestly.** -/
theorem osPtBlk_complete {σ : Val} {pt pt1 i k : ℕ} {src : Option (ℕ × ℕ)} {v : E}
    (hpt : pt < k) (hpt1 : pt1 < k) (hsrc : ∀ b o, src = some (b, o) → b < k)
    (hm : ∀ C rd, H C rd → PtMem rd σ pt pt1 i src v) :
    BlkA H σ k (osPtBlk pt pt1 i k src).2 (osPtBlk pt pt1 i k src).1 (fun _ ↦ True) := by
  rcases src with _ | ⟨b, o⟩
  · have hS : Ssa k (osPtBlk pt pt1 i k none).1 (osPtBlk pt pt1 i k none).2 :=
      .cons (.const le_rfl) (.cons (.store (by omega) (by omega)) (.cons (.const (by omega))
        (.cons (.store (by omega) (by omega)) .nil)))
    refine ssa_blk (Pt := fun _ ↦ 0) hS (fun _ _ _ _ _ _ _ ↦ trivial) fun C rd hH σ' ha hr ↦ ?_
    obtain ⟨hv, l0, l1⟩ := hm C rd hH
    simp only [PtSrcOk] at hv
    have e0 := hr k le_rfl (by simp [osPtBlk])
    have e1 := hr (k + 1) (by omega) (by simp [osPtBlk])
    simp [osPtBlk, evalV, stepV, stepW] at e0 e1
    simp only [osPtBlk, SidesOk, Side, stepW, V.n, le_refl, ↓reduceIte, and_true, true_and,
      show ¬ k + 1 ≤ k by omega, show ¬ k + 2 ≤ k + 1 by omega]
    rw [ha _ hpt, ha _ hpt1, e0, e1, word_zero, word_one, ← hv]
    exact ⟨l0, by rw [hv, add_zero] at l1; exact l1⟩
  · have hb := hsrc b o rfl
    have hS : Ssa k (osPtBlk pt pt1 i k (some (b, o))).1 (osPtBlk pt pt1 i k (some (b, o))).2 :=
      .cons (.load le_rfl (by omega)) (.cons (.store (by omega) (by omega)) (.cons (.const (by omega))
        (.cons (.load (by omega) (by omega)) (.cons (.add (by omega) (by omega) (by omega))
          (.cons (.store (by omega) (by omega)) .nil)))))
    refine ssa_blk (Pt := fun _ ↦ 0) hS (fun _ _ _ _ _ _ _ ↦ trivial) fun C rd hH σ' ha hr ↦ ?_
    obtain ⟨hv, l0, l1⟩ := hm C rd hH
    simp only [PtSrcOk] at hv
    have em : memOf H (σ (.n b)) o = v := memOf_eq (fun C rd hH ↦ (hm C rd hH).1) hH
    have e0 := hr k le_rfl (by simp [osPtBlk])
    have e3 := hr (k + 3) (by omega) (by simp [osPtBlk])
    simp [osPtBlk, evalV, stepV, stepW, show b ≠ k + 1 by omega, show b ≠ k by omega] at e0 e3
    simp only [osPtBlk, SidesOk, Side, stepW, V.n, le_refl, ↓reduceIte, and_true, true_and,
      show ¬ k + 1 ≤ k by omega, show ¬ k + 4 ≤ k + 3 by omega]
    rw [ha _ hpt, ha _ hpt1, ha _ hb, e0, e3, em, word_one]
    exact ⟨hv, l0, hv, l1⟩

theorem ptMem_agree {rd : Reader} {σ σ' : Val} {pt pt1 i k : ℕ} {src : Option (ℕ × ℕ)} {v : E}
    (hpt : pt < k) (hpt1 : pt1 < k) (hsrc : ∀ b o, src = some (b, o) → b < k)
    (ha : AgreeBelow k σ σ') (h : PtMem rd σ pt pt1 i src v) : PtMem rd σ' pt pt1 i src v := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, by rwa [ha _ hpt], by rwa [ha _ hpt1]⟩
  rcases src with _ | ⟨b, o⟩
  · exact h1
  · simp only [PtSrcOk] at h1 ⊢; rwa [ha _ (hsrc b o rfl)]

theorem osPtSrc_base {c : OsCfg} {tch i b o : ℕ} (h : osPtSrc c tch i = some (b, o)) :
    b = osFch ∨ b = tch := by
  unfold osPtSrc at h
  dsimp only at h
  split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> omega

theorem osPtBlks_next (c : OsCfg) (pt pt1 tch : ℕ) :
    ∀ n i k, k ≤ (osPtBlks c pt pt1 tch i n k).2
  | 0, _, _ => le_rfl
  | n + 1, i, k => le_trans (by have := osPtBlk_next pt pt1 i k (osPtSrc c tch i); omega)
      (osPtBlks_next c pt pt1 tch n (i + 1) _)

/-- **The point's entries `i .. i + n - 1`, honestly.** -/
theorem osPtBlks_complete {c : OsCfg} {pt pt1 tch : ℕ} (V : ℕ → E) :
    ∀ (n i k : ℕ) (σ : Val), pt < k → pt1 < k → osFch < k → tch < k →
      (∀ j < n, ∀ C rd, H C rd → PtMem rd σ pt pt1 (i + j) (osPtSrc c tch (i + j)) (V (i + j))) →
      BlkA H σ k (osPtBlks c pt pt1 tch i n k).2 (osPtBlks c pt pt1 tch i n k).1 (fun _ ↦ True)
  | 0, _, _, _, _, _, _, _, _ => BlkA.nil fun _ _ ↦ trivial
  | n + 1, i, k, σ, hpt, hpt1, hf, ht, hm => by
    have hsrc : ∀ b o, osPtSrc c tch i = some (b, o) → b < k := fun b o h ↦ by
      rcases osPtSrc_base h with rfl | rfl <;> assumption
    have h1 := osPtBlk_complete (H := H) hpt hpt1 hsrc (fun C rd hH ↦ by simpa using hm 0 (by omega) C rd hH)
    have hn := osPtBlk_next pt pt1 i k (osPtSrc c tch i)
    refine (BlkA.seq (OutB := fun _ ↦ True) (by omega) (osPtBlks_next c pt pt1 tch n (i + 1) _) h1
      fun σ1 ha1 _ ↦ ?_).mono fun _ _ ↦ trivial
    refine osPtBlks_complete V n (i + 1) _ σ1 (by omega) (by omega) (by omega) (by omega) fun j hj C rd hH ↦ ?_
    have hsrc' : ∀ b o, osPtSrc c tch (i + 1 + j) = some (b, o) → b < k := fun b o h ↦ by
      rcases osPtSrc_base h with rfl | rfl <;> assumption
    have := hm (j + 1) (by omega) C rd hH
    rw [show i + (j + 1) = i + 1 + j by ring] at this
    exact ptMem_agree hpt hpt1 hsrc' ha1 this

end
end LeanVM.Guest.B1.Whir
