/-
  LeanVM.Guest.B1.Whir.Point

  The terminal's point buffers: the rotated point and one plus it.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# The point (G:1655-1669)

Entry `i` of `point` is the challenge `osPtSrc` names (or `0` past the point), entry `i` of
`point1` one plus it (`osPtBlks_sound`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- What the point's entry `i` is: the challenge its source names, `0` without one. -/
def PtSrcOk (rd : Reader) (σ : Val) (src : Option (ℕ × ℕ)) (v : E) : Prop :=
  match src with
  | some (b, o) => LoadHolds rd (σ (.n b)) o v
  | none => v = 0

theorem osPtBlk_val {pt pt1 i k : ℕ} {src : Option (ℕ × ℕ)} {v : E} (hv : PtSrcOk rd σ src v)
    (h : AllOk C rd σ (osPtBlk pt pt1 i k src).1) :
    LoadHolds rd (σ (.n pt)) i v ∧ LoadHolds rd (σ (.n pt1)) i (1 + v) := by
  rcases src with _ | ⟨b, o⟩
  · simp only [osPtBlk, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
    obtain ⟨c0, l0, c1, l1⟩ := h
    simp only [PtSrcOk] at hv
    rw [c0, word_zero, ← hv] at l0
    rw [c1, word_one] at l1
    exact ⟨l0, by rw [hv, add_zero]; exact l1⟩
  · simp only [osPtBlk, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
    obtain ⟨l0, s0, c1, l2, a3, s3⟩ := h
    simp only [PtSrcOk] at hv
    rw [loadHolds_unique l0 hv] at s0
    rw [a3, c1, word_one, loadHolds_unique l2 hv] at s3
    exact ⟨s0, s3⟩

/-- **The point's entries `i .. i + n - 1`.** -/
theorem osPtBlks_sound {c : OsCfg} {pt pt1 tch : ℕ} (V : ℕ → E)
    (hV : ∀ i, PtSrcOk rd σ (osPtSrc c tch i) (V i)) :
    ∀ (n i k : ℕ), AllOk C rd σ (osPtBlks c pt pt1 tch i n k).1 → ∀ j < n,
      LoadHolds rd (σ (.n pt)) (i + j) (V (i + j)) ∧
        LoadHolds rd (σ (.n pt1)) (i + j) (1 + V (i + j))
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, i, k, h, j, hj => by
    simp only [osPtBlks] at h
    rw [allOk_append] at h
    rcases j with _ | j
    · exact osPtBlk_val (hV i) h.1
    · have := osPtBlks_sound V hV n (i + 1) _ h.2 j (by omega)
      rwa [show i + 1 + j = i + (j + 1) by ring] at this

end
end LeanVM.Guest.B1.Whir
