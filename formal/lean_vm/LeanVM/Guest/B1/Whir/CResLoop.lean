/-
  LeanVM.Guest.B1.Whir.CResLoop

  The residual loop helper of a non-final level holds at its honest arguments.
-/

module

public import LeanVM.Guest.B1.Whir.CFinRs
public import LeanVM.Guest.B1.Whir.CLoop
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# The residual loop, honestly

At `x = g^j`, `j < N`, the loop body reads the batch's positions at `qpos·g^po·x^8` and advances
the chains `chain[2j], chain[2j + 1]` over them into `chain[2j + 2], chain[2j + 3]` (`rcC`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- The word a reader holds at `p·g^off` (`0` where it holds none). -/
def rdMem (rd : Reader) (p : E) (off : ℕ) : E := (rd (p.limb 0 * addressOfIndex off)).getD 0

theorem rdMem_of {rd : Reader} {p : E} {off : ℕ} {v : E} (h : LoadHolds rd p off v) :
    rdMem rd p off = v ∧ LoadHolds rd p off (rdMem rd p off) := by
  have e : rdMem rd p off = v := by unfold rdMem; rw [h.2]; rfl
  exact ⟨e, by rw [e]; exact h⟩

theorem rcAt_succ (lv : OsLv) (D : ℕ → E) (hsv : List E) (Pos : ℕ → E) (mu : E) (j : ℕ) :
    rcAt lv D hsv Pos mu (j + 1) = resFold (resP lv D) (resH lv hsv) mu (rcAt lv D hsv Pos mu j)
      ((List.range resBatch).map fun i ↦ Pos (resBatch * j + i)) := by
  unfold rcAt
  rw [← resFold_append, show resBatch * (j + 1) = resBatch * j + resBatch by ring, List.range_add,
    List.map_append, List.map_map]
  rfl

/-! ## `x^resBatch`, honestly -/

/-- The square-and-multiply steps from `k` write `k, k + 1, …` in order, ending below. -/
theorem osPowSteps_ssaP (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), acc < k → x < k →
    SsaP k (osPowSteps x ds acc k).1 (k + (ds.length + (ds.filter id).length)) ∧
      (osPowSteps x ds acc k).2 < k + (ds.length + (ds.filter id).length)
  | [], _, k, hak, _ => ⟨by simpa [osPowSteps] using (SsaP.nil (w := k)), by simpa [osPowSteps] using hak⟩
  | true :: ds, acc, k, hak, hxk => by
    obtain ⟨h1, h2⟩ := osPowSteps_ssaP x ds (k + 1) (k + 2) (by omega) (by omega)
    have e : k + ((true :: ds).length + ((true :: ds).filter id).length) =
        k + 2 + (ds.length + (ds.filter id).length) := by simp; omega
    rw [e]
    simp only [osPowSteps, ↓reduceIte]
    exact ⟨.mul le_rfl hak hak (.mul le_rfl (by omega) (by omega) h1), h2⟩
  | false :: ds, acc, k, hak, hxk => by
    obtain ⟨h1, h2⟩ := osPowSteps_ssaP x ds k (k + 1) (by omega) (by omega)
    have e : k + ((false :: ds).length + ((false :: ds).filter id).length) =
        k + 1 + (ds.length + (ds.filter id).length) := by simp; omega
    rw [e]
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte]
    exact ⟨.mul le_rfl hak hak h1, h2⟩

theorem osPowSteps_loads (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ),
    loadsOf (osPowSteps x ds acc k).1 = []
  | [], _, _ => rfl
  | true :: ds, acc, k => by simpa [osPowSteps, osMul, loadsOf] using osPowSteps_loads x ds (k + 1) (k + 2)
  | false :: ds, acc, k => by simpa [osPowSteps, osMul, loadsOf] using osPowSteps_loads x ds k (k + 1)

theorem osBatchPow_ssaP (k : ℕ) (hk : 0 < k) :
    SsaP k (osBatchPow k).1 (k + batchLen) ∧ (osBatchPow k).2 < k + batchLen :=
  osPowSteps_ssaP 0 _ 0 k hk hk

theorem osBatchPow_loads (k : ℕ) : loadsOf (osBatchPow k).1 = [] := osPowSteps_loads 0 _ 0 k

end
end LeanVM.Guest.B1.Whir
