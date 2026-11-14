module

public import LeanVM.Guest.Mode.ResFam
public import LeanVM.Guest.B2C.CplSpec

/-!
# The residuals at an honest instance

What an instance's frame fixes discharges a nonzero residual whose product cell is one of the
function's fixed cells holding a nonzero constant (`nzStat`, `num_stat`: `FrameHolds.stat` read on
the reference), which `resRef_obl` takes as the product's fact.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.B2C LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec

@[expose] public section

/-- **Every nonzero residual's product is a fixed nonzero constant** of the frame: a cell of
`stat` (`plumbOf`'s) in `[2, fsn)`. -/
def nzStat (stat : List (ℕ × PC)) (fsn : ℕ) (F : Fun) (code : List OffsetInstruction) : Bool :=
  (List.range code.length).all fun i ↦ ((F.res.get i).getD []).all fun
    | .nz _ => stat.any fun p ↦ p.1 == numAt code i && decide (2 ≤ p.1) && decide (p.1 < fsn) &&
        match p.2 with
        | .k a b => decide (a < 2 ^ 64) && decide (b < 2 ^ 64) && !(a == 0 && b == 0)
        | _ => false
    | _ => true

/-- A fixed cell of an instance's frame holds its word on the reference. -/
theorem stat_ref {κ : ℕ} (hκ : κ ≤ 28) {img : MemoryImage κ} {j fp : ℕ} {σ : Core.Val} {es : List Ev}
    {vs : List V} {kfps : List ℕ} {hdr : E × E} (hF : FrameHolds img j fp σ es vs kfps hdr)
    (hfp : fp + fsN j ≤ 2 ^ 62) {c : ℕ} {w : PC} (hc : (c, w) ∈ (plumbOf j).stat) (h2 : 2 ≤ c)
    (hn : c < fsN j) : refMem img (fp + c) = w.word fp :=
  ((refRd_img hκ img) _ _ (by omega) (hF.stat _ hc h2 hn)).2

/-- **A nonzero residual's product from the frame's constants**: at an instance whose frame holds
what the completeness check reads, the product cell of each nonzero residual is nonzero on the
reference. -/
theorem num_stat {κ : ℕ} (hκ : κ ≤ 28) {img : MemoryImage κ} {j fp : ℕ} {σ : Core.Val} {es : List Ev}
    {vs : List V} {kfps : List ℕ} {hdr : E × E} (hF : FrameHolds img j fp σ es vs kfps hdr)
    (hfp : fp + fsN j ≤ 2 ^ 62) {Kc : Cert} (hs : nzStat (plumbOf j).stat (fsN j) Kc.F Kc.code = true)
    {i o : ℕ} (hi : i < Kc.code.length) (hr : Res.nz o ∈ (Kc.F.res.get i).getD []) :
    refMem img (fp + numAt Kc.code i) ≠ 0 := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hs i (List.mem_range.mpr hi)) _ hr
  dsimp only at h1
  obtain ⟨⟨c, w⟩, hp, hh⟩ := List.any_eq_true.mp h1
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
  obtain ⟨⟨⟨rfl, h2⟩, hn⟩, hw⟩ := hh
  rw [stat_ref hκ hF hfp hp h2 hn]
  cases w with
  | k a b =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      beq_eq_false_iff_ne] at hw
    obtain ⟨⟨ha, hb⟩, hab⟩ := hw
    exact imm_ne_zero ha hb (by omega)
  | fpg _ => simp at hw

end

end LeanVM.Guest.Mode
