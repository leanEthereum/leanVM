/-
  LeanVM.Guest.B1.Tables.VtWordsC

  `verify_tables` complete within its words interface's bound (`vtMax`), by a tree within its weight bound
  (`vtWeightB`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AWeight
public import LeanVM.Guest.B1.Tables.VtWords

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- `verify_tables`' own buffers: their shared tables at most `12(μ + 1)` words a table. -/
theorem VtHonest.sizes_sum_le (H : VtHonest) (hμ : H.μ < 32) : H.sizes.sum ≤ 4190 + H.μ := by
  simp only [VtHonest.sizes, VtHonest.shSizes, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.sum_replicate, smul_eq_mul]
  omega

theorem vt_bound_le {H : VtHonest} (W : VtWords fs) (hμ : H.μ < 32) (hn : H.n < 31) :
    fs "verify_tables" + H.sizes.sum + ((vtBs W.Kf W.Ksh (vtRunB fs W.K10 H.n)).sum + ifFrames fs vtPre) ≤
      vtMax fs W := by
  refine le_trans ?_ (vtBnd_le_vtMax W hμ hn)
  have := H.sizes_sum_le hμ
  unfold vtBnd
  omega

/-- **`verify_tables` is complete, placed, within `vtMax`**, at a bus depth below `32` and a height below `31`,
given its words facts. -/
theorem verify_tables_completeAtW {κ : ℕ} (hκ : 14 ≤ κ) {H : VtHonest} (h : H.Ok) (hs : VtShape H)
    (hμ : H.μ < 32) (hn : H.n < 31) (B : VtBases) (W : VtWords fs) :
    CompleteAtB fs cert κ "verify_tables" (H.linL B) (H.args B) (Returns (H.retsH B)) (vtMax fs W) :=
  (verify_tables_completeAtTBW (ι := Empty) hκ h hs B W.Kf W.Ksh W.K10 W.hKf W.hsh W.h10 nofun nofun nofun nofun
    nofun).toCompleteAtB.mono le_rfl (vt_bound_le W hμ hn)

/-- **`verify_tables` is complete within `vtMax` by a tree within its weight bound** at each `ω op`. -/
theorem verify_tables_completeAtWW {κ : ℕ} (hκ : 14 ≤ κ) {H : VtHonest} (h : H.Ok) (hs : VtShape H)
    (hμ : H.μ < 32) (hn : H.n < 31) (B : VtBases) (W : VtWords fs) {ω : Opcode → String → ℕ}
    (Ww : VtWeights ω) :
    CompleteAtDTB fs cert κ "verify_tables" (H.linL B) (H.args B) (Returns (H.retsH B))
      (fun t ↦ ∀ op, Budget.WeighsLe coreProgram (ω op) (vtWeightB Ww op) t) (vtMax fs W) :=
  (verify_tables_completeAtTBW' hκ h hs B W.Kf W.Ksh W.K10 W.hKf W.hsh W.h10 ω Ww.Kvw Ww.Wss Ww.Kw10 Ww.hKvw
    Ww.hssw Ww.h10w).mono (vt_bound_le W hμ hn) fun _ h ↦ h

/-- **`verify_tables_completeAtWW` by its honest node**: its valuation the honest one at its own buffers, which the
memory holds (`vtQn`). -/
theorem verify_tables_completeAtWWR {κ : ℕ} (hκ : 14 ≤ κ) {H : VtHonest} (h : H.Ok) (hs : VtShape H)
    (hμ : H.μ < 32) (hn : H.n < 31) (B : VtBases) (W : VtWords fs) {ω : Opcode → String → ℕ}
    (Ww : VtWeights ω) :
    CompleteAtDTBR fs cert κ "verify_tables" (H.linL B) (H.args B) (Returns (H.retsH B))
      (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (ω op) (vtWeightB Ww op) t) ∧
        ∃ σ ks, t = .node "verify_tables" σ H.sizes ks ∧ vtQn H B rd σ) (vtMax fs W) :=
  (verify_tables_completeAtTBWR' hκ h hs B W.Kf W.Ksh W.K10 W.hKf W.hsh W.h10 ω Ww.Kvw Ww.Wss Ww.Kw10 Ww.hKvw
    Ww.hssw Ww.h10w).monoV (vt_bound_le W hμ hn) fun _ _ _ _ h ↦ h

end
end LeanVM.Guest.B1.Tables
