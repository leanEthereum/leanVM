/-
  LeanVM.Guest.B1.VerifySub.H.TermPre

  `check_opening_terminal`'s precondition (`TermPre`) on an honest child, its claims' lengths and
  the WHIR terminal equation.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermCtx

/-!
# The terminal's precondition, honestly

`committed_le32`: an honest child's committed columns' logs are at most `32`. `ChildSegs.km_eq`:
the Keccak reduction's results. `ChildSegs.fin`: the WHIR terminal equation (`ChildSegs.acc`).
The terminal point's length (`whir_point_length`) is in `H/WhirLen`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-- **An honest child's committed columns' logs are at most `32`.** -/
theorem committed_le32 {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (h28 : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ 32) :
    ∀ c < Tables.nCommittedCols, (Tables.committedKappas
      (columnKappas logMem Tables.guestLogBytecode (Tables.tableHeightsOf rowsN))).getD c 0 ≤ 32 := by
  rw [stackLog_eq hbl] at h28
  intro c hc
  have hcl : c < (Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf rowsN))).length := by
    rw [Tables.committedKappas_length _ (Tables.columnKappas_length _ _ _)]; exact hc
  have := Tables.tb_le_log2Ceil_of_two_pow_le (Tables.tb_single_le_sum_map _ c hcl)
  have e : ((Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf rowsN))).map (2 ^ ·)).sum =
      Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)) := rfl
  rw [e] at this
  omega

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem km_eq (hbl : bytecode.length = 2 ^ 23) :
    S.km = (([⟨qkeccak, S.op, S.word⟩], S.kpt, S.slices), S.m0) := by
  have h := S.runK
  rw [S.hlayout, (S.lanes hbl).1, (S.lanes hbl).2.1, (S.H_run hbl).2.2.1] at h
  have hτ := S.τ_bounds hbl
  have hil : (S.chis.take S.τ).length = S.τ := by simp [S.chis_length]; omega
  obtain ⟨op', word', hk, -⟩ := keccakSeg_out h (S.runK' hbl).2.2.2.2 (by rw [hil]; omega) hil
  refine Prod.ext (Prod.ext ?_ rfl) rfl
  show S.km.1.1 = [⟨qkeccak, (S.km.1.1.headD default).point, (S.km.1.1.headD default).value⟩]
  rw [hk]; rfl

/-- **The WHIR terminal equation**, on the honest child. -/
theorem fin (hbl : bytecode.length = 2 ^ 23) :
    (S.w.inner + stackWeight S.layout (openedClaims S.claims [⟨qkeccak, S.op, S.word⟩]) S.kpt
      (ringCoefficients S.rchs) S.lam S.w.point) * S.w.residual = S.w.target := by
  have h := S.acc
  rw [S.km_eq hbl] at h
  exact h

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
