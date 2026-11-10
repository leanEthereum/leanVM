import Rv64Verifier.Proofs.Pcs.VsoLevel
import Rv64Verifier.Proofs.Pcs.VsoTailModel

/-!
# `verify_stacked_opening`'s final level: where the level loop hands over

After the final level's glue the loop branches (`0x8000b510`) to `0x8000b8ec`, the tail: the
remaining sumcheck rounds, the terminal point, the basis and every glued claim at it, the residual's
evaluation and the comparison. `VsoFinalIn` is the state there: `Head`'s context and frame, the
mirror's locals `Wl` after the glue, the residual, and the mirror's run left (`finalTailM`), for
the transcripts whose openings `OA` places in memory (`RunsF`).

Where the tail finds its inputs (`S` the entry's `sp`): the running quadratic's buffer and length
at `S - 896` and `S - 808`, the residual's at `S - 968` and `S - 960`, the fold count at
`S - 928`, the message log at `S - 872`, the transcript and its sponge at `S - 816` and
`S - 792`; `folds`, `glued` and the `StackBasis` where `Head` has them.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- The final level's tail, after the glue: `afterGlue`'s final branch. -/
def finalTailM (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (ml : ℕ) (Wl : Model.Pcs.WhirLocals) : Model.TM Unit := do
  let (_, tailFolds, runningTarget) ←
    Model.Pcs.TM.forRange (Model.Pcs.tailRoundRust ml) 0 ml (Wl.runningQuad, [], 0)
  let point := Wl.folds ++ tailFolds
  let laneFolds ← Model.TM.ofOption config.folds[0]?
  let weight ← Model.TM.ofOption (Model.Pcs.terminalWeightRust basis laneFolds Wl.glued point)
  let residualValue ← Model.TM.ofOption (Model.multilinearEvalRust residual tailFolds)
  Model.TM.require (weight * residualValue = runningTarget)

theorem afterGlue_final {logN : ℕ} {config : Model.Pcs.WhirConfigRust} {basis : List E → Option E}
    {level : ℕ} {rest : List (ℕ × ℕ)} {residual : List E} {ml : ℕ} {Wl : Model.Pcs.WhirLocals}
    (h : level = config.folds.length - 1) :
    Model.Pcs.afterGlue logN config basis level rest residual ml Wl =
      finalTailM config basis residual ml Wl := by
  rw [Model.Pcs.afterGlue, ite_eq_left h]
  rfl

/-- From the entry, on every transcript whose openings `OA` places in memory, the mirror runs on as
`m` on the transcript `u` stands for. -/
def RunsF (OA : MachineState → Word → Model.TState → Prop) (s u : MachineState)
    (m : Model.TM Unit) : Prop :=
  ∀ T, TranscriptAt s (s.getReg .x10) T → OA s (s.getReg .x10) T →
    T.roots = [(digestAt s (s.getReg .x11),
      Model.stackShape (s.getReg .x12).toNat (s.getReg .x13).toNat)] →
    ∃ T', (Model.Pcs.verifyStackedOpeningRust (s.getReg .x12).toNat (s.getReg .x13).toNat
        (claimsOf s)).run T = m.run T' ∧ TranscriptAt u (s.getReg .x10) T'

/-- A weaker `OA` keeps `RunsF`. -/
theorem RunsF.mono {OA OA' : MachineState → Word → Model.TState → Prop} {s u : MachineState}
    {m : Model.TM Unit} (h : RunsF OA s u m) (hOA : ∀ T, OA' s (s.getReg .x10) T → OA s (s.getReg .x10) T) :
    RunsF OA' s u m := fun T hT hO hr ↦ h T hT (hOA T hO) hr

/-- At `0x8000b8ec`, the final level's tail, the mirror's locals after the glue `Wl` and the
residual in memory. -/
structure VsoFinalIn (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) : Prop where
  cfg : Configured s x.b x.c x.nxb x.QP x.QL x.FP x.RP
  mark : x.FP.toNat + 8 * (K0 s + 2) ≤ x.L ∧ x.RP.toNat + 8 * (K0 s + 2) ≤ x.L ∧
    x.nxb.toNat ≤ x.L ∧ x.L ≤ heapNext x.c
  fr : DFrame x.c u (LM s x.L (u.getMem nextAddr))
  heap : HeapOk u
  mono : heapNext x.c ≤ heapNext u
  pc : u.pc = 0x8000b8ec
  sp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040
  x9 : u.getReg .x9 = x.FP
  x26 : u.getReg .x26 = s.getReg .x12
  /-- The fold count and the message log. -/
  fle : Wl.folds.length ≤ (s.getReg .x12).toNat
  m112 : u.getMem (s.getReg .x2 - 928) = BitVec.ofNat 64 Wl.folds.length
  m168 : u.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 ((s.getReg .x12).toNat - Wl.folds.length)
  m224 : u.getMem (s.getReg .x2 - 816) = s.getReg .x10
  m248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8
  folds : VecEAt u (s.getReg .x2 - 688) x.L Wl.folds
  glued : VecOk u (s.getReg .x2 - 664) 88 8 ∧
    gluedListAt u (vecPtr u (s.getReg .x2 - 664)) (vecLen u (s.getReg .x2 - 664)).toNat = Wl.glued ∧
    (vecCap u (s.getReg .x2 - 664) = 0 ∨ x.L ≤ (vecPtr u (s.getReg .x2 - 664)).toNat)
  /-- Every glued claim's buffers lie in the heap from the mark on. -/
  frozen : ∀ i < (vecLen u (s.getReg .x2 - 664)).toNat, ∀ y, InBufs u (gAddr u s i) y →
    x.L ≤ y.toNat ∧ y.toNat < heapNext u
  /-- The running quadratic: buffer at `S - 896`, length at `S - 808`. -/
  quad : eListAt u (u.getMem (s.getReg .x2 - 896)) (u.getMem (s.getReg .x2 - 808)).toNat =
      Wl.runningQuad ∧ (u.getMem (s.getReg .x2 - 896)).toNat % 8 = 0 ∧
    ((u.getMem (s.getReg .x2 - 808)).toNat = 0 ∨ x.L ≤ (u.getMem (s.getReg .x2 - 896)).toNat ∧
      (u.getMem (s.getReg .x2 - 896)).toNat + 24 * (u.getMem (s.getReg .x2 - 808)).toNat ≤
        heapNext u)
  /-- The residual: buffer at `S - 968`, length at `S - 960`. -/
  res : eListAt u (u.getMem (s.getReg .x2 - 968)) (u.getMem (s.getReg .x2 - 960)).toNat =
      residual ∧ (u.getMem (s.getReg .x2 - 968)).toNat % 8 = 0 ∧
    ((u.getMem (s.getReg .x2 - 960)).toNat = 0 ∨ x.L ≤ (u.getMem (s.getReg .x2 - 968)).toNat ∧
      (u.getMem (s.getReg .x2 - 968)).toNat + 24 * (u.getMem (s.getReg .x2 - 960)).toNat ≤
        heapNext u)
  /-- The residual's length, `next_scalars(1 << ml)`'s. -/
  rlen : residual.length = 2 ^ ((s.getReg .x12).toNat - Wl.folds.length)
  value : RunsF OA s u (finalTailM (cfgOf s) (basisOf s x) residual
    ((s.getReg .x12).toNat - Wl.folds.length) Wl)

end Rv64Verifier.Proofs.Pcs.Vso
