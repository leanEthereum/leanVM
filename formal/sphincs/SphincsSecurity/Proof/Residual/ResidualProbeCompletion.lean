import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualTableCompletion
namespace SphincsSecurity.Concrete.ResidualProbeCompletion

open _root_.OracleComp OracleSpec HiddenLabelObservation UniformTableCompletion RetainedObservation ResidualTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Cell Result : Type} [Fintype Coordinate] [DecidableEq Coordinate]
  [Fintype Cell] [DecidableEq Cell]

omit [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Cell] [DecidableEq Cell] in
theorem observe_response (labels : Coordinate → Digest) (probe : Probe Coordinate)
    (stopped : SPMF Result) (next : HashOutput → SPMF Result) :
    observe (response labels probe) stopped next =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= fun answer =>
        if probe.keep labels answer then next answer else stopped) := by
  rw [observe, response, toPMF_bind_lift]
  simp only [← PMF.monad_bind_eq_bind, evalDist_bind, bind_assoc]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, SPMF.toPMF_pure, SPMF.lift_pure, pure_bind]
  · simp only [h, if_false, SPMF.toPMF_failure, SPMF.lift_pure, pure_bind]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem fixedLabels_fresh (labels : Coordinate → Digest) (cache : Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coordinate) (stopped : SPMF Result)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table =>
      if probe.keep labels (table input) then next (table input) table else stopped) =
        observe (response labels probe) stopped
          (fun answer => completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [bind_fresh cache input hfresh (fun answer table => if probe.keep labels answer then next answer table else stopped),
    observe_response]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true]
  · simp only [h, if_false, completeRows_bind_const]

theorem bind_fresh_probe (candidates : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (candidates coordinate).Nonempty) (cache : Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coordinate) (stopped : SPMF Result)
    (next : HashOutput → (Coordinate → Digest) → (Cell → HashOutput) → SPMF Result) :
    (complete candidates >>= fun labels => completeRows cache >>= fun table =>
      if probe.keep labels (table input) then next (table input) labels table else stopped) =
        observe (lazyResponse candidates probe) stopped (fun answer =>
          complete (probe.restrict candidates answer) >>= fun labels =>
            completeRows (Function.update cache input (some answer)) >>= next answer labels) := by
  have hfixed (labels : Coordinate → Digest) := fixedLabels_fresh labels cache input hfresh probe stopped
    (fun answer table => next answer labels table)
  simp_rw [hfixed]
  exact bind_response_stopped candidates ha probe stopped
    (fun answer labels => completeRows (Function.update cache input (some answer)) >>= next answer labels)

end SphincsSecurity.Concrete.ResidualProbeCompletion
