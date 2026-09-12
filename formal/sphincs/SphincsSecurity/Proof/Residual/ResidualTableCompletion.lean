import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.Concrete.ResidualTableCompletion

open _root_.OracleComp ENNReal UniformTableCompletion
set_option backward.isDefEq.respectTransparency false

variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]

abbrev Cache (Cell : Type) := Cell → Option HashOutput

def allowed (cache : Cache Cell) : Cell → Finset HashOutput :=
  fun input => match cache input with
    | none => Finset.univ
    | some answer => {answer}

omit [Fintype Cell] [DecidableEq Cell] in
theorem allowed_nonempty (cache : Cache Cell) : ∀ input, (allowed cache input).Nonempty := by
  intro input
  cases h : cache input <;> simp only [allowed, h]
  · exact Finset.univ_nonempty
  · exact Finset.singleton_nonempty _

noncomputable def completeRows (cache : Cache Cell) : SPMF (Cell → HashOutput) :=
  complete (allowed cache)

noncomputable def reply (cache : Cache Cell) (input : Cell) : SPMF HashOutput :=
  match cache input with
  | none => liftM (PMF.uniformOfFintype HashOutput)
  | some answer => pure answer

theorem completeRows_empty :
    completeRows (Cell := Cell) (fun _ => none) = liftM (PMF.uniformOfFintype (Cell → HashOutput)) := by
  apply SPMF.ext
  intro table
  simp only [completeRows, complete_apply, allowed, Finset.mem_univ, implies_true, if_true,
    Finset.card_univ, Finset.prod_const, Finset.card_univ, SPMF.liftM_apply, PMF.uniformOfFintype_apply, Fintype.card_fun]

omit [Fintype Cell] [DecidableEq Cell] in
theorem cell_eq_reply (cache : Cache Cell) (input : Cell) : cell (allowed cache input) = reply cache input := by
  apply SPMF.ext
  intro answer
  cases h : cache input with
  | none => simp only [cell_apply, allowed, h, Finset.mem_univ, if_true, Finset.card_univ,
      reply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
  | some value => simp only [cell_apply, allowed, h, Finset.mem_singleton, Finset.card_singleton,
      Nat.cast_one, inv_one, reply, SPMF.pure_apply]

omit [Fintype Cell] in
theorem allowed_update (cache : Cache Cell) (input : Cell) (answer : HashOutput) :
    discloseTableValue (allowed cache) input answer = allowed (Function.update cache input (some answer)) := by
  funext other
  by_cases h : other = input
  · subst other
    simp only [discloseTableValue, Function.update_self, allowed]
  · simp only [discloseTableValue, Function.update_of_ne h, allowed]

theorem bind_read {Result : Type} (cache : Cache Cell) (input : Cell)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table => next (table input) table) =
      (reply cache input >>= fun answer => completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [completeRows, bind_disclose, cell_eq_reply]
  simp only [allowed_update, completeRows]

theorem bind_fresh {Result : Type} (cache : Cache Cell) (input : Cell) (hfresh : cache input = none)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table => next (table input) table) =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= fun answer =>
        completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [bind_read, reply, hfresh]

theorem completeRows_bind_const {Result : Type} (cache : Cache Cell) (next : SPMF Result) :
    (completeRows cache >>= fun _ => next) = next := by
  rw [completeRows, complete_of_nonempty _ (allowed_nonempty cache)]
  exact RetainedObservation.lift_bind_const _ _

end SphincsSecurity.Concrete.ResidualTableCompletion
