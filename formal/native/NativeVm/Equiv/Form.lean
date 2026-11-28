module

public import NativeVm.Model.Layout

/-!
# Forms and bus blocks: the model's words as the statement's values

`FormW.toForm` reads a model form (`FormW`, `NativeVm/Model/Layout.lean`) as the statement's `Form`
(`Statement/Verifier/Layout.lean`): its terms in order, each monomial as a list, each coefficient
through `EW.toE`. `BusBlockW.toSpec` reads a bus block the same way.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- A term as the statement's: the monomial as a list, the coefficient in `E`. -/
def TermW.toSpec (t : TermW) : List ℕ × E := (t.cols.toList, t.coeff.toE)

/-- A form as the statement's `Form`. -/
def FormW.toForm (f : FormW) : Form := ⟨f.toList.map TermW.toSpec⟩

/-- A bus block as the statement's `BusBlock`. -/
def BusBlockW.toSpec (b : BusBlockW) : BusBlock :=
  ⟨b.logRows, b.rows, b.coordinates.toList.map FormW.toForm, b.owner⟩

end NativeVm.Model
