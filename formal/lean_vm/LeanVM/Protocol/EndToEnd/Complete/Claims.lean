/-
  LeanVM.Protocol.EndToEnd.Complete.Claims

  The claims an honest run accumulates: a verifier column claim whose value is the true extension
  of an instance column, placed on the stack by the verifier's layout, holds of the stack and has a
  multilinear weight.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance
public import LeanVM.Protocol.Whir.Complete.Tables

/-!
# True column claims

The verifier program (`LeanVM.Protocol.Verifier`, `crates/verifier` at leanVM `40f877dc`)
accumulates column claims as data
(`Verifier.ColumnClaim`: a global column, a point, a value) and opens them on the stack through
its layout (`ColumnClaim.onStack`). Against the honest prover every claim it accumulates is a
*true claim* (`TrueClaim`): the global column is the verifier's number `refCol c` of an instance
column `c`, the point is a point `z` of the column's own variables, and the value is the
extension of the column read off the stack at `z` (`colEval`).

For the stack `q` of the leanISA instance (`inst`), a true claim on a committed column or a
`KECCAK` input lane, i.e. on no `KECCAK` output lane (`keccakOutputColumns`, which the verifier
hands the Keccak reduction instead of the opening), is what the opening needs of it
(`Whir.Complete.follows_verifyStackedOpening`):

* `TrueClaim.holds`: placed on the stack it holds of `q` (`StackClaim.Holds`), by the layout
  correspondence `Front.onStack_holds_iff`;
* `TrueClaim.multilinear`: its weight `eq(placed point, ·)` is multilinear on the stack's cube,
  the placed point being the instance's lift of `z`, of the stack's length
  (`Front.stackPoint_eq_extend`).

An output lane's true value is that of the instance's derived column (`LeanIsa.derived`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete CompPoly CMlPolynomialEval

@[expose] public section

/-- The instance the deployed verifier is complete for: leanISA. -/
abbrev inst (prog : LeanIsaProgram) (s : Sizes) : M3Instance :=
  leanIsaInstance prog s

/-- The true value of an instance column at a point of its variables: the column's extension,
the column read off the stack through the instance's layout. -/
def colEval (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) (c : Col)
    (z : Vector E (kappa prog s c)) : E :=
  eval₂Mle ((inst prog s).column q c).values (algebraMap K E) z

/-- A **true claim**: a verifier column claim on the verifier's number of an instance column, at a
point of the column's variables, whose value is the column's true value there. -/
def TrueClaim (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))
    (cl : Verifier.ColumnClaim) : Prop :=
  ∃ c : Col, ∃ z : Vector E (kappa prog s c), cl = ⟨refCol c, z.toList, colEval prog s q c z⟩

/-- Every claim of a list is true. -/
def TrueClaims (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))
    (cls : List Verifier.ColumnClaim) : Prop :=
  ∀ cl ∈ cls, TrueClaim prog s q cl

theorem trueClaims_append {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {a b : List Verifier.ColumnClaim} (ha : TrueClaims prog s q a) (hb : TrueClaims prog s q b) :
    TrueClaims prog s q (a ++ b) := by
  intro cl hcl
  rcases List.mem_append.mp hcl with h | h
  exacts [ha cl h, hb cl h]

/-- A true claim on no output lane, placed on the stack by the verifier's layout, holds of the
stack. -/
theorem TrueClaim.holds {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {cl : Verifier.ColumnClaim} (h : TrueClaim prog s q cl)
    (hout : cl.column ∉ keccakOutputColumns) :
    StackClaim.Holds (leanIsaμ prog s) (cl.stackClaim (verifierLayout prog s)) q := by
  obtain ⟨c, z, rfl⟩ := h
  exact (onStack_holds_iff prog s c ((mem_keccakOutputColumns_pyCol c).not.mp hout) z _ q).mpr
    rfl

/-- The point a claim on a column that is not an output lane is placed at has the stack's
length. -/
theorem length_stackPoint (prog : LeanIsaProgram) (s : Sizes) (c : Col) (hc : ¬ IsOut c)
    (z : Vector E (kappa prog s c)) :
    (((verifierLayout prog s).placement (refCol c)).stackPoint z.toList
      (verifierLayout prog s).stackLog).length = leanIsaμ prog s := by
  rw [stackPoint_eq_extend prog s c hc z, Vector.length_toList]

/-- A true claim's weight on no output lane is multilinear on the stack's cube. -/
theorem TrueClaim.multilinear {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {cl : Verifier.ColumnClaim} (h : TrueClaim prog s q cl)
    (hout : cl.column ∉ keccakOutputColumns) :
    IsMultilinearFn (leanIsaμ prog s) (cl.stackClaim (verifierLayout prog s)).1 := by
  obtain ⟨c, z, rfl⟩ := h
  have hm := isMultilinearFn_eqEval (((verifierLayout prog s).placement (refCol c)).stackPoint
    z.toList (verifierLayout prog s).stackLog)
  rw [length_stackPoint prog s c ((mem_keccakOutputColumns_pyCol c).not.mp hout)] at hm
  exact hm

end
end LeanVM.Protocol.EndToEnd.Complete
