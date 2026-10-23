/-
  LeanVM.Protocol.EndToEnd.Complete.Claims

  The claims an honest run accumulates: a verifier column claim whose value is the true extension
  of an instance column, placed on the stack by the verifier's layout, holds of the stack and has a
  multilinear weight.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance
public import LeanVM.Protocol.Whir.Complete.Tables

/-!
# True column claims

The verifier program (`LeanVM.Protocol.Verifier`, `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) accumulates column claims as data
(`Verifier.ColumnClaim`: a global column, a point, a value) and opens them on the stack through
its layout (`ColumnClaim.onStack`). Against the honest prover every claim it accumulates is a
*true claim* (`TrueClaim`): the global column is the Python number `pyCol c` of an instance
column `c`, the point is a point `z` of the column's own variables, and the value is the
extension of the column read off the stack at `z` (`colEval`).

For the stack `q` of the leanISA instance with the BLAKE2s Flock specification (`inst`), a true
claim is what the opening needs of it (`Whir.Complete.follows_verifyStackedOpening`):

* `TrueClaim.holds`: placed on the stack it holds of `q` (`StackClaim.Holds`), by the layout
  correspondence `Front.onStack_holds_iff`;
* `TrueClaim.multilinear`: its weight `eq(placed point, ·)` is multilinear on the stack's cube,
  the placed point being the instance's lift of `z`, of the stack's length
  (`Front.stackPoint_eq_extend`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete CompPoly CMlPolynomialEval

@[expose] public section

/-- The instance the deployed verifier is complete for: leanISA with the BLAKE2s Flock
specification. -/
abbrev inst (prog : Program) (s : Sizes) : M3Instance :=
  leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s

/-- The true value of an instance column at a point of its variables: the column's extension,
the column read off the stack through the instance's layout. -/
def colEval (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (c : Col)
    (z : Vector E (kappa prog s c)) : E :=
  eval₂Mle ((inst prog s).column q c).values (algebraMap K E) z

/-- A **true claim**: a verifier column claim on the Python number of an instance column, at a
point of the column's variables, whose value is the column's true value there. -/
def TrueClaim (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (cl : Verifier.ColumnClaim) : Prop :=
  ∃ c : Col, ∃ z : Vector E (kappa prog s c), cl = ⟨pyCol c, z.toList, colEval prog s q c z⟩

/-- Every claim of a list is true. -/
def TrueClaims (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (cls : List Verifier.ColumnClaim) : Prop :=
  ∀ cl ∈ cls, TrueClaim prog s q cl

theorem trueClaims_append {prog : Program} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {a b : List Verifier.ColumnClaim} (ha : TrueClaims prog s q a) (hb : TrueClaims prog s q b) :
    TrueClaims prog s q (a ++ b) := by
  intro cl hcl
  rcases List.mem_append.mp hcl with h | h
  exacts [ha cl h, hb cl h]

/-- A true claim, placed on the stack by the verifier's layout, holds of the stack. -/
theorem TrueClaim.holds {prog : Program} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {cl : Verifier.ColumnClaim} (h : TrueClaim prog s q cl) :
    StackClaim.Holds (leanIsaμ prog s) (cl.onStack (verifierLayout prog s)) q := by
  obtain ⟨c, z, rfl⟩ := h
  exact (onStack_holds_iff prog s Blake2sFlock.blake2sFlockSpec rfl c z _ q).mpr rfl

/-- The point a true claim is placed at has the stack's length. -/
theorem length_stackPoint (prog : Program) (s : Sizes) (c : Col)
    (z : Vector E (kappa prog s c)) :
    (((verifierLayout prog s).placements.getD (pyCol c) default).stackPoint z.toList
      (verifierLayout prog s).stackLog).length = leanIsaμ prog s := by
  rw [stackPoint_eq_extend prog s Blake2sFlock.blake2sFlockSpec rfl c z, Vector.length_toList]

/-- A true claim's weight is multilinear on the stack's cube. -/
theorem TrueClaim.multilinear {prog : Program} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {cl : Verifier.ColumnClaim} (h : TrueClaim prog s q cl) :
    IsMultilinearFn (leanIsaμ prog s) (cl.onStack (verifierLayout prog s)).1 := by
  obtain ⟨c, z, rfl⟩ := h
  have hm := isMultilinearFn_eqEval (((verifierLayout prog s).placements.getD (pyCol c)
    default).stackPoint z.toList (verifierLayout prog s).stackLog)
  rw [length_stackPoint] at hm
  exact hm

end
end LeanVM.Protocol.EndToEnd.Complete
