/-
  LeanVM.Guest.CoreMode.CoreResG

  A heap certificate's residuals of families: the generic families' (`CoreRes.lean`), and each function's own
  (`FnReg.fams`, `FnReg.gwFams`).
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.CoreResS
public import LeanVM.Guest.CoreMode.Gen.FnFams

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **A residual of a function's own family**, ghost-free (`FnReg.fams`). -/
noncomputable def ownFam (fn : Fn) (r : CRes) : Bool := FnReg.fams.any fun p ↦ fn.name == p.1 && p.2 fn r

/-- **A residual of a function's own family over its own parameter words as ghosts** (`FnReg.gwFams`), its ghost
slots `gw` some. -/
noncomputable def gwFam (fn : Fn) (gw : List (CCell × ℕ)) (r : CRes) : Bool :=
  !gw.isEmpty && FnReg.gwFams.any fun p ↦ fn.name == p.1 && p.2 fn gw r

/-! ## An own parameter word's ghost as the value read at its cell -/

/-- An index with the value `a` renamed `b`. -/
def CIdx.ren (a b : ℕ) : CIdx → CIdx
  | .num n => .num n
  | .val v => .val (if v = a then b else v)
  | .mono c => .mono ⟨c.bases.map fun p ↦ (if p.1 = a then b else p.1, p.2), c.off⟩

/-- A residual with the value `a` renamed `b` in its exponent comparisons (under their conditions). -/
def CRes.ren (a b : ℕ) : CRes → CRes
  | .lt x y => .lt (x.ren a b) (y.ren a b)
  | .under g r => .under g (r.ren a b)
  | r => r

/-- The value the first top-level `load` reads at `[p]·g^d`. -/
def ldAtP (as : List Atom) (p : V) (d : ℕ) : Option V :=
  as.findSome? fun
    | .load x p' d' => if p' = p ∧ d' = d then some x else none
    | _ => none

/-- An own parameter word's cell `[p]·g^d`. -/
def gwCell (c : CCell) : Option (ℕ × ℕ) :=
  match c.bases with
  | [(p, e)] => if e = 1 then some (p, c.off) else none
  | _ => none

/-- **An own parameter word's ghost renamed** (`HSig.gw`): ghost `GB + j` of the word at `[p]·g^d`, `p < GB`, is the
value `y` the first top-level `load` reads there; with it renamed `y`, a ghost-free residual of the exponent and
dimension facts (`resQ`). -/
noncomputable def gwAlias (fn : Fn) (gw : List (CCell × ℕ)) (r : CRes) : Bool :=
  gw.any fun x ↦ match gwCell x.1 with
    | some (p, d) => decide (p < GB) && match ldAtP (Res.topAtoms fn.body) (V.n p) d with
      | some y => decide (y = V.n y.idx) && decide (y.idx < GB) && resQ fn (r.ren (GB + x.2) y.idx) &&
          (r.ren (GB + x.2) y.idx).vals.all (Nat.blt · GB)
      | none => false
    | none => false

/-- **A residual of a family**, ghost-free (`resFam`, `resQ`, `rcPts`, `rcTab`, the function's own `ownFam`, its values
below `GB`), or of a ghost family (`ml`, `st`, `cm`, the function's own over its own parameter words `gwFam`, an own
parameter word's ghost as the value read at its cell `gwAlias`). -/
noncomputable def resFamG (fn : Fn) (xc : List ℕ) (gw : List (CCell × ℕ)) (r : CRes) : Bool :=
  ((resFam fn xc r || resQ fn r || rcPts fn r || rcTab fn r || ownFam fn r) && r.vals.all (Nat.blt · GB)) ||
    mlSub fn r || stSub fn r || cmSub fn r || gwFam fn gw r || gwAlias fn gw r

/-- **A residual of a family** (`resFamG`), or a symbolic run inside a constant run whose bounds the certificate's
own facts give (`subRS`). -/
noncomputable def resOkR (Cf : CFun) (r : CRes) : Bool := resFamG Cf.fn Cf.xc Cf.H.sig.gw r || subRS Cf.H.res r

/-- **Every residual of the function's heap certificate of a family.** -/
noncomputable def resOk (Cf : CFun) : Bool := Cf.H.res.all (resOkR Cf)

/-- **The ghost family's links** (`ml`): its caller's cells as its function's data says (`mlK`: the entries table
its one ghost slot, the bound its parameter `limit`); it names no ghost value. -/
noncomputable def mlGl (Cf : CFun) : Bool :=
  (mlK Cf.fn).any (fun p ↦ decide (Cf.gl = p.2.2.2.2.2)) && Nat.beq Cf.H.sig.ghosts 1 && ngB Cf.fn

/-- **A loop callee of `anyLink`'s links**: its caller's cell `2` its entries parameter, cell `5` its bound parameter
times `g` (`anyLink`'s), its caller's frame address its one ghost slot, after its parameters; it names no ghost
value. -/
noncomputable def alGl (Cf : CFun) : Bool :=
  Res.anyLink.fams.any (fun F ↦ Cf.fn.name == F.1 &&
    decide (Cf.gl = [(2, F.2.1, 0), (5, F.2.2, 1), (0, Cf.fn.params.length, 0)])) &&
    Nat.beq Cf.H.sig.ghosts 1 && ngB Cf.fn && Cf.H.sig.gw.isEmpty

/-- **Own parameter words as the ghost slots** (`HSig.gw`): ghost `j` the word at the `j`-th cell, one per ghost, over
values below `GB`, and the function naming no ghost value (`ngB`). -/
def gwSlots (Cf : CFun) : Bool :=
  Nat.beq Cf.H.sig.ghosts Cf.H.sig.gw.length && decide (Cf.H.sig.gw.map (·.2) = List.range Cf.H.sig.gw.length) &&
    (Cf.H.sig.gw.all fun x ↦ x.1.bases.all fun b ↦ Nat.blt b.1 GB) && ngB Cf.fn

/-- **An instance's ghost words, its own parameter words** (`gwSlots`): ghost `j` the reference's word at the `j`-th
cell's address at `σ` (`setG`), `GwR`. -/
theorem gwR_setG {κ : ℕ} {img : MemoryImage κ} {Cf : CFun} {σ : Val} (h : gwSlots Cf = true) :
    GwR img Cf.H.sig (setG σ (Cf.H.sig.gw.map fun x ↦ (img.read (x.1.addrW (vw σ))).getD 0)) := by
  intro c j hc
  simp only [gwSlots, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨hgh, hix⟩, hlt⟩, -⟩ := h
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have hij : j = i := by
    have h1 := congrArg (·[i]?) hix
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, hci, Option.map_some] at h1
    rw [List.getElem?_range hi] at h1
    exact Option.some.inj h1
  subst hij
  have haddr : c.addrW (vw (setG σ (Cf.H.sig.gw.map fun x ↦ (img.read (x.1.addrW (vw σ))).getD 0))) =
      c.addrW (vw σ) := by
    unfold CCell.addrW
    rw [valW_congr fun b hb ↦ ?_]
    exact setG_eq (show (V.n b.1).idx < GB from hlt (c, j) hc b hb)
  rw [haddr]
  have hO := ownG_setG (G := Cf.H.sig) (σ := σ)
    (gw := Cf.H.sig.gw.map fun x ↦ (img.read (x.1.addrW (vw σ))).getD 0) (by rw [List.length_map, hgh])
  have hj : j < Cf.H.sig.ghosts := by rw [hgh]; exact hi
  have h2 := congrArg (·[j]?) hO
  simp only [ownG, List.getElem?_map, List.getElem?_range hj, Option.map_some, List.getElem?_eq_getElem hi,
    hci] at h2
  exact Option.some.inj h2

/-- **The caller's cells linked** (`CFun.gl`), of a family: none, or those of a callee of `anyLink` (a read of
its caller's entries table, `Res.LinkDefs`): the caller's cell `2` its entries parameter, cell `5` its bound
parameter times `g`, with no ghost slot, or for a loop the same and its caller's frame address its one ghost slot
(`alGl`); for a ghost family specialization its function's (`mlGl`); for a cursor-run loop its caller's
run's base, bound and frame (`stGl`); for a frame loop over its caller's table its caller's entries, bound and frame (`cmGl`); or
none, the ghost slots own parameter words (`gwSlots`). -/
noncomputable def glOk (Cf : CFun) : Bool :=
  bif (cmK Cf.fn).isSome then cmGl Cf && Cf.H.sig.gw.isEmpty else
  bif (stK Cf.fn).isSome then stGl Cf && Cf.H.sig.gw.isEmpty else
  bif (mlK Cf.fn).isSome then mlGl Cf && Cf.H.sig.gw.isEmpty else
    ((Cf.gl.isEmpty || Res.anyLink.fams.any fun F ↦ Cf.fn.name == F.1 && decide (Cf.gl = [(2, F.2.1, 0), (5, F.2.2, 1)]))
      && Nat.beq Cf.H.sig.ghosts 0 && Cf.H.sig.gw.isEmpty) || (Cf.gl.isEmpty && gwSlots Cf) || alGl Cf

end

end LeanVM.Guest.CoreMode
