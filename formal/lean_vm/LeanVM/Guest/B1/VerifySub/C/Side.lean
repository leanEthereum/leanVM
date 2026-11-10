/-
  LeanVM.Guest.B1.VerifySub.C.Side

  `verify_sub`'s body holds on its honest valuation when the atoms needing a side condition and
  the dispatches do.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Hon

/-!
# The body from its side conditions

On the honest valuation every atom satisfies its equations (`vs_goodS`), so an atom whose side
condition is automatic (`needsSide` false: constants, sums, copies, products, `KECCAK`, hints)
holds. `vsCPre_holds_of`: with the others (`hside`: loads, range checks, two quotients) and the
dispatches' indices (`hdisp`), the body holds under the trivial call relation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables

@[expose] public section

/-- Not a conditional call. -/
def noCallIfB : Stmt → Bool
  | .callIf .. => false
  | _ => true

theorem vs_straight : vsCPre.all straightB = true := by decide +kernel

theorem vs_noCallIf : vsCPre.all noCallIfB = true := by decide +kernel

theorem side_of_not_needs {rd : Reader} {S : List Atom} {σ : Val} {a : Atom}
    (h : needsSide a = false) : Side rd S σ a := by
  cases a with
  | mul d x y =>
    simp only [needsSide, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Side]
    rw [ite_pos' h]
    trivial
  | load | assertEq | assertInK | assertNe | rangeCheck | frameAddr => simp [needsSide] at h
  | _ => trivial

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **The body holds** under the trivial call relation, from the atoms needing a side condition
and the dispatches' indices. -/
theorem vsCPre_holds_of (hl : args.length = 6)
    (hside : ∀ a, Stmt.atom a ∈ vsCPre → needsSide a = true → a.Holds rd (vsσ rd w args))
    (hdisp : ∀ x fs as rs, Stmt.dispatch x fs as rs ∈ vsCPre →
      ∃ j < fs.length, vsσ rd w args x = ofK (addressOfIndex j))
    {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList (fun _ _ _ ↦ True) rd (vsσ rd w args) vsCPre next kret := by
  refine holdsList_straightN vsCPre vs_straight (fun s hs ↦ ?_) hn
  cases s with
  | atom a =>
    cases hns : needsSide a
    · have hg := vs_goodS (rd := rd) (w := w) hl hs
      exact holds_of_good hg (side_of_not_needs hns)
    · exact hside a hs hns
  | call f as rs => trivial
  | dispatch x fs as rs =>
    obtain ⟨j, hj, hx⟩ := hdisp x fs as rs hs
    exact ⟨j, hj, hx, trivial⟩
  | callIf c f as => simpa [noCallIfB] using List.all_eq_true.mp vs_noCallIf _ hs
  | _ => simpa [straightB] using List.all_eq_true.mp vs_straight _ hs

end
end LeanVM.Guest.B1.VerifySub
