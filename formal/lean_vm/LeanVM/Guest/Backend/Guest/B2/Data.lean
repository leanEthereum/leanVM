/-
  LeanVM.Guest.Backend.Guest.B2.Data

  What the bridge from the back end to the certificates' contracts reads of the certificates'
  data, as one decidable test per function.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.Backend.Guest.World
public import LeanVM.Guest.Backend.Guest.B2.Sig

/-!
# The certificates' data against the back end's

Function `j ≥ 1` of the compiled guest is `coreOf j`, entry `j - 1` of the back end's input
`guestTraced` (`infoOf j`: its trace, return cells and loop flags). `dataOk j` tests, of the
certificate's signature `sigOf j` (data only: no window, cut or check of the certificate is read):

* `sigOk`: its bounds, reads and relations against `guestTab` and `xSpecOf` (`B2/Sig.lean`);
* its return words are the back end's return cells;
* its entry environment is the self pointer `fp` past the arguments exactly for a registered loop
  helper (`envOk`);
* each bound it promises at the return is one the table's postcondition gives;
* its entry is past `__jump_tables` and before the halting slot.

The kernel decides it for every function (`B2/Eval/*`).
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend.Obl
open LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

/-- What the back end's input holds of function `j ≥ 1` besides its core function. -/
def infoOf (j : ℕ) : Array Event × Nat × Bool × Option Nat := GuestData.guestInfo.getD (j - 1) default

/-- What a caller knows of compiled function `j` (`Guest.sigOf`, the certificate's signature). -/
noncomputable abbrev csig (j : ℕ) : Check.Sig := LeanVM.Guest.sigOf j

/-- The entry environment is the self pointer past the arguments exactly for a registered loop
helper. -/
def envOk (env : List (ℕ × Sym)) (reg : Bool) (na : ℕ) : Bool :=
  match env with
  | [] => !reg
  | [(o, .fpg 0)] => reg && o == 2 + na
  | _ => false

/-- The bounds a signature promises at the return are the table's. -/
def postOk (cs : Check.Sig) (ts : Obl.Sig) : Bool :=
  cs.post.all fun p => ts.post.any fun q =>
    q.1 + 2 == p.1 && decide (q.2 ≤ p.2) && decide (q.1 < cs.nargs + cs.nret)

/-- **The test of function `j`'s certificate data.** -/
noncomputable def dataOk (j : ℕ) : Bool :=
  sigOk (csig j) (guestTab.sig (coreOf j).name) (xSpecOf (coreOf j).name) &&
    (csig j).nret == (infoOf j).2.1 &&
    envOk (csig j).env (isLoopName (coreOf j).name && (infoOf j).2.2.1) (csig j).nargs &&
    postOk (csig j) (guestTab.sig (coreOf j).name) &&
    decide (Data.f0.instructionCount ≤ (csig j).entry) && decide ((csig j).entry + 1 < 2 ^ 19)

/-- The parts of `dataOk`. -/
theorem dataOk_spec {j : ℕ} (h : dataOk j = true) :
    sigOk (csig j) (guestTab.sig (coreOf j).name) (xSpecOf (coreOf j).name) = true ∧
      (csig j).nret = (infoOf j).2.1 ∧
      envOk (csig j).env (isLoopName (coreOf j).name && (infoOf j).2.2.1) (csig j).nargs = true ∧
      postOk (csig j) (guestTab.sig (coreOf j).name) = true ∧
      Data.f0.instructionCount ≤ (csig j).entry ∧ (csig j).entry + 1 < 2 ^ 19 := by
  simp only [dataOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end
end LeanVM.Guest.Backend.B2
