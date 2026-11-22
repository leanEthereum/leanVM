/-
  LeanVM.Guest.B1.Tables.VtC.FData

  The statements of the window `x@9 ..< air_acc@6+1` that evaluation alone does not settle, by kind:
  each evaluation's read and limb check, the permutations, and each table's weight division and
  two weight reads; the kernel checks that they and the reads of `fp_w` cover the window.
  The data `vtAirD` and `vtFTags` are `VtC/FDataD.lean`'s (`scripts/b1c-vt/genfdata.py`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FBase
public import LeanVM.Guest.B1.Tables.Vt.EvalsT
public import LeanVM.Guest.B1.Tables.VtC.FDataD
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The window's statements, by kind

`vtAirD[t]`: table `t`'s weight block (position, value `x`): `g^n = x·g^τ` (a division, `g^τ` the
`kappa_base` frame variable `σ (27 + t)`), `cprod` read at `zc_cprod·x`, `peq` read at
`zc_peq·g^τ` (`vtAirT`). `vtEvRest k`: evaluation `k`'s read at the cursor.
`vtF_cover`: the window's statements not settled by evaluation (`autoB`) nor reads of `fp_w`
(`rdFpw`) are, in order, those of `vtFTags` (evaluations, permutations, weight blocks; generated
by `scripts/b1c-vt/genfdata.py`). `noStoreB p`: no store goes through the pointer `.n p`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Table `t`'s `g^τ`: the `kappa_base` frame variable `28 + t`. -/
def vtTauV (t : ℕ) : ℕ := 28 + t

/-- Table `t`'s weight block's first value. -/
def vtAirX (t : ℕ) : ℕ := (vtAirD.getD t (0, 0)).2

/-- Table `t`'s weight block. -/
def vtAirT (t : ℕ) : List Stmt :=
  [.atom (.mul (.n (val% «verify_tables» "g_zc_n")) (.n (vtAirX t)) (.n (vtTauV t))),
    .atom (.mul (.n (vtAirX t + 1)) (.n (val% «verify_tables» "zc_cprod")) (.n (vtAirX t))),
    .atom (.load (.n (vtAirX t + 2)) (.n (vtAirX t + 1)) 0),
    .atom (.mul (.n (vtAirX t + 3)) (.n (val% «verify_tables» "zc_peq")) (.n (vtTauV t))),
    .atom (.load (.n (vtAirX t + 4)) (.n (vtAirX t + 3)) 0)]

theorem vtAirT_check : ∀ t < 6,
    tbStmtsEqb (vtAirT t) ((vtAt (vtAirD.getD t (0, 0)).1).take 5) = true := by
  decide +kernel

/-- Evaluation `k`'s statements evaluation alone does not settle. -/
def vtEvRest (k : ℕ) : List Stmt :=
  [.atom (.load (.n (vtEvB k)) (.n (val% «verify_tables» "cursor@5")) k)]

/-- A read of `fp_w`. -/
def rdFpw : Stmt → Bool
  | .atom (.load _ (.n 13) _) => true
  | _ => false

/-- A kind of statement to settle: an evaluation's (`0`), a permutation (`1`), a weight
block's (`3`). -/
def vtFTagT : ℕ × ℕ → List Stmt
  | (0, k) => vtEvRest k
  | (1, j) => [vtPermT j]
  | (_, t) => (vtAirT t).filter fun s ↦ !autoB s

theorem vtF_cover : tbStmtsEqb (((vtPre.drop vtFLo).take (vtFHi - vtFLo)).filter
    (fun s ↦ !(autoB s || rdFpw s))) (vtFTags.flatMap vtFTagT) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem vtFTags_spec : ∀ q ∈ vtFTags, (q.1 = 0 ∧ q.2 < 153) ∨ (q.1 = 1 ∧ q.2 < 38) ∨
    (q.1 = 3 ∧ q.2 < 6) := by
  decide +kernel

/-- No store goes through the pointer `.n p`. -/
def noStoreB (p : ℕ) : Bool :=
  vtSL.all fun a ↦ match a with
    | .load _ (.n q) _ => q != p
    | _ => true

theorem not_mem_vtSL {p : ℕ} (h : noStoreB p = true) (d : V) (off : ℕ) :
    Atom.load d (.n p) off ∉ vtSL := fun hm ↦ by
  have := List.all_eq_true.mp h _ hm
  simp at this

theorem vtF_noStore : noStoreB 13 = true ∧ noStoreB 2639 = true ∧
    ∀ t < 6, noStoreB (vtAirX t + 1) = true ∧ noStoreB (vtAirX t + 3) = true := by
  decide +kernel

theorem vtF_loadsBelow : loadsBelow [(13, 16), (2639, 153)] = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
