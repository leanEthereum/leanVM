/-
  LeanVM.Guest.B1.Main.MainGoalsHL5TB

  `main`'s honest children loop within a bound before the memory (`CompleteAtDTB`): the bounds and
  the goals, proved in `L5R.lean`.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.B1.Main.KidCoverAtB
public import LeanVM.Guest.B1.Main.ChildListGoalsTB
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop4»

/-!
# The children loop, bounded

`l5K SB Bx Bs Bv`: an iteration's words but its frame and its tail call's: its claim lists'
digests (`Bx`, `Bs`), `statement_digest` (`SB`), `verify_sub` (`Bv`). `l5ChainB`: the chain's words.
`VerifySubGoalsTB`, `MainGoalL5TB`, `l5B`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds regionL_of_mem limb0_gen_pow_mul exists_of_length_succ
  fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB CompleteAtL completeAtL_tail KidsDTB
  kidsBoundL Returns Kid OutsOk CallsMatch RegionsOk outRegion
  DisjL Within disj_append disj_nil kidsFromIn_of_kidsD regionsOk_of within_append bufL bufL_within
  bufL_disj bufL_region LowDef)

@[expose] public section

/-- **An iteration's words but its frame and its tail call's.** -/
def l5K (SB : String → ℕ) (Bx Bs Bv : ℕ) : ℕ := Bx + Bs + SB "statement_digest" + Bv

/-- **`main_loop4`'s words over its last `t + 1` iterations from child `c`**: each iteration's frame
and constant part `K c`, the last one's phantom tail call's tail. -/
def l5ChainB (fs : String → ℕ) (K : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, c => fs name% «main_loop4» + fs (tailKey name% «main_loop4») + K c
  | t + 1, c => fs name% «main_loop4» + l5ChainB fs K t (c + 1) + K c

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **Each child's `verify_sub` call complete within `Bv c`, by a tree satisfying `Pvs c`.** -/
def VerifySubGoalsTB (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (Pvs : ℕ → Tree → Prop) (Bv : ℕ → ℕ) : Prop :=
  ∀ c (hc : c < w.children.length), CompleteAtDTB fs cert 20 "verify_sub" (hLmain fs fp seed s w)
    [(digestHalves (statementDigest seed w.children[c].statement)).1,
      (digestHalves (statementDigest seed w.children[c].statement)).2,
      (digestHalves seed).1, (digestHalves seed).2, (hm fs fp seed s w).et,
      (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns []) (Pvs c) (Bv c)

/-- The children's loop complete within `B5` by trees satisfying `T5`. -/
def MainGoalL5TB (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (T5 : Tree → Prop) (B5 : ℕ) : Prop :=
  (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTB fs cert 23 name% «main_loop4» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns []) T5 B5

/-- **The honest children loop's words bound**: `l5ChainB` over the `nc` children, child `c`'s
iteration within its frame and its callees' bounds (`l5K`). -/
def l5B (fs : String → ℕ) (SB : String → ℕ) (Bxs Bss Bv : ℕ → ℕ) (w : NodeWitness) : ℕ :=
  l5ChainB fs (fun c => l5K SB (Bxs c) (Bss c) (Bv c)) (w.children.length - 1) 0

end
end LeanVM.Guest.B1.Main
