/-
  LeanVM.Guest.B1.Main.MainGoalsHL5TB

  `main`'s honest children loop's words bound before the memory.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.B1.Main.KidCoverAtB
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop4»

/-!
# The children loop, bounded

`l5K SB Bx Bs Bv`: an iteration's words but its frame and its tail call's: its claim lists'
digests (`Bx`, `Bs`), `statement_digest` (`SB`), `verify_sub` (`Bv`). `l5ChainB`: the chain's words.
`l5B`: the loop's words over the honest children.
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

/-- **The honest children loop's words bound**: `l5ChainB` over the `nc` children, child `c`'s
iteration within its frame and its callees' bounds (`l5K`). -/
def l5B (fs : String → ℕ) (SB : String → ℕ) (Bxs Bss Bv : ℕ → ℕ) (w : NodeWitness) : ℕ :=
  l5ChainB fs (fun c => l5K SB (Bxs c) (Bss c) (Bv c)) (w.children.length - 1) 0

end
end LeanVM.Guest.B1.Main
