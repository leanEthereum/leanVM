/-
  LeanVM.Guest.B1.Main.MainHonestBudgetB

  `main`'s words on a node's honest run (G7's budget), `Bmain`: an explicit function of the statement, the witness,
  the static bounds and `verify_sub`'s bound.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestB
public import LeanVM.Guest.B1.Main.MainHonestBudget
public import LeanVM.Guest.B1.Main.MainGoalsClTB
public import LeanVM.Guest.B1.Main.MainGoalsHClTBP
public import LeanVM.Guest.B1.Main.MainGoalsDvT
public import LeanVM.Guest.B1.Main.MainCoverLemmas
public import LeanVM.Guest.B1.Da.DvBound
public import LeanVM.Guest.B1.Main.MainGoalsHAgTB
public import LeanVM.Guest.B1.Main.L5R
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings

/-!
# `main` on an honest run, within its words

`MainStatics fs SB SK`: the static bounds every statically bounded callee in `main`'s tree takes
(G7-cnt's certificates): `SB g` bounds every valid tree of a static callee `g`
(`TotalLe`), a static loop helper `g`'s run `iterK fs SK g` words per iteration and its phantom
frame `fs g` once (`TotalLeOn … LoopPre`).
`hDvB`: `da_verify`'s bound at the directly held DA claim's witness. `mainBsH`: the non-static callees' bounds
(`clB`, `hDvB`, `aggB`, `l5B` with `ccBM`), `Bmain`: `main`'s, `mainBH` at those.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within CompleteAtDTB Returns)

@[expose] public section

/-- **The static bounds of `main`'s tree** (G7-cnt's certificates at `fs`). -/
structure MainStatics (fs : String → ℕ) (SB SK : String → ℕ) : Prop where
  main : MainStaticsMain fs SB SK
  dv : Da.DvStaticB fs SB SK
  ls : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")
  l15 : TotalLeOn coreProgram fs name% «claim_list_chain_loop0» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_chain_loop0» + fs
        name% «claim_list_chain_loop0»)
  l16 : TotalLeOn coreProgram fs name% «claim_list_chain_loop1» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_chain_loop1» + fs
        name% «claim_list_chain_loop1»)
  cl : TotalLe coreProgram fs "claim_list_tail" (fun _ => SB "claim_list_tail")
  l25 : TotalLeOn coreProgram fs name% «aggregate_claims_loop0» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop0» + fs
        name% «aggregate_claims_loop0»)
  l26 : TotalLeOn coreProgram fs name% «aggregate_claims_loop1» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop1» + fs
        name% «aggregate_claims_loop1»)
  l27 : TotalLeOn coreProgram fs name% «aggregate_claims_loop2» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop2» + fs
        name% «aggregate_claims_loop2»)
  bs : TotalLe coreProgram fs "batch_sumcheck__L23" (fun _ => SB "batch_sumcheck__L23")

/-- **`da_verify`'s words bound on the checked DA claim's witness.** -/
def hDvB (fs : String → ℕ) (SB SK : String → ℕ) (w : NodeWitness) : ℕ :=
  (w.daMatrix.map fun p => Da.dvB fs SB SK p.2.rows.length (Da.wLog p.2)).getD 0

/-- **The bounds of `main`'s non-static callees** on the honest run: its claim lists' digests
(`clB`), `da_verify` (`hDvB`), `aggregate_claims` (`aggB`), the children's loop (`l5B`, each
child's claim lists' digests within `ccBM`, child `c`'s `verify_sub` within `Bv c`). -/
def mainBsH (fs : String → ℕ) (SB SK : String → ℕ) (Bv : ℕ → ℕ) (s : NodeStatement) (w : NodeWitness) :
    MainBs :=
  ⟨B1.Digest.clB fs SB SK s.claims.xmss.length, B1.Digest.clB fs SB SK s.claims.sphincs.length,
    hDvB fs SB SK w, aggB fs SB SK w.children.length,
    l5B fs SB (fun c => B1.Digest.ccBM fs SB (hMonoX s w c) (hKid s w c).ex)
      (fun c => B1.Digest.ccBM fs SB (hMonoS s w c) (hKid s w c).es) Bv w⟩

/-- **`main`'s words on the honest run** at `fp`: its frame and buffers, `exponent_tables`', every
other callee's bound (`mBs`, `kidsBoundL` over `mKids`). -/
def Bmain (fs : String → ℕ) (SB SK : String → ℕ) (Bv : ℕ → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) : ℕ :=
  mainBH fs SB SK (hData seed s w) (hm fs fp seed s w) (hLmain fs fp seed s w) (mainBsH fs SB SK Bv s w)

end
end LeanVM.Guest.B1.Main
