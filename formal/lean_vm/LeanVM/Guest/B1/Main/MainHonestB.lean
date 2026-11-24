/-
  LeanVM.Guest.B1.Main.MainHonestB

  `main` placed on a node's honest run within its words, before any memory: from its callees
  within their bounds, `main`'s size at most `mainB` of their bounds.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestT
public import LeanVM.Guest.B1.Main.MainGoalsStaticB
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings

/-!
# `main` on an honest run, within its words

`MainBs`: the bounds of `main`'s non-static callees (its claim lists' digests, `da_verify`,
`aggregate_claims`, the children's loop). `mBs`: every callee's bound, aligned with `mKids`: the
static ones' (`SB`, the loops' counts times `SK`), then `MainBs`'.
`MainStaticGoalsB`: the static callees within those bounds (`mainStaticGoalsB_of`).
`MainPreds.withTotal`: each non-static callee's predicate with its tree's words within its bound.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within Kid CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB Returns
  kidsBoundL)

@[expose] public section

/-- **The bounds of `main`'s non-static callees.** -/
structure MainBs where
  Bx : ℕ
  Bs : ℕ
  Bd : ℕ
  Ba : ℕ
  B5 : ℕ

/-- **Every callee's bound**, aligned with `mKids`. -/
def mBs (fs SB SK : String → ℕ) (m : MainIn) (b : MainBs) : List ℕ :=
  [b.Bx, b.Bs, m.nxd * iterK fs SK name% «main_loop0» + fs name% «main_loop0»,
      m.nsd * iterK fs SK name% «main_loop1» + fs name% «main_loop1»,
    m.nrx * iterK fs SK name% «main_loop2» + fs name% «main_loop2»,
        m.nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3»] ++ (if m.nd = 1 then [b.Bd]
        else []) ++ [b.B5] ++
    (if m.nc = 0 then [] else [b.Ba]) ++ [SB "statement_digest"]

/-- **`main`'s words**, its callees within `mBs`. -/
def mainBH (fs : String → ℕ) (SB SK : String → ℕ) (d : MainData) (m : MainIn) (Lin : Layout)
    (b : MainBs) : ℕ :=
  mainB fs d (mKids m Lin) (mBs fs SB SK m b)

/-- Each non-static callee's predicate, its tree's words within its bound. -/
def MainPreds.withTotal (p : MainPreds) (fs : String → ℕ) (b : MainBs) : MainPreds :=
  ⟨fun t => p.Px t ∧ t.total fs ≤ b.Bx, fun t => p.Ps t ∧ t.total fs ≤ b.Bs,
    fun t => p.Pd t ∧ t.total fs ≤ b.Bd, fun t => p.Pa t ∧ t.total fs ≤ b.Ba,
    fun t => p.T5 t ∧ t.total fs ≤ b.B5⟩

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- **`main`'s static callees within their bounds.** -/
structure MainStaticGoalsB (SB SK : String → ℕ) : Prop where
  l1 : MainGoalL1B fs cert fp seed s w SK
  l2 : MainGoalL2B fs cert fp seed s w SK
  l3 : MainGoalL3B fs cert fp seed s w SK
  l4 : MainGoalL4B fs cert fp seed s w SK
  st : MainGoalStB fs cert fp seed s w SB

variable {fs cert fp seed s w} {bytecode : List K}

/-- **The static bounds of `main`'s own static callees** (G7-cnt's certificates). -/
structure MainStaticsMain (fs : String → ℕ) (SB SK : String → ℕ) : Prop where
  l1 : TotalLeOn coreProgram fs name% «main_loop0» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop0» + fs name% «main_loop0»)
  l2 : TotalLeOn coreProgram fs name% «main_loop1» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop1» + fs name% «main_loop1»)
  l3 : TotalLeOn coreProgram fs name% «main_loop2» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop2» + fs name% «main_loop2»)
  l4 : TotalLeOn coreProgram fs name% «main_loop3» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop3» + fs name% «main_loop3»)
  st : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest")

/-- **`main`'s static callees on the honest run, within their bounds.** -/
theorem mainStaticGoalsB_of {SB SK : String → ℕ} (hbl : bytecode.length = 2 ^ 23)
    (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.SphincsCompleteSpecs) (hS : MainStaticsMain fs SB SK) :
    MainStaticGoalsB fs cert fp seed s w SB SK := by
  have hb : MainBounds (2 ^ 23) (hm fs fp seed s w) := hData_bounds hl fs fp
  exact ⟨mainGoalL1B hS.l1 (by have := hb.xd; omega), mainGoalL2B hS.l2 (by have := hb.sd; omega),
    mainGoalL3B hr hl hxc hS.l3, mainGoalL4B hr hl hsc hS.l4, mainGoalStB hr hbl hS.st⟩

end
end LeanVM.Guest.B1.Main
