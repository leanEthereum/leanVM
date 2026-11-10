/-
  LeanVM.Guest.B1.Main.MainHonestBudgetB

  **`main`'s completeness on a node's honest run within its words** (G7's budget): `main` at `fp`
  within `Bmain`, an explicit function of the statement, the witness, the static bounds and
  `verify_sub`'s bound, before any memory; its non-static callees' trees of honest shape and within
  their bounds.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestB
public import LeanVM.Guest.B1.Main.MainHonestBudget
public import LeanVM.Guest.B1.Main.MainGoalsClTB
public import LeanVM.Guest.B1.Main.MainGoalsHClTB
public import LeanVM.Guest.B1.Main.MainGoalsDvTB
public import LeanVM.Guest.B1.Main.MainGoalsHAgTB
public import LeanVM.Guest.B1.Main.MainGoalsHL5TB
public import LeanVM.Guest.AcceptableChild

/-!
# `main` on an honest run, within its words

`MainStatics fs SB SK`: the static bounds every statically bounded callee in `main`'s tree takes
(G7-cnt's certificates): `SB g` bounds every valid tree of a static callee `g`
(`TotalLe`), a static loop helper `g`'s run `iterK fs SK g` words per iteration and its phantom
frame `fs g` once (`TotalLeOn … LoopPre`).
`mainBsH`: the non-static callees' bounds (`clB`, `hDvB`, `aggB`, `l5B` with `ccB`), `Bmain`:
`main`'s, `mainBH` at those. `main_honest_budgetB`: `main` within `Bmain`, its callees' trees
`mainPredsH`, each non-static one within its bound (`MainPreds.withTotal`).
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
  l15 : TotalLeOn coreProgram fs "__loop15" LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK "__loop15" + fs "__loop15")
  l16 : TotalLeOn coreProgram fs "__loop16" LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK "__loop16" + fs "__loop16")
  cl : ∀ j < 17, TotalLe coreProgram fs B1.Digest.clNames[j]! (fun _ => SB B1.Digest.clNames[j]!)
  l25 : TotalLeOn coreProgram fs "__loop33" LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK "__loop33" + fs "__loop33")
  l26 : TotalLeOn coreProgram fs "__loop34" LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK "__loop34" + fs "__loop34")
  l27 : TotalLeOn coreProgram fs "__loop35" LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK "__loop35" + fs "__loop35")
  bs : TotalLe coreProgram fs "batch_sumcheck__L23" (fun _ => SB "batch_sumcheck__L23")
  gr : TotalLe coreProgram fs "grind_check__L2" (fun _ => SB "grind_check__L2")

/-- **The bounds of `main`'s non-static callees** on the honest run: its claim lists' digests
(`clB`), `da_verify` (`hDvB`), `aggregate_claims` (`aggB`), the children's loop (`l5B`, each
child's claim lists' digests within `ccB`, child `c`'s `verify_sub` within `Bv c`). -/
def mainBsH (fs : String → ℕ) (SB SK : String → ℕ) (Bv : ℕ → ℕ) (s : NodeStatement) (w : NodeWitness) :
    MainBs :=
  ⟨B1.Digest.clB fs SB SK s.claims.xmss.length, B1.Digest.clB fs SB SK s.claims.sphincs.length,
    hDvB fs SB SK w, aggB fs SB SK w.children.length,
    l5B fs SB (fun c => B1.Digest.ccB fs SB (hKid s w c).ex) (fun c => B1.Digest.ccB fs SB (hKid s w c).es)
      Bv w⟩

/-- **`main`'s words on the honest run** at `fp`: its frame and buffers, `exponent_tables`', every
other callee's bound (`mBs`, `kidsBoundL` over `mKids`). -/
def Bmain (fs : String → ℕ) (SB SK : String → ℕ) (Bv : ℕ → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) : ℕ :=
  mainBH fs SB SK (hData seed s w) (hm fs fp seed s w) (hLmain fs fp seed s w) (mainBsH fs SB SK Bv s w)

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`main`'s non-static callees on the honest run within their bounds, by trees of honest
shape**. -/
theorem mainGoalsTB_honest {SB SK : String → ℕ} {Pvs : ℕ → Tree → Prop} {Bv : ℕ → ℕ}
    (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) (hl : DeployedLimits s w)
    (hrf : Lift.RunsFit fs cert) (hS : MainStatics fs SB SK)
    (hV : VerifySubGoalsTB fs cert fp seed s w Pvs Bv) :
    MainGoalsTB fs cert fp seed s w (mainPredsH s w (hDvNH w) Pvs) (mainBsH fs SB SK Bv s w) :=
  ⟨mainGoalClXTB fs cert fp seed s w hl hS.ls hS.l15 hS.l16 hS.cl,
    mainGoalClSTB fs cert fp seed s w hl hS.ls hS.l15 hS.l16 hS.cl,
    mainGoalDvTB fs cert fp hr hrf hS.dv,
    mainGoalAgTB fs fp cert SB SK hS.gr hS.l25 hS.l26 hS.l27 hS.bs hbl hr hl,
    mainGoalL5TB fs cert SB hS.main.st hbl hr hl hV (childListGoalsTB_honest cert hl hS.ls)⟩

/-- **`main`'s completeness on the honest run within its words**: for `NodeRelation` within `Limits`
and a bytecode of `2^23` words, from the signature schemes' completeness (B1-e), the frame runs'
certificate facts, the static bounds (`MainStatics`, `grind_check__L2`'s among them), and child `c`'s `verify_sub` within `Bv c` by a
tree satisfying `Pvs c` (B1-d): a size `n ≤ Bmain` and a layout `L` within `[fp, fp + n)`, above
`main`'s frame, pairwise disjoint, containing `main`'s honest words; on every memory holding `L`
and the statement's digest at words `0`, `1`, `main` holds at `fp` by its node at its honest
values, its walk's calls and buffers, its callees' trees satisfying `mainPredsH` and, the
non-static ones, within their bounds. -/
theorem main_honest_budgetB {SB SK : String → ℕ} {Pvs : ℕ → Tree → Prop} {Bv : ℕ → ℕ}
    (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) (hl : DeployedLimits s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.SphincsCompleteSpecs) (hrf : Lift.RunsFit fs cert)
    (hS : MainStatics fs SB SK)
    (hV : VerifySubGoalsTB fs cert fp seed s w Pvs Bv) :
    ∃ (n : ℕ) (L : B1.Main.Layout), n ≤ Bmain fs SB SK Bv fp seed s w ∧
      Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 16 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w))
              ((fun _ => True) :: mTs (hm fs fp seed s w)
                ((mainPredsH s w (hDvNH w) Pvs).withTotal fs (mainBsH fs SB SK Bv s w))) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_honest_relAtInTB hbl hr hl (mainStaticGoalsB_of hbl hr hl hxc hsc hS.main)
    (mainGoalsTB_honest hbl hr hl hrf hS hV).withTotal

end
end LeanVM.Guest.B1.Main
