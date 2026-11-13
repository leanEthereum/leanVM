/-
  LeanVM.Guest.B1.Main.MainHonestBudgetBR

  `main`'s completeness on a node's honest run within its words, its callees' trees popping given entries: the families whose pops follow from their honest trees (route S) from `main_honest_budgetB`'s goals, the others (route R) given with their pops.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestBudgetB
public import LeanVM.Guest.B1.Main.MainPopsKids

/-!
# `main` on an honest run, within its words, with its callees' pops

`mainPredsHP … q`: `mainPredsH`'s predicates within their bounds (`withTotal`), the trees popping `q`'s entries.
`MainPopsS q`: route S, each of `main_loop0`, `main_loop1` popping `q`'s entries on every valid tree of it. `MainGoalsRR q`: route R, the claim lists' digests, `main_loop2`, `main_loop3`, `da_verify`, the children's loop and `aggregate_claims` complete within their bounds by trees of `mainPredsHP` (`CompleteAtDTBR`). `main_honest_budgetBR`: `main_honest_budgetB`, the callees' trees satisfying `mainPredsHP` on each memory.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within CompleteAtDTB CompleteAtDTBR Returns)

@[expose] public section

/-- **`main`'s callees' predicates for the budget, with their pops.** -/
def mainPredsHP (fs : String → ℕ) (SB SK : String → ℕ) (Bv : ℕ → ℕ) (Pvs : ℕ → Tree → Prop) (s : NodeStatement)
    (w : NodeWitness) (q : MainPops) : MainPredsR :=
  ((mainPredsH s w (hDvNH w) Pvs).withTotal fs (mainBsH fs SB SK Bv s w)).withPops q

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- **A tree predicate whose valid trees of `f` pop `ps rd`** on the memories the callee serves, the pops added to it. -/
theorem _root_.LeanVM.Guest.B1.CompleteAtDTBR.withPopsN {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B : ℕ} {ps : Reader → List Pop}
    {T : Reader → Tree → Prop} (h : CompleteAtDTBR fs cert k f Lin args Out T B)
    (hp : ∀ rd, LowDef k rd → MemL rd Lin → ∀ t rets, t.name = f → t.Valid coreProgram rd args rets → T rd t →
      t.pops coreProgram rd = ps rd) :
    CompleteAtDTBR fs cert k f Lin args Out (fun rd t => T rd t ∧ t.pops coreProgram rd = ps rd) B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT⟩ := hr rd hl hm
    ⟨t, ht, hT, hp rd hl (memL_append.mp hm).2 t rets ht.1 ht.2.1 hT⟩⟩

/-- **Route S**: every valid tree of `main_loop0`, `main_loop1` at `main`'s arguments, on a memory holding `main`'s words, pops `q`'s entries. -/
structure MainPopsS (q : MainPops) : Prop where
  l1 : (hm fs fp seed s w).nxd ≠ 0 → ∀ rd, LowDef 20 rd → B1.Main.MemL rd (hLmain fs fp seed s w) →
    ∀ (t : Tree) rets, t.name = name% «main_loop0» → t.Valid coreProgram rd
      [1, gen ^ (hm fs fp seed s w).nxd, (hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx] rets →
      t.pops coreProgram rd = q.p0 rd
  l2 : (hm fs fp seed s w).nsd ≠ 0 → ∀ rd, LowDef 20 rd → B1.Main.MemL rd (hLmain fs fp seed s w) →
    ∀ (t : Tree) rets, t.name = name% «main_loop1» → t.Valid coreProgram rd
      [1, gen ^ (hm fs fp seed s w).nsd, (hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls] rets →
      t.pops coreProgram rd = q.p1 rd

/-- **Route R**: the claim lists' digests, `main_loop2`, `main_loop3`, `da_verify`, the children's loop and
`aggregate_claims` within their bounds by trees of `p`'s predicates (`MainGoalsTBR`'s fields). -/
structure MainGoalsRR (SK : String → ℕ) (p : MainPredsR) (b : MainBs) : Prop where
  clx : CompleteAtDTBR fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd)) p.Px b.Bx
  cls : CompleteAtDTBR fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd)) p.Ps b.Bs
  l3 : (hm fs fp seed s w).nrx ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop2» (hLmain fs fp seed s w)
      ([1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] ++ lxTagWords) (Returns []) p.P2
      ((hm fs fp seed s w).nrx * iterK fs SK name% «main_loop2» + fs name% «main_loop2»)
  l4 : (hm fs fp seed s w).nrs ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop3» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns []) p.P3
      ((hm fs fp seed s w).nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3»)
  dv : (hm fs fp seed s w).nd = 1 →
    CompleteAtDTBR fs cert 20 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et]
      (Returns (hm fs fp seed s w).daR) p.Pd b.Bd
  l5 : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop4» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns []) p.P5 b.B5
  ag : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
      [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
        (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
          (hm fs fp seed s w).et * word 133823759239872512 0] (Returns []) p.Pa b.Ba

variable {fs cert fp seed s w} {bytecode : List K}

/-- **`main`'s callees on the honest run within their bounds, by trees popping `q`'s entries**: the static and
route S ones from `main_honest_budgetB`'s goals, the route R ones given. -/
theorem mainGoalsTBR_honest {SB SK : String → ℕ} {Pvs : ℕ → Tree → Prop} {Bv : ℕ → ℕ} {q : MainPops}
    (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec) (hsc : Sig.SphincsCompleteSpecs)
    (hS : MainStatics fs SB SK) (hPS : MainPopsS fs fp seed s w q)
    (hR : MainGoalsRR fs cert fp seed s w SK (mainPredsHP fs SB SK Bv Pvs s w q) (mainBsH fs SB SK Bv s w)) :
    MainGoalsTBR fs cert fp seed s w SB SK (mainPredsHP fs SB SK Bv Pvs s w q) (mainBsH fs SB SK Bv s w) := by
  have hg : MainStaticGoalsB fs cert fp seed s w SB SK := mainStaticGoalsB_of hbl hr hl hxc hsc hS.main
  exact ⟨hR.clx, hR.cls,
    fun hn => ((hg.l1 hn).toR.withPopsN fun rd hl hL t rets htn hv _ => hPS.l1 hn rd hl hL t rets htn hv).mono le_rfl
      fun _ _ h => h.2,
    fun hn => ((hg.l2 hn).toR.withPopsN fun rd hl hL t rets htn hv _ => hPS.l2 hn rd hl hL t rets htn hv).mono le_rfl
      fun _ _ h => h.2,
    hR.l3, hR.l4, hR.dv, hR.l5, hR.ag, hg.st.toR.mono le_rfl fun _ _ _ => trivial⟩

/-- **`main`'s completeness on the honest run within its words, its callees popping `q`'s entries**:
`main_honest_budgetB`, the callees' trees satisfying `mainPredsHP` on each memory. -/
theorem main_honest_budgetBR {SB SK : String → ℕ} {Pvs : ℕ → Tree → Prop} {Bv : ℕ → ℕ} {q : MainPops}
    (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec) (hsc : Sig.SphincsCompleteSpecs)
    (hS : MainStatics fs SB SK) (hPS : MainPopsS fs fp seed s w q)
    (hR : MainGoalsRR fs cert fp seed s w SK (mainPredsHP fs SB SK Bv Pvs s w q) (mainBsH fs SB SK Bv s w)) :
    ∃ (n : ℕ) (L : B1.Main.Layout), n ≤ Bmain fs SB SK Bv fp seed s w ∧
      Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 23 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w))
              ((fun _ => True) :: mTsR (hm fs fp seed s w) (mainPredsHP fs SB SK Bv Pvs s w q) rd) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_honest_relAtInTBR hbl hr hl (mainGoalsTBR_honest hbl hr hl hxc hsc hS hPS hR)

end
end LeanVM.Guest.B1.Main
