/-
  LeanVM.Guest.B1.Main.MainHonestE

  `main` on a node's honest run within its words, its callees' trees popping given entries and every node exact on
  the memory: the free callees by kernel check, the others given.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestBudgetBR
public import LeanVM.Guest.Budget.BoundedE
public import LeanVM.Guest.Exact.Kids
public import LeanVM.Guest.Exact.FreeMain

/-!
# `main` on an honest run, every node exact

`MainPredsR.withExact p`: `p`'s predicates, each tree also exact on the memory (`Every (ExactAt …)`);
`mTsR_withExact`. `main_every`: a valid node of `main` whose callees satisfy those predicates satisfies `Every`:
`main`'s body has no computed hint (`main_pinned`), `exponent_tables` is exact for free.

`MainGoalsRE`: the E forms of `MainGoalsRR`'s fields whose callees hold computed hints (`main_loop3`, the children's loop) and of `main_loop2`'s (free, but its whole-body kernel check is too heavy for a module); `MainGoalsRR.withExact`: with them and `aggregate_claims`' (`mainGoalsRR_agE`), the others exact for free (`claim_list_digest`, `da_verify`). `main_honest_budgetBRE`: `main_honest_budgetBR`, the callees' trees exact
(`main_loop0`, `main_loop1`, `statement_digest` for free).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within CompleteAtDTB CompleteAtDTBR Returns everyAll_exact)

@[expose] public section

/-! ## The predicates -/

/-- **`p`'s predicates, every node of each tree exact on the memory.** -/
def MainPredsR.withExact (p : MainPredsR) : MainPredsR :=
  ⟨fun rd t => p.Px rd t ∧ t.Every (ExactAt coreProgram rd), fun rd t => p.Ps rd t ∧ t.Every (ExactAt coreProgram rd),
    fun rd t => p.P0 rd t ∧ t.Every (ExactAt coreProgram rd), fun rd t => p.P1 rd t ∧ t.Every (ExactAt coreProgram rd),
    fun rd t => p.P2 rd t ∧ t.Every (ExactAt coreProgram rd), fun rd t => p.P3 rd t ∧ t.Every (ExactAt coreProgram rd),
    fun rd t => p.Pd rd t ∧ t.Every (ExactAt coreProgram rd), fun rd t => p.P5 rd t ∧ t.Every (ExactAt coreProgram rd),
    fun rd t => p.Pa rd t ∧ t.Every (ExactAt coreProgram rd),
    fun rd t => p.Pst rd t ∧ t.Every (ExactAt coreProgram rd)⟩

theorem mTsR_withExact (m : MainIn) (p : MainPredsR) (rd : Reader) :
    mTsR m p.withExact rd = (mTsR m p rd).map fun T t => T t ∧ t.Every (ExactAt coreProgram rd) := by
  unfold mTsR
  by_cases h1 : m.nd = 1 <;> by_cases h2 : m.nc = 0 <;> simp [h1, h2, MainPredsR.withExact]

theorem mCalls_length_le (σ : Val) (m : MainIn) (p : MainPredsR) (rd : Reader) :
    (mCalls σ m).tail.length ≤ (mTsR m p rd).length := by
  unfold mCalls mTsR
  by_cases h1 : m.nd = 1 <;> by_cases h2 : m.nc = 0 <;> simp [h1, h2]

theorem kidsT_dropExact {cs : List Call} {m : MainIn} {p : MainPredsR} {rd : Reader} {ks : List Tree}
    (h : KidsT cs ((fun _ => True) :: mTsR m p.withExact rd) ks) : KidsT cs ((fun _ => True) :: mTsR m p rd) ks := by
  refine kidsT_imp h (.cons (fun _ h => h) ?_)
  rw [mTsR_withExact]
  generalize mTsR m p rd = Ts
  induction Ts with
  | nil => exact .nil
  | cons T Ts ih => exact .cons (fun _ h => h.1) ih

/-! ## `main`'s node -/

/-- **A valid node of `main` whose callees' trees satisfy `p.withExact` is exact at every node**, and they satisfy
`p`. -/
theorem main_every {m : MainIn} {p : MainPredsR} {rd : Reader} {σ : Val} {bufs : List ℕ} {ks : List Tree}
    (hval : (Memory.Tree.node "main" σ bufs ks).Valid coreProgram rd [] [])
    (hT : KidsT (mCalls σ m) ((fun _ => True) :: mTsR m p.withExact rd) ks) (hc : calls (mEvs σ) = mCalls σ m) :
    (Memory.Tree.node "main" σ bufs ks).Every (ExactAt coreProgram rd) := by
  have hval' := hval
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hval'
  rw [find_main] at hf
  cases hf
  rw [walk_main σ] at hw
  cases hw
  rw [hc] at hkv
  have hl := mCalls_length_le σ m p rd
  unfold mCalls at hkv hT hl
  match ks, hkv, hT with
  | k0 :: ks', ⟨hn0, hv0, hkv'⟩, ⟨_, hT'⟩ =>
    rw [mTsR_withExact] at hT'
    obtain ⟨-, hE⟩ := kidsT_every hkv' hl hT'
    refine Tree.every_node.mpr ⟨exactAt_of_body find_main main_pinned hval rd, ?_⟩
    rw [Tree.EveryKids]
    refine ⟨?_, hE⟩
    rw [ite_eq_left rfl] at hv0
    exact every_exact_of_free exponent_tables_exactFree hv0 hn0 rd

/-! ## The callees with computed hints -/

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- **`MainGoalsRR`'s fields still given in E form**: `main_loop2` (free, its whole-body check too heavy),
`main_loop3` and the children's loop (`aggregate_claims`' is `mainGoalsRR_agE`). -/
structure MainGoalsRE (SK : String → ℕ) (p : MainPredsR) (b : MainBs) : Prop where
  l3 : (hm fs fp seed s w).nrx ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop2» (hLmain fs fp seed s w)
      ([1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] ++ lxTagWords) (Returns []) p.withExact.P2
      ((hm fs fp seed s w).nrx * iterK fs SK name% «main_loop2» + fs name% «main_loop2»)
  l4 : (hm fs fp seed s w).nrs ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop3» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns [])
      p.withExact.P3 ((hm fs fp seed s w).nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3»)
  l5 : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop4» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns []) p.withExact.P5 b.B5

variable {fs cert fp seed s w}

/-- **`MainGoalsRR` with every node exact**: the callees with computed hints' E forms, the others exact for free. -/
theorem MainGoalsRR.withExact {SK : String → ℕ} {p : MainPredsR} {b : MainBs}
    (h : MainGoalsRR fs cert fp seed s w SK p b) (hE : MainGoalsRE fs cert fp seed s w SK p b)
    (hag : (hm fs fp seed s w).nc ≠ 0 →
      CompleteAtDTBR fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
        [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
          (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
            (hm fs fp seed s w).et * word 133823759239872512 0] (Returns []) p.withExact.Pa b.Ba) :
    MainGoalsRR fs cert fp seed s w SK p.withExact b where
  clx := h.clx.andEvery (everyAll_exact claim_list_digest_exactFree).everyOn
  cls := h.cls.andEvery (everyAll_exact claim_list_digest_exactFree).everyOn
  l3 := hE.l3
  l4 := hE.l4
  dv := fun hn => (h.dv hn).andEvery (everyAll_exact da_verify_exactFree).everyOn
  l5 := hE.l5
  ag := hag

variable {bytecode : List K}

/-- **`main`'s callees on the honest run within their bounds, every node exact**: `mainGoalsTBR_honest`, the static
and route S ones exact for free. -/
theorem mainGoalsTBR_honestE {SB SK : String → ℕ} {Pvs : ℕ → Tree → Prop} {Bv : ℕ → ℕ} {q : MainPops}
    (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec) (hsc : Sig.SphincsCompleteSpecs)
    (hS : MainStatics fs SB SK) (hPS : MainPopsS fs fp seed s w q)
    (hR : MainGoalsRR fs cert fp seed s w SK (mainPredsHP fs SB SK Bv Pvs s w q).withExact
      (mainBsH fs SB SK Bv s w)) :
    MainGoalsTBR fs cert fp seed s w SB SK (mainPredsHP fs SB SK Bv Pvs s w q).withExact
      (mainBsH fs SB SK Bv s w) := by
  have hg : MainStaticGoalsB fs cert fp seed s w SB SK := mainStaticGoalsB_of hbl hr hl hxc hsc hS.main
  exact ⟨hR.clx, hR.cls,
    fun hn => (((hg.l1 hn).toR.withPopsN fun rd hl hL t rets htn hv _ => hPS.l1 hn rd hl hL t rets htn hv).andEvery
      (everyAll_exact main_loop0_exactFree).everyOn).mono le_rfl fun _ _ h => ⟨h.1.2, h.2⟩,
    fun hn => (((hg.l2 hn).toR.withPopsN fun rd hl hL t rets htn hv _ => hPS.l2 hn rd hl hL t rets htn hv).andEvery
      (everyAll_exact main_loop1_exactFree).everyOn).mono le_rfl fun _ _ h => ⟨h.1.2, h.2⟩,
    hR.l3, hR.l4, hR.dv, hR.l5, hR.ag,
    (hg.st.toR.andEvery (everyAll_exact statement_digest_exactFree).everyOn).mono le_rfl
      fun _ _ h => ⟨trivial, h.2⟩⟩

/-- **`main`'s completeness on the honest run within its words, every node exact**: `main_honest_budgetBR`, the
callees' trees satisfying `(mainPredsHP …).withExact`. -/
theorem main_honest_budgetBRE {SB SK : String → ℕ} {Pvs : ℕ → Tree → Prop} {Bv : ℕ → ℕ} {q : MainPops}
    (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec) (hsc : Sig.SphincsCompleteSpecs)
    (hS : MainStatics fs SB SK) (hPS : MainPopsS fs fp seed s w q)
    (hR : MainGoalsRR fs cert fp seed s w SK (mainPredsHP fs SB SK Bv Pvs s w q).withExact
      (mainBsH fs SB SK Bv s w)) :
    ∃ (n : ℕ) (L : B1.Main.Layout), n ≤ Bmain fs SB SK Bv fp seed s w ∧
      Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 23 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w))
              ((fun _ => True) :: mTsR (hm fs fp seed s w) (mainPredsHP fs SB SK Bv Pvs s w q).withExact rd) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_honest_relAtInTBR hbl hr hl (mainGoalsTBR_honestE hbl hr hl hxc hsc hS hPS hR)

end
end LeanVM.Guest.B1.Main
