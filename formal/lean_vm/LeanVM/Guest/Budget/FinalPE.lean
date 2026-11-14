/-
  LeanVM.Guest.Budget.FinalPE

  `MainCompleteP` with every node of `main`'s tree exact on the memory.
-/

module

public import LeanVM.Guest.Budget.FinalP
public import LeanVM.Guest.B1.Main.MainHonestE

/-!
# `main` within the budget, with its pops, every node exact

`MainCompletePE`: `MainCompleteP`, the tree also `Every (ExactAt …)` on the memory; `MainCompletePE.toP`.
`mainComplete_of_boundsPE`, `mainComplete_of_mainPE`, `mainComplete_budgetPE`: `mainComplete_of_boundsP`,
`mainComplete_of_mainP`, `mainComplete_budgetP` with it, route R's callees with computed hints given in their E forms
(`MainGoalsRE`, `aggregate_claims`'), `main`'s node exact by `main_every`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (MainComplete Budget work hdrOf bytecode bytecode_length words_le_of_size)
open LeanVM.Guest.B1 (LowDef DisjL Within CompleteAtDTBR)
open LeanVM.Guest.B1.Main (Bmain mainBsH hm hData mainPredsH hDvNH VerifySubGoalsTB MainStatics hData_bounds childBv
  MainPops MainPopsS MainGoalsRR MainGoalsRE mainPredsHP main_honest_budgetBRE main_tree_popsR kidsT_imp mTsR_imp mTsR
  main_pops_honest SameStreamsBut childSeg daSeg LConsistent Layout MemL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **`MainCompleteP`, every node exact**: the tree also exact at every node on the memory. -/
def MainCompletePE (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ) (b : Budget) : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
    b.size (work s w) ≤ 2 ^ 30 →
    ∃ (N : ℕ) (L : Layout), LConsistent L ∧ (∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ N) ∧
      N ≤ 2 ^ 30 ∧ N ≤ b.words.eval (work s w) ∧
      ∀ rd, LowDef (logMem N) rd → MemL rd L → rd 1 = some (hdrOf (statementDigest seed s)).1 →
        rd g = some (hdrOf (statementDigest seed s)).2 →
          ∃ t : Tree, t.name = "main" ∧ t.Valid coreProgram rd [] [] ∧ t.BufsOk coreProgram ∧
            t.Placed coreProgram fs cert (0, t.block fs coreProgram.loop) ∧ t.total fs = N ∧
            t.LoadsIn coreProgram fs cert (fun i => i < 2) (0, t.block fs coreProgram.loop) ∧
            (∀ op, cnt t op ≤ (b.instrs op).eval (work s w)) ∧
            SameStreams (t.pops coreProgram rd)
              ((Hints.honestPushes bytecode seed s w).filter (·.1 != Hints.heapSizeStream)) ∧
            t.Every (ExactAt coreProgram rd)

theorem MainCompletePE.toP {fs : String → ℕ} {cert : String → V → ℕ} {cnt : Tree → Opcode → ℕ}
    {b : Budget} (h : MainCompletePE fs cert cnt b) : MainCompleteP fs cert cnt b := fun seed s w h1 h2 h3 h4 =>
  let ⟨N, L, a1, a2, a3, a4, hr⟩ := h seed s w h1 h2 h3 h4
  ⟨N, L, a1, a2, a3, a4, fun rd hl hL h0 h1 =>
    let ⟨t, b1, b2, b3, b4, b5, b6, b7, b8, _⟩ := hr rd hl hL h0 h1
    ⟨t, b1, b2, b3, b4, b5, b6, b7, b8⟩⟩

/-- **`MainCompletePE` from `main`'s completeness within a words bound, its tree's counts, pops and exactness.** -/
theorem mainComplete_of_boundsPE (fs : String → ℕ) (cert : String → V → ℕ)
    (cnt : Tree → Opcode → ℕ) (b : Budget)
    (T : Digest → NodeStatement → NodeWitness → Reader → Tree → Prop) (Bm : Digest → NodeStatement → NodeWitness → ℕ)
    (hfs : 2 ≤ fs "main")
    (hmain : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      ∃ (n : ℕ) (L : B1.Main.Layout), n ≤ Bm seed s w ∧ Within L 0 n ∧ (∀ q ∈ L, fs "main" ≤ q.1) ∧
        DisjL L ∧ ∀ rd, LowDef 23 rd → B1.Main.MemL rd L →
          LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
          LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
          RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) 0 n "main" [] []
            (T seed s w rd))
    (hcnt : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      ∀ (rd : Reader) (t : Tree), T seed s w rd t → t.Valid coreProgram rd [] [] →
        t.BufsOk coreProgram → ∀ op, cnt t op ≤ (b.instrs op).eval (work s w))
    (hpops : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      ∀ (rd : Reader) (t : Tree), T seed s w rd t → t.Valid coreProgram rd [] [] →
        SameStreams (t.pops coreProgram rd) ((Hints.honestPushes bytecode seed s w).filter (·.1 != Hints.heapSizeStream)))
    (hexact : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      ∀ (rd : Reader) (t : Tree), T seed s w rd t → t.Valid coreProgram rd [] [] → t.Every (ExactAt coreProgram rd))
    (hwords : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      Bm seed s w ≤ b.words.eval (work s w)) :
    MainCompletePE fs cert cnt b := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨n, L, hnB, hW, hab, hD, hR⟩ := hmain seed s w hrel hlim hok
  have hw := hwords seed s w hrel hlim
  have h28 := words_le_of_size hbs
  refine ⟨n, L, B1.Main.lConsistent_of_pairwise hD, fun q hq => ?_, by omega, by omega,
    fun rd hl hL h0 h1 => ?_⟩
  · have := hW q hq
    have := hab q hq
    omega
  · obtain ⟨t, ⟨hn, hv, hb, hp, ht, hli, -⟩, hT⟩ :=
      hR rd (hl.mono (Memory.twentyThree_le_logMem n)) hL (loadHolds_one h0) (loadHolds_gen h1)
    rw [Nat.zero_add] at hp hli
    exact ⟨t, hn, hv, hb, hp, ht, hli, hcnt seed s w hrel hlim rd t hT hv hb, hpops seed s w hrel hlim rd t hT hv,
      hexact seed s w hrel hlim rd t hT hv⟩

/-- **`main` is complete within the budget `b`, with its pops, every node exact**: `mainComplete_of_mainP`, route R's
callees in `MainGoalsRR` and those with computed hints also in `MainGoalsRE`. -/
theorem mainComplete_of_mainPE (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
    (b : Budget) {SB SK : String → ℕ} {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    {Q : Digest → NodeStatement → NodeWitness → MainPops}
    (ω : Opcode → String → ℕ) (jt : Opcode → ℕ) (H : ∀ op, MainCounts (ω op) fs)
    (hfs : 2 ≤ fs "main") (hxc : B1.Sig.verify_lean_xmss_complete_Spec)
    (hsc : B1.Sig.SphincsCompleteSpecs) (hS : MainStatics fs SB SK)
    (hPS : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      MainPopsS fs 0 seed s w (Q seed s w))
    (hR : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      MainGoalsRR fs cert 0 seed s w SK (mainPredsHP fs SB SK (childBv Bvf w) (Pvs w) s w (Q seed s w))
        (mainBsH fs SB SK (childBv Bvf w) s w))
    (hRE : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      MainGoalsRE fs cert 0 seed s w SK (mainPredsHP fs SB SK (childBv Bvf w) (Pvs w) s w (Q seed s w))
        (mainBsH fs SB SK (childBv Bvf w) s w))
    (hag : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → (hm fs 0 seed s w).nc ≠ 0 →
      CompleteAtDTBR fs cert 20 "aggregate_claims" (B1.Main.hLmain fs 0 seed s w)
        [gen ^ (hm fs 0 seed s w).nc, (hm fs 0 seed s w).a394, (hm fs 0 seed s w).a400,
          (hm fs 0 seed s w).a406, (hm fs 0 seed s w).a417, (hm fs 0 seed s w).et * LeanVM.Guest.word 133823759239872512 0]
        (B1.Returns []) (mainPredsHP fs SB SK (childBv Bvf w) (Pvs w) s w (Q seed s w)).withExact.Pa
        (mainBsH fs SB SK (childBv Bvf w) s w).Ba)
    (hseg : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ rd, MainSegs fs seed s w (Q seed s w) rd)
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op)
    (Kx Ks Kd K5 : Opcode → NodeStatement → NodeWitness → ℕ)
    (hx : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = "claim_list_digest" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      (mainPredsH s w (hDvNH w) (Pvs w)).Px t → t.weight (ω op) ≤ Kx op s w)
    (hs : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = "claim_list_digest" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      (mainPredsH s w (hDvNH w) (Pvs w)).Ps t → t.weight (ω op) ≤ Ks op s w)
    (hd : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → (hm fs 0 seed s w).nd = 1 →
      ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "da_verify" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      (mainPredsH s w (hDvNH w) (Pvs w)).Pd t → t.weight (ω op) ≤ Kd op s w)
    (h5 : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = (name% main_loop4) → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH w) (Pvs w)).T5 t →
        t.weight (ω op) ≤ K5 op s w)
    (hwords : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      Bmain fs SB SK (childBv Bvf w) 0 seed s w ≤ b.words.eval (work s w))
    (hinstrs : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op,
      mainCount (H op) (hm fs 0 seed s w) (Kx op s w) (Ks op s w) (Kd op s w) (K5 op s w) +
        jt op ≤ (b.instrs op).eval (work s w)) :
    MainCompletePE fs cert cnt b := by
  refine mainComplete_of_boundsPE fs cert cnt b
    (fun seed s w rd t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧
      B1.Main.MVals rd σ (hm fs 0 seed s w) ∧
      KidsT (B1.Main.mCalls σ (hm fs 0 seed s w))
        ((fun _ => True) :: mTsR (hm fs 0 seed s w)
          (mainPredsHP fs SB SK (childBv Bvf w) (Pvs w) s w (Q seed s w)).withExact rd) ks ∧
      calls (B1.Main.mEvs σ) = B1.Main.mCalls σ (hm fs 0 seed s w) ∧ bufs = B1.Main.mSizes (hData seed s w))
    (fun seed s w => Bmain fs SB SK (childBv Bvf w) 0 seed s w) hfs ?_ ?_ ?_ ?_ hwords
  · intro seed s w hrel hlim hok
    obtain ⟨n, L, hn, hW, hab, hD, -, hR⟩ := main_honest_budgetBRE bytecode_length hrel hlim hxc hsc
      hS (hPS seed s w hrel hlim hok) ((hR seed s w hrel hlim hok).withExact (hRE seed s w hrel hlim hok) (hag seed s w hrel hlim))
    exact ⟨n, L, hn, hW, fun q hq => by simpa using hab q hq, hD, hR⟩
  · intro seed s w hrel hlim rd t hTt hv hb op
    obtain ⟨σ, bufs, ks, ht, hMV, hT, hc, -⟩ := hTt
    subst ht
    have hw := main_weight_count (H op) (Kx op s w) (Ks op s w) (Kd op s w) (K5 op s w)
      (hx seed s w hrel hlim op) (hs seed s w hrel hlim op)
      (fun h1 => hd seed s w hrel hlim h1 op) (h5 seed s w hrel hlim op) hv hb hc hMV
      (hData_bounds hlim fs 0) (kidsT_imp (B1.Main.kidsT_dropExact hT) (mTsR_imp _ _ _ rd))
    have := hcnt rd _ hv op
    have := hinstrs seed s w hrel hlim op
    omega
  · intro seed s w hrel hlim rd t hTt hv
    obtain ⟨σ, bufs, ks, rfl, hMV, hT, hc, -⟩ := hTt
    have e := main_tree_popsR (hData_bounds hlim fs 0) hv hMV _ _ (B1.Main.kidsT_dropExact hT) hc
    have hg := hseg seed s w hrel hlim rd
    exact ((B1.Main.sameStreamsBut_of e).trans (main_pops_honest fs 0 hlim rfl rfl hg.cx hg.cs hg.d0 hg.d1 hg.r2
      hg.r3 hg.da hg.kids hg.agg)).sameStreams (B1.Main.pops_noHeap _ hv)
  · intro seed s w hrel hlim rd t hTt hv
    obtain ⟨σ, bufs, ks, rfl, -, hT, hc, -⟩ := hTt
    exact B1.Main.main_every hv hT hc

/-- **`main` is complete within `mainBudget`, with its pops, every node exact.** -/
theorem mainComplete_budgetPE (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
    {SB SK : String → ℕ} {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    {Q : Digest → NodeStatement → NodeWitness → MainPops}
    (ω : Opcode → String → ℕ) (jt : Opcode → ℕ) (H : ∀ op, MainCounts (ω op) fs)
    (hfs : 2 ≤ fs "main") (hxc : B1.Sig.verify_lean_xmss_complete_Spec)
    (hsc : B1.Sig.SphincsCompleteSpecs) (hS : MainStatics fs SB SK)
    (hPS : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      MainPopsS fs 0 seed s w (Q seed s w))
    (hR : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      MainGoalsRR fs cert 0 seed s w SK (mainPredsHP fs SB SK (childBv Bvf w) (Pvs w) s w (Q seed s w))
        (mainBsH fs SB SK (childBv Bvf w) s w))
    (hRE : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      MainGoalsRE fs cert 0 seed s w SK (mainPredsHP fs SB SK (childBv Bvf w) (Pvs w) s w (Q seed s w))
        (mainBsH fs SB SK (childBv Bvf w) s w))
    (hag : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → (hm fs 0 seed s w).nc ≠ 0 →
      CompleteAtDTBR fs cert 20 "aggregate_claims" (B1.Main.hLmain fs 0 seed s w)
        [gen ^ (hm fs 0 seed s w).nc, (hm fs 0 seed s w).a394, (hm fs 0 seed s w).a400,
          (hm fs 0 seed s w).a406, (hm fs 0 seed s w).a417, (hm fs 0 seed s w).et * LeanVM.Guest.word 133823759239872512 0]
        (B1.Returns []) (mainPredsHP fs SB SK (childBv Bvf w) (Pvs w) s w (Q seed s w)).withExact.Pa
        (mainBsH fs SB SK (childBv Bvf w) s w).Ba)
    (hseg : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ rd, MainSegs fs seed s w (Q seed s w) rd)
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op) (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (h5 : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = (name% main_loop4) → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH w) (Pvs w)).T5 t →
        t.weight (ω op) ≤ l5Lin (c5 op) (s5 op) (v5 op) (work s w)) :
    MainCompletePE fs cert cnt (mainBudget fs SB SK Bvf ω H c5 s5 v5 jt) :=
  mainComplete_of_mainPE fs cert cnt _ ω jt H hfs hxc hsc hS hPS hR hRE hag hseg hcnt
    (fun op s _ => (H op).clA + (H op).clS * s.claims.xmss.length)
    (fun op s _ => (H op).clA + (H op).clS * s.claims.sphincs.length)
    (fun op s w => (H op).dvA + (H op).dvR * (work s w).rawDaRows +
      (H op).dvP * (work s w).rawDaPad)
    (fun op s w => l5Lin (c5 op) (s5 op) (v5 op) (work s w))
    (fun _ s _ _ hl op rd t args rets hn hv hb hT =>
      clHonest_weight (H op) (n := s.claims.xmss.length) (claims_lt hl).1 rd t args rets
        hn hv hb hT)
    (fun _ s _ _ hl op rd t args rets hn hv hb hT =>
      clHonest_weight (H op) (n := s.claims.sphincs.length) (claims_lt hl).2 rd t args
        rets hn hv hb hT)
    (fun _ _ _ hr _ hnd op rd t args rets hn hv hb hT =>
      dvNH_weight (H op) hr hnd rd t args rets hn hv hb hT) h5
    (fun _ _ _ hr hl => B1.Main.Bmain_le fs SB SK Bvf hr hl)
    (fun _ _ _ _ hl op => mainCount_le (H op) (c5 op) (s5 op) (v5 op) (jt op) hl)

end
end LeanVM.Guest.Budget
