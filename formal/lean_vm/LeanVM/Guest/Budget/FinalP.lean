/-
  LeanVM.Guest.Budget.FinalP

  `MainComplete` with the tree's pops: `main`'s tree within the budget also pops the honest pushes but the advised sizes, stream by stream.
-/

module

public import LeanVM.Guest.Budget.Final
public import LeanVM.Guest.B1.Main.MainHonestBudgetBR
public import LeanVM.Guest.B1.Main.MainPushes
public import LeanVM.Guest.B1.Main.NoHeapPops

/-!
# `main` within the budget, with its pops

`MainCompleteP`: `MainComplete`, the tree popping `Hints.honestPushes` without the `heap_sizes` stream, stream by stream (`SameStreams`); `MainCompleteP.toMainComplete`. `MainSegs`: `main`'s callees' entries against their segments of the honest pushes (`main_pops_honest`'s hypotheses).

`mainComplete_of_boundsP`, `mainComplete_of_mainP`, `mainComplete_budgetP`: `mainComplete_of_bounds`, `mainComplete_of_main`, `mainComplete_budget` with the pops, from `main_honest_budgetBR` (route S `MainPopsS`, route R `MainGoalsRR`), the callees' entries against their segments; no tree pops a `heap_sizes` entry (`pops_noHeap`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (MainComplete Budget work hdrOf bytecode bytecode_length words_le_of_size)
open LeanVM.Guest.B1 (LowDef DisjL Within)
open LeanVM.Guest.B1.Main (Bmain mainBsH hm hData mainPredsH hDvNH VerifySubGoalsTB MainStatics hData_bounds childBv
  MainPops MainPopsS MainGoalsRR mainPredsHP main_honest_budgetBR main_tree_popsR kidsT_imp mTsR_imp mTsR
  main_pops_honest SameStreamsBut childSeg daSeg LConsistent Layout MemL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **`MainComplete` with the pops**: the tree also pops `Hints.honestPushes` but the advised sizes, stream by
stream. -/
def MainCompleteP (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ) (b : Budget) : Prop :=
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
              ((Hints.honestPushes bytecode seed s w).filter (·.1 != Hints.heapSizeStream))

theorem MainCompleteP.toMainComplete {fs : String → ℕ} {cert : String → V → ℕ} {cnt : Tree → Opcode → ℕ}
    {b : Budget} (h : MainCompleteP fs cert cnt b) : MainComplete fs cert cnt b := fun seed s w h1 h2 h3 h4 =>
  let ⟨N, L, a1, a2, a3, a4, hr⟩ := h seed s w h1 h2 h3 h4
  ⟨N, L, a1, a2, a3, a4, fun rd hl hL h0 h1 =>
    let ⟨t, b1, b2, b3, b4, b5, b6, b7, _⟩ := hr rd hl hL h0 h1
    ⟨t, b1, b2, b3, b4, b5, b6, b7⟩⟩

/-- **`main`'s callees' entries against their segments of the honest pushes** on the memory `rd`, a loop not
entered popping `[]`. -/
structure MainSegs (fs : String → ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness) (q : MainPops)
    (rd : Reader) : Prop where
  cx : SameStreams (q.px rd) (Hints.listPushes "claims"
    (s.claims.xmss.map fun c ↦ Hints.claimCells c.1.root c.1.parameter c.2))
  cs : SameStreams (q.ps rd) (Hints.listPushes "claims"
    (s.claims.sphincs.map fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2))
  d0 : SameStreams (if (hm fs 0 seed s w).nxd = 0 then [] else q.p0 rd)
    ((B1.Main.xPlan s w).duplicates.map fun c ↦ ("dup_claims", Hints.claimCells c.1.root c.1.parameter c.2))
  d1 : SameStreams (if (hm fs 0 seed s w).nsd = 0 then [] else q.p1 rd)
    ((B1.Main.sPlan s w).duplicates.map fun c ↦ ("dup_claims", Hints.claimCells c.1.publicSeed c.1.root c.2))
  r2 : SameStreams (if (hm fs 0 seed s w).nrx = 0 then [] else q.p2 rd)
    ((w.xmssSignatures.zip (B1.Main.xPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("raw_index", [Hints.count slot]) :: Hints.xmssHints c.1.1 c.1.2 c.2))
  r3 : SameStreams (if (hm fs 0 seed s w).nrs = 0 then [] else q.p3 rd)
    ((w.sphincsSignatures.zip (B1.Main.sPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("sp_raw_index", [Hints.count slot]) :: Hints.sphincsHints c.1.1 c.1.2 c.2))
  da : w.daMatrix.isSome → SameStreams (q.pd rd) (daSeg w)
  kids : SameStreamsBut Hints.heapSizeStream (if (hm fs 0 seed s w).nc = 0 then [] else q.p5 rd)
    (childSeg bytecode seed s w)
  agg : w.children ≠ [] → SameStreams (q.pa rd) (Hints.batchPushes w.batchingHints)

/-- **`MainCompleteP` from `main`'s completeness within a words bound, its tree's counts and its pops.** -/
theorem mainComplete_of_boundsP (fs : String → ℕ) (cert : String → V → ℕ)
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
    (hwords : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      Bm seed s w ≤ b.words.eval (work s w)) :
    MainCompleteP fs cert cnt b := by
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
    exact ⟨t, hn, hv, hb, hp, ht, hli, hcnt seed s w hrel hlim rd t hT hv hb, hpops seed s w hrel hlim rd t hT hv⟩

/-- **`main` is complete within the budget `b`, with its pops**: `mainComplete_of_main`, the callees' pops from
route S (`MainPopsS`) and route R (`MainGoalsRR`), their entries against their segments (`MainSegs`); no tree pops a `heap_sizes` entry
(`pops_noHeap`). -/
theorem mainComplete_of_mainP (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
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
    MainCompleteP fs cert cnt b := by
  refine mainComplete_of_boundsP fs cert cnt b
    (fun seed s w rd t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧
      B1.Main.MVals rd σ (hm fs 0 seed s w) ∧
      KidsT (B1.Main.mCalls σ (hm fs 0 seed s w))
        ((fun _ => True) :: mTsR (hm fs 0 seed s w) (mainPredsHP fs SB SK (childBv Bvf w) (Pvs w) s w (Q seed s w)) rd)
        ks ∧
      calls (B1.Main.mEvs σ) = B1.Main.mCalls σ (hm fs 0 seed s w) ∧ bufs = B1.Main.mSizes (hData seed s w))
    (fun seed s w => Bmain fs SB SK (childBv Bvf w) 0 seed s w) hfs ?_ ?_ ?_ hwords
  · intro seed s w hrel hlim hok
    obtain ⟨n, L, hn, hW, hab, hD, -, hR⟩ := main_honest_budgetBR bytecode_length hrel hlim hxc hsc
      hS (hPS seed s w hrel hlim hok) (hR seed s w hrel hlim hok)
    exact ⟨n, L, hn, hW, fun q hq => by simpa using hab q hq, hD, hR⟩
  · intro seed s w hrel hlim rd t hTt hv hb op
    obtain ⟨σ, bufs, ks, ht, hMV, hT, hc, -⟩ := hTt
    subst ht
    have hw := main_weight_count (H op) (Kx op s w) (Ks op s w) (Kd op s w) (K5 op s w)
      (hx seed s w hrel hlim op) (hs seed s w hrel hlim op)
      (fun h1 => hd seed s w hrel hlim h1 op) (h5 seed s w hrel hlim op) hv hb hc hMV
      (hData_bounds hlim fs 0) (kidsT_imp hT (mTsR_imp _ _ _ rd))
    have := hcnt rd _ hv op
    have := hinstrs seed s w hrel hlim op
    omega
  · intro seed s w hrel hlim rd t hTt hv
    obtain ⟨σ, bufs, ks, rfl, hMV, hT, hc, -⟩ := hTt
    have e := main_tree_popsR (hData_bounds hlim fs 0) hv hMV _ _ hT hc
    have hg := hseg seed s w hrel hlim rd
    rw [e]
    refine (main_pops_honest fs 0 hlim rfl rfl hg.cx hg.cs hg.d0 hg.d1 hg.r2 hg.r3 hg.da hg.kids hg.agg).sameStreams ?_
    rw [← e]
    exact B1.Main.pops_noHeap _ hv

/-- **`main` is complete within `mainBudget`, with its pops.** -/
theorem mainComplete_budgetP (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
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
    (hseg : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ rd, MainSegs fs seed s w (Q seed s w) rd)
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op) (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (h5 : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = (name% main_loop4) → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH w) (Pvs w)).T5 t →
        t.weight (ω op) ≤ l5Lin (c5 op) (s5 op) (v5 op) (work s w)) :
    MainCompleteP fs cert cnt (mainBudget fs SB SK Bvf ω H c5 s5 v5 jt) :=
  mainComplete_of_mainP fs cert cnt _ ω jt H hfs hxc hsc hS hPS hR hseg hcnt
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
