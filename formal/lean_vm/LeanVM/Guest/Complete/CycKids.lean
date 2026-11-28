/-
  LeanVM.Guest.Complete.CycKids

  `main`'s cycle hand facts but the children's loop's: every node below a callee of `main` other than the loop has
  its cycle hand fact (`main_kids_cyc`), and `MainCycles` from the loop's (`mainCycles_of`).
-/

module

public import LeanVM.Guest.Complete.CycOwn

/-!
# `main`'s callees but the loop, at the cycle certificates

As `HandKids` for the words: the functions outside `vsNames`, the loop and `main` are call-closed
(`nonVs_everyIn`), each node's path is within the honest pushes (`every_pathIn_of_streams`), and so has its cycle hand
fact (`cyc_of_pathIn`): no inner check (`handFact_ch_none`), a path-local one (`CycHands`), or one from the pops
(`CycOwn`). Every cycle hand function is a words hand function (`chHandIdx_ok`, by the kernel).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-- **Every cycle hand function's index is a words hand function's**, by the kernel. -/
theorem chHandIdx_ok : ∀ j < coreProgram.length, (Data.chhandJ j).isSome = true → j ∈ pathIdx ∨ j ∈ vsIdx := by
  rw [coreProgram_length]; decide +kernel

variable {s : NodeStatement} {w : NodeWitness} {rd : Reader}

set_option maxRecDepth 100000 in
/-- **A node outside `vsNames`, the loop and `main` has its cycle hand fact**, its path within the honest pushes. -/
theorem cyc_of_pathIn (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hT : ThenSame "claim_list_digest" (.n 3) (.n 12) (.n 13)) (op : Opcode) {C₂ : ℕ} {f : String} {σ : Val}
    (hS : NonVs f) (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) f σ) :
    HandFact coreProgram (chCertAt op (daCntC op (itemsOf s w).rows) C₂) (chHandAt op (daCntC op (itemsOf s w).rows) C₂)
      (chOut op) f σ := by
  obtain ⟨hv, hl, hm⟩ := hS
  obtain ⟨fn, hf, -⟩ := id hp
  cases hh : Data.chhandJ (coreIdx f) with
  | none => exact handFact_ch_none op _ _ hl hh σ
  | some h =>
  rcases chHandIdx_ok (coreIdx f) (coreIdx_lt hf) (by rw [hh]; rfl) with hi | hi
  · simp only [pathIdx, List.mem_cons, List.not_mem_nil, or_false] at hi
    have N : ∀ {j : ℕ} {nm : String}, coreIdx f = j → (coreProgram[j]?).map Fn.name = some nm → f = nm :=
      fun hj hn => name_at hf hj hn
    rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi
    · exact absurd (N hi wh_nodeIdx.nm) hm
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[6]?).map Fn.name = some "rs_eq_run")
      exact handFact_ch_rs_eq_run op _ _ hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[11]?).map Fn.name = some "squeeze_packed")
      exact handFact_ch_squeeze op _ _ hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[12]?).map Fn.name = some "ring_rows")
      exact handFact_ch_ring_rows op _ _ hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[20]?).map Fn.name = some "claim_list_digest")
      exact claim_cyc hrel hlim hT op _ _ hp
    · obtain rfl := N hi wh_nodeIdx.nd
      exact da_verify_cyc hlim op hp
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[175]?).map Fn.name = some "link_rounds__L1_L0")
      exact handFact_ch_link_L1_L0 op _ _ hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[542]?).map Fn.name = some "link_rounds__L7_L0")
      exact handFact_ch_link_L7_L0 op _ _ hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[543]?).map Fn.name = some "link_rounds__L6_L0")
      exact handFact_ch_link_L6_L0 op _ _ hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[544]?).map Fn.name = some "link_rounds__L8_L1")
      exact handFact_ch_link_L8_L1 op _ _ hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[545]?).map Fn.name = some "link_rounds__L9_L1")
      exact handFact_ch_link_L9_L1 op _ _ hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[546]?).map Fn.name = some "link_rounds__L10_L1")
      exact handFact_ch_link_L10_L1 op _ _ hp.pathHolds
  · obtain ⟨nm, hnm, hn⟩ := vsIdx_names _ hi
    exact absurd (name_at hf rfl hn ▸ hnm) hv

variable {al : String → Bool} {σ : Val} {bufs : List ℕ} {kids : List Tree}

/-- **Every node below a callee of `main` other than the loop has its cycle hand fact.** -/
theorem main_kids_cyc (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hT : ThenSame "claim_list_digest" (.n 3) (.n 12) (.n 13)) (op : Opcode) {C₂ : ℕ}
    (h : MainHonest al s w rd (.node "main" σ bufs kids)) :
    ∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (chCertAt op (daCntC op (itemsOf s w).rows) C₂) (chHandAt op (daCntC op (itemsOf s w).rows) C₂) (chOut op)) := by
  have hP := every_pathIn_of_streams h.valid h.pops
  rw [Memory.Tree.every_node] at hP
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := h.valid
  intro k hkm
  by_cases hl : k.name = "__loop4_main"
  · exact Or.inl hl
  right
  have hkP := Memory.Tree.every_of_mem hP.2 hkm
  obtain ⟨c, hc, hn, hpv⟩ := kidsValid_mem hk k hkm
  rcases hpv with ⟨f', σ'', rfl⟩ | ⟨a, r, hv⟩
  · exact Memory.Tree.every_phantom
  have hcb : c.f ∈ Stmt.blockCallees fn.body := walk_callees (σ := σ) fn.body (by rw [hw]; exact hc)
  have hS : NonVs k.name := by
    rw [hn]
    refine ⟨?_, hn ▸ hl, (calleesOff_of_find hf c.f hcb).1⟩
    rcases calleesVs_of_find hf c.f hcb with h1 | h1 | h1
    · exact h1
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
  have hN := every_of_everyIn nonVs_everyIn k hv hS
  exact Memory.Tree.Every.mono (fun f σ' hq => cyc_of_pathIn hrel hlim hT op hq.1 hq.2) (hN.and hkP)

/-- **The children's loop at the cycle certificates**: a `LoopRun` within `loopCntC iterSumV op` of the node's items,
its iterations' callees with their cycle hand facts. -/
def LoopCyc (al : String → Bool) : Prop :=
  ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∀ rd σ bufs kids, MainHonest al s w rd (.node "main" σ bufs kids) → ∀ op,
      ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
        LoopRun "__loop4_main" (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params
          (Data.chloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main")
          (fun k => k.Every (HandFact coreProgram
            (chCertAt op (daCntC op (itemsOf s w).rows) (loopCntC iterSumV op (itemsOf s w)))
            (chHandAt op (daCntC op (itemsOf s w).rows) (loopCntC iterSumV op (itemsOf s w))) (chOut op))) k S ∧
          S ≤ loopCntC iterSumV op (itemsOf s w)

/-- **`main`'s cycle hand facts from the loop's and an empty claim list's arm.** -/
theorem mainCycles_of (hT : ThenSame "claim_list_digest" (.n 3) (.n 12) (.n 13)) (hloop : LoopCyc al) :
    MainCycles al true := by
  intro s w hrel hlim hch rd t h op
  show CycH op (itemsOf s w) rd t
  cases t with
  | phantom => exact h.valid.elim
  | node f σ bufs kids =>
  have hf : f = "main" := h.name
  subst hf
  exact ⟨σ, bufs, kids, rfl, main_kids_cyc hrel hlim hT op h, hloop s w hrel hlim hch rd σ bufs kids h op,
    main_cyc_own hrel hlim h op⟩

end
end LeanVM.Guest.Complete
