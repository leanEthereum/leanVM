/-
  LeanVM.Guest.Complete.HandKids

  `main`'s hand facts but the children's loop's: every node below a callee of `main` other than the
  loop has its hand fact (`main_kids_hand`), and `main`'s hand facts from the loop's
  (`mainHand_of`).
-/

module

public import LeanVM.Guest.Complete.HandDigest
public import LeanVM.Guest.Complete.HandShape
public import LeanVM.Guest.Budget.HandSame

/-!
# `main`'s callees but the loop

Only `verify_sub` and the children's loop call the functions whose hand facts need what a caller
certifies or a child's lists (`vsNames`, `calleesVs_ok`, by the kernel), so the functions outside
them, the loop and `main` are call-closed (`nonVs_everyIn`) and hold every node below `main`'s other
callees. Each such node's path is within the honest pushes (`every_pathIn_of_streams`), and so has its
hand fact (`hand_of_pathIn`): no inner check, a path-local one (`HandFacts`), `da_verify`'s or a
nonempty claim list's from the pops (`HandDigest`), or an empty claim list's (`claimThenHand`: its virtual values off the path).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## The call-closed set -/

/-- The hand functions certified by their caller or reading a child's lists: `verify_sub`, its
callees with such facts, and `child_claim_list_digest`. -/
def vsNames : List String :=
  ["verify_sub",
    "child_claim_list_digest",
    "verify_keccak",
    "check_stack_terminal",
    "open_stacked__L0",
    "open_stacked__L1",
    "open_stacked__L2",
    "open_stacked__L3",
    "open_stacked__L4",
    "open_stacked__L5",
    "open_stacked__L6",
    "open_stacked__L7",
    "open_stacked__L8",
    "open_stacked__L9",
    "open_stacked__L10",
    "open_stacked__L11",
    "open_stacked__L12",
    "open_stacked__L13",
    "open_stacked__L14"]

/-- Function `fn` calls no function of `vsNames`, unless it is the loop or `verify_sub`. -/
def calleesVs (_ : ℕ) (fn : Fn) : Bool :=
  (Stmt.blockCallees fn.body).all fun g =>
    decide (g ∉ vsNames) || decide (fn.name = "__loop4_main") || decide (fn.name = "verify_sub")

theorem calleesVs_0 : RangeOk calleesVs 0 200 := by unfold RangeOk; decide +kernel
theorem calleesVs_200 : RangeOk calleesVs 200 200 := by unfold RangeOk; decide +kernel
theorem calleesVs_400 : RangeOk calleesVs 400 200 := by unfold RangeOk; decide +kernel
theorem calleesVs_600 : RangeOk calleesVs 600 200 := by unfold RangeOk; decide +kernel
theorem calleesVs_800 : RangeOk calleesVs 800 200 := by unfold RangeOk; decide +kernel
theorem calleesVs_1000 : RangeOk calleesVs 1000 200 := by unfold RangeOk; decide +kernel
theorem calleesVs_1200 : RangeOk calleesVs 1200 200 := by unfold RangeOk; decide +kernel
theorem calleesVs_1400 : RangeOk calleesVs 1400 169 := by unfold RangeOk; decide +kernel

/-- **Only the loop and `verify_sub` call a function of `vsNames`**, by the kernel. -/
theorem calleesVs_ok : RangeOk calleesVs 0 coreProgram.length := by
  rw [coreProgram_length]
  have h := (((((((calleesVs_0).append calleesVs_200).append calleesVs_400).append calleesVs_600).append calleesVs_800).append calleesVs_1000).append calleesVs_1200).append calleesVs_1400
  exact h

theorem calleesVs_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) :
    ∀ g ∈ Stmt.blockCallees fn.body, g ∉ vsNames ∨ f = "__loop4_main" ∨ f = "verify_sub" := by
  obtain ⟨j, hj, hjf⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some h)
  have hn : fn.name = f := fn_name_of_find (P := coreProgram) h
  have hc := RangeOk.all calleesVs_ok hj
  rw [hjf] at hc
  intro g hg
  have := List.all_eq_true.mp hc g hg
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rw [hn] at this
  rcases this with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

/-- The functions outside `vsNames`, the loop and `main`. -/
def NonVs (f : String) : Prop := f ∉ vsNames ∧ f ≠ "__loop4_main" ∧ f ≠ "main"

/-- **The functions outside `vsNames`, the loop and `main` are call-closed.** -/
theorem nonVs_everyIn {rd : Reader} : coreProgram.EveryIn rd (fun f _ => NonVs f) NonVs := by
  intro f hf fn hfn
  refine ⟨fun g hg => ?_, fun _ _ _ _ _ => hf⟩
  obtain ⟨h1, h2⟩ := calleesOff_of_find hfn g hg
  obtain ⟨hv, hl, hm⟩ := hf
  refine ⟨?_, ?_, h1⟩
  · rcases calleesVs_of_find hfn g hg with h | h | h
    · exact h
    · exact absurd h hl
    · exact absurd (h ▸ (by decide : "verify_sub" ∈ vsNames)) hv
  · rcases h2 with h2 | ⟨-, h4⟩
    · exact absurd h2 hm
    · exact h4.resolve_right hl

/-! ## Names by index -/

theorem coreIdx_lt {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) : coreIdx f < coreProgram.length := by
  have hmem : f ∈ coreProgram.map (·.name) :=
    List.mem_map.mpr ⟨fn, List.mem_of_find?_eq_some hf, fn_name_of_find (P := coreProgram) hf⟩
  simpa [coreIdx] using List.idxOf_lt_length_of_mem hmem

/-- A function's name is the one at its index. -/
theorem name_at {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {j : ℕ} (hj : coreIdx f = j)
    {nm : String} (hn : (coreProgram[j]?).map Fn.name = some nm) : f = nm := by
  have hmem : f ∈ coreProgram.map (·.name) :=
    List.mem_map.mpr ⟨fn, List.mem_of_find?_eq_some hf, fn_name_of_find (P := coreProgram) hf⟩
  have hlt := List.idxOf_lt_length_of_mem hmem
  have hget := List.getElem_idxOf hlt
  have hlt' : coreIdx f < coreProgram.length := coreIdx_lt hf
  have h2 : (coreProgram[coreIdx f]'hlt').name = f := by rw [List.getElem_map] at hget; exact hget
  subst hj
  rw [List.getElem?_eq_getElem hlt', Option.map_some, Option.some.injEq, h2] at hn
  exact hn

/-- The hand functions outside `vsNames`, by index. -/
def pathIdx : List ℕ := [0, 6, 11, 12, 20, 26, 175, 542, 543, 544, 545, 546]

/-- The hand functions of `vsNames`, by index. -/
def vsIdx : List ℕ := [8, 13, 15, 23, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273]

/-- **Every hand function's index**, by the kernel. -/
theorem handIdx_ok : ∀ j < coreProgram.length, (Data.whhandJ j).isSome = true → j ∈ pathIdx ∨ j ∈ vsIdx := by
  rw [coreProgram_length]; decide +kernel

theorem vsIdx_names : ∀ j ∈ vsIdx, ∃ nm ∈ vsNames, (coreProgram[j]?).map Fn.name = some nm := by
  decide +kernel

/-! ## Each node's hand fact -/

/-- **`claim_list_digest`'s hand fact on an empty list** (`claimThenHand`). -/
def ClaimThenHand : Prop :=
  ∀ (rd : Reader) (σ : Val) (C₁ C₂ : ℕ), PathHolds coreProgram rd "claim_list_digest" σ → σ (.n 3) = 0 →
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "claim_list_digest" σ

/-- `claim_list_digest`'s body with its nonempty list's arm emptied. -/
noncomputable def clThenBody : List Stmt :=
  (fn% «claim_list_digest»).body.take 2 ++ .ite (.n 3) Digest.cl23Zero [] :: (fn% «claim_list_digest»).body.drop 3

set_option maxRecDepth 100000 in
theorem cl_body_split : (fn% «claim_list_digest»).body = (fn% «claim_list_digest»).body.take 2 ++
    .ite (.n 3) Digest.cl23Zero Digest.cl23Else :: (fn% «claim_list_digest»).body.drop 3 := by
  rw [Digest.claim_list_digest_shape]; rfl

set_option maxRecDepth 100000 in
theorem clThen_names : (Stmt.usesList clThenBody ++ Stmt.tmpsList clThenBody).all (· ∉ [V.n 12, V.n 13]) = true ∧
    (fn% «claim_list_digest»).params.all (· ∉ [V.n 12, V.n 13]) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`claim_list_digest`'s hand fact on an empty list**: its virtual values `v12`, `v13` are named
only on the arm not taken, so set to `1` they keep the path, and the inner bound is `5071 ≤ 7283`. -/
theorem claimThenHand : ClaimThenHand := by
  intro rd σ C₁ C₂ _ h3
  have h3' : setVals σ [.n 12, .n 13] 1 (.n 3) = 0 := by rw [setVals_of_not_mem (by decide)]; exact h3
  have hsame : SameOnPath coreProgram "claim_list_digest" σ (setVals σ [.n 12, .n 13] 1) := by
    refine sameOnPath_setVals (b := clThenBody) (fun fn hfn => ?_) clThen_names.1
    rw [Digest.find_claim_list_digest] at hfn
    obtain rfl := Option.some.inj hfn
    refine ⟨clThen_names.2, ?_, ?_⟩
    · rw [cl_body_split]; exact walk_ite_zero h3 _ _
    · rw [cl_body_split]; exact walk_ite_zero h3' _ _
  refine handFact_of (j := 20) (n := 4) (bS := ⟨5071, [(2, 2028), (3, 316)]⟩) (bOS := ⟨7283, [(1, 15)]⟩)
    (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide)
    (by decide) rfl rfl (by decide +kernel) (by decide +kernel) hsame ?_
  intro fn hfn _
  rw [Digest.find_claim_list_digest] at hfn
  obtain rfl := Option.some.inj hfn
  have g12 : GPow (setVals σ [.n 12, .n 13] 1 (.n 12)) 0 := by
    rw [setVals_of_mem (by simp)]; exact ⟨(pow_zero gen).symm, by norm_num⟩
  have g13 : GPow (setVals σ [.n 12, .n 13] 1 (.n 13)) 0 := by
    rw [setVals_of_mem (by simp)]; exact ⟨(pow_zero gen).symm, by norm_num⟩
  have a2 : argExp ((fn% «claim_list_digest»).params.map σ ++
      [setVals σ [.n 12, .n 13] 1 (.n 12), setVals σ [.n 12, .n 13] 1 (.n 13)]) 2 = 0 := g12.logG
  have a3 : argExp ((fn% «claim_list_digest»).params.map σ ++
      [setVals σ [.n 12, .n 13] 1 (.n 12), setVals σ [.n 12, .n 13] 1 (.n 13)]) 3 = 0 := g13.logG
  refine ⟨argsPre_of (by decide) ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl)
    exacts [⟨_, g12⟩, ⟨_, g13⟩]
  · simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a2, a3]
    omega

variable {s : NodeStatement} {w : NodeWitness} {rd : Reader}

set_option maxRecDepth 100000 in
/-- **A node outside `vsNames`, the loop and `main` has its hand fact**, its path within the honest
pushes. -/
theorem hand_of_pathIn (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hthen : ClaimThenHand) {C₂ : ℕ} {f : String} {σ : Val} (hS : NonVs f)
    (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) f σ) :
    HandFact coreProgram (whCertAt (daWordsC (itemsOf s w).rows) C₂) (whHandAt (daWordsC (itemsOf s w).rows) C₂)
      whOut f σ := by
  obtain ⟨hv, hl, hm⟩ := hS
  obtain ⟨fn, hf, -⟩ := id hp
  have hloop : coreIdx f ≠ Data.whidxLoop := fun h => hl (name_at hf h wh_nodeIdx.nl)
  have hj0 : coreIdx f ≠ Data.whidxMain := fun h => hm (name_at hf h wh_nodeIdx.nm)
  cases hh : whHandAt (daWordsC (itemsOf s w).rows) C₂ f with
  | none => exact handFact_of_none hloop hh
  | some h =>
  have e : whHandAt (daWordsC (itemsOf s w).rows) C₂ f = Data.whhandJ (coreIdx f) := by
    simp only [whHandAt, handAt, hj0, ↓reduceIte]
  rw [e] at hh
  rcases handIdx_ok (coreIdx f) (coreIdx_lt hf) (by rw [hh]; rfl) with hi | hi
  · simp only [pathIdx, List.mem_cons, List.not_mem_nil, or_false] at hi
    have N : ∀ {j : ℕ} {nm : String}, coreIdx f = j → (coreProgram[j]?).map Fn.name = some nm → f = nm :=
      fun hj hn => name_at hf hj hn
    rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi
    · exact absurd (N hi wh_nodeIdx.nm) hm
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[6]?).map Fn.name = some "rs_eq_run")
      exact rs_eq_run_hand hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[11]?).map Fn.name = some "squeeze_packed")
      exact squeeze_packed_hand hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[12]?).map Fn.name = some "ring_rows")
      exact ring_rows_hand hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[20]?).map Fn.name = some "claim_list_digest")
      by_cases h3 : σ (.n 3) = 0
      · exact hthen rd σ _ _ hp.pathHolds h3
      · exact claim_else_hand hrel hlim hp h3
    · obtain rfl := N hi wh_nodeIdx.nd
      exact da_verify_hand hlim hp
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[175]?).map Fn.name = some "link_rounds__L1_L0")
      exact link_rounds_hand (Or.inl rfl) hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[542]?).map Fn.name = some "link_rounds__L7_L0")
      exact link_rounds_hand (Or.inr (Or.inr (Or.inl rfl))) hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[543]?).map Fn.name = some "link_rounds__L6_L0")
      exact link_rounds_hand (Or.inr (Or.inl rfl)) hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[544]?).map Fn.name = some "link_rounds__L8_L1")
      exact link_rounds_hand (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[545]?).map Fn.name = some "link_rounds__L9_L1")
      exact link_rounds_hand (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hp.pathHolds
    · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
        (coreProgram[546]?).map Fn.name = some "link_rounds__L10_L1")
      exact link_rounds_hand (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hp.pathHolds
  · obtain ⟨nm, hnm, hn⟩ := vsIdx_names _ hi
    exact absurd (name_at hf rfl hn ▸ hnm) hv

/-! ## `main`'s callees -/

variable {al : String → Bool} {σ : Val} {bufs : List ℕ} {kids : List Tree}

/-- **Every node below a callee of `main` other than the loop has its hand fact.** -/
theorem main_kids_hand (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hthen : ClaimThenHand) {C₂ : ℕ} (h : MainHonest al s w rd (.node "main" σ bufs kids)) :
    ∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (whCertAt (daWordsC (itemsOf s w).rows) C₂) (whHandAt (daWordsC (itemsOf s w).rows) C₂) whOut) := by
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
  exact Memory.Tree.Every.mono (fun f σ' hq => hand_of_pathIn hrel hlim hthen hq.1 hq.2) (hN.and hkP)

/-- **The children's loop's hand facts** (left: `loopRun_of_valid` with each iteration's two lengths
the child's, from `child_meta`'s pops, and `verify_sub`'s callees' facts certified by it). -/
def LoopHand (al : String → Bool) : Prop :=
  ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∀ rd σ bufs kids, MainHonest al s w rd (.node "main" σ bufs kids) →
      ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
        LoopRun "__loop4_main" (coreProgram[Data.whidxLoop]'wh_nodeIdx.hl).params Data.whloopHand 62
          (fun k => k.Every (HandFact coreProgram
            (whCertAt (daWordsC (itemsOf s w).rows) (loopWordsC iterSum (itemsOf s w)))
            (whHandAt (daWordsC (itemsOf s w).rows) (loopWordsC iterSum (itemsOf s w))) whOut)) k S ∧
          S ≤ loopWordsC iterSum (itemsOf s w)

/-- **`main`'s hand facts from the loop's and an empty claim list's.** -/
theorem mainHand_of (hthen : ClaimThenHand) (hloop : LoopHand al) : MainHand al true := by
  intro s w hrel hlim hch rd t h
  show HandH (itemsOf s w) rd t
  cases t with
  | phantom => exact h.valid.elim
  | node f σ bufs kids =>
  have hf : f = "main" := h.name
  subst hf
  exact ⟨σ, bufs, kids, rfl, main_kids_hand hrel hlim hthen h, hloop s w hrel hlim hch rd σ bufs kids h,
    main_hand_own hrel hlim h⟩

/-- **`main`'s hand facts from the loop's.** -/
theorem mainHand_of_loop (hloop : LoopHand al) : MainHand al true := mainHand_of claimThenHand hloop

end
end LeanVM.Guest.Complete
