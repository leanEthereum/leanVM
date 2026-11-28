/-
  LeanVM.Guest.Complete.CycLoop

  The children's loop at the cycle certificates, on `main`'s honest tree: `HandShape`'s loop lemmas with a node
  predicate the tree satisfies (`loopRun_of_validR`, `loopRun_countR`), and `LoopCyc` from the values `verify_sub`
  certifies, the iterations' child counts and `main`'s loop call (`loopCyc_of`).
-/

module

public import LeanVM.Guest.Complete.CycKids
public import LeanVM.Guest.Complete.CycVs

/-!
# The children's loop's cycle hand facts

`loopRun_of_valid` and `loopRun_count` read an iteration's values on any valid node; on `main`'s honest tree they come
from its pops (an iteration's child counts) and from what `verify_sub` certifies, facts of the tree's own nodes. So the
loop lemmas here take a node predicate `R` the loop's tree satisfies (`Every R`) and give it to each iteration and its
callees. With `R` the path within the honest pushes (`every_pathIn_of_streams`) and `VsNodeVals`, every node below an
iteration has its cycle hand fact (`cyc_node`), and with each iteration's two counts its child's claims the run is
within `loopCntC` (`cyc_loopR`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## The loop lemmas with a node predicate -/

variable {rd : Reader} {Q R : String → Val → Prop}

/-- **`loopRun_of_valid` with a node predicate `R`** the tree satisfies, given to each iteration and its callees. -/
theorem loopRun_of_validR {fn : Fn}
    (hf : coreProgram.find? "__loop4_main" = some fn) {pre : List Stmt} {c i' p0 : V} {prest : List V}
    (hps : fn.params = p0 :: prest)
    (hbody : fn.body = pre ++ [.callIf c "__loop4_main" (i' :: prest), .ret []])
    (hnr : Stmt.noRetListS pre = true)
    (hkids : ∀ σ es ks, walk σ pre = .fall es → HoldsAll rd σ es →
      Memory.Tree.KidsValid coreProgram rd σ (calls es) ks → (∀ k ∈ ks, k.Every R) → ∀ k ∈ ks, k.Every Q)
    (h : Hand) (w : ℕ) (B : E → ℕ) (Inv : List E → Prop)
    (hit : ∀ σ es, walk σ pre = .fall es → HoldsAll rd σ es → Inv (fn.params.map σ) → R "__loop4_main" σ →
      ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧
        h.b.eval ((fn.params ++ h.vps).map σ) + (if σ c = 0 then w else B (σ i')) ≤ B (σ p0) ∧
        (σ c ≠ 0 → Inv ((i' :: prest).map σ))) :
    ∀ n (t : Memory.Tree) {args rets : List E}, t.count ≤ n → t.Valid coreProgram rd args rets →
      t.name = "__loop4_main" → t.Every R → Inv args →
        ∃ S, LoopRun "__loop4_main" fn.params h w (fun k => k.Every Q) t S ∧ S ≤ B (args.headD 0)
  | _, .phantom .., _, _, _, hv, _, _, _ => hv.elim
  | 0, .node .., _, _, hn, _, _, _, _ => by rw [Memory.Tree.count] at hn; omega
  | n + 1, .node f σ bufs kids, args, rets, hcnt, hv, hname, hR, hinv => by
      simp only [Memory.Tree.name] at hname
      subst hname
      rw [Memory.Tree.every_node, Memory.Tree.everyKids_iff] at hR
      obtain ⟨hRσ, hRk⟩ := hR
      obtain ⟨fn', hf', hp, es, vs, hw, -, hes, hk⟩ := hv
      rw [hf] at hf'
      cases hf'
      rw [hbody, walk_append] at hw
      rcases walk_noRet (σ := σ) pre hnr with ⟨es1, hw1⟩ | hw1
      · rw [hw1] at hw
        have hwt : walk σ [.callIf c "__loop4_main" (i' :: prest), .ret []] =
            .ret [.inK c, if σ c = 0 then .skip "__loop4_main" (i' :: prest)
              else .call "__loop4_main" (i' :: prest) []] [] := by
          simp [walk, walk1, Out.seq, Out.pre]
        rw [hwt] at hw
        simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        have hes1 : HoldsAll rd σ es1 := fun e he => hes e (List.mem_append_left _ he)
        rw [calls_append] at hk
        obtain ⟨ks1, ks2, hks12, hk1, hk2⟩ := kidsValid_splitA hk
        have hcalls : calls [Ev.inK c, if σ c = 0 then .skip "__loop4_main" (i' :: prest)
            else .call "__loop4_main" (i' :: prest) []] =
              [⟨"__loop4_main", i' :: prest, [], !decide (σ c = 0)⟩] := by
          by_cases h0c : σ c = 0 <;> simp only [h0c, ↓reduceIte, decide_true, decide_false,
            Bool.not_true, Bool.not_false] <;> rfl
        rw [hcalls] at hk2
        match ks2, hk2 with
        | [tk], ⟨htn, htv, _⟩ =>
          subst hks12
          obtain ⟨hpre, hle, hnext⟩ := hit σ es1 hw1 hes1 (by rw [hp]; exact hinv) hRσ
          have hQk : ∀ k ∈ ks1, k.Every Q :=
            hkids σ es1 ks1 hw1 hes1 hk1 fun k hk => hRk k (List.mem_append_left _ hk)
          have hargs : args.headD 0 = σ p0 := by rw [← hp, hps]; rfl
          by_cases h0c : σ c = 0
          · simp only [h0c, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htv
            obtain ⟨⟨g', σ', rfl⟩, -⟩ := htv
            simp only [Memory.Tree.name] at htn
            subst htn
            refine ⟨_, LoopRun.step hQk hpre (LoopRun.last σ'), ?_⟩
            rw [ite_eq_left h0c] at hle
            rw [hargs]; exact hle
          · simp only [h0c, decide_false, Bool.not_false, ↓reduceIte] at htv
            have hc' : tk.count ≤ n := by
              have := countKids_le (ks := ks1 ++ [tk]) (k := tk) (by simp)
              rw [Memory.Tree.count] at hcnt
              omega
            obtain ⟨S, hrun, hS'⟩ := loopRun_of_validR hf hps hbody hnr hkids h w B Inv hit n tk hc' htv htn
              (hRk tk (by simp)) (hnext h0c)
            refine ⟨_, LoopRun.step hQk hpre hrun, ?_⟩
            rw [ite_eq_right h0c] at hle
            simp only [List.map_cons, List.headD_cons] at hS'
            rw [hargs]; omega
      · rw [hw1] at hw; simp [Out.seq] at hw

/-- **`loopRun_count` with a node predicate `R`** the tree satisfies. -/
theorem loopRun_countR {fn : Fn}
    (hf : coreProgram.find? "__loop4_main" = some fn) {pre : List Stmt} (hsh : loopShape fn none = some pre)
    (hkids : ∀ σ es ks, walk σ pre = .fall es → HoldsAll rd σ es →
      Memory.Tree.KidsValid coreProgram rd σ (calls es) ks → (∀ k ∈ ks, k.Every R) → ∀ k ∈ ks, k.Every Q)
    (h : Hand) (w n : ℕ) (hn : n < 2 ^ 64 - 1) (cost : ℕ → ℕ)
    (hcost : ∀ σ, R "__loop4_main" σ → ∀ j < n, (fn.params.map σ).take 2 = [gen ^ j, gen ^ n] →
        ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧ h.b.eval ((fn.params ++ h.vps).map σ) ≤ cost j)
    (t : Memory.Tree) {args rets : List E} (hv : t.Valid coreProgram rd args rets) (hname : t.name = "__loop4_main")
    (hR : t.Every R) {j : ℕ} (hj : j < n) (hargs : args.take 2 = [gen ^ j, gen ^ n]) :
    ∃ S, LoopRun "__loop4_main" fn.params h w (fun k => k.Every Q) t S ∧
      S ≤ (∑ m ∈ Finset.Ico j n, cost m) + w := by
  obtain ⟨c, i', p0, prest, hps, hbody, hnr, hst, x, y, hadd, hxy⟩ := loopShape_spec hsh
  rw [fn_name_of_find (P := coreProgram) hf] at hbody
  have hg1 : gen = ofK (addressOfIndex 1) := by rw [← LeanVM.Guest.Value.gen_pow_eq_ofK, pow_one]
  obtain ⟨s, e, hse, hs, he⟩ : ∃ s e, (∀ σ : Val, σ c = σ x + σ y → σ c = σ s + σ e) ∧ isStep pre p0 s = true ∧
      isEnd pre prest.head? none e = true := by
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨x, y, fun _ h => h, h1, h2⟩
    · exact ⟨y, x, fun σ h => by rw [h, add_comm], h1, h2⟩
  have hhe : prest.head? = some e := by unfold isEnd at he; simpa using he
  obtain ⟨rest, rfl⟩ : ∃ rest, prest = e :: rest := by
    cases prest with
    | nil => simp at hhe
    | cons e' rest => simp only [List.head?_cons, Option.some.injEq] at hhe; exact ⟨rest, by rw [hhe]⟩
  have hlt : ∀ m ≤ n, logG (gen ^ m) = m := fun m hm => logG_gen_pow (by omega)
  let Inv : List E → Prop := fun a => ∃ j < n, a.take 2 = [gen ^ j, gen ^ n]
  have hit : ∀ σ es, walk σ pre = .fall es → HoldsAll rd σ es → Inv (fn.params.map σ) → R "__loop4_main" σ →
      ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧
        h.b.eval ((fn.params ++ h.vps).map σ) + (if σ c = 0 then w else loopB n cost w (σ i')) ≤
          loopB n cost w (σ p0) ∧ (σ c ≠ 0 → Inv ((i' :: e :: rest).map σ)) := by
    rintro σ es1 hw1 hes1 ⟨j, hj, ht⟩ hRσ
    have ht' := ht
    rw [hps] at ht'
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at ht'
    obtain ⟨hp0, hen⟩ := ht'
    obtain ⟨hpre, hb⟩ := hcost σ hRσ j hj ht
    have hsv : σ s = gen ^ (j + 1) := by rw [isStep_val hnr hw1 hes1 hs, hp0, ← hg1, pow_succ]
    have hiv : σ i' = gen ^ (j + 1) := by rw [isStep_val hnr hw1 hes1 hst, hp0, ← hg1, pow_succ]
    have hcv : σ c = σ s + σ e := hse σ (defAtom_holds hnr hw1 hes1 hadd)
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    have hsum : ∑ m ∈ Finset.Ico j n, cost m = cost j + ∑ m ∈ Finset.Ico (j + 1) n, cost m :=
      Finset.sum_eq_sum_Ico_succ_bot hj cost
    have hB0 : loopB n cost w (σ p0) = cost j + (∑ m ∈ Finset.Ico (j + 1) n, cost m) + w := by
      rw [loopB, hp0, hlt j hj.le, hsum]
    have hlast : σ c ≠ 0 → j + 1 < n := fun h0 => by
      rcases Nat.lt_or_ge (j + 1) n with h | h
      · exact h
      · exfalso
        have : j + 1 = n := by omega
        apply h0
        rw [hcv, hsv, hen, this]
        linear_combination gen ^ n * h2
    refine ⟨hpre, ?_, fun h0 => ⟨j + 1, hlast h0, by
      simp only [List.map_cons, List.take_succ_cons, List.take_zero, hiv, hen]⟩⟩
    by_cases h0 : σ c = 0
    · rw [ite_eq_left h0, hB0]
      have hjn : j + 1 = n := by
        refine LeanVM.Guest.Value.gen_pow_inj (by omega) (by omega) ?_
        rw [← hsv, ← hen]
        linear_combination (hcv.symm.trans h0) - σ e * h2
      rw [hjn, Finset.Ico_self, Finset.sum_empty]
      omega
    · rw [ite_eq_right h0, hB0, loopB, hiv, hlt (j + 1) (hlast h0).le]
      omega
  obtain ⟨S, hrun, hS'⟩ := loopRun_of_validR hf hps hbody hnr hkids h w (loopB n cost w) Inv hit t.count t
    le_rfl hv hname hR ⟨j, hj, hargs⟩
  refine ⟨S, hrun, ?_⟩
  have ha0 : args.headD 0 = gen ^ j := by
    match args, hargs with
    | a :: _ :: _, h => simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at h; exact h.1
    | [a], h => simp at h
    | [], h => simp at h
  rw [ha0, loopB, hlt j hj.le] at hS'
  exact hS'

/-- **`cyc_loop` with a node predicate `R`** the tree satisfies: the iterations' counts from `R`. -/
theorem cyc_loopR (op : Opcode) (it : NodeItems)
    (hkids : ∀ σ es ks, walk σ loopPre = .fall es → HoldsAll rd σ es →
      Memory.Tree.KidsValid coreProgram rd σ (calls es) ks → (∀ k ∈ ks, k.Every R) → ∀ k ∈ ks, k.Every Q)
    (hn : it.children.length < 2 ^ 64 - 1)
    (hval : ∀ σ, R "__loop4_main" σ → ∀ j < it.children.length,
      ((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params.map σ).take 2 = [gen ^ j, gen ^ it.children.length] →
        logG (σ (.n 18)) + logG (σ (.n 19)) ≤ childClaims it j)
    (t : Memory.Tree) {args rets : List E} (hv : t.Valid coreProgram rd args rets) (hname : t.name = "__loop4_main")
    (hR : t.Every R) (hargs : args.take 2 = [gen ^ 0, gen ^ it.children.length]) (h0 : 0 < it.children.length) :
    ∃ S, LoopRun "__loop4_main" (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params
      (Data.chloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main") (fun k => k.Every Q) t S ∧
        S ≤ loopCntC iterSumV op it := by
  obtain ⟨S, hrun, hS'⟩ := loopRun_countR loop_find loopShape_loop hkids
    (Data.chloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main") it.children.length hn
    (fun j => iterSumV op + claimV op * childClaims it j)
    (fun σ hRσ j hj ht => by
      refine ⟨fun q hq => by simp [HandV.proj, chloopHand_pre] at hq, ?_⟩
      rw [chloopHand_eval]
      have hv := hval σ hRσ j hj ht
      have e16 : argExp (((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params ++
          (Data.chloopHand.proj (B2C.opIdx op)).vps).map σ) 16 = logG (σ (.n 18)) := by
        unfold argExp
        rw [List.getD_eq_getElem?_getD, List.map_append, List.getElem?_append_right (by simp [loop_params_length])]
        simp [loop_params_length, HandV.proj, chloopHand_vps]
      have e17 : argExp (((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params ++
          (Data.chloopHand.proj (B2C.opIdx op)).vps).map σ) 17 = logG (σ (.n 19)) := by
        unfold argExp
        rw [List.getD_eq_getElem?_getD, List.map_append, List.getElem?_append_right (by simp [loop_params_length])]
        simp [loop_params_length, HandV.proj, chloopHand_vps]
      rw [e16, e17]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hv) _)
    t hv hname hR h0 hargs
  refine ⟨S, hrun, ?_⟩
  rw [← sum_childClaims, ← ωC_loop_last]
  exact hS'

/-! ## Each node below an iteration -/

/-- The hand functions outside `vsNames`, by name, by the kernel. -/
theorem pathIdx_names : ∀ j ∈ pathIdx, ((coreProgram[j]?).map Fn.name).all (fun nm => decide (nm ∉ vsNames)) = true := by
  decide +kernel

/-- **The cycle hand functions of `vsNames`**: `verify_keccak`, `check_stack_terminal`, `verify_sub` and
`child_claim_list_digest`, by the kernel. -/
theorem chVsIdx_ok : ∀ j ∈ vsIdx, (Data.chhandJ j).isSome = true → j = 8 ∨ j = 13 ∨ j = 15 ∨ j = 23 := by
  decide +kernel

variable {s : NodeStatement} {w : NodeWitness}

set_option maxRecDepth 100000 in
/-- **A node other than `main` and the loop has its cycle hand fact**, its path within the honest pushes and its
values those `verify_sub` certifies. -/
theorem cyc_node (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hT : ThenSame "claim_list_digest" (.n 3) (.n 12) (.n 13))
    (hTc : ThenSame "child_claim_list_digest" (.n 6) (.n 15) (.n 16)) (op : Opcode) {C₂ : ℕ} {f : String}
    {σ : Val} (hm : f ≠ "main") (hl : f ≠ "__loop4_main")
    (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) f σ) (hV : VsNodeVals f σ) :
    HandFact coreProgram (chCertAt op (daCntC op (itemsOf s w).rows) C₂) (chHandAt op (daCntC op (itemsOf s w).rows) C₂)
      (chOut op) f σ := by
  by_cases hv : f ∈ vsNames
  swap
  · exact cyc_of_pathIn hrel hlim hT op ⟨hv, hl, hm⟩ hp
  obtain ⟨fn, hf, -⟩ := id hp
  cases hh : Data.chhandJ (coreIdx f) with
  | none => exact handFact_ch_none op _ _ hl hh σ
  | some h =>
  have hs : (Data.chhandJ (coreIdx f)).isSome = true := by rw [hh]; rfl
  rcases chHandIdx_ok (coreIdx f) (coreIdx_lt hf) hs with hi | hi
  · have hpn := pathIdx_names _ hi
    rcases hn : (coreProgram[coreIdx f]?).map Fn.name with _ | nm
    · rw [List.getElem?_eq_getElem (coreIdx_lt hf)] at hn
      simp at hn
    · rw [hn] at hpn
      have := name_at hf rfl hn
      subst this
      simp at hpn
      exact absurd hv hpn
  have N : ∀ {j : ℕ} {nm : String}, coreIdx f = j → (coreProgram[j]?).map Fn.name = some nm → f = nm :=
    fun hj hn => name_at hf hj hn
  rcases chVsIdx_ok _ hi hs with hi | hi | hi | hi
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[8]?).map Fn.name = some "verify_keccak")
    exact verify_keccak_cyc op _ _ hV
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[13]?).map Fn.name = some "check_stack_terminal")
    exact check_stack_terminal_cyc op _ _ hV
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[15]?).map Fn.name = some "verify_sub")
    exact verify_sub_cyc op _ _ hV
  · obtain rfl := N hi (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel) :
      (coreProgram[23]?).map Fn.name = some "child_claim_list_digest")
    exact child_claim_cyc hrel hlim hTc op _ _ hp

/-! ## `LoopCyc` -/

/-- **What `verify_sub` certifies, at every node of `main`'s honest tree** (`VsNodeVals`). -/
def VsVals (al : String → Bool) : Prop :=
  ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∀ rd t, MainHonest al s w rd t → t.Every VsNodeVals

/-- An iteration's two counts within its child's claims, at counter `g^j`. -/
def LoopMetaNode (it : NodeItems) (f : String) (σ : Val) : Prop :=
  f = "__loop4_main" → ∀ j < it.children.length,
    ((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params.map σ).take 2 = [gen ^ j, gen ^ it.children.length] →
      logG (σ (.n 18)) + logG (σ (.n 19)) ≤ childClaims it j

/-- **Each iteration's two counts its child's** (`child_meta`'s pops in order), at every node of `main`'s honest
tree. -/
def LoopMeta (al : String → Bool) : Prop :=
  ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∀ rd t, MainHonest al s w rd t → t.Every (LoopMetaNode (itemsOf s w))

/-- **`main` enters the loop at counter `g^0` with end `g^n`**, `n` its children, at least one. -/
def MainLoopCall (al : String → Bool) : Prop :=
  ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∀ rd σ bufs kids, MainHonest al s w rd (.node "main" σ bufs kids) →
      ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r →
        a.take 2 = [gen ^ 0, gen ^ (itemsOf s w).children.length] ∧ 0 < (itemsOf s w).children.length

/-- **The children's loop's cycle hand facts**, from the two digests' empty arms, what `verify_sub` certifies, each
iteration's counts and `main`'s loop call. -/
theorem loopCyc_of {al : String → Bool} (hT : ThenSame "claim_list_digest" (.n 3) (.n 12) (.n 13))
    (hTc : ThenSame "child_claim_list_digest" (.n 6) (.n 15) (.n 16)) (hV : VsVals al) (hM : LoopMeta al)
    (hC : MainLoopCall al) : LoopCyc al := by
  intro s w hrel hlim hch rd σ bufs kids h op k hk hkn a r hkv
  have hP := every_pathIn_of_streams h.valid h.pops
  have hAll := (hP.and (hV s w hrel hlim hch rd _ h)).and (hM s w hrel hlim hch rd _ h)
  rw [Memory.Tree.every_node] at hAll
  have hkR := Memory.Tree.every_of_mem hAll.2 hk
  obtain ⟨hargs, h0⟩ := hC s w hrel hlim hch rd σ bufs kids h k hk hkn a r hkv
  have hn : (itemsOf s w).children.length < 2 ^ 64 - 1 := by
    have hb := hlim.withinMemoryBudget
    simp only [NodeWitness.memoryBudget, NodeWitness.childClaimCount] at hb
    simp only [itemsOf, NodeItems.ofWitness, List.length_map]
    omega
  have hOff : coreProgram.EveryIn rd (fun f _ => OffNode f) OffNode :=
    offNode_everyIn fun f hf _ _ _ _ _ _ _ => hf
  refine cyc_loopR op (itemsOf s w) (fun σ' es ks hw hes hks hR k' hk' => ?_) hn
    (fun σ' hR j hj ht => hR.2 rfl j hj ht) k hkv hkn hkR hargs h0
  have hO := kids_every_of_offNode hOff loopPre_callees σ' es ks hw hes hks k' hk'
  exact (hO.and (hR k' hk')).mono fun f σ'' ⟨ho, ⟨hp, hv⟩, _⟩ =>
    cyc_node hrel hlim hT hTc op ho.1 ho.2.2 hp hv

/-- **`main`'s cycle hand facts** from the two digests' empty arms, what `verify_sub` certifies, each iteration's
counts and `main`'s loop call. -/
theorem mainCycles_of_vals {al : String → Bool} (hT : ThenSame "claim_list_digest" (.n 3) (.n 12) (.n 13))
    (hTc : ThenSame "child_claim_list_digest" (.n 6) (.n 15) (.n 16)) (hV : VsVals al) (hM : LoopMeta al)
    (hC : MainLoopCall al) : MainCycles al true :=
  mainCycles_of hT (loopCyc_of hT hTc hV hM hC)

end
end LeanVM.Guest.Complete
