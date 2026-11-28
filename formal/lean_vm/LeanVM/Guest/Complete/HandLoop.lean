/-
  LeanVM.Guest.Complete.HandLoop

  The children's loop's hand facts (`LoopHand`) from its entry (`LoopEntry`) and the hand facts of
  `verify_sub`'s subtree (`VsNamesHand`): each iteration pops the next child's meta, so its two
  virtual values are that child's lists' lengths.
-/

module

public import LeanVM.Guest.Complete.HandLoopKit
public import LeanVM.Guest.Complete.HandKids
public import LeanVM.Guest.Complete.Cycles
public import LeanVM.Guest.Complete.CycCall
public import LeanVM.Guest.Complete.RawKit

/-!
# The children's loop

* No function but the loop hints `child_meta` (`metaFree_ok`, by the kernel), so a tree off `main`'s
  node pops none (`noMeta_offNode`), and a loop node's `child_meta` entries are its own meta hint's,
  `[v18, v19]`, then its tail's (`loop_node_split`).
* `child_claim_list_digest`'s hand fact from the pops (`child_hand`): its empty list's arm as
  `claimThenHand`, its nonempty one's as `claim_else_hand`.
* `loopHand_of`: `loopRun_countT` with the invariant that an iteration tree at counter `g^j` pops the
  children's metas from the `j`-th on, and every node has its path within the honest pushes and, in
  `verify_sub`'s subtree, its hand fact.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## No `child_meta` outside the loop -/

/-- An atom that is no `child_meta` witness hint. -/
def noMeta : Atom → Bool
  | .hint (.witness st _) => st != "child_meta"
  | _ => true

/-- The loop, or a body with no `child_meta` hint. -/
def metaFree (_ : ℕ) (fn : Fn) : Bool := decide (fn.name = "__loop4_main") || Stmt.atomsAll noMeta fn.body

theorem metaFree_0 : RangeOk metaFree 0 200 := by unfold RangeOk; decide +kernel
theorem metaFree_200 : RangeOk metaFree 200 200 := by unfold RangeOk; decide +kernel
theorem metaFree_400 : RangeOk metaFree 400 200 := by unfold RangeOk; decide +kernel
theorem metaFree_600 : RangeOk metaFree 600 200 := by unfold RangeOk; decide +kernel
theorem metaFree_800 : RangeOk metaFree 800 200 := by unfold RangeOk; decide +kernel
theorem metaFree_1000 : RangeOk metaFree 1000 200 := by unfold RangeOk; decide +kernel
theorem metaFree_1200 : RangeOk metaFree 1200 200 := by unfold RangeOk; decide +kernel
theorem metaFree_1400 : RangeOk metaFree 1400 169 := by unfold RangeOk; decide +kernel

/-- **Only the loop hints `child_meta`**, by the kernel. -/
theorem metaFree_ok : RangeOk metaFree 0 coreProgram.length := by
  rw [coreProgram_length]
  exact (((((((metaFree_0).append metaFree_200).append metaFree_400).append metaFree_600).append
    metaFree_800).append metaFree_1000).append metaFree_1200).append metaFree_1400

theorem metaFree_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) (hf : f ≠ "__loop4_main") :
    Stmt.atomsAll noMeta fn.body = true := by
  obtain ⟨j, hj, hjf⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some h)
  have hn : fn.name = f := fn_name_of_find (P := coreProgram) h
  have hc := RangeOk.all metaFree_ok hj
  rw [hjf] at hc
  simp only [metaFree, Bool.or_eq_true, decide_eq_true_eq, hn] at hc
  exact hc.resolve_left hf

variable {rd : Reader}

theorem own_noMeta {f : String} {σ : Val} (hf : f ≠ "__loop4_main") :
    OwnPops coreProgram rd (fun p => p.1 ≠ "child_meta") f σ := by
  intro fn hfn es vs hw p hp
  obtain ⟨e, he, hpe⟩ := List.mem_flatMap.mp hp
  cases e with
  | atom a =>
      have hm := walk_atomsAll' (metaFree_of_find hfn hf) hw a he
      cases a with
      | hint hh =>
          cases hh with
          | witness st d =>
              simp only [Ev.pops, Atom.pops, Hint.pops, List.mem_singleton] at hpe
              subst hpe
              simpa [noMeta] using hm
          | _ => simp [Ev.pops, Atom.pops, Hint.pops] at hpe
      | _ => simp [Ev.pops, Atom.pops] at hpe
  | _ => simp [Ev.pops] at hpe

/-- **A callee off `main`'s node pops no `child_meta`.** -/
theorem noMeta_offNode {k : Memory.Tree}
    (hk : (∃ f σ', k = .phantom f σ') ∨ ∃ a r, k.Valid coreProgram rd a r)
    (hoff : k.Every (fun f _ => OffNode f)) : streamOf "child_meta" (k.pops coreProgram rd) = [] := by
  rcases hk with ⟨f, σ', rfl⟩ | ⟨a, r, hv⟩
  · simp [Memory.Tree.pops, streamOf]
  · exact streamOf_eq_nil.mpr (pops_of_every k hv (hoff.mono fun f σ h => own_noMeta h.2.2))

/-! ## The loop node -/

/-- The `child_meta` hints of a statement, by destination. -/
def metaDests : Stmt → List Dest
  | .atom (.hint (.witness st d)) => if st = "child_meta" then [d] else []
  | _ => []

theorem slEvs_meta {σ : Val} (s : Stmt) :
    streamOf "child_meta" (evPops rd σ (slEvs σ s)) = (metaDests s).map fun d => ("child_meta", d.words rd σ) := by
  cases s with
  | atom a =>
      cases a with
      | hint hh =>
          cases hh with
          | witness st d =>
              by_cases hs : st = "child_meta"
              · subst hs; simp [slEvs, evPops, Ev.pops, Atom.pops, Hint.pops, streamOf, metaDests]
              · simp [slEvs, evPops, Ev.pops, Atom.pops, Hint.pops, streamOf, metaDests, hs]
          | _ => simp [slEvs, evPops, Ev.pops, Atom.pops, Hint.pops, streamOf, metaDests]
      | _ => simp [slEvs, evPops, Ev.pops, Atom.pops, streamOf, metaDests]
  | callIf c f args =>
      by_cases hc : σ c = 0 <;> simp [slEvs, evPops, Ev.pops, streamOf, metaDests, hc]
  | _ => simp [slEvs, evPops, Ev.pops, streamOf, metaDests]

theorem straight_meta {σ : Val} : ∀ ss : List Stmt,
    streamOf "child_meta" (evPops rd σ (ss.flatMap (slEvs σ))) =
      (ss.flatMap metaDests).map fun d => ("child_meta", d.words rd σ)
  | [] => rfl
  | s :: ss => by
      rw [List.flatMap_cons, evPops, List.flatMap_append, ← evPops, ← evPops, streamOf_append, slEvs_meta,
        straight_meta ss, List.flatMap_cons, List.map_append]

theorem loopPre_straight : loopPre.all Stmt.straight = true := by unfold loopPre; decide +kernel

theorem loopPre_meta : loopPre.flatMap metaDests = [.stack [.n 18, .n 19]] := by unfold loopPre; decide +kernel

theorem loop_params : (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params = (List.range 16).map V.n := by
  decide +kernel

theorem popsKids_map {P : Core.Program} : ∀ ks : List Memory.Tree, Memory.Tree.popsKids P rd ks = ks.map (·.pops P rd)
  | [] => by rw [Memory.Tree.popsKids]; rfl
  | k :: ks => by rw [Memory.Tree.popsKids, popsKids_map ks, List.map_cons]

/-- **A loop node**: its path through the iteration, its callees but the tail, its `child_meta` entries
its own meta hint's then its tail's, and its tail's counter the next one. -/
theorem loop_node_split {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {a r : List E}
    (hv : (Memory.Tree.node "__loop4_main" σ bufs kids).Valid coreProgram rd a r) :
    ∃ es ks1 tk, kids = ks1 ++ [tk] ∧ walk σ loopPre = .fall es ∧ HoldsAll rd σ es ∧
      Memory.Tree.KidsValid coreProgram rd σ (calls es) ks1 ∧
      streamOf "child_meta" ((Memory.Tree.node "__loop4_main" σ bufs kids).pops coreProgram rd) =
        ("child_meta", [σ (.n 18), σ (.n 19)]) :: streamOf "child_meta" (tk.pops coreProgram rd) ∧
      tk.name = "__loop4_main" ∧ ((∃ f' σ', tk = .phantom f' σ') ∨ ∃ a' r', tk.Valid coreProgram rd a' r') ∧
      ((∃ a' r', tk.Valid coreProgram rd a' r') → tk.val (.n 0) = σ (.n 0) * gen) := by
  obtain ⟨c, i', p0, prest, hps, hbody, hnr, hst, -⟩ := loopShape_spec loopShape_loop
  rw [fn_name_of_find (P := coreProgram) loop_find] at hbody
  have hp0 : p0 = .n 0 := by
    have := hps; rw [loop_params] at this; exact (List.cons.inj this).1.symm
  subst hp0
  obtain ⟨fn', hf', hp, es, vs, hw, -, hes, hk⟩ := hv
  rw [loop_find] at hf'
  cases hf'
  have hw0 := hw
  have hw1 := walk_straight_fall σ loopPre loopPre_straight
  rw [hbody, walk_append, hw1] at hw
  have hwt : walk σ [.callIf c "__loop4_main" (i' :: prest), .ret []] =
      .ret [.inK c, if σ c = 0 then .skip "__loop4_main" (i' :: prest)
        else .call "__loop4_main" (i' :: prest) []] [] := by
    simp [walk, walk1, Out.seq, Out.pre]
  rw [hwt] at hw
  simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hes1 : HoldsAll rd σ (loopPre.flatMap (slEvs σ)) := fun e he => hes e (List.mem_append_left _ he)
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
    refine ⟨_, ks1, tk, rfl, hw1, hes1, hk1, ?_, htn, ?_, ?_⟩
    · have hS : coreProgram.EveryIn rd (fun f _ => OffNode f) OffNode :=
        offNode_everyIn fun f hf _ _ _ _ _ _ _ => hf
      have hnm : ∀ k ∈ Memory.Tree.popsKids coreProgram rd ks1, streamOf "child_meta" k = [] := by
        intro k hk'
        rw [popsKids_map] at hk'
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk'
        obtain ⟨c', -, -, hpv⟩ := kidsValid_mem hk1 t ht
        exact noMeta_offNode hpv
          (kids_every_of_offNode hS loopPre_callees σ _ ks1 hw1 hes1 hk1 t ht)
      have hl : (calls (loopPre.flatMap (slEvs σ))).length = (Memory.Tree.popsKids coreProgram rd ks1).length := by
        rw [popsKids_length, kidsValid_length hk1]
      have htail : splice rd σ [Ev.inK c, if σ c = 0 then .skip "__loop4_main" (i' :: prest)
          else .call "__loop4_main" (i' :: prest) []] [tk.pops coreProgram rd] = tk.pops coreProgram rd := by
        by_cases h0c : σ c = 0 <;> simp [splice, h0c]
      rw [pops_node (rd := rd) (bufs := bufs) (kids := ks1 ++ [tk]) loop_find hw0, splice_append,
        popsKids_append, hl, List.take_left' rfl, List.drop_left' rfl, Memory.Tree.popsKids, Memory.Tree.popsKids,
        htail, streamOf_append, streamOf_splice_own _ _ _ hnm, straight_meta, loopPre_meta]
      rfl
    · by_cases h0c : σ c = 0
      · simp only [h0c, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htv
        exact Or.inl htv.1
      · simp only [h0c, decide_false, Bool.not_false, ↓reduceIte] at htv
        exact Or.inr ⟨_, _, htv⟩
    · rintro ⟨a', r', hv'⟩
      have hi : σ i' = σ (.n 0) * ofK (addressOfIndex 1) := isStep_val hnr hw1 hes1 hst
      have hg1 : gen = ofK (addressOfIndex 1) := by rw [← LeanVM.Guest.Value.gen_pow_eq_ofK, pow_one]
      by_cases h0c : σ c = 0
      · simp only [h0c, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htv
        obtain ⟨⟨g', σ', rfl⟩, -⟩ := htv
        exact hv'.elim
      · simp only [h0c, decide_false, Bool.not_false, ↓reduceIte] at htv
        cases tk with
        | phantom => exact htv.elim
        | node g σt bt kt =>
          simp only [Memory.Tree.name] at htn
          subst htn
          obtain ⟨fn'', hf'', hp'', -⟩ := htv
          rw [loop_find] at hf''
          cases hf''
          rw [hps] at hp''
          simp only [List.map_cons, List.cons.injEq] at hp''
          show σt (.n 0) = _
          rw [hp''.1, hi, hg1]

/-! ## `child_claim_list_digest` -/

/-- `child_claim_list_digest`'s body with its nonempty list's arm emptied. -/
noncomputable def ccThenBody : List Stmt :=
  (fn% «child_claim_list_digest»).body.take 2 ++ .ite (.n 6) Digest.cc25Zero [] ::
    (fn% «child_claim_list_digest»).body.drop 3

set_option maxRecDepth 100000 in
theorem cc_body_split : ∃ n, (fn% «child_claim_list_digest»).body = (fn% «child_claim_list_digest»).body.take 2 ++
    .ite (.n 6) Digest.cc25Zero n :: (fn% «child_claim_list_digest»).body.drop 3 :=
  ⟨_, by rw [Digest.child_claim_list_digest_shape]; rfl⟩

set_option maxRecDepth 100000 in
theorem ccThen_names : (Stmt.usesList ccThenBody ++ Stmt.tmpsList ccThenBody).all (· ∉ [V.n 15, V.n 16]) = true ∧
    (fn% «child_claim_list_digest»).params.all (· ∉ [V.n 15, V.n 16]) = true := by
  decide +kernel

variable {s : NodeStatement} {w : NodeWitness}

set_option maxRecDepth 100000 in
/-- **`child_claim_list_digest`'s hand fact**, from the pops: on an empty list its virtual values are
off the path, on a nonempty one `list_split`'s returns split a list's length. -/
theorem child_hand (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) {σ : Val}
    {C₁ C₂ : ℕ}
    (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) "child_claim_list_digest" σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "child_claim_list_digest" σ := by
  by_cases h6 : σ (.n 6) = 0
  · have h6' : setVals σ [.n 15, .n 16] 1 (.n 6) = 0 := by rw [setVals_of_not_mem (by decide)]; exact h6
    have hsame : SameOnPath coreProgram "child_claim_list_digest" σ (setVals σ [.n 15, .n 16] 1) := by
      refine sameOnPath_setVals (b := ccThenBody) (fun fn hfn => ?_) ccThen_names.1
      rw [Digest.find_child_claim_list_digest] at hfn
      obtain rfl := Option.some.inj hfn
      obtain ⟨n, hn⟩ := cc_body_split
      refine ⟨ccThen_names.2, ?_, ?_⟩
      · rw [hn]; exact walk_ite_zero h6 _ _
      · rw [hn]; exact walk_ite_zero h6' _ _
    refine handFact_of (j := 23) (n := 7) (bS := ⟨7998, [(5, 6106), (6, 890)]⟩) (bOS := ⟨14228, [(4, 45)]⟩)
      (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide)
      (by decide) rfl rfl (by decide +kernel) (by decide +kernel) hsame ?_
    intro fn hfn _
    rw [Digest.find_child_claim_list_digest] at hfn
    obtain rfl := Option.some.inj hfn
    have g15 : GPow (setVals σ [.n 15, .n 16] 1 (.n 15)) 0 := by
      rw [setVals_of_mem (by simp)]; exact ⟨(pow_zero gen).symm, by norm_num⟩
    have g16 : GPow (setVals σ [.n 15, .n 16] 1 (.n 16)) 0 := by
      rw [setVals_of_mem (by simp)]; exact ⟨(pow_zero gen).symm, by norm_num⟩
    have a5 : argExp ((fn% «child_claim_list_digest»).params.map σ ++
        [setVals σ [.n 15, .n 16] 1 (.n 15), setVals σ [.n 15, .n 16] 1 (.n 16)]) 5 = 0 := g15.logG
    have a6 : argExp ((fn% «child_claim_list_digest»).params.map σ ++
        [setVals σ [.n 15, .n 16] 1 (.n 15), setVals σ [.n 15, .n 16] 1 (.n 16)]) 6 = 0 := g16.logG
    refine ⟨argsPre_of (by decide) ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl)
      exacts [⟨_, g15⟩, ⟨_, g16⟩]
    · simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a5, a6]
      omega
  · obtain ⟨fn, hf, hh, -⟩ := hp
    rw [Digest.find_child_claim_list_digest] at hf
    obtain rfl := Option.some.inj hf
    rw [Digest.child_claim_list_digest_shape] at hh
    simp only [Stmt.HoldsList, Stmt.Holds] at hh
    obtain ⟨-, -, -, -, helse⟩ := hh
    have he := helse h6
    simp only [List.map_cons, List.map_nil] at he
    obtain ⟨hmem, a, b, c, habc, hng⟩ := list_split_in he.1
    obtain ⟨n, hsplit, hn⟩ := honest_split (honest_mem s w _ hmem)
    have hnb := listLen_le hrel hlim hn
    simp only [List.cons.injEq, and_true] at habc
    obtain ⟨rfl, rfl, rfl⟩ := habc
    simp only [Prover.listSplit, List.cons.injEq, and_true] at hsplit
    obtain ⟨h15, h16, h17⟩ := hsplit
    have hcb : Prover.claimBig = 136 := rfl
    have hcg : Prover.claimGroup = 17 := rfl
    rw [hcb] at h15 h16 h17
    rw [hcg] at h16 h17
    have g15 := count_gpow (n := n / 136) (by omega)
    have g16 := count_gpow (n := n % 136 / 17) (by omega)
    have g17 := count_gpow (n := n % 136 % 17) (by omega)
    rw [← h15] at g15; rw [← h16] at g16; rw [← h17] at g17
    have g4 : GPow (σ (.n 4)) n := by
      refine ⟨?_, by omega⟩
      rw [hng, g15.1, g16.1, g17.1, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    refine handFact_of (j := 23) (n := 7) (bS := ⟨7998, [(5, 6106), (6, 890)]⟩) (bOS := ⟨14228, [(4, 45)]⟩)
      (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide)
      (by decide) rfl rfl (by decide +kernel) (by decide +kernel) SameOnPath.refl ?_
    intro fn hfn _
    rw [Digest.find_child_claim_list_digest] at hfn
    obtain rfl := Option.some.inj hfn
    have a4 : argExp ((fn% «child_claim_list_digest»).params.map σ) 4 = n := g4.logG
    have a5 : argExp ((fn% «child_claim_list_digest»).params.map σ ++ [σ (.n 15), σ (.n 16)]) 5 = n / 136 :=
      g15.logG
    have a6 : argExp ((fn% «child_claim_list_digest»).params.map σ ++ [σ (.n 15), σ (.n 16)]) 6 =
        n % 136 / 17 := g16.logG
    refine ⟨argsPre_of (by decide) ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl)
      exacts [⟨_, g15⟩, ⟨_, g16⟩]
    · simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a4, a5, a6]
      omega

/-! ## Each iteration's counts -/

/-- The children's metas, in order. -/
def childMetas (w : NodeWitness) : List Pop :=
  w.children.map fun c =>
    ("child_meta", [Prover.count c.statement.claims.xmss.length, Prover.count c.statement.claims.sphincs.length])

/-- **`main`'s loop pops the children's metas in order** (left): on `main`'s honest tree, its loop callee's
`child_meta` entries are the children's. -/
def LoopMetaStream (al : String → Bool) : Prop :=
  ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∀ rd σ bufs kids, MainHonest al s w rd (.node "main" σ bufs kids) →
      ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r →
        streamOf "child_meta" (k.pops coreProgram rd) = childMetas w

theorem loop_params2 (σ : Val) : (((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params.map σ).take 2) =
    [σ (.n 0), σ (.n 1)] := by
  rw [loop_params]; rfl

/-- **A loop tree at counter `g^j` popping the children's metas from the `j`-th on has each iteration's
counts its child's.** -/
theorem loop_meta_every (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) :
    ∀ n (t : Memory.Tree) {a r : List E}, t.count ≤ n → t.Valid coreProgram rd a r → t.name = "__loop4_main" →
      ∀ j, t.val (.n 0) = gen ^ j → streamOf "child_meta" (t.pops coreProgram rd) = (childMetas w).drop j →
        t.Every (LoopMetaNode (itemsOf s w))
  | _, .phantom .., _, _, _, hv, _, _, _, _ => hv.elim
  | 0, .node .., _, _, hn, _, _, _, _, _ => by rw [Memory.Tree.count] at hn; omega
  | n + 1, .node f σ bufs kids, a, r, hcnt, hv, hname, j, hj0, hjm => by
      simp only [Memory.Tree.name] at hname
      subst hname
      obtain ⟨es, ks1, tk, rfl, hw, hes, hk1, hst, htn, hpv, hval⟩ := loop_node_split hv
      rw [hst] at hjm
      have hjn : j < w.children.length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (by simp only [childMetas, List.length_map]; omega)] at hjm
        exact List.cons_ne_nil _ _ hjm
      have hlen : j < (childMetas w).length := by simpa [childMetas] using hjn
      rw [← List.getElem_cons_drop hlen] at hjm
      obtain ⟨hm, hrest⟩ := List.cons.inj hjm
      have hσ0 : σ (.n 0) = gen ^ j := hj0
      have hcm : (childMetas w)[j] = ("child_meta", [Prover.count w.children[j].statement.claims.xmss.length,
          Prover.count w.children[j].statement.claims.sphincs.length]) := by simp [childMetas]
      rw [hcm] at hm
      simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at hm
      obtain ⟨h18, h19⟩ := hm
      have hmem := List.getElem_mem hjn
      have hx := listLen_le hrel hlim (Or.inr (Or.inr ⟨_, hmem, Or.inl rfl⟩))
      have hy := listLen_le hrel hlim (Or.inr (Or.inr ⟨_, hmem, Or.inr rfl⟩))
      have hnlt : w.children.length < 2 ^ 64 - 1 := by
        have := hlim.atMostSixteenChildren
        have h16 : Batch.maxRecursions = 16 := rfl
        omega
      rw [Memory.Tree.every_node, Memory.Tree.everyKids_iff]
      refine ⟨fun _ j' hj' ht => ?_, fun t ht => ?_⟩
      · rw [loop_params2] at ht
        have hn' : (itemsOf s w).children.length = w.children.length := by simp [itemsOf, NodeItems.ofWitness]
        rw [hn'] at hj' ht
        simp only [List.cons.injEq, and_true] at ht
        have hjj : j' = j := LeanVM.Guest.Value.gen_pow_inj (by omega) (by omega) (ht.1.symm.trans hσ0)
        subst hjj
        have hc : childClaims (itemsOf s w) j' = w.children[j'].statement.claims.xmss.length +
            w.children[j'].statement.claims.sphincs.length := by
          simp [childClaims, itemsOf, NodeItems.ofWitness, List.getElem?_eq_getElem hjn]
        rw [hc, h18, h19, (count_gpow (by omega)).logG, (count_gpow (by omega)).logG]
      · rcases List.mem_append.mp ht with ht | ht
        · have hS : coreProgram.EveryIn rd (fun f _ => OffNode f) OffNode :=
            offNode_everyIn fun f hf _ _ _ _ _ _ _ => hf
          exact (kids_every_of_offNode hS loopPre_callees σ es ks1 hw hes hk1 t ht).mono
            fun f _ hf hl => absurd hl hf.2.2
        · obtain rfl := List.mem_singleton.mp ht
          rcases hpv with ⟨f', σ', rfl⟩ | ⟨a', r', htv⟩
          · exact Memory.Tree.every_phantom
          · have hc' : t.count ≤ n := by
              have := countKids_le (ks := ks1 ++ [t]) (k := t) (by simp)
              rw [Memory.Tree.count] at hcnt
              omega
            refine loop_meta_every hrel hlim n t hc' htv htn (j + 1) ?_ hrest
            rw [hval ⟨_, _, htv⟩, hσ0, pow_succ]

variable {al : String → Bool}

/-- **Each iteration's counts its child's** (budget8's `LoopMeta`), from `main`'s loop popping the
children's metas in order. -/
theorem loopMeta_of (hms : LoopMetaStream al) : LoopMeta al := by
  intro s w hrel hlim hch rd t h
  cases t with
  | phantom => exact h.valid.elim
  | node f σ bufs kids =>
  obtain rfl : f = "main" := h.name
  have hS : coreProgram.EveryIn rd (fun f _ => f ≠ "__loop4_main") OffNode :=
    offNode_everyIn fun f hf _ _ _ _ _ _ _ => hf.2.2
  have hv0 := h.valid
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv0
  rw [Memory.Tree.every_node, Memory.Tree.everyKids_iff]
  refine ⟨fun hm => absurd hm (by decide), fun k hkm => ?_⟩
  rcases main_kids_every hS h.valid (fun _ _ _ _ => by decide) k hkm with hl | hoff
  · obtain ⟨c, -, -, hpv⟩ := kidsValid_mem hk k hkm
    rcases hpv with ⟨f', σ', rfl⟩ | ⟨a, r, hkv⟩
    · exact Memory.Tree.every_phantom
    · obtain ⟨ha, -⟩ := mainLoopCall al s w hrel hlim hch rd σ bufs kids h k hkm hl a r hkv
      refine loop_meta_every hrel hlim k.count k le_rfl hkv hl 0 ?_
        (by rw [List.drop_zero]; exact hms s w hrel hlim hch rd σ bufs kids h k hkm hl a r hkv)
      cases k with
      | phantom => exact hkv.elim
      | node g σk bk kk =>
        simp only [Memory.Tree.name] at hl
        subst hl
        obtain ⟨fn', hf', hp', -⟩ := hkv
        rw [loop_find] at hf'
        cases hf'
        rw [← hp', loop_params2] at ha
        simp only [List.cons.injEq] at ha
        exact ha.1
  · exact hoff.mono fun f _ hf hl => absurd hl hf

end
end LeanVM.Guest.Complete
