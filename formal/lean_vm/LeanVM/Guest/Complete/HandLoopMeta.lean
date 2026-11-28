/-
  LeanVM.Guest.Complete.HandLoopMeta

  `main`'s loop pops the children's metas in order (`loopMetaStream`), so each iteration's counts are its
  child's (`loopMeta_all`).
-/

module

public import LeanVM.Guest.Complete.HandLoop

/-!
# The loop's `child_meta` stream

* The honest side: `honestPushes`' `child_meta` entries are the children's metas, in order (`honest_meta`):
  each child's block starts with its meta, and no other push is of that stream.
* `main`'s side: its own events pop no `child_meta` (`own_noMeta`), so its entries are its callees', in
  order (`streamOf_splice_kids`); its callees but the loop pop none (`main_kids_every`), and it calls the
  loop at most once (`main_loop_count`, by the kernel over its straight segments).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## Streams through splices and lists -/

section Splice

variable {rd : Reader} {σ : Val}

theorem streamOf_flatten (s : String) : ∀ L : List (List Pop), streamOf s L.flatten = (L.map (streamOf s)).flatten
  | [] => rfl
  | l :: L => by rw [List.flatten_cons, List.map_cons, List.flatten_cons, streamOf_append, streamOf_flatten s L]

theorem streamOf_flatMap {α : Type} (s : String) (f : α → List Pop) :
    ∀ L : List α, streamOf s (L.flatMap f) = L.flatMap fun a => streamOf s (f a)
  | [] => rfl
  | a :: L => by rw [List.flatMap_cons, List.flatMap_cons, streamOf_append, streamOf_flatMap s f L]

/-- **A node whose own events pop nothing of a stream**: its entries of that stream are its callees', in
order. -/
theorem streamOf_splice_kids (s : String) : ∀ (es : List Ev) (ks : List (List Pop)),
    streamOf s (evPops rd σ es) = [] →
      streamOf s (splice rd σ es ks) = streamOf s (ks.take (calls es).length).flatten
  | [], ks, _ => by simp [splice, calls, streamOf]
  | .atom a :: es, ks, h => by
      rw [evPops_cons, streamOf_append, List.append_eq_nil_iff] at h
      have h1 : streamOf s (a.pops rd σ) = [] := h.1
      have hc : calls (.atom a :: es) = calls es := rfl
      rw [splice, streamOf_append, h1, List.nil_append, streamOf_splice_kids s es ks h.2, hc]
  | .inK x :: es, ks, h => by
      rw [evPops_cons, streamOf_append, List.append_eq_nil_iff] at h
      have hc : calls (.inK x :: es) = calls es := rfl
      rw [splice, streamOf_splice_kids s es ks h.2, hc]
  | .call f a r :: es, ks, h => by
      rw [evPops_cons, streamOf_append, List.append_eq_nil_iff] at h
      have hc : calls (.call f a r :: es) = ⟨f, a, r, true⟩ :: calls es := rfl
      rw [splice, streamOf_append, streamOf_splice_kids s es ks.tail h.2, hc, List.length_cons]
      cases ks with
      | nil => simp [streamOf]
      | cons k ks => rw [List.take_succ_cons, List.flatten_cons, streamOf_append]; rfl
  | .skip f a :: es, ks, h => by
      rw [evPops_cons, streamOf_append, List.append_eq_nil_iff] at h
      have hc : calls (.skip f a :: es) = ⟨f, a, [], false⟩ :: calls es := rfl
      rw [splice, streamOf_append, streamOf_splice_kids s es ks.tail h.2, hc, List.length_cons]
      cases ks with
      | nil => simp [streamOf]
      | cons k ks => rw [List.take_succ_cons, List.flatten_cons, streamOf_append]; rfl

/-- A flattened map whose entries are empty off the one element satisfying `p`. -/
theorem flatten_map_single {α β : Type} (p : α → Bool) (g : α → List β) {k : α} :
    ∀ l : List α, k ∈ l → p k = true → l.countP p ≤ 1 → (∀ x ∈ l, p x = false → g x = []) →
      (l.map g).flatten = g k
  | [], hk, _, _, _ => absurd hk List.not_mem_nil
  | x :: l, hk, hp, hc, h0 => by
      rw [List.map_cons, List.flatten_cons]
      by_cases hx : p x = true
      · rw [List.countP_cons_of_pos hx] at hc
        have hl : ∀ y ∈ l, p y = false := fun y hy => by
          by_contra hy'
          have := List.countP_pos_iff.mpr ⟨y, hy, by simpa using hy'⟩
          omega
        have hxk : x = k := by
          rcases List.mem_cons.mp hk with h | h
          · exact h.symm
          · rw [hl k h] at hp; exact absurd hp (by decide)
        have hnil : (l.map g).flatten = [] := by
          rw [List.flatten_eq_nil_iff]
          intro m hm
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
          exact h0 y (List.mem_cons_of_mem _ hy) (hl y hy)
        rw [hnil, List.append_nil, hxk]
      · have hx' : p x = false := by simpa using hx
        rw [h0 x List.mem_cons_self hx', List.nil_append]
        rw [List.countP_cons_of_neg (by simpa using hx)] at hc
        have hkl : k ∈ l := by
          rcases List.mem_cons.mp hk with h | h
          · subst h; rw [hx'] at hp; exact absurd hp (by decide)
          · exact h
        exact flatten_map_single p g l hkl hp hc fun y hy => h0 y (List.mem_cons_of_mem _ hy)

theorem kidsValid_countP {P : Core.Program} (q : String → Bool) : ∀ {cs : List Call} {ks : List Memory.Tree},
    Memory.Tree.KidsValid P rd σ cs ks → ks.countP (fun k => q k.name) = cs.countP (fun c => q c.f)
  | [], [], _ => rfl
  | c :: cs, k :: ks, ⟨hn, _, hks⟩ => by
      simp only [List.countP_cons, hn, kidsValid_countP q hks]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

end Splice

/-! ## `main` calls the loop at most once -/

/-- A straight statement's calls of the loop. -/
def loopCalls : Stmt → ℕ
  | .call f _ _ => if f == "__loop4_main" then 1 else 0
  | .callIf _ f _ => if f == "__loop4_main" then 1 else 0
  | _ => 0

theorem slEvs_loopCalls (σ : Val) (s : Stmt) :
    (calls (slEvs σ s)).countP (fun c => c.f == "__loop4_main") = loopCalls s := by
  cases s with
  | atom a => simp [slEvs, calls, Ev.call?, loopCalls]
  | call f args rets =>
      have e : calls [Ev.call f args rets] = [⟨f, args, rets, true⟩] := rfl
      simp [slEvs, e, loopCalls, List.countP_cons]
  | callIf c f args =>
      have e : calls [Ev.inK c, if σ c = 0 then .skip f args else .call f args []] =
          [⟨f, args, [], !decide (σ c = 0)⟩] := by
        by_cases h0 : σ c = 0 <;> simp only [h0, ↓reduceIte, decide_true, decide_false, Bool.not_true,
          Bool.not_false] <;> rfl
      simp [slEvs, e, loopCalls, List.countP_cons]
  | _ => simp [slEvs, calls, loopCalls]

theorem straight_loopCalls (σ : Val) : ∀ L : List Stmt,
    (calls (L.flatMap (slEvs σ))).countP (fun c => c.f == "__loop4_main") = (L.map loopCalls).sum
  | [] => rfl
  | s :: L => by
      rw [List.flatMap_cons, calls_append, List.countP_append, slEvs_loopCalls, straight_loopCalls σ L, List.map_cons,
        List.sum_cons]

set_option maxRecDepth 200000 in
theorem main_loopCounts : (Main.mPre.map loopCalls).sum = 0 ∧ (Main.mDa.map loopCalls).sum = 0 ∧
    (Main.mDaZ.map loopCalls).sum = 0 ∧ (Main.mMid.map loopCalls).sum ≤ 1 ∧ (Main.mLeaf.map loopCalls).sum = 0 ∧
    (Main.mAgg.map loopCalls).sum = 0 ∧ (Main.mPost.map loopCalls).sum = 0 := by
  decide +kernel

/-- **`main` calls the loop at most once.** -/
theorem main_loop_count (σ : Val) : (calls (mainEvs σ)).countP (fun c => c.f == "__loop4_main") ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := main_loopCounts
  have hinK : ∀ (v : V) (L : List Stmt), calls (Ev.inK v :: L.flatMap (slEvs σ)) = calls (L.flatMap (slEvs σ)) :=
    fun _ _ => rfl
  unfold mainEvs
  simp only [calls_append, List.countP_append, hinK, straight_loopCalls]
  split_ifs <;> omega

/-! ## The honest side -/

/-- The streams of `honestPushes`' prefix before the children. -/
def preNames : List String := ["meta", "fs_seed", "signers_split", "claims", "dup_claims"] ++ rawNames

theorem listPushes_preNames (es : List Prover.Entry) : ∀ p ∈ Prover.listPushes "claims" es, p.1 ∈ preNames := by
  intro p hp
  unfold Prover.listPushes at hp
  rcases List.mem_append.mp hp with hp | hp
  · split_ifs at hp
    · simp at hp
    · rw [List.mem_singleton] at hp; subst hp; simp [preNames]
  · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hp; simp [preNames]

theorem preX_names (s : NodeStatement) (w : NodeWitness) : ∀ p ∈ mPreX s w, p.1 ∈ preNames := by
  rw [mPreX_eq]
  refine names_append (names_append (names_append (names_append (names_append (names_append ?_ ?_) ?_) ?_) ?_)
    ?_) ?_
  · simp [preNames]
  · exact listPushes_preNames _
  · exact listPushes_preNames _
  · intro p hp; obtain ⟨_, -, rfl⟩ := List.mem_map.mp hp; simp [preNames]
  · intro p hp; obtain ⟨_, -, rfl⟩ := List.mem_map.mp hp; simp [preNames]
  · intro p hp
    obtain ⟨cs, -, hp⟩ := List.mem_flatMap.mp hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [preNames, rawNames]
    · exact List.mem_append_right _ (xmssHints_names _ _ _ p hp)
  · intro p hp
    obtain ⟨cs, -, hp⟩ := List.mem_flatMap.mp hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [preNames, rawNames]
    · exact List.mem_append_right _ (sphincsHints_names _ _ _ p hp)

theorem childSlotPushes_noMeta (os : List ℕ) : ∀ p ∈ Prover.childSlotPushes os, p.1 ≠ "child_meta" := by
  intro p hp
  unfold Prover.childSlotPushes at hp
  split_ifs at hp
  · simp at hp
  · simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨_, -, rfl⟩ <;> simp
  · simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨_, -, rfl⟩ <;> simp

/-- A child's meta entry. -/
def childMetaOf (c : Child) : Pop :=
  ("child_meta", [Prover.count c.statement.claims.xmss.length, Prover.count c.statement.claims.sphincs.length])

theorem kid_meta (s : NodeStatement) (w : NodeWitness) : streamOf "child_meta" (mKidPushes s w) = childMetas w := by
  have hx : (xPlan s w).childSlots.length = w.children.length := by
    have := congrArg List.length (B1.Main.plan_children_lengths s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)))
    simp only [List.length_map] at this
    rw [xPlan, (coveragePlan_eq _ _ _).2.2]; exact this
  have hs : (sPlan s w).childSlots.length = w.children.length := by
    have := congrArg List.length (B1.Main.plan_children_lengths s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)))
    simp only [List.length_map] at this
    rw [sPlan, (coveragePlan_eq _ _ _).2.2]; exact this
  have hblk : ∀ (c : Child) (xs ss : List ℕ), streamOf "child_meta"
      (childMetaOf c :: Prover.childSlotPushes xs ++ Prover.childSlotPushes ss ++
        [("child_defer", c.statement.deferredClaim.cells), ("child_da", Prover.digestCells c.statement.claims.daDigest)] ++
        Prover.childHints guestBytecode guestSeed c) = [childMetaOf c] := by
    intro c xs ss
    have h1 : List.filter (fun p : Pop => p.1 == "child_meta") (Prover.childSlotPushes xs) = [] :=
      streamOf_eq_nil.mpr (childSlotPushes_noMeta xs)
    have h2 := streamOf_eq_nil.mpr (childSlotPushes_noMeta ss)
    have h3 : streamOf "child_meta" (Prover.childHints guestBytecode guestSeed c) = [] :=
      streamOf_eq_nil.mpr fun p hp => (ch_others _ (childHints_chNames _ _ c p hp)).2.2
    have h4 : streamOf "child_meta" [("child_defer", c.statement.deferredClaim.cells),
        ("child_da", Prover.digestCells c.statement.claims.daDigest)] = [] := streamOf_eq_nil.mpr (by simp)
    rw [streamOf_append, streamOf_append, streamOf_append, h2, h3, h4]
    simp only [List.append_nil, streamOf]
    rw [List.filter_cons_of_pos, h1]
    simp [childMetaOf]
  have key : ∀ (L : List ((Child × List ℕ) × List ℕ)) (F : (Child × List ℕ) × List ℕ → List Pop),
      (∀ x, streamOf "child_meta" (F x) = [childMetaOf x.1.1]) →
        L.flatMap (fun a => streamOf "child_meta" (F a)) = (L.map (·.1.1)).map childMetaOf := by
    intro L F hF
    induction L with
    | nil => rfl
    | cons x L ih => simp [hF x, ih]
  unfold mKidPushes
  rw [streamOf_flatMap]
  refine (key _ _ ?_).trans ?_
  · rintro ⟨⟨c, xs⟩, ss⟩
    exact hblk c xs ss
  have h1 : ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots).map (·.1.1) = w.children := by
    have e : ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots).map (·.1.1) =
        (((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots).map Prod.fst).map Prod.fst := by
      rw [List.map_map]; rfl
    rw [e, List.map_fst_zip (by simp [hx, hs]), List.map_fst_zip (by omega)]
  rw [h1]
  rfl

theorem la_meta (s : NodeStatement) (w : NodeWitness) : streamOf "child_meta" (mLA s w) = [] := by
  rw [streamOf_eq_nil]
  intro p hp
  unfold mLA at hp
  split_ifs at hp
  · rw [List.mem_singleton] at hp; subst hp; simp
  · simp only [Prover.batchPushes, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> simp

theorem da_meta (w : NodeWitness) : streamOf "child_meta" (mDA w) = [] := by
  rw [streamOf_eq_nil]
  intro p hp he
  unfold mDA at hp
  cases hm : w.daMatrix with
  | none => simp [hm] at hp
  | some cm =>
    rw [hm] at hp
    have := daHints_names cm.1 cm.2 p hp
    rw [he] at this
    exact absurd this (by decide)

/-- **`honestPushes`' `child_meta` entries are the children's metas, in order.** -/
theorem honest_meta (s : NodeStatement) (w : NodeWitness) :
    streamOf "child_meta" (Prover.honestPushes guestBytecode guestSeed s w) = childMetas w := by
  have hpre : streamOf "child_meta" (mPreX s w) = [] := by
    rw [streamOf_eq_nil]
    intro p hp he
    have := preX_names s w p hp
    rw [he] at this
    exact absurd this (by decide)
  have hpick : streamOf "child_meta" [("da_pick", [Prover.count (Prover.daPick s w)])] = [] :=
    streamOf_eq_nil.mpr (by simp)
  rw [honest_eq, streamOf_append, streamOf_append, streamOf_append, streamOf_append, hpre, kid_meta, la_meta,
    da_meta, hpick]
  simp

/-! ## `main`'s side -/

/-- **`main`'s loop pops the children's metas in order.** -/
theorem loopMetaStream (al : String → Bool) : LoopMetaStream al := by
  intro s w hrel hlim hch rd σ bufs kids h k hk hkn a r hkv
  have hst : streamOf "child_meta" ((Memory.Tree.node "main" σ bufs kids).pops coreProgram rd) =
      streamOf "child_meta" (Prover.honestPushes guestBytecode guestSeed s w) := h.pops "child_meta"
  rw [honest_meta] at hst
  rw [← hst]
  have hS : coreProgram.EveryIn rd (fun f _ => f ≠ "__loop4_main") OffNode :=
    offNode_everyIn fun f hf _ _ _ _ _ _ _ => hf.2.2
  have hkids := main_kids_every hS h.valid (fun _ _ _ _ => by decide)
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hks⟩ := h.valid
  rw [Main.find_main] at hf
  obtain rfl := Option.some.inj hf
  rw [walk_main] at hw
  obtain ⟨rfl, -⟩ := Out.ret.inj hw
  have hown : streamOf "child_meta" (evPops rd σ (mainEvs σ)) = [] :=
    streamOf_eq_nil.mpr (own_noMeta (f := "main") (by decide) _ Main.find_main _ _ (walk_main σ))
  have hlen : (Memory.Tree.popsKids coreProgram rd kids).length ≤ (calls (mainEvs σ)).length := by
    have e1 := popsKids_length (P := coreProgram) (rd := rd) kids
    have e2 := Budget.kidsValid_length hks
    omega
  rw [pops_node (rd := rd) (bufs := bufs) (kids := kids) Main.find_main (walk_main σ),
    streamOf_splice_kids _ _ _ hown, List.take_of_length_le hlen, popsKids_map, streamOf_flatten, List.map_map]
  symm
  refine flatten_map_single (fun k : Memory.Tree => k.name == "__loop4_main")
    ((streamOf "child_meta") ∘ (·.pops coreProgram rd)) kids hk (by simpa using hkn) ?_ ?_
  · exact (kidsValid_countP (fun f => f == "__loop4_main") hks).trans_le (main_loop_count σ)
  · intro x hx hxn
    rcases hkids x hx with hl | hE
    · simp [hl] at hxn
    · obtain ⟨c, -, -, hpv⟩ := kidsValid_mem hks x hx
      rcases hpv with ⟨f', σ', rfl⟩ | ⟨a', r', hxv⟩
      · simp [Memory.Tree.pops, streamOf]
      · exact streamOf_eq_nil.mpr (pops_of_every x hxv (hE.mono fun f σ hf => own_noMeta hf))

/-- **Each iteration's counts are its child's**, on every honest `main` tree. -/
theorem loopMeta_all (al : String → Bool) : LoopMeta al := loopMeta_of (loopMetaStream al)

end
end LeanVM.Guest.Complete
