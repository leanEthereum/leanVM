module

public import Common.Indiff.Ideal

@[expose] public section

/-!
# Indifferentiability: the combined game's real side is the real world over random functions

The combined game answering with its full view (`combReal`) is, once the visible view and the
random oracles' cache are forgotten, the real world over a lazily sampled random function
(`funImpl`): a fresh node of the full view takes either a fresh uniform draw or the value of a
path whose oracle points have never been queried (`UInv`), which is a fresh uniform state too
(`combRealGame_evalDistEq_funGame`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- The oracle points of the value of `β` have never been queried. -/
def FreshVal (c : ACache Msg Dg E C) (β : List (Dg × E)) : Prop :=
  c (.inr β) = none ∧ ∀ m, P.unpad β = some m → c (.inl m) = none

/-- A uniform digest part replaced by an independent one leaves a uniform state. -/
theorem uniform_digest_evalDistEq :
    (($ᵗ Dg) >>= fun d ↦ ($ᵗ (SpState Dg E C)) >>= fun t ↦
      (pure ((d, t.1.2), t.2) : ProbComp (SpState Dg E C))) =ᵈ ($ᵗ (SpState Dg E C)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (Dg × E) C,
    SampleableType.uniformSample_prod_eq_bind Dg E]
  simp only [bind_assoc, pure_bind]
  refine (EvalDistEq.bind_right _ fun d ↦ EvalDistEq.bind_const _ _).trans ?_
  exact EvalDistEq.rfl

/-- **The value of a fresh path is a uniform state.** -/
theorem val_fresh_evalDistEq {β : List (Dg × E)} {c : ACache Msg Dg E C}
    (h : FreshVal P c β) :
    Prod.fst <$> (simulateQ (aSpec Msg Dg E C).romImpl (val P β)).run c =ᵈ
      ($ᵗ (SpState Dg E C)) := by
  rcases hm : P.unpad β with _ | m
  · rw [val_run_fresh_none P hm c h.1]
    simp
  · rw [val_run_fresh_some P hm c h.1, roStep_of_none (h.2 m hm)]
    simp only [bind_assoc, pure_bind, map_bind, map_pure]
    exact uniform_digest_evalDistEq (Dg := Dg) (E := E) (C := C)

/-- A continuation reading only the first component of a draw sees its first marginal. -/
theorem bind_fst_evalDistEq {α β γ : Type} {X : ProbComp (α × β)} {Y : ProbComp α}
    (h : Prod.fst <$> X =ᵈ Y) (R : α → ProbComp γ) : (X >>= fun w ↦ R w.1) =ᵈ (Y >>= R) := by
  rw [← bind_map_left]; exact EvalDistEq.bind_left h R

omit [DecidableEq E] [DecidableEq C] in
/-- Querying the value of one path keeps the other paths fresh. -/
theorem freshVal_of_val_support {β γ : List (Dg × E)} {c c' : ACache Msg Dg E C}
    (hne : γ ≠ β) (hagree : ∀ t, ¬ ValPt (C := C) P β t → c' t = c t) (h : FreshVal P c γ) :
    FreshVal P c' γ := by
  refine ⟨by rw [hagree (.inr γ) (by simpa [ValPt] using hne)]; exact h.1, fun m hm ↦ ?_⟩
  rw [hagree (.inl m) (fun hβ ↦ hne ?_)]
  · exact h.2 m hm
  · simp only [ValPt] at hβ
    rw [← (P.unpad_eq_some_iff γ m).mp hm, ← (P.unpad_eq_some_iff β m).mp hβ]

/-- **The full view's walk is the random function's sponge**: along a path whose unused prefixes
are fresh, the walk ends in the state and log of the sponge over the lazily sampled random
function. -/
theorem allWalk_evalDistEq (used : List (Dg × E) → Bool) (pre : List (Dg × E))
    (s : SpState Dg E C) (A : PermutationEdges (SpState Dg E C)) (bs : List (Dg × E))
    (c : ACache Msg Dg E C)
    (hfresh : ∀ i < bs.length, used (pre ++ bs.take (i + 1)) = false →
      FreshVal P c (pre ++ bs.take (i + 1))) :
    Prod.fst <$> (simulateQ (aSpec Msg Dg E C).romImpl (allWalk P used pre s A bs)).run c =ᵈ
      (absorbAll (fun x ↦ lazyFun (.forward x)) s bs).run A := by
  induction bs generalizing pre s A c with
  | nil => simp [allWalk]
  | cons B bs ih =>
    -- the rest of the walk, from any cache the first value query can leave
    have hrest : ∀ w ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
        (val P (pre ++ [B]))).run c), ∀ (y : SpState Dg E C) (A' : PermutationEdges (SpState Dg E C)),
        Prod.fst <$> (simulateQ (aSpec Msg Dg E C).romImpl
          (allWalk P used (pre ++ [B]) y A' bs)).run w.2 =ᵈ
          (absorbAll (fun x ↦ lazyFun (.forward x)) y bs).run A' := by
      intro w hw y A'
      obtain ⟨-, -, hagree⟩ := val_support P _ c hw
      refine ih (pre ++ [B]) y A' w.2 fun i hi hu ↦ ?_
      have hne : pre ++ [B] ++ bs.take (i + 1) ≠ pre ++ [B] := by
        intro h
        have h2 : bs.take (i + 1) = [] := by simpa using h
        rw [List.take_eq_nil_iff] at h2
        rcases h2 with h2 | h2
        · omega
        · subst h2; simp at hi
      have := hfresh (i + 1) (by simp; omega) (by simpa [List.take_succ_cons] using hu)
      simp only [List.take_succ_cons] at this
      exact freshVal_of_val_support P hne hagree (by simpa using this)
    simp only [allWalk, absorbAll_cons, simulateQ_bind, StateT.run_bind, drawSt_run,
      bind_map_left, map_bind]
    rcases hx : forwardLookup A (absorb s B) with _ | y
    · simp only [lazyFun, StateT.run_mk, hx, bind_map_left]
      by_cases hu : used (pre ++ [B]) = true
      · simp only [hu, ↓reduceIte]
        refine (EvalDistEq.bind_congr_of_support _ fun w hw ↦
          EvalDistEq.bind_right _ fun u ↦ hrest w hw u _).trans ?_
        exact EvalDistEq.bind_const _ _
      · simp only [Bool.not_eq_true] at hu
        simp only [hu, Bool.false_eq_true, ↓reduceIte]
        refine (EvalDistEq.bind_congr_of_support _ fun w hw ↦
          (EvalDistEq.bind_const _ _).trans (hrest w hw w.1 _)).trans ?_
        exact bind_fst_evalDistEq (val_fresh_evalDistEq P (by
          simpa using hfresh 0 (by simp) (by simpa using hu)))
          (fun a ↦ (absorbAll (fun x ↦ lazyFun (.forward x)) a bs).run ((absorb s B, a) :: A))
    · simp only [lazyFun, StateT.run_mk, hx, pure_bind]
      refine (EvalDistEq.bind_congr_of_support _ fun w hw ↦
        (EvalDistEq.bind_const _ _).trans (hrest w hw y A)).trans ?_
      exact EvalDistEq.bind_const _ _

/-- The paths whose values the combined game has queried are used: `T` and `H` are cached only
at used paths and at messages whose padding is used. -/
def UInv (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) : Prop :=
  (∀ β, c (.inr β) ≠ none → usedPath P cs.sim.chains cs.hashed β = true) ∧
    (∀ m, c (.inl m) ≠ none → usedPath P cs.sim.chains cs.hashed (P.pad m) = true)

/-- An unused path is fresh. -/
theorem freshVal_of_uInv {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (h : UInv P cs c)
    {β : List (Dg × E)} (hβ : usedPath P cs.sim.chains cs.hashed β = false) : FreshVal P c β := by
  refine ⟨by by_contra h'; rw [h.1 β h'] at hβ; exact Bool.noConfusion hβ, fun m hm ↦ ?_⟩
  by_contra h'
  have := h.2 m h'
  rw [(P.unpad_eq_some_iff β m).mp hm, hβ] at this
  exact Bool.noConfusion this

/-- Used paths stay used as rooted paths and hashed messages accumulate. -/
theorem usedPath_mono {VC VC' : List (SpState Dg E C × List (Dg × E))} {L L' : List Msg}
    (hVC : ∀ p ∈ VC, p ∈ VC') (hL : ∀ m ∈ L, m ∈ L') {β : List (Dg × E)}
    (h : usedPath P VC L β = true) : usedPath P VC' L' β = true := by
  simp only [usedPath, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h ⊢
  rcases h with h | ⟨m, hm, h⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact Or.inl (List.mem_map.mpr ⟨p, hVC p hp, rfl⟩)
  · exact Or.inr ⟨m, hL m hm, h⟩

/-- The run of the combined forward step. -/
theorem combFwd_run (x : SpState Dg E C) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl ((combFwd P iv x).run cs)).run c =
      ($ᵗ (SpState Dg E C)) >>= fun u ↦ (fun w ↦ (fwdOut P iv cs x u w.1, w.2)) <$>
        (simulateQ (aSpec Msg Dg E C).romImpl (visFwd P x u cs.sim)).run c := by
  simp only [combFwd, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind, drawSt_run]
  simp

/-- The run of the combined inverse step. -/
theorem combInv_run (y : SpState Dg E C) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl ((combInv iv y).run cs)).run c =
      (fun u ↦ (invOut iv cs y u, c)) <$> ($ᵗ (SpState Dg E C)) := by
  simp only [combInv, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind, drawSt_run]
  simp

/-- The run of the combined hash step. -/
theorem combHash_run (m : Msg) (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl ((combHash P iv m).run cs)).run c =
      (simulateQ (aSpec Msg Dg E C).romImpl
        (allWalk P (usedPath P cs.sim.chains cs.hashed) [] iv cs.all (P.pad m))).run c >>=
        fun w ↦ (fun d ↦ (hashOut cs m w.1 d.1, d.2)) <$>
          roStep (hs := aSpec Msg Dg E C) (.inl m) w.2 := by
  simp only [combHash, StateT.run_mk]
  rw [simulateQ_bind, StateT.run_bind]
  refine bind_congr fun w ↦ ?_
  rw [simulateQ_bind, StateT.run_bind, run_hq]
  simp

/-- The prefixes of the padding of a message are used once it is hashed. -/
theorem usedPath_of_mem_prefixesOf {VC : List (SpState Dg E C × List (Dg × E))} {L : List Msg}
    {m : Msg} (hm : m ∈ L) {β : List (Dg × E)} (h : β ∈ prefixesOf (P.pad m)) :
    usedPath P VC L β = true := by
  simp only [usedPath, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨m, hm, h⟩

/-- A padding is its own longest prefix. -/
theorem pad_mem_prefixesOf (m : Msg) : P.pad m ∈ prefixesOf (P.pad m) := by
  rw [mem_prefixesOf]
  refine ⟨(P.pad m).length - 1, by
    have := List.length_pos_iff.mpr (P.pad_ne_nil m); omega, ?_⟩
  rw [Nat.sub_add_cancel (List.length_pos_iff.mpr (P.pad_ne_nil m)), List.take_length]

/-- **Every step of the combined game keeps the paths it queries used.** -/
theorem uInv_combStep (t : (dSpec Msg Dg (SpState Dg E C)).Domain) {cs : CState Dg E C Msg}
    {c : ACache Msg Dg E C} (hU : UInv P cs c)
    {z : ((_ × _) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combStep P iv t).run cs)).run c)) : UInv P z.1.2 z.2 := by
  rcases t with n | m | x | y
  · rw [combStep_inl_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hU
  · simp only [combStep] at hz
    obtain ⟨w, c₁, d, hw, hd, hz1⟩ := combHash_support P iv m cs c hz
    obtain ⟨hcc₁, -, hagree, -⟩ := allWalk_support P _ [] iv cs.all (P.pad m) c hw
    obtain ⟨-, -, hagree'⟩ := roStep_support (hs := aSpec Msg Dg E C) (.inl m) c₁ hd
    rw [hz1]
    have hmono : ∀ β, usedPath P cs.sim.chains cs.hashed β = true →
        usedPath P cs.sim.chains (m :: cs.hashed) β = true := fun β h ↦
      usedPath_mono P (fun p hp ↦ hp) (fun m' hm' ↦ List.mem_cons_of_mem _ hm') h
    -- a changed entry is a value point of a prefix of the padding, or the digest of `m`
    have hchanged : ∀ t, z.2 t ≠ c t → t = .inl m ∨
        ∃ i < (P.pad m).length, ValPt (C := C) P ((P.pad m).take (i + 1)) t := by
      intro t ht
      by_cases htm : t = .inl m
      · exact Or.inl htm
      · right
        by_contra hno
        push Not at hno
        exact ht ((hagree' t htm).trans (hagree t fun i hi ↦ by simpa using hno i hi))
    refine ⟨fun β hβ ↦ ?_, fun m' hm' ↦ ?_⟩
    · by_cases hc : c (.inr β) = none
      · rcases hchanged (.inr β) (by rw [hc]; exact hβ) with h | ⟨i, hi, h⟩
        · exact absurd h (by simp)
        · simp only [ValPt] at h
          subst h
          exact usedPath_of_mem_prefixesOf P List.mem_cons_self
            (mem_prefixesOf.mpr ⟨i, hi, rfl⟩)
      · exact hmono β (hU.1 β hc)
    · by_cases hc : c (.inl m') = none
      · rcases hchanged (.inl m') (by rw [hc]; exact hm') with h | ⟨i, hi, h⟩
        · simp only [Sum.inl.injEq] at h
          subst h
          exact usedPath_of_mem_prefixesOf P List.mem_cons_self (pad_mem_prefixesOf P m')
        · simp only [ValPt] at h
          rw [(P.unpad_eq_some_iff _ m').mp h]
          exact usedPath_of_mem_prefixesOf P List.mem_cons_self
            (mem_prefixesOf.mpr ⟨i, hi, rfl⟩)
      · exact hmono _ (hU.2 m' hc)
  · simp only [combStep] at hz
    obtain ⟨u, r, hr, hz1⟩ := combFwd_support P iv x cs c hz
    rw [hz1]
    rcases visFwd_support P x u cs.sim c hr with ⟨y, hy, hrz⟩ | ⟨s, β, hy, hch, hv, hrz⟩ |
        ⟨hy, hch, hrz⟩
    · simp only [Prod.mk.injEq] at hrz
      obtain ⟨rfl, hc⟩ := hrz
      rw [hc]
      exact hU
    · simp only at hrz hv
      rw [hrz]
      obtain ⟨-, -, hagree⟩ := val_support P _ c hv
      simp only at hagree
      have hmono : ∀ γ, usedPath P cs.sim.chains cs.hashed γ = true →
          usedPath P ((r.1, β ++ [blockTo s x]) :: cs.sim.chains) cs.hashed γ = true :=
        fun γ h ↦ usedPath_mono P (fun p hp ↦ List.mem_cons_of_mem _ hp) (fun _ h ↦ h) h
      have hnew : usedPath P ((r.1, β ++ [blockTo s x]) :: cs.sim.chains) cs.hashed
          (β ++ [blockTo s x]) = true := by
        simp [usedPath]
      refine ⟨fun γ hγ ↦ ?_, fun m' hm' ↦ ?_⟩
      · by_cases hγβ : γ = β ++ [blockTo s x]
        · subst hγβ; exact hnew
        · exact hmono γ (hU.1 γ (by rwa [← hagree (.inr γ) (by simpa [ValPt] using hγβ)]))
      · by_cases hm : P.unpad (β ++ [blockTo s x]) = some m'
        · rw [(P.unpad_eq_some_iff _ m').mp hm]; exact hnew
        · exact hmono _ (hU.2 m' (by rwa [← hagree (.inl m') (by simpa [ValPt] using hm)]))
    · simp only [Prod.mk.injEq] at hrz
      obtain ⟨rfl, hc⟩ := hrz
      rw [hc]
      exact hU
  · simp only [combStep] at hz
    obtain ⟨u, rfl⟩ := combInv_support iv y cs c hz
    have hsim : (invOut iv cs y u).2.sim.chains = cs.sim.chains := by
      simp only [invOut, visInv]; split <;> rfl
    exact ⟨fun β hβ ↦ by rw [hsim]; exact hU.1 β hβ, fun m hm ↦ by rw [hsim]; exact hU.2 m hm⟩

/-- The run of the simulator's step at a fresh rooted node. -/
theorem visFwd_run_rooted {σ : SimState Dg E C} {x s : SpState Dg E C} {β : List (Dg × E)}
    (hy : forwardLookup σ.edges x = none) (hch : chainOf σ.chains x = some (s, β))
    (u : SpState Dg E C) (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl (visFwd P x u σ)).run c =
      (fun w ↦ ((w.1, (⟨(x, w.1) :: σ.edges, (w.1, β ++ [blockTo s x]) :: σ.chains⟩ :
        SimState Dg E C), some (β ++ [blockTo s x], w.1)), w.2)) <$>
        (simulateQ (aSpec Msg Dg E C).romImpl (val P (β ++ [blockTo s x]))).run c := by
  simp only [visFwd, hy, hch]
  rw [simulateQ_bind, StateT.run_bind]
  simp [map_eq_bind_pure_comp]

/-- One step of the folded combined game answering with the full view. -/
theorem foldReal_run (t : (dSpec Msg Dg (SpState Dg E C)).Domain) (cs : CState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    ((foldReal P iv) t).run (cs, c) = (fun z ↦ (z.1.1.1, (z.1.2, z.2))) <$>
      (simulateQ (aSpec Msg Dg E C).romImpl ((combStep P iv t).run cs)).run c := by
  rw [foldReal, foldRO_run]
  simp [combReal, StateT.run_map, simulateQ_map, Functor.map_map]

/-- **One step of the combined game's real side is one step of the real world over random
functions**, in distribution, once the visible view and the cache are forgotten. -/
theorem combReal_step_evalDistEq (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) (hU : UInv P cs c) :
    Prod.map id (fun s ↦ s.1.all) <$> ((foldReal P iv) t).run (cs, c) =ᵈ
      (funImpl P iv t).run cs.all := by
  rw [foldReal_run, Functor.map_map]
  rcases t with n | m | x | y
  · rw [combStep_inl_run]
    simp [funImpl, Functor.map_map]
  · simp only [combStep]
    rw [combHash_run, map_bind]
    simp only [Functor.map_map, hashOut, Prod.map_apply, id_eq]
    have h1 : ∀ w : (SpState Dg E C × PermutationEdges (SpState Dg E C)) × ACache Msg Dg E C,
        (fun d : Dg × ACache Msg Dg E C ↦ (w.1.1.1.1, w.1.2)) <$>
          roStep (hs := aSpec Msg Dg E C) (.inl m) w.2 =ᵈ
        (pure (w.1.1.1.1, w.1.2) : ProbComp (Dg × PermutationEdges (SpState Dg E C))) :=
      fun w ↦ EvalDistEq.map_const _ _
    refine (EvalDistEq.bind_right _ h1).trans ?_
    simp only [funImpl, spongeWith, StateT.run_map]
    have hw := EvalDistEq.map (allWalk_evalDistEq P _ [] iv cs.all (P.pad m) c
      fun i hi hu ↦ freshVal_of_uInv P hU hu) (fun p ↦ (p.1.out, p.2))
    simpa [Functor.map_map, map_eq_bind_pure_comp] using hw
  · simp only [combStep]
    rw [combFwd_run, map_bind]
    simp only [funImpl, lazyFun, StateT.run_mk, Functor.map_map, Prod.map_apply, id_eq]
    rcases hA : forwardLookup cs.all x with _ | y
    · -- a fresh node of the full view
      simp only [fwdOut, hA]
      rcases hy : forwardLookup cs.sim.edges x with _ | y'
      · rcases hch : chainOf cs.sim.chains x with _ | ⟨s, β⟩
        · simp [visFwd, hy, hch]
        · simp only [visFwd_run_rooted P hy hch, Functor.map_map]
          by_cases hu : usedPath P cs.sim.chains cs.hashed (β ++ [blockTo s x]) = true
          · simp only [hu, ↓reduceIte]
            rw [map_eq_bind_pure_comp]
            refine EvalDistEq.bind_right _ fun u ↦ ?_
            exact EvalDistEq.map_const _ (u, (x, u) :: cs.all)
          · simp only [Bool.not_eq_true] at hu
            simp only [hu, Bool.false_eq_true, ↓reduceIte]
            refine (EvalDistEq.bind_const _ _).trans ?_
            rw [← Functor.map_map Prod.fst (fun v ↦ (v, (x, v) :: cs.all))]
            exact EvalDistEq.map (val_fresh_evalDistEq P (freshVal_of_uInv P hU hu)) _
      · simp [visFwd, hy]
    · -- a recorded node of the full view
      simp only [fwdOut, hA]
      refine (EvalDistEq.bind_right _ fun u ↦ EvalDistEq.map_const _ (y, cs.all)).trans ?_
      exact EvalDistEq.bind_const _ _
  · simp only [combStep]
    rw [combInv_run, Functor.map_map]
    simp only [funImpl, lazyFun, StateT.run_mk, invOut]
    rcases hA : inverseLookup cs.all y with _ | x
    · simp
    · simp only [Prod.map_apply, id_eq]
      exact EvalDistEq.map_const ($ᵗ (SpState Dg E C)) (x, cs.all)

/-- **The combined game's real side is the real world over random functions.** -/
theorem combReal_run_evalDistEq {α : Type} (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    (simulateQ (foldReal P iv) oa).run' ((CState.init iv : CState Dg E C Msg), ∅) =ᵈ
      (simulateQ (funImpl P iv) oa).run' [] :=
  run'_simulateQ_evalDistEq_of_inv (foldReal P iv) (funImpl P iv)
    (fun s ↦ UInv P s.1 s.2) (fun s ↦ s.1.all)
    (fun t s hs z hz ↦ by
      obtain ⟨w, hw, hz2⟩ := mem_support_fold_comb P iv t s (fun _ p ↦ p.1) hz
      rw [hz2]
      exact uInv_combStep P iv t hs hw)
    (fun t s hs ↦ combReal_step_evalDistEq P iv t s.1 s.2 hs) oa _
    ⟨fun β h ↦ absurd rfl h, fun m h ↦ absurd rfl h⟩

end Setting

end Common
