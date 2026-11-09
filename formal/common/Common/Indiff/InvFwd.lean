module

public import Common.Indiff.InvLemmas

@[expose] public section

/-!
# Indifferentiability: the forward step keeps the invariant

A forward query `π x` of the combined game keeps `Inv`, and while no collision happens, the full
view's answer is the simulator's (`inv_combFwd`). Three cases: `x` is a recorded simulator
input; `x` is a fresh rooted node, whose path is hidden (the distinguisher reaches a node the
sponge has already been through) or new; `x` is a fresh unrooted node.
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
  {P : Padding Msg (Dg × E)} [P.Lawful] {iv : SpState Dg E C}

/-! ## Monotonicity -/

/-- States at the ends of paths stay put as the cache grows. -/
theorem svC_mono {c c' : ACache Msg Dg E C} (h : c ≤ c') {β : List (Dg × E)}
    {s : SpState Dg E C} (hs : svC P iv c β = some s) : svC P iv c' β = some s := by
  unfold svC at hs ⊢
  split at hs
  · simp_all
  · simp only [*, ite_false]
    exact valC_mono P h hs

/-- Hidden edges persist when hidden paths persist and the cache grows. -/
theorem hiddenEdge_mono {vs vs' : VState Dg E C Msg} {c c' : ACache Msg Dg E C} (hc : c ≤ c')
    (hH : ∀ β, Hidden P vs β → Hidden P vs' β) {e : SpState Dg E C × SpState Dg E C}
    (he : HiddenEdge P iv vs c e) : HiddenEdge P iv vs' c' e := by
  obtain ⟨β, B, s, v, hβ, hs, hv, rfl⟩ := he
  exact ⟨β, B, s, v, hH _ hβ, svC_mono hc hs, valC_mono P hc hv, rfl⟩

/-- A known path's end state is cached. -/
theorem svC_known {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (hS : Struct P iv cs c)
    {β : List (Dg × E)} (h : KnownPath P cs β) : ∃ s, svC P iv c β = some s := by
  rcases h with h | h
  · obtain ⟨s, hs⟩ := exists_chain_of_mem_vPaths h
    exact ⟨s, hS.chainVal _ hs⟩
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hS.hCached β h.1)
    exact ⟨v, (svC_of_hidden h).trans hv⟩

/-- The value of a path cached before a step is the value after. -/
theorem valC_eq_of_le {c c' : ACache Msg Dg E C} (h : c ≤ c') {β : List (Dg × E)}
    {v v' : SpState Dg E C} (hv : valC P c β = some v) (hv' : valC P c' β = some v') :
    v = v' := by
  rw [valC_mono P h hv] at hv'; exact Option.some.inj hv'

/-- The end state of a path cached before a step is the end state after. -/
theorem svC_eq_of_le {c c' : ACache Msg Dg E C} (h : c ≤ c') {β : List (Dg × E)}
    {v v' : SpState Dg E C} (hv : svC P iv c β = some v) (hv' : svC P iv c' β = some v') :
    v = v' := by
  rw [svC_mono h hv] at hv'; exact Option.some.inj hv'

/-! ## Lookups in the full view -/

/-- The full view answers a forward query with the edge it should hold. -/
theorem fwdLookup_all {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (hS : Struct P iv cs c) (hC : Cons P iv cs c) (hEC : ¬ EC P iv cs.vis c)
    {x y : SpState Dg E C} (h : GEdge P iv cs c (x, y)) : forwardLookup cs.all x = some y :=
  fwdLookup_eq_some_of_mem ((hC.allMem _).mpr h) fun e he hex ↦ by
    have := gEdge_fst_inj hS hC.vis hEC ((hC.allMem e).mp he) h hex
    rw [this]

/-- The full view answers an inverse query with the edge it should hold. -/
theorem invLookup_all {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (hS : Struct P iv cs c) (hC : Cons P iv cs c) (hEC : ¬ EC P iv cs.vis c)
    {x y : SpState Dg E C} (h : GEdge P iv cs c (x, y)) : inverseLookup cs.all y = some x :=
  invLookup_eq_some_of_mem ((hC.allMem _).mpr h) fun e he hey ↦ by
    have := gEdge_snd_inj hS hC.vis hEC ((hC.allMem e).mp he) h hey
    rw [this]

/-- The full view has no forward answer where it should hold no edge. -/
theorem fwdLookup_all_none {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (hC : Cons P iv cs c) {x : SpState Dg E C} (h : ∀ y, ¬ GEdge P iv cs c (x, y)) :
    forwardLookup cs.all x = none := by
  rw [fwdLookup_eq_none_iff]
  intro hx
  obtain ⟨⟨x', y⟩, he, rfl⟩ := List.mem_map.mp hx
  exact h y ((hC.allMem _).mp he)

/-- The full view has no inverse answer where it should hold no edge. -/
theorem invLookup_all_none {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (hC : Cons P iv cs c) {y : SpState Dg E C} (h : ∀ x, ¬ GEdge P iv cs c (x, y)) :
    inverseLookup cs.all y = none := by
  rw [invLookup_eq_none_iff]
  intro hy
  obtain ⟨⟨x, y'⟩, he, rfl⟩ := List.mem_map.mp hy
  exact h x ((hC.allMem _).mp he)

/-! ## The visible state after a new edge -/

/-- Recording a fresh simulator edge whose answer has no visible capacity keeps the simulator's
state consistent, given how the edge is classified. -/
theorem visCons_cons {σ : SimState Dg E C} (hV : VisCons σ) {x y : SpState Dg E C}
    {VC : List (SpState Dg E C × List (Dg × E))}
    (hx : x ∉ σ.edges.map Prod.fst) (hy : y ∉ σ.edges.map Prod.snd)
    (hVC : VC = σ.chains ∨ ∃ β, VC = (y, β) :: σ.chains ∧ y.2 ∉ σ.chains.map fun p ↦ p.1.2)
    (hnew : RootedEdge ⟨(x, y) :: σ.edges, VC⟩ (x, y) ∨ ∀ p ∈ VC, p.1.2 ≠ x.2)
    (hold : ∀ e ∈ σ.edges, ∀ p ∈ VC, p ∉ σ.chains → p.1.2 ≠ e.1.2) :
    VisCons ⟨(x, y) :: σ.edges, VC⟩ := by
  have hsub : ∀ p ∈ σ.chains, p ∈ VC := by
    rcases hVC with rfl | ⟨β, rfl, -⟩
    · exact fun p hp ↦ hp
    · exact fun p hp ↦ List.mem_cons_of_mem _ hp
  refine ⟨?_, List.nodup_cons.mpr ⟨hx, hV.vKeys⟩, List.nodup_cons.mpr ⟨hy, hV.vVals⟩, ?_⟩
  · rcases hVC with rfl | ⟨β, rfl, hcap⟩
    · exact hV.chainCap
    · exact List.nodup_cons.mpr ⟨hcap, hV.chainCap⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hnew
    · rcases hV.vClass e he with ⟨s, β, B, hs, hb, h⟩ | hun
      · exact Or.inl ⟨s, β, B, hsub _ hs, hsub _ hb, h⟩
      · refine Or.inr fun p hp ↦ ?_
        by_cases hpo : p ∈ σ.chains
        · exact hun p hpo
        · exact hold e he p hp hpo

/-- `Struct` only reads the simulator's state and the hashed messages. -/
theorem Struct.of_eq {cs cs' : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (h : Struct P iv cs c) (h1 : cs'.sim = cs.sim) (h2 : cs'.hashed = cs.hashed) :
    Struct P iv cs' c := by
  obtain ⟨a, b, d, e⟩ := h
  exact ⟨h1 ▸ a, h1 ▸ b, h1 ▸ d, h2 ▸ e⟩

/-! ## The three cases -/

variable (u : SpState Dg E C)

/-- **Recorded input.** -/
theorem inv_fwd_recorded {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (hI : Inv P iv cs c) {x y : SpState Dg E C} (hy : forwardLookup cs.sim.edges x = some y) :
    Inv P iv (fwdOut P iv cs x u (y, cs.sim, none)).2 c := by
  obtain ⟨hS, hcond⟩ := hI
  refine ⟨hS.of_eq rfl rfl, fun hbad hEC ↦ ?_⟩
  simp only [fwdOut, hy, Option.isNone_some, Bool.false_and, Bool.or_false] at hbad hEC ⊢
  have hC := hcond hbad hEC
  have hxy : GEdge P iv cs c (x, y) := Or.inl (mem_of_fwdLookup_eq_some hy)
  have hA := fwdLookup_all hS hC hEC hxy
  simp only [hA]
  refine ⟨hC.vis, hC.allMem, ?_⟩
  simp [hC.noDiff]

/-- **Fresh unrooted node.** -/
theorem inv_fwd_unrooted {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}
    (hI : Inv P iv cs c) {x : SpState Dg E C} (hy : forwardLookup cs.sim.edges x = none)
    (hch : chainOf cs.sim.chains x = none) :
    Inv P iv (fwdOut P iv cs x u (u, ⟨(x, u) :: cs.sim.edges, cs.sim.chains⟩, none)).2 c := by
  obtain ⟨hS, hcond⟩ := hI
  -- the new state, field by field
  set cs' := (fwdOut P iv cs x u (u, ⟨(x, u) :: cs.sim.edges, cs.sim.chains⟩, none)).2 with hcs'
  have hsim : cs'.sim = ⟨(x, u) :: cs.sim.edges, cs.sim.chains⟩ := rfl
  have hhashed : cs'.hashed = cs.hashed := rfl
  have hvP : vPaths cs'.sim = vPaths cs.sim := rfl
  have hHid : ∀ β, Hidden P cs'.vis β ↔ Hidden P cs.vis β := fun β ↦ Iff.rfl
  have hS' : Struct P iv cs' c :=
    ⟨hS.root, hS.chainVal, fun p hp hne ↦ by
      obtain ⟨q, hq, B, h1, h2⟩ := hS.chainEdge p hp hne
      exact ⟨q, hq, B, h1, List.mem_cons_of_mem _ h2⟩, hS.hCached⟩
  refine ⟨hS', fun hbad hEC' ↦ ?_⟩
  have hbad0 : cs.bad = false ∧ u.2 ∉ knownC iv cs.sim := by
    simpa [hcs', fwdOut, hy] using hbad
  -- the known capacities only grow, so there was no hidden collision before
  have hEC : ¬ EC P iv cs.vis c := by
    rintro ⟨β, v, hβ, hv, h⟩
    refine hEC' ⟨β, v, (hHid β).mpr hβ, hv, ?_⟩
    rcases h with h | ⟨γ, w, hγ, hne, hw, hwv⟩
    · exact Or.inl ((mem_knownC_cons iv).mpr (Or.inl h))
    · exact Or.inr ⟨γ, w, (hHid γ).mpr hγ, hne, hw, hwv⟩
  have hC := hcond hbad0.1 hEC
  -- the full view has no edge at `x`
  have hnoG : ∀ y, ¬ GEdge P iv cs c (x, y) := by
    rintro y (h | ⟨β, B, s, v, hβ, hs, hv, hxy⟩)
    · exact (fwdLookup_eq_none_iff.mp hy) (List.mem_map.mpr ⟨(x, y), h, rfl⟩)
    · simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      rcases knownPath_init hS (Or.inr hβ) with hk | hk
      · obtain ⟨t, ht⟩ := exists_chain_of_mem_vPaths hk
        have := hS.chainVal _ ht
        rw [hs] at this
        obtain rfl := Option.some.inj this
        exact chainOf_none hch _ ht rfl
      · refine hEC' ⟨β, s, (hHid β).mpr hk, (svC_of_hidden hk) ▸ hs, Or.inl ?_⟩
        exact (mem_knownC_cons iv).mpr (Or.inr (Or.inl rfl))
  have hA := fwdLookup_all_none hC hnoG
  have hcap : ∀ p ∈ cs.sim.chains, p.1.2 ∈ knownC iv cs.sim := fun p hp ↦
    chain_cap_mem_knownC P iv hS hp
  refine ⟨?_, fun e ↦ ?_, ?_⟩
  · exact visCons_cons hC.vis (fwdLookup_eq_none_iff.mp hy)
      (fun h ↦ by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
        exact hbad0.2 (snd_mem_knownC iv he))
      (Or.inl rfl) (Or.inr (chainOf_none hch)) (fun e _ p hp hpo ↦ absurd hp hpo)
  · simp only [hcs', fwdOut, hA, GEdge, List.mem_cons]
    constructor
    · rintro (rfl | h)
      · exact Or.inl (Or.inl rfl)
      · rcases (hC.allMem e).mp h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rintro ((rfl | h) | h)
      · exact Or.inl rfl
      · exact Or.inr ((hC.allMem e).mpr (Or.inl h))
      · exact Or.inr ((hC.allMem e).mpr (Or.inr h))
  · simp [hcs', fwdOut, hA, hC.noDiff]

/-- Hidden edges after a step were hidden edges before, when hidden paths after were hidden
before and the cache grew. -/
theorem hiddenEdge_back {cs : CState Dg E C Msg} {vs' : VState Dg E C Msg}
    {c c' : ACache Msg Dg E C} (hS : Struct P iv cs c) (hc : c ≤ c')
    (hH : ∀ δ, Hidden P vs' δ → Hidden P cs.vis δ) {e : SpState Dg E C × SpState Dg E C}
    (he : HiddenEdge P iv vs' c' e) : HiddenEdge P iv cs.vis c e := by
  obtain ⟨γ, G, t, w, hδ, ht, hw, rfl⟩ := he
  have hδ0 := hH _ hδ
  obtain ⟨w₀, hw₀⟩ := Option.ne_none_iff_exists'.mp (hS.hCached _ hδ0.1)
  obtain ⟨t₀, ht₀⟩ := svC_known hS (knownPath_init hS (Or.inr hδ0))
  obtain rfl := valC_eq_of_le hc hw₀ hw
  obtain rfl := svC_eq_of_le hc ht₀ ht
  exact ⟨γ, G, t₀, w₀, hδ0, ht₀, hw₀, rfl⟩

/-- **Fresh rooted node.** -/
theorem inv_fwd_rooted {cs : CState Dg E C Msg} {c c' : ACache Msg Dg E C}
    (hI : Inv P iv cs c) {x s v : SpState Dg E C} {β : List (Dg × E)}
    (hy : forwardLookup cs.sim.edges x = none) (hch : chainOf cs.sim.chains x = some (s, β))
    (hv : (v, c') ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      (val P (β ++ [blockTo s x]))).run c)) :
    Inv P iv (fwdOut P iv cs x u (v, ⟨(x, v) :: cs.sim.edges,
      (v, β ++ [blockTo s x]) :: cs.sim.chains⟩, some (β ++ [blockTo s x], v))).2 c' := by
  obtain ⟨hS, hcond⟩ := hI
  obtain ⟨hsβ, hsx⟩ := chainOf_some hch
  set B := blockTo s x with hB
  have hxB : absorb s B = x := absorb_blockTo hsx
  obtain ⟨hcc, hvv, -⟩ := val_support P (β ++ [B]) c hv
  simp only at hcc hvv
  set cs' := (fwdOut P iv cs x u (v, ⟨(x, v) :: cs.sim.edges,
    (v, β ++ [B]) :: cs.sim.chains⟩, some (β ++ [B], v))).2 with hcs'
  have hsim : cs'.sim = ⟨(x, v) :: cs.sim.edges, (v, β ++ [B]) :: cs.sim.chains⟩ := rfl
  have hhashed : cs'.hashed = cs.hashed := rfl
  have hvP : vPaths cs'.sim = (β ++ [B]) :: vPaths cs.sim := rfl
  have hne : β ++ [B] ≠ [] := by simp
  -- the bookkeeping
  have hS' : Struct P iv cs' c' := by
    refine ⟨List.mem_cons_of_mem _ hS.root, fun p hp ↦ ?_, fun p hp hpne ↦ ?_,
      fun δ hδ ↦ ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · simpa [svC, hne] using hvv
      · exact svC_mono hcc (hS.chainVal p hp)
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨(s, β), List.mem_cons_of_mem _ hsβ, B, rfl, by
          rw [hxB]; exact List.mem_cons_self⟩
      · obtain ⟨q, hq, B', h1, h2⟩ := hS.chainEdge p hp hpne
        exact ⟨q, List.mem_cons_of_mem _ hq, B', h1, List.mem_cons_of_mem _ h2⟩
    · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (hS.hCached δ hδ)
      rw [valC_mono P hcc hw]; simp
  refine ⟨hS', fun hbad hEC' ↦ ?_⟩
  have hbad0 : cs.bad = false ∧ v.2 ∉ knownC iv cs.sim := by
    simpa [hcs', fwdOut, hy] using hbad
  have hvK' : v.2 ∈ knownC iv cs'.sim :=
    (mem_knownC_cons iv).mpr (Or.inr (Or.inr rfl))
  have hK' : ∀ k, k ∈ knownC iv cs.sim → k ∈ knownC iv cs'.sim := fun k hk ↦
    (mem_knownC_cons iv).mpr (Or.inl hk)
  have hHid' : ∀ δ, Hidden P cs'.vis δ ↔ Hidden P cs.vis δ ∧ δ ≠ β ++ [B] := by
    intro δ
    simp only [Hidden, CState.vis, hhashed, hvP, List.mem_cons, not_or]
    tauto
  -- no hidden collision before
  have hEC : ¬ EC P iv cs.vis c := by
    rintro ⟨β₀, v₀, hβ₀, hv₀, h⟩
    have hv₀' := valC_mono P hcc hv₀
    by_cases h0 : β₀ = β ++ [B]
    · subst h0
      obtain rfl := valC_eq_of_le hcc hv₀ hvv
      rcases h with h | ⟨γ, w, hγ, hγne, hw, hwv⟩
      · exact hbad0.2 h
      · refine hEC' ⟨γ, w, (hHid' γ).mpr ⟨hγ, hγne⟩, valC_mono P hcc hw, Or.inl ?_⟩
        rw [hwv]; exact hvK'
    · refine hEC' ⟨β₀, v₀, (hHid' β₀).mpr ⟨hβ₀, h0⟩, hv₀', ?_⟩
      rcases h with h | ⟨γ, w, hγ, hγne, hw, hwv⟩
      · exact Or.inl (hK' _ h)
      · by_cases hγ0 : γ = β ++ [B]
        · subst hγ0
          obtain rfl := valC_eq_of_le hcc hw hvv
          exact Or.inl (hwv ▸ hvK')
        · exact Or.inr ⟨γ, w, (hHid' γ).mpr ⟨hγ, hγ0⟩, hγne, valC_mono P hcc hw, hwv⟩
  have hC := hcond hbad0.1 hEC
  -- the new path was not rooted
  have hnotV : β ++ [B] ∉ vPaths cs.sim := by
    intro h
    obtain ⟨v₀, hv₀⟩ := exists_chain_of_mem_vPaths h
    obtain ⟨q, hq, B', h1, h2⟩ := hS.chainEdge _ hv₀ hne
    obtain ⟨h3, h4⟩ := List.append_inj' h1 rfl
    obtain rfl : B = B' := List.singleton_inj.mp h4
    have := chain_eq_of_path hS hC.vis hq hsβ h3.symm
    subst this
    exact (fwdLookup_eq_none_iff.mp hy) (List.mem_map.mpr ⟨_, h2, by simp [hxB]⟩)
  have hcap : ∀ p ∈ cs.sim.chains, p.1.2 ∈ knownC iv cs.sim := fun p hp ↦
    chain_cap_mem_knownC P iv hS hp
  have hvis : VisCons cs'.sim :=
    visCons_cons hC.vis (fwdLookup_eq_none_iff.mp hy)
      (fun h ↦ by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
        exact hbad0.2 (snd_mem_knownC iv he))
      (Or.inr ⟨β ++ [B], rfl, fun h ↦ by
        obtain ⟨p, hp, hpv⟩ := List.mem_map.mp h
        exact hbad0.2 (hpv ▸ hcap p hp)⟩)
      (Or.inl ⟨s, β, B, List.mem_cons_of_mem _ hsβ, List.mem_cons_self, hxB.symm⟩)
      (fun e he p hp hpo ↦ by
        rcases List.mem_cons.mp hp with rfl | hp
        · exact fun h ↦ hbad0.2 (h ▸ fst_mem_knownC iv he)
        · exact absurd hp hpo)
  -- the hidden edges after are the hidden edges before, but for the new path
  have hHE : ∀ e, HiddenEdge P iv cs'.vis c' e ↔
      HiddenEdge P iv cs.vis c e ∧ e ≠ (x, v) := by
    intro e
    constructor
    · intro he
      refine ⟨hiddenEdge_back hS hcc (fun δ hδ ↦ ((hHid' δ).mp hδ).1) he, ?_⟩
      rintro rfl
      obtain ⟨γ, G, t, w, hδ, ht, hw, hxe⟩ := he
      simp only [Prod.mk.injEq] at hxe
      obtain ⟨hxe, rfl⟩ := hxe
      have hδ0 := (hHid' _).mp hδ
      obtain ⟨t₀, ht₀⟩ := svC_known hS (knownPath_init hS (Or.inr hδ0.1))
      obtain rfl := svC_eq_of_le hcc ht₀ ht
      have hk : KnownPath P cs (γ ++ [G]) := Or.inr hδ0.1
      have htx : t₀.2 = x.2 := by rw [hxe]; rfl
      have := sv_cap_inj hS hC.vis hEC (knownPath_init hS hk) (Or.inl (List.mem_map.mpr
        ⟨_, hsβ, rfl⟩)) ht₀ (hS.chainVal _ hsβ) (by simp only; rw [htx, hsx])
      subst this
      rw [hS.chainVal _ hsβ] at ht₀
      obtain rfl := Option.some.inj ht₀
      obtain rfl := absorb_injective s (hxe.symm.trans hxB.symm)
      exact hδ0.2 rfl
    · rintro ⟨he, hne'⟩
      obtain ⟨γ, G, t, w, hδ, ht, hw, rfl⟩ := he
      refine ⟨γ, G, t, w, (hHid' _).mpr ⟨hδ, ?_⟩, svC_mono hcc ht, valC_mono P hcc hw, rfl⟩
      intro hδB
      obtain ⟨rfl, hGB⟩ := List.append_inj' hδB rfl
      obtain rfl : G = B := List.singleton_inj.mp hGB
      rw [hS.chainVal _ hsβ] at ht
      obtain rfl := Option.some.inj ht
      obtain rfl := valC_eq_of_le hcc hw hvv
      exact hne' (by rw [hxB])
  -- the two cases: the new path is hidden, or new
  have hxv_eq : ∀ w, HiddenEdge P iv cs.vis c (x, w) → Hidden P cs.vis (β ++ [B]) := by
    rintro w ⟨γ, G, t, w', hδ, ht, hw, hxe⟩
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨hxe, rfl⟩ := hxe
    obtain ⟨t₀, ht₀⟩ := svC_known hS (knownPath_init hS (Or.inr hδ))
    rw [ht] at ht₀
    obtain rfl := Option.some.inj ht₀
    have htx : t.2 = x.2 := by rw [hxe]; rfl
    have := sv_cap_inj hS hC.vis hEC (knownPath_init hS (Or.inr hδ)) (Or.inl (List.mem_map.mpr
      ⟨_, hsβ, rfl⟩)) ht (hS.chainVal _ hsβ) (by simp only; rw [htx, hsx])
    subst this
    have hts : t = s := Option.some.inj (ht.symm.trans (hS.chainVal _ hsβ))
    have hGB : absorb s G = absorb s B := by rw [hxB, ← hts]; exact hxe.symm
    rw [absorb_injective s hGB] at hδ
    exact hδ
  by_cases hH : β ++ [B] ∈ hPaths P cs.hashed
  · -- the distinguisher reaches a node of a hashed path: the full view already holds it
    have hHB : Hidden P cs.vis (β ++ [B]) := ⟨hH, hnotV⟩
    obtain ⟨v₀, hv₀⟩ := Option.ne_none_iff_exists'.mp (hS.hCached _ hH)
    obtain rfl := valC_eq_of_le hcc hv₀ hvv
    have hG : GEdge P iv cs c (x, v₀) :=
      Or.inr ⟨β, B, s, v₀, hHB, hS.chainVal _ hsβ, hv₀, by rw [hxB]⟩
    have hA := fwdLookup_all hS hC hEC hG
    have hall' : cs'.all = cs.all := by simp [hcs', fwdOut, hA]
    refine ⟨hvis, fun e ↦ ?_, ?_⟩
    · show e ∈ cs'.all ↔ e ∈ cs'.sim.edges ∨ HiddenEdge P iv cs'.vis c' e
      rw [hall', hHE e, hC.allMem e, hsim]
      simp only [GEdge, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · by_cases hex : e = (x, v₀)
          · exact Or.inl (Or.inl hex)
          · exact Or.inr ⟨h, hex⟩
      · rintro ((rfl | h) | ⟨h, -⟩)
        · exact hG
        · exact Or.inl h
        · exact Or.inr h
    · simp [hcs', fwdOut, hA, hC.noDiff]
  · -- a new path: neither view holds the node
    have hnoG : ∀ y, ¬ GEdge P iv cs c (x, y) := by
      rintro y (h | h)
      · exact (fwdLookup_eq_none_iff.mp hy) (List.mem_map.mpr ⟨(x, y), h, rfl⟩)
      · exact hH (hxv_eq y h).1
    have hA := fwdLookup_all_none hC hnoG
    have hU : usedPath P cs.sim.chains cs.hashed (β ++ [B]) = false := by
      simp only [usedPath, Bool.or_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false]
      refine ⟨hnotV, fun m hm hmem ↦ hH ?_⟩
      simp only [decide_eq_true_eq] at hmem
      exact List.mem_flatMap.mpr ⟨m, hm, hmem⟩
    have hall' : cs'.all = (x, v) :: cs.all := by simp [hcs', fwdOut, hA, hU]
    refine ⟨hvis, fun e ↦ ?_, ?_⟩
    · show e ∈ cs'.all ↔ e ∈ cs'.sim.edges ∨ HiddenEdge P iv cs'.vis c' e
      rw [hall', hHE e, hsim]
      simp only [List.mem_cons]
      rw [hC.allMem e]
      constructor
      · rintro (rfl | h)
        · exact Or.inl (Or.inl rfl)
        · rcases h with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨h, fun hex ↦ hH (hxv_eq v (hex ▸ h)).1⟩
      · rintro ((rfl | h) | ⟨h, -⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · simp [hcs', fwdOut, hA, hU, hC.noDiff]

omit u in
/-- **The forward step keeps the invariant.** -/
theorem inv_combFwd {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (hI : Inv P iv cs c)
    (x : SpState Dg E C)
    {z : ((SpState Dg E C × SpState Dg E C) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl
      ((combFwd P iv x).run cs)).run c)) : Inv P iv z.1.2 z.2 := by
  obtain ⟨u, r, hr, hz1⟩ := combFwd_support P iv x cs c hz
  rw [hz1]
  rcases visFwd_support P x u cs.sim c hr with ⟨y, hy, hrz⟩ | ⟨s, β, hy, hch, hv, hrz⟩ |
      ⟨hy, hch, hrz⟩
  · simp only [Prod.mk.injEq] at hrz
    obtain ⟨rfl, hc⟩ := hrz
    rw [hc]
    exact inv_fwd_recorded u hI hy
  · simp only at hrz hv
    rw [hrz]
    exact inv_fwd_rooted u hI hy hch hv
  · simp only [Prod.mk.injEq] at hrz
    obtain ⟨rfl, hc⟩ := hrz
    rw [hc]
    exact inv_fwd_unrooted u hI hy hch

/-- **The inverse step keeps the invariant.** -/
theorem inv_invOut {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (hI : Inv P iv cs c)
    (y : SpState Dg E C) : Inv P iv (invOut iv cs y u).2 c := by
  obtain ⟨hS, hcond⟩ := hI
  rcases hx : inverseLookup cs.sim.edges y with _ | x
  · -- a fresh inverse query
    set cs' := (invOut iv cs y u).2 with hcs'
    have hsim : cs'.sim = ⟨(u, y) :: cs.sim.edges, cs.sim.chains⟩ := by
      simp [hcs', invOut, visInv, hx]
    have hhashed : cs'.hashed = cs.hashed := rfl
    have hHid : ∀ β, Hidden P cs'.vis β ↔ Hidden P cs.vis β := by
      intro β; simp [Hidden, CState.vis, hsim, hhashed, vPaths]
    have hS' : Struct P iv cs' c := by
      refine ⟨?_, ?_, fun p hp hne ↦ ?_, hhashed ▸ hS.hCached⟩
      · rw [hsim]; exact hS.root
      · rw [hsim]; exact hS.chainVal
      · rw [hsim] at hp ⊢
        obtain ⟨q, hq, B, h1, h2⟩ := hS.chainEdge p hp hne
        exact ⟨q, hq, B, h1, List.mem_cons_of_mem _ h2⟩
    refine ⟨hS', fun hbad hEC' ↦ ?_⟩
    have hbad0 : cs.bad = false ∧ u.2 ∉ knownC iv cs.sim := by
      simpa [hcs', invOut, hx] using hbad
    have hK' : ∀ k, k ∈ knownC iv cs.sim → k ∈ knownC iv cs'.sim := fun k hk ↦ by
      rw [hsim]; exact (mem_knownC_cons iv).mpr (Or.inl hk)
    have hEC : ¬ EC P iv cs.vis c := by
      rintro ⟨β, v, hβ, hv, h⟩
      refine hEC' ⟨β, v, (hHid β).mpr hβ, hv, ?_⟩
      rcases h with h | ⟨γ, w, hγ, hne, hw, hwv⟩
      · exact Or.inl (hK' _ h)
      · exact Or.inr ⟨γ, w, (hHid γ).mpr hγ, hne, hw, hwv⟩
    have hC := hcond hbad0.1 hEC
    have hnoG : ∀ x, ¬ GEdge P iv cs c (x, y) := by
      rintro x (h | ⟨β, B, s, v, hβ, hs, hv, hxy⟩)
      · exact (invLookup_eq_none_iff.mp hx) (List.mem_map.mpr ⟨(x, y), h, rfl⟩)
      · simp only [Prod.mk.injEq] at hxy
        obtain ⟨-, rfl⟩ := hxy
        refine hEC' ⟨β ++ [B], y, (hHid _).mpr hβ, hv, Or.inl ?_⟩
        show y.2 ∈ knownC iv cs'.sim
        rw [hsim]
        exact (mem_knownC_cons iv).mpr (Or.inr (Or.inr rfl))
    have hA := invLookup_all_none hC hnoG
    have hall' : cs'.all = (u, y) :: cs.all := by simp [hcs', invOut, hA]
    have hcap : ∀ p ∈ cs.sim.chains, p.1.2 ∈ knownC iv cs.sim := fun p hp ↦
      chain_cap_mem_knownC P iv hS hp
    refine ⟨?_, fun e ↦ ?_, ?_⟩
    · rw [hsim]
      exact visCons_cons hC.vis
        (fun h ↦ by
          obtain ⟨e, he, he'⟩ := List.mem_map.mp h
          exact hbad0.2 (he' ▸ fst_mem_knownC iv he))
        (invLookup_eq_none_iff.mp hx) (Or.inl rfl)
        (Or.inr fun p hp h ↦ hbad0.2 (h ▸ hcap p hp)) (fun e _ p hp hpo ↦ absurd hp hpo)
    · show e ∈ cs'.all ↔ e ∈ cs'.sim.edges ∨ HiddenEdge P iv cs'.vis c e
      have hHE : ∀ e, HiddenEdge P iv cs'.vis c e ↔ HiddenEdge P iv cs.vis c e := by
        intro e
        simp only [HiddenEdge, hHid]
      rw [hall', hHE e, hsim]
      simp only [List.mem_cons]
      rw [hC.allMem e]
      simp only [GEdge]
      tauto
    · simp [hcs', invOut, hA, hx, hC.noDiff, visInv]
  · -- a recorded inverse query
    refine ⟨hS.of_eq (by simp [invOut, visInv, hx]) rfl, fun hbad hEC ↦ ?_⟩
    simp only [invOut, visInv, hx, Option.isNone_some, Bool.false_and, Bool.or_false]
      at hbad hEC ⊢
    have hC := hcond hbad hEC
    have hG : GEdge P iv cs c (x, y) := Or.inl (mem_of_invLookup_eq_some hx)
    have hA := invLookup_all hS hC hEC hG
    simp only [hA]
    refine ⟨hC.vis, hC.allMem, ?_⟩
    simp [hC.noDiff]

end Setting

end Common
