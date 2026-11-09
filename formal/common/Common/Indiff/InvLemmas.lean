module

public import Common.Indiff.Inv

@[expose] public section

/-!
# Indifferentiability: consequences of the invariant

Without collisions, the states at the end of the rooted and hidden paths have distinct
capacities (`sv_cap_inj`), so distinct paths have distinct sponge nodes (`node_inj`), and the
edges the full view should hold form a partial bijection (`gEdge_fst_inj`, `gEdge_snd_inj`).
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

/-- A path the analysis keeps track of: rooted by the simulator, or hidden. -/
def KnownPath (cs : CState Dg E C Msg) (β : List (Dg × E)) : Prop :=
  β ∈ vPaths cs.sim ∨ Hidden P cs.vis β

variable {P iv} {cs : CState Dg E C Msg} {c : ACache Msg Dg E C}

omit [DecidableEq E] [DecidableEq C] [DecidableEq Msg] in
/-- Prefixes of paddings are nonempty. -/
theorem ne_nil_of_mem_prefixesOf {bs β : List (Dg × E)} (h : β ∈ prefixesOf bs) : β ≠ [] := by
  rw [mem_prefixesOf] at h
  obtain ⟨i, hi, rfl⟩ := h
  rcases bs with _ | ⟨b, bs⟩
  · simp at hi
  · simp

theorem ne_nil_of_mem_hPaths {L : List Msg} {β : List (Dg × E)} (h : β ∈ hPaths P L) :
    β ≠ [] := by
  simp only [hPaths, List.mem_flatMap] at h
  obtain ⟨m, -, h⟩ := h
  exact ne_nil_of_mem_prefixesOf h

/-- The state at the end of a nonempty path is its value. -/
theorem svC_of_ne_nil {β : List (Dg × E)} (h : β ≠ []) : svC P iv c β = valC P c β := by
  simp [svC, h]

/-- The state at the end of a hidden path is its value. -/
theorem svC_of_hidden {β : List (Dg × E)} (h : Hidden P cs.vis β) :
    svC P iv c β = valC P c β := svC_of_ne_nil (ne_nil_of_mem_hPaths h.1)

/-- The prefixes of hashed messages are closed under dropping the last block. -/
theorem hPaths_init {L : List Msg} {β : List (Dg × E)} {B : Dg × E}
    (h : β ++ [B] ∈ hPaths P L) : β = [] ∨ β ∈ hPaths P L := by
  simp only [hPaths, List.mem_flatMap] at h ⊢
  obtain ⟨m, hm, h⟩ := h
  rcases init_mem_prefixesOf h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨m, hm, h⟩

/-- A rooted path has its rooted state. -/
theorem exists_chain_of_mem_vPaths {β : List (Dg × E)} (h : β ∈ vPaths cs.sim) :
    ∃ s, (s, β) ∈ cs.sim.chains := by
  simp only [vPaths, List.mem_map] at h
  obtain ⟨⟨s, β'⟩, hp, rfl⟩ := h
  exact ⟨s, hp⟩

/-- The empty path is rooted. -/
theorem nil_mem_vPaths (hS : Struct P iv cs c) : ([] : List (Dg × E)) ∈ vPaths cs.sim :=
  List.mem_map.mpr ⟨(iv, []), hS.root, rfl⟩

/-- Known paths are closed under dropping the last block. -/
theorem knownPath_init (hS : Struct P iv cs c) {β : List (Dg × E)} {B : Dg × E}
    (h : KnownPath P cs (β ++ [B])) : KnownPath P cs β := by
  rcases h with h | h
  · obtain ⟨v, hv⟩ := exists_chain_of_mem_vPaths h
    obtain ⟨q, hq, B', hβ, -⟩ := hS.chainEdge _ hv (by simp)
    have : β = q.2 := (List.append_inj' hβ rfl).1
    exact Or.inl (List.mem_map.mpr ⟨q, hq, this.symm⟩)
  · rcases hPaths_init h.1 with h' | h'
    · subst h'; exact Or.inl (nil_mem_vPaths hS)
    · by_cases hv : β ∈ vPaths cs.sim
      · exact Or.inl hv
      · exact Or.inr ⟨h', hv⟩

/-- Rooted states with the same capacity are the same chain. -/
theorem chain_eq_of_cap (hC : VisCons cs.sim) {p q : SpState Dg E C × List (Dg × E)}
    (hp : p ∈ cs.sim.chains) (hq : q ∈ cs.sim.chains) (h : p.1.2 = q.1.2) : p = q :=
  List.inj_on_of_nodup_map hC.chainCap hp hq h

/-- Rooted states with the same path are the same chain. -/
theorem chain_eq_of_path (hS : Struct P iv cs c) (hC : VisCons cs.sim)
    {p q : SpState Dg E C × List (Dg × E)} (hp : p ∈ cs.sim.chains) (hq : q ∈ cs.sim.chains)
    (h : p.2 = q.2) : p = q := by
  have h1 := hS.chainVal p hp
  have h2 := hS.chainVal q hq
  rw [h] at h1
  rw [h1] at h2
  exact chain_eq_of_cap hC hp hq (by rw [Option.some.inj h2])

/-- **Capacities determine known paths.** Without collisions, the states at the end of distinct
known paths have distinct capacities. -/
theorem sv_cap_inj (hS : Struct P iv cs c) (hC : VisCons cs.sim) (hEC : ¬ EC P iv cs.vis c)
    {β γ : List (Dg × E)} {s s' : SpState Dg E C} (hβ : KnownPath P cs β)
    (hγ : KnownPath P cs γ) (hs : svC P iv c β = some s) (hs' : svC P iv c γ = some s')
    (h : s.2 = s'.2) : β = γ := by
  -- a hidden path's value has no visible capacity, nor another hidden value's capacity
  have hid_vis : ∀ {β γ : List (Dg × E)} {s s' : SpState Dg E C}, Hidden P cs.vis β →
      γ ∈ vPaths cs.sim → svC P iv c β = some s → svC P iv c γ = some s' → s.2 = s'.2 →
      False := by
    intro β γ s s' hβ hγ hs hs' h
    obtain ⟨t, ht⟩ := exists_chain_of_mem_vPaths hγ
    have := hS.chainVal _ ht
    rw [hs'] at this
    obtain rfl := Option.some.inj this
    refine hEC ⟨β, s, hβ, (svC_of_hidden hβ) ▸ hs, Or.inl ?_⟩
    rw [h]
    exact chain_cap_mem_knownC P iv hS ht
  rcases hβ with hβ | hβ <;> rcases hγ with hγ | hγ
  · obtain ⟨t, ht⟩ := exists_chain_of_mem_vPaths hβ
    obtain ⟨t', ht'⟩ := exists_chain_of_mem_vPaths hγ
    have e1 := hS.chainVal _ ht
    have e2 := hS.chainVal _ ht'
    simp only at e1 e2
    rw [hs] at e1; rw [hs'] at e2
    obtain rfl := Option.some.inj e1
    obtain rfl := Option.some.inj e2
    have := chain_eq_of_cap hC ht ht' h
    simp only [Prod.mk.injEq] at this
    exact this.2
  · exact (hid_vis hγ hβ hs' hs h.symm).elim
  · exact (hid_vis hβ hγ hs hs' h).elim
  · by_contra hne
    refine hEC ⟨β, s, hβ, (svC_of_hidden hβ) ▸ hs, Or.inr ⟨γ, s', hγ, Ne.symm hne,
      (svC_of_hidden hγ) ▸ hs', h.symm⟩⟩

/-- **Nodes determine known paths.** -/
theorem node_inj (hS : Struct P iv cs c) (hC : VisCons cs.sim) (hEC : ¬ EC P iv cs.vis c)
    {β γ : List (Dg × E)} {B B' : Dg × E} {s s' : SpState Dg E C}
    (hβ : KnownPath P cs (β ++ [B])) (hγ : KnownPath P cs (γ ++ [B']))
    (hs : svC P iv c β = some s) (hs' : svC P iv c γ = some s')
    (h : absorb s B = absorb s' B') : β = γ ∧ B = B' := by
  have hcap : s.2 = s'.2 := by
    have := congrArg Prod.snd h
    simpa using this
  have hβγ := sv_cap_inj hS hC hEC (knownPath_init hS hβ) (knownPath_init hS hγ) hs hs' hcap
  subst hβγ
  rw [hs] at hs'
  obtain rfl := Option.some.inj hs'
  exact ⟨rfl, absorb_injective s h⟩

/-- A rooted simulator edge is the edge into the value of its rooted path. -/
theorem rootedEdge_spec (hS : Struct P iv cs c) {e : SpState Dg E C × SpState Dg E C}
    (h : RootedEdge cs.sim e) :
    ∃ β B s, (β ++ [B]) ∈ vPaths cs.sim ∧ svC P iv c β = some s ∧
      valC P c (β ++ [B]) = some e.2 ∧ e.1 = absorb s B := by
  obtain ⟨s, β, B, hs, hv, he⟩ := h
  refine ⟨β, B, s, List.mem_map.mpr ⟨_, hv, rfl⟩, hS.chainVal _ hs, ?_, he⟩
  have := hS.chainVal _ hv
  simpa [svC] using this

/-- An unrooted simulator edge's input is no node of a known path. -/
theorem unrooted_ne_node (hS : Struct P iv cs c) (hEC : ¬ EC P iv cs.vis c)
    {e : SpState Dg E C × SpState Dg E C} (he : e ∈ cs.sim.edges)
    (hun : ∀ p ∈ cs.sim.chains, p.1.2 ≠ e.1.2) {β : List (Dg × E)} {B : Dg × E}
    {s : SpState Dg E C} (hβ : KnownPath P cs β) (hs : svC P iv c β = some s) :
    e.1 ≠ absorb s B := by
  intro hx
  have hcap : e.1.2 = s.2 := by rw [hx]; rfl
  rcases hβ with hβ | hβ
  · obtain ⟨t, ht⟩ := exists_chain_of_mem_vPaths hβ
    have := hS.chainVal _ ht
    rw [hs] at this
    obtain rfl := Option.some.inj this
    exact hun _ ht hcap.symm
  · refine hEC ⟨β, s, hβ, (svC_of_hidden hβ) ▸ hs, Or.inl ?_⟩
    rw [← hcap]
    exact fst_mem_knownC iv he

/-- A hidden value has no visible capacity. -/
theorem hidden_cap_notMem (hEC : ¬ EC P iv cs.vis c) {β : List (Dg × E)}
    {v : SpState Dg E C} (hβ : Hidden P cs.vis β) (hv : valC P c β = some v) :
    v.2 ∉ knownC iv cs.sim := fun h ↦ hEC ⟨β, v, hβ, hv, Or.inl h⟩

/-- The edges the full view should hold have distinct inputs. -/
theorem gEdge_fst_inj (hS : Struct P iv cs c) (hC : VisCons cs.sim) (hEC : ¬ EC P iv cs.vis c)
    {e e' : SpState Dg E C × SpState Dg E C} (he : GEdge P iv cs c e)
    (he' : GEdge P iv cs c e') (h : e.1 = e'.1) : e = e' := by
  -- every edge is a visible edge or the edge into a known path's value
  have node_eq : ∀ {β β' : List (Dg × E)} {B B' : Dg × E} {s s' v v' : SpState Dg E C},
      KnownPath P cs (β ++ [B]) → KnownPath P cs (β' ++ [B']) →
      svC P iv c β = some s → svC P iv c β' = some s' →
      valC P c (β ++ [B]) = some v → valC P c (β' ++ [B']) = some v' →
      absorb s B = absorb s' B' → v = v' := by
    intro β β' B B' s s' v v' hk hk' hs hs' hv hv' hx
    obtain ⟨rfl, rfl⟩ := node_inj hS hC hEC hk hk' hs hs' hx
    rw [hv] at hv'
    exact Option.some.inj hv'
  rcases he with he | ⟨β, B, s, v, hβ, hs, hv, rfl⟩ <;>
    rcases he' with he' | ⟨β', B', s', v', hβ', hs', hv', rfl⟩
  · exact List.inj_on_of_nodup_map hC.vKeys he he' h
  · rcases hC.vClass e he with hr | hun
    · obtain ⟨γ, G, t, hγ, ht, hv₀, hx⟩ := rootedEdge_spec hS hr
      obtain ⟨rfl, rfl⟩ := node_inj hS hC hEC (Or.inl hγ) (Or.inr hβ') ht hs' (hx ▸ h)
      exact absurd hγ hβ'.2
    · exact absurd h (unrooted_ne_node hS hEC he hun (knownPath_init hS (Or.inr hβ')) hs')
  · rcases hC.vClass e' he' with hr | hun
    · obtain ⟨γ, G, t, hγ, ht, hv₀, hx⟩ := rootedEdge_spec hS hr
      obtain ⟨rfl, rfl⟩ := node_inj hS hC hEC (Or.inl hγ) (Or.inr hβ) ht hs (hx ▸ h.symm)
      exact absurd hγ hβ.2
    · exact absurd h.symm (unrooted_ne_node hS hEC he' hun (knownPath_init hS (Or.inr hβ)) hs)
  · obtain ⟨rfl, rfl⟩ := node_inj hS hC hEC (Or.inr hβ) (Or.inr hβ') hs hs' h
    rw [hs] at hs'
    obtain rfl := Option.some.inj hs'
    rw [hv] at hv'
    obtain rfl := Option.some.inj hv'
    rfl

/-- The edges the full view should hold have distinct outputs. -/
theorem gEdge_snd_inj (hS : Struct P iv cs c) (hC : VisCons cs.sim) (hEC : ¬ EC P iv cs.vis c)
    {e e' : SpState Dg E C × SpState Dg E C} (he : GEdge P iv cs c e)
    (he' : GEdge P iv cs c e') (h : e.2 = e'.2) : e = e' := by
  rcases he with he | ⟨β, B, s, v, hβ, hs, hv, rfl⟩ <;>
    rcases he' with he' | ⟨β', B', s', v', hβ', hs', hv', rfl⟩
  · exact List.inj_on_of_nodup_map hC.vVals he he' h
  · have hk := snd_mem_knownC iv he
    simp only at h
    rw [h] at hk
    exact absurd hk (hidden_cap_notMem hEC hβ' hv')
  · have hk := snd_mem_knownC iv he'
    simp only at h
    rw [← h] at hk
    exact absurd hk (hidden_cap_notMem hEC hβ hv)
  · simp only at h
    subst h
    have hp := sv_cap_inj hS hC hEC (Or.inr hβ) (Or.inr hβ')
      ((svC_of_hidden hβ).trans hv) ((svC_of_hidden hβ').trans hv') rfl
    obtain ⟨rfl, hBB⟩ := List.append_inj' hp rfl
    obtain rfl : B = B' := List.singleton_inj.mp hBB
    rw [hs] at hs'
    obtain rfl := Option.some.inj hs'
    rfl

end Setting

end Common
