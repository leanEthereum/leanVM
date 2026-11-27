module

public import XmssSecurity.State
public import EthLib.Cryptography.Proofs.Hash.Keccak.OneBlock
public import EthLib.Cryptography.Proofs.SufCma.Permutation

/-!
# leanVM's random permutation is EthLib's

The statement's model (`Common.runWithRandomPermutation`) samples `π` lazily over leanVM's Keccak
state, EthLib's (`EthLib.Cryptography.SufCma.randomPermutationModel`) over its own. A computation
over EthLib's oracles, its queries answered by leanVM's at the same lanes (`ethLibOracles`), runs
in leanVM's model with the law it has in EthLib's
(`runWithRandomPermutation_simulateQ_ethLibOracles`).
-/

@[expose] public section

namespace XmssSecurity

open OracleComp OracleSpec Common
open EthLib.Cryptography.LazyPermutation (PermSpec PermCache)
open EthLib.Cryptography.Hash.Keccak (State)

/-- EthLib's cache of leanVM's edges: both components carried to EthLib's layout. -/
def edgesToEthLib (E : PermutationEdges LeanVM.Semantics.KeccakState) : PermCache State :=
  E.map fun p => (stateEquiv p.1, stateEquiv p.2)

/-- A forward lookup in the carried edges is the carried lookup. -/
theorem lookup_edgesToEthLib (E : PermutationEdges LeanVM.Semantics.KeccakState)
    (x : LeanVM.Semantics.KeccakState) :
    (edgesToEthLib E).lookup (stateEquiv x) = (forwardLookup E x).map stateEquiv := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = x
    · subst h
      simp [edgesToEthLib, forwardLookup]
    · have hb : (stateEquiv x == stateEquiv a) = false :=
        beq_false_of_ne fun e => h (stateEquiv.injective e).symm
      simpa [edgesToEthLib, forwardLookup, List.lookup, h, hb] using ih

section Outside

open EthLib.Cryptography EthLib.Cryptography.LazyPermutation

variable {A : Type} [FinEnum A]

/-- The values outside a list, as `FinEnum` lists them, are as many as the subtype. -/
theorem length_filter_toList_eq_card (used : List A) :
    ((FinEnum.toList A).filter fun b => b ∉ used).length =
      Fintype.card {b // b ∉ used} := by
  classical
  rw [Fintype.card_subtype, ← List.toFinset_card_of_nodup ((FinEnum.nodup_toList).filter _)]
  congr 1
  ext b
  simp

/-- A draw outside a list never gives a value of the list. -/
theorem prEvent_uniformOutside_of_mem (used : List A) (d t : A) (h : ∃ y, y ∉ used)
    (ht : t ∈ used) : Pr{let y ← uniformOutside used d}[y = t] = 0 := by
  have hne : ((FinEnum.toList A).filter fun b => b ∉ used) ≠ [] := by
    obtain ⟨y, hy⟩ := h
    exact List.ne_nil_of_mem (a := y) (by simpa using hy)
  exact prEvent_uniformFrom_eq_of_notMem hne d (by simpa using ht)

/-- A draw outside a list gives each value outside it the same chance. -/
theorem prEvent_uniformOutside_of_notMem (used : List A) (d t : A) (ht : t ∉ used) :
    Pr{let y ← uniformOutside used d}[y = t] = (Fintype.card {b // b ∉ used} : ENNReal)⁻¹ := by
  rw [← length_filter_toList_eq_card]
  exact prEvent_uniformFrom_eq_of_mem ((FinEnum.nodup_toList).filter _) d (by simpa using ht)

end Outside

/-- A uniform draw outside `L`, carried over, never meets a carried value of `L`. -/
theorem prEvent_map_stateEquiv_subtype_of_mem (L : List LeanVM.Semantics.KeccakState)
    {inst : SampleableType {y // y ∉ L}} {t : State} (hm : stateEquiv.symm t ∈ L) :
    Pr{let a ← $ᵗ {y // y ∉ L}}[stateEquiv ↑a = t] = 0 := by
  refine (SampleableType.prEvent_uniformSample_eq_zero_iff _).2 fun a hq => a.2 ?_
  simpa [← hq] using hm

/-- A uniform draw outside `L`, carried over, is uniform on the carried complement. -/
theorem prEvent_map_stateEquiv_subtype_of_notMem (L : List LeanVM.Semantics.KeccakState)
    {inst : SampleableType {y // y ∉ L}} {t : State} (hm : stateEquiv.symm t ∉ L) :
    Pr{let a ← $ᵗ {y // y ∉ L}}[stateEquiv ↑a = t] =
      (Fintype.card {b // b ∉ L.map stateEquiv} : ENNReal)⁻¹ := by
  rw [prEvent_congr (p := fun a : {y // y ∉ L} => stateEquiv ↑a = t)
    (q := fun a => a = ⟨stateEquiv.symm t, hm⟩) _ fun a => by
      rw [Subtype.ext_iff, ← stateEquiv.eq_symm_apply]]
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  exact congrArg (fun n : ℕ => (n : ENNReal)⁻¹)
    (Fintype.card_congr (Equiv.subtypeEquiv stateEquiv fun a => by simp))

open EthLib.Cryptography EthLib.Cryptography.LazyPermutation in
/-- leanVM's draw outside a list, carried over, is EthLib's draw outside the carried list. -/
theorem map_stateEquiv_uniformAvoiding (L : List LeanVM.Semantics.KeccakState)
    (h : ∃ y, y ∉ L) (d : State) :
    (stateEquiv <$> uniformAvoiding L : ProbComp State) =ᵈ
      uniformOutside (L.map stateEquiv) d := by
  rw [uniformAvoiding, dite_eq_left_of_eq_true (eq_true h)]
  refine evalDistEq_of_forall_prEvent_eq_output fun t => ?_
  simp only [Functor.map_map]
  have ht : t ∈ L.map stateEquiv ↔ stateEquiv.symm t ∈ L := by
    simp only [List.mem_map]
    exact ⟨fun ⟨a, ha, e⟩ => by simpa [← e] using ha, fun h' => ⟨_, h', by simp⟩⟩
  by_cases hm : stateEquiv.symm t ∈ L
  · rw [prEvent_uniformOutside_of_mem _ d t (by
      obtain ⟨y, hy⟩ := h
      exact ⟨stateEquiv y, fun hh => hy (by simpa using hh)⟩) (ht.2 hm),
      prEvent_map_stateEquiv_subtype_of_mem L hm]
  · rw [prEvent_uniformOutside_of_notMem _ d t (fun hh => hm (ht.1 hh)),
      prEvent_map_stateEquiv_subtype_of_notMem L hm]
    simp only [Fintype.card_eq_nat_card]

/-- An inverse lookup in the carried edges is the carried lookup. -/
theorem lookup_swap_edgesToEthLib (E : PermutationEdges LeanVM.Semantics.KeccakState)
    (y : LeanVM.Semantics.KeccakState) :
    ((edgesToEthLib E).map Prod.swap).lookup (stateEquiv y) =
      (inverseLookup E y).map stateEquiv := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : b = y
    · subst h
      simp [edgesToEthLib, inverseLookup]
    · have hb : (stateEquiv y == stateEquiv b) = false :=
        beq_false_of_ne fun e => h (stateEquiv.injective e).symm
      simpa [edgesToEthLib, inverseLookup, List.lookup, h, hb] using ih

/-- Edges whose inputs are pairwise distinct, and whose outputs are. -/
def EdgesInjective (E : PermutationEdges LeanVM.Semantics.KeccakState) : Prop :=
  (E.map Prod.fst).Nodup ∧ (E.map Prod.snd).Nodup

/-- A forward lookup that finds nothing means the input is no recorded input. -/
theorem notMem_map_fst_of_forwardLookup_eq_none {E : PermutationEdges LeanVM.Semantics.KeccakState}
    {x : LeanVM.Semantics.KeccakState} (h : forwardLookup E x = none) : x ∉ E.map Prod.fst := by
  induction E with
  | nil => simp
  | cons p E ih =>
    obtain ⟨a, b⟩ := p
    by_cases hax : a = x
    · simp [forwardLookup, hax] at h
    · simp only [forwardLookup, hax, ite_false] at h
      simp [Ne.symm hax, ih h]

/-- An inverse lookup that finds nothing means the output is no recorded output. -/
theorem notMem_map_snd_of_inverseLookup_eq_none {E : PermutationEdges LeanVM.Semantics.KeccakState}
    {y : LeanVM.Semantics.KeccakState} (h : inverseLookup E y = none) : y ∉ E.map Prod.snd := by
  induction E with
  | nil => simp
  | cons p E ih =>
    obtain ⟨a, b⟩ := p
    by_cases hby : b = y
    · simp [inverseLookup, hby] at h
    · simp only [inverseLookup, hby, ite_false] at h
      simp [Ne.symm hby, ih h]

/-- A list of the length of a repeat-free list that misses a value misses some value. -/
theorem exists_notMem_of_nodup_of_notMem {L L' : List LeanVM.Semantics.KeccakState}
    (hL : L.Nodup) {x : LeanVM.Semantics.KeccakState} (hx : x ∉ L) (hlen : L'.length = L.length) :
    ∃ y, y ∉ L' := by
  by_contra hall
  have hall : ∀ y, y ∈ L' := fun y => by_contra fun hy => hall ⟨y, hy⟩
  have h1 : L.length < Fintype.card LeanVM.Semantics.KeccakState := by
    have := (List.nodup_cons.2 ⟨hx, hL⟩).length_le_card
    simpa using this
  have h2 : Fintype.card LeanVM.Semantics.KeccakState ≤ L'.length := by
    classical
    calc Fintype.card LeanVM.Semantics.KeccakState = (Finset.univ : Finset _).card :=
        Finset.card_univ.symm
      _ ≤ L'.toFinset.card := Finset.card_le_card fun y _ => List.mem_toFinset.2 (hall y)
      _ ≤ L'.length := List.toFinset_card_le _
  omega

/-- A draw outside a list that has room gives a value outside it. -/
theorem notMem_of_mem_support_uniformAvoiding {L : List LeanVM.Semantics.KeccakState}
    (h : ∃ y, y ∉ L) {m : ProbComp LeanVM.Semantics.KeccakState} (hm : m = uniformAvoiding L)
    {y : LeanVM.Semantics.KeccakState} (hy : y ∈ support m) : y ∉ L := by
  rw [hm, uniformAvoiding, dite_eq_left_of_eq_true (eq_true h)] at hy
  rw [support_map] at hy
  obtain ⟨a, -, rfl⟩ := hy
  exact a.2

/-- A fresh forward edge keeps the edges injective. -/
theorem edgesInjective_cons_forward {E : PermutationEdges LeanVM.Semantics.KeccakState}
    {x : LeanVM.Semantics.KeccakState} (hE : EdgesInjective E) (hx : x ∉ E.map Prod.fst)
    (hex : ∃ y, y ∉ E.map Prod.snd) {m₀ : ProbComp LeanVM.Semantics.KeccakState}
    (hm₀ : m₀ = uniformAvoiding (E.map Prod.snd))
    {m : ProbComp (LeanVM.Semantics.KeccakState × PermutationEdges LeanVM.Semantics.KeccakState)}
    (hm : m = (fun y => (y, (x, y) :: E)) <$> m₀) : ∀ z ∈ support m, EdgesInjective z.2 := by
  intro z hz
  rw [hm, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hy' := notMem_of_mem_support_uniformAvoiding hex hm₀ hy
  exact ⟨List.nodup_cons.2 ⟨hx, hE.1⟩, List.nodup_cons.2 ⟨hy', hE.2⟩⟩

open EthLib.Cryptography EthLib.Cryptography.LazyPermutation in
/-- A forward query of leanVM's permutation is EthLib's, on carried edges. -/
private theorem core_forward (x : LeanVM.Semantics.KeccakState)
    (E : PermutationEdges LeanVM.Semantics.KeccakState) (hE : EdgesInjective E) :
    (Prod.map stateEquiv edgesToEthLib <$> (lazyRandomPermutation (.forward x)).run E =ᵈ
      (lazyPermOracle (.inl (stateEquiv x)) : StateT (PermCache State) ProbComp _).run
        (edgesToEthLib E)) ∧
    ∀ {m : ProbComp (LeanVM.Semantics.KeccakState × PermutationEdges LeanVM.Semantics.KeccakState)},
      m = (lazyRandomPermutation (.forward x)).run E → ∀ z ∈ support m, EdgesInjective z.2 := by
  rw [lazyPermOracle_inl_run]
  cases hl : forwardLookup E x with
  | some y =>
    have hl' := lookup_eq_of_decidableEq (r := some (stateEquiv y)) (by
      rw [lookup_edgesToEthLib, hl]; rfl) (FinEnum.decEq (α := State))
    rw [hl']
    refine ⟨?_, ?_⟩
    · simp [lazyRandomPermutation, hl]
    · intro m hm z hz
      rw [hm] at hz
      simp [lazyRandomPermutation, hl] at hz
      exact hz ▸ hE
  | none =>
    have hl' := lookup_eq_of_decidableEq (r := none) (by
      have := lookup_edgesToEthLib E x
      rwa [hl] at this) (FinEnum.decEq (α := State))
    rw [hl']
    have hx := notMem_map_fst_of_forwardLookup_eq_none hl
    have hex : ∃ y, y ∉ E.map Prod.snd :=
      exists_notMem_of_nodup_of_notMem hE.1 hx (by simp)
    have hsnd : (edgesToEthLib E).map Prod.snd = (E.map Prod.snd).map stateEquiv := by
      simp [edgesToEthLib, List.map_map, Function.comp_def]
    have hrun : (lazyRandomPermutation (.forward x)).run E =
        (fun y => (y, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.snd) := by
      simp [lazyRandomPermutation, hl]
    refine ⟨?_, ?_⟩
    · rw [hrun, hsnd, Functor.map_map]
      have := (map_stateEquiv_uniformAvoiding (E.map Prod.snd) hex (stateEquiv x)).map
        (fun b => (b, (stateEquiv x, b) :: edgesToEthLib E))
      rw [Functor.map_map] at this
      exact this
    · intro m hm
      exact edgesInjective_cons_forward hE hx hex rfl (hm.trans hrun)

/-- A fresh inverse edge keeps the edges injective. -/
theorem edgesInjective_cons_inverse {E : PermutationEdges LeanVM.Semantics.KeccakState}
    {y : LeanVM.Semantics.KeccakState} (hE : EdgesInjective E) (hy : y ∉ E.map Prod.snd)
    (hex : ∃ x, x ∉ E.map Prod.fst) {m₀ : ProbComp LeanVM.Semantics.KeccakState}
    (hm₀ : m₀ = uniformAvoiding (E.map Prod.fst))
    {m : ProbComp (LeanVM.Semantics.KeccakState × PermutationEdges LeanVM.Semantics.KeccakState)}
    (hm : m = (fun x => (x, (x, y) :: E)) <$> m₀) : ∀ z ∈ support m, EdgesInjective z.2 := by
  intro z hz
  rw [hm, support_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hx' := notMem_of_mem_support_uniformAvoiding hex hm₀ hx
  exact ⟨List.nodup_cons.2 ⟨hx', hE.1⟩, List.nodup_cons.2 ⟨hy, hE.2⟩⟩

open EthLib.Cryptography EthLib.Cryptography.LazyPermutation in
/-- An inverse query of leanVM's permutation is EthLib's, on carried edges. -/
private theorem core_inverse (y : LeanVM.Semantics.KeccakState)
    (E : PermutationEdges LeanVM.Semantics.KeccakState) (hE : EdgesInjective E) :
    (Prod.map stateEquiv edgesToEthLib <$> (lazyRandomPermutation (.inverse y)).run E =ᵈ
      (lazyPermOracle (.inr (stateEquiv y)) : StateT (PermCache State) ProbComp _).run
        (edgesToEthLib E)) ∧
    ∀ {m : ProbComp (LeanVM.Semantics.KeccakState × PermutationEdges LeanVM.Semantics.KeccakState)},
      m = (lazyRandomPermutation (.inverse y)).run E → ∀ z ∈ support m, EdgesInjective z.2 := by
  rw [lazyPermOracle_inr_run]
  cases hl : inverseLookup E y with
  | some x =>
    have hl' := lookup_eq_of_decidableEq (r := some (stateEquiv x)) (by
      rw [lookup_swap_edgesToEthLib, hl]; rfl) (FinEnum.decEq (α := State))
    rw [hl']
    refine ⟨?_, ?_⟩
    · simp [lazyRandomPermutation, hl]
    · intro m hm z hz
      rw [hm] at hz
      simp [lazyRandomPermutation, hl] at hz
      exact hz ▸ hE
  | none =>
    have hl' := lookup_eq_of_decidableEq (r := none) (by
      have := lookup_swap_edgesToEthLib E y
      rwa [hl] at this) (FinEnum.decEq (α := State))
    rw [hl']
    have hy := notMem_map_snd_of_inverseLookup_eq_none hl
    have hex : ∃ x, x ∉ E.map Prod.fst :=
      exists_notMem_of_nodup_of_notMem hE.2 hy (by simp)
    have hfst : (edgesToEthLib E).map Prod.fst = (E.map Prod.fst).map stateEquiv := by
      simp [edgesToEthLib, List.map_map, Function.comp_def]
    have hrun : (lazyRandomPermutation (.inverse y)).run E =
        (fun x => (x, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.fst) := by
      simp [lazyRandomPermutation, hl]
    refine ⟨?_, ?_⟩
    · rw [hrun, hfst, Functor.map_map]
      have := (map_stateEquiv_uniformAvoiding (E.map Prod.fst) hex (stateEquiv y)).map
        (fun a => (a, (a, stateEquiv y) :: edgesToEthLib E))
      rw [Functor.map_map] at this
      exact this
    · intro m hm
      exact edgesInjective_cons_inverse hE hy hex rfl (hm.trans hrun)

/-- Two binds have the same law when the first steps and the continuations correspond. -/
private theorem bind_step {σ₁ σ₂ β γ : Type} (f : σ₁ → σ₂) (A : ProbComp (β × σ₁))
    (B : ProbComp (β × σ₂)) (M : β × σ₁ → ProbComp (γ × σ₁)) (N : β × σ₂ → ProbComp (γ × σ₂))
    (hAB : Prod.map id f <$> A =ᵈ B)
    (hMN : ∀ z ∈ support A, Prod.map id f <$> M z =ᵈ N (Prod.map id f z)) :
    Prod.map id f <$> (A >>= M) =ᵈ (B >>= N) := by
  rw [map_bind]
  refine EvalDistEq.trans (EvalDistEq.bind_congr_of_support _ hMN) ?_
  have := hAB.bind_left N
  rwa [bind_map_left] at this

open EthLib.Cryptography.LazyPermutation in
/-- A coin of the relabelled oracles is a coin of EthLib's, and keeps the edges. -/
private theorem step_coin (n : ℕ) (E : PermutationEdges LeanVM.Semantics.KeccakState) :
    (Prod.map id edgesToEthLib <$>
        (simulateQ lazyRandomPermutationOracles (ethLibOracles (Sum.inl n))).run E =ᵈ
      (lazyPermImpl (Sum.inl n) : StateT (PermCache State) ProbComp _).run (edgesToEthLib E)) ∧
    ∀ z ∈ support ((simulateQ lazyRandomPermutationOracles (ethLibOracles (Sum.inl n))).run E),
      z.2 = E := by
  simp [ethLibOracles, lazyRandomPermutationOracles]

/-- The relabelled forward oracle is leanVM's forward query, its answer carried over. -/
private theorem run_ethLibOracles_forward (a : State)
    (E : PermutationEdges LeanVM.Semantics.KeccakState) :
    (simulateQ lazyRandomPermutationOracles (ethLibOracles (Sum.inr (Sum.inl a)))).run E =
      (fun p => (stateEquiv p.1, p.2)) <$>
        (lazyRandomPermutation (.forward (stateEquiv.symm a))).run E := by
  simp [ethLibOracles, lazyRandomPermutationOracles, StateT.run_map]

/-- The relabelled inverse oracle is leanVM's inverse query, its answer carried over. -/
private theorem run_ethLibOracles_inverse (b : State)
    (E : PermutationEdges LeanVM.Semantics.KeccakState) :
    (simulateQ lazyRandomPermutationOracles (ethLibOracles (Sum.inr (Sum.inr b)))).run E =
      (fun p => (stateEquiv p.1, p.2)) <$>
        (lazyRandomPermutation (.inverse (stateEquiv.symm b))).run E := by
  simp [ethLibOracles, lazyRandomPermutationOracles, StateT.run_map]

open EthLib.Cryptography.LazyPermutation in
/-- A relabelled forward query is EthLib's, on carried edges, and keeps them injective. -/
private theorem step_forward (a : State) (E : PermutationEdges LeanVM.Semantics.KeccakState)
    (hE : EdgesInjective E) :
    (Prod.map id edgesToEthLib <$>
        (simulateQ lazyRandomPermutationOracles (ethLibOracles (Sum.inr (Sum.inl a)))).run E =ᵈ
      (lazyPermImpl (Sum.inr (Sum.inl a)) : StateT (PermCache State) ProbComp _).run
        (edgesToEthLib E)) ∧
    ∀ z ∈ support ((simulateQ lazyRandomPermutationOracles
      (ethLibOracles (Sum.inr (Sum.inl a)))).run E), EdgesInjective z.2 := by
  obtain ⟨h1, h2⟩ := core_forward (stateEquiv.symm a) E hE
  rw [Equiv.apply_symm_apply] at h1
  refine ⟨?_, ?_⟩
  · rw [run_ethLibOracles_forward, Functor.map_map]
    exact h1
  · intro z hz
    rw [run_ethLibOracles_forward, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact h2 rfl w hw

open EthLib.Cryptography.LazyPermutation in
/-- A relabelled inverse query is EthLib's, on carried edges, and keeps them injective. -/
private theorem step_inverse (b : State) (E : PermutationEdges LeanVM.Semantics.KeccakState)
    (hE : EdgesInjective E) :
    (Prod.map id edgesToEthLib <$>
        (simulateQ lazyRandomPermutationOracles (ethLibOracles (Sum.inr (Sum.inr b)))).run E =ᵈ
      (lazyPermImpl (Sum.inr (Sum.inr b)) : StateT (PermCache State) ProbComp _).run
        (edgesToEthLib E)) ∧
    ∀ z ∈ support ((simulateQ lazyRandomPermutationOracles
      (ethLibOracles (Sum.inr (Sum.inr b)))).run E), EdgesInjective z.2 := by
  obtain ⟨h1, h2⟩ := core_inverse (stateEquiv.symm b) E hE
  rw [Equiv.apply_symm_apply] at h1
  refine ⟨?_, ?_⟩
  · rw [run_ethLibOracles_inverse, Functor.map_map]
    exact h1
  · intro z hz
    rw [run_ethLibOracles_inverse, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact h2 rfl w hw

/-- From injective edges, the relabelled run is EthLib's lazy run on the carried edges. -/
private theorem key {α : Type} (oa : OracleComp (unifSpec + PermSpec State) α)
    (E : PermutationEdges LeanVM.Semantics.KeccakState) (hE : EdgesInjective E) :
    (Prod.map id edgesToEthLib <$>
      (simulateQ lazyRandomPermutationOracles (simulateQ ethLibOracles oa)).run E) =ᵈ
    (simulateQ EthLib.Cryptography.LazyPermutation.lazyPermImpl oa).run (edgesToEthLib E) := by
  induction oa using OracleComp.inductionOn generalizing E with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, OracleQuery.cont_query,
      OracleQuery.input_query, id_map]
    rcases t with n | a | b
    · obtain ⟨h1, h2⟩ := step_coin n E
      refine bind_step edgesToEthLib _ _ _ _ h1 fun z hz => ?_
      obtain ⟨u, s⟩ := z
      have hs : s = E := h2 (u, s) hz
      subst hs
      exact ih u s hE
    · obtain ⟨h1, h2⟩ := step_forward a E hE
      exact bind_step edgesToEthLib _ _ _ _ h1 fun z hz => ih z.1 z.2 (h2 z hz)
    · obtain ⟨h1, h2⟩ := step_inverse b E hE
      exact bind_step edgesToEthLib _ _ _ _ h1 fun z hz => ih z.1 z.2 (h2 z hz)

/-- **leanVM's random permutation is EthLib's.** A computation over EthLib's oracles, answered by
leanVM's, runs against leanVM's lazy permutation with the law of its run in EthLib's model. -/
theorem runWithRandomPermutation_simulateQ_ethLibOracles {α : Type} [MeasurableSpace α]
    (oa : OracleComp (unifSpec + PermSpec State) α) :
    evalDist (runWithRandomPermutation (simulateQ ethLibOracles oa)) =
      evalDist (EthLib.Cryptography.SufCma.runIn
        (EthLib.Cryptography.SufCma.randomPermutationModel State) oa) := by
  have h := (key oa [] ⟨List.nodup_nil, List.nodup_nil⟩).map Prod.fst
  rw [Functor.map_map] at h
  rw [EthLib.Cryptography.SufCma.runIn_randomPermutationModel]
  exact EvalDistEq.evalDist_eq h

end XmssSecurity

end
