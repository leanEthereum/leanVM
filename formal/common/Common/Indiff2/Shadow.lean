module

public import Common.Indiff2.Bridge

@[expose] public section

/-!
# The two-oracle model: the shadow world

The world with `F` (`ideal1FImpl`) answers a direct call `F x` with the simulator. The shadow
world (`shadowImpl`) answers it with `F x` itself, recording the edge in the simulator's
bookkeeping as the simulator would. The two agree on every step except a direct call where they
*disagree* (`disagree`): at a recorded input whose answer is not `F`'s, or at a fresh input ending
a sponge path (where the simulator answers with `H`).

Both worlds carry a book (`Book`) of the fresh draws, the direct calls' answers, a violation flag
(a direct call breaking the duplex discipline) and a disagreement flag; they are identical until
the disagreement flag (`ideal1F_le_shadow`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

/-- **Augmenting** a stateful implementation with a book updated from each step's state and
answer. -/
def augImpl {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ B : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (upd : (t : ι) → σ → spec.Range t → B → B) :
    QueryImpl spec (StateT (σ × B) ProbComp) :=
  fun t ↦ StateT.mk fun s ↦ (fun z ↦ (z.1, (z.2, upd t s.1 z.1 s.2))) <$> (impl t).run s.1

theorem augImpl_run {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ B : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (upd : (t : ι) → σ → spec.Range t → B → B)
    (t : ι) (s : σ × B) :
    ((augImpl impl upd) t).run s =
      (fun z ↦ (z.1, (z.2, upd t s.1 z.1 s.2))) <$> (impl t).run s.1 := rfl

/-- Forgetting the book gives the implementation. -/
theorem augImpl_proj {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ B α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (upd : (t : ι) → σ → spec.Range t → B → B)
    (oa : OracleComp spec α) (s : σ × B) :
    Prod.map id Prod.fst <$> (simulateQ (augImpl impl upd) oa).run s =
      (simulateQ impl oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t s ↦ by
    simp [augImpl, Functor.map_map]) oa s

/-- Output form of `augImpl_proj`. -/
theorem prEvent_augImpl {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ B α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (upd : (t : ι) → σ → spec.Range t → B → B)
    (oa : OracleComp spec α) (s : σ) (b : B) (p : α → Prop) :
    Pr{let z ← (simulateQ (augImpl impl upd) oa).run (s, b)}[p z.1] =
      Pr{let a ← (simulateQ impl oa).run' s}[p a] := by
  have h := augImpl_proj impl upd oa (s, b)
  rw [StateT.run'_eq, ← h, prEvent_map, prEvent_map]
  rfl

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-! ## The shadow world -/

/-- **The shadow world**: like the world with `F`, but a direct call `F x` is answered by `F`,
recording the edge as the simulator would. -/
noncomputable def shadowImpl : QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
  | .inr (.inl m) => liftM (hQuery (Msg := Msg) (Dg := Dg) (E := E) (C := C) m)
  | .inr (.inr (.inl q)) => simulator2 P q
  | .inr (.inr (.inr x)) => StateT.mk fun σ ↦ do
      let y ← fQuery (Msg := Msg) (Dg := Dg) x
      pure (y, replayStep σ (.forward x, y))

theorem shadow_F_run (x : SpState Dg E C) (s : FState Msg Dg E C) :
    ((foldRO (shadowImpl P)) (.inr (.inr (.inr x)))).run s = fStep x s := by
  rw [foldRO_run]
  simp only [shadowImpl, StateT.run_mk, simulateQ_bind, StateT.run_bind, fQuery_run,
    simulateQ_pure, StateT.run_pure, fStep]
  simp

theorem shadow_eq_ideal1F (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain)
    (ht : ∀ x, t ≠ .inr (.inr (.inr x))) :
    (foldRO (shadowImpl P)) t = (foldRO (ideal1FImpl P)) t := by
  rcases t with n | m | q | x
  · rfl
  · rfl
  · rfl
  · exact absurd rfl (ht x)

/-! ## The book -/

/-- The book: the fresh draws (`dF`: forward answers and `F`'s answers; `dI`: inverse answers),
the answers of the direct calls (`hist`, newest first), the violation flag and the
disagreement flag. -/
structure Book (St : Type) where
  dF : List St
  dI : List St
  hist : List St
  viol : Bool
  flag : Bool

/-- The empty book. -/
def Book.init {St : Type} : Book St := ⟨[], [], [], false, false⟩

/-- A fresh forward query ends a sponge path: its path pads a message. -/
def rootedFinal (σ : SimState Dg E C) (x : SpState Dg E C) : Bool :=
  match chainOf σ.chains x with
  | some (r, β) => (P.unpad (β ++ [blockTo r x])).isSome
  | none => false

/-- The world with `F` and the shadow world **disagree** on a direct call `F x`: at a recorded
input whose answer is not `F`'s, or at a fresh input ending a sponge path or with `F` known. -/
def disagree (s : FState Msg Dg E C) (x : SpState Dg E C) : Bool :=
  match forwardLookup s.1.edges x with
  | some y => decide (s.2 (.inr x) ≠ some y)
  | none => rootedFinal P s.1 x || (s.2 (.inr x)).isSome

instance (NF : (Dg × E) → Prop) [DecidablePred NF] (hist : List (SpState Dg E C))
    (x : SpState Dg E C) : Decidable (Admissible iv NF hist x) := by
  unfold Admissible; infer_instance

/-- The book's update by a step. -/
def bookUpd (NF : (Dg × E) → Prop) [DecidablePred NF] :
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) → FState Msg Dg E C →
      (dSpec2 Msg Dg (SpState Dg E C)).Range t → Book (SpState Dg E C) → Book (SpState Dg E C)
  | .inl _, _, _, b => b
  | .inr (.inl _), _, _, b => b
  | .inr (.inr (.inl (.forward x))), s, a, b =>
      if forwardLookup s.1.edges x = none ∧ (rootedFinal P s.1 x = true ∨ s.2 (.inr x) = none) then
        { b with dF := a :: b.dF } else b
  | .inr (.inr (.inl (.inverse y))), s, a, b =>
      if inverseLookup s.1.edges y = none then { b with dI := a :: b.dI } else b
  | .inr (.inr (.inr x)), s, a, b =>
      { dF := if s.2 (.inr x) = none then a :: b.dF else b.dF
        dI := b.dI
        hist := a :: b.hist
        viol := b.viol || !decide (Admissible iv NF b.hist x)
        flag := b.flag || disagree P s x }

/-- The world with `F`, with the book. -/
noncomputable def aug1 (NF : (Dg × E) → Prop) [DecidablePred NF] :
    QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
      (StateT (FState Msg Dg E C × Book (SpState Dg E C)) ProbComp) :=
  augImpl (foldRO (ideal1FImpl P)) (bookUpd P iv NF)

/-- The shadow world, with the book. -/
noncomputable def aug2 (NF : (Dg × E) → Prop) [DecidablePred NF] :
    QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
      (StateT (FState Msg Dg E C × Book (SpState Dg E C)) ProbComp) :=
  augImpl (foldRO (shadowImpl P)) (bookUpd P iv NF)

/-! ## Identical until disagreement -/

/-- Where the worlds agree, the simulator's forward step is the direct call. -/
theorem fwdStep2_eq_fStep (x : SpState Dg E C) (s : FState Msg Dg E C)
    (h : disagree P s x = false) : fwdStep2 P x s = fStep x s := by
  obtain ⟨σ, c⟩ := s
  simp only [disagree] at h
  simp only [fwdStep2]
  rcases hy : forwardLookup σ.edges x with _ | y
  · simp only [hy, Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      rootedFinal] at h
    obtain ⟨h1, -⟩ := h
    simp only
    rcases hch : chainOf σ.chains x with _ | ⟨r, β⟩
    · rfl
    · simp only [hch, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h1
      simp only [h1]
  · simp only [hy, decide_eq_false_iff_not, not_not] at h
    simp only [fStep, roStep_of_some h, map_pure, replayStep, hy]

theorem bookUpd_flag (NF : (Dg × E) → Prop) [DecidablePred NF]
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (s : FState Msg Dg E C) (a)
    (b : Book (SpState Dg E C)) (hb : b.flag = true) : (bookUpd P iv NF t s a b).flag = true := by
  rcases t with n | m | (x | y) | x
  · exact hb
  · exact hb
  · simp only [bookUpd]; split_ifs <;> exact hb
  · simp only [bookUpd]; split_ifs <;> exact hb
  · simp [bookUpd, hb]

theorem aug_flag_mono (NF : (Dg × E) → Prop) [DecidablePred NF]
    (impl : QueryImpl (dSpec2 Msg Dg (SpState Dg E C)) (StateT (FState Msg Dg E C) ProbComp))
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (s : FState Msg Dg E C × Book (SpState Dg E C))
    (hs : s.2.flag = true) :
    ∀ z ∈ support (((augImpl impl (bookUpd P iv NF)) t).run s), z.2.2.flag = true := by
  intro z hz
  rw [augImpl_run, support_map] at hz
  obtain ⟨w, -, rfl⟩ := hz
  exact bookUpd_flag P iv NF t _ _ _ hs

/-- **The worlds agree on every step from a state without disagreement.** -/
theorem aug_agree (NF : (Dg × E) → Prop) [DecidablePred NF]
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (s : FState Msg Dg E C × Book (SpState Dg E C))
    (q : (dSpec2 Msg Dg (SpState Dg E C)).Range t × (FState Msg Dg E C × Book (SpState Dg E C)) →
      Prop) :
    Pr{let z ← ((aug1 P iv NF) t).run s}[q z ∧ ¬z.2.2.flag = true] =
      Pr{let z ← ((aug2 P iv NF) t).run s}[q z ∧ ¬z.2.2.flag = true] := by
  by_cases ht : ∃ x, t = .inr (.inr (.inr x))
  · obtain ⟨x, rfl⟩ := ht
    simp only [aug1, aug2, augImpl_run, ideal1F_F_run, shadow_F_run]
    cases hd : disagree P s.1 x
    · rw [fwdStep2_eq_fStep P x s.1 hd]
    · rw [prEvent_map, prEvent_map,
        prEvent_eq_zero_of_forall_mem_support _ _ fun z _ h ↦ h.2 (by simp [bookUpd, hd]),
        prEvent_eq_zero_of_forall_mem_support _ _ fun z _ h ↦ h.2 (by simp [bookUpd, hd])]
  · push Not at ht
    simp only [aug1, aug2, augImpl_run, shadow_eq_ideal1F P t ht]

/-- **The world with `F` and the shadow world are identical until disagreement.** -/
theorem ideal1F_le_shadow (NF : (Dg × E) → Prop) [DecidablePred NF] {α : Type}
    (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) (p : α → Prop) :
    Pr{let a ← (simulateQ (foldRO (ideal1FImpl P)) D).run' (SimState.init iv, ∅)}[p a] ≤
        Pr{let a ← (simulateQ (foldRO (shadowImpl P)) D).run' (SimState.init iv, ∅)}[p a] +
          Pr{let z ← ((simulateQ (aug2 P iv NF) D).run
            ((SimState.init iv, ∅), Book.init))}[z.2.2.flag = true] ∧
      Pr{let a ← (simulateQ (foldRO (shadowImpl P)) D).run' (SimState.init iv, ∅)}[p a] ≤
        Pr{let a ← (simulateQ (foldRO (ideal1FImpl P)) D).run' (SimState.init iv, ∅)}[p a] +
          Pr{let z ← ((simulateQ (aug2 P iv NF) D).run
            ((SimState.init iv, ∅), Book.init))}[z.2.2.flag = true] := by
  let s₀ : FState Msg Dg E C × Book (SpState Dg E C) := ((SimState.init iv, ∅), Book.init)
  have hagree := fun t s (_ : ¬ s.2.flag = true) q ↦ aug_agree P iv NF t s q
  have hm1 := fun t s hs ↦ aug_flag_mono P iv NF (foldRO (ideal1FImpl P)) t s hs
  have hm2 := fun t s hs ↦ aug_flag_mono P iv NF (foldRO (shadowImpl P)) t s hs
  have h1 := prEvent_run_le_add_bad (aug1 P iv NF) (aug2 P iv NF) (fun s ↦ s.2.flag = true)
    hagree hm1 hm2 D s₀ p
  have h2 := prEvent_run_le_add_bad (aug2 P iv NF) (aug1 P iv NF) (fun s ↦ s.2.flag = true)
    (fun t s hs q ↦ (hagree t s hs q).symm) hm2 hm1 D s₀ p
  have heq := prEvent_run_bad_eq (aug1 P iv NF) (aug2 P iv NF) (fun s ↦ s.2.flag = true)
    hagree hm1 hm2 D s₀
  rw [heq] at h2
  have e1 : Pr{let z ← (simulateQ (aug1 P iv NF) D).run s₀}[p z.1] =
      Pr{let a ← (simulateQ (foldRO (ideal1FImpl P)) D).run' (SimState.init iv, ∅)}[p a] :=
    prEvent_augImpl _ _ D _ _ p
  have e2 : Pr{let z ← (simulateQ (aug2 P iv NF) D).run s₀}[p z.1] =
      Pr{let a ← (simulateQ (foldRO (shadowImpl P)) D).run' (SimState.init iv, ∅)}[p a] :=
    prEvent_augImpl _ _ D _ _ p
  rw [e1, e2] at h1 h2
  exact ⟨h1, h2⟩

end Setting

end Common
