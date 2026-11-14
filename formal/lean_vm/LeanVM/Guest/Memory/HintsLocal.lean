/-
  LeanVM.Guest.Memory.HintsLocal

  The soundness of the heap hint check (`Memory.HintsCheck`): on a valid, placed node every heap hint
  word is in the node's own data or loaded by its path, so a tree whose loads are in a region has its
  heap hints in it too.
-/

module

public import LeanVM.Guest.Memory.HintsIn
public import LeanVM.Guest.Value.FieldBits
public import LeanVM.Guest.Memory.SizeTotal

/-!
# Heap hints resting on the path

`quickR_sound`: a block passing the recursors' check passes `hintsOkL` and its callees the test.
`hintsOkL_sound`: on a path of a checked block, every hint atom rests on atoms of the path
(`Rests`). `hintAddrs_local`: on a valid, placed node with its `HeapBuf`s, every heap hint word is
in one of its `HeapBuf`s or loaded by its path. `Tree.HintsQ Q`: every node's heap hint words are
loaded by its path, in its own data or in `Q` (`NodeHints`); `hintsIn_of_hintsQ`: with its loads in
a region `R` and `Q` within its data and `R`, a tree has its heap hints in `R`; `hintsQ_of_closed`:
the valid, placed trees of a closed set of functions passing the check (`HintsClosed`) are
`HintsQ`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

theorem vEq_spec {a b : V} (h : vEq a b = true) : a = b := by
  simp only [vEq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2


/-! ## The recursors' checks -/

theorem atomNoHeap_sound {a : Atom} (h : atomNoHeap a = true) : atomHeapDest? a = none := by
  cases a with
  | hint x =>
    cases x with
    | witness _ d => cases d <;> first | rfl | exact absurd h Bool.false_ne_true
    | bits _ _ _ d => cases d <;> first | rfl | exact absurd h Bool.false_ne_true
    | bitsExp _ _ d => cases d <;> first | rfl | exact absurd h Bool.false_ne_true
    | digitsExp _ _ _ _ _ _ d => cases d <;> first | rfl | exact absurd h Bool.false_ne_true
    | windowsExp _ _ _ _ d => cases d <;> first | rfl | exact absurd h Bool.false_ne_true
    | _ => rfl
  | _ => rfl

mutual
theorem quickS_sound {p : String → Bool} : ∀ (s : Stmt), quickS p s = true →
    (∀ Γ post, hintsOkS Γ post s = true) ∧ ∀ c ∈ Stmt.callees s, p c = true
  | .atom a, h => by
      refine ⟨fun Γ post => ?_, fun c hc => by simp [Stmt.callees] at hc⟩
      simp only [hintsOkS, coverOk]
      rw [atomNoHeap_sound h]
  | .ite _ z n, h => by
      have h' : (quickR p z && quickR p n) = true := h
      simp only [Bool.and_eq_true] at h'
      have hz := quickR_sound z h'.1
      have hn := quickR_sound n h'.2
      refine ⟨fun Γ _ => ?_, fun c hc => ?_⟩
      · simp only [hintsOkS, Bool.and_eq_true]; exact ⟨hz.1 Γ, hn.1 Γ⟩
      · simp only [Stmt.callees, List.mem_append] at hc; exact hc.elim (hz.2 c) (hn.2 c)
  | .match_ _ arms, h => by
      have ha := quickA_sound arms h
      exact ⟨fun Γ _ => by simp only [hintsOkS]; exact ha.1 Γ, fun c hc => by
        simp only [Stmt.callees] at hc; exact ha.2 c hc⟩
  | .call f _ _, h => ⟨fun _ _ => rfl, fun c hc => by
      simp only [Stmt.callees, List.mem_singleton] at hc; subst hc; exact h⟩
  | .callIf _ f _, h => ⟨fun _ _ => rfl, fun c hc => by
      simp only [Stmt.callees, List.mem_singleton] at hc; subst hc; exact h⟩
  | .dispatch _ fs _ _, h => ⟨fun _ _ => rfl, fun c hc => by
      simp only [Stmt.callees] at hc; exact List.all_eq_true.mp h c hc⟩
  | .ret _, _ => ⟨fun _ _ => rfl, fun c hc => by simp [Stmt.callees] at hc⟩

theorem quickR_sound {p : String → Bool} : ∀ (ss : List Stmt), quickR p ss = true →
    (∀ Γ, hintsOkL Γ ss = true) ∧ ∀ c ∈ Stmt.blockCallees ss, p c = true
  | [], _ => ⟨fun _ => rfl, fun c hc => by simp [Stmt.blockCallees] at hc⟩
  | s :: ss, h => by
      have h' : (quickS p s && quickR p ss) = true := h
      simp only [Bool.and_eq_true] at h'
      have hs := quickS_sound s h'.1
      have hss := quickR_sound ss h'.2
      refine ⟨fun Γ => ?_, fun c hc => ?_⟩
      · simp only [hintsOkL, Bool.and_eq_true]; exact ⟨hs.1 Γ _, hss.1 _⟩
      · simp only [Stmt.blockCallees, List.mem_append] at hc; exact hc.elim (hs.2 c) (hss.2 c)

theorem quickA_sound {p : String → Bool} : ∀ (as : List (List Stmt)), quickA p as = true →
    (∀ Γ, hintsOkA Γ as = true) ∧ ∀ c ∈ Stmt.armsCallees as, p c = true
  | [], _ => ⟨fun _ => rfl, fun c hc => by simp [Stmt.armsCallees] at hc⟩
  | a :: as, h => by
      have h' : (quickR p a && quickA p as) = true := h
      simp only [Bool.and_eq_true] at h'
      have ha := quickR_sound a h'.1
      have has := quickA_sound as h'.2
      refine ⟨fun Γ => ?_, fun c hc => ?_⟩
      · simp only [hintsOkA, Bool.and_eq_true]; exact ⟨ha.1 Γ, has.1 Γ⟩
      · simp only [Stmt.armsCallees, List.mem_append] at hc; exact hc.elim (ha.2 c) (has.2 c)
end

mutual
theorem calleesS_sound {p : String → Bool} : ∀ (s : Stmt), calleesS p s = true →
    ∀ c ∈ Stmt.callees s, p c = true
  | .atom _, _, c, hc => by simp [Stmt.callees] at hc
  | .ite _ z n, h, c, hc => by
      have h' : (calleesR p z && calleesR p n) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [Stmt.callees, List.mem_append] at hc
      exact hc.elim (calleesR_sound z h'.1 c) (calleesR_sound n h'.2 c)
  | .match_ _ arms, h, c, hc => by
      simp only [Stmt.callees] at hc
      exact calleesA_sound arms h c hc
  | .call f _ _, h, c, hc => by
      simp only [Stmt.callees, List.mem_singleton] at hc
      subst hc; exact h
  | .callIf _ f _, h, c, hc => by
      simp only [Stmt.callees, List.mem_singleton] at hc
      subst hc; exact h
  | .dispatch _ fs _ _, h, c, hc => by
      simp only [Stmt.callees] at hc
      exact List.all_eq_true.mp h c hc
  | .ret _, _, c, hc => by simp [Stmt.callees] at hc

theorem calleesR_sound {p : String → Bool} : ∀ (ss : List Stmt), calleesR p ss = true →
    ∀ c ∈ Stmt.blockCallees ss, p c = true
  | [], _, c, hc => by simp [Stmt.blockCallees] at hc
  | s :: ss, h, c, hc => by
      have h' : (calleesS p s && calleesR p ss) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [Stmt.blockCallees, List.mem_append] at hc
      exact hc.elim (calleesS_sound s h'.1 c) (calleesR_sound ss h'.2 c)

theorem calleesA_sound {p : String → Bool} : ∀ (as : List (List Stmt)), calleesA p as = true →
    ∀ c ∈ Stmt.armsCallees as, p c = true
  | [], _, c, hc => by simp [Stmt.armsCallees] at hc
  | a :: as, h, c, hc => by
      have h' : (calleesR p a && calleesA p as) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [Stmt.armsCallees, List.mem_append] at hc
      exact hc.elim (calleesR_sound a h'.1 c) (calleesA_sound as h'.2 c)
end

theorem quickR_append (p : String → Bool) (l l' : List Stmt) :
    quickR p (l ++ l') = (quickR p l && quickR p l') := by
  induction l with
  | nil => rfl
  | cons s l ih =>
      show (quickS p s && quickR p (l ++ l')) = ((quickS p s && quickR p l) && quickR p l')
      rw [ih, Bool.and_assoc]

theorem calleesR_append (p : String → Bool) (l l' : List Stmt) :
    calleesR p (l ++ l') = (calleesR p l && calleesR p l') := by
  induction l with
  | nil => rfl
  | cons s l ih =>
      show (calleesS p s && calleesR p (l ++ l')) = ((calleesS p s && calleesR p l) && calleesR p l')
      rw [ih, Bool.and_assoc]

/-! ## Paths -/

section Walk

variable {σ : Val}

/-- `Q`'s atoms are events of `E`. -/
def AtomsIn (Q : List Atom) (E : List Ev) : Prop := ∀ a ∈ Q, Ev.atom a ∈ E

theorem out_pre_evs (es : List Ev) : ∀ {o : Out}, o ≠ .stuck → (o.pre es).evs = es ++ o.evs
  | .fall _, _ => rfl
  | .ret _ _, _ => rfl
  | .stuck, h => absurd rfl h

theorem out_pre_stuck (es : List Ev) : ∀ {o : Out}, o.pre es = .stuck → o = .stuck
  | .fall _, h => by cases h
  | .ret _ _, h => by cases h
  | .stuck, _ => rfl

theorem out_seq_fall {es : List Ev} {k : Out} : (Out.fall es).seq k = k.pre es := rfl

/-- The events of a statement then a block: the statement's, then the block's if it falls through. -/
theorem walk_cons_evs (s : Stmt) (ss : List Stmt) {e : Ev} (he : e ∈ (walk σ (s :: ss)).evs) :
    e ∈ (walk1 σ s).evs ∨ ((∃ es, walk1 σ s = .fall es) ∧ e ∈ (walk σ ss).evs) := by
  rw [walk] at he
  rcases h1 : walk1 σ s with es | ⟨es, vs⟩ | _ <;> rw [h1] at he
  · rw [out_seq_fall] at he
    by_cases hs : walk σ ss = .stuck
    · rw [hs] at he; exact (List.not_mem_nil he).elim
    · rw [out_pre_evs _ hs, List.mem_append] at he
      exact he.imp id fun h => ⟨⟨es, rfl⟩, h⟩
  · exact Or.inl he
  · exact (List.not_mem_nil he).elim

theorem walk_cons_sub {s : Stmt} {ss : List Stmt} {E : List Ev}
    (hE : ∀ e ∈ (walk σ (s :: ss)).evs, e ∈ E) (hf : ∃ es, walk1 σ s = .fall es) :
    ∀ e ∈ (walk σ ss).evs, e ∈ E := by
  obtain ⟨es, h1⟩ := hf
  intro e he
  apply hE
  rw [walk, h1, out_seq_fall]
  have hs : walk σ ss ≠ .stuck := by intro hs; rw [hs] at he; exact List.not_mem_nil he
  rw [out_pre_evs _ hs]
  exact List.mem_append_right _ he

/-- **The run after a statement is on the path** when the block's path goes on. -/
theorem runAtoms_mem : ∀ (ss : List Stmt), walk σ ss ≠ .stuck → AtomsIn (runAtoms ss) (walk σ ss).evs
  | [], _ => fun _ h => (List.not_mem_nil h).elim
  | .atom a :: ss, hs => by
      have hs' : walk σ ss ≠ .stuck := fun h => hs (by rw [walk, walk1, out_seq_fall, h]; rfl)
      have hev : (walk σ (.atom a :: ss)).evs = .atom a :: (walk σ ss).evs := by
        rw [walk, walk1, out_seq_fall, out_pre_evs _ hs']; rfl
      intro q hq
      rw [hev]
      simp only [runAtoms] at hq
      split at hq
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (runAtoms_mem ss hs' q hq)
      · exact List.mem_cons_of_mem _ (runAtoms_mem ss hs' q hq)
  | .call f args rets :: ss, hs => by
      have hs' : walk σ ss ≠ .stuck := fun h => hs (by rw [walk, walk1, out_seq_fall, h]; rfl)
      intro q hq
      rw [walk, walk1, out_seq_fall, out_pre_evs _ hs']
      exact List.mem_append_right _ (runAtoms_mem ss hs' q hq)
  | .callIf c f args :: ss, hs => by
      have hs' : walk σ ss ≠ .stuck := fun h => hs (by rw [walk, walk1, out_seq_fall, h]; rfl)
      intro q hq
      rw [walk, walk1, out_seq_fall, out_pre_evs _ hs']
      exact List.mem_append_right _ (runAtoms_mem ss hs' q hq)
  | .ite .. :: _, _ => fun _ h => (List.not_mem_nil h).elim
  | .match_ .. :: _, _ => fun _ h => (List.not_mem_nil h).elim
  | .dispatch .. :: _, _ => fun _ h => (List.not_mem_nil h).elim
  | .ret _ :: _, _ => fun _ h => (List.not_mem_nil h).elim

theorem hintsOkA_mem {Γ : List Atom} : ∀ {arms : List (List Stmt)}, hintsOkA Γ arms = true →
    ∀ a ∈ arms, hintsOkL Γ a = true
  | [], _, _, h => (List.not_mem_nil h).elim
  | b :: bs, h, a, ha => by
      simp only [hintsOkA, Bool.and_eq_true] at h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.1
      · exact hintsOkA_mem h.2 a ha

theorem walkArms_cases (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    walkArms σ x j arms = .stuck ∨ ∃ a ∈ arms, walkArms σ x j arms = walk σ a
  | [], _ => Or.inl (by rw [walkArms])
  | a :: as, j => by
      unfold walkArms
      split_ifs
      · exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
      · rcases walkArms_cases x as (j + 1) with h | ⟨b, hb, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem pick_cases' {x : V} {a r : List V} : ∀ (gs : List String) (j : ℕ),
    pick σ x a r j gs = .stuck ∨ ∃ g, pick σ x a r j gs = .fall [.call g a r]
  | [], _ => Or.inl rfl
  | g :: gs, j => by
      unfold pick
      split_ifs
      · exact Or.inr ⟨g, rfl⟩
      · exact pick_cases' gs (j + 1)

/-- A call, a conditional call, a dispatch or a return makes no atom event. -/
theorem walk1_noAtom {s : Stmt} (hs : ∀ a, s ≠ .atom a) (hi : ∀ c z n, s ≠ .ite c z n)
    (hm : ∀ x arms, s ≠ .match_ x arms) (a : Atom) : Ev.atom a ∉ (walk1 σ s).evs := by
  cases s with
  | atom a => exact absurd rfl (hs a)
  | ite c z n => exact absurd rfl (hi c z n)
  | match_ x arms => exact absurd rfl (hm x arms)
  | call f args rets => simp [walk1, Out.evs]
  | callIf c f args =>
      intro ha
      simp only [walk1, Out.evs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with h | h
      · cases h
      · split_ifs at h
  | dispatch x fs args rets =>
      rw [walk1]
      rcases pick_cases' (σ := σ) (x := x) (a := args) (r := rets) fs 0 with h | ⟨g, h⟩
      · rw [h]; exact List.not_mem_nil
      · rw [h]; simp [Out.evs]
  | ret vs => exact List.not_mem_nil

/-- **A hint atom rests on atoms of the path.** -/
def Rests (E : List Ev) (a : Atom) : Prop :=
  ∃ Γ post, AtomsIn Γ E ∧ AtomsIn post E ∧ coverOk Γ post a = true

/-- An outcome then a block, the atoms of each resting on `E`. -/
theorem rests_of_seq {o k : Out} {E : List Ev} (hE : ∀ e ∈ (o.seq k).evs, e ∈ E)
    (ho : (∀ e ∈ o.evs, e ∈ E) → ∀ a, Ev.atom a ∈ o.evs → Rests E a)
    (hk : (∀ e ∈ k.evs, e ∈ E) → ∀ a, Ev.atom a ∈ k.evs → Rests E a) :
    ∀ a, Ev.atom a ∈ (o.seq k).evs → Rests E a := by
  intro a ha
  rcases o with es | ⟨es, vs⟩ | _
  · rw [out_seq_fall] at ha hE
    by_cases hs : k = .stuck
    · rw [hs] at ha; exact (List.not_mem_nil ha).elim
    · rw [out_pre_evs _ hs] at ha hE
      rcases List.mem_append.mp ha with ha | ha
      · exact ho (fun e he => hE e (List.mem_append_left _ he)) a ha
      · exact hk (fun e he => hE e (List.mem_append_right _ he)) a ha
  · exact ho hE a ha
  · exact (List.not_mem_nil ha).elim

theorem rests_pre {o : Out} {E : List Ev} {pre : List Ev} (hpre : ∀ a, Ev.atom a ∉ pre)
    (hE : ∀ e ∈ (o.pre pre).evs, e ∈ E) (ho : (∀ e ∈ o.evs, e ∈ E) → ∀ a, Ev.atom a ∈ o.evs → Rests E a) :
    ∀ a, Ev.atom a ∈ (o.pre pre).evs → Rests E a := by
  intro a ha
  by_cases hs : o = .stuck
  · rw [hs] at ha; exact (List.not_mem_nil ha).elim
  · rw [out_pre_evs _ hs] at ha hE
    rcases List.mem_append.mp ha with ha | ha
    · exact absurd ha (hpre a)
    · exact ho (fun e he => hE e (List.mem_append_right _ he)) a ha

mutual
/-- **On a path of a checked statement other than an atom, every atom rests on the path.** -/
theorem hintsOkS_sound : ∀ (s : Stmt) (Γ post : List Atom) (E : List Ev), hintsOkS Γ post s = true →
    AtomsIn Γ E → (∀ a', s ≠ .atom a') → (∀ e ∈ (walk1 σ s).evs, e ∈ E) →
      ∀ a, Ev.atom a ∈ (walk1 σ s).evs → Rests E a
  | .atom a', _, _, _, _, _, hs, _, _, _ => absurd rfl (hs a')
  | .ite c z n, Γ, _, E, h, hΓ, _, hE, a, ha => by
      simp only [hintsOkS, Bool.and_eq_true] at h
      rw [walk1] at hE ha
      refine rests_pre (fun a h => by simp at h) hE (fun hE' a ha => ?_) a ha
      by_cases hc : σ c = 0
      · rw [ite_eq_left hc] at hE' ha; exact hintsOkL_sound z Γ E h.1 hΓ hE' a ha
      · rw [ite_eq_right hc] at hE' ha; exact hintsOkL_sound n Γ E h.2 hΓ hE' a ha
  | .match_ x arms, Γ, _, E, h, hΓ, _, hE, a, ha => by
      simp only [hintsOkS] at h
      rw [walk1] at hE ha
      exact hintsOkA_sound x arms 0 Γ E h hΓ hE a ha
  | .call .., _, _, _, _, _, _, _, a, ha => absurd ha (walk1_noAtom (fun _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) a)
  | .callIf .., _, _, _, _, _, _, _, a, ha => absurd ha (walk1_noAtom (fun _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) a)
  | .dispatch .., _, _, _, _, _, _, _, a, ha => absurd ha (walk1_noAtom (fun _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) a)
  | .ret _, _, _, _, _, _, _, _, a, ha => absurd ha (walk1_noAtom (fun _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) a)

/-- **On a path of a checked block, every atom rests on the path.** -/
theorem hintsOkL_sound : ∀ (ss : List Stmt) (Γ : List Atom) (E : List Ev), hintsOkL Γ ss = true →
    AtomsIn Γ E → (∀ e ∈ (walk σ ss).evs, e ∈ E) → ∀ a, Ev.atom a ∈ (walk σ ss).evs → Rests E a
  | [], _, _, _, _, _, _, ha => (List.not_mem_nil ha).elim
  | .atom a' :: ss, Γ, E, h, hΓ, hE, a, ha => by
      simp only [hintsOkL, hintsOkS, Bool.and_eq_true] at h
      obtain ⟨hs, hss⟩ := h
      have hs' : walk σ ss ≠ .stuck := by
        intro hst; rw [walk, walk1, out_seq_fall, hst] at ha; exact List.not_mem_nil ha
      have hev : (walk σ (.atom a' :: ss)).evs = .atom a' :: (walk σ ss).evs := by
        rw [walk, walk1, out_seq_fall, out_pre_evs _ hs']; rfl
      rw [hev] at ha hE
      have hE' : ∀ e ∈ (walk σ ss).evs, e ∈ E := fun e he => hE e (List.mem_cons_of_mem _ he)
      rcases List.mem_cons.mp ha with ha | ha
      · cases ha
        exact ⟨Γ, runAtoms ss, hΓ, fun q hq => hE' _ (runAtoms_mem ss hs' q hq), hs⟩
      · refine hintsOkL_sound ss _ E hss (fun q hq => ?_) hE' a ha
        simp only [keepAfter] at hq
        split at hq
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact hE _ List.mem_cons_self
          · exact hΓ q hq
        · exact hΓ q hq
  | .ite c z n :: ss, Γ, E, h, hΓ, hE, a, ha => by
      simp only [hintsOkL, Bool.and_eq_true] at h
      rw [walk] at hE ha
      exact rests_of_seq hE (hintsOkS_sound _ Γ _ E h.1 hΓ (fun _ h => by cases h))
        (hintsOkL_sound ss Γ E h.2 hΓ) a ha
  | .match_ x arms :: ss, Γ, E, h, hΓ, hE, a, ha => by
      simp only [hintsOkL, Bool.and_eq_true] at h
      rw [walk] at hE ha
      exact rests_of_seq hE (hintsOkS_sound _ Γ _ E h.1 hΓ (fun _ h => by cases h))
        (hintsOkL_sound ss Γ E h.2 hΓ) a ha
  | .call f args rets :: ss, Γ, E, h, hΓ, hE, a, ha => by
      simp only [hintsOkL, Bool.and_eq_true] at h
      rw [walk] at hE ha
      exact rests_of_seq hE (hintsOkS_sound _ Γ _ E h.1 hΓ (fun _ h => by cases h))
        (hintsOkL_sound ss Γ E h.2 hΓ) a ha
  | .callIf c f args :: ss, Γ, E, h, hΓ, hE, a, ha => by
      simp only [hintsOkL, Bool.and_eq_true] at h
      rw [walk] at hE ha
      exact rests_of_seq hE (hintsOkS_sound _ Γ _ E h.1 hΓ (fun _ h => by cases h))
        (hintsOkL_sound ss Γ E h.2 hΓ) a ha
  | .dispatch x fs args rets :: ss, Γ, E, h, hΓ, hE, a, ha => by
      simp only [hintsOkL, Bool.and_eq_true] at h
      rw [walk] at hE ha
      exact rests_of_seq hE (hintsOkS_sound _ Γ _ E h.1 hΓ (fun _ h => by cases h))
        (hintsOkL_sound ss Γ E h.2 hΓ) a ha
  | .ret vs :: ss, Γ, E, h, hΓ, hE, a, ha => by
      simp only [hintsOkL, Bool.and_eq_true] at h
      rw [walk] at hE ha
      exact rests_of_seq hE (hintsOkS_sound _ Γ _ E h.1 hΓ (fun _ h => by cases h))
        (hintsOkL_sound ss Γ E h.2 hΓ) a ha

/-- The arms' version. -/
theorem hintsOkA_sound (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) (Γ : List Atom) (E : List Ev),
    hintsOkA Γ arms = true → AtomsIn Γ E → (∀ e ∈ (walkArms σ x j arms).evs, e ∈ E) →
      ∀ a, Ev.atom a ∈ (walkArms σ x j arms).evs → Rests E a
  | [], j, _, _, _, _, _, a, ha => by rw [walkArms] at ha; exact (List.not_mem_nil ha).elim
  | b :: bs, j, Γ, E, h, hΓ, hE, a, ha => by
      simp only [hintsOkA, Bool.and_eq_true] at h
      unfold walkArms at hE ha
      split_ifs at hE ha
      · exact hintsOkL_sound b Γ E h.1 hΓ hE a ha
      · exact hintsOkA_sound x bs (j + 1) Γ E h.2 hΓ hE a ha
end

end Walk

/-! ## Nodes -/

section Node

variable {rd : Reader} {σ : Val}

theorem powWord_spec {w : E} {e : ℕ} (h : powWord w e = true) :
    w = ofK (addressOfIndex e) ∧ e < 2 ^ 20 := by
  simp only [powWord, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨he, h1⟩, h0⟩ := h
  have h0' : w.limb 0 = addressOfIndex e := by
    split at h0
    · rename_i h64
      rw [decide_eq_true_eq] at h0
      rw [h0, Parameters.addressOfIndex, g_pow_eq_ofBits h64]
    · rw [decide_eq_true_eq] at h0
      rw [h0, Pow.gpowW_eq he]
  refine ⟨E.ext fun i => ?_, he⟩
  rw [limb_ofK]
  fin_cases i
  · simpa using h0'
  · simpa using h1

/-- A `HeapBuf` event of a path: its pointer and size are at one index of the path's lists. -/
theorem alloc_index {e : Ev} {d : V} {m : ℕ} (hd : e.allocDst? = some d) (hm : e.alloc? σ = some m) :
    ∀ {es : List Ev}, e ∈ es → ∃ j : ℕ, (allocDsts es)[j]? = some d ∧ (allocs σ es)[j]? = some m
  | [], h => (List.not_mem_nil h).elim
  | e' :: es, h => by
      have hiff : ∀ e'' : Ev, (e''.allocDst?).isSome = (e''.alloc? σ).isSome := by
        intro e''
        rcases e'' with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ | _⟩ | _ | _ | _ <;> rfl
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp [allocDsts, hd], by simp [allocs, hm]⟩
      · obtain ⟨j, h1, h2⟩ := alloc_index hd hm h
        rcases hx : e'.allocDst? with _ | x
        · have hy : e'.alloc? σ = none := by
            have := hiff e'; rw [hx] at this; exact Option.not_isSome_iff_eq_none.mp (by simp [← this])
          exact ⟨j, by simp [allocDsts, hx, ← h1, allocDsts],
            by simp [allocs, hy, ← h2, allocs]⟩
        · obtain ⟨y, hy⟩ : ∃ y, e'.alloc? σ = some y := by
            have := hiff e'; rw [hx] at this; exact Option.isSome_iff_exists.mp (by simp [← this])
          exact ⟨j + 1, by simp [allocDsts, hx, ← h1, allocDsts],
            by simp [allocs, hy, ← h2, allocs]⟩

/-- **A `HeapBuf` of a placed path holds `m` words from its pointer.** -/
theorem alloc_words {es : List Ev} {c : ℕ} {bufs : List ℕ}
    (hbuf : (allocDsts es).map σ = (bases c bufs).map fun b => ofK (addressOfIndex b))
    (hbo : bufs = allocs σ es) {e : Ev} (he : e ∈ es) {d : V} {m : ℕ} (hd : e.allocDst? = some d)
    (hm : e.alloc? σ = some m) : ∃ b, σ d = ofK (addressOfIndex b) ∧ (m, b) ∈ bufs.zip (bases c bufs) := by
  obtain ⟨j, h1, h2⟩ := alloc_index hd hm he
  have hlen : (bases c bufs).length = bufs.length := length_bases
  have hj : j < bufs.length := by
    rw [hbo]; exact (List.getElem?_eq_some_iff.mp h2).1
  have hjb : j < (bases c bufs).length := by rw [hlen]; exact hj
  refine ⟨(bases c bufs)[j], ?_, ?_⟩
  · have := congrArg (·[j]?) hbuf
    simp only [List.getElem?_map, h1, Option.map_some] at this
    rw [List.getElem?_eq_getElem hjb, Option.map_some] at this
    exact Option.some.inj this
  · have hbj : bufs[j] = m := by
      have := List.getElem?_eq_getElem hj
      rw [← hbo] at h2
      rw [h2] at this
      exact (Option.some.inj this).symm
    rw [List.mem_iff_getElem?]
    exact ⟨j, by rw [List.getElem?_zip_eq_some]; exact ⟨by rw [List.getElem?_eq_getElem hj, hbj],
      List.getElem?_eq_getElem hjb⟩⟩

theorem loadsSeq_sound {p : V} : ∀ {o n : ℕ} {Q : List Atom}, loadsSeq p o n Q = true →
    ∀ k < n, ∃ d, Atom.load d p (o + k) ∈ Q
  | _, 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | _, _ + 1, [], h, _, _ => absurd h Bool.false_ne_true
  | o, n + 1, a :: Q, h, k, hk => by
      have hrest : loadsSeq p o (n + 1) Q = true → ∃ d, Atom.load d p (o + k) ∈ a :: Q := fun h' =>
        let ⟨d', hd'⟩ := loadsSeq_sound h' k hk
        ⟨d', List.mem_cons_of_mem _ hd'⟩
      cases a with
      | load d q o' =>
        simp only [loadsSeq] at h
        split at h
        · rename_i hm
          simp only [Bool.and_eq_true, beq_iff_eq] at hm
          obtain ⟨hpq, rfl⟩ := hm
          rcases k with _ | k
          · exact ⟨d, by rw [vEq_spec hpq, Nat.add_zero]; exact List.mem_cons_self⟩
          · obtain ⟨d', hd'⟩ := loadsSeq_sound h k (by omega)
            exact ⟨d', List.mem_cons_of_mem _ (by rwa [show o' + 1 + k = o' + (k + 1) by omega] at hd')⟩
        · exact hrest h
      | _ => simp only [loadsSeq] at h; exact hrest h

/-- **The words of a hint resting on a placed path**: loaded by the path, or in one of its
`HeapBuf`s. -/
theorem rests_words {es : List Ev} {c : ℕ} {bufs : List ℕ} (hh : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases c bufs).map fun b => ofK (addressOfIndex b))
    (hbo : bufs = allocs σ es) {a : Atom} (hr : Rests es a) :
    ∀ A ∈ (Ev.atom a).hintAddrs σ, A ∈ loadAddrs σ es ∨
      ∃ i, A = addressOfIndex i ∧ ∃ q ∈ bufs.zip (bases c bufs), q.2 ≤ i ∧ i < q.2 + q.1 := by
  obtain ⟨Q, post, hQ, hpost, hc⟩ := hr
  intro A hA
  cases a with
  | hint h =>
    simp only [Ev.hintAddrs] at hA
    split at hA
    · rename_i p off len hd
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hA
      rw [List.mem_range] at hk
      have hd' : atomHeapDest? (.hint h) = some (p, off, len) := hd
      simp only [coverOk, hd', Bool.or_eq_true] at hc
      rcases hc with hc | hc
      · right
        obtain ⟨q, hq, hq'⟩ := List.any_eq_true.mp hc
        have hal : ∃ m, off + len ≤ m ∧ ∃ e ∈ es, e.allocDst? = some p ∧ e.alloc? σ = some m := by
          split at hq'
          · rename_i d m
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
            obtain ⟨hpd, hm⟩ := hq'
            exact ⟨m, hm, _, hQ _ hq, by rw [vEq_spec hpd]; rfl, rfl⟩
          · rename_i d sz
            simp only [Bool.and_eq_true] at hq'
            obtain ⟨hpd, hs⟩ := hq'
            obtain ⟨q', hq'', hs'⟩ := List.any_eq_true.mp hs
            split at hs'
            · rename_i d' w
              simp only [Bool.and_eq_true] at hs'
              obtain ⟨hsd, hi⟩ := hs'
              obtain ⟨i, -, hw⟩ := List.any_eq_true.mp hi
              obtain ⟨hw, h20⟩ := powWord_spec hw
              have hsv : σ sz = w := by
                have := hh _ (hQ _ hq'')
                simp only [Ev.Holds, Atom.Holds] at this
                rw [← vEq_spec hsd]; exact this
              refine ⟨off + len + i, Nat.le_add_right _ _, _, hQ _ hq, by rw [vEq_spec hpd]; rfl, ?_⟩
              simp only [Ev.alloc?, hsv, hw]
              rw [logG_spec (by omega)]
            · exact absurd hs' Bool.false_ne_true
          · exact absurd hq' Bool.false_ne_true
        obtain ⟨m, hle, e, he, hed, hem⟩ := hal
        obtain ⟨b, hb, hq⟩ := alloc_words hbuf hbo he hed hem
        refine ⟨b + (off + k), ?_, _, hq, Nat.le_add_right _ _, by simp only; omega⟩
        rw [hb, show (ofK (addressOfIndex b)).limb 0 = addressOfIndex b by simp]
        simp only [Parameters.addressOfIndex, pow_add]
      · left
        obtain ⟨d, hq⟩ := loadsSeq_sound hc k hk
        exact List.mem_filterMap.mpr ⟨_, hpost _ hq, rfl⟩
    · exact (List.not_mem_nil hA).elim
  | _ => simp [Ev.hintAddrs] at hA

/-- **A node's heap hint words**: loaded by its path, or in one of its `HeapBuf`s, when its function
passes the check. -/
theorem hintAddrs_local {fn : Fn} {es : List Ev} {vs : List V} {c : ℕ} {bufs : List ℕ}
    (hck : hintsOkL [] fn.body = true) (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases c bufs).map fun b => ofK (addressOfIndex b))
    (hbo : bufs = allocs σ es) :
    ∀ A ∈ heapHintAddrs σ es, A ∈ loadAddrs σ es ∨
      ∃ i, A = addressOfIndex i ∧ ∃ q ∈ bufs.zip (bases c bufs), q.2 ≤ i ∧ i < q.2 + q.1 := by
  intro A hA
  obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
  cases e with
  | atom a =>
    have hes : (walk σ fn.body).evs = es := by rw [hw]; rfl
    have hr := hintsOkL_sound fn.body [] es hck (fun _ h => (List.not_mem_nil h).elim)
      (fun e h => by rw [hes] at h; exact h) a (by rw [hes]; exact he)
    exact rests_words hh hbuf hbo hr A hA
  | _ => simp [Ev.hintAddrs] at hA

end Node

/-! ## Trees -/

section Tree

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

/-- **A node's heap hint words**: loaded by its path, in its own data, or in `Q`. -/
def NodeHints (Q : ℕ → Prop) (p : ℕ × ℕ) (f : String) (σ : Val) (bufs : List ℕ) (es : List Ev) :
    Prop :=
  ∀ A ∈ heapHintAddrs σ es, A ∈ loadAddrs σ es ∨
    ∃ i, A = addressOfIndex i ∧ (ownData cert p.1 p.2 f bufs es i ∨ Q i)

mutual
/-- **Every node of `t` placed from `p` is `NodeHints Q`.** -/
def Tree.HintsQ (Q : ℕ → Prop) : ℕ × ℕ → Tree → Prop
  | p, t@(.node f σ bufs kids) => NodeHints cert Q p f σ bufs (t.events P) ∧
      Tree.HintsQKids Q (kidPos fs P.loop p f bufs (kids.map (Tree.sz fs P.loop))) kids
  | _, .phantom .. => True

/-- `Tree.HintsQ` of the callees `ks` at `ps`. -/
def Tree.HintsQKids (Q : ℕ → Prop) : List (ℕ × ℕ) → List Tree → Prop
  | _, [] => True
  | [], _ :: _ => True
  | p :: ps, k :: ks => k.HintsQ Q p ∧ Tree.HintsQKids Q ps ks
end

/-- **A set of functions passing the check, closed under calls.** -/
def HintsClosed (S : String → Prop) : Prop :=
  ∀ g, S g → ∀ fn, P.find? g = some fn → hintsOkL [] fn.body = true ∧ ∀ c ∈ Stmt.blockCallees fn.body, S c

variable {P fs cert}

theorem hintsQ_node {Q : ℕ → Prop} {p : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} :
    (Tree.node f σ bufs kids).HintsQ P fs cert Q p ↔
      NodeHints cert Q p f σ bufs ((Tree.node f σ bufs kids).events P) ∧
        Tree.HintsQKids P fs cert Q (kidPos fs P.loop p f bufs (kids.map (Tree.sz fs P.loop))) kids := by
  rw [Tree.HintsQ]

theorem hintsQ_phantom {Q : ℕ → Prop} {p : ℕ × ℕ} {f : String} {σ : Val} :
    (Tree.phantom f σ).HintsQ P fs cert Q p := by
  rw [Tree.HintsQ]; trivial

theorem hintsQKids_cons {Q : ℕ → Prop} {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree} {ks : List Tree} :
    Tree.HintsQKids P fs cert Q (p :: ps) (k :: ks) ↔ k.HintsQ P fs cert Q p ∧ Tree.HintsQKids P fs cert Q ps ks := by
  rw [Tree.HintsQKids]

theorem hintsQKids_nil {Q : ℕ → Prop} {ps : List (ℕ × ℕ)} : Tree.HintsQKids P fs cert Q ps [] := by
  cases ps <;> (rw [Tree.HintsQKids]; trivial)

mutual
/-- **Heap hints in the loads' region**: a tree whose loads are in `R` and whose nodes are
`NodeHints Q`, `Q` within its data and `R`, has its heap hints in `R`. -/
theorem hintsIn_of_hintsQ : ∀ (t : Tree) (R Q : ℕ → Prop) (p : ℕ × ℕ), t.LoadsIn P fs cert R p →
    (∀ i, Q i → t.Data P fs cert p i ∨ R i) → t.HintsQ P fs cert Q p → t.HintsIn P fs cert R p
  | .node f σ bufs kids, R, Q, p, hl, hQ, hh => by
      rw [loadsIn_node] at hl
      rw [hintsQ_node] at hh
      rw [hintsIn_node]
      refine ⟨fun A hA => ?_, hintsInKids_of_hintsQ kids _ Q _ hl.2 hQ hh.2⟩
      rcases hh.1 A hA with hA | ⟨i, rfl, hi | hi⟩
      · exact hl.1 _ hA
      · exact ⟨i, rfl, Or.inl (data_node.mpr (Or.inl hi))⟩
      · exact ⟨i, rfl, hQ i hi⟩
  | .phantom .., _, _, _, _, _, _ => hintsIn_phantom

/-- `hintsIn_of_hintsQ` for the callees. -/
theorem hintsInKids_of_hintsQ : ∀ (ks : List Tree) (R Q : ℕ → Prop) (ps : List (ℕ × ℕ)),
    Tree.LoadsInKids P fs cert R ps ks → (∀ i, Q i → R i) → Tree.HintsQKids P fs cert Q ps ks →
      Tree.HintsInKids P fs cert R ps ks
  | [], _, _, _, _, _, _ => hintsInKids_nil
  | _ :: _, _, _, [], _, _, _ => by rw [Tree.HintsInKids]; trivial
  | k :: ks, R, Q, p :: ps, hl, hQ, hh => by
      rw [loadsInKids_cons] at hl
      rw [hintsQKids_cons] at hh
      rw [hintsInKids_cons]
      exact ⟨hintsIn_of_hintsQ k R Q p hl.1 (fun i hi => Or.inr (hQ i hi)) hh.1,
        hintsInKids_of_hintsQ ks R Q ps hl.2 hQ hh.2⟩
end

variable {rd : Reader} {S : String → Prop}

/-- **A node of a function passing the check is `NodeHints`.** -/
theorem nodeHints_of_check {Q : ℕ → Prop} {p : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {args rets : List E} (hv : (Tree.node f σ bufs kids).Valid P rd args rets)
    (hb : (Tree.node f σ bufs kids).BufsOk P) (hp : (Tree.node f σ bufs kids).Placed P fs cert p)
    (hck : ∀ fn, P.find? f = some fn → hintsOkL [] fn.body = true) :
    NodeHints cert Q p f σ bufs ((Tree.node f σ bufs kids).events P) := by
  obtain ⟨fn, hf, -, es, vs, hw, -, hes, -⟩ := hv
  rw [Tree.BufsOk, events_node hf hw] at hb
  rw [placed_node, events_node hf hw] at hp
  rw [events_node hf hw]
  intro A hA
  rcases hintAddrs_local (hck fn hf) hw hes hp.1.1 hb.1 A hA with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, Or.inl (Or.inl h)⟩

mutual
/-- **The trees of a closed set of functions passing the check are `HintsQ`.** -/
theorem hintsQ_of_closed (hS : HintsClosed P S) (Q : ℕ → Prop) : ∀ (t : Tree) {args rets : List E}
    (p : ℕ × ℕ), t.Valid P rd args rets → t.BufsOk P → t.Placed P fs cert p → S t.name →
      t.HintsQ P fs cert Q p
  | .node f σ bufs kids, args, rets, p, hv, hb, hp, hn => by
      have hv' := hv
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv'
      have hck := hS f hn
      rw [hintsQ_node]
      refine ⟨nodeHints_of_check hv hb hp fun fn' hf' => (hck fn' hf').1, ?_⟩
      rw [Tree.BufsOk] at hb
      rw [placed_node] at hp
      exact hintsQKids_of_closed hS Q kids σ (calls es) _ hk hb.2 hp.2 fun c hc =>
        (hck fn hf).2 c.f (walk_callees (σ := σ) fn.body (by rw [hw]; exact hc))
  | .phantom .., _, _, _, _, _, _, _ => hintsQ_phantom

/-- `hintsQ_of_closed` for the callees. -/
theorem hintsQKids_of_closed (hS : HintsClosed P S) (Q : ℕ → Prop) : ∀ (ks : List Tree) (σ : Val)
    (cs : List Call) (ps : List (ℕ × ℕ)), Tree.KidsValid P rd σ cs ks → Tree.BufsOkKids P ks →
      Tree.PlacedKids P fs cert ps ks → (∀ c ∈ cs, S c.f) → Tree.HintsQKids P fs cert Q ps ks
  | [], _, _, _, _, _, _, _ => hintsQKids_nil
  | _ :: _, _, _, [], _, _, _, _ => by rw [Tree.HintsQKids]; trivial
  | k :: ks, σ, c :: cs, p :: ps, ⟨hn, hc, hks⟩, hb, hp, hS' => by
      rw [Tree.BufsOkKids] at hb
      rw [placedKids_cons] at hp
      rw [hintsQKids_cons]
      refine ⟨?_, hintsQKids_of_closed hS Q ks σ cs ps hks hb.2 hp.2 fun c' h => hS' c' (List.mem_cons_of_mem _ h)⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact hintsQ_of_closed hS Q k p hc hb.1 hp.1 (hn ▸ hS' c List.mem_cons_self)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact hintsQ_phantom
  | _ :: _, _, [], _ :: _, h, _, _, _ => h.elim
end

end Tree

end
end LeanVM.Guest.Memory
