module

public import LeanVM.Guest.Mode.SoundJoin
public import LeanVM.Guest.Mode.Win

/-!
# The pass, offset by offset

What the walk knows at offset `i` of a function: the paths and pending edges its pass has before the
offset (`preAt`, the run of the code's first `i` instructions), and a state of the executor is at
the offset when one of those paths holds there or a pending edge into the offset does (`AtOff`).
`atOff_zero`: the entry. `atOff_step`: at an offset the walk accepts, some path holds and its step
(`offStep`) goes through; what falls through holds at the next offset, and an edge it adds into a
later offset `j` (`Cov`) holds at `j`, whatever the walk does in between (`cov_forward`: a pending
edge survives each offset before its target, its groups' targets increasing, `PendOk`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest
open LeanVM.Prover.Exec (St)

@[expose] public section

/-- Some group of `P` enters offset `j` with a state that holds at `s`. -/
def Cov (s : St) (P : Pend) (j : ℕ) : Prop := ∃ G ∈ P, j ∈ G.ts ∧ ∃ B ∈ G.Bs, Holds s B

/-- Every group's targets increase, from `k` on. -/
def PendOk (P : Pend) (k : ℕ) : Prop := ∀ G ∈ P, incr G.ts = true ∧ ∀ t ∈ G.ts, k ≤ t

/-- Every edge of `P` is one of `Q`'s. -/
def PendLe (P Q : Pend) : Prop := ∀ s j, Cov s P j → Cov s Q j

theorem PendLe.refl (P : Pend) : PendLe P P := fun _ _ h ↦ h

theorem PendLe.trans {P Q R : Pend} (h1 : PendLe P Q) (h2 : PendLe Q R) : PendLe P R :=
  fun s j h ↦ h2 s j (h1 s j h)

/-- The paths and pending edges before offset `i`. -/
noncomputable def preAt (E : Env) (F : Fun) (code : List OffsetInstruction) (i : ℕ) :
    Option (List Abs × Pend) :=
  runCode E F (code.take i) 0 [entryAbs E F.sig] []

/-- **A state at offset `i`**: a path the walk has there holds, or a pending edge into it does. -/
def AtOff (E : Env) (F : Fun) (code : List OffsetInstruction) (i : ℕ) (s : St) : Prop :=
  ∃ cur pend, preAt E F code i = some (cur, pend) ∧ ((∃ A ∈ cur, Holds s A) ∨ Cov s pend i)

/-! ## Increasing targets -/

theorem incr_lt : ∀ {t : ℕ} {ts : List ℕ}, incr (t :: ts) = true → ∀ u ∈ ts, t < u
  | _, [], _, _, hu => absurd hu List.not_mem_nil
  | t, b :: l, h, u, hu => by
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · exact lt_trans h.1 (incr_lt h.2 u hu)

theorem incr_tail {t : ℕ} {ts : List ℕ} (h : incr (t :: ts) = true) : incr ts = true := by
  cases ts with
  | nil => rfl
  | cons b l => simp only [incr, Bool.and_eq_true] at h; exact h.2

theorem PendOk.cons {G : Grp} {P : Pend} {k : ℕ} (h : PendOk (G :: P) k) : PendOk P k :=
  fun G' hG' ↦ h G' (List.mem_cons_of_mem _ hG')

/-! ## Taking the edges into an offset -/

theorem popAt_nil' (i : ℕ) (Bs : List Abs) (m : Bool) (gs : Pend) :
    popAt i (⟨[], Bs, m⟩ :: gs) = popAt i gs := by
  conv_lhs => unfold popAt

theorem popAt_cons' (i t : ℕ) (ts : List ℕ) (Bs : List Abs) (m : Bool) (gs : Pend) :
    popAt i (⟨t :: ts, Bs, m⟩ :: gs) = if t = i then
      (Bs ++ (popAt i gs).1, (popAt i gs).2.1 + (if m then 3 else Bs.length),
        if ts = [] then (popAt i gs).2.2 else ⟨ts, Bs, m⟩ :: (popAt i gs).2.2)
    else ((popAt i gs).1, (popAt i gs).2.1, ⟨t :: ts, Bs, m⟩ :: (popAt i gs).2.2) := by
  conv_lhs => unfold popAt
  rcases popAt i gs with ⟨As, n, ps⟩
  by_cases h : t = i
  · subst h; cases ts <;> simp
  · simp [h]

theorem popAt_sub (i : ℕ) (g : Grp) (gs : Pend) :
    ∀ A ∈ (popAt i gs).1, A ∈ (popAt i (g :: gs)).1 := fun A hA ↦ by
  obtain ⟨ts0, Bs, m⟩ := g
  rcases ts0 with _ | ⟨t, ts⟩
  · rw [popAt_nil']; exact hA
  · rw [popAt_cons']
    by_cases ht : t = i
    · rw [ite_eq_left ht]; exact List.mem_append_right _ hA
    · rw [ite_eq_right ht]; exact hA

theorem popAt_cov {s : St} {i : ℕ} : ∀ {P : Pend}, PendOk P i → Cov s P i →
    ∃ A ∈ (popAt i P).1, Holds s A
  | [], _, ⟨_, hG, _⟩ => absurd hG List.not_mem_nil
  | g :: gs, hP, ⟨G, hG, hj, B, hB, hH⟩ => by
    rcases List.mem_cons.mp hG with rfl | hG
    · obtain ⟨hinc, hge⟩ := hP G (List.mem_cons_self ..)
      obtain ⟨ts0, Bs, m⟩ := G
      rcases ts0 with _ | ⟨t, ts⟩
      · exact absurd hj List.not_mem_nil
      · have hti : t = i := by
          rcases List.mem_cons.mp hj with h | h
          · exact h.symm
          · have := incr_lt hinc i h; have := hge t (List.mem_cons_self ..); omega
        rw [popAt_cons', ite_eq_left hti]
        exact ⟨B, List.mem_append_left _ hB, hH⟩
    · obtain ⟨A, hA, hHA⟩ := popAt_cov hP.cons ⟨G, hG, hj, B, hB, hH⟩
      exact ⟨A, popAt_sub i g gs A hA, hHA⟩

theorem popAt_keep {s : St} {i j : ℕ} (hji : j ≠ i) : ∀ {P : Pend}, Cov s P j →
    Cov s (popAt i P).2.2 j
  | [], ⟨_, hG, _⟩ => absurd hG List.not_mem_nil
  | g :: gs, ⟨G, hG, hj, B, hB, hH⟩ => by
    rcases List.mem_cons.mp hG with rfl | hG
    · obtain ⟨ts0, Bs, m⟩ := G
      rcases ts0 with _ | ⟨t, ts⟩
      · exact absurd hj List.not_mem_nil
      · rw [popAt_cons']
        by_cases ht : t = i
        · rw [ite_eq_left ht]
          have hj' : j ∈ ts := by
            rcases List.mem_cons.mp hj with h | h
            · omega
            · exact h
          by_cases hts : ts = []
          · rw [hts] at hj'; exact absurd hj' List.not_mem_nil
          · rw [ite_eq_right hts]; exact ⟨_, List.mem_cons_self .., hj', B, hB, hH⟩
        · rw [ite_eq_right ht]; exact ⟨_, List.mem_cons_self .., hj, B, hB, hH⟩
    · obtain ⟨G', hG', hj', B', hB', hH'⟩ := popAt_keep hji ⟨G, hG, hj, B, hB, hH⟩
      have key : ∀ X ∈ (popAt i gs).2.2, X ∈ (popAt i (g :: gs)).2.2 := fun X hX ↦ by
        obtain ⟨ts0, Bs, m⟩ := g
        rcases ts0 with _ | ⟨t, ts⟩
        · rw [popAt_nil']; exact hX
        · rw [popAt_cons']
          by_cases ht : t = i
          · rw [ite_eq_left ht]
            by_cases hts : ts = []
            · rw [ite_eq_left hts]; exact hX
            · rw [ite_eq_right hts]; exact List.mem_cons_of_mem _ hX
          · rw [ite_eq_right ht]; exact List.mem_cons_of_mem _ hX
      exact ⟨G', key G' hG', hj', B', hB', hH'⟩

theorem popAt_ok {i : ℕ} : ∀ {P : Pend}, PendOk P i → PendOk (popAt i P).2.2 (i + 1)
  | [], _ => fun _ h ↦ absurd h List.not_mem_nil
  | g :: gs, hP => by
    have ih := popAt_ok hP.cons
    obtain ⟨hinc, hge⟩ := hP g (List.mem_cons_self ..)
    obtain ⟨ts0, Bs, m⟩ := g
    rcases ts0 with _ | ⟨t, ts⟩
    · rw [popAt_nil']; exact ih
    · rw [popAt_cons']
      by_cases ht : t = i
      · rw [ite_eq_left ht]
        by_cases hts : ts = []
        · rw [ite_eq_left hts]; exact ih
        · rw [ite_eq_right hts]
          intro G hG
          rcases List.mem_cons.mp hG with rfl | hG
          · exact ⟨incr_tail hinc, fun u hu ↦ by have := incr_lt hinc u hu; omega⟩
          · exact ih G hG
      · rw [ite_eq_right ht]
        intro G hG
        rcases List.mem_cons.mp hG with rfl | hG
        · refine ⟨hinc, fun u hu ↦ ?_⟩
          have h0 := hge t (List.mem_cons_self ..)
          rcases List.mem_cons.mp hu with rfl | hu
          · omega
          · have := incr_lt hinc u hu; omega
        · exact ih G hG

theorem joinAt_holds {s : St} {i : ℕ} {cur : List Abs} {pend : Pend} (hP : PendOk pend i)
    (h : (∃ A ∈ cur, Holds s A) ∨ Cov s pend i) : ∃ A ∈ (joinAt i cur pend).1, Holds s A := by
  have h' : ∃ A ∈ cur ++ (popAt i pend).1, Holds s A := by
    rcases h with ⟨A, hA, hH⟩ | h
    · exact ⟨A, List.mem_append_left _ hA, hH⟩
    · obtain ⟨A, hA, hH⟩ := popAt_cov hP h
      exact ⟨A, List.mem_append_right _ hA, hH⟩
  unfold joinAt
  rcases e : popAt i pend with ⟨As, n, ps⟩
  rw [e] at h'
  dsimp only
  split_ifs
  · exact Holds.meetAll h'
  · exact h'

theorem joinAt_pend (i : ℕ) (cur : List Abs) (pend : Pend) :
    (joinAt i cur pend).2 = (popAt i pend).2.2 := by
  unfold joinAt
  rcases popAt i pend with ⟨As, n, ps⟩
  rfl

/-! ## Adding edges -/

theorem addGrp_cons (ts : List ℕ) (A : Abs) (g : Grp) (gs : Pend) : addGrp ts A (g :: gs) =
    if g.ts == ts then
      (if g.m || 3 ≤ (g.Bs ++ [A]).length then ⟨g.ts, meetAll (g.Bs ++ [A]), true⟩ :: gs
        else ⟨g.ts, g.Bs ++ [A], false⟩ :: gs)
    else g :: addGrp ts A gs := by
  conv_lhs => unfold addGrp
  simp only [listSeq_id, forceAll_eq]

theorem addGrp_keep (ts : List ℕ) (A : Abs) : ∀ (P : Pend), PendLe P (addGrp ts A P)
  | [], _, _, ⟨_, hG, _⟩ => absurd hG List.not_mem_nil
  | g :: gs, s, j, ⟨G, hG, hj, B, hB, hH⟩ => by
    rw [addGrp_cons]
    rcases List.mem_cons.mp hG with rfl | hG
    · split_ifs
      · exact ⟨_, List.mem_cons_self .., hj,
          Holds.meetAll ⟨B, List.mem_append_left _ hB, hH⟩⟩
      · exact ⟨_, List.mem_cons_self .., hj, B, List.mem_append_left _ hB, hH⟩
      · exact ⟨G, List.mem_cons_self .., hj, B, hB, hH⟩
    · split_ifs
      · exact ⟨G, List.mem_cons_of_mem _ hG, hj, B, hB, hH⟩
      · exact ⟨G, List.mem_cons_of_mem _ hG, hj, B, hB, hH⟩
      · obtain ⟨G', hG', h'⟩ := addGrp_keep ts A gs s j ⟨G, hG, hj, B, hB, hH⟩
        exact ⟨G', List.mem_cons_of_mem _ hG', h'⟩

/-- **An added edge** into a target of `ts`, from a state that holds. -/
theorem addGrp_new {s : St} {ts : List ℕ} {A : Abs} (hA : Holds s A) {j : ℕ} (hj : j ∈ ts) :
    ∀ (P : Pend), Cov s (addGrp ts A P) j
  | [] => ⟨_, List.mem_singleton_self _, hj, A, List.mem_singleton_self _, hA⟩
  | g :: gs => by
    rw [addGrp_cons]
    split_ifs with h1
    · rw [beq_iff_eq.mp h1]
      exact ⟨_, List.mem_cons_self .., hj, Holds.meetAll ⟨A, List.mem_append_right _
        (List.mem_singleton_self _), hA⟩⟩
    · exact ⟨_, List.mem_cons_self .., by rw [beq_iff_eq.mp h1]; exact hj, A,
        List.mem_append_right _ (List.mem_singleton_self _), hA⟩
    · obtain ⟨G', hG', h'⟩ := addGrp_new hA hj gs
      exact ⟨G', List.mem_cons_of_mem _ hG', h'⟩

theorem addGrp_ok {ts : List ℕ} {A : Abs} {k : ℕ} (hinc : incr ts = true) (hge : ∀ t ∈ ts, k ≤ t) :
    ∀ {P : Pend}, PendOk P k → PendOk (addGrp ts A P) k
  | [], _ => fun G hG ↦ by
    rw [List.mem_singleton.mp hG]; exact ⟨hinc, hge⟩
  | g :: gs, hP => by
    rw [addGrp_cons]
    have hg := hP g (List.mem_cons_self ..)
    split_ifs
    all_goals first
      | (intro G hG
         rcases List.mem_cons.mp hG with rfl | hG
         · exact hg
         · exact hP G (List.mem_cons_of_mem _ hG))
      | (intro G hG
         rcases List.mem_cons.mp hG with rfl | hG
         · exact hg
         · exact addGrp_ok hinc hge hP.cons G hG)

/-! ## One offset -/

theorem jumpBind_pend {i : ℕ} {pend pend' : Pend} {cs fall : List Abs} {o : Option (Go × Abs)}
    (h : (o.bind fun a ↦ match a.1 with
      | Go.to ts => if ((ts.all fun x ↦ decide (i < x)) && incr ts) = true then
          some (fall, if ts.isEmpty = true then pend else a.2.force fun A' ↦ addGrp ts A' pend) else none
      | Go.out => some (fall, pend)) = some (cs, pend')) :
    pend' = pend ∨ ∃ ts A', incr ts = true ∧ (∀ t ∈ ts, i < t) ∧ pend' = addGrp ts A' pend := by
  obtain ⟨⟨go, A'⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  rcases go with ts | _
  · dsimp only at h
    split_ifs at h with h1 h2
    · cases h; exact Or.inl rfl
    · cases h
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h1
      rw [Abs.force_eq]
      exact Or.inr ⟨_, A', h1.2, h1.1, rfl⟩
  · cases h; exact Or.inl rfl

/-- What one path's step does to the pending edges: nothing, or edges into later offsets. -/
theorem offStep_pend {E : Env} {F : Fun} {i : ℕ} {A : Abs} {ins : OffsetInstruction} {pend pend' : Pend}
    {cs : List Abs} (h : offStep E F i A ins pend = some (cs, pend')) :
    pend' = pend ∨ ∃ ts A', incr ts = true ∧ (∀ t ∈ ts, i < t) ∧ pend' = addGrp ts A' pend := by
  unfold offStep at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨A1, -, A2, -, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨A3, -, h⟩ := h
    split at h
    · cases h; exact Or.inl rfl
    · split at h <;> exact jumpBind_pend h
  · obtain ⟨_, -, h⟩ := Option.map_eq_some_iff.mp h
    cases h; exact Or.inl rfl

theorem offStep_le {E : Env} {F : Fun} {i : ℕ} {A : Abs} {ins : OffsetInstruction} {pend pend' : Pend}
    {cs : List Abs} (h : offStep E F i A ins pend = some (cs, pend')) : PendLe pend pend' := by
  rcases offStep_pend h with rfl | ⟨ts, A', -, -, rfl⟩
  · exact PendLe.refl _
  · exact addGrp_keep ts A' pend

theorem offStep_ok {E : Env} {F : Fun} {i : ℕ} {A : Abs} {ins : OffsetInstruction} {pend pend' : Pend}
    {cs : List Abs} (h : offStep E F i A ins pend = some (cs, pend')) (hP : PendOk pend (i + 1)) :
    PendOk pend' (i + 1) := by
  rcases offStep_pend h with rfl | ⟨ts, A', hinc, hge, rfl⟩
  · exact hP
  · exact addGrp_ok hinc (fun t ht ↦ hge t ht) hP

/-- Every path at an offset: each one's step, from the edges pending before it. -/
theorem stepAll_spec {E : Env} {F : Fun} {i : ℕ} {ins : OffsetInstruction} :
    ∀ {sts : List Abs} {pend pend' : Pend} {cur : List Abs},
      stepAll E F i ins sts pend = some (cur, pend') → PendOk pend (i + 1) →
      PendLe pend pend' ∧ PendOk pend' (i + 1) ∧ ∀ A ∈ sts, ∃ pa cs pb,
        offStep E F i A ins pa = some (cs, pb) ∧ PendOk pa (i + 1) ∧ (∀ X ∈ cs, X ∈ cur) ∧
          PendLe pb pend'
  | [], pend, pend', cur, h, hP => by
    cases h
    exact ⟨PendLe.refl _, hP, fun A hA ↦ absurd hA List.not_mem_nil⟩
  | A :: As, pend, pend', cur, h, hP => by
    simp only [stepAll] at h
    split at h
    · rename_i cs pb e
      obtain ⟨⟨cur2, pend2⟩, e2, h⟩ := Option.map_eq_some_iff.mp h
      cases h
      have hok := offStep_ok e hP
      obtain ⟨hle, hok2, hall⟩ := stepAll_spec e2 hok
      refine ⟨(offStep_le e).trans hle, hok2, fun X hX ↦ ?_⟩
      rcases List.mem_cons.mp hX with rfl | hX
      · exact ⟨pend, cs, pb, e, hP, fun Y hY ↦ List.mem_append_left _ hY, hle⟩
      · obtain ⟨pa, cs', pb', e', h1, h2, h3⟩ := hall X hX
        exact ⟨pa, cs', pb', e', h1, fun Y hY ↦ List.mem_append_right _ (h2 Y hY), h3⟩
    · cases h

/-! ## Cuts -/

theorem subAll_holds {s : St} : ∀ {Ss As : List Abs}, subAll Ss As = true → ∀ A ∈ As, Holds s A →
    ∃ S ∈ Ss, Holds s S
  | [], [], _, A, hA, _ => absurd hA List.not_mem_nil
  | S :: Ss, A' :: As, h, A, hA, hH => by
    simp only [subAll, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hA with rfl | hA
    · exact ⟨S, List.mem_cons_self .., hH.sub h.1⟩
    · obtain ⟨S', hS', h'⟩ := subAll_holds h.2 A hA hH
      exact ⟨S', List.mem_cons_of_mem _ hS', h'⟩
  | [], _ :: _, h, _, _, _ => by simp [subAll] at h
  | _ :: _, [], h, _, _, _ => by simp [subAll] at h

theorem pendSub_le : ∀ {S P : Pend}, pendSub S P = true → PendLe P S
  | [], [], _, _, _, ⟨_, hG, _⟩ => absurd hG List.not_mem_nil
  | S :: Ss, G :: Gs, h, s, j, ⟨G', hG', hj, B, hB, hH⟩ => by
    simp only [pendSub, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hts, -⟩, hsub⟩, hrest⟩ := h
    rcases List.mem_cons.mp hG' with rfl | hG'
    · obtain ⟨S', hS', hH'⟩ := subAll_holds hsub B hB hH
      exact ⟨S, List.mem_cons_self .., by rw [hts]; exact hj, S', hS', hH'⟩
    · obtain ⟨X, hX, h'⟩ := pendSub_le hrest s j ⟨G', hG', hj, B, hB, hH⟩
      exact ⟨X, List.mem_cons_of_mem _ hX, h'⟩
  | [], _ :: _, h, _, _, _ => by simp [pendSub] at h
  | _ :: _, [], h, _, _, _ => by simp [pendSub] at h

theorem pendSub_ok {k : ℕ} : ∀ {S P : Pend}, pendSub S P = true → PendOk P k → PendOk S k
  | [], [], _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | S :: Ss, G :: Gs, h, hP => by
    simp only [pendSub, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hts, -⟩, -⟩, hrest⟩ := h
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · rw [hts]; exact hP G (List.mem_cons_self ..)
    · exact pendSub_ok hrest hP.cons X hX
  | [], _ :: _, h, _ => by simp [pendSub] at h
  | _ :: _, [], h, _ => by simp [pendSub] at h

theorem cutAt_spec {F : Fun} {k : ℕ} {cur cur' : List Abs} {pend pend' : Pend}
    (h : cutAt F k cur pend = some (cur', pend')) :
    (∀ s, (∃ A ∈ cur, Holds s A) → ∃ A ∈ cur', Holds s A) ∧ PendLe pend pend' ∧
      (PendOk pend k → PendOk pend' k) := by
  unfold cutAt at h
  split at h
  · rename_i S _
    split_ifs at h with h1
    cases h
    simp only [Bool.and_eq_true] at h1
    exact ⟨fun s ⟨A, hA, hH⟩ ↦ subAll_holds h1.1 A hA hH, pendSub_le h1.2, pendSub_ok h1.2⟩
  · cases h
    exact ⟨fun _ h ↦ h, PendLe.refl _, id⟩

/-! ## The pass -/

theorem runCode_one (E : Env) (F : Fun) (ins : OffsetInstruction) (i : ℕ) (c : List Abs) (p : Pend) :
    runCode E F [ins] i c p = (stepAll E F i ins (joinAt i c p).1 (joinAt i c p).2).bind fun q ↦
      cutAt F (i + 1) q.1 q.2 := by
  rw [runCode_cons]
  congr 1
  funext q
  rcases cutAt F (i + 1) q.1 q.2 with _ | ⟨c', p'⟩ <;> rfl

theorem preAt_succ {E : Env} {F : Fun} {code : List OffsetInstruction} {i : ℕ} (hi : i < code.length) :
    preAt E F code (i + 1) = (preAt E F code i).bind fun S ↦ runCode E F [code[i]] i S.1 S.2 := by
  unfold preAt
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, runCode_append,
    List.length_take, Nat.zero_add, Nat.min_eq_left hi.le]

theorem preAt_isSome {E : Env} {F : Fun} {code : List OffsetInstruction} (hw : walk E F code = true)
    (i : ℕ) : ∃ S, preAt E F code i = some S := by
  unfold walk at hw
  split at hw
  · rename_i S0 e
    rw [← List.take_append_drop i code, runCode_append] at e
    obtain ⟨S, hS, -⟩ := Option.bind_eq_some_iff.mp e
    exact ⟨S, hS⟩
  · cases hw

theorem preAt_ok {E : Env} {F : Fun} {code : List OffsetInstruction} :
    ∀ {i : ℕ} {cur : List Abs} {pend : Pend}, i ≤ code.length → preAt E F code i = some (cur, pend) →
      PendOk pend i
  | 0, cur, pend, _, h => by
    simp only [preAt, List.take_zero, runCode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fun _ h ↦ absurd h List.not_mem_nil
  | i + 1, cur, pend, hi, h => by
    rw [preAt_succ (by omega)] at h
    obtain ⟨⟨c0, p0⟩, h0, h⟩ := Option.bind_eq_some_iff.mp h
    have hP0 := preAt_ok (by omega) h0
    rw [runCode_one] at h
    obtain ⟨⟨c1, p1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hJ : PendOk (joinAt i c0 p0).2 (i + 1) := by rw [joinAt_pend]; exact popAt_ok hP0
    exact (cutAt_spec h).2.2 (stepAll_spec h1 hJ).2.1

theorem preAt_end {E : Env} {F : Fun} {code : List OffsetInstruction} (hw : walk E F code = true)
    {i : ℕ} (hi : code.length ≤ i) {cur : List Abs} {pend : Pend}
    (h : preAt E F code i = some (cur, pend)) : pend = [] := by
  unfold walk at hw
  unfold preAt at h
  rw [List.take_of_length_le hi] at h
  rw [h] at hw
  exact List.isEmpty_iff.mp hw

/-- **A pending edge survives** to its target. -/
theorem cov_forward {E : Env} {F : Fun} {code : List OffsetInstruction} (hw : walk E F code = true)
    {s : St} {j : ℕ} : ∀ (d i : ℕ) {cur : List Abs} {pend : Pend}, i + d = j →
      preAt E F code i = some (cur, pend) → Cov s pend j → AtOff E F code j s
  | 0, i, cur, pend, hd, h, hc => by
    rw [Nat.add_zero] at hd; subst hd
    exact ⟨cur, pend, h, Or.inr hc⟩
  | d + 1, i, cur, pend, hd, h, hc => by
    by_cases hi : i < code.length
    · obtain ⟨⟨c2, p2⟩, h2⟩ := preAt_isSome hw (i + 1)
      have h2' := h2
      rw [preAt_succ hi, h, Option.bind_some, runCode_one] at h2'
      obtain ⟨⟨c1, p1⟩, h1, h3⟩ := Option.bind_eq_some_iff.mp h2'
      have hJ : PendOk (joinAt i cur pend).2 (i + 1) := by
        rw [joinAt_pend]; exact popAt_ok (preAt_ok (by omega) h)
      have hc1 : Cov s (joinAt i cur pend).2 j := by
        rw [joinAt_pend]; exact popAt_keep (by omega) hc
      have hc2 := (cutAt_spec h3).2.1 s j ((stepAll_spec h1 hJ).1 s j hc1)
      exact cov_forward hw d (i + 1) (by omega) h2 hc2
    · obtain ⟨G, hG, -⟩ := hc
      rw [preAt_end hw (by omega) h] at hG
      exact absurd hG List.not_mem_nil

/-- **The entry**: the state the walk starts from holds at offset `0`. -/
theorem atOff_zero {E : Env} {F : Fun} {code : List OffsetInstruction} {s : St}
    (h : Holds s (entryAbs E F.sig)) : AtOff E F code 0 s :=
  ⟨[entryAbs E F.sig], [], by simp [preAt, runCode], Or.inl ⟨_, List.mem_singleton_self _, h⟩⟩

/-- **One offset**: at an offset the walk accepts, a path holds and its step goes through; what falls
through holds at the next offset, and an edge the step adds holds at its target. -/
theorem atOff_step {E : Env} {F : Fun} {code : List OffsetInstruction} (hw : walk E F code = true)
    {i : ℕ} (hi : i < code.length) {s : St} (h : AtOff E F code i s) :
    ∃ A, Holds s A ∧ ∃ pa cs pb, offStep E F i A code[i] pa = some (cs, pb) ∧ PendOk pa (i + 1) ∧
      (∀ s', (∃ X ∈ cs, Holds s' X) → AtOff E F code (i + 1) s') ∧
      ∀ s' j, Cov s' pb j → AtOff E F code j s' := by
  obtain ⟨cur, pend, h0, hh⟩ := h
  obtain ⟨⟨c2, p2⟩, h2⟩ := preAt_isSome hw (i + 1)
  have h2' := h2
  rw [preAt_succ hi, h0, Option.bind_some, runCode_one] at h2'
  obtain ⟨⟨c1, p1⟩, h1, h3⟩ := Option.bind_eq_some_iff.mp h2'
  have hP := preAt_ok (by omega) h0
  have hJ : PendOk (joinAt i cur pend).2 (i + 1) := by rw [joinAt_pend]; exact popAt_ok hP
  obtain ⟨A, hA, hH⟩ := joinAt_holds hP hh
  obtain ⟨-, -, hall⟩ := stepAll_spec h1 hJ
  obtain ⟨pa, cs, pb, e, hpa, hcs, hpb⟩ := hall A hA
  obtain ⟨hcut1, hcut2, -⟩ := cutAt_spec h3
  have hP2 := preAt_ok (by omega) h2
  refine ⟨A, hH, pa, cs, pb, e, hpa, fun s' ⟨X, hX, hHX⟩ ↦ ?_, fun s' j hc ↦ ?_⟩
  · exact ⟨c2, p2, h2, Or.inl (hcut1 s' ⟨X, hcs X hX, hHX⟩)⟩
  · have hc2 := hcut2 s' j (hpb s' j hc)
    obtain ⟨G, hG, hjG, -⟩ := id hc2
    have hij := (hP2 G hG).2 j hjG
    exact cov_forward hw (j - (i + 1)) (i + 1) (by omega) h2 hc2

end

end LeanVM.Guest.Mode
