module

public import Common.Indiff.InvMain
public import Common.Indiff.Proj

@[expose] public section

/-!
# Indifferentiability: postponing the sponge's path queries

The visible game with the sponge's path queries (`visImpl P iv true`) and without them
(`visImpl P iv false`) give the same joint distribution of output, visible state and final
random-oracle cache, once both are followed by the *end phase* (`endPhase`): the path queries of
every hashed message, made after the distinguisher stops (`visRun_true_evalDistEq_false`). The
path queries' answers are never used, and random-oracle queries commute
(`run_bind_bind_comm`); after the end phase the postponed queries are cache hits. Without the
path queries, the values of hidden paths are first drawn in the end phase, fresh: this is what
the hidden-collision bound uses.
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

/-- The end phase: the sponge's path queries for every hashed message. -/
noncomputable def endPhase : List Msg → OracleComp (unifSpec + aSpec Msg Dg E C) Unit
  | [] => pure ()
  | m :: ms => do
    skel (C := C) P [] (P.pad m)
    endPhase ms

/-- The visible game followed by the end phase. -/
noncomputable def visRun (pre : Bool) {α : Type}
    (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) (vs : VState Dg E C Msg) :
    OracleComp (unifSpec + aSpec Msg Dg E C) (α × VState Dg E C Msg) :=
  (simulateQ (visImpl P iv pre) oa).run vs >>= fun z ↦ endPhase P z.2.2.1 >>= fun _ ↦ pure z

/-- The path queries cache the values of all their paths, and keep the cache. -/
theorem skel_support (pre bs : List (Dg × E)) (c : ACache Msg Dg E C)
    {z : Unit × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl (skel (C := C) P pre bs)).run c)) :
    c ≤ z.2 ∧ ∀ i < bs.length, valC P z.2 (pre ++ bs.take (i + 1)) ≠ none := by
  rw [← map_allWalk (Msg := Msg) P (fun _ ↦ false) pre (Classical.arbitrary _) [] bs, simulateQ_map,
    StateT.run_map] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨h1, h2, -⟩ := allWalk_support P _ pre _ [] bs c hw
  exact ⟨h1, h2⟩

/-- Path queries at cached paths change nothing. -/
theorem skel_run_of_cached (pre bs : List (Dg × E)) (c : ACache Msg Dg E C)
    (h : ∀ i < bs.length, valC P c (pre ++ bs.take (i + 1)) ≠ none) :
    (simulateQ (aSpec Msg Dg E C).romImpl (skel (C := C) P pre bs)).run c =ᵈ
      (pure ((), c) : ProbComp (Unit × ACache Msg Dg E C)) := by
  induction bs generalizing pre with
  | nil => simp [skel]
  | cons B bs ih =>
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (h 0 (by simp))
    simp only [List.take_succ_cons, List.take_zero] at hv
    simp only [skel, simulateQ_bind, StateT.run_bind, val_run_of_valC P _ c hv, pure_bind,
      drawSt_run, bind_map_left]
    refine (EvalDistEq.bind_right _ fun u ↦ ih (pre ++ [B]) fun i hi ↦ ?_).trans ?_
    · simpa [List.take_succ_cons] using h (i + 1) (by simp; omega)
    · exact EvalDistEq.bind_const _ _

/-- After the end phase, the values of all paths of the hashed messages are cached. -/
theorem endPhase_support (ms : List Msg) (c : ACache Msg Dg E C)
    {z : Unit × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl (endPhase (C := C) P ms)).run c)) :
    c ≤ z.2 ∧ ∀ m ∈ ms, ∀ i < (P.pad m).length, valC P z.2 ((P.pad m).take (i + 1)) ≠ none := by
  induction ms generalizing c with
  | nil =>
    simp only [endPhase, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact ⟨le_rfl, by simp⟩
  | cons m ms ih =>
    simp only [endPhase, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨h1, h2⟩ := skel_support P [] (P.pad m) c hw
    obtain ⟨h3, h4⟩ := ih w.2 hz
    refine ⟨le_trans h1 h3, fun m' hm' i hi ↦ ?_⟩
    rcases List.mem_cons.mp hm' with rfl | hm'
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (h2 i hi)
      simp only [List.nil_append] at hv
      rw [valC_mono P h3 hv]; simp
    · exact h4 m' hm' i hi

/-- Hashed messages are never forgotten by the visible game. -/
theorem visImpl_hashed_mono (pre : Bool) {α : Type}
    (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) (vs : VState Dg E C Msg) (m : Msg)
    (hm : m ∈ vs.2.1) {z : α × VState Dg E C Msg}
    (hz : z ∈ support ((simulateQ (visImpl P iv pre) oa).run vs)) : m ∈ z.2.2.1 := by
  refine inv_of_mem_support_run (spec' := unifSpec + aSpec Msg Dg E C) (visImpl P iv pre)
    (fun vs ↦ m ∈ vs.2.1) (fun t s hs z hz ↦ ?_) oa hm z hz
  rcases t with n | m' | x | y
  · simp only [visImpl] at hz
    rw [StateT.run_monadLift] at hz
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · simp only [visImpl, StateT.run_mk] at hz
    split at hz
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨-, -, d, -, rfl⟩ := hz
      exact List.mem_cons_of_mem _ hs
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨d, -, rfl⟩ := hz
      exact List.mem_cons_of_mem _ hs
  · simp only [visImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, r, -, rfl⟩ := hz
    exact hs
  · simp only [visImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs

/-- An output reachable in the random oracle model is reachable with arbitrary answers. -/
theorem fst_mem_support_of_mem_support_run {β : Type}
    {X : OracleComp (unifSpec + aSpec Msg Dg E C) β} {c : ACache Msg Dg E C}
    {z : β × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (aSpec Msg Dg E C).romImpl X).run c)) : z.1 ∈ support X :=
  support_simulateQ_run'_subset (aSpec Msg Dg E C).romImpl X c (by
    rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)

/-- The visible game's hash step with path queries is the path queries, then the step without. -/
theorem visImpl_true_hash (m : Msg) (vs : VState Dg E C Msg) :
    (visImpl P iv true (.inr (.inl m))).run vs =
      (skel (C := C) P [] (P.pad m) >>= fun _ ↦ (visImpl P iv false (.inr (.inl m))).run vs) := by
  simp [visImpl]

/-- The visible game's hash step records the message. -/
theorem visImpl_hash_support (pre : Bool) (m : Msg) (vs : VState Dg E C Msg)
    {z : Dg × VState Dg E C Msg} (hz : z ∈ support ((visImpl P iv pre (.inr (.inl m))).run vs)) :
    z.2.2.1 = m :: vs.2.1 := by
  simp only [visImpl, StateT.run_mk] at hz
  split at hz
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨-, -, d, -, rfl⟩ := hz
    rfl
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨d, -, rfl⟩ := hz
    rfl

/-- A visible-game run with its end phase. -/
theorem visRun_query_bind (pre : Bool) {α : Type}
    (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (k : (dSpec Msg Dg (SpState Dg E C)).Range t → OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (vs : VState Dg E C Msg) :
    visRun P iv pre ((liftM ((dSpec Msg Dg (SpState Dg E C)).query t) :
      OracleComp (dSpec Msg Dg (SpState Dg E C)) _) >>= k) vs =
      ((visImpl P iv pre t).run vs >>= fun p ↦ visRun P iv pre (k p.1) p.2) := by
  simp [visRun, simulateQ_bind, StateT.run_bind, bind_assoc]

/-- **Postponing the path queries.** With its end phase, the visible game with the sponge's path
queries gives the joint distribution of output, visible state and cache of the visible game
without them. -/
theorem visRun_true_evalDistEq_false {α : Type}
    (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    (simulateQ (aSpec Msg Dg E C).romImpl (visRun P iv true oa vs)).run c =ᵈ
      (simulateQ (aSpec Msg Dg E C).romImpl (visRun P iv false oa vs)).run c := by
  induction oa using OracleComp.inductionOn generalizing vs c with
  | pure a => simp [visRun]
  | query_bind t k ih =>
    rw [visRun_query_bind, visRun_query_bind]
    rcases t with n | m | x | y
    · simp only [simulateQ_bind, StateT.run_bind]
      exact EvalDistEq.bind_right _ fun p ↦ ih p.1.1 p.1.2 p.2
    · rw [visImpl_true_hash, bind_assoc]
      set Y := ((visImpl P iv false (.inr (.inl m))).run vs >>= fun p ↦
        visRun P iv false (k p.1) p.2) with hY
      calc (simulateQ (aSpec Msg Dg E C).romImpl (skel (C := C) P [] (P.pad m) >>= fun _ ↦
            (visImpl P iv false (.inr (.inl m))).run vs >>= fun p ↦
              visRun P iv true (k p.1) p.2)).run c
          =ᵈ (simulateQ (aSpec Msg Dg E C).romImpl (skel (C := C) P [] (P.pad m) >>= fun _ ↦
            Y >>= fun r ↦ pure r)).run c := by
            simp only [hY, bind_pure, simulateQ_bind, StateT.run_bind]
            exact EvalDistEq.bind_right _ fun w ↦ EvalDistEq.bind_right _ fun p ↦
              ih p.1.1 p.1.2 p.2
        _ =ᵈ (simulateQ (aSpec Msg Dg E C).romImpl (Y >>= fun r ↦
            skel (C := C) P [] (P.pad m) >>= fun _ ↦ pure r)).run c :=
            run_bind_bind_comm _ Y (fun _ r ↦ pure r) c
        _ =ᵈ (simulateQ (aSpec Msg Dg E C).romImpl Y).run c := by
            simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
            conv_rhs => rw [← bind_pure ((simulateQ (aSpec Msg Dg E C).romImpl Y).run c)]
            refine EvalDistEq.bind_congr_of_support _ fun z hz ↦ ?_
            -- after the end phase, the postponed path queries are cache hits
            have hcached : ∀ i < (P.pad m).length,
                valC P z.2 ([] ++ (P.pad m).take (i + 1)) ≠ none := by
              intro i hi
              simp only [hY, visRun, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
                simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              obtain ⟨p, hp, w, hw, e, he, rfl⟩ := hz
              have hpm := visImpl_hash_support P iv false m vs
                (fst_mem_support_of_mem_support_run hp)
              have hwm := visImpl_hashed_mono P iv false (k p.1.1) p.1.2 m
                (by rw [hpm]; exact List.mem_cons_self) (fst_mem_support_of_mem_support_run hw)
              simpa using (endPhase_support P w.1.2.2.1 w.2 he).2 m hwm i hi
            refine (EvalDistEq.bind_left (skel_run_of_cached P [] (P.pad m) z.2 hcached)
              _).trans ?_
            simp
    · simp only [simulateQ_bind, StateT.run_bind]
      exact EvalDistEq.bind_right _ fun p ↦ ih p.1.1 p.1.2 p.2
    · simp only [simulateQ_bind, StateT.run_bind]
      exact EvalDistEq.bind_right _ fun p ↦ ih p.1.1 p.1.2 p.2

end Setting

end Common
