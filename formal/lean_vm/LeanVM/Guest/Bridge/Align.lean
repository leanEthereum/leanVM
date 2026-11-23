/-
  LeanVM.Guest.Bridge.Align

  What the alignment check gives: a function passing it is at its body at offset `0`, the start the tree track against the run needs.
-/

module

public import LeanVM.Guest.Bridge.AlignRun

/-!
# The alignment check's facts

`alignAt_zero`: on a function passing `alignOk`, the body position at offset `0` is the body, so `refOk_init` applies with the alignment `alignAt` (by name). The pass records each offset it reaches once, at the offset it is at (`stepI_rec`, `alignGo_rec`), so the record of offset `0`, the body's start, is found past the later ones. `posOf_nil`: a cursor at the top level names the body's rest.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Core
open LeanVM.Guest.Exec (natSeq_eq)

public section

theorem posOf_nil (body : List Stmt) (k : ℕ) : posOf body [] k = body.drop k := rfl

/-- A step records at most its own offset. -/
theorem stepI_rec (X : AlignCtx) (ins : OffsetInstruction) {st : St} {r : St × Option (ℕ × Zip)}
    (h : stepI X ins st = some r) : ∀ e ∈ r.2, e.1 = st.i := by
  unfold stepI at h
  rw [natSeq_eq] at h
  generalize spanP st.i st.pend = S at h
  generalize hintsAt (Nat.add X.entry st.i) st.hs = H at h
  obtain ⟨here, rest⟩ := S
  obtain ⟨h1, hs'⟩ := H
  simp only [Bool.cond_eq_ite] at h
  have hv : ∀ c, visit X ins st.i st.i.succ h1 hs' rest st.tabs c = some r → ∀ e ∈ r.2, e.1 = st.i := by
    intro c hc
    simp only [visit] at hc
    obtain ⟨z, -, hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simp
  split at h
  · split at h
    · exact hv _ h
    · cases h
  · cases h; simp
  · split at h
    · exact hv _ h
    · cases h

/-- The pass records the offsets it reaches, from the state's on, before what it had recorded. -/
theorem alignGo_rec (X : AlignCtx) : ∀ (c : List OffsetInstruction) {st st' : St} {acc acc' : List (ℕ × Zip)},
    alignGo X c st acc = some (st', acc') → ∃ l, acc' = l ++ acc ∧ ∀ e ∈ l, st.i ≤ e.1
  | [], _, _, _, _, h => by
    simp only [alignGo, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by rw [h.2]; rfl, by simp⟩
  | ins :: c, st, st', acc, acc', h => by
    rw [alignGo_cons] at h
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
    have hi : p.1.i = st.i + 1 := by
      unfold stepI at hp
      rw [natSeq_eq] at hp
      generalize spanP st.i st.pend = S at hp
      generalize hintsAt (Nat.add X.entry st.i) st.hs = H at hp
      obtain ⟨here, rest⟩ := S
      obtain ⟨h1, hs'⟩ := H
      simp only [Bool.cond_eq_ite] at hp
      have hv : ∀ c, visit X ins st.i st.i.succ h1 hs' rest st.tabs c = some p → p.1.i = st.i + 1 := by
        intro c hc
        simp only [visit] at hc
        obtain ⟨z, -, hc⟩ := Option.bind_eq_some_iff.mp hc
        obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hc
        rfl
      split at hp
      · split at hp
        · exact hv _ hp
        · cases hp
      · cases hp; rfl
      · split at hp
        · exact hv _ hp
        · cases hp
    obtain ⟨l, rfl, hl⟩ := alignGo_rec X c h
    refine ⟨l ++ p.2.toList, by rw [List.append_assoc], fun e he ↦ ?_⟩
    rcases List.mem_append.mp he with he | he
    · have := hl e he; omega
    · rw [stepI_rec X ins hp e (Option.mem_toList.mp he)]

/-- **Offset `0` is the body.** -/
theorem alignAt_zero {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : alignOk X body code d = true) :
    alignAt X body code d 0 = some body := by
  rw [alignOk, AlignCtx.seq_eq] at h
  change (alignPre X d && (alignRun X body code d).isSome) = true at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp h.2
  cases code with
  | nil => simp [alignRun, alignGo, alignEnd, Zip.init] at hres
  | cons ins code =>
    simp only [alignRun] at hres
    obtain ⟨⟨st', acc'⟩, hgo, hend⟩ := Option.bind_eq_some_iff.mp hres
    rw [alignGo_cons] at hgo
    obtain ⟨p, hp, hgo⟩ := Option.bind_eq_some_iff.mp hgo
    obtain ⟨l, hl, hl0⟩ := alignGo_rec X code hgo
    have hi : p.1.i = 1 := (stepI_ok (body := body) (hs0 := d.2.2) X ins
      ⟨⟨0, rfl⟩, by simpa using zOk_init body, by simp, by simp⟩ hp).2
    have hp2 : p.2 = some (0, Zip.init body) := by
      unfold stepI at hp
      rw [natSeq_eq] at hp
      simp only [spanP, Bool.cond_eq_ite, allKey, List.all_nil, ite_true] at hp
      simp only [visit] at hp
      obtain ⟨z, -, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hp
      rfl
    have hacc : res = acc' := by
      simp only [alignEnd, Bool.cond_eq_ite] at hend
      split at hend
      · exact (Option.some.inj hend).symm
      · cases hend
    subst hacc
    rw [hp2] at hl
    simp only [Option.toList_some, List.append_nil] at hl
    subst hl
    have key : ∀ l : List (ℕ × Zip), (∀ e ∈ l, 1 ≤ e.1) →
        (l ++ [(0, Zip.init body)]).lookup 0 = some (Zip.init body) := by
      intro l hl
      induction l with
      | nil => simp
      | cons e l ih =>
        have he := hl e List.mem_cons_self
        simp only [List.cons_append, List.lookup, show (0 == e.1) = false from by simp; omega]
        exact ih fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')
    have hlook := key l fun e he ↦ hi ▸ hl0 e he
    simp only [alignAt]
    change ((alignRun X body (ins :: code) d).bind fun l ↦ l.lookup 0).map Zip.pos = some body
    simp only [alignRun]
    rw [hres, Option.bind_some, hlook]
    simp [Zip.pos, Zip.init]

end

end LeanVM.Guest.Bridge
