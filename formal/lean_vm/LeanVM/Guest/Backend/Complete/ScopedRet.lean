/-
  LeanVM.Guest.Backend.Complete.ScopedRet

  A scoped function's return areas fit its return cells.
-/

module

public import LeanVM.Guest.Backend.Complete.Scoped

/-!
# Return areas of a scoped function

`scopedE` reads the whole trace, and `flushS` refuses a return area longer than the return cells,
so every return area of a scoped function's trace fits (`scoped_retShort`). The walk only ever
drops a prefix of the trace whose return areas fit (`Cons`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Guest.Core

@[expose] public section

/-- The trace `r'` is what is left of `r` after a prefix whose return areas fit `rc` cells. -/
def Cons (rc : ℕ) (r r' : List Event) : Prop :=
  ∃ pre, r = pre ++ r' ∧ ∀ vs : List V, Event.alloc vs .ret ∈ pre → vs.length ≤ rc

theorem Cons.refl (rc : ℕ) (r : List Event) : Cons rc r r := ⟨[], rfl, fun _ h => nomatch h⟩

theorem Cons.trans {rc : ℕ} {r r' r'' : List Event} (h₁ : Cons rc r r') (h₂ : Cons rc r' r'') :
    Cons rc r r'' := by
  obtain ⟨p₁, rfl, hp₁⟩ := h₁
  obtain ⟨p₂, rfl, hp₂⟩ := h₂
  refine ⟨p₁ ++ p₂, by rw [List.append_assoc], fun vs h => ?_⟩
  rcases List.mem_append.mp h with h | h
  · exact hp₁ vs h
  · exact hp₂ vs h

theorem Cons.cons {rc : ℕ} {e : Event} {r r' : List Event} (he : ∀ vs, e ≠ .alloc vs .ret)
    (h : Cons rc r r') : Cons rc (e :: r) r' := by
  obtain ⟨p, rfl, hp⟩ := h
  refine ⟨e :: p, rfl, fun vs hm => ?_⟩
  rcases List.mem_cons.mp hm with hm | hm
  · exact absurd hm.symm (he vs)
  · exact hp vs hm

theorem except_bind_inv {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem flushS_cons (rc : ℕ) : ∀ (r : List Event) (live : VMap Unit) (b : Bool) (s' : SSt),
    flushS rc r live b = .ok s' → Cons rc r s'.rest
  | [], _, _, s', h => by
      simp only [flushS] at h
      cases h
      exact Cons.refl _ _
  | e :: es, live, b, s', h => by
      simp only [flushS] at h
      split at h
      · next vs kind =>
        split at h
        · next hk =>
          have hk' : kind = .ret := by simpa using hk
          subst hk'
          split at h
          · cases h
          · split at h
            · cases h
            · next hlt =>
              obtain ⟨p, hp, hpp⟩ := flushS_cons rc es _ _ s' h
              refine ⟨Event.alloc vs .ret :: p, by rw [hp]; rfl, fun vs' hm => ?_⟩
              rcases List.mem_cons.mp hm with hm | hm
              · cases hm; omega
              · exact hpp vs' hm
        · next hk =>
          refine Cons.cons (fun vs' he => ?_) (flushS_cons rc es _ _ s' h)
          cases he
          exact hk rfl
      · split at h
        · exact Cons.cons (fun _ he => nomatch he) (flushS_cons rc es _ _ s' h)
        · cases h
      · split at h
        · exact Cons.cons (fun _ he => nomatch he) (flushS_cons rc es _ _ s' h)
        · cases h
      · exact Cons.cons (fun _ he => nomatch he) (flushS_cons rc es _ _ s' h)
      · exact Cons.cons (fun _ he => nomatch he) (flushS_cons rc es _ _ s' h)
      · cases h
        exact Cons.refl _ _

theorem flushAt_cons {rc : ℕ} {s s' : SSt} (h : flushAt rc s = .ok s') : Cons rc s.rest s'.rest :=
  flushS_cons rc _ _ _ s' h

/-- The events `expectS` passes are no allocation. -/
def NoAlloc (e : Event → Bool) : Prop := ∀ vs k, e (.alloc vs k) = false

theorem expectS_cons {rc : ℕ} {e : Event → Bool} {what : String} {s s' : SSt} (he : NoAlloc e)
    (h : expectS e what s = .ok s') : Cons rc s.rest s'.rest := by
  unfold expectS at h
  split at h
  · next ev es hr =>
    split at h
    · next hev =>
      cases h
      rw [hr]
      refine Cons.cons (fun vs h' => ?_) (Cons.refl _ _)
      subst h'
      rw [he] at hev
      cases hev
    · cases h
  · cases h

theorem noAlloc_emit : NoAlloc isEmit := fun _ _ => rfl
theorem noAlloc_enter : NoAlloc isEnter := fun _ _ => rfl
theorem noAlloc_leave : NoAlloc isLeave := fun _ _ => rfl

theorem scopeInner_cons {rc : ℕ} {blk : SSt → Except String SSt}
    (hb : ∀ s s', blk s = .ok s' → Cons rc s.rest s'.rest) {s s' : SSt}
    (h : scopeInner rc blk s = .ok s') : Cons rc s.rest s'.rest := by
  unfold scopeInner at h
  split at h
  · cases h
  · next s₁ h₁ =>
    split at h
    · cases h
    · next s₂ h₂ =>
      split at h
      · cases h
      · next s₃ h₃ =>
        split at h
        · cases h
        · next s₄ h₄ =>
          cases h
          exact (expectS_cons noAlloc_enter h₁).trans ((hb _ _ h₂).trans
            ((flushAt_cons h₃).trans (expectS_cons (s' := s₄) noAlloc_leave h₄)))

theorem scopeFlat_cons {rc : ℕ} {st : Stmt} {s s' : SSt} (h : scopeFlat rc st s = .ok s') :
    Cons rc s.rest s'.rest := by
  unfold scopeFlat at h
  split at h
  · cases h
  · next s₁ h₁ =>
    split at h
    · cases h
    · next s₂ h₂ =>
      split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact (flushAt_cons h₁).trans (expectS_cons noAlloc_emit h₂)

theorem scopeIteTail_cons {rc : ℕ} {e : Bool} {nz : SSt → Except String SSt} {b : Bool}
    (hnz : ∀ s s', nz s = .ok s' → Cons rc s.rest s'.rest) {s s' : SSt}
    (h : scopeIteTail e nz b s = .ok s') : Cons rc s.rest s'.rest := by
  unfold scopeIteTail at h
  split at h
  · split at h
    · cases h
    · next s₂ h₂ =>
      exact (hnz _ _ h₂).trans (expectS_cons
        (s := { s₂ with retDone := s.retDone || s₂.retDone }) noAlloc_emit h)
  · split at h
    · cases h
    · exact expectS_cons noAlloc_emit h

mutual
theorem scopeBlock_cons (rc : ℕ) : ∀ (ss : List Stmt) (s s' : SSt), scopeBlock rc ss s = .ok s' →
    Cons rc s.rest s'.rest
  | [], s, s', h => by
      simp only [scopeBlock] at h
      cases h
      exact Cons.refl _ _
  | st :: rest, s, s', h => by
      simp only [scopeBlock] at h
      split at h
      · cases h
      · next s₁ h₁ => exact (scopeStmt_cons rc st s s₁ h₁).trans (scopeBlock_cons rc rest s₁ s' h)

theorem scopeStmt_cons (rc : ℕ) : ∀ (st : Stmt) (s s' : SSt), scopeStmt rc st s = .ok s' →
    Cons rc s.rest s'.rest
  | .ite c z nz, s, s', h => by
      simp only [scopeStmt] at h
      split at h
      · cases h
      · next s₀ h₀ =>
        split at h
        · cases h
        · split at h
          · cases h
          · next s₁ h₁ =>
            exact (flushAt_cons h₀).trans ((scopeInner_cons (scopeBlock_cons rc z) h₁).trans
              (scopeIteTail_cons (fun _ _ h' => scopeInner_cons (scopeBlock_cons rc nz) h') h))
  | .match_ x arms, s, s', h => by
      simp only [scopeStmt] at h
      split at h
      · cases h
      · next s₀ h₀ =>
        split at h
        · cases h
        · split at h
          · cases h
          · next s₁ h₁ =>
            exact (flushAt_cons h₀).trans ((scopeArms_cons rc arms _ _ s₁ h₁).trans
              (expectS_cons noAlloc_emit h))
  | .atom _, s, s', h => scopeFlat_cons h
  | .call .., s, s', h => scopeFlat_cons h
  | .callIf .., s, s', h => scopeFlat_cons h
  | .dispatch .., s, s', h => scopeFlat_cons h
  | .ret _, s, s', h => scopeFlat_cons h

theorem scopeArms_cons (rc : ℕ) : ∀ (arms : List (List Stmt)) (s : SSt) (acc : Bool) (s' : SSt),
    scopeArms rc arms s acc = .ok s' → Cons rc s.rest s'.rest
  | [], s, acc, s', h => by
      simp only [scopeArms] at h
      cases h
      exact Cons.refl _ _
  | arm :: more, s, acc, s', h => by
      simp only [scopeArms] at h
      split at h
      · cases h
      · next s₁ h₁ =>
        exact (scopeInner_cons (scopeBlock_cons rc arm) h₁).trans
          (scopeArms_cons rc more { s₁ with retDone := s.retDone } _ s' h)
end

/-- **A scoped function's return areas fit its return cells.** -/
theorem scoped_retShort {tf : TracedFn} (h : Scoped tf) :
    ∀ vs : List V, Event.alloc vs .ret ∈ tf.trace.toList → vs.length ≤ tf.rets := by
  unfold Scoped scopedB at h
  split at h
  · next he =>
    unfold scopedE at he
    split at he
    · cases he
    · next s₁ h₁ =>
      split at he
      · cases he
      · next s₂ h₂ =>
        split at he
        · next hemp =>
          obtain ⟨p, hp, hpp⟩ := (scopeBlock_cons _ _ _ _ h₁).trans (flushAt_cons h₂)
          intro vs hm
          have hr : s₂.rest = [] := by simpa using hemp
          rw [hr, List.append_nil] at hp
          exact hpp vs (hp ▸ hm)
        · cases he
  · cases h

end
end LeanVM.Guest.Backend.Complete
