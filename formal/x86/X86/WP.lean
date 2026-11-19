module

public import X86.QM

/-!
# A program logic for the x86 subset

`WP c s P E`: run from `s`, the statement `c` ends, normally in a state satisfying `P` or at the
failure exit in a state satisfying `E`. It is `Exec` with a postcondition, so a proof of it is a
run that does not get stuck (every load and store inside `QState.mem`) and terminates (each loop
by a variant).
-/

@[expose] public section

namespace X86

/-- `c` run from `s` ends in `P` (normally) or `E` (failed). -/
def WP (c : Stmt) (s : QState) (P E : QState → Prop) : Prop :=
  ∃ o, Exec c s o ∧ match o with
    | .ok s' => P s'
    | .err s' => E s'

namespace WP

variable {P E P' E' : QState → Prop} {s : QState}

theorem mono {c : Stmt} (h : WP c s P E) (hP : ∀ s, P s → P' s) (hE : ∀ s, E s → E' s) :
    WP c s P' E' := by
  obtain ⟨o, hx, ho⟩ := h
  refine ⟨o, hx, ?_⟩
  cases o <;> simp_all

theorem skip (h : P s) : WP .skip s P E := ⟨_, .skip s, h⟩

theorem ins {i : QInstr} {s' : QState} (hs : i.step s = some s') (h : P s') : WP (.ins i) s P E :=
  ⟨_, .ins hs, h⟩

/-- An instruction, its result computed by `QInstr.step`. -/
theorem ins' {i : QInstr} (h : match i.step s with | some s' => P s' | none => False) :
    WP (.ins i) s P E := by
  cases hs : i.step s with
  | none => rw [hs] at h; exact h.elim
  | some s' => rw [hs] at h; exact ins hs h

theorem fail (h : E s) : WP .fail s P E := ⟨_, .fail s, h⟩

theorem seq {a b : Stmt} (h : WP a s (fun s₁ ↦ WP b s₁ P E) E) : WP (.seq a b) s P E := by
  obtain ⟨o, hx, ho⟩ := h
  cases o with
  | ok s₁ =>
    obtain ⟨o', hx', ho'⟩ := ho
    exact ⟨o', .seqOk hx hx', ho'⟩
  | err s₁ => exact ⟨_, .seqErr hx, ho⟩

theorem ite {c : Cond} {t e : Stmt}
    (h : if c.eval s then WP t s P E else WP e s P E) : WP (.ite c t e) s P E := by
  cases hc : c.eval s
  · rw [hc] at h
    obtain ⟨o, hx, ho⟩ := h
    exact ⟨o, .iteFalse hc hx, ho⟩
  · rw [hc] at h
    obtain ⟨o, hx, ho⟩ := h
    exact ⟨o, .iteTrue hc hx, ho⟩

theorem blk_nil (h : P s) : WP (blk []) s P E := skip h

theorem blk_cons {x : Stmt} {xs : List Stmt}
    (h : WP x s (fun s₁ ↦ WP (blk xs) s₁ P E) E) : WP (blk (x :: xs)) s P E := by
  cases xs with
  | nil =>
    refine mono h (fun s₁ h₁ ↦ ?_) (fun _ h ↦ h)
    obtain ⟨o, hx, ho⟩ := h₁
    cases hx
    exact ho
  | cons y ys => exact seq h

/-- A loop, by an invariant `I` and a variant `μ` that every pass of the body decreases. -/
theorem loop {c : Cond} {b : Stmt} (I : QState → Prop) (μ : QState → Nat) (h0 : I s)
    (hstep : ∀ s, I s → c.eval s = true → WP b s (fun s₁ ↦ I s₁ ∧ μ s₁ < μ s) E)
    (hexit : ∀ s, I s → c.eval s = false → P s) : WP (.loop c b) s P E := by
  induction h : μ s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    cases hc : c.eval s
    · exact ⟨_, .loopFalse hc, hexit s h0 hc⟩
    · obtain ⟨o, hx, ho⟩ := hstep s h0 hc
      cases o with
      | ok s₁ =>
        obtain ⟨hI, hμ⟩ := ho
        obtain ⟨o', hx', ho'⟩ := ih (μ s₁) (h ▸ hμ) hI rfl
        exact ⟨o', .loopTrue hc hx hx', ho'⟩
      | err s₁ => exact ⟨_, .loopErr hc hx, ho⟩

end WP

/-- `Exec` is deterministic. -/
theorem Exec.det {c : Stmt} {s : QState} {o o' : Outcome} (h : Exec c s o) (h' : Exec c s o') :
    o = o' := by
  induction h generalizing o' with
  | skip => cases h'; rfl
  | ins hs => cases h' with | ins hs' => rw [hs] at hs'; cases hs'; rfl
  | seqOk _ _ ih1 ih2 =>
    cases h' with
    | seqOk h1 h2 => cases ih1 h1; exact ih2 h2
    | seqErr h1 => cases ih1 h1
  | seqErr _ ih1 =>
    cases h' with
    | seqOk h1 _ => cases ih1 h1
    | seqErr h1 => exact ih1 h1
  | iteTrue hc _ ih =>
    cases h' with
    | iteTrue _ h => exact ih h
    | iteFalse hc' _ => rw [hc] at hc'; cases hc'
  | iteFalse hc _ ih =>
    cases h' with
    | iteTrue hc' _ => rw [hc] at hc'; cases hc'
    | iteFalse _ h => exact ih h
  | loopTrue hc _ _ ih1 ih2 =>
    cases h' with
    | loopTrue _ h1 h2 => cases ih1 h1; exact ih2 h2
    | loopErr _ h1 => cases ih1 h1
    | loopFalse hc' => rw [hc] at hc'; cases hc'
  | loopErr hc _ ih1 =>
    cases h' with
    | loopTrue _ h1 _ => cases ih1 h1
    | loopErr _ h1 => exact ih1 h1
    | loopFalse hc' => rw [hc] at hc'; cases hc'
  | loopFalse hc =>
    cases h' with
    | loopTrue hc' _ _ => rw [hc] at hc'; cases hc'
    | loopErr hc' _ => rw [hc] at hc'; cases hc'
    | loopFalse _ => rfl
  | fail => cases h'; rfl

/-! ## Registers and memory after an update -/

@[simp] theorem QState.setReg_reg (s : QState) (r : Reg64) (v : UInt64) (r' : Reg64) :
    (s.setReg r v).reg r' = if r' = r then v else s.reg r' := by
  simp [QState.setReg, Function.update_apply]

@[simp] theorem QState.setReg_mem (s : QState) (r : Reg64) (v : UInt64) :
    (s.setReg r v).mem = s.mem := rfl

@[simp] theorem QState.setMem_reg (s : QState) (a v : UInt64) : (s.setMem a v).reg = s.reg := rfl

@[simp] theorem QState.setMem_mem (s : QState) (a v : UInt64) (a' : UInt64) :
    (s.setMem a v).mem a' = if a' = a then some v else s.mem a' := by
  simp [QState.setMem, Function.update_apply]

end X86
