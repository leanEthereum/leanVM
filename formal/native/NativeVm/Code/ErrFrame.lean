module

public import NativeVm.Transcript

/-!
# What a gadget keeps when it fails

The transcript gadgets' specs (`NativeVm.Transcript`) say when a gadget fails, not what the failure
keeps; the failure exit needs it (it reads the saved registers through `rdi`). `ErrF c s F`: every
failed run of `c` from `s` ends in `F`. The gadgets fail only at checks made while `rdi` is at the
context (never inside `hashAt` or `permuteAt`, which move it), so each failure keeps what an
ordinary end keeps: `readScalar_err`, `grind_err`, `commit_err` give `Keeps clobbers (Foot env)`,
`finish_err` the whole memory.

Syntax does most of it: `canFail` (no `fail` inside), and `errKeep` (every failure happens before
the first store), with `Exec.reg_frame` for the registers. Where a gadget fails after it stored
(`grind`'s proof of work, `commit`'s second scalar), the states before are the specs' ordinary
ends, read off by determinism (`WP.ok_exec`). `WP.withErr` adds a failure frame to a spec.
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Transcript LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.Compile

/-! ## Syntax -/

/-- A store instruction. -/
def isStore : QInstr → Bool
  | .store _ _ | .storei _ _ => true
  | _ => false

/-- No store inside. -/
def storeFree : Stmt → Bool
  | .ins i => !isStore i
  | .seq a b | .ite _ a b => storeFree a && storeFree b
  | .loop _ b => storeFree b
  | .skip | .fail => true

/-- A `fail` inside. -/
def canFail : Stmt → Bool
  | .fail => true
  | .seq a b | .ite _ a b => canFail a || canFail b
  | .loop _ b => canFail b
  | .skip | .ins _ => false

/-- Every failure happens before the first store. -/
def errKeep : Stmt → Bool
  | .seq a b => errKeep a && (!canFail b || storeFree a && errKeep b)
  | .ite _ a b => errKeep a && errKeep b
  | .loop _ b => storeFree b || !canFail b
  | .skip | .ins _ | .fail => true

variable {c x y : Stmt} {xs : List Stmt} {s s' s₁ : QState} {o : Outcome}
  {P E F F' : QState → Prop}

theorem step_mem_of_not_store {i : QInstr} (hi : isStore i = false) (h : i.step s = some s') :
    s'.mem = s.mem := by
  cases i <;> first
    | (simp only [QInstr.step, Option.map_eq_some_iff, Option.some.injEq] at h
       first | (subst h; rfl) | (obtain ⟨v, -, rfl⟩ := h; rfl))
    | simp [isStore] at hi

theorem exec_storeFree (h : Exec c s o) (hc : storeFree c = true) : o.st.mem = s.mem := by
  induction h with
  | skip => rfl
  | ins hs => exact step_mem_of_not_store (by simpa [storeFree] using hc) hs
  | seqOk _ _ ih1 ih2 =>
    simp only [storeFree, Bool.and_eq_true] at hc
    exact (ih2 hc.2).trans (ih1 hc.1)
  | seqErr _ ih =>
    simp only [storeFree, Bool.and_eq_true] at hc
    exact ih hc.1
  | iteTrue _ _ ih =>
    simp only [storeFree, Bool.and_eq_true] at hc
    exact ih hc.1
  | iteFalse _ _ ih =>
    simp only [storeFree, Bool.and_eq_true] at hc
    exact ih hc.2
  | loopTrue _ _ _ ih1 ih2 => exact (ih2 hc).trans (ih1 hc)
  | loopErr _ _ ih => exact ih hc
  | loopFalse => rfl
  | fail => rfl

theorem exec_canFail (h : Exec c s o) : ∀ s', o = .err s' → canFail c = true := by
  induction h with
  | skip => intro _ e; cases e
  | ins _ => intro _ e; cases e
  | seqOk _ _ _ ih2 => intro s' e; simp [canFail, ih2 s' e]
  | seqErr _ ih => intro s' e; cases e; simp [canFail, ih _ rfl]
  | iteTrue _ _ ih => intro s' e; simp [canFail, ih s' e]
  | iteFalse _ _ ih => intro s' e; simp [canFail, ih s' e]
  | loopTrue _ _ _ _ ih2 => intro s' e; exact ih2 s' e
  | loopErr _ _ ih => intro s' e; cases e; exact ih _ rfl
  | loopFalse => intro _ e; cases e
  | fail => intro _ _; rfl

theorem exec_errKeep (h : Exec c s o) (hc : errKeep c = true) : ∀ s', o = .err s' → s'.mem = s.mem := by
  induction h with
  | skip => intro _ e; cases e
  | ins _ => intro _ e; cases e
  | seqOk ha hb _ ih2 =>
    intro s' e
    simp only [errKeep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
    rcases hc.2 with hf | ⟨hs, hk⟩
    · rw [exec_canFail hb s' e] at hf
      cases hf
    · exact (ih2 hk s' e).trans (exec_storeFree ha hs)
  | seqErr _ ih =>
    intro s' e
    cases e
    simp only [errKeep, Bool.and_eq_true] at hc
    exact ih hc.1 _ rfl
  | iteTrue _ _ ih =>
    intro s' e
    simp only [errKeep, Bool.and_eq_true] at hc
    exact ih hc.1 s' e
  | iteFalse _ _ ih =>
    intro s' e
    simp only [errKeep, Bool.and_eq_true] at hc
    exact ih hc.2 s' e
  | loopTrue _ hb hl _ ih2 =>
    intro s' e
    have hc' := hc
    simp only [errKeep, Bool.or_eq_true, Bool.not_eq_true'] at hc'
    rcases hc' with hs | hf
    · exact (ih2 hc s' e).trans (exec_storeFree hb hs)
    · have := exec_canFail hl s' e
      simp only [canFail] at this
      rw [hf] at this
      cases this
  | loopErr _ hb _ =>
    intro s' e
    cases e
    simp only [errKeep, Bool.or_eq_true, Bool.not_eq_true'] at hc
    rcases hc with hs | hf
    · exact exec_storeFree hb hs
    · rw [exec_canFail hb _ rfl] at hf
      cases hf
  | loopFalse => intro _ e; cases e
  | fail => intro s' e; cases e; rfl

/-! ## Failure frames -/

/-- **Every failed run of `c` from `s` ends in `F`.** -/
def ErrF (c : Stmt) (s : QState) (F : QState → Prop) : Prop := ∀ s', Exec c s (.err s') → F s'

theorem ErrF.mono (h : ErrF c s F) (hF : ∀ s', F s' → F' s') : ErrF c s F' :=
  fun s' hx ↦ hF s' (h s' hx)

theorem ErrF.of_canFail (hc : canFail c = false) : ErrF c s F := fun s' hx ↦ by
  have := exec_canFail hx s' rfl
  rw [hc] at this
  cases this

/-- A statement failing before it stores: the memory kept, and the registers it does not write. -/
theorem ErrF.syntax (hc : errKeep c = true) :
    ErrF c s fun s' ↦ s'.mem = s.mem ∧ ∀ r, c.writes r = false → s'.reg r = s.reg r :=
  fun s' hx ↦ ⟨exec_errKeep hx hc s' rfl, fun _ hr ↦ Exec.reg_frame hx hr⟩

theorem ErrF.of_wp (h : WP c s P E) (hE : ∀ s', E s' → F s') : ErrF c s F := fun s' hx ↦ by
  obtain ⟨o, hx', ho⟩ := h
  cases Exec.det hx hx'
  exact hE _ ho

/-- The ordinary end of a run, read off a spec. -/
theorem _root_.Native.WP.ok_exec (h : WP c s P E) (hx : Exec c s (.ok s₁)) : P s₁ := by
  obtain ⟨o, hx', ho⟩ := h
  cases Exec.det hx hx'
  exact ho

/-- **A spec with a failure frame.** -/
theorem _root_.Native.WP.withErr (h : WP c s P E) (hf : ErrF c s F) :
    WP c s P fun s' ↦ E s' ∧ F s' := by
  obtain ⟨o, hx, ho⟩ := h
  refine ⟨o, hx, ?_⟩
  cases o with
  | ok _ => exact ho
  | err s' => exact ⟨ho, hf s' hx⟩

theorem exec_blk_cons_err (h : Exec (blk (x :: xs)) s (.err s')) :
    Exec x s (.err s') ∨ ∃ s₁, Exec x s (.ok s₁) ∧ Exec (blk xs) s₁ (.err s') := by
  cases xs with
  | nil => exact .inl h
  | cons y ys =>
    change Exec (.seq x (blk (y :: ys))) s (.err s') at h
    cases h with
    | seqOk h1 h2 => exact .inr ⟨_, h1, h2⟩
    | seqErr h1 => exact .inl h1

theorem ErrF.blk_cons (hx : ErrF x s F) (hxs : ∀ s₁, Exec x s (.ok s₁) → ErrF (blk xs) s₁ F) :
    ErrF (blk (x :: xs)) s F := fun s' h ↦ by
  rcases exec_blk_cons_err h with h | ⟨s₁, h₁, h₂⟩
  · exact hx s' h
  · exact hxs s₁ h₁ s' h₂

/-- Two statements, the rest after their ordinary end. -/
theorem ErrF.blk_pair {rest : List Stmt} (hx : ErrF x s F)
    (hy : ∀ s₁, Exec x s (.ok s₁) → ErrF y s₁ F)
    (hr : ∀ s₂, Exec (blk [x, y]) s (.ok s₂) → ErrF (blk rest) s₂ F) :
    ErrF (blk (x :: y :: rest)) s F :=
  blk_cons hx fun s₁ h₁ ↦ blk_cons (hy s₁ h₁) fun s₂ h₂ ↦ hr s₂ (.seqOk h₁ h₂)

/-! ## `Keeps` -/

variable {env : Env} {st : VerifierProgramState}

theorem _root_.NativeVm.Transcript.Keeps.widen {rs : List Reg64} {W : UInt64 → Prop} (h : Keeps rs W s s')
    (hl : rs ⊆ clobbers := by simp [clobbers]) : Keeps clobbers W s s' :=
  ⟨h.rdi, rf_mono h.regs hl, h.mem⟩

theorem Keeps.setReg {W : UInt64 → Prop} {r : Reg64} (hr : r ∈ clobbers) (v : UInt64) :
    Keeps clobbers W s (s.setReg r v) :=
  ⟨by reg_simp; split <;> first | rfl | (subst r; simp [clobbers] at hr), rf_setReg (rf_refl _ _) hr v,
    fun _ _ ↦ rfl⟩

/-- A statement failing before it stores, writing only `clobbers`. -/
theorem ErrF.keeps {W : UInt64 → Prop} (hc : errKeep c = true)
    (hw : ∀ r, r ∉ clobbers → c.writes r = false) : ErrF c s (Keeps clobbers W s) :=
  (ErrF.syntax hc).mono fun _ ⟨hm, hr⟩ ↦
    ⟨hr _ (hw _ (by simp [clobbers])), fun r h ↦ hr r (hw r h), fun a _ ↦ by rw [hm]⟩

/-- The registers a statement writes are among `rs`, register by register. -/
macro "writes_tac" : tactic => `(tactic| (intro r hr; revert hr; cases r <;> decide))

/-- The next scalar and its absorption, as `nextAbsorb_then` gives them. -/
theorem nextAbsorb_ok {tag : Nat} (h : SimState env st s) :
    WP (blk [Transcript.nextScalar, Transcript.absorb tag]) s (fun s' ↦ ∃ x xs, st.stream = x :: xs ∧
      SimState env ⟨Id.run (Compile.absorb (m := Id) keccakF1600 st.sponge x tag), xs, st.openings,
        st.roots⟩ s' ∧ Keeps [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] (Foot env) s s')
      (fun _ ↦ st.stream = []) :=
  nextAbsorb_then (rest := []) h (fun hn _ ↦ hn) fun x xs _ hst h' _ _ _ k ↦ WP.blk_nil ⟨x, xs, hst, h', k⟩

/-! ## The gadgets -/

/-- **`read`'s failures** keep what its end keeps. -/
theorem readScalar_err (h : SimState env st s) :
    ErrF Transcript.readScalar s (Keeps clobbers (Foot env) s) := by
  unfold Transcript.readScalar
  refine ErrF.blk_cons (ErrF.keeps (by decide) (by writes_tac)) fun s₁ hx₁ ↦ ?_
  obtain ⟨-, rfl⟩ := WP.ok_exec (checkGround_spec h.rdi h.sponge.ground) hx₁
  refine ErrF.blk_cons ((ErrF.keeps (by decide) (by writes_tac)).mono fun _ k ↦
    (Keeps.setReg (by simp [clobbers]) 0).trans' k) fun _ _ ↦ ErrF.of_canFail (by decide +kernel)

/-- **`grind`'s failures** keep what its end keeps. -/
theorem grind_err {bits : Nat} (h : SimState env st s) (hb : bits < 2 ^ 64)
    (hrsi : s.reg .rsi = bits.toUInt64) : ErrF Transcript.grind s (Keeps clobbers (Foot env) s) := by
  unfold Transcript.grind
  refine ErrF.blk_cons (ErrF.keeps (by decide) (by writes_tac)) fun s₁ hx₁ ↦ ?_
  obtain ⟨-, rfl⟩ := WP.ok_exec (checkGround_spec h.rdi h.sponge.ground) hx₁
  have k₁ : Keeps clobbers (Foot env) s (s.setReg .rax 0) := Keeps.setReg (by simp [clobbers]) 0
  refine ErrF.blk_pair ((ErrF.keeps (by decide) (by writes_tac)).mono fun _ k ↦ k₁.trans' k)
    (fun _ _ ↦ ErrF.of_canFail (by decide +kernel)) fun s₂ hx₂ ↦ ?_
  obtain ⟨n, xs, -, h₂, k₂⟩ :=
    WP.ok_exec (nextAbsorb_ok (tag := dsPowNonce) (h.setReg (by decide) 0)) hx₂
  refine ErrF.blk_cons (ErrF.of_canFail (by decide +kernel)) fun s₃ hx₃ ↦ ?_
  obtain ⟨hsp₃, kk₃, r₃⟩ :=
    WP.ok_exec (duplex_spec (Q := fun _ ↦ False) h₂.rdi h₂.sponge h₂.layout.dom) hx₃
  have d₃ : ∀ a, (s₃.mem a).isSome = (s₂.mem a).isSome := Exec.mem_isSome hx₃
  have hrdi₃ : s₃.reg .rdi = env.ctx := by rw [r₃ _ (by simp)]; exact h₂.rdi
  have hdom₃ := h₂.layout.dom.of_isSome d₃
  have k₃ : Keeps clobbers (Foot env) s s₃ := k₁.trans' (k₂.widen.trans'
    ⟨r₃ _ (by simp), rf_mono r₃ (by simp [clobbers]),
      fun a ha ↦ kk₃ a fun h' ↦ ha (foot_ctx h' le_rfl (by lay_omega))⟩)
  have l0 := hsp₃.lanes 0 (by omega)
  have l1 := hsp₃.lanes 1 (by omega)
  have l2 := hsp₃.lanes 2 (by omega)
  rw [Nat.add_zero] at l0
  have hrsi₃ : s₃.reg .rsi = bits.toUInt64 := by
    rw [r₃ _ (by simp), k₂.regs _ (by simp)]; reg_simp; exact hrsi
  refine ErrF.of_wp (P := fun _ ↦ True) ?_ fun _ h ↦ h
  refine wp_load (eval_cw hrdi₃ _) l0 ?_
  refine wp_store (eval_cw (by reg_simp; exact hrdi₃) _) (by some_tac) ?_
  refine wp_load (eval_cw (by reg_simp; exact hrdi₃) _) (by mem_simp; exact l1) ?_
  refine wp_store (eval_cw (by reg_simp; exact hrdi₃) _) (by some_tac) ?_
  refine wp_storei (eval_cw (by reg_simp; exact hrdi₃) _) (by some_tac) ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  refine wp_then (mask_spec hb (by reg_simp; exact hrsi₃) (by reg_simp; rw [hrsi₃])) ?_
  rintro s₅ ⟨-, hm₅, r₅⟩
  have hrdi₅ : s₅.reg .rdi = env.ctx := by rw [r₅ _ (by simp)]; reg_simp; exact hrdi₃
  refine wp_load (eval_cw hrdi₅ _) (by rw [hm₅]; mem_simp; exact l2) (wp_reg rfl ?_)
  refine WP.ite ?_
  split
  · refine WP.fail ⟨by reg_simp; rw [hrdi₅, h.rdi], fun r hr ↦ ?_, fun a ha ↦ ?_⟩
    · have : r ≠ .rax ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r9 := by simp_all [clobbers]
      reg_simp
      simp only [this.1, ↓reduceIte]
      rw [r₅ r (by simp_all [clobbers])]
      reg_simp
      simp only [this.2.1, this.2.2.1, this.2.2.2, ↓reduceIte]
      exact k₃.regs r hr
    · simp only [QState.setReg_mem, hm₅, QState.setMem_mem]
      have hne : ∀ k, scratchW ≤ k → k < ctxEnd → a ≠ wd env.ctx k := fun k h1 h2 e ↦
        ha (.inl ⟨k, h1, h2, e⟩)
      rw [ite_of_not (hne _ (by lay_omega) (by lay_omega)),
        ite_of_not (hne _ (by lay_omega) (by lay_omega)),
        ite_of_not (hne _ (by lay_omega) (by lay_omega)), k₃.mem a ha]
  · exact WP.skip trivial

/-- **`commit`'s failures** keep what its end keeps. -/
theorem commit_err (h : SimState env st s) (hroom : st.roots.length < maxRoots) :
    ErrF Transcript.commit s (Keeps clobbers (Foot env) s) := by
  unfold Transcript.commit
  refine ErrF.blk_cons (ErrF.keeps (by decide) (by writes_tac)) fun s₁ hx₁ ↦ ?_
  obtain ⟨-, rfl⟩ := WP.ok_exec (checkGround_spec h.rdi h.sponge.ground) hx₁
  have k₁ : Keeps clobbers (Foot env) s (s.setReg .rax 0) := Keeps.setReg (by simp [clobbers]) 0
  refine ErrF.blk_pair ((ErrF.keeps (by decide) (by writes_tac)).mono fun _ k ↦ k₁.trans' k)
    (fun _ _ ↦ ErrF.of_canFail (by decide +kernel)) fun s₂ hx₂ ↦ ?_
  obtain ⟨_, _, -, h₂, k₂⟩ :=
    WP.ok_exec (nextAbsorb_ok (tag := dsObserve) (h.setReg (by decide) 0)) hx₂
  refine ErrF.blk_cons (ErrF.of_canFail (by decide +kernel)) fun s₃ hx₃ ↦ ?_
  obtain ⟨-, -, -, -, hk₃, r₃⟩ :=
    WP.ok_exec (storeRootPair_spec (k := 0) (Q := fun _ ↦ False) h₂ hroom (by lay_omega)) hx₃
  have k₃ : Keeps clobbers (Foot env) s s₃ :=
    k₁.trans' (k₂.widen.trans' ⟨r₃ _ (by simp), rf_mono r₃ (by simp [clobbers]), hk₃⟩)
  exact ErrF.blk_pair ((ErrF.keeps (by decide) (by writes_tac)).mono fun _ k ↦ k₃.trans' k)
    (fun _ _ ↦ ErrF.of_canFail (by decide +kernel)) fun _ _ ↦ ErrF.of_canFail (by decide +kernel)

/-- **`finish`'s failures** write nothing. -/
theorem finish_err : ErrF Transcript.finish s fun s' ↦ s'.mem = s.mem ∧
    RegsFrame [.rax, .rcx, .rdx, .r11] s s' :=
  (ErrF.syntax (by decide)).mono fun _ ⟨hm, hr⟩ ↦ ⟨hm, fun r h ↦ hr r (by revert h; cases r <;> decide)⟩

end NativeVm.Code
