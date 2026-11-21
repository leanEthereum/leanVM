module

public import NativeVm.Transcript.Sim

/-!
# `read`

`readScalar_spec`: from a state that simulates `st`, `readScalar` ends with the next scalar's limbs
in `r9`, `r10` and a state that simulates `readStep st`'s, or fails when `readStep st` is `none` (a
ground challenge waits, or the stream is consumed). Its parts: `checkGround_spec`, `nextScalar_spec`
(the next stream element and the cursor), and `absorb_spec`.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

variable {env : Env} {st : VerifierProgramState} {s : QState} {P Q : QState → Prop}

/-! ## Facts the gadgets share -/

theorem SpongeAt.congr {ctx : UInt64} {sp : Sponge} {m m' : UInt64 → Option UInt64}
    (h : SpongeAt m ctx sp) (hm : ∀ k, laneW ≤ k → k < groundW + 3 → m' (wd ctx k) = m (wd ctx k)) :
    SpongeAt m' ctx sp where
  lanes i hi := (hm _ (by lay_omega) (by lay_omega)).trans (h.lanes i hi)
  pendingLen := h.pendingLen
  count := (hm _ (by lay_omega) (by lay_omega)).trans h.count
  rate i hi := (hm _ (by lay_omega) (by lay_omega)).trans (h.rate i hi)
  ground := h.ground.congr (hm _ (by lay_omega) (by lay_omega)) (hm _ (by lay_omega) (by lay_omega))
    (hm _ (by lay_omega) (by lay_omega))

theorem Layout.work_not_ctxIn {mem : UInt64 → Option UInt64} (h : Layout env mem) {lo hi k : Nat}
    (hhi : hi ≤ ctxEnd) (hk : k < workWords) : ¬ CtxIn env.ctx lo hi (wd env.work k) := by
  rintro ⟨j, -, hj, e⟩
  exact h.work_ne_ctx hk (by omega) e

/-- The words a run of register and memory updates of the working area leaves. -/
theorem keep_work_update {m : UInt64 → Option UInt64} {k : Nat} (hk : k < workWords) (v : UInt64) :
    Keep (Foot env) m (Function.update m (wd env.work k) (some v)) :=
  (Keep.refl _ m).update (foot_work hk) _

/-- `Keeps` composed. -/
theorem Keeps.trans' {rs : List Reg64} {W : UInt64 → Prop} {s₁ s₂ s₃ : QState}
    (h : Keeps rs W s₁ s₂) (h' : Keeps rs W s₂ s₃) : Keeps rs W s₁ s₃ :=
  ⟨h'.rdi.trans h.rdi, fun r hr ↦ (h'.regs r hr).trans (h.regs r hr),
    fun a ha ↦ (h'.mem a ha).trans (h.mem a ha)⟩

/-- The stream after `c` elements. -/
theorem drop_eq_cons {α : Type} {l : List α} {c : Nat} (h : c < l.length) :
    l.drop c = l[c] :: l.drop (c + 1) := by
  rw [List.drop_eq_getElem_cons h]

/-! ## The pieces -/

theorem eval_at0 (r : Reg64) (s : QState) : (at_ r 0).eval s = s.reg r := by
  simp only [Addr.eval, at_]
  rw [show Int64.toUInt64 0 = 0 from rfl, UInt64.add_zero, UInt64.add_zero]

/-- `checkGround` passes when no challenge waits and fails when one does. -/
theorem checkGround_spec {ctx : UInt64} {g : Option E} (hrdi : s.reg .rdi = ctx)
    (hg : GroundAt s.mem ctx g) :
    WP checkGround s (fun s' ↦ g = none ∧ s' = s.setReg .rax 0) (fun _ ↦ g.isSome) := by
  unfold checkGround
  cases g with
  | none =>
    refine wp_load (eval_cw hrdi _) hg (WP.blk_cons (wp_ite_false ?_ (WP.skip (WP.skip ⟨rfl, rfl⟩))))
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte, int64_toUInt64, bne_self_eq_false]
  | some c =>
    refine wp_load (eval_cw hrdi _) hg.1 (WP.blk_cons (wp_ite_true ?_ (WP.fail rfl)))
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte, int64_toUInt64]
    decide

/-- **The next stream element**: its limbs in `r9`, `r10` and the cursor advanced, or a failure at
the stream's end. -/
theorem nextScalar_spec (h : SimState env st s) {c : Nat} (hc : c ≤ env.proof.stream.length)
    (hcur : s.mem (wd env.work workCursor) = some c.toUInt64) :
    WP nextScalar s (fun s' ↦ ∃ hlt : c < env.proof.stream.length,
      s'.reg .r9 = (env.proof.stream[c].limb 0).lane ∧ s'.reg .r10 = (env.proof.stream[c].limb 1).lane ∧
      s'.mem = Function.update s.mem (wd env.work workCursor) (some (c + 1).toUInt64) ∧
      RegsFrame [.rax, .rcx, .rdx, .r9, .r10, .r11] s s')
      (fun _ ↦ env.proof.stream.length ≤ c) := by
  have hL := h.layout
  have hdec := h.decoded
  obtain ⟨hsl, h0, hel, -⟩ := hdec
  have hfit := hL.fitDec
  have hdw := decodedWords_eq env.L
  have hsl' : env.proof.stream.length ≤ env.L / 16 := hsl
  have hfitn : 8 * decodedWords env.L ≤ 2 ^ 64 := by unfold Fits at hfit; omega
  set n := env.proof.stream.length with hn
  unfold nextScalar
  refine wp_load (eval_cw h.rdi _) hL.workPtr ?_
  refine wp_load (eval_cw (by reg_simp; exact h.rdi) _) hL.decPtr ?_
  refine wp_load (work_reg (by reg_simp) _) hcur ?_
  refine wp_load (by rw [eval_at0]; reg_simp; exact (wd_zero _).symm) h0 ?_
  by_cases hlt : c < n
  · refine wp_failIf ?_ ?_
    · simp only [Cond.eval, Rhs.eval]
      reg_simp
      rw [decide_eq_false_iff_not, toUInt64_le (by omega) (by omega)]
      omega
    refine wp_reg rfl (wp_reg rfl ?_)
    have hrcx : c.toUInt64 <<< (4 : Nat).toUInt64 = (8 * (2 * c)).toUInt64 := by
      rw [toUInt64_shl _ _ (by omega)]
      congr 1
      omega
    have ea : ∀ (t : QState) k, t.reg .rdx = wd env.dec 0 → t.reg .rcx = (8 * (2 * c)).toUInt64 →
        (decAt k).eval t = wd env.dec (2 * c + k) := fun t k h1 h2 ↦ by
      rw [decAt, eval_idx8 h1 h2]
      congr 1
      omega
    have e0 := hel c hlt 0 (by omega)
    have e1 := hel c hlt 1 (by omega)
    simp only [eWords, List.getD_cons_zero, List.getD_cons_succ] at e0 e1
    refine wp_load (ea _ 1 (by reg_simp; exact (wd_zero _).symm) (by reg_simp; exact hrcx))
      (by rw [show 2 * c + 1 = 1 + 2 * c + 0 by omega]; exact e0) ?_
    refine wp_load (ea _ 2 (by reg_simp; exact (wd_zero _).symm) (by reg_simp; exact hrcx))
      (by rw [show 2 * c + 2 = 1 + 2 * c + 1 by omega]; exact e1) ?_
    refine wp_reg rfl (wp_store (work_reg (by reg_simp) _) (hL.workSome _ (by lay_omega))
      (wp_done ⟨hlt, by reg_simp, by reg_simp, ?_, ?_⟩))
    · reg_simp
      rw [toUInt64_succ]
      rfl
    · rf_tac
  · refine wp_failIf_fail ?_ (by omega)
    simp only [Cond.eval, Rhs.eval]
    reg_simp
    rw [decide_eq_true_eq, toUInt64_le (by omega) (by omega)]
    omega

/-- **`read`**: the next scalar absorbed, its limbs in `r9`, `r10`; a failure exactly where
`readStep` is `none`. -/
theorem readScalar_spec (h : SimState env st s) :
    WP readScalar s (fun s' ↦ ∃ x st', readStep st = some (x, st') ∧ SimState env st' s' ∧
      s'.reg .r9 = (x.limb 0).lane ∧ s'.reg .r10 = (x.limb 1).lane ∧ Keeps clobbers (Foot env) s s')
      (fun _ ↦ readStep st = none) := by
  obtain ⟨c, hc, hcw, hst⟩ := h.cursor
  unfold readScalar
  refine wp_then (WP.mono (checkGround_spec h.rdi h.sponge.ground) (fun s' h' ↦ h') ?_) ?_
  · intro _ hg
    unfold readStep
    obtain ⟨g, hg'⟩ := Option.isSome_iff_exists.mp hg
    rw [hg']
    cases st.stream <;> rfl
  rintro s₁ ⟨hg, rfl⟩
  refine wp_then' (WP.mono (nextScalar_spec (s := s.setReg .rax 0) ⟨by reg_simp; exact h.rdi,
    h.layout, h.decoded, h.sponge, h.cursor, h.phase, h.phaseCount, h.rootsLen, h.rootCount,
    h.roots⟩ hc hcw) (fun s' h' ↦ h') ?_) ?_
  · intro _ hle
    unfold readStep
    rw [hst, List.drop_eq_nil_of_le hle]
  rintro s₂ ⟨hlt, h9, h10, hm₂, hr₂⟩ d₂
  have hrdi₂ : s₂.reg .rdi = env.ctx := by rw [hr₂ _ (by simp)]; reg_simp; exact h.rdi
  have hsp₂ : SpongeAt s₂.mem env.ctx st.sponge := h.sponge.congr fun k _ _ ↦ by
    rw [hm₂, Function.update_of_ne (h.layout.work_ne_ctx (by lay_omega) (by lay_omega)).symm]
    rfl
  refine WP.blk_cons (WP.mono (WP.frame (absorb_spec hrdi₂ hsp₂ ((h.layout.dom).of_isSome
    (fun a ↦ by rw [d₂]; rfl)) h9 h10)) ?_ (fun _ h ↦ h.1))
  rintro s₃ ⟨⟨hsp₃, hk₃, hr₃⟩, d₃, -⟩
  have hst' : st.stream = env.proof.stream[c] :: env.proof.stream.drop (c + 1) := by
    rw [hst, drop_eq_cons hlt]
  have hread : readStep st = some (env.proof.stream[c],
      ⟨Id.run (Compile.absorb (m := Id) keccakF1600 st.sponge env.proof.stream[c] dsObserve),
        env.proof.stream.drop (c + 1), st.openings, st.roots⟩) := by
    unfold readStep
    rw [hst', hg]
  have hm₃ : ∀ k, k < workWords → s₃.mem (wd env.work k) = s₂.mem (wd env.work k) :=
    fun k hk ↦ hk₃ _ (h.layout.work_not_ctxIn (by lay_omega) hk)
  have hk : Keep (Foot env) s.mem s₃.mem := by
    intro a ha
    rw [hk₃ a (fun h' ↦ ha (foot_ctx h' le_rfl (by lay_omega))), hm₂,
      Function.update_of_ne (fun e ↦ ha (by rw [e]; exact foot_work (by lay_omega)))]
    rfl
  have hw : ∀ k, k < workWords → k ≠ workCursor → s₃.mem (wd env.work k) = s.mem (wd env.work k) :=
    fun k hk hne ↦ by
      rw [hm₃ k hk, hm₂, Function.update_of_ne (by rw [Ne, wd_inj (by lay_omega) (by lay_omega)]; exact hne)]
      rfl
  refine wp_done ⟨_, _, hread, SimState.mk' h ?_ ?_ hk hsp₃ ?_ ?_ ?_ h.rootsLen ?_ ?_, ?_, ?_, ?_⟩
  · rw [hr₃ _ (by simp), hrdi₂]
  · intro a; rw [d₃, d₂]; rfl
  · refine ⟨c + 1, hlt, ?_, rfl⟩
    rw [hm₃ _ (by lay_omega), hm₂, Function.update_self]
  · obtain ⟨p, hp, h1, h2, h3⟩ := h.phase
    exact ⟨p, hp, (hw _ (by lay_omega) (by lay_omega)).trans h1,
      (hw _ (by lay_omega) (by lay_omega)).trans h2, h3⟩
  · exact (hw _ (by lay_omega) (by lay_omega)).trans h.phaseCount
  · exact (hw _ (by lay_omega) (by lay_omega)).trans h.rootCount
  · intro j hj
    obtain ⟨r1, r2, r3, r4, r5⟩ := h.roots j hj
    have hj8 : j < 8 := lt_of_lt_of_le hj h.rootsLen
    refine ⟨fun k hk ↦ (hw _ (by lay_omega) (by lay_omega)).trans (r1 k hk), r2, r3,
      (hw _ (by lay_omega) (by lay_omega)).trans r4, (hw _ (by lay_omega) (by lay_omega)).trans r5⟩
  · rw [hr₃ _ (by simp), h9]
  · rw [hr₃ _ (by simp), h10]
  · refine ⟨by rw [hr₃ _ (by simp), hrdi₂, h.rdi], fun r hr ↦ ?_, hk⟩
    rw [hr₃ r (by simp_all [clobbers]), hr₂ r (by simp_all [clobbers])]
    reg_simp
    simp_all [clobbers]

end NativeVm.Transcript
