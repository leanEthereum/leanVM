module

public import NativeVm.Transcript.Read

/-!
# `sample`

`sampleChallenge_spec`: from a state that simulates `st`, `sampleChallenge` ends with the challenge
`sampleStep st` squeezes in `r9`, `r10` and a state that simulates `sampleStep st`'s; it never
fails. `SimState.withSponge` is the relation after a gadget that writes only the sponge's words.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

variable {env : Env} {st : VerifierProgramState} {s : QState} {P Q : QState → Prop}

theorem squeeze_some (sp : Sponge) {c : E} (h : sp.ground = some c) :
    Id.run (squeeze (m := Id) keccakF1600 sp) = (c, { sp with ground := none }) := by
  unfold squeeze; rw [h]; rfl

theorem squeeze_none (sp : Sponge) (h : sp.ground = none) :
    Id.run (squeeze (m := Id) keccakF1600 sp) =
      (challengeOf (keccakF1600 (duplexInput sp)), ⟨keccakF1600 (duplexInput sp), [], sp.ground⟩) := by
  unfold squeeze
  conv_lhs => rw [h]
  rfl

theorem challengeOf_limb0 (A : KeccakState) : ((challengeOf A).limb 0).lane = Keccak.lane A 0 := (rfl)

theorem challengeOf_limb1 (A : KeccakState) : ((challengeOf A).limb 1).lane = Keccak.lane A 1 := (rfl)

/-- **`SimState` after a gadget that writes only the sponge's words.** -/
theorem SimState.withSponge {sp : Sponge} {s' : QState} (h : SimState env st s)
    (hrdi : s'.reg .rdi = env.ctx) (hs : ∀ a, (s'.mem a).isSome = (s.mem a).isSome)
    (hk : Keep (CtxIn env.ctx scratchW (groundW + 3)) s.mem s'.mem)
    (hsp : SpongeAt s'.mem env.ctx sp) : SimState env { st with sponge := sp } s' := by
  have hw : ∀ k, k < workWords → s'.mem (wd env.work k) = s.mem (wd env.work k) :=
    fun k hk' ↦ hk _ (h.layout.work_not_ctxIn (by lay_omega) hk')
  obtain ⟨c, hc, h1, h2⟩ := h.cursor
  obtain ⟨p, hp, g1, g2, g3⟩ := h.phase
  refine SimState.mk' h hrdi hs (hk.mono fun a ha ↦ foot_ctx ha le_rfl (by lay_omega)) hsp
    ⟨c, hc, (hw _ (by lay_omega)).trans h1, h2⟩
    ⟨p, hp, (hw _ (by lay_omega)).trans g1, (hw _ (by lay_omega)).trans g2, g3⟩
    ((hw _ (by lay_omega)).trans h.phaseCount) h.rootsLen ((hw _ (by lay_omega)).trans h.rootCount)
    fun j hj ↦ ?_
  obtain ⟨r1, r2, r3, r4, r5⟩ := h.roots j hj
  have hj8 : j < 8 := lt_of_lt_of_le hj h.rootsLen
  exact ⟨fun k hk' ↦ (hw _ (by lay_omega)).trans (r1 k hk'), r2, r3, (hw _ (by lay_omega)).trans r4,
    (hw _ (by lay_omega)).trans r5⟩

/-- **`sample`**: the challenge in `r9`, `r10`. -/
theorem sampleChallenge_spec (h : SimState env st s) :
    WP sampleChallenge s (fun s' ↦ SimState env (sampleStep st).2 s' ∧
      s'.reg .r9 = ((sampleStep st).1.limb 0).lane ∧ s'.reg .r10 = ((sampleStep st).1.limb 1).lane ∧
      Keeps clobbers (Foot env) s s') Q := by
  have hsp := h.sponge
  have hdom := h.layout.dom
  unfold sampleChallenge sampleStep
  cases hg : st.sponge.ground with
  | some c =>
    have hgr := hsp.ground
    rw [hg] at hgr
    obtain ⟨g0, g1, g2⟩ := hgr
    rw [squeeze_some _ hg]
    refine wp_load (eval_cw h.rdi _) g0 (WP.blk_cons (wp_ite_true (by simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte]; decide) ?_))
    refine wp_load (eval_cw (by reg_simp; exact h.rdi) _) g1 ?_
    refine wp_load (eval_cw (by reg_simp; exact h.rdi) _) g2 ?_
    refine wp_storei (eval_cw (by reg_simp; exact h.rdi) _) (by some_tac) ?_
    apply WP.skip
    apply wp_done
    refine ⟨SimState.withSponge h (by reg_simp; exact h.rdi) ?_ ?_ ?_, by reg_simp,
        by reg_simp, ⟨by reg_simp, ?_, ?_⟩⟩
    · intro a; simp only [QState.setMem_mem, QState.setReg_mem]; split <;> simp_all
    · refine Keep.setMem (Keep.setReg (Keep.setReg (Keep.setReg (Keep.refl _ _) _ _) _ _) _ _)
        (CtxIn.word (by lay_omega) (by lay_omega)) _
    · refine ⟨fun i hi ↦ ?_, hsp.pendingLen, ?_, fun i hi ↦ ?_, ?_⟩
      · mem_simp; exact hsp.lanes i hi
      · mem_simp; exact hsp.count
      · mem_simp; exact hsp.rate i hi
      · show _ = _
        mem_simp
    · intro r hr
      reg_simp
      simp_all [clobbers]
    · intro a ha
      simp only [QState.setMem_mem, QState.setReg_mem]
      rw [ite_of_not (fun e ↦ ha (by rw [e]; exact foot_ctx (CtxIn.word (lo := groundW)
        (hi := groundW + 1) le_rfl (by omega)) (by lay_omega) (by lay_omega)))]
  | none =>
    have hgr := hsp.ground
    rw [hg] at hgr
    rw [squeeze_none _ hg]
    refine wp_load (eval_cw h.rdi _) hgr (WP.blk_cons (wp_ite_false (by simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte]; decide) ?_))
    refine wp_then' (duplex_spec (by reg_simp; exact h.rdi) hsp hdom) ?_
    rintro s₁ ⟨h₁, k₁, r₁⟩ d₁
    have hrdi₁ : s₁.reg .rdi = env.ctx := by rw [r₁ _ (by simp)]; reg_simp; exact h.rdi
    have l0 := h₁.lanes 0 (by omega)
    have l1 := h₁.lanes 1 (by omega)
    rw [duplex_eq'] at l0 l1
    refine wp_load (eval_cw hrdi₁ _) (by rw [Nat.add_zero] at l0; exact l0) ?_
    refine wp_load (eval_cw (by reg_simp; exact hrdi₁) _) l1 ?_
    apply wp_done
    apply wp_done
    dsimp only
    refine ⟨?_, by reg_simp; exact (challengeOf_limb0 _).symm, by reg_simp; exact (challengeOf_limb1 _).symm,
      ⟨by reg_simp; rw [hrdi₁, h.rdi], ?_, ?_⟩⟩
    · rw [← duplex_eq']
      refine SimState.withSponge h (by reg_simp; exact hrdi₁) (fun a ↦ by simp only [QState.setReg_mem]; rw [d₁]; rfl)
        (fun a ha ↦ ?_) (by simpa only [QState.setReg_mem] using h₁)
      simp only [QState.setReg_mem]
      rw [k₁ a (fun h' ↦ ha (h'.mono le_rfl (by lay_omega)))]
      rfl
    · intro r hr
      reg_simp
      have : r ≠ .r9 ∧ r ≠ .r10 ∧ r ∉ [Reg64.rax, .rcx, .r8] := by simp_all [clobbers]
      simp only [this.1, this.2.1, ↓reduceIte]
      rw [r₁ r this.2.2]
      reg_simp
      simp_all [clobbers]
    · intro a ha
      simp only [QState.setReg_mem]
      rw [k₁ a (fun h' ↦ ha (foot_ctx h' le_rfl (by lay_omega)))]
      rfl

end NativeVm.Transcript
