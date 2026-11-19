module

public import NativeVm.Code.Phase6.Scr
public import NativeVm.Code.Phase2.Kit

/-!
# Phase 6's state, and the transcript gadgets into the scratch

A state of phase 6's code holds the model's (`CodeRel`), keeps what the phase must keep from its
start `s0` (`Base`, the scratch's region `rs6`), has the scratch's address in `rbp` and the scratch holding
some `f` (`St f t s`). Code that writes only scratch words and no register but its own keeps
`CodeRel` and `Base` (`St.step`). The transcript's gadgets refine their model steps from `St f` to
`St f'`, the element they read or sample stored: `rdEl` (`readScalar`), `smpEl`
(`sampleChallenge`), `rdN` (`readScalars`), `smpN` (`sampleChallenges`), `grind3` (a grind of `3`
bits). `StA`: the same while the phase writes its results, its regions `rsAll`.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code
open NativeVm.Transcript (wd wd_add wd_zero wd_inj wdisp wdisp_toUInt64 Env Foot clobbers Keeps)

/-- The region phase 6's scratch computation writes. -/
def rs6 : List Region := [scratchR]

/-- Phase 6's regions: its results and its scratch. -/
def rsAll : List Region := [keccakR, claimsR, scratchR]

/-- The scratch's address. -/
def sb (env : Env) : UInt64 := wd env.work scratchR.off

/-- `rbp` at the scratch, which holds `f`. -/
def X6 (env : Env) (f : Nat → EW) (s : QState) : Prop := s.reg .rbp = sb env ∧ Scr s.mem (sb env) f

/-- **A state of phase 6's code**, the scratch holding `f`. -/
def St (env : Env) (s0 : QState) (f : Nat → EW) (t : TState) (s : QState) : Prop :=
  CodeRel env t s ∧ Fr env rs6 s0 (X6 env f) s

/-- **A state of phase 6's code while it writes its results**: as `St`, its regions all of
`rsAll`. -/
def StA (env : Env) (s0 : QState) (f : Nat → EW) (t : TState) (s : QState) : Prop :=
  CodeRel env t s ∧ Fr env rsAll s0 (X6 env f) s

variable {env : Env} {inp : Input} {s0 s s' : QState} {t : TState} {f f' : Nat → EW}

theorem St.toA (h : St env s0 f t s) : StA env s0 f t s :=
  ⟨h.1, ⟨h.2.1.1.mono fun r hr ↦ by simp [rs6] at hr; simp [rsAll, hr], h.2.1.2⟩, h.2.2⟩

theorem scratchR_off_val : scratchR.off = 52670 := by decide

theorem scratchR_size_val : scratchR.size = 32768 := by decide

theorem sb_wd (k : Nat) : wd (sb env) k = wd env.work (scratchR.off + k) := by
  rw [sb, NativeVm.Code.wd_wd]

theorem scratch_in_work {k : Nat} (hk : k < 2 * scrN) :
    scratchR.off + k < workWords inp.bytecode.size := by
  have := stop_le_of_mem (r := scratchR) (by simp [regions]) inp.bytecode.size
  unfold Region.stop at this
  rw [scrN_val] at hk
  rw [scratchR_size_val] at this
  omega

theorem inScr_not_foot (hin : Inputs env inp s0.mem) {a : UInt64} (ha : InScr (sb env) a) :
    ¬ Foot env a := by
  obtain ⟨k, hk, rfl⟩ := ha
  rw [sb_wd]
  exact hin.not_foot_work (by rw [scratchR_off_val, NativeVm.Transcript.workWords_val]; omega)
    (scratch_in_work hk)

theorem inScr_region {a : UInt64} : InScr (sb env) a ↔ scratchR.In env.work a := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by rw [scrN_val] at hk; rw [scratchR_size_val]; omega, sb_wd k⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by rw [scrN_val]; rw [scratchR_size_val] at hk; omega, (sb_wd k).symm⟩

theorem stable_X6 (hin : Inputs env inp s0.mem) : Stable env (X6 env f) :=
  fun _ _ ⟨hp, hs⟩ hk ↦ ⟨(hk.regs .rbp (by decide)).trans hp,
    hs.congr fun a ha ↦ hk.mem a (inScr_not_foot hin ha)⟩

/-- `CodeRel` through a run that writes only scratch words and keeps `rdi`. -/
theorem codeRel_scr (h : CodeRel env t s) (hin : Inputs env inp s0.mem)
    (hrdi : s'.reg .rdi = s.reg .rdi) (hm : ∀ a, ¬ InScr (sb env) a → s'.mem a = s.mem a)
    (hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome) : CodeRel env t s' := by
  obtain ⟨st, h1, h2, h3, h4⟩ := h
  have hww := workWords_lt hin
  have nin : ∀ k, k < 2 * scrN → scratchR.off + k < workWords inp.bytecode.size :=
    fun k hk ↦ scratch_in_work hk
  refine ⟨st, h1, h2.congrW (hrdi.trans h2.rdi) hd (fun k hk ↦ ?_) (fun k hk ↦ ?_)
    (fun k hk ↦ ?_), h3, h4⟩
  · refine hm _ fun ⟨j, hj, e⟩ ↦ hin.ctx_ne_work (k := scratchR.off + j) ?_ (nin j hj)
      (e.trans (sb_wd j))
    rcases hk with hk | hk
    · rw [NativeVm.Transcript.scratchW_val] at hk; rw [NativeVm.Transcript.ctxEnd_val]; omega
    · rw [NativeVm.Transcript.laneW_val] at hk; rw [NativeVm.Transcript.groundW_val] at hk
      rw [NativeVm.Transcript.ctxEnd_val]; omega
  · exact hm _ fun ⟨j, hj, e⟩ ↦ NativeVm.Transcript.wd_ne_of_disj h2.layout.fitDec hin.fitWork
      hin.disjDec hk (nin j hj) (e.trans (sb_wd j))
  · refine hm _ fun ⟨j, hj, e⟩ ↦ ?_
    rw [sb_wd] at e
    rw [NativeVm.Transcript.workWords_val] at hk
    have h1 := nin j hj
    rw [scratchR_off_val] at h1 e
    have := (wd_inj (by omega) (by omega)).mp e
    omega

/-- `Base` through a run that writes only scratch words and keeps `rdi`. -/
theorem base_scr (h : Base env rs6 s0 s) (hrdi : s'.reg .rdi = s.reg .rdi)
    (hm : ∀ a, ¬ InScr (sb env) a → s'.mem a = s.mem a)
    (hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome) : Base env rs6 s0 s' :=
  ⟨⟨hrdi.trans h.1.1, fun a hf hr ↦ by
      rw [hm a fun ha ↦ hr scratchR (by simp [rs6]) (inScr_region.mp ha)]
      exact h.1.2 a hf hr⟩, fun a ↦ (hd a).trans (h.2 a)⟩

/-- **A step of code that writes only the scratch**, `rbp` and `rdi` kept: the state goes from `St f`
to `St f'`. -/
theorem St.step {c : Stmt} {R : QState → Prop} {E : QState → Prop} (hin : Inputs env inp s0.mem)
    (h : St env s0 f t s)
    (hc : WP c s (fun s' ↦ Scr s'.mem (sb env) f' ∧ (∀ a, ¬ InScr (sb env) a → s'.mem a = s.mem a) ∧
      s'.reg .rdi = s.reg .rdi ∧ s'.reg .rbp = s.reg .rbp ∧ R s') E) :
    WP c s (fun s' ↦ St env s0 f' t s' ∧ R s') E :=
  WP.mono (NativeVm.Transcript.WP.frame hc) (fun _ ⟨⟨h1, h2, h3, h4, h5⟩, hd, _⟩ ↦
    ⟨⟨codeRel_scr h.1 hin h3 h2 hd, base_scr h.2.1 h3 h2 hd, h4.trans h.2.2.1, h1⟩, h5⟩) (fun _ h ↦ h.1)

/-- **A state of phase 6's code from another**: the scratch rewritten, every other word, `rdi` and
`rbp` kept. -/
theorem St.mk' (hin : Inputs env inp s0.mem) (h : St env s0 f t s) (hs : Scr s'.mem (sb env) f')
    (hm : ∀ a, ¬ InScr (sb env) a → s'.mem a = s.mem a) (hrdi : s'.reg .rdi = s.reg .rdi)
    (hrbp : s'.reg .rbp = s.reg .rbp) : St env s0 f' t s' := by
  have hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome := fun a ↦ by
    by_cases ha : InScr (sb env) a
    · obtain ⟨k, hk, rfl⟩ := ha
      have h1 := h.2.2.2
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [show j + j = 2 * j by omega, (hs j (by omega)).1, (h1 j (by omega)).1]; rfl
      · rw [(hs j (by omega)).2, (h1 j (by omega)).2]; rfl
    · rw [hm a ha]
  exact ⟨codeRel_scr h.1 hin hrdi hm hd, base_scr h.2.1 hrdi hm hd, hrbp.trans h.2.2.1, hs⟩

/-- A register frame without `rdi` and `rbp` keeps them. -/
theorem RegsFrame.rdi_rbp {L : List Reg64} (h : RegsFrame L s s') (h1 : Reg64.rdi ∉ L)
    (h2 : Reg64.rbp ∉ L) : s'.reg .rdi = s.reg .rdi ∧ s'.reg .rbp = s.reg .rbp :=
  ⟨h .rdi h1, h .rbp h2⟩

/-! ## Refinement after code with no model step -/

theorem Refines.then_blk {α : Type} {P : TState → QState → Prop} {c : Stmt} {cs : List Stmt}
    {m : VM α} {Q Q' : α → TState → QState → Prop} {E : QState → Prop}
    (h : Refines P c m Q E) (h₂ : ∀ x t s, Q x t s → WP (blk cs) s (Q' x t) fun _ ↦ False) :
    Refines P (blk (c :: cs)) m Q' E :=
  fun t s hts ↦ WP.blk_cons (WP.mono (h t s hts)
    (fun _ ⟨x, t', hr, hq⟩ ↦ WP.mono (h₂ x t' _ hq) (fun _ h ↦ ⟨x, t', hr, h⟩) (fun _ h ↦ h.elim))
    (fun _ h ↦ h))

/-- A precondition with a fact of its parameter. -/
theorem Refines.ex {α β : Type} {P : β → TState → QState → Prop} {D : β → Prop} {c : Stmt} {m : VM α}
    {Q : α → TState → QState → Prop} {E : QState → Prop}
    (h : ∀ b, D b → Refines (P b) c m Q E) :
    Refines (fun t s ↦ ∃ b, D b ∧ P b t s) c m Q E :=
  fun t s ⟨b, hb, hp⟩ ↦ h b hb t s hp

/-! ## Storing an element -/

/-- Store `(r9, r10)` as element `o` of the scratch. -/
def stEl (o : Nat) : List Stmt :=
  [I (.store (at_ .rbp (wdisp (2 * o))) .r9), I (.store (at_ .rbp (wdisp (2 * o + 1))) .r10)]

theorem stEl_spec {o : Nat} {p : UInt64} {x : EW} {xs : List Stmt} {P E : QState → Prop}
    (ho : o < scrN) (hp : s.reg .rbp = p) (hs : Scr s.mem p f) (h9 : s.reg .r9 = x.c0)
    (h10 : s.reg .r10 = x.c1)
    (k : ∀ s', Scr s'.mem p (Function.update f o x) → (∀ a, ¬ InScr p a → s'.mem a = s.mem a) →
      s'.reg = s.reg → WP (blk xs) s' P E) :
    WP (blk (stEl o ++ xs)) s P E := by
  unfold stEl
  refine NativeVm.Transcript.wp_store (eval_el (p := p) hp _) (by rw [(hs o ho).1]; rfl) ?_
  refine NativeVm.Transcript.wp_store (eval_el (p := p) (by rw [QState.setMem_reg]; exact hp) _)
    (by
      simp only [QState.setMem_mem]
      split
      · rfl
      · rw [(hs o ho).2]; rfl) ?_
  refine k _ ?_ (fun a ha ↦ ?_) rfl
  · have := hs.store ho x
    simpa [QState.setMem, h9, h10] using this
  · have := store_out (mem := s.mem) ha ho x
    simpa [QState.setMem, h9, h10] using this

/-! ## The gadgets into the scratch -/

/-- `readScalar` into element `o`. -/
def rdEl (o : Nat) : Stmt := blk (Transcript.readScalar :: stEl o)

/-- `sampleChallenge` into element `o`. -/
def smpEl (o : Nat) : Stmt := blk (Transcript.sampleChallenge :: stEl o)

/-- A grind of `3` bits. -/
def grind3 : Stmt := blk [I (.movi .rsi 3), Transcript.grind]

variable (env inp s0)

theorem rdEl_refines (hin : Inputs env inp s0.mem) {o : Nat} (ho : o < scrN) (f : Nat → EW) :
    Refines (St env s0 f) (rdEl o) Model.readScalar
      (fun x t s ↦ St env s0 (Function.update f o x) t s) (Kept env rs6 s0) := by
  refine Refines.then_blk (readScalar_fr (stable_X6 hin)) fun x t s ⟨hc, ⟨hb, hp, hs⟩, h9, h10⟩ ↦ ?_
  have := St.step (f' := Function.update f o x) (R := fun _ ↦ True) (c := blk (stEl o))
    (E := fun _ ↦ False) hin ⟨hc, hb, hp, hs⟩
    (by
      rw [← List.append_nil (stEl o)]
      exact stEl_spec ho hp hs h9 h10 fun s' h1 h2 h3 ↦ WP.blk_nil
        ⟨h1, h2, by rw [h3], by rw [h3], trivial⟩)
  exact WP.mono this (fun _ h ↦ h.1) (fun _ h ↦ h)

theorem smpEl_refines (hin : Inputs env inp s0.mem) {o : Nat} (ho : o < scrN) (f : Nat → EW) :
    Refines (St env s0 f) (smpEl o) Model.sampleChallenge
      (fun x t s ↦ St env s0 (Function.update f o x) t s) (Kept env rs6 s0) := by
  refine Refines.then_blk (sampleChallenge_fr (stable_X6 hin))
    fun x t s ⟨hc, ⟨hb, hp, hs⟩, h9, h10⟩ ↦ ?_
  have := St.step (f' := Function.update f o x) (R := fun _ ↦ True) (c := blk (stEl o))
    (E := fun _ ↦ False) hin ⟨hc, hb, hp, hs⟩
    (by
      rw [← List.append_nil (stEl o)]
      exact stEl_spec ho hp hs h9 h10 fun s' h1 h2 h3 ↦ WP.blk_nil
        ⟨h1, h2, by rw [h3], by rw [h3], trivial⟩)
  exact WP.mono this (fun _ h ↦ h.1) (fun _ h ↦ h)

theorem grind3_refines (hin : Inputs env inp s0.mem) (f : Nat → EW) :
    Refines (St env s0 f) grind3 (Model.grind 3) (fun _ t s ↦ St env s0 f t s) (Kept env rs6 s0) := by
  intro t s ⟨hc, hb, hx⟩
  unfold grind3
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine WP.mono (grind_fr (rs := rs6) (s0 := s0) (by decide) (by decide) (stable_X6 hin) t _
    ⟨hc.setReg (r := .rsi) (by decide) _, ⟨hb.setReg (d := .rsi) (by decide) _, ?_⟩, ?_⟩)
    (fun _ h ↦ h) (fun _ h ↦ h)
  · exact ⟨by rw [QState.setReg_reg, NativeVm.Transcript.ite_of_not (by decide)]; exact hx.1,
      hx.2.congr fun _ _ ↦ rfl⟩
  · simp only [QState.setReg_reg, ↓reduceIte]; rfl

end NativeVm.Code.P6
