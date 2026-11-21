module

public import NativeVm.Transcript.Mem
public import NativeVm.Transcript.Run
public import Mathlib.Data.List.GetD

/-!
# The sponge's code

`duplex_spec` and `absorb_spec`: on the sponge's words (`SpongeAt`), `duplex` and `absorb` compute
the statement's `duplex` and `absorb` over Keccak-f[1600], writing only the context's words from
the scratch area to the count.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## The statement's sponge -/

theorem lane_ofFn (f : Fin 25 → UInt64) {i : Nat} (h : i < 25) :
    Keccak.lane (Vector.ofFn f) i = f ⟨i, h⟩ := by
  simp [Keccak.lane, h]

theorem lane_duplexInput (sp : Sponge) {i : Nat} (h : i < 25) :
    Keccak.lane (duplexInput sp) i =
      if i < 16 then (pendingLanes sp.pending).getD i 0 else Keccak.lane sp.state i := by
  unfold duplexInput
  rw [lane_ofFn _ h]

theorem duplex_eq' (sp : Sponge) :
    Id.run (Compile.duplex (m := Id) keccakF1600 sp) = ⟨keccakF1600 (duplexInput sp), [], sp.ground⟩ := (rfl)

theorem absorb_eq (sp : Sponge) (x : E) (tag : Nat) :
    Id.run (Compile.absorb (m := Id) keccakF1600 sp x tag) =
      let sp' := if sp.pending.length = rateScalars then Id.run (Compile.duplex (m := Id) keccakF1600 sp)
        else sp
      { sp' with pending := sp'.pending ++ [(x, tag)] } := by
  unfold Compile.absorb
  split <;> rfl

theorem pendingLanes_length (p : List (E × Nat)) : (pendingLanes p).length = 4 * p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [pendingLanes, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    rw [ih]
    omega

theorem pendingLanes_append (p : List (E × Nat)) (x : E) (tag : Nat) :
    pendingLanes (p ++ [(x, tag)]) =
      pendingLanes p ++ [(x.limb 0).lane, (x.limb 1).lane, 0, tag.toUInt64] := by
  simp [pendingLanes, List.flatMap_append]

/-- The rate lanes after appending a scalar. -/
theorem pendingLanes_append_getD (p : List (E × Nat)) (x : E) (tag i : Nat) :
    (pendingLanes (p ++ [(x, tag)])).getD i 0 =
      if i < 4 * p.length then (pendingLanes p).getD i 0
      else [(x.limb 0).lane, (x.limb 1).lane, 0, tag.toUInt64].getD (i - 4 * p.length) 0 := by
  rw [pendingLanes_append]
  split
  · exact List.getD_append _ _ _ _ (by rw [pendingLanes_length]; omega)
  · rw [List.getD_append_right _ _ _ _ (by rw [pendingLanes_length]; omega), pendingLanes_length]

theorem pendingLanes_getD_ge (p : List (E × Nat)) {i : Nat} (h : 4 * p.length ≤ i) :
    (pendingLanes p).getD i 0 = 0 :=
  List.getD_eq_default _ _ (by rw [pendingLanes_length]; exact h)

/-! ## The sponge's words -/

theorem keep_ctx_trans {ctx : UInt64} {a b c d lo hi : Nat} {m₁ m₂ m₃ : UInt64 → Option UInt64}
    (h : Keep (CtxIn ctx a b) m₁ m₂) (h' : Keep (CtxIn ctx c d) m₂ m₃) (h1 : lo ≤ a) (h2 : b ≤ hi)
    (h3 : lo ≤ c) (h4 : d ≤ hi) : Keep (CtxIn ctx lo hi) m₁ m₃ :=
  h.trans h' (fun _ h ↦ h.mono h1 h2) (fun _ h ↦ h.mono h3 h4)

/-- The ground challenge's words, kept. -/
theorem GroundAt.congr {ctx : UInt64} {g : Option E} {m m' : UInt64 → Option UInt64}
    (h : GroundAt m ctx g) (h0 : m' (wd ctx groundW) = m (wd ctx groundW))
    (h1 : m' (wd ctx (groundW + 1)) = m (wd ctx (groundW + 1)))
    (h2 : m' (wd ctx (groundW + 2)) = m (wd ctx (groundW + 2))) : GroundAt m' ctx g := by
  cases g with
  | none => unfold GroundAt at h ⊢; rw [h0]; exact h
  | some c => unfold GroundAt at h ⊢; rw [h0, h1, h2]; exact h

/-- The ground challenge's words, kept by a block that writes only up to the count. -/
theorem GroundAt.keep {ctx : UInt64} {g : Option E} {m m' : UInt64 → Option UInt64}
    (h : GroundAt m ctx g) {lo : Nat} (hk : Keep (CtxIn ctx lo (countW + 1)) m m') :
    GroundAt m' ctx g :=
  h.congr (hk.ctx (by lay_omega) (by lay_omega) (by lay_omega))
    (hk.ctx (by lay_omega) (by lay_omega) (by lay_omega))
    (hk.ctx (by lay_omega) (by lay_omega) (by lay_omega))

variable {s : QState} {P Q : QState → Prop}

/-- **`duplex`** permutes the sponge. -/
theorem duplex_spec {ctx : UInt64} {sp : Sponge} (hrdi : s.reg .rdi = ctx)
    (hsp : SpongeAt s.mem ctx sp) (hdom : Dom ctx s.mem) :
    WP duplex s (fun s' ↦ SpongeAt s'.mem ctx (Id.run (Compile.duplex (m := Id) keccakF1600 sp)) ∧
      Keep (CtxIn ctx scratchW (countW + 1)) s.mem s'.mem ∧ RegsFrame [.rax, .rcx, .r8] s s') Q := by
  unfold Transcript.duplex
  refine wp_then' (copyCtx_spec (f := fun t ↦ (pendingLanes sp.pending).getD t 0) hrdi
    (by lay_omega) (by lay_omega) (by lay_omega) (fun t ht ↦ hsp.rate t ht)
    (fun t ht ↦ hdom _ (by lay_omega))) ?_
  rintro s₁ ⟨h₁, k₁, r₁⟩ d₁
  have hrdi₁ : s₁.reg .rdi = ctx := (r₁ _ (by simp)).trans hrdi
  have hdom₁ := hdom.of_isSome d₁
  refine wp_then' (copyCtx_spec (f := fun t ↦ Keccak.lane sp.state (16 + t)) hrdi₁
    (by lay_omega) (by lay_omega) (by lay_omega) (fun t ht ↦ ?_)
    (fun t ht ↦ hdom₁ _ (by lay_omega))) ?_
  · rw [k₁.ctx (by lay_omega) (by lay_omega) (by lay_omega),
      show laneW + 16 + t = laneW + (16 + t) by omega]
    exact hsp.lanes _ (by omega)
  rintro s₂ ⟨h₂, k₂, r₂⟩ d₂
  have hrdi₂ : s₂.reg .rdi = ctx := (r₂ _ (by simp)).trans hrdi₁
  have hdom₂ := hdom₁.of_isSome d₂
  refine wp_then' (permuteAt_spec (A := duplexInput sp) hrdi₂
    (fun k hk ↦ hdom₂ _ (by lay_omega)) (fun i hi ↦ ?_)) ?_
  · rw [lane_duplexInput sp hi]
    split
    · rw [k₂.ctx (by lay_omega) (by lay_omega) (by lay_omega)]
      exact h₁ i (by omega)
    · have := h₂ (i - 16) (by omega)
      rwa [show scratchW + 16 + (i - 16) = scratchW + i by omega,
        show 16 + (i - 16) = i by omega] at this
  rintro s₃ ⟨h₃, -, k₃, r₃⟩ d₃
  have hrdi₃ : s₃.reg .rdi = ctx := (r₃ _ (by simp)).trans hrdi₂
  have hdom₃ := hdom₂.of_isSome d₃
  refine wp_then' (copyCtx_spec (f := fun t ↦ Keccak.lane (keccakF1600 (duplexInput sp)) t)
    hrdi₃ (by lay_omega) (by lay_omega) (by lay_omega) (fun t ht ↦ h₃ t ht)
    (fun t ht ↦ hdom₃ _ (by lay_omega))) ?_
  rintro s₄ ⟨h₄, k₄, r₄⟩ d₄
  have hrdi₄ : s₄.reg .rdi = ctx := (r₄ _ (by simp)).trans hrdi₃
  have hdom₄ := hdom₃.of_isSome d₄
  refine wp_then' (zeroCtx_spec hrdi₄ (by lay_omega) (fun t ht ↦ hdom₄ _ (by lay_omega))) ?_
  rintro s₅ ⟨h₅, k₅, r₅⟩ d₅
  have hrdi₅ : s₅.reg .rdi = ctx := by rw [r₅]; exact hrdi₄
  have hdom₅ := hdom₄.of_isSome d₅
  have k₅' : Keep (CtxIn ctx scratchW (countW + 1)) s.mem s₅.mem :=
    keep_ctx_trans (keep_ctx_trans (keep_ctx_trans (keep_ctx_trans k₁ k₂ le_rfl (by lay_omega)
      (by lay_omega) (by lay_omega)) k₃ le_rfl le_rfl (by lay_omega) (by lay_omega)) k₄ le_rfl
      le_rfl (by lay_omega) (by lay_omega)) k₅ le_rfl le_rfl (by lay_omega) (by lay_omega)
  refine wp_storei (eval_cw hrdi₅ _) (hdom₅ _ (by lay_omega)) (wp_done ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩)
  · intro i hi
    rw [duplex_eq']
    mem_simp
    rw [k₅.ctx (by lay_omega) (by lay_omega) (by lay_omega)]
    exact h₄ i hi
  · simp [duplex_eq']
  · rw [duplex_eq']
    mem_simp
    rfl
  · intro i hi
    rw [duplex_eq']
    mem_simp
    rw [show rateW + i = rateW + i from rfl, h₅ i hi]
    rfl
  · rw [duplex_eq']
    refine hsp.ground.congr ?_ ?_ ?_ <;> mem_simp <;>
      exact k₅' _ (not_ctxIn (by lay_omega) (by lay_omega) (by lay_omega))
  · exact k₅'.setMem (CtxIn.word (by lay_omega) (by lay_omega)) _
  · refine rf_setMem ?_ _ _
    intro r hr
    rw [congrFun r₅ r, r₄ r (by simp_all), r₃ r hr, r₂ r (by simp_all), r₁ r (by simp_all)]

theorem pendingLanes_cons_getD (p : List (E × Nat)) (x : E) (tag j : Nat) (hj : j < 4) :
    (pendingLanes (p ++ [(x, tag)])).getD (4 * p.length + j) 0 =
      [(x.limb 0).lane, (x.limb 1).lane, 0, tag.toUInt64].getD j 0 := by
  rw [pendingLanes_append_getD]
  simp only [show ¬ (4 * p.length + j < 4 * p.length) by omega, ↓reduceIte, Nat.add_sub_cancel_left]

/-- Appending to a queue that is not full. -/
theorem appendPending_spec {ctx : UInt64} {sp : Sponge} {x : E} {tag : Nat}
    (hrdi : s.reg .rdi = ctx) (hsp : SpongeAt s.mem ctx sp) (hdom : Dom ctx s.mem)
    (hlen : sp.pending.length < rateScalars) (h9 : s.reg .r9 = (x.limb 0).lane)
    (h10 : s.reg .r10 = (x.limb 1).lane) :
    WP (blk (appendPending tag)) s (fun s' ↦
      SpongeAt s'.mem ctx { sp with pending := sp.pending ++ [(x, tag)] } ∧
      Keep (CtxIn ctx scratchW (countW + 1)) s.mem s'.mem ∧ RegsFrame [.rax, .rdx] s s') Q := by
  unfold rateScalars at hlen
  obtain ⟨n, hn⟩ : ∃ n, sp.pending.length = n := ⟨_, rfl⟩
  have hcount := hsp.count
  rw [hn] at hcount
  have hrdi0 : s.reg .rdi = wd ctx 0 := by rw [hrdi, wd_zero]
  have ea : ∀ (t : QState) k, t.reg .rdi = wd ctx 0 → t.reg .rdx = (8 * (4 * n)).toUInt64 →
      (rateAt k).eval t = wd ctx (rateW + 4 * n + k) := fun t k h1 h2 ↦ by
    rw [rateAt, eval_idx8 h1 h2]
    congr 1
    omega
  have h5 : n.toUInt64 <<< (5 : Nat).toUInt64 = (8 * (4 * n)).toUInt64 := by
    rw [toUInt64_shl _ _ (by omega)]
    congr 1
    omega
  refine wp_load (eval_cw hrdi _) hcount (wp_reg rfl (wp_reg rfl ?_))
  refine wp_store (ea _ 0 (by reg_simp; exact hrdi0) (by reg_simp; exact h5)) (by some_tac) ?_
  refine wp_store (ea _ 1 (by reg_simp; exact hrdi0) (by reg_simp; exact h5)) (by some_tac) ?_
  refine wp_storei (ea _ 2 (by reg_simp; exact hrdi0) (by reg_simp; exact h5))
    (by some_tac) ?_
  refine wp_storei (ea _ 3 (by reg_simp; exact hrdi0) (by reg_simp; exact h5))
    (by some_tac) ?_
  refine wp_reg rfl ?_
  refine wp_store (eval_cw (b := ctx) ?_ _) ?_ ?_
  · reg_simp
    exact hrdi
  · some_tac
  refine wp_done ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    mem_simp
    exact hsp.lanes i hi
  · simp only [List.length_append, List.length_cons, List.length_nil]
    unfold rateScalars
    omega
  · mem_simp
    simp only [List.length_append, List.length_cons, List.length_nil, hn, toUInt64_succ]
  · intro i hi
    rw [pendingLanes_append_getD, hn]
    by_cases hlt : i < 4 * n
    · mem_simp
      rw [hsp.rate i hi]
      simp only [hlt, ↓reduceIte]
    simp only [hlt, ↓reduceIte]
    by_cases h0 : i = 4 * n
    · mem_simp
      simp [h0, h9]
    by_cases h1 : i = 4 * n + 1
    · mem_simp
      simp [h1, h10]
    by_cases h2 : i = 4 * n + 2
    · mem_simp
      simp [h2]
    by_cases h3 : i = 4 * n + 3
    · mem_simp
      simp [h3]
    mem_simp
    rw [hsp.rate i hi, pendingLanes_getD_ge _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
  · refine hsp.ground.congr ?_ ?_ ?_ <;> mem_simp
  · intro a ha
    simp only [QState.setMem_mem, QState.setReg_mem]
    rw [ite_eq_right_iff.mpr, ite_eq_right_iff.mpr, ite_eq_right_iff.mpr, ite_eq_right_iff.mpr,
      ite_eq_right_iff.mpr] <;>
      exact fun e ↦ absurd (e ▸ CtxIn.word (by lay_omega) (by lay_omega)) ha
  · rf_tac

/-- **`absorb`**: a full queue permuted first, then the scalar appended with its tag. -/
theorem absorb_spec {ctx : UInt64} {sp : Sponge} {x : E} {tag : Nat}
    (hrdi : s.reg .rdi = ctx) (hsp : SpongeAt s.mem ctx sp) (hdom : Dom ctx s.mem)
    (h9 : s.reg .r9 = (x.limb 0).lane) (h10 : s.reg .r10 = (x.limb 1).lane) :
    WP (Transcript.absorb tag) s (fun s' ↦
      SpongeAt s'.mem ctx (Id.run (Compile.absorb (m := Id) keccakF1600 sp x tag)) ∧
      Keep (CtxIn ctx scratchW (countW + 1)) s.mem s'.mem ∧
      RegsFrame [.rax, .rcx, .rdx, .r8] s s') Q := by
  rw [absorb_eq]
  have hle := hsp.pendingLen
  unfold Transcript.absorb
  refine wp_load (eval_cw hrdi _) hsp.count ?_
  apply WP.blk_cons
  by_cases hf : sp.pending.length = rateScalars
  · refine wp_ite_true (by simp [Cond.eval, Rhs.eval, hf, rateScalars]; rfl) ?_
    refine WP.mono (WP.frame (duplex_spec (by simpa using hrdi) hsp hdom)) ?_ (fun _ h ↦ h.1)
    rintro s₁ ⟨⟨h₁, k₁, r₁⟩, d₁, -⟩
    simp only [hf, ↓reduceIte]
    refine WP.mono (appendPending_spec ((r₁ _ (by simp)).trans (by simpa using hrdi)) h₁
      (hdom.of_isSome d₁) (by simp [duplex_eq']; unfold rateScalars; omega)
      ((r₁ _ (by simp)).trans (by simpa using h9)) ((r₁ _ (by simp)).trans (by simpa using h10)))
      ?_ (fun _ h ↦ h)
    rintro s₂ ⟨h₂, k₂, r₂⟩
    refine ⟨h₂, (k₁.trans k₂ (fun _ h ↦ h) (fun _ h ↦ h)).mono fun _ h ↦ h, ?_⟩
    intro r hr
    rw [r₂ r (by simp_all), r₁ r (by simp_all)]
    simp only [QState.setReg_reg]
    split
    · subst r; simp at hr
    · rfl
  · refine wp_ite_false ?_ (WP.skip ?_)
    · simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte, int64_toUInt64]
      simp only [beq_eq_false_iff_ne, ne_eq]
      rw [show (4 : UInt64) = (4 : Nat).toUInt64 from rfl, toUInt64_inj (by unfold rateScalars at hle; omega) (by omega)]
      unfold rateScalars at hf
      exact hf
    simp only [hf, ↓reduceIte]
    refine WP.mono (appendPending_spec (by simpa using hrdi) hsp hdom
      (by unfold rateScalars at hf hle ⊢; omega) (by simpa using h9) (by simpa using h10)) ?_ (fun _ h ↦ h)
    rintro s₂ ⟨h₂, k₂, r₂⟩
    refine ⟨h₂, k₂, ?_⟩
    intro r hr
    rw [r₂ r (by simp_all)]
    simp only [QState.setReg_reg]
    split
    · subst r; simp at hr
    · rfl

end NativeVm.Transcript
