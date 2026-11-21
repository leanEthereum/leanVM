module

public import NativeVm.Transcript.Grind

/-!
# `commit`

`commit_spec`: from a state that simulates `st`, with fewer than `maxRoots` roots read, `height` in
`rsi` and `width` in `rbx`, `commit` ends in a state that simulates `commitStep height width st`'s,
or fails when it is `none` (a ground challenge waits, or fewer than two scalars are left).
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

variable {env : Env} {st : VerifierProgramState} {s : QState} {P Q : QState → Prop}

/-- A write to a root entry not yet read keeps the relation. -/
theorem SimState.setFree {k : Nat} (h : SimState env st s)
    (hk : rootW st.roots.length 0 ≤ k) (hk' : k < workWords) (v : UInt64) :
    SimState env st (s.setMem (wd env.work k) v) := by
  have hl := h.rootsLen
  simp only [rootW, workRoots_val, rootStride_val] at hk
  simp only [maxRoots_val] at hl
  have hne : ∀ j, j < workWords → j ≠ k → (s.setMem (wd env.work k) v).mem (wd env.work j) =
      s.mem (wd env.work j) := fun j hj hjk ↦ setMem_wd_ne _ _ hjk (by lay_omega) (by lay_omega)
  obtain ⟨c, hc, h1, h2⟩ := h.cursor
  obtain ⟨p, hp, g1, g2, g3⟩ := h.phase
  refine SimState.mk' h h.rdi (fun a ↦ isSome_setMem _ _ (h.layout.workSome _ hk') a)
    ((Keep.refl _ _).setMem (foot_work hk') _) (h.sponge.congr fun j _ _ ↦ ?_)
    ⟨c, hc, (hne _ (by lay_omega) (by lay_omega)).trans h1, h2⟩
    ⟨p, hp, (hne _ (by lay_omega) (by lay_omega)).trans g1, (hne _ (by lay_omega) (by lay_omega)).trans g2,
      g3⟩
    ((hne _ (by lay_omega) (by lay_omega)).trans h.phaseCount) hl
    ((hne _ (by lay_omega) (by lay_omega)).trans h.rootCount) fun j hj ↦ ?_
  · rw [QState.setMem_mem, ite_of_not (h.layout.work_ne_ctx hk' (by lay_omega)).symm]
  · obtain ⟨r1, r2, r3, r4, r5⟩ := h.roots j hj
    exact ⟨fun k' hk'' ↦ (hne _ (by lay_omega) (by lay_omega)).trans (r1 k' hk''), r2, r3,
      (hne _ (by lay_omega) (by lay_omega)).trans r4, (hne _ (by lay_omega) (by lay_omega)).trans r5⟩

/-- The relation through register updates. -/
theorem SimState.setReg (h : SimState env st s) {r : Reg64} (hr : r ≠ .rdi) (v : UInt64) :
    SimState env st (s.setReg r v) :=
  ⟨by reg_simp; simp only [Ne.symm hr, ↓reduceIte]; exact h.rdi, h.layout, h.decoded, h.sponge,
    h.cursor, h.phase, h.phaseCount, h.rootsLen, h.rootCount, h.roots⟩

/-- `rcx` at entry `n`'s offset. -/
theorem shl6 (n : Nat) : n.toUInt64 <<< (6 : Nat).toUInt64 = (8 * (8 * n)).toUInt64 := by
  rw [toUInt64_shl _ _ (by omega)]
  congr 1
  omega

/-- **Half a root** into the next entry, words `k`, `k + 1`. -/
theorem storeRootPair_spec {k : Nat} (h : SimState env st s) (hroom : st.roots.length < maxRoots)
    (hk : k + 1 < rootStride) :
    WP (storeRootPair k) s (fun s' ↦ SimState env st s' ∧
      s'.mem (wd env.work (rootW st.roots.length k)) = some (s.reg .r9) ∧
      s'.mem (wd env.work (rootW st.roots.length (k + 1))) = some (s.reg .r10) ∧
      (∀ j, j < workWords → j ≠ rootW st.roots.length k → j ≠ rootW st.roots.length (k + 1) →
        s'.mem (wd env.work j) = s.mem (wd env.work j)) ∧
      (∀ a, ¬ Foot env a → s'.mem a = s.mem a) ∧ RegsFrame [.rcx, .r11] s s') Q := by
  set n := st.roots.length
  unfold storeRootPair
  refine wp_load (eval_cw h.rdi _) h.layout.workPtr ?_
  refine wp_load (work_reg (by reg_simp) _) h.rootCount (wp_reg rfl ?_)
  have ea : ∀ (t : QState) j, t.reg .r11 = wd env.work 0 → t.reg .rcx = (8 * (8 * n)).toUInt64 →
      (rootAt j).eval t = wd env.work (rootW n j) := fun t j h1 h2 ↦ by
    rw [rootAt, eval_idx8 h1 h2]
    congr 1
    simp only [rootW, rootStride_val]
    omega
  have hrc : ∀ v, ((((s.setReg .r11 env.work).setReg .rcx n.toUInt64).setReg .rcx v).reg .rcx) = v :=
    fun v ↦ by reg_simp
  refine wp_store (ea _ k (by reg_simp; exact (wd_zero _).symm) (by reg_simp; exact shl6 _))
    (h.layout.workSome _ (by simp only [rootW]; lay_omega)) ?_
  refine wp_store (ea _ (k + 1) (by reg_simp; exact (wd_zero _).symm)
    (by reg_simp; exact shl6 _)) (by
      rw [QState.setMem_mem]; split
      · rfl
      · exact h.layout.workSome _ (by simp only [rootW]; lay_omega)) ?_
  have hR : RegsFrame [.rcx, .r11] s ((((s.setReg .r11 env.work).setReg .rcx n.toUInt64).setReg .rcx
      (n.toUInt64 <<< (6 : Nat).toUInt64))) := by rf_tac
  have hrdi : (((s.setReg .r11 env.work).setReg .rcx n.toUInt64).setReg .rcx
      (n.toUInt64 <<< (6 : Nat).toUInt64)).reg .rdi = env.ctx := (hR _ (by simp)).trans h.rdi
  refine wp_done ⟨?_, ?_, ?_, fun j hj h1 h2 ↦ ?_, fun a ha ↦ ?_, rf_setMem (rf_setMem hR _ _) _ _⟩
  · have h3 := (h.setReg (r := .r11) (by decide) env.work).setReg (r := .rcx) (by decide) n.toUInt64
    have h4 := h3.setReg (r := .rcx) (by decide) (n.toUInt64 <<< (6 : Nat).toUInt64)
    exact (h4.setFree (k := rootW n k) (by simp only [rootW]; lay_omega)
      (by simp only [rootW]; lay_omega) _).setFree (k := rootW n (k + 1))
      (by simp only [rootW]; lay_omega) (by simp only [rootW]; lay_omega) _
  · mem_simp
  · mem_simp
  · mem_simp
  · simp only [QState.setMem_mem, QState.setReg_mem]
    rw [ite_of_not (fun e ↦ ha (by rw [e]; exact foot_work (by lay_omega))),
      ite_of_not (fun e ↦ ha (by rw [e]; exact foot_work (by lay_omega)))]

theorem digestFromHalves_get (x0 x1 : E) :
    (digestFromHalves (x0, x1))[0] = (x0.limb 0).lane ∧ (digestFromHalves (x0, x1))[1] = (x0.limb 1).lane ∧
    (digestFromHalves (x0, x1))[2] = (x1.limb 0).lane ∧ (digestFromHalves (x0, x1))[3] = (x1.limb 1).lane :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`commit height width`**, `height` in `rsi` and `width` in `rbx`, room for one more root. -/
theorem commit_spec {height width : Nat} (h : SimState env st s) (hroom : st.roots.length < maxRoots)
    (hh : height < 2 ^ 64) (hw : width < 2 ^ 64) (hrsi : s.reg .rsi = height.toUInt64)
    (hrbx : s.reg .rbx = width.toUInt64) :
    WP commit s (fun s' ↦ ∃ st', commitStep height width st = some st' ∧ SimState env st' s' ∧
      Keeps clobbers (Foot env) s s') (fun _ ↦ commitStep height width st = none) := by
  set n := st.roots.length with hn
  have hn8 : n < 8 := hroom
  unfold commit
  refine wp_then (WP.mono (checkGround_spec h.rdi h.sponge.ground) (fun s' h' ↦ h') ?_) ?_
  · intro _ hg
    unfold commitStep
    obtain ⟨g, hg'⟩ := Option.isSome_iff_exists.mp hg
    rw [hg']
    rcases st.stream with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  rintro s₁ ⟨hg, rfl⟩
  refine nextAbsorb_then (h.setReg (by decide) 0) (fun hn' _ ↦ by unfold commitStep; rw [hn']) ?_
  intro x0 xs0 s₂ hst0 h₂ h9 h10 hw₂ k₂
  refine wp_then (storeRootPair_spec (k := 0) h₂ hroom (by lay_omega)) ?_
  rintro s₃ ⟨h₃, e0, e1, hw₃, hk₃, r₃⟩
  rw [h9] at e0
  rw [h10] at e1
  refine nextAbsorb_then h₃ (fun hn' _ ↦ by unfold commitStep; rw [hst0]; simp only at hn'; rw [hn']) ?_
  intro x1 xs s₄ hst1 h₄ g9 g10 hw₄ k₄
  refine wp_then (storeRootPair_spec (k := 2) h₄ hroom (by lay_omega)) ?_
  rintro s₅ ⟨h₅, f2, f3, hw₅, hk₅, r₅⟩
  rw [g9] at f2
  rw [g10] at f3
  simp only at hst1 h₄ h₅ f2 f3 hw₅
  have hrsi₅ : s₅.reg .rsi = height.toUInt64 := by
    rw [r₅ _ (by simp), k₄.regs _ (by simp), r₃ _ (by simp), k₂.regs _ (by simp)]; reg_simp; exact hrsi
  have hrbx₅ : s₅.reg .rbx = width.toUInt64 := by
    rw [r₅ _ (by simp), k₄.regs _ (by simp), r₃ _ (by simp), k₂.regs _ (by simp)]; reg_simp; exact hrbx
  have hL := h₅.layout
  refine wp_load (eval_cw h₅.rdi _) hL.workPtr ?_
  refine wp_load (work_reg (by reg_simp) _) h₅.rootCount (wp_reg rfl (wp_reg rfl ?_))
  have ea : ∀ (t : QState) j, t.reg .r11 = wd env.work 0 → t.reg .rcx = (8 * (8 * n)).toUInt64 →
      (rootAt j).eval t = wd env.work (rootW n j) := fun t j h1 h2 ↦ by
    rw [rootAt, eval_idx8 h1 h2]
    congr 1
    simp only [rootW, rootStride_val]
    omega
  have hwd := hL.wdom
  refine wp_store (ea _ 4 (by reg_simp; exact (wd_zero _).symm) (by reg_simp; exact shl6 _))
    (by wsome_tac) ?_
  refine wp_store (ea _ 5 (by reg_simp; exact (wd_zero _).symm) (by reg_simp; exact shl6 _))
    (by wsome_tac) ?_
  refine wp_reg rfl (wp_store (work_reg (env := env) (by reg_simp) _) (by wsome_tac) ?_)
  have hstep : commitStep height width st = some ⟨Id.run (Compile.absorb (m := Id) keccakF1600
      (Id.run (Compile.absorb (m := Id) keccakF1600 st.sponge x0 dsObserve)) x1 dsObserve), xs,
      st.openings, st.roots ++ [(digestFromHalves (x0, x1), height, width)]⟩ := by
    unfold commitStep
    rw [hst0, hst1, hg]
  refine wp_done_gen fun s₆ hs₆ ↦ ?_
  have hw₆ : ∀ j, j < workWords → j ≠ rootW n 4 → j ≠ rootW n 5 → j ≠ workRootCount →
      s₆.mem (wd env.work j) = s₅.mem (wd env.work j) := fun j hj a b c ↦ by
    rw [← hs₆]; mem_simp
  have hsome : ∀ a, (s₆.mem a).isSome = (s₅.mem a).isSome := fun a ↦ by
    rw [← hs₆]
    wisSome_tac
  have hk₆ : Keep (Foot env) s₅.mem s₆.mem := by
    rw [← hs₆]
    keep_tac
  refine ⟨_, hstep, ?_, ?_⟩
  · obtain ⟨c, hc, c1, c2⟩ := h₅.cursor
    obtain ⟨p, hp, p1, p2, p3⟩ := h₅.phase
    refine SimState.mk' h₅ (by rw [← hs₆]; reg_simp; exact h₅.rdi) hsome hk₆
      (h₅.sponge.congr fun j _ _ ↦ ?_) ⟨c, hc, (hw₆ _ (by lay_omega) (by lay_omega) (by lay_omega)
        (by lay_omega)).trans c1, c2⟩
      ⟨p, hp, (hw₆ _ (by lay_omega) (by lay_omega) (by lay_omega) (by lay_omega)).trans p1,
        (hw₆ _ (by lay_omega) (by lay_omega) (by lay_omega) (by lay_omega)).trans p2, p3⟩
      ((hw₆ _ (by lay_omega) (by lay_omega) (by lay_omega) (by lay_omega)).trans h₅.phaseCount)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; lay_omega)
      ?_ ?_
    · have hj : j < ctxEnd := by lay_omega
      rw [← hs₆]
      simp only [QState.setReg_mem, QState.setMem_mem]
      rw [ite_of_not (hL.work_ne_ctx (by lay_omega) hj).symm, ite_of_not (hL.work_ne_ctx (by lay_omega) hj).symm,
        ite_of_not (hL.work_ne_ctx (by lay_omega) hj).symm]
    · rw [← hs₆]; mem_simp
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [← hn, toUInt64_succ]
    · intro j hj
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hjn : j < n
      · rw [List.getElem_append_left hjn]
        obtain ⟨r1, r2, r3, r4, r5⟩ := h₅.roots j hjn
        exact ⟨fun k hk ↦ (hw₆ _ (by lay_omega) (by lay_omega) (by lay_omega) (by lay_omega)).trans (r1 k hk),
          r2, r3, (hw₆ _ (by lay_omega) (by lay_omega) (by lay_omega) (by lay_omega)).trans r4,
          (hw₆ _ (by lay_omega) (by lay_omega) (by lay_omega) (by lay_omega)).trans r5⟩
      · have hjn' : j = n := by omega
        subst hjn'
        have hone : ∀ i (hi : i < 1), ([(digestFromHalves (x0, x1), height, width)] :
            List (Digest × Nat × Nat))[i] = (digestFromHalves (x0, x1), height, width) := by
          intro i hi; interval_cases i; rfl
        rw [List.getElem_append_right (by omega), hone]
        obtain ⟨d0, d1, d2, d3⟩ := digestFromHalves_get x0 x1
        have w5 : ∀ k, k < 4 → s₆.mem (wd env.work (rootW n k)) = s₅.mem (wd env.work (rootW n k)) :=
          fun k hk ↦ hw₆ _ (by lay_omega) (by lay_omega) (by lay_omega) (by lay_omega)
        have w3 : ∀ k, k < 2 → s₅.mem (wd env.work (rootW n k)) = s₃.mem (wd env.work (rootW n k)) :=
          fun k hk ↦ (hw₅ _ (by lay_omega) (by lay_omega) (by lay_omega)).trans
            (hw₄ _ (by lay_omega) (by lay_omega))
        refine ⟨fun k hk ↦ ?_, hh, hw, ?_, ?_⟩
        · rw [w5 k hk]
          interval_cases k
          · rw [w3 0 (by omega), e0, d0]
          · rw [w3 1 (by omega), e1, d1]
          · rw [f2, d2]
          · rw [f3, d3]
        · rw [← hs₆]; mem_simp; rw [hrsi₅]
        · rw [← hs₆]; mem_simp; rw [hrbx₅]
  · refine ⟨by rw [← hs₆]; reg_simp; rw [h₅.rdi, h.rdi], fun r hr ↦ ?_, fun a ha ↦ ?_⟩
    · have hr' : r ∉ [Reg64.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] := by simp_all [clobbers]
      have hr'' : r ∉ [Reg64.rcx, .r11] := by simp_all [clobbers]
      rw [← hs₆]
      reg_simp
      have : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .r11 := by simp_all [clobbers]
      simp only [this.1, this.2.1, this.2.2, ↓reduceIte]
      rw [r₅ r hr'', k₄.regs r hr', r₃ r hr'', k₂.regs r hr']
      reg_simp
      simp_all [clobbers]
    · rw [hk₆ a ha, hk₅ a ha, k₄.mem a ha, hk₃ a ha, k₂.mem a ha]
      rfl

end NativeVm.Transcript
