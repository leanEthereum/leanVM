module

public import NativeVm.Code.Phase2.Kit
public import NativeVm.Code.Phase2.Model

/-!
# Phase 2: the stack's commitment and its out-of-domain claim

The code of `phase2M` (`commitStack`, `readOod`), proved against it (`phase2_ok : Phase2Ok phase2`).

Within the window phase 1 checked, `commitStack` reads the stack's root of `2^(μ − 6 + rate)`
leaves of `64` words (`phase2M_eq`): `phase2Shape` puts that shape in `rsi`, `rbx` for `commit`.
Then the grind of `oodGrindingBits = 15`, and the `μ` challenges `z` (`oodLoop`, `r13` counting
down, `r12` at the next coordinate) straight into `EqClaimAt`'s vector at `oodR` (its count `μ`
first, `oodStart`), and the value read into its last two words (`oodValue`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters

/-! ## The code -/

/-- The stack's shape: `rsi := μ − 6 + rate`, `rbx := 64`. -/
def phase2Shape : Stmt := blk [
  I (.load .r11 (cw ctxWork)),
  I (.load .rsi (at_ .r11 (wdisp (layoutR.off + 2)))),
  I (.load .rax (at_ .r11 (wdisp (layoutR.off + 3)))),
  I (.subi .rsi 6), I (.add .rsi .rax), I (.movi .rbx 64)]

/-- The point's count `μ` at `oodR`; `r13 := μ`, `r12` at its first coordinate. -/
def oodStart : Stmt := blk [
  I (.load .r11 (cw ctxWork)),
  I (.load .r13 (at_ .r11 (wdisp (layoutR.off + 2)))),
  I (.store (at_ .r11 (wdisp oodR.off)) .r13),
  I (.lea .r12 (at_ .r11 (wdisp (oodR.off + 1))))]

/-- One coordinate: a challenge stored at `r12`. -/
def oodStep : Stmt := blk [
  Transcript.sampleChallenge,
  I (.store (at_ .r12 (wdisp 0)) .r9), I (.store (at_ .r12 (wdisp 1)) .r10),
  I (.addi .r12 (wdisp 2)), I (.subi .r13 1)]

/-- The value, read into `r9`, `r10`, after the point. -/
def oodValue : Stmt := blk [
  I (.load .r11 (cw ctxWork)),
  I (.store (at_ .r11 (wdisp (oodR.off + vecWords stackCap))) .r9),
  I (.store (at_ .r11 (wdisp (oodR.off + vecWords stackCap + 1))) .r10)]

/-- **Phase 2**: the stack's commitment and its out-of-domain claim. -/
def phase2 : Stmt := blk [
  phase2Shape, Transcript.commit, I (.movi .rsi 15), Transcript.grind,
  oodStart, .loop (.cmp .ne .r13 (.imm 0)) oodStep, Transcript.readScalar, oodValue]

/-! ## Numbers -/

theorem oodR_off : oodR.off = 559 := by decide
theorem oodR_size : oodR.size = 63 := by decide
theorem stackCap_val : stackCap = 30 := (rfl)
theorem vecWords_stackCap : vecWords stackCap = 61 := (rfl)

/-- The phase's regions. -/
abbrev rs2 : List Region := [oodR, scratchR]

theorem rs2_regions : ∀ r ∈ rs2, r ∈ regions := by decide +kernel

theorem oodR_mem : oodR ∈ regions := by decide +kernel

theorem toUInt64_sub6 {a : Nat} (h : 6 ≤ a) : a.toUInt64 - 6 = (a - 6).toUInt64 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 6 := ⟨a - 6, by omega⟩
  rw [Nat.add_sub_cancel, ← toUInt64_add]
  simp

/-! ## The loop -/

/-- After `k` of the `n` coordinates `acc`: the counters, the count word, the coordinates. -/
def OodX (env : Env) (n k : Nat) (acc : Array EW) (s : QState) : Prop :=
  n ≤ 30 ∧ k ≤ n ∧ acc.size = k ∧ s.reg .r13 = (n - k).toUInt64 ∧
    s.reg .r12 = wd env.work (oodR.off + 1 + 2 * k) ∧ NatAt s.mem (oodR.at env.work) n ∧
    EWArr s.mem (wd env.work (oodR.off + 1)) acc

theorem OodX.stable {env : Env} {inp : Input} {mem : UInt64 → Option UInt64}
    (hin : Inputs env inp mem) {n k : Nat} {acc : Array EW} : Stable env (OodX env n k acc) := by
  rintro s s' ⟨h1, h2, h3, h4, h5, h6, h7⟩ hk
  have hS := hin.keeps_same hk oodR_mem
  refine ⟨h1, h2, h3, (hk.reg (by decide)).trans h4, (hk.reg (by decide)).trans h5,
    h6.congr (hS.base (by rw [oodR_size]; omega) rfl), h7.congr (n := 2 * acc.size) ?_ le_rfl⟩
  have := hS.sub (a := 1) (m := 2 * acc.size) (by rw [oodR_size]; omega)
  rwa [Region.at, wd_wd] at this

theorem EWArr.push {mem : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} {x : EW}
    (h : EWArr mem p xs) (hx : EWAt mem (wd p (2 * xs.size)) x) : EWArr mem p (xs.push x) := by
  intro i hi
  rw [Array.size_push] at hi
  rw [Array.getElem_push]
  split
  · exact h i (by omega)
  · rw [show i = xs.size by omega]
    exact hx

/-- **One coordinate.** -/
theorem oodStep_ref {env : Env} {inp : Input} {s0 : QState} (hin : Inputs env inp s0.mem)
    {n k : Nat} (hk : k < n) (acc : Array EW) :
    Refines (fun t s ↦ CodeRel env t s ∧ Fr env rs2 s0 (OodX env n k acc) s) oodStep
      (Model.sampleChallenge >>= fun x ↦ pure (acc.push x))
      (fun acc' t' s' ↦ CodeRel env t' s' ∧ Fr env rs2 s0 (OodX env n (k + 1) acc') s')
      (Kept env rs2 s0) := by
  unfold oodStep
  refine Refines.blk_cons (sampleChallenge_fr (OodX.stable hin)) fun x ↦ Refines.pure ?_
  rintro t s ⟨hc, ⟨hb, h1, h2, h3, h4, h5, h6, h7⟩, h9, h10⟩
  have hww := workWords_lt hin
  have ho := oodR_off
  have hr12 : s.reg .r12 = wd env.work (oodR.off + 1 + 2 * k) := h5
  have e0 : wd (wd env.work (oodR.off + 1 + 2 * k)) 0 = wd env.work (oodR.off + (1 + 2 * k)) := by
    rw [wd_wd]; congr 1; omega
  have e1 : wd (wd env.work (oodR.off + 1 + 2 * k)) 1 = wd env.work (oodR.off + (2 + 2 * k)) := by
    rw [wd_wd]; congr 1; omega
  have hj0 : 1 + 2 * k < oodR.size := by rw [oodR_size]; omega
  have hj1 : 2 + 2 * k < oodR.size := by rw [oodR_size]; omega
  have hs0 := hin.region_some hb oodR_mem hj0
  refine wp_store ((eval_work hr12 0).trans e0) hs0 ?_
  have hb1 := hb.setMem (q := oodR) (by simp) hj0 rfl hs0 (s.reg .r9)
  have hs1 := hin.region_some hb1 oodR_mem hj1
  refine wp_store ((eval_work (by reg_simp; exact hr12) 1).trans e1) hs1 ?_
  have hb2 := hb1.setMem (q := oodR) (by simp) hj1 rfl hs1 (s.reg .r10)
  refine wp_reg rfl (wp_reg rfl (wp_done ?_))
  simp only [QState.setMem_reg] at hb2 ⊢
  refine ⟨((((hc.setMem hin oodR_mem hj0 rfl hs0 _).setMem hin oodR_mem hj1 rfl hs1 _).setReg
    (by decide) _).setReg (by decide) _),
    ⟨(hb2.setReg (by decide) _).setReg (by decide) _, h1, by omega, by rw [Array.size_push, h3],
      ?_, ?_, ?_, ?_⟩⟩
  · reg_simp
    rw [h4, toUInt64_sub1 (by omega)]
    congr 1
  · reg_simp
    rw [hr12, wdisp_toUInt64, wd_add]
    congr 1
  · have hS : Same s.mem (((s.setMem (wd env.work (oodR.off + (1 + 2 * k))) (s.reg .r9)).setMem
        (wd env.work (oodR.off + (2 + 2 * k))) (s.reg .r10))).mem (oodR.at env.work) 1 := by
      intro j hj
      rw [Region.at, wd_wd, setMem_wd_ne _ _ (by omega) (by omega) (by omega),
        setMem_wd_ne _ _ (by omega) (by omega) (by omega)]
    simp only [QState.setReg_mem]
    exact h6.congr (hS.base (by omega) rfl)
  · simp only [QState.setReg_mem]
    refine EWArr.push (h7.congr (n := 2 * acc.size) (fun j hj ↦ ?_) le_rfl) ⟨?_, ?_⟩
    · rw [wd_wd, setMem_wd_ne _ _ (by omega) (by omega) (by omega),
        setMem_wd_ne _ _ (by omega) (by omega) (by omega)]
    · rw [wd_wd, h3, setMem_wd_ne _ _ (by omega) (by omega) (by omega),
        setMem_wd_eq _ _ (by omega), h9]
    · rw [wd_wd, wd_wd, h3, setMem_wd_eq _ _ (by omega), h10]

/-! ## The contract -/

/-- **Phase 2 computes `phase2M`.** -/
theorem phase2_ok : Phase2Ok phase2 := by
  intro env inp t0 s0 layout rate hc hroom hin hlay
  obtain ⟨hb1, hb2⟩ := hlay.stackLogBound
  obtain ⟨hr1, hr2⟩ := hlay.rateBound
  simp only [Whir.minLogStack, Whir.maxLogStack] at hb1 hb2
  have hww := workWords_lt hin
  have ho := oodR_off
  have hn : NatAt s0.mem (wd env.work (layoutR.off + 2)) layout.stackLog := by
    have := hlay.stackLog; rwa [Region.at, wd_wd] at this
  have hrt : NatAt s0.mem (wd env.work (layoutR.off + 3)) rate := by
    have := hlay.rateWord; rwa [Region.at, wd_wd] at this
  have hbase : Base env rs2 s0 s0 := Base.start hc.rdi
  have hlayS : ∀ s, Base env rs2 s0 s → ∀ j < 4,
      s.mem (wd env.work (layoutR.off + j)) = s0.mem (wd env.work (layoutR.off + j)) := by
    intro s hb j hj
    have := hb.same hin rs2_regions (q := layoutR) (by decide +kernel) (by decide +kernel) j
      (by rw [layoutR_size]; omega)
    rwa [Region.at, wd_wd] at this
  apply runs_of_refines
  rw [phase2M_eq hb1 hb2 hr1 hr2]
  unfold phase2
  -- the stack's shape
  refine Refines.pre_blk (P' := fun t s ↦ CodeRel env t s ∧ Fr env rs2 s0 (fun _ ↦ True) s ∧
    t.roots.size < maxRoots ∧ s.reg .rsi = (layout.stackLog - 6 + rate).toUInt64 ∧
    s.reg .rbx = (64 : Nat).toUInt64) ?_ ?_
  · rintro t s ⟨rfl, rfl⟩
    unfold phase2Shape
    refine wp_load (eval_cw hc.rdi _) hc.layout.workPtr ?_
    refine wp_load (eval_work (w := env.work) (by reg_simp) _)
      (by rw [QState.setReg_mem]; exact hn.2) ?_
    refine wp_load (eval_work (w := env.work) (by reg_simp) _)
      (by simp only [QState.setReg_mem]; exact hrt.2) ?_
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_done ⟨?_, ⟨?_, trivial⟩, hroom, ?_, ?_⟩)))
    · exact (((((hc.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _).setReg
        (by decide) _).setReg (by decide) _).setReg (by decide) _
    · exact (((((hbase.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _).setReg
        (by decide) _).setReg (by decide) _).setReg (by decide) _
    · reg_simp
      rw [toUInt64_sub6 (by omega), toUInt64_add]
    · reg_simp
      rfl
  -- the root
  refine Refines.blk_cons (commit_fr (by omega) (by omega) stable_true) fun _ ↦ ?_
  refine Refines.pre_blk (P' := fun t s ↦ CodeRel env t s ∧ Fr env rs2 s0 (fun _ ↦ True) s ∧
    s.reg .rsi = (15 : Nat).toUInt64) ?_ ?_
  · rintro t s ⟨hc', hf⟩
    exact WP.ins rfl ⟨hc'.setReg (by decide) _, ⟨hf.1.setReg (by decide) _, trivial⟩,
      by reg_simp; rfl⟩
  -- the grind
  refine Refines.blk_cons (grind_fr (by decide) (by decide) stable_true) fun _ ↦ ?_
  -- the point's count
  refine Refines.pre_blk (P' := fun t s ↦ CodeRel env t s ∧
    Fr env rs2 s0 (OodX env layout.stackLog 0 #[]) s) ?_ ?_
  · rintro t s ⟨hc', hb', -⟩
    have hrdi : s.reg .rdi = env.ctx := hb'.1.1
    unfold oodStart
    refine wp_load (eval_cw hrdi _) hc'.layout.workPtr ?_
    refine wp_load (eval_work (w := env.work) (by reg_simp) _)
      (by rw [QState.setReg_mem, hlayS s hb' 2 (by omega)]; exact hn.2) ?_
    have hj0 : 0 < oodR.size := by rw [oodR_size]; omega
    have hs0 := hin.region_some hb' oodR_mem hj0
    refine wp_store (eval_work (w := env.work) (by reg_simp) _)
      (by simp only [QState.setReg_mem]; exact hs0) ?_
    refine wp_reg rfl (wp_done ⟨?_, ⟨?_, by omega, by omega, rfl, ?_, ?_, ⟨hn.1, ?_⟩, ?_⟩⟩)
    · exact (((hc'.setReg (by decide) _).setReg (by decide) _).setMem hin oodR_mem hj0 rfl
        (by simp only [QState.setReg_mem]; exact hs0) _).setReg (by decide) _
    · exact (((hb'.setReg (by decide) _).setReg (by decide) _).setMem (by simp) hj0 rfl
        (by simp only [QState.setReg_mem]; exact hs0) _).setReg (by decide) _
    · reg_simp
      rfl
    · reg_simp
      rw [eval_work (w := env.work) (by reg_simp) _]
    · simp only [Region.at, QState.setReg_mem, QState.setMem_mem, ↓reduceIte, QState.setReg_reg]
    · exact fun i h ↦ absurd h (Nat.not_lt_zero _)
  -- the coordinates
  have hloop : Refines (fun t s ↦ CodeRel env t s ∧
      Fr env rs2 s0 (OodX env layout.stackLog 0 #[]) s)
      (.loop (.cmp .ne .r13 (.imm 0)) oodStep) (sampleChallenges layout.stackLog)
      (fun z t s ↦ CodeRel env t s ∧ Fr env rs2 s0 (OodX env layout.stackLog layout.stackLog z) s)
      (Kept env rs2 s0) := by
    refine Refines.mono (Refines.foldlM (l := List.range layout.stackLog)
      (Inv := fun k acc t s ↦ CodeRel env t s ∧ Fr env rs2 s0 (OodX env layout.stackLog k acc) s)
      ?_ ?_ (init := #[])) (fun _ _ h ↦ h) (fun _ _ _ h ↦ by rwa [List.length_range] at h)
      (fun _ h ↦ h)
    · rintro k acc t s ⟨-, -, -, h2, -, h4, -⟩
      rw [List.length_range, cond_ne, rhs_imm, h4,
        show ((0 : Int64).toUInt64) = (0 : Nat).toUInt64 from rfl, bne_iff_ne, ne_eq,
        toUInt64_inj (by omega) (by omega)]
      omega
    · intro k hk acc
      rw [List.length_range] at hk
      exact oodStep_ref hin hk acc
  refine Refines.blk_cons hloop fun z ↦ ?_
  -- the value
  refine Refines.blk_cons (readScalar_fr (OodX.stable hin)) fun v ↦ Refines.pure ?_
  rintro t s ⟨hc', ⟨hb', h1, -, h3, -, -, h6, h7⟩, h9, h10⟩
  change WP oodValue s _ _
  unfold oodValue
  refine wp_load (eval_cw hb'.1.1 _) hc'.layout.workPtr ?_
  have hj1 : vecWords stackCap < oodR.size := by rw [oodR_size, vecWords_stackCap]; omega
  have hj2 : vecWords stackCap + 1 < oodR.size := by rw [oodR_size, vecWords_stackCap]; omega
  have hs1 := hin.region_some hb' oodR_mem hj1
  refine wp_store (eval_work (w := env.work) (by reg_simp) _)
    (by simp only [QState.setReg_mem]; exact hs1) ?_
  have hb1 := (hb'.setReg (d := .r11) (by decide) env.work).setMem (q := oodR) (by simp) hj1 rfl
    (by simp only [QState.setReg_mem]; exact hs1) (s.reg .r9)
  have hs2 := hin.region_some hb1 oodR_mem hj2
  rw [← Nat.add_assoc] at hs2
  refine wp_store (eval_work (w := env.work) (by reg_simp) _) hs2 ?_
  have hb2 := hb1.setMem (q := oodR) (by simp) hj2 (by rw [Nat.add_assoc]) hs2 (s.reg .r10)
  have hv := vecWords_stackCap
  refine wp_done ⟨?_, ⟨z, rfl, ⟨by rw [h3]; exact h1, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact (((hc'.setReg (by decide) _).setMem hin oodR_mem hj1 rfl
      (by simp only [QState.setReg_mem]; exact hs1) _).setMem hin oodR_mem hj2
      (by rw [Nat.add_assoc]) hs2 _)
  · rw [h3]
    refine ⟨h6.1, ?_⟩
    rw [Region.at, ← h6.2, setMem_wd_ne _ _ (by omega) (by omega) (by omega),
      setMem_wd_ne _ _ (by omega) (by omega) (by omega), QState.setReg_mem]
    rfl
  · rw [show wd (oodR.at env.work) 1 = wd env.work (oodR.off + 1) from wd_wd _ _ _]
    refine h7.congr (n := 2 * z.size) (fun j hj ↦ ?_) le_rfl
    rw [wd_wd, setMem_wd_ne _ _ (by omega) (by omega) (by omega),
      setMem_wd_ne _ _ (by omega) (by omega) (by omega), QState.setReg_mem]
  · rw [show wd (oodR.at env.work) (vecWords stackCap) = wd env.work (oodR.off + vecWords stackCap)
      from wd_wd _ _ _]
    refine ⟨?_, ?_⟩
    · rw [setMem_wd_ne _ _ (by omega) (by omega) (by omega), setMem_wd_eq _ _ rfl]
      try reg_simp
      rw [h9]
    · rw [wd_wd, setMem_wd_eq _ _ (by omega)]
      try reg_simp
      rw [h10]
  · exact hb2.1

end NativeVm.Code
