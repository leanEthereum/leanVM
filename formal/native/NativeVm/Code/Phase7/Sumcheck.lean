module

public import NativeVm.Code.Phase7.EOps
public import NativeVm.Code.Phase7.Scalars

/-!
# Phase 7: the final level's sumcheck

`sumcheckC` runs `sumcheckPlain claim 3 mu`: the rounds `mu` at work word `cMu`, the running claim
in the pair at work words `tmpO + 14`, `tmpO + 15`, the challenges stored at `spO + 2 i`. A round
(`smcRound`) reads `c₀` (to `tmpO`) and `t` (to `tmpO + 2`); its grind is of `grindingBits 2 = 0`
bits, no code; the challenge `r` goes to the point and to `tmpO + 4`; the new claim
`polyEval #[c₀, claim + t, t] r = ((t·r + claim) + t)·r + c₀` (`smcPoly`) by the `E` operations on
the area (`NativeVm.Code.Phase7.EOps`). The rounds left are in `r15`, the next challenge's address
in `r13`, the area's in `rbp`: the gadgets and the `E` operations keep all three.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model NativeVm.Field
open NativeVm.Transcript (wd Env ctxWork clobbers wd_inj wd_add wp_load wp_store wp_reg cond_ne
  rhs_imm eval_cw rf_trans)

/-! ## The model -/

/-- One plain round of degree 2, its grind of no bits dropped. -/
def smcRound (acc : Array EW × EW) : VM (Array EW × EW) := do
  let c0 ← readScalar
  let tt ← readScalar
  let r ← sampleChallenge
  pure (acc.1.push r, (tt * r + acc.2 + tt) * r + c0)

theorem smcPoly (c0 cl tt r : EW) :
    polyEval (#[c0, cl + sumE #[tt]] ++ #[tt]) r = (tt * r + cl + tt) * r + c0 := by
  have e : polyEval (#[c0, cl + sumE #[tt]] ++ #[tt]) r =
      ((0 * r + tt) * r + (cl + (0 + tt))) * r + c0 := rfl
  rw [e]
  apply Equiv.EW.toE_injective
  simp only [Equiv.EW.toE_add, Equiv.EW.toE_mul, Equiv.EW.toE_zero]
  ring

/-- `sumcheck`'s step on a plain round of three coefficients. -/
def smcStep (acc : Array EW × EW) (equality : Option EW) : VM (Array EW × EW) := do
  let message ← sumcheckRoundPoly 3 acc.2 equality
  let challenge ← sampleChallenge
  pure (acc.1.push challenge, polyEval message challenge)

theorem smcStep_none (acc : Array EW × EW) : smcStep acc none = smcRound acc := by
  simp only [smcStep, sumcheckRoundPoly, readScalars, show grindingBits (3 - 1) = 0 by decide,
    grind, ite_true, show 3 - 2 = 1 from rfl, List.range_one, List.foldlM_cons, List.foldlM_nil,
    bind_assoc, pure_bind, smcRound]
  simp only [show ∀ x : EW, (#[] : Array EW).push x = #[x] from fun _ ↦ rfl, smcPoly]

theorem sumcheckPlain_eq (claim : EW) (mu : Nat) :
    sumcheckPlain claim 3 mu = (List.replicate mu (none : Option EW)).foldlM smcStep (#[], claim) := by
  rw [sumcheckPlain, sumcheck, ← Array.foldlM_toList, Array.toList_replicate]
  rfl

/-! ## Stores to the area -/

variable {p : Par} {t : TState} {s : QState} {P F : QState → Prop} {rest : List Stmt}

theorem smc_frM_regs {s s' : QState} (hrdi : s'.reg .rdi = s.reg .rdi) (hm : s'.mem = s.mem) :
    FrM p.env s s' :=
  ⟨hrdi, fun a ↦ by rw [hm], fun a _ ↦ by rw [hm]⟩

/-- Two stores, of `r9` and `r10`, to the area's words `j`, `j + 1`. -/
theorem smc_st2_wp {j : Nat} {a0 a1 : Addr} (hj : mineLo ≤ j ∧ j + 1 < dataEnd)
    (hb : Base p t s) (ha0 : a0.eval s = wd p.env.work j) (ha1 : a1.eval s = wd p.env.work (j + 1))
    (h : ∀ s' : QState, Base p t s' → s'.reg = s.reg →
      EWAt s'.mem (wd p.env.work j) ⟨s.reg .r9, s.reg .r10⟩ →
      (∀ i, i < 2 ^ 61 → (i < j ∨ j + 1 < i) → s'.mem (wd p.env.work i) = s.mem (wd p.env.work i)) →
      WP (blk rest) s' P F) :
    WP (blk (I (.store a0 .r9) :: I (.store a1 .r10) :: rest)) s P F := by
  have hww := workWords_ge p.inp.bytecode.size
  have de := dataEnd_eq
  have ml := mineLo_val
  have h0 : (s.mem (wd p.env.work j)).isSome := hb.inp.workSome _ (by omega)
  have h1 : (s.mem (wd p.env.work (j + 1))).isSome := hb.inp.workSome _ (by omega)
  have ne : wd p.env.work (j + 1) ≠ wd p.env.work j := fun e ↦ by
    have := (wd_inj (by omega) (by omega)).mp e; omega
  have h1' : ((s.setMem (wd p.env.work j) (s.reg .r9)).mem (wd p.env.work (j + 1))).isSome := by
    rw [NativeVm.Transcript.isSome_setMem _ _ h0]; exact h1
  refine wp_store ha0 h0 (wp_store (x := wd p.env.work (j + 1)) ha1 h1' ?_)
  refine h _ (hb.frM ⟨rfl, fun a ↦ ?_, fun a ha ↦ ?_⟩) rfl ⟨?_, ?_⟩ fun i hi hne ↦ ?_
  · rw [NativeVm.Transcript.isSome_setMem _ _ h1', NativeVm.Transcript.isSome_setMem _ _ h0]
  · have n0 : a ≠ wd p.env.work j := fun e ↦ ha (e ▸ inMine_wd hj.1 (by omega))
    have n1 : a ≠ wd p.env.work (j + 1) := fun e ↦ ha (e ▸ inMine_wd (by omega) hj.2)
    simp only [QState.setMem_mem, n0, n1, ite_false]
  · simp only [QState.setMem_mem, Ne.symm ne, ite_true, ite_false]
  · rw [wd_wd]
    simp only [QState.setMem_mem, ite_true]
    rfl
  · have n0 : wd p.env.work i ≠ wd p.env.work j := fun e ↦ by
      have := (wd_inj hi (by omega)).mp e; omega
    have n1 : wd p.env.work i ≠ wd p.env.work (j + 1) := fun e ↦ by
      have := (wd_inj hi (by omega)).mp e; omega
    simp only [QState.setMem_mem, n0, n1, ite_false]

theorem smc_ewAt_keep {m m' : UInt64 → Option UInt64} {b : UInt64} {j jj : Nat} {x : EW}
    (h : EWAt m (wd b j) x)
    (he : ∀ i, i < 2 ^ 61 → (i < jj ∨ jj + 1 < i) → m' (wd b i) = m (wd b i))
    (hj : j + 1 < 2 ^ 61) (hd : j + 1 < jj ∨ jj + 1 < j) : EWAt m' (wd b j) x := by
  refine ⟨by rw [he j (by omega) (by omega)]; exact h.1, ?_⟩
  rw [wd_wd, he (j + 1) hj (by omega)]
  rw [← wd_wd]
  exact h.2

theorem smc_ewArr_keep {m m' : UInt64 → Option UInt64} {b : UInt64} {o jj : Nat} {xs : Array EW}
    (h : EWArr m (wd b o) xs)
    (he : ∀ i, i < 2 ^ 61 → (i < jj ∨ jj + 1 < i) → m' (wd b i) = m (wd b i))
    (hb : o + 2 * xs.size < 2 ^ 61) (hd : o + 2 * xs.size ≤ jj ∨ jj + 1 < o) :
    EWArr m' (wd b o) xs := fun i hi ↦ by
  have := smc_ewAt_keep (j := o + 2 * i) (by rw [← wd_wd]; exact h i hi) he (by omega) (by omega)
  rwa [← wd_wd] at this

theorem smc_only_keep {env : Env} {W : Nat → Prop} {m0 m m' : UInt64 → Option UInt64} {jj : Nat}
    (h : Only env W m0 m)
    (he : ∀ i, i < 2 ^ 61 → (i < jj ∨ jj + 1 < i) → m' (wd env.work i) = m (wd env.work i))
    (hw : W jj ∧ W (jj + 1)) : Only env W m0 m' := fun k h1 h2 hk ↦ by
  have de := dataEnd_eq
  have hne : k < jj ∨ jj + 1 < k := by
    rcases Nat.lt_or_ge k jj with h' | h'
    · exact .inl h'
    · rcases Nat.lt_or_ge (jj + 1) k with h'' | h''
      · exact .inr h''
      · exfalso
        rcases Nat.eq_or_lt_of_le h' with e | e
        · exact hk (e ▸ hw.1)
        · exact hk (by rw [show k = jj + 1 by omega]; exact hw.2)
  rw [he k (by omega) hne]
  exact h k h1 h2 hk

theorem smc_ewArr_push {m : UInt64 → Option UInt64} {b : UInt64} {o : Nat} {xs : Array EW}
    {x : EW} (h : EWArr m (wd b o) xs) (hx : EWAt m (wd b (o + 2 * xs.size)) x) :
    EWArr m (wd b o) (xs.push x) := fun i hi ↦ by
  rw [Array.size_push] at hi
  rw [Array.getElem_push]
  split
  · exact h i ‹_›
  · rw [show i = xs.size by omega, wd_wd]
    exact hx

/-! ## The loop's state -/

/-- The words `sumcheckC` writes: the point and the temporaries. -/
abbrev smcW : Nat → Prop := fun k ↦ spO ≤ k ∧ k < spO + 64 ∨ tmpO ≤ k ∧ k < tmpO + 32

/-- The area's facts after `k` rounds. -/
def SmcM (p : Par) (m0 : UInt64 → Option UInt64) (mu k : Nat) (acc : Array EW × EW)
    (mem : UInt64 → Option UInt64) : Prop :=
  k ≤ mu ∧ acc.1.size = k ∧ EWArr mem (wd p.env.work spO) acc.1 ∧
    EWAt mem (wd p.env.work (tmpO + 14)) acc.2 ∧ Only p.env smcW m0 mem

/-- The registers and the area after `k` rounds. -/
def SmcR (p : Par) (m0 : UInt64 → Option UInt64) (mu k : Nat) (acc : Array EW × EW)
    (s : QState) : Prop :=
  s.reg .rbp = p.env.work ∧ s.reg .r15 = (mu - k).toUInt64 ∧
    s.reg .r13 = wd p.env.work (spO + 2 * k) ∧ SmcM p m0 mu k acc s.mem

theorem smc_ewAt_mine {env : Env} {j : Nat} {x : EW} (hj : mineLo ≤ j ∧ j + 1 < dataEnd) :
    MineOnly env fun m ↦ EWAt m (wd env.work j) x := by
  intro m m' hm h
  refine ⟨by rw [hm _ (inMine_wd hj.1 (by omega))]; exact h.1, ?_⟩
  rw [wd_wd, hm _ (inMine_wd (by omega) hj.2), ← wd_wd]
  exact h.2

theorem smcM_mine {m0 : UInt64 → Option UInt64} {mu k : Nat} {acc : Array EW × EW}
    (hmu : mu ≤ 30) : MineOnly p.env (SmcM p m0 mu k acc) := by
  intro m m' hm ⟨hk, hsz, harr, hcl, hon⟩
  have so := scratch_off
  have hto : tmpO = scratchR.off + 32 := rfl
  have sp : spO = scratchR.off + 1280 := rfl
  have ml := mineLo_val
  have de := dataEnd_eq
  refine ⟨hk, hsz, fun i hi ↦ ?_, smc_ewAt_mine (by omega) m m' hm hcl, fun k h1 h2 hk ↦ ?_⟩
  · have := smc_ewAt_mine (env := p.env) (j := spO + 2 * i) (x := acc.1[i]) (by omega) m m' hm
      (by rw [← wd_wd]; exact harr i hi)
    rwa [← wd_wd] at this
  · rw [hm _ (inMine_wd h1 h2)]
    exact hon k h1 h2 hk

theorem smcR_gok {m0 : UInt64 → Option UInt64} {mu k : Nat} {acc : Array EW × EW}
    (hmu : mu ≤ 30) : GOk p.env p.inp (SmcR p m0 mu k acc) :=
  GOk.and (GOk.reg (by decide) _) (GOk.and (GOk.reg (by decide) _)
    (GOk.and (GOk.reg (by decide) _) (GOk.of_mine (smcM_mine hmu))))

/-! ## The code -/

/-- One round: `c₀` to `tmpO`, `t` to `tmpO + 2`, `r` to the point and `tmpO + 4`, the new claim
to `tmpO + 14`. -/
def smcRoundC : Stmt := blk [
  Transcript.readScalar, blk (stA tmpO),
  Transcript.readScalar, blk (stA (tmpO + 2)),
  Transcript.sampleChallenge,
  blk ([I (.store (at_ .r13 0) .r9), I (.store (at_ .r13 8) .r10)] ++ stA (tmpO + 4) ++
    ldA (tmpO + 2) ++ mulM (tmpO + 4) ++ addM (tmpO + 14) ++ addM (tmpO + 2) ++ mulM (tmpO + 4) ++
    addM tmpO ++ stA (tmpO + 14) ++ [I (.addi .r13 16), I (.subi .r15 1)])]

/-- **The final level's sumcheck**: `mu` at work word `cMu`, the claim at `tmpO + 14`. -/
def sumcheckC : Stmt := blk [ldW, ldw .r15 cMu, leaw .r13 spO,
  .loop (.cmp .ne .r15 (.imm 0)) smcRoundC]

/-- The registers the `E` operations write. -/
abbrev smcOpRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12]

/-- A store to a temporary keeps the loop's state. -/
theorem smc_tmp_store {m0 : UInt64 → Option UInt64} {mu k : Nat} {acc : Array EW × EW}
    {j : Nat} {s' : QState} (hmu : mu ≤ 30) (hj : tmpO ≤ j ∧ j + 1 < tmpO + 14)
    (hR : SmcR p m0 mu k acc s) (hreg : s'.reg = s.reg)
    (he : ∀ i, i < 2 ^ 61 → (i < j ∨ j + 1 < i) → s'.mem (wd p.env.work i) = s.mem (wd p.env.work i)) :
    SmcR p m0 mu k acc s' := by
  obtain ⟨hbp, h15, h13, hk, hsz, harr, hcl, hon⟩ := hR
  have so := scratch_off
  have hto : tmpO = scratchR.off + 32 := rfl
  have sp : spO = scratchR.off + 1280 := rfl
  refine ⟨by rw [hreg]; exact hbp, by rw [hreg]; exact h15, by rw [hreg]; exact h13, hk, hsz,
    smc_ewArr_keep harr he (by omega) (by omega), smc_ewAt_keep hcl he (by omega) (by omega),
    smc_only_keep hon he ⟨.inr ⟨by omega, by omega⟩, .inr ⟨by omega, by omega⟩⟩⟩

/-- **A round.** -/
theorem smcRoundC_spec {m0 : UInt64 → Option UInt64} {mu k : Nat} (hmu : mu ≤ 30) (hk : k < mu)
    (acc : Array EW × EW) :
    Refines (fun t s ↦ Base p t s ∧ SmcR p m0 mu k acc s) smcRoundC (smcRound acc)
      (fun acc' t s ↦ Base p t s ∧ SmcR p m0 mu (k + 1) acc' s) (Err p) := by
  have so := scratch_off
  have hto : tmpO = scratchR.off + 32 := rfl
  have sp : spO = scratchR.off + 1280 := rfl
  have ml := mineLo_val
  have de := dataEnd_eq
  have hR0 := smcR_gok (p := p) (m0 := m0) (k := k) (acc := acc) hmu
  unfold smcRoundC smcRound
  refine Refines.blk_cons (readScalar_b hR0) fun c0 ↦ ?_
  refine Refines.pre_blk (P' := fun t s ↦ Base p t s ∧ SmcR p m0 mu k acc s ∧
      EWAt s.mem (wd p.env.work tmpO) c0) ?_ ?_
  · rintro t s ⟨hb, hR, h9, h10⟩
    refine smc_st2_wp (rest := []) (by omega) hb (eval_w hR.1 _) (eval_w hR.1 _)
      fun s' hb' hreg hx he ↦ WP.blk_nil ⟨hb', smc_tmp_store hmu (by omega) hR hreg he, ?_⟩
    rw [h9, h10] at hx
    exact hx
  have hR1 := GOk.and hR0 (GOk.of_mine (smc_ewAt_mine (env := p.env) (j := tmpO) (x := c0)
    (by omega)))
  refine Refines.blk_cons (readScalar_b hR1) fun tt ↦ ?_
  refine Refines.pre_blk (P' := fun t s ↦ Base p t s ∧ (SmcR p m0 mu k acc s ∧
      EWAt s.mem (wd p.env.work tmpO) c0) ∧ EWAt s.mem (wd p.env.work (tmpO + 2)) tt) ?_ ?_
  · rintro t s ⟨hb, ⟨hR, hc0⟩, h9, h10⟩
    refine smc_st2_wp (rest := []) (by omega) hb (eval_w hR.1 _) (eval_w hR.1 _)
      fun s' hb' hreg hx he ↦ WP.blk_nil ⟨hb', ⟨smc_tmp_store hmu (by omega) hR hreg he,
        smc_ewAt_keep hc0 he (by omega) (by omega)⟩, ?_⟩
    rw [h9, h10] at hx
    exact hx
  have hR2 := GOk.and hR1 (GOk.of_mine (smc_ewAt_mine (env := p.env) (j := tmpO + 2) (x := tt)
    (by omega)))
  refine Refines.blk_cons (sample_b hR2) fun r ↦ Refines.pure ?_
  rintro t s ⟨hb, ⟨⟨hR, hc0⟩, htt⟩, h9, h10⟩
  obtain ⟨hbp, h15, h13, hkm, hsz, harr, hcl, hon⟩ := hR
  -- the challenge to the point
  refine smc_st2_wp (j := spO + 2 * k) (by omega) hb
    (by rw [eval_at, h13, int64Zero_toUInt64, UInt64.add_zero])
    (by rw [eval_at, h13, show (8 : Int64).toUInt64 = (8 * 1 : Nat).toUInt64 from rfl, wd_add])
    fun s1 hb1 hr1 hx1 he1 ↦ ?_
  rw [h9, h10] at hx1
  have w1 : s1.reg .rbp = p.env.work := by rw [hr1]; exact hbp
  -- and to `tmpO + 4`
  refine smc_st2_wp (j := tmpO + 4) (by omega) hb1 (eval_w w1 _) (eval_w w1 _)
    fun s2 hb2 hr2 hx2 he2 ↦ ?_
  rw [hr1, h9, h10] at hx2
  have w2 : s2.reg .rbp = p.env.work := by rw [hr2]; exact w1
  have he12 : ∀ j, j + 1 < 2 ^ 61 → (j + 1 < tmpO + 4 ∨ tmpO + 4 + 1 < j) →
      (j + 1 < spO + 2 * k ∨ spO + 2 * k + 1 < j) → ∀ x : EW,
      EWAt s.mem (wd p.env.work j) x → EWAt s2.mem (wd p.env.work j) x :=
    fun j hj d2 d1 x h ↦ smc_ewAt_keep (smc_ewAt_keep h he1 hj d1) he2 hj d2
  have c0' := he12 tmpO (by omega) (by omega) (by omega) _ hc0
  have tt' := he12 (tmpO + 2) (by omega) (by omega) (by omega) _ htt
  have cl' := he12 (tmpO + 14) (by omega) (by omega) (by omega) _ hcl
  -- the new claim
  refine ldA_wp w2 tt' fun s3 m3 l9 l10 f3 ↦ ?_
  have w3 : s3.reg .rbp = p.env.work := by rw [f3 .rbp (by decide)]; exact w2
  refine mulM_wp (b := r) w3 l9 l10 (by rw [m3]; exact hx2) fun s4 m4 l9 l10 f4 ↦ ?_
  have w4 : s4.reg .rbp = p.env.work := by rw [f4 .rbp (by decide)]; exact w3
  refine addM_wp (b := acc.2) w4 l9 l10 (by rw [m4, m3]; exact cl') fun s5 m5 l9 l10 f5 ↦ ?_
  have w5 : s5.reg .rbp = p.env.work := by rw [f5 .rbp (by decide)]; exact w4
  refine addM_wp (b := tt) w5 l9 l10 (by rw [m5, m4, m3]; exact tt') fun s6 m6 l9 l10 f6 ↦ ?_
  have w6 : s6.reg .rbp = p.env.work := by rw [f6 .rbp (by decide)]; exact w5
  refine mulM_wp (b := r) w6 l9 l10 (by rw [m6, m5, m4, m3]; exact hx2) fun s7 m7 l9 l10 f7 ↦ ?_
  have w7 : s7.reg .rbp = p.env.work := by rw [f7 .rbp (by decide)]; exact w6
  refine addM_wp (b := c0) w7 l9 l10 (by rw [m7, m6, m5, m4, m3]; exact c0') fun s8 m8 l9 l10 f8 ↦ ?_
  have f38 : RegsFrame smcOpRegs s2 s8 :=
    rf_trans (l'' := smcOpRegs) (rf_trans (l'' := smcOpRegs) (rf_trans (l'' := smcOpRegs)
      (rf_trans (l'' := smcOpRegs) (rf_trans (l'' := smcOpRegs) f3 f4) f5) f6) f7) f8
  have m38 : s8.mem = s2.mem := by rw [m8, m7, m6, m5, m4, m3]
  have hb8 : Base p t s8 := hb2.frM (smc_frM_regs (f38 .rdi (by decide)) m38)
  have w8 : s8.reg .rbp = p.env.work := by rw [f38 .rbp (by decide)]; exact w2
  -- stored
  refine smc_st2_wp (j := tmpO + 14) (by omega) hb8 (eval_w w8 _) (eval_w w8 _)
    fun s9 hb9 hr9 hx9 he9 ↦ ?_
  rw [l9, l10] at hx9
  fstep; fstep
  apply WP.blk_nil
  refine ⟨hb9.frM (((frM_setReg (r := .r13) (by decide) _).trans
    (frM_setReg (r := .r15) (by decide) _))), ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rsimp; rw [hr9]; exact w8
  · rsimp
    rw [hr9, f38 .r15 (by decide), hr2, hr1, h15, show mu - k = (mu - (k + 1)) + 1 by omega,
      toUInt64_succ_sub]
  · rsimp
    rw [hr9, f38 .r13 (by decide), hr2, hr1, h13,
      show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]
    congr 1
  · rw [Array.size_push, hsz]
  · simp only [QState.setReg_mem]
    have a1 : EWArr s1.mem (wd p.env.work spO) (acc.1.push r) :=
      smc_ewArr_push (smc_ewArr_keep harr he1 (by omega) (by omega)) (by rw [hsz]; exact hx1)
    have a2 : EWArr s8.mem (wd p.env.work spO) (acc.1.push r) := by
      rw [m38]
      exact smc_ewArr_keep a1 he2 (by rw [Array.size_push, hsz]; omega)
        (by rw [Array.size_push, hsz]; omega)
    exact smc_ewArr_keep a2 he9 (by rw [Array.size_push, hsz]; omega)
      (by rw [Array.size_push, hsz]; omega)
  · simp only [QState.setReg_mem]
    exact hx9
  · simp only [QState.setReg_mem]
    have o2 : Only p.env smcW m0 s8.mem := by
      rw [m38]
      exact smc_only_keep (smc_only_keep hon he1
        ⟨.inl ⟨by omega, by omega⟩, .inl ⟨by omega, by omega⟩⟩) he2
        ⟨.inr ⟨by omega, by omega⟩, .inr ⟨by omega, by omega⟩⟩
    exact smc_only_keep o2 he9 ⟨.inr ⟨by omega, by omega⟩, .inr ⟨by omega, by omega⟩⟩

/-- **`sumcheckC` runs the final level's sumcheck.** -/
theorem sumcheckC_spec {p : Par} {m0 : UInt64 → Option UInt64} {mu : Nat} {claim : EW}
    (hmu : mu ≤ 30) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ NatAt s.mem (wd p.env.work cMu) mu ∧
        EWAt s.mem (wd p.env.work (tmpO + 14)) claim)
      sumcheckC (sumcheckPlain claim 3 mu)
      (fun r t s ↦ Base p t s ∧ EWArr s.mem (wd p.env.work spO) r.1 ∧ r.1.size = mu ∧
        EWAt s.mem (wd p.env.work (tmpO + 14)) r.2 ∧
        Only p.env (fun k ↦ spO ≤ k ∧ k < spO + 64 ∨ tmpO ≤ k ∧ k < tmpO + 32) m0 s.mem)
      (Err p) := by
  rw [sumcheckPlain_eq]
  have key := Refines.foldlM (l := List.replicate mu (none : Option EW)) (f := smcStep)
    (cond := .cmp .ne .r15 (.imm 0)) (body := smcRoundC) (E := Err p)
    (Inv := fun k acc t s ↦ Base p t s ∧ SmcR p m0 mu k acc s) ?_ ?_ (init := (#[], claim))
  · rintro t s ⟨hb, hm, hc, hcl⟩
    unfold sumcheckC ldW ldw leaw
    refine wp_load (eval_cw hb.rdi ctxWork) hb.workPtr ?_
    have hW : (s.setReg .rbp p.env.work).reg .rbp = p.env.work := by rsimp
    refine wp_load (eval_w hW cMu) (by rsimp; exact hc.2) ?_
    refine wp_reg (by simp only [QInstr.step]; rfl) ?_
    show WP (Stmt.loop _ _) _ _ _
    refine WP.mono (key t _ ?_) ?_ fun _ h ↦ h
    · refine ⟨hb.frM ⟨by rsimp, fun _ ↦ rfl, fun _ _ ↦ rfl⟩, by rsimp, by rsimp; simp,
        ?_, Nat.zero_le _, rfl, fun i hi ↦ absurd hi (by simp), ?_, ?_⟩
      · rsimp
        exact eval_w (by rsimp) spO
      · simp only [QState.setReg_mem]
        exact hcl
      · simp only [QState.setReg_mem]
        rw [hm]
        exact Only.refl _ _
    · rintro s' ⟨r, t', hrun, hb', -, -, -, -, hsz, harr, hcl', hon⟩
      rw [List.length_replicate] at hsz
      exact ⟨r, t', hrun, hb', harr, hsz, hcl', hon⟩
  · rintro k acc t s ⟨-, -, h15, -, hkm, -⟩
    rw [List.length_replicate, cond_ne, rhs_imm, h15, int64Zero_toUInt64, bne_iff_ne, ne_eq]
    constructor
    · intro hne
      by_contra hjn
      exact hne (by rw [show mu - k = 0 by omega]; rfl)
    · intro hjn e
      have := toUInt64_eq_zero (show mu - k < 2 ^ 64 by omega) e
      omega
  · intro k hk acc
    rw [List.length_replicate] at hk
    rw [List.getElem_replicate, smcStep_none]
    exact smcRoundC_spec hmu hk acc

end NativeVm.Code.P7
