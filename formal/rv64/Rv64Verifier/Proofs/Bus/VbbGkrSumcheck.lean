import Rv64Verifier.Proofs.Bus.VbbGkrEqs

/-!
# `verify_bus_balance`: an iteration's sumcheck

`count = (1 << step) + 1` (`4 >> (layer & 1)` plus one, `b8000677c_x19'`, `b8000677c_x13'`),
`sumcheck` on the claim at `S - 152` and `equalities`, into `S - 608` (`Err` to `0x80007100`,
`err7100`); the point `x` kept in `s10`/`s0`/`s5`, the claim in `s7`, `S - 1208`, `S - 1216`; to
the first `next_scalars`' entry (`AtNs`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem and_one_toNat (x : Word) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]
  exact Nat.and_one_is_mod _

theorem b8000677c_x19' {s t : MachineState} (h : b8000677c.Holds s t) {n : Nat}
    (hn : (s.getReg .x25).toNat = n) : t.getReg .x19 = BitVec.ofNat 64 (2 ^ stepOf n) :=
  h.reg_eq .x19 rfl (by
    rv_eval []
    rw [and_one_toNat, hn]
    unfold stepOf
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h0 <;> simp only [h0] <;> decide)

theorem b8000677c_x13' {s t : MachineState} (h : b8000677c.Holds s t) {n : Nat}
    (hn : (s.getReg .x25).toNat = n) : t.getReg .x13 = BitVec.ofNat 64 (2 ^ stepOf n + 1) :=
  h.reg_eq .x13 rfl (by
    rv_eval []
    rw [and_one_toNat, hn]
    unfold stepOf
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h0 <;> simp only [h0] <;> decide)

theorem stepOf_le (n : Nat) : 1 ≤ stepOf n ∧ stepOf n ≤ 2 := by
  unfold stepOf; split <;> omega

/-- The `Err` exit through `0x80007100` (`s2` reloaded) of a run the mirror fails. -/
theorem err7100 {bev : MachineState → Word → List E → Option E} {s u : MachineState} {k : Start}
    (hpre : BusBalancePre s) (h : Inv s u) (hk : Kept s u k) (hpc : u.pc = 0x80007100)
    (hnone : ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) :
    ∃ t, Reaches Image.code u t ∧ Done bev s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := h.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007100_spec hpc (by
    rv_eval [sp]
    valid_access hval [hb1])
  have m₁ := b80007100_mem_same h₁
  obtain ⟨t, hrt, hd⟩ := errDone (bev := bev) hpre (h.same m₁ (b80007100_keeps h₁ .x2 (by decide)))
    (by
      rw [b80007100_x18 h₁, sp, show s.getReg .x2 - 1344 + 32 = s.getReg .x2 - 1312 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      exact hk.out) (b80007100_pc h₁) hnone
  exact ⟨t, hr₁.trans hrt, hd⟩

/-- At the first `next_scalars`' entry: `x` in `s10`/`s0`/`s5`, the claim `cl`. -/
structure AtNs (s u w : MachineState) (k : Start) (cnt : E) (P : Word) (n : ℕ) (comb : E)
    (x : List E) (cl : E) : Prop where
  ctx : Ctx s w k cnt P
  regs : ∀ r ∈ ([.x9, .x20, .x24, .x25] : List Reg), w.getReg r = u.getReg r
  x19 : w.getReg .x19 = BitVec.ofNat 64 (2 ^ stepOf n)
  x22 : (w.getReg .x22).toNat = n % 2
  x1 : w.getReg .x1 = 0x800067dc
  x10 : w.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608
  x11 : w.getReg .x11 = s.getReg .x12
  x12 : w.getReg .x12 = BitVec.ofNat 64 (2 ^ stepOf n)
  combAt : eAt w (s.getReg .x2 - BitVec.ofNat 64 128) = comb
  valuesPtr : w.getMem (s.getReg .x2 - 1280) = P
  xv : NewVecR u w (w.getReg .x26) (w.getReg .x8) (w.getReg .x21) x
  claimAt : eOf3 (w.getReg .x23) (w.getMem (s.getReg .x2 - 1208)) (w.getMem (s.getReg .x2 - 1216)) = cl
  step : StepR s u w (Scratch s)

theorem optEListAt_same {v w : MachineState} (hm : ∀ a, w.getMem a = v.getMem a) (p : Word)
    (n : Nat) : optEListAt w p n = optEListAt v p n := by
  simp only [optEListAt, optEAt, Rv64Verifier.eAt, hm]

theorem sumcheckStack_eq : sumcheckStack = 1632 := rfl

/-- `sumcheck`'s arguments: the result at `S - 608`, the claim at `S - 152`, the equalities a
buffer allocated since the entry. -/
theorem scPre {s v : MachineState} (hpre : BusBalancePre s) (h : Inv s v)
    (h10 : v.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608) (h11 : v.getReg .x11 = s.getReg .x12)
    (h12 : v.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 152) (h13 : 2 ≤ (v.getReg .x13).toNat)
    (hbuf : NewBuf s v (v.getReg .x14) (32 * (v.getReg .x15).toNat) 8) : SumcheckPre v := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have T := tpre hpre h (k := 608) (n := 48) (m := sumcheckStack) (by omega) (by omega) (by omega)
    (by decide) (by decide) h10 h11
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := sumcheckStack) hpre h (k := 152) (n := 24) (by omega)
    (by omega) (by omega) (by decide)
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hsl : stackLo v sumcheckStack = s.getReg .x2 - BitVec.ofNat 64 2976 := by
    simp only [stackLo, h.sp, sumcheckStack_eq]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hm := h.mono
  have hn := h.heap.hi
  have ha := hpre.stack.above
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have ps := hpre.proofStack
  have hr := hpre.stack.rodata
  have hrb : rodataBase.toNat = 2684354560 := rfl
  rw [stackLo_eq] at ha ss ps hr
  simp only [ProofApart] at ps
  have hl := hpre.heap.lo
  simp only [Outside, NewBuf, heapNext, heapEnd, heapStart] at sf hbuf hm hn ha hl
  have hb : (v.getReg .x15).toNat = 0 ∨ ((s.getMem nextAddr).toNat ≤ (v.getReg .x14).toNat ∧
      (v.getReg .x14).toNat + 32 * (v.getReg .x15).toNat ≤ (v.getMem nextAddr).toNat) := by
    rcases hbuf.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr h0
  exact { T with
    count := h13
    claim := h12 ▸ o1
    eqs := by
      rcases hb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by addr_omega [h0, hn, hbuf.1, hl])
    claimFree := h12 ▸ o2
    eqsFree := by
      rcases hb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by simp only [Outside, heapNext, heapEnd]; addr_omega [h0, hn])
    claimStack := h12 ▸ o3
    eqsStack := by rw [hsl]; addr_omega [hb, hn, ha, hb1]
    claimSelf := by rw [h11, h12]; addr_omega [hb1, ss, hS]
    eqsSelf := by rw [h11]; addr_omega [hb, hn, sf, hm]
    claimOut := by rw [h10, h12]; addr_omega [hb1]
    eqsOut := by rw [h10]; addr_omega [hb, hn, ha, hb1]
    claimEqs := by rw [h12]; addr_omega [hb, hn, ha, hb1]
    proofClaim := by
      rw [h11, h12]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [ps.1, hb1], by addr_omega [ps.2, hb1]⟩
    claimRodata := by rw [h12]; simp only [rodataSize] at hr ⊢; addr_omega [hr, hrb, hb1] }

theorem two_pow_step_toNat (n : Nat) :
    (BitVec.ofNat 64 (2 ^ stepOf n + 1)).toNat = 2 ^ stepOf n + 1 := by
  have := stepOf_le n
  have : 2 ^ stepOf n ≤ 4 := by
    unfold stepOf; split <;> decide
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- The call of `sumcheck`, from `0x8000677c` to the first `next_scalars`' entry. -/
theorem sumcheckStep (hSC : SumcheckSpec) {bev : MachineState → Word → List E → Option E}
    {s u w₀ : MachineState} {k : Start} {cnt : E} {P : Word} {st : GkrState} {comb : E} {n : ℕ}
    {K : List E × E → TM BusResultRust} (hpre : BusBalancePre s)
    (h : AtEqs s u w₀ k cnt P st comb) (hpc : w₀.pc = 0x8000677c)
    (hu : heapNext s ≤ heapNext u) (h9 : u.getReg .x9 = 0xffffffffffffffff)
    (h20 : u.getReg .x20 = s.getReg .x12) (h25 : (u.getReg .x25).toNat = n)
    (htr : Tracks (prog bev s) (s.getReg .x12) s w₀ (TM.sumcheck (polyEvalRust st.values comb)
      (2 ^ stepOf n + 1) (st.point.map some) >>= K)) :
    ∃ w, Reaches Image.code w₀ w ∧ (Done bev s w ∨ Dead Image.code w ∨ ∃ x cl,
      w.pc = 0x80004818 ∧ AtNs s u w k cnt P n comb x cl ∧
      Tracks (prog bev s) (s.getReg .x12) s w (K (x, cl))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C := h.ctx
  have I := C.inv
  have sp := I.sp
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000677c_spec hpc trivial
  have k₁ := b8000677c_keeps h₁
  have m₁ := b8000677c_mem_same h₁
  have I₁ := I.same m₁ (k₁ .x2 (by decide))
  have x25₀ : (w₀.getReg .x25).toNat = n := by rw [h.regs .x25 (by decide)]; exact h25
  have h10₁ : w₁.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [b8000677c_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have h11₁ : w₁.getReg .x11 = s.getReg .x12 := by
    rw [b8000677c_x11 h₁, h.regs .x20 (by decide), h20]
  have h12₁ : w₁.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 152 := by
    rw [b8000677c_x12 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have h13₁ : (w₁.getReg .x13).toNat = 2 ^ stepOf n + 1 := by
    rw [b8000677c_x13' h₁ x25₀]; exact two_pow_step_toNat n
  have hn₁ : heapNext w₁ = heapNext w₀ := by simp only [heapNext, m₁]
  have hbuf : NewBuf s w₁ (w₁.getReg .x14) (32 * (w₁.getReg .x15).toNat) 8 := by
    have hb := h.eqBuf
    have hm := h.step.mono
    rw [k₁ .x14 (by decide), k₁ .x15 (by decide)]
    simp only [NewBuf, hn₁] at hb ⊢
    exact ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩
  have pre := scPre hpre I₁ h10₁ h11₁ h12₁ (by rw [h13₁]; have := Nat.two_pow_pos (stepOf n); omega) hbuf
  obtain ⟨w₂, hr₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hSC.call hr₁ (b8000677c_pc h₁) pre
  swap
  · exact ⟨w₂, hr₂, Or.inr (Or.inl hd)⟩
  have hsl : stackLo w₁ sumcheckStack = s.getReg .x2 - BitVec.ofNat 64 2976 := by
    simp only [stackLo, I₁.sp, sumcheckStack_eq]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hf := post.frame
  rw [h10₁, h11₁, h12₁, hsl] at hf
  have st₂ : StepR s w₁ w₂ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 48 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 152) 24 :=
    ⟨hf.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr ha)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha))), post.heap, post.mono, hp₂.reg .x2⟩
  have fW : FrameW s fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 48 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 152) 24 := fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have I₂ := I₁.afterR hpre fW st₂
  have sp₂ : w₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  have hargs : TM.sumcheck (eAt w₁ (w₁.getReg .x12)) (w₁.getReg .x13).toNat
      (optEListAt w₁ (w₁.getReg .x14) (w₁.getReg .x15).toNat) =
      TM.sumcheck (polyEvalRust st.values comb) (2 ^ stepOf n + 1) (st.point.map some) := by
    rw [h12₁, h13₁, k₁ .x14 (by decide), k₁ .x15 (by decide), optEListAt_same m₁, h.eqs,
      ← h.claimAt]
    simp only [Rv64Verifier.eAt, m₁]
  have hT₁ (T : TState) (hT : TranscriptAt w₀ (s.getReg .x12) T) :
      TranscriptAt w₁ (w₁.getReg .x11) T := h11₁ ▸ TranscriptAt.same hpre I m₁ hT
  obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800067a0_spec
    (by rw [hpc₂, returnAddress_eq, b8000677c_x1 h₁]; decide) (by
      rv_eval [sp₂]
      and_intros <;> valid_access hval [hb1])
  have k₃ := b800067a0_keeps h₃
  have m₃ := b800067a0_mem_same h₃
  have e736 : w₂.getReg .x2 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x9₂ : w₂.getReg .x9 = 0xffffffffffffffff := by
    rw [hp₂.reg .x9, k₁ .x9 (by decide), h.regs .x9 (by decide), h9]
  have stS₂ : StepR s w₀ w₂ (Scratch s) :=
    ((StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))).trans st₂).weaken fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact False.elim ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
  by_cases hcap : w₂.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0xffffffffffffffff
  · -- `Err`
    have hpc₃ := b800067a0_pc_taken h₃ (by rw [e736, x9₂]; exact hcap)
    have st₃ : StepR s w₀ w₃ (Scratch s) :=
      (stS₂.trans (StepR.same m₃ I₂.heap (k₃ .x2 (by decide)) (A := fun _ ↦ False))).weaken
        fun a ha ↦ by
          rcases ha with ha | ha
          · exact ha
          · exact False.elim ha
    have C₃ := C.step hpre st₃
    obtain ⟨t, hrt, hdt⟩ := err7100 (bev := bev) hpre C₃.inv C₃.kept hpc₃ (htr.fail fun T hT ↦ by
      have hv := post.value T (hT₁ T hT)
      rw [hargs] at hv
      rcases hrun : (TM.sumcheck (polyEvalRust st.values comb) (2 ^ stepOf n + 1)
        (st.point.map some)).run T with _ | ⟨⟨x', cl'⟩, T'⟩
      · rfl
      · rw [hrun] at hv; dsimp only at hv
        exact absurd (by rw [h10₁]; exact hcap) hv.1)
    exact ⟨t, hr₂.trans (hr₃.trans hrt), Or.inl hdt⟩
  have hpc₃ := b800067a0_pc_not_taken h₃ (by rw [e736, x9₂]; exact hcap)
  have sp₃ : w₃.getReg .x2 = s.getReg .x2 - 1344 := by rw [k₃ .x2 (by decide)]; exact sp₂
  set x := vecEs w₂ (s.getReg .x2 - BitVec.ofNat 64 608) with hx
  set cl := eAt w₂ (s.getReg .x2 - BitVec.ofNat 64 584) with hcl
  have e584 : s.getReg .x2 - BitVec.ofNat 64 608 + 24 = s.getReg .x2 - BitVec.ofNat 64 584 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hok (T : TState) (hT : TranscriptAt w₀ (s.getReg .x12) T) : ∃ T',
      (TM.sumcheck (polyEvalRust st.values comb) (2 ^ stepOf n + 1) (st.point.map some)).run T =
        some ((x, cl), T') ∧ NewVecE w₁ w₂ (s.getReg .x2 - BitVec.ofNat 64 608) x ∧
        TranscriptAt w₂ (s.getReg .x12) T' := by
    have hv := post.value T (hT₁ T hT)
    rw [hargs] at hv
    rcases hrun : (TM.sumcheck (polyEvalRust st.values comb) (2 ^ stepOf n + 1)
      (st.point.map some)).run T with _ | ⟨⟨x', cl'⟩, T'⟩
    · rw [hrun] at hv; dsimp only at hv
      exact absurd (by rw [← h10₁]; exact hv) hcap
    · rw [hrun] at hv; dsimp only at hv
      obtain ⟨-, hxv, hc, hT'⟩ := hv
      rw [h10₁] at hxv hc
      rw [e584] at hc
      have hx' : x' = x := by rw [hx, hxv.elems]
      rw [hx'] at hxv
      exact ⟨T', by rw [hx', ← hc], hxv, h11₁ ▸ hT'⟩
  obtain ⟨w₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800067b0_spec hpc₃ (by
    rv_eval [sp₃]
    and_intros <;> valid_access hval [hb1])
  have k₄ := b800067b0_keeps h₄
  have fr₄ := b800067b0_frame h₄ (by rw [sp₃]; addr_omega [hb1])
  rw [sp₃, show s.getReg .x2 - 1344 + 128 = s.getReg .x2 - 1216 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₄
  have st₄ : StepR s w₃ w₄ (Within · (s.getReg .x2 - 1216) 16) :=
    StepR.ofMemFrame (I₂.same m₃ (k₃ .x2 (by decide))).heap fr₄ (fun _ h ↦ h) (by addr_omega [hb1])
      (k₄ .x2 (by decide))
  have I₃ := I₂.same m₃ (k₃ .x2 (by decide))
  have stF : StepR s w₀ w₄ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 48 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 152) 24 ∨ Within a (s.getReg .x2 - 1216) 16 :=
    ((((StepR.same m₁ C.inv.heap (k₁ .x2 (by decide)) (A := fun _ ↦ False)).trans st₂).trans
      (StepR.same m₃ I₂.heap (k₃ .x2 (by decide)) (A := fun _ ↦ False))).trans st₄).weaken
      fun a ha ↦ by
        rcases ha with ((ha | ha | ha) | ha) | ha
        · exact False.elim ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact False.elim ha
        · exact Or.inr (Or.inr ha)
  have stAll : StepR s w₀ w₄ (Scratch s) := stF.weaken fun a ha ↦ by
    rcases ha with ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
    · exact Or.inr (Or.inr (Or.inl ha))
  have rg (r : Reg) (hr : r ∈ ([.x9, .x19, .x20, .x24, .x25] : List Reg)) :
      w₄.getReg r = w₁.getReg r := by
    rw [k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), hp₂ r (mem_of_mem hr _)]
  have m128 := b800067b0_m_x2_128 h₄
  have m136 := b800067b0_m_x2_136 h₄
  rw [sp₃, show s.getReg .x2 - 1344 + 128 = s.getReg .x2 - 1216 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 776 =
      s.getReg .x2 - BitVec.ofNat 64 584 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
    m₃] at m128
  rw [sp₃, show s.getReg .x2 - 1344 + 136 = s.getReg .x2 - 1208 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 768 =
      s.getReg .x2 - BitVec.ofNat 64 584 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
    m₃] at m136
  have x23₄ := b800067b0_x23 h₄
  rw [sp₃, show s.getReg .x2 - 1344 + 760 = s.getReg .x2 - BitVec.ofNat 64 584 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₃] at x23₄
  -- `x` as a `Vec` in registers
  have hv₂ : ∀ T, TranscriptAt w₀ (s.getReg .x12) T →
      NewVecE w₁ w₂ (s.getReg .x2 - BitVec.ofNat 64 608) x := fun T hT ↦ by obtain ⟨_, _, hn, _⟩ := hok T hT; exact hn
  obtain ⟨T₀, hT₀⟩ : ∃ T, TranscriptAt w₀ (s.getReg .x12) T :=
    ⟨canonT w₀ (s.getReg .x12), canonT_at _ _⟩
  have V := hv₂ T₀ hT₀
  have hm01 := h.step.mono
  have hm4 := st₄.mono
  have hm12 := st₂.mono
  have hn3 : heapNext w₃ = heapNext w₂ := by simp only [heapNext, m₃]
  have xr : NewVecR s w₂ (vecCap w₂ (s.getReg .x2 - BitVec.ofNat 64 608))
      (vecPtr w₂ (s.getReg .x2 - BitVec.ofNat 64 608))
      (vecLen w₂ (s.getReg .x2 - BitVec.ofNat 64 608)) x := by
    have hb := V.buf
    simp only [NewBuf] at hb
    exact ⟨V.vec.len, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by have := I₁.mono; omega, h'.2⟩⟩, V.elems⟩
  have xr₄ := (xr.keepG hpre (s := s) (StepR.same m₃ I₂.heap (k₃ .x2 (by decide)) (A := fun _ ↦ False))
    (fun _ h ↦ h.elim)).keepG hpre st₄ (fun a ha ↦ by addr_omega [ha, hb1])
  refine ⟨w₄, hr₂.trans (hr₃.trans hr₄), Or.inr (Or.inr ⟨x, cl, b800067b0_pc h₄, {
    ctx := C.step hpre stAll
    regs := fun r hr ↦ by
      rw [rg r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
      exact h.regs r (mem_of_mem hr _)
    x19 := by rw [rg .x19 (by decide)]; exact b8000677c_x19' h₁ x25₀
    x22 := by
      rw [k₄ .x22 (by decide), k₃ .x22 (by decide), hp₂ .x22 (by decide), b8000677c_x22 h₁,
        and_one_toNat, x25₀]
    x1 := b800067b0_x1 h₄
    x10 := by rw [b800067b0_x10 h₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x11 := by rw [b800067b0_x11 h₄, k₃ .x20 (by decide), hp₂ .x20 (by decide), k₁ .x20 (by decide),
      h.regs .x20 (by decide), h20]
    x12 := by rw [b800067b0_x12 h₄, k₃ .x19 (by decide), hp₂ .x19 (by decide)]
              exact b8000677c_x19' h₁ x25₀
    combAt := by
      rw [stF.eAtFrame hpre (by omega) (by omega) (fun y hy hs ↦ by
        rcases hs with hs | hs | hs <;> addr_omega [hy, hs, hb1])]
      exact h.combAt
    valuesPtr := by
      rw [stF.word hpre (fun y hy hs ↦ by rcases hs with hs | hs | hs <;> addr_omega [hy, hs, hb1])
        (Or.inl (by addr_omega [hb1]))]
      exact h.valuesPtr
    xv := by
      rw [k₄ .x26 (by decide), b800067a0_x26 h₃, b800067b0_x8 h₄, b800067a0_x27 h₃,
        k₄ .x21 (by decide), b800067a0_x21 h₃, sp₂,
        show s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
        show s.getReg .x2 - 1344 + 744 = s.getReg .x2 - BitVec.ofNat 64 608 + 8 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
        show s.getReg .x2 - 1344 + 752 = s.getReg .x2 - BitVec.ofNat 64 608 + 16 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      have hb := V.buf
      simp only [NewBuf] at hb
      refine ⟨V.vec.len, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨?_, ?_⟩⟩, xr₄.elems⟩
      · simp only [heapNext, vecPtr, vecCap] at hm01 hn₁ h' ⊢; omega
      · simp only [heapNext, vecPtr, vecCap] at hm4 hn3 h' ⊢; omega
    claimAt := by
      rw [x23₄, m136, m128, hcl, eAt_eOf3]
    step := (h.step.trans stAll).weaken fun a ha ↦ by rcases ha with ha | ha <;> exact ha },
    htr.bind (v := w₄) (fun T hT ↦ ?_)⟩)⟩
  obtain ⟨T', e, -, hT'⟩ := hok T hT
  refine ⟨T', e, I₃.transcript hpre st₄.heap ((DFrame.of_memFrame fr₄).mono fun a ha ↦
    Or.inl (by addr_omega [ha, hb1])) (TranscriptAt.same hpre I₂ m₃ hT')⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
