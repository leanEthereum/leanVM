import Rv64Verifier.Proofs.Pcs.VsoFinalPoly

/-!
# `verify_stacked_opening`'s final level: the tail's rounds

`0x8000b8ec` zeroes the running target (`S - 904`, `S - 920`, `S - 864`), starts the tail folds
empty and, with rounds to run, enters their loop (`0x8000b914`); `0x8000b92c` loops or, after the
last, stores the target (`0x8000ba08`). Either way the rounds end at `0x8000ba14` (`TA`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000ba14`, the rounds done: the tail folds `tf`, the running target `rt`. -/
structure TA (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) (tf : List E) (rt : E) :
    Prop extends TI OA s x u v Wl residual where
  pc : v.pc = 0x8000ba14
  tfl : tf.length = mlF s Wl
  x9 : v.getReg .x9 = x.FP
  x19 : v.getReg .x19 = BitVec.ofNat 64 (mlF s Wl)
  m224 : v.getMem (s.getReg .x2 - 816) = s.getReg .x10
  tail : TailV s u v tf
  trg : E.ofLimbs (BF64.ofBitVec (v.getMem (s.getReg .x2 - 904)))
    (BF64.ofBitVec (v.getMem (s.getReg .x2 - 920))) (BF64.ofBitVec (v.getMem (s.getReg .x2 - 864))) = rt
  value : RunsF OA s v (afterTail (cfgOf s) (basisOf s x) residual Wl tf rt)

/-- `0x8000b92c`: the next round, or the target stored. -/
theorem tNext {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E} {i : ℕ} {q tf : List E}
    {rt : E} (hpre : VsoPre s) (hn : TN OA s x u v Wl residual i q tf rt) :
    ∃ w, Reaches Image.code v w ∧ ((i + 1 < mlF s Wl ∧ TR OA s x u w Wl residual (i + 1) q tf) ∨
      TA OA s x u w Wl residual tf rt) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hn.sp
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b92c_spec hn.pc trivial
  have k₁ := b8000b92c_keeps h₁
  have hm₁ := b8000b92c_mem_same h₁
  obtain ⟨T₁, -⟩ := hn.toTI.stepS hpre (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₁ .x2 (by decide))
  have hml : mlF s Wl < 2 ^ 64 := by have := (s.getReg .x12).isLt; simp only [mlF]; omega
  have hilt := hn.ilt
  by_cases hlast : i + 1 = mlF s Wl
  · obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000ba08_spec
      (b8000b92c_pc_taken h₁ (by rw [hn.x12, hn.x20, hlast])) (by
        rv_eval [k₁ .x2 (by decide), hsp]; and_intros <;> valid_access hst.valid [hb])
    have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₁.sp
    have k₂ := b8000ba08_keeps h₂
    have X₂ : DFrame t₁ t₂ fun a ↦ Within a (s.getReg .x2 - 920) 24 := by
      have := DFrame.of_memFrame (b8000ba08_frame h₂ (by rw [sp₁]; addr_omega [hb]))
      rw [sp₁] at this
      exact this.mono fun a ha ↦ by addr_omega [ha, hb]
    obtain ⟨T₂, n₂⟩ := T₁.stepS hpre X₂ (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
      (k₂ .x2 (by decide))
    have kw (y : Word) (hy : (s.getReg .x2 - 896).toNat ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) : t₂.getMem y = v.getMem y := by
      rw [X₂.word (fun a ha hx ↦ by addr_omega [ha, hx, hy, hb]) (by addr_omega [hy, hb]), hm₁]
    refine ⟨t₂, r₁.trans r₂, Or.inr {
      toTI := T₂
      pc := b8000ba08_pc h₂
      tfl := by rw [hn.tfl, hlast]
      x9 := by rw [k₂ .x9 (by decide), k₁ .x9 (by decide), hn.x9]
      x19 := by
        rw [b8000ba08_x19 h₂, sp₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 168 =
          s.getReg .x2 - 872 by addr_omega [hb], hm₁]
        exact hn.m168
      m224 := by rw [kw _ (by addr_omega [hb])]; exact hn.m224
      tail := hn.tail.keep hn.heap hn.toTI.fin.su ((DFrame.of_same hm₁ _).trans X₂ fun _ h ↦ h)
        (fun a ha hw ↦ by addr_omega [ha, hw, hb])
        (fun a ha ↦ SS.heap hpre (Or.inl (by addr_omega [ha, hb])) hn.heap.hi) (by addr_omega [hb])
        (by simp only [heapNext, n₂, hm₁]; rfl)
      trg := by
        have m0 := b8000ba08_m_x2_136 h₂
        have m1 := b8000ba08_m_x2_120 h₂
        rw [sp₁, k₁ .x26 (by decide)] at m0
        rw [sp₁, k₁ .x27 (by decide)] at m1
        rw [show s.getReg .x2 - 904 = s.getReg .x2 - BitVec.ofNat 64 1040 + 136 by addr_omega [hb],
          show s.getReg .x2 - 920 = s.getReg .x2 - BitVec.ofNat 64 1040 + 120 by addr_omega [hb],
          m0, m1, kw _ (by addr_omega [hb])]
        exact hn.trg
      value := by
        have hv := hn.value
        rw [hlast, roundsK_end] at hv
        exact (hv.keep hpre (hn.toTI.inv hpre) (DFrame.of_same hm₁ (fun _ ↦ False))
          fun _ h ↦ h.elim).keep hpre (T₁.inv hpre) X₂ fun a ha ↦ Or.inl (by addr_omega [ha, hb]) }⟩
  · have hmore : i + 1 < mlF s Wl := by omega
    have hm : BitVec.ofNat 64 (mlF s Wl) ≠ BitVec.ofNat 64 (i + 1) := fun he ↦ hlast (by
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega)
    refine ⟨t₁, r₁, Or.inl ⟨hmore, {
      toTI := T₁
      pc := b8000b92c_pc_not_taken h₁ (by rw [hn.x12, hn.x20]; exact hm)
      ilt := hmore
      tfl := hn.tfl
      x9 := by rw [k₁ .x9 (by decide), hn.x9]
      x18 := by rw [k₁ .x18 (by decide), hn.x18]; simp only [vecPtr]; rw [hm₁]
      x19 := by
        rw [b8000b92c_x19 h₁, hn.x19, show (24 : Word) = BitVec.ofNat 64 24 from rfl,
          ← BitVec.ofNat_add]; rfl
      x20 := by rw [k₁ .x20 (by decide), hn.x20]
      x21 := by rw [k₁ .x21 (by decide), hn.x21]
      x24 := by rw [k₁ .x24 (by decide), hn.x24]
      x25 := by rw [k₁ .x25 (by decide), hn.x25]
      m168 := by rw [hm₁]; exact hn.m168
      m224 := by rw [hm₁]; exact hn.m224
      tail := hn.tail.keep hn.heap hn.toTI.fin.su (DFrame.of_same hm₁ (fun _ ↦ False))
        (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) (by addr_omega [hb]) (by simp only [heapNext, hm₁]; rfl)
      quad := (hn.quad hmore).keep (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
        (fun _ h ↦ h.elim) ⟨by addr_omega [hb], by addr_omega [hb]⟩ hn.heap.hi
        (by simp only [heapNext, hm₁]; rfl)
      value := by
        have hv := hn.value
        rw [roundsK_succ _ _ _ _ hmore] at hv
        exact hv.keep hpre (hn.toTI.inv hpre) (DFrame.of_same hm₁ (fun _ ↦ False))
          fun _ h ↦ h.elim }⟩⟩

theorem TI.init {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}
    (h : VsoFinalIn OA s x u Wl residual) : TI OA s x u u Wl residual :=
  ⟨h, DFrame.refl _ _, h.heap, Nat.le_refl _, h.sp⟩

/-- `0x8000b8ec`: into the rounds' loop, or straight to `0x8000ba14` when there are none. -/
theorem tEnter {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E} (hpre : VsoPre s)
    (h : VsoFinalIn OA s x u Wl residual) :
    ∃ v, Reaches Image.code u v ∧ ((0 < mlF s Wl ∧ TR OA s x u v Wl residual 0 Wl.runningQuad []) ∨
      TA OA s x u v Wl residual [] 0) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.sp
  have T₀ := TI.init h
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b8ec_spec h.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000b8ec_keeps h₁
  have X₁ : DFrame u t₁ fun a ↦ Within a (s.getReg .x2 - 920) 8 ∨
      Within a (s.getReg .x2 - 904) 8 ∨ Within a (s.getReg .x2 - 864) 8 ∨
      Within a (s.getReg .x2 - 304) 24 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000b8ec, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rv_eval [hsp] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (Or.inl (by addr_omega [hw, hb]))
        | exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))
        | exact Or.inr (Or.inr (Or.inr (by addr_omega [hw, hb])))
  have hX₁ (a : Word) (ha : Within a (s.getReg .x2 - 920) 8 ∨
      Within a (s.getReg .x2 - 904) 8 ∨ Within a (s.getReg .x2 - 864) 8 ∨
      Within a (s.getReg .x2 - 304) 24) : SS s a := by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  obtain ⟨T₁, n₁⟩ := T₀.stepS hpre X₁ hX₁ (k₁ .x2 (by decide))
  have kw (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 920).toNat ∨ (s.getReg .x2 - 896).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 864).toNat ∨ (s.getReg .x2 - 856).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 304).toNat) : t₁.getMem y = u.getMem y :=
    X₁.word (fun a ha hx ↦ by
      rcases hy with hy | hy | hy <;> rcases hx with hx | hx | hx | hx <;>
        addr_omega [ha, hx, hy, hb]) (by rcases hy with hy | hy | hy <;> addr_omega [hy, hb])
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₁.sp
  have m736 := b8000b8ec_m_x2_736 h₁
  have m744 := b8000b8ec_m_x2_744 h₁
  have m752 := b8000b8ec_m_x2_752 h₁
  rw [hsp] at m736 m744 m752
  have hc : vecCap t₁ (s.getReg .x2 - 304) = 0 := by
    simp only [vecCap]; rw [show s.getReg .x2 - 304 = s.getReg .x2 - BitVec.ofNat 64 1040 + 736 by
      addr_omega [hb], m736]
  have hp : vecPtr t₁ (s.getReg .x2 - 304) = 8 := by
    simp only [vecPtr]; rw [show s.getReg .x2 - 304 + 8 = s.getReg .x2 - BitVec.ofNat 64 1040 + 744 by
      addr_omega [hb], m744]
  have hl : vecLen t₁ (s.getReg .x2 - 304) = 0 := by
    simp only [vecLen]; rw [show s.getReg .x2 - 304 + 16 = s.getReg .x2 - BitVec.ofNat 64 1040 + 752 by
      addr_omega [hb], m752]
  have tail₁ : TailV s u t₁ [] := by
    refine ⟨⟨?_, by rw [hc, hl]⟩, by simp only [vecEs, hl, hp]; rfl, ?_⟩
    · simp only [RawVecOk, Buf, hc, hp]; exact ⟨rfl, Or.inl rfl⟩
    · simp only [NewBuf, hc, hp]; exact ⟨rfl, Or.inl rfl⟩
  have hfl := h.fle
  have hx26 : u.getReg .x26 = s.getReg .x12 := h.x26
  have h112 : u.getMem (u.getReg .x2 + 112) = BitVec.ofNat 64 Wl.folds.length := by
    rw [hsp, show s.getReg .x2 - BitVec.ofNat 64 1040 + 112 = s.getReg .x2 - 928 by
      addr_omega [hb]]; exact h.m112
  have hv0 := h.value
  rw [finalTailM_eq] at hv0
  have v₁ := hv0.keep hpre (h.invR hpre) X₁ fun a ha ↦ Or.inl (by
    rcases ha with ha | ha | ha | ha <;> addr_omega [ha, hb])
  by_cases h0 : (s.getReg .x12).toNat - Wl.folds.length = 0
  · -- no rounds
    have he : (s.getReg .x12).toNat = Wl.folds.length := by omega
    refine ⟨t₁, r₁, Or.inr {
      toTI := T₁
      pc := b8000b8ec_pc_taken h₁ (by
        rw [hx26, h112, ← he]; exact ofNat_toNat_eq rfl)
      tfl := by simp only [mlF, List.length_nil]; omega
      x9 := by rw [k₁ .x9 (by decide), h.x9]
      x19 := by rw [b8000b8ec_x19 h₁]; simp only [mlF, h0]; rfl
      m224 := by rw [kw _ (Or.inr (Or.inr (by addr_omega [hb])))]; exact h.m224
      tail := tail₁
      trg := by
        have m0 := b8000b8ec_m_x2_136 h₁
        have m1 := b8000b8ec_m_x2_120 h₁
        have m2 := b8000b8ec_m_x2_176 h₁
        rw [hsp] at m0 m1 m2
        rw [show s.getReg .x2 - 904 = s.getReg .x2 - BitVec.ofNat 64 1040 + 136 by addr_omega [hb],
          show s.getReg .x2 - 920 = s.getReg .x2 - BitVec.ofNat 64 1040 + 120 by addr_omega [hb],
          show s.getReg .x2 - 864 = s.getReg .x2 - BitVec.ofNat 64 1040 + 176 by addr_omega [hb],
          m0, m1, m2]
        rfl
      value := by
        rw [h0, roundsK_end] at v₁
        exact v₁ }⟩
  -- the rounds' loop
  have hpos : 0 < mlF s Wl := by simp only [mlF]; omega
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000b914_spec
    (b8000b8ec_pc_not_taken h₁ (by
      rw [hx26, h112]; intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.getReg .x12).isLt; omega)] at this
      omega)) (by
      rv_eval [sp₁]; and_intros <;> valid_access hst.valid [hb])
  have k₂ := b8000b914_keeps h₂
  have hm₂ := b8000b914_mem_same h₂
  obtain ⟨T₂, n₂⟩ := T₁.stepS hpre (DFrame.of_same hm₂ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₂ .x2 (by decide))
  have hq := h.quad
  have hsL := h.hs
  refine ⟨t₂, r₁.trans r₂, Or.inl ⟨hpos, {
    toTI := T₂
    pc := b8000b914_pc h₂
    ilt := hpos
    tfl := rfl
    x9 := by rw [k₂ .x9 (by decide), k₁ .x9 (by decide), h.x9]
    x18 := by rw [k₂ .x18 (by decide), b8000b8ec_x18 h₁]; simp only [vecPtr]; rw [hm₂]; exact hp.symm
    x19 := by rw [b8000b914_x19 h₂]; rfl
    x20 := by rw [b8000b914_x20 h₂]; rfl
    x21 := b8000b914_x21 h₂
    x24 := by
      rw [b8000b914_x24 h₂, sp₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 224 =
        s.getReg .x2 - 816 by addr_omega [hb], kw _ (Or.inr (Or.inr (by addr_omega [hb])))]
      exact h.m224
    x25 := by
      rw [b8000b914_x25 h₂, sp₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 248 =
        s.getReg .x2 - 792 by addr_omega [hb], kw _ (Or.inr (Or.inr (by addr_omega [hb])))]
      exact h.m248
    m168 := by rw [hm₂, kw _ (Or.inr (Or.inl (by addr_omega [hb])))]; exact h.m168
    m224 := by rw [hm₂, kw _ (Or.inr (Or.inr (by addr_omega [hb])))]; exact h.m224
    tail := tail₁.keep T₁.heap T₁.fin.su (DFrame.of_same hm₂ (fun _ ↦ False)) (fun _ h ↦ h.elim)
      (fun _ h ↦ h.elim) (by addr_omega [hb]) (by simp only [heapNext, hm₂]; rfl)
    quad := by
      have q₀ : QuadAt s u Wl.runningQuad := ⟨hq.1, hq.2.1, by
        rcases hq.2.2 with h0 | h0
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, h0.2⟩⟩
      have q₁ := q₀.keep X₁ (fun a ha ↦ ⟨fun hw ↦ by
          rcases ha with ha | ha | ha | ha <;> addr_omega [ha, hw, hb], fun hw ↦ by
          rcases ha with ha | ha | ha | ha <;> addr_omega [ha, hw, hb]⟩)
        (fun a ha ↦ SS.heap hpre (hX₁ a ha) h.heap.hi) ⟨by addr_omega [hb], by addr_omega [hb]⟩
        h.heap.hi (by simp only [heapNext, n₁]; rfl)
      exact q₁.keep (DFrame.of_same hm₂ (fun _ ↦ False)) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
        ⟨by addr_omega [hb], by addr_omega [hb]⟩ T₁.heap.hi (by simp only [heapNext, hm₂]; rfl)
    value := by
      rw [roundsK_succ _ _ _ _ hpos] at v₁
      exact v₁.keep hpre (T₁.inv hpre) (DFrame.of_same hm₂ (fun _ ↦ False)) fun _ h ↦ h.elim }⟩⟩

/-- The rounds from `i` on. -/
theorem tLoop (hD : DuplexSpec) (hPE : PolyEvalSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8)
    (hRP : RoundPolyErrSpec) {OA : MachineState → Word → Model.TState → Prop} {s : MachineState}
    {x : LCtx} {u : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}
    (hpre : VsoPre s) : ∀ n i q tf v, mlF s Wl - i = n → TR OA s x u v Wl residual i q tf →
      ∃ w, Reaches Image.code v w ∧ (FailR s w ∨ ∃ tf rt, TA OA s x u w Wl residual tf rt) := by
  intro n
  induction n with
  | zero => intro i q tf v hn hr; exact absurd hr.ilt (by omega)
  | succ n ih =>
    intro i q tf v hn hr
    obtain ⟨w₁, r₁, hw₁⟩ := tSample hD hPE hpre hr
    rcases hw₁ with hd | ⟨c, hp⟩
    · exact ⟨w₁, r₁, Or.inl (Or.inl hd)⟩
    obtain ⟨w₂, r₂, hs⟩ := tMove hpre hp
    have hst : ∃ w₃, Reaches Image.code w₂ w₃ ∧ (Dead Image.code w₃ ∨
        TS OA s x u w₃ Wl residual i q tf c ∧ w₃.pc = 0x8000b998) := by
      rcases hs.pcr with h | h
      · exact ⟨w₂, Reaches.refl _, Or.inr ⟨hs, h.1⟩⟩
      · exact tGrow hG hpre hs h.1
    obtain ⟨w₃, r₃, hw₃⟩ := hst
    rcases hw₃ with hd | ⟨hs₃, hpc₃⟩
    · exact ⟨w₃, r₁.trans (r₂.trans r₃), Or.inl (Or.inl hd)⟩
    obtain ⟨w₄, r₄, hq⟩ := tStore hpre hs₃ hpc₃
    have hN : ∃ w₅, Reaches Image.code w₄ w₅ ∧ (FailR s w₅ ∨
        ∃ q', TN OA s x u w₅ Wl residual i q' (tf ++ [c]) (Model.polyEvalRust q c)) := by
      rcases hq.pcr with h | h
      · exact ⟨w₄, Reaches.refl _, Or.inr ⟨q, tLast hq h.1 h.2⟩⟩
      · exact tPoly hRP hpre hq h.1 h.2
    obtain ⟨w₅, r₅, hw₅⟩ := hN
    have r₁₅ := r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅)))
    rcases hw₅ with hf | ⟨q', hn'⟩
    · exact ⟨w₅, r₁₅, Or.inl hf⟩
    obtain ⟨w₆, r₆, hw₆⟩ := tNext hpre hn'
    rcases hw₆ with ⟨-, hr'⟩ | ha
    · obtain ⟨w, rw', hw⟩ := ih (i + 1) q' (tf ++ [c]) w₆ (by omega) hr'
      exact ⟨w, r₁₅.trans (r₆.trans rw'), hw⟩
    · exact ⟨w₆, r₁₅.trans r₆, Or.inr ⟨_, _, ha⟩⟩

/-- **The tail's rounds**: from `0x8000b8ec` to `0x8000ba14`, or an `Err`. -/
theorem tRounds (hD : DuplexSpec) (hPE : PolyEvalSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8)
    (hRP : RoundPolyErrSpec) {OA : MachineState → Word → Model.TState → Prop} {s : MachineState}
    {x : LCtx} {u : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}
    (hpre : VsoPre s) (h : VsoFinalIn OA s x u Wl residual) :
    ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ ∃ tf rt, TA OA s x u v Wl residual tf rt) := by
  obtain ⟨v, r, hv⟩ := tEnter hpre h
  rcases hv with ⟨-, hr⟩ | ha
  · obtain ⟨w, rw', hw⟩ := tLoop hD hPE hG hRP hpre _ 0 _ _ v rfl hr
    exact ⟨w, r.trans rw', hw⟩
  · exact ⟨v, r, Or.inr ⟨_, _, ha⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
