module

public import NativeRustcVmArm.Code.Vm.RingCoefficients.Names
public import NativeRustcVmArm.Ring.Coeff.Steps

/-!
# `ring_coefficients`: the prologue, the turn's end, the epilogue

- `stepEntry` (`b0`): the frame saved, `G = g` in its locations, the pointers and the counter set
  (`Head 0`);
- `stepTail` (`b17`): `G_7`'s image stored, the pointers moved, the counter decremented: the next
  turn's head, or after the last turn `Done`;
- `stepExit` (`b18`): `out` holds `ringCoefficients f g`, the registers restored.
-/

namespace NativeRustcVmArm.Ring.Coeff

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- **The prologue**: the slots, `g`'s elements into `G`'s locations, the pointers, the counter. -/
def entryOk (S : SState) : Bool :=
  (List.range 8).all (fun b ↦ locSet 176 S (.load 1 (16 * b) 8) (gLoc b).1 &&
      locSet 176 S (.load 1 (16 * b + 8) 8) (gLoc b).2) &&
    S.reg .X10 == some (.lit 8) && S.reg .X26 == some (.bin .add .W64 (.reg .X2) (.lit 64)) &&
    S.reg .X27 == some (.bin .add .W64 (.reg .X0) (.lit 8)) && S.sp == .ptr 0 0 &&
    slotsOk S slots && S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 176)

/-- **The turn's end**: `G_7`'s image stored, the pointers moved, the counter decremented. -/
def tailOk (S : SState) : Bool :=
  locSet 176 S (.reg .X0) (gLoc 7).1 && locSet 176 S (.reg .X1) (gLoc 7).2 && gKeep 7 S &&
    S.reg .X10 == some (.bin .sub .W64 cntLoc (.lit 1)) && S.reg .X26 == some (.ptr 1 192) &&
    S.reg .X27 == some (.ptr 2 24) && S.sp == .ptr 0 0 && S.mem == []

/-- The turn's branch back to the head. -/
def tailExit : Exit := .cond (.not (.cmp .eq .W64 cntLoc (.lit 1))) NativeRustcVmArm.Vm.RingCoefficients.label_1

/-- **After the last turn**: the frame, `out` complete. -/
structure Done [Labels] (m0 m : MachineData) : Prop where
  fr : CFr m0 m
  out : NativeRustcVm.EWsAt m.dmem (oA m0) (rc m0 8).1.toList

end

public section

variable {m0 : MachineData}

theorem toUInt64_toBitVec (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

/-! ## The prologue -/

/-- At the entry: the frame (region 0), `g` (region 1). -/
abbrev env0 (m0 : MachineData) : Env := Env.ofMachine m0 [(fb m0, 176), (gA m0, 128)]

theorem entry_wf (h : P m0) : (env0 m0).WF := by
  have hN := h.hN
  have he := stack_eq
  have hSP := m0.regs.SP.toNat_lt
  have hfb := h.fbN
  have hgs : Apart (gA m0) 128 (fb m0) 176 := apart_frame hN (by decide) h.gs
  have := h.gw
  unfold NoWrap Apart at *
  refine Env.wf_of ⟨⟨frame_mapped h.st (by decide), ?_⟩, ⟨h.gm, ?_⟩, trivial⟩
    (List.pairwise_pair.mpr ?_)
  · show (fb m0).toNat + 176 ≤ _; omega
  · show (gA m0).toNat + 128 ≤ _; omega
  · show (fb m0).toNat + 176 ≤ (gA m0).toNat ∨ (gA m0).toNat + 128 ≤ (fb m0).toNat
    omega

theorem entry_match [Labels] (h : P m0) : Match (env0 m0) entryS m0 :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.st (by decide) (by decide), rfl,
      fun h ↦ absurd h (by decide), trivial⟩
    (by
      show m0.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (176 : Nat)
      rw [BitVec.ofInt_natCast, base_add_eq])
    ⟨by show (m0.regs.getXReg .X1).toBitVec = _; simp [Sym.eval, gA]; rfl, trivial⟩
    trivial trivial trivial

variable [Host] {k : Nat}

/-- **The prologue** (`b0`). -/
theorem stepEntry (h : P m0) {i : Nat} {ds : List Directive} {S' : SState}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds entryS = some (S', .fall))
    (hS : entryOk S' = true) {R : MachineState → Prop}
    (cont : ∀ m1, Head m0 0 m1 →
      Eventually (step1 Host.exe) R ⟨m1, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf i⟩ := by
  have hwf := entry_wf h
  refine exec_then hk hrun hwf (entry_match h) fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  obtain ⟨d, pc⟩ := st
  simp only at hpc hm1
  subst hpc
  refine cont d ?_
  simp only [entryOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨hg, h10⟩, h26⟩, h27⟩, hsp⟩, hslots⟩, hmem⟩ := hS
  have hfr : CFr m0 d :=
    Fr.ofPrologue h.hN (by decide) hm1 hwf hsp hslots slots_le hmem (fun _ h ↦ by cases h)
  have hword : ∀ o, o + 8 ≤ 128 →
      (Sym.load 1 o 8).eval (env0 m0) =
        (NativeRustcVm.wordOf m0.dmem (gA m0 + BitVec.ofNat 64 o)).toBitVec := fun o _ ↦ by
    simp only [Sym.eval]
    rw [load_eq_wordOf]
    rfl
  exact {
    fr := hfr
    lt := by decide
    x26 := by
      rw [hm1.regs .X26 _ h26]
      simp [Sym.eval, BinOp.apply, rowA, oA]
      rfl
    x27 := by
      rw [hm1.regs .X27 _ h27]
      simp [Sym.eval, BinOp.apply, fA]
      rfl
    x10 := reg_of hm1 h10 rfl
    g := fun b hb ↦ by
      obtain ⟨k1, k2⟩ := hg b hb
      simp only [gv]
      rw [locVal_set hm1 k1, locVal_set hm1 k2, hword _ (by omega), hword _ (by omega),
        gG_zero hb, ← NativeRustcVm.addr_add_add]
      rfl
    out := by
      show NativeRustcVm.EWsAt _ _ (rcAt _ _ 0).1.toList
      rw [rcAt_zero]
      exact NativeRustcVm.ewsAt_nil _ _ }

/-! ## The turn's end -/

/-- **The turn's end** (`b17`): the next turn's head at the loop's label, or after the last turn
`Done` after the block. -/
theorem stepTail (h : P m0) {i p : Nat} {ds : List Directive} {S' : SState}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds midS = some (S', tailExit))
    (hS : tailOk S' = true) {m : MachineData} (hQ : SqD m0 p 7 m) {R : MachineState → Prop}
    (hnext : ∀ m1, Head m0 (p + 1) m1 →
      Eventually (step1 Host.exe) R ⟨m1, Labels.label NativeRustcVmArm.Vm.RingCoefficients.label_1⟩)
    (hdone : ∀ m1, Done m0 m1 →
      Eventually (step1 Host.exe) R ⟨m1, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := body_wf h hQ.toBody
  have hm := body_match h hQ.toBody
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  simp only [tailOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨hs1, hs2⟩, hg⟩, h10⟩, h26⟩, h27⟩, hsp⟩, hmem⟩ := hS
  have hp := hQ.lt
  have hfr : CFr m0 st.data :=
    hQ.fr.ofBlock hm hm1 hwf rfl hmem (by rw [hsp]; rfl) fun _ h ↦ by cases h
  have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf hmem
  have hgv : ∀ b < 8, gv m0 st.data b = frobenius8 (gG m0 p b) 1 := by
    intro b hb
    by_cases hb7 : b = 7
    · subst hb7
      simp only [gv]
      rw [locVal_set hm1 hs1, locVal_set hm1 hs2]
      simp only [Sym.eval, Env.ofMachine_regs, hQ.x0, hQ.x1]
    simp only [gKeep, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Bool.and_eq_true] at hg
    rcases hg b hb with hb8 | ⟨k1, k2⟩
    · exact absurd hb8 hb7
    have := hQ.g b hb
    simp only [gv] at this ⊢
    rw [locVal_keep hm1 k1, locVal_keep hm1 k2, this]
    simp [show b < 7 by omega]
  have hcnt : (cntLoc.eval (envB m0 p m)) = BitVec.ofNat 64 (8 - p) :=
    congrArg UInt64.toBitVec hQ.cnt
  simp only [PcOk, tailExit, SBool.eval, CmpOp.apply, Sym.eval, hcnt] at hpc
  by_cases hlast : p = 7
  · subst hlast
    have hc : (!(low RegWidth.W64 (BitVec.ofNat 64 (8 - 7)) == low RegWidth.W64 (BitVec.ofNat 64 1))) = false := by
      decide
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc
    obtain ⟨d, pc⟩ := st
    simp only at hpc hfr hd
    subst hpc
    refine hdone d ⟨hfr, ?_⟩
    rw [hd]
    exact hQ.out
  · have hc : (!(low RegWidth.W64 (BitVec.ofNat 64 (8 - p)) == low RegWidth.W64 (BitVec.ofNat 64 1))) = true := by
      simp only [low_W64]
      rw [Bool.not_eq_true', beq_eq_false_iff_ne]
      intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      omega
    simp only [hc, ↓reduceIte] at hpc
    obtain ⟨d, pc⟩ := st
    simp only at hpc hfr hd hgv
    subst hpc
    refine hnext d ?_
    exact {
      fr := hfr
      lt := by omega
      x26 := by
        rw [hm1.regs .X26 _ h26]
        simp only [Sym.eval]
        apply BitVec.eq_of_toNat_eq
        have := h.ow
        unfold NoWrap at this
        rw [show (envB m0 p m).base 1 = rowA m0 p from rfl,
          show BitVec.ofInt 64 192 = BitVec.ofNat 64 192 from rfl,
          NativeRustcVm.toNat_add_ofNat (by rw [rowA_toNat h hp]; omega), rowA_toNat h hp,
          NativeRustcVm.toNat_add_ofNat (by rw [rowA_toNat h (by omega)]; omega),
          rowA_toNat h (by omega)]
        omega
      x27 := by
        rw [hm1.regs .X27 _ h27]
        simp only [Sym.eval]
        apply BitVec.eq_of_toNat_eq
        have := h.fw
        unfold NoWrap at this
        rw [show (envB m0 p m).base 2 = fA m0 + BitVec.ofNat 64 (16 * p) from rfl,
          show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.toNat_add_ofNat (by rw [fp_toNat h hp]; omega),
          fp_toNat h hp, NativeRustcVm.toNat_add_ofNat (by rw [fp_toNat h (by omega)]; omega),
          fp_toNat h (by omega)]
        omega
      x10 := by
        refine reg_of hm1 h10 ?_
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show (Sym.eval (envB m0 p m) cntLoc) = _ from hcnt]
        apply BitVec.eq_of_toNat_eq
        simp only [toUInt64_toBitVec, BitVec.toNat_sub, BitVec.toNat_ofNat,
          show (2 : Nat) ^ MemWidth.W64.bits = 2 ^ 64 from rfl]
        omega
      g := fun b hb ↦ by rw [hgv b hb, gG_succ hp hb]
      out := by rw [hd]; exact hQ.out }

/-! ## The epilogue -/

/-- At the epilogue: region 0 the frame. -/
abbrev envX (m0 m : MachineData) : Env := Env.ofMachine m [(fb m0, 176)]

/-- **The epilogue** (`b18`). -/
theorem stepExit (h : P m0) {i : Nat} (hk : Vm.RingCoefficients.b18.IsInfixAt Host.prog i)
    {m : MachineData} (hD : Done m0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ RingCoefficientsPost m0 st.data)
      ⟨m, Host.addrOf i⟩ := by
  have hN := h.hN
  have he := stack_eq
  have hwf : (envX m0 m).WF :=
    Env.wf_of ⟨⟨fun j hj ↦ hD.fr.kept _ (frame_mapped h.st (by decide) j hj),
      base_noWrap (by omega)⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (envX m0 m) exitS m :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.st (by decide) (by decide), trivial⟩
      (by
        show m.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (0 : Nat)
        rw [hD.fr.sp]
        simp)
      trivial trivial trivial trivial
  refine exec_then hk run_b18 hwf hm fun st hm1 hpc ↦ ?_
  obtain ⟨hret, hsaved⟩ := hD.fr.exit hm1 hwf (by decide)
  have hpc' : st.pc = retOf m0 := by simp only [PcOk] at hpc; rw [hpc, hret]
  have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  refine .done _ ⟨hpc', ?_, ?_, hsaved⟩
  · rw [hd]
    have := hD.out
    rwa [rc, show (8 : Nat) = (fl m0).length from fl_length.symm, rcAt_length] at this
  · intro q hq
    rw [hd]
    refine hD.fr.same q fun hc ↦ hq ?_
    rcases hc with hc | hc
    · exact .inr hc
    · exact .inl hc

end

end NativeRustcVmArm.Ring.Coeff
