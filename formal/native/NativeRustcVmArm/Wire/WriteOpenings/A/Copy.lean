module

public import NativeRustcVmArm.Wire.WriteOpenings.A.Scan
public import NativeRustcVmArm.Wire.WriteOpenings.Copy

/-!
# `write_openings`' leaf copy set up and done (`h > 0`)

Query `j` found at position `i` (`FoundA`): the arguments saved (`found_step`, `b6`); four words
at a time or one (`b7_step`, `b7`, `b8`); the last words set up (`b11_step`, `b11`); the leaf
copied, opening `j`'s addresses saved, the first level (`b13_step`, `b13`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

/-- The registers the copy keeps. -/
abbrev cpRegs : List XReg := [.X15, .X16, .X17, .X19, .X20, .X21, .X22, .X23, .X25, .X26, .X29]

section
variable [Host]

/-- The leaf's copy set up (`b7`), none copied. -/
structure AtB7 (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b7Offset
  c : CopyA R j i 0 st.data
  x8 : rv st.data .X8 = R.lv + BitVec.ofNat 64 (512 * i)
  x9 : rv st.data .X9 = R.lv + BitVec.ofNat 64 (512 * i + 16)
  lw0 : 0 < R.lw

/-- The last words, one at a time (`b11`), `t` copied. -/
structure AtB11 (R : Run) (j i t : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b11Offset
  c : CopyA R j i t st.data
  x8 : rv st.data .X8 = R.lv + BitVec.ofNat 64 (512 * i)
  x10 : rv st.data .X10 = BitVec.ofNat 64 t
  tlt : t < R.lw

/-- The leaf copied (`b13`). -/
structure AtB13 (R : Run) (j i : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b13Offset
  c : CopyA R j i R.lw st.data

end

end

public section

variable {R : Run} {j i : Nat}

theorem CopyA.keep {t : Nat} {m m' : MachineData} (h : CopyA R j i t m) (hfr : Frm R m')
    (hd : m'.dmem = m.dmem) (hk : ∀ r ∈ cpRegs, m'.regs.getXReg r = m.regs.getXReg r) :
    CopyA R j i t m' where
  fr := hfr
  cs := h.cs.keep fun r hr ↦ hk r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h <;> simp [h])
  cr := h.cr.keep fun r hr ↦ hk r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h])
  x25 := by rw [hk .X25 (by simp)]; exact h.x25
  lt := h.lt
  ilt := h.ilt
  h0 := h.h0
  pos := h.pos
  w1 := hd ▸ h.w1
  mem := hd ▸ h.mem
  leaf := hd ▸ h.leaf
  tle := h.tle

/-- Frame words apart from a write in the frame survive it. -/
theorem Geo.fw_keepF (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (InRange (base R.m0 176 + BitVec.ofNat 64 o) n)) (hon : o + n ≤ 176)
    {f : Nat} (hf : f + 8 ≤ 176) (hd : f + 8 ≤ o ∨ o + n ≤ f) {v : BitVec 64}
    (h : FW R d f v) : FW R d' f v := by
  have hnw : NativeRustcVm.NoWrap (base R.m0 176) 176 := G.noWrap (i := 0) (by omega)
  exact NativeRustcVm.BytesAt.of_sameOutside h hs fun t ht ↦ by
    rw [NativeRustcVm.length_wordBytes] at ht
    rw [NativeRustcVm.addr_add_add]
    exact NativeRustcVm.not_inRange_sub hnw hon (by omega) (by omega)

variable [Host]

/-- **The arguments saved** (`b6`): the copy, or none (`lw = 0`). -/
theorem found_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : FoundA R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtB7 R j i st' ∨ AtB13 R j i st') st := by
  have hj := H.lt
  have hlw := G.lw64
  have hwf := G.wf0 H.fr.kept
  have hm := frMatch G H.fr
  refine run_block G hp b6_in_code (by simp [b6]) run_b6 H.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem
      (InRange (base R.m0 176 + BitVec.ofNat 64 32) 48) :=
    Match.sameOutside_in hm1 hwf (r0 := 0) (o := 32) (n := 48) rfl (by omega) (by decide)
  have hmem : Begun R j s1.data.dmem := G.begun_keepW hs (G.frame_apart (by omega)) hj H.mem
  have hk1 := regs_keep hm hm1 (rs := .X8 :: .X9 :: cpRegs) (by decide)
  have w1 : FrW1 R j s1.data.dmem := by
    have w32 := stored hm1 (r := 0) (o := 32) (sz := 176) (v := .reg .X13) rfl (by omega)
      (by decide)
    have w40 := stored hm1 (r := 0) (o := 40) (sz := 176) (v := .reg .X4) rfl (by omega)
      (by decide)
    have w48 := stored hm1 (r := 0) (o := 48) (sz := 176) (v := .reg .X3) rfl (by omega)
      (by decide)
    have w56 := stored hm1 (r := 0) (o := 56) (sz := 176) (v := .reg .X1) rfl (by omega)
      (by decide)
    have w64 := stored hm1 (r := 0) (o := 64) (sz := 176) (v := .reg .X5) rfl (by omega)
      (by decide)
    have w72 := stored hm1 (r := 0) (o := 72) (sz := 176) (v := .reg .X2) rfl (by omega)
      (by decide)
    simp only [Sym.eval, Env.ofMachine_regs] at w32 w40 w48 w56 w64 w72
    rw [H.x13] at w32
    rw [H.args.x4] at w40
    rw [H.args.x3] at w48
    rw [H.args.x1] at w56
    rw [H.args.x5] at w64
    rw [H.x2] at w72
    exact ⟨w32, w40, w48, w56, w64, w72⟩
  have C : ∀ t, R.LeafPart s1.data.dmem j i t → t ≤ R.lw → CopyA R j i t s1.data :=
    fun t hl ht ↦ ⟨hfr1, H.cs.keep (regs_keep hm hm1 (by decide)),
      H.cr.keep (regs_keep hm hm1 (by decide)), by rw [hk1 .X25 (by simp)]; exact H.x25, hj,
      H.ilt, H.h0, H.pos, w1, hmem, hl, ht⟩
  have hc : (SBool.cmp .eq .W64 (.reg .X21) (.lit 0)).eval (envOf R st.data []) =
      decide (R.lw = 0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs]
    rw [H.cs.x21, ofNat_toNat (by omega), ofNat_toNat (by omega)]
  simp only [PcOk, hc] at hpc1
  by_cases hl0 : R.lw = 0
  · simp only [hl0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b13Offset) NativeRustcVmArm.Vm.WriteOpenings.label_12_at] at hpc1
    exact .done _ (.inr ⟨hpc1, C _ (by rw [hl0]; exact leaf_zero) (le_refl _)⟩)
  · simp only [hl0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact .done _ (.inl ⟨hpc1.trans (congrArg Host.addrOf rfl), C 0 leaf_zero (Nat.zero_le _),
      by rw [hk1 .X8 (by simp)]; exact H.x8, by rw [hk1 .X9 (by simp)]; exact H.x9, by omega⟩)

/-- **Four words at a time, or one** (`b7`, `b8`). -/
theorem b7_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : AtB7 R j i st) :
    Eventually (step1 Host.exe) (fun st' ↦ ChunkA R j i 0 st' ∨ AtB11 R j i 0 st') st := by
  have C := H.c
  have hlw := G.lw64
  have hwf := G.wf0 C.fr.kept
  have hm := frMatch G C.fr
  refine run_block G hp b7_in_code (by simp [b7]) run_b7 C.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := .X8 :: .X9 :: cpRegs) (by decide)
  have C1 : CopyA R j i 0 s1.data :=
    C.keep hfr1 hd1 fun r hr ↦ hk1 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  have hc : (SBool.cmp .ult .W64 (.reg .X21) (.lit 4)).not.eval (envOf R st.data []) =
      decide (4 ≤ R.lw) := by
    simp only [SBool.eval, ult_apply, Sym.eval, Env.ofMachine_regs]
    rw [C.cs.x21, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    by_cases h : 4 ≤ R.lw
    · rw [decide_eq_false (by omega : ¬R.lw < 4), decide_eq_true h]; rfl
    · rw [decide_eq_true (by omega : R.lw < 4), decide_eq_false h]; rfl
  simp only [PcOk, hc] at hpc1
  by_cases h4 : 4 ≤ R.lw
  · simp only [h4, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b9Offset) NativeRustcVmArm.Vm.WriteOpenings.label_8_at] at hpc1
    refine .done _ (.inl ⟨hpc1, C1, by rw [hk1 .X8 (by simp)]; exact H.x8, ?_, ?_, ?_, rfl,
      by show 0 + 4 ≤ R.lw / 4 * 4; omega⟩)
    · rw [hk1 .X9 (by simp), H.x9, Nat.mul_zero, Nat.add_zero]
    · rw [hm1.regs .X10 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [C.cr.x16, Nat.mul_zero, Nat.add_zero]
    · rw [hm1.regs .X11 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [C.cs.x21, and124 (by omega), Nat.sub_zero]
  · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hwf2 := G.wf0 hfr1.kept
    have hm2 := frMatch G hfr1
    refine run_block G hp b8_in_code (by simp [b8]) run_b8 hfr1
      (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
      fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hk2 := regs_keep hm2 hm2' (rs := .X8 :: cpRegs) (by decide)
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b11Offset) NativeRustcVmArm.Vm.WriteOpenings.label_10_at] at hpc2
    refine .done _ (.inr ⟨hpc2, C1.keep hfr2 hd2 fun r hr ↦ hk2 r (List.mem_cons_of_mem _ hr),
      by rw [hk2 .X8 (by simp), hk1 .X8 (by simp)]; exact H.x8, ?_, H.lw0⟩)
    rw [hm2'.regs .X10 _ rfl]
    rfl

/-- **The last words set up** (`b11`). -/
theorem b11_step (hp : Placed code R.k) (G : Geo R) {t : Nat} {st : MachineState}
    (H : AtB11 R j i t st) : Eventually (step1 Host.exe) (RemA R j i t) st := by
  have C := H.c
  have hlw := G.lw64
  have ht := H.tlt
  have hwf := G.wf0 C.fr.kept
  have hm := frMatch G C.fr
  refine run_block G hp b11_in_code (by simp [b11]) run_b11 C.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ .done _ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := cpRegs) (by decide)
  refine ⟨hpc1.trans (congrArg Host.addrOf rfl), C.keep hfr1 hd1 hk1, ?_, ?_, ?_, ht⟩
  · rw [hm1.regs .X8 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, lsl3]
    rw [H.x8, H.x10, ofNat_toNat (by omega)]
    exact addr_add rfl
  · rw [hm1.regs .X9 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, lsl3]
    rw [C.cr.x17, H.x10, ofNat_toNat (by omega)]
    exact addr_add rfl
  · rw [hm1.regs .X10 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [C.cs.x21, H.x10, ofNat_sub (by omega)]

/-- **The leaf copied** (`b13`): opening `j`'s addresses saved, its first level. -/
theorem b13_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : AtB13 R j i st) :
    Eventually (step1 Host.exe) (LevA R j 0) st := by
  have C := H.c
  have hj := C.lt
  have hwf := G.wf0 C.fr.kept
  have hm := frMatch G C.fr
  refine run_block G hp b13_in_code (by simp [b13]) run_b13 C.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ .done _ ?_
  have hs : SameOutside st.data.dmem s1.data.dmem
      (InRange (base R.m0 176 + BitVec.ofNat 64 8) 24) :=
    Match.sameOutside_in hm1 hwf (r0 := 0) (o := 8) (n := 24) rfl (by omega) (by decide)
  have hW := G.frame_apart (o := 8) (n := 24) (by omega)
  have hk1 := regs_keep hm hm1 (rs := cpRegs) (by decide)
  have w2 : FrW2 R j s1.data.dmem := by
    have w8 := stored hm1 (r := 0) (o := 8) (sz := 176) (v := .reg .X20) rfl (by omega)
      (by decide)
    have w16 := stored hm1 (r := 0) (o := 16) (sz := 176) (v := .reg .X17) rfl (by omega)
      (by decide)
    have w24 := stored hm1 (r := 0) (o := 24) (sz := 176) (v := .reg .X16) rfl (by omega)
      (by decide)
    simp only [Sym.eval, Env.ofMachine_regs] at w8 w16 w24
    rw [C.cr.x20] at w8
    rw [C.cr.x17] at w16
    rw [C.cr.x16] at w24
    exact ⟨w8, w16, w24⟩
  have w1 : FrW1 R j s1.data.dmem :=
    ⟨G.fw_keepF hs (by omega) (by omega) (by omega) C.w1.w32,
      G.fw_keepF hs (by omega) (by omega) (by omega) C.w1.w40,
      G.fw_keepF hs (by omega) (by omega) (by omega) C.w1.w48,
      G.fw_keepF hs (by omega) (by omega) (by omega) C.w1.w56,
      G.fw_keepF hs (by omega) (by omega) (by omega) C.w1.w64,
      G.fw_keepF hs (by omega) (by omega) (by omega) C.w1.w72⟩
  simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b16Offset) NativeRustcVmArm.Vm.WriteOpenings.label_15_at] at hpc1
  refine ⟨hpc1, hfr1, C.cs.keep fun r hr ↦ hk1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h <;> simp [h]), ?_,
    by rw [hk1 .X25 (by simp)]; exact C.x25, by rw [hm1.regs .X27 _ rfl]; rfl,
    by rw [hm1.regs .X28 _ rfl]; rfl, hj, C.h0, w1, w2, G.begun_keepW hs hW hj C.mem,
    ⟨i, C.pos, G.leaf_keepW hs hW hj (le_refl _) C.leaf⟩, path_zero⟩
  rw [hk1 .X20 (by simp), C.cr.x20, Nat.mul_zero, Nat.add_zero]

end

end NativeRustcVmArm.Wire.WriteOpenings
