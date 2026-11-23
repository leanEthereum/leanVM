module

public import NativeRustcVmArm.Code.Vm.RdRows.Names
public import NativeRustcVmArm.Code.Vm.ReaderWords.Names
public import NativeRustcVmArm.Wire.RdRows.RowB

/-!
# `rd_rows` meets its contract

`rdRows_spec`: the prologue and the width check (`b0`, `rw ≤ lw` always), the set-up (`b3`), then
rows of `rw > 0` words (`b4`, `loopA`) or none (`b15`, `loopB`).
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.RdRows
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem frame_sub (hst : StackOk m0 144) {q : BitVec 64} (h : InRange (base m0 112) 112 q) :
    InRange (base m0 144) 144 q := by
  rw [← Ring.base_add (F := 112) (N := 144) (by omega) hst.2.1] at h
  exact NativeRustcVm.InRange.of_sub h (Ring.base_noWrap hst.2.1) (by omega)

/-- **The places** from the precondition. -/
theorem geo_of [Labels] (h : RdRowsPre m0) (hR : ReaderAt m0.dmem (rdr m0) bp B c) : Geo m0 bp B := by
  obtain ⟨hst, hn0, hn, hlw, hrw, ⟨hom, honw⟩, bp', B', c', hR', hd⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := hR'.unique hR
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hd
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := hd
  exact ⟨RGeo.of_apart hst hR.ok.2 hR.noWrap honw h1 h2 h3 h4 h5 h6, hom, honw, hn0, hn, hlw, hrw,
    h3.symm, h5.symm, h6.symm⟩

variable [Host] {k : Nat}

/-- **From the entry.** -/
theorem entry_spec (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hw : Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) :
    Eventually (step1 Host.exe) (Post m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.RdRows.b0Offset)⟩ := by
  have hst := G.g.st
  have hN := hst.2.1
  have hlw := G.lw64
  have hrl := G.rwlw
  have hn := G.n256
  have hn0 := G.n0
  have hnw := G.lvNw
  let env0 := Env.ofMachine m0 [(base m0 112, 112)]
  have hb := Ring.base_noWrap (m0 := m0) (F := 112) (by omega)
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨Ring.frame_mapped hst (by omega), hb⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 := match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show BitVec.ofInt 64 112 = BitVec.ofNat 64 112 from rfl]
        exact Ring.base_add_eq.symm)
    trivial trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  rw [← after_eq run_b0] at hm1
  have hfr1 : Frm m0 s1.data :=
    Fr.ofPrologue hN (by omega) hm1 hwf0 (by decide) (by decide +kernel) (by decide)
      (by decide +kernel) (by simp)
  have hs1 := Match.sameOutside_in hm1 hwf0 (r0 := 0) (o := 0) (n := 112) rfl (by omega)
    (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at hs1
  have hR1 : ReaderAt s1.data.dmem (rdr m0) bp B c :=
    G.g.reader_frame rfl hR (NativeRustcVm.SameOutside.mono hs1 fun _ h ↦ .inl (frame_sub hst h))
  have e1 : ∀ x v, (after b0 entryS).reg x = some v →
      (s1.data.regs.getXReg x).toBitVec = v.eval env0 := fun x v h ↦ hm1.regs x v h
  have hc : (SBool.cmp .ult .W64 (.reg .X2) (.reg .X3)).not.eval env0 = true := by
    simp only [SBool.eval, ult_apply, Sym.eval, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt]
    exact hrl
  simp only [PcOk, hc, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b3Offset) NativeRustcVmArm.Vm.RdRows.label_3_at] at hpc1
  have h8 : (s1.data.regs.getXReg .X8).toNat = zc m0 := by
    show (s1.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [e1 .X8 (.bin .sub .W64 (.reg .X2) (.reg .X3)) (by decide)]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_sub]
    show (2 ^ 64 - rw m0 + lw m0) % 2 ^ 64 = lw m0 - rw m0
    have := m0.regs.X3.toNat_lt
    omega
  have ha : ∀ x ∈ [XReg.X0, .X1, .X2, .X3, .X4], s1.data.regs.getXReg x = m0.regs.getXReg x := by
    intro x hx
    exact Match.reg_eq hm0 hm1 (v := .reg x)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  -- `b3`
  have hwf3 := frEnv_wf hst hfr1
  have hm3 := frEnv_match hst hfr1
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3 hpc1 hm3 fun s3 hm3' hpc3 ↦ ?_
  have hd3 : s3.data.dmem = s1.data.dmem := hm3'.dmem_eq hwf3 rfl
  have hfr3 : Frm m0 s3.data := Fr.ofBlock hfr1 hm3 hm3' hwf3 rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have e3 : ∀ x v, (after b3 frS).reg x = some v →
      (s3.data.regs.getXReg x).toBitVec = v.eval (frEnv m0 s1.data) := fun x v h ↦ by
    rw [after_eq run_b3] at h; exact hm3'.regs x v h
  have x19 : (s3.data.regs.getXReg .X19).toBitVec = leaf m0 0 := by
    rw [e3 .X19 (.reg .X4) (by decide)]
    show (s1.data.regs.getXReg .X4).toBitVec = _
    rw [ha .X4 (by simp)]
    show _ = lv m0 + BitVec.ofNat 64 (512 * 0)
    rw [Nat.mul_zero, NativeRustcVm.addr_add_zero]; rfl
  have x20 : s3.data.regs.getXReg .X20 = m0.regs.X2 := by
    apply UInt64.toBitVec_inj.mp
    rw [e3 .X20 (.reg .X2) (by decide)]
    show (s1.data.regs.getXReg .X2).toBitVec = _
    rw [ha .X2 (by simp)]; rfl
  have x21 : (s3.data.regs.getXReg .X21).toBitVec = rdr m0 := by
    rw [e3 .X21 (.reg .X0) (by decide)]
    show (s1.data.regs.getXReg .X0).toBitVec = _
    rw [ha .X0 (by simp)]; rfl
  have x22 : s3.data.regs.getXReg .X22 = m0.regs.X3 := by
    apply UInt64.toBitVec_inj.mp
    rw [e3 .X22 (.reg .X3) (by decide)]
    show (s1.data.regs.getXReg .X3).toBitVec = _
    rw [ha .X3 (by simp)]; rfl
  have x24 : (s3.data.regs.getXReg .X24).toBitVec = leaf m0 (nr m0) := by
    rw [hm3'.regs .X24 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [ha .X4 (by simp), ha .X1 (by simp)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [lsl9 (by show 512 * nr m0 < 2 ^ 64; omega), BitVec.toNat_ofNat]
    show 512 * nr m0 = 512 * nr m0 % 2 ^ 64
    omega
  have x8 : (s3.data.regs.getXReg .X8).toNat = zc m0 := by
    rw [Match.reg_eq hm3 hm3' (v := .reg .X8) rfl rfl]; exact h8
  have hkept : Kept m0 bp B c 0 [] c s3.data.dmem :=
    ⟨rfl, by rw [hd3]; exact hR1, fun _ h ↦ absurd h (by simp)⟩
  have hc3 : (SBool.cmp .eq .W64 (.reg .X3) (.lit 0)).eval (frEnv m0 s1.data) =
      decide (rw m0 = 0) := by
    simp only [SBool.eval, eq_apply, Sym.eval, Env.ofMachine_regs, ha .X3 (by simp)]
    rfl
  simp only [PcOk, hc3] at hpc3
  by_cases hr0 : rw m0 = 0
  · -- no row: `b15`
    simp only [hr0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.RdRows.b15Offset) NativeRustcVmArm.Vm.RdRows.label_13_at] at hpc3
    have hwf4 := frEnv_wf hst hfr3
    have hm4 := frEnv_match hst hfr3
    refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf4 hpc3 hm4
      fun s4 hm4' hpc4 ↦ ?_
    have hd4 : s4.data.dmem = s3.data.dmem := hm4'.dmem_eq hwf4 rfl
    have hfr4 : Frm m0 s4.data := Fr.ofBlock hfr3 hm4 hm4' hwf4 rfl rfl rfl
      fun x hx ↦ absurd hx (by simp)
    have hk : ∀ x ∈ [XReg.X19, .X20, .X21, .X24],
        s4.data.regs.getXReg x = s3.data.regs.getXReg x :=
      regs_keep hm4 hm4' (by decide)
    have h20 : (s3.data.regs.getXReg .X20).toBitVec.toNat = lw m0 := by rw [x20]; rfl
    have h22 : (UnOp.apply (.ubfm 61 60) .W64 (s3.data.regs.getXReg .X20).toBitVec).toNat =
        8 * lw m0 := by
      rw [lsl3 (by rw [h20]; omega), h20]
    simp only [PcOk] at hpc4
    refine loopB hp G hR hw (rows := []) (ci := c) ⟨hpc4.trans (congrArg Host.addrOf rfl),
      ⟨hfr4, by rw [hk .X19 (by simp)]; exact x19, by rw [hk .X20 (by simp)]; exact x20,
        by rw [hk .X21 (by simp)]; exact x21, ?_, ?_, by rw [hk .X24 (by simp)]; exact x24, ?_, ?_,
        ?_, ?_, G.n0, hr0⟩, by rw [hd4]; exact hkept⟩
    · show (s4.data.regs.getXReg .X22).toBitVec.toNat = _
      rw [hm4'.regs .X22 _ rfl]
      exact h22
    · intro hl
      show (s4.data.regs.getXReg .X23).toBitVec.toNat = _
      rw [hm4'.regs .X23 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [toNat_sub_lit (by rw [h22]; omega) (by omega), h22]
    · intro hl
      show (s4.data.regs.getXReg .X25).toBitVec.toNat = _
      rw [hm4'.regs .X25 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [toNat_add_lit (by rw [lsr3, toNat_sub_lit (by rw [h22]; omega) (by omega), h22]; omega)
        (by omega), lsr3, toNat_sub_lit (by rw [h22]; omega) (by omega), h22]
      omega
    · intro hl
      show (s4.data.regs.getXReg .X26).toBitVec.toNat = _
      rw [hm4'.regs .X26 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      have e25 : (BinOp.apply .add .W64 (UnOp.apply (.ubfm 3 63) .W64 (BinOp.apply .sub .W64
          (UnOp.apply (.ubfm 61 60) .W64 (s3.data.regs.getXReg .X20).toBitVec)
          (BitVec.ofNat 64 8))) (BitVec.ofNat 64 1)).toNat = lw m0 := by
        rw [toNat_add_lit (by rw [lsr3, toNat_sub_lit (by rw [h22]; omega) (by omega), h22]; omega)
          (by omega), lsr3, toNat_sub_lit (by rw [h22]; omega) (by omega), h22]
        omega
      rw [and_mask (by rw [e25]; omega), e25]
    · intro hl
      show (s4.data.regs.getXReg .X27).toBitVec.toNat = _
      rw [hm4'.regs .X27 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      have e25 : (BinOp.apply .add .W64 (UnOp.apply (.ubfm 3 63) .W64 (BinOp.apply .sub .W64
          (UnOp.apply (.ubfm 61 60) .W64 (s3.data.regs.getXReg .X20).toBitVec)
          (BitVec.ofNat 64 8))) (BitVec.ofNat 64 1)).toNat = lw m0 := by
        rw [toNat_add_lit (by rw [lsr3, toNat_sub_lit (by rw [h22]; omega) (by omega), h22]; omega)
          (by omega), lsr3, toNat_sub_lit (by rw [h22]; omega) (by omega), h22]
        omega
      have hq := q4_le (lw m0)
      rw [lsl3 (by rw [and_mask (by rw [e25]; omega), e25]; omega), and_mask (by rw [e25]; omega),
        e25]
    · rw [hm4'.regs .X28 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [x19]
  -- rows: `b4`
  simp only [hr0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
  have hwf4 := frEnv_wf hst hfr3
  have hm4 := frEnv_match hst hfr3
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf4 hpc3 hm4
    fun s4 hm4' hpc4 ↦ ?_
  have hfr4 : Frm m0 s4.data := Fr.ofBlockW hfr3 hm4 hm4' hwf4 rfl rfl
    (fun x hx ↦ absurd hx (by simp)) rfl (by omega) hN (by decide) (by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      left
      decide)
  have hs4 : SameOutside s3.data.dmem s4.data.dmem (InRange (base m0 112 + BitVec.ofNat 64 8) 8) :=
    Match.sameOutside_in hm4' hwf4 (r0 := 0) (o := 8) (n := 8) rfl (by omega)
      (by decide)
  have hkept4 : Kept m0 bp B c 0 [] c s4.data.dmem :=
    ⟨rfl, G.g.reader_frame rfl hkept.hrd (NativeRustcVm.SameOutside.mono hs4 fun q h ↦ .inl
      (frame_sub hst (NativeRustcVm.InRange.of_sub h hb (by omega)))),
      fun _ h ↦ absurd h (by simp)⟩
  have hk : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X24], s4.data.regs.getXReg x = s3.data.regs.getXReg x :=
    regs_keep hm4 hm4' (by decide)
  have h20 : (s3.data.regs.getXReg .X20).toBitVec.toNat = lw m0 := by rw [x20]; rfl
  have h22 : (s3.data.regs.getXReg .X22).toBitVec.toNat = rw m0 := by rw [x22]; rfl
  have hzc : zc m0 = lw m0 - rw m0 := rfl
  have e25 : 0 < zc m0 → (BinOp.apply .bic .W64 (BitVec.ofNat 64 2305843009213693951)
      (BinOp.apply .sub .W64 (s3.data.regs.getXReg .X22).toBitVec
        (s3.data.regs.getXReg .X20).toBitVec)).toNat = zc m0 - 1 := fun hz ↦ by
    rw [bic_sub (by rw [h20, h22]; omega) (by rw [h20]; omega), h20, h22]
  have e9 : 0 < zc m0 → (BinOp.apply .and .W64 (BinOp.apply .add .W64
      (BinOp.apply .bic .W64 (BitVec.ofNat 64 2305843009213693951)
        (BinOp.apply .sub .W64 (s3.data.regs.getXReg .X22).toBitVec
          (s3.data.regs.getXReg .X20).toBitVec)) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 4611686018427387900)).toNat = q4 (zc m0) := fun hz ↦ by
    rw [and_mask (by rw [toNat_add_lit (by rw [e25 hz]; omega) (by omega), e25 hz]; omega),
      toNat_add_lit (by rw [e25 hz]; omega) (by omega), e25 hz]
    congr 1
    omega
  simp only [PcOk] at hpc4
  refine loopA hp G hR hw (rows := []) (ci := c) ⟨hpc4.trans (congrArg Host.addrOf rfl),
    ⟨hfr4, by rw [hk .X19 (by simp)]; exact x19, by rw [hk .X20 (by simp)]; exact x20,
      by rw [hk .X21 (by simp)]; exact x21, by rw [hk .X22 (by simp)]; exact x22, ?_,
      by rw [hk .X24 (by simp)]; exact x24, ?_, ?_, ?_, ?_, ?_, G.n0, by omega⟩, hkept4⟩
  · show (s4.data.regs.getXReg .X23).toBitVec.toNat = _
    rw [hm4'.regs .X23 _ rfl]
    rfl
  · intro hz
    show (s4.data.regs.getXReg .X25).toBitVec.toNat = _
    rw [hm4'.regs .X25 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    exact e25 hz
  · rw [hm4'.regs .X27 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [x19]
  · show (s4.data.regs.getXReg .X28).toBitVec.toNat = _
    rw [hm4'.regs .X28 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [lsl3 (by show 8 * (s3.data.regs.getXReg .X8).toNat < 2 ^ 64; rw [x8]; omega)]
    exact congrArg (8 * ·) x8
  · intro hz
    show (s4.data.regs.getXReg .X29).toBitVec.toNat = _
    rw [hm4'.regs .X29 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    have hq := q4_le (zc m0)
    rw [lsl3 (by rw [e9 hz]; omega), e9 hz]
  · intro hz
    have h := hm4'.bytesAt_write (r := 0) (o := 8) (n := 8) (b := base m0 112) (sz := 112) rfl
      (by omega) (v := .bin .and .W64 (.bin .add .W64 (.bin .bic .W64 (.lit 2305843009213693951)
        (.bin .sub .W64 (.reg .X22) (.reg .X20))) (.lit 1)) (.lit 4611686018427387900))
      (by decide)
    rw [byteOf_range] at h
    have hq := q4_le (zc m0)
    have hv : UInt64.ofBitVec ((Sym.bin .and .W64 (.bin .add .W64 (.bin .bic .W64
        (.lit 2305843009213693951) (.bin .sub .W64 (.reg .X22) (.reg .X20))) (.lit 1))
        (.lit 4611686018427387900)).eval (frEnv m0 s3.data)) = (q4 (zc m0)).toUInt64 := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_ofBitVec, Sym.eval, Env.ofMachine_regs]
      rw [e9 hz]
      exact (toNat_toUInt64_of_lt (by omega)).symm
    rw [hv] at h
    exact h

/-- **`rd_rows` meets its contract.** -/
theorem rdRows_spec (hp : Placed code k)
    (hw : Spec (Labels.label NativeRustcVmArm.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost := by
  intro m0 hpre
  obtain ⟨-, -, -, -, -, -, bp, B, c, hR, -⟩ := id hpre
  rw [hp.label (j := NativeRustcVmArm.Vm.RdRows.entryOffset) NativeRustcVmArm.Vm.RdRows.entry_at]
  exact entry_spec hp (geo_of hpre hR) hR hw

end

end NativeRustcVmArm.Wire.RdRows
