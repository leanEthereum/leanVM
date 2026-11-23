module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldR4

/-!
# `keccak_open`'s fold: round 5

Rows 0 and 1 copied (`b88`, `b89`), the pointers set (`b90`), the inner loop (`b91`, `b92`) with
the counter X23 counting down and the three pointers X25, X24, X21 counting up (`I5`, `step5`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- After `b90`. -/
def k91 : List (XReg × Sym) :=
  [(.X20, V1), (.X22, V0), (.X23, .lit 1024), (.X21, .ptr 2 8), (.X24, .ptr 0 1112),
    (.X25, .ptr 0 88)]

/-- **Round 5's loop at entry `j`**. -/
structure I5 [Labels] (c : Cx) (m0 : MachineData) (fa fb G : Nat → EW) (j : Nat)
    (st : MachineData) : Prop where
  mid : Mid c m0 st
  x22 : st.regs.getXReg .X22 = (c.sl.getD 5 0).c0
  x20 : st.regs.getXReg .X20 = (c.sl.getD 5 0).c1
  x21 : (st.regs.getXReg .X21).toBitVec =
    rwA m0 + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 8
  x24 : (st.regs.getXReg .X24).toBitVec =
    fbA m0 + BitVec.ofNat 64 (1104 + 16 * j) + BitVec.ofInt 64 8
  x25 : (st.regs.getXReg .X25).toBitVec =
    fbA m0 + BitVec.ofNat 64 (80 + 16 * j) + BitVec.ofInt 64 8
  x23 : (st.regs.getXReg .X23).toBitVec.toNat = 1024 - 16 * j
  bufA : ElemsAt st.dmem (fbA m0 + BitVec.ofNat 64 80) fa 64
  bufB : ElemsAt st.dmem (fbA m0 + BitVec.ofNat 64 1104) fb 64
  rows : ElemsAt st.dmem (rwA m0) G 4096

end

public section

theorem adv16 (b : BitVec 64) (x : Nat) :
    BinOp.apply .add .W64 (b + BitVec.ofNat 64 x + BitVec.ofInt 64 8) (BitVec.ofNat 64 16) =
      b + BitVec.ofNat 64 (x + 16) + BitVec.ofInt 64 8 := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofInt 64 8) (BitVec.ofNat 64 16),
    ← BitVec.add_assoc (BitVec.ofNat 64 x), ← BitVec.ofNat_add]

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData}

/-- **A turn of round 5's loop**: entry `j` of row 0 folded. -/
theorem step5 (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (ok : Ok c.a m0) {fa fb : Nat → EW} {G : Nat → Nat → EW}
    (hG : ∀ j < 64, G (j + 1) = fun n ↦ if n = j then foldE (c.sl.getD 5 0) fa fb j else G j n)
    (j : Nat) (s : MachineState) (hj : j < 64) (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b91Offset))
    (hI : I5 c m0 fa fb (G j) j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦
      (j + 1 < 64 ∧ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b91Offset) ∧ I5 c m0 fa fb (G (j + 1)) (j + 1) s'.data) ∨
      (j + 1 = 64 ∧ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b93Offset) ∧
        I5 c m0 fa fb (G (j + 1)) (j + 1) s'.data)) s := by
  have hn := ok.nums
  have hN := hn.hN
  have hrS := hn.rS
  have hrW := hn.rW
  have hsl := spN_lt m0
  have hm0 : Match (Env.ofMachine s.data (bufR m0 j)) lo5S s.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨hI.x25, hI.x24, trivial⟩
  refine (stepL hp hmul ok b91_in_code (List.cons_ne_nil _ _) run_b91 (cx0 := .X22)
    (cx1 := .X20) (lo0 := .X19) (lo1 := .X26) (by decide) hj hpc hI.mid hm0 hI.bufA
    hI.bufB).bind fun s2 ⟨hpc2, hmid2, hso2, hprod, hlo0, hlo1, hreg2⟩ ↦ ?_
  have kp2 : ∀ r, calleeSaved r = true → r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25] →
      s2.data.regs.getXReg r = s.data.regs.getXReg r := fun r hr hm ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp (hreg2 _ _ hr rfl)
  have e21 := kp2 .X21 rfl (by simp)
  have e22 := kp2 .X22 rfl (by simp)
  have e20 := kp2 .X20 rfl (by simp)
  have e23 := kp2 .X23 rfl (by simp)
  have e24 := kp2 .X24 rfl (by simp)
  have e25 := kp2 .X25 rfl (by simp)
  have hm3 : Match (Env.ofMachine s2.data [(rwA m0 + BitVec.ofNat 64 (16 * j), 0 + 16)]) st5S
      s2.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by
        show (s2.data.regs.getXReg .X21).toBitVec = _
        rw [e21]; exact hI.x21, trivial⟩
  refine (stepS hp ok b92_in_code (List.cons_ne_nil _ _) run_b92 (lo0 := .X19) (lo1 := .X26)
    (C := 0) rfl rfl (o := 16 * j) (by omega) (by rw [hpc2, Nat.add_assoc]; rfl) hmid2 hm3).bind
    fun s3 ⟨hm3', hpc3, hmid3, hso3, hew3⟩ ↦ ?_
  have hreg3 := hm3'.regs
  have keepF : ∀ {o' : Nat} {f : Nat → EW}, o' + 1024 ≤ 2224 → 56 ≤ o' →
      ElemsAt s.data.dmem (fbA m0 + BitVec.ofNat 64 o') f 64 →
      ElemsAt s3.data.dmem (fbA m0 + BitVec.ofNat 64 o') f 64 := fun {o' f} ho1 ho2 h ↦ by
    have e := fbA_add hn (o := o') (by omega)
    refine ElemsAt.keepN (ElemsAt.keepN h hso2 (by rw [e]; omega) fun q hq ↦ ?_) hso3
      (by rw [e]; omega) fun q hq ↦ ?_
    · unfold MulR at hq
      rw [e]
      omega
    · rw [e]
      omega
  have hrows : ElemsAt s3.data.dmem (rwA m0) (G (j + 1)) 4096 := by
    rw [hG j hj]
    refine ElemsAt.setN (ElemsAt.keepN hI.rows hso2 (by omega) fun q hq ↦ ?_) (by omega)
      (m := j) (by omega) hso3 (fun q hq ↦ by omega) ?_
    · unfold MulR at hq
      omega
    · rw [hI.x22, hI.x20] at hprod
      rw [← foldE_eq hprod hlo0 hlo1]
      exact hew3
  have h23 : (s2.data.regs.getXReg .X23).toBitVec.toNat = 1024 - 16 * j := by
    rw [e23]; exact hI.x23
  have hI3 : I5 c m0 fa fb (G (j + 1)) (j + 1) s3.data := by
    refine ⟨hmid3, ?_, ?_, ?_, ?_, ?_, ?_, keepF (by decide) (by decide) hI.bufA,
      keepF (by decide) (by decide) hI.bufB, hrows⟩
    · apply UInt64.toBitVec_inj.mp
      rw [hreg3 .X22 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs, e22, hI.x22]
    · apply UInt64.toBitVec_inj.mp
      rw [hreg3 .X20 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs, e20, hI.x20]
    · rw [hreg3 .X21 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs, e21, hI.x21]
      rw [adv16, show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [hreg3 .X24 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs, e24, hI.x24]
      rw [adv16, show 1104 + 16 * j + 16 = 1104 + 16 * (j + 1) by omega]
    · rw [hreg3 .X25 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs, e25, hI.x25]
      rw [adv16, show 80 + 16 * j + 16 = 80 + 16 * (j + 1) by omega]
    · rw [hreg3 .X23 _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h23, BitVec.toNat_ofNat]; omega), h23,
        BitVec.toNat_ofNat]
      omega
  simp only [PcOk] at hpc3
  simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs] at hpc3
  rw [lblAt hp b91_in_code] at hpc3
  rcases Nat.lt_or_ge (j + 1) 64 with hl | hl
  · have hne : ((s2.data.regs.getXReg .X23).toBitVec == BitVec.ofNat 64 16) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      rw [h23, BitVec.toNat_ofNat] at this
      omega
    simp only [hne, Bool.not_false, ↓reduceIte] at hpc3
    exact .done _ (Or.inl ⟨hl, hpc3, hI3⟩)
  · have heq : ((s2.data.regs.getXReg .X23).toBitVec == BitVec.ofNat 64 16) = true := by
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [h23, BitVec.toNat_ofNat]
      omega
    simp only [heq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    exact .done _ (Or.inr ⟨by omega, by rw [hpc3, Nat.add_assoc]; rfl, hI3⟩)

/-- **Round 5**: row 0 from rows 0 and 1, `b88` to `b93`. -/
theorem round5 (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    {rows : Array (Array EW)} (hsz : rows.size = 64)
    (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b88Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 5 0) k88 s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (Fr c.sl rows 5) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b93Offset) ∧ Mid c m0 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (Fr c.sl rows 6) 4096) s := by
  have hsl : 5 < c.sl.size := by rw [hmid.sl_size]; decide
  rw [← F_zero] at hrw
  refine (copyRow hp hmemcpy ok (ks' := k89) (by decide) hsl rfl rfl b88_in_code
    (List.cons_ne_nil _ _) run_b88 (D := 80) ⟨by decide, by decide⟩ (v := .ptr 2 0) (by decide)
    (r := 0) (by decide) (evP2 0) hpc hmid hk hrw).bind
    fun s1 ⟨hpc1, hmid1, hk1, hrw1, hbA1, _⟩ ↦ ?_
  refine (copyRow hp hmemcpy ok (ks' := k90) (by decide) hsl rfl rfl b89_in_code
    (List.cons_ne_nil _ _) run_b89 (D := 1104) ⟨by decide, by decide⟩ (v := .ptr 2 1024)
    (by decide) (r := 1) (by decide) (evP2 1024) (hpc1.trans (by rw [Nat.add_assoc]; rfl))
    hmid1 hk1 hrw1).bind fun s2 ⟨hpc2, hmid2, hk2, hrw2, hbB2, hkeep2⟩ ↦ ?_
  have hbA2 := hkeep2 80 _ (Or.inl (by decide)) (by decide) hbA1
  refine (zeroBlock hp ok (ks' := k91) (by decide) hsl rfl rfl b90_in_code (List.cons_ne_nil _ _)
    run_b90 rfl (by decide) (hpc2.trans (by rw [Nat.add_assoc]; rfl)) hmid2 hk2).bind
    fun s3 ⟨hpc3, hmid3, hk3, hd3⟩ ↦ ?_
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b91Offset) := hpc3.trans (by rw [Nat.add_assoc]; rfl)
  have hI : I5 c m0 (fun z ↦ F c.sl rows 5 0 0 (64 * (2 * 0) + z))
      (fun z ↦ F c.sl rows 5 0 0 (64 * (2 * 0 + 1) + z)) (F c.sl rows 5 0 0) 0 s3.data := by
    refine ⟨hmid3, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hd3]; exact hbA2, by rw [hd3]; exact hbB2,
      by rw [hd3]; exact hrw2⟩
    · exact UInt64.toBitVec_inj.mp
        ((hk3.reg (memK (show inK .X22 V0 k91 = true by decide))).trans rfl)
    · exact UInt64.toBitVec_inj.mp
        ((hk3.reg (memK (show inK .X20 V1 k91 = true by decide))).trans rfl)
    · refine (hk3.reg (memK (show inK .X21 (.ptr 2 8) k91 = true by decide))).trans ?_
      show rwA m0 + BitVec.ofInt 64 8 = _
      rw [show 16 * 0 = 0 from rfl, NativeRustcVm.addr_add_zero]
    · refine (hk3.reg (memK (show inK .X24 (.ptr 0 1112) k91 = true by decide))).trans ?_
      show fbA m0 + BitVec.ofInt 64 1112 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 by decide, NativeRustcVm.addr_add_add,
        show BitVec.ofInt 64 1112 = BitVec.ofNat 64 (1104 + 16 * 0 + 8) by decide]
    · refine (hk3.reg (memK (show inK .X25 (.ptr 0 88) k91 = true by decide))).trans ?_
      show fbA m0 + BitVec.ofInt 64 88 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 by decide, NativeRustcVm.addr_add_add,
        show BitVec.ofInt 64 88 = BitVec.ofNat 64 (80 + 16 * 0 + 8) by decide]
    · rw [hk3.reg (memK (show inK .X23 (.lit 1024) k91 = true by decide))]
      rfl
  have hh : 0 < half 5 := by decide
  refine (loopN (P := fun j st ↦ I5 c m0 (fun z ↦ F c.sl rows 5 0 0 (64 * (2 * 0) + z))
      (fun z ↦ F c.sl rows 5 0 0 (64 * (2 * 0 + 1) + z)) (F c.sl rows 5 0 j) j st)
    (step5 hp hmul ok (G := fun j ↦ F c.sl rows 5 0 j) fun j hj ↦ by
      rw [F_succ_fun hsz hrow hsl hh hj, show 64 * 0 + j = j by omega])
    (by decide) hpc3' hI).mono fun s' ⟨hpc', hI'⟩ ↦ ⟨hpc', hI'.mid, ?_⟩
  have := hI'.rows
  rwa [F_row, show 0 + 1 = half 5 from rfl, F_half] at this

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
