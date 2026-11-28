module

public import NativeRustcVmX64.Ring.Coeff.Steps
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.RingCoefficients.Names

/-!
# `ring_coefficients`: a turn (x86-64)

`turn_body`: from the head of turn `p` (`b1`, the template `tH` with `hv p`), the row's 8 products,
`G`'s Frobenius images and the loop's test (`b17`): at its exit, back at the head when `p < 7`,
else at the epilogue (`b18`), in `tRn` with `bv p 17`.
-/

namespace NativeRustcVmX64.Ring.Coeff

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingCoefficients

@[expose] public section

variable [Host]

/-- The end of turn `p`. -/
def TEnd (m0 m : MachineData) (p k : Nat) (F : EW) (g G' : Nat → EW) (st : MachineState) : Prop :=
  st.pc = (if p = 7 then Host.addrOf (k + NativeRustcVmX64.Vm.RingCoefficients.b18Offset) else Labels.label NativeRustcVmX64.Vm.RingCoefficients.label_1) ∧
    Bnd (own m0 m) 176 NC (rsP m0 p) wrRow tRn (bvG m0 p F g G' 17) st.data

end

public section

variable [Host] {k : Nat} {m0 m : MachineData} {p : Nat}

omit [Host] in
theorem rbp_next (_hpl : p < 8) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 16) (BitVec.ofNat 64 (16 * p)) =
      BitVec.ofNat 64 (16 * (p + 1)) := by
  rw [NativeRustcVmX64.Field.Lin.add_apply, ← BitVec.ofNat_add]
  congr 1
  omega

omit [Host] in
theorem loop_test (hpl : p < 8) :
    (!CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 16) (BitVec.ofNat 64 (16 * p)))
      (BitVec.ofNat 64 128)) = !decide (p = 7) := by
  rw [rbp_next hpl]
  simp only [CmpOp.apply, low_W64]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

/-- The row's products. -/
theorem turn_rows (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (_hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (h : P m0) (hM : Mem m0 m) (hpl : p < 8) {F : EW} (hF : fE m0 p = F) {g G' : Nat → EW}
    (_hG : ∀ b, frobenius8 (g b) 1 = G' b) {st : MachineState}
    (hA : TAt m0 m p k 40 tH (hvG m0 p g) st) :
    Eventually (step1 Host.exe) (TAt m0 m p k 100 (tR 7) (bvG m0 p F g G' 8)) st := by
  refine Eventually.bind (mstep hp hmul h hM hpl b1_in_code (by simp [b1]) rfl (T' := (tR 0))
    (vals' := bvG m0 p F g G' 1) run_b1 rfl rfl rfl rfl (fun m' hM' ↦ by
      vtacR
      exacts [(fload h hM' hpl _).1.trans (by rw [hF]; rfl), (fload h hM' hpl _).2.trans (by rw [hF]; rfl)])
    (fun m' hM' ret mc hR ↦ (mulRes_of (x := F) (y := g 0) hR rfl rfl rfl rfl
      ((fload h hM' hpl ret).1.trans (by rw [hF])) ((fload h hM' hpl ret).2.trans (by rw [hF])) rfl rfl).trans rfl)
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (mstep hp hmul h hM hpl b2_in_code (by simp [b2]) rfl (T' := (tR 1))
    (vals' := bvG m0 p F g G' 2) run_b2 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (mulRes_of (x := F) (y := g 1) hR rfl rfl rfl rfl rfl rfl rfl rfl).trans rfl)
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (mstep hp hmul h hM hpl b3_in_code (by simp [b3]) rfl (T' := (tR 2))
    (vals' := bvG m0 p F g G' 3) run_b3 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (mulRes_of (x := F) (y := g 2) hR rfl rfl rfl rfl rfl rfl rfl rfl).trans rfl)
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (mstep hp hmul h hM hpl b4_in_code (by simp [b4]) rfl (T' := (tR 3))
    (vals' := bvG m0 p F g G' 4) run_b4 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (mulRes_of (x := F) (y := g 3) hR rfl rfl rfl rfl rfl rfl rfl rfl).trans rfl)
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (mstep hp hmul h hM hpl b5_in_code (by simp [b5]) rfl (T' := (tR 4))
    (vals' := bvG m0 p F g G' 5) run_b5 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (mulRes_of (x := F) (y := g 4) hR rfl rfl rfl rfl rfl rfl rfl rfl).trans rfl)
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (mstep hp hmul h hM hpl b6_in_code (by simp [b6]) rfl (T' := (tR 5))
    (vals' := bvG m0 p F g G' 6) run_b6 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (mulRes_of (x := F) (y := g 5) hR rfl rfl rfl rfl rfl rfl rfl rfl).trans rfl)
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (mstep hp hmul h hM hpl b7_in_code (by simp [b7]) rfl (T' := (tR 6))
    (vals' := bvG m0 p F g G' 7) run_b7 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (mulRes_of (x := F) (y := g 6) hR rfl rfl rfl rfl rfl rfl rfl rfl).trans rfl)
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (mstep hp hmul h hM hpl b8_in_code (by simp [b8]) rfl (T' := (tR 7))
    (vals' := bvG m0 p F g G' 8) run_b8 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (mulRes_of (x := F) (y := g 7) hR rfl rfl rfl rfl rfl rfl rfl rfl).trans rfl)
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ .done _ hA


/-- `G`'s Frobenius images. -/
theorem turn_frob (hp : Placed code k)
    (_hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (h : P m0) (hM : Mem m0 m) (hpl : p < 8) {F : EW} (_hF : fE m0 p = F) {g G' : Nat → EW}
    (hG : ∀ b, frobenius8 (g b) 1 = G' b) {st : MachineState}
    (hA : TAt m0 m p k 100 (tR 7) (bvG m0 p F g G' 8) st) :
    Eventually (step1 Host.exe) (TAt m0 m p k 148 (tR 8) (bvG m0 p F g G' 16)) st := by
  refine Eventually.bind (sstep hp hsq h hM hpl b9_in_code (by simp [b9]) rfl (T' := (tR 8))
    (vals' := bvG m0 p F g G' 9) run_b9 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (sqRes_of (x := g 0) hR rfl rfl rfl rfl rfl).trans (by rw [hG]; rfl))
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (sstep hp hsq h hM hpl b10_in_code (by simp [b10]) rfl (T' := (tR 8))
    (vals' := bvG m0 p F g G' 10) run_b10 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (sqRes_of (x := g 1) hR rfl rfl rfl rfl rfl).trans (by rw [hG]; rfl))
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (sstep hp hsq h hM hpl b11_in_code (by simp [b11]) rfl (T' := (tR 8))
    (vals' := bvG m0 p F g G' 11) run_b11 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (sqRes_of (x := g 2) hR rfl rfl rfl rfl rfl).trans (by rw [hG]; rfl))
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (sstep hp hsq h hM hpl b12_in_code (by simp [b12]) rfl (T' := (tR 8))
    (vals' := bvG m0 p F g G' 12) run_b12 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (sqRes_of (x := g 3) hR rfl rfl rfl rfl rfl).trans (by rw [hG]; rfl))
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (sstep hp hsq h hM hpl b13_in_code (by simp [b13]) rfl (T' := (tR 8))
    (vals' := bvG m0 p F g G' 13) run_b13 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (sqRes_of (x := g 4) hR rfl rfl rfl rfl rfl).trans (by rw [hG]; rfl))
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (sstep hp hsq h hM hpl b14_in_code (by simp [b14]) rfl (T' := (tR 8))
    (vals' := bvG m0 p F g G' 14) run_b14 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (sqRes_of (x := g 5) hR rfl rfl rfl rfl rfl).trans (by rw [hG]; rfl))
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (sstep hp hsq h hM hpl b15_in_code (by simp [b15]) rfl (T' := (tR 8))
    (vals' := bvG m0 p F g G' 15) run_b15 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (sqRes_of (x := g 6) hR rfl rfl rfl rfl rfl).trans (by rw [hG]; rfl))
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (sstep hp hsq h hM hpl b16_in_code (by simp [b16]) rfl (T' := (tR 8))
    (vals' := bvG m0 p F g G' 16) run_b16 rfl rfl rfl rfl (fun _ _ ↦ by vtacR)
    (fun _ _ ret mc hR ↦ (sqRes_of (x := g 7) hR rfl rfl rfl rfl rfl).trans (by rw [hG]; rfl))
    rfl rfl rfl rfl rfl (keys_ok rfl rfl rfl rfl) rfl hA) fun st hA ↦ .done _ hA


/-- The loop's test. -/
theorem turn_test (hp : Placed code k)
    (_hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (_hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (h : P m0) (hM : Mem m0 m) (hpl : p < 8) {F : EW} (_hF : fE m0 p = F) {g G' : Nat → EW}
    (_hG : ∀ b, frobenius8 (g b) 1 = G' b) {st : MachineState}
    (hA : TAt m0 m p k 148 (tR 8) (bvG m0 p F g G' 16) st) :
    Eventually (step1 Host.exe) (TEnd m0 m p k F g G') st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB⟩ := hA
  simp only at hpc hB
  subst hpc
  refine jumpStep (lay h hM hpl) hB (b17_in_code.trans hp.1 (by simp [b17])) run_b17
    (fun l hl ↦ by cases hl) rfl (T' := tRn) (vals' := bvG m0 p F g G' 17) rfl rfl
    (by
      vtacR
      exact rbp_next hpl) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) (fun _ _ _ _ h ↦ by cases h)
    fun st hpc hB _ ↦ .done _ ⟨?_, hB⟩
  simp only [PcOk] at hpc
  rw [hpc, show k + NativeRustcVmX64.Vm.RingCoefficients.b17Offset + b17.length = k + NativeRustcVmX64.Vm.RingCoefficients.b18Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.RingCoefficients.b17_next]]
  have hc : (SBool.not (SBool.cmp .eq .W64 (Sym.bin .add .W64 (.lit 16) (.var 8)) (.lit 128))).eval
      (envS (own m0 m) d 176 (rsP m0 p) (bvG m0 p F g G' 16) 0) = !decide (p = 7) := loop_test hpl
  rw [hc]
  by_cases h7 : p = 7
  · simp only [h7, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  · simp only [h7, decide_false, Bool.not_false, ite_true, ite_false]


/-- **A turn.** -/
theorem turn_body (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (h : P m0) (hM : Mem m0 m) (hpl : p < 8) {F : EW} (hF : fE m0 p = F) {g G' : Nat → EW}
    (hG : ∀ b, frobenius8 (g b) 1 = G' b) {st : MachineState}
    (hA : TAt m0 m p k 40 tH (hvG m0 p g) st) : Eventually (step1 Host.exe) (TEnd m0 m p k F g G') st :=
  Eventually.bind (turn_rows hp hmul hsq h hM hpl hF hG hA) fun _ hA ↦
    Eventually.bind (turn_frob hp hmul hsq h hM hpl hF hG hA) fun _ hA ↦
      turn_test hp hmul hsq h hM hpl hF hG hA

end

end NativeRustcVmX64.Ring.Coeff
