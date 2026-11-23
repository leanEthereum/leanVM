module

public import NativeRustcVmArm.Code.Vm.Kinv.Names
public import NativeRustcVmArm.Code.Vm.KinvSq.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Field.Kinv.Exec
public import NativeRustcVmArm.Field.Prologue
public import NativeRustcVmArm.Field.W32
public import NativeRustcVm.Field.Pow

/-!
# `kinv` on AArch64

`kinv_spec`: rustc's `kinv(a)`, placed anywhere in the program, given the contracts of `kmul` and
`kinv::sq`, returns `Model.kinv a`. It is straight-line: the Itoh-Tsujii chain of `field.rs`
(`chain`), each block setting up a call; X0 the running value, X19-X21 the kept powers (`At`), the
last `kinv::sq` a tail call. `chain_eq`: the chain is `Field.kinv`, the model's by `Field.kinv_eq`.
-/

namespace NativeRustcVmArm.Field.Kinv

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.Kinv
open NativeVm.Model (kmul)

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (XReg × Nat) := [(.X30, 0), (.X21, 8), (.X20, 16), (.X19, 24)]

/-- The callee-saved registers it uses. -/
def used : List XReg := [.X19, .X20, .X21]

/-- The Itoh-Tsujii chain, `t_k = a^(2^k - 1)`. -/
def chain (a : UInt64) : UInt64 :=
  let t2 := kmul (ksqIter 1 a) a
  let t3 := kmul (ksqIter 1 t2) a
  let t6 := kmul (ksqIter 3 t3) t3
  let t12 := kmul (ksqIter 6 t6) t6
  let t24 := kmul (ksqIter 12 t12) t12
  let t48 := kmul (ksqIter 24 t24) t24
  let t60 := kmul (ksqIter 12 t48) t12
  let t63 := kmul (ksqIter 3 t60) t3
  ksqIter 1 t63

end

public section

theorem repeat_comm {α : Type} (f : α → α) : ∀ (n : Nat) (a : α),
    Nat.repeat f n (f a) = f (Nat.repeat f n a)
  | 0, _ => rfl
  | n + 1, a => congrArg f (repeat_comm f n a)

/-- `Field.sq` is `ksqIter`. -/
theorem sq_bv : ∀ (n : Nat) (v : UInt64),
    NativeRustcVm.Field.sq v.toBitVec n = (ksqIter n v).toBitVec
  | 0, _ => rfl
  | n + 1, v => by
    rw [NativeRustcVm.Field.sq, NativeRustcVm.Field.ksquare, NativeRustcVm.Field.kmul_toBitVec,
      sq_bv n]
    show (Nat.repeat (fun v ↦ kmul v v) n (kmul v v)).toBitVec = _
    rw [repeat_comm]
    rfl

/-- **The chain is the inverse.** -/
theorem chain_eq (a : UInt64) : chain a = NativeVm.Model.kinv a := by
  apply UInt64.toBitVec_inj.mp
  have h := NativeRustcVm.Field.kinv_eq a.toBitVec
  simp only [NativeRustcVm.Field.kinv, sq_bv, NativeRustcVm.Field.kmul_toBitVec,
    UInt64.ofBitVec_toBitVec] at h
  rw [← h]
  rfl

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b0Offset) :=
  b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _)
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b1Offset) :=
  b1_in_code.trans hp.1 (by rw [b1]; exact List.cons_ne_nil _ _)
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b2Offset) :=
  b2_in_code.trans hp.1 (by rw [b2]; exact List.cons_ne_nil _ _)
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b3Offset) :=
  b3_in_code.trans hp.1 (by rw [b3]; exact List.cons_ne_nil _ _)
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b4Offset) :=
  b4_in_code.trans hp.1 (by rw [b4]; exact List.cons_ne_nil _ _)
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b5Offset) :=
  b5_in_code.trans hp.1 (by rw [b5]; exact List.cons_ne_nil _ _)
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b6Offset) :=
  b6_in_code.trans hp.1 (by rw [b6]; exact List.cons_ne_nil _ _)
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b7Offset) :=
  b7_in_code.trans hp.1 (by rw [b7]; exact List.cons_ne_nil _ _)
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b8Offset) :=
  b8_in_code.trans hp.1 (by rw [b8]; exact List.cons_ne_nil _ _)
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b9Offset) :=
  b9_in_code.trans hp.1 (by rw [b9]; exact List.cons_ne_nil _ _)
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b10Offset) :=
  b10_in_code.trans hp.1 (by rw [b10]; exact List.cons_ne_nil _ _)
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b11Offset) :=
  b11_in_code.trans hp.1 (by rw [b11]; exact List.cons_ne_nil _ _)
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b12Offset) :=
  b12_in_code.trans hp.1 (by rw [b12]; exact List.cons_ne_nil _ _)
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b13Offset) :=
  b13_in_code.trans hp.1 (by rw [b13]; exact List.cons_ne_nil _ _)
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b14Offset) :=
  b14_in_code.trans hp.1 (by rw [b14]; exact List.cons_ne_nil _ _)
theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b15Offset) :=
  b15_in_code.trans hp.1 (by rw [b15]; exact List.cons_ne_nil _ _)
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kinv.b16Offset) :=
  b16_in_code.trans hp.1 (by rw [b16]; exact List.cons_ne_nil _ _)

/-- The state before block `j`: X0, X19, X20, X21 hold `a0`, `a19`, `a20`, `a21`. -/
structure At (m0 m1 : MachineData) (k j : Nat) (a0 a19 a20 a21 : UInt64) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + j)
  fr : Fr m0 m1 32 kinvStack used st.data
  x0 : st.data.regs.X0 = a0
  x19 : st.data.regs.X19 = a19
  x20 : st.data.regs.X20 = a20
  x21 : st.data.regs.X21 = a21

omit [Host] in
theorem geo {m0 : MachineData} (hpre : KinvPre m0) : Geo m0 32 kinvStack :=
  ⟨hpre, rfl, by decide⟩

omit [Host] in
theorem keep [Labels] {d : MachineData} {S : SState} {st : MachineData}
    (hm : Match (Env.ofMachine d []) S st) {r r' : XReg} (h : S.reg r = some (.reg r')) :
    st.regs.getXReg r = d.regs.getXReg r' :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-- **A block calling `kmul`**: X0 times the register `r1` the block moves to X1. -/
theorem kmul_blk (hkmul : Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost) {m0 m1 : MachineData}
    (hpre : KinvPre m0) {ds : List Directive} {j : Nat} {S' : SState} {r1 : XReg}
    (hk : ds.IsInfixAt Host.prog (k + j)) (hrun : exec ds regS = some (S', .call NativeRustcVmArm.Vm.Kmul.entryLabel))
    (hmem : S'.mem = []) (hsp : S'.sp = .sp) (hkeep : keepsExcept used S' = true)
    (h0 : S'.reg .X0 = some (.reg .X0)) (h1 : S'.reg .X1 = some (.reg r1))
    (h19 : S'.reg .X19 = some (.reg .X19)) (h20 : S'.reg .X20 = some (.reg .X20))
    (h21 : S'.reg .X21 = some (.reg .X21)) {a0 a19 a20 a21 b : UInt64}
    (hb : ∀ d : MachineData, d.regs.X19 = a19 → d.regs.X20 = a20 → d.regs.X21 = a21 →
      d.regs.getXReg r1 = b) {st : MachineState} (hA : At m0 m1 k j a0 a19 a20 a21 st) :
    Eventually (step1 Host.exe) (At m0 m1 k (j + ds.length) (kmul a0 b) a19 a20 a21) st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hx0, hx19, hx20, hx21⟩ := hA
  simp only at hpc hF hx0 hx19 hx20 hx21
  subst hpc
  refine block hF hk hrun hmem hsp hkeep fun st1 hm1 hpc1 hF1 ↦ ?_
  have e0 : st1.data.regs.X0 = a0 := (keep hm1 h0).trans hx0
  have e1 : st1.data.regs.X1 = b := (keep hm1 h1).trans (hb d hx19 hx20 hx21)
  have e19 : st1.data.regs.X19 = a19 := (keep hm1 h19).trans hx19
  have e20 : st1.data.regs.X20 = a20 := (keep hm1 h20).trans hx20
  have e21 : st1.data.regs.X21 = a21 := (keep hm1 h21).trans hx21
  refine call g hF1 hpc1 (S := kmulStack) (by decide) hkmul id (fun _ _ h ↦ h.2)
    fun st2 hpc2 hq hF2 ↦ .done _ ⟨by rw [hpc2, Nat.add_assoc], hF2, ?_, ?_, ?_, ?_⟩
  · rw [hq.1, e0, e1]
  · exact (hq.2.2.1 .X19 rfl).trans e19
  · exact (hq.2.2.1 .X20 rfl).trans e20
  · exact (hq.2.2.1 .X21 rfl).trans e21

/-- **A block calling `kinv::sq`** with the count `c` in W1, after moving X0 or nothing to each of
X19, X20, X21. -/
theorem sq_blk (hsq : Spec (Labels.label NativeRustcVmArm.Vm.KinvSq.entryLabel) KinvSqPre KinvSqPost) {m0 m1 : MachineData}
    (hpre : KinvPre m0) {ds : List Directive} {j : Nat} {S' : SState} {c : Nat} {r19 r20 r21 : XReg}
    (hk : ds.IsInfixAt Host.prog (k + j)) (hrun : exec ds regS = some (S', .call NativeRustcVmArm.Vm.KinvSq.entryLabel))
    (hmem : S'.mem = []) (hsp : S'.sp = .sp) (hkeep : keepsExcept used S' = true)
    (h0 : S'.reg .X0 = some (.reg .X0)) (h1 : S'.reg .X1 = some (.lit c)) (hc : c < 2 ^ 32)
    (hc0 : c ≠ 0)
    (h19 : S'.reg .X19 = some (.reg r19)) (h20 : S'.reg .X20 = some (.reg r20))
    (h21 : S'.reg .X21 = some (.reg r21)) {a0 a19 a20 a21 a19' a20' a21' : UInt64}
    (hv : ∀ d : MachineData, d.regs.X0 = a0 → d.regs.X19 = a19 → d.regs.X20 = a20 →
      d.regs.X21 = a21 →
      d.regs.getXReg r19 = a19' ∧ d.regs.getXReg r20 = a20' ∧ d.regs.getXReg r21 = a21')
    {st : MachineState} (hA : At m0 m1 k j a0 a19 a20 a21 st) :
    Eventually (step1 Host.exe)
      (At m0 m1 k (j + ds.length) (ksqIter c a0) a19' a20' a21') st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hx0, hx19, hx20, hx21⟩ := hA
  simp only at hpc hF hx0 hx19 hx20 hx21
  subst hpc
  obtain ⟨v19, v20, v21⟩ := hv d hx0 hx19 hx20 hx21
  refine block hF hk hrun hmem hsp hkeep fun st1 hm1 hpc1 hF1 ↦ ?_
  have e0 : st1.data.regs.X0 = a0 := (keep hm1 h0).trans hx0
  have e1 : st1.data.regs.X1.toNat = c := by
    show (st1.data.regs.getXReg .X1).toBitVec.toNat = c
    rw [hm1.regs .X1 _ h1]
    show (BitVec.ofNat 64 c).toNat = c
    rw [BitVec.toNat_ofNat]
    omega
  have hcnt : kinvSqCount st1.data = c := by
    rw [kinvSqCount, e1]
    omega
  have e19 : st1.data.regs.X19 = a19' := (keep hm1 h19).trans v19
  have e20 : st1.data.regs.X20 = a20' := (keep hm1 h20).trans v20
  have e21 : st1.data.regs.X21 = a21' := (keep hm1 h21).trans v21
  refine call g hF1 hpc1 (S := kinvSqStack) (by decide) hsq (fun h ↦ ⟨h, by rw [hcnt]; exact hc0⟩)
    (fun _ _ h ↦ h.2) fun st2 hpc2 hq hF2 ↦
      .done _ ⟨by rw [hpc2, Nat.add_assoc], hF2, ?_, ?_, ?_, ?_⟩
  · rw [hq.1, hcnt, e0]
  · exact (hq.2.2.1 .X19 rfl).trans e19
  · exact (hq.2.2.1 .X20 rfl).trans e20
  · exact (hq.2.2.1 .X21 rfl).trans e21

/-- **`kinv` computes the inverse.** -/
theorem kinv_spec (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hsq : Spec (Labels.label NativeRustcVmArm.Vm.KinvSq.entryLabel) KinvSqPre KinvSqPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.Kinv.entryLabel) KinvPre KinvPost := by
  intro m0 hpre
  have g := geo hpre
  rw [show Labels.label NativeRustcVmArm.Vm.Kinv.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Kinv.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.Kinv.entryOffset) NativeRustcVmArm.Vm.Kinv.entry_at]
  refine prologue (used := used) (slots := slots) g (hb0 hp) run_b0 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) fun st1 hm1 hpc1 hF1 hsl ↦ ?_
  have e0 : st1.data.regs.X0 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
  have e19 : st1.data.regs.X19 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X19 (.reg .X0) rfl)
  have e20 : st1.data.regs.X20 = m0.regs.X20 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl)
  have e21 : st1.data.regs.X21 = m0.regs.X21 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have hcnt : kinvSqCount st1.data = 1 := by
    rw [kinvSqCount]
    show (st1.data.regs.getXReg .X1).toBitVec.toNat % 2 ^ 32 = 1
    rw [hm1.regs .X1 (.lit 1) rfl]
    rfl
  refine call g hF1 hpc1 (S := kinvSqStack) (by decide) hsq (fun h ↦ ⟨h, by rw [hcnt]; decide⟩)
    (fun _ _ h ↦ h.2) fun st2 hpc2 hq hF2 ↦ ?_
  have hA : At m0 st1.data k 6 (ksqIter 1 m0.regs.X0) m0.regs.X0 m0.regs.X20 m0.regs.X21 st2 :=
    ⟨hpc2, hF2, by rw [hq.1, hcnt, e0], (hq.2.2.1 .X19 rfl).trans e19,
      (hq.2.2.1 .X20 rfl).trans e20, (hq.2.2.1 .X21 rfl).trans e21⟩
  refine Eventually.bind (kmul_blk hkmul hpre (hb1 hp) run_b1 rfl rfl
    (by decide +kernel) rfl rfl rfl rfl rfl (fun _ h _ _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb2 hp) run_b2 rfl rfl (by decide +kernel) rfl rfl
    (by decide) (by decide) rfl rfl rfl (fun _ _ h19 h20 h21 ↦ ⟨h19, h20, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb3 hp) run_b3 rfl rfl
    (by decide +kernel) rfl rfl rfl rfl rfl (fun _ h _ _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb4 hp) run_b4 rfl rfl (by decide +kernel) rfl rfl
    (by decide) (by decide) rfl rfl rfl (fun _ h0 _ h20 h21 ↦ ⟨h0, h20, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb5 hp) run_b5 rfl rfl
    (by decide +kernel) rfl rfl rfl rfl rfl (fun _ h _ _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb6 hp) run_b6 rfl rfl (by decide +kernel) rfl rfl
    (by decide) (by decide) rfl rfl rfl (fun _ h0 h19 _ h21 ↦ ⟨h19, h0, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb7 hp) run_b7 rfl rfl
    (by decide +kernel) rfl rfl rfl rfl rfl (fun _ _ h _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb8 hp) run_b8 rfl rfl (by decide +kernel) rfl rfl
    (by decide) (by decide) rfl rfl rfl (fun _ h0 h19 _ h21 ↦ ⟨h19, h0, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb9 hp) run_b9 rfl rfl
    (by decide +kernel) rfl rfl rfl rfl rfl (fun _ _ h _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb10 hp) run_b10 rfl rfl (by decide +kernel) rfl rfl
    (by decide) (by decide) rfl rfl rfl (fun _ h0 h19 h20 _ ↦ ⟨h19, h20, h0⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb11 hp) run_b11 rfl rfl
    (by decide +kernel) rfl rfl rfl rfl rfl (fun _ _ _ h ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb12 hp) run_b12 rfl rfl (by decide +kernel) rfl rfl
    (by decide) (by decide) rfl rfl rfl (fun _ _ h19 h20 h21 ↦ ⟨h19, h20, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb13 hp) run_b13 rfl rfl
    (by decide +kernel) rfl rfl rfl rfl rfl (fun _ _ h _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb14 hp) run_b14 rfl rfl (by decide +kernel) rfl rfl
    (by decide) (by decide) rfl rfl rfl (fun _ _ h19 h20 h21 ↦ ⟨h19, h20, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb15 hp) run_b15 rfl rfl
    (by decide +kernel) rfl rfl rfl rfl rfl (fun _ h _ _ ↦ h) hA) fun st hA ↦ ?_
  -- The epilogue and the tail call.
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hx0, -, -, -⟩ := hA
  simp only at hpc hF hx0
  subst hpc
  refine Eventually.bind (epilogue_gen g hF hsl (hb16 hp) run_b16 (by decide +kernel) rfl rfl)
    fun st3 ⟨hpc3, hret, hso, hsv, hm3⟩ ↦ ?_
  simp only [PcOk] at hpc3
  have h30 : st3.data.regs.X0 = d.regs.X0 := UInt64.toBitVec_inj.mp (hm3.regs .X0 (.reg .X0) rfl)
  have hcnt3 : kinvSqCount st3.data = 1 := by
    rw [kinvSqCount]
    show (st3.data.regs.getXReg .X1).toBitVec.toNat % 2 ^ 32 = 1
    rw [hm3.regs .X1 (.lit 1) rfl]
    rfl
  have hsp3 : st3.data.regs.SP = m0.regs.SP := hsv.2.1
  refine Eventually.mono (Spec.apply hsq hpc3
    ⟨StackOk.of_saved (StackOk.mono (n := kinvSqStack) hpre (by decide)) hsv,
      by rw [hcnt3]; decide⟩) fun st ⟨hpc, hq⟩ ↦ ⟨by rw [hpc, hret], ?_, ?_, hsv.trans hq.2.2⟩
  · rw [hq.1, hcnt3, h30, hx0, ← chain_eq]
    rfl
  · intro p hp'
    have hsb : stackBelow st3.data kinvSqStack = stackBelow m0 kinvSqStack := by
      simp only [stackBelow, hsp3]
    rw [hq.2.1 p fun h ↦ hp' (inRange_mono (by decide) hpre.2.1 (hsb ▸ h)), hso p hp']

end

end NativeRustcVmArm.Field.Kinv
