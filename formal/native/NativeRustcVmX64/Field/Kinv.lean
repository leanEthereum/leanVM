module

public import NativeRustcVmX64.Field.Kinv.Exec
public import NativeRustcVmX64.Field.Call
public import NativeRustcVmX64.Field.W32
public import NativeRustcVm.Field.Pow
public import NativeRustcVmX64.Code.Vm.Kinv.Names
public import NativeRustcVmX64.Code.Vm.KinvSq.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `kinv` on x86-64

`kinv_spec`: rustc's `kinv(a)`, placed anywhere in the program, given the contracts of `kmul` and
`kinv::sq`, returns `Model.kinv a`. It is straight-line: the Itoh-Tsujii chain of `field.rs`
(`chain`), each block setting up a call; RAX the running value, RBX, R14, R15 the kept powers
(`At`), the last `kinv::sq` a tail call. `chain_eq`: the chain is `Field.kinv`, the model's by
`Field.kinv_eq`.
-/

namespace NativeRustcVmX64.Field.Kinv

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.Kinv
open NativeVm.Model (kmul)

@[expose] public section

/-- The pushed registers' slots. -/
def slots : List (Reg64 × Nat) := [(.rbx, 8), (.r14, 16), (.r15, 24)]

/-- The callee-saved registers it uses. -/
def used : List Reg64 := [.rbx, .r14, .r15]

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

theorem hb (hp : Placed code k) {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j)
    (hne : ds ≠ []) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- The state before the block at `j`: RAX, RBX, R14, R15 hold `a0`, `abx`, `a14`, `a15`. -/
structure At (m0 m1 : MachineData) (k j : Nat) (a0 abx a14 a15 : UInt64) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + j)
  fr : Fr m0 m1 32 kinvStack 8 used st.data
  rax : reg st.data .rax = a0.toBitVec
  rbx : reg st.data .rbx = abx.toBitVec
  r14 : reg st.data .r14 = a14.toBitVec
  r15 : reg st.data .r15 = a15.toBitVec

omit [Host] in
theorem geo {m0 : MachineData} (hpre : KinvPre m0) : Geo m0 32 kinvStack :=
  ⟨hpre, by decide, by decide⟩

/-- **A block calling `kmul`**: RAX times the register `r1` the block moves to RSI. -/
theorem kmul_blk (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost) {m0 m1 : MachineData}
    (hpre : KinvPre m0) {ds : List Directive} {j : Nat} {S' : SState} {r1 : Reg64}
    (hk : ds.IsInfixAt Host.prog (k + j)) (hrun : exec ds (midS 32) = some (S', .call NativeRustcVmX64.Vm.Kmul.entryLabel))
    (hsp : S'.reg .rsp = some (.ptr 0 ((0 : Nat) : Int)))
    (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 8) (hkeep : keepsExcept used S' = true)
    (h0 : S'.reg .rdi = some (.reg .rax)) (h1 : S'.reg .rsi = some (.reg r1))
    (hbx : S'.reg .rbx = some (.reg .rbx)) (h14 : S'.reg .r14 = some (.reg .r14))
    (h15 : S'.reg .r15 = some (.reg .r15)) {a0 abx a14 a15 b : UInt64}
    (hb : ∀ d : MachineData, reg d .rbx = abx.toBitVec → reg d .r14 = a14.toBitVec →
      reg d .r15 = a15.toBitVec → reg d r1 = b.toBitVec) {st : MachineState}
    (hA : At m0 m1 k j a0 abx a14 a15 st) :
    Eventually (step1 Host.exe) (At m0 m1 k (j + ds.length) (kmul a0 b) abx a14 a15) st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hx0, hxbx, hx14, hx15⟩ := hA
  simp only at hpc hF hx0 hxbx hx14 hx15
  subst hpc
  refine block g hF (vars := fun _ ↦ 0) hk hrun hsp hw hkeep fun st1 hm1 hpc1 hF1 ↦ ?_
  have e0 : reg st1.data .rdi = a0.toBitVec := (hm1.regs .rdi _ h0).trans hx0
  have e1 : reg st1.data .rsi = b.toBitVec := (hm1.regs .rsi _ h1).trans (hb d hxbx hx14 hx15)
  have ebx : reg st1.data .rbx = abx.toBitVec := (hm1.regs .rbx _ hbx).trans hxbx
  have e14 : reg st1.data .r14 = a14.toBitVec := (hm1.regs .r14 _ h14).trans hx14
  have e15 : reg st1.data .r15 = a15.toBitVec := (hm1.regs .r15 _ h15).trans hx15
  refine call g hF1 hpc1 (S := kmulStack) (by decide) hkmul id (fun _ _ h ↦ h.2)
    fun st2 hpc2 hq hF2 ↦ .done _ ⟨by rw [hpc2, Nat.add_assoc], hF2, ?_, ?_, ?_, ?_⟩
  · rw [hq.1, e0, e1, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  · exact (hq.2.2.1 .rbx rfl).trans ebx
  · exact (hq.2.2.1 .r14 rfl).trans e14
  · exact (hq.2.2.1 .r15 rfl).trans e15

/-- **A block calling `kinv::sq`** with the count `c` in ESI, after moving RAX or nothing to each
of RBX, R14, R15. -/
theorem sq_blk (hsq : Spec (Labels.label NativeRustcVmX64.Vm.KinvSq.entryLabel) KinvSqPre KinvSqPost) {m0 m1 : MachineData}
    (hpre : KinvPre m0) {ds : List Directive} {j : Nat} {S' : SState} {c : Nat}
    {rbx' r14' r15' : Reg64} (hk : ds.IsInfixAt Host.prog (k + j))
    (hrun : exec ds (midS 32) = some (S', .call NativeRustcVmX64.Vm.KinvSq.entryLabel))
    (hsp : S'.reg .rsp = some (.ptr 0 ((0 : Nat) : Int)))
    (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 8) (hkeep : keepsExcept used S' = true)
    (h0 : S'.reg .rdi = some (.reg .rax)) (h1 : S'.reg .rsi = some (.lit c)) (hc : c < 2 ^ 32)
    (hc0 : c ≠ 0) (hbx : S'.reg .rbx = some (.reg rbx')) (h14 : S'.reg .r14 = some (.reg r14'))
    (h15 : S'.reg .r15 = some (.reg r15')) {a0 abx a14 a15 abx' a14' a15' : UInt64}
    (hv : ∀ d : MachineData, reg d .rax = a0.toBitVec → reg d .rbx = abx.toBitVec →
      reg d .r14 = a14.toBitVec → reg d .r15 = a15.toBitVec →
      reg d rbx' = abx'.toBitVec ∧ reg d r14' = a14'.toBitVec ∧ reg d r15' = a15'.toBitVec)
    {st : MachineState} (hA : At m0 m1 k j a0 abx a14 a15 st) :
    Eventually (step1 Host.exe) (At m0 m1 k (j + ds.length) (ksqIter c a0) abx' a14' a15') st := by
  have g := geo hpre
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hx0, hxbx, hx14, hx15⟩ := hA
  simp only at hpc hF hx0 hxbx hx14 hx15
  subst hpc
  obtain ⟨vbx, v14, v15⟩ := hv d hx0 hxbx hx14 hx15
  refine block g hF (vars := fun _ ↦ 0) hk hrun hsp hw hkeep fun st1 hm1 hpc1 hF1 ↦ ?_
  have e0 : reg st1.data .rdi = a0.toBitVec := (hm1.regs .rdi _ h0).trans hx0
  have hcnt : kinvSqCount st1.data = c := by
    rw [kinvSqCount, show reg st1.data .rsi = _ from hm1.regs .rsi _ h1]
    show (BitVec.ofNat 64 c).toNat % 2 ^ 32 = c
    rw [BitVec.toNat_ofNat]
    omega
  have ebx : reg st1.data .rbx = abx'.toBitVec := (hm1.regs .rbx _ hbx).trans vbx
  have e14 : reg st1.data .r14 = a14'.toBitVec := (hm1.regs .r14 _ h14).trans v14
  have e15 : reg st1.data .r15 = a15'.toBitVec := (hm1.regs .r15 _ h15).trans v15
  refine call g hF1 hpc1 (S := kinvSqStack) (by decide) hsq (fun h ↦ ⟨h, by rw [hcnt]; exact hc0⟩)
    (fun _ _ h ↦ h.2) fun st2 hpc2 hq hF2 ↦
      .done _ ⟨by rw [hpc2, Nat.add_assoc], hF2, ?_, ?_, ?_, ?_⟩
  · rw [hq.1, hcnt, e0, UInt64.ofBitVec_toBitVec]
  · exact (hq.2.2.1 .rbx rfl).trans ebx
  · exact (hq.2.2.1 .r14 rfl).trans e14
  · exact (hq.2.2.1 .r15 rfl).trans e15

/-- **`kinv` computes the inverse.** -/
theorem kinv_spec (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.KinvSq.entryLabel) KinvSqPre KinvSqPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.Kinv.entryLabel) KinvPre KinvPost := by
  intro m0 hpre
  have g := geo hpre
  rw [show Labels.label NativeRustcVmX64.Vm.Kinv.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Kinv.b0Offset) from hp.label NativeRustcVmX64.Vm.Kinv.entry_at]
  refine prologue (used := used) (slots := slots) (vars := fun _ ↦ 0) g
    (hb hp b0_in_code (List.cons_ne_nil _ _)) run_b0 (o := 0) rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) fun st1 hm1 hpc1 hF1 hsl ↦ ?_
  have e0 : reg st1.data .rdi = reg m0 .rdi := hm1.regs .rdi _ rfl
  have ebx : reg st1.data .rbx = reg m0 .rdi := hm1.regs .rbx _ rfl
  have e14 : reg st1.data .r14 = reg m0 .r14 := hm1.regs .r14 _ rfl
  have e15 : reg st1.data .r15 = reg m0 .r15 := hm1.regs .r15 _ rfl
  have hcnt : kinvSqCount st1.data = 1 := by
    rw [kinvSqCount, show reg st1.data .rsi = _ from hm1.regs .rsi (.lit 1) rfl]
    rfl
  refine call g hF1 hpc1 (S := kinvSqStack) (by decide) hsq (fun h ↦ ⟨h, by rw [hcnt]; decide⟩)
    (fun _ _ h ↦ h.2) fun st2 hpc2 hq hF2 ↦ ?_
  let a : UInt64 := .ofBitVec (reg m0 .rdi)
  have hA : At m0 st1.data k 7 (ksqIter 1 a) a (.ofBitVec (reg m0 .r14))
      (.ofBitVec (reg m0 .r15)) st2 :=
    ⟨hpc2, hF2, by rw [hq.1, hcnt, e0], (hq.2.2.1 .rbx rfl).trans ebx,
      (hq.2.2.1 .r14 rfl).trans e14, (hq.2.2.1 .r15 rfl).trans e15⟩
  refine Eventually.bind (kmul_blk hkmul hpre (hb hp b1_in_code (List.cons_ne_nil _ _)) run_b1 rfl
    (by decide) (by decide +kernel) rfl rfl rfl rfl rfl (fun _ h _ _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb hp b2_in_code (List.cons_ne_nil _ _)) run_b2 rfl
    (by decide) (by decide +kernel) rfl rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ h19 h20 h21 ↦ ⟨h19, h20, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb hp b3_in_code (List.cons_ne_nil _ _)) run_b3 rfl
    (by decide) (by decide +kernel) rfl rfl rfl rfl rfl (fun _ h _ _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb hp b4_in_code (List.cons_ne_nil _ _)) run_b4 rfl
    (by decide) (by decide +kernel) rfl rfl (by decide) (by decide) rfl rfl rfl
    (fun _ h0 _ h20 h21 ↦ ⟨h0, h20, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb hp b5_in_code (List.cons_ne_nil _ _)) run_b5 rfl
    (by decide) (by decide +kernel) rfl rfl rfl rfl rfl (fun _ h _ _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb hp b6_in_code (List.cons_ne_nil _ _)) run_b6 rfl
    (by decide) (by decide +kernel) rfl rfl (by decide) (by decide) rfl rfl rfl
    (fun _ h0 h19 _ h21 ↦ ⟨h19, h0, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb hp b7_in_code (List.cons_ne_nil _ _)) run_b7 rfl
    (by decide) (by decide +kernel) rfl rfl rfl rfl rfl (fun _ _ h _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb hp b8_in_code (List.cons_ne_nil _ _)) run_b8 rfl
    (by decide) (by decide +kernel) rfl rfl (by decide) (by decide) rfl rfl rfl
    (fun _ h0 h19 _ h21 ↦ ⟨h19, h0, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb hp b9_in_code (List.cons_ne_nil _ _)) run_b9 rfl
    (by decide) (by decide +kernel) rfl rfl rfl rfl rfl (fun _ _ h _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb hp b10_in_code (List.cons_ne_nil _ _)) run_b10 rfl
    (by decide) (by decide +kernel) rfl rfl (by decide) (by decide) rfl rfl rfl
    (fun _ h0 h19 h20 _ ↦ ⟨h19, h20, h0⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb hp b11_in_code (List.cons_ne_nil _ _)) run_b11
    rfl (by decide) (by decide +kernel) rfl rfl rfl rfl rfl (fun _ _ _ h ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb hp b12_in_code (List.cons_ne_nil _ _)) run_b12 rfl
    (by decide) (by decide +kernel) rfl rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ h19 h20 h21 ↦ ⟨h19, h20, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb hp b13_in_code (List.cons_ne_nil _ _)) run_b13
    rfl (by decide) (by decide +kernel) rfl rfl rfl rfl rfl (fun _ _ h _ ↦ h) hA) fun st hA ↦ ?_
  refine Eventually.bind (sq_blk hsq hpre (hb hp b14_in_code (List.cons_ne_nil _ _)) run_b14 rfl
    (by decide) (by decide +kernel) rfl rfl (by decide) (by decide) rfl rfl rfl
    (fun _ _ h19 h20 h21 ↦ ⟨h19, h20, h21⟩) hA) fun st hA ↦ ?_
  refine Eventually.bind (kmul_blk hkmul hpre (hb hp b15_in_code (List.cons_ne_nil _ _)) run_b15
    rfl (by decide) (by decide +kernel) rfl rfl rfl rfl rfl (fun _ h _ _ ↦ h) hA) fun st hA ↦ ?_
  -- The epilogue and the tail call.
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hF, hx0, -, -, -⟩ := hA
  simp only at hpc hF hx0
  subst hpc
  refine Eventually.bind (epilogue g hF hsl (vars := fun _ ↦ 0)
    (hb hp b16_in_code (List.cons_ne_nil _ _)) run_b16 (by decide +kernel) rfl)
    fun st3 ⟨hm3, hpc3, hso, hsv⟩ ↦ ?_
  simp only [PcOk] at hpc3
  have h3di : reg st3.data .rdi = reg d .rax := hm3.regs .rdi _ rfl
  have hcnt3 : kinvSqCount st3.data = 1 := by
    rw [kinvSqCount, show reg st3.data .rsi = _ from hm3.regs .rsi (.lit 1) rfl]
    rfl
  have hrsp3 : rspOf st3.data = rspOf m0 := (hm3.regs .rsp _ rfl).trans frame_top
  refine Eventually.mono (Spec.apply hsq hpc3
    ⟨StackOk.transfer (StackOk.mono g.ok (by decide)) hrsp3 hsv.2, by rw [hcnt3]; decide⟩)
    fun st ⟨hpc, hrsp, hq⟩ ↦ ⟨by rw [hpc, retOf_eq hrsp3 (g.ret_same hso)], by rw [hrsp, hrsp3],
      ?_, ?_, hsv.trans hq.2.2⟩
  · rw [hq.1, hcnt3, h3di, hx0, UInt64.ofBitVec_toBitVec, ← chain_eq]
    rfl
  · intro p hp'
    have hsb : stackBelow st3.data kinvSqStack = stackBelow m0 kinvSqStack := by
      simp only [stackBelow, hrsp3]
    rw [hq.2.1 p fun h ↦ hp' ?_, hso p hp']
    rw [hsb] at h
    rw [inRange_N g]
    have hs := g.sp
    have ht := g.top
    simp only [kinvStack, kinvSqStack, kmulStack] at hs ⊢
    have hb : (stackBelow m0 kinvSqStack).toNat = (rspOf m0).toNat - kinvSqStack :=
      stackBelow_toNat' (by simp only [kinvSqStack, kmulStack]; omega)
    rw [inRange_iff (by rw [hb]; simp only [kinvSqStack, kmulStack]; omega), hb] at h
    simp only [kinvSqStack, kmulStack] at h
    omega

end

end NativeRustcVmX64.Field.Kinv
