module

public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Code.Vm.TablePhase.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Call5

/-!
# `verify_execution`: the bus

`b6` calls `verify_bus_balance` on the layout, the bytecode, the bus's result and the column
claims; on `None` `b7` fails, else the table sumcheck (`call4`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeVm.Math (verifyBusBalance_roots)
open NativeRustcVm.Top (workAreaBytes walkBus walkTables run_bind_eq)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open LeanVM.Protocol.Verifier (memory0)

public section

variable [Host] {k : Nat}

/-- **The bus**, from `b6`: the function returns the walk's rest. -/
theorem call4 (hp : Placed code k)
    (hbb : ∀ a s L, Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L))
    (htp : ∀ a s layout bus, Spec (Labels.label NativeRustcVmArm.Vm.TablePhase.entryLabel) (TablePhasePre a s layout bus)
      (TablePhasePost a s layout bus))
    (htc : ∀ evals cs, Spec (Labels.label NativeRustcVmArm.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre evals cs)
      (TableColumnClaimsPost evals cs))
    (hpi : ∀ a s layout pub cs, Spec (Labels.label NativeRustcVmArm.Vm.PublicInputPhase.entryLabel)
      (PublicInputPhasePre a s layout pub cs) (PublicInputPhasePost a s layout pub cs))
    (hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmArm.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmArm.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b6Offset)) {rate : Nat} (h21 : st.data.regs.X21.toNat = rate)
    (h22 : st.data.regs.X22 = m0.regs.X3) (h23 : st.data.regs.X23 = m0.regs.X2)
    (h24 : st.data.regs.X24 = m0.regs.X1) {P : Vector UInt64 4}
    (hP : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec P.toList) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L)
    (hvc : (L.placement memory0).variableCount ≤ 31) (hBn : L.bytecode.size = m0.regs.X2.toNat)
    (hB : NativeRustcVm.WordsAt m0.dmem m0.regs.X1.toBitVec L.bytecode.toList)
    {ood : StackClaimW}
    (hood : OodAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkBus P L rate ood).run s)) st := by
  have hs := g.s
  have hwN := g.wN
  have hN : verifyBusBalanceStack ≤ 18288 := by decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb6 hp) run_b6 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b6 (by simp)
  rw [after_eq run_b6] at hk
  obtain ⟨h1, hd1⟩ := h.block g hm1 hk.1 hk.2
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    have := hm1.regs .X0 _ rfl
    rw [← h.x20]; exact this
  have r1 : st1.data.regs.X1.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 0 := by
    have := hm1.regs .X1 _ rfl
    rw [eval_ptrW] at this; exact this
  have r2 : st1.data.regs.X2 = m0.regs.X1 := by
    rw [← h24]; exact UInt64.toBitVec_inj.mp (hm1.regs .X2 _ rfl)
  have r3 : st1.data.regs.X3 = m0.regs.X2 := by
    rw [← h23]; exact UInt64.toBitVec_inj.mp (hm1.regs .X3 _ rfl)
  have r4 : st1.data.regs.X4.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 4416 := by
    have := hm1.regs .X4 _ rfl
    rw [eval_ptrW] at this; exact this
  have r5 : st1.data.regs.X5.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 123992 := by
    have := hm1.regs .X5 _ rfl
    rw [eval_ptrW] at this; exact this
  have k21 : st1.data.regs.X21 = st.data.regs.X21 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have k22 : st1.data.regs.X22 = st.data.regs.X22 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have k25 : st1.data.regs.X25 = 123992 := UInt64.toBitVec_inj.mp (hm1.regs .X25 _ rfl)
  have k26 : st1.data.regs.X26 = 4416 := UInt64.toBitVec_inj.mp (hm1.regs .X26 _ rfl)
  rw [← hd1] at hts hL hood
  have hR := h1.rodataAt g hN
  have hsb := h1.sb g hN
  have hbN := g.bN
  have hpre : VerifyBusBalancePre a s L st1.data := by
    unfold VerifyBusBalancePre InOk
    simp only [r0, r1, r2, r3, r4, r5]
    have hbt := g.bt
    have hbw := g.bw
    have hbS := g.bS
    have hwS := g.wS
    refine ⟨h1.stackOk g hN, hR.rcAt, hR, hts, h1.tstateOk g hN,
      by rw [NativeRustcVm.addr_add_zero]; exact hL,
      ⟨h1.readable g (o := 0) (n := 3912) (by omega) (by omega),
        h1.offStack g (o := 0) (n := 3912) (by omega) (by omega) hN⟩,
      g.apartWT (o := 0) (n := 3912) (by omega) (by omega), hBn,
      h1.bc g (by rw [Array.length_toList, hBn]) hB,
      ⟨h1.mapped g.mB, hbN⟩, fun hn ↦ ?_,
      h1.outOk g (o := 4416) (n := 107768) (by omega) (by omega) hN,
      g.rodataApart (o := 4416) (n := 107768) (by omega) (by omega),
      g.apartW (o := 4416) (n := 107768) (o' := 0) (n' := 3912) (by omega) (by omega) (by omega),
      fun hn ↦ ?_,
      h1.outOk g (o := 123992) (n := 97288) (by omega) (by omega) hN,
      g.rodataApart (o := 123992) (n := 97288) (by omega) (by omega),
      g.apartW (o := 123992) (n := 97288) (o' := 0) (n' := 3912) (by omega) (by omega) (by omega),
      fun hn ↦ ?_,
      g.apartW (o := 4416) (n := 107768) (o' := 123992) (n' := 97288) (by omega) (by omega)
        (by omega), g.rt, fun hn ↦ ?_⟩
    · have := hbS hn
      show _ ∨ _
      rw [hsb]; omega
    · have := hbw hn
      show _ ∨ _
      rw [g.wAddr (by omega), NativeRustcVm.Bus.busBytes_eq]; omega
    · have := hbw hn
      show _ ∨ _
      rw [g.wAddr (by omega), NativeRustcVm.Layout.claimsBytes_eq]; omega
    · have := hbt hn
      show _ ∨ _
      unfold tstateBytes; omega
  refine call_then hpc1 (hbb a s L) hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hres, hch, hsv⟩ := hpost
  simp only [r0, r4, r5] at hres hch
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with hq | hq | hq | hq
    · exact wr_t g hq
    · exact wr_w g (o := 4416) (n := 107768) (by omega) (by omega) hq
    · exact wr_w g (o := 123992) (n := 97288) (by omega) (by omega) hq
    · exact wr_stk h1 g hN hq
  have hsW : ∀ {o n : Nat}, o + n ≤ 4416 →
      NativeRustcVm.Layout.Same st1.data.dmem st2.data.dmem
        (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun hn ↦
    g.sameW hch (by omega) (by omega) fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · have := g.inT hq; have := g.tw; omega
      · have := g.inW (o := 4416) (n := 107768) (by omega) (by omega) hq; omega
      · have := g.inW (o := 123992) (n := 97288) (by omega) (by omega) hq; omega
      · have := h1.inStk g hN hq; have := g.wS; omega
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b6Offset + b6.length = k + NativeRustcVmArm.Vm.VerifyExecution.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b6_next]] at hpc2
  rw [walkBus, run_bind_eq]
  generalize hr : (verifyBusBalance L).run s = r at hx0 hres
  have bk := branch_keeps b7 (by simp)
  have ck := call_keeps b7 (by simp)
  rw [after_eq run_b7] at bk ck
  refine branch hp g (hb7 hp) run_b7 bk ck.1 h2 hpc2 (cbz_eval hx0) (fun hb ↦ ?_)
    fun hb st3 h3 hreg3 hd3 hpc3 ↦ ?_
  · cases r with
    | none => rfl
    | some _ => cases hb
  obtain ⟨⟨bus, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hts', hbus, hcl⟩ := hres _ _ rfl
  have hcs := (NativeRustcVm.Top.verifyBusBalance_claims L).gives _ _ _ hr
  have hroots' : s'.roots = s.roots := (verifyBusBalance_roots L).keeps _ _ _ hr
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b7Offset + b7.length = k + NativeRustcVmArm.Vm.VerifyExecution.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b7_next]] at hpc3
  have reg : ∀ x : XReg, calleeSaved x = true →
      st3.data.regs.getXReg x = st1.data.regs.getXReg x := fun x hx ↦
    (hreg3 x).trans (hsv.1 x hx)
  have e21 : st3.data.regs.X21 = st1.data.regs.X21 := reg .X21 rfl
  have e22 : st3.data.regs.X22 = st1.data.regs.X22 := reg .X22 rfl
  have e25 : st3.data.regs.X25 = st1.data.regs.X25 := reg .X25 rfl
  have e26 : st3.data.regs.X26 = st1.data.regs.X26 := reg .X26 rfl
  have hL2 := NativeRustcVm.Tables.LayoutWAt.of_same (by rw [NativeRustcVm.addr_add_zero]; exact hL)
    (hsW (o := 0) (n := 3912) (by omega))
  rw [NativeRustcVm.addr_add_zero] at hL2
  exact call5 hp htp htc hpi hkp hrs hvso g h3 hpc3 (rate := rate) (by rw [e21, k21, h21])
    (by rw [e22, k22, h22]) (by rw [e25, k25]) (by rw [e26, k26]) hP
    (hd3 ▸ hts') (by rw [hroots']; exact hroots) (hd3 ▸ hL2) hvc (hd3 ▸ hbus) (hd3 ▸ hcl) hcs
    (hd3 ▸ NativeRustcVm.Top.OodAt.of_same hood (hsW (o := 3912) (n := 504) (by omega)))

end

end NativeRustcVmArm.Top.VerifyExecution
