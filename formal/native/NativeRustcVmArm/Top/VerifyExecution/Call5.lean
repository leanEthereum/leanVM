module

public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Code.Vm.TablePhase.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Call6

/-!
# `verify_execution`: the table sumcheck

`b8` calls `table_phase` on the layout, the bus's result and the tables' evaluations; on `None`
`b9` fails, else the tables' column claims (`call5`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeVm.Math (tablePhase_roots)
open NativeRustcVm.Top (workAreaBytes walkTables walkPublic run_bind_eq)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open NativeRustcVm.Bus (BusWAt)
open LeanVM.Protocol.Verifier (memory0)

public section

variable [Host] {k : Nat}

/-- **The table sumcheck**, from `b8`: the function returns the walk's rest. -/
theorem call5 (hp : Placed code k)
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
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b8Offset)) {rate : Nat} (h21 : st.data.regs.X21.toNat = rate)
    (h22 : st.data.regs.X22 = m0.regs.X3) (h25 : st.data.regs.X25 = 123992)
    (h26 : st.data.regs.X26 = 4416) {P : Vector UInt64 4}
    (hP : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec P.toList) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L)
    (hvc : (L.placement memory0).variableCount ≤ 31) {bus : BusResultW}
    (hbus : BusWAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 4416) bus)
    (hcl : ClaimsWAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 123992) bus.claims)
    (hcs : bus.claims.size = 4)
    {ood : StackClaimW}
    (hood : OodAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkTables P L rate ood bus).run s)) st := by
  have hs := g.s
  have hwN := g.wN
  have hN : tablePhaseStack ≤ 18288 := by decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb8 hp) run_b8 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b8 (by simp)
  rw [after_eq run_b8] at hk
  obtain ⟨h1, hd1⟩ := h.block g hm1 hk.1 hk.2
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    have := hm1.regs .X0 _ rfl
    rw [← h.x20]; exact this
  have r1 : st1.data.regs.X1.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 0 := by
    have := hm1.regs .X1 _ rfl
    rw [eval_ptrW] at this; exact this
  have r2 : st1.data.regs.X2.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 4416 := by
    have := hm1.regs .X2 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X26.toBitVec = _
    rw [h26]; rfl
  have r3 : st1.data.regs.X3.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 112184 := by
    have := hm1.regs .X3 _ rfl
    rw [eval_ptrW] at this; exact this
  have k21 : st1.data.regs.X21 = st.data.regs.X21 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have k22 : st1.data.regs.X22 = st.data.regs.X22 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have k23 : st1.data.regs.X23 = 112184 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have k25 : st1.data.regs.X25 = st.data.regs.X25 := UInt64.toBitVec_inj.mp (hm1.regs .X25 _ rfl)
  rw [← hd1] at hts hL hbus hcl hood
  have hR := h1.rodataAt g hN
  have hws : ∀ {o n : Nat}, o + n ≤ 112184 →
      ∀ w ∈ [(⟨m0.regs.X0.toBitVec, tstateBytes⟩ : NativeRustcVm.Region),
        ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 112184, NativeRustcVm.Tables.tableEvalsBytes⟩],
      NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n w.addr w.size :=
    fun hn ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨g.apartWT (by omega) (by omega),
        g.apartW (o' := 112184) (n' := 11808) (by omega) (by omega) (by omega)⟩
  have hpre : TablePhasePre a s L bus st1.data := by
    unfold TablePhasePre TablesAt
    simp only [r0, r1, r2, r3]
    exact ⟨h1.stackOk g hN, hR.rcAt, hR, hts, h1.tstateOk g hN,
      h1.outOk g (o := 112184) (n := 11808) (by omega) (by omega) hN, g.rt,
      g.rodataApart (o := 112184) (n := 11808) (by omega) (by omega),
      h1.readIn g (o := 0) (n := 3912) (by omega) (by omega) hN (hws (by omega)),
      by rw [NativeRustcVm.addr_add_zero]; exact hL,
      h1.readIn g (o := 4416) (n := 107768) (by omega) (by omega) hN (hws (by omega)), hbus⟩
  refine call_then hpc1 (htp a s L bus) hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hres, hnext, hch, hsv⟩ := hpost
  simp only [r0, r3] at hres hnext hch
  have hsb := h1.sb g hN
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact wr_t g hq
    · exact wr_w g (o := 112184) (n := 11808) (by omega) (by omega) hq
    · exact wr_stk h1 g hN hq
  have hsW : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      (o + n ≤ 112184 ∨ 112184 + 11808 ≤ o) →
      NativeRustcVm.Layout.Same st1.data.dmem st2.data.dmem
        (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun ho hn hle ↦
    g.sameW hch ho hn fun q hq ↦ by
      rcases hq with hq | hq | hq
      · have := g.inT hq; have := g.tw; omega
      · have := g.inW (o := 112184) (n := 11808) (by omega) (by omega) hq; omega
      · have := h1.inStk g hN hq; have := g.wS; omega
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b8Offset + b8.length = k + NativeRustcVmArm.Vm.VerifyExecution.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b8_next]] at hpc2
  rw [walkTables, run_bind_eq]
  generalize hr : (tablePhase L bus).run s = r at hx0 hres hnext
  have bk := branch_keeps b9 (by simp)
  have ck := call_keeps b9 (by simp)
  rw [after_eq run_b9] at bk ck
  refine branch hp g (hb9 hp) run_b9 bk ck.1 h2 hpc2 (cbz_eval hx0) (fun hb ↦ ?_)
    fun hb st3 h3 hreg3 hd3 hpc3 ↦ ?_
  · cases r with
    | none => rfl
    | some _ => cases hb
  obtain ⟨⟨ev, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  have hev := hres _ _ rfl
  have hts' := hnext _ _ rfl
  have hsh := NativeRustcVm.Top.tablePhase_shape hL.heights_size hbus.forms_size hr
  have hroots' : s'.roots = s.roots := (tablePhase_roots L bus).keeps _ _ _ hr
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b9Offset + b9.length = k + NativeRustcVmArm.Vm.VerifyExecution.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b9_next]] at hpc3
  have reg : ∀ x : XReg, calleeSaved x = true →
      st3.data.regs.getXReg x = st1.data.regs.getXReg x := fun x hx ↦
    (hreg3 x).trans (hsv.1 x hx)
  have e21 : st3.data.regs.X21 = st1.data.regs.X21 := reg .X21 rfl
  have e22 : st3.data.regs.X22 = st1.data.regs.X22 := reg .X22 rfl
  have e23 : st3.data.regs.X23 = st1.data.regs.X23 := reg .X23 rfl
  have e25 : st3.data.regs.X25 = st1.data.regs.X25 := reg .X25 rfl
  have hL2 := NativeRustcVm.Tables.LayoutWAt.of_same (by rw [NativeRustcVm.addr_add_zero]; exact hL)
    (hsW (o := 0) (n := 3912) (by omega) (by omega) (by omega))
  rw [NativeRustcVm.addr_add_zero] at hL2
  exact call6 hp htc hpi hkp hrs hvso g h3 hpc3 (rate := rate) (by rw [e21, k21, h21])
    (by rw [e22, k22, h22]) (by rw [e23, k23]) (by rw [e25, k25, h25]) hP
    (hd3 ▸ hts') (by rw [hroots']; exact hroots) (hd3 ▸ hL2) hvc (hd3 ▸ hev) hsh
    (hd3 ▸ NativeRustcVm.Tables.ClaimsWAt.of_same hcl
      (hsW (o := 123992) (n := 97288) (by omega) (by omega) (by omega))) hcs
    (hd3 ▸ NativeRustcVm.Top.OodAt.of_same hood (hsW (o := 3912) (n := 504) (by omega) (by omega)
      (by omega)))

end

end NativeRustcVmArm.Top.VerifyExecution
