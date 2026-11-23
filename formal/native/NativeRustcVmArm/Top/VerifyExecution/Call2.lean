module

public import NativeRustcVmArm.Code.Vm.CommitStack.Names
public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.ReadOod.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Code.Vm.TablePhase.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Call4

/-!
# `verify_execution`: the stack's commitment and its out-of-domain sample

`b2` reads the stack's log-size from the layout and calls `commit_stack`; on `None` `b3` fails,
else `b4` calls `read_ood` into the out-of-domain claim (`call3`); on `None` `b5` fails, else the
bus (`call2`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeVm.Math (readOod_roots)
open NativeRustcVm.Top (workAreaBytes walkCommit walkOod walkBus run_bind_eq commitStack_roots)
open NativeRustcVm.Layout (LayoutWAt OodAt)
open LeanVM.Protocol.Verifier (memory0)

public section

variable [Host] {k : Nat}

/-- The callees from the bus on. -/
structure Rest : Prop where
  hbb : ∀ a s L, Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
    (VerifyBusBalancePost a s L)
  htp : ∀ a s layout bus, Spec (Labels.label NativeRustcVmArm.Vm.TablePhase.entryLabel) (TablePhasePre a s layout bus)
    (TablePhasePost a s layout bus)
  htc : ∀ evals cs, Spec (Labels.label NativeRustcVmArm.Vm.TableColumnClaims.entryLabel) (TableColumnClaimsPre evals cs)
    (TableColumnClaimsPost evals cs)
  hpi : ∀ a s layout pub cs, Spec (Labels.label NativeRustcVmArm.Vm.PublicInputPhase.entryLabel)
    (PublicInputPhasePre a s layout pub cs) (PublicInputPhasePost a s layout pub cs)
  hkp : ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmArm.Vm.KeccakPhase.entryLabel)
    (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals)
  hrs : ∀ a s point, Spec (Labels.label NativeRustcVmArm.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
    (RingSwitchPost a s point)
  hvso : ∀ a s layout target coefficients point slices cs z value,
    Spec (Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.entryLabel)
      (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
      (VerifyStackedOpeningPost a s layout target coefficients point cs z value)

/-- **The out-of-domain sample**, from `b4`: the function returns the walk's rest. -/
theorem call3 (hp : Placed code k) (hR : Rest)
    (hro : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b4Offset)) {rate : Nat} (h21 : st.data.regs.X21.toNat = rate)
    (h22 : st.data.regs.X22 = m0.regs.X3) (h23 : st.data.regs.X23 = m0.regs.X2)
    (h24 : st.data.regs.X24 = m0.regs.X1) {L : LayoutW}
    (h25 : st.data.regs.X25.toNat = L.stackLog) {P : Vector UInt64 4}
    (hP : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec P.toList) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size ≤ 2)
    (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L) (hsl : L.stackLog ≤ 30)
    (hvc : (L.placement memory0).variableCount ≤ 31) (hBn : L.bytecode.size = m0.regs.X2.toNat)
    (hB : NativeRustcVm.WordsAt m0.dmem m0.regs.X1.toBitVec L.bytecode.toList) :
    Eventually (step1 Host.exe) (Done a m0 ((walkOod P L rate).run s)) st := by
  have hs := g.s
  have hwN := g.wN
  have hN : readOodStack ≤ 18288 := by decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb4 hp) run_b4 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b4 (by simp)
  rw [after_eq run_b4] at hk
  obtain ⟨h1, hd1⟩ := h.block g hm1 hk.1 hk.2
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    have := hm1.regs .X0 _ rfl
    rw [← h.x20]; exact this
  have r1 : st1.data.regs.X1 = st.data.regs.X25 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  have r2 : st1.data.regs.X2.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 3912 := by
    have := hm1.regs .X2 _ rfl
    rw [eval_ptrW] at this; exact this
  have k21 : st1.data.regs.X21 = st.data.regs.X21 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have k22 : st1.data.regs.X22 = st.data.regs.X22 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have k23 : st1.data.regs.X23 = st.data.regs.X23 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have k24 : st1.data.regs.X24 = st.data.regs.X24 := UInt64.toBitVec_inj.mp (hm1.regs .X24 _ rfl)
  rw [← hd1] at hts hL
  have hpre : ReadOodPre a s st1.data := by
    unfold ReadOodPre
    simp only [r0, r2]
    exact ⟨h1.stackOk g hN, (h1.rodataAt g hN).rcAt, hts, h1.tstateOk g hN,
      by rw [r1, h25]; exact hsl, h1.outOk g (o := 3912) (n := 504) (by omega) (by omega) hN⟩
  refine call_then hpc1 (hro a s) hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hres, hch, hsv⟩ := hpost
  simp only [r0, r1, r2, h25] at hres hch hx0
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact wr_w g (o := 3912) (n := 504) (by omega) (by omega) hq
    · exact wr_t g hq
    · exact wr_stk h1 g hN hq
  have hsW : ∀ {o n : Nat}, o + n ≤ 3912 →
      NativeRustcVm.Layout.Same st1.data.dmem st2.data.dmem
        (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun hn ↦
    g.sameW hch (by omega) (by omega) fun q hq ↦ by
      rcases hq with hq | hq | hq
      · have := g.inW (o := 3912) (n := 504) (by omega) (by omega) hq; omega
      · have := g.inT hq; have := g.tw; omega
      · have := h1.inStk g hN hq; have := g.wS; omega
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b4Offset + b4.length = k + NativeRustcVmArm.Vm.VerifyExecution.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b4_next]] at hpc2
  rw [walkOod, run_bind_eq]
  generalize hr : (readOod L.stackLog).run s = r at hx0 hres
  have bk := branch_keeps b5 (by simp)
  have ck := call_keeps b5 (by simp)
  rw [after_eq run_b5] at bk ck
  refine branch hp g (hb5 hp) run_b5 bk ck.1 h2 hpc2 (cbz_eval hx0) (fun hb ↦ ?_)
    fun hb st3 h3 hreg3 hd3 hpc3 ↦ ?_
  · cases r with
    | none => rfl
    | some _ => cases hb
  obtain ⟨⟨ood, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hood, hts'⟩ := hres _ _ rfl
  have hroots' : s'.roots = s.roots := (readOod_roots L.stackLog).keeps _ _ _ hr
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b5Offset + b5.length = k + NativeRustcVmArm.Vm.VerifyExecution.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b5_next]] at hpc3
  have reg : ∀ x : XReg, calleeSaved x = true →
      st3.data.regs.getXReg x = st1.data.regs.getXReg x := fun x hx ↦
    (hreg3 x).trans (hsv.1 x hx)
  have e21 : st3.data.regs.X21 = st1.data.regs.X21 := reg .X21 rfl
  have e22 : st3.data.regs.X22 = st1.data.regs.X22 := reg .X22 rfl
  have e23 : st3.data.regs.X23 = st1.data.regs.X23 := reg .X23 rfl
  have e24 : st3.data.regs.X24 = st1.data.regs.X24 := reg .X24 rfl
  have hL2 := NativeRustcVm.Tables.LayoutWAt.of_same (by rw [NativeRustcVm.addr_add_zero]; exact hL)
    (hsW (o := 0) (n := 3912) (by omega))
  rw [NativeRustcVm.addr_add_zero] at hL2
  exact call4 hp hR.hbb hR.htp hR.htc hR.hpi hR.hkp hR.hrs hR.hvso g h3 hpc3 (rate := rate)
    (by rw [e21, k21, h21]) (by rw [e22, k22, h22]) (by rw [e23, k23, h23]) (by rw [e24, k24, h24])
    hP (hd3 ▸ hts') (by rw [hroots']; exact hroots) (hd3 ▸ hL2) hvc hBn hB (hd3 ▸ hood)

/-- **The stack's commitment**, from `b2`: the function returns the walk's rest. -/
theorem call2 (hp : Placed code k) (hR : Rest)
    (hcs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s))
    (hro : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b2Offset)) {rate : Nat} (h1r : st.data.regs.X1.toNat = rate)
    (h22 : st.data.regs.X22 = m0.regs.X3) (h23 : st.data.regs.X23 = m0.regs.X2)
    (h24 : st.data.regs.X24 = m0.regs.X1) {P : Vector UInt64 4}
    (hP : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec P.toList) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size = 0)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L) (hsl : L.stackLog ≤ 30)
    (hvc : (L.placement memory0).variableCount ≤ 31) (hBn : L.bytecode.size = m0.regs.X2.toNat)
    (hB : NativeRustcVm.WordsAt m0.dmem m0.regs.X1.toBitVec L.bytecode.toList) :
    Eventually (step1 Host.exe) (Done a m0 ((walkCommit P L rate).run s)) st := by
  have hs := g.s
  have hwN := g.wN
  have hN : commitStackStack ≤ 18288 := by decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb2 hp) run_b2 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b2 (by simp)
  rw [after_eq run_b2] at hk
  obtain ⟨h1, hd1⟩ := h.block g hm1 hk.1 hk.2
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    have := hm1.regs .X0 _ rfl
    rw [← h.x20]; exact this
  have hsw : NativeRustcVm.WordAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 16)
      L.stackLog.toUInt64 := hL.stack_log
  have r1 : st1.data.regs.X1 = L.stackLog.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X1 _ rfl).trans (load_wordAt (r := 1) hsw))
  have r25 : st1.data.regs.X25 = L.stackLog.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X25 _ rfl).trans (load_wordAt (r := 1) hsw))
  have r2 : st1.data.regs.X2 = st.data.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X2 _ rfl)
  have k21 : st1.data.regs.X21 = st.data.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have k22 : st1.data.regs.X22 = st.data.regs.X22 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have k23 : st1.data.regs.X23 = st.data.regs.X23 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have k24 : st1.data.regs.X24 = st.data.regs.X24 := UInt64.toBitVec_inj.mp (hm1.regs .X24 _ rfl)
  have hslN : L.stackLog.toUInt64.toNat = L.stackLog := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  rw [← hd1] at hts hL
  have hRo := h1.rodataAt g hN
  have hpre : CommitStackPre a s st1.data := by
    unfold CommitStackPre
    simp only [r0]
    exact ⟨h1.stackOk g hN, hRo.rcAt, hRo, hts, h1.tstateOk g hN, by rw [hroots]; decide⟩
  refine call_then hpc1 (hcs a s) hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hnext, hch, hsv⟩ := hpost
  simp only [r0, r1, r2, hslN, h1r] at hx0 hnext hch
  have hN' : commitStackStack ≤ 18288 := hN
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with hq | hq
    · exact wr_t g hq
    · exact wr_stk h1 g hN' hq
  have hsW : NativeRustcVm.Layout.Same st1.data.dmem st2.data.dmem
      (m0.regs.X4.toBitVec + BitVec.ofNat 64 0) 3912 :=
    g.sameW hch (by omega) (by omega) fun q hq ↦ by
      rcases hq with hq | hq
      · have := g.inT hq; have := g.tw; omega
      · have := h1.inStk g hN' hq; have := g.wS; omega
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b2Offset + b2.length = k + NativeRustcVmArm.Vm.VerifyExecution.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b2_next]] at hpc2
  rw [walkCommit, run_bind_eq]
  generalize hr : (commitStack L.stackLog rate).run s = r at hx0 hnext
  have bk := branch_keeps b3 (by simp)
  have ck := call_keeps b3 (by simp)
  rw [after_eq run_b3] at bk ck
  refine branch hp g (hb3 hp) run_b3 bk ck.1 h2 hpc2 (cbz_eval hx0) (fun hb ↦ ?_)
    fun hb st3 h3 hreg3 hd3 hpc3 ↦ ?_
  · cases r with
    | none => rfl
    | some _ => cases hb
  obtain ⟨⟨u, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  have hts' := hnext _ _ rfl
  have hroots' : s'.roots.size ≤ s.roots.size + 1 :=
    (commitStack_roots L.stackLog rate).grows _ _ _ hr
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b3Offset + b3.length = k + NativeRustcVmArm.Vm.VerifyExecution.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b3_next]] at hpc3
  have reg : ∀ x : XReg, calleeSaved x = true →
      st3.data.regs.getXReg x = st1.data.regs.getXReg x := fun x hx ↦
    (hreg3 x).trans (hsv.1 x hx)
  have e21 : st3.data.regs.X21 = st1.data.regs.X21 := reg .X21 rfl
  have e22 : st3.data.regs.X22 = st1.data.regs.X22 := reg .X22 rfl
  have e23 : st3.data.regs.X23 = st1.data.regs.X23 := reg .X23 rfl
  have e24 : st3.data.regs.X24 = st1.data.regs.X24 := reg .X24 rfl
  have e25 : st3.data.regs.X25 = st1.data.regs.X25 := reg .X25 rfl
  have hL2 := NativeRustcVm.Tables.LayoutWAt.of_same (by rw [NativeRustcVm.addr_add_zero]; exact hL)
    hsW
  rw [NativeRustcVm.addr_add_zero] at hL2
  exact call3 hp hR hro g h3 hpc3 (rate := rate) (by rw [e21, k21, h1r])
    (by rw [e22, k22, h22]) (by rw [e23, k23, h23]) (by rw [e24, k24, h24])
    (by rw [e25, r25, hslN]) hP (hd3 ▸ hts') (show s'.roots.size ≤ 2 by omega) (hd3 ▸ hL2) hsl hvc
    hBn hB

end

end NativeRustcVmArm.Top.VerifyExecution
