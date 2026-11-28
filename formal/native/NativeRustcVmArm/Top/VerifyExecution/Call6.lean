module

public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Call7

/-!
# `verify_execution`: the tables' column claims

`b10` calls `table_column_claims` on the tables' evaluations and the column claims; on `None`
(the claims would not fit) `b11` fails, else the public input (`call6`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes walkPublic)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open NativeRustcVm.Tables (TableEvalsAt)
open LeanVM.Protocol.Verifier (opKeccak keccakOut memory0)

public section

variable [Host] {k : Nat}

/-- **The tables' column claims**, from `b10`: the function returns the walk's rest. -/
theorem call6 (hp : Placed code k)
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
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b10Offset)) {rate : Nat} (h21 : st.data.regs.X21.toNat = rate)
    (h22 : st.data.regs.X22 = m0.regs.X3) (h23 : st.data.regs.X23 = 112184)
    (h25 : st.data.regs.X25 = 123992) {P : Vector UInt64 4}
    (hP : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec P.toList) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L)
    (hvc : (L.placement memory0).variableCount ≤ 31) {ev : Array (Array EW × Array EW)}
    (hev : TableEvalsAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 112184) ev)
    (hsh : ev.size = 6 ∧ ∀ t < 6, (ev.getD t (#[], #[])).2.size = NativeVm.Math.Tables.widths.getD t 0 ∧
      (ev.getD t (#[], #[])).1.size = L.tableLogHeights.getD t 0)
    {cs : Array ColumnClaimW}
    (hcl : ClaimsWAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 123992) cs)
    (hcs : cs.size = 4)
    {ood : StackClaimW}
    (hood : OodAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 3912) ood) :
    Eventually (step1 Host.exe)
      (Done a m0 ((walkPublic P L rate ood (cs ++ tableColumnClaims ev) ev).run s)) st := by
  have hs := g.s
  have hwN := g.wN
  have hN : tableColumnClaimsStack ≤ 18288 := by decide
  have hsz := NativeRustcVm.Top.tableColumnClaims_size hsh.1 fun t ht ↦ (hsh.2 t ht).1
  have hfits : cs.size + (tableColumnClaims ev).size ≤ claimCap := by
    rw [hcs, hsz]; decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb10 hp) run_b10 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b10 (by simp)
  rw [after_eq run_b10] at hk
  obtain ⟨h1, hd1⟩ := h.block g hm1 hk.1 hk.2
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 112184 := by
    have := hm1.regs .X0 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X23.toBitVec = _
    rw [h23]; rfl
  have r1 : st1.data.regs.X1.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 123992 := by
    have := hm1.regs .X1 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X25.toBitVec = _
    rw [h25]; rfl
  have k21 : st1.data.regs.X21 = st.data.regs.X21 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have k22 : st1.data.regs.X22 = st.data.regs.X22 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have k23 : st1.data.regs.X23 = st.data.regs.X23 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have k25 : st1.data.regs.X25 = st.data.regs.X25 := UInt64.toBitVec_inj.mp (hm1.regs .X25 _ rfl)
  rw [← hd1] at hts hL hev hcl hood
  have hpre : TableColumnClaimsPre ev cs st1.data := by
    unfold TableColumnClaimsPre
    simp only [r0, r1]
    refine ⟨h1.stackOk g hN, h1.readIn g (o := 112184) (n := 11808) (by omega) (by omega) hN ?_,
      hev, h1.readable g (o := 123992) (n := 97288) (by omega) (by omega),
      h1.offStack g (o := 123992) (n := 97288) (by omega) (by omega) hN, hcl⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact g.apartW (o := 112184) (n := 11808) (o' := 123992) (n' := 97288) (by omega) (by omega)
      (by omega)
  refine call_then hpc1 (htc ev cs) hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hres, hch, hsv⟩ := hpost
  unfold Changes at hch
  simp only [r1] at hres hch
  have hsb := h1.sb g hN
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with hq | hq
    · exact wr_w g (o := 123992) (n := 97288) (by omega) (by omega) hq
    · exact wr_stk h1 g hN hq
  have hsW : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      (o + n ≤ 123992 ∨ 123992 + 97288 ≤ o) →
      NativeRustcVm.Layout.Same st1.data.dmem st2.data.dmem
        (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun ho hn hle ↦
    g.sameW hch ho hn fun q hq ↦ by
      rcases hq with hq | hq
      · have := g.inW (o := 123992) (n := 97288) (by omega) (by omega) hq; omega
      · have := h1.inStk g hN hq; have := g.wS; omega
  have hts2 : TStateAt st2.data.dmem m0.regs.X0.toBitVec a s :=
    hts.frame hsv.2.2 (fun q hq ↦ by
      rcases hq with hq | hq
      · exact g.notTA_w (o := 123992) (n := 97288) (by omega) (by omega) hq
      · exact h1.notTA_stk g hN hq) hch
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b10Offset + b10.length = k + NativeRustcVmArm.Vm.VerifyExecution.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b10_next]] at hpc2
  have bk := branch_keeps b11 (by simp)
  have ck := call_keeps b11 (by simp)
  rw [after_eq run_b11] at bk ck
  refine branch hp g (hb11 hp) run_b11 bk ck.1 h2 hpc2 (b := true)
    (by rw [cbz_eval hx0, decide_eq_true hfits]) (fun hb ↦ by cases hb)
    fun _ st3 h3 hreg3 hd3 hpc3 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b11Offset + b11.length = k + NativeRustcVmArm.Vm.VerifyExecution.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b11_next]] at hpc3
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
  have hk5 := hsh.2 5 (by omega)
  exact call7 hp hpi hkp hrs hvso g h3 hpc3 (rate := rate) (by rw [e21, k21, h21])
    (by rw [e22, k22, h22]) (by rw [e23, k23, h23]) (by rw [e25, k25, h25]) hP
    (hd3 ▸ hts2) hroots (hd3 ▸ hL2) hvc
    (hd3 ▸ NativeRustcVm.Top.TableEvalsAt.of_same hev
      (hsW (o := 112184) (n := 11808) (by omega) (by omega) (by omega))) hk5.2
    (by show keccakOut ≤ (ev.getD 5 (#[], #[])).2.size
        rw [hk5.1]; exact (Nat.le_add_right _ _).trans NativeRustcVm.Top.keccakOut_le)
    (hd3 ▸ hres hfits) (by rw [Array.size_append, hcs, hsz]; decide)
    (hd3 ▸ NativeRustcVm.Top.OodAt.of_same hood (hsW (o := 3912) (n := 504) (by omega) (by omega)
      (by omega)))

end

end NativeRustcVmArm.Top.VerifyExecution
