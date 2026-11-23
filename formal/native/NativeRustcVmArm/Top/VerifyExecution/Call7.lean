module

public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Call8

/-!
# `verify_execution`: the public input

`b12` calls `public_input_phase` on the layout, the public input and the column claims; on `None`
`b13` fails, else `KECCAK`'s validity (`call7`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeVm.Math (publicInputPhase_roots)
open NativeRustcVm.Top (workAreaBytes walkPublic walkKeccak run_bind_eq)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt claimCap)
open NativeRustcVm.Tables (TableEvalsAt)
open LeanVM.Protocol.Verifier (opKeccak keccakOut memory0)

public section

variable [Host] {k : Nat}

/-- **The public input**, from `b12`: the function returns the walk's rest. -/
theorem call7 (hp : Placed code k)
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
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b12Offset)) {rate : Nat} (h21 : st.data.regs.X21.toNat = rate)
    (h22 : st.data.regs.X22 = m0.regs.X3) (h23 : st.data.regs.X23 = 112184)
    (h25 : st.data.regs.X25 = 123992) {P : Vector UInt64 4}
    (hP : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec P.toList) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L)
    (hvc : (L.placement memory0).variableCount ≤ 31) {ev : Array (Array EW × Array EW)}
    (hev : TableEvalsAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 112184) ev)
    (hk1 : (ev.getD opKeccak (#[], #[])).1.size = L.tableLogHeights.getD opKeccak 0)
    (hk2 : keccakOut ≤ (ev.getD opKeccak (#[], #[])).2.size) {cs : Array ColumnClaimW}
    (hcl : ClaimsWAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 123992) cs)
    (hcs : cs.size + 2 < claimCap)
    {ood : StackClaimW}
    (hood : OodAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkPublic P L rate ood cs ev).run s)) st := by
  have hs := g.s
  have hwN := g.wN
  have hN : publicInputPhaseStack ≤ 18288 := by decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb12 hp) run_b12 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b12 (by simp)
  rw [after_eq run_b12] at hk
  obtain ⟨h1, hd1⟩ := h.block g hm1 hk.1 hk.2
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    have := hm1.regs .X0 _ rfl
    rw [← h.x20]; exact this
  have r1 : st1.data.regs.X1.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 0 := by
    have := hm1.regs .X1 _ rfl
    rw [eval_ptrW] at this; exact this
  have r2 : st1.data.regs.X2.toBitVec = m0.regs.X3.toBitVec := by
    have := hm1.regs .X2 _ rfl
    rw [← h22]; exact this
  have r3 : st1.data.regs.X3.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 123992 := by
    have := hm1.regs .X3 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X25.toBitVec = _
    rw [h25]; rfl
  have k21 : st1.data.regs.X21 = st.data.regs.X21 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have k23 : st1.data.regs.X23 = st.data.regs.X23 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have k25 : st1.data.regs.X25 = st.data.regs.X25 := UInt64.toBitVec_inj.mp (hm1.regs .X25 _ rfl)
  rw [← hd1] at hts hL hev hcl hood
  have hpre : PublicInputPhasePre a s L P cs st1.data := by
    unfold PublicInputPhasePre
    simp only [r0, r1, r2, r3]
    refine ⟨h1.stackOk g hN, (h1.rodataAt g hN).rcAt, hts, h1.tstateOk g hN,
      h1.outOk g (o := 123992) (n := 97288) (by omega) (by omega) hN, hcl,
      h1.readIn g (o := 0) (n := 3912) (by omega) (by omega) hN ?_,
      by rw [NativeRustcVm.addr_add_zero]; exact hL, hvc,
      h1.pubIn g (o := 123992) (n := NativeRustcVm.Layout.claimsBytes) (by omega) (by decide) hN,
      h1.pub g hP⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨g.apartWT (by omega) (by omega),
      g.apartW (o := 0) (n := 3912) (o' := 123992) (n' := 97288) (by omega) (by omega) (by omega)⟩
  refine call_then hpc1 (hpi a s L P cs) hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hres, hnext, hch, hsv⟩ := hpost
  simp only [r0, r3] at hres hnext hch
  have hsb := h1.sb g hN
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact wr_t g hq
    · exact wr_w g (o := 123992) (n := 97288) (by omega) (by omega) hq
    · exact wr_stk h1 g hN hq
  have hsW : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      (o + n ≤ 123992 ∨ 123992 + 97288 ≤ o) →
      NativeRustcVm.Layout.Same st1.data.dmem st2.data.dmem
        (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun ho hn hle ↦
    g.sameW hch ho hn fun q hq ↦ by
      rcases hq with hq | hq | hq
      · have := g.inT hq; have := g.tw; omega
      · have := g.inW (o := 123992) (n := 97288) (by omega) (by omega) hq; omega
      · have := h1.inStk g hN hq; have := g.wS; omega
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b12Offset + b12.length = k + NativeRustcVmArm.Vm.VerifyExecution.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b12_next]] at hpc2
  rw [walkPublic, run_bind_eq]
  generalize hr : (publicInputPhase L P).run s = r at hx0 hres hnext
  have hfits : cs.size + 2 ≤ claimCap := by omega
  have bk := branch_keeps b13 (by simp)
  have ck := call_keeps b13 (by simp)
  rw [after_eq run_b13] at bk ck
  refine branch hp g (hb13 hp) run_b13 bk ck.1 h2 hpc2 (cbz_eval hx0) (fun hb ↦ ?_)
    fun hb st3 h3 hreg3 hd3 hpc3 ↦ ?_
  · cases r with
    | none => rfl
    | some _ => simp [hfits] at hb
  have hb' : r.isSome = true := by simp at hb; exact hb.1
  obtain ⟨⟨pc, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb'
  have hcl' := hres _ _ rfl hfits
  have hts' := hnext _ _ rfl
  have hpc2' : pc.size = 2 := (NativeRustcVm.Top.publicInputPhase_size L P).gives _ _ _ hr
  have hroots' : s'.roots = s.roots := (publicInputPhase_roots L P).keeps _ _ _ hr
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b13Offset + b13.length = k + NativeRustcVmArm.Vm.VerifyExecution.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b13_next]] at hpc3
  have reg : ∀ x : XReg, calleeSaved x = true →
      st3.data.regs.getXReg x = st1.data.regs.getXReg x := fun x hx ↦
    (hreg3 x).trans (hsv.1 x hx)
  have e21 : st3.data.regs.X21 = st1.data.regs.X21 := reg .X21 rfl
  have e23 : st3.data.regs.X23 = st1.data.regs.X23 := reg .X23 rfl
  have e25 : st3.data.regs.X25 = st1.data.regs.X25 := reg .X25 rfl
  have hL2 := NativeRustcVm.Tables.LayoutWAt.of_same (by rw [NativeRustcVm.addr_add_zero]; exact hL)
    (hsW (o := 0) (n := 3912) (by omega) (by omega) (by omega))
  rw [NativeRustcVm.addr_add_zero] at hL2
  exact call8 hp hkp hrs hvso g h3 hpc3 (rate := rate) (by rw [e21, k21, h21])
    (by rw [e23, k23, h23]) (by rw [e25, k25, h25]) (hd3 ▸ hts') (by rw [hroots']; exact hroots)
    (hd3 ▸ hL2)
    (hd3 ▸ NativeRustcVm.Top.TableEvalsAt.of_same hev
      (hsW (o := 112184) (n := 11808) (by omega) (by omega) (by omega))) hk1 hk2
    (hd3 ▸ hcl') (by rw [Array.size_append, hpc2']; omega)
    (hd3 ▸ NativeRustcVm.Top.OodAt.of_same hood (hsW (o := 3912) (n := 504) (by omega) (by omega)
      (by omega)))

end

end NativeRustcVmArm.Top.VerifyExecution
