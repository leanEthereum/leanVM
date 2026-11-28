module

public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Keep

/-!
# `verify_execution`: the stacked opening

`b18` stores the `WhirW`'s address at SP and calls `verify_stacked_opening` on the layout, the
ring switch's output, the Keccak output, the column claims, the out-of-domain claim and the scales'
buffer; its result is the walk's, which `b19` and the epilogue return (`call10`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt EqClaimAt)
open NativeRustcVm.Ring (RingWAt)
open NativeRustcVm.KeccakGkr (KeccakOutAt)
open NativeRustcVm.Whir (whirBytes scalesBytes)

public section

variable [Host] {k : Nat}

/-- **The stacked opening**, from `b18`: the function returns its result. -/
theorem call10 (hp : Placed code k)
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b18Offset)) {rate : Nat} (h21 : st.data.regs.X21.toNat = rate)
    (h22 : st.data.regs.X22 = 221280) (h23 : st.data.regs.X23 = 222888)
    (h25 : st.data.regs.X25 = 123992) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L) {target : EW}
    {coeffs : Array EW}
    (hring : RingWAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 222888) target coeffs)
    {kp ks : Array EW}
    (hko : KeccakOutAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 221280) kp ks)
    {cs : Array ColumnClaimW}
    (hcl : ClaimsWAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 123992) cs)
    {ood : StackClaimW} (hood : OodAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 3912) ood)
    {R : Option (Unit × TState)}
    (hR : R = (verifyStackedOpening L.stackLog rate (#[ringSwitchClaim L target kp coeffs] ++
      cs.filterMap (·.onStack L) ++ #[ood])).run s) :
    Eventually (step1 Host.exe) (Done a m0 R) st := by
  have hs := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hF := frame_toNat g
  have hwN := g.wN
  have hwS := g.wS
  have htw := g.tw
  have htS := g.tS
  have haS := g.aS
  have haw := g.aw
  have hN : verifyStackedOpeningStack ≤ 18288 := by decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb18 hp) run_b18 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hm1' : Match (envOf m0 st.data) (after b18 callS) st1.data := by
    rw [after_eq run_b18]; exact hm1
  have hk := b18_keeps
  -- The store: the frame's first word.
  have hWr : ∀ q, Written (envOf m0 st.data) (after b18 callS) q →
      m0.regs.SP.toBitVec.toNat - 96 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toBitVec.toNat - 96 + 8 :=
    fun q hq ↦ by
      have := written_sub (r := 0) (lo := 0) (hi := 8) rfl
        (fun w hw ↦ ⟨(hk.2 w hw).1, Nat.zero_le _, (hk.2 w hw).2⟩) hq
      rw [hF] at this
      exact this
  have h1 : At m0 st1.data := h.blockW g hm1' hk.1 fun q hq ↦ by
    have := hWr q hq
    refine ⟨⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩, by omega⟩
    show InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 verifyExecutionStack) verifyExecutionStack q
    rw [inRange_below (show verifyExecutionStack ≤ _ from hs)]
    unfold verifyExecutionStack
    omega
  have hs1 : SameOutside st.data.dmem st1.data.dmem
      (Written (envOf m0 st.data) (after b18 callS)) :=
    hm1'.sameOutside hwf
  have hsW : ∀ {o n : Nat}, o < 495552 → o + n ≤ 495552 →
      NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem
        (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n :=
    fun ho hn ↦ g.sameW hs1 ho hn fun q hq ↦ by have := hWr q hq; omega
  -- The arguments.
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    have := hm1.regs .X0 _ rfl
    rw [← h.x20]; exact this
  have r1 : st1.data.regs.X1.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 0 := by
    have := hm1.regs .X1 _ rfl
    rw [eval_ptrW] at this; exact this
  have r2 : st1.data.regs.X2.toNat = rate := by
    have := hm1.regs .X2 _ rfl
    rw [← h21]; exact congrArg BitVec.toNat this
  have r3 : st1.data.regs.X3.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 222888 := by
    have := hm1.regs .X3 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X23.toBitVec = _
    rw [h23]; rfl
  have r4 : st1.data.regs.X4.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 221280 := by
    have := hm1.regs .X4 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X22.toBitVec = _
    rw [h22]; rfl
  have r5 : st1.data.regs.X5.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 123992 := by
    have := hm1.regs .X5 _ rfl
    rw [eval_addW] at this; refine this.trans ?_; show _ + st.data.regs.X25.toBitVec = _
    rw [h25]; rfl
  have r6 : st1.data.regs.X6.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 3912 := by
    have := hm1.regs .X6 _ rfl
    rw [eval_ptrW] at this; exact this
  have r7 : st1.data.regs.X7.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 223928 := by
    have := hm1.regs .X7 _ rfl
    rw [eval_ptrW] at this; exact this
  have hsp1 : st1.data.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 96 := h1.body.sp
  have harg :
      (whirStackArg st1.data 0).toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 226528 := by
    have hb := Match.bytesAt_write hm1' (r := 0) (o := 0) (n := 8) rfl (by omega)
      (v := .ptr 1 226528) fun i hi ↦ by rw [Nat.zero_add]; exact b18_arg i hi
    rw [eval_ptrW, ← wordBytes_byteOf (UInt64.ofBitVec _)] at hb
    unfold whirStackArg
    rw [show st1.data.regs.SP.toBitVec + BitVec.ofNat 64 (8 * 0) =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 96 + BitVec.ofNat 64 0 by rw [hsp1]]
    rw [NativeRustcVm.wordOf_of_wordAt hb]
    rfl
  -- The memory kept by the store.
  have hts1 : TStateAt st1.data.dmem m0.regs.X0.toBitVec a s :=
    hts.frame (hm1'.kept hwf) (fun q hq ↦ by
      have := hWr q hq
      refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
      · have := (inRange_nat g.tN).mp hi; omega
      · have := (inRange_nat g.aN).mp hi; omega) hs1
  have hL1 : LayoutWAt st1.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 0) L :=
    NativeRustcVm.Tables.LayoutWAt.of_same (by rw [NativeRustcVm.addr_add_zero]; exact hL)
      (hsW (o := 0) (n := 3912) (by omega) (by omega))
  have hring1 := NativeRustcVm.Top.RingWAt.of_same hring (hsW (by omega) (by decide))
  have hko1 := NativeRustcVm.Top.KeccakOutAt.of_same hko (hsW (by omega) (by decide))
  have hcl1 := NativeRustcVm.Tables.ClaimsWAt.of_same hcl (hsW (by omega) (by decide))
  obtain ⟨z, hz, hood1⟩ := NativeRustcVm.Top.OodAt.of_same hood (hsW (by omega) (by decide))
  -- The precondition.
  have hpre : VerifyStackedOpeningPre a s L target coeffs kp ks cs z ood.value st1.data := by
    have hin : ∀ {o n : Nat}, o + n ≤ 223928 →
        WhirIn st1.data (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n verifyStackedOpeningStack ∧
        NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n m0.regs.X0.toBitVec
          tstateBytes ∧
        NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n
          (m0.regs.X4.toBitVec + BitVec.ofNat 64 226528) whirBytes ∧
        NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n
          (m0.regs.X4.toBitVec + BitVec.ofNat 64 223928) scalesBytes := fun {o n} hn ↦
      ⟨⟨h1.readable g (by omega) (by omega), h1.offStack g (by omega) (by omega) hN⟩,
        g.apartWT (by omega) (by omega), g.apartW (by omega) (by omega) (by omega),
        g.apartW (by omega) (by omega) (by omega)⟩
    have ap : ∀ {o n o' n' : Nat}, o < 495552 → o' < 495552 → o + n ≤ o' ∨ o' + n' ≤ o →
        NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n
          (m0.regs.X4.toBitVec + BitVec.ofNat 64 o') n' := fun ho ho' hle ↦ g.apartW ho ho' hle
    unfold VerifyStackedOpeningPre vsoInputs NativeRustcVm.Whir.BasisAddrs.regions WhirT
    simp only [r0, r1, r3, r4, r5, r6, r7, harg, List.tail_cons, List.mem_cons, List.mem_nil_iff,
      or_false, forall_eq_or_imp, forall_eq, List.pairwise_cons, List.Pairwise.nil, and_true]
    have hT : StackOk st1.data verifyStackedOpeningStack := h1.stackOk g hN
    have hR : RodataAt st1.data verifyStackedOpeningStack := h1.rodataAt g hN
    refine ⟨⟨hT, hR.rcAt, hR, h1.tstateOk g hN, g.rt⟩, hts1, hroots, hL1, hring1, hko1,
      hcl1, hood1, h1.readableSP g, h1.spApartT g,
      h1.spApartW g (o := 223928) (n := 2600) (by omega) (by omega),
      h1.whirOut g (o := 226528) (n := 63200) (by omega) (by omega) hN,
      h1.whirOut g (o := 223928) (n := 2600) (by omega) (by omega) hN,
      ap (o := 226528) (n := 63200) (o' := 223928) (n' := 2600) (by omega) (by omega) (by omega),
      ⟨hin (o := 0) (n := 3912) (by omega), hin (o := 222888) (n := 1040) (by omega),
        hin (o := 221280) (n := 1608) (by omega), hin (o := 123992) (n := 97288) (by omega),
        hin (o := 3912) (n := 504) (by omega)⟩,
      ⟨ap (o := 0) (n := 3912) (o' := 222888) (n' := 1040) (by omega) (by omega) (by omega),
        ap (o := 0) (n := 3912) (o' := 221280) (n' := 1608) (by omega) (by omega) (by omega),
        ap (o := 0) (n := 3912) (o' := 123992) (n' := 97288) (by omega) (by omega) (by omega),
        ap (o := 0) (n := 3912) (o' := 3912) (n' := 504) (by omega) (by omega) (by omega)⟩,
      ⟨ap (o := 222888) (n := 1040) (o' := 221280) (n' := 1608) (by omega) (by omega) (by omega),
        ap (o := 222888) (n := 1040) (o' := 123992) (n' := 97288) (by omega) (by omega) (by omega),
        ap (o := 222888) (n := 1040) (o' := 3912) (n' := 504) (by omega) (by omega) (by omega)⟩,
      ⟨ap (o := 221280) (n := 1608) (o' := 123992) (n' := 97288) (by omega) (by omega) (by omega),
        ap (o := 221280) (n := 1608) (o' := 3912) (n' := 504) (by omega) (by omega) (by omega)⟩,
      ap (o := 123992) (n := 97288) (o' := 3912) (n' := 504) (by omega) (by omega) (by omega),
      fun _ h ↦ h.elim⟩
  refine call_then hpc1 (hvso a s L target coeffs kp ks cs z ood.value) hpre
    fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hnext, hch, hsv⟩ := hpost
  have hcl' : NativeRustcVm.Whir.stackClaims L target kp coeffs cs z ood.value =
      #[ringSwitchClaim L target kp coeffs] ++ cs.filterMap (·.onStack L) ++ #[ood] := by
    obtain ⟨w, v⟩ := ood
    cases hz
    rfl
  rw [r2, hcl', ← hR, r0] at hnext
  rw [hcl', r2, ← hR] at hx0
  have hsb := h1.sb g hN
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with ⟨r, hr, hq⟩ | hq
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [harg] at hq; exact wr_w g (o := 226528) (n := 63200) (by omega) (by omega) hq
      · rw [r7] at hq; exact wr_w g (o := 223928) (n := 2600) (by omega) (by omega) hq
      · rw [r0] at hq; exact wr_t g hq
    · exact wr_stk h1 g hN hq
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b18Offset + b18.length = k + NativeRustcVmArm.Vm.VerifyExecution.b19Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b18_next]] at hpc2
  obtain ⟨hwf2, hm2⟩ := h2.env g
  refine exec_at (hb19 hp) run_b19 hwf2 hpc2 hm2 fun st3 hm3 hpc3 ↦ ?_
  have hk3 := call_keeps b19 (by simp)
  rw [after_eq run_b19] at hk3
  obtain ⟨h3, hd3⟩ := h2.block g hm3 hk3.1 hk3.2
  have hx03 : st3.data.regs.X0 = st2.data.regs.X0 := UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl)
  simp only [PcOk, lbl_11 hp] at hpc3
  refine Eventually.mono (exitRet hp g h3 hpc3) fun st' ⟨e1, e2, e3, e4⟩ ↦
    ⟨e1, by rw [e2, hx03, hx0], by rw [e3, hd3]; exact hnext, fun q hq ↦ ?_, e4⟩
  rw [e3]
  exact h3.body.same q hq

end

end NativeRustcVmArm.Top.VerifyExecution
