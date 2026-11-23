module

public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Top.VerifyExecution.Call10

/-!
# `verify_execution`: ring switching

`b16` calls `ring_switch` on the Keccak output's slices and the ring switch's output; on `None`
`b17` fails, else the stacked opening (`call9`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model NativeVm.Math
open NativeRustcVm.Top (workAreaBytes walkRing run_bind_eq ringSwitch_point)
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt OodAt)
open NativeRustcVm.KeccakGkr (KeccakOutAt)
open NativeRustcVm.Ring (coeffCount)

public section

variable [Host] {k : Nat}

/-- **Ring switching**, from `b16`: the function returns the walk's rest. -/
theorem call9 (hp : Placed code k)
    (hrs : ∀ a s point, Spec (Labels.label NativeRustcVmArm.Vm.RingSwitch.entryLabel) (RingSwitchPre a s)
      (RingSwitchPost a s point))
    (hvso : ∀ a s layout target coefficients point slices cs z value,
      Spec (Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.entryLabel)
        (VerifyStackedOpeningPre a s layout target coefficients point slices cs z value)
        (VerifyStackedOpeningPost a s layout target coefficients point cs z value))
    {a : DecArea} {m0 : MachineData} (g : Geo a m0) {st : MachineState} (h : At m0 st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyExecution.b16Offset)) {rate : Nat} (h21 : st.data.regs.X21.toNat = rate)
    (h22 : st.data.regs.X22 = 221280) (h25 : st.data.regs.X25 = 123992) {s : TState}
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s) (hroots : s.roots.size ≤ 2)
    {L : LayoutW} (hL : LayoutWAt st.data.dmem m0.regs.X4.toBitVec L) {kp ks : Array EW}
    (hko : KeccakOutAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 221280) kp ks)
    {cs : Array ColumnClaimW}
    (hcl : ClaimsWAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 123992) cs)
    {ood : StackClaimW}
    (hood : OodAt st.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 3912) ood) :
    Eventually (step1 Host.exe) (Done a m0 ((walkRing L rate ood cs kp ks).run s)) st := by
  have hs := g.s
  have hwN := g.wN
  have hN : ringSwitchStack ≤ 18288 := by decide
  obtain ⟨hwf, hm⟩ := h.env g
  refine exec_at (hb16 hp) run_b16 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hk := call_keeps b16 (by simp)
  rw [after_eq run_b16] at hk
  obtain ⟨h1, hd1⟩ := h.block g hm1 hk.1 hk.2
  have r0 : st1.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
    have := hm1.regs .X0 _ rfl
    rw [← h.x20]; exact this
  have r1 : st1.data.regs.X1.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 221864 := by
    have := hm1.regs .X1 _ rfl
    rw [eval_ptrW] at this; exact this
  have r2 : st1.data.regs.X2.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 222888 := by
    have := hm1.regs .X2 _ rfl
    rw [eval_ptrW] at this; exact this
  have k21 : st1.data.regs.X21 = st.data.regs.X21 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have k22 : st1.data.regs.X22 = st.data.regs.X22 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have k23 : st1.data.regs.X23 = 222888 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have k25 : st1.data.regs.X25 = st.data.regs.X25 := UInt64.toBitVec_inj.mp (hm1.regs .X25 _ rfl)
  rw [← hd1] at hts hL hko hcl hood
  -- The slices.
  obtain ⟨hkp, hks, hksE⟩ := hko
  have hsl : NativeRustcVm.EWsAt st1.data.dmem (m0.regs.X4.toBitVec + BitVec.ofNat 64 221864)
      ks.toList := by
    have e : m0.regs.X4.toBitVec + BitVec.ofNat 64 221864 =
        m0.regs.X4.toBitVec + BitVec.ofNat 64 221280 + BitVec.ofNat 64 584 := by
      rw [NativeRustcVm.addr_add_add]
    rw [e]; exact hksE
  have harr : arr st1.data st1.data.regs.X1 coeffCount = ks := by
    unfold arr
    rw [r1, show coeffCount = ks.toList.length by simp [hks]; rfl, NativeRustcVm.ewsOf_of_ewsAt hsl]
  have hpre : RingSwitchPre a s st1.data := by
    unfold RingSwitchPre ArrOk
    simp only [r0, r1, r2]
    refine ⟨h1.stackOk g hN, (h1.rodataAt g hN).rcAt, hts, h1.tstateOk g hN,
      h1.outOk g (o := 222888) (n := 1040) (by omega) (by omega) hN,
      ⟨h1.readable g (o := 221864) (n := 1024) (by omega) (by omega),
        h1.offStack g (o := 221864) (n := 1024) (by omega) (by omega) hN⟩,
      g.apartWT (o := 221864) (n := 1024) (by omega) (by omega),
      g.apartW (o := 221864) (n := 1024) (o' := 222888) (n' := 1040) (by omega) (by omega)
        (by omega)⟩
  refine call_then hpc1 (hrs a s kp) hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hx0, hres, hch, hsv⟩ := hpost
  rw [harr] at hx0 hres
  have hsb := h1.sb g hN
  have h2 : At m0 st2.data := h1.call g hch hsv fun q hq ↦ by
    rcases hq with hq | hq | hq
    · rw [r2] at hq; exact wr_w g (o := 222888) (n := 1040) (by omega) (by omega) hq
    · rw [r0] at hq; exact wr_t g hq
    · exact wr_stk h1 g hN hq
  have hsW : ∀ {o n : Nat}, o < 495552 → o + n ≤ 222888 →
      NativeRustcVm.Layout.Same st1.data.dmem st2.data.dmem
        (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun ho hn ↦
    g.sameW hch ho (by omega) fun q hq ↦ by
      rcases hq with hq | hq | hq
      · rw [r2] at hq; have := g.inW (o := 222888) (n := 1040) (by omega) (by omega) hq; omega
      · rw [r0] at hq; have := g.inT hq; have := g.tw; omega
      · have := h1.inStk g hN hq; have := g.wS; omega
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b16Offset + b16.length = k + NativeRustcVmArm.Vm.VerifyExecution.b17Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b16_next]] at hpc2
  rw [walkRing, run_bind_eq]
  generalize hr : (ringSwitch kp ks).run s = r at hx0 hres
  have bk := branch_keeps b17 (by simp)
  have ck := call_keeps b17 (by simp)
  rw [after_eq run_b17] at bk ck
  refine branch hp g (hb17 hp) run_b17 bk ck.1 h2 hpc2 (cbz_eval hx0) (fun hb ↦ ?_)
    fun hb st3 h3 hreg3 hd3 hpc3 ↦ ?_
  · cases r with
    | none => rfl
    | some _ => cases hb
  obtain ⟨⟨⟨target, rp, coeffs⟩, s'⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨hring, hts'⟩ := hres _ _ rfl
  have hrp : rp = kp := (ringSwitch_point kp ks).gives _ _ _ hr
  have hroots' : s'.roots = s.roots := (NativeRustcVm.Top.ringSwitch_roots kp ks).keeps _ _ _ hr
  subst hrp
  rw [show k + NativeRustcVmArm.Vm.VerifyExecution.b17Offset + b17.length = k + NativeRustcVmArm.Vm.VerifyExecution.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyExecution.b17_next]] at hpc3
  have reg : ∀ x : XReg, calleeSaved x = true →
      st3.data.regs.getXReg x = st1.data.regs.getXReg x := fun x hx ↦
    (hreg3 x).trans (hsv.1 x hx)
  have e21 : st3.data.regs.X21 = st1.data.regs.X21 := reg .X21 rfl
  have e22 : st3.data.regs.X22 = st1.data.regs.X22 := reg .X22 rfl
  have e23 : st3.data.regs.X23 = st1.data.regs.X23 := reg .X23 rfl
  have e25 : st3.data.regs.X25 = st1.data.regs.X25 := reg .X25 rfl
  rw [r0] at hts' 
  have hL2 := NativeRustcVm.Tables.LayoutWAt.of_same (by rw [NativeRustcVm.addr_add_zero]; exact hL)
    (hsW (o := 0) (n := 3912) (by omega) (by omega))
  rw [NativeRustcVm.addr_add_zero] at hL2
  refine call10 hp hvso g h3 hpc3 (rate := rate)
    (by rw [e21, k21, h21]) (by rw [e22, k22, h22]) (e23.trans k23) (by rw [e25, k25, h25])
    (hd3 ▸ hts') (by rw [hroots']; exact hroots) (hd3 ▸ hL2)
    (hd3 ▸ (by rw [r2] at hring; exact hring))
    (hd3 ▸ NativeRustcVm.Top.KeccakOutAt.of_same ⟨hkp, hks, hksE⟩
      (hsW (o := 221280) (n := 1608) (by omega) (by omega)))
    (hd3 ▸ NativeRustcVm.Tables.ClaimsWAt.of_same hcl
      (hsW (o := 123992) (n := 97288) (by omega) (by omega)))
    (hd3 ▸ NativeRustcVm.Top.OodAt.of_same hood (hsW (o := 3912) (n := 504) (by omega) (by omega)))
    rfl

end

end NativeRustcVmArm.Top.VerifyExecution
