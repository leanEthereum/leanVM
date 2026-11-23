module

public import NativeRustcVmArm.Code.Vm.RingCoefficients.Names
public import NativeRustcVmArm.Ring.Switch.Sample

/-!
# `ring_switch`: the coefficients

`stepCoeff` (`b3`): `g` (the challenges `8 … 15`) copied to frame byte `256`,
`ring_coefficients(f, g, out.coefficients)` (`G3`).
-/

namespace NativeRustcVmArm.Ring.Switch

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.RingSwitch

@[expose] public section

/-- `f`: the first `8` challenges. -/
def fOf (xs : Array EW) : Array EW := xs.extract 0 8
/-- `g`: the other `8`. -/
def gOf (xs : Array EW) : Array EW := xs.extract 8 xs.size

/-- **After the coefficients**: `g`'s copy at frame byte `256`, the coefficients at the
`RingW`'s byte `16`. -/
structure G3 (a : DecArea) (s2 : TState) (xs : Array EW) (m0 m : MachineData) : Prop
    extends G2 a s2 xs m0 m where
  gc : NativeRustcVm.ewsOf m.dmem (fb m0 + BitVec.ofNat 64 256) 8 = xs.toList.drop 8
  coef : NativeRustcVm.EWsAt m.dmem (oA m0 + 16#64) (ringCoefficients (fOf xs) (gOf xs)).toList

/-- `b3`'s writes: frame bytes `256` to `384`. -/
def wrCopy (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r == 0 && decide (256 ≤ w.off) && decide (w.off + w.n ≤ 384)

/-- `b3`'s copy: frame word `128 + 8 j` to `256 + 8 j`. -/
def copyOk (S : SState) : Bool :=
  (List.range 16).all fun j ↦ (List.range 8).all fun i ↦
    findWrite 0 (256 + 8 * j + i) S.mem == some (.load 0 (128 + 8 * j) 8, i)

end

public section

variable {m0 : MachineData} {a : DecArea} {s : TState}

theorem arrF {d : Mem 64} {b : BitVec 64} {xs : Array EW}
    (hch : NativeRustcVm.EWsAt d b xs.toList) (hsz : xs.size = 16) :
    (NativeRustcVm.ewsOf d b 8).toArray = fOf xs := by
  have e := NativeRustcVm.ewsOf_of_ewsAt hch
  rw [Array.length_toList, hsz] at e
  rw [← ewsOf_take d b (n := 16) (k := 8) (by decide), e]
  apply Array.ext'
  simp [fOf]

theorem arrG {d : Mem 64} {b : BitVec 64} {xs : Array EW}
    (hgc : NativeRustcVm.ewsOf d b 8 = xs.toList.drop 8) (hsz : xs.size = 16) :
    (NativeRustcVm.ewsOf d b 8).toArray = gOf xs := by
  rw [hgc]
  apply Array.ext'
  simp [gOf, hsz]

/-- A shifted range is in the unshifted one, longer. -/
theorem inRange_shift {b q : BitVec 64} {o n : Nat} (h : InRange (b + BitVec.ofNat 64 o) n q)
    (hn : o + n < 2 ^ 64) : InRange b (o + n) q := by
  unfold InRange at *
  rw [BitVec.toNat_sub] at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h
  have := b.isLt
  have := q.isLt
  omega

/-- A byte a block wrote: in region 0's bytes `lo` to `hi`. -/
theorem written_in [Labels] {env : Env} {S : SState} {q b : BitVec 64} {F lo hi : Nat}
    (hq : Written env S q) (h0 : env.regions[0]? = some (b, F))
    (hm : S.mem.all (fun w ↦ w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) = true) :
    b.toNat + lo ≤ q.toNat ∧ q.toNat < b.toNat + hi := by
  obtain ⟨w, hw, b', sz, hb, h1, h2⟩ := hq
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨hr, hl⟩, hn⟩ := hm w hw
  rw [hr, h0] at hb
  cases hb
  omega

/-- The coefficients' range is in the `RingW`. -/
theorem coef_within {q : BitVec 64}
    (hq : InRange (oA m0 + 16#64) 1024 q) : InRange (oA m0) ringWBytes q :=
  inRange_shift (o := 16) hq (by decide)

section
variable [Labels]

/-- **`b3`'s copy**: frame word `128 + 8 j` at `256 + 8 j`. -/
theorem copy_word {m st : MachineData} {S : SState}
    (hm1 : Match (envM m0 m) S st) (hc : copyOk S = true) {j : Nat} (hj : j < 16) :
    NativeRustcVm.wordOf st.dmem (fb m0 + BitVec.ofNat 64 (256 + 8 * j)) =
      NativeRustcVm.wordOf m.dmem (fb m0 + BitVec.ofNat 64 (128 + 8 * j)) := by
  simp only [copyOk, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  have hw := hm1.bytesAt_write (r := 0) (o := 256 + 8 * j) (n := 8) (b := fb m0) (sz := 432) rfl
    (by omega) (v := .load 0 (128 + 8 * j) 8) fun i hi ↦ hc j hj i hi
  rw [wordBytes_reg] at hw
  rw [NativeRustcVm.wordOf_of_wordAt hw]
  show UInt64.ofBitVec (Env.load _ 0 (128 + 8 * j) 8) = _
  rw [load_eq_wordOf]
  rfl

/-- The `RingW` is apart from a callee's stack. -/
theorem out_callee (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) {N' : Nat}
    (hle : 432 + N' ≤ ringSwitchStack) : Apart (oA m0) ringWBytes (stackBelow m N') N' :=
  hfr.apart (hN h) h.2.2.2.2.1.2.2.2.2.1 hle

/-- `s` is apart from a callee's stack. -/
theorem s_callee (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) {N' : Nat}
    (hle : 432 + N' ≤ ringSwitchStack) : Apart (sA m0) 1024 (stackBelow m N') N' :=
  hfr.apart (hN h) h.2.2.2.2.2.1.2 hle

/-- **Bytes in the `RingW`** are kept by a call changing only its stack. -/
theorem out_keep (h : RingSwitchPre a s m0) {m m' : MachineData} (hfr : SFr m0 m) {N' : Nat}
    (hle : 432 + N' ≤ ringSwitchStack)
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m N') N' q)
    {o : Nat} {bs : List UInt8} (hon : o + bs.length ≤ ringWBytes)
    (hb : NativeRustcVm.BytesAt m.dmem (oA m0 + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m'.dmem (oA m0 + BitVec.ofNat 64 o) bs := by
  have hw := o_noWrap h
  have hsw : NoWrap (stackBelow m N') N' := by
    have := hN h
    have hSP := m0.regs.SP.toNat_lt
    rw [stackBelow_eq hfr.sp (by omega)]
    unfold NoWrap; rw [base_toNat (by omega)]; omega
  refine NativeRustcVm.BytesAt.of_sameOutside hb hs fun j hj hq ↦ ?_
  rw [NativeRustcVm.addr_add_add] at hq
  exact NativeRustcVm.Apart.not_inRange_add (out_callee h hfr hle) hw hsw (by omega) hq

end

variable [Host] {k : Nat}

/-- **The coefficients** (`b3`). -/
theorem stepCoeff (hp : Placed code k) (h : RingSwitchPre a s m0)
    (hrc : Spec (Labels.label NativeRustcVmArm.Vm.RingCoefficients.entryLabel) RingCoefficientsPre RingCoefficientsPost)
    {s2 : TState} {xs : Array EW} {m : MachineData} (hG : G2 a s2 xs m0 m)
    {R : MachineState → Prop}
    (cont : ∀ m', G3 a s2 xs m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b4Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b3Offset)⟩ := by
  have hwf := envM_wf h hG.fr
  have hm := matchM h hG.fr
  refine exec_then (hb b3_in_code (by simp [b3]) hp) run_b3 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : SFr m0 st.data :=
    hG.fr.ofBlockW hm hm1 hwf rfl rfl (keep_ok (by decide) (by decide)) rfl (by decide) (hN h)
      slots_le (writeOk_low (by decide))
  have hfw := fbw h
  have hfN := fbN h
  have hN' := hN h
  rw [stack_eq] at hN'
  have hSP := m0.regs.SP.toNat_lt
  unfold NoWrap at hfw
  have hlen : (xs.toList.flatMap NativeRustcVm.ewBytes).length = 256 := by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hG.sz]
  -- the challenges kept, `g` copied
  have hch1 : NativeRustcVm.EWsAt st.data.dmem (fb m0) xs.toList :=
    NativeRustcVm.BytesAt.of_sameOutside hG.ch (hm1.sameOutside hwf) fun j hj hq ↦ by
      have := written_in hq rfl (lo := 256) (hi := 384) (by decide)
      rw [hlen] at hj
      rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
      omega
  have hts1 : TStateAt st.data.dmem (tA m0) a s2 :=
    ts_keep h hG.ts (hm1.kept hwf) (hm1.sameOutside hwf) fun q hq ↦
      frame_within h (written_frame hq rfl (by decide))
  have hcopy : NativeRustcVm.ewsOf st.data.dmem (fb m0 + BitVec.ofNat 64 256) 8 =
      xs.toList.drop 8 := by
    rw [← NativeRustcVm.ewsOf_of_ewsAt hG.ch, Array.length_toList, hG.sz,
      show 16 = 8 + 8 from rfl, ewsOf_drop]
    refine ewsOf_of_words fun j hj ↦ ?_
    rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add,
      show 16 * 8 + 8 * j = 128 + 8 * j by omega]
    exact copy_word hm1 (by decide) hj
  have e0 : st.data.regs.X0.toBitVec = fb m0 := by
    rw [show st.data.regs.X0 = st.data.regs.getXReg .X0 from rfl, hm1.regs .X0 (.ptr 0 0) rfl]
    simp [Sym.eval]
  have e1 : st.data.regs.X1.toBitVec = fb m0 + BitVec.ofNat 64 256 := by
    rw [show st.data.regs.X1 = st.data.regs.getXReg .X1 from rfl, hm1.regs .X1 (.ptr 0 256) rfl]
    simp only [Sym.eval]
    rw [show ((256 : Int)) = ((256 : Nat) : Int) from rfl, BitVec.ofInt_natCast]
    rfl
  have e2 : st.data.regs.X2.toBitVec = oA m0 + 16#64 := by
    rw [show st.data.regs.X2 = st.data.regs.getXReg .X2 from rfl,
      hm1.regs .X2 (.bin .add .W64 (.reg .X19) (.lit 16)) rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [hG.x19]
    rfl
  have how := o_noWrap h
  unfold NoWrap ringWBytes coeffCount at how
  have hoF := o_frame h
  have hoS := out_callee h hfr1 (N' := ringCoefficientsStack) (by decide)
  have ho16 : (oA m0 + 16#64).toNat = (oA m0).toNat + 16 := NativeRustcVm.toNat_add_ofNat (by omega)
  have hf256 : (fb m0 + BitVec.ofNat 64 256).toNat = (fb m0).toNat + 256 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  unfold ringWBytes coeffCount at hoF hoS
  have hpre : RingCoefficientsPre st.data := by
    simp only [RingCoefficientsPre, ArrOk, Readable, OffStack, e0, e1, e2, ringWidth, coeffCount]
    refine ⟨hfr1.stackOk h.1 (by decide) (by decide), ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩,
      ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩, ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · exact hfr1.kept _ (frame_mapped h.1 (by decide) j (by omega))
    · unfold NoWrap; omega
    · have := apart_callee h hfr1 (o := 0) (n := 128) (N' := ringCoefficientsStack) (by decide)
        (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    · rw [NativeRustcVm.addr_add_add]
      exact hfr1.kept _ (frame_mapped h.1 (by decide) _ (by omega))
    · unfold NoWrap; omega
    · exact apart_callee h hfr1 (by decide) (by decide)
    · rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add]
      exact hfr1.kept _ (h.2.2.2.2.1.1 _ (by unfold ringWBytes coeffCount; omega))
    · unfold NoWrap; omega
    · unfold Apart at *; omega
    · unfold Apart at *; omega
    · unfold Apart at *; omega
  refine Fr.leafAt hfr1 (hN h) (N' := ringCoefficientsStack) (by decide) keep_cs slots_le
    (outs_frame h) hrc hpc hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ hq.elim
      (fun hq ↦ .inr (.inl (coef_within (by rw [e2] at hq; exact hq)))) .inl, hq.2.2⟩)
    fun m2 hfr2 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingSwitch.b3Offset + b3.length = k + NativeRustcVmArm.Vm.RingSwitch.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingSwitch.b3_next]]
  obtain ⟨hcoef, hchg, hS⟩ := hq
  have hs : SameOutside st.data.dmem m2.dmem fun q ↦
      InRange (stackBelow st.data ringCoefficientsStack) ringCoefficientsStack q ∨ outs m0 q :=
    NativeRustcVm.SameOutside.mono hchg fun q hq ↦ hq.elim
      (fun hq ↦ .inr (.inl (coef_within (by rw [e2] at hq; exact hq)))) .inl
  refine cont m2 {
    fr := hfr2
    x19 := (hcs .X19 rfl).trans ((Match.reg_eq hm hm1 (r := .X19) rfl rfl).trans hG.x19)
    x20 := (hcs .X20 rfl).trans ((Match.reg_eq hm hm1 (r := .X20) rfl rfl).trans hG.x20)
    x21 := (hcs .X21 rfl).trans ((Match.reg_eq hm hm1 (r := .X21) rfl rfl).trans hG.x21)
    x22 := (hcs .X22 rfl).trans ((Match.reg_eq hm hm1 (r := .X22) rfl rfl).trans hG.x22)
    ts := ts_keep h hts1 hS.2.2 hchg fun q hq ↦ hq.elim
      (fun hq ↦ .inr (coef_within (by rw [e2] at hq; exact hq))) (stack_within h hfr1 (by decide))
    ch := by
      have := frame_bytes_keep h hfr1 (by decide) hs (o := 0) (bs := xs.toList.flatMap
        NativeRustcVm.ewBytes) (by rw [hlen]; omega) (by rw [NativeRustcVm.addr_add_zero]; exact hch1)
      rwa [NativeRustcVm.addr_add_zero] at this
    sz := hG.sz
    gc := by
      rw [NativeRustcVm.ewsOf_congr (d := st.data.dmem) fun j hj ↦ hs _
        (frame_safe h hfr1 (by decide) (o := 256) (n := 128) (by decide) hj)]
      exact hcopy
    coef := by
      rw [e2] at hcoef
      unfold arr at hcoef
      rwa [e0, e1, ringWidth, arrF hch1 hG.sz, arrG hcopy hG.sz] at hcoef }

end

end NativeRustcVmArm.Ring.Switch
