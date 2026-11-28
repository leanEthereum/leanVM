module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Ring.Weight.Basic

/-!
# `ring_weight`: what a block or a call keeps

A block of registers only (`regs_fr`); one writing a window of the powers (`frWin`: the frame
kept; `ew_write`: the element written; `ew_keep`: an element apart from the window kept); a block
ending in a call of `EW::mul` (`mulStep`), the frame's elements across it (`ew_call`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

public section

variable {m0 : MachineData}

theorem slots_out : ∀ p ∈ slots, p.1 + 8 ≤ 16 ∨ 592 ≤ p.1 := by decide

/-- The bytes a block writes, all in region `r`'s `sz` bytes. -/
theorem written_in {m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState} {r sz : Nat}
    {b : BitVec 64} (hr : rs[r]? = some (b, sz)) (hW : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ sz)
    {q : BitVec 64} (hq : Written (Env.ofMachine m rs) S q) :
    b.toNat ≤ q.toNat ∧ q.toNat < b.toNat + sz := by
  obtain ⟨w, hw, b', sz', hb, h1, h2⟩ := hq
  obtain ⟨hwr, hle⟩ := hW w hw
  rw [hwr] at hb
  change rs[r]? = some (b', sz') at hb
  rw [hr] at hb
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  omega

section
variable [Labels]

/-- **A block of registers only** keeps the frame. -/
theorem regs_fr {m m' : MachineData} {S' : SState} (hfr : WFr m0 m)
    (hm' : Match (Env.ofMachine m []) S' m') (hmem : S'.mem = []) (hsp : S'.sp = .sp) :
    WFr m0 m' :=
  hfr.ofBlock (match_nil m) hm' (Env.wf_nil m) rfl hmem hsp fun r hr ↦ by simp at hr

/-- **A block writing a window of the powers** (region `r`, frame bytes `o` to `o + sz`) keeps
the frame. -/
theorem frWin (h : RingWeightPre m0) {m m' : MachineData} {rs : List (BitVec 64 × Nat)}
    {S S' : SState} {r o sz : Nat} (hfr : WFr m0 m) (hm : Match (Env.ofMachine m rs) S m)
    (hm' : Match (Env.ofMachine m rs) S' m') (hwf : (Env.ofMachine m rs).WF) (hsp : S'.sp = S.sp)
    (hr : rs[r]? = some (fb m0 + BitVec.ofNat 64 o, sz)) (ho : 16 ≤ o) (hos : o + sz ≤ 592)
    (hW : ∀ w ∈ S'.mem, w.r = r ∧ w.off + w.n ≤ sz) : WFr m0 m' := by
  have hb := frame_toNat h (o := o) (by omega)
  have hN' := hN h
  rw [stack_eq] at hN'
  have hnwN := base_noWrap (m0 := m0) (F := ringWeightStack) (hN h)
  have hbN := base_toNat (m0 := m0) (F := ringWeightStack) (hN h)
  rw [stack_eq] at hnwN hbN
  refine hfr.step (W := Written (Env.ofMachine m rs) S') (Match.sp_eq hm hm' hsp)
    (fun r hr ↦ by simp at hr) (hm'.kept hwf) (hm'.sameOutside hwf) (fun q hq ↦ .inl ?_) ?_
  · obtain ⟨h1, h2⟩ := written_in hr hW hq
    rw [stack_eq, Sym.inRange_iff hnwN, hbN]
    rw [hb] at h1 h2
    omega
  · intro p hp i hi hq
    obtain ⟨h1, h2⟩ := written_in hr hW hq
    have hpo := slots_out p hp
    have hpl := slots_le p hp
    rw [hb] at h1 h2
    rw [NativeRustcVm.addr_add_add, frame_toNat h (by omega)] at h1 h2
    omega

/-- **An element a block wrote**: the words `v0`, `v1` at bytes `o`, `o + 8` of region `r`. -/
theorem ew_write {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r o sz : Nat}
    {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (hle : o + 16 ≤ sz) {v0 v1 : Sym}
    (h0 : ∀ i < 8, findWrite r (o + i) S.mem = some (v0, i))
    (h1 : ∀ i < 8, findWrite r (o + 8 + i) S.mem = some (v1, i)) :
    NativeRustcVm.EWAt m.dmem (b + BitVec.ofNat 64 o)
      ⟨UInt64.ofBitVec (v0.eval env), UInt64.ofBitVec (v1.eval env)⟩ := by
  have w0 := hm.bytesAt_write hb (by omega) h0
  have w1 := hm.bytesAt_write hb (o := o + 8) (by omega) h1
  rw [wordBytes_reg] at w0 w1
  rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
  exact ⟨w0, w1⟩

/-- **An element apart from a block's writes** is kept. -/
theorem ew_keep {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S' : SState}
    (hm' : Match (Env.ofMachine m rs) S' m') (hwf : (Env.ofMachine m rs).WF) {r sz : Nat}
    {b : BitVec 64} (hr : rs[r]? = some (b, sz)) (hW : ∀ w ∈ S'.mem, w.r = r ∧ w.off + w.n ≤ sz)
    {a : BitVec 64} {x : EW} (hx : NativeRustcVm.EWAt m.dmem a x) (hnw : a.toNat + 16 ≤ 2 ^ 64)
    (hap : a.toNat + 16 ≤ b.toNat ∨ b.toNat + sz ≤ a.toNat) : NativeRustcVm.EWAt m'.dmem a x :=
  NativeRustcVm.BytesAt.of_sameOutside hx (hm'.sameOutside hwf) fun i hi hq ↦ by
    rw [NativeRustcVm.length_ewBytes] at hi
    obtain ⟨h1, h2⟩ := written_in hr hW hq
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at h1 h2
    omega

end

/-- **An element of the frame across a call of `EW::mul`.** -/
theorem ew_call (h : RingWeightPre m0) {st m2 : MachineData} (hfr : WFr m0 st)
    (hq : EWMulPost st m2) {o : Nat} (ho : o + 16 ≤ 688) {x : EW}
    (hx : NativeRustcVm.EWAt st.dmem (fb m0 + BitVec.ofNat 64 o) x) :
    NativeRustcVm.EWAt m2.dmem (fb m0 + BitVec.ofNat 64 o) x := by
  have e : ewMulStack = 592 := rfl
  have hN' := hN h
  rw [stack_eq] at hN'
  have hsb := stackBelow_eq hfr.sp (N' := ewMulStack) (by rw [e]; omega)
  have hb := base_toNat (m0 := m0) (F := 688 + ewMulStack) (by rw [e]; omega)
  have hnw : NoWrap (base m0 (688 + ewMulStack)) ewMulStack := by
    unfold NoWrap; rw [hb]; have := m0.regs.SP.toNat_lt; rw [e]; omega
  refine NativeRustcVm.BytesAt.of_sameOutside hx hq.2.2.1 fun i hi hin ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hi
  rw [hsb, Sym.inRange_iff hnw, hb, NativeRustcVm.addr_add_add, frame_toNat h (by omega)] at hin
  rw [e] at hin
  omega

theorem at_pc {P : MachineState → Prop} {st : MachineState} {a : Int64} (h : st.pc = a)
    (c : P ⟨st.data, a⟩) : P st := by
  obtain ⟨d, pc⟩ := st
  simp only at h
  subst h
  exact c

theorem add_bv (a b : BitVec 64) : BinOp.apply .add .W64 a b = a + b := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]

theorem eor_bv (a b : BitVec 64) : BinOp.apply .eor .W64 a b = a ^^^ b := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]

theorem eor_eval [Labels] {env : Env} {s t : Sym} {a b : UInt64} (hs : s.eval env = a.toBitVec)
    (ht : t.eval env = b.toBitVec) : (Sym.bin .eor .W64 s t).eval env = (a ^^^ b).toBitVec := by
  simp only [Sym.eval]
  rw [eor_bv, hs, ht]
  rfl

theorem addr_eq {a : BitVec 64} {x y z : Nat} (h : x + y = z) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 z := by
  rw [NativeRustcVm.addr_add_add, h]

theorem ofInt_lit (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by simp

/-- `v - c` on small values. -/
theorem sub_lit {v c : Nat} (hc : c ≤ v) (hv : v < 2 ^ 64) :
    BinOp.apply .sub .W64 (BitVec.ofNat 64 v) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (v - c) := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  show BitVec.ofNat 64 v - BitVec.ofNat 64 c = _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `8 | v << 4` (`orr x, #8, v, lsl #4`): `16 v + 8`. -/
theorem orr8 (v : BitVec 64) (hv : v.toNat < 2 ^ 59) :
    BinOp.apply .orr .W64 (BitVec.ofNat 64 8) (UnOp.apply (.shift .LSL 4) .W64 v) =
      BitVec.ofNat 64 (16 * v.toNat + 8) := by
  simp only [BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64, shiftW]
  show BitVec.ofNat 64 8 ||| v <<< 4 = _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 8 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (by omega), Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (show 8 < 2 ^ 4 by decide), Nat.shiftLeft_eq]
  omega

section
variable [Labels]

/-- **A copied element**: the words of region `rs`'s bytes `o'`, `o' + 8` written at bytes `o`,
`o + 8` of region `rd`. -/
theorem ew_copy {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S' : SState}
    (hm : Match (Env.ofMachine m rs) S' st) {rd sz : Nat} {bd : BitVec 64}
    (hd : rs[rd]? = some (bd, sz)) {o : Nat} (hle : o + 16 ≤ sz) {rsrc szs : Nat}
    {bs : BitVec 64} (hs : rs[rsrc]? = some (bs, szs)) {o' o8 : Nat} (ho8 : o8 = o' + 8)
    (h0 : ∀ i < 8, findWrite rd (o + i) S'.mem = some (.load rsrc o' 8, i))
    (h1 : ∀ i < 8, findWrite rd (o + 8 + i) S'.mem = some (.load rsrc o8 8, i)) :
    NativeRustcVm.EWAt st.dmem (bd + BitVec.ofNat 64 o)
      (NativeRustcVm.ewOf m.dmem (bs + BitVec.ofNat 64 o')) := by
  subst ho8
  have := ew_write hm hd hle h0 h1
  rw [load_c0 hs, load_c1 hs, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec] at this
  exact this

end

variable [Host]

theorem hb {k : Nat} {ds : List Directive} {j : Nat} (h : ds.IsInfixAt Vm.RingWeight.code j)
    (hne : ds ≠ []) (hp : Placed Vm.RingWeight.code k) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **A block ending in a call of `EW::mul`**, writing nothing: the call's contract, the frame
after it. -/
theorem mulStep (h : RingWeightPre m0) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {rs : List (BitVec 64 × Nat)} {S S' : SState} {ds : List Directive} {i : Nat}
    {m : MachineData} {R : MachineState → Prop} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds S = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hfr : WFr m0 m)
    (hm : Match (Env.ofMachine m rs) S m) (hwf : (Env.ofMachine m rs).WF) (hmem : S'.mem = [])
    (hsp : S'.sp = S.sp)
    (cont : ∀ st m2 : MachineData, Match (Env.ofMachine m rs) S' st → WFr m0 st → WFr m0 m2 →
      EWMulPost st m2 → (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : WFr m0 st.data := hfr.ofBlock hm hm1 hwf rfl hmem hsp fun r hr ↦ by simp at hr
  exact Fr.leaf hfr1 (hN h) (N' := ewMulStack) (by decide) keep_nil slots_le (fun _ h ↦ h.elim)
    hmul (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ .inl h, hq.2.2.2⟩) hpc
    (hfr1.stackOk h.1 (by decide) (by decide)) fun m2 hfr2 hq hcs ↦
      cont st.data m2 hm1 hfr1 hfr2 hq hcs

end

end NativeRustcVmArm.Ring.Weight
