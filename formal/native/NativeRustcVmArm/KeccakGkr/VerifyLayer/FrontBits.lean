module

public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontProj

/-!
# `verify_layer`'s front: a round constant's bit weights

The two loops (`b18`, `b20`) summing the claim's bit weights `z < 64` a round constant keeps,
four bits a turn into four accumulators (`BitsA`/`bitsA_loop`, `BitsB`/`bitsB_loop`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)

@[expose] public section

/-- Accumulator `e` of the bit weights after `i` turns. -/
abbrev bAcc (c : KeccakClaimW) (k : UInt64) (e i : Nat) : EW :=
  xs (fun l ↦ bitSel c.weights k (4 * l + e)) i

/-- **The first loop's head** (`b18`), `i` turns done. -/
structure BitsA [Labels] (m0 : MachineData) (c : KeccakClaimW) (k : UInt64) (i : Nat)
    (st0 st : MachineData) : Prop where
  fb : FB m0 st
  dm : st.dmem = st0.dmem
  keep : Bus.KeepRegs [.X0, .X1, .X21, .X22, .X25] st0 st
  lt : i < 16
  x17 : st.regs.X17.toNat = 4 * i
  x2 : st.regs.X2.toBitVec = sA m0 + BitVec.ofNat 64 (25656 + 64 * i)
  x18 : st.regs.X18 = k
  x3 : st.regs.X3.toNat = 2 ^ 0
  x4 : st.regs.X4.toNat = 2 ^ 1
  x5 : st.regs.X5.toNat = 2 ^ 2
  x6 : st.regs.X6.toNat = 2 ^ 3
  a0 : (⟨st.regs.X12, st.regs.X8⟩ : EW) = bAcc c k 0 i
  a1 : (⟨st.regs.X13, st.regs.X9⟩ : EW) = bAcc c k 1 i
  a2 : (⟨st.regs.X14, st.regs.X10⟩ : EW) = bAcc c k 2 i
  a3 : (⟨st.regs.X16, st.regs.X11⟩ : EW) = bAcc c k 3 i

/-- **The second loop's head** (`b20`), `i` turns done. -/
structure BitsB [Labels] (m0 : MachineData) (c : KeccakClaimW) (k : UInt64) (i : Nat)
    (st0 st : MachineData) : Prop where
  fb : FB m0 st
  dm : st.dmem = st0.dmem
  keep : Bus.KeepRegs [.X10, .X11, .X21, .X22, .X25] st0 st
  lt : i < 16
  x4 : st.regs.X4.toNat = 4 * i
  x13 : st.regs.X13.toBitVec = sA m0 + BitVec.ofNat 64 (25656 + 64 * i)
  x12 : st.regs.X12 = k
  x14 : st.regs.X14.toNat = 2 ^ 0
  x15 : st.regs.X15.toNat = 2 ^ 1
  x16 : st.regs.X16.toNat = 2 ^ 2
  x20 : st.regs.X20.toNat = 2 ^ 3
  a0 : (⟨st.regs.X5, st.regs.X17⟩ : EW) = bAcc c k 0 i
  a1 : (⟨st.regs.X6, st.regs.X18⟩ : EW) = bAcc c k 1 i
  a2 : (⟨st.regs.X7, st.regs.X2⟩ : EW) = bAcc c k 2 i
  a3 : (⟨st.regs.X19, st.regs.X3⟩ : EW) = bAcc c k 3 i

end

public section

theorem lslv_pow {x y : BitVec 64} {e s : Nat} (hx : x.toNat = 2 ^ e) (hy : y.toNat = s)
    (h : s + e < 64) : (BinOp.apply .lslv .W64 x y).toNat = 2 ^ (s + e) := by
  sym_simp
  have hw : RegWidth.W64.bits = 64 := rfl
  rw [BitVec.toNat_shiftLeft, hy, hx, Nat.shiftLeft_eq, hw,
    Nat.mod_eq_of_lt (show s < 64 by omega), ← Nat.pow_add, Nat.add_comm e s]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)

/-- An accumulator plus a kept term. -/
theorem acc_sel (acc x : EW) (b : Bool) :
    (⟨acc.c0 ^^^ (if b then x.c0 else 0), acc.c1 ^^^ (if b then x.c1 else 0)⟩ : EW) =
      acc + sel b x := by
  cases b
  · show (⟨acc.c0 ^^^ 0, acc.c1 ^^^ 0⟩ : EW) = acc + 0
    rw [ew_add_zero']
    simp
  · rfl

theorem bAcc_succ (c : KeccakClaimW) (k : UInt64) (e i : Nat) :
    bAcc c k e (i + 1) = bAcc c k e i + bitSel c.weights k (4 * i + e) := xs_succ _ _

/-- The four accumulators make the sum. -/
theorem bits_four (c : KeccakClaimW) (k : UInt64) :
    bitsOf c.weights k = bAcc c k 0 16 + bAcc c k 1 16 + (bAcc c k 2 16 + bAcc c k 3 16) := by
  rw [bits_eq, show 64 = 4 * 16 from rfl, xs_split4]
  rfl

section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- The bit weights `4 i` to `4 i + 3` as a region. -/
theorem wf_bits (h : VerifyLayerPre a s c m0) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {i : Nat} (hi : i < 25) :
    (Env.ofMachine m [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)]).WF := by
  have g := geo_of h
  have pg := pgeo_of h
  have := g.hs
  have e := g.sa (o := 25600 + 64 * i) (by omega)
  exact Env.wf_of ⟨⟨mapped_sub hk pg.sm (by omega), by unfold NoWrap; rw [e]; omega⟩, trivial⟩
    (List.pairwise_singleton _ _)

/-- The bit weights' words in the region. -/
theorem bits_word (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) {i q : Nat}
    (hi : i < 16) (hq : q < 4) :
    NativeRustcVm.WordAt m.dmem
        (sA m0 + BitVec.ofNat 64 (25600 + 64 * i) + BitVec.ofNat 64 (16 * q))
        (c.weights.getD (4 * i + q) 0).c0 ∧
      NativeRustcVm.WordAt m.dmem
        (sA m0 + BitVec.ofNat 64 (25600 + 64 * i) + BitVec.ofNat 64 (16 * q + 8))
        (c.weights.getD (4 * i + q) 0).c1 := by
  have := w_word (weightsAt_fb h hb) (z := 4 * i + q) (by omega)
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add,
    show 25600 + 64 * i + 16 * q = 25600 + 16 * (4 * i + q) by omega,
    show 25600 + 64 * i + (16 * q + 8) = 25600 + 16 * (4 * i + q) + 8 by omega]
  exact this

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem label14 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_14 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b18Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b18Offset) NativeRustcVmArm.Vm.VerifyLayer.label_14_at

theorem label16 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_16 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b20Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b20Offset) NativeRustcVmArm.Vm.VerifyLayer.label_16_at

/-- **The first bit weights' loop**, to `b19`. -/
theorem bitsA_loop (hp : Placed code k) (h : VerifyLayerPre a s c m0) {w : UInt64}
    {st0 : MachineData} {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b19Offset) → FB m0 st'.data →
      st'.data.dmem = st0.dmem → Bus.KeepRegs [.X0, .X1, .X21, .X22, .X25] st0 st'.data →
      (⟨st'.data.regs.X12, st'.data.regs.X8⟩ : EW) = bAcc c w 0 16 →
      (⟨st'.data.regs.X13, st'.data.regs.X9⟩ : EW) = bAcc c w 1 16 →
      (⟨st'.data.regs.X14, st'.data.regs.X10⟩ : EW) = bAcc c w 2 16 →
      (⟨st'.data.regs.X16, st'.data.regs.X11⟩ : EW) = bAcc c w 3 16 →
      Eventually (step1 Host.exe) R st') :
    ∀ r i (st : MachineState), 16 - i = r → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b18Offset) →
      BitsA m0 c w i st0 st.data → Eventually (step1 Host.exe) R st := by
  have g := geo_of h
  intro r
  induction r with
  | zero => intro i st hr _ hi; have := hi.lt; omega
  | succ r ih =>
    intro i st hr hpc hi
    have hl := hi.lt
    have hwf := wf_bits h hi.fb.kept (i := i) (by omega)
    have hm : Match (Env.ofMachine st.data [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)])
        bits2S st.data :=
      match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
        ⟨by
          show st.data.regs.X2.toBitVec = sA m0 + BitVec.ofNat 64 (25600 + 64 * i) +
            BitVec.ofInt 64 56
          rw [hi.x2, show BitVec.ofInt 64 56 = BitVec.ofNat 64 56 from rfl,
            NativeRustcVm.addr_add_add]
          exact addr_eq (by omega), trivial⟩ trivial trivial trivial
    refine fb_run hi.fb (blk hp b18_in_code (by simp [b18])) e18 hwf rfl hpc hm rfl rfl
      fun st1 hb1 hd1 hm1 hpc1 ↦ ?_
    have wq := fun q (hq : q < 4) ↦ bits_word h hi.fb (c := c) (i := i) (q := q) hl hq
    have r17 : (st.data.regs.getXReg .X17).toNat = 4 * i := hi.x17
    have r18 : (st.data.regs.getXReg .X18).toBitVec = w.toBitVec := congrArg _ hi.x18
    have hA : ∀ (r : XReg) (e : Nat), (st.data.regs.getXReg r).toNat = 2 ^ e → e < 4 →
        ((Sym.bin .lslv .W64 (.reg r) (.reg .X17)).eval (Env.ofMachine st.data
          [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)])).toNat = 2 ^ (4 * i + e) :=
      fun r e hr he ↦ by
        rw [ev_bin, ev_regU, ev_regU]
        exact lslv_pow hr r17 (by omega)
    have hB : (Sym.reg .X18).eval (Env.ofMachine st.data
        [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)]) = w.toBitVec := regB .X18 r18
    have v12 := reg_val (r := .X12) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X3 0 hi.x3 (by decide)) hB (ldF (wq 0 (by decide)).1)))
    have v8 := reg_val (r := .X8) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X3 0 hi.x3 (by decide)) hB (ldF (wq 0 (by decide)).2)))
    have v13 := reg_val (r := .X13) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X4 1 hi.x4 (by decide)) hB (ldF (wq 1 (by decide)).1)))
    have v9 := reg_val (r := .X9) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X4 1 hi.x4 (by decide)) hB (ldF (wq 1 (by decide)).2)))
    have v14 := reg_val (r := .X14) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X5 2 hi.x5 (by decide)) hB (ldF (wq 2 (by decide)).1)))
    have v10 := reg_val (r := .X10) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X5 2 hi.x5 (by decide)) hB (ldF (wq 2 (by decide)).2)))
    have v16 := reg_val (r := .X16) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X6 3 hi.x6 (by decide)) hB (ldF (wq 3 (by decide)).1)))
    have v11 := reg_val (r := .X11) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X6 3 hi.x6 (by decide)) hB (ldF (wq 3 (by decide)).2)))
    have k1 : Bus.KeepRegs [.X0, .X1, .X3, .X4, .X5, .X6, .X18, .X21, .X22, .X25]
        st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
    have hacc : ∀ e (u v : UInt64) (x0 x1 : UInt64), (⟨x0, x1⟩ : EW) = bAcc c w e i →
        u = x0 ^^^ (if testBitW w (4 * i + e) then (c.weights.getD (4 * i + e) 0).c0 else 0) →
        v = x1 ^^^ (if testBitW w (4 * i + e) then (c.weights.getD (4 * i + e) 0).c1 else 0) →
        (⟨u, v⟩ : EW) = bAcc c w e (i + 1) := by
      intro e u v x0 x1 hx hu hv
      rw [bAcc_succ, ← hx, hu, hv, bitSel, ← acc_sel]
    have r17' : ((Sym.bin .add .W64 (.reg .X17) (.lit 4)).eval (Env.ofMachine st.data
        [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)])).toNat = 4 * (i + 1) := by
      rw [ev_bin, add_toNat, regN .X17 r17, litN 4]
      omega
    have keep' : Bus.KeepRegs [.X0, .X1, .X21, .X22, .X25] st0 st1.data :=
      hi.keep.trans fun r hr ↦ k1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
    have a0 : (⟨st1.data.regs.X12, st1.data.regs.X8⟩ : EW) = bAcc c w 0 (i + 1) :=
      hacc 0 _ _ _ _ hi.a0 v12 v8
    have a1 : (⟨st1.data.regs.X13, st1.data.regs.X9⟩ : EW) = bAcc c w 1 (i + 1) :=
      hacc 1 _ _ _ _ hi.a1 v13 v9
    have a2 : (⟨st1.data.regs.X14, st1.data.regs.X10⟩ : EW) = bAcc c w 2 (i + 1) :=
      hacc 2 _ _ _ _ hi.a2 v14 v10
    have a3 : (⟨st1.data.regs.X16, st1.data.regs.X11⟩ : EW) = bAcc c w 3 (i + 1) :=
      hacc 3 _ _ _ _ hi.a3 v16 v11
    have hc : (SBool.not (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X17) (.lit 4)) (.lit 64))).eval
        (Env.ofMachine st.data [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)]) =
          !decide (i + 1 = 16) := by
      rw [sb_not, sb_cmp, eq_apply, r17', litN 64]
      by_cases he : i + 1 = 16
      · rw [decide_eq_true he, decide_eq_true (by omega)]
      · rw [decide_eq_false he, decide_eq_false (by omega)]
    by_cases he : i + 1 = 16
    · have hpc1' := pc_false hpc1 (by rw [hc, decide_eq_true he]; rfl)
      rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b18Offset + b18.length = k + NativeRustcVmArm.Vm.VerifyLayer.b19Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b18_next]] at hpc1'
      rw [he] at a0 a1 a2 a3
      exact cont st1 hpc1' hb1 (hd1.trans hi.dm) keep' a0 a1 a2 a3
    · have hpc1' := (pc_true hpc1 (by rw [hc, decide_eq_false he]; rfl)).trans (label14 hp)
      refine ih (i + 1) st1 (by omega) hpc1' ⟨hb1, hd1.trans hi.dm, keep', by omega, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, a0, a1, a2, a3⟩
      · show (st1.data.regs.getXReg .X17).toBitVec.toNat = _
        rw [hm1.regs .X17 _ rfl, r17']
      · show (st1.data.regs.getXReg .X2).toBitVec = _
        rw [hm1.regs .X2 _ rfl, ev_ptr]
        show sA m0 + BitVec.ofNat 64 (25600 + 64 * i) + BitVec.ofInt 64 120 = _
        rw [show BitVec.ofInt 64 120 = BitVec.ofNat 64 120 from rfl, NativeRustcVm.addr_add_add]
        exact addr_eq (by omega)
      · exact (kg k1 .X18).trans hi.x18
      · exact (congrArg UInt64.toNat (kg k1 .X3)).trans hi.x3
      · exact (congrArg UInt64.toNat (kg k1 .X4)).trans hi.x4
      · exact (congrArg UInt64.toNat (kg k1 .X5)).trans hi.x5
      · exact (congrArg UInt64.toNat (kg k1 .X6)).trans hi.x6

/-- **The second bit weights' loop**, to `b21`. -/
theorem bitsB_loop (hp : Placed code k) (h : VerifyLayerPre a s c m0) {w : UInt64}
    {st0 : MachineData} {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset) → FB m0 st'.data →
      st'.data.dmem = st0.dmem → Bus.KeepRegs [.X10, .X11, .X21, .X22, .X25] st0 st'.data →
      (⟨st'.data.regs.X5, st'.data.regs.X17⟩ : EW) = bAcc c w 0 16 →
      (⟨st'.data.regs.X6, st'.data.regs.X18⟩ : EW) = bAcc c w 1 16 →
      (⟨st'.data.regs.X7, st'.data.regs.X2⟩ : EW) = bAcc c w 2 16 →
      (⟨st'.data.regs.X19, st'.data.regs.X3⟩ : EW) = bAcc c w 3 16 →
      Eventually (step1 Host.exe) R st') :
    ∀ r i (st : MachineState), 16 - i = r → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b20Offset) →
      BitsB m0 c w i st0 st.data → Eventually (step1 Host.exe) R st := by
  have g := geo_of h
  intro r
  induction r with
  | zero => intro i st hr _ hi; have := hi.lt; omega
  | succ r ih =>
    intro i st hr hpc hi
    have hl := hi.lt
    have hwf := wf_bits h hi.fb.kept (i := i) (by omega)
    have hm : Match (Env.ofMachine st.data [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)])
        bits13S st.data :=
      match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
        ⟨by
          show st.data.regs.X13.toBitVec = sA m0 + BitVec.ofNat 64 (25600 + 64 * i) +
            BitVec.ofInt 64 56
          rw [hi.x13, show BitVec.ofInt 64 56 = BitVec.ofNat 64 56 from rfl,
            NativeRustcVm.addr_add_add]
          exact addr_eq (by omega), trivial⟩ trivial trivial trivial
    refine fb_run hi.fb (blk hp b20_in_code (by simp [b20])) e20 hwf rfl hpc hm rfl rfl
      fun st1 hb1 hd1 hm1 hpc1 ↦ ?_
    have wq := fun q (hq : q < 4) ↦ bits_word h hi.fb (c := c) (i := i) (q := q) hl hq
    have r4 : (st.data.regs.getXReg .X4).toNat = 4 * i := hi.x4
    have r12 : (st.data.regs.getXReg .X12).toBitVec = w.toBitVec := congrArg _ hi.x12
    have hA : ∀ (r : XReg) (e : Nat), (st.data.regs.getXReg r).toNat = 2 ^ e → e < 4 →
        ((Sym.bin .lslv .W64 (.reg r) (.reg .X4)).eval (Env.ofMachine st.data
          [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)])).toNat = 2 ^ (4 * i + e) :=
      fun r e hr he ↦ by
        rw [ev_bin, ev_regU, ev_regU]
        exact lslv_pow hr r4 (by omega)
    have hB : (Sym.reg .X12).eval (Env.ofMachine st.data
        [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)]) = w.toBitVec := regB .X12 r12
    have v5 := reg_val (r := .X5) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X14 0 hi.x14 (by decide)) hB (ldF (wq 0 (by decide)).1)))
    have v17 := reg_val (r := .X17) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X14 0 hi.x14 (by decide)) hB (ldF (wq 0 (by decide)).2)))
    have v6 := reg_val (r := .X6) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X15 1 hi.x15 (by decide)) hB (ldF (wq 1 (by decide)).1)))
    have v18 := reg_val (r := .X18) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X15 1 hi.x15 (by decide)) hB (ldF (wq 1 (by decide)).2)))
    have v7 := reg_val (r := .X7) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X16 2 hi.x16 (by decide)) hB (ldF (wq 2 (by decide)).1)))
    have v2 := reg_val (r := .X2) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X16 2 hi.x16 (by decide)) hB (ldF (wq 2 (by decide)).2)))
    have v19 := reg_val (r := .X19) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X20 3 hi.x20 (by decide)) hB (ldF (wq 3 (by decide)).1)))
    have v3 := reg_val (r := .X3) hm1 rfl (eorSym (ev_regU _ _ _)
      (selSym' (by omega) (hA .X20 3 hi.x20 (by decide)) hB (ldF (wq 3 (by decide)).2)))
    have k1 : Bus.KeepRegs [.X10, .X11, .X12, .X14, .X15, .X16, .X20, .X21, .X22, .X25]
        st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
    have hacc : ∀ e (u v : UInt64) (x0 x1 : UInt64), (⟨x0, x1⟩ : EW) = bAcc c w e i →
        u = x0 ^^^ (if testBitW w (4 * i + e) then (c.weights.getD (4 * i + e) 0).c0 else 0) →
        v = x1 ^^^ (if testBitW w (4 * i + e) then (c.weights.getD (4 * i + e) 0).c1 else 0) →
        (⟨u, v⟩ : EW) = bAcc c w e (i + 1) := by
      intro e u v x0 x1 hx hu hv
      rw [bAcc_succ, ← hx, hu, hv, bitSel, ← acc_sel]
    have r4' : ((Sym.bin .add .W64 (.reg .X4) (.lit 4)).eval (Env.ofMachine st.data
        [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)])).toNat = 4 * (i + 1) := by
      rw [ev_bin, add_toNat, regN .X4 r4, litN 4]
      omega
    have keep' : Bus.KeepRegs [.X10, .X11, .X21, .X22, .X25] st0 st1.data :=
      hi.keep.trans fun r hr ↦ k1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
    have a0 : (⟨st1.data.regs.X5, st1.data.regs.X17⟩ : EW) = bAcc c w 0 (i + 1) :=
      hacc 0 _ _ _ _ hi.a0 v5 v17
    have a1 : (⟨st1.data.regs.X6, st1.data.regs.X18⟩ : EW) = bAcc c w 1 (i + 1) :=
      hacc 1 _ _ _ _ hi.a1 v6 v18
    have a2 : (⟨st1.data.regs.X7, st1.data.regs.X2⟩ : EW) = bAcc c w 2 (i + 1) :=
      hacc 2 _ _ _ _ hi.a2 v7 v2
    have a3 : (⟨st1.data.regs.X19, st1.data.regs.X3⟩ : EW) = bAcc c w 3 (i + 1) :=
      hacc 3 _ _ _ _ hi.a3 v19 v3
    have hc : (SBool.not (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X4) (.lit 4)) (.lit 64))).eval
        (Env.ofMachine st.data [(sA m0 + BitVec.ofNat 64 (25600 + 64 * i), 64)]) =
          !decide (i + 1 = 16) := by
      rw [sb_not, sb_cmp, eq_apply, r4', litN 64]
      by_cases he : i + 1 = 16
      · rw [decide_eq_true he, decide_eq_true (by omega)]
      · rw [decide_eq_false he, decide_eq_false (by omega)]
    by_cases he : i + 1 = 16
    · have hpc1' := pc_false hpc1 (by rw [hc, decide_eq_true he]; rfl)
      rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b20Offset + b20.length = k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b20_next]] at hpc1'
      rw [he] at a0 a1 a2 a3
      exact cont st1 hpc1' hb1 (hd1.trans hi.dm) keep' a0 a1 a2 a3
    · have hpc1' := (pc_true hpc1 (by rw [hc, decide_eq_false he]; rfl)).trans (label16 hp)
      refine ih (i + 1) st1 (by omega) hpc1' ⟨hb1, hd1.trans hi.dm, keep', by omega, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, a0, a1, a2, a3⟩
      · show (st1.data.regs.getXReg .X4).toBitVec.toNat = _
        rw [hm1.regs .X4 _ rfl, r4']
      · show (st1.data.regs.getXReg .X13).toBitVec = _
        rw [hm1.regs .X13 _ rfl, ev_ptr]
        show sA m0 + BitVec.ofNat 64 (25600 + 64 * i) + BitVec.ofInt 64 120 = _
        rw [show BitVec.ofInt 64 120 = BitVec.ofNat 64 120 from rfl, NativeRustcVm.addr_add_add]
        exact addr_eq (by omega)
      · exact (kg k1 .X12).trans hi.x12
      · exact (congrArg UInt64.toNat (kg k1 .X14)).trans hi.x14
      · exact (congrArg UInt64.toNat (kg k1 .X15)).trans hi.x15
      · exact (congrArg UInt64.toNat (kg k1 .X16)).trans hi.x16
      · exact (congrArg UInt64.toNat (kg k1 .X20)).trans hi.x20

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
