module

public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Layers

/-!
# `verify_keccak` after the layers: tools

A branch to the failure exit from a state of the frame, registers of a list kept
(`failBranchF`); `Mid` across a block without writes (`Mid.of_dmem`); the branch conditions
comparing two registers (`condNe`); `ite`s on a bound (`eval_ite_lt`); elements compared limb by
limb (`ew_beq_c0`, `ew_beq_c1`, `ew_beq_true`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

public section

section
variable [Labels] {env : Env}

theorem condNe {r1 r2 : XReg} :
    (SBool.not (.cmp .eq .W64 (.reg r1) (.reg r2))).eval env = !(env.regs r1 == env.regs r2) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]

theorem eval_ite_lt {x y z : Sym} {B : Nat} (hB : B < 2 ^ 64) (h : (x.eval env).toNat < B) :
    (Sym.ite (.cmp .ult .W64 x (.lit B)) y z).eval env = y.eval env := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, ult_ofNat _ hB, h, decide_true,
    ite_true]

end

theorem ew_beq_c0 {x y : EW} (h : x.c0 ≠ y.c0) : (x == y) = false := by
  cases hb : (x == y)
  · rfl
  · exact absurd (congrArg EW.c0 (beq_iff_eq.mp hb)) h

theorem ew_beq_c1 {x y : EW} (h : x.c1 ≠ y.c1) : (x == y) = false := by
  cases hb : (x == y)
  · rfl
  · exact absurd (congrArg EW.c1 (beq_iff_eq.mp hb)) h

theorem ew_beq_true {x y : EW} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : (x == y) = true := by
  obtain ⟨x0, x1⟩ := x
  obtain ⟨y0, y1⟩ := y
  simp only at h0 h1
  subst h0 h1
  exact beq_self_eq_true _

theorem bv_beq {x y : UInt64} : (x.toBitVec == y.toBitVec) = (x == y) := by
  cases h : (x == y)
  · cases h' : (x.toBitVec == y.toBitVec)
    · rfl
    · exact absurd (UInt64.toBitVec_inj.mp (beq_iff_eq.mp h')) (by simpa using h)
  · rw [beq_iff_eq.mp h]; exact beq_self_eq_true _

theorem u64_toNat {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  rw [UInt64.toNat_toBitVec, Nat.toUInt64,
    UInt64.toNat_ofNat_of_lt' (show n < UInt64.size by simp [UInt64.size]; omega)]

theorem u64_toNat' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  rw [← UInt64.toNat_toBitVec]; exact u64_toNat h

variable {m0 : MachineData}

section
variable [Labels]

theorem eval_add_reg {m : MachineData} {rs : List (BitVec 64 × Nat)} {y : XReg} {c : Nat}
    {p : BitVec 64} (hy : (m.regs.getXReg y).toBitVec = p) :
    (Sym.bin .add .W64 (.reg y) (.lit c)).eval (Env.ofMachine m rs) = p + BitVec.ofNat 64 c := by
  simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, hy]

theorem eval_ptr0 {m : MachineData} {rs : List (BitVec 64 × Nat)} {o : Nat} :
    (Sym.ptr 0 (o : Int)).eval (Env.ofMachine m ((fb m0, 3360) :: rs)) = loc m0 o := by
  simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some, BitVec.ofInt_natCast]

/-- A register a block set to a register plus a literal. -/
theorem reg_add {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState} {x y : XReg}
    {c : Nat} (hm : Match (Env.ofMachine m rs) S st)
    (hx : S.reg x = some (.bin .add .W64 (.reg y) (.lit c))) {p : BitVec 64}
    (hy : (m.regs.getXReg y).toBitVec = p) :
    (st.regs.getXReg x).toBitVec = p + BitVec.ofNat 64 c := by
  rw [hm.regs x _ hx]; exact eval_add_reg hy

/-- **A frame word a block wrote.** -/
theorem wordOf_loc {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S st) {o : Nat} {v : Sym}
    (ho : o + 8 ≤ 3360) (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) {w : UInt64}
    (hv : v.eval (Env.ofMachine m ((fb m0, 3360) :: rs)) = w.toBitVec) :
    NativeRustcVm.wordOf st.dmem (loc m0 o) = w := by
  rw [NativeRustcVm.wordOf_of_wordAt (Sumcheck.Match.wordAt_write hm rfl ho hw), hv]

end

/-- `keccak_open`'s value from the words at SP. -/
theorem openValue_eq {st : MachineData} (hsp : st.regs.SP.toBitVec = fb m0) {x : EW}
    (h0 : NativeRustcVm.wordOf st.dmem (loc m0 0) = x.c0)
    (h8 : NativeRustcVm.wordOf st.dmem (loc m0 8) = x.c1) : openValue st = x := by
  obtain ⟨x0, x1⟩ := x
  have e0 : NativeRustcVm.wordOf st.dmem st.regs.SP.toBitVec = x0 := by
    rw [hsp, show fb m0 = loc m0 0 from (NativeRustcVm.addr_add_zero _).symm]; exact h0
  have e8 : NativeRustcVm.wordOf st.dmem (st.regs.SP.toBitVec + BitVec.ofNat 64 8) = x1 := by
    rw [hsp]; exact h8
  unfold openValue
  rw [e0, e8]

/-- `keccak_open`'s slot point's address from the word at SP + 16. -/
theorem openSlot_eq {st : MachineData} (hsp : st.regs.SP.toBitVec = fb m0) {p : BitVec 64}
    (h : NativeRustcVm.wordOf st.dmem (loc m0 16) = UInt64.ofBitVec p) : openSlot st = p := by
  unfold openSlot; rw [hsp]; exact congrArg UInt64.toBitVec h

/-- `keccak_open`'s rows' address from the word at SP + 24. -/
theorem openRows_eq {st : MachineData} (hsp : st.regs.SP.toBitVec = fb m0) {p : BitVec 64}
    (h : NativeRustcVm.wordOf st.dmem (loc m0 24) = UInt64.ofBitVec p) : openRows st = p := by
  unfold openRows; rw [hsp]; exact congrArg UInt64.toBitVec h

section
variable [Labels] {a : DecArea} {inst : Array EW} {st : MachineData}

omit [Labels] in
/-- A part of a region the entry's facts make data memory, from an offset. -/
theorem ok_off {A : BitVec 64} {N : Nat} (hm : Mapped m0.dmem A N) (hw : A.toNat + N ≤ 2 ^ 64)
    (hfr : VFr m0 st) {o n : Nat} (h0 : 0 < n) (hn : o + n ≤ N) :
    NativeRustcVm.Region.Ok st.dmem ⟨A + BitVec.ofNat 64 o, n⟩ :=
  ⟨mapped_of hm hfr hn, by
    show (A + BitVec.ofNat 64 o).toNat + n ≤ 2 ^ 64
    rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega⟩

theorem scN (hn : Nums a inst m0) {o : Nat} (ho : o < 205824) :
    (scA m0 + BitVec.ofNat 64 o).toNat = (scA m0).toNat + o :=
  NativeRustcVm.toNat_add_ofNat (by have := hn.sW; omega)

theorem oN (hn : Nums a inst m0) {o : Nat} (ho : o < 1608) :
    (oA m0 + BitVec.ofNat 64 o).toNat = (oA m0).toNat + o :=
  NativeRustcVm.toNat_add_ofNat (by have := hn.oW; omega)

end

/-- `Mid` across a block without writes, `Regs`'s registers kept. -/
theorem Mid.of_dmem [Labels] {m m' : MachineData} (h : Mid m0 m) (hfr : VFr m0 m')
    (hd : m'.dmem = m.dmem) (hregs : ∀ r ∈ regsL, m'.regs.getXReg r = m.regs.getXReg r) :
    Mid m0 m' :=
  ⟨hfr, h.regs.of_eq hregs, by rw [hd]; exact h.pk⟩

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW}

/-- **A branch to the failure exit** from a state of the frame, taken when `b` is false; the
registers `L` kept. -/
theorem failBranchF (hp : Placed code k) (hn : Nums a inst m0) {ds : List Directive} {i : Nat}
    {S' : SState} {c : SBool} {m : MachineData} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .cond c NativeRustcVmArm.Vm.VerifyKeccak.label_31)) (hfr : VFr m0 m)
    (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0) {L : List XReg}
    (hrk : L.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    {b : Bool} (hc : c.eval (envM m0 m) = !b) (hfail : b = false → run0 s inst output m0 = none)
    (cont : b = true → ∀ m', VFr m0 m' → m'.dmem = m.dmem →
      (∀ r ∈ L, m'.regs.getXReg r = m.regs.getXReg r) →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf i⟩ := by
  refine blockStep hn hk hrun hfr hmem hsp fun st hm1 hfr1 hd hpc ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only [PcOk, hc] at hpc
  cases b
  · simp only [Bool.not_false, ↓reduceIte] at hpc
    subst hpc
    exact goal_fail hp hn hfr1 (hfail rfl)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    subst hpc
    exact cont rfl d hfr1 hd fun r hr ↦ Match.regs_keep (matchM hn hfr) hm1 L hrk r hr

end

/-- `apart_auto` with the scratch's and the `KeccakOutW`'s offsets as numbers. -/
macro "apart_vk " hn:term:max hfr:term:max : tactic => `(tactic| (
  try unfold NativeRustcVm.Apart
  try unfold NativeRustcArm.Apart
  try simp only [NativeRustcVmArm.stackRegion, NativeRustcVm.Transcript.DecArea.region,
    NativeRustcVmArm.rcRegion, NativeRustcVmArm.projectRegion, NativeRustcVmArm.rhoRegion]
  try simp only [NativeRustcVmArm.ewsRegion, NativeVm.Math.Keccak.qkeccakSlotBits_eq]
  try simp only [NativeRustcVm.Transcript.tstateBytes, NativeRustcVm.Layout.claimsBytes,
    NativeRustcVm.KeccakGkr.scratchBytes, NativeRustcVm.KeccakGkr.outBytes,
    NativeRustcVm.KeccakGkr.claimBytes, NativeRustcVm.KeccakGkr.weightsBytes,
    NativeRustcVm.KeccakGkr.rowsBytes]
  try simp (disch := decide) only [NativeRustcVmArm.KeccakGkr.VerifyKeccak.sb_toNat ($hn).hN $hfr]
  try simp (disch := decide) only [NativeRustcVmArm.KeccakGkr.VerifyKeccak.loc_toNat ($hn).hN]
  try simp (disch := decide) only [NativeRustcVmArm.KeccakGkr.VerifyKeccak.scN $hn]
  try simp (disch := decide) only [NativeRustcVmArm.KeccakGkr.VerifyKeccak.oN $hn]
  have := ($hn).hN
  try omega
  try (have := ($hn).tS; omega)
  try (have := ($hn).sS; omega)
  try (have := ($hn).cS; omega)
  try (have := ($hn).oS; omega)
  try (have := ($hn).wS; omega)
  try (have := ($hn).iS; omega)
  try (have := ($hn).rcS; omega)
  try (have := ($hn).txs; omega)
  try (have := ($hn).txc; omega)
  try (have := ($hn).txo; omega)
  try (have := ($hn).sxc; omega)
  try (have := ($hn).sxo; omega)
  try (have := ($hn).cxo; omega)
  try (have := ($hn).t_w; omega)
  try (have := ($hn).t_rc; omega)
  try (have := ($hn).s_w; omega)
  try (have := ($hn).s_rc; omega)
  try (have := ($hn).c_w; omega)
  try (have := ($hn).c_i; omega)
  try (have := ($hn).o_w; omega)
  try (have := ($hn).o_rc; omega)))

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
