module

public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Wire.ReaderLe.Exec
public import NativeRustcVmArm.Wire.ReaderLe.Value
public import NativeRustcVmArm.Spec.Wire
public import NativeRustcVm.Wire.ReaderFacts
import NativeVm.Wire.Read

/-!
# `Reader::le` meets its contract

`readerLe_spec`: the read of `n ∈ {4, 8}` bytes from the cursor `c` fits (`c + n ≤ L`): the
blocks from `okS n` load the bytes (region 1, at the bytes' address plus the cursor), store the
new cursor and assemble the word (`leNat`, `Value`); it does not: `b0` branches to `b1`, `None`.
-/

namespace NativeRustcVmArm.Wire.ReaderLe

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Vm.ReaderLe

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-- `Reader::le`'s first branch: to the read exactly when it fits (no carry, within the length). -/
theorem fits_eval [Labels] (env : Env) (C N L : Sym) :
    (SBool.not (SBool.bit .W32 (Sym.ite
      (SBool.or (SBool.cmp .ult .W64 (Sym.bin .add .W64 C N) L)
        (SBool.cmp .eq .W64 (Sym.bin .add .W64 C N) L))
      (Sym.un .trunc .W32 (Sym.ite (SBool.not (SBool.cmp .addC .W64 C N)) (Sym.lit 0) (Sym.lit 1)))
      (Sym.lit 1)) 0)).eval env =
      decide ((C.eval env).toNat + (N.eval env).toNat ≤ (L.eval env).toNat) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, UnOp.apply, Sym.low_W64,
    Sym.ext_W64, Sym.low_W32, Sym.ext_W32, BitVec.ult, BitVec.unsigned]
  have hC := (C.eval env).isLt
  have hN := (N.eval env).isLt
  have hL := (L.eval env).isLt
  generalize C.eval env = c at *
  generalize N.eval env = n at *
  generalize L.eval env = l at *
  have hb1 : (BitVec.setWidth 32 (1#64)).getLsbD 0 = true := by decide
  have hb0 : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (0#64)))).getLsbD 0 = false := by
    decide
  have hb1' : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (1#64)))).getLsbD 0 = true := by
    decide
  by_cases hcarry : c.toNat + n.toNat < 2 ^ 64
  · have hadd : (c + n).toNat = c.toNat + n.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hcarry]
    have hQ : (!((((c + n).toNat : Nat) : Int) != ((c.toNat : Nat) : Int) + ((n.toNat : Nat) : Int))) =
        true := by simp [hadd]
    by_cases hfit : c.toNat + n.toNat ≤ l.toNat
    · have hP : (decide ((c + n).toNat < l.toNat) || (c + n == l)) = true := by
        rcases Nat.lt_or_eq_of_le hfit with h | h
        · simp [hadd, h]
        · have : c + n = l := BitVec.eq_of_toNat_eq (by omega)
          simp [this]
      simp only [hP, hQ, ↓reduceIte, hb0, decide_eq_true hfit]
      rfl
    · have hP : (decide ((c + n).toNat < l.toNat) || (c + n == l)) = false := by
        have h1 : ¬ (c + n).toNat < l.toNat := by omega
        have h2 : (c + n == l) = false := beq_eq_false_iff_ne.mpr fun h ↦ hfit (by rw [← h, hadd])
        rw [decide_eq_false h1, h2]
        rfl
      simp only [hP, Bool.false_eq_true, ↓reduceIte, hb1, decide_eq_false hfit]
      rfl
  · have hQ : (!((((c + n).toNat : Nat) : Int) != ((c.toNat : Nat) : Int) + ((n.toNat : Nat) : Int))) =
        false := by
      have : (c + n).toNat ≠ c.toNat + n.toNat := by
        have := (c + n).isLt
        omega
      have h' : (((c + n).toNat : Nat) : Int) ≠ ((c.toNat : Nat) : Int) + ((n.toNat : Nat) : Int) := by
        omega
      simpa [bne_iff_ne] using h'
    have hfit : ¬ c.toNat + n.toNat ≤ l.toNat := by omega
    rw [decide_eq_false hfit]
    split
    · simp only [hQ, Bool.false_eq_true, ↓reduceIte, hb1']
      rfl
    · rw [hb1]
      rfl

theorem toBitVec_toUInt64_toNat {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  rw [UInt64.toNat_toBitVec, toNat_toUInt64_of_lt h]

/-- The postcondition from the reader's own bytes and cursor. -/
theorem post_of [Labels] {m m' : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m.dmem m.regs.X0.toBitVec bp B c)
    (hres : match rdLe B c m.regs.X1.toNat with
      | some (v, c') => m'.regs.X0 = 1 ∧ m'.regs.X1 = v ∧ ReaderAt m'.dmem m.regs.X0.toBitVec bp B c'
      | none => m'.regs.X0 = 0)
    (hs : NativeRustcVm.SameOutside m.dmem m'.dmem (curRegion m.regs.X0.toBitVec).Holds) (hsv : Saved m m') :
    ReaderLePost m m' := by
  refine ⟨fun bp' B' c' hR' ↦ ?_, hs, hsv⟩
  obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
  exact hres

variable [Host] {k : Nat}

/-- What `Reader::le` reaches: its postcondition at the return address. -/
abbrev Post (m : MachineData) (st : MachineState) : Prop := st.pc = retOf m ∧ ReaderLePost m st.data

/-- **The read does not fit**: `None`. -/
theorem fail_spec (hp : Placed code k) {m : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m.dmem m.regs.X0.toBitVec bp B c) (hfit : ¬ c + m.regs.X1.toNat ≤ B.length) :
    Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.ReaderLe.b0Offset)⟩ := by
  let env := Env.ofMachine m [(m.regs.X0.toBitVec, 24)]
  have hwf : env.WF := Env.wf_of ⟨hR.ok, trivial⟩ (List.pairwise_singleton _ _)
  have hb0 : env.base 0 = m.regs.X0.toBitVec := Env.base_ofMachine m _ _ rfl
  have hm : Match env failS m := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  have hx1 : env.regs .X1 = m.regs.X1.toBitVec := rfl
  have hL := hR.len_lt
  have hlen : env.load 0 8 8 = B.length.toUInt64.toBitVec := load_word (by rw [hb0]; exact hR.len)
  have hcur : env.load 0 16 8 = c.toUInt64.toBitVec := load_word (by rw [hb0]; exact hR.cur)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_f0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [fits_eval] at hpc1
  simp only [Sym.eval, hlen, hcur, hx1, toBitVec_toUInt64_toNat hL,
    toBitVec_toUInt64_toNat (show c < 2 ^ 64 by have := hR.c_le; omega), UInt64.toNat_toBitVec,
    decide_eq_false hfit, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmArm.Vm.ReaderLe.b0Offset + b0.length = k + NativeRustcVmArm.Vm.ReaderLe.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReaderLe.b0_next]] at hpc1
  have run := run_f1
  rw [after_eq run_f0] at run
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run hwf hpc1 hm1 fun s2 hm2 hpc2 ↦
    .done _ ⟨?_, ?_⟩
  · have h30 : s2.data.regs.X30 = m.regs.X30 := Match.reg_eq (r := .X30) hm hm2 rfl rfl
    simp only [PcOk] at hpc2
    rw [hpc2, retOf, retOf, h30]
  · have hd : s2.data.dmem = m.dmem := hm2.dmem_eq hwf rfl
    refine post_of hR ?_ (fun p _ ↦ by rw [hd]) (Match.saved hm hm2 hwf rfl (by decide))
    simp only [rdLe, hfit, ↓reduceIte]
    apply UInt64.toBitVec_inj.mp
    exact hm2.regs .X0 _ rfl

/-- The read of `n` bytes fits: the reader (region 0) and the bytes read (region 1). -/
abbrev okEnv (m : MachineData) (bp : BitVec 64) (c n : Nat) : Env :=
  Env.ofMachine m [(m.regs.X0.toBitVec, 24), (bp + BitVec.ofNat 64 c, n)]

section Ok

variable {m : MachineData} {bp : BitVec 64} {B : List UInt8} {c n : Nat}
  (hR : ReaderAt m.dmem m.regs.X0.toBitVec bp B c) (hfit : c + n ≤ B.length)
include hR hfit

omit [Host] in
theorem ok_window (hn : 0 < n) : NativeRustcVm.NoWrap (bp + BitVec.ofNat 64 c) n ∧
    (bp + BitVec.ofNat 64 c).toNat = bp.toNat + c := by
  have hnw := hR.noWrap
  unfold NativeRustcVm.NoWrap at hnw ⊢
  have : (bp + BitVec.ofNat 64 c).toNat = bp.toNat + c :=
    NativeRustcVm.toNat_add_ofNat (by have := hR.len_lt; omega)
  exact ⟨by omega, this⟩

omit [Host] in
theorem ok_wf (hn : 0 < n) : (okEnv m bp c n).WF := by
  obtain ⟨hw, hwn⟩ := ok_window hR hfit hn
  refine Env.wf_of ⟨hR.ok, ⟨fun i hi ↦ ?_, hw⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  · rw [addr_add_add]
    exact hR.bytes.mapped _ (by omega)
  · have hap := hR.apart (by omega)
    unfold NativeRustcVm.Apart at hap
    show NativeRustcArm.Apart _ _ _ _
    unfold NativeRustcArm.Apart
    dsimp only
    omega

omit [Host] in
theorem ok_byte {i : Nat} (hi : i < n) :
    ((okEnv m bp c n).load 1 i 1).toNat = (B.getD (c + i) 0).toNat := by
  refine load_byte ?_
  rw [Env.base_ofMachine m _ _ rfl, addr_add_add, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact hR.bytes _ (by omega)

omit hfit in
theorem ok_match (hx1 : m.regs.X1.toNat = n) : Match (okEnv m bp c n) (okS n) m := by
  have hb0 : (okEnv m bp c n).base 0 = m.regs.X0.toBitVec := Env.base_ofMachine m _ _ rfl
  have hb1 : (okEnv m bp c n).base 1 = bp + BitVec.ofNat 64 c := Env.base_ofMachine m _ _ rfl
  have hptr : (okEnv m bp c n).load 0 0 8 = bp :=
    load_word (by rw [hb0, NativeRustcVm.addr_add_zero]; exact hR.ptr)
  have hcur : (okEnv m bp c n).load 0 16 8 = c.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.cur)
  refine match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
    ⟨by simp [Sym.eval]; rfl, ?_, trivial⟩ trivial trivial ⟨?_, trivial⟩
  · show m.regs.X1.toBitVec = BitVec.ofNat 64 n
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := m.regs.X1.toNat_lt; omega)]
  · show (Sym.bin .add .W64 (.load 0 0 8) (.load 0 16 8)).eval (okEnv m bp c n) = _
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, hptr, hcur, hb1]
    rw [BitVec.ofInt_ofNat, BitVec.add_zero]
    congr 1

theorem ok_branch (hx1 : m.regs.X1.toNat = n) :
    (SBool.not (SBool.bit .W32 (Sym.ite
      (SBool.or (SBool.cmp .ult .W64 (Sym.bin .add .W64 (.load 0 16 8) (.lit n)) (.load 0 8 8))
        (SBool.cmp .eq .W64 (Sym.bin .add .W64 (.load 0 16 8) (.lit n)) (.load 0 8 8)))
      (Sym.un .trunc .W32 (Sym.ite (SBool.not (SBool.cmp .addC .W64 (.load 0 16 8) (.lit n)))
        (Sym.lit 0) (Sym.lit 1)))
      (Sym.lit 1)) 0)).eval (okEnv m bp c n) = true := by
  have hb0 : (okEnv m bp c n).base 0 = m.regs.X0.toBitVec := Env.base_ofMachine m _ _ rfl
  have hL := hR.len_lt
  have hlen : (okEnv m bp c n).load 0 8 8 = B.length.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.len)
  have hcur : (okEnv m bp c n).load 0 16 8 = c.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.cur)
  have hn64 : n < 2 ^ 64 := by have := m.regs.X1.toNat_lt; omega
  rw [fits_eval]
  simp only [Sym.eval, hlen, hcur, toBitVec_toUInt64_toNat hL,
    toBitVec_toUInt64_toNat (show c < 2 ^ 64 by have := hR.c_le; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn64]
  exact decide_eq_true hfit

/-- **The end of a read that fits**: `Some` of the word, the cursor advanced. -/
theorem ok_finish (hx1 : m.regs.X1.toNat = n) {S : SState} {st : MachineState} {next : Int64}
    (hwf : (okEnv m bp c n).WF) (hm : Match (okEnv m bp c n) (okS n) m)
    (hmS : Match (okEnv m bp c n) S st.data) (hpc : PcOk (okEnv m bp c n) .ret next st)
    (hmem : S.mem = [⟨0, 16, 8, .bin .add .W64 (.load 0 16 8) (.lit n)⟩])
    (hkeep : keeps (okS n) S = true) (h0 : S.reg .X0 = some (.lit 1))
    (h30 : S.reg .X30 = some (.reg .X30)) (hv : st.data.regs.X1 = leAt B c n) : Post m st := by
  have hb0 : (okEnv m bp c n).base 0 = m.regs.X0.toBitVec := Env.base_ofMachine m _ _ rfl
  have hcur : (okEnv m bp c n).load 0 16 8 = c.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.cur)
  have h30' : st.data.regs.X30 = m.regs.X30 := Match.reg_eq (r := .X30) hm hmS rfl h30
  refine ⟨by simp only [PcOk] at hpc; rw [hpc, retOf, retOf, h30'], ?_⟩
  have hs : NativeRustcVm.SameOutside m.dmem st.data.dmem (curRegion m.regs.X0.toBitVec).Holds :=
    Match.sameOutside_in hmS hwf (r0 := 0) (b := m.regs.X0.toBitVec) (sz := 24) (o := 16) (n := 8)
      rfl (by omega) (by simp [hmem])
  have hw := hmS.bytesAt_write (r := 0) (o := 16) (n := 8) (b := m.regs.X0.toBitVec) (sz := 24) rfl
    (by omega) (v := .bin .add .W64 (.load 0 16 8) (.lit n))
    (fun i hi ↦ by rw [hmem]; exact findWrite_head hi)
  rw [byteOf_range] at hw
  have hval : UInt64.ofBitVec ((Sym.bin .add .W64 (.load 0 16 8) (.lit n)).eval (okEnv m bp c n)) =
      (c + n).toUInt64 := by
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, hcur]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
      Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [hval] at hw
  refine post_of hR ?_ hs (Match.saved hm hmS hwf rfl hkeep)
  simp only [rdLe, hx1, hfit, ↓reduceIte]
  exact ⟨UInt64.toBitVec_inj.mp (hmS.regs .X0 _ h0), hv, hR.update hs hw (by omega)⟩

end Ok

theorem lbl (hp : Placed code k) {j : Nat} {l : Label} (h : Vm.ReaderLe.code[j]? = some (.label l)) :
    Labels.label l = Host.addrOf (k + j) :=
  hp.label h

/-- **Four bytes**: `b0`, `b2`, `b3`. -/
theorem ok4_spec (hp : Placed code k) {m : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m.dmem m.regs.X0.toBitVec bp B c) (hx1 : m.regs.X1.toNat = 4)
    (hfit : c + 4 ≤ B.length) :
    Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.ReaderLe.b0Offset)⟩ := by
  have hwf := ok_wf hR hfit (by omega)
  have hm := ok_match hR hx1
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_a0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, ok_branch hR hfit hx1, ↓reduceIte, lbl hp (j := 9) rfl] at hpc1
  have r2 := run_a2
  rw [after_eq run_a0] at r2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) r2 hwf hpc1 hm1 fun s2 hm2 hpc2 ↦ ?_
  simp only [PcOk, SBool.eval, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmArm.Vm.ReaderLe.b2Offset + b2.length = k + NativeRustcVmArm.Vm.ReaderLe.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReaderLe.b2_next]] at hpc2
  have r3 := run_a3
  rw [after_eq run_a2] at r3
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) r3 hwf hpc2 hm2 fun s3 hm3 hpc3 ↦ ?_
  refine .done _ (ok_finish hR hfit hx1 hwf hm hm3 hpc3 rfl (by decide) rfl rfl ?_)
  apply UInt64.toBitVec_inj.mp
  rw [show s3.data.regs.X1.toBitVec = (hornerSym 0 0).eval (okEnv m bp c 4) from hm3.regs .X1 _ rfl]
  apply BitVec.eq_of_toNat_eq
  rw [eval_horner _ B c 0 0 (by omega) fun i hi ↦ by rw [ok_byte hR hfit (by omega), Nat.zero_add, Nat.add_zero],
    leAt, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by
      have := leNat_lt B c 4; norm_num at this ⊢; omega)]
  rfl

/-- **Eight bytes**: `b0`, `b2`, `b4`, `b6`, `b8`, `b10`. -/
theorem ok8_spec (hp : Placed code k) {m : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m.dmem m.regs.X0.toBitVec bp B c) (hx1 : m.regs.X1.toNat = 8)
    (hfit : c + 8 ≤ B.length) :
    Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.ReaderLe.b0Offset)⟩ := by
  have hwf := ok_wf hR hfit (by omega)
  have hm := ok_match hR hx1
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, ok_branch hR hfit hx1, ↓reduceIte, lbl hp (j := 9) rfl] at hpc1
  have r2 := run_b2
  rw [after_eq run_b0] at r2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) r2 hwf hpc1 hm1 fun s2 hm2 hpc2 ↦ ?_
  simp only [PcOk, SBool.eval, ↓reduceIte, lbl hp (j := 27) rfl] at hpc2
  have r4 := run_b4
  rw [after_eq run_b2] at r4
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) r4 hwf hpc2 hm2 fun s4 hm4 hpc4 ↦ ?_
  simp only [PcOk, SBool.eval, ↓reduceIte, lbl hp (j := 34) rfl] at hpc4
  have r6 := run_b6
  rw [after_eq run_b4] at r6
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) r6 hwf hpc4 hm4 fun s6 hm6 hpc6 ↦ ?_
  simp only [PcOk, SBool.eval, ↓reduceIte, lbl hp (j := 41) rfl] at hpc6
  have r8 := run_b8
  rw [after_eq run_b6] at r8
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) r8 hwf hpc6 hm6 fun s8 hm8 hpc8 ↦ ?_
  simp only [PcOk, SBool.eval, ↓reduceIte, lbl hp (j := 48) rfl] at hpc8
  have r10 := run_b10
  rw [after_eq run_b8] at r10
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) r10 hwf hpc8 hm8 fun s10 hm10 hpc10 ↦ ?_
  refine .done _ (ok_finish hR hfit hx1 hwf hm hm10 hpc10 rfl (by decide) rfl rfl ?_)
  apply UInt64.toBitVec_inj.mp
  rw [show s10.data.regs.X1.toBitVec = (hornerSym 0 4).eval (okEnv m bp c 8) from
    hm10.regs .X1 _ rfl]
  apply BitVec.eq_of_toNat_eq
  rw [eval_horner _ B c 4 0 (by omega) fun i hi ↦ by rw [ok_byte hR hfit (by omega), Nat.zero_add, Nat.add_zero],
    leAt, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by
      have := leNat_lt B c 8; norm_num at this ⊢; omega)]
  rfl

/-- **`Reader::le` meets its contract.** -/
theorem readerLe_spec (hp : Placed code k) : Spec (label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost := by
  intro m ⟨_, hn, bp, B, c, hR⟩
  rw [lbl hp (j := 0) (l := NativeRustcVmArm.Vm.ReaderLe.entryLabel) rfl]
  by_cases hfit : c + m.regs.X1.toNat ≤ B.length
  · rcases hn with hn | hn
    · exact ok4_spec hp hR hn (by omega)
    · exact ok8_spec hp hR hn (by omega)
  · exact fail_spec hp hR hfit

end

end NativeRustcVmArm.Wire.ReaderLe
