module

public import NativeRustcVmX64.Wire.ReaderLe.Exec
public import NativeRustcVmX64.Wire.Common
public import NativeRustcVmX64.Spec.Wire
public import NativeRustcVm.Wire.ReaderFacts
import NativeVm.Wire.Read
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `Reader::le` meets its contract (x86-64)

`readerLe_spec`: the read of `n ∈ {4, 8}` bytes from the cursor `c` fits (`c + n ≤ L`): the
blocks from `okS n` store the new cursor and load the bytes (region 1, at the bytes' address plus
the cursor): for `n = 4` the 32-bit word (`b2`), for `n = 8` the upper 32-bit word, then each lower
byte shifted in (`b3` to `b6`), `leNat` of them; it does not: `b0` (a carry) or `b1` branch to the
return with RAX `0`. The final `retq` (`b7`) runs from `sRet` (`ret_keep`).
-/

namespace NativeRustcVmX64.Wire.ReaderLe

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ReaderLe

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-- `addq`'s carry. -/
theorem carry_apply (x y : BitVec 64) :
    CmpOp.apply .addC .W64 x y = decide (2 ^ 64 ≤ x.toNat + y.toNat) := by
  simp only [CmpOp.apply, low_W64, BitVec.unsigned]
  rw [BitVec.toNat_add, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat
  · rw [decide_eq_true h]
    simp only [bne_iff_ne, ne_eq]
    omega
  · rw [decide_eq_false h, Nat.mod_eq_of_lt (by omega)]
    simp

/-- `ja`: above. -/
theorem above_apply (x y : BitVec 64) :
    (!CmpOp.apply .ult .W64 x y && !CmpOp.apply .eq .W64 x y) = decide (y.toNat < x.toNat) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult]
  by_cases h : x = y
  · subst h
    simp
  · have h' : x.toNat ≠ y.toNat := fun e ↦ h (BitVec.eq_of_toNat_eq e)
    rw [show (x == y) = false from beq_eq_false_iff_ne.mpr h]
    by_cases hl : x.toNat < y.toNat
    · simp [hl]
      omega
    · simp [hl]
      omega

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  rw [UInt64.toNat_toBitVec, toNat_toUInt64_of_lt h]

/-- One step of the assembly: a byte below the word shifted by 8. -/
@[expose] def stepSym (o : Nat) (x : Sym) : Sym :=
  .bin .or .W64 (.bin .shl .W64 x (.lit 8)) (.un (.zext .W8) .W32 (.load 1 o 1))

/-- The eight bytes as the assembly assembles them. -/
@[expose] def word8Sym : Sym := stepSym 0 (stepSym 1 (stepSym 2 (stepSym 3 (.load 1 4 4))))

theorem eval_step [Labels] (env : Env) (B : List UInt8) (p o q j : Nat) (x : Sym) (hj : j ≤ 7)
    (hq : q = p + o + 1) (hx : (x.eval env).toNat = leNat B q j)
    (hy : (env.load 1 o 1).toNat = (B.getD (p + o) 0).toNat) :
    ((stepSym o x).eval env).toNat = leNat B (p + o) (j + 1) := by
  subst hq
  have hlt := leNat_lt B (p + o + 1) j
  have hp : 256 ^ j ≤ 2 ^ 56 :=
    (Nat.pow_le_pow_right (by omega) (show j ≤ 7 by omega)).trans (by norm_num)
  have hb := (B.getD (p + o) 0).toNat_lt
  have hz : (UnOp.apply (.zext .W8) .W32 (env.load 1 o 1)).toNat = (B.getD (p + o) 0).toNat := by
    simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth, Width.bits]
    omega
  have hs : (BinOp.apply .shl .W64 (x.eval env) (BitVec.ofNat 64 8)).toNat =
      (x.eval env).toNat * 2 ^ 8 := by
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [show shiftCount .W64 (BitVec.ofNat 64 8) = 8 by decide]
    exact toNat_shl (by omega)
  simp only [stepSym, Sym.eval]
  rw [show ∀ a b : BitVec 64, BinOp.apply .or .W64 a b = b ||| a from fun a b ↦ by
      simp only [BinOp.apply, low_W64, ext_W64]; exact BitVec.or_comm _ _,
    toNat_or_add (k := 8) (by omega) (by rw [hs]; exact Nat.dvd_mul_left _ _), hz, hs, hx,
    leNat_cons]
  omega

theorem eval_word8 [Labels] (env : Env) (B : List UInt8) (p : Nat)
    (hy : ∀ i < 8, env.mem0.get? (env.base 1 + BitVec.ofNat 64 i) = some (B.getD (p + i) 0)) :
    (word8Sym.eval env).toNat = leNat B p 8 := by
  have hb : ∀ o < 4, (env.load 1 o 1).toNat = (B.getD (p + o) 0).toNat := fun o ho ↦
    load_byte (by rw [hy o (by omega)])
  have h4 : (env.load 1 4 4).toNat = leNat B (p + 4) 4 :=
    load_le (by omega) fun i hi ↦ by rw [hy (4 + i) (by omega), Nat.add_assoc]
  have e3 := eval_step env B p 3 (p + 4) 4 (.load 1 4 4) (by omega) (by omega)
    (by rw [Sym.eval, h4]) (hb 3 (by omega))
  have e2 := eval_step env B p 2 (p + 3) 5 _ (by omega) (by omega) e3 (hb 2 (by omega))
  have e1 := eval_step env B p 1 (p + 2) 6 _ (by omega) (by omega) e2 (hb 1 (by omega))
  have e0 := eval_step env B p 0 (p + 1) 7 _ (by omega) (by omega) e1 (hb 0 (by omega))
  exact e0

/-- The postcondition from the reader's own bytes and cursor. -/
theorem post_of [Labels] {m m' : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m.dmem (reg m .rdi) bp B c)
    (hres : match rdLe B c (reg m .rsi).toNat with
      | some (v, c') => reg m' .rax = 1 ∧ reg m' .rdx = v.toBitVec ∧
          ReaderAt m'.dmem (reg m .rdi) bp B c'
      | none => reg m' .rax = 0)
    (hs : NativeRustcVm.SameOutside m.dmem m'.dmem (curRegion (reg m .rdi)).Holds)
    (hsv : Saved m m') : ReaderLePost m m' := by
  refine ⟨fun bp' B' c' hR' ↦ ?_, hs, hsv⟩
  obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
  exact hres

variable [Host] {k : Nat}

/-- What `Reader::le` reaches: its postcondition at the return address, RSP 8 above. -/
abbrev Post (m : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧ ReaderLePost m st.data

theorem lbl (hp : Placed code k) {j : Nat} {l : Label} (h : Vm.ReaderLe.code[j]? = some (.label l)) :
    Labels.label l = Host.addrOf (k + j) :=
  hp.label h

/-- **The return** from `NativeRustcVmX64.Vm.ReaderLe.label_7` (`b7`), memory changed at most in the cursor word, with
the result's registers. -/
theorem finish (hp : Placed code k) {m : MachineData} {st : MachineState} (hstk : StackOk m 0)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderLe.b7Offset)) (hsp : st.data.regs.get64 .rsp = rspOf m)
    (hap : NativeRustcVm.Apart (reg m .rdi) 24 (rspOf m) 8)
    (hnw : NativeRustcVm.NoWrap (reg m .rdi) 24)
    (hs : NativeRustcVm.SameOutside m.dmem st.data.dmem (curRegion (reg m .rdi)).Holds)
    (hsv : Saved m st.data) {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m.dmem (reg m .rdi) bp B c)
    (hres : match rdLe B c (reg m .rsi).toNat with
      | some (v, c') => reg st.data .rax = 1 ∧ reg st.data .rdx = v.toBitVec ∧
          ReaderAt st.data.dmem (reg m .rdi) bp B c'
      | none => reg st.data .rax = 0) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hslot : ∀ i < 8, st.data.dmem.get? (rspOf m + BitVec.ofNat 64 i) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 i) := fun i hi ↦ by
    refine hs _ fun hin ↦ ?_
    have hst := hstk.2.1
    unfold NativeRustcVm.Apart at hap
    unfold NativeRustcVm.NoWrap at hnw
    have h16 : (reg m .rdi + BitVec.ofNat 64 16).toNat = (reg m .rdi).toNat + 16 :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    have hi' : (rspOf m + BitVec.ofNat 64 i).toNat = (rspOf m).toNat + i :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    change InRange (reg m .rdi + BitVec.ofNat 64 16) 8 _ at hin
    rw [NativeRustcX64.Sym.inRange_iff (by omega), h16, hi'] at hin
    omega
  refine Eventually.mono (ret_keep (infix_of b7_in_code (by simp [b7]) hp) run_ret rfl rfl
    (by decide) hpc hstk hsp hslot) fun st' ⟨hpc', hrsp', hd', hr', hsv'⟩ ↦ ⟨hpc', hrsp', ?_⟩
  have hrax : reg st'.data .rax = reg st.data .rax := hr' .rax _ rfl
  have hrdx : reg st'.data .rdx = reg st.data .rdx := hr' .rdx _ rfl
  refine post_of hR ?_ (fun p hp' ↦ by rw [hd']; exact hs p hp')
    ⟨fun r hr ↦ (hsv'.1 r hr).trans (hsv.1 r hr), fun p h ↦ hsv'.2 p (hsv.2 p h)⟩
  rw [hrax, hrdx, hd']
  exact hres

/-- **The read does not fit**: `None`. -/
theorem fail_spec (hp : Placed code k) {m : MachineData} {bp : BitVec 64} {B : List UInt8}
    {c : Nat} (hstk : StackOk m 0) (hR : ReaderAt m.dmem (reg m .rdi) bp B c)
    (hap : NativeRustcVm.Apart (reg m .rdi) 24 (rspOf m) 8)
    (hfit : ¬ c + (reg m .rsi).toNat ≤ B.length) :
    Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.ReaderLe.b0Offset)⟩ := by
  let env := Env.ofMachine m [(reg m .rdi, 24)]
  have hwf : env.WF := Env.wf_of ⟨hR.ok, trivial⟩ (List.pairwise_singleton _ _)
  have hb0 : env.base 0 = reg m .rdi := Env.base_ofMachine m _ _ _ rfl
  have hm : Match env failS m := match_ofMachine ⟨rfl, trivial⟩
    ⟨by simp [Sym.eval], trivial⟩ trivial trivial trivial
  have hL := hR.len_lt
  have hlen : env.load 0 8 8 = B.length.toUInt64.toBitVec := load_word (by rw [hb0]; exact hR.len)
  have hcur : env.load 0 16 8 = c.toUInt64.toBitVec := load_word (by rw [hb0]; exact hR.cur)
  have hc : c < 2 ^ 64 := by have := hR.c_le; omega
  have hrsi : env.regs .rsi = reg m .rsi := rfl
  have hfin : ∀ st, Match env (after b0 failS) st.data ∨ Match env (after b1 (after b0 failS))
      st.data → st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderLe.b7Offset) → Eventually (step1 Host.exe) (Post m) st := by
    intro st hmS hpc
    have hk : ∀ {S : SState}, Match env S st.data → S.mem = [] →
        S.reg .rsp = some (.reg .rsp) → S.reg .rax = some (.lit 0) → keeps failS S = true →
        Eventually (step1 Host.exe) (Post m) st := fun {S} hmS hmem hrsp hrax hkp ↦ by
      have hd : st.data.dmem = m.dmem := hmS.dmem_eq hwf hmem
      refine finish hp hstk hpc (Match.reg_eq hm hmS rfl hrsp) hap hR.ok.2
        (fun p _ ↦ by rw [hd]) (Match.saved hm hmS hwf rfl hkp) hR ?_
      simp only [rdLe, hfit, ↓reduceIte]
      exact hmS.regs .rax _ hrax
    rcases hmS with hmS | hmS
    · exact hk hmS (by rw [after_eq run_f0]) (by rw [after_eq run_f0]; rfl)
        (by rw [after_eq run_f0]; rfl) (by rw [after_eq run_f0]; decide)
    · exact hk hmS (by rw [after_eq run_f1]) (by rw [after_eq run_f1]; rfl)
        (by rw [after_eq run_f1]; rfl) (by rw [after_eq run_f1]; decide)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_f0 hwf nofun hm
    fun s1 hm1 hpc1 ↦ ?_
  have hm1' : Match env (after b0 failS) s1.data := by rw [after_eq run_f0]; exact hm1
  simp only [PcOk, SBool.eval, Sym.eval, carry_apply, hrsi, hcur, toNat_toUInt64 hc,
    hp.label NativeRustcVmX64.Vm.ReaderLe.label_7_at, show k + NativeRustcVmX64.Vm.ReaderLe.b0Offset + b0.length = k + NativeRustcVmX64.Vm.ReaderLe.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b0_next]] at hpc1
  by_cases hcy : 2 ^ 64 ≤ (reg m .rsi).toNat + c
  · simp only [decide_eq_true hcy, ↓reduceIte] at hpc1
    exact hfin s1 (.inl hm1') hpc1
  · rw [decide_eq_false hcy] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    have r1 := run_f1
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) r1 hwf nofun hpc1 hm1'
      fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, SBool.eval, Sym.eval, BinOp.apply, low_W64, ext_W64, above_apply, hrsi,
      hcur, hlen, hp.label NativeRustcVmX64.Vm.ReaderLe.label_7_at] at hpc2
    have hab : (B.length.toUInt64.toBitVec).toNat < (reg m .rsi + c.toUInt64.toBitVec).toNat := by
      rw [toNat_toUInt64 hL, BitVec.toNat_add, toNat_toUInt64 hc, Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [decide_eq_true hab, ↓reduceIte] at hpc2
    exact hfin s2 (.inr hm2) hpc2

/-- The read of `n` bytes fits: the reader (region 0) and the bytes read (region 1). -/
abbrev okEnv (m : MachineData) (bp : BitVec 64) (c n : Nat) : Env :=
  Env.ofMachine m [(reg m .rdi, 24), (bp + BitVec.ofNat 64 c, n)]

section Ok

variable {m : MachineData} {bp : BitVec 64} {B : List UInt8} {c n : Nat}
  (hR : ReaderAt m.dmem (reg m .rdi) bp B c) (hfit : c + n ≤ B.length)
include hR hfit

omit [Host] in
theorem ok_wf (hn : 0 < n) : (okEnv m bp c n).WF := by
  have hnw := hR.noWrap
  unfold NativeRustcVm.NoWrap at hnw
  have hw : (bp + BitVec.ofNat 64 c).toNat = bp.toNat + c :=
    NativeRustcVm.toNat_add_ofNat (by have := hR.len_lt; omega)
  refine Env.wf_of ⟨hR.ok, ⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  · rw [NativeRustcVm.addr_add_add]
    exact hR.bytes.mapped _ (by omega)
  · show (bp + BitVec.ofNat 64 c).toNat + n ≤ 2 ^ 64
    omega
  · have hap := hR.apart (by omega)
    unfold NativeRustcVm.Apart at hap
    show (reg m .rdi).toNat + 24 ≤ (bp + BitVec.ofNat 64 c).toNat ∨
      (bp + BitVec.ofNat 64 c).toNat + n ≤ (reg m .rdi).toNat
    omega

omit [Host] in
theorem ok_byte {i : Nat} (hi : i < n) :
    (okEnv m bp c n).mem0.get? ((okEnv m bp c n).base 1 + BitVec.ofNat 64 i) =
      some (B.getD (c + i) 0) := by
  rw [Env.base_ofMachine m _ _ _ rfl, NativeRustcVm.addr_add_add, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact hR.bytes _ (by omega)

omit hfit in
theorem ok_match (hx : (reg m .rsi).toNat = n) : Match (okEnv m bp c n) (okS n) m := by
  have hb0 : (okEnv m bp c n).base 0 = reg m .rdi := Env.base_ofMachine m _ _ _ rfl
  have hb1 : (okEnv m bp c n).base 1 = bp + BitVec.ofNat 64 c := Env.base_ofMachine m _ _ _ rfl
  have hptr : (okEnv m bp c n).load 0 0 8 = bp :=
    load_word (by rw [hb0, NativeRustcVm.addr_add_zero]; exact hR.ptr)
  have hcur : (okEnv m bp c n).load 0 16 8 = c.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.cur)
  have hcs : cursorSym.eval (okEnv m bp c n) = bp + BitVec.ofNat 64 c := by
    simp only [cursorSym, Sym.eval, BinOp.apply, low_W64, ext_W64, hptr, hcur]
    congr 1
  have hn : n < 2 ^ 64 := by have := (reg m .rsi).isLt; omega
  refine match_ofMachine ⟨rfl, rfl, trivial⟩
    ⟨by simp [Sym.eval], ?_, trivial⟩ trivial trivial ⟨?_, ?_, trivial⟩
  · show reg m .rsi = BitVec.ofNat 64 n
    apply BitVec.eq_of_toNat_eq
    rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  · show BinOp.apply .add .W64 (BitVec.ofNat 64 n) (cursorSym.eval _) = _
    simp only [BinOp.apply, low_W64, ext_W64, hcs, hb1, BitVec.ofInt_natCast]
    exact BitVec.add_comm _ _
  · show cursorSym.eval _ = _
    rw [hcs, hb1, BitVec.ofInt_ofNat, BitVec.add_zero]

/-- **The end of a read that fits**: `Some` of the word, the cursor advanced. -/
theorem ok_finish (hp : Placed code k) (hstk : StackOk m 0)
    (hap : NativeRustcVm.Apart (reg m .rdi) 24 (rspOf m) 8) (hx : (reg m .rsi).toNat = n)
    {S : SState} {st : MachineState} (hwf : (okEnv m bp c n).WF)
    (hm : Match (okEnv m bp c n) (okS n) m) (hmS : Match (okEnv m bp c n) S st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReaderLe.b7Offset))
    (hmem : S.mem = [⟨0, 16, 8, .bin .add .W64 (.lit n) (.load 0 16 8)⟩])
    (hkeep : keeps (okS n) S = true) (hrsp : S.reg .rsp = some (.reg .rsp))
    (h0 : S.reg .rax = some (.lit 1)) (hv : reg st.data .rdx = (leAt B c n).toBitVec) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hb0 : (okEnv m bp c n).base 0 = reg m .rdi := Env.base_ofMachine m _ _ _ rfl
  have hcur : (okEnv m bp c n).load 0 16 8 = c.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.cur)
  have hs : NativeRustcVm.SameOutside m.dmem st.data.dmem (curRegion (reg m .rdi)).Holds :=
    Match.sameOutside_in hmS hwf (r0 := 0) (b := reg m .rdi) (sz := 24) (o := 16) (n := 8)
      rfl (by omega) (by simp [hmem])
  have hw := hmS.bytesAt_write (r := 0) (o := 16) (n := 8) (b := reg m .rdi) (sz := 24) rfl
    (by omega) (v := .bin .add .W64 (.lit n) (.load 0 16 8))
    (fun i hi ↦ by rw [hmem]; exact findWrite_head hi)
  rw [byteOf_range] at hw
  have hval : UInt64.ofBitVec ((Sym.bin .add .W64 (.lit n) (.load 0 16 8)).eval (okEnv m bp c n)) =
      (c + n).toUInt64 := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hcur]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_ofBitVec, BitVec.toNat_add, UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
      Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [hval] at hw
  refine finish hp hstk hpc (Match.reg_eq hm hmS rfl hrsp) hap hR.ok.2 hs
    (Match.saved hm hmS hwf rfl hkeep) hR ?_
  simp only [rdLe, hx, hfit, ↓reduceIte]
  exact ⟨hmS.regs .rax _ h0, hv, hR.update hs hw (by omega)⟩

end Ok

/-- **Four bytes**: `b0`, `b1`, `b2`. -/
theorem ok4_spec (hp : Placed code k) {m : MachineData} {bp : BitVec 64} {B : List UInt8}
    {c : Nat} (hstk : StackOk m 0) (hR : ReaderAt m.dmem (reg m .rdi) bp B c)
    (hap : NativeRustcVm.Apart (reg m .rdi) 24 (rspOf m) 8) (hx : (reg m .rsi).toNat = 4)
    (hfit : c + 4 ≤ B.length) :
    Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.ReaderLe.b0Offset)⟩ := by
  have hwf := ok_wf hR hfit (by omega)
  have hm := ok_match hR hx
  have hb0 : (okEnv m bp c 4).base 0 = reg m .rdi := Env.base_ofMachine m _ _ _ rfl
  have hL := hR.len_lt
  have hc : c < 2 ^ 64 := by have := hR.c_le; omega
  have hlen : (okEnv m bp c 4).load 0 8 8 = B.length.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.len)
  have hcur : (okEnv m bp c 4).load 0 16 8 = c.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.cur)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_a0 hwf nofun hm
    fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, SBool.eval, Sym.eval, carry_apply, hcur, toNat_toUInt64 hc,
    show (BitVec.ofNat 64 4).toNat = 4 from rfl, show k + NativeRustcVmX64.Vm.ReaderLe.b0Offset + b0.length = k + NativeRustcVmX64.Vm.ReaderLe.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b0_next]] at hpc1
  rw [decide_eq_false (by omega)] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  have r1 := run_a1
  rw [after_eq run_a0] at r1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) r1 hwf nofun hpc1 hm1
    fun s2 hm2 hpc2 ↦ ?_
  simp only [PcOk, SBool.eval, Sym.eval, BinOp.apply, low_W64, ext_W64, above_apply, hcur, hlen,
    show k + NativeRustcVmX64.Vm.ReaderLe.b1Offset + b1.length = k + NativeRustcVmX64.Vm.ReaderLe.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b1_next]] at hpc2
  rw [decide_eq_false (by
    rw [toNat_toUInt64 hL, BitVec.toNat_add, toNat_toUInt64 hc, BitVec.toNat_ofNat]; omega)] at hpc2
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
  have r2 := run_a2
  rw [after_eq run_a1] at r2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) r2 hwf nofun hpc2 hm2
    fun s3 hm3 hpc3 ↦ ?_
  simp only [PcOk, SBool.eval, ↓reduceIte, hp.label NativeRustcVmX64.Vm.ReaderLe.label_7_at] at hpc3
  refine ok_finish hR hfit hp hstk hap hx hwf hm hm3 hpc3 rfl (by decide) rfl rfl ?_
  apply BitVec.eq_of_toNat_eq
  rw [show reg s3.data .rdx = (Sym.load 1 0 4).eval (okEnv m bp c 4) from hm3.regs .rdx _ rfl,
    Sym.eval, load_le (B := B) (p := c) (by omega) fun i hi ↦ by
      rw [Nat.zero_add]; exact ok_byte hR hfit hi,
    leAt, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by
      have := leNat_lt B c 4; norm_num at this ⊢; omega)]

/-- **Eight bytes**: `b0` to `b6`. -/
theorem ok8_spec (hp : Placed code k) {m : MachineData} {bp : BitVec 64} {B : List UInt8}
    {c : Nat} (hstk : StackOk m 0) (hR : ReaderAt m.dmem (reg m .rdi) bp B c)
    (hap : NativeRustcVm.Apart (reg m .rdi) 24 (rspOf m) 8) (hx : (reg m .rsi).toNat = 8)
    (hfit : c + 8 ≤ B.length) :
    Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.ReaderLe.b0Offset)⟩ := by
  have hwf := ok_wf hR hfit (by omega)
  have hm := ok_match hR hx
  have hb0 : (okEnv m bp c 8).base 0 = reg m .rdi := Env.base_ofMachine m _ _ _ rfl
  have hL := hR.len_lt
  have hc : c < 2 ^ 64 := by have := hR.c_le; omega
  have hlen : (okEnv m bp c 8).load 0 8 8 = B.length.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.len)
  have hcur : (okEnv m bp c 8).load 0 16 8 = c.toUInt64.toBitVec :=
    load_word (by rw [hb0]; exact hR.cur)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, SBool.eval, Sym.eval, carry_apply, hcur, toNat_toUInt64 hc,
    show (BitVec.ofNat 64 8).toNat = 8 from rfl, show k + NativeRustcVmX64.Vm.ReaderLe.b0Offset + b0.length = k + NativeRustcVmX64.Vm.ReaderLe.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b0_next]] at hpc1
  rw [decide_eq_false (by omega)] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  have r1 := run_b1
  rw [after_eq run_b0] at r1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) r1 hwf nofun hpc1 hm1
    fun s2 hm2 hpc2 ↦ ?_
  simp only [PcOk, SBool.eval, Sym.eval, BinOp.apply, low_W64, ext_W64, above_apply, hcur, hlen,
    show k + NativeRustcVmX64.Vm.ReaderLe.b1Offset + b1.length = k + NativeRustcVmX64.Vm.ReaderLe.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b1_next]] at hpc2
  rw [decide_eq_false (by
    rw [toNat_toUInt64 hL, BitVec.toNat_add, toNat_toUInt64 hc, BitVec.toNat_ofNat]; omega)] at hpc2
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
  have r2 := run_b2
  rw [after_eq run_b1] at r2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) r2 hwf nofun hpc2 hm2
    fun s3 hm3 hpc3 ↦ ?_
  simp only [PcOk, SBool.eval, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmX64.Vm.ReaderLe.b2Offset + b2.length = k + NativeRustcVmX64.Vm.ReaderLe.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b2_next]] at hpc3
  have r3 := run_b3
  rw [after_eq run_b2] at r3
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) r3 hwf nofun hpc3 hm3
    fun s4 hm4 hpc4 ↦ ?_
  simp only [PcOk, SBool.eval, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmX64.Vm.ReaderLe.b3Offset + b3.length = k + NativeRustcVmX64.Vm.ReaderLe.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b3_next]] at hpc4
  have r4 := run_b4
  rw [after_eq run_b3] at r4
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) r4 hwf nofun hpc4 hm4
    fun s5 hm5 hpc5 ↦ ?_
  simp only [PcOk, SBool.eval, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmX64.Vm.ReaderLe.b4Offset + b4.length = k + NativeRustcVmX64.Vm.ReaderLe.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b4_next]] at hpc5
  have r5 := run_b5
  rw [after_eq run_b4] at r5
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) r5 hwf nofun hpc5 hm5
    fun s6 hm6 hpc6 ↦ ?_
  simp only [PcOk, SBool.eval, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmX64.Vm.ReaderLe.b5Offset + b5.length = k + NativeRustcVmX64.Vm.ReaderLe.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b5_next]] at hpc6
  have r6 := run_b6
  rw [after_eq run_b5] at r6
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) r6 hwf nofun hpc6 hm6
    fun s7 hm7 hpc7 ↦ ?_
  simp only [PcOk, show k + NativeRustcVmX64.Vm.ReaderLe.b6Offset + b6.length = k + NativeRustcVmX64.Vm.ReaderLe.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReaderLe.b6_next]] at hpc7
  refine ok_finish hR hfit hp hstk hap hx hwf hm hm7 hpc7 rfl (by decide) rfl rfl ?_
  apply BitVec.eq_of_toNat_eq
  rw [show reg s7.data .rdx = word8Sym.eval (okEnv m bp c 8) from hm7.regs .rdx _ rfl,
    eval_word8 _ B c fun i hi ↦ ok_byte hR hfit hi,
    leAt, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by
      have := leNat_lt B c 8; norm_num at this ⊢; omega)]

/-- **`Reader::le` meets its contract.** -/
theorem readerLe_spec (hp : Placed code k) : Spec (label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost := by
  intro m ⟨hstk, hn, bp, B, c, hR, hdis⟩
  have hap : NativeRustcVm.Apart (reg m .rdi) 24 (rspOf m) 8 := by
    have := (List.pairwise_pair.mp hdis)
    have hsb : stackBelow m readerLeStack = rspOf m := BitVec.sub_zero _
    simp only [stackR, hsb] at this
    unfold NativeRustcVm.Apart at this ⊢
    omega
  rw [hp.label NativeRustcVmX64.Vm.ReaderLe.entry_at]
  by_cases hfit : c + (reg m .rsi).toNat ≤ B.length
  · rcases hn with hn | hn
    · exact ok4_spec hp hstk hR hap hn (by omega)
    · exact ok8_spec hp hstk hR hap hn (by omega)
  · exact fail_spec hp hstk hR hap hfit

end

end NativeRustcVmX64.Wire.ReaderLe
