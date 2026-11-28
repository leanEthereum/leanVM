module

public import NativeRustcVmX64.Wire.PhaseM.Basic
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `phase_m`: the reads (x86-64)

A block from `frS` ending in a call of `Reader::le` for four bytes and the call (`le4`). From the
entry: the prologue and the query count (`b0`, `b1`, at most 256), to the queries' loop (`b2`,
`b3`) or, with none, past it (`first_run`); the queries into the working area (`b4` to `b6`,
`qloop`); the height, the leaf width and the row width (`b7` to `b13`, `rest_run`), to the sort's
head (`SortSt`), the model's phase now `tail` of what was read, or to `None`.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  Frame.of_prologue Frame.entry after after_eq sameOutside_low MidOk match_rsp eval_ptr0
  wordAt_write)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.Decode (eqv_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **The queries' loop** (`b4`), query `i` of `count`. -/
structure AtQ [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b4Offset)
  bod : Bod m0 8 st.data
  h1 : rdU32 B c = some (count, c + 4)
  cnt : count ≤ 256
  ilt : i < count
  f40 : FW m0 st.data.dmem 40 count.toUInt64
  r13 : (reg st.data .r13).toNat = 8 * count
  r15 : (reg st.data .r15).toNat = 8 * i
  qs : ∃ qs, rdU32s B i (c + 4) = some (qs, c + 4 + 4 * i) ∧
    NativeRustcVm.WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64) ∧
    ReaderAt st.data.dmem (RD m0) bp B (c + 4 + 4 * i)

/-- **After the queries** (`b7`). -/
structure At7 [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (c2 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b7Offset)
  bod : Bod m0 8 st.data
  h1 : rdU32 B c = some (count, c + 4)
  cnt : count ≤ 256
  hqs : rdU32s B count (c + 4) = some (qs, c2)
  f40 : FW m0 st.data.dmem 40 count.toUInt64
  r13 : (reg st.data .r13).toNat = 8 * count
  qsW : NativeRustcVm.WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (RD m0) bp B c2

/-- **At the sort's head** (`b14`), query `i`: the reads done, the queries at the working area's
start, the distinct positions of the first `i` at its byte 2048. -/
structure SortSt [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height lw rw c5 i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b14Offset)
  bod : Bod m0 8 st.data
  model : phaseM B c = tail B qs height lw rw c5
  len : qs.length = count
  cnt0 : 0 < count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  hlt : height < 2 ^ 32
  lwlt : lw < 2 ^ 32
  rwlt : rw < 2 ^ 32
  ilt : i < count
  f40 : FW m0 st.data.dmem 40 count.toUInt64
  f32 : FW m0 st.data.dmem 32 height.toUInt64
  f16 : FW m0 st.data.dmem 16 lw.toUInt64
  f24 : FW m0 st.data.dmem 24 rw.toUInt64
  r13 : (reg st.data .r13).toNat = 8 * count
  r15 : (reg st.data .r15).toNat = 8 * i
  rbp : (reg st.data .rbp).toNat = (sortD (qs.take i)).length
  rdi : reg st.data .rdi = wa m0 2048
  qsW : NativeRustcVm.WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  psW : NativeRustcVm.WordsAt st.data.dmem (wa m0 2048) ((sortD (qs.take i)).map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (RD m0) bp B c5

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem toNat_reg_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : UInt64.ofBitVec x = n.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofBitVec, toNat_toUInt64 (by have := x.isLt; omega), h]

theorem wordsAt_snoc {d : Mem 64} {a : BitVec 64} {ws : List UInt64} {v : UInt64}
    (h : NativeRustcVm.WordsAt d a ws) (hv : NativeRustcVm.WordAt d (off a (8 * ws.length)) v) :
    NativeRustcVm.WordsAt d a (ws ++ [v]) :=
  NativeRustcVm.wordsAt_append_iff.mpr ⟨h, NativeRustcVm.wordsAt_singleton_iff.mpr hv⟩

/-- `b1`'s test: the read failed or the count is past `256`. -/
theorem c1_eval [Labels] (env : Sym.Env) (ha : env.regs .rax = 0 ∨ env.regs .rax = 1) :
    c1.eval env = !(decide ((env.regs .rdx).toNat < 257) && decide (env.regs .rax = 1)) := by
  have hc : CmpOp.apply .ult .W64 (env.regs .rdx) (BitVec.ofNat 64 257) =
      decide ((env.regs .rdx).toNat < 257) := by
    rw [NativeRustcVmX64.Wire.Decode.ult_eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
  simp only [c1, SBool.eval, Sym.eval, hc]
  rw [NativeRustcVmX64.Wire.Decode.c6_val _ _ _ ha]

theorem and1_eval [Labels] (env : Sym.Env) (h : env.regs .rax = 0 ∨ env.regs .rax = 1) :
    (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.lit 1)) (.lit 0)).eval env =
      decide (env.regs .rax = 0) := by
  simp only [SBool.eval, Sym.eval]
  rcases h with h | h <;> rw [h] <;> decide

theorem eight_eval [Labels] (env : Sym.Env) {n : Nat} (h : (env.load 0 40 8).toNat = n)
    (hn : n ≤ 256) : (eightC.eval env).toNat = 8 * n := by
  simp only [eightC, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat, h]
  omega

variable [Host] {k : Nat}

/-- **A block ending in a call of `Reader::le` for four bytes**, and the call: the block writes
the call's slot only, RDI R12, RSI `4`. -/
theorem le4 (hp : Placed code k) (G : Geo m0 bp B.length)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) {bj : List Directive}
    {j : Nat} (hb : bj.IsInfixAt code j) (hne : bj ≠ [])
    (hrun : exec bj frS = some (after bj frS,
      .call NativeRustcVmX64.Vm.ReaderLe.entryLabel))
    (hok : MidOk 160 0 slots (after bj frS) = true)
    (hw : ∀ w ∈ (after bj frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8)
    (hsi : (after bj frS).reg .rsi = some (.lit 4)) (hdi : (after bj frS).reg .rdi = some (.reg .r12))
    (h12 : (after bj frS).reg .r12 = some (.reg .r12))
    (h14 : (after bj frS).reg .r14 = some (.reg .r14))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hbod : Bod m0 8 st.data) {c : Nat}
    (hR : ReaderAt st.data.dmem (RD m0) bp B c) {R : MachineState → Prop}
    (cont : ∀ (s1 : MachineState) (m2 : MachineData), Bod m0 8 m2 →
      Match (frameEnv m0 st.data 160 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec)
        (after bj frS) s1.data →
      (∀ x, calleeSaved x = true → reg m2 x = reg s1.data x) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        (SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 152) ∨
        ((RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24)) →
      Read4 (RD m0) bp B c m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + j + bj.length)⟩) :
    Eventually (step1 Host.exe) R st := by
  have hst : StackOk m0 1216 := G.st
  have hsp := G.sp
  have htop := G.top
  have hrn := G.rNw
  have hsR := G.sR
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 160) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + j + bj.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hbod.fr.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec)
      frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hS := stackBelow_toNat (m := m0) (n := 160) (by omega)
  have hs1 : NativeRustcVm.SameOutside st.data.dmem s1.data.dmem
      (fun q ↦ SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 152) :=
    (sameOutside_low hwf hm1 (r := 0) rfl (hi := 8) (by omega) hw).mono fun q h ↦ by
      have := iv_of_inRange (by rw [hS]; omega) h
      rw [hS] at this
      omega
  have hf1 : Frame m0 160 slots 0 s1.data := Frame.of_block hbod.fr hwf hm1 hok slots_le
  have hR1 : ReaderAt s1.data.dmem (RD m0) bp B c :=
    reader_keep hR hs1 (fun q hq ↦ by omega) (fun q hq ↦ by have := G.sB; omega)
  have hdi1 : reg s1.data .rdi = RD m0 := (hm1.regs .rdi _ hdi).trans hbod.r12
  have hsi1 : (reg s1.data .rsi).toNat = 4 := by
    rw [show reg s1.data .rsi = _ from hm1.regs .rsi _ hsi]; rfl
  refine le4_call hle hst (F := 160) (by omega) (lo := 112) (by omega) slots_lo hf1 hR1 hdi1 hsi1
    (by omega) (by omega) hpc1 fun m2 hf2 hcs2 hso2 hr2 ↦ ?_
  have h16 : (off (RD m0) 16).toNat = (RD m0).toNat + 16 := toNat_off (by omega)
  have hso2' : NativeRustcVm.SameOutside s1.data.dmem m2.dmem
      (fun q ↦ (RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24) := hso2.mono fun q h ↦ by
    have := iv_of_inRange (by rw [h16]; omega) h
    rw [h16] at this; omega
  have hout1 : FW m0 s1.data.dmem 48 (UInt64.ofBitVec (OUT m0)) :=
    hbod.out.keep G (by omega) hs1 fun q hq ↦ by omega
  refine cont s1 m2 ⟨hf2, (hbod.chg.trans (hs1.trans hso2')).mono fun q hq ↦ ?_,
    (hcs2 .r12 rfl).trans ((hm1.regs .r12 _ h12).trans hbod.r12),
    (hcs2 .r14 rfl).trans ((hm1.regs .r14 _ h14).trans hbod.r14),
    hout1.keep G (by omega) hso2' fun q hq ↦ by omega⟩ hm1 hcs2
    ((hs1.trans hso2').mono fun q hq ↦ hq) hr2
  rcases hq with hq | hq | hq
  · exact hq
  · exact .inl (by omega)
  · exact .inr (.inl hq)

end

end NativeRustcVmX64.Wire.PhaseM
