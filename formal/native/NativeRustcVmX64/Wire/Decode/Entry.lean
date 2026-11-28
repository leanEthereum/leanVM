module

public import NativeRustcVmX64.Wire.Decode.Steps
public import NativeRustcVmX64.Wire.Decode.Model
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `decode`: the prologue and the stream's count (x86-64)

`entry_run`: the prologue (`b0`, the reader at the frame's byte `8`: the wire's address, its
length, cursor `0`), `Reader::le` for the stream's count `n`, its tag (`b1`) and `2 n` against the
decoded area's words (`b2`): to `None`, or to `Reader::words`' call (`At3`).
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.Decode
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  Frame.of_prologue Frame.entry after after_eq match_rsp eval_ptr0 wordAt_write sameOutside_low
  mapped_off)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.PhaseM (bytesAt_keep wordAt_keep wordsAt_keep reader_keep iv_of_inRange
  le4_call Read4 read4_cases callee_toNat toNat_toUInt64)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **At `Reader::words`' call** (`b3`): the count `n` read, `2 n` below the area's words. -/
structure At3 [Labels] [Host] (m0 : MachineData) (k n : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b3Offset)
  bod : Bod m0 8 st.data
  rd : ReaderAt st.data.dmem (rdA m0) (BP m0) (Bs m0) 4
  h1 : rdU32 (Bs m0) 0 = some (n, 4)
  nlt : n < 2 ^ 32
  rcx : (reg st.data .rcx).toNat = n
  rdx : (reg st.data .rdx).toNat = 2 * n
  hlt : 2 * n < LEN m0
  r13 : reg st.data .r13 = DEC m0
  r14 : reg st.data .r14 = reg m0 .rcx
  pos : 4 ≤ LN m0

end

public section

theorem ofBitVec_eq_toUInt64 (x : BitVec 64) : UInt64.ofBitVec x = x.toNat.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofBitVec, toNat_toUInt64 x.isLt]

variable {m0 : MachineData}

section
variable [Labels]

/-- **The reader at the entry**, from the frame's three words. -/
theorem reader0 (G : Geo m0) {d : Mem 64}
    (hk : Kept m0.dmem d)
    (hs : NativeRustcVm.SameOutside m0.dmem d (NativeRustcVm.InRange (stackBelow m0 80) 80))
    (hp : NativeRustcVm.WordAt d (rdA m0) (UInt64.ofBitVec (BP m0)))
    (hl : NativeRustcVm.WordAt d (off (rdA m0) 8) (UInt64.ofBitVec (reg m0 .rsi)))
    (hc : NativeRustcVm.WordAt d (off (rdA m0) 16) (UInt64.ofBitVec (BitVec.ofNat 64 0))) :
    ReaderAt d (rdA m0) (BP m0) (Bs m0) 0 := by
  have hsp := G.sp
  have htop := G.top
  have hr := G.fr (j := 8) (by omega)
  have hS := stackBelow_toNat (m := m0) (n := 80) (by omega)
  have hbn := G.bNw
  refine ⟨⟨fun i hi ↦ ?_, ?_⟩, hp, ?_, ?_, ?_, ?_, fun hL ↦ ?_, Nat.zero_le _⟩
  · have hm := mapped_off (o := 8) (k := 24)
      (Mapped.keeps (frame_mapped G.st (F := 80) (by omega)) hk) (by omega)
    exact hm i hi
  · show (rdA m0).toNat + 24 ≤ 2 ^ 64
    rw [hr]; omega
  · rw [length_Bs, ← ofBitVec_eq_toUInt64]; exact hl
  · exact hc
  · refine bytesAt_keep (bytes_entry G) hs (by rw [length_Bs]; exact hbn) fun q hq ↦ ?_
    have := iv_of_inRange (by rw [hS]; omega) hq
    rw [hS] at this
    rw [length_Bs]
    by_cases hL : 0 < LN m0
    · have := G.sB hL; omega
    · omega
  · rw [length_Bs]; exact hbn
  · rw [length_Bs] at hL ⊢
    have := G.sB hL
    unfold NativeRustcVm.Apart
    rw [hr]; omega

end

variable [Host] {k : Nat}

/-- **From the entry** to `Reader::words`' call, or out with `None`. -/
theorem entry_run (hp : Placed code k) (G : Geo m0)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) :
    Eventually (step1 Host.exe) (fun st ↦ Post m0 st ∨ ∃ n, At3 m0 k n st)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b0Offset)⟩ := by
  have hst := G.st
  have hsp := G.sp
  have htop := G.top
  have hS := stackBelow_toNat (m := m0) (n := 80) (by omega)
  have hr := G.fr (j := 8) (by omega)
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 80) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b0Offset + b0.length)).toBitVec)
    ⟨frame_mapped hst (by omega), frame_noWrap hst (by omega)⟩ (by simp)
    (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 80 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b0Offset + b0.length)).toBitVec)
      entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw8, hw16, hw24, hws, hrdi, hrsi, hrbx, hr13, hr14, hr15⟩ := ok_b0
  have hf1 : Frame m0 80 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 80) 80) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (hi := 80) (by omega) fun w hw ↦
      ⟨(hws w hw).1, by rcases (hws w hw).2 with h | h <;> omega⟩
  have hR1 : ReaderAt st1.data.dmem (rdA m0) (BP m0) (Bs m0) 0 := by
    have w8 := wordAt_write hm1 (r := 0) (o := 8) (b := stackBelow m0 80) (sz := 88) rfl
      (by omega) hw8
    have w16 := wordAt_write hm1 (r := 0) (o := 16) (b := stackBelow m0 80) (sz := 88) rfl
      (by omega) hw16
    have w24 := wordAt_write hm1 (r := 0) (o := 24) (b := stackBelow m0 80) (sz := 88) rfl
      (by omega) hw24
    simp only [Sym.eval, Env.ofMachine_regs] at w8 w16 w24
    refine reader0 G (hm1.kept hwf0) hs1 w8 ?_ ?_
    · rw [off_off]; exact w16
    · rw [off_off]; exact w24
  have hrdi1 : reg st1.data .rdi = rdA m0 := (hm1.regs .rdi _ hrdi).trans (eval_ptr0 8)
  have hrsi1 : (reg st1.data .rsi).toNat = 4 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]; rfl
  refine le4_call hle hst (F := 80) (by omega) (lo := 32) (by omega) slots_lo hf1 hR1 hrdi1 hrsi1
    (by rw [hr]; omega) (by rw [hr]; omega) hpc1 fun m2 hf2 hcs2 hso2 hr2 ↦ ?_
  have hc16 : (off (rdA m0) 16).toNat = SP0 m0 - 80 + 24 := by rw [off_off]; exact G.fr (by omega)
  have hbod2 : Bod m0 8 m2 := by
    refine ⟨hf2, (hs1.trans hso2).mono fun q hq ↦ ?_, ?_, ?_⟩
    · left
      rcases hq with hq | hq
      · have := iv_of_inRange (by rw [hS]; omega) hq
        rw [hS] at this; omega
      · have := iv_of_inRange (by rw [hc16]; omega) hq
        rw [hc16] at this; omega
    · rw [hcs2 .rbx rfl]; exact hm1.regs .rbx _ hrbx
    · rw [hcs2 .r15 rfl]; exact hm1.regs .r15 _ hr15
  have e13 : reg m2 .r13 = DEC m0 := by rw [hcs2 .r13 rfl]; exact hm1.regs .r13 _ hr13
  have e14 : reg m2 .r14 = reg m0 .rcx := by rw [hcs2 .r14 rfl]; exact hm1.regs .r14 _ hr14
  -- `b1`: the tag.
  refine fblk hp G b1_in_code (by simp [b1]) exit_b1 nofun ok_b1.1 (ok_b1.2 .rbx (by simp))
    (ok_b1.2 .r15 (by simp)) (st := ⟨m2, _⟩) rfl hbod2 fun st3 hb3 hd3 hm3 hpc3 ↦ ?_
  have r3 : ∀ x ∈ [Reg64.rdx, .rbx, .r13, .r14, .r15], reg st3.data x = reg m2 x :=
    fun x hx ↦ hm3.regs x _ (ok_b1.2 x hx)
  simp only [PcOk, SBool.eval, Sym.eval, eqv_eval, Env.ofMachine_regs] at hpc3
  rcases read4_cases hr2 with ⟨hn, h0⟩ | ⟨n, hv, h0, hdx, hnl, hR4⟩
  · -- No count: `None`.
    rw [show m2.regs.get64 .rax = 0 from h0] at hpc3
    simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.Decode.label_9_at] at hpc3
    exact Eventually.mono (none_run hp G hpc3 hb3 (by rw [decodeM_eq, hn])) fun _ h ↦ .inl h
  rw [show m2.regs.get64 .rax = 1 from h0] at hpc3
  simp only [show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat,
    decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
  simp only [Nat.zero_add] at hv hR4
  -- `b2`: `2 n` against the words.
  refine fblk hp G b2_in_code (by simp [b2]) exit_b2 nofun ok_b2.1 (ok_b2.2.2.2 .rbx (by simp))
    (ok_b2.2.2.2 .r15 (by simp)) (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b1_next)) hb3 fun st4 hb4 hd4 hm4 hpc4 ↦ ?_
  have hdx3 : (reg st3.data .rdx).toNat = n := by rw [r3 .rdx (by simp)]; exact hdx
  have h2n : (BinOp.apply .add .W64 (reg st3.data .rdx) (reg st3.data .rdx)).toNat = 2 * n := by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, hdx3]
    omega
  have h14 : reg st3.data .r14 = reg m0 .rcx := by rw [r3 .r14 (by simp)]; exact e14
  simp only [PcOk, SBool.eval, Sym.eval, ult_eval, Env.ofMachine_regs] at hpc4
  change st4.pc = if (!decide ((BinOp.apply .add .W64 (reg st3.data .rdx) (reg st3.data .rdx)).toNat <
    (reg st3.data .r14).toNat)) = true then _ else _ at hpc4
  rw [h2n, h14] at hpc4
  have hlen := G.len
  rw [decodedWords_eq] at hlen
  by_cases hroom : 2 * n < LEN m0
  · rw [decide_eq_true hroom] at hpc4
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    have r4 : ∀ x ∈ [Reg64.rbx, .r13, .r14, .r15], reg st4.data x = reg st3.data x :=
      fun x hx ↦ hm4.regs x _ (ok_b2.2.2.2 x hx)
    refine .done _ (.inr ⟨n, hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Decode.b2_next), hb4, ?_, ?_, hnl, ?_, ?_, hroom, ?_, ?_,
      ?_⟩)
    · rw [hd4, hd3]; exact hR4
    · rw [hv]
    · rw [show reg st4.data .rcx = _ from hm4.regs .rcx _ ok_b2.2.1]; exact hdx3
    · rw [show reg st4.data .rdx = _ from hm4.regs .rdx _ ok_b2.2.2.1]; exact h2n
    · rw [r4 .r13 (by simp), r3 .r13 (by simp)]; exact e13
    · rw [r4 .r14 (by simp)]; exact h14
    · have := hR4.c_le; rw [length_Bs] at this; exact this
  · -- No room for the stream: the model reads past the wire.
    rw [decide_eq_false hroom] at hpc4
    simp only [Bool.not_false, ↓reduceIte] at hpc4
    rw [hp.label NativeRustcVmX64.Vm.Decode.label_9_at] at hpc4
    refine Eventually.mono (none_run hp G hpc4 hb4 ?_) fun _ h ↦ .inl h
    rw [decodeM_eq, hv]
    simp only
    rw [show rdWords (Bs m0) (2 * n) 4 = none by
      unfold rdWords
      split
      · rename_i h; rw [length_Bs] at h; omega
      · rfl]

end

end NativeRustcVmX64.Wire.Decode
