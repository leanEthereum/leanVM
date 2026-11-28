module

public import NativeRustcX64.WotsLeaf.Digest.Prologue
public meta import NativeRustcX64.WotsLeaf.FrameS
public meta import NativeRustcX64.Code.Xmss.WotsLeaf

/-!
# The epilogue and returning the result

`epilogue`: from `b12` (directive 158) with RSP the frame's base, the saved registers in place and
the entry's mapped bytes kept, the machine returns to the caller with the entry's callee-saved
registers, RSP 8 above the entry's and memory as it was. `finish`: with memory changed only at
`out` and in the stack area and the result at `out` (`WotsLeafOut1`), the function returns with
its postcondition (`Run.Done`). `fail_path`: from `b11` (directive 155) the tag `0` stored at
`out`, then `finish`. `out` as the executor's region 4, reached by the alias of the word at `96`
(`outS`, `match_out`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- `out` (region 4) reached by the alias of the word at `96`, the registers `k`. -/
def outS (k : List (Reg64 × Sym)) : SState := frameS k [75] [] [(.load 0 96 8, (4, 0))]

end

set_option Elab.async false

sym_block run_b11 := exec b11 (outS [])
sym_block run_b12 := exec b12 (frameS [])

public section

/-- A word's bytes loaded: the word. -/
theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (wordBytes v)) = v.toBitVec := by
  have hw := Hasher.wordBytes_ofBitVec v.toBitVec
  have hb := Sym.ofBytes_byteOf v.toBitVec 0 8
  simp only [Nat.zero_add] at hb
  rw [show UInt64.ofBitVec v.toBitVec = v from rfl] at hw
  rw [hw, hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := v.toBitVec.isLt
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

namespace Run

variable (r : Run) [Labels]

/-- A saved register in the frame: the word at `2712 + 8 j`. -/
theorem load_saved {m : MachineData} (hsv : BytesAt m.dmem (r.off 2712) (savedBytes r.m0))
    (extra : List (BitVec 64 × Nat)) (ret : BitVec 64) (j o : Nat) (ho : o = 2712 + 8 * j)
    (x : UInt64) (hx : ((savedBytes r.m0).drop (8 * j)).take 8 = wordBytes x) :
    (r.envR m extra ret).load 0 o 8 = x.toBitVec := by
  have h := BytesAt.slice hsv (8 * j) 8
  rw [hx, off, addr_add_add] at h
  rw [Env.load_of_bytesAt (length_wordBytes x) (by rw [ho]; exact h), ofInt_ofBytes_wordBytes]

/-- The frame's byte `2760`: RSP at the entry. -/
theorem off_ret (hpre : r.Pre) : r.off 2760 = rspOf r.m0 := by
  have hb := r.base_toNat hpre
  have ho := r.off_toNat hpre (a := 2760) (by decide)
  apply BitVec.eq_of_toNat_eq
  omega

/-- The frame's byte `2768`: RSP 8 above the entry's. -/
theorem off_ret8 (hpre : r.Pre) : r.base + BitVec.ofInt 64 2768 = rspOf r.m0 + 8#64 := by
  rw [← r.off_args hpre]
  rfl

end Run

/-- The return address: the word at `2760`. -/
theorem Run.load_ret [Labels] (r : Run) (hpre : r.Pre) {m : MachineData}
    (hs : SameOutside r.m0.dmem m.dmem r.Changed) (extra : List (BitVec 64 × Nat))
    (ret : BitVec 64) :
    Int64.ofBitVec ((r.envR m extra ret).load 0 2760 8) = retOf r.m0 := by
  rw [r.load_arg hpre hs (by decide) (by decide), r.off_ret hpre]
  rfl

variable [Host]

/-- **The epilogue**: from a state at `b12` with RSP the frame's base, the saved registers in
place, the entry's mapped bytes still mapped and memory changed only at `out` and in the stack
area, the machine returns to the caller with the entry's callee-saved registers, RSP 8 above the
entry's, memory as it was. -/
theorem epilogue (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre)
    (m : MachineData) (hsp : reg m .rsp = r.base)
    (hsv : BytesAt m.dmem (r.off 2712) (savedBytes r.m0)) (hk : Kept r.m0.dmem m.dmem)
    (hs : SameOutside r.m0.dmem m.dmem r.Changed) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf r.m0 ∧
      rspOf st.data = rspOf r.m0 + 8#64 ∧ Saved r.m0 st.data ∧
      ∀ p, st.data.dmem.get? p = m.dmem.get? p) ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b12Offset⟩ := by
  have hwf := envR_wf hpre hk extraOK_nil (r.pc (NativeRustcX64.Xmss.WotsLeaf.b12Offset + b12.length)).toBitVec
  have hm : Match (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b12Offset + b12.length)).toBitVec) (frameS []) m :=
    match_frameS (fun _ hl _ hi => r.got_byte_changed hpre hs hl hi)
      hsp (extra := []) (sextra := []) (k := []) (bounds := []) (aliases := [])
      trivial trivial trivial trivial
  refine blk r hp b12_in_code (List.cons_ne_nil _ _) run_b12 hwf rfl hm fun st hm' hpc ↦
    .done _ ?_
  have ls := fun j o ho x hx ↦ r.load_saved hsv [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b12Offset + b12.length)).toBitVec j o ho x hx
  have hreg : ∀ x : Reg64, calleeSaved x = true → reg st.data x = reg r.m0 x := by
    intro x hx
    unfold reg
    cases x <;> simp only [calleeSaved, Bool.false_eq_true] at hx
    · exact (hm'.regs .rbx _ rfl).trans (ls 0 2712 rfl _ rfl)
    · exact (hm'.regs .rbp _ rfl).trans (ls 5 2752 rfl _ rfl)
    · exact (hm'.regs .r12 _ rfl).trans (ls 1 2720 rfl _ rfl)
    · exact (hm'.regs .r13 _ rfl).trans (ls 2 2728 rfl _ rfl)
    · exact (hm'.regs .r14 _ rfl).trans (ls 3 2736 rfl _ rfl)
    · exact (hm'.regs .r15 _ rfl).trans (ls 4 2744 rfl _ rfl)
  have hsame : ∀ p, st.data.dmem.get? p = m.dmem.get? p := fun p ↦
    hm'.get?_mem0 hwf (fun ⟨w, hw, _⟩ ↦ by simp at hw) |>.trans rfl
  refine ⟨?_, ?_, ⟨hreg, fun p h ↦ by rw [hsame p]; exact hk p h⟩, hsame⟩
  · rw [hpc]
    exact r.load_ret hpre hs [] _
  · show reg st.data .rsp = _
    unfold reg
    rw [hm'.regs .rsp _ rfl]
    exact r.off_ret8 hpre

end

end NativeRustcX64.WotsLeafProof
