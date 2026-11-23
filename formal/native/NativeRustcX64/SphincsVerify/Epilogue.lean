module

public import NativeRustcX64.SphincsVerify.Frame
public import NativeRustcX64.Sym
public import NativeRustcX64.Hasher.Bytes
public meta import NativeRustcX64.Code.Sphincs.SphincsVerify.Part4

/-!
# `sphincs_verify`'s epilogue (x86-64)

`b196` (`.LSphincsVerify_85`): RSP back to the pushed registers, RBX, R12 .. R15,
RBP popped, `retq`. From any state of the frame it returns to the caller, RSP 8 above the entry's,
with the registers of the entry and RAX as it was (`epilogue`); with RAX the boolean `v`, that is
`Done v` (`done_of_epilogue`). `b195` (`xorl %eax, %eax`) falls into it:
`Done false` (`fail_return`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc LeanVM.Protocol.KeccakHash

set_option Elab.async false

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

/-- `n` bytes from byte `k` of bytes in memory. -/
theorem bytesAt_slice {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (k n : Nat) (hk : k + n ≤ bs.length) :
    BytesAt d (a + BitVec.ofNat 64 k) ((bs.drop k).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [Sym.addr_add, h (k + i) (by omega)]
  simp [List.getElem_take, List.getElem_drop]

namespace Run

variable (r : Run) [Labels]

/-- A pushed register in the frame: the word at `29352 + 8 j`. -/
theorem load_saved {m : MachineData} (hF : r.Frame m) (vars : Nat → BitVec 64) (ret : BitVec 64)
    (j o : Nat) (ho : o = 29352 + 8 * j) (hj : j < 6) (x : UInt64)
    (hx : ((savedBytes r.m0).drop (8 * j)).take 8 = wordBytes x) :
    (r.env m vars ret).load 0 o 8 = x.toBitVec := by
  have h := bytesAt_slice hF.2.1 (8 * j) 8 (by rw [length_savedBytes]; omega)
  rw [hx, off, Sym.addr_add] at h
  rw [Sym.Env.load_of_bytesAt (length_wordBytes x) (by rw [ho]; exact h),
    ofInt_ofBytes_wordBytes]

/-- RSP at the entry: the frame's end. -/
theorem base_add_frame (hpre : r.Pre) :
    r.base + BitVec.ofInt 64 29400 = rspOf r.m0 := by
  have hb := r.base_toNat hpre
  apply BitVec.eq_of_toNat_eq
  rw [show BitVec.ofInt 64 29400 = BitVec.ofNat 64 29400 from rfl,
    Sym.toNat_add_ofNat _ _ (by omega)]
  omega

/-- The return address's bytes are the entry's: they are outside the stack area. -/
theorem ret_slot (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) :
    ∀ i < 8, m.dmem.get? (rspOf r.m0 + BitVec.ofNat 64 i) =
      r.m0.dmem.get? (rspOf r.m0 + BitVec.ofNat 64 i) := by
  intro i hi
  have hb := r.base_toNat hpre
  apply hF.2.2.1
  rw [r.stackArea_iff hpre, Sym.toNat_add_ofNat _ _ (by omega)]
  omega

end Run

sym_block b196_exec := Sym.exec Sphincs.SphincsVerify.b196
  (Sym.init [29408, 16, 8, 8] [(.rsp, .ptr 0 0)])

sym_block b195_exec := Sym.exec Sphincs.SphincsVerify.b195
  (Sym.init [29408, 16, 8, 8] [(.rsp, .ptr 0 0)])

variable [Host]

/-- **The epilogue**: from a state of the frame at `b196`, the machine returns to the caller, RSP
8 above the entry's, with RAX as it was, no byte changed outside the stack area, and the entry's
callee-saved registers and mapped bytes. -/
theorem epilogue (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf r.m0 ∧
      rspOf st.data = rspOf r.m0 + 8#64 ∧ reg st.data .rax = reg m .rax ∧
      SameOutside r.m0.dmem st.data.dmem r.StackArea ∧ Saved r.m0 st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b196Offset⟩ := by
  have hk := Sphincs.SphincsVerify.b196_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) 0
  have hm : Sym.Match (r.env m (fun _ ↦ 0) 0) (Sym.init [frameRegion, 16, 8, 8] [(.rsp, .ptr 0 0)]) m :=
    Sym.match_ofMachine ⟨rfl, rfl, rfl, rfl, trivial⟩
      ⟨by show rspOf m = r.base + BitVec.ofInt 64 0; simp only [BitVec.ofInt_ofNat,
        BitVec.add_zero]; exact hF.1, trivial⟩ trivial trivial trivial
  have hread := hm.read hwf (r := 0) (o := 29400) (n := 8) rfl (by decide) (by decide)
  refine Sym.exec_then hk b196_exec hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ .done _ ?_
  have ls := fun j o ho hj x hx ↦ r.load_saved hF (fun _ ↦ 0) 0 j o ho hj x hx
  have hreg : ∀ x : Reg64, calleeSaved x = true → st.data.regs.get64 x = r.m0.regs.get64 x := by
    intro x hx
    cases x <;> simp only [calleeSaved, Bool.false_eq_true] at hx
    · exact (hm'.regs .rbx _ rfl).trans (ls 0 29352 rfl (by decide) _ rfl)
    · exact (hm'.regs .rbp _ rfl).trans (ls 5 29392 rfl (by decide) _ rfl)
    · exact (hm'.regs .r12 _ rfl).trans (ls 1 29360 rfl (by decide) _ rfl)
    · exact (hm'.regs .r13 _ rfl).trans (ls 2 29368 rfl (by decide) _ rfl)
    · exact (hm'.regs .r14 _ rfl).trans (ls 3 29376 rfl (by decide) _ rfl)
    · exact (hm'.regs .r15 _ rfl).trans (ls 4 29384 rfl (by decide) _ rfl)
  refine ⟨?_, ?_, (hm'.regs .rax _ rfl), ?_, hreg, fun p h ↦ hm'.kept hwf p (hF.2.2.2 p h)⟩
  · simp only [Sym.PcOk] at hpc
    rw [hpc]
    rw [show (r.env m (fun _ ↦ 0) 0).base 0 + BitVec.ofNat 64 29400 = rspOf r.m0 from
      r.base_add_frame hpre, Sym.loadInt_congr (r.ret_slot hpre hF)] at hread
    exact (retOf_of_loadInt hread).symm
  · rw [rspOf, hm'.regs .rsp _ rfl]
    show r.base + BitVec.ofInt 64 29408 = rspOf r.m0 + 8#64
    rw [← r.base_add_frame hpre, BitVec.add_assoc]
    rfl
  · rw [hm'.dmem_eq hwf rfl]
    exact hF.2.2.1

/-- **Returning `v`**: from a state of the frame at `b196` with RAX the boolean `v`, `Done v`. -/
theorem done_of_epilogue (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) {v : Bool} (hx : reg m .rax = if v then 1 else 0) :
    Eventually (step1 Host.exe) (r.Done v) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b196Offset⟩ :=
  Eventually.mono (epilogue r hp hpre m hF) fun _ ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, h3.trans hx, h4, h5⟩

/-- **Returning `0`** from `b195`, where a layer has no codeword. -/
theorem fail_return (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) :
    Eventually (step1 Host.exe) (r.Done false) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b195Offset⟩ := by
  have hk := Sphincs.SphincsVerify.b195_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) 0
  have hm : Sym.Match (r.env m (fun _ ↦ 0) 0) (Sym.init [frameRegion, 16, 8, 8] [(.rsp, .ptr 0 0)]) m :=
    Sym.match_ofMachine ⟨rfl, rfl, rfl, rfl, trivial⟩
      ⟨by show rspOf m = r.base + BitVec.ofInt 64 0; simp only [BitVec.ofInt_ofNat,
        BitVec.add_zero]; exact hF.1, trivial⟩ trivial trivial trivial
  refine Sym.exec_then hk b195_exec hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  obtain ⟨m', pc⟩ := st
  simp only [Sym.PcOk] at hpc
  subst hpc
  exact done_of_epilogue r hp hpre m' (Run.Frame.of_match r hpre hF hm' hwf rfl rfl)
    (hm'.regs .rax _ rfl)

end

end NativeRustcX64.SphincsVerifyProof
