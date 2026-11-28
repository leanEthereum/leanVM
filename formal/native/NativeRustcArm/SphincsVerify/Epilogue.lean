module

public import NativeRustcArm.SphincsVerify.Frame
public import NativeRustcArm.Sym
public import NativeRustcArm.Hasher.Bytes
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify.Part5

/-!
# `sphincs_verify`'s epilogue

`b188` (`.LSphincsVerify_92`, directive 2781): SP back to the entry's, the callee-saved registers
and X29, X30 reloaded from the frame's top, `ret`. From any state of the frame it returns to the
caller with the registers of the entry and X0 as it was (`epilogue`); with X0 the boolean `v`,
that is `Done v` (`done_of_epilogue`). `b187` (directive 2779, `mov x0, xzr`) falls into it:
`Done false` (`fail_return`).
-/

namespace NativeRustcArm.SphincsVerifyProof

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

omit [Labels] in
/-- A saved register in the frame: the word at `29280 + 8 j`. -/
theorem load_saved {m : MachineData} (hF : r.Frame m) (vars : Nat → BitVec 64)
    (j o : Nat) (ho : o = 29280 + 8 * j) (hj : j < 12) (x : UInt64)
    (hx : ((savedBytes r.m0).drop (8 * j)).take 8 = wordBytes x) :
    (r.env m vars).load 0 o 8 = x.toBitVec := by
  have h := bytesAt_slice hF.2.2.1 (8 * j) 8 (by rw [length_savedBytes]; omega)
  rw [hx, off, Sym.addr_add] at h
  rw [Sym.Env.load_of_bytesAt (length_wordBytes x) (by rw [ho]; exact h),
    ofInt_ofBytes_wordBytes]

/-- SP at the entry: the frame's end. -/
theorem base_add_frame (hpre : r.Pre) :
    r.base + BitVec.ofInt 64 29376 = r.m0.regs.SP.toBitVec := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  apply BitVec.eq_of_toNat_eq
  rw [show BitVec.ofInt 64 29376 = BitVec.ofNat 64 29376 from rfl, Sym.toNat_add_ofNat _ _ (by omega),
    sp_toNat]
  omega

end Run

sym_block b188_exec := Sym.exec Sphincs.SphincsVerify.b188 (Sym.init [(29376, true)] (.ptr 0 0))

sym_block b187_exec := Sym.exec Sphincs.SphincsVerify.b187
  (Sym.init [(29376, true)] (.ptr 0 0) [(.X29, .ptr 0 29280)])

variable [NativeRustcArm.Host]

/-- **The epilogue**: from a state of the frame at `b188`, the machine returns to the caller with
X0 as it was, no byte changed outside the stack area, and the entry's callee-saved registers, SP
and mapped bytes. -/
theorem epilogue (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf r.m0 ∧
      st.data.regs.X0 = m.regs.X0 ∧ SameOutside r.m0.dmem st.data.dmem r.StackArea ∧
      Saved r.m0 st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b188Offset⟩ := by
  have hk := Sphincs.SphincsVerify.b188_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm := r.match_frame hpre hF (vars := fun _ ↦ 0) (known := []) (labels := []) (bounds := [])
    (aliases := []) trivial trivial trivial trivial
  refine Sym.exec_then hk b188_exec hwf hm fun st hm' hpc ↦ .done _ ?_
  have ls := fun j o ho hj x hx ↦ r.load_saved hF (fun _ ↦ 0) j o ho hj x hx
  have hreg : ∀ x : XReg, calleeSaved x = true ∨ x = .X30 →
      st.data.regs.getXReg x = r.m0.regs.getXReg x := by
    intro x hx
    apply UInt64.toBitVec_inj.mp
    cases x <;> simp only [calleeSaved, reduceCtorEq, or_false, or_true, Bool.false_eq_true]
      at hx
    · exact (hm'.regs .X19 _ rfl).trans (ls 11 29368 rfl (by decide) _ rfl)
    · exact (hm'.regs .X20 _ rfl).trans (ls 10 29360 rfl (by decide) _ rfl)
    · exact (hm'.regs .X21 _ rfl).trans (ls 9 29352 rfl (by decide) _ rfl)
    · exact (hm'.regs .X22 _ rfl).trans (ls 8 29344 rfl (by decide) _ rfl)
    · exact (hm'.regs .X23 _ rfl).trans (ls 7 29336 rfl (by decide) _ rfl)
    · exact (hm'.regs .X24 _ rfl).trans (ls 6 29328 rfl (by decide) _ rfl)
    · exact (hm'.regs .X25 _ rfl).trans (ls 5 29320 rfl (by decide) _ rfl)
    · exact (hm'.regs .X26 _ rfl).trans (ls 4 29312 rfl (by decide) _ rfl)
    · exact (hm'.regs .X27 _ rfl).trans (ls 3 29304 rfl (by decide) _ rfl)
    · exact (hm'.regs .X28 _ rfl).trans (ls 2 29296 rfl (by decide) _ rfl)
    · exact (hm'.regs .X29 _ rfl).trans (ls 0 29280 rfl (by decide) _ rfl)
    · exact (hm'.regs .X30 _ rfl).trans (ls 1 29288 rfl (by decide) _ rfl)
  refine ⟨?_, ?_, ?_, fun x hx ↦ hreg x (.inl hx), ?_, ?_⟩
  · rw [hpc]
    simp only [retOf]
    rw [show st.data.regs.X30 = r.m0.regs.X30 from hreg .X30 (.inr rfl)]
  · exact UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)
  · rw [hm'.dmem_eq hwf rfl]
    exact hF.2.2.2.1
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.sp]
    exact r.base_add_frame hpre
  · exact fun p h ↦ hm'.kept hwf p (hF.2.2.2.2 p h)

/-- **Returning `v`**: from a state of the frame at `b188` with X0 the boolean `v`, `Done v`. -/
theorem done_of_epilogue (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) {v : Bool} (hx : m.regs.X0 = if v then 1 else 0) :
    Eventually (step1 NativeRustcArm.Host.exe) (r.Done v) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b188Offset⟩ :=
  NativeRustcArm.Eventually.mono (epilogue r hp hpre m hF) fun _ ⟨h1, h2, h3, h4⟩ ↦
    ⟨h1, h2.trans hx, h3, h4⟩

/-- **Returning `0`** from `b187`, where a layer has no codeword. -/
theorem fail_return (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) :
    Eventually (step1 NativeRustcArm.Host.exe) (r.Done false) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b187Offset⟩ := by
  have hk := Sphincs.SphincsVerify.b187_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm := r.match_frame hpre hF (vars := fun _ ↦ 0) (known := [(.X29, .ptr 0 29280)])
    (labels := []) (bounds := []) (aliases := []) ⟨hF.2.1, trivial⟩ trivial trivial trivial
  refine Sym.exec_then hk b187_exec hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨m', pc⟩ := st
  simp only [Sym.PcOk] at hpc
  subst hpc
  exact done_of_epilogue r hp hpre m' (Run.Frame.of_match r hpre hF hm' hwf rfl rfl rfl)
    (UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl))

end

end NativeRustcArm.SphincsVerifyProof
