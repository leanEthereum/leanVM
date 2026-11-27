module

public import NativeRustcArm.SphincsVerify.Frame
public import NativeRustcArm.Sym
public import NativeRustcArm.Hasher.Bytes
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify.Part5

/-!
# `sphincs_verify`'s epilogue

`b179` (`.LBB3_84`): SP back to the entry's, the callee-saved registers
and X29, X30 reloaded from the frame's top, `ret`. From any state of the frame it returns to the
caller with the registers of the entry and X0 as it was (`epilogue`); with X0 the boolean `v`,
that is `Done v` (`done_of_epilogue`). `b178` (`mov x0, xzr`) falls into it:
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
/-- A saved register in the frame: the word at `21520 + 8 j`. -/
theorem load_saved {m : MachineData} (hF : r.Frame m) (vars : Nat → BitVec 64)
    (j o : Nat) (ho : o = 21520 + 8 * j) (hj : j < 12) (x : UInt64)
    (hx : ((savedBytes r.m0).drop (8 * j)).take 8 = wordBytes x) :
    (r.env m vars).load 0 o 8 = x.toBitVec := by
  have h := bytesAt_slice hF.2.2.1 (8 * j) 8 (by rw [length_savedBytes]; omega)
  rw [hx, off, Sym.addr_add] at h
  rw [Sym.Env.load_of_bytesAt (length_wordBytes x) (by rw [ho]; exact h),
    ofInt_ofBytes_wordBytes]

/-- SP at the entry: the frame's end. -/
theorem base_add_frame (hpre : r.Pre) :
    r.base + BitVec.ofInt 64 21616 = r.m0.regs.SP.toBitVec := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  apply BitVec.eq_of_toNat_eq
  rw [show BitVec.ofInt 64 21616 = BitVec.ofNat 64 21616 from rfl, Sym.toNat_add_ofNat _ _ (by omega),
    sp_toNat]
  omega

end Run

sym_block b179_exec := Sym.exec Sphincs.SphincsVerify.b179 (Sym.init [(21616, true)] (.ptr 0 0))

sym_block b178_exec := Sym.exec Sphincs.SphincsVerify.b178
  (Sym.init [(21616, true)] (.ptr 0 0) [(.X29, .ptr 0 21520)])

variable [ElfHost]

/-- **The epilogue**: from a state of the frame at `b179`, the machine returns to the caller with
X0 as it was, no byte changed outside the stack area, and the entry's callee-saved registers, SP
and mapped bytes. -/
theorem epilogue (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = retOf r.m0 ∧
      st.data.regs.X0 = m.regs.X0 ∧ SameOutside r.m0.dmem st.data.dmem r.StackArea ∧
      Saved r.m0 st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b179Offset⟩ := by
  have hk := Sphincs.SphincsVerify.b179_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm := r.match_frame hpre hF (vars := fun _ ↦ 0) (known := []) (labels := []) (bounds := [])
    (aliases := []) trivial trivial trivial trivial
  refine Sym.exec_then_elf hk b179_exec hwf hm fun st hm' hpc ↦ .done _ ?_
  have ls := fun j o ho hj x hx ↦ r.load_saved hF (fun _ ↦ 0) j o ho hj x hx
  have hreg : ∀ x : XReg, calleeSaved x = true ∨ x = .X30 →
      st.data.regs.getXReg x = r.m0.regs.getXReg x := by
    intro x hx
    apply UInt64.toBitVec_inj.mp
    cases x <;> simp only [calleeSaved, reduceCtorEq, or_false, or_true, Bool.false_eq_true]
      at hx
    · exact (hm'.regs .X19 _ rfl).trans (ls 11 21608 rfl (by decide) _ rfl)
    · exact (hm'.regs .X20 _ rfl).trans (ls 10 21600 rfl (by decide) _ rfl)
    · exact (hm'.regs .X21 _ rfl).trans (ls 9 21592 rfl (by decide) _ rfl)
    · exact (hm'.regs .X22 _ rfl).trans (ls 8 21584 rfl (by decide) _ rfl)
    · exact (hm'.regs .X23 _ rfl).trans (ls 7 21576 rfl (by decide) _ rfl)
    · exact (hm'.regs .X24 _ rfl).trans (ls 6 21568 rfl (by decide) _ rfl)
    · exact (hm'.regs .X25 _ rfl).trans (ls 5 21560 rfl (by decide) _ rfl)
    · exact (hm'.regs .X26 _ rfl).trans (ls 4 21552 rfl (by decide) _ rfl)
    · exact (hm'.regs .X27 _ rfl).trans (ls 3 21544 rfl (by decide) _ rfl)
    · exact (hm'.regs .X28 _ rfl).trans (ls 2 21536 rfl (by decide) _ rfl)
    · exact (hm'.regs .X29 _ rfl).trans (ls 0 21520 rfl (by decide) _ rfl)
    · exact (hm'.regs .X30 _ rfl).trans (ls 1 21528 rfl (by decide) _ rfl)
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

/-- **Returning `v`**: from a state of the frame at `b179` with X0 the boolean `v`, `Done v`. -/
theorem done_of_epilogue (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) {v : Bool} (hx : m.regs.X0 = if v then 1 else 0) :
    Eventually (elfStep1 ElfHost.exe) (r.Done v) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b179Offset⟩ :=
  NativeRustcArm.Eventually.mono_elf (epilogue r hp hpre m hF) fun _ ⟨h1, h2, h3, h4⟩ ↦
    ⟨h1, h2.trans hx, h3, h4⟩

/-- **Returning `0`** from `b178`, where a layer has no codeword. -/
theorem fail_return (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    (m : MachineData) (hF : r.Frame m) :
    Eventually (elfStep1 ElfHost.exe) (r.Done false) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b178Offset⟩ := by
  have hk := Sphincs.SphincsVerify.b178_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm := r.match_frame hpre hF (vars := fun _ ↦ 0) (known := [(.X29, .ptr 0 21520)])
    (labels := []) (bounds := []) (aliases := []) ⟨hF.2.1, trivial⟩ trivial trivial trivial
  refine Sym.exec_then_elf hk b178_exec hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨m', pc⟩ := st
  simp only [Sym.PcOk] at hpc
  subst hpc
  exact done_of_epilogue r hp hpre m' (Run.Frame.of_match r hpre hF hm' hwf rfl rfl rfl)
    (UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl))

end

end NativeRustcArm.SphincsVerifyProof
