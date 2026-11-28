module

public import NativeRustcArm.WotsLeaf.Steps
public import NativeRustcArm.Hasher.Bytes
public meta import NativeRustcArm.Code.Xmss.WotsLeaf.Part0

/-!
# `wots_leaf`'s epilogue

`b12` (`.LWotsLeaf_6`, directive 164): SP back to the entry's, the callee-saved registers and
X29, X30 reloaded from the frame's top, `ret`. From a state with SP the frame's base, the saved
registers in place and the entry's mapped bytes, it returns to the caller with the registers of
the entry and memory as it was (`epilogue`).
-/

namespace NativeRustcArm.WotsLeafProof

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

namespace Run

variable (r : Run) [Labels]

omit [Labels] in
/-- A saved register in the frame: the word at `2656 + 8 j`. -/
theorem load_saved {m : MachineData} (hsv : BytesAt m.dmem (r.off 2656) (savedBytes r.m0))
    (vars : Nat → BitVec 64) (j o : Nat) (ho : o = 2656 + 8 * j) (x : UInt64)
    (hx : ((savedBytes r.m0).drop (8 * j)).take 8 = wordBytes x) :
    (r.env m vars).load 0 o 8 = x.toBitVec := by
  have h := BytesAt.slice hsv (8 * j) 8
  rw [hx, off, addr_add_add] at h
  rw [Sym.Env.load_of_bytesAt (length_wordBytes x) (by rw [ho]; exact h),
    ofInt_ofBytes_wordBytes]

/-- SP at the entry: the frame's end. -/
theorem base_add_frame (hpre : r.Pre) :
    r.base + BitVec.ofInt 64 2752 = r.m0.regs.SP.toBitVec := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  apply BitVec.eq_of_toNat_eq
  rw [show BitVec.ofInt 64 2752 = BitVec.ofNat 64 2752 from rfl, Sym.toNat_add_ofNat _ _ (by omega),
    sp_toNat]
  omega

end Run

sym_block b12_exec := Sym.exec Xmss.WotsLeaf.b12 (Sym.init [(2752, true)] (.ptr 0 0))

variable [NativeRustcArm.Host]

/-- **The epilogue**: from a state at `b12` with SP the frame's base, the saved registers in place
and the entry's mapped bytes still mapped, the machine returns to the caller with the entry's
callee-saved registers, SP and mapped bytes, memory as it was. -/
theorem epilogue (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre)
    (m : MachineData) (hsp : m.regs.SP.toBitVec = r.base)
    (hsv : BytesAt m.dmem (r.off 2656) (savedBytes r.m0)) (hk : Kept r.m0.dmem m.dmem) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf r.m0 ∧
      Saved r.m0 st.data ∧ ∀ p, st.data.dmem.get? p = m.dmem.get? p) ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b12Offset⟩ := by
  have hk' := Xmss.WotsLeaf.b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have h := r.frame_mapped_kept hpre hk (a := 0) (n := 2752) (by decide)
  rw [Run.off_zero] at h
  have hwf : (r.env m fun _ ↦ 0).WF := Sym.Env.wf_of ⟨h, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Sym.Match (r.env m fun _ ↦ 0) (Sym.init [(2752, true)] (.ptr 0 0)) m :=
    Sym.match_ofMachine ⟨rfl, fun _ ↦ r.base_aligned hpre, trivial⟩
      (by show m.regs.SP.toBitVec = r.base + BitVec.ofInt 64 0; simp only [BitVec.ofInt_ofNat,
        BitVec.add_zero]; exact hsp) trivial trivial trivial trivial
  refine Sym.exec_then hk' b12_exec hwf hm fun st hm' hpc ↦ .done _ ?_
  have ls := fun j o ho x hx ↦ r.load_saved hsv (fun _ ↦ 0) j o ho x hx
  have hreg : ∀ x : XReg, calleeSaved x = true ∨ x = .X30 →
      st.data.regs.getXReg x = r.m0.regs.getXReg x := by
    intro x hx
    apply UInt64.toBitVec_inj.mp
    cases x <;> simp only [calleeSaved, reduceCtorEq, or_false, or_true, Bool.false_eq_true]
      at hx
    · exact (hm'.regs .X19 _ rfl).trans (ls 11 2744 rfl _ rfl)
    · exact (hm'.regs .X20 _ rfl).trans (ls 10 2736 rfl _ rfl)
    · exact (hm'.regs .X21 _ rfl).trans (ls 9 2728 rfl _ rfl)
    · exact (hm'.regs .X22 _ rfl).trans (ls 8 2720 rfl _ rfl)
    · exact (hm'.regs .X23 _ rfl).trans (ls 7 2712 rfl _ rfl)
    · exact (hm'.regs .X24 _ rfl).trans (ls 6 2704 rfl _ rfl)
    · exact (hm'.regs .X25 _ rfl).trans (ls 5 2696 rfl _ rfl)
    · exact (hm'.regs .X26 _ rfl).trans (ls 4 2688 rfl _ rfl)
    · exact (hm'.regs .X27 _ rfl).trans (ls 3 2680 rfl _ rfl)
    · exact (hm'.regs .X28 _ rfl).trans (ls 2 2672 rfl _ rfl)
    · exact (hm'.regs .X29 _ rfl).trans (ls 0 2656 rfl _ rfl)
    · exact (hm'.regs .X30 _ rfl).trans (ls 1 2664 rfl _ rfl)
  have hsame : ∀ p, st.data.dmem.get? p = m.dmem.get? p := fun p ↦
    hm'.get?_mem0 hwf (fun ⟨w, hw, _⟩ ↦ by simp at hw) |>.trans rfl
  refine ⟨?_, ⟨fun x hx ↦ hreg x (.inl hx), ?_, ?_⟩, hsame⟩
  · rw [hpc]
    simp only [retOf]
    rw [show st.data.regs.X30 = r.m0.regs.X30 from hreg .X30 (.inr rfl)]
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.sp]
    exact r.base_add_frame hpre
  · exact fun p h ↦ by rw [hsame p]; exact hk p h

end

end NativeRustcArm.WotsLeafProof
