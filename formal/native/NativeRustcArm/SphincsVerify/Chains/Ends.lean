module

public import NativeRustcArm.SphincsVerify.Chains.Outer

/-!
# A chain's end stored, a chain's head

`b113` stores chain `i`'s end at `28224 + 16 i` and goes on with chain `i + 1` or to `b143`
(`seg_b113`); `b114` reads chain `i`'s digit and value (`seg_b114`), then the chain's steps.
Their symbolic states index the frame by the chain: `b113`'s regions are the spills, the end's
16 bytes and the chain's value; `b114`'s the codeword, the chain's value in the signature and the
chain's value.
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

public section

variable [NativeRustcArm.Host] {r : Run}

/-- The frame's bytes `a .. a + n` and `a' .. a' + n'`, apart, as regions. -/
theorem apart_regions (hpre : r.Pre) {a n a' n' : Nat} (ha : a + n ≤ 29376)
    (ha' : a' + n' ≤ 29376) (h : a + n ≤ a' ∨ a' + n' ≤ a) :
    (fun e e' : BitVec 64 × Nat ↦ Apart e.1 e.2 e'.1 e'.2) (r.off a, n) (r.off a', n') :=
  r.apart_off hpre ha ha' h

/-- **`b113`**: chain `i`'s end stored after the ends so far; on to chain `i + 1`, or `b143`
after chain 63. -/
theorem seg_b113 (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) {i : Nat} (hi : i < 64) (hEl : E.length = 16 * i)
    {e : List UInt8} (he : e.length = 16) {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r l x E m) (h28 : Run.RegIs m .X28 (BitVec.ofNat 64 i))
    (hcell : BytesAt m.dmem (r.off 15984) e)
    (cont : ∀ m', Keep r l x (E ++ e) m' → Run.RegIs m' .X0 (BitVec.ofNat 64 (i + 1)) →
      Run.RegIs m' .X8 (r.off (12900 + 1028 * l)) →
      Eventually (step1 NativeRustcArm.Host.exe) R
        ⟨m', if i + 1 = 64 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b143Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b114Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b113Offset⟩ := by
  have hF := hK.1
  obtain ⟨m0, w0⟩ := r.frame_mapped hpre hF (a := 0) (n := 432) (by decide)
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := 28224 + 16 * i) (n := 16) (by omega)
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF (a := 15984) (n := 16) (by decide)
  have hwf : (Env.ofMachine m [(r.off 0, 432), (r.off (28224 + 16 * i), 16),
      (r.off 15984, 16)]).WF :=
    Env.wf_of ⟨⟨m0, w0⟩, ⟨m1, w1⟩, ⟨m2, w2⟩, trivial⟩
      (List.Pairwise.cons (fun e he ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl
          · exact apart_regions hpre (by decide) (by omega) (by omega)
          · exact apart_regions hpre (by decide) (by decide) (by omega))
        (List.Pairwise.cons (fun e he ↦ by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            subst he
            exact apart_regions hpre (by omega) (by decide) (by omega))
          (List.Pairwise.cons (fun _ h ↦ nomatch h) List.Pairwise.nil)))
  have hm : Match (Env.ofMachine m [(r.off 0, 432), (r.off (28224 + 16 * i), 16),
      (r.off 15984, 16)]) s113 m := by
    refine match_ofMachine ⟨rfl, fun _ ↦ by rw [Run.off_zero]; exact r.base_aligned hpre, rfl,
      fun h ↦ Bool.noConfusion h, rfl, fun h ↦ Bool.noConfusion h, trivial⟩ ?_ ⟨?_, trivial⟩ trivial
      trivial ⟨?_, ?_, ?_, trivial⟩
    · show m.regs.SP.toBitVec = r.off 0 + BitVec.ofInt 64 0
      rw [off_add_ofInt 0 (b := 0) (by simp), Run.off_zero]
      exact hF.1
    · show (m.regs.getXReg .X29).toBitVec = r.off 15984 + BitVec.ofInt 64 13296
      rw [off_add_ofInt 15984 (b := 29280) (by omega)]
      exact hF.2.1
    · show BinOp.apply .add .W64 (r.off 0 + BitVec.ofInt 64 28224)
        (UnOp.apply (.shift .LSL 4) .W64 (m.regs.getXReg .X28).toBitVec) =
          r.off (28224 + 16 * i) + BitVec.ofInt 64 0
      rw [h28]
      sym_simp
      rw [shl4 (by omega), off_add_ofInt 0 (b := 28224) (by omega), r.off_add,
        off_add_ofInt _ (b := 28224 + 16 * i) (by simp)]
    · show r.off 0 + BitVec.ofInt 64 15984 = r.off 15984 + BitVec.ofInt 64 0
      rw [off_add_ofInt 0 (b := 15984) (by omega), off_add_ofInt 15984 (b := 15984) (by omega)]
    · show r.off 0 + BitVec.ofInt 64 15992 = r.off 15984 + BitVec.ofInt 64 8
      rw [off_add_ofInt 0 (b := 15992) (by omega), off_add_ofInt 15984 (b := 15992) (by omega)]
  refine blk r hp b113_in_code (List.cons_ne_nil _ _) run_b113 hwf hm fun st hm1 hpc ↦ ?_
  have hslot := copy16_gen hm1 (k := 1) (b := r.off (28224 + 16 * i)) rfl (o := 0) (by decide)
    (k' := 2) (o' := 0) (by decide +kernel) (by decide +kernel) he (bytesAt_add_zero hcell)
  have hsp : st.data.regs.SP.toBitVec = r.base := by
    rw [hm1.sp]
    show r.off 0 + BitVec.ofInt 64 0 = r.base
    rw [off_add_ofInt 0 (b := 0) (by simp), Run.off_zero]
  have h29 : Run.RegIs st.data .X29 (r.off 29280) := by
    unfold Run.RegIs
    rw [hm1.regs .X29 _ rfl]
    exact off_add_ofInt 15984 (by omega)
  have hK1 := Keep.of_change hpre hx (by omega) hK (a := 28224 + 16 * i) (n := 16) (by omega)
    (Or.inr (Or.inr (by omega))) hsp h29 (reg_same hm1 rfl) (reg_same hm1 rfl) (reg_same hm1 rfl)
    (sameOutside_region hm1 hwf (k := 1) rfl (by decide +kernel)) (hm1.kept hwf)
  have hE' : BytesAt st.data.dmem (r.off 28224) (E ++ e) :=
    BytesAt.cat hK1.2.2.2.2.2.2.2 (by simpa using hslot) (by rw [hEl])
  have h0 : Run.RegIs st.data .X0 (BitVec.ofNat 64 (i + 1)) := by
    unfold Run.RegIs
    rw [hm1.regs .X0 _ rfl]
    show BinOp.apply .add .W64 (m.regs.getXReg .X28).toBitVec (BitVec.ofNat 64 1) = _
    rw [h28]
    sym_simp
    rw [BitVec.ofNat_add]
  obtain ⟨-, -, -, -, -, -, -, s8, -, -, -⟩ := hK.2.2.1
  have h8 : Run.RegIs st.data .X8 (r.off (12900 + 1028 * l)) := by
    unfold Run.RegIs
    rw [hm1.regs .X8 _ rfl]
    have hb : BytesAt m.dmem (r.off 0 + BitVec.ofNat 64 392) (wordBytes (r.addr (12900 + 1028 * l))) := by
      rw [r.off_add]
      exact s8
    show Env.load _ 0 392 8 = _
    rw [Env.load_of_bytesAt (NativeRustc.length_wordBytes _) hb, ofInt_ofBytes_wordBytes]
    rfl
  refine pc_at (a := if i + 1 = 64 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b143Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b114Offset) ?_ (cont _ (hK1.extend hE') h0 h8)
  rw [pc_cond hpc, labelAt r hp b143_in_code rfl]
  have h28' : (Env.ofMachine m [(r.off 0, 432), (r.off (28224 + 16 * i), 16),
      (r.off 15984, 16)]).regs .X28 = BitVec.ofNat 64 i := h28
  sym_simp
  rw [h28', ← BitVec.ofNat_add, beq_ofNat (by omega) (by omega)]
  by_cases h : i + 1 = 64 <;> simp [h]
  rfl

end

end NativeRustcArm.SphincsVerifyProof.Chains
