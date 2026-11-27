module

public import NativeRustcArm.SphincsVerify.Chains.Outer

/-!
# A chain's end stored, a chain's head

`b104` stores chain `i`'s end at `20464 + 16 i` and goes on with chain `i + 1` or to `b134`
(`seg_b104`); `b105` reads chain `i`'s digit and value (`seg_b105`), then the chain's steps.
Their symbolic states index the frame by the chain: `b104`'s regions are the spills, the end's
16 bytes and the chain's value; `b105`'s the codeword, the chain's value in the signature, the
chain's value and the spills `408 .. 424`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

public section

variable [ElfHost] {r : Run}

/-- The frame's bytes `a .. a + n` and `a' .. a' + n'`, apart, as regions. -/
theorem apart_regions (hpre : r.Pre) {a n a' n' : Nat} (ha : a + n ≤ 21616)
    (ha' : a' + n' ≤ 21616) (h : a + n ≤ a' ∨ a' + n' ≤ a) :
    (fun e e' : BitVec 64 × Nat ↦ Apart e.1 e.2 e'.1 e'.2) (r.off a, n) (r.off a', n') :=
  r.apart_off hpre ha ha' h

/-- **`b104`**: chain `i`'s end stored after the ends so far; on to chain `i + 1`, or `b134`
after chain 63. -/
theorem seg_b104 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) {i : Nat} (hi : i < 64) (hEl : E.length = 16 * i)
    {e : List UInt8} (he : e.length = 16) {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r l x E m) (hw416 : r.WordAt m 416 i.toUInt64)
    (hcell : BytesAt m.dmem (r.off 8224) e)
    (cont : ∀ m', Keep r l x (E ++ e) m' → Run.RegIs m' .X1 (BitVec.ofNat 64 (i + 1)) →
      Eventually (elfStep1 ElfHost.exe) R
        ⟨m', if i + 1 = 64 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b134Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b105Offset⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b104Offset⟩ := by
  have hF := hK.1
  obtain ⟨m0, w0⟩ := r.frame_mapped hpre hF (a := 0) (n := 448) (by decide)
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF (a := 20464 + 16 * i) (n := 16) (by omega)
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF (a := 8224) (n := 16) (by decide)
  have hwf : (Env.ofMachine m [(r.off 0, 448), (r.off (20464 + 16 * i), 16),
      (r.off 8224, 16)]).WF :=
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
  have hld416 : (Env.ofMachine m [(r.off 0, 448), (r.off (20464 + 16 * i), 16),
      (r.off 8224, 16)]).load 0 416 8 = BitVec.ofNat 64 i := by
    have hb : BytesAt m.dmem (r.off 0 + BitVec.ofNat 64 416) (wordBytes i.toUInt64) := by
      rw [r.off_add]; exact hw416
    rw [Env.load_of_bytesAt (NativeRustc.length_wordBytes _) hb, ofInt_ofBytes_wordBytes]
    rfl
  have hm : Match (Env.ofMachine m [(r.off 0, 448), (r.off (20464 + 16 * i), 16),
      (r.off 8224, 16)]) s104 m := by
    refine match_ofMachine ⟨rfl, fun _ ↦ by rw [Run.off_zero]; exact r.base_aligned hpre, rfl,
      fun h ↦ Bool.noConfusion h, rfl, fun h ↦ Bool.noConfusion h, trivial⟩ ?_ ⟨?_, trivial⟩ trivial
      trivial ⟨?_, ?_, ?_, trivial⟩
    · show m.regs.SP.toBitVec = r.off 0 + BitVec.ofInt 64 0
      rw [off_add_ofInt 0 (b := 0) (by simp), Run.off_zero]
      exact hF.1
    · show (m.regs.getXReg .X29).toBitVec = r.off 8224 + BitVec.ofInt 64 13296
      rw [off_add_ofInt 8224 (b := 21520) (by omega)]
      exact hF.2.1
    · show BinOp.apply .add .W64 (r.off 0 + BitVec.ofInt 64 20464)
        (UnOp.apply (.shift .LSL 4) .W64 ((Env.ofMachine m [(r.off 0, 448), (r.off (20464 + 16 * i), 16),
          (r.off 8224, 16)]).load 0 416 8)) =
          r.off (20464 + 16 * i) + BitVec.ofInt 64 0
      rw [hld416]
      sym_simp
      rw [shl4 (by omega), off_add_ofInt 0 (b := 20464) (by omega), r.off_add,
        off_add_ofInt _ (b := 20464 + 16 * i) (by simp)]
    · show r.off 0 + BitVec.ofInt 64 8224 = r.off 8224 + BitVec.ofInt 64 0
      rw [off_add_ofInt 0 (b := 8224) (by omega), off_add_ofInt 8224 (b := 8224) (by omega)]
    · show r.off 0 + BitVec.ofInt 64 8232 = r.off 8224 + BitVec.ofInt 64 8
      rw [off_add_ofInt 0 (b := 8232) (by omega), off_add_ofInt 8224 (b := 8232) (by omega)]
  refine blk r hp b104_in_code (List.cons_ne_nil _ _) run_b104 hwf hm fun st hm1 hpc ↦ ?_
  have hslot := copy16_gen hm1 (k := 1) (b := r.off (20464 + 16 * i)) rfl (o := 0) (by decide)
    (k' := 2) (o' := 0) (by decide +kernel) (by decide +kernel) he (bytesAt_add_zero hcell)
  have hsp : st.data.regs.SP.toBitVec = r.base := by
    rw [hm1.sp]
    show r.off 0 + BitVec.ofInt 64 0 = r.base
    rw [off_add_ofInt 0 (b := 0) (by simp), Run.off_zero]
  have h29 : Run.RegIs st.data .X29 (r.off 21520) := by
    unfold Run.RegIs
    rw [hm1.regs .X29 _ rfl]
    exact off_add_ofInt 8224 (by omega)
  have hK1 := Keep.of_change hpre hx (by omega) hK (a := 20464 + 16 * i) (n := 16) (by omega)
    (Or.inr (Or.inr (by omega))) hsp h29 (reg_same hm1 rfl) (reg_same hm1 rfl) (reg_same hm1 rfl)
    (reg_same hm1 rfl) (sameOutside_region hm1 hwf (k := 1) rfl (by decide +kernel)) (hm1.kept hwf)
  have hE' : BytesAt st.data.dmem (r.off 20464) (E ++ e) :=
    BytesAt.cat hK1.2.2.2.2.2.2.2.2 (by simpa using hslot) (by rw [hEl])
  have h1 : Run.RegIs st.data .X1 (BitVec.ofNat 64 (i + 1)) := by
    unfold Run.RegIs
    rw [hm1.regs .X1 _ rfl]
    show BinOp.apply .add .W64 ((Env.ofMachine m [(r.off 0, 448), (r.off (20464 + 16 * i), 16),
      (r.off 8224, 16)]).load 0 416 8) (BitVec.ofNat 64 1) = _
    rw [hld416]
    sym_simp
    rw [BitVec.ofNat_add]
  refine pc_at (a := if i + 1 = 64 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b134Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b105Offset) ?_ (cont _ (hK1.extend hE') h1)
  rw [pc_cond hpc, labelAt r hp b134_in_code rfl]
  sym_simp
  rw [hld416, ← BitVec.ofNat_add, beq_ofNat (by omega) (by omega)]
  by_cases h : i + 1 = 64 <;> simp [h]
  rfl

end

end NativeRustcArm.SphincsVerifyProof.Chains
