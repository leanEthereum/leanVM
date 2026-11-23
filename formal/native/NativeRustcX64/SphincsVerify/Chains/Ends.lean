module

public import NativeRustcX64.SphincsVerify.Chains.Outer

/-!
# A chain's end stored on x86-64

`b116` stores chain `i`'s end at `28296 + 16 i` (the address RSP plus `176(%rsp)`) and goes on
with chain `i + 1` or, after chain 63, to `b151` (`seg_b116`). Its symbolic state: region 0 the
frame's first 28296 bytes, region 1 the end's 16 bytes.
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

public section

variable [Host] {r : Run}

/-- The frame's bytes `a .. a + n` and `a' .. a' + n'`, apart, as regions. -/
theorem apart_regions (hpre : r.Pre) {a n a' n' : Nat} (ha : a + n ≤ 29400)
    (ha' : a' + n' ≤ 29400) (h : a + n ≤ a' ∨ a' + n' ≤ a) :
    (fun e e' : BitVec 64 × Nat ↦ Apart e.1 e.2 e'.1 e'.2) (r.off a, n) (r.off a', n') :=
  r.apart_off hpre ha ha' h

/-- **`b116`**: chain `i`'s end stored after the ends so far; on to chain `i + 1`, or `b151`
after chain 63. -/
theorem seg_b116 (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) {i : Nat} (hi : i < 64) (hEl : E.length = 16 * i)
    {e : List UInt8} (he : e.length = 16) {R : MachineState → Prop} {m : MachineData}
    (hF : r.Frame m) (hK : KeepRest r l x E m) (h80 : r.WordAt m 80 i.toUInt64)
    (h168 : r.WordAt m 176 (16 * i).toUInt64) (h12 : Run.RegIs m .r12 (r.off 4104))
    (hcell : BytesAt m.dmem (r.off 1592) e)
    (hf : Funcs m)
    (cont : ∀ m', r.Frame m' → KeepRest r l x (E ++ e) m' →
      Run.RegIs m' .rax (BitVec.ofNat 64 (i + 1)) → Run.RegIs m' .r12 (r.off 4104) → Funcs m' →
      Eventually (step1 Host.exe) R ⟨m', if i + 1 = 64 then r.pc NativeRustcX64.Sphincs.SphincsVerify.b151Offset else r.pc NativeRustcX64.Sphincs.SphincsVerify.b117Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b116Offset⟩ := by
  obtain ⟨m0, w0⟩ := r.frame_mapped hpre hF.2.2.2 (a := 0) (n := 28296) (by decide)
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF.2.2.2 (a := 28296 + 16 * i) (n := 16) (by omega)
  have hwf : (Env.ofMachine m [(r.off 0, 28296), (r.off (28296 + 16 * i), 16)]).WF :=
    Env.wf_of ⟨⟨m0, w0⟩, ⟨m1, w1⟩, trivial⟩
      (List.pairwise_pair.mpr (apart_regions hpre (by decide) (by omega) (by omega)))
  have hm : Match (Env.ofMachine m [(r.off 0, 28296), (r.off (28296 + 16 * i), 16)]) s116 m := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨?_, trivial⟩ trivial trivial ⟨?_, trivial⟩
    · show m.regs.get64 .rsp = r.off 0 + BitVec.ofInt 64 0
      rw [off_add_ofInt 0 (b := 0) (by simp), off_zero']
      exact hF.1
    · show BinOp.apply .add .W64 (r.off 0 + BitVec.ofInt 64 0)
        ((Env.ofMachine m [(r.off 0, 28296), (r.off (28296 + 16 * i), 16)]).load 0 176 8) =
          r.off (28296 + 16 * i) + BitVec.ofInt 64 (-28296)
      rw [load0_word h168, toBitVec_toUInt64, off_add_ofInt 0 (b := 0) (by simp),
        off_add_ofInt (28296 + 16 * i) (b := 16 * i) (by omega)]
      simp only [BinOp.apply, low_W64, ext_W64]
      rw [Run.off_add, Nat.zero_add]
  refine blk r hp b116_in_code (List.cons_ne_nil _ _) run_b116 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  have hslot := copy16 hm1 (k := 1) (b := r.off (28296 + 16 * i)) rfl (o := 0) (by decide)
    (k' := 0) (o' := 1592) (by decide +kernel) (by decide +kernel) he (by
      show BytesAt m.dmem (r.off 0 + BitVec.ofNat 64 1592) e
      rw [Run.off_add]
      exact hcell)
  have hout := sameOutside_region hm1 hwf (k := 1) rfl (by decide +kernel)
  have hsp : rspOf st.data = r.base := by
    rw [rspOf, hm1.regs .rsp _ rfl]
    show r.off 0 + BitVec.ofInt 64 0 = r.base
    rw [off_add_ofInt 0 (b := 0) (by simp), off_zero']
  have hF1 : r.Frame st.data :=
    Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 hsp hout
      (fun _ hp ↦ r.inRange_off hpre (a := 28296 + 16 * i) (n := 16) (by omega) hp) (hm1.kept hwf)
  have hK1 := KeepRest.of_change hx (by omega) hK hout
    (fun o ho hk ↦ r.not_inRange_off hpre (by omega) ho (by omega)) (reg_same hm1 rfl)
  have hE' : BytesAt st.data.dmem (r.off 28296) (E ++ e) :=
    BytesAt.cat hK1.2.2.2.2 (BytesAt.of_add_zero hslot) (by rw [hEl])
  have h0 : Run.RegIs st.data .rax (BitVec.ofNat 64 (i + 1)) := by
    unfold Run.RegIs reg
    rw [hm1.regs .rax _ rfl]
    show BinOp.apply .add .W64
      ((Env.ofMachine m [(r.off 0, 28296), (r.off (28296 + 16 * i), 16)]).load 0 80 8)
        (BitVec.ofNat 64 1) = _
    rw [load0_word h80, toBitVec_toUInt64]
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [BitVec.ofNat_add]
  have h12' : Run.RegIs st.data .r12 (r.off 4104) := by
    unfold Run.RegIs reg
    rw [reg_same hm1 rfl]
    exact h12
  refine pc_at (a := if i + 1 = 64 then r.pc NativeRustcX64.Sphincs.SphincsVerify.b151Offset else r.pc NativeRustcX64.Sphincs.SphincsVerify.b117Offset) ?_
    (cont _ hF1 (hK1.extend hE') h0 h12'
      ⟨regIs_reg hm1 rfl hf.1, regIs_reg hm1 rfl hf.2⟩)
  rw [pc_cond hpc, labelAt r hp b151_in_code rfl]
  have hl : (Env.ofMachine m [(r.off 0, 28296), (r.off (28296 + 16 * i), 16)]).load 0 80 8 =
      BitVec.ofNat 64 i := load0_word h80
  sym_simp
  rw [hl, ← BitVec.ofNat_add, beq_ofNat (by omega) (by omega)]
  by_cases h : i + 1 = 64 <;> simp [h]
  rfl

end

end NativeRustcX64.SphincsVerifyProof.Chains
