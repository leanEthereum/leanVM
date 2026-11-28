module

public import NativeRustcArm.WotsLeaf.Chain.Basic

/-!
# A chain's step, its end: the final block, `keccak_f`, the new value

From B's 64 buffered bytes `T` at `1632` and A's zero state at `1776`: `b37`, `b38` zero the block
at `2504` and copy `T` there (`seg_b37`), `b39` XORs the padded block into A's state and calls
`keccak_f` (`seg_b39`), `b40` copies A's first 16 bytes to the chain's value at `1384` and goes
back to the step's head `b15` or, after position 2, on to `b41` (`seg_b40`).
-/

namespace NativeRustcArm.WotsLeafProof.Chain

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf
open NativeRustcArm.SphincsVerifyProof.InlineTh

@[expose] public section

/-- What follows a step that leaves the chain's value `th` of the padded `T`: from the state
after `b40`, at `b15` for the next step or `b41` after position 2. -/
def StepCont [NativeRustcArm.Host] (r : Run) (x E : List UInt8) (pos i : Nat) (T : List UInt8)
    (R : MachineState → Prop) : Prop :=
  ∀ m', r.CK x E m' → r.SRegs m' (pos + 1) i →
    BytesAt m'.dmem (r.off 1384)
      ((Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T))).take 16) →
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcArm.Xmss.WotsLeaf.b41Offset else r.pc NativeRustcArm.Xmss.WotsLeaf.b15Offset⟩

end

public section

variable [NativeRustcArm.Host] {r : Run}

/-- **`b40`**: the first 16 bytes of hasher A become the chain's value; on to the next step or,
after position 2, to `b41`. -/
theorem seg_b40 (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) {x E : List UInt8}
    {pos i : Nat} (hpos : pos ≤ 2) {A : List UInt8} (hA16 : 16 ≤ A.length)
    {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m) (hR : r.SRegs m (pos + 1) i)
    (hA : BytesAt m.dmem (r.off 1776) A)
    (cont : ∀ m', r.CK x E m' → r.SRegs m' (pos + 1) i → BytesAt m'.dmem (r.off 1384) (A.take 16) →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcArm.Xmss.WotsLeaf.b41Offset else r.pc NativeRustcArm.Xmss.WotsLeaf.b15Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b40Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK.1.1 (knownK hR (k := []) trivial)
  refine blk r hp b40_in_code (List.cons_ne_nil _ _) run_b40 hwf hm fun st hm1 hpc ↦ ?_
  have hK1 := CK.of_block hpre hK hm1 hwf (by decide +kernel) (by decide +kernel)
  have hval := frame_copy16 hm1 (o := 1384) (o' := 1776) (by decide) (by decide +kernel)
    (by decide +kernel) (bs := A.take 16) (by simp; omega) (take_of_bytesAt hA 16)
  refine pc_at ?_ (cont _ hK1 (SRegs.of_block hm1 rfl rfl rfl rfl rfl rfl hR) hval)
  have h22 : (r.env st.data).regs .X22 = BitVec.ofNat 64 (pos + 1) := by
    show (st.data.regs.getXReg .X22).toBitVec = _
    exact (SRegs.of_block hm1 rfl rfl rfl rfl rfl rfl hR).2.2.2.2.1
  have h22' : (r.env m).regs .X22 = BitVec.ofNat 64 (pos + 1) := hR.2.2.2.2.1
  rw [pc_cond hpc (b := !decide (pos + 1 = 3)) (by
    sym_simp
    rw [h22']
    obtain rfl | rfl | rfl : pos = 0 ∨ pos = 1 ∨ pos = 2 := by omega
    all_goals rfl)]
  by_cases h3 : pos + 1 = 3
  · simp only [h3, decide_true, Bool.not_true, ite_true]
    rfl
  · simp only [h3, decide_false, Bool.not_false, ite_true, ite_false]
    exact Run.label_of_block r hp b15_in_code rfl

/-- **`b39`**: the padded block XORed into hasher A's zero state, `keccak_f`; then `b40`. -/
theorem seg_b39 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {pos i : Nat} (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64)
    {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m) (hR : r.SRegs m (pos + 1) i)
    (h26 : Run.RegIs m .X26 (BitVec.ofNat 64 64))
    (hA0 : BytesAt m.dmem (r.off 1776) (List.replicate 200 0))
    (hblk : BytesAt m.dmem (r.off 2504) (T ++ List.replicate 72 0))
    (cont : StepCont r x E pos i T R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b39Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK.1.1 (knownK hR (k := [(.X26, .lit 64)]) ⟨known_lit h26, trivial⟩)
  refine blk r hp b39_in_code (List.cons_ne_nil _ _) run_b39 hwf hm fun st hm1 hpc ↦ ?_
  have hK1 := CK.of_block hpre hK hm1 hwf (by decide +kernel) (by decide +kernel)
  have hxor := xorFinal hm1 hwf (r := 0) (b := r.base) (sz := 2752) rfl (oA := 1776)
    (oK := 2504) (by decide) (by decide +kernel) hT (by decide) hblk
  have hz : bytesOf m.dmem (r.off 1776) 200 = List.replicate 200 0 := by
    have := bytesOf_of_bytesAt hA0
    rwa [List.length_replicate] at this
  have hxor' : BytesAt st.data.dmem (r.off 1776)
      (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)) := by
    rw [← hz]
    exact hxor
  have h0 : Run.RegIs st.data .X0 (r.off 1776) := regIs_ptr hm1 rfl
  have hR1 := SRegs.of_block hm1 rfl rfl rfl rfl rfl rfl hR
  refine callAt hpc hc.2.2.2.2 ?_
  obtain ⟨hpre2, hpost2⟩ := keccakFrame hpre hK1.1 h0 (by decide) (cSlots_off r x (by decide))
    (Keccak.length_stateBytes _) hxor'
  refine ⟨hpre2, fun m2 hQ ↦ ?_⟩
  obtain ⟨hK2, hS2, hkc, hk2⟩ := hpost2 m2 hQ
  exact seg_b40 hp hpre hpos (by rw [Keccak.keccakF, Keccak.length_stateBytes]; decide)
    (CK.of_call hK1 hK2 hkc (by decide)) (SRegs.of_saved hS2 hR1) hk2 cont

/-- **`b37`, `b38`**: the block at `2504` zeroed, B's 64 buffered bytes copied there; then
`b39`. -/
theorem seg_b37 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {pos i : Nat} (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64)
    {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m) (hR : r.SRegs m (pos + 1) i)
    (h26 : Run.RegIs m .X26 (BitVec.ofNat 64 64))
    (hA0 : BytesAt m.dmem (r.off 1776) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 1632) T) (cont : StepCont r x E pos i T R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b37Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK.1.1 (knownK hR (k := [(.X26, .lit 64)]) ⟨known_lit h26, trivial⟩)
  refine blk r hp b37_in_code (List.cons_ne_nil _ _) run_b37 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b38Offset) ((pc_false hpc).trans rfl) ?_
  refine blk r hp b38_in_code (List.cons_ne_nil _ _) (exec_after run_b37 run_b38) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hK2 := CK.of_block hpre hK hm2 hwf (by decide +kernel) (by decide +kernel)
  have hz := frame_write_zero hm2 (o := 2568) (n := 72) (by decide) (by decide +kernel)
  have hA0' := r.bytesAt_kept hpre hm2 hwf (by rw [List.length_replicate]; decide) hA0
    (by decide +kernel)
  have hB' := r.bytesAt_kept hpre hm2 hwf (by omega) hB (by rw [hT]; decide +kernel)
  have h0 : Run.RegIs st2.data .X0 (r.off 2504) := regIs_ptr hm2 rfl
  have h1 : Run.RegIs st2.data .X1 (r.off 1632) := regIs_ptr hm2 rfl
  have h2 := x2_eq hm2 (c := 64) rfl (by decide)
  have h26' : Run.RegIs st2.data .X26 (BitVec.ofNat 64 64) := regIs_lit hm2 rfl
  have hR2 := SRegs.of_block hm2 rfl rfl rfl rfl rfl rfl hR
  refine callAt hpc2 hc.1 ?_
  obtain ⟨hpre3, hpost3⟩ := memcpyFrame hpre hK2.1 h0 h1 h2 (by decide) (by decide) (by decide)
    (cSlots_off r x (by decide)) hT hB'
  refine ⟨hpre3, fun m3 hQ ↦ ?_⟩
  obtain ⟨hK3, hS3, hkc, hT3⟩ := hpost3 m3 hQ
  have hz3 := hkc 2568 _ (by rw [List.length_replicate]; decide) (Or.inr (by decide)) hz
  have hA3 := hkc 1776 _ (by rw [List.length_replicate]; decide)
    (Or.inl (by rw [List.length_replicate]; decide)) hA0'
  exact seg_b39 hp hc hpre hpos hT (CK.of_call hK2 hK3 hkc (by decide)) (SRegs.of_saved hS3 hR2)
    (RegIs.of_saved hS3 rfl h26') hA3 (BytesAt.cat hT3 hz3 (by rw [hT])) cont

end

end NativeRustcArm.WotsLeafProof.Chain
