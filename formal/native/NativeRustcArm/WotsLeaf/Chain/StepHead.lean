module

public import NativeRustcArm.WotsLeaf.Chain.StepMid
public import NativeRustcArm.WotsLeaf.Chain.Bytes

/-!
# A chain's step, its head: the payload, the address, `P` and the address absorbed

`b15` copies the chain's value and the chain's index to the payload at `1400`, builds the step's
address at `2504`, then `memset`s hasher A (`seg_b15`); `b16`, `b19`, `b21 .. b23` buffer `P` (read
through X20, region 1) and copy the address into A's buffer (`seg_b16`); then `b24`.
-/

namespace NativeRustcArm.WotsLeafProof.Chain

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf
open LeanVM.Protocol.KeccakHash

public section

variable [NativeRustcArm.Host] {r : Run}

/-- **`b16`, `b19`, `b21 .. b23`**: `P` buffered in A, the address copied after it; then
`b24`. -/
theorem seg_b16 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {pos i : Nat} (hpos : pos ≤ 2) {ad P : List UInt8} (had : ad.length = 16)
    (hP : P.length = 32) {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m)
    (hR : r.SRegs m pos i) (hA0 : BytesAt m.dmem (r.off 1776) (List.replicate 344 0))
    (hadr : BytesAt m.dmem (r.off 2504) ad) (hpay : BytesAt m.dmem (r.off 1400) P)
    (cont : StepCont r x E pos i (r.pp ++ ad ++ P) R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b16Offset⟩ := by
  have hF := hK.1.1
  have hin := r.pre_pp hpre
  have hwf : (r.envR m [(r.m0.regs.X1.toBitVec, 16)]).WF := by
    refine r.frame_wfR hpre hF (rest := [(r.m0.regs.X1.toBitVec, 16)])
      ⟨⟨r.input_mapped hF.2.2.2.2 hin, hin.2.1⟩, trivial⟩ ?_
      (List.pairwise_singleton _ _) _
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    have := r.apart_input hpre (a := 0) (n' := 2752) (by decide) hin
    rwa [Run.off_zero] at this
  have h2112 : BytesAt m.dmem (r.off 2112) ((List.range 8).map (byteOf (BitVec.ofNat 64 0))) := by
    have := BytesAt.slice hA0 336 8
    rw [r.off_add, List.drop_replicate, List.take_replicate] at this
    rw [bytes_zero]
    exact this
  have hm0 := r.match_frameR hpre hF (vars := fun _ ↦ 0) (rest := [(r.m0.regs.X1.toBitVec, 16)])
    (srest := [(16, false)]) (known := (.X29, .ptr 0 2656) :: (.X20, .ptr 1 0) :: keptK)
    (labels := []) (bounds := []) (aliases := [])
    ⟨rfl, ⟨fun h ↦ absurd h (by decide), trivial⟩⟩
    ⟨hF.2.1.trans (eval_ptr0R m _ _ 2656).symm,
      by show _ = r.m0.regs.X1.toBitVec + BitVec.ofInt 64 0
         simpa [Run.RegIs] using hR.2.1,
      hR.1, hR.2.2.1.trans (eval_ptr0R m _ _ 1976).symm,
      hR.2.2.2.1.trans (eval_ptr0R m _ _ 1632).symm, trivial⟩
    trivial trivial trivial
  have hm := match_withLit hm0 rfl h2112
  refine blk r hp b16_in_code (List.cons_ne_nil _ _) run_b16 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b19Offset) ((pc_true hpc).trans (Run.label_of_block r hp b19_in_code rfl)) ?_
  refine blk r hp b19_in_code (List.cons_ne_nil _ _) (exec_after run_b16 run_b19) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b21Offset) (hpc2.trans (Run.label_of_block r hp b21_in_code rfl)) ?_
  refine blk r hp b21_in_code (List.cons_ne_nil _ _) (exec_after run_b19 run_b21) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b22Offset) ((pc_false hpc3).trans rfl) ?_
  refine blk r hp b22_in_code (List.cons_ne_nil _ _) (exec_after run_b21 run_b22) hwf hm3
    fun st4 hm4 hpc4 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b23Offset) ((pc_false hpc4).trans rfl) ?_
  refine blk r hp b23_in_code (List.cons_ne_nil _ _) (exec_after run_b22 run_b23) hwf hm4
    fun st5 hm5 hpc5 ↦ ?_
  have hK5 := CK.of_blockR hpre hK hm5 hwf (by decide +kernel) (by decide +kernel) rfl rfl
    (by decide +kernel)
  have hpp0 : BytesAt m.dmem (r.m0.regs.X1.toBitVec + BitVec.ofNat 64 0) r.pp := by
    simpa [Run.pp, WotsLeafPre.pp] using r.input_bytes hpre hF hin
  have hpp : BytesAt st5.data.dmem (r.off 1976) r.pp :=
    copy16_gen hm5 (k := 0) (b := r.base) rfl (o := 1976) (by decide) (k' := 1) (o' := 0)
      (by decide +kernel) (by decide +kernel) (length_pp r) hpp0
  have hA16 := frame_write_lit hm5 (o := 2112) (n := 8) (c := 16) (by decide) (by decide +kernel)
  have hA0t : BytesAt m.dmem (r.off 1776) (List.replicate 200 0) := by
    have := take_of_bytesAt hA0 200
    rwa [List.take_replicate, show min 200 344 = 200 from rfl] at this
  have hA0' := r.bytesAt_keptR hpre hm5 hwf (by decide +kernel)
    (by rw [List.length_replicate]; decide) hA0t (by rw [List.length_replicate]; decide +kernel)
  have had' := r.bytesAt_keptR hpre hm5 hwf (by decide +kernel) (by omega) hadr
    (by rw [had]; decide +kernel)
  have hpay' := r.bytesAt_keptR hpre hm5 hwf (by decide +kernel) (by omega) hpay
    (by rw [hP]; decide +kernel)
  have h0 : Run.RegIs st5.data .X0 (r.off 1992) := regIs_ptrR hm5 rfl
  have h1 : Run.RegIs st5.data .X1 (r.off 2504) := regIs_ptrR hm5 rfl
  have h2 := x2_eq hm5 (c := 16) rfl (by decide)
  have h24 : Run.RegIs st5.data .X24 (r.off 2504) := regIs_ptrR hm5 rfl
  have h25 : Run.RegIs st5.data .X25 (BitVec.ofNat 64 16) := regIs_lit hm5 rfl
  have h26 : Run.RegIs st5.data .X26 (BitVec.ofNat 64 16) := regIs_lit hm5 rfl
  have hR5 : r.SRegs st5.data (pos + 1) i := by
    refine ⟨regIs_lit hm5 rfl, ?_, regIs_ptrR hm5 rfl, regIs_ptrR hm5 rfl, ?_,
      regIs_reg hm5 rfl hR.2.2.2.2.2⟩
    · unfold Run.RegIs
      rw [hm5.regs .X20 _ rfl]
      show r.m0.regs.X1.toBitVec + BitVec.ofInt 64 0 = _
      simp
    · unfold Run.RegIs
      rw [hm5.regs .X22 _ rfl]
      have h22 : (r.envR m [(r.m0.regs.X1.toBitVec, 16)]).regs .X22 = BitVec.ofNat 64 pos :=
        hR.2.2.2.2.1
      sym_simp
      rw [h22, BitVec.ofNat_add]
  refine callAt hpc5 hc.1 ?_
  obtain ⟨hpre6, hpost6⟩ := memcpyFrame hpre hK5.1 h0 h1 h2 (by decide) (by decide) (by decide)
    (cSlots_off r x (by decide)) had had'
  refine ⟨hpre6, fun m6 hQ ↦ ?_⟩
  obtain ⟨hK6, hS6, hkc, had6⟩ := hpost6 m6 hQ
  have hpp6 := hkc 1976 _ (by rw [length_pp]; decide) (Or.inl (by rw [length_pp])) hpp
  have hA16' := hkc 2112 _ (by simp) (Or.inr (by decide)) hA16
  have hA0'' := hkc 1776 _ (by rw [List.length_replicate]; decide)
    (Or.inl (by rw [List.length_replicate]; decide)) hA0'
  have hpay6 := hkc 1400 P (by omega) (Or.inl (by omega)) hpay'
  exact seg_b24 hp hc hpre hpos (by simp [length_pp, had]) hP (CK.of_call hK5 hK6 hkc (by decide))
    (SRegs.of_saved hS6 hR5) (RegIs.of_saved hS6 rfl h24) (RegIs.of_saved hS6 rfl h25)
    (RegIs.of_saved hS6 rfl h26) hA16' hA0'' (BytesAt.cat hpp6 had6 (by rw [length_pp])) hpay6
    cont

/-- **`b15`**: the payload (the chain's value, the chain's index as a `u128`) at `1400`, the
step's address at `2504`, `memset` of hasher A; then `b16`. -/
theorem seg_b15 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {pos i : Nat} (hpos : pos ≤ 2) {v : List UInt8} (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m) (hR : r.SRegs m pos i)
    (hval : BytesAt m.dmem (r.off 1384) v)
    (cont : StepCont r x E pos i (r.pp ++ r.addr 1 pos ++ (v ++ u128Bytes i)) R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b15Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK.1.1 (knownK hR (k := []) trivial)
  refine blk r hp b15_in_code (List.cons_ne_nil _ _) run_b15 hwf hm fun st hm1 hpc ↦ ?_
  have hK1 := CK.of_block hpre hK hm1 hwf (by decide +kernel) (by decide +kernel)
  have hadr := addr_bytes hm1 hK hpos hR.2.2.2.2.1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hpay := payload_bytes hm1 hR.2.2.2.2.2 hv hval (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hlp : (v ++ u128Bytes i).length = 32 := by simp [hv, length_u128Bytes]
  -- `memset` of A.
  have h0 : Run.RegIs st.data .X0 (r.off 1776) := regIs_ptr hm1 rfl
  refine callAt hpc hc.2.1 ?_
  obtain ⟨hpre2, hpost2⟩ := memsetFrame hpre hK1.1 h0 (x1_zero hm1 rfl)
    (x2_eq hm1 (c := 344) rfl (by decide)) (by decide) (cSlots_off r x (by decide))
  refine ⟨hpre2, fun m2 hQ ↦ ?_⟩
  obtain ⟨hK2, hS2, hkc, hz⟩ := hpost2 m2 hQ
  have hadr2 := hkc 2504 _ (by rw [length_addr]; decide) (Or.inr (by decide)) hadr
  have hpay2 := hkc 1400 _ (by rw [hlp]; decide) (Or.inl (by rw [hlp]; decide)) hpay
  exact seg_b16 hp hc hpre hpos (length_addr r 1 pos) hlp (CK.of_call hK1 hK2 hkc (by decide))
    (SRegs.of_saved hS2 (SRegs.of_block hm1 rfl rfl rfl rfl rfl rfl hR)) hz hadr2 hpay2 cont

end

end NativeRustcArm.WotsLeafProof.Chain
