module

public import NativeRustcArm.WotsLeaf.Chain.StepTail

/-!
# A chain's step, its middle: the clone, the payload, the state's copy

From hasher A holding `P | A` (32 bytes, its state zero) and the payload at `1400`: `b24`, `b20`,
`b27` clone A into hasher B (`seg_b24`), `b28`, `b30 .. b32` copy the payload into B's buffer
(`seg_b28`), `b33`, `b29`, `b36` copy B's zero state back into A (`seg_b33`); then `b37`.
-/

namespace NativeRustcArm.WotsLeafProof.Chain

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf

public section

variable [NativeRustcArm.Host] {r : Run}

/-- **`b33`, `b29`, `b36`**: B's `buf_len` 64, B's zero state copied into A; then `b37`. -/
theorem seg_b33 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {pos i : Nat} (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64)
    {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m) (hR : r.SRegs m (pos + 1) i)
    (h24 : Run.RegIs m .X24 (r.off 1400)) (h25 : Run.RegIs m .X25 (BitVec.ofNat 64 32))
    (h27 : Run.RegIs m .X27 (BitVec.ofNat 64 32))
    (hB32 : BytesAt m.dmem (r.off 1768) ((List.range 8).map (byteOf (BitVec.ofNat 64 32))))
    (hB0 : BytesAt m.dmem (r.off 1432) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 1632) T) (cont : StepCont r x E pos i T R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b33Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_withLit (match_frameS hpre hK.1.1
    (knownK hR (k := [(.X24, .ptr 0 1400), (.X25, .lit 32), (.X27, .lit 32)])
      ⟨known_ptr h24, known_lit h25, known_lit h27, trivial⟩)) rfl hB32
  refine blk r hp b33_in_code (List.cons_ne_nil _ _) run_b33 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b29Offset) ((pc_true hpc).trans (Run.label_of_block r hp b29_in_code rfl)) ?_
  refine blk r hp b29_in_code (List.cons_ne_nil _ _) (exec_after run_b33 run_b29) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b36Offset) ((pc_true hpc2).trans (Run.label_of_block r hp b36_in_code rfl)) ?_
  refine blk r hp b36_in_code (List.cons_ne_nil _ _) (exec_after run_b29 run_b36) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hK3 := CK.of_block hpre hK hm3 hwf (by decide +kernel) (by decide +kernel)
  have hB0' := r.bytesAt_kept hpre hm3 hwf (by rw [List.length_replicate]; decide) hB0
    (by decide +kernel)
  have hB' := r.bytesAt_kept hpre hm3 hwf (by omega) hB (by rw [hT]; decide +kernel)
  have h0 : Run.RegIs st3.data .X0 (r.off 1776) := regIs_ptr hm3 rfl
  have h1 : Run.RegIs st3.data .X1 (r.off 1432) := regIs_ptr hm3 rfl
  have h2 := x2_eq hm3 (c := 200) rfl (by decide)
  have h26 : Run.RegIs st3.data .X26 (BitVec.ofNat 64 64) := regIs_lit hm3 rfl
  have hR3 := SRegs.of_block hm3 rfl rfl rfl rfl rfl rfl hR
  refine callAt hpc3 hc.1 ?_
  obtain ⟨hpre4, hpost4⟩ := memcpyFrame hpre hK3.1 h0 h1 h2 (by decide) (by decide) (by decide)
    (cSlots_off r x (by decide)) (List.length_replicate) hB0'
  refine ⟨hpre4, fun m4 hQ ↦ ?_⟩
  obtain ⟨hK4, hS4, hkc, hA4⟩ := hpost4 m4 hQ
  have hB4 := hkc 1632 T (by omega) (Or.inl (by omega)) hB'
  exact seg_b37 hp hc hpre hpos hT (CK.of_call hK3 hK4 hkc (by decide)) (SRegs.of_saved hS4 hR3)
    (RegIs.of_saved hS4 rfl h26) hA4 hB4 cont

/-- **`b28`, `b30 .. b32`**: the payload copied into B's buffer after its 32 bytes; then
`b33`. -/
theorem seg_b28 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {pos i : Nat} (hpos : pos ≤ 2) {SA P : List UInt8} (hSA : SA.length = 32)
    (hP : P.length = 32) {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m)
    (hR : r.SRegs m (pos + 1) i)
    (hB32 : BytesAt m.dmem (r.off 1768) ((List.range 8).map (byteOf (BitVec.ofNat 64 32))))
    (hB0 : BytesAt m.dmem (r.off 1432) (List.replicate 200 0))
    (hBsa : BytesAt m.dmem (r.off 1632) SA) (hpay : BytesAt m.dmem (r.off 1400) P)
    (cont : StepCont r x E pos i (SA ++ P) R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b28Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_withLit (match_frameS hpre hK.1.1 (knownK hR (k := []) trivial)) rfl hB32
  refine blk r hp b28_in_code (List.cons_ne_nil _ _) run_b28 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b30Offset) (hpc.trans (Run.label_of_block r hp b30_in_code rfl)) ?_
  refine blk r hp b30_in_code (List.cons_ne_nil _ _) (exec_after run_b28 run_b30) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b31Offset) ((pc_false hpc2).trans rfl) ?_
  refine blk r hp b31_in_code (List.cons_ne_nil _ _) (exec_after run_b30 run_b31) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b32Offset) ((pc_false hpc3).trans rfl) ?_
  refine blk r hp b32_in_code (List.cons_ne_nil _ _) (exec_after run_b31 run_b32) hwf hm3
    fun st4 hm4 hpc4 ↦ ?_
  have hK4 := CK.of_block hpre hK hm4 hwf (by decide +kernel) (by decide +kernel)
  have hB32' := frame_write_lit hm4 (o := 1768) (n := 8) (c := 32) (by decide) (by decide +kernel)
  have hB0' := r.bytesAt_kept hpre hm4 hwf (by rw [List.length_replicate]; decide) hB0
    (by decide +kernel)
  have hBsa' := r.bytesAt_kept hpre hm4 hwf (by omega) hBsa (by rw [hSA]; decide +kernel)
  have hpay' := r.bytesAt_kept hpre hm4 hwf (by omega) hpay (by rw [hP]; decide +kernel)
  have h0 : Run.RegIs st4.data .X0 (r.off 1664) := regIs_ptr hm4 rfl
  have h1 : Run.RegIs st4.data .X1 (r.off 1400) := regIs_ptr hm4 rfl
  have h2 := x2_eq hm4 (c := 32) rfl (by decide)
  have h24 : Run.RegIs st4.data .X24 (r.off 1400) := regIs_ptr hm4 rfl
  have h25 : Run.RegIs st4.data .X25 (BitVec.ofNat 64 32) := regIs_lit hm4 rfl
  have h27 : Run.RegIs st4.data .X27 (BitVec.ofNat 64 32) := regIs_lit hm4 rfl
  have hR4 := SRegs.of_block hm4 rfl rfl rfl rfl rfl rfl hR
  refine callAt hpc4 hc.1 ?_
  obtain ⟨hpre5, hpost5⟩ := memcpyFrame hpre hK4.1 h0 h1 h2 (by decide) (by decide) (by decide)
    (cSlots_off r x (by decide)) hP hpay'
  refine ⟨hpre5, fun m5 hQ ↦ ?_⟩
  obtain ⟨hK5, hS5, hkc, hP5⟩ := hpost5 m5 hQ
  have hB32'' := hkc 1768 _ (by simp) (Or.inr (by decide)) hB32'
  have hB0'' := hkc 1432 _ (by rw [List.length_replicate]; decide)
    (Or.inl (by rw [List.length_replicate]; decide)) hB0'
  have hBsa'' := hkc 1632 SA (by omega) (Or.inl (by omega)) hBsa'
  exact seg_b33 hp hc hpre hpos (by simp [hSA, hP]) (CK.of_call hK4 hK5 hkc (by decide))
    (SRegs.of_saved hS5 hR4) (RegIs.of_saved hS5 rfl h24) (RegIs.of_saved hS5 rfl h25)
    (RegIs.of_saved hS5 rfl h27) hB32'' hB0'' (BytesAt.cat hBsa'' hP5 (by rw [hSA])) cont

/-- **`b24`, `b20`, `b27`**: A's `buf_len` 32, A cloned into B; then `b28`. -/
theorem seg_b24 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {pos i : Nat} (hpos : pos ≤ 2) {SA P : List UInt8} (hSA : SA.length = 32)
    (hP : P.length = 32) {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m)
    (hR : r.SRegs m (pos + 1) i) (h24 : Run.RegIs m .X24 (r.off 2504))
    (h25 : Run.RegIs m .X25 (BitVec.ofNat 64 16)) (h26 : Run.RegIs m .X26 (BitVec.ofNat 64 16))
    (hA16 : BytesAt m.dmem (r.off 2112) ((List.range 8).map (byteOf (BitVec.ofNat 64 16))))
    (hA0 : BytesAt m.dmem (r.off 1776) (List.replicate 200 0))
    (hAsa : BytesAt m.dmem (r.off 1976) SA) (hpay : BytesAt m.dmem (r.off 1400) P)
    (cont : StepCont r x E pos i (SA ++ P) R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b24Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_withLit (match_frameS hpre hK.1.1
    (knownK hR (k := [(.X24, .ptr 0 2504), (.X25, .lit 16), (.X26, .lit 16)])
      ⟨known_ptr h24, known_lit h25, known_lit h26, trivial⟩)) rfl hA16
  refine blk r hp b24_in_code (List.cons_ne_nil _ _) run_b24 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b20Offset) ((pc_true hpc).trans (Run.label_of_block r hp b20_in_code rfl)) ?_
  refine blk r hp b20_in_code (List.cons_ne_nil _ _) (exec_after run_b24 run_b20) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Xmss.WotsLeaf.b27Offset) ((pc_true hpc2).trans (Run.label_of_block r hp b27_in_code rfl)) ?_
  refine blk r hp b27_in_code (List.cons_ne_nil _ _) (exec_after run_b20 run_b27) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hK3 := CK.of_block hpre hK hm3 hwf (by decide +kernel) (by decide +kernel)
  have hA32 := frame_write_lit hm3 (o := 2112) (n := 8) (c := 32) (by decide) (by decide +kernel)
  have hA0' := r.bytesAt_kept hpre hm3 hwf (by rw [List.length_replicate]; decide) hA0
    (by decide +kernel)
  have hAsa' := r.bytesAt_kept hpre hm3 hwf (by omega) hAsa (by rw [hSA]; decide +kernel)
  have hpay' := r.bytesAt_kept hpre hm3 hwf (by omega) hpay (by rw [hP]; decide +kernel)
  have h0 : Run.RegIs st3.data .X0 (r.off 1432) := regIs_ptr hm3 rfl
  have h1 : Run.RegIs st3.data .X1 (r.off 1776) := regIs_ptr hm3 rfl
  have h2 := x2_eq hm3 (c := 344) rfl (by decide)
  have hR3 := SRegs.of_block hm3 rfl rfl rfl rfl rfl rfl hR
  have hmap := bytesAt_bytesOf (r.frame_mapped hpre hK3.1.1 (a := 1776) (n := 344) (by decide)).1
  refine callAt hpc3 hc.1 ?_
  obtain ⟨hpre4, hpost4⟩ := memcpyFrame hpre hK3.1 h0 h1 h2 (by decide) (by decide) (by decide)
    (cSlots_off r x (by decide)) (length_bytesOf _ _ _) hmap
  refine ⟨hpre4, fun m4 hQ ↦ ?_⟩
  obtain ⟨hK4, hS4, hkc, hB4⟩ := hpost4 m4 hQ
  have hpay4 := hkc 1400 P (by omega) (Or.inl (by omega)) hpay'
  exact seg_b28 hp hc hpre hpos hSA hP (CK.of_call hK3 hK4 hkc (by decide))
    (SRegs.of_saved hS4 hR3) (copy_slice (c := 336) hB4 (by simp) hA32)
    (copy_slice (c := 0) hB4 (by rw [List.length_replicate]; decide) hA0')
    (copy_slice (c := 200) hB4 (by omega) hAsa') hpay4 cont

end

end NativeRustcArm.WotsLeafProof.Chain
