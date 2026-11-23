module

public import NativeRustcArm.SphincsVerify.Chains.StepTail

/-!
# A chain's step, its middle: the clone, the value, the state's copy, the block

From hasher A holding `PK.seed | ADRS` (48 bytes, its state zero) and the chain's value at
`15984`: `b125 .. b128` clone A into hasher B (`seg_b125`), `b129 .. b133` copy the value into B's
buffer (`seg_b129`), `b134 .. b137` copy B's zero state back into A (`seg_b134`), `b138`, `b139`
copy B's 64 buffered bytes to `24720` after zeros (`seg_b138`); then `b140`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

public section

variable [NativeRustcArm.Host] {r : Run}

/-- **`b138`, `b139`**: `24720 .. 24856` zeroed, B's 64 buffered bytes copied there; then
`b140`. -/
theorem seg_b138 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E m) (hR : Regs m (pos + 1) i)
    (h24 : Run.RegIs m .X24 (BitVec.ofNat 64 64))
    (hA0 : BytesAt m.dmem (r.off 16400) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 26968) T) (cont : StepCont r l x E pos i T R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b138Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := [(.X24, .lit 64)]) ⟨known_lit h24, trivial⟩
  refine blk r hp b138_in_code (List.cons_ne_nil _ _) run_b138 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b139Offset) ((pc_false hpc).trans rfl) ?_
  refine blk r hp b139_in_code (List.cons_ne_nil _ _) (exec_after run_b138 run_b139) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hK2 := Keep.of_block hpre hx hE hK hm2 hwf (by decide +kernel)
  have hz := frame_write_zero hm2 (o := 24784) (n := 72) (by decide) (by decide +kernel)
  have hA0' := r.bytesAt_kept hpre hm2 hwf (by len_tac) hA0 (by decide +kernel)
  have hB' := r.bytesAt_kept hpre hm2 hwf (by omega) hB (by rw [hT]; decide +kernel)
  have h0 : Run.RegIs st2.data .X0 (r.off 24720) := regIs_ptr hm2 rfl
  have h1 : Run.RegIs st2.data .X1 (r.off 26968) := regIs_ptr hm2 rfl
  have h2 := x2_eq hm2 (c := 64) rfl (by decide)
  have h24' : Run.RegIs st2.data .X24 (BitVec.ofNat 64 64) := regIs_lit hm2 rfl
  have hR2 := Regs.of_block hm2 rfl rfl rfl hR
  refine call_then hpc2 hc.1 (r.memcpy_pre hpre hK2.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st3 hpc3 hpost ↦ ?_
  obtain ⟨hc3, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK3 := Keep.of_call hpre hx hE hK2 hS (a := 24720) (n := 64) (by unfold Scratch; omega)
    (by decide) hout
  have hT3 : BytesAt st3.data.dmem (r.off 24720) T :=
    copy_slice (c := 0) hc3 (by omega) hB'
  have hz3 := r.bytesAt_of_call hpre hK2.1 (a := 24720) (n := 64) (by decide) (by decide) hout
    (o := 24784) (by len_tac) (by len_tac) hz
  have hA3 := r.bytesAt_of_call hpre hK2.1 (a := 24720) (n := 64) (by decide) (by decide) hout
    (o := 16400) (by len_tac) (by len_tac) hA0'
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b140Offset) (by rw [hpc3]; rfl)
    (seg_b140 hp hc hpre hx hE hpos hT hK3 (Regs.of_saved hS hR2) (RegIs.of_saved hS rfl h24') hA3
      (BytesAt.cat hT3 hz3 (by omega)) cont)

/-- **`b134`, `b130`, `b137`**: B's `buf_len` 64, B's zero state copied into A; then `b138`. -/
theorem seg_b134 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E m) (hR : Regs m (pos + 1) i)
    (h22 : Run.RegIs m .X22 (r.off 15984)) (h23 : Run.RegIs m .X23 (BitVec.ofNat 64 16))
    (h27 : Run.RegIs m .X27 (BitVec.ofNat 64 16))
    (hB48 : BytesAt m.dmem (r.off 27104) ((List.range 8).map (byteOf (BitVec.ofNat 64 48))))
    (hB0 : BytesAt m.dmem (r.off 26768) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 26968) T) (cont : StepCont r l x E pos i T R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b134Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_withLit (match_frameS hpre hK
    (k := [(.X22, .ptr 0 15984), (.X23, .lit 16), (.X27, .lit 16)])
    ⟨known_ptr h22, known_lit h23, known_lit h27, trivial⟩) rfl hB48
  refine blk r hp b134_in_code (List.cons_ne_nil _ _) run_b134 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b130Offset) ((pc_true hpc).trans (labelAt r hp b130_in_code rfl)) ?_
  refine blk r hp b130_in_code (List.cons_ne_nil _ _) (exec_after run_b134 run_b130) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b137Offset) ((pc_true hpc2).trans (labelAt r hp b137_in_code rfl)) ?_
  refine blk r hp b137_in_code (List.cons_ne_nil _ _) (exec_after run_b130 run_b137) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hK3 := Keep.of_block hpre hx hE hK hm3 hwf (by decide +kernel)
  have hB0' := r.bytesAt_kept hpre hm3 hwf (by len_tac) hB0 (by decide +kernel)
  have hB' := r.bytesAt_kept hpre hm3 hwf (by omega) hB (by rw [hT]; decide +kernel)
  have h0 : Run.RegIs st3.data .X0 (r.off 16400) := regIs_ptr hm3 rfl
  have h1 : Run.RegIs st3.data .X1 (r.off 26768) := regIs_ptr hm3 rfl
  have h2 := x2_eq hm3 (c := 200) rfl (by decide)
  have h24 : Run.RegIs st3.data .X24 (BitVec.ofNat 64 64) := regIs_lit hm3 rfl
  have hR3 := Regs.of_block hm3 rfl rfl rfl hR
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hK3.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st4 hpc4 hpost ↦ ?_
  obtain ⟨hc4, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK4 := Keep.of_call hpre hx hE hK3 hS (a := 16400) (n := 200) (by unfold Scratch; omega)
    (by decide) hout
  have hA4 : BytesAt st4.data.dmem (r.off 16400) (List.replicate 200 0) :=
    copy_slice (c := 0) hc4 (by len_tac) hB0'
  have hB4 := r.bytesAt_of_call hpre hK3.1 (a := 16400) (n := 200) (by decide) (by decide) hout
    (o := 26968) (by omega) (by omega) hB'
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b138Offset) (by rw [hpc4]; rfl)
    (seg_b138 hp hc hpre hx hE hpos hT hK4 (Regs.of_saved hS hR3) (RegIs.of_saved hS rfl h24) hA4
      hB4 cont)

/-- **`b129 .. b133`**: the chain's value copied into B's buffer after its 48 bytes; then
`b134`. -/
theorem seg_b129 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) {SA v : List UInt8} (hSA : SA.length = 48) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m) (hR : Regs m (pos + 1) i)
    (hB48 : BytesAt m.dmem (r.off 27104) ((List.range 8).map (byteOf (BitVec.ofNat 64 48))))
    (hB0 : BytesAt m.dmem (r.off 26768) (List.replicate 200 0))
    (hBsa : BytesAt m.dmem (r.off 26968) SA) (hval : BytesAt m.dmem (r.off 15984) v)
    (cont : StepCont r l x E pos i (SA ++ v) R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b129Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_withLit (match_frameS hpre hK (k := []) trivial) rfl hB48
  refine blk r hp b129_in_code (List.cons_ne_nil _ _) run_b129 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b131Offset) (hpc.trans (labelAt r hp b131_in_code rfl)) ?_
  refine blk r hp b131_in_code (List.cons_ne_nil _ _) (exec_after run_b129 run_b131) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b132Offset) ((pc_false hpc2).trans rfl) ?_
  refine blk r hp b132_in_code (List.cons_ne_nil _ _) (exec_after run_b131 run_b132) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b133Offset) ((pc_false hpc3).trans rfl) ?_
  refine blk r hp b133_in_code (List.cons_ne_nil _ _) (exec_after run_b132 run_b133) hwf hm3
    fun st4 hm4 hpc4 ↦ ?_
  have hK4 := Keep.of_block hpre hx hE hK hm4 hwf (by decide +kernel)
  have hB48' := frame_write_lit hm4 (o := 27104) (n := 8) (c := 48) (by decide) (by decide +kernel)
  have hB0' := r.bytesAt_kept hpre hm4 hwf (by len_tac) hB0 (by decide +kernel)
  have hBsa' := r.bytesAt_kept hpre hm4 hwf (by omega) hBsa (by rw [hSA]; decide +kernel)
  have hval' := r.bytesAt_kept hpre hm4 hwf (by omega) hval (by rw [hv]; decide +kernel)
  have h0 : Run.RegIs st4.data .X0 (r.off 27016) := regIs_ptr hm4 rfl
  have h1 : Run.RegIs st4.data .X1 (r.off 15984) := regIs_ptr hm4 rfl
  have h2 := x2_eq hm4 (c := 16) rfl (by decide)
  have h22 : Run.RegIs st4.data .X22 (r.off 15984) := regIs_ptr hm4 rfl
  have h23 : Run.RegIs st4.data .X23 (BitVec.ofNat 64 16) := regIs_lit hm4 rfl
  have h27 : Run.RegIs st4.data .X27 (BitVec.ofNat 64 16) := regIs_lit hm4 rfl
  have hR4 := Regs.of_block hm4 rfl rfl rfl hR
  refine call_then hpc4 hc.1 (r.memcpy_pre hpre hK4.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st5 hpc5 hpost ↦ ?_
  obtain ⟨hc5, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK5 := Keep.of_call hpre hx hE hK4 hS (a := 27016) (n := 16) (by unfold Scratch; omega)
    (by decide) hout
  have hv5 : BytesAt st5.data.dmem (r.off 27016) v := copy_slice (c := 0) hc5 (by omega) hval'
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29376)
      (hd : o + bs.length ≤ 27016 ∨ 27032 ≤ o) (h : BytesAt st4.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK4.1 (a := 27016) (n := 16) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b134Offset) (by rw [hpc5]; rfl)
    (seg_b134 hp hc hpre hx hE hpos (by simp; omega) hK5 (Regs.of_saved hS hR4)
      (RegIs.of_saved hS rfl h22) (RegIs.of_saved hS rfl h23) (RegIs.of_saved hS rfl h27)
      (kept (by len_tac) (by len_tac) hB48') (kept (by len_tac) (by len_tac) hB0')
      (BytesAt.cat (kept (by omega) (by omega) hBsa') hv5 (by omega)) cont)

/-- **`b125`, `b121`, `b128`**: A's `buf_len` 48, A cloned into B; then `b129`. -/
theorem seg_b125 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) {SA v : List UInt8} (hSA : SA.length = 48) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m) (hR : Regs m (pos + 1) i)
    (h22 : Run.RegIs m .X22 (r.off 21648)) (h23 : Run.RegIs m .X23 (BitVec.ofNat 64 32))
    (h24 : Run.RegIs m .X24 (BitVec.ofNat 64 32))
    (hA16 : BytesAt m.dmem (r.off 16736) ((List.range 8).map (byteOf (BitVec.ofNat 64 16))))
    (hA0 : BytesAt m.dmem (r.off 16400) (List.replicate 200 0))
    (hAsa : BytesAt m.dmem (r.off 16600) SA) (hval : BytesAt m.dmem (r.off 15984) v)
    (cont : StepCont r l x E pos i (SA ++ v) R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b125Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_withLit (match_frameS hpre hK
    (k := [(.X22, .ptr 0 21648), (.X23, .lit 32), (.X24, .lit 32)])
    ⟨known_ptr h22, known_lit h23, known_lit h24, trivial⟩) rfl hA16
  refine blk r hp b125_in_code (List.cons_ne_nil _ _) run_b125 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b121Offset) ((pc_true hpc).trans (labelAt r hp b121_in_code rfl)) ?_
  refine blk r hp b121_in_code (List.cons_ne_nil _ _) (exec_after run_b125 run_b121) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b128Offset) ((pc_true hpc2).trans (labelAt r hp b128_in_code rfl)) ?_
  refine blk r hp b128_in_code (List.cons_ne_nil _ _) (exec_after run_b121 run_b128) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hK3 := Keep.of_block hpre hx hE hK hm3 hwf (by decide +kernel)
  have hA48 := frame_write_lit hm3 (o := 16736) (n := 8) (c := 48) (by decide) (by decide +kernel)
  have hA0' := r.bytesAt_kept hpre hm3 hwf (by len_tac) hA0 (by decide +kernel)
  have hAsa' := r.bytesAt_kept hpre hm3 hwf (by omega) hAsa (by rw [hSA]; decide +kernel)
  have hval' := r.bytesAt_kept hpre hm3 hwf (by omega) hval (by rw [hv]; decide +kernel)
  have h0 : Run.RegIs st3.data .X0 (r.off 26768) := regIs_ptr hm3 rfl
  have h1 : Run.RegIs st3.data .X1 (r.off 16400) := regIs_ptr hm3 rfl
  have h2 := x2_eq hm3 (c := 344) rfl (by decide)
  have hR3 := Regs.of_block hm3 rfl rfl rfl hR
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hK3.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st4 hpc4 hpost ↦ ?_
  obtain ⟨hc4, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK4 := Keep.of_call hpre hx hE hK3 hS (a := 26768) (n := 344) (by unfold Scratch; omega)
    (by decide) hout
  have hval4 := r.bytesAt_of_call hpre hK3.1 (a := 26768) (n := 344) (by decide) (by decide) hout
    (o := 15984) (by omega) (by omega) hval'
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b129Offset) (by rw [hpc4]; rfl)
    (seg_b129 hp hc hpre hx hE hpos hSA hv hK4 (Regs.of_saved hS hR3)
      (copy_slice (c := 336) hc4 (by len_tac) hA48) (copy_slice (c := 0) hc4 (by len_tac) hA0')
      (copy_slice (c := 200) hc4 (by omega) hAsa') hval4 cont)

end

end NativeRustcArm.SphincsVerifyProof.Chains
