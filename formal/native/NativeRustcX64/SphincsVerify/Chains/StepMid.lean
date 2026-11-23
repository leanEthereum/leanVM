module

public import NativeRustcX64.SphincsVerify.Chains.StepTail

/-!
# A chain's step on x86-64, its middle: the clone, the value, the state's copy, the block

From hasher A holding `PK.seed | ADRS` (48 bytes, its state zero) and the chain's value at
`1632`: `b129 .. b133` clone A into hasher B (`seg_b129`), `b134 .. b139` copy the value into B's
buffer (`seg_b134`), `b140 .. b144` copy B's zero state back into A (`seg_b140`), `b145`, `b146`
zero the block at `2048` (`seg_b145`), `b147` copies B's 64 buffered bytes there (`seg_b147`);
then `b148`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

variable [Host] {r : Run}

public section

/-- **`b147`**: B's 64 buffered bytes copied to the zeroed block; then `b148`. -/
theorem seg_b147 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E i m) (h12 : Run.RegIs m .r12 (r.off 4096))
    (hbx : Run.RegIs m .rbx (BitVec.ofNat 64 64)) (h64 : r.WordAt m 64 (pos + 1).toUInt64)
    (hA0 : BytesAt m.dmem (r.off 4096) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 776) T) (hK0 : BytesAt m.dmem (r.off 2048) (List.replicate 136 0))
    (hcopy : Run.RegIs m .r15 (Labels.label "memcpy").toBitVec)
    (hset : Run.RegIs m .r14 (Labels.label "memset").toBitVec)
    (cont : StepCont r l x E i pos T R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b147Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b148Offset).toBitVec
  have hm := match_frameS hpre hK.1 hK.2.1
    (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b148Offset).toBitVec)
    (k := [(.rbx, .lit 64), (.r15, .label "memcpy")]) ⟨known_lit hbx, hcopy, trivial⟩
  refine blk r hp b147_in_code (List.cons_ne_nil _ _) run_b147 hwf (fun _ _ ↦ rfl) hm
    fun st hm' hpc ↦ ?_
  have hK1 := KeepC.of_block hpre hx hE hK hm' hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm' hwf ho h hn
  have hA0' := kept (by len_tac) hA0 (by decide +kernel)
  have hB' := kept (by omega) hB (by rw [hT]; decide +kernel)
  have hK0' := kept (by len_tac) hK0 (by decide +kernel)
  have h64' := kept (by simp [NativeRustc.length_wordBytes]) h64
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st.data .rdi (r.off 2048) := regIs_ptr hm' rfl
  have h1 : Run.RegIs st.data .rsi (r.off 776) := regIs_ptr hm' rfl
  have h2 := toNat_of_lit hm' (y := .rdx) (c := 64) rfl (by decide)
  have hbx' : Run.RegIs st.data .rbx (BitVec.ofNat 64 64) := regIs_lit hm' rfl
  have h12' := regIs_reg hm' rfl h12
  refine call_then hpc hc.1 (r.memcpy_pre hpre hK1.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hc2, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK2 := Keep.of_call hpre hx hE hK1 hS hrsp2 (a := 2048) (n := 64)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (hd : o + bs.length ≤ 2048 ∨ 2112 ≤ o) (h : BytesAt st.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK1.1 (a := 2048) (n := 64) (by decide) (by decide) hout ho hd h
  have hT2 : BytesAt st2.data.dmem (r.off 2048) T := copy_slice (c := 0) hc2 (by omega) hB'
  have hz : BytesAt st2.data.dmem (r.off 2112) (List.replicate 72 0) := by
    have := BytesAt.slice hK0' 64 72
    rw [Run.off_add, List.drop_replicate, List.take_replicate] at this
    exact kept2 (by len_tac) (by len_tac) this
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b148Offset) (by rw [hpc2]; rfl)
    (seg_b148 hp hc hpre hx hE hpos hT hK2 (RegIs.of_saved hS rfl h12')
      (RegIs.of_saved hS rfl hbx')
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h64')
      (kept2 (by len_tac) (by len_tac) hA0') (BytesAt.cat hT2 hz (by omega))
      (RegIs.of_saved hS rfl (regIs_label (y := .r15) hm' rfl))
      (RegIs.of_saved hS rfl (regIs_reg hm' rfl hset)) cont)

/-- **`b145`, `b146`**: the block at `2048` zeroed; then `b147`. -/
theorem seg_b145 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E i m) (h12 : Run.RegIs m .r12 (r.off 4096))
    (h14 : Run.RegIs m .r14 (BitVec.ofNat 64 64)) (h64 : r.WordAt m 64 (pos + 1).toUInt64)
    (hA0 : BytesAt m.dmem (r.off 4096) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 776) T)
    (hcopy : Run.RegIs m .r15 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r l x E i pos T R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b145Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b147Offset).toBitVec
  have hm := match_frameS hpre hK.1 hK.2.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b147Offset).toBitVec) (k := [(.r14, .lit 64)])
    ⟨known_lit h14, trivial⟩
  refine blk r hp b145_in_code (List.cons_ne_nil _ _) run_b145 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b146Offset) ((pc_false hpc).trans rfl) ?_
  refine blk r hp b146_in_code (List.cons_ne_nil _ _) (exec_after run_b145 run_b146) hwf
    (fun _ _ ↦ rfl) hm1 fun st2 hm2 hpc2 ↦ ?_
  have hK1 := KeepC.of_block hpre hx hE hK hm2 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm2 hwf ho h hn
  have hA0' := kept (by len_tac) hA0 (by decide +kernel)
  have hB' := kept (by omega) hB (by rw [hT]; decide +kernel)
  have h64' := kept (by simp [NativeRustc.length_wordBytes]) h64
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st2.data .rdi (r.off 2048) := regIs_ptr hm2 rfl
  have h1 := toNat_of_lit hm2 (y := .rsi) (c := 0) rfl (by decide)
  have h2 := toNat_of_lit hm2 (y := .rdx) (c := 136) rfl (by decide)
  have hbx : Run.RegIs st2.data .rbx (BitVec.ofNat 64 64) := regIs_lit hm2 rfl
  have h12' := regIs_reg hm2 rfl h12
  refine call_then hpc2 hc.2.1 (r.memset_pre hpre hK1.1 h0 h2 (by decide))
    fun st3 hpc3 hrsp3 hpost ↦ ?_
  obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
  rw [h1] at hz
  have hK3 := Keep.of_call hpre hx hE hK1 hS hrsp3 (a := 2048) (n := 136)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (hd : o + bs.length ≤ 2048 ∨ 2184 ≤ o) (h : BytesAt st2.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK1.1 (a := 2048) (n := 136) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b147Offset) (by rw [hpc3]; rfl)
    (seg_b147 hp hc hpre hx hE hpos hT hK3 (RegIs.of_saved hS rfl h12') (RegIs.of_saved hS rfl hbx)
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h64')
      (kept2 (by len_tac) (by len_tac) hA0') (kept2 (by omega) (by omega) hB') hz
      (RegIs.of_saved hS rfl (regIs_reg hm2 rfl hcopy))
      (RegIs.of_saved hS rfl (regIs_label (y := .r14) hm2 rfl)) cont)

/-- **`b140`, `b136`, `b144`**: B's `buf_len` 64, B's zero state copied into A; then `b145`. -/
theorem seg_b140 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E i m) (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 16))
    (hbx : Run.RegIs m .rbx (r.off 1632)) (h12 : Run.RegIs m .r12 (BitVec.ofNat 64 16))
    (h64 : r.WordAt m 64 (pos + 1).toUInt64)
    (hB48 : BytesAt m.dmem (r.off 912) ((List.range 8).map (byteOf (BitVec.ofNat 64 48))))
    (hB0 : BytesAt m.dmem (r.off 576) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 776) T)
    (hcopy : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r l x E i pos T R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b140Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b145Offset).toBitVec
  have hm := match_withLit (match_frameS hpre hK.1 hK.2.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b145Offset).toBitVec)
    (k := [(.r15, .lit 16), (.rbx, .ptr 0 1632), (.r12, .lit 16), (.r14, .label "memcpy")])
    ⟨known_lit h15, known_ptr hbx, known_lit h12, hcopy, trivial⟩) rfl hB48
  refine blk r hp b140_in_code (List.cons_ne_nil _ _) run_b140 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b136Offset) ((pc_true hpc).trans (labelAt r hp b136_in_code rfl)) ?_
  refine blk r hp b136_in_code (List.cons_ne_nil _ _) (exec_after run_b140 run_b136) hwf
    (fun _ h ↦ nomatch h) hm1 fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b144Offset) ((pc_true hpc2).trans (labelAt r hp b144_in_code rfl)) ?_
  refine blk r hp b144_in_code (List.cons_ne_nil _ _) (exec_after run_b136 run_b144) hwf
    (fun _ _ ↦ rfl) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hK3 := KeepC.of_block hpre hx hE hK hm3 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm3 hwf ho h hn
  have hB0' := kept (by len_tac) hB0 (by decide +kernel)
  have hB' := kept (by omega) hB (by rw [hT]; decide +kernel)
  have h64' := kept (by simp [NativeRustc.length_wordBytes]) h64
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st3.data .rdi (r.off 4096) := regIs_ptr hm3 rfl
  have h1 : Run.RegIs st3.data .rsi (r.off 576) := regIs_ptr hm3 rfl
  have h2 := toNat_of_lit hm3 (y := .rdx) (c := 200) rfl (by decide)
  have h14 : Run.RegIs st3.data .r14 (BitVec.ofNat 64 64) := regIs_lit hm3 rfl
  have h12' : Run.RegIs st3.data .r12 (r.off 4096) := regIs_ptr hm3 rfl
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hK3.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st4 hpc4 hrsp4 hpost ↦ ?_
  obtain ⟨hc4, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK4 := Keep.of_call hpre hx hE hK3 hS hrsp4 (a := 4096) (n := 200)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (hd : o + bs.length ≤ 4096 ∨ 4296 ≤ o) (h : BytesAt st3.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK3.1 (a := 4096) (n := 200) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b145Offset) (by rw [hpc4]; rfl)
    (seg_b145 hp hc hpre hx hE hpos hT hK4 (RegIs.of_saved hS rfl h12') (RegIs.of_saved hS rfl h14)
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h64')
      (copy_slice (c := 0) hc4 (by len_tac) hB0') (kept2 (by omega) (by omega) hB')
      (RegIs.of_saved hS rfl (regIs_label (y := .r15) hm3 rfl)) cont)

/-- **`b134 .. b139`**: the chain's value copied into B's buffer after its 48 bytes; then
`b140`. -/
theorem seg_b134 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {SA v : List UInt8} (hSA : SA.length = 48) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E i m)
    (h64 : r.WordAt m 64 (pos + 1).toUInt64)
    (hB48 : BytesAt m.dmem (r.off 912) ((List.range 8).map (byteOf (BitVec.ofNat 64 48))))
    (hB0 : BytesAt m.dmem (r.off 576) (List.replicate 200 0))
    (hBsa : BytesAt m.dmem (r.off 776) SA) (hval : BytesAt m.dmem (r.off 1632) v)
    (hcopy : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r l x E i pos (SA ++ v) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b134Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b140Offset).toBitVec
  have hm := match_withLit (match_frameS hpre hK.1 hK.2.1
    (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b140Offset).toBitVec)
    (k := [(.r14, .label "memcpy")]) ⟨hcopy, trivial⟩) rfl hB48
  refine blk r hp b134_in_code (List.cons_ne_nil _ _) run_b134 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b137Offset) (hpc.trans (labelAt r hp b137_in_code rfl)) ?_
  refine blk r hp b137_in_code (List.cons_ne_nil _ _) (exec_after run_b134 run_b137) hwf
    (fun _ h ↦ nomatch h) hm1 fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b138Offset) ((pc_false hpc2).trans rfl) ?_
  refine blk r hp b138_in_code (List.cons_ne_nil _ _) (exec_after run_b137 run_b138) hwf
    (fun _ h ↦ nomatch h) hm2 fun st3 hm3 hpc3 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b139Offset) ((pc_false hpc3).trans rfl) ?_
  refine blk r hp b139_in_code (List.cons_ne_nil _ _) (exec_after run_b138 run_b139) hwf
    (fun _ _ ↦ rfl) hm3 fun st4 hm4 hpc4 ↦ ?_
  have hK4 := KeepC.of_block hpre hx hE hK hm4 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm4 hwf ho h hn
  have hB48' := bytesAt_write_val hm4 (r := 0) (b := r.base) (sz := frameRegion) rfl (o := 912) (n := 8)
    (v := .lit 48) (by decide) (by decide +kernel)
  have hB0' := kept (by len_tac) hB0 (by decide +kernel)
  have hBsa' := kept (by omega) hBsa (by rw [hSA]; decide +kernel)
  have hval' := kept (by omega) hval (by rw [hv]; decide +kernel)
  have h64' := kept (by simp [NativeRustc.length_wordBytes]) h64
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st4.data .rdi (r.off 824) := regIs_ptr hm4 rfl
  have h1 : Run.RegIs st4.data .rsi (r.off 1632) := regIs_ptr hm4 rfl
  have h2 := toNat_of_lit hm4 (y := .rdx) (c := 16) rfl (by decide)
  have h15 : Run.RegIs st4.data .r15 (BitVec.ofNat 64 16) := regIs_lit hm4 rfl
  have hbx : Run.RegIs st4.data .rbx (r.off 1632) := regIs_ptr hm4 rfl
  have h12 : Run.RegIs st4.data .r12 (BitVec.ofNat 64 16) := regIs_lit hm4 rfl
  refine call_then hpc4 hc.1 (r.memcpy_pre hpre hK4.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st5 hpc5 hrsp5 hpost ↦ ?_
  obtain ⟨hc5, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK5 := Keep.of_call hpre hx hE hK4 hS hrsp5 (a := 824) (n := 16)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (hd : o + bs.length ≤ 824 ∨ 840 ≤ o) (h : BytesAt st4.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK4.1 (a := 824) (n := 16) (by decide) (by decide) hout ho hd h
  have hv5 : BytesAt st5.data.dmem (r.off 824) v := copy_slice (c := 0) hc5 (by omega) hval'
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b140Offset) (by rw [hpc5]; rfl)
    (seg_b140 hp hc hpre hx hE hpos (by simp; omega) hK5 (RegIs.of_saved hS rfl h15)
      (RegIs.of_saved hS rfl hbx) (RegIs.of_saved hS rfl h12)
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h64')
      (kept2 (by len_tac) (by len_tac) hB48') (kept2 (by len_tac) (by len_tac) hB0')
      (BytesAt.cat (kept2 (by omega) (by omega) hBsa') hv5 (by omega))
      (RegIs.of_saved hS rfl (regIs_label (y := .r14) hm4 rfl)) cont)

/-- **`b129`, `b125`, `b133`**: A's `buf_len` 48, A cloned into B; then `b134`. -/
theorem seg_b129 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {SA v : List UInt8} (hSA : SA.length = 48) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E i m)
    (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 32)) (hbx : Run.RegIs m .rbx (r.off 8320))
    (h12 : Run.RegIs m .r12 (BitVec.ofNat 64 32)) (h64 : r.WordAt m 64 (pos + 1).toUInt64)
    (hA16 : BytesAt m.dmem (r.off 4432) ((List.range 8).map (byteOf (BitVec.ofNat 64 16))))
    (hA0 : BytesAt m.dmem (r.off 4096) (List.replicate 200 0))
    (hAsa : BytesAt m.dmem (r.off 4296) SA) (hval : BytesAt m.dmem (r.off 1632) v)
    (hcopy : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r l x E i pos (SA ++ v) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b129Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b134Offset).toBitVec
  have hm := match_withLit (match_frameS hpre hK.1 hK.2.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b134Offset).toBitVec)
    (k := [(.r15, .lit 32), (.rbx, .ptr 0 8320), (.r12, .lit 32), (.r14, .label "memcpy")])
    ⟨known_lit h15, known_ptr hbx, known_lit h12, hcopy, trivial⟩) rfl hA16
  refine blk r hp b129_in_code (List.cons_ne_nil _ _) run_b129 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b125Offset) ((pc_true hpc).trans (labelAt r hp b125_in_code rfl)) ?_
  refine blk r hp b125_in_code (List.cons_ne_nil _ _) (exec_after run_b129 run_b125) hwf
    (fun _ h ↦ nomatch h) hm1 fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b133Offset) ((pc_true hpc2).trans (labelAt r hp b133_in_code rfl)) ?_
  refine blk r hp b133_in_code (List.cons_ne_nil _ _) (exec_after run_b125 run_b133) hwf
    (fun _ _ ↦ rfl) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hK3 := KeepC.of_block hpre hx hE hK hm3 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm3 hwf ho h hn
  have hA48 := bytesAt_write_val hm3 (r := 0) (b := r.base) (sz := frameRegion) rfl (o := 4432) (n := 8)
    (v := .lit 48) (by decide) (by decide +kernel)
  have hA0' := kept (by len_tac) hA0 (by decide +kernel)
  have hAsa' := kept (by omega) hAsa (by rw [hSA]; decide +kernel)
  have hval' := kept (by omega) hval (by rw [hv]; decide +kernel)
  have h64' := kept (by simp [NativeRustc.length_wordBytes]) h64
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st3.data .rdi (r.off 576) := regIs_ptr hm3 rfl
  have h1 : Run.RegIs st3.data .rsi (r.off 4096) := regIs_ptr hm3 rfl
  have h2 := toNat_of_lit hm3 (y := .rdx) (c := 344) rfl (by decide)
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hK3.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st4 hpc4 hrsp4 hpost ↦ ?_
  obtain ⟨hc4, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK4 := Keep.of_call hpre hx hE hK3 hS hrsp4 (a := 576) (n := 344)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (hd : o + bs.length ≤ 576 ∨ 920 ≤ o) (h : BytesAt st3.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK3.1 (a := 576) (n := 344) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b134Offset) (by rw [hpc4]; rfl)
    (seg_b134 hp hc hpre hx hE hpos hSA hv hK4
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h64')
      (copy_slice (c := 336) hc4 (by len_tac) hA48) (copy_slice (c := 0) hc4 (by len_tac) hA0')
      (copy_slice (c := 200) hc4 (by omega) hAsa') (kept2 (by omega) (by omega) hval')
      (RegIs.of_saved hS rfl (regIs_label (y := .r14) hm3 rfl)) cont)

end

end NativeRustcX64.SphincsVerifyProof.Chains
