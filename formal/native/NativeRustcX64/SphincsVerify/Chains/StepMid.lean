module

public import NativeRustcX64.SphincsVerify.Chains.StepTail

/-!
# A chain's step on x86-64, its middle: the clone, the value, the state's copy, the block

From hasher A holding `PK.seed | ADRS` (48 bytes, its state zero) and the chain's value at
`8296`: `b120 .. b124` clone A into hasher B (`seg_b120`), `b125 .. b130` copy the value into B's
buffer (`seg_b125`), `b131 .. b135` copy B's zero state back into A (`seg_b131`), `b136`, `b137`
zero the block at `2024` (`seg_b136`), `b138` copies B's 64 buffered bytes there (`seg_b138`);
then `b139`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

variable [ElfHost] {r : Run}

public section

/-- **`b138`**: B's 64 buffered bytes copied to the zeroed block; then `b139`. -/
theorem seg_b138 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E i m) (h12 : Run.RegIs m .r12 (r.off 4072))
    (hbx : Run.RegIs m .rbx (BitVec.ofNat 64 64)) (h56 : r.WordAt m 56 (pos + 1).toUInt64)
    (hA0 : BytesAt m.dmem (r.off 4072) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 760) T) (hK0 : BytesAt m.dmem (r.off 2024) (List.replicate 136 0))
    (hcopy : Run.RegIs m .r15 (Labels.label "memcpy").toBitVec)
    (hbp : Run.RegIs m .rbp (r.off 2024))
    (hset : Run.RegIs m .r14 (Labels.label "memset").toBitVec)
    (cont : StepCont r l x E i pos T R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b138Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b139Offset).toBitVec
  have hm := match_frameS hpre hK.1 hK.2.1
    (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b139Offset).toBitVec)
    (k := [(.rbx, .lit 64), (.r15, .label "memcpy"), (.rbp, .ptr 0 2024)])
    ⟨known_lit hbx, hcopy, known_ptr hbp, trivial⟩
  refine blk r hp b138_in_code (List.cons_ne_nil _ _) run_b138 hwf (fun _ _ ↦ rfl) hm
    fun st hm' hpc ↦ ?_
  have hK1 := KeepC.of_block hpre hx hE hK hm' hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm' hwf ho h hn
  have hA0' := kept (by len_tac) hA0 (by decide +kernel)
  have hB' := kept (by omega) hB (by rw [hT]; decide +kernel)
  have hK0' := kept (by len_tac) hK0 (by decide +kernel)
  have h56' := kept (by simp [NativeRustc.length_wordBytes]) h56
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st.data .rdi (r.off 2024) := regIs_ptr hm' rfl
  have h1 : Run.RegIs st.data .rsi (r.off 760) := regIs_ptr hm' rfl
  have h2 := toNat_of_lit hm' (y := .rdx) (c := 64) rfl (by decide)
  have hbx' : Run.RegIs st.data .rbx (BitVec.ofNat 64 64) := regIs_lit hm' rfl
  have h12' := regIs_reg hm' rfl h12
  refine call_then_elf hpc hc.1 (r.memcpy_pre hpre hK1.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hc2, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK2 := Keep.of_call hpre hx hE hK1 hS hrsp2 (a := 2024) (n := 64)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (hd : o + bs.length ≤ 2024 ∨ 2088 ≤ o) (h : BytesAt st.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK1.1 (a := 2024) (n := 64) (by decide) (by decide) hout ho hd h
  have hT2 : BytesAt st2.data.dmem (r.off 2024) T := copy_slice (c := 0) hc2 (by omega) hB'
  have hz : BytesAt st2.data.dmem (r.off 2088) (List.replicate 72 0) := by
    have := BytesAt.slice hK0' 64 72
    rw [Run.off_add, List.drop_replicate, List.take_replicate] at this
    exact kept2 (by len_tac) (by len_tac) this
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b139Offset) (by rw [hpc2]; rfl)
    (seg_b139 hp hc hpre hx hE hpos hT hK2 (RegIs.of_saved hS rfl h12')
      (RegIs.of_saved hS rfl hbx')
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h56')
      (kept2 (by len_tac) (by len_tac) hA0') (BytesAt.cat hT2 hz (by omega))
      (RegIs.of_saved hS rfl (regIs_label (y := .r15) hm' rfl))
      (RegIs.of_saved hS rfl (regIs_reg hm' rfl hset)) cont)

/-- **`b136`, `b137`**: the block at `2024` zeroed; then `b138`. -/
theorem seg_b136 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E i m) (h12 : Run.RegIs m .r12 (r.off 4072))
    (h14 : Run.RegIs m .r14 (BitVec.ofNat 64 64)) (h56 : r.WordAt m 56 (pos + 1).toUInt64)
    (hA0 : BytesAt m.dmem (r.off 4072) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 760) T)
    (hcopy : Run.RegIs m .r15 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r l x E i pos T R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b136Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b138Offset).toBitVec
  have hm := match_frameS hpre hK.1 hK.2.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b138Offset).toBitVec) (k := [(.r14, .lit 64)])
    ⟨known_lit h14, trivial⟩
  refine blk r hp b136_in_code (List.cons_ne_nil _ _) run_b136 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b137Offset) ((pc_false hpc).trans rfl) ?_
  refine blk r hp b137_in_code (List.cons_ne_nil _ _) (exec_after run_b136 run_b137) hwf
    (fun _ _ ↦ rfl) hm1 fun st2 hm2 hpc2 ↦ ?_
  have hK1 := KeepC.of_block hpre hx hE hK hm2 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm2 hwf ho h hn
  have hA0' := kept (by len_tac) hA0 (by decide +kernel)
  have hB' := kept (by omega) hB (by rw [hT]; decide +kernel)
  have h56' := kept (by simp [NativeRustc.length_wordBytes]) h56
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st2.data .rdi (r.off 2024) := regIs_ptr hm2 rfl
  have h1 := toNat_of_lit hm2 (y := .rsi) (c := 0) rfl (by decide)
  have h2 := toNat_of_lit hm2 (y := .rdx) (c := 136) rfl (by decide)
  have hbx : Run.RegIs st2.data .rbx (BitVec.ofNat 64 64) := regIs_lit hm2 rfl
  have h12' := regIs_reg hm2 rfl h12
  refine call_then_elf hpc2 hc.2.1 (r.memset_pre hpre hK1.1 h0 h2 (by decide))
    fun st3 hpc3 hrsp3 hpost ↦ ?_
  obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
  rw [h1] at hz
  have hK3 := Keep.of_call hpre hx hE hK1 hS hrsp3 (a := 2024) (n := 136)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (hd : o + bs.length ≤ 2024 ∨ 2160 ≤ o) (h : BytesAt st2.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK1.1 (a := 2024) (n := 136) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b138Offset) (by rw [hpc3]; rfl)
    (seg_b138 hp hc hpre hx hE hpos hT hK3 (RegIs.of_saved hS rfl h12') (RegIs.of_saved hS rfl hbx)
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h56')
      (kept2 (by len_tac) (by len_tac) hA0') (kept2 (by omega) (by omega) hB') hz
      (RegIs.of_saved hS rfl (regIs_reg hm2 rfl hcopy))
      (RegIs.of_saved hS rfl (regIs_ptr (y := .rbp) hm2 rfl))
      (RegIs.of_saved hS rfl (regIs_label (y := .r14) hm2 rfl)) cont)

/-- **`b131`, `b127`, `b135`**: B's `buf_len` 64, B's zero state copied into A; then `b136`. -/
theorem seg_b131 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E i m) (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 16))
    (hbx : Run.RegIs m .rbx (r.off 8296)) (h12 : Run.RegIs m .r12 (BitVec.ofNat 64 16))
    (h56 : r.WordAt m 56 (pos + 1).toUInt64)
    (hB48 : BytesAt m.dmem (r.off 896) ((List.range 8).map (byteOf (BitVec.ofNat 64 48))))
    (hB0 : BytesAt m.dmem (r.off 560) (List.replicate 200 0))
    (hB : BytesAt m.dmem (r.off 760) T)
    (hcopy : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    (hbp : Run.RegIs m .rbp (r.off 560))
    (cont : StepCont r l x E i pos T R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b131Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b136Offset).toBitVec
  have hm := match_withLit (match_frameS hpre hK.1 hK.2.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b136Offset).toBitVec)
    (k := [(.r15, .lit 16), (.rbx, .ptr 0 8296), (.r12, .lit 16), (.r14, .label "memcpy"), (.rbp, .ptr 0 560)])
    ⟨known_lit h15, known_ptr hbx, known_lit h12, hcopy, known_ptr hbp, trivial⟩) rfl hB48
  refine blk r hp b131_in_code (List.cons_ne_nil _ _) run_b131 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b127Offset) ((pc_true hpc).trans (labelAt r hp b127_in_code rfl)) ?_
  refine blk r hp b127_in_code (List.cons_ne_nil _ _) (exec_after run_b131 run_b127) hwf
    (fun _ h ↦ nomatch h) hm1 fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b135Offset) ((pc_true hpc2).trans (labelAt r hp b135_in_code rfl)) ?_
  refine blk r hp b135_in_code (List.cons_ne_nil _ _) (exec_after run_b127 run_b135) hwf
    (fun _ _ ↦ rfl) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hK3 := KeepC.of_block hpre hx hE hK hm3 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm3 hwf ho h hn
  have hB0' := kept (by len_tac) hB0 (by decide +kernel)
  have hB' := kept (by omega) hB (by rw [hT]; decide +kernel)
  have h56' := kept (by simp [NativeRustc.length_wordBytes]) h56
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st3.data .rdi (r.off 4072) := regIs_ptr hm3 rfl
  have h1 : Run.RegIs st3.data .rsi (r.off 560) := regIs_ptr hm3 rfl
  have h2 := toNat_of_lit hm3 (y := .rdx) (c := 200) rfl (by decide)
  have h14 : Run.RegIs st3.data .r14 (BitVec.ofNat 64 64) := regIs_lit hm3 rfl
  have h12' : Run.RegIs st3.data .r12 (r.off 4072) := regIs_ptr hm3 rfl
  refine call_then_elf hpc3 hc.1 (r.memcpy_pre hpre hK3.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st4 hpc4 hrsp4 hpost ↦ ?_
  obtain ⟨hc4, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK4 := Keep.of_call hpre hx hE hK3 hS hrsp4 (a := 4072) (n := 200)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (hd : o + bs.length ≤ 4072 ∨ 4272 ≤ o) (h : BytesAt st3.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK3.1 (a := 4072) (n := 200) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b136Offset) (by rw [hpc4]; rfl)
    (seg_b136 hp hc hpre hx hE hpos hT hK4 (RegIs.of_saved hS rfl h12') (RegIs.of_saved hS rfl h14)
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h56')
      (copy_slice (c := 0) hc4 (by len_tac) hB0') (kept2 (by omega) (by omega) hB')
      (RegIs.of_saved hS rfl (regIs_label (y := .r15) hm3 rfl)) cont)

/-- **`b125 .. b130`**: the chain's value copied into B's buffer after its 48 bytes; then
`b131`. -/
theorem seg_b125 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {SA v : List UInt8} (hSA : SA.length = 48) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E i m)
    (h56 : r.WordAt m 56 (pos + 1).toUInt64)
    (hB48 : BytesAt m.dmem (r.off 896) ((List.range 8).map (byteOf (BitVec.ofNat 64 48))))
    (hB0 : BytesAt m.dmem (r.off 560) (List.replicate 200 0))
    (hBsa : BytesAt m.dmem (r.off 760) SA) (hval : BytesAt m.dmem (r.off 8296) v)
    (hcopy : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    (hbp : Run.RegIs m .rbp (r.off 560))
    (cont : StepCont r l x E i pos (SA ++ v) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b125Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b131Offset).toBitVec
  have hm := match_withLit (match_frameS hpre hK.1 hK.2.1
    (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b131Offset).toBitVec)
    (k := [(.r14, .label "memcpy")]) ⟨hcopy, trivial⟩) rfl hB48
  refine blk r hp b125_in_code (List.cons_ne_nil _ _) run_b125 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b128Offset) (hpc.trans (labelAt r hp b128_in_code rfl)) ?_
  refine blk r hp b128_in_code (List.cons_ne_nil _ _) (exec_after run_b125 run_b128) hwf
    (fun _ h ↦ nomatch h) hm1 fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b129Offset) ((pc_false hpc2).trans rfl) ?_
  refine blk r hp b129_in_code (List.cons_ne_nil _ _) (exec_after run_b128 run_b129) hwf
    (fun _ h ↦ nomatch h) hm2 fun st3 hm3 hpc3 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b130Offset) ((pc_false hpc3).trans rfl) ?_
  refine blk r hp b130_in_code (List.cons_ne_nil _ _) (exec_after run_b129 run_b130) hwf
    (fun _ _ ↦ rfl) hm3 fun st4 hm4 hpc4 ↦ ?_
  have hK4 := KeepC.of_block hpre hx hE hK hm4 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm4 hwf ho h hn
  have hB48' := bytesAt_write_val hm4 (r := 0) (b := r.base) (sz := frameRegion) rfl (o := 896) (n := 8)
    (v := .lit 48) (by decide) (by decide +kernel)
  have hB0' := kept (by len_tac) hB0 (by decide +kernel)
  have hBsa' := kept (by omega) hBsa (by rw [hSA]; decide +kernel)
  have hval' := kept (by omega) hval (by rw [hv]; decide +kernel)
  have h56' := kept (by simp [NativeRustc.length_wordBytes]) h56
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st4.data .rdi (r.off 808) := regIs_ptr hm4 rfl
  have h1 : Run.RegIs st4.data .rsi (r.off 8296) := regIs_ptr hm4 rfl
  have h2 := toNat_of_lit hm4 (y := .rdx) (c := 16) rfl (by decide)
  have h15 : Run.RegIs st4.data .r15 (BitVec.ofNat 64 16) := regIs_lit hm4 rfl
  have hbx : Run.RegIs st4.data .rbx (r.off 8296) := regIs_ptr hm4 rfl
  have h12 : Run.RegIs st4.data .r12 (BitVec.ofNat 64 16) := regIs_lit hm4 rfl
  refine call_then_elf hpc4 hc.1 (r.memcpy_pre hpre hK4.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st5 hpc5 hrsp5 hpost ↦ ?_
  obtain ⟨hc5, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK5 := Keep.of_call hpre hx hE hK4 hS hrsp5 (a := 808) (n := 16)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (hd : o + bs.length ≤ 808 ∨ 824 ≤ o) (h : BytesAt st4.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK4.1 (a := 808) (n := 16) (by decide) (by decide) hout ho hd h
  have hv5 : BytesAt st5.data.dmem (r.off 808) v := copy_slice (c := 0) hc5 (by omega) hval'
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b131Offset) (by rw [hpc5]; rfl)
    (seg_b131 hp hc hpre hx hE hpos (by simp; omega) hK5 (RegIs.of_saved hS rfl h15)
      (RegIs.of_saved hS rfl hbx) (RegIs.of_saved hS rfl h12)
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h56')
      (kept2 (by len_tac) (by len_tac) hB48') (kept2 (by len_tac) (by len_tac) hB0')
      (BytesAt.cat (kept2 (by omega) (by omega) hBsa') hv5 (by omega))
      (RegIs.of_saved hS rfl (regIs_label (y := .r14) hm4 rfl))
      (RegIs.of_saved hS rfl (regIs_reg hm4 rfl hbp)) cont)

/-- **`b120`, `b116`, `b124`**: A's `buf_len` 48, A cloned into B; then `b125`. -/
theorem seg_b120 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {SA v : List UInt8} (hSA : SA.length = 48) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E i m)
    (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 32)) (hbx : Run.RegIs m .rbx (r.off 9320))
    (h12 : Run.RegIs m .r12 (BitVec.ofNat 64 32)) (h56 : r.WordAt m 56 (pos + 1).toUInt64)
    (hA16 : BytesAt m.dmem (r.off 4408) ((List.range 8).map (byteOf (BitVec.ofNat 64 16))))
    (hA0 : BytesAt m.dmem (r.off 4072) (List.replicate 200 0))
    (hAsa : BytesAt m.dmem (r.off 4272) SA) (hval : BytesAt m.dmem (r.off 8296) v)
    (hcopy : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    (hbp : Run.RegIs m .rbp (r.off 560))
    (cont : StepCont r l x E i pos (SA ++ v) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b120Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b125Offset).toBitVec
  have hm := match_withLit (match_frameS hpre hK.1 hK.2.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b125Offset).toBitVec)
    (k := [(.r15, .lit 32), (.rbx, .ptr 0 9320), (.r12, .lit 32), (.r14, .label "memcpy"), (.rbp, .ptr 0 560)])
    ⟨known_lit h15, known_ptr hbx, known_lit h12, hcopy, known_ptr hbp, trivial⟩) rfl hA16
  refine blk r hp b120_in_code (List.cons_ne_nil _ _) run_b120 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b116Offset) ((pc_true hpc).trans (labelAt r hp b116_in_code rfl)) ?_
  refine blk r hp b116_in_code (List.cons_ne_nil _ _) (exec_after run_b120 run_b116) hwf
    (fun _ h ↦ nomatch h) hm1 fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b124Offset) ((pc_true hpc2).trans (labelAt r hp b124_in_code rfl)) ?_
  refine blk r hp b124_in_code (List.cons_ne_nil _ _) (exec_after run_b116 run_b124) hwf
    (fun _ _ ↦ rfl) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hK3 := KeepC.of_block hpre hx hE hK hm3 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm3 hwf ho h hn
  have hA48 := bytesAt_write_val hm3 (r := 0) (b := r.base) (sz := frameRegion) rfl (o := 4408) (n := 8)
    (v := .lit 48) (by decide) (by decide +kernel)
  have hA0' := kept (by len_tac) hA0 (by decide +kernel)
  have hAsa' := kept (by omega) hAsa (by rw [hSA]; decide +kernel)
  have hval' := kept (by omega) hval (by rw [hv]; decide +kernel)
  have h56' := kept (by simp [NativeRustc.length_wordBytes]) h56
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  have h0 : Run.RegIs st3.data .rdi (r.off 560) := regIs_ptr hm3 rfl
  have h1 : Run.RegIs st3.data .rsi (r.off 4072) := regIs_ptr hm3 rfl
  have h2 := toNat_of_lit hm3 (y := .rdx) (c := 344) rfl (by decide)
  refine call_then_elf hpc3 hc.1 (r.memcpy_pre hpre hK3.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st4 hpc4 hrsp4 hpost ↦ ?_
  obtain ⟨hc4, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK4 := Keep.of_call hpre hx hE hK3 hS hrsp4 (a := 560) (n := 344)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
      (hd : o + bs.length ≤ 560 ∨ 904 ≤ o) (h : BytesAt st3.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK3.1 (a := 560) (n := 344) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b125Offset) (by rw [hpc4]; rfl)
    (seg_b125 hp hc hpre hx hE hpos hSA hv hK4
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h56')
      (copy_slice (c := 336) hc4 (by len_tac) hA48) (copy_slice (c := 0) hc4 (by len_tac) hA0')
      (copy_slice (c := 200) hc4 (by omega) hAsa') (kept2 (by omega) (by omega) hval')
      (RegIs.of_saved hS rfl (regIs_label (y := .r14) hm3 rfl))
      (RegIs.of_saved hS rfl (regIs_ptr (y := .rbp) hm3 rfl)) cont)

end

end NativeRustcX64.SphincsVerifyProof.Chains
