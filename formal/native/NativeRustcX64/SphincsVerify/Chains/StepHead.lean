module

public import NativeRustcX64.SphincsVerify.Chains.StepMid
public import NativeRustc.Sphincs.Address

/-!
# A chain's step on x86-64, its head: the address, `PK.seed`, the address absorbed

`b119` builds the step's address at `8320`, copies the chain's value to `1632` and spills the
position at `64`, then `memset`s hasher A (`seg_b119`); `b120 .. b128` buffer `PK.seed`, count the
position up and copy the address into A's buffer (`seg_b120`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- Step `pos` of chain `i`'s address on layer `l`: the position it leaves (`chain`). -/
def chainAdrs (r : Run) (l i pos : Nat) : List UInt8 :=
  withHash (withChain ((r.key l).adrs 0) i.toUInt32) pos.toUInt32

end

public section

/-- The address's bytes: the layer, zero, the tree, the type `WOTS_HASH`, the key pair, the chain,
the position. -/
theorem chainAdrs_eq (r : Run) (l i pos : Nat) : chainAdrs r l i pos =
    be32 l.toUInt32 ++ (be32 0 ++ (be64 (r.key l).tree ++ (be32 0 ++ (be32 (r.key l).leaf ++
      (be32 i.toUInt32 ++ be32 pos.toUInt32))))) := by
  rw [chainAdrs, OtsKey.adrs_eq, withChain_eq, withHash_eq, adrsBytes]
  rfl

theorem length_chainAdrs (r : Run) (l i pos : Nat) : (chainAdrs r l i pos).length = 32 := by
  rw [chainAdrs_eq]
  rfl

theorem length_seed (r : Run) : r.seed.length = 16 := by
  show ((pkBytes r.w).take 16).length = 16
  simp [length_pkBytes]

/-- The bytes of `0` as a `u32`. -/
theorem bytes_zero4 : (List.range 4).map (byteOf (BitVec.ofNat 64 0)) = be32 0 := by decide

/-- The position's word `BE32(pos)` (`bswap`). -/
theorem bytes_bswap {pos : Nat} (hpos : pos ≤ 2) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32
      (UnOp.apply .trunc .W32 (BitVec.ofNat 64 pos))))) = be32 pos.toUInt32 := by
  obtain rfl | rfl | rfl : pos = 0 ∨ pos = 1 ∨ pos = 2 := by omega
  all_goals decide

variable [Host] {r : Run}

/-- **`b120 .. b128`**: `PK.seed` buffered in A, the position counted up, the address copied
after `PK.seed`; then `b129`. -/
theorem seg_b120 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {adrs v : List UInt8} (hadrs : adrs.length = 32) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E i m)
    (h64 : r.WordAt m 64 pos.toUInt64)
    (hAz : BytesAt m.dmem (r.off 4096) (List.replicate 344 0))
    (hAd : BytesAt m.dmem (r.off 8320) adrs) (hval : BytesAt m.dmem (r.off 1632) v)
    (hcopy : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r l x E i pos (r.seed ++ adrs ++ v) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b120Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b129Offset).toBitVec
  have h0 : BytesAt m.dmem (r.off 4432) ((List.range 8).map (byteOf (BitVec.ofNat 64 0))) := by
    have := BytesAt.slice hAz 336 8
    rw [Run.off_add] at this
    exact this
  have hm := match_withLit (match_frameS hpre hK.1 hK.2.1
    (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b129Offset).toBitVec)
    (k := [(.r14, .label "memcpy")]) ⟨hcopy, trivial⟩) rfl h0
  refine blk r hp b120_in_code (List.cons_ne_nil _ _) run_b120 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b123Offset) ((pc_true hpc).trans (labelAt r hp b123_in_code rfl)) ?_
  refine blk r hp b123_in_code (List.cons_ne_nil _ _) (exec_after run_b120 run_b123) hwf
    (fun _ h ↦ nomatch h) hm1 fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b126Offset) (hpc2.trans (labelAt r hp b126_in_code rfl)) ?_
  refine blk r hp b126_in_code (List.cons_ne_nil _ _) (exec_after run_b123 run_b126) hwf
    (fun _ h ↦ nomatch h) hm2 fun st3 hm3 hpc3 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b127Offset) ((pc_false hpc3).trans rfl) ?_
  refine blk r hp b127_in_code (List.cons_ne_nil _ _) (exec_after run_b126 run_b127) hwf
    (fun _ h ↦ nomatch h) hm3 fun st4 hm4 hpc4 ↦ ?_
  refine pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b128Offset) ((pc_false hpc4).trans rfl) ?_
  refine blk r hp b128_in_code (List.cons_ne_nil _ _) (exec_after run_b127 run_b128) hwf
    (fun _ _ ↦ rfl) hm4 fun st5 hm5 hpc5 ↦ ?_
  have hK5 := KeepC.of_block hpre hx hE hK hm5 hwf (by decide +kernel) rfl
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm5 hwf ho h hn
  have hseed := frame_copy16 hm5 (o := 4296) (o' := 112) (by decide) (by decide +kernel)
    (by decide +kernel) (bs := r.seed) (length_seed r) (take_of_bytesAt hK.2.1.1.1 16)
  have hA16 := bytesAt_write_val hm5 (r := 0) (b := r.base) (sz := frameRegion) rfl (o := 4432)
    (n := 8) (v := .lit 16) (by decide) (by decide +kernel)
  have h64' := frame_write_word hm5 (o := 64) (v := .bin .add .W64 (.load 0 64 8) (.lit 1))
    (w := (pos + 1).toUInt64) (by decide) (by decide +kernel) (by
      have hl : (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b129Offset).toBitVec).load 0 64 8 = pos.toUInt64.toBitVec :=
        load_word h64
      sym_simp
      rw [hl, toBitVec_toUInt64, toBitVec_toUInt64, BitVec.ofNat_add])
  have hA0 : BytesAt m.dmem (r.off 4096) (List.replicate 200 0) := by
    have := take_of_bytesAt hAz 200
    rwa [List.take_replicate, show min 200 344 = 200 from rfl] at this
  have hA0' := kept (by len_tac) hA0 (by decide +kernel)
  have hAd' := kept (by omega) hAd (by rw [hadrs]; decide +kernel)
  have hval' := kept (by omega) hval (by rw [hv]; decide +kernel)
  have h0 : Run.RegIs st5.data .rdi (r.off 4312) := regIs_ptr hm5 rfl
  have h1 : Run.RegIs st5.data .rsi (r.off 8320) := regIs_ptr hm5 rfl
  have h2 := toNat_of_lit hm5 (y := .rdx) (c := 32) rfl (by decide)
  have h15 : Run.RegIs st5.data .r15 (BitVec.ofNat 64 32) := regIs_lit hm5 rfl
  have hbx : Run.RegIs st5.data .rbx (r.off 8320) := regIs_ptr hm5 rfl
  have h12 : Run.RegIs st5.data .r12 (BitVec.ofNat 64 32) := regIs_lit hm5 rfl
  refine call_then hpc5 hc.1 (r.memcpy_pre hpre hK5.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st6 hpc6 hrsp6 hpost ↦ ?_
  obtain ⟨hc6, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK6 := Keep.of_call hpre hx hE hK5 hS hrsp6 (a := 4312) (n := 32)
    (by unfold Scratch; omega) (by decide) hout
  have hAd6 : BytesAt st6.data.dmem (r.off 4312) adrs := copy_slice (c := 0) hc6 (by omega) hAd'
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (hd : o + bs.length ≤ 4312 ∨ 4344 ≤ o) (h : BytesAt st5.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK5.1 (a := 4312) (n := 32) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b129Offset) (by rw [hpc6]; rfl)
    (seg_b129 hp hc hpre hx hE hpos (SA := r.seed ++ adrs) (by simp [length_seed, hadrs]) hv hK6
      (RegIs.of_saved hS rfl h15) (RegIs.of_saved hS rfl hbx) (RegIs.of_saved hS rfl h12)
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h64')
      (kept2 (by len_tac) (by len_tac) hA16) (kept2 (by len_tac) (by len_tac) hA0')
      (BytesAt.cat (kept2 (by rw [length_seed]; omega) (by rw [length_seed]; omega) hseed) hAd6
        (by rw [length_seed]))
      (kept2 (by omega) (by omega) hval')
      (RegIs.of_saved hS rfl (regIs_label (y := .r14) hm5 rfl)) cont)

/-- **`b119`**: the step's address at `8320`, the chain's value copied to `1632`, the position
spilled, `memset` of hasher A; then `b120`. -/
theorem seg_b119 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {v : List UInt8} (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E i m) (hR : Regs r m pos)
    (hcell : BytesAt m.dmem (r.off 184) v)
    (cont : StepCont r l x E i pos (r.seed ++ chainAdrs r l i pos ++ v) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b119Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b120Offset).toBitVec
  have hm := match_frameS hpre hK.1 hK.2.1
    (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b120Offset).toBitVec)
    (k := [(.r12, .ptr 0 4096), (.rbx, .label "memset")])
    ⟨known_ptr hR.2.1, hR.2.2.1, trivial⟩
  refine blk r hp b119_in_code (List.cons_ne_nil _ _) run_b119 hwf (fun _ _ ↦ rfl) hm
    fun st hm1 hpc ↦ ?_
  have hK1 := KeepC.of_block hpre hx hE hK hm1 hwf (by decide +kernel) rfl
  obtain ⟨-, -, -, -, -, s6, s7, s8, -, -⟩ := hK.2.1.2.1
  have p1 := frame_write_load hm1 (o := 8320) (o' := 104) (n := 4) (by decide) (by decide +kernel)
    rfl (by decide) s6
  have p2 := frame_write_val hm1 (o := 8324) (n := 4) (v := .lit 0) (by decide) (by decide +kernel)
  have p3 := frame_write_load hm1 (o := 8328) (o' := 88) (n := 8) (by decide) (by decide +kernel)
    rfl (by decide) s7
  have p4 := frame_write_val hm1 (o := 8336) (n := 4) (v := .lit 0) (by decide) (by decide +kernel)
  have p5 := frame_write_load hm1 (o := 8340) (o' := 60) (n := 4) (by decide) (by decide +kernel)
    rfl (by decide) s8
  have p6 := frame_write_load hm1 (o := 8344) (o' := 72) (n := 4) (by decide) (by decide +kernel)
    rfl (by decide) hK.2.2.2.2
  have p7 := frame_write_val hm1 (o := 8348) (n := 4)
    (v := .un .trunc .W32 (.un .bswap .W32 (.un .trunc .W32 (.reg .rsi)))) (by decide)
    (by decide +kernel)
  have e7 : (Sym.un .trunc .W32 (.un .bswap .W32 (.un .trunc .W32 (.reg .rsi)))).eval
      (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b120Offset).toBitVec) = UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32
        (UnOp.apply .trunc .W32 (BitVec.ofNat 64 pos))) := by
    show UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32 (UnOp.apply .trunc .W32
      (m.regs.get64 .rsi))) = _
    rw [show m.regs.get64 .rsi = BitVec.ofNat 64 pos from hR.1]
  have e0 : (Sym.lit 0).eval (r.env m (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b120Offset).toBitVec) = BitVec.ofNat 64 0 := rfl
  rw [e0, bytes_zero4] at p2 p4
  rw [e7, bytes_bswap hpos] at p7
  have hadrs : BytesAt st.data.dmem (r.off 8320) (chainAdrs r l i pos) := by
    rw [chainAdrs_eq]
    exact BytesAt.cat p1 (BytesAt.cat p2 (BytesAt.cat p3 (BytesAt.cat p4 (BytesAt.cat p5
      (BytesAt.cat p6 p7 rfl) rfl) rfl) rfl) rfl) rfl
  have hval := frame_copy16 hm1 (o := 1632) (o' := 184) (by decide) (by decide +kernel)
    (by decide +kernel) hv hcell
  have h64 := frame_write_word hm1 (o := 64) (v := .reg .rsi) (w := pos.toUInt64) (by decide)
    (by decide +kernel) hR.1
  have h0 : Run.RegIs st.data .rdi (r.off 4096) := regIs_ptr hm1 rfl
  have h1 := toNat_of_lit hm1 (y := .rsi) (c := 0) rfl (by decide)
  have h2 := toNat_of_lit hm1 (y := .rdx) (c := 344) rfl (by decide)
  refine call_then hpc hc.2.1 (r.memset_pre hpre hK1.1 h0 h2 (by decide))
    fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
  rw [h1] at hz
  have hK2 := Keep.of_call hpre hx hE hK1 hS hrsp2 (a := 4096) (n := 344)
    (by unfold Scratch; omega) (by decide) hout
  have kept2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
      (hd : o + bs.length ≤ 4096 ∨ 4440 ≤ o) (h : BytesAt st.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK1.1 (a := 4096) (n := 344) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b120Offset) (by rw [hpc2]; rfl)
    (seg_b120 hp hc hpre hx hE hpos (length_chainAdrs r l i pos) hv hK2
      (kept2 (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h64)
      hz (kept2 (by rw [length_chainAdrs]; decide) (by rw [length_chainAdrs]; decide) hadrs)
      (kept2 (by omega) (by omega) hval)
      (RegIs.of_saved hS rfl (regIs_reg hm1 rfl hR.2.2.2)) cont)

end

end NativeRustcX64.SphincsVerifyProof.Chains
