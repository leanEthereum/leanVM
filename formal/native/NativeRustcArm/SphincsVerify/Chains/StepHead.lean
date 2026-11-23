module

public import NativeRustcArm.SphincsVerify.Chains.StepMid

/-!
# A chain's step, its head: the address, `PK.seed`, the address absorbed

`b116` builds the step's address at `21648` and copies the chain's value to `15984`, then
`memset`s hasher A (`seg_b116`); `b117 .. b124` buffer `PK.seed` and copy the address into A's
buffer (`seg_b117`). With `StepMid`, `StepTail`: **a step** (`step`), from the step's head at
position `pos` to the value `th` of the chain's address and the old value.
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- Step `pos` of chain `i`'s address on layer `l`: the position it leaves (`chain`). -/
def chainAdrs (r : Run) (l i pos : Nat) : List UInt8 :=
  withHash (withChain ((r.key l).adrs 0) i.toUInt32) pos.toUInt32

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

variable [NativeRustcArm.Host] {r : Run}

/-- **`b117 .. b124`**: `PK.seed` buffered in A, the address copied after it; then `b125`. -/
theorem seg_b117 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) {adrs v : List UInt8} (hadrs : adrs.length = 32) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m) (hR : Regs m pos i)
    (hAz : BytesAt m.dmem (r.off 16400) (List.replicate 344 0))
    (hAd : BytesAt m.dmem (r.off 21648) adrs) (hval : BytesAt m.dmem (r.off 15984) v)
    (cont : StepCont r l x E pos i (r.seed ++ adrs ++ v) R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b117Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have h0 : BytesAt m.dmem (r.off 16736) ((List.range 8).map (byteOf (BitVec.ofNat 64 0))) := by
    have := BytesAt.slice hAz 336 8
    rw [r.off_add] at this
    exact this
  have hm := match_withLit (match_frameS hpre hK (k := []) trivial) rfl h0
  refine blk r hp b117_in_code (List.cons_ne_nil _ _) run_b117 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b120Offset) ((pc_true hpc).trans (labelAt r hp b120_in_code rfl)) ?_
  refine blk r hp b120_in_code (List.cons_ne_nil _ _) (exec_after run_b117 run_b120) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b122Offset) (hpc2.trans (labelAt r hp b122_in_code rfl)) ?_
  refine blk r hp b122_in_code (List.cons_ne_nil _ _) (exec_after run_b120 run_b122) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b123Offset) ((pc_false hpc3).trans rfl) ?_
  refine blk r hp b123_in_code (List.cons_ne_nil _ _) (exec_after run_b122 run_b123) hwf hm3
    fun st4 hm4 hpc4 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b124Offset) ((pc_false hpc4).trans rfl) ?_
  refine blk r hp b124_in_code (List.cons_ne_nil _ _) (exec_after run_b123 run_b124) hwf hm4
    fun st5 hm5 hpc5 ↦ ?_
  have hK5 := Keep.of_block hpre hx hE hK hm5 hwf (by decide +kernel)
  have hseed := frame_copy16 hm5 (o := 16600) (o' := 8208) (by decide) (by decide +kernel)
    (by decide +kernel) (bs := r.seed) (length_seed r) (take_of_bytesAt hK.2.1.1 16)
  have hA16 := frame_write_lit hm5 (o := 16736) (n := 8) (c := 16) (by decide) (by decide +kernel)
  have hA0 : BytesAt m.dmem (r.off 16400) (List.replicate 200 0) := by
    have := take_of_bytesAt hAz 200
    rwa [List.take_replicate, show min 200 344 = 200 from rfl] at this
  have hA0' := r.bytesAt_kept hpre hm5 hwf (by len_tac) hA0 (by decide +kernel)
  have hAd' := r.bytesAt_kept hpre hm5 hwf (by omega) hAd (by rw [hadrs]; decide +kernel)
  have hval' := r.bytesAt_kept hpre hm5 hwf (by omega) hval (by rw [hv]; decide +kernel)
  have h0 : Run.RegIs st5.data .X0 (r.off 16616) := regIs_ptr hm5 rfl
  have h1 : Run.RegIs st5.data .X1 (r.off 21648) := regIs_ptr hm5 rfl
  have h2 := x2_eq hm5 (c := 32) rfl (by decide)
  have h22 : Run.RegIs st5.data .X22 (r.off 21648) := regIs_ptr hm5 rfl
  have h23 : Run.RegIs st5.data .X23 (BitVec.ofNat 64 32) := regIs_lit hm5 rfl
  have h24 : Run.RegIs st5.data .X24 (BitVec.ofNat 64 32) := regIs_lit hm5 rfl
  have hR5 : Regs st5.data (pos + 1) i := by
    refine ⟨?_, regIs_reg hm5 rfl hR.2.1, regIs_reg hm5 rfl hR.2.2⟩
    unfold Run.RegIs
    rw [hm5.regs .X19 _ rfl]
    have h19 : (r.env m).regs .X19 = BitVec.ofNat 64 pos := hR.1
    sym_simp
    rw [h19, BitVec.ofNat_add]
  refine call_then hpc5 hc.1 (r.memcpy_pre hpre hK5.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st6 hpc6 hpost ↦ ?_
  obtain ⟨hc6, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK6 := Keep.of_call hpre hx hE hK5 hS (a := 16616) (n := 32) (by unfold Scratch; omega)
    (by decide) hout
  have hAd6 : BytesAt st6.data.dmem (r.off 16616) adrs := copy_slice (c := 0) hc6 (by omega) hAd'
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29376)
      (hd : o + bs.length ≤ 16616 ∨ 16648 ≤ o) (h : BytesAt st5.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK5.1 (a := 16616) (n := 32) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b125Offset) (by rw [hpc6]; rfl)
    (seg_b125 hp hc hpre hx hE hpos (SA := r.seed ++ adrs) (by simp [length_seed, hadrs]) hv hK6
      (Regs.of_saved hS hR5) (RegIs.of_saved hS rfl h22) (RegIs.of_saved hS rfl h23)
      (RegIs.of_saved hS rfl h24) (kept (by len_tac) (by len_tac) hA16)
      (kept (by len_tac) (by len_tac) hA0')
      (BytesAt.cat (kept (by rw [length_seed]; omega) (by rw [length_seed]; omega) hseed) hAd6
        (by rw [length_seed]))
      (kept (by omega) (by omega) hval') cont)

/-- **`b116`**: the step's address at `21648`, the chain's value copied to `15984`, `memset` of
hasher A; then `b117`. -/
theorem seg_b116 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) (hi : i < 64) {v : List UInt8} (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m) (hR : Regs m pos i)
    (h22 : Run.RegIs m .X22 (r.off 21648)) (hcell : BytesAt m.dmem (r.off 29248) v)
    (cont : StepCont r l x E pos i (r.seed ++ chainAdrs r l i pos ++ v) R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b116Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := [(.X22, .ptr 0 21648)]) ⟨known_ptr h22, trivial⟩
  refine blk r hp b116_in_code (List.cons_ne_nil _ _) run_b116 hwf hm fun st hm1 hpc ↦ ?_
  have hK1 := Keep.of_block hpre hx hE hK hm1 hwf (by decide +kernel)
  obtain ⟨-, -, -, -, -, -, -, -, s9, s10, s11⟩ := hK.2.2.1
  have p1 := frame_write_load hm1 (o := 21648) (o' := 416) (n := 4) (by decide) (by decide +kernel)
    rfl (by decide) s10
  have p2 := frame_write_lit hm1 (o := 21652) (n := 4) (c := 0) (by decide) (by decide +kernel)
  have p3 := frame_write_load hm1 (o := 21656) (o' := 424) (n := 8) (by decide) (by decide +kernel)
    rfl (by decide) s11
  have p4 := frame_write_lit hm1 (o := 21664) (n := 4) (c := 0) (by decide) (by decide +kernel)
  have p5 := frame_write_load hm1 (o := 21668) (o' := 408) (n := 4) (by decide) (by decide +kernel)
    rfl (by decide) s9
  have p6 := frame_write_val hm1 (o := 21672) (n := 4) (v := .reg .X20) (by decide)
    (by decide +kernel)
  have p7 := frame_write_val hm1 (o := 21676) (n := 4) (v := .un .rev .W32 (.reg .X19))
    (by decide) (by decide +kernel)
  rw [bytes_zero4] at p2 p4
  have h20 : (Sym.reg .X20).eval (r.env m) = BitVec.ofNat 64 (i * 16777216) := hR.2.1
  rw [h20, bytes_chainWord (by omega)] at p6
  have h19 : (Sym.un .rev .W32 (.reg .X19)).eval (r.env m) =
      UnOp.apply .rev .W32 (BitVec.ofNat 64 pos) := congrArg _ hR.1
  rw [h19, bytes_rev32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at p7
  have hadrs : BytesAt st.data.dmem (r.off 21648) (chainAdrs r l i pos) := by
    rw [chainAdrs_eq]
    exact BytesAt.cat p1 (BytesAt.cat p2 (BytesAt.cat p3 (BytesAt.cat p4 (BytesAt.cat p5
        (BytesAt.cat p6 p7 rfl) rfl) rfl) rfl) rfl) rfl
  have hval := frame_copy16 hm1 (o := 15984) (o' := 29248) (by decide) (by decide +kernel)
    (by decide +kernel) hv hcell
  have h0 : Run.RegIs st.data .X0 (r.off 16400) := regIs_ptr hm1 rfl
  have h2 := x2_eq hm1 (c := 344) rfl (by decide)
  have hR1 := Regs.of_block hm1 rfl rfl rfl hR
  refine call_then hpc hc.2.1 (r.memset_pre hpre hK1.1 h0 h2 (by decide)) fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
  rw [x1_zero hm1 rfl] at hz
  have hK2 := Keep.of_call hpre hx hE hK1 hS (a := 16400) (n := 344) (by unfold Scratch; omega)
    (by decide) hout
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29376)
      (hd : o + bs.length ≤ 16400 ∨ 16744 ≤ o) (h : BytesAt st.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK1.1 (a := 16400) (n := 344) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b117Offset) (by rw [hpc2]; rfl)
    (seg_b117 hp hc hpre hx hE hpos (length_chainAdrs r l i pos) hv hK2 (Regs.of_saved hS hR1) hz
      (kept (by rw [length_chainAdrs]; decide) (by rw [length_chainAdrs]; decide) hadrs) (kept (by omega) (by omega) hval) cont)

end

end NativeRustcArm.SphincsVerifyProof.Chains
