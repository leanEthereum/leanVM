module

public import NativeRustcArm.SphincsVerify.Chains.StepMid

/-!
# A chain's step, its head: the address, `PK.seed`, the address absorbed

`b107` builds the step's address at `13888` and copies the chain's value to `12864`, then
`memset`s hasher A (`seg_b107`); `b108 .. b115` buffer `PK.seed` and copy the address into A's
buffer (`seg_b108`). With `StepMid`, `StepTail`: **a step** (`step`), from the step's head at
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
  show (r.pkBytes.take 16).length = 16
  simp [r.hpk]

/-- The bytes of `0` as a `u32`. -/
theorem bytes_zero4 : (List.range 4).map (byteOf (BitVec.ofNat 64 0)) = be32 0 := by decide

variable [ElfHost] {r : Run}

/-- **`b108 .. b115`**: `PK.seed` buffered in A, the address copied after it; then `b116`. -/
theorem seg_b108 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) {adrs v : List UInt8} (hadrs : adrs.length = 32) (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m) (hR : Regs r m pos i)
    (hAz : BytesAt m.dmem (r.off 8640) (List.replicate 344 0))
    (hAd : BytesAt m.dmem (r.off 13888) adrs) (hval : BytesAt m.dmem (r.off 12864) v)
    (cont : StepCont r l x E pos i (r.seed ++ adrs ++ v) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b108Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have h0 : BytesAt m.dmem (r.off 8976) ((List.range 8).map (byteOf (BitVec.ofNat 64 0))) := by
    have := BytesAt.slice hAz 336 8
    rw [r.off_add] at this
    exact this
  have hm := match_withLit (match_frameS hpre hK (k := []) trivial) rfl h0
  refine blk r hp b108_in_code (List.cons_ne_nil _ _) run_b108 hwf hm fun st hm1 hpc ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b111Offset) ((pc_true hpc).trans (labelAt r hp b111_in_code rfl)) ?_
  refine blk r hp b111_in_code (List.cons_ne_nil _ _) (exec_after run_b108 run_b111) hwf hm1
    fun st2 hm2 hpc2 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b113Offset) (hpc2.trans (labelAt r hp b113_in_code rfl)) ?_
  refine blk r hp b113_in_code (List.cons_ne_nil _ _) (exec_after run_b111 run_b113) hwf hm2
    fun st3 hm3 hpc3 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b114Offset) ((pc_false hpc3).trans rfl) ?_
  refine blk r hp b114_in_code (List.cons_ne_nil _ _) (exec_after run_b113 run_b114) hwf hm3
    fun st4 hm4 hpc4 ↦ ?_
  refine pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b115Offset) ((pc_false hpc4).trans rfl) ?_
  refine blk r hp b115_in_code (List.cons_ne_nil _ _) (exec_after run_b114 run_b115) hwf hm4
    fun st5 hm5 hpc5 ↦ ?_
  have hK5 := Keep.of_block hpre hx hE hK hm5 hwf (by decide +kernel)
  have hseed := frame_copy16 hm5 (o := 8840) (o' := 448) (by decide) (by decide +kernel)
    (by decide +kernel) (bs := r.seed) (length_seed r) (take_of_bytesAt hK.2.1.1 16)
  have hA16 := frame_write_lit hm5 (o := 8976) (n := 8) (c := 16) (by decide) (by decide +kernel)
  have hA0 : BytesAt m.dmem (r.off 8640) (List.replicate 200 0) := by
    have := take_of_bytesAt hAz 200
    rwa [List.take_replicate, show min 200 344 = 200 from rfl] at this
  have hA0' := r.bytesAt_kept hpre hm5 hwf (by len_tac) hA0 (by decide +kernel)
  have hAd' := r.bytesAt_kept hpre hm5 hwf (by omega) hAd (by rw [hadrs]; decide +kernel)
  have hval' := r.bytesAt_kept hpre hm5 hwf (by omega) hval (by rw [hv]; decide +kernel)
  have h0 : Run.RegIs st5.data .X0 (r.off 8856) := regIs_ptr hm5 rfl
  have h1 : Run.RegIs st5.data .X1 (r.off 13888) := regIs_ptr hm5 rfl
  have h2 := x2_eq hm5 (c := 32) rfl (by decide)
  have h22 : Run.RegIs st5.data .X22 (r.off 13888) := regIs_ptr hm5 rfl
  have h23 : Run.RegIs st5.data .X23 (BitVec.ofNat 64 32) := regIs_lit hm5 rfl
  have h24 : Run.RegIs st5.data .X24 (BitVec.ofNat 64 32) := regIs_lit hm5 rfl
  have hR5 : Regs r st5.data (pos + 1) i := by
    refine ⟨?_, regIs_reg hm5 rfl hR.2.1,
      r.bytesAt_kept hpre hm5 hwf (by rw [NativeRustc.length_wordBytes]; decide) hR.2.2
        (by rw [NativeRustc.length_wordBytes]; decide +kernel)⟩
    unfold Run.RegIs
    rw [hm5.regs .X20 _ rfl]
    have h20 : (r.env m).regs .X20 = BitVec.ofNat 64 pos := hR.1
    sym_simp
    rw [h20, BitVec.ofNat_add]
  refine call_then_elf hpc5 hc.1 (r.memcpy_pre hpre hK5.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st6 hpc6 hpost ↦ ?_
  obtain ⟨hc6, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hK6 := Keep.of_call hpre hx hE hK5 hS (a := 8856) (n := 32) (by unfold Scratch; omega)
    (by decide) hout
  have hAd6 : BytesAt st6.data.dmem (r.off 8856) adrs := copy_slice (c := 0) hc6 (by omega) hAd'
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21616)
      (hd : o + bs.length ≤ 8856 ∨ 8888 ≤ o) (h : BytesAt st5.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK5.1 (a := 8856) (n := 32) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b116Offset) (by rw [hpc6]; rfl)
    (seg_b116 hp hc hpre hx hE hpos (SA := r.seed ++ adrs) (by simp [length_seed, hadrs]) hv hK6
      (Regs.of_call hpre hK5.1 hS (a := 8856) (n := 32) (by unfold Scratch; omega) (by decide) hout hR5)
      (RegIs.of_saved hS rfl h22) (RegIs.of_saved hS rfl h23)
      (RegIs.of_saved hS rfl h24) (kept (by len_tac) (by len_tac) hA16)
      (kept (by len_tac) (by len_tac) hA0')
      (BytesAt.cat (kept (by rw [length_seed]; omega) (by rw [length_seed]; omega) hseed) hAd6
        (by rw [length_seed]))
      (kept (by omega) (by omega) hval') cont)

/-- **`b107`**: the step's address at `13888`, the chain's value copied to `12864`, `memset` of
hasher A; then `b108`. -/
theorem seg_b107 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) (hi : i < 64) {v : List UInt8} (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m) (hR : Regs r m pos i)
    (hcell : BytesAt m.dmem (r.off 8224) v)
    (cont : StepCont r l x E pos i (r.seed ++ chainAdrs r l i pos ++ v) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b107Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := []) trivial
  refine blk r hp b107_in_code (List.cons_ne_nil _ _) run_b107 hwf hm fun st hm1 hpc ↦ ?_
  have hK1 := Keep.of_block hpre hx hE hK hm1 hwf (by decide +kernel)
  obtain ⟨-, -, -, -, -, -, -, -, s9, s10, s11⟩ := hK.2.2.1
  have p1 := frame_write_load hm1 (o := 13888) (o' := 432) (n := 4) (by decide) (by decide +kernel)
    rfl (by decide) s10
  have p2 := frame_write_lit hm1 (o := 13892) (n := 4) (c := 0) (by decide) (by decide +kernel)
  have p3 := frame_write_load hm1 (o := 13896) (o' := 440) (n := 8) (by decide) (by decide +kernel)
    rfl (by decide) s11
  have p4 := frame_write_lit hm1 (o := 13904) (n := 4) (c := 0) (by decide) (by decide +kernel)
  have p5 := frame_write_load hm1 (o := 13908) (o' := 424) (n := 4) (by decide) (by decide +kernel)
    rfl (by decide) s9
  have p6 := frame_write_val hm1 (o := 13912) (n := 4) (v := .reg .X26) (by decide)
    (by decide +kernel)
  have p7 := frame_write_val hm1 (o := 13916) (n := 4) (v := .un .rev .W32 (.reg .X20))
    (by decide) (by decide +kernel)
  rw [bytes_zero4] at p2 p4
  have h26 : (Sym.reg .X26).eval (r.env m) = BitVec.ofNat 64 (i * 16777216) := hR.2.1
  rw [h26, bytes_chainWord (by omega)] at p6
  have h20 : (Sym.un .rev .W32 (.reg .X20)).eval (r.env m) =
      UnOp.apply .rev .W32 (BitVec.ofNat 64 pos) := congrArg _ hR.1
  rw [h20, bytes_rev32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at p7
  have hadrs : BytesAt st.data.dmem (r.off 13888) (chainAdrs r l i pos) := by
    rw [chainAdrs_eq]
    exact BytesAt.cat p1 (BytesAt.cat p2 (BytesAt.cat p3 (BytesAt.cat p4 (BytesAt.cat p5
        (BytesAt.cat p6 p7 rfl) rfl) rfl) rfl) rfl) rfl
  have hval := frame_copy16 hm1 (o := 12864) (o' := 8224) (by decide) (by decide +kernel)
    (by decide +kernel) hv hcell
  have h0 : Run.RegIs st.data .X0 (r.off 8640) := regIs_ptr hm1 rfl
  have h2 := x2_eq hm1 (c := 344) rfl (by decide)
  have hR1 := Regs.of_block hpre hm1 hwf rfl rfl (by decide +kernel) hR
  refine call_then_elf hpc hc.2.1 (r.memset_pre hpre hK1.1 h0 h2 (by decide)) fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
  rw [x1_zero hm1 rfl] at hz
  have hK2 := Keep.of_call hpre hx hE hK1 hS (a := 8640) (n := 344) (by unfold Scratch; omega)
    (by decide) hout
  have kept := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21616)
      (hd : o + bs.length ≤ 8640 ∨ 8984 ≤ o) (h : BytesAt st.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hK1.1 (a := 8640) (n := 344) (by decide) (by decide) hout ho hd h
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b108Offset) (by rw [hpc2]; rfl)
    (seg_b108 hp hc hpre hx hE hpos (length_chainAdrs r l i pos) hv hK2
      (Regs.of_call hpre hK1.1 hS (a := 8640) (n := 344) (by unfold Scratch; omega) (by decide) hout hR1)
      hz (kept (by rw [length_chainAdrs]; decide) (by rw [length_chainAdrs]; decide) hadrs)
      (kept (by omega) (by omega) hval) cont)

end

end NativeRustcArm.SphincsVerifyProof.Chains
