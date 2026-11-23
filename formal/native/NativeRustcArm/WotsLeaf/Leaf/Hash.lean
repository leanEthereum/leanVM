module

public import NativeRustcArm.WotsLeaf.Chain.Loop
public import NativeRustcArm.WotsLeaf.Leaf.Bytes

/-!
# The leaf's hash

From the chains' end at `b44` (directive 603): the leaf hash's address (type 2) at 1776
(`leafAddr_bytes`), `memset` of the hasher at 2160 (`leaf_b44`); `update` with `P`, the address
and the 928 bytes of the ends, `finalize` into 2128 (`leaf_b45`), at `b49` (directive 631).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Keccak NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf
open LeanVM.Protocol.KeccakHash Leaf Chain

public section

section
variable {r : Run} [Labels]

/-- **The leaf hash's address** at 1776, as `b44` writes it. -/
theorem leafAddr_bytes {x E : List UInt8} {m m' : MachineData} {S : SState}
    (hm : Match (r.env m) S m') (hK : r.CK x E m)
    (w1 : covers S.mem 0 1776 4 (.load 0 24 4) = true)
    (w2 : covers S.mem 0 1780 2 (.load 0 28 4) = true)
    (w3 : covers S.mem 0 1782 1 (.load 0 20 4) = true)
    (w4 : covers S.mem 0 1783 1 (.lit 2) = true) (w5 : covers S.mem 0 1784 8 (.lit 0) = true) :
    BytesAt m'.dmem (r.off 1776) (r.addr 2 0) := by
  have a1 : BytesAt m'.dmem (r.off 1776) (u32Bytes r.e) :=
    frame_write_load hm (o := 1776) (o' := 24) (n := 4) (by decide) w1 (length_u32Bytes _)
      (by decide) (CK.slot24 hK)
  have a2 : BytesAt m'.dmem (r.off 1780) ((u32Bytes r.hi).take 2) :=
    bytesAt_write_loadTake hm (r := 0) (o := 1780) (n := 2) (b := r.base) (sz := 2752) rfl
      (by decide) (r' := 0) (o' := 28) (k := 4) w2 (bs := u32Bytes r.hi) (length_u32Bytes _)
      (by decide) (by decide) (CK.slot28 hK)
  have a3 : BytesAt m'.dmem (r.off 1782) ((u32Bytes (r.hi >>> 16)).take 1) :=
    bytesAt_write_loadTake hm (r := 0) (o := 1782) (n := 1) (b := r.base) (sz := 2752) rfl
      (by decide) (r' := 0) (o' := 20) (k := 4) w3 (bs := u32Bytes (r.hi >>> 16))
      (length_u32Bytes _) (by decide) (by decide) (CK.slot20 hK)
  rw [take_hi16] at a3
  have a4 : BytesAt m'.dmem (r.off 1783) [(2 : UInt8) ||| (0 : Nat).toUInt8 <<< 5] := by
    have := bytesAt_write_val hm (b := r.base) (sz := 2752) rfl (o := 1783) (n := 1) (by decide) w4
    have e : (List.range 1).map (byteOf (BitVec.ofNat 64 2)) =
        [(2 : UInt8) ||| (0 : Nat).toUInt8 <<< 5] := by decide
    rw [← e]
    exact this
  have a5 : BytesAt m'.dmem (r.off 1784) (List.replicate 8 0) := by
    have := bytesAt_write_val hm (b := r.base) (sz := 2752) rfl (o := 1784) (n := 8) (by decide) w5
    rw [← bytes_zero]
    exact this
  rw [Run.addr_eq]
  refine BytesAt.cat a1 (BytesAt.cat a2 (BytesAt.cat a3 (BytesAt.cat a4 a5 rfl) ?_) ?_) ?_
  · rw [List.length_take, List.length_drop, length_u32Bytes]; decide
  · rw [List.length_take, length_u32Bytes]; decide
  · rw [length_u32Bytes]

end

variable [NativeRustcArm.Host] {r : Run}

/-- **`b44`**: the leaf hash's address at 1776, `memset` of the hasher at 2160; then `b45`. -/
theorem leaf_b44 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m)
    (h20 : Run.RegIs m .X20 r.m0.regs.X1.toBitVec)
    (cont : ∀ m', r.CK x E m' → Run.RegIs m' .X20 r.m0.regs.X1.toBitVec →
      BytesAt m'.dmem (r.off 1776) (r.addr 2 0) → HasherAt r m' 2160 [] →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', r.pc NativeRustcArm.Xmss.WotsLeaf.b45Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b44Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK.1.1 (k := []) trivial
  refine blk r hp b44_in_code (List.cons_ne_nil _ _) run_b44 hwf hm fun st hm1 hpc ↦ ?_
  have hK1 := CK.of_block hpre hK hm1 hwf (by decide +kernel) (by decide +kernel)
  have hadr := leafAddr_bytes hm1 hK (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have h20' := regIs_reg hm1 rfl h20
  refine callAt hpc hc.2.1 ?_
  obtain ⟨hpre2, hpost2⟩ := memsetFrame hpre hK1.1 (regIs_ptr hm1 (o := 2160) rfl)
    (x1_zero hm1 rfl) (x2_eq hm1 (c := 344) rfl (by decide)) (by decide)
    (cSlots_off r x (by decide))
  refine ⟨hpre2, fun m2 hQ ↦ ?_⟩
  obtain ⟨hK2, hS2, hkc, hz⟩ := hpost2 m2 hQ
  exact cont m2 (CK.of_call hK1 hK2 hkc (by decide)) (RegIs.of_saved hS2 rfl h20')
    (hkc 1776 _ (by rw [length_addr]; decide) (Or.inl (by rw [length_addr]; decide)) hadr)
    ⟨_, hz, Keccak.holds_new⟩

/-- **`b45 .. b48`**: `update` with `P`, the address and the ends, `finalize` into 2128; then
`b49`. -/
theorem leaf_b45 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} (hE : E.length = 928) {R : MachineState → Prop} {m : MachineData}
    (hK : r.CK x E m) (h20 : Run.RegIs m .X20 r.m0.regs.X1.toBitVec)
    (hadr : BytesAt m.dmem (r.off 1776) (r.addr 2 0)) (hH : HasherAt r m 2160 [])
    (cont : ∀ m', r.CK x E m' → BytesAt m'.dmem (r.off 2128) (hashBytes (r.pp ++ r.addr 2 0 ++ E)) →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', r.pc NativeRustcArm.Xmss.WotsLeaf.b49Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b45Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  -- `update` with `P`.
  refine blk r hp b45_in_code (List.cons_ne_nil _ _) run_b45 hwf
    (match_frameS hpre hK.1.1 (k := []) trivial) fun st3 hm3 hpc3 ↦ ?_
  have hK3 := CK.of_block hpre hK hm3 hwf (by decide +kernel) (by decide +kernel)
  have hH3 := hH.keepB (kb_of_block hpre hm3 hwf) (by decide) (by decide +kernel)
  have hadr3 := r.bytesAt_kept hpre hm3 hwf (by rw [length_addr]; decide) hadr
    (by rw [length_addr]; decide +kernel)
  refine callAt hpc3 hc.2.2.1 ?_
  obtain ⟨hpre4, hpost4⟩ := updateInput hpre hK3.1 (regIs_ptr hm3 (o := 2160) rfl)
    (regIs_of_reg hm3 rfl h20) (x2_eq hm3 (c := 16) rfl (by decide)) (r.pre_pp hpre) (by decide)
    (cSlots_off r x (by decide)) hH3
  refine ⟨hpre4, fun m4 hQ4 ↦ ?_⟩
  obtain ⟨hK4', -, hkc4, hH4⟩ := hpost4 m4 hQ4
  have hK4 := CK.of_call hK3 hK4' hkc4 (by decide)
  have hadr4 := hkc4 1776 _ (by rw [length_addr]; decide) (Or.inl (by rw [length_addr]; decide))
    hadr3
  -- `update` with the address.
  have hwf4 := r.frame_wf hpre hK4.1.1 (fun _ ↦ 0)
  refine blk r hp b46_in_code (List.cons_ne_nil _ _) run_b46 hwf4
    (match_frameS hpre hK4.1.1 (k := []) trivial) fun st5 hm5 hpc5 ↦ ?_
  have hK5 := CK.of_block hpre hK4 hm5 hwf4 (by decide +kernel) (by decide +kernel)
  have hH5 := hH4.keepB (kb_of_block hpre hm5 hwf4) (by decide) (by decide +kernel)
  have hadr5 := r.bytesAt_kept hpre hm5 hwf4 (by rw [length_addr]; decide) hadr4
    (by rw [length_addr]; decide +kernel)
  refine callAt hpc5 hc.2.2.1 ?_
  obtain ⟨hpre6, hpost6⟩ := updateFrame hpre hK5.1 (regIs_ptr hm5 (o := 2160) rfl)
    (regIs_ptr hm5 (o := 1776) rfl) (x2_eq hm5 (c := 16) rfl (by decide)) (by decide) (by decide)
    (by decide) (cSlots_off r x (by decide)) hH5 (length_addr r 2 0) hadr5
  refine ⟨hpre6, fun m6 hQ6 ↦ ?_⟩
  obtain ⟨hK6', -, hkc6, hH6⟩ := hpost6 m6 hQ6
  have hK6 := CK.of_call hK5 hK6' hkc6 (by decide)
  -- `update` with the ends.
  have hwf6 := r.frame_wf hpre hK6.1.1 (fun _ ↦ 0)
  refine blk r hp b47_in_code (List.cons_ne_nil _ _) run_b47 hwf6
    (match_frameS hpre hK6.1.1 (k := []) trivial) fun st7 hm7 hpc7 ↦ ?_
  have hK7 := CK.of_block hpre hK6 hm7 hwf6 (by decide +kernel) (by decide +kernel)
  have hH7 := hH6.keepB (kb_of_block hpre hm7 hwf6) (by decide) (by decide +kernel)
  refine callAt hpc7 hc.2.2.1 ?_
  obtain ⟨hpre8, hpost8⟩ := updateFrame hpre hK7.1 (regIs_ptr hm7 (o := 2160) rfl)
    (regIs_ptr hm7 (o := 440) rfl) (x2_eq hm7 (c := 928) rfl (by decide)) (by decide)
    (by decide) (by decide) (cSlots_off r x (by decide)) hH7 hE hK7.2.1
  refine ⟨hpre8, fun m8 hQ8 ↦ ?_⟩
  obtain ⟨hK8', -, hkc8, hH8⟩ := hpost8 m8 hQ8
  have hK8 := CK.of_call hK7 hK8' hkc8 (by decide)
  -- `finalize` into 2128.
  have hwf8 := r.frame_wf hpre hK8.1.1 (fun _ ↦ 0)
  refine blk r hp b48_in_code (List.cons_ne_nil _ _) run_b48 hwf8
    (match_frameS hpre hK8.1.1 (k := []) trivial) fun st9 hm9 hpc9 ↦ ?_
  have hK9 := CK.of_block hpre hK8 hm9 hwf8 (by decide +kernel) (by decide +kernel)
  have hH9 := hH8.keepB (kb_of_block hpre hm9 hwf8) (by decide) (by decide +kernel)
  refine callAt hpc9 hc.2.2.2.1 ?_
  obtain ⟨hpre10, hpost10⟩ := finalizeFrame hpre hK9.1 (regIs_ptr hm9 (o := 2128) rfl)
    (regIs_ptr hm9 (o := 2160) rfl) (by decide) (by decide) (by decide)
    (cSlots_off r x (by decide)) hH9
  refine ⟨hpre10, fun m10 hQ10 ↦ ?_⟩
  obtain ⟨hK10', -, hkc10, hD⟩ := hpost10 m10 hQ10
  refine cont m10 (CK.of_call hK9 hK10' hkc10 (by decide)) ?_
  rw [List.nil_append] at hD
  exact hD

end

end NativeRustcArm.WotsLeafProof
