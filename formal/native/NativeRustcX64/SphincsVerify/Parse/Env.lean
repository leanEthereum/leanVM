module

public import NativeRustcX64.SphincsVerify.Parse.Glue
public import NativeRustcX64.SphincsVerify.Parse.State

/-!
# The parse's environments (x86-64)

Region 0 is the frame, region 1 the 16 bytes below it, region 2 the input, and regions 3 and 4
the memcpy and memset GOT slots (`regs3`), preserving the input's index. The input words
(`input_words`), a loaded word
(`load_word`). After a block of an environment whose regions 0 and 1 are the frame's, with writes
there (`frameWrites`) or below the return address (`entryWrites`): the stack area
(`written_stack`), the frame's invariant (`frame_of_block`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The frame's regions and the input. -/
abbrev regs3 (r : Run) [Labels] : List (BitVec 64 × Nat) :=
  [(r.base, frameRegion), (r.base - 16#64, 16), (r.input, 7816),
    (gotAddr "memcpy", 8), (gotAddr "memset", 8)]

/-- The writes are in region 0 below the return address, or in region 1. -/
def entryWrites (S : SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 29384)) || (w.r == 1 && decide (w.off + w.n ≤ 16))

end

public section

theorem slice_words (w : Nat → UInt64) {s n : Nat} (h : s + n ≤ 977) :
    slice (Native.Keccak.wordsBytes ((List.range 977).map w)) (8 * s) (8 * n) = wb w s n := by
  rw [slice, slice_wordsBytes, wb]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp

theorem bytesAt_sub {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) {k n : Nat}
    (hk : k + n ≤ bs.length) : BytesAt d (a + BitVec.ofNat 64 k) (slice bs k n) := by
  intro i hi
  have hl : (slice bs k n).length = n := by simp [slice]; omega
  rw [addr_add, h (k + i) (by omega)]
  simp [slice]

variable (r : Run) [Labels]

theorem input_toNat (hpre : r.Pre) : r.input.toNat + 8 * 977 ≤ 2 ^ 64 := hpre.2.2.2.2.2.2.1

/-- **The input words `s .. s + n`** in a state changed only in the stack area. -/
theorem input_words (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea)
    {s n : Nat} (h : s + n ≤ 977) : BytesAt d (r.input + BitVec.ofNat 64 (8 * s)) (wb r.w s n) := by
  have hlen : (Native.Keccak.wordsBytes ((List.range 977).map r.w)).length = 8 * 977 := by
    rw [Native.Keccak.Proof.length_wordsBytes, List.length_map, List.length_range]
  have hin := r.bytesAt_entry hpre hS hpre.2.2.2.2.2.1 (hlen ▸ hpre.2.2.2.2.2.2.2.1)
    (hlen ▸ hpre.2.2.2.2.2.2.1)
  rw [← slice_words r.w h]
  exact bytesAt_sub hin (by rw [hlen]; omega)

/-- The input word `k` at the input's byte `o = 8 k`. -/
theorem input_word (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea)
    {k o : Nat} (ho : o = 8 * k) (h : k < 977) :
    BytesAt d (r.input + BitVec.ofNat 64 o) (wordBytes (r.w k)) := by
  have := input_words r hpre hS (s := k) (n := 1) (by omega)
  rwa [show wb r.w k 1 = wordBytes (r.w k) by simp [wb, Native.Keccak.wordsBytes], ← ho] at this

/-- **The frame's regions and the input are a well-formed environment**. -/
theorem wf3 (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (Env.ofMachine m (regs3 r) vars ret).WF := by
  have hw := r.frame_wf hpre hk vars ret
  have hb := r.base_toNat hpre
  have hbl := r.below_toNat hpre
  have hi := input_toNat r hpre
  have hA := hpre.2.2.2.2.2.2.2.1
  have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  have hmap := (input_words r hpre hS (s := 0) (n := 977) (by decide)).mapped
  rw [length_wb] at hmap
  simp only [Nat.mul_zero, BitVec.add_zero] at hmap
  have h0 : Mapped m.dmem r.base frameRegion ∧ NoWrap r.base frameRegion :=
    ⟨hw.mapped 0 r.base frameRegion rfl, hw.noWrap 0 r.base frameRegion rfl⟩
  have h1 : Mapped m.dmem (r.base - 16#64) 16 ∧ NoWrap (r.base - 16#64) 16 :=
    ⟨hw.mapped 1 (r.base - 16#64) 16 rfl, hw.noWrap 1 (r.base - 16#64) 16 rfl⟩
  have h3 : Mapped m.dmem (gotAddr "memcpy") 8 ∧ NoWrap (gotAddr "memcpy") 8 :=
    ⟨hw.mapped 2 (gotAddr "memcpy") 8 rfl, hw.noWrap 2 (gotAddr "memcpy") 8 rfl⟩
  have h4 : Mapped m.dmem (gotAddr "memset") 8 ∧ NoWrap (gotAddr "memset") 8 :=
    ⟨hw.mapped 3 (gotAddr "memset") 8 rfl, hw.noWrap 3 (gotAddr "memset") 8 rfl⟩
  refine Sym.Env.wf_of ⟨h0, h1,
    ⟨fun i hi ↦ hmap i (by omega), by unfold NoWrap; omega⟩, h3, h4, trivial⟩ ?_
  simp only [Apart, Run.sphincsStack_eq] at hA hbl
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ ?_))
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hw.disjoint 0 1 _ _ _ _ (by decide) rfl rfl
    · show Apart r.base frameRegion r.input 7816
      unfold Apart
      rw [Run.frameRegion_eq]
      omega
    · exact (r.got_apart_frame hpre (by simp)).symm
    · exact (r.got_apart_frame hpre (by simp)).symm
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · show Apart (r.base - 16#64) 16 r.input 7816
      unfold Apart
      omega
    · exact (r.got_apart_below hpre (by simp)).symm
    · exact (r.got_apart_below hpre (by simp)).symm
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (((r.got hpre).1 "memcpy" (by simp)).2.2.2 (r.input, 8 * 977) (by simp)).symm
    · exact (((r.got hpre).1 "memset" (by simp)).2.2.2 (r.input, 8 * 977) (by simp)).symm
  · simpa using (r.got hpre).2

/-- **The input's bytes `8 s .. 8 s + k` and the frame's `a .. a + n`** are a well-formed
environment. -/
theorem wf_in_frame (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) {s k a n : Nat} (hs : 8 * s + k ≤ 8 * 977)
    (hk0 : 0 < k) (ha : a + n ≤ 29384) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (Env.ofMachine m [(r.input + BitVec.ofNat 64 (8 * s), k), (r.off a, n)] vars ret).WF := by
  have hi := input_toNat r hpre
  have hbl := r.below_toNat hpre
  have hb := r.base_toNat hpre
  have ho := r.off_toNat hpre (a := a) (by omega)
  have hA := hpre.2.2.2.2.2.2.2.1
  have hmap := (input_words r hpre hS (s := 0) (n := 977) (by decide)).mapped
  rw [length_wb] at hmap
  simp only [Nat.mul_zero, BitVec.add_zero] at hmap
  have hs' : (r.input + BitVec.ofNat 64 (8 * s)).toNat = r.input.toNat + 8 * s :=
    Sym.toNat_add_ofNat _ _ (by omega)
  refine Sym.Env.wf_of ⟨⟨fun i hi ↦ ?_, by show NoWrap _ k; unfold NoWrap; rw [hs']; omega⟩,
    r.frame_mapped hpre hk ha, trivial⟩ (List.pairwise_pair.mpr ?_)
  · rw [addr_add]
    exact hmap _ (by omega)
  · show Apart _ k _ n
    simp only [Apart, Run.sphincsStack_eq] at hA hbl ⊢
    rw [hs', ho]
    omega

omit [Labels] in
/-- **A loaded word**. -/
theorem load_word {env : Env} {r' o : Nat} {x : UInt64}
    (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o) (wordBytes x)) :
    env.load r' o 8 = x.toBitVec := by
  rw [Env.load_of_bytesAt (length_wordBytes x) h]
  have := ofBytes_regBytes x.toBitVec
  rwa [regBytes_eq_wordBytes] at this

omit [Labels] in
theorem base1 : r.base - 16#64 + BitVec.ofInt 64 8 = r.base + BitVec.ofInt 64 (-8) :=
  (r.alias8).symm

/-- **The places a block's writes cover**, in an environment whose regions 0 and 1 are the
frame's: in the stack area, and off the saved registers where `frameWrites`. -/
theorem written_stack (hpre : r.Pre) {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (h0 : regions[0]? = some (r.base, 29392))
    (h1 : regions[1]? = some (r.base - 16#64, 16)) {S : SState} (hw : entryWrites S = true) :
    ∀ p, Sym.Written (Env.ofMachine m regions vars ret) S p → r.StackArea p := by
  have hb := r.base_toNat hpre
  rintro p ⟨w, hwm, b, sz, hr, h1', h2⟩
  simp only [entryWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  rw [r.stackArea_iff hpre]
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hwn⟩
  · rw [hw0] at hr
    simp only [Env.ofMachine_regions, h0, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    omega
  · rw [hw1] at hr
    simp only [Env.ofMachine_regions, h1, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    omega

theorem written_frame (hpre : r.Pre) {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (h0 : regions[0]? = some (r.base, 29392))
    (h1 : regions[1]? = some (r.base - 16#64, 16)) {S : SState} (hw : Run.frameWrites S = true) :
    ∀ p, Sym.Written (Env.ofMachine m regions vars ret) S p →
      r.StackArea p ∧ ¬InRange (r.off 29336) 48 p := by
  have hb := r.base_toNat hpre
  rintro p ⟨w, hwm, b, sz, hr, h1', h2⟩
  simp only [Run.frameWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  have hs := r.off_toNat hpre (a := 29336) (by decide)
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hwn⟩
  · rw [hw0] at hr
    simp only [Env.ofMachine_regions, h0, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    omega
  · rw [hw1] at hr
    simp only [Env.ofMachine_regions, h1, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    omega

/-- **The frame's invariant after a block** of an environment whose regions 0 and 1 are the
frame's, its writes there off the saved registers, RSP the base. -/
theorem frame_of_block (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (h0 : regions[0]? = some (r.base, 29392)) (h1 : regions[1]? = some (r.base - 16#64, 16))
    {S : SState} (hm : Match (Env.ofMachine m regions vars ret) S m')
    (hwf : (Env.ofMachine m regions vars ret).WF) (hsp : S.reg .rsp = some (.ptr 0 0))
    (hw : Run.frameWrites S = true) : r.Frame m' :=
  Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2
    (by rw [rspOf, hm.regs .rsp _ hsp]; simp [Sym.eval, Env.base, h0])
    (hm.sameOutside hwf) (written_frame r hpre h0 h1 hw) (hm.kept hwf)

end

end NativeRustcX64.SphincsVerifyProof.Parse
