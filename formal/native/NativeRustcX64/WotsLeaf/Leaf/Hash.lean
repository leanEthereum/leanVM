module

public import NativeRustcX64.WotsLeaf.Chain.Outer
public import NativeRustcX64.WotsLeaf.Leaf.Exec

/-!
# The leaf's hash

From `b51` (directive 525) with the 58 ends at `1080`: the leaf's address (type 2) at `112`, the
leaf's hasher at `2352` zeroed (`b51`), updated with `P` (`b52`), the address (`b53`) and the
ends (`b54`), finalized into `1048` (`b55`); then `b56` (directive 554) (`leaf_hash`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Leaf
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The leaf's hash input: `P`, the leaf's address, the ends. -/
def Run.leafIn (r : Run) : List UInt8 := r.pp ++ r.addr 2 0 ++ r.endsPre 58

end

public section

variable [Host] {r : Run}

/-- **The leaf's hash**: from `b51`, its 32 bytes at `1048` at `b56`. -/
theorem leaf_hash (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r (r.outerSlots 58) m)
    (cont : ∀ m', Keep r (r.outerSlots 58 ++ [(1048, 32, Keccak.hashBytes r.leafIn)]) m' →
      Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Xmss.WotsLeaf.b56Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b51Offset⟩ := by
  replace hK : Keep r (r.chainSlots ++ [(1080, 928, r.endsPre 58)]) m := hK
  obtain ⟨s8, s48, s52, -, s104, -, -⟩ : SlotsAt r m r.chainSlots := allOf_left hK.2
  obtain ⟨⟨hEl, -, -⟩, -⟩ := allOf_right hK.2
  -- `b51`: the address, `memset` of the hasher.
  refine frameCall r hp hpre b51_in_code (List.cons_ne_nil _ _) run_b51 (by decide) rfl hK
    trivial extraOK_nil trivial trivial trivial hc.2.1 fun m₁ hm₁ hK₁ _ ↦ ?_
  have a1 := covers_load hm₁ (o := 112) (n := 4) (o' := 52) (by decide) (by decide)
    (by decide +kernel) (length_u32Bytes' r.e) s52.2.2
  have a2 : BytesAt m₁.dmem (r.off 116) ((u32Bytes r.hi).take 2) := by
    have := frame_covers hm₁ (o := 116) (n := 2) (v := .un .trunc .W16 (.load 0 8 8)) (by decide)
      (by decide +kernel)
    rw [show (Sym.un .trunc .W16 (.load 0 8 8)).eval
        (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b51Offset + b51.length)).toBitVec) = UnOp.apply .trunc .W16 r.layerW by
      show UnOp.apply .trunc .W16 ((r.envR m [] _).load 0 8 8) = _
      rw [r.load_word s8.2.2], bytes_layerW16] at this
    exact this
  have a3 : BytesAt m₁.dmem (r.off 118) (((u32Bytes r.hi).drop 2).take 1) := by
    have := frame_covers hm₁ (o := 118) (n := 1) (v := .un .trunc .W8 (.load 0 48 4)) (by decide)
      (by decide +kernel)
    rw [show (Sym.un .trunc .W8 (.load 0 48 4)).eval
        (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b51Offset + b51.length)).toBitVec) = UnOp.apply .trunc .W8 r.hi16 by
      show UnOp.apply .trunc .W8 ((r.envR m [] _).load 0 48 4) = _
      rw [load_word4 (hi16_lt r) s48.2.2], byte_hi16] at this
    exact this
  have a4 : BytesAt m₁.dmem (r.off 119) [(2 : UInt8) ||| (0 : Nat).toUInt8 <<< 5] := by
    have := frame_covers hm₁ (o := 119) (n := 1) (v := .lit 2) (by decide) (by decide +kernel)
    rw [show (Sym.lit 2).eval (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b51Offset + b51.length)).toBitVec) =
      BitVec.ofNat 64 2 from rfl, bytes_byte] at this
    rw [show ((2 : UInt8) ||| (0 : Nat).toUInt8 <<< 5) = UInt8.ofNat 2 by decide]
    exact this
  have a5 : BytesAt m₁.dmem (r.off 120) (List.replicate 8 0) := by
    have := frame_covers hm₁ (o := 120) (n := 8) (v := .lit 0) (by decide) (by decide +kernel)
    rwa [show (Sym.lit 0).eval (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b51Offset + b51.length)).toBitVec) =
      BitVec.ofNat 64 0 from rfl, bytes_zero] at this
  have had : BytesAt m₁.dmem (r.off 112) (r.addr 2 0) := by
    rw [Run.addr_eq]
    refine BytesAt.cat a1 (BytesAt.cat a2 (BytesAt.cat a3 (BytesAt.cat a4 a5 rfl) ?_) ?_) ?_
    · simp [u32Bytes, Native.XmssVerifier.bytes]
    · simp [u32Bytes, Native.XmssVerifier.bytes]
    · rw [length_u32Bytes']
  have hbx₁ : Run.RegIs m₁ .rbx (r.off 2352) := regIs_ptr hm₁ rfl
  obtain ⟨hpre₁, hpost₁⟩ := memsetFrame hpre
    (hK₁.add (L' := [(112, 16, r.addr 2 0)]) ⟨⟨length_addr r 2 0, by norm_num, had⟩, trivial⟩)
    (regIs_ptr hm₁ rfl) (byte_zero hm₁ rfl) (toNat_of_lit hm₁ rfl (by decide)) (by decide)
    (by simp [slotsOff, Run.chainSlots])
  refine ⟨hpre₁, fun m₂ hsp₂ hQ₂ ↦ ?_⟩
  obtain ⟨hK₂, hS₂, -, hZ⟩ := hpost₁ m₂ hsp₂ hQ₂
  have hH₂ : HasherAt r m₂ 2352 [] := ⟨_, hZ, Keccak.holds_new⟩
  have hbx₂ := RegIs.of_saved hS₂ rfl hbx₁
  -- `b52`: `update` with `P`.
  refine frameCall r hp hpre b52_in_code (List.cons_ne_nil _ _) run_b52 (by decide) rfl hK₂
    trivial extraOK_nil ⟨known_ptr hbx₂, trivial⟩ trivial trivial hc.2.2.1
    fun m₃ hm₃ hK₃ hkb₃ ↦ ?_
  obtain ⟨hpre₃, hpost₃⟩ := updateInput hpre hK₃ (regIs_ptr hm₃ rfl)
    (regIs_eval hm₃ (v := .load 0 104 8) rfl
      (r.load_word (allOf_left (allOf_left hK₂.2)).2.2.2.2.1.2.2))
    (toNat_of_lit hm₃ rfl (by decide)) (r.pre_pp hpre) (by decide)
    (by simp [slotsOff, Run.chainSlots])
    (((r.got hpre).1 "memcpy" (by simp)).2.2.2 (reg r.m0 .rsi, 16) (by simp))
    (hH₂.keepB hkb₃ (by decide) (by decide +kernel))
  refine ⟨hpre₃, fun m₄ hsp₄ hQ₄ ↦ ?_⟩
  obtain ⟨hK₄, hS₄, -, hH₄⟩ := hpost₃ m₄ hsp₄ hQ₄
  have hbx₄ := RegIs.of_saved hS₄ rfl (regIs_ptr hm₃ (y := .rbx) rfl)
  -- `b53`: `update` with the address.
  refine frameCall r hp hpre b53_in_code (List.cons_ne_nil _ _) run_b53 (by decide) rfl hK₄
    trivial extraOK_nil ⟨known_ptr hbx₄, trivial⟩ trivial trivial hc.2.2.1
    fun m₅ hm₅ hK₅ hkb₅ ↦ ?_
  obtain ⟨hpre₅, hpost₅⟩ := updateFrame hpre hK₅ (regIs_ptr hm₅ rfl) (regIs_ptr hm₅ rfl)
    (toNat_of_lit hm₅ rfl (by decide)) (by decide) (by decide) (by decide)
    (by simp [slotsOff, Run.chainSlots])
    (hH₄.keepB hkb₅ (by decide) (by decide +kernel)) (length_addr r 2 0)
    (allOf_right hK₅.2).1.2.2
  refine ⟨hpre₅, fun m₆ hsp₆ hQ₆ ↦ ?_⟩
  obtain ⟨hK₆, hS₆, -, hH₆⟩ := hpost₅ m₆ hsp₆ hQ₆
  have hbx₆ := RegIs.of_saved hS₆ rfl (regIs_ptr hm₅ (y := .rbx) rfl)
  -- `b54`: `update` with the ends.
  refine frameCall r hp hpre b54_in_code (List.cons_ne_nil _ _) run_b54 (by decide) rfl hK₆
    trivial extraOK_nil ⟨known_ptr hbx₆, trivial⟩ trivial trivial hc.2.2.1
    fun m₇ hm₇ hK₇ hkb₇ ↦ ?_
  obtain ⟨hpre₇, hpost₇⟩ := updateFrame hpre hK₇ (regIs_ptr hm₇ rfl) (regIs_ptr hm₇ rfl)
    (toNat_of_lit hm₇ rfl (by decide)) (by decide) (by decide) (by decide)
    (by simp [slotsOff, Run.chainSlots])
    (hH₆.keepB hkb₇ (by decide) (by decide +kernel)) hEl
    (allOf_right (allOf_left hK₇.2)).1.2.2
  refine ⟨hpre₇, fun m₈ hsp₈ hQ₈ ↦ ?_⟩
  obtain ⟨hK₈, hS₈, -, hH₈⟩ := hpost₇ m₈ hsp₈ hQ₈
  have hbx₈ := RegIs.of_saved hS₈ rfl (regIs_ptr hm₇ (y := .rbx) rfl)
  -- `b55`: `finalize` into `1048`.
  refine frameCall r hp hpre b55_in_code (List.cons_ne_nil _ _) run_b55 (by decide) rfl
    hK₈.left trivial extraOK_nil ⟨known_ptr hbx₈, trivial⟩ trivial trivial hc.2.2.2.1
    fun m₉ hm₉ hK₉ hkb₉ ↦ ?_
  obtain ⟨hpre₉, hpost₉⟩ := finalizeFrame hpre hK₉ (regIs_ptr hm₉ rfl) (regIs_ptr hm₉ rfl)
    (by decide) (by decide) (by decide) rfl (hH₈.keepB hkb₉ (by decide) (by decide +kernel))
  refine ⟨hpre₉, fun m₁₀ hsp₁₀ hQ₁₀ ↦ ?_⟩
  obtain ⟨hK₁₀, -, -, hD⟩ := hpost₉ m₁₀ hsp₁₀ hQ₁₀
  rw [List.nil_append] at hD
  exact cont m₁₀ (hK₁₀.add ⟨⟨length_hashBytes _, by norm_num, hD⟩, trivial⟩)

end

end NativeRustcX64.WotsLeafProof
