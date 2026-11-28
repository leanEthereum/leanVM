module

public import NativeRustcX64.WotsLeaf.Codeword.Loop
public import NativeRustcX64.WotsLeaf.Finish

/-!
# Region 2: the codeword

From `b6` (directive 47, `Run.AtCheck`): if the digest's top 12 bits are set (`b6`) or it is not
a codeword (`b7`), the tag `0` at `out` and the return (`fail_path`); else `hi` at `8` (`b8`), the
58 digits at `614` (the loop `b9`), `hi >> 16` at `48` (`b10`), and the jump to the chains' loop
`b15` (directive 177) with `Run.AtChains0` (`codeword_region`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Codeword
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- `hi >> 16`, the 32-bit shift `b10` stores at `48`. -/
def Run.hi16 (r : Run) : BitVec 64 := BinOp.apply .shr .W32 r.layerW (BitVec.ofNat 64 16)

/-- The slots of the chains: `hi`, `hi >> 16`, `e`, `out`, `P`'s address, the digits. -/
def Run.chainSlots (r : Run) : List Slot :=
  [(8, 8, regBytes r.layerW), (48, 4, (List.range 4).map (byteOf r.hi16)), (52, 4, u32Bytes r.e),
    (96, 8, regBytes r.out), (104, 8, regBytes (reg r.m0 .rsi)), (614, 58, r.digitsPre 58)]

/-- **At the chains' loop, chain 0**: what the frame keeps, RDX `0`, R12 the frame's byte `112`. -/
def Run.AtChains0 [Labels] (r : Run) (m : MachineData) : Prop :=
  Keep r r.chainSlots m ∧ Run.RegIs m .rdx (BitVec.ofNat 64 0) ∧ Run.RegIs m .r12 (r.off 112) ∧
    Run.RegIs m .r13 (Labels.label "memcpy").toBitVec ∧
    Run.RegIs m .rbx (Labels.label "memset").toBitVec

end

public section

section
variable {r : Run} [Labels]

/-- The digest's low word, loaded. -/
theorem load_lo {m : MachineData} (h : BytesAt m.dmem (r.off 112) r.digest32)
    (extra : List (BitVec 64 × Nat)) (ret : BitVec 64) :
    (r.envR m extra ret).load 0 112 8 = r.lo := by
  have := BytesAt.slice h 0 8
  rw [List.drop_zero, Run.off, addr_add_add] at this
  exact Env.load_of_bytesAt (by simp [length_digest32]) this

/-- The digest's high word, loaded. -/
theorem load_hiW {m : MachineData} (h : BytesAt m.dmem (r.off 112) r.digest32)
    (extra : List (BitVec 64 × Nat)) (ret : BitVec 64) :
    (r.envR m extra ret).load 0 120 8 = r.hiW := by
  have := BytesAt.slice h 8 8
  rw [Run.off, addr_add_add] at this
  exact Env.load_of_bytesAt (by simp [length_digest32]) this

end

/-- The result when the digest is not a codeword. -/
theorem result_none (r : Run) (h : isCodeword r.dNum = false) : r.result = none := by
  simp [Run.result, wotsLeaf, messageDigest_eq, codeword, leNat_digest16, h]

variable [Host]

/-- **Region 2, the codeword.** -/
theorem codeword_region : RegionSpec (fun r m ↦ r.AtCheck m) NativeRustcX64.Xmss.WotsLeaf.b6Offset fun r st ↦ r.Done st ∨
    (st.pc = r.pc NativeRustcX64.Xmss.WotsLeaf.b15Offset ∧ r.AtChains0 st.data ∧ isCodeword r.dNum = true) := by
  intro r hp hc hpre m hA
  -- `b6`: the top bits.
  refine frameStep r hp hpre b6_in_code (List.cons_ne_nil _ _) run_b6 (by decide) rfl hA trivial
    extraOK_nil trivial trivial trivial fun st6 hm6 hK6 _ hpc6 ↦ ?_
  have hD6 : BytesAt st6.data.dmem (r.off 112) r.digest32 := hK6.2.2.2.2.2.1.2.2
  have h96 : BytesAt st6.data.dmem (r.off 96) (regBytes r.out) := hK6.2.2.2.1.2.2
  have hc6 := pc_cond hpc6 (b6_cond run_b6 (load_hiW hA.2.2.2.2.2.1.2.2 _ _))
  by_cases h52 : r.hiW.toNat < 2 ^ 52
  swap
  · rw [decide_eq_false h52] at hc6
    simp only [Bool.not_false, ite_true] at hc6
    rw [Run.label_of_block r hp b11_in_code rfl] at hc6
    refine pc_at hc6 (Eventually.mono (fail_path r hp hpre st6.data hK6 h96 (result_none r ?_))
      fun _ h ↦ .inl h)
    rw [Run.dNum]
    exact Swar.isCodeword_top _ _ h52
  rw [decide_eq_true h52] at hc6
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hc6
  refine pc_at hc6 ?_
  -- `b7`: the bit counts.
  refine frameStep r hp hpre b7_in_code (List.cons_ne_nil _ _) run_b7 (by decide) rfl hK6 trivial
    extraOK_nil ⟨(hm6.regs .rdx _ rfl).trans ((load_hiW hA.2.2.2.2.2.1.2.2 _ _).trans
      (load_hiW hD6 _ _).symm), trivial⟩ trivial trivial fun st7 hm7 hK7 _ hpc7 ↦ ?_
  have hD7 : BytesAt st7.data.dmem (r.off 112) r.digest32 := hK7.2.2.2.2.2.1.2.2
  have hc7 := pc_cond hpc7 (b7_cond run_b7 (load_lo hD6 _ _) (load_hiW hD6 _ _) h52)
  rw [← Run.dNum] at hc7
  cases hcw : isCodeword r.dNum
  · rw [hcw] at hc7
    simp only [Bool.not_false, ite_true] at hc7
    rw [Run.label_of_block r hp b11_in_code rfl] at hc7
    exact pc_at hc7 (Eventually.mono (fail_path r hp hpre st7.data hK7 hK7.2.2.2.1.2.2
      (result_none r hcw)) fun _ h ↦ .inl h)
  rw [hcw] at hc7
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hc7
  refine pc_at hc7 ?_
  -- `b8`: `hi` at 8.
  have hK7' : Keep r [(52, 4, u32Bytes r.e), (96, 8, regBytes r.out),
      (104, 8, regBytes (reg r.m0 .rsi)), (112, 32, r.digest32)] st7.data := ⟨hK7.1, hK7.2.2⟩
  refine frameStep r hp hpre b8_in_code (List.cons_ne_nil _ _) run_b8 (by decide) rfl hK7'
    trivial extraOK_nil trivial trivial trivial fun st8 hm8 hK8 _ hpc8 ↦ pc_at hpc8 ?_
  have h8 : BytesAt st8.data.dmem (r.off 8) (regBytes r.layerW) := by
    have := frame_covers hm8 (o := 8) (n := 8) (by decide)
      (v := .bin .shl .W32 (.load 0 8 8) (.lit 23)) (by decide)
    rwa [show (Sym.bin .shl .W32 (.load 0 8 8) (.lit 23)).eval
        (r.envR st7.data [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b8Offset + b8.length)).toBitVec) = r.layerW by
      show BinOp.apply .shl .W32 ((r.envR st7.data [] _).load 0 8 8) (BitVec.ofNat 64 23) = _
      rw [r.load_word hK7.2.1.2.2]
      rfl] at this
  have hA8 : r.AtDigits 0 st8.data := by
    refine ⟨⟨hK8.1, ⟨length_regBytes _, by norm_num, h8⟩, hK8.2⟩, fun i hi ↦ ?_, ?_, ?_,
      regIs_lit hm8 rfl, regIs_ptr hm8 rfl⟩
    · simp [Run.digitsPre] at hi
    · refine regIs_reg hm8 rfl ?_
      unfold Run.RegIs reg
      rw [hm7.regs .rsi _ rfl]
      exact load_lo hD6 _ _
    · refine regIs_reg hm8 rfl ?_
      unfold Run.RegIs reg
      rw [hm7.regs .rdx _ rfl]
      exact load_hiW hD6 _ _
  refine Eventually.bind (digits_loop r hp hpre 29 0 rfl (by decide) st8.data hA8)
    fun st ⟨hpc9, hA9⟩ ↦ pc_at hpc9 ?_
  -- `b10`: `hi >> 16` at 48, the jump to the chains.
  obtain ⟨hK9, hD9, -⟩ := hA9
  refine frameStep r hp hpre b10_in_code (List.cons_ne_nil _ _) run_b10 (by decide) rfl hK9
    trivial extraOK_nil trivial trivial trivial fun st10 hm10 hK10 hkb10 hpc10 ↦ ?_
  have h48 : BytesAt st10.data.dmem (r.off 48) ((List.range 4).map (byteOf r.hi16)) := by
    have := frame_covers hm10 (o := 48) (n := 4) (by decide)
      (v := .bin .shr .W32 (.load 0 8 8) (.lit 16)) (by decide)
    rwa [show (Sym.bin .shr .W32 (.load 0 8 8) (.lit 16)).eval
        (r.envR st.data [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b10Offset + b10.length)).toBitVec) = r.hi16 by
      show BinOp.apply .shr .W32 ((r.envR st.data [] _).load 0 8 8) (BitVec.ofNat 64 16) = _
      rw [r.load_word hK9.2.1.2.2]
      rfl] at this
  have hD10 := hkb10 614 _ (by rw [length_digitsPre]; omega)
    (by rw [length_digitsPre]; decide) hD9
  refine .done _ (.inr ⟨?_, ⟨⟨hK10.1, hK10.2.1, ⟨by simp, by norm_num, h48⟩, hK10.2.2.1, hK10.2.2.2.1,
    hK10.2.2.2.2.1, ⟨length_digitsPre _ _, by norm_num, hD10⟩, trivial⟩, regIs_lit hm10 rfl,
    regIs_ptr hm10 rfl, hm10.regs .r13 _ rfl, hm10.regs .rbx _ rfl⟩, hcw⟩)
  rw [show st10.pc = _ from hpc10]
  exact Run.label_of_block r hp b15_in_code rfl

end

end NativeRustcX64.WotsLeafProof
