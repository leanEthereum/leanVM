module

public import NativeRustcArm.SphincsVerify.Digest.Call

/-!
# `h_msg`'s hasher: `b36 .. b40`

`b36` clears the hasher at `19008` (`memset`, `Hasher::new`), `b37 .. b40`
update it with `R` (the parsed signature's randomizer, `5124`), `PK.seed` (`448`), `PK.root`
(`464`) and the message (`r.msgPtr` in X21): at `b41` it has absorbed `hInput r`
(`absorb_spec`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- What `h_msg`'s hasher absorbs before the counter: `R | PK.seed | PK.root | M`. -/
def hInput (r : Run) : List UInt8 := r.sig.randomizer ++ r.seed ++ r.pk.root ++ r.msg

/-- **At `b41`**: what the digest keeps, X19 `h_msg`'s place (`16960`), the hasher at `19008`
having absorbed `hInput r`. -/
def Absorbed (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X19 (r.off 16960) ∧ HasherAt r m 19008 (hInput r)

end

public section

/-- `n` bytes from byte `k` of bytes in memory. -/
theorem bytesAt_drop_take {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (k n : Nat) (hk : k + n ≤ bs.length) :
    BytesAt d (a + BitVec.ofNat 64 k) ((bs.drop k).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [Sym.addr_add, h (k + i) (by omega)]
  simp [List.getElem_take, List.getElem_drop]

/-- `R` in the frame. -/
theorem Keep.rand {r : Run} {m : MachineData} (hK : Keep r m) :
    BytesAt m.dmem (r.off 5124) r.sig.randomizer := by
  have := bytesAt_drop_take hK.2.1.2.1 4640 16 (by rw [r.length_sigMem]; omega)
  rwa [Run.off_add, r.sigMem_randomizer] at this

/-- `PK.seed` in the frame. -/
theorem Keep.seed {r : Run} {m : MachineData} (hK : Keep r m) : BytesAt m.dmem (r.off 448) r.seed := by
  have := bytesAt_drop_take hK.2.1.1 0 16 (by rw [r.hpk]; omega)
  rwa [Run.off_add, List.drop_zero] at this

theorem length_seed (r : Run) : r.seed.length = 16 := by
  simp [Run.seed, Run.pk, PublicKey.fromBytes, r.hpk]

theorem length_root (r : Run) : r.pk.root.length = 16 := by
  simp [Run.pk, PublicKey.fromBytes, r.hpk]

/-- `PK.root` in the frame. -/
theorem Keep.root {r : Run} {m : MachineData} (hK : Keep r m) :
    BytesAt m.dmem (r.off 464) r.pk.root := by
  have := bytesAt_drop_take hK.2.1.1 16 16 (by rw [r.hpk])
  rwa [Run.off_add, List.take_of_length_le (by rw [List.length_drop, r.hpk])] at this

variable [ElfHost]

/-- **`h_msg`'s hasher absorbs `R | PK.seed | PK.root | M`.** -/
theorem absorb_spec (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : r.AtHMsg m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b41Offset ∧ Absorbed r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b36Offset⟩ := by
  obtain ⟨hF, hI, h20, h25, h26, h19, h21, h408⟩ := hA
  have hK : Keep r m := ⟨hF, hI, h408⟩
  -- b36: memset of the hasher
  refine Run.memsetCall r hp hpre hc Sphincs.SphincsVerify.b36_in_code rfl run_b36 rfl (a := 19008) (n := 344) hK
    (knownOK_nil m) rfl rfl rfl ⟨by decide, by decide⟩ fun m₁ hm₁ hK₁ hkb₁ m₂ hK₂ hS₂ hkc₂ hB₂ ↦ ?_
  have g20 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h20)
  have g25 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h25)
  have g26 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h26)
  have g19 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h19)
  have g21 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h21)
  have gH : HasherAt r m₂ 19008 [] := ⟨_, hB₂, Keccak.holds_new⟩
  -- b37: `R`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b37_in_code rfl run_b37 rfl (a := 19008) (b := 5124) (n := 16) hK₂
    (knownOK_ptr g25 (knownOK_lit g26 (knownOK_nil m₂))) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) (r.length_randomizer) fun m₃ hm₃ hK₃ hkb₃ ↦
      ⟨gH.keepB hkb₃ (by decide) rfl, hK₃.rand, fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g20 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g20)
  have g19 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g19)
  have g21 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g21)
  -- b38: `PK.seed`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b38_in_code rfl run_b38 rfl (a := 19008) (b := 448) (n := 16) hK₄
    (knownOK_nil m₄) rfl rfl rfl ⟨by decide, by decide⟩ (by decide) (by decide)
    (length_seed r) fun m₅ hm₅ hK₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, hK₅.seed, fun m₆ hK₆ hS₆ hkc₆ hH₆ ↦ ?_⟩
  have g20 := regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g20)
  have g19 := regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g19)
  have g21 := regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g21)
  -- b39: `PK.root`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b39_in_code rfl run_b39 rfl (a := 19008) (b := 464) (n := 16) hK₆
    (knownOK_ptr g20 (knownOK_nil m₆)) rfl rfl rfl ⟨by decide, by decide⟩ (by decide)
    (by decide) (length_root r) fun m₇ hm₇ hK₇ hkb₇ ↦
      ⟨hH₆.keepB hkb₇ (by decide) rfl, hK₇.root, fun m₈ hK₈ hS₈ hkc₈ hH₈ ↦ ?_⟩
  have g19 := regIs_of_saved hS₈ rfl (regIs_keep hm₇ rfl g19)
  have g21 := regIs_of_saved hS₈ rfl (regIs_keep hm₇ rfl g21)
  -- b40: the message at `r.msgPtr` (X21)
  refine Run.updateCallMsg r hp hpre hc Sphincs.SphincsVerify.b40_in_code rfl run_b40 rfl (a := 19008)
    hK₈ (knownOK_nil m₈) rfl rfl g21 rfl ⟨by decide, by decide⟩ fun m₉ hm₉ hK₉ hkb₉ ↦
      ⟨hH₈.keepB hkb₉ (by decide) rfl,
        fun m₁₀ hK₁₀ hS₁₀ _ hH₁₀ ↦ .done _ ⟨rfl, hK₁₀, ?_, ?_⟩⟩
  · exact regIs_of_saved hS₁₀ rfl (regIs_keep hm₉ rfl g19)
  · simpa [hInput, List.append_assoc] using hH₁₀

end

end NativeRustcArm.SphincsVerifyProof.Digest
