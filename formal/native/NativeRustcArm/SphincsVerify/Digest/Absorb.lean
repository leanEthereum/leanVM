module

public import NativeRustcArm.SphincsVerify.Digest.Call

/-!
# `h_msg`'s hasher: `b45 .. b49`

`b45` (directive 536) clears the hasher at `26768` (`memset`, `Hasher::new`), `b46 .. b49`
update it with `R` (the parsed signature's randomizer, `12884`), `PK.seed` (`8208`), `PK.root`
(`8224`) and the message (`432`): at `b50` (directive 562) it has absorbed `hInput r`
(`absorb_spec`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- What `h_msg`'s hasher absorbs before the counter: `R | PK.seed | PK.root | M`. -/
def hInput (r : Run) : List UInt8 := r.sig.randomizer ++ r.seed ++ r.pk.root ++ r.msg

/-- **At `b50`**: what the digest keeps, X21 `h_msg`'s place, the hasher at `26768` having
absorbed `hInput r`. -/
def Absorbed (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X21 (r.off 24720) ∧ HasherAt r m 26768 (hInput r)

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

theorem length_msg (r : Run) : r.msg.length = 16 + 16 := by
  simp [Run.msg, messageBytes, Native.Keccak.Proof.length_wordsBytes]

/-- `R` in the frame. -/
theorem Keep.rand {r : Run} {m : MachineData} (hK : Keep r m) :
    BytesAt m.dmem (r.off 12884) r.sig.randomizer := by
  have := bytesAt_drop_take hK.2.1.2.1 4640 16 (by rw [r.length_sigMem]; omega)
  rwa [Run.off_add, r.sigMem_randomizer] at this

/-- `PK.seed` in the frame. -/
theorem Keep.seed {r : Run} {m : MachineData} (hK : Keep r m) : BytesAt m.dmem (r.off 8208) r.seed := by
  have := bytesAt_drop_take hK.2.1.1 0 16 (by rw [length_pkBytes]; omega)
  rwa [Run.off_add, List.drop_zero] at this

theorem length_seed (r : Run) : r.seed.length = 16 := by
  simp [Run.seed, Run.pk, PublicKey.fromBytes, length_pkBytes]

theorem length_root (r : Run) : r.pk.root.length = 16 := by
  simp [Run.pk, PublicKey.fromBytes, length_pkBytes]

/-- `PK.root` in the frame. -/
theorem Keep.root {r : Run} {m : MachineData} (hK : Keep r m) :
    BytesAt m.dmem (r.off 8224) r.pk.root := by
  have := bytesAt_drop_take hK.2.1.1 16 16 (by rw [length_pkBytes])
  rwa [Run.off_add, List.take_of_length_le (by rw [List.length_drop, length_pkBytes])] at this

variable [NativeRustcArm.Host]

/-- **`h_msg`'s hasher absorbs `R | PK.seed | PK.root | M`.** -/
theorem absorb_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : r.AtHMsg m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b50Offset ∧ Absorbed r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b45Offset⟩ := by
  obtain ⟨hF, hI, h19, h23, h24, h21, hmsg, h392⟩ := hA
  have hK : Keep r m := ⟨hF, hI, h392⟩
  have hm32 := length_msg r
  -- b45: memset of the hasher
  refine Run.memsetCall r hp hpre hc Sphincs.SphincsVerify.b45_in_code rfl run_b45 rfl (a := 26768) (n := 344) hK
    (knownOK_nil m) rfl rfl rfl ⟨by decide, by decide⟩ fun m₁ hm₁ hK₁ hkb₁ m₂ hK₂ hS₂ hkc₂ hB₂ ↦ ?_
  have g19 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h19)
  have g23 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h23)
  have g24 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h24)
  have g21 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h21)
  have gmsg := hkc₂ 432 _ (by omega) (by omega) (hkb₁ 432 _ (by omega) rfl hmsg)
  have gH : HasherAt r m₂ 26768 [] := ⟨_, hB₂, Keccak.holds_new⟩
  -- b46: `R`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b46_in_code rfl run_b46 rfl (a := 26768) (b := 12884) (n := 16) hK₂
    (knownOK_ptr g23 (knownOK_lit g24 (knownOK_nil m₂))) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) (r.length_randomizer) fun m₃ hm₃ hK₃ hkb₃ ↦
      ⟨gH.keepB hkb₃ (by decide) rfl, hK₃.rand, fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g19 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g19)
  have g21 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g21)
  have gmsg := hkc₄ 432 _ (by omega) (by omega) (hkb₃ 432 _ (by omega) rfl gmsg)
  -- b47: `PK.seed`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b47_in_code rfl run_b47 rfl (a := 26768) (b := 8208) (n := 16) hK₄
    (knownOK_nil m₄) rfl rfl rfl ⟨by decide, by decide⟩ (by decide) (by decide)
    (length_seed r) fun m₅ hm₅ hK₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, hK₅.seed, fun m₆ hK₆ hS₆ hkc₆ hH₆ ↦ ?_⟩
  have g19 := regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g19)
  have g21 := regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g21)
  have gmsg := hkc₆ 432 _ (by omega) (by omega) (hkb₅ 432 _ (by omega) rfl gmsg)
  -- b48: `PK.root`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b48_in_code rfl run_b48 rfl (a := 26768) (b := 8224) (n := 16) hK₆
    (knownOK_ptr g19 (knownOK_nil m₆)) rfl rfl rfl ⟨by decide, by decide⟩ (by decide)
    (by decide) (length_root r) fun m₇ hm₇ hK₇ hkb₇ ↦
      ⟨hH₆.keepB hkb₇ (by decide) rfl, hK₇.root, fun m₈ hK₈ hS₈ hkc₈ hH₈ ↦ ?_⟩
  have g21 := regIs_of_saved hS₈ rfl (regIs_keep hm₇ rfl g21)
  have gmsg := hkc₈ 432 _ (by omega) (by omega) (hkb₇ 432 _ (by omega) rfl gmsg)
  -- b49: the message
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b49_in_code rfl run_b49 rfl (a := 26768) (b := 432) (n := 32) hK₈
    (knownOK_nil m₈) rfl rfl rfl ⟨by decide, by decide⟩ (by decide) (by decide)
    (by rw [hm32]) fun m₉ hm₉ hK₉ hkb₉ ↦
      ⟨hH₈.keepB hkb₉ (by decide) rfl, hkb₉ 432 _ (by omega) rfl gmsg,
        fun m₁₀ hK₁₀ hS₁₀ _ hH₁₀ ↦ .done _ ⟨rfl, hK₁₀, ?_, ?_⟩⟩
  · exact regIs_of_saved hS₁₀ rfl (regIs_keep hm₉ rfl g21)
  · simpa [hInput, List.append_assoc] using hH₁₀

end

end NativeRustcArm.SphincsVerifyProof.Digest
