module

public import NativeVm.Model.KeccakGkr

/-!
# The embedding's tables as literals

`rmfeEmbed` and `rmfeProject` (`Statement/Verifier/Keccak.lean`, `rmfe`) are the statement's
literal tables. `rmfeEmbed_eq` and `rmfeProject_eq` identify them with their decimal forms.
The model's words (`rmfeEmbedW`, `rmfeProjectW`) are then the literal word tables the native
code holds (`rmfeEmbedW_eq`, `rmfeProjectW_eq`), and a word's bit is the number's
(`testBitW_toUInt64`): every entry is below `2^64`, so its bits below `64` are the number's.
-/

public section

namespace NativeVm.Equiv

open LeanVM.Parameters LeanVM.Protocol.Verifier NativeVm.Model

/-- `RMFE_EMBED` (`keccak.rs`), in decimal. -/
@[expose] def rmfeEmbedLit : List ℕ := [4244747, 8354290, 4935178, 7500812, 5461978, 1907870,
  310894, 7885382, 621788, 1089150, 2036820, 2178300, 5045448, 7821168, 1602438, 8489494]

/-- `RMFE_PROJECT` (`keccak.rs`), in decimal. -/
@[expose] def rmfeProjectLit : List ℕ := [1, 140737488355327, 43218598786281, 32136906789799,
  111925089164473, 101951566367639, 112771593653537, 102871349771039, 126754541004432,
  60819261648545, 20682647020959, 30409630824272, 11891857888673, 6939470531743, 76314673122000,
  70368744177664]

theorem rmfeEmbed_eq : rmfeEmbed = rmfeEmbedLit := by rfl

theorem rmfeProject_eq : rmfeProject = rmfeProjectLit := by rfl

theorem rmfeEmbed_length : rmfeEmbed.length = 16 := by rw [rmfeEmbed_eq]; rfl

theorem rmfeProject_length : rmfeProject.length = 16 := by rw [rmfeProject_eq]; rfl

/-- `RMFE_EMBED` as the native code's words. -/
@[expose] def rmfeEmbedWLit : Array UInt64 := #[4244747, 8354290, 4935178, 7500812, 5461978,
  1907870, 310894, 7885382, 621788, 1089150, 2036820, 2178300, 5045448, 7821168, 1602438, 8489494]

/-- `RMFE_PROJECT` as the native code's words. -/
@[expose] def rmfeProjectWLit : Array UInt64 := #[1, 140737488355327, 43218598786281,
  32136906789799, 111925089164473, 101951566367639, 112771593653537, 102871349771039,
  126754541004432, 60819261648545, 20682647020959, 30409630824272, 11891857888673, 6939470531743,
  76314673122000, 70368744177664]

theorem rmfeEmbedW_eq : rmfeEmbedW = rmfeEmbedWLit := by
  rw [rmfeEmbedW, rmfeEmbed_eq]; decide +kernel

theorem rmfeProjectW_eq : rmfeProjectW = rmfeProjectWLit := by
  rw [rmfeProjectW, rmfeProject_eq]; decide +kernel

/-- A word's bit below `64` is its value's. -/
theorem testBitW_eq (w : UInt64) {b : ℕ} (hb : b < 64) : testBitW w b = w.toNat.testBit b := by
  have hb' : (b.toUInt64).toNat = b := by simp; omega
  rw [testBitW, Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and,
    UInt64.toNat_shiftRight, hb', Nat.mod_eq_of_lt hb, Nat.testBit, Nat.and_comm]
  simp

/-- A number's word has its bits below `64`. -/
theorem testBitW_toUInt64 (n : ℕ) {b : ℕ} (hb : b < 64) : testBitW n.toUInt64 b = n.testBit b := by
  rw [testBitW_eq _ hb, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow]
  simp [hb]

end NativeVm.Equiv
