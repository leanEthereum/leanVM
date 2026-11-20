/-
  Rv64mc.Proof.Walk.MainEntry

  `main`'s entry, before its first cut point: what its precondition (`MainPre`) gives of the input words, for the
  callees' preconditions `rv_auto` leaves at the entry: the bytecode's count read and checked (`count_le`), the
  slice `Bytecode::new` reads as a `WordsAt` and `Live` for any count (`slice_words`, `slice_live`, given to
  `rv_auto` as `with` facts), its length (`slice_len`), and the input below the stack (`input_far`).
-/

import Rv64mc.Proof.Walk.MainBase

namespace Rv64mc.Proof.Walk.Main

open RiscvZkvm.Rv64

theorem input_end {env : Env} {m : MachineState} {words : List Word} (h7 : words.length ≤ inputCapacity)
    (h9 : env.next m = heapStart) : 0x10000000 + 8 * words.length ≤ (env.next m).toNat := by
  rw [h9, show heapStart.toNat = 0x20000000 from rfl]; unfold inputCapacity at h7; omega

theorem input_word {m : MachineState} {words : List Word}
    (h8 : ∀ (i : ℕ) (h : i < words.length), m.getMem (inputBase + BitVec.ofNat 64 (8 * i)) = words[i])
    {i : Nat} (h : i < words.length) : m.getMem (0x10000000#64 + BitVec.ofNat 64 (8 * i)) = words[i] := h8 i h

theorem input_word0 {m : MachineState} {words : List Word}
    (h8 : ∀ (i : ℕ) (h : i < words.length), m.getMem (inputBase + BitVec.ofNat 64 (8 * i)) = words[i])
    (h : 0 < words.length) : m.getMem 0x10000000#64 = words[0] := by
  have := h8 0 h; rwa [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this

/-- The bytecode's count, read and checked against the input's length. -/
theorem count_le {words : List Word} (h7 : words.length ≤ inputCapacity) (h0 : 0 < words.length)
    (hc : words[0] ≤ BitVec.ofNat 64 words.length + 18446744073709551615#64) : words[0].toNat ≤ words.length - 1 := by
  unfold inputCapacity at h7
  rw [sub_lit (k := 1) _ (by decide) (by omega) (by omega), BitVec.le_def, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)] at hc
  exact hc

theorem headD_eq {ws : List Word} (h : 0 < ws.length) : ws.headD 0 = ws[0] := by
  cases ws with
  | nil => simp at h
  | cons w ws => rfl

theorem slice_len {words : List Word} (h0 : 0 < words.length) (hn : words[0].toNat ≤ words.length - 1) :
    words[0] = BitVec.ofNat 64 (List.take (words.headD 0).toNat (List.drop 1 words)).length := by
  rw [headD_eq h0, List.length_take, List.length_drop, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem add_ofNat_lit (k : Nat) :
    (268435464#64 : Word) + BitVec.ofNat 64 (8 * k) = 0x10000000#64 + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [show (268435464#64 : Word) = 0x10000000#64 + 8#64 by decide, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem slice_words {m : MachineState} {words : List Word}
    (h8 : ∀ (i : ℕ) (h : i < words.length), m.getMem (inputBase + BitVec.ofNat 64 (8 * i)) = words[i])
    (h7 : words.length ≤ inputCapacity) (N : Nat) : WordsAt m 268435464#64 (List.take N (List.drop 1 words)) := by
  unfold inputCapacity at h7
  refine ⟨by simp only [List.length_take, List.length_drop, BitVec.toNat_ofNat]; omega, fun k hk => ?_⟩
  simp only [List.length_take, List.length_drop] at hk
  rw [add_ofNat_lit, input_word h8 (by omega), List.getElem_take, List.getElem_drop]
  simp only [Nat.add_comm]

theorem slice_live {env : Env} {m : MachineState} {words : List Word} (h7 : words.length ≤ inputCapacity)
    (h9 : env.next m = heapStart) (N : Nat) :
    env.Live m 268435464#64 (8 * (List.take N (List.drop 1 words)).length) := by
  unfold Env.Live inputCapacity at *
  rw [show (268435464#64 : Word).toNat = 268435464 from rfl, List.length_take, List.length_drop, h9,
    show heapStart.toNat = 0x20000000 from rfl]
  omega

theorem slice_le (words : List Word) (N : Nat) : (List.take N (List.drop 1 words)).length ≤ words.length := by
  simp only [List.length_take, List.length_drop]; omega

theorem input_far {env : Env} {m : MachineState} {words : List Word} (h7 : words.length ≤ inputCapacity)
    (h5 : (env.next m).toNat ≤ env.heapEnd.toNat) (h9 : env.next m = heapStart) :
    0x10000008 + 8 * words.length ≤ env.stackLimit.toNat := by
  have := env.layout
  unfold inputCapacity at h7
  rw [h9, show heapStart.toNat = 0x20000000 from rfl] at h5
  omega

end Rv64mc.Proof.Walk.Main
