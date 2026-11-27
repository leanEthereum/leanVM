/-
  LeanVM.Guest.B1.Sig.SphincsSoundLayer

  A layer of `verify_sig_lean_sphincs` (`sp_layer`, `lean_ethereum.py`, after its counter) is sound: its encoding digest is the hash of `P`, `A0`,
  `key + WOTS_ENC`, the value it signs and the counter's four bytes, and its root the path's fold
  from the leaf `sp_wots` returns.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundFors
import LeanVM.Guest.StmtsAppend

/-!
# A layer, sound

`sHtLayer … b` is `layerPre … b` (`enc_at` at `b + 1`, the encoding's `keccak`, its output at
`b + 9`), the call of `sp_wots` (its leaf at `b + 10`), then the path from `b + 11`
(`sHtLayer_split`), each position after `b + 2` one up for each `A0` set before (`a0W`):

* `sLayerEnc_sound`: the encoding digest, the counter a word `N < 2^32` (its four low bytes).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-- A layer's statements before its call: `enc_at = key + WOTS_ENC` at `b + 1`, the encoding's
`A0`, then the encoding's 68-byte `keccak` of `P`, `A0`, `enc_at`, `signed` and the counter, then
the call's `A0`. -/
def layerPre (pad : Nat) (pp a0 : V) (ac : Option E) (key signed ctr : V) (b : Nat) : List Stmt :=
  ([cst b (lit (7 * 2 ^ 24)), addS (.n (b + 1)) key (.n b)] ++ a0Pre ac (b + 2)) ⧺
    ((kMsg pad [.cell pp, .cell (a0Cell a0 ac (b + 2)), .cell (.n (b + 1)), .cell signed, .cell ctr]
      68 false none (b + 2 + a0W ac)).1 ++ a0Pre ac (b + 10 + a0W ac))

theorem kEnc_shape (pad : Nat) (pp a0 ea signed ctr : V) (y : Nat) :
    (kMsg pad [.cell pp, .cell a0, .cell ea, .cell signed, .cell ctr] 68 false none y).2.1 =
        y + 8 ∧
      (kMsg pad [.cell pp, .cell a0, .cell ea, .cell signed, .cell ctr] 68 false none y).2.2 =
        y + 7 := by
  constructor <;> rfl

/-- **A layer, split around its call.** -/
theorem sHtLayer_split (pad : Nat) (pp a0 : V) (ac : Option E) (key signed ctr : V)
    (bit val : Nat → V) (off height b : Nat) :
    sHtLayer pad pp a0 ac key signed ctr bit val off height b =
      (layerPre pad pp a0 ac key signed ctr b ⧺
          [.call "sp_wots" [pp, a0Cell a0 ac (b + 10 + a0W ac), key, .n (b + 9 + a0W ac)]
            [.n (b + 10 + 2 * a0W ac)]] ⧺
          (sPath pad pp a0 ac bit val off height 0 (.n (b + 10 + 2 * a0W ac))
            (b + 10 + 2 * a0W ac + 1)).1,
        (sPath pad pp a0 ac bit val off height 0 (.n (b + 10 + 2 * a0W ac))
            (b + 10 + 2 * a0W ac + 1)).2.1,
        (sPath pad pp a0 ac bit val off height 0 (.n (b + 10 + 2 * a0W ac))
            (b + 10 + 2 * a0W ac + 1)).2.2) := by
  simp only [sHtLayer, layerPre, (kEnc_shape ..).1, (kEnc_shape ..).2, List.append_assoc]
  rw [show b + 2 + a0W ac + 8 + a0W ac = b + 10 + 2 * a0W ac by omega,
    show b + 2 + a0W ac + 8 = b + 10 + a0W ac by omega, show b + 2 + a0W ac + 7 = b + 9 + a0W ac by omega]

variable {rd : Reader} {σ : Val}

/-- The bytes of cells ending in a counter's word are zero past its four bytes. -/
theorem cellsBytes_counter_zero (cs : List E) {N : Nat} (hN : N < 2 ^ 32) :
    ∀ j, 16 * cs.length + 4 ≤ j → (cellsBytes (cs ++ [eOfNat N])).getD j 0 = 0 := by
  intro j hj
  have hl := flatMap_cellBytes_length cs
  rw [cellsBytes_eq_flatMap, List.flatMap_append, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [cellBytes_eOfNat (by omega)]
  by_cases h16 : j - 16 * cs.length < 16
  · rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some, getElem_leBytes]
    have : N / 256 ^ (j - 16 * cs.length) = 0 := Nat.div_eq_of_lt (by
      calc N < 2 ^ 32 := hN
        _ ≤ 256 ^ 4 := by norm_num
        _ ≤ 256 ^ (j - 16 * cs.length) := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [this]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- **A layer's encoding, sound**: with the counter a word `N < 2^32`, the encoding digest is the
Keccak-256 of `P`, `A0`, `key + WOTS_ENC`, `signed` (whole cells) and the counter's four low
bytes. -/
theorem sLayerEnc_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 : V} {ac : Option E}
    {key signed ctr : V} {b N : Nat} (hN : N < 2 ^ 32) (hctr : σ ctr = eOfNat N)
    (h : AtomsHold rd σ (layerPre pad pp a0 ac key signed ctr b)) :
    σ (.n (b + 9 + a0W ac)) = (digestHalves (keccak256 (cellsBytes [σ pp, a0Val σ a0 ac,
      σ key + lit (7 * 2 ^ 24), σ signed] ++ leBytes N 4))).1 := by
  have c0 : σ (.n b) = lit (7 * 2 ^ 24) := h.left.left.atom (a := .const (.n b) _) (by simp [cst])
  have a1 : σ (.n (b + 1)) = σ key + σ (.n b) :=
    h.left.left.atom (a := .add (.n (b + 1)) _ _) (by simp [addS])
  have ha := a0Pre_sound (a0 := a0) h.left.right
  have hm : [KC.cell pp, .cell (a0Cell a0 ac (b + 2)), .cell (.n (b + 1)), .cell signed,
      .cell ctr].map (KC.val σ) =
      [σ pp, a0Val σ a0 ac, σ key + lit (7 * 2 ^ 24), σ signed] ++ [eOfNat N] := by
    simp [KC.val, a1, c0, hctr, ha]
  have k := kMsg_sound (cells := [.cell pp, .cell (a0Cell a0 ac (b + 2)), .cell (.n (b + 1)),
    .cell signed, .cell ctr])
    (len := 68) (tailRun := false) (out := none) hp (fun h => by simp at h)
    h.right.left (by simp)
    (fun j hj => by rw [hm]; exact cellsBytes_counter_zero _ hN j (by simp; omega))
  rw [(kEnc_shape ..).2] at k
  rw [show b + 2 + a0W ac + 7 = b + 9 + a0W ac by omega] at k
  have k1 := k
  rw [k1, hm]
  congr 3
  have h64 : (List.flatMap cellBytes [σ pp, a0Val σ a0 ac, σ key + lit (7 * 2 ^ 24),
      σ signed]).length = 64 := by rw [flatMap_cellBytes_length]; rfl
  rw [cellsBytes_eq_flatMap, cellsBytes_eq_flatMap, List.flatMap_append,
    List.take_append, List.take_of_length_le (by omega), h64,
    show (68 : Nat) - 64 = 4 from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [cellBytes_eOfNat (by omega), ← leBytes_append N 4 12, List.take_left' (by simp)]

end
end LeanVM.Guest.B1.Sig
