/-
  LeanVM.Guest.B1.Sig.SphincsSoundLayer

  A layer of `verify_sig_lean_sphincs` (`sp_layer`, `lean_ethereum.py:4128-4140`, after its counter) is sound: its encoding digest is the hash of `P`, `A0`,
  `key + WOTS_ENC`, the value it signs and the counter's four bytes, and its root the path's fold
  from the leaf `sp_wots` returns.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundFors

/-!
# A layer, sound

`sHtLayer … b` is `layerPre … b` (`enc_at` at `b + 1`, the encoding's `keccak`, its output at
`b + 9`), the call of `sp_wots` (its leaf at `b + 10`), then the path from `b + 11`
(`sHtLayer_split`):

* `sLayerEnc_sound`: the encoding digest, the counter a word `N < 2^32` (its four low bytes);
* `sHtLayer_root`: the root, `pFold` of `pNodeE` from the leaf, the siblings `sPathSib`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-- A layer's statements before its call: `enc_at = key + WOTS_ENC` at `b + 1`, then the
encoding's 68-byte `keccak` of `P`, `A0`, `enc_at`, `signed` and the counter. -/
def layerPre (pad : Nat) (pp a0 key signed ctr : V) (b : Nat) : List Stmt :=
  [cst b (lit (7 * 2 ^ 24)), addS (.n (b + 1)) key (.n b)] ++
    (kMsg pad [.cell pp, .cell a0, .cell (.n (b + 1)), .cell signed, .cell ctr] 68 false none
      (b + 2)).1

theorem kEnc_shape (pad : Nat) (pp a0 ea signed ctr : V) (y : Nat) :
    (kMsg pad [.cell pp, .cell a0, .cell ea, .cell signed, .cell ctr] 68 false none y).2.1 =
        y + 8 ∧
      (kMsg pad [.cell pp, .cell a0, .cell ea, .cell signed, .cell ctr] 68 false none y).2.2 =
        y + 7 := by
  constructor <;> rfl

/-- **A layer, split around its call.** -/
theorem sHtLayer_split (pad : Nat) (pp a0 key signed ctr : V) (bit val : Nat → V)
    (off height b : Nat) :
    sHtLayer pad pp a0 key signed ctr bit val off height b =
      (layerPre pad pp a0 key signed ctr b ++
          [.call "sp_wots" [pp, a0, key, .n (b + 9)] [.n (b + 10)]] ++
          (sPath pad pp a0 bit val off height 0 (.n (b + 10)) (b + 11)).1,
        (sPath pad pp a0 bit val off height 0 (.n (b + 10)) (b + 11)).2.1,
        (sPath pad pp a0 bit val off height 0 (.n (b + 10)) (b + 11)).2.2) := by
  simp only [sHtLayer, layerPre, (kEnc_shape ..).1, (kEnc_shape ..).2, List.append_assoc]

theorem layerPre_atoms (pad : Nat) (pp a0 key signed ctr : V) (b : Nat) :
    atomsOnly (layerPre pad pp a0 key signed ctr b) = true := by
  simp only [layerPre, atomsOnly_append, kMsg_atoms]
  rfl

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
theorem sLayerEnc_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 key signed ctr : V} {b N : Nat}
    (hN : N < 2 ^ 32) (hctr : σ ctr = eOfNat N)
    (h : AtomsHold rd σ (layerPre pad pp a0 key signed ctr b)) :
    σ (.n (b + 9)) = (digestHalves (keccak256 (cellsBytes [σ pp, σ a0, σ key + lit (7 * 2 ^ 24),
      σ signed] ++ leBytes N 4))).1 := by
  have c0 : σ (.n b) = lit (7 * 2 ^ 24) := h.atom (a := .const (.n b) _) (by simp [layerPre, cst])
  have a1 : σ (.n (b + 1)) = σ key + σ (.n b) :=
    h.atom (a := .add (.n (b + 1)) _ _) (by simp [layerPre, addS])
  have hm : [KC.cell pp, .cell a0, .cell (.n (b + 1)), .cell signed, .cell ctr].map (KC.val σ) =
      [σ pp, σ a0, σ key + lit (7 * 2 ^ 24), σ signed] ++ [eOfNat N] := by
    simp [KC.val, a1, c0, hctr]
  have k := kMsg_sound (cells := [.cell pp, .cell a0, .cell (.n (b + 1)), .cell signed, .cell ctr])
    (len := 68) (tailRun := false) (out := none) hp (fun h => by simp at h)
    (h.sub fun x hx => List.mem_append_right _ hx) (by simp)
    (fun j hj => by rw [hm]; exact cellsBytes_counter_zero _ hN j (by simp; omega))
  rw [(kEnc_shape ..).2] at k
  rw [show b + 2 + 7 = b + 9 by omega] at k
  have k1 := k
  rw [k1, hm]
  congr 3
  have h64 : (List.flatMap cellBytes [σ pp, σ a0, σ key + lit (7 * 2 ^ 24), σ signed]).length =
      64 := by rw [flatMap_cellBytes_length]; rfl
  rw [cellsBytes_eq_flatMap, cellsBytes_eq_flatMap, List.flatMap_append,
    List.take_append, List.take_of_length_le (by omega), h64,
    show (68 : Nat) - 64 = 4 from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [cellBytes_eOfNat (by omega), ← leBytes_append N 4 12, List.take_left' (by simp)]

/-- **A layer's root, sound**: after its call, the path from the leaf at `b + 10` reaches `pFold` of
`pNodeE`, its bits those of `e < 2^height` and its shifts `e`'s. -/
theorem sHtLayer_root {pad : Nat} (hp : PadOK σ pad) {pp a0 key signed ctr : V}
    {bit val : Nat → V} {off e height b : Nat} (hh : height ≤ 16) (he : e < 2 ^ height)
    (hbit : ∀ z < height, σ (bit (off + z)) = if e.testBit z then 1 else 0)
    (hval : ∀ z, z < height → σ (val (off + z)) = eOfNat (e >>> z))
    (h : AtomsHold rd σ (sPath pad pp a0 bit val off height 0 (.n (b + 10)) (b + 11)).1) :
    σ (sHtLayer pad pp a0 key signed ctr bit val off height b).2.2 =
      pFold (pNodeE (σ pp) (σ a0) e (sPathSib σ bit off height 0 (b + 11))) height
        (σ (.n (b + 10))) := by
  rw [sHtLayer_split, ← nIter_zero]
  exact sPath_sound hp hh he hbit hval height 0 _ _ (by omega) h

end
end LeanVM.Guest.B1.Sig
