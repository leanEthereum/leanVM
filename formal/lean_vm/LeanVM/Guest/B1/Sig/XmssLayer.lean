/-
  LeanVM.Guest.B1.Sig.XmssLayer

  A layer of `verify_lean_xmss`'s address cells and message bytes are leanXMSS's.
-/

module

public import LeanVM.Guest.B1.Sig.Codeword
public import LeanVM.Guest.B1.Sig.Shifts
public import LeanVM.Guest.B1.Sig.Digest80
public import LeanVM.Guest.B1.Sig.XmssT
public import Common.WithHash
public import LeanVM.Guest.WithHash

/-!
# A layer of `verify_lean_xmss`

`xIdxNat layer L`: the layer's index, the leaf index's key, the top layer's bit `55` set.
`xStepAddrs_sound`: the step addresses' atoms holding, they hold the index's word plus their
constants. `xStepAdr_bytes`, `xLeafAdr_bytes`, `xMsgAdr_bytes`, `xNodeAdr_bytes`: the chain step,
leaf, message and node address cells' bytes are leanXMSS's addresses'. `bytesLE_cellPairVal`: a
message's bytes are its two cells'. `chainT_eq_xChain'`: a chain is leanXMSS's chain.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Addresses -/

theorem two_pow_mul_xor_mul (s a b : Nat) : 2 ^ s * a ^^^ 2 ^ s * b = 2 ^ s * (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, Nat.testBit_two_pow_mul]
  cases decide (s ≤ j) <;> simp

/-- An address cell: the index's word plus a constant above bit 32. -/
theorem idx_add_word {q1 q2 key : Nat} (hkey : key < 2 ^ 32) :
    eOfNat (2 ^ 32 * q1 + key) + word (2 ^ 32 * q2) 0 = eOfNat (2 ^ 32 * (q1 ^^^ q2) + key) := by
  rw [word_eq_eOfNat, ← Value.eOfNat_add_of_lt hkey, ← Value.eOfNat_add_of_lt hkey, add_right_comm,
    ← Value.eOfNat_xor, two_pow_mul_xor_mul]

theorem word_add_eOfNat {q lo : Nat} (hlo : lo < 2 ^ 32) :
    word (2 ^ 32 * q) 0 + eOfNat lo = eOfNat (2 ^ 32 * q + lo) := by
  rw [word_eq_eOfNat, Value.eOfNat_add_of_lt hlo]

/-- The index of layer `layer`: the leaf index's key, the top layer's bit `55` set. -/
def xIdxNat (layer L : Nat) : Nat := 2 ^ 32 * (2 ^ 23 * layer) + L >>> (16 * layer)

theorem key_lt (L layer : Nat) (hL : L < 2 ^ 32) : L >>> (16 * layer) < 2 ^ 32 :=
  lt_of_le_of_lt (Nat.shiftRight_le _ _) hL

theorem xIdxNat_zero (L : Nat) : xIdxNat 0 L = L := by simp [xIdxNat]

theorem xIdxNat_one {L : Nat} (hL : L < 2 ^ 32) :
    eOfNat (L >>> 16) + word lxTop 0 = eOfNat (xIdxNat 1 L) := by
  rw [add_comm, show lxTop = 2 ^ 32 * 2 ^ 23 by simp [lxTop], word_add_eOfNat (key_lt L 1 hL)]
  simp [xIdxNat]

/-- A message's bytes are its two cells', the first low. -/
theorem bytesLE_cellPairVal (c d : E) : HashSig.littleEndianBytes 32 (cellPairVal c d) = cellBytes c ++ cellBytes d := by
  have h0 := cellNat_lt c
  have h1 := cellNat_lt d
  have ht : (cellPairVal c d).toNat = cellNat c + 2 ^ 128 * cellNat d := by
    rw [cellPairVal, BitVec.toNat_append, toNat_cellVal, toNat_cellVal, Nat.shiftLeft_eq, mul_comm,
      two_pow_mul_or h0]
    ring
  rw [bytesLE_eq, ht, cellBytes_eq_leBytes, cellBytes_eq_leBytes,
    show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num, show 32 = 16 + 16 from rfl,
    leBytes_add_mul _ _ _ _ (by norm_num; omega)]

/-! ## The target sum -/

theorem xTarget_eq : xTarget = gen ^ 106 := by
  rw [Value.gen_pow_eq_ofK, xTarget, word, K.ofBits_zero]
  rw [← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

/-! ## A layer, sound -/

theorem cellsBytes_getD_past {cs : List E} {j : Nat} (h : 16 * cs.length ≤ j) :
    (cellsBytes cs).getD j 0 = 0 := by
  rw [List.getD_eq_default _ _ (by rw [length_cellsBytes]; exact h)]

attribute [local irreducible] kMsg

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem xStepAddrs_sound {idx : V} {a : Nat} (h : AtomsHold rd σ (xStepAddrs idx a)) :
    ∀ s < 3, σ (.n (a + 2 * s + 1)) = σ idx + word (tw 1 + s * stepMul) 0 := by
  intro s hs
  have e1 := h.atom (a := .const (.n (a + 2 * s)) (word (tw 1 + s * stepMul) 0)) (by
    simp only [xStepAddrs, List.mem_flatMap, List.mem_range]
    exact ⟨s, hs, List.mem_cons_self ..⟩)
  have e2 := h.atom (a := .add (.n (a + 2 * s + 1)) idx (.n (a + 2 * s))) (by
    simp only [xStepAddrs, List.mem_flatMap, List.mem_range]
    exact ⟨s, hs, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)
  simp only [Atom.Holds] at e1 e2
  rw [e2, e1]

theorem xStepAddrs_atoms (idx : V) (a : Nat) : atomsOnly (xStepAddrs idx a) = true := rfl

theorem atomsOnly_cst_addS (c : Nat) (w : E) (d x y : V) : atomsOnly [cst c w, addS d x y] = true := rfl

/-- The key of layer `layer` a leaf index signs with. -/
theorem keyAt_val (L : Nat) (hL : L < 2 ^ 32) (layer : Nat) (hl : layer < 2) :
    (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩).val = L >>> (16 * layer) := by
  simp [LeanXmss.keyIndexOnLayer, LeanXmss.layerHeight, Nat.shiftRight_eq_div_pow]

theorem chainT_eq_xChain' {f : Nat → Nat → E → E} {pp : E} {adr : Nat → E} {i : Nat}
    (hf : ∀ s y, f i s y = (hcell [pp, adr s, y, eOfNat i]).1) :
    ∀ (m s : Nat) (x : E), chainT f i m s x = xChain pp adr i m s x
  | 0, _, _ => rfl
  | m + 1, s, x => by
      rw [chainT, xChain, hf]
      exact chainT_eq_xChain' hf m (s + 1) _

/-- **The chain step addresses.** -/
theorem xStepAdr_bytes {L layer s : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) (hs : s < 3) :
    cellBytes (eOfNat (xIdxNat layer L) + word (tw 1 + s * stepMul) 0) =
      LeanXmss.tweakBytes (.chain ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩) ⟨s, by
        simp [HashSig.chainLength, HashSig.winternitzBits]; omega⟩) := by
  have hk := key_lt L layer hL
  rw [show LeanXmss.tweakBytes (.chain ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩)
      ⟨s, _⟩) =
      LeanXmss.addressBytes (LeanXmss.tweakFields 1 s (0 + 2 ^ 23 * layer) (L >>> (16 * layer))) by
      rw [← keyAt_val L hL layer hl]; rfl, fieldBytes_tweakFields, xIdxNat,
    show tw 1 + s * stepMul = 2 ^ 32 * (2 ^ 24 + 2 ^ 29 * s) by simp [tw, stepMul]; ring,
    idx_add_word hk]
  congr 2
  unfold addrNat
  rw [Nat.mod_eq_of_lt hk]
  interval_cases layer <;> interval_cases s <;> norm_num <;> omega

/-- **The leaf address.** -/
theorem xLeafAdr_bytes {L layer : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) :
    cellBytes (eOfNat (xIdxNat layer L) + word (tw 2) 0) =
      LeanXmss.tweakBytes (.leaf ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩)) := by
  have hk := key_lt L layer hL
  rw [show LeanXmss.tweakBytes (.leaf ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩)) =
      LeanXmss.addressBytes (LeanXmss.tweakFields 2 0 (0 + 2 ^ 23 * layer) (L >>> (16 * layer))) by
      rw [← keyAt_val L hL layer hl]; rfl, fieldBytes_tweakFields, xIdxNat,
    show tw 2 = 2 ^ 32 * 2 ^ 25 by simp [tw], idx_add_word hk]
  congr 2
  unfold addrNat
  rw [Nat.mod_eq_of_lt hk]
  interval_cases layer <;> norm_num <;> omega

/-- **The message address.** -/
theorem xMsgAdr_bytes {L layer : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) :
    cellBytes (eOfNat (xIdxNat layer L) + word (tw 12) 0) =
      LeanXmss.tweakBytes (.message ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer,
          hl⟩)) := by
  have hk := key_lt L layer hL
  rw [show LeanXmss.tweakBytes (.message ⟨layer, hl⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer,
      hl⟩)) =
      LeanXmss.addressBytes (LeanXmss.tweakFields 12 0 (0 + 2 ^ 23 * layer) (L >>> (16 * layer))) by
      rw [← keyAt_val L hL layer hl]; rfl, fieldBytes_tweakFields, xIdxNat,
    show tw 12 = 2 ^ 32 * (12 * 2 ^ 24) by simp [tw], idx_add_word hk]
  congr 2
  unfold addrNat
  rw [Nat.mod_eq_of_lt hk]
  interval_cases layer <;> norm_num <;> omega

/-- **The node addresses**: level `l`'s, the parent's index added unless it is the root. -/
theorem xNodeAdr_bytes {L layer l : Nat} (hL : L < 2 ^ 32) (hl : layer < 2) (hl16 : l < 16) :
    cellBytes (word (xAddrOf layer l) 0 + (if 16 * layer + l + 1 = 32 then 0 else
        eOfNat (L >>> (16 * layer + l + 1)))) =
      LeanXmss.tweakBytes (.node ⟨layer, hl⟩ (l + 1)
        ((LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩).val / 2 ^ (l + 1))) := by
  have hk := key_lt L layer hL
  rw [show LeanXmss.tweakBytes (.node ⟨layer, hl⟩ (l + 1)
        ((LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨layer, hl⟩).val / 2 ^ (l + 1))) =
      LeanXmss.addressBytes (LeanXmss.tweakFields 3 0 (l + 1 + 2 ^ 23 * layer)
        ((L >>> (16 * layer)) / 2 ^ (l + 1))) by rw [← keyAt_val L hL layer hl]; rfl,
    fieldBytes_tweakFields,
    show xAddrOf layer l = 2 ^ 32 * (3 * 2 ^ 24 + (l + 1) + 2 ^ 23 * layer) by
      simp [xAddrOf, tw, hiMul, lxTop]; ring]
  have hdiv : L >>> (16 * layer) / 2 ^ (l + 1) = L >>> (16 * layer + l + 1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
    ring_nf
  rw [hdiv]
  have hlt : L >>> (16 * layer + l + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.shiftRight_le _ _) hL
  split
  · rename_i h32
    have h0 : L >>> (16 * layer + l + 1) = 0 := by
      rw [h32, Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hL
    rw [h0, add_zero, word_eq_eOfNat]
    congr 2
    unfold addrNat
    interval_cases layer <;> omega
  · rw [word_add_eOfNat hlt]
    congr 2
    unfold addrNat
    rw [Nat.mod_eq_of_lt hlt]
    interval_cases layer <;> omega

end
end LeanVM.Guest.B1.Sig
