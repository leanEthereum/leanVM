/-
  LeanVM.Guest.B1.Sig.SphincsSoundWots

  `sp_wots` (`lean_ethereum.py:4072-4102`) against the statement: whenever its
  body holds, at a one-time key's address cells, the encoding digest's `base_2b` digits reach the
  target sum and its leaf is the statement's leaf of the chain values its frame hints.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsSound
public import LeanVM.Guest.B1.Sig.SphincsHash
public import LeanVM.Guest.B1.Sig.SphincsCompleteSpec
public import LeanVM.Guest.B1.Sig.SphincsSig

/-!
# `sp_wots` against the statement

`sp_wots_sound_cells` (over cells) gives the leaf as `spLeafCell` of the digits `spDigitR σ` and
the starts `spStartR σ`, the encoding digest the `XOR` of the digits' fields (`spX`). Here:

* `cellVal_eOfNat128`, `base2bDigits_spX`: the statement's `base_2b` digits of that cell are the
  digits (`spX_digit`), so they reach the target sum (`valid_spX`);
* `spChainStep_cells`, `chainWalk_cells`: a chain step of the statement at a key's address is
  `spStepCell` (`adrsCell1_add_step`), a walk `chainT`;
* `wotsLeafOf_cells`: the statement's leaf of the chain values is `spLeafCell`'s
  (`adrsCell1_add_type`: `a1 + SP_WOTS_PK`);
* `sChainValuesOf_eq`: `SphincsSig`'s chain values are the values at `spStartR σ`;
* `sp_wots_sound_stmt`, `wots_call_sound`: the body, and a call under a call relation that unfolds at
  a frame map.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.Verifier
open HashSig HashSig.OverPermutation

@[expose] public section

/-! ## The digits -/

/-- A cell's value. -/
theorem cellVal_eOfNat128 {X : Nat} (hX : X < 2 ^ 128) : cellVal (eOfNat128 X) = BitVec.ofNat 128 X :=
  BitVec.eq_of_toNat_eq (by rw [toNat_cellVal, cellNat_eOfNat128 hX, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hX])

/-- **The statement's `base_2b` digits of the encoding cell are the digits.** -/
theorem base2bDigits_spX {d : Nat → Nat} (hd : ∀ j, d j < 4) (i : Sphincs.ChainIndex) :
    (Sphincs.TargetSum.base2bDigits (cellVal (eOfNat128 (spX d 64))) i).val = d i.val := by
  have hi := i.isLt
  have hX := spX_lt hd (m := 64) le_rfl
  rw [cellVal_eOfNat128 hX, ← spX_digit hd (i := i.val) hi]
  unfold Sphincs.TargetSum.base2bDigits
  rw [BitVec.val_toFin]
  show (BitVec.extractLsb' (8 * (i.val / 4) + 6 - 2 * (i.val % 4)) 2
    (BitVec.ofNat 128 (spX d 64) : BitVec 128)).toNat = _
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hX, Nat.shiftRight_eq_div_pow]
  have : 8 * (i.val / 4) + 6 - 2 * (i.val % 4) = spDigitPos i.val := by
    unfold spDigitPos
    have : i.val % 4 < 4 := Nat.mod_lt _ (by norm_num)
    omega
  rw [this]

/-- **Digits of sum `128` are a codeword.** -/
theorem valid_spX {d : Nat → Nat} (hd : ∀ j, d j < 4) (hs : ∑ i ∈ Finset.range 64, d i = 128) :
    Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits (cellVal (eOfNat128 (spX d 64)))) := by
  unfold Sphincs.TargetSum.Valid Sphincs.TargetSum.sum
  simp only [base2bDigits_spX hd]
  exact (Fin.sum_univ_eq_sum_range d 64).trans hs

/-! ## The chains -/

/-- **A chain step of the statement over cells**: at the key's address cells, step `t` of chain `i`
on a cell's value is `spStepCell`'s. -/
theorem spChainStep_cells (pp y : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (lf : Sphincs.TreeLeafIndex) (i : Sphincs.ChainIndex) (t : ChainStep) :
    Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp)
        (.chain layer tree lf i t) (littleEndianBytes 16 (cellVal y)) =
      cellVal (spStepCell pp (adrsCell0 layer.val tree.val) (adrsCell1 0 lf.val 0 0) i.val t.val y) := by
  have hi : i.val < 256 := lt_of_lt_of_le i.isLt (by decide)
  have ht : t.val < 256 := lt_of_lt_of_le t.isLt (by decide)
  rw [digest_cells, tweakableHash_sphincsCells, spStepCell, spStepC, adrsCell1_add_step hi ht]
  rfl

/-- **A walk of the statement over cells** is `chainT` of `spStepCell`. -/
theorem chainWalk_cells (pp : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (lf : Sphincs.TreeLeafIndex) (i : Sphincs.ChainIndex) (s : Nat) (x : E) :
    ∀ m, s + m ≤ 3 →
      Id.run (Sphincs.Verification.chainWalk (m := Id) keccakF1600 (cellVal pp) layer tree lf i s m
          (cellVal x)) =
        cellVal (chainT (spStepCell pp (adrsCell0 layer.val tree.val) (adrsCell1 0 lf.val 0 0)) i.val
          m s x)
  | 0, _ => rfl
  | m + 1, h => by
      have ih := chainWalk_cells pp layer tree lf i s x m (by omega)
      have hlt : s + m < chainLength - 1 := by
        simp only [chainLength, winternitzBits]; omega
      rw [chainT_succ]
      simp only [Sphincs.Verification.chainWalk] at ih ⊢
      simp only [walkChain, Id.run_bind, hlt, ↓reduceDIte, ih]
      exact spChainStep_cells pp _ layer tree lf i ⟨s + m, hlt⟩

/-- **The statement's leaf over cells**: at the key's address cells, the leaf the values
`cellVal (starts i)` recover at digits `d` is `spLeafCell`'s. -/
theorem wotsLeafOf_cells (pp : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (lf : Sphincs.TreeLeafIndex) (enc : Digest) (d : Nat → Nat) (starts : Nat → E)
    (hd : ∀ i : Sphincs.ChainIndex, (Sphincs.TargetSum.base2bDigits enc i).val = d i.val) :
    wotsLeafOf (cellVal pp) layer tree lf enc (fun i => cellVal (starts i.val)) =
      cellVal (spLeafCell pp (adrsCell0 layer.val tree.val) (adrsCell1 0 lf.val 0 0) d starts) := by
  have hc : ∀ i : Sphincs.ChainIndex,
      Sphincs.Verification.recoverChain (m := Id) keccakF1600 (cellVal pp) layer tree lf i
          (Sphincs.TargetSum.base2bDigits enc i) (cellVal (starts i.val)) =
        cellVal (chainT (spStepCell pp (adrsCell0 layer.val tree.val) (adrsCell1 0 lf.val 0 0)) i.val
          (3 - d i.val) (d i.val) (starts i.val)) := by
    intro i
    have h4 := (Sphincs.TargetSum.base2bDigits enc i).isLt
    simp only [chainLength, winternitzBits] at h4
    unfold Sphincs.Verification.recoverChain
    rw [hd i] at h4 ⊢
    rw [show chainLength - 1 - d i.val = 3 - d i.val by simp [chainLength, winternitzBits]]
    exact chainWalk_cells pp layer tree lf i (d i.val) (starts i.val) (3 - d i.val) (by omega)
  unfold wotsLeafOf
  rw [Id.run_bind, sequenceFin_id, Sphincs.Verification.leafHash]
  have e := digestsPayload_cells fun i : Sphincs.ChainIndex =>
    chainT (spStepCell pp (adrsCell0 layer.val tree.val) (adrsCell1 0 lf.val 0 0)) i.val
      (3 - d i.val) (d i.val) (starts i.val)
  rw [show (fun i => Sphincs.Verification.recoverChain (m := Id) keccakF1600 (cellVal pp) layer tree lf
      i (Sphincs.TargetSum.base2bDigits enc i) (cellVal (starts i.val))) = _ from funext hc]
  change Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp) (.leaf layer tree lf)
    (digestsPayload fun i : Sphincs.ChainIndex => cellVal (chainT (spStepCell pp
      (adrsCell0 layer.val tree.val) (adrsCell1 0 lf.val 0 0)) i.val (3 - d i.val) (d i.val)
        (starts i.val))) = _
  rw [e, tweakableHash_sphincsCells, spLeafCell]
  have hpk : adrsCell1 0 lf.val 0 0 + spPkC = adrsCell1 1 lf.val 0 0 := by
    rw [show spPkC = word (1 * 2 ^ 24) 0 by rw [one_mul]; rfl]
    exact adrsCell1_add_type (by norm_num)
  rw [hpk, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-! ## `sp_wots`, against the statement -/

/-- `SphincsSig`'s chain values are the values at the starts. -/
theorem sChainValuesOf_eq (σ : Val) : sChainValuesOf σ = fun i => cellVal (σ (spStartR σ i.val)) :=
  rfl

variable {C : CallRel} {rd : Reader}

/-- **`sp_wots`'s body, against the statement**: it returns one word, and at a one-time key's
address cells the digest's digits reach the target sum and the word is the leaf the chain values
`sChainValuesOf σ` recover. -/
theorem sp_wots_sound_stmt {σ : Val} {rets : List E}
    (h : Stmt.HoldsList C rd σ (Fn.«sp_wots».core).body False (fun rs => rs = rets)) :
    ∃ leaf, rets = [leaf] ∧ ∀ (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
      (lf : Sphincs.TreeLeafIndex), (σ (.n 1), σ (.n 2)) = keyAdrsCells layer.val tree.val lf.val →
        Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits (cellVal (σ (.n 3)))) ∧
        cellVal leaf = wotsLeafOf (cellVal (σ (.n 0))) layer tree lf (cellVal (σ (.n 3)))
          (sChainValuesOf σ) := by
  obtain ⟨leaf, hr, hd, hs, h3, hl⟩ := sp_wots_sound_cells h
  refine ⟨leaf, hr, fun layer tree lf hk => ⟨?_, ?_⟩⟩
  · rw [h3]; exact valid_spX hd hs
  · simp only [keyAdrsCells, adrsWotsHash, Prod.mk.injEq] at hk
    rw [hl, hk.1, hk.2, sChainValuesOf_eq, h3,
      wotsLeafOf_cells _ layer tree lf _ (spDigitR σ) (fun i => σ (spStartR σ i)) (base2bDigits_spX hd)]

/-- **A call of `sp_wots`** under a call relation that unfolds at `V`: at a one-time key's address
cells, the encoding's digits reach the target sum and the leaf is the one the chain values of its
frame recover. -/
theorem wots_call_sound {P : Program} [Finds P "sp_wots" Fn.«sp_wots».core] {V : FrameMap}
    (hV : UnfoldsVP P rd C V) {pp a0 a1 enc leaf : E}
    (hc : C "sp_wots" [pp, a0, a1, enc] [leaf]) :
    ∀ (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (lf : Sphincs.TreeLeafIndex),
      (a0, a1) = keyAdrsCells layer.val tree.val lf.val →
        Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits (cellVal enc)) ∧
        cellVal leaf = wotsLeafOf (cellVal pp) layer tree lf (cellVal enc)
          (sChainValuesOf (V "sp_wots" [pp, a0, a1, enc] [leaf])) := by
  obtain ⟨fn, hf, hp, hb⟩ := hV _ _ _ hc
  rw [Finds.find (P := P) (name := "sp_wots") (fn := Fn.«sp_wots».core)] at hf
  cases hf
  rw [sp_wots_params] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3⟩ := hp
  obtain ⟨l, hl, hw⟩ := sp_wots_sound_stmt hb
  simp only [List.cons.injEq, and_true] at hl
  intro layer tree lf hk
  have := hw layer tree lf (by rw [h1, h2]; exact hk)
  rw [h0, h3, ← hl] at this
  exact this

end
end LeanVM.Guest.B1.Sig
