/-
  LeanVM.Guest.B1.Sig.SphincsTopComplete

  A layer of `verify_sig_lean_sphincs` (`sp_layer`, `lean_ethereum.py:4129-4140, 4233-4242`)
  is complete for an honest signature: the root it reaches is the statement's.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBottomComplete
public import LeanVM.Guest.B1.Sig.SphincsHtComplete

/-!
# A layer of an honest signature, complete

`layer_stage`: when the statement's layer `l` reaches `r` from the value of a cell `S`
(`LayerReaches`), and the valuation holds what the stages before leave (`BottomPost`), layer `l`'s
key's address cells and `S` where the layer reads them, the layer completes with its root cell
`layerRootCell` (whose value is `r`), its counter hinted as `BE_32` of the signature's, the call of
`sp_wots` holding by `SpWotsCalls`, its path hinted as the signature's. `layer_stage_vals` also gives the call's
arguments and return, the honest call's (`LayerCallAt`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

open LeanVM.Guest.Memory (SplicePops)

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem sHeightOf_eq {l : Nat} (hl : l < 3) : sHeightOf l = Sphincs.layerHeight ⟨l, hl⟩ := by
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl <;> rfl

/-- **Layer `L`'s entries**, signing the value of `S`, its call's `k` spliced in: its counter, the call's, then its path's children. -/
def layerPops (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) (L : Sphincs.Layer) (S : E)
    (k : List Pop) : List Pop :=
  counterPop (sig.layers L).counter.toNat :: (k ++ climbPops "siblings"
    (pNodeE (cellOf128 pk.publicSeed) (adrsCell0 L.val (layerTreeN (digestT pk m sig) L.val))
      (layerLeafN (digestT pk m sig) L.val) (layerSibCell sig L))
    (layerLeafN (digestT pk m sig) L.val).testBit (layerSibCell sig L) (sHeightOf L.val) 0
    (cellOf128 (layerLeaf pk (digestIdx pk m sig) sig L S)))

/-- Layer `l`'s call of `sp_wots`: its arguments. -/
def sCallArgs (l : Nat) : List V := [sPP, sA0Of l, sA1Of l, sEncOf l]

/-- The arguments of layer `L`'s honest call of `sp_wots`, signing the value of `S`. -/
def spCallArgs (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) (L : Sphincs.Layer) (S : E) :
    List E :=
  [cellOf128 pk.publicSeed, adrsCell0 L.val (Sphincs.treeOfIndex L (digestIdx pk m sig)).val,
    adrsCell1 0 (Sphincs.leafOfIndex L (digestIdx pk m sig)).val 0 0, layerEnc pk (digestIdx pk m sig) sig L S]

/-- **Layer `L`'s call of `sp_wots` under `σ`**, signing the value of `S`: its arguments and its return are the honest
call's. -/
def LayerCallAt (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) (σ : Val) (L : Sphincs.Layer)
    (S : E) : Prop :=
  (sCallArgs L.val).map σ = spCallArgs pk m sig L S ∧
    σ (sLeafOf L.val) = cellOf128 (layerLeaf pk (digestIdx pk m sig) sig L S)

theorem LayerCallAt.congr {pk : Sphincs.PublicKey} {m : HashSig.Message} {sig : Sphincs.Signature} {σ σ' : Val}
    {L : Sphincs.Layer} {S : E} {K : Nat} (h : LayerCallAt pk m sig σ L S) (hK : sLayerBase L.val + 48 ≤ K)
    (ha : ∀ k < K, σ' (.n k) = σ (.n k)) : LayerCallAt pk m sig σ' L S := by
  have Sh := layerShape L.isLt
  have t : ∀ v : V, NBv K v → σ' v = σ v := fun v ⟨k, hk, ek⟩ => by rw [ek]; exact ha k hk
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by rw [t (sLeafOf L.val) ⟨sLayerBase L.val + 47, by omega, rfl⟩]; exact h2⟩
  rw [← h1]
  simp only [sCallArgs, List.map_cons, List.map_nil]
  rw [t sPP ⟨2, by have := Sh.digest; omega, rfl⟩, t _ (Sh.a0.mono' (by omega)), t _ (Sh.a1.mono' (by omega)),
    t (sEncOf L.val) ⟨sLayerBase L.val + 46, by omega, rfl⟩]

/-- **Layer `l` of an honest signature completes** to the root cell of the statement's layer, its call of
`sp_wots` the honest one. -/
theorem layer_stage_vals (hB : SphincsBlocksComplete) (hC : SpWotsCalls C) (hm : MemOK rd 256) {bb : E}
    (hbb : ByteBits rd bb) {pk : Sphincs.PublicKey} {m : HashSig.Message} {sig : Sphincs.Signature}
    {l : Nat} (hl : l < 3) {S : E} {r : HashSig.Digest}
    (hr : LayerReaches pk.publicSeed (digestIdx pk m sig) sig ⟨l, hl⟩ (cellVal S) r)
    (σ : Val) (h1 : σ (.n 1) = bb) (hbot : BottomPost bb pk m sig σ)
    (ha0 : σ (sA0Of l) = adrsCell0 l (layerTreeN (digestT pk m sig) l))
    (ha1 : σ (sA1Of l) = adrsCell1 0 (layerLeafN (digestT pk m sig) l) 0 0)
    (hsg : σ (sSignedOf l) = S) :
    r = cellVal (layerRootCell pk (digestIdx pk m sig) sig ⟨l, hl⟩ S) ∧
      Completes C rd (sLayerBase l) (sLayerBlk l).2.1 (sLayerBlk l).1 σ (fun σ' =>
        σ' (sLayerBlk l).2.2 = layerRootCell pk (digestIdx pk m sig) sig ⟨l, hl⟩ S ∧
          TablePtrs bb σ' (sLayerBlk l).1 ∧
          (∀ k, SplicePops rd σ' (sLayerBlk l).1 [k] (layerPops pk m sig ⟨l, hl⟩ S k)) ∧
          LayerCallAt pk m sig σ' ⟨l, hl⟩ S) := by
  obtain ⟨hV, hr'⟩ := layer_cells hr
  refine ⟨hr', ?_⟩
  obtain ⟨hp, hpp, -, hd, -⟩ := hbot
  have et := treeOf_idx pk m sig ⟨l, hl⟩
  have el := leafOf_idx pk m sig ⟨l, hl⟩
  have hc := layer_call hC hV
  have henc : encDigestCell (σ sPP) (σ (sA0Of l)) (σ (sA1Of l) + lit (7 * 2 ^ 24)) (σ (sSignedOf l))
      (eOfNat (beWordAt 0 (sig.layers ⟨l, hl⟩).counter.toNat)) =
      layerEnc pk (digestIdx pk m sig) sig ⟨l, hl⟩ S := by
    rw [hpp, ha0, ha1, adrsCell1_enc, hsg, layerEnc, et, el]
  have hcall : C "sp_wots" [σ sPP, σ (sA0Of l), σ (sA1Of l),
      encDigestCell (σ sPP) (σ (sA0Of l)) (σ (sA1Of l) + lit (7 * 2 ^ 24)) (σ (sSignedOf l))
        (eOfNat (beWordAt 0 (sig.layers ⟨l, hl⟩).counter.toNat))]
      [cellOf128 (layerLeaf pk (digestIdx pk m sig) sig ⟨l, hl⟩ S)] := by
    rw [henc, hpp, ha0, ha1]
    rw [et, el] at hc
    exact hc
  have hL := sLayerBlk_complete_vals (C := C) hB hm hbb hl (sig.layers ⟨l, hl⟩).counter.isLt
    (e := layerLeafN (digestT pk m sig) l) (sib := layerSibCell sig ⟨l, hl⟩) σ h1 hp hcall
    (layerLeafN_lt _ l)
    (fun z hz => by
      rw [hd.leafBit (sOff_lt hl hz), testBit_layerLeafN, show sOffOf l = sLeafOff l from rfl]
      have hz' : z < sLeafLen l := hz
      simp only [hz', decide_true, Bool.true_and, bitE])
    (fun z hz => hd.2.2.2.1 l hl z hz)
  obtain ⟨σ', he', ⟨h3, h4, h5, h6, h7⟩, hh'⟩ := hL
  have Sh := layerShape hl
  have t : ∀ v : V, NBv (sLayerBase l) v → σ' v = σ v := fun v ⟨k, hk, ek⟩ => by
    rw [ek]; exact he'.apply (Or.inl hk)
  refine ⟨σ', he', ⟨?_, h4, fun k => ?_, ⟨?_, h7⟩⟩, hh'⟩
  · rw [h3, layerRootCell, hpp, ha0, et, el, sHeightOf_eq hl]
  · have h := h5 k
    rw [hpp, ha0] at h
    exact h
  · simp only [sCallArgs, spCallArgs, sEncOf, List.map_cons, List.map_nil]
    rw [t sPP ⟨2, by have := Sh.digest; omega, rfl⟩, t _ Sh.a0, t _ Sh.a1, h6, henc, hpp, ha0, ha1, et, el]

/-- **Layer `l` of an honest signature completes** (`layer_stage_vals` without its call). -/
theorem layer_stage (hB : SphincsBlocksComplete) (hC : SpWotsCalls C) (hm : MemOK rd 256) {bb : E}
    (hbb : ByteBits rd bb) {pk : Sphincs.PublicKey} {m : HashSig.Message} {sig : Sphincs.Signature}
    {l : Nat} (hl : l < 3) {S : E} {r : HashSig.Digest}
    (hr : LayerReaches pk.publicSeed (digestIdx pk m sig) sig ⟨l, hl⟩ (cellVal S) r)
    (σ : Val) (h1 : σ (.n 1) = bb) (hbot : BottomPost bb pk m sig σ)
    (ha0 : σ (sA0Of l) = adrsCell0 l (layerTreeN (digestT pk m sig) l))
    (ha1 : σ (sA1Of l) = adrsCell1 0 (layerLeafN (digestT pk m sig) l) 0 0)
    (hsg : σ (sSignedOf l) = S) :
    r = cellVal (layerRootCell pk (digestIdx pk m sig) sig ⟨l, hl⟩ S) ∧
      Completes C rd (sLayerBase l) (sLayerBlk l).2.1 (sLayerBlk l).1 σ (fun σ' =>
        σ' (sLayerBlk l).2.2 = layerRootCell pk (digestIdx pk m sig) sig ⟨l, hl⟩ S ∧
          TablePtrs bb σ' (sLayerBlk l).1 ∧
          ∀ k, SplicePops rd σ' (sLayerBlk l).1 [k] (layerPops pk m sig ⟨l, hl⟩ S k)) :=
  let h := layer_stage_vals hB hC hm hbb hl hr σ h1 hbot ha0 ha1 hsg
  ⟨h.1, h.2.mono le_rfl le_rfl fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩⟩

end
end LeanVM.Guest.B1.Sig
