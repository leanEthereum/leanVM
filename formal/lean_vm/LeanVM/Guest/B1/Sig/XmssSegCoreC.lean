/-
  LeanVM.Guest.B1.Sig.XmssSegCoreC

  A layer of leanXMSS's check inline in `__loop2`, after its message digest, completes, given the
  path windows' completeness (`LxWindowsC`), and reads the signature's layer back (`sPart_eq`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegLayerC
public import LeanVM.Guest.B1.Sig.XmssSegDigestC
public import LeanVM.Guest.B1.Sig.XmssSegWinSpec

/-!
# A layer after its digest, complete

* `LxWindowsC`: what the path windows' completeness establishes (`XmssSegPathC`): a layer's two
  windows complete from the leaf, the root canonical and the hinted siblings the given ones;
* `sCore_complete`: the step addresses, the codeword, the leaf and the two windows complete;
* `xVals`, `xSibs`, `sPart_eq`: the layer signature as cells, read back off the valuation;
* `digest_digits`, `layerRoot_decode`, `cellPairVal_cellOf128`: the scheme's side.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

attribute [local irreducible] kMsg sCodewordT lxWindowT

/-! ## The scheme's side -/

theorem canon_lit (N : Nat) : IsCanonical128 (lit N) := canon_word _ _

/-- **A canonical digest that decodes** is the literal of its `58` digits, which sum to `106`. -/
theorem digest_digits {x : E} {enc : LeanXmss.Encoding} (hx : IsCanonical128 x)
    (hd : LeanXmss.Codeword.decode (xv x) = some enc) :
    x = lit (∑ i ∈ Finset.range 58, (xv x).toNat / 4 ^ i % 4 * 4 ^ i) ∧
      ∑ i ∈ Finset.range 58, (xv x).toNat / 4 ^ i % 4 = 106 := by
  obtain ⟨-, hs, he⟩ := decode_some hd
  refine ⟨?_, hs⟩
  have he' : (xv x).toNat = ∑ i ∈ Finset.range 58, (xv x).toNat / 4 ^ i % 4 * 4 ^ i := he
  rw [← he']
  apply cellVal_inj hx (canon_lit _)
  rw [cellVal_lit]
  show cellVal x = BitVec.ofNat 128 (cellVal x).toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cellPairVal_cellOf128 (m : HashSig.Message) :
    cellPairVal (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)) = m := by
  apply BitVec.eq_of_toNat_eq
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [cellPairVal, BitVec.toNat_append, cellVal_cellOf128, cellVal_cellOf128, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, Nat.shiftLeft_eq, mul_comm, two_pow_mul_or (Nat.mod_lt _ (by positivity)),
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.mod_eq_of_lt (a := m.toNat / 2 ^ 128) (by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa using hm)]
  exact Nat.div_add_mod _ _

/-- **A layer's root exists only when its message digest decodes.** -/
theorem layerRoot_decode {P : HashSig.PublicParameter} {lay : LeanXmss.Layer} {key : LeanXmss.KeyIndex}
    {M : HashSig.HashInput} {part : LeanXmss.LayerSignature} {r : HashSig.Digest}
    (h : @LeanXmss.Verification.layerRootWithHash Id _ ⟨Node.keccakBits⟩ P lay key M part = some r) :
    ∃ enc, LeanXmss.Codeword.decode
      (@LeanXmss.Verification.messageDigestWithHash Id _ ⟨Node.keccakBits⟩ P lay key M part.randomizer) =
        some enc := by
  rw [layerRoot_id, otsLeaf_id] at h
  cases hd : LeanXmss.Codeword.decode
      (@LeanXmss.Verification.messageDigestWithHash Id _ ⟨Node.keccakBits⟩ P lay key M part.randomizer) with
  | none => rw [hd] at h; simp at h
  | some enc => exact ⟨enc, rfl⟩

/-- A layer's chains' starts as cells. -/
def xVals (part : LeanXmss.LayerSignature) (i : Nat) : E :=
  if h : i < 58 then cellOf128 (part.chainValues ⟨i, h⟩) else 0

/-- A layer's siblings as cells. -/
def xSibs (part : LeanXmss.LayerSignature) (l : Nat) : E :=
  if h : l < 16 then cellOf128 (part.authenticationPath ⟨l, h⟩) else 0

theorem xVals_canon (part : LeanXmss.LayerSignature) (i : Nat) : IsCanonical128 (xVals part i) := by
  unfold xVals; split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

theorem xSibs_canon (part : LeanXmss.LayerSignature) (l : Nat) : IsCanonical128 (xSibs part l) := by
  unfold xSibs; split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

/-- **The valuation holds the layer's signature** when it holds its randomizer, its starts and its
siblings. -/
theorem sPart_eq {layer b : Nat} {σ : Val} {part : LeanXmss.LayerSignature}
    (hr : σ (sRho layer b) = cellOf128 part.randomizer)
    (hs : ∀ i < 58, σ (sStart (sW layer b) σ (sA layer b + 6) (sA layer b + 6 + 70) i) = xVals part i)
    (hp : ∀ l < 16, sSibAt σ layer b l = xSibs part l) :
    sPart layer b σ = part := by
  cases part with
  | mk r cv pa =>
    simp only [sPart, LeanXmss.LayerSignature.mk.injEq]
    refine ⟨by rw [hr]; exact cellVal_cellOf128 _, funext fun i => ?_, funext fun l => ?_⟩
    · have hi : i.val < 58 := i.isLt
      rw [hs i.val hi]
      simp only [xVals, hi, ↓reduceDIte]
      exact cellVal_cellOf128 _
    · have hl : l.val < 16 := l.isLt
      rw [hp l.val hl]
      simp only [xSibs, hl, ↓reduceDIte]
      exact cellVal_cellOf128 _

/-! ## A layer after its digest -/

theorem sLeafCells_nb (layer b : Nat) :
    ∀ c ∈ (sLeafCells layer b).map KC.cell, KCb ((sCw layer b).2.1 + 2) c := by
  have b1 := sCw_snd_ge layer b
  have htips : (sCw layer b).2.2 = (List.range 58).map (sTip (sW layer b) (sA layer b + 6 + 70)) :=
    sCodewordT_tips _ _ _ _
  intro c hc
  simp only [sLeafCells, List.map_cons, List.mem_cons, htips, List.map_map, List.mem_map,
    List.mem_range, Function.comp_apply] at hc
  rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
  · exact ⟨66, by omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩
  · exact (sTip_nb layer b hi).mono' (by omega)

theorem sLeafK_ge {layer b : Nat} (hA : 103 ≤ sA layer b) : (sCw layer b).2.1 + 2 ≤ (sLeafK layer b).2.1 := by
  have := sCw_snd_ge layer b
  exact kMsg_le (show sLxPad + 5 ≤ (sCw layer b).2.1 + 2 by simp [sLxPad]; omega) (sLeafCells_nb layer b)

theorem sLeafPart_nb {layer b : Nat} (hidx : NBv (sA layer b) (sLxIdx layer b))
    (hd0 : NBv (sA layer b) (sD0 layer b)) (hA : 103 ≤ sA layer b) :
    NumBelow (sLeafK layer b).2.1 (Stmt.valsList (xStepAddrs (sLxIdx layer b) (sA layer b) ++ ((sCw layer b).1 ++
      ([cst (sCw layer b).2.1 (word (tw 2) 0), addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b)
        (.n (sCw layer b).2.1)] ++ (sLeafK layer b).1)))) := by
  have b1 := sCw_snd_ge layer b
  have b2 := sLeafK_ge hA
  have hseq : SeqOK (sCw layer b).2.1 [cst (sCw layer b).2.1 (word (tw 2) 0),
      addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b) (.n (sCw layer b).2.1)] ((sCw layer b).2.1 + 2) :=
    ⟨rfl, ⟨rfl, hidx.mono' (by omega), ⟨_, by omega, rfl⟩⟩, rfl⟩
  have hcw : NumBelow (sCw layer b).2.1 (Stmt.valsList (sCw layer b).1) := by
    rw [sCw_eq]
    exact sCodewordT_numBelow (sWc_shape hA) le_rfl (sWc_pw layer b hA) (hd0.mono' (by omega))
  simp only [valsList_append]
  exact ((xStepAddrs_seq hidx).numBelow.mono (by omega)).append ((hcw.mono (by omega)).append
    ((hseq.numBelow.mono b2).append (kMsg_numBelow (by simp [sLxPad]; omega) (sLeafCells_nb layer b))))

/-- **A layer after its digest completes**, given the path windows' completeness: its codeword at
the digest's digits `N`, its chains' starts `vals`, its siblings `sibs`; its root canonical, and on
any valuation agreeing below its end the starts and siblings read off are `vals` and `sibs`. -/
theorem sCore_complete (hW : LxWindowsC) {layer b : Nat} (hl : layer < 2) (hA : 103 ≤ sA layer b)
    (hm : MemOK rd 256) (σ : Val) (hpad : PadOK σ sLxPad) (hPc : IsCanonical128 (σ sLxPP))
    (htags : ∀ i < 58, IsCanonical128 (σ (sTag i))) (hpow : ∀ s < 13, σ (sPower s) = gen ^ s)
    {L : Nat} (hL : L < 2 ^ 32) (hhis : ∀ v < 4, σ (sHis v) = eOfNat (L >>> (8 * v)))
    (hwin : ∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w)))
    (hidx : NBv (sA layer b) (sLxIdx layer b)) (hidxc : IsCanonical128 (σ (sLxIdx layer b)))
    (hd0 : NBv (sA layer b) (sD0 layer b)) {N : Nat}
    (hN : σ (sD0 layer b) = lit (∑ i ∈ Finset.range 58, N / 4 ^ i % 4 * 4 ^ i))
    (hs : ∑ i ∈ Finset.range 58, N / 4 ^ i % 4 = 106) (vals : Nat → E) (hv : ∀ i, IsCanonical128 (vals i))
    (sibs : Nat → E) (hsc : ∀ l < 16, IsCanonical128 (sibs l)) :
    NumBelow (sWin1 layer b).2.1 (Stmt.valsList (xStepAddrs (sLxIdx layer b) (sA layer b) ++ ((sCw layer b).1 ++
      ([cst (sCw layer b).2.1 (word (tw 2) 0), addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b)
        (.n (sCw layer b).2.1)] ++ ((sLeafK layer b).1 ++ ((sWin0 layer b).1 ++ (sWin1 layer b).1)))))) ∧
    sA layer b + 83 ≤ (sWin1 layer b).2.1 ∧
    Completes C rd (sA layer b) (sWin1 layer b).2.1
      (xStepAddrs (sLxIdx layer b) (sA layer b) ++ ((sCw layer b).1 ++
        ([cst (sCw layer b).2.1 (word (tw 2) 0), addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b)
          (.n (sCw layer b).2.1)] ++ ((sLeafK layer b).1 ++ ((sWin0 layer b).1 ++ (sWin1 layer b).1))))) σ
      (fun σ' => IsCanonical128 (σ' (.n (sWin1 layer b).2.2)) ∧ ∀ σ'', AgreeBelow (sWin1 layer b).2.1 σ' σ'' →
        (∀ i < 58, σ'' (sStart (sW layer b) σ'' (sA layer b + 6) (sA layer b + 6 + 70) i) = vals i) ∧
        ∀ l < 16, sSibAt σ'' layer b l = sibs l) := by
  have b1 := sCw_snd_ge layer b
  have b2 := sLeafK_ge hA
  have hout : (sLeafK layer b).2.2 + 1 ≤ (sLeafK layer b).2.1 :=
    kMsg_out sLxPad ((sLeafCells layer b).map KC.cell) 960 false ((sCw layer b).2.1 + 2)
  obtain ⟨hwe, hwnb, hwc⟩ := hW C rd layer hl (.n (sLeafK layer b).2.2) (sLeafK layer b).2.1 L hm hL
    ⟨_, by omega, rfl⟩ (by omega)
  have hwe' : (sLeafK layer b).2.1 ≤ (sWin1 layer b).2.1 := hwe
  have hlnb := sLeafPart_nb hidx hd0 hA
  have hsplit : ∀ (A B C' D E F : List Stmt), A ++ (B ++ (C' ++ (D ++ (E ++ F)))) =
      (A ++ (B ++ (C' ++ D))) ++ (E ++ F) := fun _ _ _ _ _ _ => by simp
  refine ⟨?_, by
      show sA layer b + 83 ≤ (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) (.n (sLeafK layer b).2.2)
        (sLeafK layer b).2.1).2.2) (lxWindowT (2 * layer) (.n (sLeafK layer b).2.2) (sLeafK layer b).2.1).2.1).2.1
      omega, ?_⟩
  · rw [hsplit, valsList_append]
    exact (hlnb.mono hwe).append hwnb
  rw [hsplit]
  refine Completes.append (m := (sLeafK layer b).2.1) (by omega) hwe hlnb
    (sLeaf_complete (C := C) (rd := rd) hA hm σ hpad hPc htags hpow hidx hidxc hd0 hN hs vals hv)
    (fun σ4 he4 ⟨hc4, hk4⟩ => ?_)
  have hag4 : AgreeBelow (sA layer b) σ σ4 := fun k hk => he4.agree k hk
  have t : ∀ k < 88, σ4 (.n k) = σ (.n k) := fun k hk => hag4.apply ⟨k, by omega, rfl⟩
  have hc := hwc σ4 (hpad.congr (b := sA layer b) (by simp [sLxPad]; omega) hag4)
    (by rw [show sLxPP = V.n 66 from rfl, t 66 (by norm_num)]; exact hPc) hc4
    (fun v hv => by rw [show sHis v = V.n (67 + v) from rfl, t _ (by omega)]; exact hhis v hv)
    (fun w hw => by rw [show sWin w = V.n (71 + w) from rfl, t _ (by omega)]; exact hwin w hw)
    (fun s hs => by rw [show sPower s = V.n (75 + s) from rfl, t _ (by omega)]; exact hpow s hs) sibs hsc
  refine (hc.keep (Q := fun σ => (∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w))) ∧
      ∀ σ'', AgreeBelow (sLeafK layer b).2.1 σ σ'' →
      ∀ i < 58, σ'' (sStart (sW layer b) σ'' (sA layer b + 6) (sA layer b + 6 + 70) i) = vals i)
    (Q' := fun σ => (∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w))) ∧
      ∀ σ'', AgreeBelow (sLeafK layer b).2.1 σ σ'' →
      ∀ i < 58, σ'' (sStart (sW layer b) σ'' (sA layer b + 6) (sA layer b + 6 + 70) i) = vals i)
    ⟨fun w hw => by rw [show sWin w = V.n (71 + w) from rfl, t _ (by omega)]; exact hwin w hw,
      fun σ'' hag => (hk4 σ'' hag).2⟩
    (fun σ' he' ⟨hq1, hq2⟩ => ⟨fun w hw => by
        rw [show sWin w = V.n (71 + w) from rfl, he'.apply (Or.inl (by omega))]; exact hq1 w hw,
      fun σ'' hag => hq2 σ'' (fun k hk => (he'.agree k hk).trans (hag k hk))⟩)).mono le_rfl le_rfl
    (fun σ5 ⟨⟨hc5, hs5⟩, hw5, hq5⟩ => ⟨hc5, fun σ'' hag => ⟨hq5 σ'' (hag.mono (by omega)), fun l hl => ?_⟩⟩)
  have hkw : ∀ w < 4, sKw σ'' w = lxWin L w := fun w hw => by
    unfold sKw
    rw [show sWin w = V.n (71 + w) from rfl, hag.apply ⟨71 + w, by omega, rfl⟩]
    exact logG_eq (lxWin_lt L w) (by norm_num) (hw5 w hw)
  obtain ⟨h0, h1⟩ := hs5 σ'' hag
  unfold sSibAt
  split
  · rw [hkw _ (by omega)]
    exact h0 l (by assumption)
  · rw [hkw _ (by omega)]
    have := h1 (l - 8) (by omega)
    rwa [show 8 + (l - 8) = l by omega] at this

end
end LeanVM.Guest.B1.Sig
