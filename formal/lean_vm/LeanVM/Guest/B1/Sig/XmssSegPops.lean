/-
  LeanVM.Guest.B1.Sig.XmssSegPops

  The witness-stream entries leanXMSS's check inline in `main_loop2` pops: on every valuation holding the values its completeness hints (`XSegVals`), the leaf index's shifts and windows, then per layer the randomizer, the digit words, the chains' starts and the siblings (`xSegPops`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegComplete
public import LeanVM.Guest.B1.Sig.XmssWinPops

/-!
# The check's pops

* `sCodewordT_pops`: the codeword pops its digit words, then each group's chains' starts in the arm its digits take;
* `sCore_pops`: a layer after its digest pops its digit words, its `58` starts and its `16` siblings (`corePops`);
* `sPrologue_pops`, `sDigest0_pops`, `sDigest1_pops`: the shifts and windows, each randomizer;
* `xSeg_pops`, `verify_lean_xmss_complete_pops_of`: the check pops `xSegPops` on every valuation agreeing below its end with the completing one.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## The codeword -/

theorem lxChains_flatMap {α : Type} (F : Nat → α) :
    (List.range 15).flatMap (fun q => (List.range (lxN q)).map fun t => F (4 * q + t)) =
      (List.range 58).map F := by
  have h : (List.range 15).flatMap (fun q => (List.range (lxN q)).map fun t => 4 * q + t) = List.range 58 := by
    decide
  rw [← h, List.map_flatMap]
  simp only [List.map_map, Function.comp_def]

/-- **The codeword pops its digit words, then its chains' starts** in the arms its digits `K` take. -/
theorem sCodewordT_pops {W : WotsT} (hW : StepQuiet W) (target : E) (d0 : V) (dg : Nat) {σ : Val}
    {K : Nat → Nat} (hK : ∀ p < 15, K p < 4 ^ lxN p)
    (hx : ∀ q < 15, σ (.n (dg + q)) = ofK (addressOfIndex (K q))) :
    FallPops rd σ (sCodewordT W target d0 dg).1
      (("lx_digits", (List.range 15).map fun q => ofK (addressOfIndex (K q))) ::
        (List.range 15).flatMap fun q => (List.range (lxN q)).map fun t =>
          startPop (σ (sgPos W (dg + 70) K q t))) := by
  rw [sCodewordT_fst]
  have e : (runV dg 15).map σ = (List.range 15).map fun q => ofK (addressOfIndex (K q)) := by
    rw [runV, List.map_map]
    exact List.map_congr_left fun q hq => hx q (List.mem_range.mp hq)
  have hh : FallPops rd σ [hintW "lx_digits" (runV dg 15)]
      [("lx_digits", (List.range 15).map fun q => ofK (addressOfIndex (K q)))] := by
    rw [← e]
    exact FallPops.atom _
  have hm : FallPops rd σ ((List.range 15).map fun q => sgMatch W dg (dg + 70) q)
      ((List.range 15).flatMap fun q => (List.range (lxN q)).map fun t => startPop (σ (sgPos W (dg + 70) K q t))) :=
    fallPops_map _ _ _ fun q hq => by
      have hq' := List.mem_range.mp hq
      have h256 : 4 ^ lxN q ≤ 256 := by unfold lxN; split <;> norm_num
      obtain ⟨hl, he⟩ := sGroupArms_getElem W (p := q) (by omega) (hK q hq') (sgState W (dg + 70) q).1
        (sgState W (dg + 70) q).2.1 (sgState W (dg + 70) q).2.2
      refine FallPops.match_ hl (by have := hK q hq'; omega) (hx q hq') ?_
      rw [he]
      exact armT_pops hW σ _ _ _ _ _ _ _ _ _ _
  have hc : quiet (sDigitChecks dg) = true := quiet_flatMap _ (fun _ => rfl) _
  -- A generic shape: `simp` on the instantiated pops leaves the kernel unfolding the arms.
  have e : ∀ {α : Type} (x : α) (F : List α), [x] ++ ([] ++ ([] ++ (F ++ []))) = x :: F := by
    intros; simp only [List.nil_append, List.append_nil, List.singleton_append]
  exact FallPops.congr_pops (hh.append ((fallPops_quiet σ hc).append ((fallPops_quiet σ rfl).append
    (hm.append (fallPops_quiet σ rfl))))) (e _ _)

/-! ## A layer after its digest -/

/-- A layer's pops after its digest: its digit words (the groups of `N`), its chains' starts `vals`, its siblings `sibs`. -/
def corePops (N : Nat) (vals sibs : Nat → E) : List Pop :=
  (("lx_digits", (List.range 15).map fun q => ofK (addressOfIndex (lxK N q))) ::
    (List.range 58).map fun i => startPop (vals i)) ++ lxPathPops 16 sibs

theorem sW_quiet (layer b : Nat) : StepQuiet (sW layer b) := fun _ _ _ _ _ => rfl

/-- **A layer after its digest pops its digit words, its starts and its siblings**, from any valuation holding them. -/
theorem sCore_pops {layer b : Nat} (hl : layer < 2) {σ : Val} {L N : Nat}
    (hwin : ∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w)))
    (hd : ∀ q < 15, σ (.n (sA layer b + 6 + q)) = ofK (addressOfIndex (lxK N q))) {vals sibs : Nat → E}
    (hs : ∀ i < 58, σ (sStart (sW layer b) σ (sA layer b + 6) (sA layer b + 6 + 70) i) = vals i)
    (hp : ∀ l < 16, sSibAt σ layer b l = sibs l) :
    FallPops rd σ (sCore layer b) (corePops N vals sibs) := by
  have hcw := sCodewordT_pops (rd := rd) (sW_quiet layer b) xTarget (sD0 layer b) (sA layer b + 6)
    (fun p _ => lxK_lt N p) hd
  have hst : ((List.range 15).flatMap fun q => (List.range (lxN q)).map fun t =>
      startPop (σ (sgPos (sW layer b) (sA layer b + 6 + 70) (lxK N) q t))) =
      (List.range 58).map fun i => startPop (vals i) := by
    rw [← lxChains_flatMap]
    refine List.flatMap_congr fun q hq => List.map_congr_left fun t ht => ?_
    have hq' := List.mem_range.mp hq
    have ht' := List.mem_range.mp ht
    have ht4 : t < 4 := lt_of_lt_of_le ht' (lxN_le q)
    have hi : 4 * q + t < 58 := lt_of_lt_of_le (by omega) (lxN_fit (p := q) (by omega))
    rw [← hs _ hi, sStart_eq_sgPos (sW layer b) σ (fun p _ => lxK_lt N p) hd hi,
      show (4 * q + t) / 4 = q by omega, show (4 * q + t) % 4 = t by omega]
  rw [hst, show sCodewordT (sW layer b) xTarget (sD0 layer b) (sA layer b + 6) = sCw layer b from rfl] at hcw
  have hkw : ∀ w < 4, sKw σ w = lxWin L w := fun w hw => logG_eq (lxWin_lt L w) (by norm_num) (hwin w hw)
  have hpath := lxWindows_pops (rd := rd) hl (.n (sLeafK layer b).2.2) (sLeafK layer b).2.1 hwin (sibs := sibs)
    (fun r hr => by
      have := hp r (by omega)
      unfold sSibAt at this
      simp only [hr, ↓reduceIte, hkw _ (show 2 * layer < 4 by omega)] at this
      exact this)
    (fun r hr => by
      have := hp (8 + r) (by omega)
      unfold sSibAt at this
      have h8 : ¬ 8 + r < 8 := by omega
      simp only [h8, ↓reduceIte, hkw _ (show 2 * layer + 1 < 4 by omega), show 8 + r - 8 = r by omega] at this
      exact this)
  rw [show lxWindowT (2 * layer) (.n (sLeafK layer b).2.2) (sLeafK layer b).2.1 = sWin0 layer b from rfl,
    show lxWindowT (2 * layer + 1) (.n (sWin0 layer b).2.2) (sWin0 layer b).2.1 = sWin1 layer b from rfl] at hpath
  have ha : quiet (xStepAddrs (sLxIdx layer b) (sA layer b)) = true := quiet_flatMap _ (fun _ => rfl) _
  have hm : quiet [cst (sCw layer b).2.1 (word (tw 2) 0), addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b)
      (.n (sCw layer b).2.1)] = true := rfl
  have hk : quiet (sLeafK layer b).1 = true := kMsg_quiet _ _ _ _ _ _ _
  unfold sCore
  exact FallPops.congr_pops ((fallPops_quiet σ ha).append (hcw.append ((fallPops_quiet σ hm).append
    ((fallPops_quiet σ hk).append hpath)))) (by simp only [corePops, List.nil_append, List.cons_append])

/-! ## The prologue and the digests -/

theorem sPrologue_pops {σ : Val} {his win : Nat → E} (hh : ∀ v < 4, σ (sHis v) = his v)
    (hw : ∀ w < 4, σ (sWin w) = win w) :
    FallPops rd σ sPrologue [("lx_index", (List.range 4).map his), ("lx_windows", (List.range 4).map win)] := by
  have e1 : (runV 67 4).map σ = (List.range 4).map his := by
    rw [runV, List.map_map]; exact List.map_congr_left fun v hv => hh v (List.mem_range.mp hv)
  have e2 : (runV 71 4).map σ = (List.range 4).map win := by
    rw [runV, List.map_map]; exact List.map_congr_left fun v hv => hw v (List.mem_range.mp hv)
  have h1 : FallPops rd σ [hintW "lx_index" (runV 67 4)] [("lx_index", (List.range 4).map his)] := by
    rw [← e1]; exact FallPops.atom _
  have h2 : FallPops rd σ [hintW "lx_windows" (runV 71 4)] [("lx_windows", (List.range 4).map win)] := by
    rw [← e2]; exact FallPops.atom _
  have hc : FallPops rd σ ((List.range 13).map (fun s => cst (75 + s) (word (2 ^ s) 0))) [] :=
    fallPops_quiet σ rfl
  rw [sPrologue_split]
  exact FallPops.congr_pops ((h1.append h2).append hc).cons_atom rfl

theorem sDigest0_pops (σ : Val) : FallPops rd σ (sDigest0 88) [("randomizer", [σ (.n 88)])] := by
  have h : FallPops rd σ [hintW "randomizer" [.n 88]] [("randomizer", [σ (.n 88)])] := FallPops.atom _
  rw [sDigest0_split]
  exact FallPops.congr_pops (h.append (fallPops_quiet σ rfl)) rfl

theorem sDigest1_pops (σ : Val) (b : Nat) (root : V) :
    FallPops rd σ (sDigest1 b root) [("randomizer", [σ (.n (b + 2))])] := by
  have h : FallPops rd σ [hintW "randomizer" [.n (b + 2)]] [("randomizer", [σ (.n (b + 2))])] := FallPops.atom _
  rw [sDigest1_split]
  exact FallPops.congr_pops ((fallPops_quiet σ rfl).append (h.append (fallPops_quiet σ rfl))) rfl

/-! ## The check -/

/-- A layer's pops: its randomizer, then its pops after its digest. -/
def xLayerPops (part : LeanXmss.LayerSignature) (N : Nat) : List Pop :=
  ("randomizer", [cellOf128 part.randomizer]) :: corePops N (xVals part) (xSibs part)

/-- **The check's pops** for the signature `sig` of `m` under `pk`: the leaf index's shifts and windows, then each layer's, bottom first. -/
def xSegPops (pk : HashSig.PublicKey) (m : HashSig.Message) (sig : LeanXmss.Signature) : List Pop :=
  [("lx_index", (List.range 4).map fun v => eOfNat (sig.leafIndex.val >>> (8 * v))),
    ("lx_windows", (List.range 4).map fun w => ofK (addressOfIndex (lxWin sig.leafIndex.val w)))] ++
    (xLayerPops (sig.layers LeanXmss.bottomLayer) (xN0 pk m sig) ++
      xLayerPops (sig.layers LeanXmss.topLayer) (xN1 pk m sig))

/-- **The check pops `xSegPops`** on a valuation holding the values it hints. -/
theorem xSeg_pops {pk : HashSig.PublicKey} {m : HashSig.Message} {sig : LeanXmss.Signature} {σ : Val}
    (h : XSegVals pk m sig σ) : FallPops rd σ xSeg (xSegPops pk m sig) := by
  obtain ⟨hh, hw, ⟨r0, d0, s0, p0⟩, ⟨r1, d1, s1, p1⟩⟩ := h
  rw [xSeg_split]
  have hd0 := sDigest0_pops (rd := rd) σ
  rw [show σ (.n 88) = _ from r0] at hd0
  have hd1 := sDigest1_pops (rd := rd) σ 62605 (.n 50364)
  rw [show σ (.n (62605 + 2)) = _ from r1] at hd1
  have ht : quiet [loadS (.n 120763) sSigner 0, .atom (.assertEq (.n 112857) (.n 120763))] = true := rfl
  exact FallPops.congr_pops ((sPrologue_pops (rd := rd) hh hw).append (hd0.append
    ((sCore_pops (rd := rd) (layer := 0) (b := 88) (by norm_num) hw d0 s0 p0).append (hd1.append
      ((sCore_pops (rd := rd) (layer := 1) (b := 62605) (by norm_num) hw d1 s1 p1).append
        (fallPops_quiet σ ht)))))) (by
    simp only [xSegPops, xLayerPops, List.cons_append, List.nil_append, List.append_nil])

/-- **`verify_lean_xmss` completes popping `xSegPops`**, given the path windows' completeness: on every valuation agreeing below its end with the completing one. -/
theorem verify_lean_xmss_complete_pops_of (hW : LxWindowsC) (C : CallRel) (rd : Reader) (σ : Val)
    (pk : HashSig.PublicKey) (m : HashSig.Message) (sig : LeanXmss.Signature) (hm : MemOK rd 256)
    (htags : LxTagsHold (fun j => σ (sTagParam j)))
    (hat : ClaimAt rd (σ sSigner) (cellOf128 pk.root) (cellOf128 pk.parameter)
      (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)))
    (hv : LeanXmss.verifyWithKeccak pk m sig = true) :
    Completes C rd 66 120764 xSeg σ
      (fun σ' => ∀ σ'', AgreeBelow 120764 σ' σ'' → FallPops rd σ'' xSeg (xSegPops pk m sig)) :=
  (verify_lean_xmss_complete_vals_of hW C rd σ pk m sig hm htags hat hv).mono le_rfl le_rfl
    fun _ h σ'' hag => xSeg_pops (h σ'' hag)

end
end LeanVM.Guest.B1.Sig
