module

public import Quantum.StdModel.Qrom.Tcr2
public import Quantum.StdModel.Qrom.XmssTcr

@[expose] public section

/-!
# The leanXMSS SM-TCR-C bound of B4, with free answers and re-reads

`Quantum.StdModel.Qrom.Tcr2.probAvg_smTcrIn_slRed_le_free` at leanXMSS's restricted SM-TCR-C game
`smTcrIn romWorld xmssTcrC xmssTcrD TcrInKind` played by B4 (`tcrRed`). Every in-kind `G`-cell
is the cell of a leaf or node slot (`isG_tcr_treeSlot`), so B4's own reads of `G`-cells are at
most its queries at the tree slots (`tcrRed_onChallenge`): none in its setup (the leaves and
nodes are the challenger's answers, free) and its handler (it reads them back from its
transcript), `293` in its output. With the judge's read, `n = 294`:
`probAvg ≤ (q + 294)² · gradeEta (2^128)` (`probAvg_smTcrIn_tcrRed_le`).
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common
open Quantum.StdModel.Qrom.Tcr (GCell IsG)
open Quantum.StdModel.Qrom.Tcr2 (gWR probAvg_smTcrIn_slRed_le_free)

-- A bound on a whole tree is otherwise unfolded by `whnf`.
attribute [local irreducible] QueryCostAtMost Gen.treeNode grind preTrees sequenceFin walkChain
  foldPath

/-- `card_truncateHash_fiber_le` with the classical decision of the fibers. -/
theorem card_truncateHash_fiber_le_cl (o : Digest) :
    (@Finset.filter HashOutput (fun y ↦ xmssTcrC.trunc y = o)
      (fun _ ↦ Classical.propDecidable _) Finset.univ).card ≤ 2 ^ 128 := by
  convert card_truncateHash_fiber_le o

/-- **An in-kind `G`-cell names a leaf or node slot.** -/
theorem isG_tcr_treeSlot {z : Qrom.HashDomain} (h : IsG xmssTcrC TcrInKind z) :
    (Qrom.Xmss.slotOf z).any treeSlots = true := by
  obtain ⟨P, ⟨s, hs⟩, l, m, ht, hz⟩ := h
  obtain ⟨d, hd⟩ := xmssTcrC_layout_of_inKind P ht m
  rw [hd, Qrom.Xmss.encodeInput_slotInput] at hz
  cases hz
  rw [Qrom.Xmss.slotOf_cell P hs d]
  change SlotInKind l s at ht
  cases l <;> cases s <;> first | exact False.elim ht | rfl

/-- B4's own reads of `G`-cells are among its queries at the tree slots. -/
theorem gWR_le_slotCost (t : (romWorld.Oracles + TcrPorts).Domain) :
    gWR xmssTcrC TcrInKind (R' := TcrPorts) t ≤ sumCost (slotCost treeSlots) t := by
  rcases t with (n | z) | q
  · exact le_rfl
  · simp only [gWR, sumCost, slotCost]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (isG_tcr_treeSlot h1) h2
    · exact Nat.zero_le _
    · exact le_rfl
  · exact le_rfl

/-- **The QROM bound of leanXMSS's restricted SM-TCR-C game played by B4**, the challenger's
answers and B4's re-reads of its targets free: with `q` adversary calls,
`probAvg ≤ (q + 294)² (2 √(2^128/N) + √((2^128 + 2)/N))²`, `N = 2^256`. -/
theorem probAvg_smTcrIn_tcrRed_le
    (A : SufAdversary romWorld PublicKey SigningRequest (Option Signature) Forgery) {q : ℕ}
    (hq : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q) :
    romWorld.probAvg ((smTcrIn romWorld xmssTcrC xmssTcrD TcrInKind).game (tcrRed romWorld A)) ≤
      ((q + 294 : ℕ) : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (Qrom.gradeEta HashOutput (2 ^ 128)) :=
  probAvg_smTcrIn_slRed_le_free xmss_gSep xmssTcrC_layout_injective xmssTcrD_tweakSeparated
    xmssTcrC_lengthLe card_truncateHash_fiber_le_cl (fun _ ↦ tcrPre romWorld)
    (fun _ d ↦ A ⟨d.root, d.P⟩) (fun _ d ↦ (d, [])) (fun _ ↦ tcrSigner romWorld)
    (fun _ ↦ tcrPost romWorld) (fun _ ↦ chalFirst_tcrPre) (fun _ ↦ cost_tcrSigner_chalW)
    (fun _ ↦ cost_tcrPost_chalW) (fun _ ↦ hq _) 0 293
    (tcrRed_onChallenge.1.mono_weight gWR_le_slotCost)
    (fun s r ↦ (tcrRed_onChallenge.2.1 s r).mono_weight gWR_le_slotCost)
    (fun d F s ↦ (tcrRed_onChallenge.2.2 d F s).mono_weight gWR_le_slotCost)

end Quantum.StdModel.Xmss

end
