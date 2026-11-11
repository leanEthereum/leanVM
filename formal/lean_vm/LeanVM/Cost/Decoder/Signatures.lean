module

public import LeanVM.Cost.Decoder.Kids
public import LeanVM.Guest.Fast.Sphincs
public import LeanVM.Guest.Fast.Whir

/-!
# The guest decoder's compiled chain: the signatures and the children's proofs

The readers of a callee's witness off its check's frame, restated off arrays (`Guest/Fast/`, each
proved equal to the deployed decoder's reader there at the tables built; leanXMSS's in
`Xmss.lean`, next in the chain): a leanSPHINCS signature off
`verify_sig_lean_sphincs`' and its three `sp_wots` frames (`sphincsSigOfA`, its positions off the
tables `SpTabs`), a child's proof off
`verify_sub`'s and the frame map keyed by index (`vsPiOfA`, `vsPiOfA_tabs`, the cursor's length
`cl` a parameter). Their tables (`XmssTabs`, `SpTabs`, `WhirTabs`: the lanes of `g^k`, the
chain starts, the selectors and path bases, `open_stacked`'s stream words and calls) are arrays the decoder's top level builds once
(`readerTabsC`, `Frames.lean`) and passes; consecutive cells are read by stepping the address
(`wordsFrom`), each query's windows once, their exponents off the lanes (`winLogsFrom`), each
query's position once (`oqQueryAt`), its siblings off its `walk_path` call's frame (`oqWalkArgs`),
the loop's frames at the next power of `g` (`oqItersFrom`). The compiled names stay the readers' (`xmssSigOfNC`, `sphincsSigOfNC`,
`vsPiOfNC`, `oqsOfNC`, …). Their records are encoded by their constructors (`Oq`, `OsCall`, the
tables).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.Fast

@[expose] public section

cost_enc LeanVM.Guest.B1.Oq
cost_enc LeanVM.Guest.Fast.OsCall
cost_enc LeanVM.Guest.B1.OqShape
cost_enc LeanVM.Guest.Fast.SpTabs
cost_enc LeanVM.Guest.Fast.WhirTabs

/-! ## The tables

The literals and helpers the readers call, each under a name of its own (stable across the
chain's reallocations of on-demand indices), compiled before their callers. -/

cost_compile gLanesC := gLanes
cost_compile spSelC := spSel
cost_compile spFirstC := spFirst
cost_compile spRestC := spRest
cost_compile spLastC := spLast
cost_compile spForsKidsC := spForsKids
cost_compile spForsBitsC := spForsBits
cost_compile spPathKidsC := spPathKids
cost_compile spPathBitsC := spPathBits
cost_compile osWordsTabC := osWordsTab
set_option maxRecDepth 100000 in
cost_compile osCallsTabC := osCallsTab
cost_compile tabAC := tabA
cost_compile offAtAC := offAtA
cost_compile idxBelowC measure fun _ l _ _ ↦ l.length := idxBelow
cost_compile logGTWithC := logGTWith
cost_compile spTabsC := spTabs
cost_compile whirTabsC := whirTabs

/-! ## A sibling, a chain's start -/

cost_compile sibNC := sibN
cost_compile cwCellC := cwCellA

/-! ## leanSPHINCS -/

cost_compile spForsBaseC := spForsBase
cost_compile forsOpeningAC := forsOpeningA
cost_compile spLayerBaseC := spLayerBase
cost_compile spCtrC := spCtr
cost_compile spEncC := spEnc
cost_compile spLeafC := spLeaf
cost_compile spA0C := spA0
cost_compile spA1C := spA1
cost_compile beWordAtC := LeanVM.Guest.B1.Sig.beWordAt
cost_compile layerAC := layerA
cost_compile sphincsSigOfNC := sphincsSigOfA
cost_compile spWotsArgsC := spWotsArgs
cost_compile spWotsRetsC := spWotsRets

/-! ## A child's proof

A query's result (`oqRes`) at the final level is `novel_eval`'s next free value, which `oqNovel`
computes beside its statements (no machine encoding): `oqResN` computes it alone (`nvEnd`), and
the readers compile `oqRes` through it (`oqRes_eq_oqResN`). -/

/-- The next free value after `c` levels of `novel_eval` on `n` values from `k` (`nvLevelsT`'s). -/
def nvEnd : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k
  | c + 1, n, k => nvEnd c ((n + 1) / 2) (k + n)

theorem nvLevelT_end (w : LeanVM.Guest.Core.V) : ∀ (ins : List ℕ) (k : ℕ),
    (nvLevelT w ins k).2.2 = k + ins.length ∧
      (nvLevelT w ins k).2.1.length = (ins.length + 1) / 2
  | lo :: hi :: rest, k => by
    obtain ⟨h1, h2⟩ := nvLevelT_end w rest (k + 2)
    simp only [nvLevelT, List.length_cons, h1, h2]
    omega
  | [_], _ => by simp [nvLevelT]
  | [], _ => by simp [nvLevelT]

theorem nvLevelsT_end (ws : ℕ → ℕ) : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ),
    (nvLevelsT ws c i ins k).2.2 = nvEnd c ins.length k
  | 0, _, _, _ => rfl
  | c + 1, i, ins, k => by
    simp only [nvLevelsT, nvEnd]
    rw [nvLevelsT_end ws c, (nvLevelT_end _ _ _).2, (nvLevelT_end _ _ _).1]

/-- A query's result (`oqRes`), `novel_eval`'s next free value counted alone. -/
def oqResN (s : Oq) (b : ℕ) (emit : Bool) : ℕ :=
  if s.final = 1 then
    nvEnd (s.hsBits - 1) (s.nHs / 2) (oqVal s (oqCh s b emit) + 2 + 3 * s.mu + 4 * (s.nHs / 2))
  else oqVal s (oqCh s b emit)

theorem oqRes_eq_oqResN (s : Oq) (b : ℕ) (emit : Bool) : oqRes s b emit = oqResN s b emit := by
  unfold oqRes oqResN oqNovel
  split_ifs
  · rw [nvLevelsT_end, List.length_map, List.length_range]
  · rfl

cost_rewrite oqRes_eq_oqResN

/-- The shapes of `openingQueriesLoops`, without their names (strings have no machine encoding). -/
def oqShapeTab : List OqShape :=
  [⟨0, 1, 6, 32, 17, 8, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩,
    ⟨0, 1, 6, 32, 18, 8, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩,
    ⟨0, 1, 6, 32, 19, 8, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩,
    ⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩,
    ⟨0, 1, 6, 32, 21, 8, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩,
    ⟨0, 1, 6, 32, 22, 8, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩,
    ⟨0, 1, 6, 32, 23, 8, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩,
    ⟨1, 1, 6, 32, 18, 7, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩,
    ⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩,
    ⟨1, 1, 6, 32, 20, 7, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩,
    ⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩,
    ⟨1, 1, 6, 32, 22, 7, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩,
    ⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩,
    ⟨1, 1, 6, 32, 24, 7, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 20, 4, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩,
    ⟨0, 0, 4, 16, 16, 5, 4, 1131, 20, 5, 1, [1, 6, 360, 18245760]⟩,
    ⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩,
    ⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩,
    ⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩,
    ⟨0, 0, 4, 16, 19, 4, 4, 1464, 20, 5, 1, [1, 6, 360, 18245760]⟩,
    ⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩,
    ⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩, ⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 17, 5, 4, 1677, 20, 5, 1, [1, 6, 360, 18245760]⟩,
    ⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩,
    ⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 18, 4, 2, 1846, 8, 3, 1, [1, 6]⟩,
    ⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩,
    ⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 20, 4, 4, 2010, 20, 5, 1, [1, 6, 360, 18245760]⟩,
    ⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩,
    ⟨1, 1, 6, 32, 26, 6, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩,
    ⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩, ⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩]

theorem oqShapeTab_eq : openingQueriesLoops.map (·.2.2) = oqShapeTab := rfl

theorem oqShapeAt_eq_tab (i : ℕ) :
    LeanVM.Guest.B1.Whir.oqShapeAt i = oqShapeTab.getD i LeanVM.Guest.B1.Whir.oqShapeZero := by
  rw [LeanVM.Guest.B1.Whir.oqShapeAt, List.getD_eq_getElem?_getD, ← oqShapeTab_eq,
    List.getElem?_map]

cost_rewrite oqShapeAt_eq_tab

cost_compile oqRowC := oqRow
cost_compile digestOfCellsWC := LeanVM.Guest.B1.digestOfCells
cost_compile oqSibsOfC := oqSibsOf
cost_compile OqIC := Oq.I
cost_compile OqNcellsC := Oq.ncells
cost_compile oqK1C := oqK1
cost_compile oqKLC := oqKL
cost_compile OqBC := Oq.B
cost_compile OqChainLenC := Oq.chainLen
cost_compile oqChC := oqCh
cost_compile oqRKC measure fun _ _ j ↦ j := oqRK
cost_compile oqValC := oqVal
cost_compile nvEndC measure fun c _ _ ↦ c := nvEnd
cost_compile oqResNC := oqResN
cost_compile oqEndC := oqEnd
cost_compile oqE1C := oqE1
cost_compile oqBsC := oqBs
cost_compile oqOutC := oqOut
cost_compile wpChC := wpCh
cost_compile oqWalkArgsC := oqWalkArgs
cost_compile oqLoopArgsC := oqLoopArgs
cost_compile memReadC := memRead
cost_compile capSibC := LeanVM.Guest.B1.Whir.capSib
cost_compile capSibsOfC := LeanVM.Guest.B1.Whir.capSibsOf
cost_compile toOpeningC := LeanVM.Guest.B1.Whir.toOpening
cost_compile vsOsArgsC := LeanVM.Guest.B1.VerifySub.vsOsArgs
cost_compile vsOsRetsC := LeanVM.Guest.B1.VerifySub.vsOsRets
cost_compile wordsFromC measure fun _ _ n ↦ n := wordsFrom
cost_compile winLogsFromC measure fun _ _ _ n ↦ n := winLogsFrom
cost_compile qwNpC := qwNp
cost_compile qwNC := qwN
cost_compile qwWinC := qwWin
cost_compile qwAtC := qwAt
cost_compile winBitC := winBit
cost_compile bitsBC measure fun l ↦ l.length := bitsB
cost_compile winPosAtC := winPosAt
cost_compile winPosOfWC := winPosOfW
cost_compile oqQueryAtC := oqQueryAt
cost_compile oqQueryAC := oqQueryA
cost_compile oqIterAC := oqIterA
cost_compile oqItersFromC measure fun _ _ _ _ _ _ _ n _ ↦ n := oqItersFrom
cost_compile oqsOfNC := oqsOfA
set_option maxRecDepth 100000 in
cost_compile oqShapeTabC := oqShapeTab
cost_compile oqShapeZeroC := LeanVM.Guest.B1.Whir.oqShapeZero
cost_compile OqShapeOqC := OqShape.oq
cost_compile OsCallShapeC := OsCall.shape
cost_compile levelOsAtC := levelOsAt
cost_compile levelOsNC := levelOsA
cost_compile vsPiOfAtC := vsPiOfAt
cost_compile vsPiOfMC := vsPiOfM
cost_compile vsPiOfNC := vsPiOfA

end

end LeanVM.Cost.Decoder
