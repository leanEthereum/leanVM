/-
  LeanVM.Guest.B1.Stack.TermPure

  The stacked claims' basis at the opening point, as the guest builds it.
-/

module

public import LeanVM.Guest.B1.Stack.TermLayout

/-!
# The basis, as the guest builds it

`basisPure`: the terminal's value in the guest's terms, the blocks' selectors `selW` (`eqAbove`),
the slots' `eq` weights `kernW`, the ring weight per piece (`ringPure`), the memory term, the sent
columns (`sentPure`, in `SENT_TARGET`'s order without the lanes no block holds), the public input's
two claims, the Keccak output claim and the out-of-domain claim, batched by Horner in `λ`.
`stackedBasis_pure`: in a layout `buildLayout` returns, with the link's pieces and columns as
`StackCtxAt` has them, the stacked claims exist and their basis is `basisPure`.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The guest's terms -/

/-- Block `b`'s placement. -/
def blockP (layout : Layout) (b : ℕ) : Placement := (layout.placements.getD (blockColumn b) none).getD default

/-- Block `b`'s selector at `x`. -/
def selW (layout : Layout) (x : List E) (b : ℕ) : E := (blockP layout b).eqAbove x

/-- Table `t`'s height. -/
def hgt (layout : Layout) (t : ℕ) : ℕ := layout.tableLogHeights.getD t 0

/-- Slot `s`'s `eq` weight at the six coordinates above `KECCAK`'s height. -/
def kernW (layout : Layout) (x : List E) (s : ℕ) : E := (eqKernel ((x.drop (hgt layout 5)).take 6)).getD s 0

/-- A column of kind `k`'s weight above its window. -/
def maskW (layout : Layout) (x : List E) (k : ℕ) : E :=
  if k < 52 then selW layout x k else kernW layout x (k - 52) * selW layout x 2

/-- A ring piece's term at the point `pt`, above weight `above` and scale `s`. -/
def ringT (cs x pt : List E) (above s : E) : E :=
  ∑ k ∈ Finset.range kBits, cs.getD k 0 * eqEval (pt.map (· ^ 2 ^ k)) (x.take pt.length) * (above * s ^ 2 ^ k)

/-- The merged ring claim's weight: the Keccak input claim's piece, then the pointers'. -/
def ringPure (layout : Layout) (x chi qPoint kIn f g : List E) (rho : E) : E :=
  ringT (ringCoefficients f g) x kIn (selW layout x 2) 1 +
    ∑ q ∈ Finset.range 33, ringT (ringCoefficients f g) x (chi.take (hgt layout (ptrTab.getD q 0)))
      (maskW layout x (ptrKinds.getD q 0)) (rho * (eqKernel qPoint).getD q 0)

/-- A sent column's weight, by its kind. -/
def sentPure (layout : Layout) (x chi : List E) (k : ℕ) : E :=
  if k < 52 then
    eqEval (chi.take (blockP layout k).variableCount) (x.take (blockP layout k).variableCount) * selW layout x k
  else eqEval (chi.take (hgt layout 5)) (x.take (hgt layout 5)) * selW layout x 2 * kernW layout x (k - 52)

/-- The sent columns' kinds with a placement. -/
def sentList : List ℕ := sentKinds.filter (· ≠ 1000)

/-- Horner in `λ`: `a_0 + λ (a_1 + λ (…))`. -/
def hornerL (lam : E) : List E → E
  | [] => 0
  | a :: l => a + lam * hornerL lam l

/-- The claims after the memory term: the sent columns, the public input's two, the Keccak output,
the out-of-domain claim. -/
def tailPure (layout : Layout) (x chi kOut z : List E) (rm : E) : List E :=
  sentList.map (sentPure layout x chi) ++
    [eqEval (rm :: List.replicate (layout.logMemory - 1) 0) (x.take layout.logMemory) * selW layout x 0,
      eqEval (rm :: List.replicate (layout.logMemory - 1) 0) (x.take layout.logMemory) * selW layout x 1,
      eqEval kOut (x.take (hgt layout 5 + 6)) * selW layout x 2, eqEval z x]

/-- **The basis, as the guest builds it.** -/
def basisPure (layout : Layout) (link : LinkEnd) (x chi r qPoint kIn kOut f g z : List E) (rho lam rm : E) : E :=
  ringPure layout x chi qPoint kIn f g rho + lam * (eqEval (r.take layout.logMemory) (x.take layout.logMemory) *
    (link.memoryScales.1 * selW layout x 0 + link.memoryScales.2 * selW layout x 1) +
    lam * hornerL lam (tailPure layout x chi kOut z rm))

/-! ## Facts -/

theorem dot_powers_hornerL (lam : E) : ∀ l : List E, dot (powers lam l.length) l = hornerL lam l
  | [] => by simp [dot, powers, powersFrom, hornerL]
  | a :: l => by rw [List.length_cons, dot_powers_cons, dot_powers_hornerL lam l, hornerL]

theorem ringCoefficients_length (f g : List E) (hf : f.length = 8) (hg : g.length = 8) :
    (ringCoefficients f g).length = kBits := by
  have h : ∀ (fl acc pw : List E), (fl.foldl (fun (acc : List E × List E) fP ↦
      (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8 · 1))) (acc, pw)).1.length =
      acc.length + fl.length * pw.length := by
    intro fl
    induction fl with
    | nil => simp
    | cons fp fl ih =>
      intro acc pw
      rw [List.foldl_cons, ih, List.length_append, List.length_map, List.length_map, List.length_cons]
      ring
  unfold ringCoefficients
  rw [h, hf, hg]
  rfl

theorem buildLayout_lm {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) : 1 ≤ layout.logMemory := by
  have hlm := (buildLayout_some h).1
  unfold buildLayout at h
  split at h
  · cases h
  · split_ifs at h with hc
    rw [hlm]
    exact hc.1

theorem blockKap_eq (layout : Layout) :
    blockKap layout 0 = layout.logMemory ∧ blockKap layout 1 = layout.logMemory ∧
      blockKap layout 2 = hgt layout 5 + 6 := by
  have e : ∀ b < 52, blockKap layout b = csKap (kvOf layout.logMemory layout.tableLogHeights) (grpOf b) :=
    fun b hb ↦ blockKappa _ _ hb
  have g0 : grpOf 0 = 0 ∧ grpOf 1 = 0 ∧ grpOf 2 = 1 := by decide
  have s0 : (csG 0).src = 1 ∧ (csG 0).adj = 0 ∧ (csG 1).src = 7 ∧ (csG 1).adj = 6 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [e 0 (by decide), g0.1, csKap, s0.1, s0.2.1]; simp [kvOf]
  · rw [e 1 (by decide), g0.2.1, csKap, s0.1, s0.2.1]; simp [kvOf]
  · rw [e 2 (by decide), g0.2.2, csKap, s0.2.2.1, s0.2.2.2]; simp [kvOf, hgt]

/-- A block's placement, with its window inside the stack. -/
theorem block_placed {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) {b : ℕ} (hb : b < 52) :
    layout.placements.getD (blockColumn b) none = some (blockP layout b) ∧
      (blockP layout b).variableCount = blockKap layout b ∧
      2 ^ (blockP layout b).variableCount ∣ (blockP layout b).index ∧
      (blockP layout b).variableCount ≤ layout.stackLog := by
  obtain ⟨p, hp, hvc, -, hal, hin⟩ := layout_block hbl hb
  have hP : blockP layout b = p := by rw [blockP, hp]; rfl
  rw [hP]
  refine ⟨hp, hvc, hal, ?_⟩
  have : 2 ^ p.variableCount ≤ 2 ^ layout.stackLog := le_trans (Nat.le_add_left _ _) hin
  exact (Nat.pow_le_pow_iff_right (by decide)).1 this

/-- **A slot column's `eqAbove`.** -/
theorem slot_mask {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) {x : List E} (hx : x.length = layout.stackLog)
    {col s : ℕ} (hc : col < colSrc.length) (hsrc : colSrc.getD col (0, 0) = (2 + 5, 0))
    (hs : qkeccakSlot col = some s) (hs64 : s < 64) :
    ∃ P : Placement, layout.placements.getD col none = some P ∧ P.variableCount = hgt layout 5 ∧
      P.eqAbove x = kernW layout x s * selW layout x 2 ∧ hgt layout 5 + 6 ≤ x.length := by
  obtain ⟨p2, hp2, hcol⟩ := layout_slot hbl hc hs
  rw [layout_kappa _ _ hc hsrc] at hcol
  obtain ⟨hb2, hvc2, hal2, hin2⟩ := block_placed hbl (b := 2) (by decide)
  rw [block2_column, hp2, Option.some.injEq] at hb2
  rw [← hb2] at hvc2 hal2 hin2
  rw [(blockKap_eq layout).2.2] at hvc2
  rw [hvc2] at hal2 hin2
  refine ⟨_, hcol, rfl, ?_, by rw [hx]; exact hin2⟩
  have hp2e : p2 = ⟨hgt layout 5 + 6, p2.index⟩ := by
    rw [← hvc2]
  rw [selW, blockP, block2_column, hp2, Option.getD_some, kernW, hp2e]
  exact slot_eqAbove hal2 hs64 (by rw [hx]; exact hin2)

/-! ## The claims' weights -/

theorem onStack_weights (layout : Layout) (x : List E) : ∀ L : List ColumnClaim,
    (L.filterMap (·.onStack layout)).map (·.1 x) =
      (L.map fun c ↦ (c.column, c.point)).filterMap fun cp ↦
        (layout.placements.getD cp.1 none).map fun p ↦ eqEval (p.stackPoint cp.2 layout.stackLog) x
  | [] => rfl
  | c :: L => by
    have ih := onStack_weights layout x L
    rw [List.filterMap_cons, List.map_cons, List.filterMap_cons]
    rcases hc : layout.placements.getD c.column none with _ | p
    · have hcs : c.onStack layout = none := by simp only [ColumnClaim.onStack, hc, Option.map_none]
      rw [hcs]
      simp only [Option.map_none]
      exact ih
    · have hcs : c.onStack layout = some (fun y ↦ eqEval (p.stackPoint c.point layout.stackLog) y, c.value) := by
        simp only [ColumnClaim.onStack, hc, Option.map_some]
      rw [hcs]
      simp only [Option.map_some, List.map_cons]
      rw [ih]

/-- **The sent columns' weights.** -/
theorem sent_weights {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) {x chi : List E} (hx : x.length = layout.stackLog)
    (hchi : ∀ t < 6, hgt layout t ≤ chi.length) : ∀ Z : List ((ℕ × ℕ) × ℕ), (∀ z ∈ Z, KindOk z.1.1 z.1.2 z.2) →
      (Z.map fun z ↦ (z.1.2, chi.take (hgt layout z.1.1))).filterMap (fun cp ↦
          (layout.placements.getD cp.1 none).map fun p ↦ eqEval (p.stackPoint cp.2 layout.stackLog) x) =
        ((Z.map (·.2)).filter (· ≠ 1000)).map (sentPure layout x chi)
  | [] => fun _ ↦ rfl
  | ((t, col), k) :: Z => fun hZ ↦ by
    have ih := sent_weights hbl hx hchi Z fun z hz ↦ hZ z (List.mem_cons_of_mem _ hz)
    obtain ⟨ht, hc, hsrc, hblk, hslot, hnone, hk⟩ := hZ _ List.mem_cons_self
    simp only at ht hc hsrc hblk hslot hnone hk
    rw [List.map_cons, List.filterMap_cons, List.map_cons, List.filter_cons]
    simp only
    rcases Nat.lt_or_ge k 52 with hk52 | hk52
    · -- a block
      obtain ⟨hp, hvc, -, hle⟩ := block_placed hbl hk52
      rw [hblk hk52] at hp
      have hvct : (blockP layout k).variableCount = hgt layout t := by
        rw [hvc, blockKap, hblk hk52, layout_kappa _ _ hc hsrc]; rfl
      have hne : k ≠ 1000 := by omega
      rw [hp, Option.map_some]
      simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons, ih]
      have hlen : (chi.take (hgt layout t)).length = (blockP layout k).variableCount := by
        rw [List.length_take, hvct]; exact min_eq_left (hchi t ht)
      rw [← hx, stackPoint_eqEval _ hlen (by rw [hx]; exact hle)]
      simp only [sentPure, hk52, ↓reduceIte, selW, hvct]
    · rcases Nat.lt_or_ge k 1000 with hk1 | hk1
      · -- a slot
        obtain ⟨hs, hk116, rfl⟩ := hslot hk52 hk1
        obtain ⟨P, hP, hPvc, hPab, h56⟩ := slot_mask hbl hx hc hsrc hs (by omega)
        have hne : k ≠ 1000 := by omega
        rw [hP, Option.map_some]
        simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons, ih]
        have hlen : (chi.take (hgt layout 5)).length = P.variableCount := by
          rw [List.length_take, hPvc]; exact min_eq_left (hchi 5 (by decide))
        rw [← hx, stackPoint_eqEval _ hlen (by rw [hPvc, hx]; omega), hPab, hPvc]
        simp only [sentPure, show ¬ k < 52 by omega, ↓reduceIte]
        ring_nf
      · -- no placement
        have hk1000 : k = 1000 := by omega
        obtain ⟨hs, hnb⟩ := hnone hk1000
        rw [layout_none hbl hc hs hnb, Option.map_none, ih, hk1000]
        simp

/-! ## The ring weight -/

theorem sumE_zipIdx_gen {α : Type} (d : α) (F : α × ℕ → E) : ∀ (l : List α) (n : ℕ),
    sumE ((l.zipIdx n).map F) = ∑ k ∈ Finset.range l.length, F (l.getD k d, n + k)
  | [], _ => by simp [sumE]
  | a :: l, n => by
    have ih := sumE_zipIdx_gen d F l (n + 1)
    rw [sumE_eq_sum] at ih ⊢
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih, List.length_cons,
      Finset.sum_range_succ' _ l.length]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [show n + 1 + k = n + (k + 1) by omega]

/-- A pointer's above weight is its kind's mask. -/
theorem ptr_mask {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) {x : List E} (hx : x.length = layout.stackLog)
    {q : ℕ} (hq : q < 33) :
    ((layout.placements.getD (ptrCols.getD q (0, 0)).2 none).getD default).eqAbove x =
      maskW layout x (ptrKinds.getD q 0) := by
  obtain ⟨⟨ht, hc, hsrc, hblk, hslot, -, hk⟩, hne⟩ := ptr_ok.2 q hq
  rcases Nat.lt_or_ge (ptrKinds.getD q 0) 52 with hk52 | hk52
  · rw [← hblk hk52]
    simp only [maskW, hk52, ↓reduceIte, selW, blockP]
  · obtain ⟨hs, hk116, ht5⟩ := hslot hk52 (by omega)
    rw [ht5] at hsrc
    obtain ⟨P, hP, -, hPab, -⟩ := slot_mask hbl hx hc hsrc hs (by omega)
    rw [hP, Option.getD_some, hPab]
    simp only [maskW, show ¬ ptrKinds.getD q 0 < 52 by omega, ↓reduceIte]

theorem ptrTab_getD (q : ℕ) : ptrTab.getD q 0 = (ptrCols.getD q (0, 0)).1 := by
  rw [← ptr_tab, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases ptrCols[q]? <;> rfl

/-- **The merged ring claim's weight, as the guest builds it.** -/
theorem ring_weight_pure {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) (link : LinkEnd) {x chi qPoint kIn f g slices : List E}
    {rho : E} (hx : x.length = layout.stackLog) (hpieces : link.ring.pieces = pointerPieces layout chi qPoint)
    (hf : f.length = 8) (hg : g.length = 8) :
    (ringMerge [keccakRingClaim (blockP layout 2) kIn slices, link.ring] f g rho).1 x =
      ringPure layout x chi qPoint kIn f g rho := by
  have hcs := ringCoefficients_length f g hf hg
  rw [ringMerge_weight]
  simp only [mergeTotal, keccakRingClaim, List.map_cons, List.map_nil, one_mul, add_zero]
  rw [hpieces, pointerPieces_eq, List.map_map, sumE_zipIdx_gen (0, 0), ptr_ok.1, sumE_eq_sum]
  simp only [List.sum_cons, List.sum_nil, add_zero, ringPure]
  congr 1
  · rw [stepTerm, pieceTerm_eq _ _ hcs, ringT]
    simp [aboveOf, selW]
  · refine Finset.sum_congr rfl fun q hq ↦ ?_
    have hq := Finset.mem_range.1 hq
    simp only [Function.comp, Nat.zero_add, stepTerm, ptrPiece, aboveOf]
    rw [pieceTerm_eq _ _ hcs, ptr_mask hbl hx hq, ptrTab_getD]
    rfl

/-! ## The claims and their basis -/

/-- **The stacked claims and their basis, as the guest builds it.** -/
theorem stackedBasis_pure {bytecode : List K} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode layout.logMemory rows = some layout) (link : LinkEnd)
    {chi r qPoint kOut kIn f g x z keccakSlices : List E} {rho lam rm v0 v1 oodValue : E}
    {outputs : List ColumnClaim}
    (hpieces : link.ring.pieces = pointerPieces layout chi qPoint)
    (hcols : link.columns.map (fun c ↦ (c.1, c.2.map (·.1))) =
      tables.zipIdx.map (fun (table, t) ↦ (chi.take (layout.tableLogHeights.getD t 0), nonPointerColumns table)))
    (hchi : ∀ t < nTables, layout.tableLogHeights.getD t 0 ≤ chi.length)
    (hmp : link.memoryPoint = r.take layout.logMemory) (hr : layout.logMemory ≤ r.length)
    (hout : ∃ word, outputs = [⟨qkeccak, kOut, word⟩])
    (hkOut : kOut.length = layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits)
    (hf : f.length = 8) (hg : g.length = 8) (hx : x.length = layout.stackLog) :
    ∃ claims, stackedClaims layout link (publicClaimsPure layout rm v0 v1) outputs kIn keccakSlices f g rho
        (fun y ↦ eqEval z y, oodValue) = some claims ∧
      stackedBasis claims lam x = basisPure layout link x chi r qPoint kIn kOut f g z rho lam rm := by
  obtain ⟨hp0, hvc0, -, hle0⟩ := block_placed hbl (b := 0) (by decide)
  obtain ⟨hp1, hvc1, -, hle1⟩ := block_placed hbl (b := 1) (by decide)
  obtain ⟨hp2, hvc2, -, hle2⟩ := block_placed hbl (b := 2) (by decide)
  rw [block01_column.1] at hp0
  rw [block01_column.2] at hp1
  rw [block2_column] at hp2
  obtain ⟨hk0, hk1, hk2⟩ := blockKap_eq layout
  rw [hk0] at hvc0
  rw [hk1] at hvc1
  rw [hk2] at hvc2
  have hlm1 := buildLayout_lm hbl
  obtain ⟨word, rfl⟩ := hout
  -- the memory term
  have hmpl : link.memoryPoint.length = layout.logMemory := by rw [hmp, List.length_take]; omega
  have hmt : memoryTermPure layout link = some (fun y ↦ 0 +
      link.memoryScales.1 * eqEval ((blockP layout 0).stackPoint link.memoryPoint layout.stackLog) y +
      link.memoryScales.2 * eqEval ((blockP layout 1).stackPoint link.memoryPoint layout.stackLog) y,
      link.memoryValue) := by
    unfold memoryTermPure
    rw [hp0, hp1]
    rfl
  have hrest : ((linkColumnClaims link ++ publicClaimsPure layout rm v0 v1 ++
      [(⟨qkeccak, kOut, word⟩ : ColumnClaim)]).filterMap (·.onStack layout)).map (fun c ↦ c.1 x) ++ [eqEval z x] =
      tailPure layout x chi kOut z rm := by
    rw [onStack_weights, List.map_append, List.map_append, List.filterMap_append, List.filterMap_append,
      linkColumnClaims_colPts link (fun t ↦ chi.take (layout.tableLogHeights.getD t 0)) hcols]
    have hZ1 : sentCols = (sentCols.zip sentKinds).map Prod.fst :=
      (List.map_fst_zip (by rw [sent_ok.1]; rfl)).symm
    have hZ2 : sentKinds = (sentCols.zip sentKinds).map Prod.snd :=
      (List.map_snd_zip (by rw [sent_ok.1]; rfl)).symm
    have hsw := sent_weights hbl hx (fun t ht ↦ hchi t ht) (sentCols.zip sentKinds) sent_ok.2
    rw [← hZ2] at hsw
    have hsent : (sentCols.map fun e ↦ (e.2, chi.take (layout.tableLogHeights.getD e.1 0))) =
        (sentCols.zip sentKinds).map fun z ↦ (z.1.2, chi.take (hgt layout z.1.1)) := by
      conv_lhs => rw [hZ1]
      rw [List.map_map]
      rfl
    rw [hsent, hsw]
    have hpt : (rm :: List.replicate (layout.logMemory - 1) 0).length = layout.logMemory := by
      simp; omega
    simp only [publicClaimsPure, hp0, Option.map_some, Option.getD_some, hvc0, List.map_cons, List.map_nil,
      List.filterMap_cons, List.filterMap_nil, hp1, hp2]
    rw [← hx, stackPoint_eqEval _ (by rw [hpt, hvc0]) (by rw [hvc0, hx]; omega),
      stackPoint_eqEval _ (by rw [hpt, hvc1]) (by rw [hvc1, hx]; omega),
      stackPoint_eqEval _ (by rw [hkOut, hvc2]; rfl) (by rw [hx]; exact hle2), hvc0, hvc1, hvc2]
    simp only [tailPure, sentList, selW, List.append_assoc, List.cons_append, List.nil_append]
  have hmem : 0 + link.memoryScales.1 * eqEval ((blockP layout 0).stackPoint link.memoryPoint layout.stackLog) x +
      link.memoryScales.2 * eqEval ((blockP layout 1).stackPoint link.memoryPoint layout.stackLog) x =
      eqEval (r.take layout.logMemory) (x.take layout.logMemory) *
        (link.memoryScales.1 * selW layout x 0 + link.memoryScales.2 * selW layout x 1) := by
    rw [← hx, stackPoint_eqEval _ (by rw [hmpl, hvc0]) (by rw [hvc0, hx]; omega),
      stackPoint_eqEval _ (by rw [hmpl, hvc1]) (by rw [hvc1, hx]; omega), hvc0, hvc1, hmp]
    simp only [selW]
    ring
  refine ⟨_, by simp only [stackedClaims, hp2, hmt]; rfl, ?_⟩
  unfold stackedBasis
  rw [show ∀ l : List StackClaim, l.length = (l.map fun c ↦ c.1 x).length from fun l ↦ by simp,
    dot_powers_hornerL]
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, hornerL]
  rw [ring_weight_pure hbl link hx hpieces hf hg, hmem, hrest]
  rfl

end
end LeanVM.Guest.B1.Stack
