/-
  LeanVM.Guest.B1.Opening.QueriesComplete4

  The completeness of one query of `opening_queries`: every atom holds at the honest values, and
  the query's value is the row's dot product.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete3

/-!
# One query, completeness

`QD.Ok` is what `QueryOpens` and the windows say of an honest query (`exists_of_opens`): the
siblings and the row's length, the memory (`MemOk`: the windows at the window pointer, the cap
leaf, the flag), the weights at `wp`, the position below `2^depth`. `query_complete`: at a
valuation that is the honest values on the query's indices, with the padding run `1, 0, 0, 0, 0`,
every statement of `oqQueryT` holds and the query's value is `rowDot` (by the soundness
direction, `oqQuery_sound`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A row's dot product reads the weights below `rowLo I + I / rowLo I` only. -/
theorem rowDot_congr {base I : ℕ} {row : List K} {w w' : ℕ → E}
    (h : ∀ l < rowLo I + I / rowLo I, w l = w' l) : rowDot base I row w = rowDot base I row w' := by
  unfold rowDot
  refine congrArg (List.foldl _ _) (List.map_congr_left fun hh hm => ?_)
  rw [List.mem_range] at hm
  rw [h _ (by omega)]
  refine congrArg (w' _ * ·) (congrArg (List.foldl _ _) (List.map_congr_left fun l hl => ?_))
  rw [List.mem_range] at hl
  rw [h l (by omega)]

namespace QD

/-- What `QueryOpens` and the windows say of an honest query. -/
structure Ok (d : QD) (rd : Reader) (wp bpv : E) : Prop where
  hsibs : d.sibs.length = d.s.pd
  hrow : d.row.length = d.s.R
  hmem : (d.wd bpv).MemOk rd
  hw : ∀ l < d.s.lo + d.s.I / d.s.lo, LoadHolds rd wp l (d.w l)
  hq : d.q < 2 ^ (d.s.pd + d.s.cd)

/-- **An opening with its windows is an honest query**, wherever it is placed. -/
theorem exists_of_opens {rd : Reader} {s : Oq} {cap flags wp bpv : E} {q : ℕ} {row : List K}
    {dv : E} (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd bpv i (gen ^ qwVal (s.pd + s.cd) s.cd q i))
    (h : QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q row dv) :
    ∃ (w : ℕ → E) (sibs : List Digest), dv = rowDot s.base s.I row w ∧
      ∀ b emit pr, (QD.mk s b emit pr row w q sibs cap flags).Ok rd wp bpv := by
  obtain ⟨hrl, sibs, w, hsl, hw, hc0, hc1, hfl, hd⟩ := h
  rw [show s.pd + s.cd - s.cd = s.pd by omega] at hsl hc0 hc1 hfl
  exact ⟨w, sibs, hd, fun b emit pr => ⟨hsl, hrl, ⟨hwin, hc0, hc1, hfl⟩, hw, hq⟩⟩

variable (d : QD) {rd : Reader} {σ : Val}

/-- The padding run a query emits. -/
theorem pad_of_emit (he : d.emit = true)
    (hv : ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i) :
    σ (.n d.prV) = word 1 0 0 ∧ ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0 := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hkL : d.kL = d.k1 + d.s.D + 5 := by rw [kL_eq, he]; rfl
  have hpr : d.prV = d.k1 + d.s.D := by simp only [prV, oqPr, he, ↓reduceIte]; rfl
  refine ⟨?_, fun i hi => ?_⟩
  · have := hv (d.k1 + d.s.D + 0) (by omega) (by omega)
    rw [val_pad d he (by omega)] at this
    simpa only [hpr, Nat.add_zero, List.getD_cons_zero] using this
  · have := hv (d.k1 + d.s.D + (i + 1)) (by omega) (by omega)
    rw [val_pad d he (by omega)] at this
    rw [hpr, show d.k1 + d.s.D + 1 + i = d.k1 + d.s.D + (i + 1) by omega, this]
    interval_cases i <;> rfl

/-- The row a query's atoms read is the honest row. -/
theorem oqRow_eq (hrow : d.row.length = d.s.R)
    (hv : ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i) : oqRow d.b d.s.R σ = d.row := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  refine List.ext_getElem (by simp [oqRow, hrow]) fun i h1 h2 => ?_
  have hi : i < d.s.R := by simpa [oqRow] using h1
  simp only [oqRow, List.getElem_map, List.getElem_range]
  rw [hv _ (by omega) (by omega), val_row d hi, QD.rw, limb_ofK]
  simp [List.getD_eq_getElem?_getD, h2]

/-- The query's statements but its call of the walk: atoms. -/
theorem oqQueryT_eq (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr : ℕ) (walk : String) :
    oqQueryT s bp cap flags wp b emit pr walk =
      (oqRowT b s.R ++ oqPacksT b s.R ++ oqDotT s wp b ++
        (if emit then oqPadT (oqK1 b s.R + s.D) else []) ++ oqLeafT s b (oqPr s b emit pr) (oqKL s b emit)) ++
      [.call walk [.n (oqOut s (oqKL s b emit) (s.B - 1) 0), .n (oqOut s (oqKL s b emit) (s.B - 1) 1),
        bp, cap, flags] []] := rfl

/-- **One query's atoms hold at the honest values.** -/
theorem query_atoms (hs : d.s.RowShape) {wp : V} {bpv : E} (hok : d.Ok rd (σ wp) bpv) (hv : d.Hv σ)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0) :
    AllAtoms (oqRowT d.b d.s.R ++ oqPacksT d.b d.s.R ++ oqDotT d.s wp d.b ++
        (if d.emit then oqPadT (oqK1 d.b d.s.R + d.s.D) else []) ++ oqLeafT d.s d.b d.prV d.kL) ∧
      ∀ a, Stmt.atom a ∈ (oqRowT d.b d.s.R ++ oqPacksT d.b d.s.R ++ oqDotT d.s wp d.b ++
        (if d.emit then oqPadT (oqK1 d.b d.s.R + d.s.D) else []) ++ oqLeafT d.s d.b d.prV d.kL) →
        a.Holds rd σ := by
  refine ⟨allAtoms_append (allAtoms_append (allAtoms_append
      (allAtoms_append (oqRowT_atoms _ _) (oqPacksT_atoms _ _)) (oqDotT_atoms _ _ _)) ?_)
      (oqLeafT_atoms _ _ _ _), fun a ha => ?_⟩
  · split
    · exact oqPadT_atoms _
    · exact allAtoms_nil
  · simp only [List.mem_append] at ha
    rcases ha with ((((ha | ha) | ha) | ha) | ha)
    · simp only [oqRowT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      subst ha
      trivial
    · exact d.oqPacks_complete hv a ha
    · exact d.oqDot_complete hs hv hok.hw a ha
    · cases he : d.emit
      · simp [he] at ha
      · simp only [he, ↓reduceIte] at ha
        exact d.oqPad_complete he hv a ha
    · exact d.oqLeaf_complete hs hv hpad hz a ha

/-- **One query holds at the honest values**, its call of `walk` in `C` on the leaf's halves, the
window pointer, the cap and the flags; its value is the row's dot product (by the soundness
direction, `oqQuery_pieces`), and its leaf cells the leaf's digest's halves. -/
theorem query_complete (hs : d.s.RowShape) {walk : String} {C : CallRel}
    {bp cap flags wp : V} (hok : d.Ok rd (σ wp) (σ bp)) (hv : d.Hv σ)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    (hcap : σ cap = d.capv) (hflags : σ flags = d.flagsv)
    (hC : C walk [(digestHalves d.leaf).1, (digestHalves d.leaf).2, σ bp, d.capv, d.flagsv] []) :
    BlockOkC C rd σ (oqQueryT d.s bp cap flags wp d.b d.emit d.pr walk) ∧
      σ (.n (oqDot d.s d.b)) = rowDot d.s.base d.s.I d.row d.w ∧
      (σ (.n (oqOut d.s d.kL (d.s.B - 1) 0)), σ (.n (oqOut d.s d.kL (d.s.B - 1) 1))) =
        digestHalves d.leaf := by
  obtain ⟨hAA, hA⟩ := d.query_atoms hs hok hv hpad hz
  have hT : BlockOkC (fun _ _ _ ↦ True) rd σ (oqQueryT d.s bp cap flags wp d.b d.emit d.pr walk) := by
    rw [oqQueryT_eq]
    refine blockOkC_append.mpr ⟨blockOkC_of_blockOk (blockOk_of_atoms hAA hA), fun s hs ↦ ?_⟩
    simp only [List.mem_singleton] at hs
    subst hs
    trivial
  have hz' : ∀ i < 4, σ (.n (oqPr d.s d.b d.emit d.pr + 1 + i)) = 0 := fun i hi => by
    rw [← word_zero]; exact hz i hi
  have hleaf := oqQuery_leaf hs hT hpad hz'
  rw [d.oqRow_eq hok.hrow hv] at hleaf
  obtain ⟨hP, hD, -, -, -⟩ := oqQuery_pieces hT
  obtain ⟨hw', hdot⟩ := oqDot_sound hs hD (oqWord_sound hs hP hD)
  refine ⟨?_, ?_, hleaf⟩
  · rw [oqQueryT_eq]
    refine blockOkC_append.mpr ⟨blockOkC_of_blockOk (blockOk_of_atoms hAA hA), fun s hs ↦ ?_⟩
    simp only [List.mem_singleton] at hs
    subst hs
    show C walk _ _
    simp only [List.map_cons, List.map_nil]
    have e0 := congrArg Prod.fst hleaf
    have e1 := congrArg Prod.snd hleaf
    simp only at e0 e1
    rw [e0, e1, hcap, hflags]
    exact hC
  · rw [hdot, rowDot_eq, d.oqRow_eq hok.hrow hv]
    exact rowDot_congr fun l hl => loadHolds_unique (hw' l hl) (hok.hw l hl)

end QD

end
end LeanVM.Guest.B1
