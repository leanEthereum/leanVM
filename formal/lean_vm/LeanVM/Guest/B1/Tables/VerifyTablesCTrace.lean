/-
  LeanVM.Guest.B1.Tables.VerifyTablesCTrace

  `tablesSeg`'s run, read back with its stream and states: what `verify_tables` follows.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesInv
public import LeanVM.Guest.B1.Tables.GkrPair

/-!
# The run of `tablesSeg`, with its stream

`vt_trace`: a run reads the bus's three memory words and two final counters, the table
sumcheck's rounds (three words each, `roundPoly 4`), then each table's evaluations; the
sumcheck's final claim is the tables' terms' sum, and the public input's challenge is squeezed
last.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem RunsTo.roundPoly4_inv {claim : E} {cv cv' : Digest} {ws : List E} {r : E × E}
    (h : RunsTo (roundPoly 4 claim none) cv ws r cv') : ws.length = 3 := by
  unfold roundPoly at h
  obtain ⟨x1, x2, msg, cv1, hx, h1, h⟩ := RunsTo.bind_inv' h
  unfold sumcheckRoundPoly at h1
  obtain ⟨y1, y2, c, cv2, hy, h2, h1⟩ := RunsTo.bind_inv' h1
  obtain ⟨hy1, -⟩ := RunsTo.readE_inv h2
  obtain ⟨y3, y4, tail, cv3, hz, h3, h1⟩ := RunsTo.bind_inv' h1
  obtain ⟨hl, -, -⟩ := RunsTo.readN_inv h3
  obtain ⟨hy4, -, -⟩ := RunsTo.ret_inv h1
  obtain ⟨x3, x4, ch, cv4, hw, h4, h⟩ := RunsTo.bind_inv' h
  obtain ⟨hx3, -, -⟩ := RunsTo.sampleE_inv h4
  obtain ⟨hx4, -, -⟩ := RunsTo.ret_inv h
  rw [hx, hy, hz, hy1, hy4, hw, hx3, hx4]
  simp [hl]

/-- **`tableTerms`' run, inverted, with its stream.** -/
theorem RunsTo.tableTerms_trace (cp fp pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E) (claims : List ColumnClaim)
      (cv cv' : Digest) (xs : List E) (r : E × List ColumnClaim),
      RunsTo (tableTerms cp fp pt rows cursor final claims) cv xs r cv' →
      ∃ evss : List (List E), evss.length = rows.length ∧
        (∀ i (h1 : i < evss.length) (h2 : i < rows.length), evss[i].length = rows[i].1.width) ∧
        xs = evss.flatten ∧ r = ttVal cp fp pt rows evss cursor final claims ∧ cv' = obsAll cv evss.flatten
  | [], cursor, final, claims, cv, cv', xs, r, h => by
    have h' : RunsTo (pure (final, claims) : Prog (E × List ColumnClaim)) cv xs r cv' := h
    obtain ⟨rfl, rfl, rfl⟩ := RunsTo.ret_inv h'
    exact ⟨[], rfl, fun i h1 => absurd h1 (by simp), rfl, rfl, rfl⟩
  | (table, height, forms, weight) :: rest, cursor, final, claims, cv, cv', xs, r, h => by
    unfold tableTerms at h
    obtain ⟨x1, x2, evs, cv1, rfl, h1, h2⟩ := RunsTo.bind_inv' h
    obtain ⟨hl, he, hc⟩ := RunsTo.readN_inv h1
    subst he hc
    obtain ⟨evss, hl', hw, rfl, rfl, rfl⟩ := RunsTo.tableTerms_trace cp fp pt rest _ _ _ _ _ _ _ h2
    refine ⟨evs :: evss, by simp [hl'], fun i h1 h2 => ?_, by simp, rfl, ?_⟩
    · match i with
      | 0 => simpa using hl
      | i + 1 => simpa using hw i (by simpa using h1) (by simpa using h2)
    · simp [obsAll, List.foldl_append]

/-- `busRest`'s stream and state. -/
theorem RunsTo.busRest_trace {ev : Evaluations} {layout : Layout} {alphas : List E} {beta : E}
    {point tv : List E} {cv cv' : Digest} {xs : List E} {bus : BusResult} {bv : E}
    (hbv : BytecodeAt ev layout.bytecode (point.take layout.logBytecode ++ alphas) bv)
    (h : RunsTo (busRest ev layout alphas beta point tv) cv xs bus cv') :
    ∃ (memory : List E) (mF bF : E), memory.length = 3 ∧ xs = memory ++ [mF, bF] ∧
      bus = busVal layout alphas beta point tv memory mF bF bv ∧
      cv' = obsAll cv (memory ++ [mF, bF]) := by
  unfold busRest at h
  obtain ⟨x1, x2, memory, cv1, e1, h1, k1⟩ := RunsTo.bind_inv' h
  obtain ⟨hl, em, ec1⟩ := RunsTo.readN_inv h1
  obtain ⟨x3, x4, mF, cv3, e3, h3, k3⟩ := RunsTo.bind_inv' k1
  obtain ⟨ex3, ec3⟩ := RunsTo.readE_inv h3
  obtain ⟨x5, x6, bF, cv5, e5, h5, k5⟩ := RunsTo.bind_inv' k3
  obtain ⟨ex5, ec5⟩ := RunsTo.readE_inv h5
  obtain ⟨x7, x8, bv', cv7, e7, h7, k7⟩ := RunsTo.bind_inv' k5
  obtain ⟨ex7, eb, ec7⟩ := (runsTo_bytecodeAt hbv _).det_nil h7
  have k8 : RunsTo (pure (busVal layout alphas beta point tv memory mF bF bv') : Prog BusResult) cv7 x8 bus cv' := k7
  obtain ⟨ex8, eb', ec8⟩ := RunsTo.ret_inv k8
  refine ⟨memory, mF, bF, by rw [em]; exact hl, ?_, by rw [eb', eb], ?_⟩
  · rw [e1, e3, e5, e7, ex3, ex5, ex7, ex8, em]; simp
  · rw [ec8, ec7, ec5, ec3, ec1, em]
    simp [obsAll, List.foldl_append]

/-- The table sumcheck's round count. -/
def vtN (layout : Layout) : ℕ := layout.tableLogHeights.foldl max 0

/-- The constraint count. -/
abbrev vtNC : ℕ := (tables.map Table.nConstraints).sum

/-- The table sumcheck's rows at its point. -/
def vtRows (layout : Layout) (bus : BusResult) (rs : List E) : List (Table × ℕ × List Form × E) :=
  List.zip tables (List.zip layout.tableLogHeights (List.zip bus.forms
    (tableWeights layout.tableLogHeights bus.point rs)))

/-- **`tablesSeg`'s run, read back**: the bus's five words (`memory`, `mF`, `bF`), the table
sumcheck's rounds from the state after them (`cl`, `cvr`, `wsr`, `ch`), the tables' evaluations
`evss`, the terms' sum the last claim, and the claims and state at the end. -/
theorem RunsTo.tablesSeg_trace {ev : Evaluations} {layout : Layout} {pi : Digest} {alphas : List E}
    {beta : E} {point tv : List E} {cv cv' : Digest} {xs : List E} {bus : BusResult}
    {claims : List ColumnClaim} {bv : E}
    (hbv : BytecodeAt ev layout.bytecode (point.take layout.logBytecode ++ alphas) bv)
    (h : RunsTo (tablesSeg ev layout pi alphas beta point tv) cv xs (bus, claims) cv') :
    ∃ (memory : List E) (mF bF : E) (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch : ℕ → E)
      (evss : List (List E)), memory.length = 3 ∧
      bus = busVal layout alphas beta point tv memory mF bF bv ∧
      xs = memory ++ [mF, bF] ++ ((List.range (vtN layout)).flatMap wsr ++ evss.flatten) ∧
      cl 0 = dot ((powers (challengeOf (sqCv (obsAll cv (memory ++ [mF, bF])))) (vtNC + 3)).drop vtNC)
        bus.totals ∧
      cvr 0 = sqCv (obsAll cv (memory ++ [mF, bF])) ∧
      (∀ r < vtN layout, RunsTo (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) ∧
      evss.length = (vtRows layout bus ((List.range (vtN layout)).map ch).reverse).length ∧
      (∀ i (h1 : i < evss.length) (h2 : i < (vtRows layout bus ((List.range (vtN layout)).map ch).reverse).length),
        evss[i].length = (vtRows layout bus ((List.range (vtN layout)).map ch).reverse)[i].1.width) ∧
      (ttVal ((powers (challengeOf (sqCv (obsAll cv (memory ++ [mF, bF])))) (vtNC + 3)).take vtNC)
        ((powers (challengeOf (sqCv (obsAll cv (memory ++ [mF, bF])))) (vtNC + 3)).drop vtNC)
        ((List.range (vtN layout)).map ch).reverse (vtRows layout bus ((List.range (vtN layout)).map ch).reverse)
        evss 0 0 []).1 = cl (vtN layout) ∧
      claims = bus.claims ++
        (ttVal ((powers (challengeOf (sqCv (obsAll cv (memory ++ [mF, bF])))) (vtNC + 3)).take vtNC)
          ((powers (challengeOf (sqCv (obsAll cv (memory ++ [mF, bF])))) (vtNC + 3)).drop vtNC)
          ((List.range (vtN layout)).map ch).reverse
          (vtRows layout bus ((List.range (vtN layout)).map ch).reverse) evss 0 0 []).2 ++
        piClaims layout pi (challengeOf (sqCv (obsAll (cvr (vtN layout)) evss.flatten))) ∧
      cv' = sqCv (obsAll (cvr (vtN layout)) evss.flatten) := by
  unfold tablesSeg at h
  obtain ⟨x1, x2, bus1, cv1, e1, h1, k1⟩ := RunsTo.bind_inv' h
  obtain ⟨memory, mF, bF, hl, ex1, eb1, ec1⟩ := RunsTo.busRest_trace hbv h1
  obtain ⟨x3, x4, tc, cv3, e3, h3, k3⟩ := RunsTo.bind_inv' k1
  obtain ⟨x5, x6, pc, cv5, e5, h5, k5⟩ := RunsTo.bind_inv' k3
  obtain ⟨ex6, epc, ec6⟩ := RunsTo.ret_inv k5
  simp only [Prod.mk.injEq] at epc
  obtain ⟨rfl, rfl⟩ := epc
  -- the public input
  unfold publicInputPhase at h5
  obtain ⟨y1, y2, rm, cy1, f1, g1, k6⟩ := RunsTo.bind_inv' h5
  obtain ⟨fy1, frm, fcy1⟩ := RunsTo.sampleE_inv g1
  obtain ⟨fy2, fpc, fcy2⟩ := RunsTo.ret_inv k6
  -- the table phase
  unfold tablePhase at h3
  obtain ⟨z1, z2, xi, cz1, f2, g2, k7⟩ := RunsTo.bind_inv' h3
  obtain ⟨fz1, fxi, fcz1⟩ := RunsTo.sampleE_inv g2
  obtain ⟨z3, z4, tcl, cz3, f3, g3, k8⟩ := RunsTo.bind_inv' k7
  obtain ⟨fz4, ftc, fcz4⟩ := RunsTo.ret_inv k8
  unfold tableSumcheck at g3
  obtain ⟨w1, w2, ⟨chs, cl⟩, cw1, f4, g4, k9⟩ := RunsTo.bind_inv' g3
  obtain ⟨cl', cvr, wsr, ch, hc0, hcv0, hr, hws, hpt, hfin, hcvS⟩ := RunsTo.sumcheck_inv _ _ _ _ _ _ _ g4
  obtain ⟨w3, w4, ⟨fin, tcs⟩, cw3, f5, g5, k10⟩ := RunsTo.bind_inv' k9
  obtain ⟨evss, hel, hew, fx, fr, fc⟩ := RunsTo.tableTerms_trace _ _ _ _ _ _ _ _ _ _ _ g5
  obtain ⟨w5, w6, u, cw5, f6, g6, k11⟩ := RunsTo.bind_inv' k10
  obtain ⟨hreq, fw5, fcw5⟩ := RunsTo.require_inv g6
  obtain ⟨fw6, ftcs, fcw6⟩ := RunsTo.ret_inv k11
  simp only [List.length_replicate] at hr hws hpt hfin hcvS
  subst e1 ex1 e3 f2 fz1 f3 f4 hws f5 fx f6 fw5 fw6 fz4 e5 f1 fy1 fy2 ex6
  subst fxi fcz1 ec1 hcvS fcw5 fcw6 fcz4 fc fcy1 fcy2 frm fpc ftcs ftc hpt hfin
  have hfin' : fin = cl' (vtN layout) := hreq
  have hf1 := congrArg Prod.fst fr
  have hf2 := congrArg Prod.snd fr
  simp only at hf1 hf2
  unfold vtN at hfin' ⊢
  unfold vtRows
  refine ⟨memory, mF, bF, cl', cvr, wsr, ch, evss, hl, eb1, by simp, hc0, hcv0, fun r hr' => ?_, hel, hew,
    by rw [← hf1, hfin'], ?_, ec6⟩
  · have := hr r (by simpa using hr')
    simpa using this
  · rw [← hf2]; rfl

end
end LeanVM.Guest.B1.VerifySub
