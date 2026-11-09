/-
  LeanVM.Guest.B1.VerifySub.H.Vt

  `verify_tables`' honest data (B1-c's `VtHonest`) from a run of `tablesSeg`: the stream words cut
  as the run reads them.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Tables.VtC.ADefs
public import LeanVM.Guest.B1.Tables.Vt.AsmRun
public import LeanVM.Guest.B1.Tables.Vt.AsmForms

/-!
# `verify_tables`' honest data from a run

`runsTo_len`: a run of a program that runs on every `k` words reads `k` words. `chunks`: a list cut
in pieces of given lengths. `vtHOf`: B1-c's `VtHonest` of a run of `tablesSeg` on the words `xs`
(the five framework words, the `3 n` rounds' words, the tables' evaluations, `vtW6` words each).
`vtH_run`: such a run makes it `Ok`, the words are cut in place (`5 + 3 n + 159` of them), and the
run ends with nothing waiting.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The tables' widths, table by table. -/
theorem vtH_tables_widths : ∀ t < 6, (tables.getD t default).width = vtW6.getD t 0 := by decide

theorem vtH_rowsT_length {H : VtHonest} (hr : H.rows.length = 6) : H.rowsT.length = 6 := by
  have hf : H.busH.forms.length = 6 :=
    (vt_forms3_shape H.bc H.lm hr H.alphas H.beta H.point (H.xs5.take 3) (H.xs5.getD 3 0)
      (H.xs5.getD 4 0) H.bv (H.values.getD 0 0) (H.values.getD 1 0) (H.values.getD 2 0)).1
  have hh : H.L.tableLogHeights.length = 6 := vt_tableHeights_length hr
  have ht : tables.length = 6 := rfl
  simp only [VtHonest.rowsT, vtRows, List.length_zip, hh, hf, ht,
    LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
  rfl

/-- **The honest evaluations' shape**: six tables, each its width. -/
theorem vtH_evsT_shape {H : VtHonest} (h : H.Ok) (hr : H.rows.length = 6) :
    H.evsT.length = 6 ∧ ∀ t < 6, (H.evsT.getD t []).length = vtW6.getD t 0 := by
  have hl := h.hevl
  rw [vtH_rowsT_length hr] at hl
  refine ⟨hl, fun t ht ↦ ?_⟩
  have hz : (H.rowsT[t]'(by rw [vtH_rowsT_length hr]; exact ht), H.evsT[t]'(by omega)) ∈
      List.zip H.rowsT H.evsT := by
    rw [List.mem_iff_getElem]
    exact ⟨t, by simp [vtH_rowsT_length hr, hl, ht], by simp⟩
  have hw := h.hevw _ hz
  simp only at hw
  have ht1 : (H.rowsT[t]'(by rw [vtH_rowsT_length hr]; exact ht)).1 = tables.getD t default := by
    simp [VtHonest.rowsT, vtRows, List.getElem_zip, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show t < tables.length from ht)]
  rw [List.getD_eq_getElem _ _ (by omega), hw, ht1, vtH_tables_widths t ht]

/-- **A run reads the words every run reads**: when the program runs on every `k` words, a run of
it reads `k` words. -/
theorem runsTo_len {α : Type} {p : VerifierProgram α} {s t : Fs} {xs : List E} {a : α} (h : RunsTo p
    s xs a t)
    (hc : ∃ sp, s.Carries sp) {k : ℕ}
    (hall : ∀ ys : List E, ys.length = k → ∃ (b : α) (u : Fs), RunsTo p s ys b u) :
    xs.length = k := by
  obtain ⟨b, u, hb⟩ := hall ((xs ++ List.replicate k 0).take k) (by simp)
  obtain ⟨-, -, hr⟩ := runsTo_det h hb hc (r1 := List.replicate k 0)
    (r2 := (xs ++ List.replicate k 0).drop k) (List.take_append_drop _ _).symm
  have := congrArg List.length hr
  simp only [List.length_replicate, List.length_drop, List.length_append] at this
  omega

/-- A list cut in pieces of the given lengths. -/
def chunks : List ℕ → List E → List (List E)
  | [], _ => []
  | k :: ks, l => l.take k :: chunks ks (l.drop k)

theorem chunks_length : ∀ (ks : List ℕ) (l : List E), (chunks ks l).length = ks.length
  | [], _ => rfl
  | _ :: ks, l => by simp [chunks, chunks_length ks]

theorem chunks_flatten : ∀ (ks : List ℕ) (l : List E), l.length = ks.sum → (chunks ks l).flatten = l
  | [], l, h => by simp at h; simp [chunks, h]
  | k :: ks, l, h => by
    simp only [List.sum_cons] at h
    rw [chunks, List.flatten_cons, chunks_flatten ks (l.drop k) (by simp; omega),
      List.take_append_drop]

theorem chunks_getElem_length : ∀ (ks : List ℕ) (l : List E), l.length = ks.sum →
    ∀ i (hi : i < (chunks ks l).length), ((chunks ks l)[i]).length = ks.getD i 0
  | [], _, _, i, hi => absurd hi (by simp [chunks])
  | k :: ks, l, h, 0, _ => by simp only [List.sum_cons] at h; simp [chunks]; omega
  | k :: ks, l, h, i + 1, hi => by
    simp only [List.sum_cons] at h
    simp only [chunks, List.getElem_cons_succ, List.getD_cons_succ]
    exact chunks_getElem_length ks (l.drop k) (by simp; omega) i (by simpa [chunks] using hi)

/-- **Rows of the tables, with their evaluations cut from `159` words.** -/
theorem zip_chunks {X : Type} (rows : List (Table × X)) (hrows : rows.map (·.1) = tables)
    (ys : List E) (hy : ys.length = 159) :
    (List.zip rows (chunks vtW6 ys)).map (·.1) = rows ∧
      (List.zip rows (chunks vtW6 ys)).flatMap (·.2) = ys ∧
      ∀ p ∈ List.zip rows (chunks vtW6 ys), p.2.length = p.1.1.width := by
  have hrl : rows.length = 6 := by
    have : rows.length = tables.length := by simpa using congrArg List.length hrows
    rw [this]; rfl
  have hcl : (chunks vtW6 ys).length = 6 := by rw [chunks_length]; rfl
  refine ⟨List.map_fst_zip (by omega), ?_, fun p hp ↦ ?_⟩
  · rw [vt_flatMap_snd, List.map_snd_zip (by omega), chunks_flatten _ _ (by rw [hy]; rfl)]
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    simp only [List.length_zip] at hi
    simp only [List.getElem_zip]
    rw [chunks_getElem_length _ _ (by rw [hy]; rfl)]
    have h1 : rows[i].1 = tables[i]'(by simp [← hrows]; omega) := by
      have := congrArg (·[i]?) hrows
      simp only [List.getElem?_map] at this
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by rw [← hrows]; simp; omega)]
        at this
      simpa using this
    rw [h1, ← List.getD_eq_getElem _ default, vtH_tables_widths i (by omega)]

/-- The table loop runs on every `159` words. -/
theorem tableTerms_any (cp fp point : List E) (hs : List ℕ) (fs : List (List Form)) (ws : List E)
    (h1 : 6 ≤ hs.length) (h2 : 6 ≤ fs.length) (h3 : 6 ≤ ws.length) (u : Fs) (ys : List E)
    (hy : ys.length = 159) :
    ∃ (b : E × List ColumnClaim) (v : Fs),
      RunsTo (tableTermsClaims cp fp point (List.zip tables (List.zip hs (List.zip fs ws))) 0 0 []) u ys
        b v := by
  obtain ⟨e1, e2, hw⟩ := zip_chunks (List.zip tables (List.zip hs (List.zip fs ws)))
    (List.map_fst_zip (by simp only [List.length_zip]; show 6 ≤ _; omega)) ys hy
  have h := vt_runsTo_tableTerms cp fp point _ 0 0 [] u hw
  rw [e1, e2] at h
  exact ⟨_, _, h⟩

/-- **`verify_tables`' honest data of a run of `tablesSeg`** on the words `xs`. -/
noncomputable def vtHOf (bc : List K) (lm : ℕ) (pi : Digest) (alphas point values : List E)
    (beta : E) (rows : List ℕ) (f : List E) (ev : (List K → List E → VerifierProgram E)) (bv : E)
        (xs : List E)
    (bus : BusResult) (claims : List ColumnClaim) (cap' : List E) : VtHonest :=
  ⟨bc, lm, pi, alphas, point, values, beta, rows, f, ev, bv, xs.take 5,
    (xs.drop 5).take (3 * (tableHeightsOf rows).foldl max 0),
    chunks vtW6 (xs.drop (5 + 3 * (tableHeightsOf rows).foldl max 0)), bus, claims, cap'⟩

theorem rowsT_fst (H : VtHonest) (hr : H.rows.length = 6) : H.rowsT.map (·.1) = tables := by
  have hf : H.busH.forms.length = 6 :=
    (vt_forms3_shape H.bc H.lm hr H.alphas H.beta H.point (H.xs5.take 3) (H.xs5.getD 3 0)
      (H.xs5.getD 4 0) H.bv (H.values.getD 0 0) (H.values.getD 1 0) (H.values.getD 2 0)).1
  have hh : H.L.tableLogHeights.length = 6 := vt_tableHeights_length hr
  simp only [VtHonest.rowsT, vtRows]
  refine List.map_fst_zip ?_
  simp only [List.length_zip, hh, hf, LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
  decide

/-- **A run of `tablesSeg` is `verify_tables`' honest run**: its words cut in place, `Ok`, and
nothing waiting at its end. -/
theorem vtH_run {bc : List K} {lm : ℕ} {pi : Digest} {alphas point values : List E} {beta : E}
    {rows : List ℕ} {f : List E} {ev : (List K → List E → VerifierProgram E)} {bv : E} {xs : List E} {bus : BusResult}
    {claims : List ColumnClaim} {s' : Fs} (hr : rows.length = 6)
    (h : RunsTo (tablesSeg ev (layoutOf bc lm rows) pi alphas beta point values) ⟨f, []⟩ xs
      (bus, claims) s')
    (hcar : ∃ sp, (⟨f, []⟩ : Fs).Carries sp)
    (hbv : BytecodeAt ev (layoutOf bc lm rows).bytecode
      (point.take (layoutOf bc lm rows).logBytecode ++ alphas) bv) :
    (vtHOf bc lm pi alphas point values beta rows f ev bv xs bus claims s'.cap).Ok ∧
      xs = (vtHOf bc lm pi alphas point values beta rows f ev bv xs bus claims s'.cap).xs5 ++
        (vtHOf bc lm pi alphas point values beta rows f ev bv xs bus claims s'.cap).xsR ++
        (vtHOf bc lm pi alphas point values beta rows f ev bv xs bus claims s'.cap).evsT.flatten ∧
      s' = ⟨s'.cap, []⟩ ∧
      xs.length = 5 + 3 * (tableHeightsOf rows).foldl max 0 + 159 := by
  set n := (tableHeightsOf rows).foldl max 0 with hn
  -- the words, cut
  have key : ∃ x1 x2 x3 : List E, xs = x1 ++ x2 ++ x3 ∧ x1.length = 5 ∧ x2.length = 3 * n ∧
      x3.length = 159 ∧ s'.pend = [] := by
    have h0 := h
    unfold tablesSeg at h0
    obtain ⟨a1, xs1, xs2, t1, he1, r1, k1⟩ := RunsTo.unbind h0 hcar
    have l1 : xs1.length = 5 := runsTo_len r1 hcar fun ys hy ↦ ⟨_, _, by
      have hb := vt_busRest_run ev (layoutOf bc lm rows) alphas beta point values (ys.take 3)
        (by simp [hy]) (ys.getD 3 0) (ys.getD 4 0) bv hbv ⟨f, []⟩
      rwa [← vt_xs5_split hy] at hb⟩
    have c1 := RunsTo.carries r1 hcar
    obtain ⟨a2, xs3, xs4, t2, he2, r2, k2⟩ := RunsTo.unbind k1 c1
    have c2' := RunsTo.carries r2 c1
    obtain ⟨pc, p1s, p2s, u6, hp, o1, o2⟩ := RunsTo.unbind k2 c2'
    obtain ⟨-, eu6, ep⟩ := runsTo_det o1 (vt_publicInputPhase_run (layoutOf bc lm rows) pi t2) c2'
      (r1 := p2s) (r2 := p1s ++ p2s) (by simp)
    have ep' : p1s = [] := by simpa using ep
    subst ep'
    obtain ⟨-, eu7, ep2⟩ := runsTo_ret_inv o2 (RunsTo.carries o1 c2')
    subst ep2
    -- the table phase
    unfold tablePhaseClaims at r2
    obtain ⟨xi, ys1, ys2, u1, hy, q1, q2⟩ := RunsTo.unbind r2 c1
    obtain ⟨-, eu1, ey1⟩ := runsTo_det q1 (runsTo_sampleE _) c1 (r1 := ys2) (r2 := ys1 ++ ys2)
      (by simp)
    have ey1' : ys1 = [] := by simpa using ey1
    subst ey1' eu1
    have c2 := RunsTo.carries q1 c1
    obtain ⟨tc, zs1, zs2, u2, hz, w1, w2⟩ := RunsTo.unbind q2 c2
    obtain ⟨-, -, ez2⟩ := runsTo_ret_inv w2 (RunsTo.carries w1 c2)
    subst ez2
    unfold tableSumcheckClaims at w1
    obtain ⟨⟨ch, cl⟩, v1s, v2s, u3, hv, g1, g2⟩ := RunsTo.unbind w1 c2
    have l2 : v1s.length = 3 * n := runsTo_len g1 c2 fun ys hy ↦ ⟨_, _, zc_run _ _ hy⟩
    have c3 := RunsTo.carries g1 c2
    obtain ⟨⟨fin, cls⟩, x1, x2, u4, hx, m1, m2⟩ := RunsTo.unbind g2 c3
    have c4 := RunsTo.carries m1 c3
    obtain ⟨u, y1, y2, u5, hy', n1, n2⟩ := RunsTo.unbind m2 c4
    have hreq := runsTo_require_inv n1 c4
    obtain ⟨-, -, ey⟩ := runsTo_det n1 (tb_runsTo_require hreq _) c4 (r1 := y2) (r2 := y1 ++ y2)
      (by simp)
    have ey' : y1 = [] := by simpa using ey
    subst ey'
    obtain ⟨-, -, ey2⟩ := runsTo_ret_inv n2 (RunsTo.carries n1 c4)
    subst ey2
    have hf : a1.forms.length = 6 := by
      obtain ⟨ea1, -, -⟩ := runsTo_det r1 (by
        have hb := vt_busRest_run ev (layoutOf bc lm rows) alphas beta point values
          (xs1.take 3) (by simp [l1]) (xs1.getD 3 0) (xs1.getD 4 0) bv hbv ⟨f, []⟩
        rwa [← vt_xs5_split l1] at hb) hcar (r1 := []) (r2 := []) rfl
      rw [ea1]
      exact (vt_forms3_shape bc lm hr alphas beta point (xs1.take 3) (xs1.getD 3 0)
        (xs1.getD 4 0) bv (values.getD 0 0) (values.getD 1 0) (values.getD 2 0)).1
    have hh : (layoutOf bc lm rows).tableLogHeights.length = 6 := vt_tableHeights_length hr
    have l3 : x1.length = 159 := runsTo_len m1 c3 fun ys hy ↦ tableTerms_any _ _ _ _ _ _
      (by rw [hh]) (by rw [hf])
      (by rw [LeanVM.Protocol.EndToEnd.Complete.length_tableWeights, hh]) _ ys hy
    refine ⟨xs1, v1s, x1, ?_, l1, l2, l3, ?_⟩
    · rw [he1, he2, hy, hz, hv, hx, hy', hp]; simp
    · rw [eu7, eu6]; rfl
  obtain ⟨x1, x2, x3, hxs, l1, l2, l3, hpend⟩ := key
  set H := vtHOf bc lm pi alphas point values beta rows f ev bv xs bus claims s'.cap with hH
  have e5 : H.xs5 = x1 := by
    show xs.take 5 = x1; rw [hxs, List.append_assoc, List.take_left' l1]
  have eR : H.xsR = x2 := by
    show (xs.drop 5).take (3 * n) = x2
    rw [hxs, List.append_assoc, List.drop_left' l1, List.take_left' l2]
  have eE : H.evsT = chunks vtW6 x3 := by
    show chunks vtW6 (xs.drop (5 + 3 * n)) = _
    rw [hxs, List.append_assoc, ← List.drop_drop, List.drop_left' l1, List.drop_left' l2]
  have hn' : H.n = n := rfl
  have hfl : H.evsT.flatten = x3 := by rw [eE, chunks_flatten _ _ (by rw [l3]; rfl)]
  have hsplit : xs = H.xs5 ++ H.xsR ++ H.evsT.flatten := by rw [e5, eR, hfl, hxs]
  have hs' : s' = ⟨s'.cap, []⟩ := by cases s'; simp only at hpend; simp [hpend]
  refine ⟨⟨?_, hcar, by rw [e5, l1], by rw [eR, l2, hn'], ?_, ?_, hbv⟩, hsplit, hs', ?_⟩
  · show RunsTo _ ⟨f, []⟩ _ _ ⟨s'.cap, []⟩
    rw [← hsplit, ← hs']; exact h
  · rw [eE, chunks_length, vtH_rowsT_length hr]; rfl
  · intro p hp
    rw [eE] at hp
    exact (zip_chunks H.rowsT (rowsT_fst H hr) x3 l3).2.2 p hp
  · rw [hxs, List.length_append, List.length_append, l1, l2, l3]

end
end LeanVM.Guest.B1.Tables
