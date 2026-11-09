/-
  LeanVM.Guest.B1.Whir.QueriesOpenW

  A level's queries with their witness named: the openings `toOpening` builds of the queries'
  witness and the cap's cells pass `openOne`, and the queries' sum is the Spec's.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesOpen
public import LeanVM.Guest.B1.Whir.InterfaceW
public import LeanVM.Guest.B1.Opening.QueriesW
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The queries' openings, named

`cap_climb_w`: up the cap by the siblings `capSibsOf` reads off the cap's cells (`cap_climb` with
its siblings named). `queries_open_w`: `opening_queries`' meaning with its queries `ws` named
(`MeaningOpeningQueriesW`) over a checked cap gives the openings `ws.map (toOpening …)`, at the
queries' positions, each passing `openOne` at the Spec's position, and the queries' sum their
`enforcedSum`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem capSibsOf_length (rd : Reader) (cap : E) (D p : ℕ) : (capSibsOf rd cap D p).length = D := by
  simp [capSibsOf]

theorem take_capSibsOf_succ {cap : E} {D p j : ℕ} (hj : j < D) :
    (capSibsOf rd cap D p).take (j + 1) = (capSibsOf rd cap D p).take j ++
      [digestOfCells (memRead rd cap (2 * capSib D p j)) (memRead rd cap (2 * capSib D p j + 1))] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [capSibsOf_length]; exact hj)]
  simp [capSibsOf]

/-- **Up the cap by the siblings its cells hold** (`cap_climb`, the siblings named). -/
theorem cap_climb_w {D : ℕ} (hD : 2 ≤ D) {cap flags r0 r1 : E} {root : Digest}
    (hcap : MeaningVerifyMerkleCap D rd [cap, flags] [r0, r1])
    (hroot : (r0, r1) = digestHalves root) {p : ℕ} (hp : p < 2 ^ D) {x : Digest}
    (hx0 : LoadHolds rd cap (2 * (2 ^ D + p)) (digestHalves x).1)
    (hx1 : LoadHolds rd cap (2 * (2 ^ D + p) + 1) (digestHalves x).2)
    (hfl : LoadHolds rd flags (2 ^ (D - 1) + p / 2) 1) :
    climbD x p (capSibsOf rd cap D p) = root := by
  obtain ⟨cell, fl, hc, hf, hh, hpin, hret⟩ := hcap
  have hD2 : 2 ^ (D + 2) = 4 * 2 ^ D := by rw [pow_add]; ring
  have hpow : ∀ j, j < D → 2 ≤ 2 ^ (D - j) := fun j hj ↦ by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ D - j by omega)
    simpa using this
  have hle : ∀ j, 2 ^ (D - j) ≤ 2 ^ D := fun j ↦ Nat.pow_le_pow_right (by norm_num) (by omega)
  have chain : ∀ j, 1 ≤ j → j < D → fl (capAnc D p j) ≠ 0 := by
    intro j hj1 hjD
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · show fl (capAnc D p 1) ≠ 0
        have hA : capAnc D p 1 = 2 ^ (D - 1) + p / 2 := by simp [capAnc]
        have hb := capAnc_bounds hp (show 1 ≤ D by omega)
        have hD1 := two_pow_sub_succ (show 0 < D by omega)
        simp only [Nat.sub_zero, Nat.zero_add] at hD1
        have h1 := (hf (capAnc D p 1) (by have := hpow 1 (by omega); omega)
          (by omega)).1
        rw [hA] at h1 ⊢
        rw [loadHolds_unique h1 hfl]
        exact one_ne_zero
      · intro h0
        have hprev := ih (by omega) (by omega)
        have hb := capAnc_bounds hp (show j + 1 ≤ D by omega)
        have hs := capAnc_succ (p := p) (show j < D by omega)
        have hD1 := two_pow_sub_succ (show j < D by omega)
        have hle' := hle j
        have hpw := hpow (j + 1) hjD
        have hle2 : 2 * 2 ^ (D - j) ≤ 2 ^ D := by
          rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        generalize p / 2 ^ j = t at hs
        obtain ⟨z0, z1⟩ := hpin (capAnc D p (j + 1)) (by omega) (by omega) h0
        have hbj := capAnc_bounds hp (show j ≤ D by omega)
        have hfj := (hf (capAnc D p j) (by omega) (by omega)).1
        apply hprev
        rcases Nat.mod_two_eq_zero_or_one t with hb0 | hb1
        · rw [hs, hb0, Nat.add_zero] at hfj ⊢
          exact loadHolds_unique hfj z0
        · rw [hs, hb1] at hfj ⊢
          exact loadHolds_unique hfj z1
  have climb : ∀ j, j ≤ D →
      (cell (2 * capAnc D p j), cell (2 * capAnc D p j + 1)) =
        digestHalves (climbD x p ((capSibsOf rd cap D p).take j)) := by
    intro j hjD
    induction j with
    | zero =>
      have e : capAnc D p 0 = 2 ^ D + p := by simp [capAnc]
      have hpD := Nat.one_le_two_pow (n := D)
      rw [List.take_zero, e, climbD_nil, loadHolds_unique (hc _ (by omega) (by omega)) hx0,
        loadHolds_unique (hc _ (by omega) (by omega)) hx1]
    | succ j ih =>
      have hcs := ih (by omega)
      have hb := capAnc_bounds hp (show j + 1 ≤ D by omega)
      have hbj := capAnc_bounds hp (show j ≤ D by omega)
      have hs := capAnc_succ (p := p) (show j < D by omega)
      have hle2 : 2 * 2 ^ (D - (j + 1)) ≤ 2 ^ D := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hflag : capAnc D p (j + 1) = 1 ∨ fl (capAnc D p (j + 1)) ≠ 0 := by
        rcases Nat.lt_or_ge (j + 1) D with h | h
        · exact Or.inr (chain (j + 1) (by omega) h)
        · left; rw [show j + 1 = D by omega]; exact capAnc_last hp
      obtain ⟨dl, dr, hl', hr', hpar⟩ := hashesPair_digests
        (hh (capAnc D p (j + 1)) (by have := Nat.one_le_two_pow (n := D - (j + 1)); omega)
          (by omega) hflag)
      have hlen : ((capSibsOf rd cap D p).take j).length = j := by
        rw [List.length_take, capSibsOf_length]; omega
      rw [take_capSibsOf_succ (by omega), climbD_snoc, hlen]
      set A := capAnc D p (j + 1) with hA
      have hcell : ∀ k, 2 ≤ k → k < 2 ^ (D + 2) → memRead rd cap k = cell k :=
        fun k h1 h2 ↦ memRead_of_load (hc k h1 h2)
      rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ j) with hb0 | hb1
      · have hsib : capSib D p j = 2 * A + 1 := by
          unfold capSib; simp only [hb0, ↓reduceIte]; unfold capAnc at hs; omega
        rw [hs, hb0, Nat.add_zero, show 2 * (2 * A) = 4 * A by ring] at hcs
        have hy : dl = climbD x p ((capSibsOf rd cap D p).take j) :=
          capDigestScalars_injective (hl'.symm.trans hcs)
        have hdr : digestOfCells (memRead rd cap (2 * capSib D p j))
            (memRead rd cap (2 * capSib D p j + 1)) = dr := by
          rw [hsib, hcell _ (by omega) (by omega), hcell _ (by omega) (by omega),
            show 2 * (2 * A + 1) = 4 * A + 2 by ring, show 4 * A + 2 + 1 = 4 * A + 3 by ring]
          simp only [Prod.ext_iff] at hr'
          rw [hr'.1, hr'.2, digestOfCells_scalars]
        simp only [hb0, ↓reduceIte]
        rw [← hy, hdr]
        exact hpar
      · have hsib : capSib D p j = 2 * A := by
          unfold capSib; simp only [show ¬ (p / 2 ^ j % 2 = 0) by omega, ↓reduceIte]; unfold capAnc at hs; omega
        rw [hs, hb1, show 2 * (2 * A + 1) = 4 * A + 2 by ring] at hcs
        have hy : dr = climbD x p ((capSibsOf rd cap D p).take j) :=
          capDigestScalars_injective (hr'.symm.trans hcs)
        have hdl : digestOfCells (memRead rd cap (2 * capSib D p j))
            (memRead rd cap (2 * capSib D p j + 1)) = dl := by
          rw [hsib, hcell _ (by omega) (by omega), hcell _ (by omega) (by omega),
            show 2 * (2 * A) = 4 * A by ring]
          simp only [Prod.ext_iff] at hl'
          rw [hl'.1, hl'.2, digestOfCells_scalars]
        simp only [show ¬ (p / 2 ^ j % 2 = 0) by omega, ↓reduceIte]
        rw [← hy, hdl]
        exact hpar
  have hcs := climb D le_rfl
  rw [capAnc_last hp, List.take_of_length_le (by rw [capSibsOf_length])] at hcs
  simp only [List.cons.injEq, and_true] at hret
  refine capDigestScalars_injective ?_
  rw [← hcs, ← hroot, hret.1, hret.2]

/-- **A query's opening passes `openOne`**: its row, its siblings below the cap, then the cap's
siblings its cells hold. -/
theorem query_openOne_w {D depth width : ℕ} (hD : 2 ≤ D) (hDd : D ≤ depth)
    {cap flags r0 r1 : E} {root : Digest}
    (hcap : MeaningVerifyMerkleCap D rd [cap, flags] [r0, r1])
    (hroot : (r0, r1) = digestHalves root) {q : ℕ} (hq : q < 2 ^ depth) {row : List K}
    (hw : row.length = width) {sibs : List Digest} (hsl : sibs.length = depth - D)
    (h0 : LoadHolds rd cap (2 * (2 ^ D + q / 2 ^ (depth - D)))
      (digestHalves (climbD (merkleLeafDigest row) q sibs)).1)
    (h1 : LoadHolds rd cap (2 * (2 ^ D + q / 2 ^ (depth - D)) + 1)
      (digestHalves (climbD (merkleLeafDigest row) q sibs)).2)
    (hfl : LoadHolds rd flags (2 ^ (D - 1) + q / 2 ^ (depth - D + 1)) 1) :
    Id.run (Compile.openOneWithHash (m := Id) keccak256 root depth width q
      (toOpening rd cap D depth (q, row, sibs))) = true := by
  have hp : q / 2 ^ (depth - D) < 2 ^ D := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_cancel' hDd]
    exact hq
  have hf2 : q / 2 ^ (depth - D + 1) = q / 2 ^ (depth - D) / 2 := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hf2] at hfl
  have hc := cap_climb_w hD hcap hroot hp h0 h1 hfl
  unfold Compile.openOneWithHash toOpening
  rw [ite_pos' ⟨hw, by simp [hsl, capSibsOf_length]; omega⟩]
  show decide ((climbD (merkleLeafDigest row) q (sibs ++ capSibsOf rd cap D (q / 2 ^ (depth - D)))).toList =
    root.toList) = true
  rw [climbD_append, hsl, hc]
  exact decide_eq_true rfl

/-- A frame run's word read by a load is the run's. -/
theorem frameRun_load {p v : E} {n i : ℕ} {f : ℕ → E} (h : FrameRun rd p n f) (hi : i < n)
    (hl : LoadHolds rd p i v) : v = f i := h.2 i hi v hl.2

/-- Two positions whose windows a run holds are equal. -/
theorem winPos_unique {p : E} {d cd q q' : ℕ} (hcd : cd ≤ 8) (hq : q < 2 ^ d) (hq' : q' < 2 ^ d)
    (hl : ∀ i < qwN d cd, LoadHolds rd p i (gen ^ qwVal d cd q i))
    (hr : FrameRun rd p (qwN d cd) fun i ↦ gen ^ qwVal d cd q' i) : q = q' := by
  have hl' : ∀ i < qwN d cd, LoadHolds rd p i (gen ^ qwVal d cd q' i) := by
    intro i hi
    have := hl i hi
    rwa [frameRun_load hr hi this] at this
  rw [← winPosOf_eq hcd hq hl, winPosOf_eq hcd hq' hl']

/-- **The queries' openings and sum, named.** -/
theorem queries_open_w {odd base I depth cd q N0 : ℕ} {cap flags lam lamN qptrs wp nG sum r0 r1 : E}
    {root : Digest} {ws : List QW} {cap0 : E} (hc0 : cap0 = cap)
    (hm : MeaningOpeningQueriesW odd base I depth cd rd ws [cap, flags, lam, lamN, qptrs, wp, nG]
      [sum])
    (hcap : MeaningVerifyMerkleCap cd rd [cap, flags] [r0, r1])
    (hroot : (r0, r1) = digestHalves root) (hcd : 2 ≤ cd) (hcd8 : cd ≤ 8) (hcdd : cd ≤ depth)
    (hnG : nG = gen ^ N0) (hN0 : N0 < ordG) (hQ : oqCount odd base N0 = q) (hodd : odd ≤ 1)
    (hb : base = 1 ∨ (base = 0 ∧ odd = 0))
    (qs : List ℕ) (hqsl : qs.length = q) (hqlt : ∀ k < q, qs.getD k 0 < 2 ^ depth)
    (hbits : ∀ k < q, ∃ bp, LoadHolds rd qptrs k bp ∧
      FrameRun rd bp (qwN depth cd) fun i ↦ gen ^ qwVal depth cd (qs.getD k 0) i)
    (hlamN : lamN = lam ^ q) {width : ℕ} (hwidth : (if base = 1 then I else 3 * I) = width)
    (specRow : List K → List E) (fd : List E)
    (hdot : ∀ (row : List K) (w : ℕ → E), row.length = width →
      (∀ l < rowLo I + I / rowLo I, LoadHolds rd wp l (w l)) →
        rowDot base I row w = dot (specRow row) (eqKernel fd)) :
    (ws.map (toOpening rd cap0 cd depth)).length = q ∧
      (∀ k (hk : k < qs.length) (ho : k < (ws.map (toOpening rd cap0 cd depth)).length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root depth width qs[k]
          (ws.map (toOpening rd cap0 cd depth))[k]) = true) ∧
      sum = enforcedSum (((ws.map (toOpening rd cap0 cd depth)).map (·.leaf)).map specRow) fd
        (powers lam q) ∧
      (ws.map (toOpening rd cap0 cd depth)).map Opening.leafIndex = qs := by
  subst hc0
  obtain ⟨N, hN, hnG', hlam, hwl, bps, ds, hall, ch, -, hret⟩ := hm
  have hNN : N = N0 := gen_pow_inj hN hN0 (hnG'.symm.trans hnG)
  subst hNN
  rw [hQ] at hwl hall
  have hql : (ws.map (toOpening rd cap0 cd depth)).length = q := by rw [List.length_map, hwl]
  -- the positions
  have hqs' : ∀ k < q, (ws.getD k default).1 = qs.getD k 0 := by
    intro k hk
    obtain ⟨hbp, hlt, hb', -⟩ := hall k hk
    obtain ⟨bp, hbp', hbits'⟩ := hbits k hk
    have e := loadHolds_unique hbp hbp'
    subst e
    exact winPos_unique hcd8 hlt (hqlt k hk) hb' hbits'
  have hget : ∀ k (hk : k < q), (ws.map (toOpening rd cap0 cd depth))[k]'(by rw [hql]; exact hk) =
      toOpening rd cap0 cd depth (ws.getD k default) := by
    intro k hk
    rw [List.getElem_map, List.getD_eq_getElem _ _ (by rw [hwl]; exact hk)]
  refine ⟨hql, fun k hk ho ↦ ?_, ?_, ?_⟩
  · have hkq : k < q := by rw [hql] at ho; exact ho
    obtain ⟨-, hlt, -, hop⟩ := hall k hkq
    obtain ⟨hrow, hsl, w, -, h0, h1, hfl, -⟩ := hop
    rw [hget k hkq, ← List.getD_eq_getElem _ 0 hk, ← hqs' k hkq]
    exact query_openOne_w hcd hcdd hcap hroot hlt (hrow.trans hwidth) hsl h0 h1 hfl
  · have hds : ∀ k < q, ds k = dot (specRow (ws.getD k default).2.1) (eqKernel fd) := by
      intro k hk
      obtain ⟨-, -, -, hrow, -, w, hw, -, -, -, hd⟩ := hall k hk
      rw [hd]
      exact hdot _ _ (hrow.trans hwidth) hw
    obtain ⟨hret, -⟩ := List.cons_eq_cons.mp hret
    rw [hret, hlamN, ← hQ, oqChain_powers hlam hodd hb, hQ]
    have hrl : (((ws.map (toOpening rd cap0 cd depth)).map (·.leaf)).map specRow).length = q := by
      simp [hwl]
    rw [← hrl, enforcedSum_eq, hrl]
    unfold powSum
    have hL : ∀ k < q, (((ws.map (toOpening rd cap0 cd depth)).map (·.leaf)).map specRow).getD k [] =
        specRow (ws.getD k default).2.1 := by
      intro k hk
      rw [List.getD_eq_getElem _ _ (by simp [hwl]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [toOpening]
    have hmap : (List.range q).map (fun k ↦ lam ^ k * ds k) =
        (List.range q).map (fun k ↦ lam ^ k *
          dot ((((ws.map (toOpening rd cap0 cd depth)).map (·.leaf)).map specRow).getD k [])
            (eqKernel fd)) := by
      refine List.map_congr_left fun k hk ↦ ?_
      have hk' : k < q := List.mem_range.mp hk
      rw [hds k hk', hL k hk']
    rw [hmap]
  · apply List.ext_getElem (by simp [hwl, hqsl])
    intro k h1 h2
    have hk : k < q := by simpa [hwl] using h1
    have e := hqs' k hk
    rw [List.getD_eq_getElem _ _ (by rw [hwl]; exact hk), List.getD_eq_getElem _ _ h2] at e
    simpa [toOpening] using e

theorem meaningW_args {odd base I depth cd : ℕ} {ws : List QW} {A A' R : List E}
    (h : MeaningOpeningQueriesW odd base I depth cd rd ws A R) (e : A = A') :
    MeaningOpeningQueriesW odd base I depth cd rd ws A' R := e ▸ h

end
end LeanVM.Guest.B1.Whir
