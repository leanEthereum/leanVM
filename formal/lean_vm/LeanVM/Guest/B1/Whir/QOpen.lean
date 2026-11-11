/-
  LeanVM.Guest.B1.Whir.QOpen

  A level's queries: the openings `toOpening` builds of the queries' witness and the cap's cells
  pass `openOne` against the level's root.
-/

module

public import LeanVM.Guest.B1.Whir.Witness
public import LeanVM.Guest.B1.Merkle.Climb
public import LeanVM.Guest.B1.Opening.QueriesW
public import LeanVM.Protocol.WithHash

/-!
# The queries' openings (G:1638-1642, 1695-1702)

`cap_climb_w`: up the cap by the siblings `capSibsOf` reads off the cap's cells, a node whose cells
the cap check (`verify_merkle_cap`) holds and whose parent is flagged reaches the root.
`query_openOne_w`: a query's opening (`toOpening`: its row, its siblings below the cap, then the
cap's) passes `openOne`. `queries_open`: `opening_queries`' meaning with its queries `ws` named
(`MeaningOpeningQueriesW`), over a checked cap and at positions the decodes wrote, gives the
openings `ws.map (toOpening …)` at the positions `qs`, each passing `openOne`, the rounds read
from `coefs` and the chain of the folds returned.
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


/-- **A level's queries, opened** (`opening_queries` over a checked cap): the openings
`ws.map (toOpening …)` sit at the positions `qs` and pass `openOne` against the root; the rounds
and the final coefficients the meaning reads; each query's fold. -/
theorem queries_open {sh : OqShape} {cap flags lamInv coefs hs positions qptrs nG r0 r1 : E}
    {rets : List E} {root : Digest} {ws : List QW} {N0 Q : ℕ}
    (hm : MeaningOpeningQueriesW sh rd ws [cap, flags, lamInv, coefs, hs, positions, qptrs, nG] rets)
    (hcap : MeaningVerifyMerkleCap sh.cd rd [cap, flags] [r0, r1])
    (hroot : (r0, r1) = digestHalves root) (hcd : 2 ≤ sh.cd) (hcd8 : sh.cd ≤ 8)
    (hcdd : sh.cd ≤ sh.depth) (hnG : nG = gen ^ N0) (hN0 : N0 < ordG)
    (hQ : oqCount sh.odd sh.base N0 = Q) (hQpos : 0 < Q) (qs : List ℕ) (hqsl : qs.length = Q)
    (hqlt : ∀ k < Q, qs.getD k 0 < 2 ^ sh.depth)
    (hbits : ∀ k < Q, ∃ bp, LoadHolds rd qptrs k bp ∧
      FrameRun rd bp (qwN sh.depth sh.cd) fun i ↦ gen ^ qwVal sh.depth sh.cd (qs.getD k 0) i) :
    ∃ (rounds : List FoldRound) (hsv : List E), rounds.length = sh.folds ∧ hsv.length = sh.nHs ∧
      RoundsAt rd coefs rounds ∧ (sh.final = 1 → WordsAt rd hs hsv) ∧
      (ws.map (toOpening rd cap sh.cd sh.depth)).length = Q ∧
      (∀ k (hk : k < qs.length) (ho : k < (ws.map (toOpening rd cap sh.cd sh.depth)).length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root sh.depth (rowLen sh.base sh.folds)
          qs[k] (ws.map (toOpening rd cap sh.cd sh.depth))[k]) = true) ∧
      (ws.map (toOpening rd cap sh.cd sh.depth)).map Opening.leafIndex = qs ∧
      (∀ k < Q, (ws.getD k default).1 = qs.getD k 0) ∧
      (sh.final = 1 → ∀ k < Q, qwFold sh.base rounds (ws.getD k default) =
        novelSum hsv (wsChain (sh.vs.map K.ofBits) (eOfNat (qs.getD k 0))) sh.nHs sh.hsBits) ∧
      (sh.final = 1 → rets = [0]) ∧
      (sh.final ≠ 1 → rets = [oqChain sh.odd sh.base lamInv
        (fun k ↦ qwFold sh.base rounds (ws.getD k default)) N0]) := by
  obtain ⟨N, hN, hnG', hwl, rounds, hsv, hrl, hhl, hall, hret⟩ := hm
  have hNN : N = N0 := gen_pow_inj hN hN0 (hnG'.symm.trans hnG)
  subst hNN
  rw [hQ] at hwl hall
  have hql : (ws.map (toOpening rd cap sh.cd sh.depth)).length = Q := by rw [List.length_map, hwl]
  have hqs' : ∀ k < Q, (ws.getD k default).1 = qs.getD k 0 := by
    intro k hk
    obtain ⟨-, -, -, hlt, ⟨bp, hbp, hb'⟩, -⟩ := hall k hk
    obtain ⟨bp', hbp', hbits'⟩ := hbits k hk
    have e := loadHolds_unique hbp hbp'
    subst e
    exact winPos_unique hcd8 hlt (hqlt k hk) hb' hbits'
  have hget : ∀ k (hk : k < Q), (ws.map (toOpening rd cap sh.cd sh.depth))[k]'(by rw [hql]; exact hk) =
      toOpening rd cap sh.cd sh.depth (ws.getD k default) := by
    intro k hk
    rw [List.getElem_map, List.getD_eq_getElem _ _ (by rw [hwl]; exact hk)]
  refine ⟨rounds, hsv, hrl, hhl, (hall 0 hQpos).1, (hall 0 hQpos).2.1, hql, fun k hk ho ↦ ?_, ?_, hqs',
    fun hf k hk ↦ ?_, fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have hkq : k < Q := by rw [hql] at ho; exact ho
    obtain ⟨-, -, -, hlt, -, hop, -⟩ := hall k hkq
    obtain ⟨hrow, hsl, h0, h1, hfl⟩ := hop
    rw [hget k hkq, ← List.getD_eq_getElem _ 0 hk, ← hqs' k hkq]
    exact query_openOne_w hcd hcdd hcap hroot hlt hrow hsl h0 h1 hfl
  · apply List.ext_getElem (by simp [hwl, hqsl])
    intro k h1 h2
    have hk : k < Q := by simpa [hwl] using h1
    have e := hqs' k hk
    rw [List.getD_eq_getElem _ _ (by rw [hwl]; exact hk), List.getD_eq_getElem _ _ h2] at e
    simpa [toOpening] using e
  · rw [← hqs' k hk]; exact (hall k hk).2.2.2.2.2.2 hf
  · simpa [hf] using hret
  · simp only [hf, ↓reduceIte] at hret
    obtain ⟨-, -, h⟩ := hret
    exact h

end
end LeanVM.Guest.B1.Whir
