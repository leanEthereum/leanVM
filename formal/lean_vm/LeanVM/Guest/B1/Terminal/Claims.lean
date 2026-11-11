/-
  LeanVM.Guest.B1.Terminal.Claims

  Each claim's term of `check_opening_terminal`'s sum is the claim's batched weight on the stack.
-/

module

public import LeanVM.Guest.B1.Terminal.Blocks
public import LeanVM.Guest.B1.Terminal.Weights
public import LeanVM.Guest.B1.Terminal.Layout

/-!
# The claims' terms

`ClaimsCtx` collects what the head of `check_opening_terminal` and its precondition establish
about the words the claims' blocks read: the selectors (`selProd` of each committed column's offset
bits), the chains at `zeta` and `chi` (the points' weights), the slot points, the public input's
chain, the columns' sizes (over the base `[0, log_mem, τ_0, …, τ_5]`, `kbExp`) and placements and
the claims' points and their low lengths (`claimLow`). A claim's source and adjustment are its
column's (`claimKappa_col`, `claimKappa_lane`), so its low length is its column's size.
`claimTerm_eq`: claim `j`'s term at `λ^(1 + poolRank j)` is that power times its weight on the
stack, `0` for an output lane.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

/-- The claims' global columns: the bus's `0 .. 4`, the tables' `6 .. 164`, the public input's
`0 .. 2`. -/
def claimColOf (j : ℕ) : ℕ := if j < 5 then j else if j < 164 then j + 1 else j - 164

theorem claimColumns_eq : Tables.claimColumns = (List.range 167).map claimColOf := by
  decide +kernel

theorem claimColumns_getD {j : ℕ} (hj : j < 167) : Tables.claimColumns.getD j 0 = claimColOf j := by
  rw [claimColumns_eq, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getElem_range]

theorem claimCol_out {j : ℕ} (hj : j < 167) :
    Tables.claimColumns.getD j 0 ∈ keccakOutputColumns ↔ 112 ≤ j ∧ j < 137 := by
  rw [claimColumns_getD hj, keccakOutputColumns_eq, claimColOf]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, he⟩; split at he <;> [omega; split at he <;> omega]
  · rintro ⟨h1, h2⟩; exact ⟨j - 112, by omega, by split <;> [omega; split <;> omega]⟩

theorem gen_pow_inj_le {a b : ℕ} (ha : a ≤ 64) (hb : b ≤ 64) (h : gen ^ a = gen ^ b) : a = b :=
  gen_pow_inj (lt_of_le_of_lt ha (by norm_num)) (lt_of_le_of_lt hb (by norm_num)) h

/-- The exponents of `kappa_base`: `[0, log_mem, τ_0, …, τ_5]`. -/
def kbExp (layout : Layout) (i : ℕ) : ℕ :=
  ([0, layout.logMemory] ++ layout.tableLogHeights).getD i 0

theorem cLow_kbExp (layout : Layout) (j : ℕ) : cLow (kbExp layout) j = claimLow layout j := rfl

/-- A claim on a chain (kinds `0`, `1`) has its column's source and adjustment. -/
theorem claimKappa_col_all :
    (List.range Tables.nClaims).all (fun j ↦ !(decide (termKind j < 2)) ||
      (Tables.colKappaSrc (termCol j) == claimKappaSrc j &&
        Tables.colKappaAdj (termCol j) == claimKappaAdj j)) = true := by
  decide +kernel

theorem claimKappa_col {j : ℕ} (hj : j < Tables.nClaims) (hk : termKind j < 2) :
    Tables.colKappaSrc (termCol j) = claimKappaSrc j ∧
      Tables.colKappaAdj (termCol j) = claimKappaAdj j := by
  have := List.all_eq_true.mp claimKappa_col_all j (List.mem_range.mpr hj)
  simpa [hk] using this

/-- A `q_keccak` lane's claim (kind `2`) is `KECCAK`'s height long. -/
theorem claimKappa_lane {j : ℕ} (hk : termKind j = 2) :
    claimKappaSrc j = 7 ∧ claimKappaAdj j = 0 := by
  unfold termKind at hk
  unfold claimKappaSrc claimKappaAdj
  split_ifs at hk ⊢ <;> omega

/-- What the head and the precondition give the claims' blocks. -/
structure ClaimsCtx (rd : Reader) (σ : Val) (layout : Layout) (kappas : List ℕ)
    (claims : List ColumnClaim) (zs chis x : List E) (rm : E) : Prop where
  hkap : kappas.length = 165
  hKC : Tables.committedKappas kappas = (List.range Tables.nCommittedCols).map fun c ↦
    (0 :: layout.logMemory :: layout.tableLogHeights).getD (Tables.colKappaSrc c) 0 +
      Tables.colKappaAdj c
  hP : layout.placements = (placementsOf kappas).1
  hx : x.length = layout.stackLog
  hL : layout.stackLog ≤ 32
  hK : ∀ c < Tables.nCommittedCols, (Tables.committedKappas kappas).getD c 0 ≤ layout.stackLog
  hq : 2 ^ (Tables.committedKappas kappas).getD 5 0 ∣
    (stackOffsets (Tables.committedKappas kappas)).1.getD 5 0
  hK5 : (Tables.committedKappas kappas).getD 5 0 = layout.tableLogHeights.getD opKeccak 0 + 6
  hlane : ∀ g, 73 ≤ g → g < 165 → kappas.getD g 0 = layout.tableLogHeights.getD opKeccak 0
  hmem : ∀ c < 3, (Tables.committedKappas kappas).getD c 0 = layout.logMemory
  hlm : 1 ≤ layout.logMemory
  hmem0 : (layout.placement memory0).variableCount = layout.logMemory
  hcols : claims.map (·.column) = Tables.claimColumns
  hzs : zs.length ≤ 40
  hchis : chis.length ≤ zs.length
  hpz : ∀ j < 5, (claims.getD j default).point = zs.take (claims.getD j default).point.length
  hpc : ∀ j, 5 ≤ j → j < 164 →
    (claims.getD j default).point = chis.take (claims.getD j default).point.length
  hpp : ∀ j, 164 ≤ j → j < 167 → (claims.getD j default).point =
    rm :: List.replicate ((layout.placement memory0).variableCount - 1) 0
  hlen : ∀ j < 164, (claims.getD j default).point.length = claimLow layout j
  hsel : ∀ c < Tables.nCommittedCols, σ (.n (selV c)) =
    selProd ((stackOffsets (Tables.committedKappas kappas)).1.getD c 0)
      ((Tables.committedKappas kappas).getD c 0)
      (layout.stackLog - (Tables.committedKappas kappas).getD c 0) x
  hzc : ∀ n ≤ zs.length, n ≤ layout.stackLog →
    valOf rd (σ (.n 18)) n = eqEval (zs.take n) (x.take n)
  hrc : ∀ n ≤ chis.length, n ≤ layout.stackLog →
    valOf rd (σ (.n 20)) n = eqEval (chis.take n) (x.take n)
  hs1 : ∀ k < 6, valOf rd (σ (.n 22)) k = x.getD (layout.tableLogHeights.getD opKeccak 0 + k) 0
  hs0 : ∀ k < 6, valOf rd (σ (.n 23)) k = 1 + x.getD (layout.tableLogHeights.getD opKeccak 0 + k) 0
  hpi : σ (.n 32) = eqEval (rm :: List.replicate (layout.logMemory - 1) 0) (x.take layout.logMemory)

theorem ClaimsCtx.kappa_eq {rd : Reader} {σ : Val} {layout : Layout} {kappas : List ℕ}
    {claims : List ColumnClaim} {zs chis x : List E} {rm : E}
    (T : ClaimsCtx rd σ layout kappas claims zs chis x rm) {c : ℕ}
    (hc : c < Tables.nCommittedCols) :
    (Tables.committedKappas kappas).getD c 0 =
      (0 :: layout.logMemory :: layout.tableLogHeights).getD (Tables.colKappaSrc c) 0 +
        Tables.colKappaAdj c := by
  rw [T.hKC, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

theorem claim_column {claims : List ColumnClaim} (hcols : claims.map (·.column) = Tables.claimColumns)
    {j : ℕ} (hj : j < 167) : (claims.getD j default).column = claimColOf j := by
  have hl : claims.length = 167 := by
    rw [← List.length_map (f := (·.column)), hcols, claimColumns_eq]; simp
  rw [← claimColumns_getD hj, ← hcols, List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]

/-- A pooled claim on a committed column, its point a prefix of `A` read by the chain `ch`. -/
theorem term_committed {layout : Layout} {kappas : List ℕ} {x : List E} {c : ColumnClaim}
    {cc : ℕ} (hcc : cc < Tables.nCommittedCols) (hkap : kappas.length = 165)
    (hP : layout.placements = (placementsOf kappas).1)
    (hcol : c.column = (Tables.committedCols 165).getD cc 0)
    (hx : x.length = layout.stackLog) (hK : (Tables.committedKappas kappas).getD cc 0 ≤ layout.stackLog)
    (hlen : c.point.length = (Tables.committedKappas kappas).getD cc 0) {L chainV sel : E}
    (hch : chainV = eqEval c.point (x.take c.point.length))
    (hsel : sel = selProd ((stackOffsets (Tables.committedKappas kappas)).1.getD cc 0)
      ((Tables.committedKappas kappas).getD cc 0)
      (layout.stackLog - (Tables.committedKappas kappas).getD cc 0) x) :
    L * chainV * sel = L * wOf layout x c := by
  rw [wOf_committed (by rw [hcol]; exact placement_committed hkap hP hcc) hlen hx hK, hch, hsel,
    hlen, mul_assoc]

/-- The slot factor is the slot's bits' weight. -/
theorem slotProd_eq {τ s : ℕ} {x : List E} {s1 s0 : ℕ → E} (h1 : ∀ k < 6, s1 k = x.getD (τ + k) 0)
    (h0 : ∀ k < 6, s0 k = 1 + x.getD (τ + k) 0) :
    slotProd s1 s0 s = ∏ i ∈ range 6, bitF (s.testBit i) (x.getD (τ + i) 0) := by
  have hf : ∀ k < 6, (if s.testBit k then s1 k else s0 k) = bitF (s.testBit k) (x.getD (τ + k) 0) := by
    intro k hk
    unfold bitF
    split
    · exact h1 k hk
    · exact h0 k hk
  simp only [slotProd, prod_range_succ, prod_range_zero, one_mul]
  rw [hf 0 (by decide), hf 1 (by decide), hf 2 (by decide), hf 3 (by decide), hf 4 (by decide),
    hf 5 (by decide)]
  ring

/-- **Claim `j`'s term** is its batched weight on the stack, `0` on an output lane. -/
theorem claimTerm_eq {rd : Reader} {σ : Val} {layout : Layout} {kappas : List ℕ}
    {claims : List ColumnClaim} {zs chis x : List E} {lam rm : E}
    (T : ClaimsCtx rd σ layout kappas claims zs chis x rm) {j : ℕ} (hj : j < 167) :
    claimTerm rd σ (kbExp layout) (lam ^ (1 + poolRank j)) j =
      if Tables.claimColumns.getD j 0 ∉ keccakOutputColumns then
        lam ^ (1 + poolRank j) * wOf layout x (claims.getD j default) else 0 := by
  have hcolj := claim_column T.hcols hj
  have hout := claimCol_out hj
  by_cases h4 : 112 ≤ j ∧ j < 137
  · have hk : termKind j = 4 := by unfold termKind; split_ifs <;> omega
    simp only [claimTerm, hk, hout.mpr h4, not_true_eq_false, ↓reduceIte]
  have hnot : Tables.claimColumns.getD j 0 ∉ keccakOutputColumns := fun h ↦ h4 (hout.mp h)
  simp only [hnot, not_false_eq_true, ↓reduceIte]
  have hL := T.hL
  have hzs := T.hzs
  have hchis := T.hchis
  have hNC : Tables.nCommittedCols = 101 := rfl
  -- a chain claim's low length is its column's size
  have hlenK : ∀ (hk : termKind j < 2) (hcc : termCol j < Tables.nCommittedCols),
      (claims.getD j default).point.length =
        (Tables.committedKappas kappas).getD (termCol j) 0 := by
    intro hk hcc
    have hj162 : j < 164 := by unfold termKind at hk; split_ifs at hk <;> omega
    obtain ⟨e1, e2⟩ := claimKappa_col hj hk
    rw [T.hlen j hj162, T.kappa_eq hcc, claimLow, e1, e2]
    rfl
  by_cases h0 : j < 5
  · have hk : termKind j = 0 := by unfold termKind; simp [h0]
    have ht : termCol j = j := by unfold termCol; simp [h0]
    simp only [claimTerm, hk]
    have hp := T.hpz j h0
    have hpl : (claims.getD j default).point.length ≤ zs.length := by
      have := congrArg List.length hp; rw [List.length_take] at this; omega
    have hκ := hlenK (by omega) (by rw [ht]; omega)
    rw [ht] at hκ ⊢
    have hKj := T.hK j (by omega)
    refine term_committed (cc := j) (by omega) T.hkap T.hP ?_ T.hx hKj hκ ?_
      (T.hsel j (by omega))
    · rw [hcolj, committedCols_getD (by omega)]; simp [claimColOf, colOfCommitted, h0]; omega
    · rw [cLow_kbExp, ← T.hlen j (by omega), T.hzc _ hpl (by rw [hκ]; exact hKj), ← hp]
  by_cases h1 : j < 72 ∨ j = 86 ∨ (137 ≤ j ∧ j < 164)
  · have hk : termKind j = 1 := by unfold termKind; split_ifs <;> omega
    have ht : termCol j = if j < 72 then j + 1 else if j = 86 then 73 else j - 63 := by
      unfold termCol; split_ifs <;> omega
    simp only [claimTerm, hk]
    have hp := T.hpc j (by omega) (by omega)
    have hpl : (claims.getD j default).point.length ≤ chis.length := by
      have := congrArg List.length hp; rw [List.length_take] at this; omega
    have hcc : termCol j < Tables.nCommittedCols := by rw [ht]; split_ifs <;> omega
    have hκ := hlenK (by omega) hcc
    have hKj := T.hK _ hcc
    refine term_committed (cc := termCol j) hcc T.hkap T.hP ?_ T.hx hKj hκ ?_ (T.hsel _ hcc)
    · rw [hcolj, committedCols_getD hcc, ht, claimColOf, colOfCommitted]; split_ifs <;> omega
    · rw [cLow_kbExp, ← T.hlen j (by omega), T.hrc _ hpl (by rw [hκ]; exact hKj), ← hp]
  by_cases h2 : (72 ≤ j ∧ j < 86) ∨ (87 ≤ j ∧ j < 112)
  · have hk : termKind j = 2 := by unfold termKind; split_ifs <;> omega
    simp only [claimTerm, hk]
    have hp := T.hpc j (by omega) (by omega)
    have hpl : (claims.getD j default).point.length ≤ chis.length := by
      have := congrArg List.length hp; rw [List.length_take] at this; omega
    have hK5 := T.hK 5 (by decide)
    rw [T.hK5] at hK5
    have hκ : (claims.getD j default).point.length = layout.tableLogHeights.getD opKeccak 0 := by
      obtain ⟨e1, e2⟩ := claimKappa_lane hk
      rw [T.hlen j (by omega), claimLow, e1, e2]
      rfl
    have hpl' : layout.placement (claims.getD j default).column =
        Placement.mk (layout.tableLogHeights.getD opKeccak 0)
          ((stackOffsets (Tables.committedKappas kappas)).1.getD 5 0 +
            termSlot j * 2 ^ layout.tableLogHeights.getD opKeccak 0) := by
      have e1 : claimColOf j = j + 1 := by simp [claimColOf, show ¬ j < 5 by omega, show j < 164 by omega]
      have es : slotOfCol (j + 1) = some (termSlot j) := by
        unfold slotOfCol termSlot; split_ifs <;> first | rfl | omega
      rw [hcolj, e1, placement_slot T.hkap T.hP (by omega) es, T.hlane _ (by omega) (by omega)]
    have hslot : termSlot j < 64 := by unfold termSlot; split_ifs <;> omega
    have hq := T.hq
    rw [T.hK5] at hq
    rw [wOf_lane hpl' hκ T.hx hK5 hq hslot, T.hsel 5 (by decide), T.hK5,
      slotProd_eq (τ := layout.tableLogHeights.getD opKeccak 0) (fun k hk ↦ T.hs1 k hk)
        (fun k hk ↦ T.hs0 k hk),
      cLow_kbExp, ← T.hlen j (by omega), T.hrc _ hpl (by omega), ← hp, hκ]
    ring
  -- the public input's claims
  have h3 : 164 ≤ j := by omega
  have hk : termKind j = 3 := by unfold termKind; split_ifs <;> omega
  have ht : termCol j = j - 164 := by unfold termCol; split_ifs <;> omega
  simp only [claimTerm, hk, ht]
  have hp := T.hpp j h3 hj
  rw [T.hmem0] at hp
  have hlen : (claims.getD j default).point.length =
      (Tables.committedKappas kappas).getD (j - 164) 0 := by
    rw [hp, T.hmem _ (by omega)]; simp; have := T.hlm; omega
  refine term_committed (cc := j - 164) (by omega) T.hkap T.hP ?_ T.hx (T.hK _ (by omega)) hlen ?_
    (T.hsel _ (by omega))
  · rw [hcolj, committedCols_getD (by omega)]
    simp [claimColOf, colOfCommitted, show ¬ j < 5 by omega, show ¬ j < 164 by omega,
      show j - 164 < 73 by omega]
  · rw [T.hpi, hlen, T.hmem _ (by omega), hp]

end
end LeanVM.Guest.B1.VerifySub
