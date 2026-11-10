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

`claimFact_all` checks, entry by entry, what the source's arrays say of each claim against the
specification's claims (`ClaimFact`). `ClaimsCtx` collects what the head of `check_opening_terminal` and its precondition establish
about the words the claims' blocks read: the selectors (`selProd` of each committed column's offset
bits), the chains at `zeta` and `chi` (the points' weights), the slot points, the public input's
chain, the columns' sizes (over the base `[0, log_mem, τ_0, …, τ_5]`, `kbExp`) and placements and
the claims' points and their low lengths (`claimLow`). A claim's source and adjustment are its
column's (`ChainFact`; a lane's are `KECCAK`'s height), so its low length is its column's size.
`claimTerm_eq`: claim `j`'s term at `λ^(1 + poolRank j)` is that power times its weight on the
stack, `0` for an output lane.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

/-- The claims' global columns: the bus's `0 .. 3`, the tables' `5 .. 157`, the public input's
`0, 1`. -/
def claimColOf (j : ℕ) : ℕ := if j < 4 then j else if j < 157 then j + 1 else j - 157

theorem claimColumns_eq : Tables.claimColumns = (List.range 159).map claimColOf := by
  decide +kernel

theorem claimColumns_getD {j : ℕ} (hj : j < 159) : Tables.claimColumns.getD j 0 = claimColOf j := by
  rw [claimColumns_eq, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getElem_range]

theorem gen_pow_inj_le {a b : ℕ} (ha : a ≤ 64) (hb : b ≤ 64) (h : gen ^ a = gen ^ b) : a = b :=
  gen_pow_inj (lt_of_le_of_lt ha (by norm_num)) (lt_of_le_of_lt hb (by norm_num)) h

/-- The exponents of `kappa_base`: `[0, log_mem, τ_0, …, τ_5]`. -/
def kbExp (layout : Layout) (i : ℕ) : ℕ :=
  ([0, layout.logMemory] ++ layout.tableLogHeights).getD i 0

/-- A claim on a committed column `termCol j`: that column is claim `j`'s, and its source and
adjustment are the claim's. -/
abbrev ChainFact (j : ℕ) : Prop :=
  termCol j < Tables.nCommittedCols ∧ colOfCommitted (termCol j) = claimColOf j ∧
    Tables.colKappaSrc (termCol j) = claimKappaSrc j ∧ Tables.colKappaAdj (termCol j) = claimKappaAdj j

/-- **What claim `j`'s kind says of it**, the source's arrays against the specification's claims:
its sources are `Tables`', an output lane's kind is `4`, the bus's claims are `0 .. 3`, the
tables' `4 .. 156`, the public input's `157, 158` on the memory's columns, and a lane's slot is its
column's. -/
abbrev ClaimFact (j : ℕ) : Prop :=
  termKind j < 5 ∧ (claimColOf j ∈ (List.range 25).map (106 + ·) ↔ termKind j = 4) ∧
    Tables.claimKappaSrc.getD j 0 = claimKappaSrc j ∧ Tables.claimKappaAdj j = claimKappaAdj j ∧
    (termKind j = 0 → j < 4 ∧ ChainFact j) ∧
    (termKind j = 1 → 4 ≤ j ∧ j < 157 ∧ ChainFact j) ∧
    (termKind j = 2 → 157 ≤ j ∧ termCol j < 3 ∧ ChainFact j) ∧
    (termKind j = 3 → 4 ≤ j ∧ j < 157 ∧ 66 ≤ claimColOf j ∧ claimColOf j < 158 ∧
      slotOfCol (claimColOf j) = some (termSlot j) ∧ termSlot j < 64 ∧ claimKappaSrc j = 7 ∧
      claimKappaAdj j = 0)

instance (j : ℕ) : Decidable (ClaimFact j) := by unfold ClaimFact ChainFact; infer_instance

theorem claimFact_all : ∀ j < 159, ClaimFact j := by decide +kernel

theorem claimCol_out {j : ℕ} (hj : j < 159) :
    Tables.claimColumns.getD j 0 ∈ keccakOutputColumns ↔ termKind j = 4 := by
  rw [claimColumns_getD hj, keccakOutputColumns_eq]
  exact (claimFact_all j hj).2.1

theorem termKind_lt {j : ℕ} (hj : j < 159) : termKind j < 5 := (claimFact_all j hj).1

theorem cLow_kbExp (layout : Layout) {j : ℕ} (hj : j < 159) :
    cLow (kbExp layout) j = claimLow layout j := by
  obtain ⟨-, -, hs, ha, -⟩ := claimFact_all j hj
  rw [cLow, claimLow, Tables.claimLowDim, hs, ha]
  rfl

/-- What the head and the precondition give the claims' blocks. -/
structure ClaimsCtx (rd : Reader) (σ : Val) (layout : Layout) (kappas : List ℕ)
    (claims : List ColumnClaim) (zs chis x : List E) (rm : E) : Prop where
  hkap : kappas.length = 158
  hKC : Tables.committedKappas kappas = (List.range Tables.nCommittedCols).map fun c ↦
    (0 :: layout.logMemory :: layout.tableLogHeights).getD (Tables.colKappaSrc c) 0 +
      Tables.colKappaAdj c
  hP : layout.placements = (placementsOf kappas).1
  hx : x.length = layout.stackLog
  hL : layout.stackLog ≤ 28
  hK : ∀ c < Tables.nCommittedCols, (Tables.committedKappas kappas).getD c 0 ≤ layout.stackLog
  hq : 2 ^ (Tables.committedKappas kappas).getD 4 0 ∣
    (stackOffsets (Tables.committedKappas kappas)).1.getD 4 0
  hK4 : (Tables.committedKappas kappas).getD 4 0 = layout.tableLogHeights.getD opKeccak 0 + 6
  hlane : ∀ g, 66 ≤ g → g < 158 → kappas.getD g 0 = layout.tableLogHeights.getD opKeccak 0
  hmem : ∀ c < 3, (Tables.committedKappas kappas).getD c 0 = layout.logMemory
  hlm : 1 ≤ layout.logMemory
  hmem0 : (layout.placement memory0).variableCount = layout.logMemory
  hcols : claims.map (·.column) = Tables.claimColumns
  hzs : zs.length ≤ 40
  hchis : chis.length ≤ zs.length
  hpz : ∀ j < 4, (claims.getD j default).point = zs.take (claims.getD j default).point.length
  hpc : ∀ j, 4 ≤ j → j < 157 →
    (claims.getD j default).point = chis.take (claims.getD j default).point.length
  hpp : ∀ j, 157 ≤ j → j < 159 → (claims.getD j default).point =
    rm :: List.replicate ((layout.placement memory0).variableCount - 1) 0
  hlen : ∀ j < 157, (claims.getD j default).point.length = claimLow layout j
  hsel : ∀ c < Tables.nCommittedCols, σ (.n (selV c)) =
    selProd ((stackOffsets (Tables.committedKappas kappas)).1.getD c 0)
      ((Tables.committedKappas kappas).getD c 0)
      (layout.stackLog - (Tables.committedKappas kappas).getD c 0) x
  hzc : ∀ n ≤ zs.length, n ≤ layout.stackLog →
    valOf rd (σ (.n 20)) n = eqEval (zs.take n) (x.take n)
  hrc : ∀ n ≤ chis.length, n ≤ layout.stackLog →
    valOf rd (σ (.n 22)) n = eqEval (chis.take n) (x.take n)
  hs1 : ∀ k < 6, valOf rd (σ (.n 24)) k = x.getD (layout.tableLogHeights.getD opKeccak 0 + k) 0
  hs0 : ∀ k < 6, valOf rd (σ (.n 25)) k = 1 + x.getD (layout.tableLogHeights.getD opKeccak 0 + k) 0
  hpi : σ (.n 34) = eqEval (rm :: List.replicate (layout.logMemory - 1) 0) (x.take layout.logMemory)

theorem ClaimsCtx.kappa_eq {rd : Reader} {σ : Val} {layout : Layout} {kappas : List ℕ}
    {claims : List ColumnClaim} {zs chis x : List E} {rm : E}
    (T : ClaimsCtx rd σ layout kappas claims zs chis x rm) {c : ℕ}
    (hc : c < Tables.nCommittedCols) :
    (Tables.committedKappas kappas).getD c 0 =
      (0 :: layout.logMemory :: layout.tableLogHeights).getD (Tables.colKappaSrc c) 0 +
        Tables.colKappaAdj c := by
  rw [T.hKC, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

theorem claim_column {claims : List ColumnClaim} (hcols : claims.map (·.column) = Tables.claimColumns)
    {j : ℕ} (hj : j < 159) : (claims.getD j default).column = claimColOf j := by
  have hl : claims.length = 159 := by
    rw [← List.length_map (f := (·.column)), hcols, claimColumns_eq]; simp
  rw [← claimColumns_getD hj, ← hcols, List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]

/-- A pooled claim on a committed column, its point a prefix of `A` read by the chain `ch`. -/
theorem term_committed {layout : Layout} {kappas : List ℕ} {x : List E} {c : ColumnClaim}
    {cc : ℕ} (hcc : cc < Tables.nCommittedCols) (hkap : kappas.length = 158)
    (hP : layout.placements = (placementsOf kappas).1)
    (hcol : c.column = (Tables.committedCols 158).getD cc 0)
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

/-- A claim on a committed column, its point a prefix of `A`, read by a chain whose values at
every `n` are `A`'s weight. -/
theorem term_chain {rd : Reader} {σ : Val} {layout : Layout} {kappas : List ℕ}
    {claims : List ColumnClaim} {zs chis x : List E} {rm : E}
    (T : ClaimsCtx rd σ layout kappas claims zs chis x rm) {j : ℕ} (hj : j < 157)
    (hf : ChainFact j) {A : List E} {ch : ℕ}
    (hpA : (claims.getD j default).point = A.take (claims.getD j default).point.length)
    (hch : ∀ n ≤ A.length, n ≤ layout.stackLog → valOf rd (σ (.n ch)) n = eqEval (A.take n) (x.take n))
    (L : E) :
    L * valOf rd (σ (.n ch)) (cLow (kbExp layout) j) * σ (.n (selV (termCol j))) =
      L * wOf layout x (claims.getD j default) := by
  obtain ⟨hcc, hcolc, hsrc, hadj⟩ := hf
  have hκ : (claims.getD j default).point.length =
      (Tables.committedKappas kappas).getD (termCol j) 0 := by
    rw [T.hlen j hj, ← cLow_kbExp layout (by omega), T.kappa_eq hcc, cLow, hsrc, hadj]
    rfl
  have hpl : (claims.getD j default).point.length ≤ A.length := by
    have := congrArg List.length hpA; rw [List.length_take] at this; omega
  have hKj := T.hK _ hcc
  refine term_committed hcc T.hkap T.hP ?_ T.hx hKj hκ ?_ (T.hsel _ hcc)
  · rw [claim_column T.hcols (by omega), committedCols_getD hcc, hcolc]
  · rw [cLow_kbExp layout (by omega), ← T.hlen j hj, hch _ hpl (by rw [hκ]; exact hKj), ← hpA]

/-- **Claim `j`'s term** is its batched weight on the stack, `0` on an output lane. -/
theorem claimTerm_eq {rd : Reader} {σ : Val} {layout : Layout} {kappas : List ℕ}
    {claims : List ColumnClaim} {zs chis x : List E} {lam rm : E}
    (T : ClaimsCtx rd σ layout kappas claims zs chis x rm) {j : ℕ} (hj : j < 159) :
    claimTerm rd σ (kbExp layout) (lam ^ (1 + poolRank j)) j =
      if Tables.claimColumns.getD j 0 ∉ keccakOutputColumns then
        lam ^ (1 + poolRank j) * wOf layout x (claims.getD j default) else 0 := by
  have hcolj := claim_column T.hcols hj
  have hout := claimCol_out hj
  obtain ⟨-, -, -, -, f0, f1, f2, f3⟩ := claimFact_all j hj
  have hL := T.hL
  have hzs := T.hzs
  have hchis := T.hchis
  rcases hk : termKind j with _ | _ | _ | _ | k
  · -- the bus's claims
    obtain ⟨hj4, hf⟩ := f0 hk
    have hno : Tables.claimColumns.getD j 0 ∉ keccakOutputColumns := fun h ↦ by
      have := hout.mp h; omega
    simp only [claimTerm, hk, hno, not_false_eq_true, ↓reduceIte]
    exact term_chain T (by omega) hf (T.hpz j hj4) T.hzc _
  · -- the tables' claims
    obtain ⟨hj4, hj157, hf⟩ := f1 hk
    have hno : Tables.claimColumns.getD j 0 ∉ keccakOutputColumns := fun h ↦ by
      have := hout.mp h; omega
    simp only [claimTerm, hk, hno, not_false_eq_true, ↓reduceIte]
    exact term_chain T hj157 hf (T.hpc j hj4 hj157) T.hrc _
  · -- the public input's claims
    obtain ⟨hj157, hc3, hcc, hcolc, -, -⟩ := f2 hk
    have hno : Tables.claimColumns.getD j 0 ∉ keccakOutputColumns := fun h ↦ by
      have := hout.mp h; omega
    simp only [claimTerm, hk, hno, not_false_eq_true, ↓reduceIte]
    have hp := T.hpp j hj157 hj
    rw [T.hmem0] at hp
    have hlen : (claims.getD j default).point.length =
        (Tables.committedKappas kappas).getD (termCol j) 0 := by
      rw [hp, T.hmem _ hc3]; simp; have := T.hlm; omega
    refine term_committed hcc T.hkap T.hP ?_ T.hx (T.hK _ hcc) hlen ?_ (T.hsel _ hcc)
    · rw [hcolj, committedCols_getD hcc, hcolc]
    · rw [T.hpi, hlen, T.hmem _ hc3, hp]
  · -- a `q_keccak` lane's claim
    obtain ⟨hj4, hj157, hg66, hg158, es, hslot, hsrc, hadj⟩ := f3 hk
    have hno : Tables.claimColumns.getD j 0 ∉ keccakOutputColumns := fun h ↦ by
      have := hout.mp h; omega
    simp only [claimTerm, hk, hno, not_false_eq_true, ↓reduceIte]
    have hp := T.hpc j hj4 hj157
    have hpl : (claims.getD j default).point.length ≤ chis.length := by
      have := congrArg List.length hp; rw [List.length_take] at this; omega
    have hK4 := T.hK 4 (by decide)
    rw [T.hK4] at hK4
    have hκ : (claims.getD j default).point.length = layout.tableLogHeights.getD opKeccak 0 := by
      rw [T.hlen j hj157, ← cLow_kbExp layout hj, cLow, hsrc, hadj]
      rfl
    have hpl' : layout.placement (claims.getD j default).column =
        Placement.mk (layout.tableLogHeights.getD opKeccak 0)
          ((stackOffsets (Tables.committedKappas kappas)).1.getD 4 0 +
            termSlot j * 2 ^ layout.tableLogHeights.getD opKeccak 0) := by
      rw [hcolj, placement_slot T.hkap T.hP hg158 es, T.hlane _ hg66 hg158]
    have hq := T.hq
    rw [T.hK4] at hq
    rw [wOf_lane hpl' hκ T.hx hK4 hq hslot, T.hsel 4 (by decide), T.hK4,
      slotProd_eq (τ := layout.tableLogHeights.getD opKeccak 0) (fun k hk ↦ T.hs1 k hk)
        (fun k hk ↦ T.hs0 k hk),
      cLow_kbExp layout hj, ← T.hlen j hj157, T.hrc _ hpl (by omega), ← hp, hκ]
    ring
  · -- an output lane's claim
    have h4 : termKind j = 4 := by have := termKind_lt hj; omega
    simp only [claimTerm, hk, hout.mpr h4, not_true_eq_false, ↓reduceIte]

end
end LeanVM.Guest.B1.VerifySub
