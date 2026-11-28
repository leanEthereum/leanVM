/-
  LeanVM.Protocol.Keccak.Iface

  The Keccak reduction as the assembly takes it (`Relation.KeccakIface`): `keccakValidity` on the
  link's end, from the `KECCAK` output-lane claims failing or the defect surviving, to the
  reduction's claims on `q_keccak` failing, read on a committed stack.
-/

module

public import LeanVM.Protocol.Keccak.Gkr
public import LeanVM.Protocol.Relation.Iface
public import LeanVM.Protocol.Relation.Placement
public import LeanVM.Protocol.Relation.Frame

/-!
# The Keccak reduction's interface

`keccakValidity layout link` (`walk`, `crates/verifier/src/lib.rs`) reads the `KECCAK` table's row
point `inst` and its output lanes' values off the link's end (`lanesOf`, the first value per lane)
and runs `verifyKeccak` there (`keccakValidity_eq`). On a stack `q`, `q_keccak`'s rows are
`columnRow layout q qkeccak` (`colOf`), the column `gkrSpec` reads:

* the link's output-lane claims are the reduction's `outClaimsTrueMid` (`columnClaimHolds_out_iff`):
  under `LinkShape`, an output-lane claim is the `KECCAK` table's (`mem_keccakOutputClaims`), the
  one value `lanesOf` reads for its lane;
* the defect surviving at `inst` is the failure of the reduction's `midAgree`
  (`not_midAgree_of_defect`);
* the reduction's claims on `q_keccak` and its input slices are `colTrue` and `slicesTrue`
  (`colTrue_of_holds`, `slicesTrue_of_ringClaimHolds`), at the shapes its returns have
  (`returns_verifyKeccak`).

`keccakValiditySpec` is `gkrSpec` at one candidate (`L₀ = 1`): its lead `6/|E|`, each layer's
evaluation point `46/|E|` after its `3`-bit grind, every other round at most `3/|E|`, all within
`εmsg`. `keccakIface : KeccakIface`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Relation Finset
open scoped ENNReal

@[expose] public section

/-! ## Returns -/

theorem returns_readScalars : ∀ {n : ℕ} {xs : List E},
    VerifierProgram.Returns (VerifierProgram.readScalars n) xs → xs.length = n
  | 0, xs, h => by
    unfold VerifierProgram.readScalars at h
    rw [VerifierProgram.returns_ret h]
    rfl
  | n + 1, xs, h => by
    unfold VerifierProgram.readScalars at h
    obtain ⟨x, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨ys, hys, h⟩ := VerifierProgram.returns_bind h
    rw [VerifierProgram.returns_ret h, List.length_cons, returns_readScalars hys]

theorem returns_sampleChallenges : ∀ {n : ℕ} {xs : List E},
    VerifierProgram.Returns (VerifierProgram.sampleChallenges n) xs → xs.length = n
  | 0, xs, h => by
    unfold VerifierProgram.sampleChallenges at h
    rw [VerifierProgram.returns_ret h]
    rfl
  | n + 1, xs, h => by
    unfold VerifierProgram.sampleChallenges at h
    obtain ⟨x, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨ys, hys, h⟩ := VerifierProgram.returns_bind h
    rw [VerifierProgram.returns_ret h, List.length_cons, returns_sampleChallenges hys]

theorem returns_keccakOpen {logSteps : ℕ} {claim : KeccakClaim} {first count : ℕ} {value : E}
    {r : List E × List E × E}
    (h : VerifierProgram.Returns (keccakOpen logSteps claim first count value) r) :
    r.1.length = qkeccakSlotBits := by
  unfold keccakOpen at h
  obtain ⟨⟨slot, v⟩, hs, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  simpa using returns_sumcheck hs

theorem returns_verifyKeccakLayer {logSteps step : ℕ} {claim c : KeccakClaim}
    (h : VerifierProgram.Returns (verifyKeccakLayer logSteps step claim) c) :
    c.point.length = claim.point.length := by
  unfold verifyKeccakLayer at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨⟨pt, v⟩, hp, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨⟨lp, v'⟩, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  simpa using returns_sumcheck hp

theorem returns_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim)
    {c : KeccakClaim}, VerifierProgram.Returns (keccakLayers logSteps steps claim) c →
      c.point.length = claim.point.length
  | [], claim, c, h => by
    unfold keccakLayers at h
    rw [VerifierProgram.returns_ret h]
  | step :: steps, claim, c, h => by
    unfold keccakLayers at h
    obtain ⟨c', hc', h⟩ := VerifierProgram.returns_bind h
    rw [returns_keccakLayers logSteps steps c' h, returns_verifyKeccakLayer hc']

/-- **What `verifyKeccak` returns**: its shape held, its column claims are on `q_keccak` at
`h + 6` coordinates, its ring point has `h + 6`, and it leaves `64` slices. -/
theorem returns_verifyKeccak {h : ℕ} {inst output : List E}
    {r : List ColumnClaim × List E × List E}
    (hr : VerifierProgram.Returns (verifyKeccak h inst output) r) :
    KeccakGkr.KeccakShape h inst output ∧
      (∀ c ∈ r.1, c.column = qkeccak ∧ c.point.length = h + 6) ∧ r.2.1.length = h + 6 ∧
        r.2.2.length = 64 ∧ r.1.length ≤ 1 := by
  rw [verifyKeccak_eq] at hr
  obtain ⟨_, hs, hr⟩ := VerifierProgram.returns_bind hr
  have hs : KeccakGkr.KeccakShape h inst output := VerifierProgram.returns_require hs
  unfold gkrProg at hr
  obtain ⟨seg, hseg, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨lanesPt, -, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨committed, -, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨claim, hcl, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨x, hx, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨word, -, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
  unfold inputTail at hr
  obtain ⟨y, hy, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨x', hx', hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨sl, hsl, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
  have hret := VerifierProgram.returns_ret hr
  subst hret
  obtain ⟨hi, ho, h4⟩ := hs
  have hseg' := returns_sampleChallenges hseg
  have hcl' := returns_keccakLayers h _ _ hcl
  have hx1 := returns_keccakOpen hx
  have hx1' := returns_keccakOpen hx'
  have hy1 := returns_sumcheck hy
  have hsl' := returns_readScalars hsl
  rw [firstClaim_point] at hcl'
  have h6 : qkeccakSlotBits = 6 := by decide
  have h1 : keccakSegmentBits = 1 := by decide
  refine ⟨⟨hi, ho, h4⟩, ?_, ?_, hsl', by simp⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, List.length_take, List.length_drop, hx1, h6, hi]
    omega
  · simp only [List.length_append, List.length_take, hx1', hy1, List.length_replicate, hcl',
      List.length_drop, hseg', h6, h1, hi]
    omega

/-! ## Multilinear extensions -/

/-- The Keccak reduction's equality weight is `eq_eval` at the cube point. -/
theorem eqAt_eq_eqEval : ∀ (pt : List E) (x : ℕ),
    eqAt pt x = eqEval pt (Tables.boolPoint pt.length x)
  | [], x => by simp [eqEval, Tables.boolPoint]
  | r :: rs, x => by
    rw [eqAt_cons, eqAt_eq_eqEval rs (x / 2), List.length_cons, Tables.boolPoint_succ,
      Tables.eqEval_cons, Nat.testBit_zero]
    congr 1
    by_cases hx : x % 2 = 1
    · simp only [hx, ↓reduceIte, decide_true]
      rw [add_comm 1 r, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp [hx]

/-- **`rowMle` is the sum with the Keccak reduction's equality weights.** -/
theorem rowMle_eq_sum (pt : List E) (f : ℕ → E) :
    rowMle pt f = ∑ x ∈ range (2 ^ pt.length), eqAt pt x * f x := by
  unfold rowMle
  rw [Tables.multilinearEval_eq_sum pt.length _ pt (by simp) rfl]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [eqAt_eq_eqEval, Tables.eqEval_comm, mul_comm]
  congr 1
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hx)]

/-! ## `q_keccak` on a stack -/

/-- `q_keccak`'s rows on a stack. -/
def colOf (layout : Layout) {μ : ℕ} (q : Column μ) : ℕ → K := columnRow layout q qkeccak

theorem colOf_eq {layout : Layout} {qkp : Placement}
    (hqk : layout.placements.getD qkeccak none = some qkp) {μ : ℕ} (q : Column μ) (n : ℕ) :
    colOf layout q n = cell q (qkp.index + n) := by
  unfold colOf columnRow
  rw [hqk]

theorem qkeccakLane_eq (layout : Layout) {μ : ℕ} (q : Column μ) (slot row : ℕ) :
    qkeccakLane layout q slot row =
      K.lane (colOf layout q (row + 2 ^ keccakHeight layout * slot)) := by
  unfold qkeccakLane colOf
  rw [show slot * 2 ^ keccakHeight layout + row = row + 2 ^ keccakHeight layout * slot by ring]

theorem keccakInput_eq (layout : Layout) {μ : ℕ} (q : Column μ) (row : ℕ) :
    keccakInput layout q row = inState (keccakHeight layout) (colOf layout q) 0 row := by
  unfold keccakInput inState
  congr 1
  funext l
  rw [qkeccakLane_eq]
  simp

theorem keccakMid_eq (layout : Layout) {μ : ℕ} (q : Column μ) (row : ℕ) :
    keccakMid layout q row = inState (keccakHeight layout) (colOf layout q) 1 row := by
  unfold keccakMid inState
  congr 1
  funext l
  rw [qkeccakLane_eq]
  simp [keccakStateLanes]

theorem keccakRounds_eq (a : KeccakState) (start count : ℕ) :
    keccakRounds a start count = roundsFrom start count a := rfl

theorem lane_ofFn (f : Fin 25 → UInt64) {l : ℕ} (hl : l < 25) :
    Keccak.lane (Vector.ofFn f) l = f ⟨l, hl⟩ := by
  rw [lane_eq _ hl, Vector.getElem_ofFn]

/-! ## The defect -/

/-- A row of the defect, on `q_keccak`'s rows. -/
theorem keccakDefect_eq (layout : Layout) {μ : ℕ} (q : Column μ) {l : ℕ} (hl : l < 25) (x : ℕ) :
    keccakDefect layout q l x =
      ofK (colOf layout q (x + 2 ^ keccakHeight layout * (25 + l))) -
        ofK (laneWord (roundsFrom 0 12 (inState (keccakHeight layout) (colOf layout q) 0 x)) l) := by
  have e1 : ofK (K.ofLane (Keccak.lane (keccakMid layout q x) l)) =
      ofK (colOf layout q (x + 2 ^ keccakHeight layout * (25 + l))) := by
    rw [keccakMid_eq, lane_inState _ _ _ _ hl]; rfl
  have e2 : ofK (K.ofLane (Keccak.lane (keccakRounds (keccakInput layout q x) 0 keccakDepth) l)) =
      ofK (laneWord (roundsFrom 0 12 (inState (keccakHeight layout) (colOf layout q) 0 x)) l) := by
    rw [keccakInput_eq, keccakRounds_eq, show keccakDepth = 12 from rfl, laneWord]
  unfold keccakDefect
  rw [e1, e2]

/-- **The defect surviving at `inst` breaks the reduction's `midAgree`.** -/
theorem not_midAgree_of_defect {layout : Layout} {μ : ℕ} {q : Column μ} {link : LinkEnd}
    (hi : (link.columns.getD opKeccak ([], [])).1.length = keccakHeight layout)
    (hd : KeccakDefectAt layout q link) :
    ¬ midAgree (keccakHeight layout) (colOf layout q) (link.columns.getD opKeccak ([], [])).1 := by
  intro hmid
  obtain ⟨l, hl, hne⟩ := hd
  apply hne
  rw [rowMle_eq_sum, hi]
  have hm := hmid l hl
  unfold stepMle at hm
  simp only [keccakDefect_eq layout q hl, mul_sub]
  rw [sum_sub_distrib, hm, sub_self]

/-! ## The output lanes -/

/-- The lanes `keccakValidity` reads: per lane, the first value the `KECCAK` table sent for its
output column. -/
def lanesOf (values : List (ℕ × E)) : Option (List E) :=
  (List.range keccakStateLanes).mapM fun lane ↦
    (values.find? fun value ↦ value.1 = keccakOut + lane).map (·.2)

/-- **`keccakValidity` is the lanes' lookup, then the reduction.** -/
theorem keccakValidity_eq (layout : Layout) (link : LinkEnd) :
    keccakValidity layout link =
      liftOption (lanesOf (link.columns.getD opKeccak ([], [])).2) >>= fun lanes ↦
        verifyKeccak (keccakHeight layout) (link.columns.getD opKeccak ([], [])).1 lanes := by
  unfold keccakValidity
  rfl

theorem mapM_getD {f : ℕ → Option E} : ∀ (L : List ℕ) (ys : List E), L.mapM f = some ys →
    ys.length = L.length ∧ ∀ i (hi : i < L.length), f L[i] = some (ys.getD i 0)
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | a :: L, ys, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    obtain ⟨hl, hg⟩ := mapM_getD L ys' hys'
    refine ⟨by simp [hl], fun i hi ↦ ?_⟩
    rcases i with _ | i
    · simpa using hy
    · simpa using hg i (by simpa using hi)

theorem find_eq_of_nodup {values : List (ℕ × E)} (hnd : (values.map Prod.fst).Nodup) {k : ℕ}
    {v : E} (hm : (k, v) ∈ values) :
    (values.find? fun value ↦ value.1 = k) = some (k, v) := by
  have hsome : (values.find? fun value ↦ decide (value.1 = k)).isSome :=
    List.find?_isSome.mpr ⟨(k, v), hm, decide_eq_true rfl⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
  have hwm := List.mem_of_find?_eq_some hw
  have h1 := List.find?_some hw
  have hwk : w.1 = k := by simpa using h1
  rw [hw, List.inj_on_of_nodup_map hnd hwm hm (by simpa using hwk)]

theorem lt_of_mem_zip_globalColumnBases {link : LinkEnd} {x : ℕ × List E × List (ℕ × E)}
    (hx : x ∈ globalColumnBases.zip link.columns) :
    ∃ t < nTables, x = (globalColumnBases.getD t 0, link.columns.getD t ([], [])) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi1 : i < globalColumnBases.length := by simp at hi; omega
  have hi2 : i < link.columns.length := by simp at hi; omega
  have hlen : globalColumnBases.length = nTables := by simp [globalColumnBases]
  refine ⟨i, hlen ▸ hi1, ?_⟩
  rw [List.getElem_zip, List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2]

/-- Every table but `KECCAK` ends below the `KECCAK` table's first column. -/
theorem bases_below : ∀ t < opKeccak,
    globalColumnBases.getD t 0 + tableWidths.getD t 0 ≤ globalColumnBases.getD opKeccak 0 := by
  decide +kernel

/-- **An output-lane claim of the link's end is the `KECCAK` table's**, under `LinkShape`: at its
row point, on the output column of a lane, with the value the table sent there. -/
theorem mem_keccakOutputClaims {layout : Layout} {link : LinkEnd} (hs : LinkShape layout link)
    {c : ColumnClaim} (hc : c ∈ keccakOutputClaims link) :
    ∃ l < keccakStateLanes, c.column = globalColumnBases.getD opKeccak 0 + keccakOut + l ∧
      keccakOutputLane c.column = some l ∧ c.point = (link.columns.getD opKeccak ([], [])).1 ∧
        (keccakOut + l, c.value) ∈ (link.columns.getD opKeccak ([], [])).2 := by
  obtain ⟨-, -, -, hcols, -⟩ := hs
  simp only [keccakOutputClaims, List.mem_filter] at hc
  obtain ⟨hc, hlane⟩ := hc
  simp only [linkColumnClaims, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨x, hx, ⟨col, v⟩, hcv, rfl⟩ := hc
  obtain ⟨t, ht, rfl⟩ := lt_of_mem_zip_globalColumnBases hx
  obtain ⟨-, hw⟩ := hcols t ht
  have hcw := hw _ hcv
  simp only at hcw hlane ⊢
  rcases Option.isSome_iff_exists.mp hlane with ⟨l, hl⟩
  have hl' := hl
  dsimp only [keccakOutputLane] at hl'
  split at hl'
  · next hin =>
    simp only [Option.some.injEq] at hl'
    by_cases htk : t = opKeccak
    · subst htk
      refine ⟨l, by omega, by omega, hl, rfl, ?_⟩
      rwa [show keccakOut + l = col by omega]
    · have hlt : t < opKeccak := by
        have : nTables = opKeccak + 1 := rfl
        omega
      have := bases_below t hlt
      omega
  · cases hl'

/-- **An output-lane claim holds exactly when the reduction's output claim on its lane does.** -/
theorem columnClaimHolds_out_iff {layout : Layout} {μ : ℕ} (q : Column μ) {c : ColumnClaim}
    {l : ℕ} (hk : keccakOutputLane c.column = some l)
    (hi : c.point.length = keccakHeight layout) :
    ColumnClaimHolds layout q c ↔
      stepMle (keccakHeight layout) c.point
        (fun x ↦ laneWord (roundsFrom 12 12 (inState (keccakHeight layout) (colOf layout q) 1 x)) l) =
        c.value := by
  unfold ColumnClaimHolds
  rw [rowMle_eq_sum, hi, eq_comm]
  unfold stepMle
  refine iff_of_eq (congrArg (· = c.value) (sum_congr rfl fun x _ ↦ ?_))
  simp only [columnValue, hk, keccakOutput, keccakMid_eq, keccakRounds_eq, laneWord]
  rfl

/-- **An output-lane claim failing breaks the reduction's `outClaimsTrueMid`** at the lanes
`keccakValidity` reads. -/
theorem not_outClaims_of_fail {layout : Layout} {μ : ℕ} {q : Column μ} {link : LinkEnd}
    (hs : LinkShape layout link) {lanes : List E}
    (hlanes : lanesOf (link.columns.getD opKeccak ([], [])).2 = some lanes)
    (hi : (link.columns.getD opKeccak ([], [])).1.length = keccakHeight layout)
    (hf : ¬ ∀ c ∈ keccakOutputClaims link, ColumnClaimHolds layout q c) :
    ¬ outClaimsTrueMid (keccakHeight layout) (colOf layout q)
      (link.columns.getD opKeccak ([], [])).1 lanes := by
  intro hout
  apply hf
  intro c hc
  obtain ⟨l, hl, -, hk, hpt, hmem⟩ := mem_keccakOutputClaims hs hc
  obtain ⟨-, -, -, hcols, -⟩ := hs
  have hnd := (hcols opKeccak (by decide)).1
  obtain ⟨-, hg⟩ := mapM_getD _ lanes hlanes
  have hget := hg l (by simpa using hl)
  simp only [List.getElem_range, find_eq_of_nodup hnd hmem, Option.map_some,
    Option.some.injEq] at hget
  rw [columnClaimHolds_out_iff q hk (by rw [hpt, hi]), hpt, hget]
  exact hout l hl

/-! ## The reduction's claims -/

theorem keccakOutputLane_qkeccak : keccakOutputLane qkeccak = none := by
  dsimp only [keccakOutputLane]
  rw [keccakBase_eq]
  split
  · exact absurd ‹_ ∧ _›.1 (by simp only [qkeccak]; omega)
  · rfl

theorem colTrue_of_holds {layout : Layout} {μ : ℕ} (q : Column μ) {h : ℕ} {c : ColumnClaim}
    (hc : c.column = qkeccak) (hl : c.point.length = h + 6) (hh : ColumnClaimHolds layout q c) :
    colTrue h (colOf layout q) c := by
  refine ⟨hc, hl, ?_⟩
  rw [hh, rowMle_eq_sum, hl]
  refine sum_congr rfl fun n _ ↦ ?_
  simp [columnValue, hc, keccakOutputLane_qkeccak, colOf]

theorem slicesTrue_of_ringClaimHolds {layout : Layout} {qkp : Placement}
    (hqk : layout.placements.getD qkeccak none = some qkp) {μ : ℕ} (q : Column μ) {h : ℕ}
    {point slices : List E} (hp : point.length = h + 6)
    (hr : RingClaimHolds q (keccakRingClaim qkp point slices)) :
    slicesTrue h (colOf layout q) point slices := by
  simp only [keccakRingClaim] at hr
  obtain ⟨hlen, hb⟩ := hr
  refine ⟨hp, hlen, fun i hi ↦ ?_⟩
  rw [hb i hi]
  simp only [List.map_cons, List.map_nil, sumE, List.foldl_cons, List.foldl_nil,
    zero_add, one_mul, rowMle_eq_sum, hp]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [colOf_eq hqk]
  rfl

/-! ## The specification -/

/-- The precondition the assembly gives the reduction. -/
def KPre (layout : Layout) (link : LinkEnd) (S : Set (Column layout.stackLog)) : Prop :=
  ∀ q ∈ S, ¬ (∀ c ∈ keccakOutputClaims link, ColumnClaimHolds layout q c) ∨
    KeccakDefectAt layout q link

/-- The postcondition the assembly takes of the reduction. -/
def KPost (layout : Layout) (qkp : Placement) (S : Set (Column layout.stackLog))
    (r : List ColumnClaim × List E × List E) : Prop :=
  ∀ q ∈ S, ¬ (∀ c ∈ r.1, ColumnClaimHolds layout q c) ∨
    ¬ RingClaimHolds q (keccakRingClaim qkp r.2.1 r.2.2)

theorem errE_eq (d : ℕ) : errE d = (d : ℝ≥0∞) / Fintype.card E := by
  rw [errE, div_eq_mul_inv]

theorem h46_le : (2 : ℝ≥0∞)⁻¹ ^ grindingBits (productBits - 1) * (((1 : ℕ) : ℝ≥0∞) * errE 46) ≤
    εmsg := by
  rw [Nat.cast_one, one_mul, errE_eq, show productBits - 1 = 46 from rfl]
  exact grindingBits_discount 46

theorem small_le {d : ℕ} (hd : d ≤ 8) : ((1 : ℕ) : ℝ≥0∞) * errE d ≤ εmsg := by
  have := grindingBits_discount d
  rw [grindingBits_eq_zero_of_le hd, pow_zero, one_mul] at this
  rwa [Nat.cast_one, one_mul, errE_eq]

open Classical in
/-- **The Keccak reduction on the link's end**, at the candidates `S` (at most one). -/
noncomputable def keccakValiditySpec (layout : Layout) (link : LinkEnd)
    (hs : LinkShape layout link) (qkp : Placement)
    (hqk : layout.placements.getD qkeccak none = some qkp) (S : Set (Column layout.stackLog))
    (hS : S.Subsingleton) (T : ENNReal) (hT : T ≤ εmsg) :
    Spec (keccakValidity layout link) (fun _ ↦ KPre layout link S) (fun r _ ↦ KPost layout qkp S r)
      εmsg (((keccakSegmentBits + keccakLaneBits : ℕ) : ENNReal) / Fintype.card E + T) T := by
  refine Spec.congr (keccakValidity_eq layout link).symm ?_
  rcases ho : lanesOf (link.columns.getD opKeccak ([], [])).2 with _ | lanes
  · exact Spec.congr rfl ((Spec.fail).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl)
  · refine Spec.congr (show verifyKeccak (keccakHeight layout)
      (link.columns.getD opKeccak ([], [])).1 lanes = _ from rfl) ?_
    by_cases hsh : KeccakGkr.KeccakShape (keccakHeight layout)
        (link.columns.getD opKeccak ([], [])).1 lanes
    · obtain ⟨hi, ho25, h4⟩ := hsh
      let P := keccakHeight layout - 4
      have hP : keccakHeight layout = P + 4 := (Nat.sub_add_cancel h4).symm
      have hi' : (link.columns.getD opKeccak ([], [])).1.length = P + 4 := hi.trans hP
      have hcard : ∀ _ : List Ev, (S).ncard ≤ 1 := fun _ ↦ (Set.ncard_le_one hS.finite).2 hS
      have S0 := Spec.retInv (gkrSpec (C := fun _ ↦ S) (L₀ := 1) (εmax := εmsg) (T := T)
        (fun _ _ _ ↦ rfl) hcard (fun _ ↦ True) (fun q ↦ colOf layout q) P hi' ho25 hT h46_le
        (small_le (by norm_num)))
        (fun r ↦ (∀ c ∈ r.1, c.column = qkeccak ∧ c.point.length = P + 4 + 6) ∧
          r.2.1.length = P + 4 + 6) fun r hr ↦ by
          obtain ⟨-, h1, h2, -, -⟩ := returns_verifyKeccak hr
          exact ⟨h1, h2⟩
      rw [hP]
      refine S0.mono (fun _ hpre q hq ⟨hout, hmid, _⟩ ↦ ?_) (fun r _ ⟨hpost, hcl, hpt⟩ q hq ↦ ?_)
        le_rfl ?_ le_rfl
      · rcases hpre q hq with hf | hd
        · exact not_outClaims_of_fail hs ho hi hf (hP ▸ hout)
        · exact not_midAgree_of_defect hi hd (hP ▸ hmid)
      · by_contra hboth
        simp only [not_or, not_not] at hboth
        exact hpost q hq ⟨fun c hc ↦ colTrue_of_holds q (hcl c hc).1 (hcl c hc).2
          (hboth.1 c hc), slicesTrue_of_ringClaimHolds hqk q hpt hboth.2, trivial⟩
      · rw [show keccakSegmentBits + keccakLaneBits = 6 from rfl, Nat.cast_one, one_mul, errE_eq]
        exact le_self_add
    · exact Spec.congr (verifyKeccak_eq _ _ _).symm
        ((Spec.require (Post := fun _ _ ↦ False) fun _ _ hc ↦ absurd hc hsh).bind'
          fun _ ↦ Spec.dead)

/-- **The Keccak reduction's interface.** -/
noncomputable def keccakIface : KeccakIface where
  keccakSpec _ layout _ _ link hs qk hqk S hS T hT := keccakValiditySpec layout link hs qk hqk S hS T hT
  keccakShape _ layout _ _ link _ r hr := by
    rw [keccakValidity_eq] at hr
    obtain ⟨lanes, -, hr⟩ := VerifierProgram.returns_bind hr
    obtain ⟨-, h1, h2, h3, h4⟩ := returns_verifyKeccak hr
    have h6 : qkeccakSlotBits = 6 := by decide
    exact ⟨fun c hc ↦ ⟨(h1 c hc).1, by rw [(h1 c hc).2, h6]⟩, by rw [h2, h6], h3, h4⟩

end
end LeanVM.Protocol.KeccakGkr
