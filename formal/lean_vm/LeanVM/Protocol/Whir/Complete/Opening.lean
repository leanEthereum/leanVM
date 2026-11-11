/-
  LeanVM.Protocol.Whir.Complete.Opening

  The honest prover of leanVM's WHIR opening, the statement's own (`openingFast`'s levels on the
  stack's and the claims' tables), the commitment it opens, and the completeness of the stacked
  opening as the simulation `OpeningComplete`.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Whir.Complete.Script
public import LeanVM.Protocol.Whir.Complete.Encoding
public import Statement.Prover.Whir

/-!
# Completeness of the WHIR opening

The verifier is `LeanVM.Protocol.Verifier.verifyStackedOpening` / `verifyWhir`
(`crates/verifier/src/lib.rs:136-157`, `whir.rs:223-343`), with the commitment `commitStack`.
The honest prover is the statement's (`LeanVM.Prover.levelsA`, `Statement/Prover/Whir.lean`) run
on the stack's table and the batched claims' weight table in the WHIR variable order
(`stackTable`, `basisTable`): the affine fold rounds on novel-basis coefficient tables, the next
level's word, the out-of-domain values, the final level's folded lane and the tail sumcheck.

* `honestOpening μ R q claims`: the batching challenge, then those levels.
* `stackCommit μ R q`, `follows_commitStack`: the stack's word, which `commitStack` reads.
* `OpeningComplete`: **perfect completeness of the stacked opening as a simulation**: for an
  admissible `(μ, R)` and at most `maxStackedClaims` stack claims that hold of `q` with
  multilinear weights, `honestOpening` follows `verifyStackedOpening` from the commitments
  `[stackCommit μ R q]`. Every `require` holds: the claim count, each level's query check of the
  final level, and the terminal check. Its proof is the affine fold's honest identities (the
  table's `u₁ = ⟨W₁, G⟩` in characteristic two, the folded claim by linearity, the fold of an
  opened row being the folded lane at its point by Annex D's `lem:mulx`) and the tail sumcheck's.
  The consequences below take it as a hypothesis.
* `follows_verifyStackedOpening`, `runFrom_verifyStackedOpening`: the simulation, and the
  interactive run it gives against every challenge function.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Prover (Script levelsA)

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  LeanVM.Protocol.Compile LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## The ladder -/

private theorem admissible_bounded {μ R : ℕ} (h : Whir.Admissible μ R) :
    μ < Whir.maxLogStack + 1 ∧ R < 5 := by
  obtain ⟨_, h2, _, h4⟩ := h
  exact ⟨Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h4⟩

/-- Every admissible ladder starts with the lane fold at the announced rate, and its folds fit
in the stack. -/
theorem ladder_head_sum {μ R : ℕ} (h : Whir.Admissible μ R) :
    ∀ levels, Whir.ladder μ R = some levels →
      levels.head?.map (fun l ↦ (l.fold, l.logInvRate)) = some (laneBits, R) ∧
        (levels.map (·.fold)).sum ≤ μ := by
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
      ∀ levels, Whir.ladder μ r = some levels →
        levels.head?.map (fun l ↦ (l.fold, l.logInvRate)) = some (laneBits, r) ∧
          (levels.map (·.fold)).sum ≤ μ := by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 R h2 h

/-- The ladder of an admissible pair, with its first level made explicit. -/
theorem exists_ladder {μ R : ℕ} (h : Whir.Admissible μ R) :
    ∃ q₀ rest, Whir.ladder μ R = some (⟨laneBits, R, q₀⟩ :: rest) ∧
      laneBits + (rest.map (·.fold)).sum ≤ μ := by
  obtain ⟨config, hc⟩ := Option.isSome_iff_exists.mp (Whir.ladder_isSome h)
  obtain ⟨hhead, hsum⟩ := ladder_head_sum h config hc
  rcases config with _ | ⟨⟨f, r, q₀⟩, rest⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hhead
    obtain ⟨rfl, rfl⟩ := hhead
    refine ⟨q₀, rest, hc, ?_⟩
    simpa using hsum

/-! ## The stack claims -/

/-- The batched basis of the stack claims, `p ↦ Σ_k s_k·w_k(p)` (`verify_stacked_opening`'s
`evaluate_basis`). -/
def batchedBasis (scales : List E) (claims : List StackClaim) : List E → E :=
  fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- The batched basis of multilinear weights is multilinear. -/
theorem isMultilinearFn_batchedBasis {m : ℕ} :
    ∀ (scales : List E) (claims : List StackClaim), (∀ c ∈ claims, IsMultilinearFn m c.1) →
      IsMultilinearFn m (batchedBasis scales claims)
  | [], _, _ => isMultilinearFn_congr (isMultilinearFn_const_zero m) fun p _ ↦ by
      simp [batchedBasis]
  | _ :: _, [], _ => isMultilinearFn_congr (isMultilinearFn_const_zero m) fun p _ ↦ by
      simp [batchedBasis]
  | a :: scales, c :: claims, h => by
    refine isMultilinearFn_congr (isMultilinearFn_add (isMultilinearFn_const_mul (h c (by simp)) a)
      (isMultilinearFn_batchedBasis scales claims fun c' hc' ↦ h c' (by simp [hc'])))
      fun p _ ↦ ?_
    simp [batchedBasis, dot_cons]

/-- The batched value of claims that hold is the batched basis paired with the stack. -/
theorem dot_values_eq_sum {μ : ℕ} (q : Column μ) :
    ∀ (scales : List E) (claims : List StackClaim), (∀ c ∈ claims, StackClaim.Holds μ c q) →
      dot scales (claims.map (·.2)) =
        ∑ x ∈ range (2 ^ μ), batchedBasis scales claims (boolPoint μ x) * ofK (q.values.getD x 0)
  | [], _, _ => by simp [batchedBasis]
  | _ :: _, [], _ => by simp [batchedBasis]
  | a :: scales, c :: claims, h => by
    have hc := h c (by simp)
    rw [StackClaim.Holds, Fin.sum_univ_eq_sum_range
      (fun x ↦ c.1 (boolPoint μ x) * ofK (q.values.getD x 0))] at hc
    simp only [List.map_cons, dot_cons, batchedBasis] at *
    rw [dot_values_eq_sum q scales claims fun c' hc' ↦ h c' (by simp [hc']), ← hc, mul_sum,
      ← sum_add_distrib]
    exact sum_congr rfl fun x _ ↦ by simp only [batchedBasis]; ring

/-- The batched basis at the rotated point: the weight table of the opening's starting claim. -/
def basisTable (μ : ℕ) (scales : List E) (claims : List StackClaim) : List E :=
  tableOf μ fun p ↦ batchedBasis scales claims (p.drop laneBits ++ p.take laneBits)

/-- **The starting claim.** The batched value of claims that hold is the pairing of the basis
table with the stack table, both in the WHIR variable order. -/
theorem dot_values_eq_dot {μ : ℕ} (hμ : laneBits ≤ μ) (q : Column μ) (scales : List E)
    (claims : List StackClaim) (h : ∀ c ∈ claims, StackClaim.Holds μ c q) :
    dot scales (claims.map (·.2)) = dot (basisTable μ scales claims) (stackTable μ q) := by
  rw [dot_values_eq_sum q scales claims h, basisTable, dot_tableOf _ _ _ (length_stackTable μ q)]
  obtain ⟨n, rfl⟩ : ∃ n, μ = laneBits + n := ⟨μ - laneBits, by omega⟩
  have hn : laneBits + n - laneBits = n := by omega
  have hrot := sum_rotIndex laneBits n
    (fun x ↦ batchedBasis scales claims (boolPoint (n + laneBits) x) *
      ofK (q.values.getD x 0))
  rw [Nat.add_comm n laneBits] at hrot
  rw [← hrot]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' : i < 2 ^ (laneBits + n) := mem_range.mp hi
  have hb := boolPoint_rotIndex laneBits n i hi'
  rw [Nat.add_comm n laneBits] at hb
  simp only [stackTable, hn]
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range, hb]

/-- The batched basis at the rotated point is the extension of the basis table. -/
theorem multilinearEval_basisTable {μ : ℕ} (hμ : laneBits ≤ μ) (scales : List E)
    (claims : List StackClaim) (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) (p : List E)
    (hp : p.length = μ) :
    multilinearEval (basisTable μ scales claims) p =
      batchedBasis scales claims (p.drop laneBits ++ p.take laneBits) := by
  obtain ⟨n, rfl⟩ : ∃ n, μ = laneBits + n := ⟨μ - laneBits, by omega⟩
  have hB := isMultilinearFn_batchedBasis scales claims hml
  rw [Nat.add_comm] at hB
  exact multilinearEval_tableOf (isMultilinearFn_rotate hB) p hp

/-! ## The opening -/

/-- **The honest prover of the stacked opening** (`verify_stacked_opening`, then `verify_whir`):
receive the batching challenge, then run the statement's levels from the stack table and the
basis table. -/
def honestOpening (μ R : ℕ) (q : Column μ) (claims : List StackClaim) : Script Unit := do
  let c ← Script.sampleE
  let scales := powers c claims.length
  match Whir.ladder μ R with
  | none => return ()
  | some config => levelsA μ config (stackTable μ q).toArray (basisTable μ scales claims).toArray

/-- The commitment the opening opens at level `0`: the stack's word, `2^(μ−6+R)` leaves of `64`
words. -/
def stackCommit (μ R : ℕ) (q : Column μ) : ℕ × ℕ × Word :=
  (μ - laneBits + R, 2 ^ laneBits, stackWord μ R q)

/-- **The honest commitment follows `commitStack`.** -/
theorem follows_commitStack {μ R : ℕ} (hadm : Whir.Admissible μ R) (q : Column μ)
    (cs : Commits) :
    Follows (fun cs' _ _ ↦ cs' = cs ++ [stackCommit μ R q]) (Script.commitS (stackWord μ R q))
      (commitStack μ R) cs := by
  obtain ⟨q₀, rest, hc, _⟩ := exists_ladder hadm
  simp only [commitStack, hc, Verifier.liftOption, VerifierProgram.bind_eq,
      VerifierProgram.ret_bind, levelShape]
  exact Follows.commitS_commitP (wellShaped_stackWord μ R q) cs

/-- **Perfect completeness of the stacked opening, as a simulation**: see the module docstring. -/
def OpeningComplete : Prop :=
  ∀ {μ R : ℕ}, Whir.Admissible μ R → ∀ (q : Column μ) (claims : List StackClaim),
    claims.length ≤ maxStackedClaims → (∀ c ∈ claims, StackClaim.Holds μ c q) →
    (∀ c ∈ claims, IsMultilinearFn μ c.1) →
    Follows (fun _ _ _ ↦ True) (honestOpening μ R q claims) (verifyStackedOpening μ R claims)
      [stackCommit μ R q]

/-- The simulation, from `OpeningComplete`. -/
theorem follows_verifyStackedOpening (hW : OpeningComplete) {μ R : ℕ} (hadm : Whir.Admissible μ R)
    (q : Column μ) (claims : List StackClaim) (hlen : claims.length ≤ maxStackedClaims)
    (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q) (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) :
    Follows (fun _ _ _ ↦ True) (honestOpening μ R q claims) (verifyStackedOpening μ R claims)
      [stackCommit μ R q] :=
  hW hadm q claims hlen hholds hml

/-- **Perfect completeness of the stacked opening**, from `OpeningComplete`: from any history
whose only commitment is the stack's honest word, every strategy that sends what the honest
prover sends after that history makes the interactive run of `verifyStackedOpening` return `()`
against every challenge function, and commits well-shaped words. -/
theorem runFrom_verifyStackedOpening (hW : OpeningComplete) {μ R : ℕ}
    (hadm : Whir.Admissible μ R) (q : Column μ) (claims : List StackClaim)
    (hlen : claims.length ≤ maxStackedClaims) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) (h : List Ev)
    (hcs : commits h = [stackCommit μ R q]) (S : Strategy)
    (hS : ∀ e, S.msg (h ++ e) = (honestOpening μ R q claims).msgAt e ∧
      S.word (h ++ e) = (honestOpening μ R q claims).wordAt e) (chal : List Ev → E) :
    S.runFrom chal (verifyStackedOpening μ R claims) h = some () ∧
      S.ShapedFrom chal (verifyStackedOpening μ R claims) h := by
  obtain ⟨⟨b, hb, -⟩, hsh⟩ := runFrom_of_follows' S chal hS
    (hcs ▸ follows_verifyStackedOpening hW hadm q claims hlen hholds hml)
  exact ⟨hb, hsh⟩

end
end LeanVM.Protocol.Whir.Complete
