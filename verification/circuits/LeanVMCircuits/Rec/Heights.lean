module

public import LeanVMCircuits.Rec.TableSum
public import LeanVMCircuits.Rec.Design

@[expose] public section

/-!
The layout's heights from `Tree::converge`, and the table sumcheck's rounds.

`Tree::new` builds every circuit at its tier's heights `σ t` (`Tree::converge`, `Design.converge`): it rebuilds the circuits at the tiers' heights until no circuit's heights (`Circuit::heights`) pass its tier's, each round requiring `RecLayout::from_taus` to accept each tier's (every `τ` at most `MAX_TAU = 32`), and then raises each circuit's floor to its tier's heights (`Circuit::with_floor`). A node's verifier reads a child of tier `t` at `σ t` (`RecShape::new`). `layoutFits_converge`: where each circuit's heights hold its rows (`HeightsHold`: `Table::height_log` is at least the rows' `clog 2`), every circuit `converge` returns fits its tier's layout (`LayoutFits`), the hypothesis `AirLink.checksGiveInst_of_table` takes.

`constraints::verify` runs `n` rounds, `n` the tallest owned table's `τ` (`airs.iter().map(|a| a.tau).max()`): `taus_le_rounds` is the other hypothesis, every owned table's `τ` at most `n`.

`circuitHeights` transcribes `Circuit::heights` (`Table::height_log` of each table's rows, at least its floor), and `heightsHold_circuit` proves it holds the rows; `checksGiveRows_of_tree` is `checksGiveRows_of_converge` at those heights, `HeightsHold` discharged.
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset Edges

/-- The tables, `Table.all`. -/
instance : Fintype Table where
  elems := {.emul, .exk, .hash, .split, .cast, .pub}
  complete T := by cases T <;> simp

/-- A circuit's heights hold its rows: each table's rows at most `2^h_T` (`Circuit::heights`). -/
def HeightsHold (s : State) (h : Table → ℕ) : Prop := ∀ T, (rowsOf s T).size ≤ 2 ^ h T

/-- `RecLayout::from_taus` accepts the heights: every `τ` at most `MAX_TAU = 32`. -/
def fitsTaus (σ : Table → ℕ) : Bool := decide (∀ T, σ T ≤ 32)

/-- The least heights holding a circuit's rows: `clog 2` of each table's rows, which `Table::height_log` is at least
(`log2_ceil_usize`, and flock's batch for the hash table). -/
theorem heightsHold_clog (s : State) : HeightsHold s fun T => Nat.clog 2 (rowsOf s T).size :=
  fun _ => Nat.le_pow_clog (by norm_num) _

/-- Heights holding a circuit's rows, below heights `RecLayout::from_taus` accepts, make a layout that fits. -/
theorem layoutFits_of_le {s : State} {h σ : Table → ℕ} (hh : HeightsHold s h) (hle : ∀ T, h T ≤ σ T)
    (hσ : fitsTaus σ = true) : LayoutFits s σ := by
  have h32 : ∀ T, σ T ≤ 32 := by simpa [fitsTaus] using hσ
  exact fun T => ⟨(hh T).trans (Nat.pow_le_pow_right (by norm_num) (hle T)), h32 T⟩

/-- Every circuit `Tree::converge` returns fits its tier's layout: circuit `p` of tier `t`, built at the tiers'
heights `σ` (`circ σ p`), with heights `H σ p` holding its rows, fits `σ t`. -/
theorem layoutFits_converge (n : ℕ) (members : ℕ → List ℕ) (circ : (ℕ → Table → ℕ) → ℕ → State)
    (H : (ℕ → Table → ℕ) → ℕ → Table → ℕ) (hH : ∀ σ p, HeightsHold (circ σ p) (H σ p)) (k : ℕ)
    (σ₀ σ : ℕ → Table → ℕ) (h : Design.converge n members H fitsTaus k σ₀ = some σ) :
    ∀ t < n, ∀ p ∈ members t, LayoutFits (circ σ p) (σ t) := by
  obtain ⟨hfit, hle, -⟩ := Design.converge_fits n members H fitsTaus k σ₀ σ h
  exact fun t ht p hp => layoutFits_of_le (hH σ p) (hle t ht p hp) (hfit t ht)

/-- Non-vacuity: a tier of one empty circuit at heights three converges in two rounds, and fits them. -/
example : Design.converge 1 (fun _ => [0]) (fun _ _ _ => 3) fitsTaus 2 (fun _ _ => 3) = some (fun _ _ => 3) ∧
    LayoutFits ({} : State) fun _ => 3 :=
  have h : Design.converge 1 (fun _ => [0]) (fun _ _ _ => 3) fitsTaus 2 (fun _ _ => 3) = some (fun _ _ => 3) :=
    rfl
  ⟨h, layoutFits_converge 1 (fun _ => [0]) (fun _ _ => {}) (fun _ _ _ => 3)
    (fun _ _ T => by cases T <;> simp [rowsOf]) 2 _ _ h 0 one_pos 0 (by simp)⟩

/-- The table sumcheck's rounds, `constraints::verify`'s `n`: the tallest owned table's `τ`. -/
def rounds (taus : Table → ℕ) : ℕ := owned.sup taus

/-- Every owned table's `τ` is at most the rounds. -/
theorem taus_le_rounds (taus : Table → ℕ) : ∀ T ∈ owned, taus T ≤ rounds taus := fun _ hT => le_sup hT

/-- `ChecksGiveRows` from `ChecksGiveTable` for a tree `Tree::converge` built: each child `v` is circuit `pos v` of
tier `tier v` built at the converged heights `σ`, its parent's verifier reads it at its tier's heights, and the table
sumcheck runs `rounds` of them. `checksGiveRows_of_table`'s layout and rounds hypotheses hold (`layoutFits_converge`,
`taus_le_rounds`). -/
theorem checksGiveRows_of_converge {ι Ω : Type} [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → Edges.EdgeCert)
    (t : ι → State) (os : ι → Array (List ℕ)) (L : Edges.Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K)
    (val : ι → Ω → Val) (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad)
    (tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K) (m : ℕ) (members : ℕ → List ℕ)
    (circ : (ℕ → Table → ℕ) → ℕ → State) (H : (ℕ → Table → ℕ) → ℕ → Table → ℕ)
    (hH : ∀ σ p, HeightsHold (circ σ p) (H σ p)) (k : ℕ) (σ₀ σ : ℕ → Table → ℕ)
    (hconv : Design.converge m members H fitsTaus k σ₀ = some σ) (tier pos : ι → ℕ)
    (hpos : ∀ v ∈ T.nodes, tier v < m ∧ pos v ∈ members (tier v) ∧ t v = circ σ (pos v) ∧ taus v = σ (tier v) ∧
      n v = rounds (taus v))
    (h : ChecksGiveTable T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols) :
    ChecksGiveRows T cert t os L slot stRoot val P
      (fun v => batchBad (witAt T cert t slot stRoot val taus cols v)
        (fun ω ζ i => formSums (witAt T cert t slot stRoot val taus cols v ω) ζ (qforms v ω ζ) i - tot v ω ζ i)
        (bdraw v))
      draw (witAt T cert t slot stRoot val taus cols) := by
  refine checksGiveRows_of_table T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols
    (fun v hv => ?_) (fun v hv T' hT' => ?_) h
  · obtain ⟨ht, hp, htv, hτ, -⟩ := hpos v hv
    rw [htv, hτ]
    exact layoutFits_converge m members circ H hH k σ₀ σ hconv (tier v) ht (pos v) hp
  · obtain ⟨-, -, -, -, hn⟩ := hpos v hv
    rw [hn]
    exact taus_le_rounds (taus v) T' hT'

/-! `Circuit::heights`, transcribed. -/

/-- `primitives::log2_ceil_usize`: `0` up to one, else `ilog2 (n - 1) + 1`. -/
def log2Ceil (n : ℕ) : ℕ := if n ≤ 1 then 0 else Nat.log 2 (n - 1) + 1

/-- `flock::reduction::min_n_blocks_log`: `max n 8`'s `next_power_of_two().trailing_zeros()`, the least `k` with
`max n 8 ≤ 2^k`. -/
def minBlocksLog (n : ℕ) : ℕ := Nat.clog 2 (max n 8)

/-- `Table::height_log`: for the hash table `tables::batch_log`, the larger of `min_n_blocks_log` of the rows (at least
one) and flock's floor `cube` (`MIN_CUBE_LOG` less the hash circuit's `k_log`, saturating); for the others
`log2_ceil_usize` of the rows (at least one). -/
def heightLog (cube : ℕ) (T : Table) (rows : ℕ) : ℕ :=
  if T = .hash then max (minBlocksLog (max rows 1)) cube else log2Ceil (max rows 1)

/-- `Circuit::heights`: each table's `height_log` of its rows, at least its floor. -/
def circuitHeights (cube : ℕ) (floor : Table → ℕ) (s : State) (T : Table) : ℕ :=
  max (heightLog cube T (rowsOf s T).size) (floor T)

theorem le_pow_log2Ceil (n : ℕ) : n ≤ 2 ^ log2Ceil n := by
  unfold log2Ceil
  split_ifs with h
  · simp only [pow_zero]
    exact h
  · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n - 1)
    rw [Nat.succ_eq_add_one] at this
    omega

/-- A table's height holds its rows. -/
theorem le_pow_heightLog (cube : ℕ) (T : Table) (rows : ℕ) : rows ≤ 2 ^ heightLog cube T rows := by
  unfold heightLog
  split_ifs
  · calc rows ≤ max (max rows 1) 8 := le_max_of_le_left (le_max_left _ _)
      _ ≤ 2 ^ minBlocksLog (max rows 1) := Nat.le_pow_clog (by norm_num) _
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  · exact (le_max_left rows 1).trans (le_pow_log2Ceil _)

/-- `Circuit::heights` holds its rows, whatever its floor: `HeightsHold`, the premise `layoutFits_converge` takes. -/
theorem heightsHold_circuit (cube : ℕ) (floor : Table → ℕ) (s : State) :
    HeightsHold s (circuitHeights cube floor s) := fun T =>
  (le_pow_heightLog cube T _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

/-- Non-vacuity: three hash rows at flock's floor `4` take height `2^4`, and ten SPLIT rows `2^4`. -/
example : heightLog 4 .hash 3 = 4 ∧ heightLog 4 .split 10 = 4 := by decide

/-- `checksGiveRows_of_converge` with the heights `Tree::converge` reads, `Circuit::heights` at no floor
(`circuitHeights`): their premise `HeightsHold` is proven (`heightsHold_circuit`). Left as the tree's building facts:
each child is its position's circuit built at the converged heights, its parent reads it at its tier's heights, and
the table sumcheck runs `rounds` of them (`hpos`). -/
theorem checksGiveRows_of_tree {ι Ω : Type} [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → Edges.EdgeCert)
    (t : ι → State) (os : ι → Array (List ℕ)) (L : Edges.Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K)
    (val : ι → Ω → Val) (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad)
    (tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K) (m : ℕ) (members : ℕ → List ℕ)
    (circ : (ℕ → Table → ℕ) → ℕ → State) (cube k : ℕ) (σ₀ σ : ℕ → Table → ℕ)
    (hconv : Design.converge m members (fun σ p => circuitHeights cube (fun _ => 0) (circ σ p)) fitsTaus k σ₀ =
      some σ) (tier pos : ι → ℕ)
    (hpos : ∀ v ∈ T.nodes, tier v < m ∧ pos v ∈ members (tier v) ∧ t v = circ σ (pos v) ∧ taus v = σ (tier v) ∧
      n v = rounds (taus v))
    (h : ChecksGiveTable T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols) :
    ChecksGiveRows T cert t os L slot stRoot val P
      (fun v => batchBad (witAt T cert t slot stRoot val taus cols v)
        (fun ω ζ i => formSums (witAt T cert t slot stRoot val taus cols v ω) ζ (qforms v ω ζ) i - tot v ω ζ i)
        (bdraw v))
      draw (witAt T cert t slot stRoot val taus cols) :=
  checksGiveRows_of_converge T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols m members circ
    _ (fun σ p => heightsHold_circuit cube _ (circ σ p)) k σ₀ σ hconv tier pos hpos h

end LeanVMCircuits.Rec.AirLink
