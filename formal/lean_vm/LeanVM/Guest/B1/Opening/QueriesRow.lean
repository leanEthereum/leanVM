/-
  LeanVM.Guest.B1.Opening.QueriesRow

  One query's row: its packs, its fold at the point, and the final level's check.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT
public import LeanVM.Guest.B1.Common.Atoms

/-!
# A query's row, fold and final check (`opening_query`)

* `oqPack_sound`: a level-0 pack puts its two row words in `K` and makes the packed cell
  `E.ofLimbs` of their limbs (`pack64x2`); `oqRow s b σ` is the row's `K` words (level 0: the
  cells' low limbs; deeper: both limbs of each cell, `extRow`'s inverse).
* `oqFold_sound`: the fold's value is `foldRowE` of the lanes (the cells, reversed at level 0) at
  the point, the rounds read at `coefs` (`FoldAlg.guestFold_value`).
* `oqFin_sound`: the final check's coefficients are read at `hs` and the fold's value is
  `novelSum` of them over `wsChain` at the point.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Atoms -/

theorem oqRowT_atoms (b I : ℕ) : AllAtoms (oqRowT b I) := allAtoms_cons allAtoms_nil

theorem oqPackT_atoms (b I j : ℕ) : AllAtoms (oqPackT b I j) := by
  unfold oqPackT
  exact allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil)))

theorem oqPacksT_atoms (b I : ℕ) : AllAtoms (oqPacksT b I) :=
  allAtoms_map_flatten fun _ _ => oqPackT_atoms _ _ _

theorem oqPrepT_atoms (s : Oq) (b : ℕ) : AllAtoms (oqPrepT s b) := by
  unfold oqPrepT
  refine allAtoms_append (oqRowT_atoms _ _) ?_
  split
  · exact oqPacksT_atoms _ _
  · exact allAtoms_nil

theorem oqRoundT_atoms (s : Oq) (coefs x : V) (b F j : ℕ) : AllAtoms (oqRoundT s coefs x b F j) := by
  unfold oqRoundT
  refine allAtoms_append ?_ (allAtoms_map_flatten fun _ _ =>
    allAtoms_cons (allAtoms_cons allAtoms_nil))
  repeat' apply allAtoms_cons
  exact allAtoms_nil

theorem oqFoldT_atoms (s : Oq) (coefs x : V) (b F : ℕ) : AllAtoms (oqFoldT s coefs x b F) :=
  allAtoms_map_flatten fun _ _ => oqRoundT_atoms _ _ _ _ _ _

theorem oqWsT_atoms (s : Oq) (x : V) (v : ℕ) : AllAtoms (oqWsT s x v) :=
  allAtoms_cons (allAtoms_map_flatten fun _ _ =>
    allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil)))

theorem nvLevel0T_atoms (hs w : V) (n k : ℕ) : AllAtoms (nvLevel0T hs w n k) :=
  allAtoms_map_flatten fun _ _ =>
    allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil)))

theorem nvLevelT_atoms (w : V) : ∀ (ins : List ℕ) (k : ℕ), AllAtoms (nvLevelT w ins k).1
  | lo :: hi :: rest, k => by
    rw [nvLevelT]
    exact allAtoms_append (allAtoms_cons (allAtoms_cons allAtoms_nil)) (nvLevelT_atoms w rest (k + 2))
  | [_], _ => allAtoms_cons allAtoms_nil
  | [], _ => allAtoms_nil

theorem nvLevelsT_atoms (ws : ℕ → ℕ) : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ),
    AllAtoms (nvLevelsT ws c i ins k).1
  | 0, _, _, _ => allAtoms_nil
  | c + 1, i, ins, k => by
    rw [nvLevelsT]
    exact allAtoms_append (nvLevelT_atoms _ _ _) (nvLevelsT_atoms ws c _ _ _)

theorem oqNovel_atoms (s : Oq) (hs : V) (v : ℕ) : AllAtoms (oqNovel s hs v).1 :=
  allAtoms_append (nvLevel0T_atoms _ _ _ _) (nvLevelsT_atoms _ _ _ _ _)

theorem oqFinT_atoms (s : Oq) (x hs : V) (v : ℕ) : AllAtoms (oqFinT s x hs v) :=
  allAtoms_append (allAtoms_append (oqWsT_atoms _ _ _) (oqNovel_atoms _ _ _))
    (allAtoms_cons (allAtoms_cons allAtoms_nil))

/-! ## The row and the packs -/

/-- The row's `K` words: at level 0 the cells' low limbs, deeper both limbs of each cell. -/
def oqRow (s : Oq) (b : ℕ) (σ : Val) : List K :=
  if s.base = 1 then (List.range s.I).map fun j ↦ (σ (.n (b + j))).limb 0
  else (List.range s.I).flatMap fun j ↦ [(σ (.n (b + j))).limb 0, (σ (.n (b + j))).limb 1]

/-- The row's cells, as hinted. -/
def oqCells (s : Oq) (b : ℕ) (σ : Val) : List E := (List.range s.I).map fun j ↦ σ (.n (b + j))

/-- The lanes the guest folds: the cells, reversed at level 0. -/
def oqLanes (s : Oq) (b : ℕ) (σ : Val) : List E :=
  if s.base = 1 then (oqCells s b σ).reverse else oqCells s b σ

theorem mem_oqPacksT {b I j : ℕ} (hj : j < I / 2) {a : Atom} (h : Stmt.atom a ∈ oqPackT b I j) :
    Stmt.atom a ∈ oqPacksT b I :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, h⟩

/-- **A pack** (`pack64x2(row[2j], row[2j+1])`): both words in `K`, the packed cell the cell of
their limbs. -/
theorem oqPack_sound {b I j : ℕ} (hA : ∀ a, Stmt.atom a ∈ oqPacksT b I → a.Holds rd σ)
    (hj : j < I / 2) :
    IsInK (σ (.n (b + 2 * j))) ∧ IsInK (σ (.n (b + 2 * j + 1))) ∧
      σ (.n (b + I + 3 * j + 2)) =
        E.ofLimbs ((σ (.n (b + 2 * j))).limb 0) ((σ (.n (b + 2 * j + 1))).limb 0) := by
  have h1 := hA _ (mem_oqPacksT hj (by simp [oqPackT]) :
    Stmt.atom (.assertInK (.n (b + 2 * j)) (.n (b + 2 * j + 1))) ∈ _)
  have h2 := hA _ (mem_oqPacksT hj (by simp [oqPackT]) :
    Stmt.atom (.const (.n (b + I + 3 * j)) (word 0 1)) ∈ _)
  have h3 := hA _ (mem_oqPacksT hj (by simp [oqPackT]) :
    Stmt.atom (.mul (.n (b + I + 3 * j + 1)) (.n (b + I + 3 * j)) (.n (b + 2 * j + 1))) ∈ _)
  have h4 := hA _ (mem_oqPacksT hj (by simp [oqPackT]) :
    Stmt.atom (.add (.n (b + I + 3 * j + 2)) (.n (b + 2 * j)) (.n (b + I + 3 * j + 1))) ∈ _)
  simp only [Atom.Holds] at h1 h2 h3 h4
  refine ⟨h1.1, h1.2, ?_⟩
  rw [h4, h3, h2, word_y]
  exact pack64x2_eq h1.1 h1.2

/-! ## The fold -/

theorem mem_oqFoldT_round {s : Oq} {coefs x : V} {b F j : ℕ} (hj : j < s.folds) {a : Atom}
    (h : Stmt.atom a ∈ oqRoundT s coefs x b F j) : Stmt.atom a ∈ oqFoldT s coefs x b F :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, h⟩

theorem mem_oqRoundT_head {s : Oq} {coefs x : V} {b F j : ℕ} {a : Atom}
    (h : Stmt.atom a ∈ [Stmt.atom (.load (.n (oqRK s F j)) coefs (2 * j)),
      .atom (.load (.n (oqRK s F j + 1)) coefs (2 * j + 1)),
      .atom (.mul (.n (oqRK s F j + 2)) (.n (oqRK s F j + 1)) x),
      .atom (.add (.n (oqRK s F j + 3)) (.n (oqRK s F j)) (.n (oqRK s F j + 2)))]) :
    Stmt.atom a ∈ oqRoundT s coefs x b F j := by
  unfold oqRoundT
  exact List.mem_append_left _ h

theorem mem_oqRoundT_out {s : Oq} {coefs x : V} {b F j m : ℕ} (hm : m < 2 ^ (s.folds - 1 - j))
    {a : Atom} (h : Stmt.atom a ∈ [Stmt.atom (.mul (.n (oqRO s F j + 2 * m)) (.n (oqRK s F j + 3))
        (.n (oqLoHi s b F j m).1)),
      .atom (.add (.n (oqRO s F j + 2 * m + 1)) (.n (oqLoHi s b F j m).2) (.n (oqRO s F j + 2 * m)))]) :
    Stmt.atom a ∈ oqRoundT s coefs x b F j := by
  unfold oqRoundT
  exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩, h⟩)

/-- The rounds a fold reads: round `j`'s `α, β` at its values `K, K + 1`. -/
def oqRounds (s : Oq) (F : ℕ) (σ : Val) : List FoldRound :=
  (List.range s.folds).map fun j ↦ ⟨σ (.n (oqRK s F j)), σ (.n (oqRK s F j + 1))⟩

theorem oqRounds_getD {s : Oq} {F : ℕ} {σ : Val} {j : ℕ} (hj : j < s.folds) :
    (oqRounds s F σ).getD j ⟨0, 0⟩ = ⟨σ (.n (oqRK s F j)), σ (.n (oqRK s F j + 1))⟩ := by
  simp [oqRounds, List.getD_eq_getElem?_getD, hj]

/-- **The fold** (`opening_query`'s rounds): its value is `foldRowE` of the lanes at the point,
the rounds read at `coefs`. -/
theorem oqFold_sound {s : Oq} (hf : 1 ≤ s.folds) {coefs x : V} {b F : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqFoldT s coefs x b F → a.Holds rd σ) :
    RoundsAt rd (σ coefs) (oqRounds s F σ) ∧
      σ (.n (oqVal s F)) = foldRowE (oqLanes s b σ) (σ x) (oqRounds s F σ) := by
  have hR : ∀ j < s.folds, ∀ a, Stmt.atom a ∈ oqRoundT s coefs x b F j → a.Holds rd σ :=
    fun j hj a h ↦ hA a (mem_oqFoldT_round hj h)
  -- each round's head
  have head : ∀ j < s.folds,
      LoadHolds rd (σ coefs) (2 * j) (σ (.n (oqRK s F j))) ∧
      LoadHolds rd (σ coefs) (2 * j + 1) (σ (.n (oqRK s F j + 1))) ∧
      σ (.n (oqRK s F j + 3)) = σ (.n (oqRK s F j)) + σ (.n (oqRK s F j + 1)) * σ x := by
    intro j hj
    have g : ∀ a, Stmt.atom a ∈ _ → a.Holds rd σ := fun a h ↦ hR j hj a (mem_oqRoundT_head h)
    have l0 := g _ (List.mem_cons_self ..)
    have l1 := g _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have m2 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have a3 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
    simp only [Atom.Holds] at l0 l1 m2 a3
    exact ⟨l0, l1, by rw [a3, m2]⟩
  have hlen : (oqRounds s F σ).length = s.folds := by simp [oqRounds]
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [hlen] at hj
    rw [oqRounds_getD hj]
    exact ⟨(head j hj).1, (head j hj).2.1⟩
  · have hI : s.I = 2 ^ s.folds := rfl
    refine guestFold_value hlen hf (by simp [oqLanes, oqCells, hI]; split <;> simp)
      (acc := fun j m ↦ σ (.n (oqAcc s F j m))) (ts := fun j ↦ σ (.n (oqRK s F j + 3)))
      (fun j hj ↦ by rw [oqRounds_getD hj]; exact (head j hj).2.2)
      (fun m hm ↦ ?_) (fun j hj m hm ↦ ?_)
    · have hm' : m < 2 ^ (s.folds - 1 - 0) := by simpa using hm
      have hmul := hR 0 (by omega) _ (mem_oqRoundT_out hm' (List.mem_cons_self ..))
      have hadd := hR 0 (by omega) _ (mem_oqRoundT_out hm' (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      simp only [Atom.Holds] at hmul hadd
      simp only [oqAcc]
      rw [hadd, hmul]
      have h2m : 2 * m + 1 < s.I := by
        have : 2 ^ s.folds = 2 * 2 ^ (s.folds - 1) := by rw [← pow_succ']; congr 1; omega
        rw [hI]; omega
      unfold oqLoHi oqLanes oqCells
      by_cases hb : s.base = 1
      · simp only [hb, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_reverse,
          List.length_map, List.length_range, List.getElem?_map, List.getElem?_range,
          show 2 * m < s.I by omega, h2m, show s.I - 1 - 2 * m < s.I by omega,
          show s.I - 1 - (2 * m + 1) < s.I by omega, Option.map_some, Option.getD_some]
        rw [show s.I - 1 - (2 * m + 1) = s.I - 2 - 2 * m by omega,
          show b + (s.I - 1 - 2 * m) = b + s.I - 1 - 2 * m by omega,
          show b + (s.I - 2 - 2 * m) = b + s.I - 2 - 2 * m by omega]
      · simp only [hb, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
          show 2 * m < s.I by omega, h2m, Option.map_some, Option.getD_some, ← Nat.add_assoc]
    · have e : s.folds - 2 - j = s.folds - 1 - (j + 1) := by omega
      have hm' : m < 2 ^ (s.folds - 1 - (j + 1)) := by rw [← e]; exact hm
      have hmul := hR (j + 1) hj _ (mem_oqRoundT_out hm' (List.mem_cons_self ..))
      have hadd := hR (j + 1) hj _ (mem_oqRoundT_out hm' (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      simp only [Atom.Holds] at hmul hadd
      simp only [oqAcc]
      rw [hadd, hmul]
      simp only [oqLoHi, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, oqAcc]

/-! ## The final check -/

theorem nvLevelT_sound {w : V} : ∀ (ins : List ℕ) (k : ℕ),
    (∀ a, Stmt.atom a ∈ (nvLevelT w ins k).1 → a.Holds rd σ) →
      (nvLevelT w ins k).2.1.map (fun v ↦ σ (.n v)) = nvPair (σ w) (ins.map fun v ↦ σ (.n v))
  | lo :: hi :: rest, k, hA => by
    rw [nvLevelT] at hA ⊢
    have hm := hA _ (List.mem_append_left _ (List.mem_cons_self ..))
    have ha := hA _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only [Atom.Holds] at hm ha
    simp only [List.map_cons, nvPair]
    rw [nvLevelT_sound rest (k + 2) fun a h ↦ hA a (List.mem_append_right _ h), ha, hm]
  | [lo], k, hA => by
    rw [nvLevelT] at hA ⊢
    have hc := hA _ (List.mem_cons_self ..)
    simp only [Atom.Holds] at hc
    simp [nvPair, hc]
  | [], _, _ => by simp [nvLevelT, nvPair]

theorem nvLevelsT_sound {ws : ℕ → ℕ} : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ),
    (∀ a, Stmt.atom a ∈ (nvLevelsT ws c i ins k).1 → a.Holds rd σ) →
      (nvLevelsT ws c i ins k).2.1.map (fun v ↦ σ (.n v)) =
        nvTree (fun i ↦ σ (.n (ws i))) c i (ins.map fun v ↦ σ (.n v))
  | 0, _, _, _, _ => rfl
  | c + 1, i, ins, k, hA => by
    rw [nvLevelsT] at hA ⊢
    rw [nvTree, ← nvLevelT_sound ins k fun a h ↦ hA a (List.mem_append_left _ h)]
    exact nvLevelsT_sound c (i + 1) _ _ fun a h ↦ hA a (List.mem_append_right _ h)

/-- The chain's words: `W_i` at `oqWs v i`, `i ≤ mu`. -/
theorem oqWs_sound {s : Oq} {x : V} {v : ℕ} (hA : ∀ a, Stmt.atom a ∈ oqWsT s x v → a.Holds rd σ) :
    ∀ i ≤ s.mu, σ (.n (oqWs v i)) = wsChain (s.vs.map K.ofBits) (σ x) i
  | 0, _ => by
    have h := hA _ (List.mem_cons_self ..)
    simp only [Atom.Holds] at h
    simpa [oqWs, wsChain] using h
  | i + 1, hi => by
    have mem : ∀ a, Stmt.atom a ∈ [Stmt.atom (.const (.n (v + 2 + 3 * i)) (word (s.vs.getD i 0) 0)),
        .atom (.add (.n (v + 3 + 3 * i)) (.n (oqWs v i)) (.n (v + 2 + 3 * i))),
        .atom (.mul (.n (v + 4 + 3 * i)) (.n (oqWs v i)) (.n (v + 3 + 3 * i)))] →
        Stmt.atom a ∈ oqWsT s x v := fun a h ↦
      List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr
        (by omega), rfl⟩, h⟩)
    have hc := hA _ (mem _ (List.mem_cons_self ..))
    have ha := hA _ (mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hm := hA _ (mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    simp only [Atom.Holds] at hc ha hm
    have e : oqWs v (i + 1) = v + 4 + 3 * i := by simp only [oqWs]; split <;> omega
    rw [e, hm, ha, hc, oqWs_sound hA i (by omega), wsChain, word_eOfNat, eOfNat]
    congr 3
    simp [List.getD_eq_getElem?_getD]
    cases s.vs[i]? <;> rfl

/-- The final coefficients a check reads: the loads of its level `0`. -/
def oqHsv (s : Oq) (v : ℕ) (σ : Val) : List E :=
  (List.range s.nHs).map fun c ↦ σ (.n (v + 2 + 3 * s.mu + 4 * (c / 2) + c % 2))

theorem nvPair_range' (w : E) (f : ℕ → E) : ∀ (h s : ℕ),
    nvPair w ((List.range' s (2 * h)).map f) =
      (List.range h).map fun m ↦ f (s + 2 * m) + w * f (s + 2 * m + 1)
  | 0, s => by simp [nvPair]
  | h + 1, s => by
    rw [show 2 * (h + 1) = 2 * h + 1 + 1 by ring, List.range'_succ, List.range'_succ,
      List.range_succ_eq_map]
    simp only [List.map_cons, nvPair, List.map_map]
    rw [show s + 1 + 1 = s + 2 by omega, nvPair_range' w f h (s + 2)]
    simp only [Nat.mul_zero, Nat.add_zero]
    refine congrArg _ (List.map_congr_left fun m _ ↦ ?_)
    simp only [Function.comp_apply]
    rw [show s + 2 + 2 * m = s + 2 * (m + 1) by ring]

theorem nvLevel0T_sound {hs w : V} {n k : ℕ} (hn : n % 2 = 0)
    (hA : ∀ a, Stmt.atom a ∈ nvLevel0T hs w n k → a.Holds rd σ) :
    (∀ c < n, LoadHolds rd (σ hs) c (σ (.n (k + 4 * (c / 2) + c % 2)))) ∧
      ((List.range (n / 2)).map fun m ↦ k + 4 * m + 3).map (fun v ↦ σ (.n v)) =
        nvPair (σ w) ((List.range n).map fun c ↦ σ (.n (k + 4 * (c / 2) + c % 2))) := by
  have mem : ∀ m < n / 2, ∀ a, Stmt.atom a ∈
      [Stmt.atom (.load (.n (k + 4 * m)) hs (2 * m)), .atom (.load (.n (k + 4 * m + 1)) hs (2 * m + 1)),
        .atom (.mul (.n (k + 4 * m + 2)) w (.n (k + 4 * m + 1))),
        .atom (.add (.n (k + 4 * m + 3)) (.n (k + 4 * m)) (.n (k + 4 * m + 2)))] →
      a.Holds rd σ := fun m hm a h ↦
    hA a (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩, h⟩)
  refine ⟨fun c hc ↦ ?_, ?_⟩
  · have hm : c / 2 < n / 2 := by omega
    have l0 := mem (c / 2) hm _ (List.mem_cons_self ..)
    have l1 := mem (c / 2) hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [Atom.Holds] at l0 l1
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
    · rw [h0, Nat.add_zero]
      rw [show 2 * (c / 2) = c by omega] at l0
      exact l0
    · rw [h1]
      rw [show 2 * (c / 2) + 1 = c by omega] at l1
      exact l1
  · obtain ⟨h, rfl⟩ : ∃ h, n = 2 * h := ⟨n / 2, by omega⟩
    rw [show 2 * h / 2 = h by omega, show List.range (2 * h) = List.range' 0 (2 * h) from
      List.range_eq_range', nvPair_range', List.map_map]
    refine List.map_congr_left fun m hm ↦ ?_
    have hm' : m < 2 * h / 2 := by rw [List.mem_range] at hm; omega
    have hmul := mem m hm' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hadd := mem m hm' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
    simp only [Atom.Holds] at hmul hadd
    simp only [Function.comp_apply, Nat.zero_add]
    rw [hadd, hmul, show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega,
      show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]
    simp only [Nat.add_zero]

theorem nvLevelT_ne {w : V} : ∀ (ins : List ℕ) (k : ℕ), ins ≠ [] → (nvLevelT w ins k).2.1 ≠ []
  | _ :: _ :: _, _, _ => by simp [nvLevelT]
  | [_], _, _ => by simp [nvLevelT]
  | [], _, h => absurd rfl h

theorem nvLevelsT_ne {ws : ℕ → ℕ} : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ), ins ≠ [] →
    (nvLevelsT ws c i ins k).2.1 ≠ []
  | 0, _, _, _, h => h
  | c + 1, i, ins, k, h => by
    rw [nvLevelsT]
    exact nvLevelsT_ne c (i + 1) _ _ (nvLevelT_ne ins k h)

/-- **The final check**: the coefficients read at `hs` and the fold's value `v` their `novelSum`
over the chain at the point, `n_hs` even and the chain long enough. -/
theorem oqFin_sound {s : Oq} {x hs : V} {v : ℕ} (hn : s.nHs % 2 = 0) (hn2 : 2 ≤ s.nHs)
    (hb : 1 ≤ s.hsBits)
    (hmu : s.hsBits - 1 ≤ s.mu) (hA : ∀ a, Stmt.atom a ∈ oqFinT s x hs v → a.Holds rd σ) :
    WordsAt rd (σ hs) (oqHsv s v σ) ∧ (oqHsv s v σ).length = s.nHs ∧
      σ (.n v) = novelSum (oqHsv s v σ) (wsChain (s.vs.map K.ofBits) (σ x)) s.nHs s.hsBits := by
  have hW := oqWs_sound (rd := rd) (σ := σ) (s := s) (x := x) (v := v)
    fun a h ↦ hA a (List.mem_append_left _ (List.mem_append_left _ h))
  have hN : ∀ a, Stmt.atom a ∈ (oqNovel s hs v).1 → a.Holds rd σ :=
    fun a h ↦ hA a (List.mem_append_left _ (List.mem_append_right _ h))
  have h0 := nvLevel0T_sound hn fun a h ↦ hN a (List.mem_append_left _ h)
  have hL := nvLevelsT_sound (ws := oqWs v) _ _ _ _ fun a h ↦ hN a (List.mem_append_right _ h)
  have heq := hA _ (List.mem_append_right _ (List.mem_cons_self ..))
  simp only [Atom.Holds] at heq
  have hlen : (oqHsv s v σ).length = s.nHs := by simp [oqHsv]
  refine ⟨fun c hc ↦ ?_, hlen, ?_⟩
  · rw [hlen] at hc
    have := h0.1 c hc
    simpa [oqHsv, List.getD_eq_getElem?_getD, hc] using this
  · have hv : σ (.n v) = σ (.n ((oqNovel s hs v).2.1.headD 0)) := by
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at heq; exact heq
    rw [hv, novelSum, List.take_of_length_le (by omega)]
    obtain ⟨c, hc⟩ : ∃ c, s.hsBits = c + 1 := ⟨s.hsBits - 1, by omega⟩
    rw [hc, nvTree]
    have hws : ∀ i ≤ c, σ (.n (oqWs v i)) = wsChain (s.vs.map K.ofBits) (σ x) i :=
      fun i hi ↦ hW i (by omega)
    have hpair : nvPair (wsChain (s.vs.map K.ofBits) (σ x) 0) (oqHsv s v σ) =
        ((List.range (s.nHs / 2)).map fun m ↦ v + 2 + 3 * s.mu + 4 * m + 3).map (fun u ↦ σ (.n u)) := by
      rw [h0.2, ← hW 0 (Nat.zero_le _)]
      rfl
    have htree : ∀ (c i : ℕ) (l : List E), (∀ j < c, σ (.n (oqWs v (i + j))) =
        wsChain (s.vs.map K.ofBits) (σ x) (i + j)) →
        nvTree (fun i ↦ σ (.n (oqWs v i))) c i l = nvTree (wsChain (s.vs.map K.ofBits) (σ x)) c i l := by
      intro c
      induction c with
      | zero => intro i l _; rfl
      | succ c ih =>
        intro i l h
        rw [nvTree, nvTree, show σ (.n (oqWs v i)) = wsChain (s.vs.map K.ofBits) (σ x) i by
          simpa using h 0 (by omega)]
        exact ih (i + 1) _ fun j hj ↦ by rw [show i + 1 + j = i + (j + 1) by omega]; exact h _ (by omega)
    rw [hpair, ← htree c 1 _ (fun j hj ↦ hws _ (by omega))]
    have hsb : s.hsBits - 1 = c := by omega
    have hL' : ((oqNovel s hs v).2.1).map (fun u ↦ σ (.n u)) = nvTree (fun i ↦ σ (.n (oqWs v i)))
        (s.hsBits - 1) 1
        (((List.range (s.nHs / 2)).map fun m ↦ v + 2 + 3 * s.mu + 4 * m + 3).map fun u ↦ σ (.n u)) := hL
    rw [hsb] at hL'
    have hne : (oqNovel s hs v).2.1 ≠ [] := nvLevelsT_ne _ _ _ _ (by
      simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega)
    rw [← hL']
    revert hne
    generalize (oqNovel s hs v).2.1 = outs
    intro hne
    cases outs with
    | nil => exact absurd rfl hne
    | cons o _ => rfl

end
end LeanVM.Guest.B1
