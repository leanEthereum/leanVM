/-
  LeanVM.Semantics.KeccakCells

  The thirteen cells of a `KECCAK` instruction: the cells holding a state's lanes in a layout,
  the state they hold, and what `execute` checks of a `KECCAK` instruction.
-/

module

public import LeanVM.Semantics.Lemmas
public import Statement.LeanIsa
public import LeanVM.Facts.IsaWith
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords

/-!
# The cells of `KECCAK`

`KECCAK` reads thirteen cells holding a Keccak state, two lanes to a cell, in one of two layouts
(`cellLanes`), and writes the first one, two or thirteen of the thirteen cells of the
permutation (`Statement.LeanIsa`). This module names the cells holding given
lanes in a layout (`laneCells`: a limb holding no lane reads `free`), and proves the three facts
the arithmetization needs:

* `stateOfCells_laneCells`: the state the cells hold is the lanes, whatever the free limb;
* `cellsOfState_eq_laneCells`: the cells `KECCAK` writes are `laneCells` of the output state,
  the free limb zero;
* `laneCells_eq_iff`: two such cell lists (free limb zero) are equal exactly when their lanes
  are, since every lane sits in exactly one limb;

and `execute_keccak_eq_some_iff`, `execute` of a `KECCAK` as reads and the relation.
-/

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-- The limb of a cell holding lane `l?` of the lanes `L`: `free` where the limb holds no lane. -/
def laneLimb (L : Fin 25 → K) (free : K) : Option ℕ → K
  | some l => if h : l < 25 then L ⟨l, h⟩ else 0
  | none => free

/-- The thirteen cells holding the lanes `L` in the layout `odd`: two lanes to a cell, one per
limb, the limb holding no lane `free`. -/
def laneCells (L : Fin 25 → K) (odd : Bool) (free : K) (c : Fin 13) : E :=
  E.ofLimbs (laneLimb L free (cellLanes odd c).1) (laneLimb L free (cellLanes odd c).2)

/-- The state of the lanes `L`, each as a 64-bit lane. -/
def laneState (L : Fin 25 → K) : KeccakState := Vector.ofFn fun l ↦ (L l).lane

/-- The lanes of a state, as `K` words. -/
def stateLanes (S : KeccakState) (l : Fin 25) : K := K.ofLane (Keccak.lane S l)

theorem laneState_stateLanes (S : KeccakState) : laneState (stateLanes S) = S := by
  apply Vector.ext
  intro i hi
  simp [laneState, stateLanes, Keccak.lane, Array.getD_eq_getD_getElem?]

theorem stateLanes_laneState (L : Fin 25 → K) : stateLanes (laneState L) = L := by
  funext l
  simp [laneState, stateLanes, Keccak.lane, Array.getD_eq_getD_getElem?]

/-! ## The three facts -/

set_option maxHeartbeats 4000000 in
/-- **The state the cells hold is the lanes**, whatever the limb holding no lane holds. -/
theorem stateOfCells_laneCells (L : Fin 25 → K) (odd : Bool) (free : K) :
    stateOfCells (laneCells L odd free) odd = laneState L := by
  cases odd <;>
  · apply Vector.ext
    intro i hi
    simp only [stateOfCells, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldl,
      laneCells, cellLanes, laneLimb, limb_ofLimbs]
    interval_cases i <;> simp [laneState]

set_option maxHeartbeats 4000000 in
/-- **The cells `KECCAK` writes** are the cells of the state's lanes, the free limb zero. -/
theorem cellsOfState_eq_laneCells (S : KeccakState) (odd : Bool) :
    cellsOfState S odd = laneCells (stateLanes S) odd 0 := by
  funext c
  cases odd <;> fin_cases c <;> simp [cellsOfState, laneCells, cellLanes, laneLimb, stateLanes]

set_option maxHeartbeats 4000000 in
/-- **Cells with the free limb zero are equal exactly when their lanes are**: every lane sits in
one limb of one cell, in either layout. -/
theorem laneCells_eq_iff {L L' : Fin 25 → K} {odd : Bool} :
    laneCells L odd 0 = laneCells L' odd 0 ↔ L = L' := by
  constructor
  · intro h
    have hs := congrArg (fun cells ↦ stateOfCells cells odd) h
    simp only [stateOfCells_laneCells] at hs
    rw [← stateLanes_laneState L, ← stateLanes_laneState L', hs]
  · rintro rfl
    rfl

/-- The limb of the cells that holds no lane in the layout `odd`: cell `8`'s high limb in the even
layout, cell `0`'s low limb in the odd one. -/
def freeLimb (cells : Fin 13 → E) (odd : Bool) : K :=
  if odd then (cells 0).limb 0 else (cells 8).limb 1

set_option maxHeartbeats 4000000 in
/-- **Cells are the cells of the lanes they hold**, the limb holding no lane theirs. -/
theorem laneCells_stateOfCells (cells : Fin 13 → E) (odd : Bool) :
    laneCells (stateLanes (stateOfCells cells odd)) odd (freeLimb cells odd) = cells := by
  funext c
  apply E.ext
  intro i
  cases odd <;> fin_cases c <;> fin_cases i <;>
    simp [laneCells, cellLanes, laneLimb, stateLanes, stateOfCells, freeLimb, List.finRange,
      List.ofFn, Fin.foldr, Fin.foldr.loop, Keccak.lane]

/-- **The deployed check implies the reduction-blind one**: the cells Keccak-f writes have their
free limb zero. -/
theorem freeLimbZero_of_keccakCells {input output : Fin 13 → E} {inOdd outOdd : Bool}
    {outCells : KeccakOutputCells} (h : KeccakCellsRelation input inOdd output outOdd outCells) :
    FreeLimbZero output outOdd outCells := by
  have ho : ∀ c : Fin 13, c.val < outCells.cellCount →
      output c = laneCells (stateLanes (keccakF1600 (stateOfCells input inOdd))) outOdd 0 c := by
    intro c hc; rw [h c hc, cellsOfState_eq_laneCells]
  have h0 : 0 < outCells.cellCount := by cases outCells <;> decide
  cases outOdd
  · intro h8
    rw [ho 8 h8]; simp [laneCells, cellLanes, laneLimb, limb_ofLimbs]
  · show (output 0).limb 0 = 0
    rw [ho 0 h0]; simp [laneCells, cellLanes, laneLimb, limb_ofLimbs]

/-! ## Segments of the permutation -/

/-- Segment `m` of Keccak-f[1600]: its rounds `12m` to `12m + 11` (the Keccak reduction's
`KECCAK_DEPTH = 12`, `crates/verifier/src/layout.rs:83`). -/
def keccakSegment (m : ℕ) (a : KeccakState) : KeccakState :=
  ((keccakRC.drop (12 * m)).take 12).foldl Keccak.round a

/-- **Keccak-f[1600] is its two segments.** -/
theorem keccakF_eq_segments (a : KeccakState) : keccakF1600 a = keccakSegment 1 (keccakSegment 0 a) := by
  unfold keccakF1600 keccakSegment
  rw [← List.foldl_append]
  rfl

/-! ## Reading the cells -/

/-- The fold of `readCells` over a list of cells: it succeeds with `f` exactly when every cell of
the list reads `f` of it, and `f` is zero off the list. -/
theorem readCells_fold_eq_some_iff (read : K → Option E) (fp : K) (offset : Fin 13 → K) :
    ∀ (cs : List (Fin 13)) (f : Fin 13 → E),
      cs.foldr (fun c (acc : Option (Fin 13 → E)) ↦ (do
          let v ← read (fp * offset c)
          let rest ← acc
          pure fun c' ↦ if c' = c then v else rest c' : Option (Fin 13 → E))) (some fun _ ↦ 0) =
          some f ↔
        (∀ c ∈ cs, read (fp * offset c) = some (f c)) ∧ ∀ c, c ∉ cs → f c = 0
  | [], f => by
    simp only [List.foldr_nil, Option.some.injEq, List.not_mem_nil, false_imp_iff, implies_true,
      not_false_eq_true, forall_const, true_and]
    constructor
    · rintro rfl c; rfl
    · intro h; funext c; exact (h c).symm
  | c :: cs, f => by
    rw [List.foldr_cons]
    constructor
    · intro h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v, hv, g, hg, rfl⟩ := h
      obtain ⟨hg1, hg2⟩ := (readCells_fold_eq_some_iff read fp offset cs g).mp hg
      refine ⟨?_, ?_⟩
      · intro c' hc'
        by_cases hcc : c' = c
        · subst hcc; simpa using hv
        · simp only [hcc, ↓reduceIte]
          exact hg1 c' ((List.mem_cons.mp hc').resolve_left hcc)
      · intro c' hc'
        have hne : c' ≠ c := fun h ↦ hc' (h ▸ List.mem_cons_self)
        simp only [hne, ↓reduceIte]
        exact hg2 c' fun h ↦ hc' (List.mem_cons_of_mem _ h)
    · rintro ⟨h1, h2⟩
      have hv := h1 c List.mem_cons_self
      let g : Fin 13 → E := fun c' ↦ if c' ∈ cs then f c' else 0
      have hg : cs.foldr (fun c (acc : Option (Fin 13 → E)) ↦ (do
          let v ← read (fp * offset c)
          let rest ← acc
          pure fun c' ↦ if c' = c then v else rest c' : Option (Fin 13 → E)))
          (some fun _ ↦ 0) = some g := by
        refine (readCells_fold_eq_some_iff read fp offset cs g).mpr ⟨?_, ?_⟩
        · intro c' hc'
          simp only [g, hc', ↓reduceIte]
          exact h1 c' (List.mem_cons_of_mem _ hc')
        · intro c' hc'
          simp [g, hc']
      simp only [Option.bind_eq_bind, Option.pure_def] at hg ⊢
      rw [hv, Option.bind_some, hg, Option.bind_some, Option.some.injEq]
      funext c'
      by_cases hcc : c' = c
      · subst hcc; simp
      · simp only [hcc, ↓reduceIte, g]
        split_ifs with hm
        · rfl
        · exact (h2 c' fun h ↦ (List.mem_cons.mp h).elim hcc hm).symm

/-- `readCells` succeeds with `f` exactly when every cell reads `f` of it. -/
theorem readCells_eq_some_iff (read : K → Option E) (fp : K) (offset : Fin 13 → K)
    (f : Fin 13 → E) :
    readCells read fp offset = some f ↔ ∀ c, read (fp * offset c) = some (f c) := by
  unfold readCells
  rw [readCells_fold_eq_some_iff]
  simp [List.mem_finRange]

/-- The fold of `readFirstCells` over a list of cells: it succeeds with `f` exactly when every
cell of the list below `n` reads `f` of it, and `f` is zero at every other cell. -/
theorem readFirstCells_fold_eq_some_iff (read : K → Option E) (fp : K) (offset : Fin 13 → K)
    (n : ℕ) : ∀ (cs : List (Fin 13)) (f : Fin 13 → E),
      cs.foldr (fun c (acc : Option (Fin 13 → E)) ↦ if c.val < n then (do
          let v ← read (fp * offset c)
          let rest ← acc
          pure fun c' ↦ if c' = c then v else rest c' : Option (Fin 13 → E)) else acc)
          (some fun _ ↦ 0) = some f ↔
        (∀ c ∈ cs, c.val < n → read (fp * offset c) = some (f c)) ∧
          ∀ c, (c ∈ cs → n ≤ c.val) → f c = 0
  | [], f => by
    simp only [List.foldr_nil, Option.some.injEq, List.not_mem_nil, implies_true, true_and,
      IsEmpty.forall_iff, forall_const]
    constructor
    · rintro rfl c; rfl
    · intro h; funext c; exact (h c).symm
  | c :: cs, f => by
    rw [List.foldr_cons]
    by_cases hcn : c.val < n
    · simp only [hcn, ↓reduceIte]
      constructor
      · intro h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨v, hv, g, hg, rfl⟩ := h
        obtain ⟨hg1, hg2⟩ := (readFirstCells_fold_eq_some_iff read fp offset n cs g).mp hg
        refine ⟨?_, ?_⟩
        · intro c' hc' hn'
          by_cases hcc : c' = c
          · subst hcc; simpa using hv
          · simp only [hcc, ↓reduceIte]
            exact hg1 c' ((List.mem_cons.mp hc').resolve_left hcc) hn'
        · intro c' hc'
          have hne : c' ≠ c := fun h ↦ absurd (hc' (h ▸ List.mem_cons_self)) (by omega)
          simp only [hne, ↓reduceIte]
          exact hg2 c' fun h ↦ hc' (List.mem_cons_of_mem _ h)
      · rintro ⟨h1, h2⟩
        have hv := h1 c List.mem_cons_self hcn
        let g : Fin 13 → E := fun c' ↦ if c' ∈ cs ∧ c'.val < n then f c' else 0
        have hg : cs.foldr (fun c (acc : Option (Fin 13 → E)) ↦ if c.val < n then (do
            let v ← read (fp * offset c)
            let rest ← acc
            pure fun c' ↦ if c' = c then v else rest c' : Option (Fin 13 → E)) else acc)
            (some fun _ ↦ 0) = some g := by
          refine (readFirstCells_fold_eq_some_iff read fp offset n cs g).mpr ⟨?_, ?_⟩
          · intro c' hc' hn'
            simp only [g, hc', hn', and_self, ↓reduceIte]
            exact h1 c' (List.mem_cons_of_mem _ hc') hn'
          · intro c' hc'
            simp only [g]
            split_ifs with hm
            · exact absurd (hc' hm.1) (by omega)
            · rfl
        simp only [Option.bind_eq_bind, Option.pure_def] at hg ⊢
        rw [hv, Option.bind_some, hg, Option.bind_some, Option.some.injEq]
        funext c'
        by_cases hcc : c' = c
        · subst hcc; simp
        · simp only [hcc, ↓reduceIte, g]
          split_ifs with hm
          · rfl
          · refine (h2 c' fun h ↦ ?_).symm
            rcases List.mem_cons.mp h with h | h
            · exact absurd h hcc
            · by_contra hlt; exact hm ⟨h, by omega⟩
    · simp only [hcn, ↓reduceIte]
      rw [readFirstCells_fold_eq_some_iff read fp offset n cs f]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun c' hc' hn' ↦ ?_, fun c' hc' ↦ h2 c' fun h ↦ hc' (List.mem_cons_of_mem _ h)⟩
        rcases List.mem_cons.mp hc' with rfl | h
        · exact absurd hn' hcn
        · exact h1 c' h hn'
      · rintro ⟨h1, h2⟩
        refine ⟨fun c' hc' hn' ↦ h1 c' (List.mem_cons_of_mem _ hc') hn', fun c' hc' ↦ h2 c' ?_⟩
        intro h
        rcases List.mem_cons.mp h with rfl | h
        · omega
        · exact hc' h

/-- `readFirstCells` succeeds with `f` exactly when every cell below `n` reads `f` of it and `f` is
zero at every cell from `n` on. -/
theorem readFirstCells_eq_some_iff (read : K → Option E) (fp : K) (offset : Fin 13 → K) (n : ℕ)
    (f : Fin 13 → E) :
    readFirstCells read fp offset n = some f ↔
      (∀ c : Fin 13, c.val < n → read (fp * offset c) = some (f c)) ∧
        ∀ c : Fin 13, n ≤ c.val → f c = 0 := by
  unfold readFirstCells
  rw [readFirstCells_fold_eq_some_iff]
  simp [List.mem_finRange]

/-- **`execute` of a `KECCAK`**: the thirteen cells read and the first `outCells.cellCount` cells
written exist, and the relation holds of them; the successor is the next instruction. A cell past
them is not read. -/
theorem execute_keccak_eq_some_iff {κ : ℕ} (mem : MemoryImage κ) (r : Registers K) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (outCells : KeccakOutputCells)
    (next : Registers K) :
    execute mem r (.keccak om otail ob8 ocap oout inOdd outOdd outCells) = some next ↔
      ∃ input output : Fin 13 → E,
        (∀ c, mem.read (r.fp * keccakInputCellOffset om otail ob8 ocap c) = some (input c)) ∧
        (∀ c : Fin 13, c.val < outCells.cellCount →
          mem.read (r.fp * (g ^ c.val * oout)) = some (output c)) ∧
        KeccakCellsRelation input inOdd output outOdd outCells ∧ next = r.next := by
  simp only [execute, executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨input, hin, output, hout, u, hu, hn⟩
    unfold guard at hu
    split_ifs at hu with hc
    simp only [Option.pure_def, Option.some.injEq] at hn
    exact ⟨input, output, (readCells_eq_some_iff _ _ _ _).mp hin,
      ((readFirstCells_eq_some_iff _ _ _ _ _).mp hout).1, hc, hn.symm⟩
  · rintro ⟨input, output, hin, hout, hc, rfl⟩
    let output' : Fin 13 → E := fun c ↦ if c.val < outCells.cellCount then output c else 0
    have hc' : KeccakCellsRelation input inOdd output' outOdd outCells :=
      fun c h ↦ by simp only [output', h, ↓reduceIte]; exact hc c h
    refine ⟨input, (readCells_eq_some_iff _ _ _ _).mpr hin, output',
      (readFirstCells_eq_some_iff _ _ _ _ _).mpr ⟨fun c h ↦ ?_, fun c h ↦ ?_⟩, (), ?_, rfl⟩
    · simp only [output', h, ↓reduceIte]; exact hout c h
    · simp only [output']; split_ifs <;> first | omega | rfl
    · simp [guard, hc']

end
end LeanVM.Semantics
