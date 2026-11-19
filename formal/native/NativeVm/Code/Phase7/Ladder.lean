module

public import NativeVm.Code.Phase7.Base

/-!
# Phase 7: the WHIR ladder

`ladderC` stores `Whir.ladder μ r` (`LevelsAt`: the level count, then each level's fold, rate
exponent and query count) for `μ` in `rcx`, `r` in `rdx`, at `r14`. The ladder of the admissible
window (`μ ∈ 16..30`, `r ∈ 1..4`) is a literal table (`ladderTable`, row `r - 1`, entry `μ - 16`),
checked against `Whir.ladder` by `decide +kernel` (`ladder_table`); the code picks the row by two
chains of comparisons (`pick`: `r`, then `μ`) and stores its words by `storei` (`storeRow`).
`ladder_ok`: what the opening needs of a ladder (`LadderOk`), checked on the window.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native LeanVM.Parameters NativeVm.Code
open NativeVm.Transcript (wd wd_inj wd_zero wdisp wdisp_toUInt64 eval_at wp_storei
  wp_ite_true wp_ite_false toUInt64_inj isSome_setMem)

/-- What the opening needs of a ladder. `muAfter μ L k`: the variables left after level k's folds. -/
def muAfter (μ : Nat) (L : List Whir.Level) (k : Nat) : Nat := μ - ((L.take (k + 1)).map (·.fold)).sum

/-- What the opening needs of a ladder: two to six levels, level 0 folding `initialFold`, every
level folding `1..6` variables (a later one at most `4` and at most what is left), at most
`residualMaxLog` variables left at the end, rate exponents from `1` with room for the domain, at
most `230` queries. -/
structure LadderOk (μ : Nat) (L : List Whir.Level) : Prop where
  len : 2 ≤ L.length ∧ L.length ≤ 6
  head : ∀ h : 0 < L.length, L[0].fold = Whir.initialFold
  folds : ∀ k (h : k < L.length), 1 ≤ L[k].fold ∧ L[k].fold ≤ 6 ∧ ((L.take (k + 1)).map (·.fold)).sum ≤ μ
  final : muAfter μ L (L.length - 1) ≤ Whir.residualMaxLog
  rates : ∀ k (h : k < L.length), 1 ≤ L[k].logInvRate ∧ muAfter μ L k + L[k].logInvRate < 64 ∧ L[k].queries ≤ 230
  next : ∀ k (h : k + 1 < L.length), L[k + 1].fold ≤ muAfter μ L k ∧ L[k+1].fold ≤ 4

instance (μ : Nat) (L : List Whir.Level) : Decidable (LadderOk μ L) :=
  decidable_of_iff ((2 ≤ L.length ∧ L.length ≤ 6) ∧
      (∀ h : 0 < L.length, L[0].fold = Whir.initialFold) ∧
      (∀ k (h : k < L.length), 1 ≤ L[k].fold ∧ L[k].fold ≤ 6 ∧
        ((L.take (k + 1)).map (·.fold)).sum ≤ μ) ∧
      muAfter μ L (L.length - 1) ≤ Whir.residualMaxLog ∧
      (∀ k (h : k < L.length), 1 ≤ L[k].logInvRate ∧ muAfter μ L k + L[k].logInvRate < 64 ∧
        L[k].queries ≤ 230) ∧
      ∀ k < L.length - 1, ∀ h : k + 1 < L.length, L[k + 1].fold ≤ muAfter μ L k ∧ L[k+1].fold ≤ 4)
    ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun k hk ↦ h.2.2.2.2.2 k (by omega) hk⟩,
      fun h ↦ ⟨h.len, h.head, h.folds, h.final, h.rates, fun k _ h' ↦ h.next k h'⟩⟩

/-! ## The table -/

/-- `Whir.ladder μ r` on the window, as (fold, rate exponent, queries) per level: row `r - 1`,
entry `μ - 16`. -/
def ladderTable : List (List (List (Nat × Nat × Nat))) := [
  [[(6, 1, 230), (4, 4, 60), (4, 7, 42)],
   [(6, 1, 225), (4, 4, 58), (4, 7, 38)],
   [(6, 1, 222), (4, 4, 57), (4, 7, 35)],
   [(6, 1, 220), (4, 4, 56), (4, 7, 34)],
   [(6, 1, 219), (4, 4, 55), (4, 7, 33), (4, 10, 27)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 25)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 24)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 23)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 20)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 19)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 16)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 15)],
   [(6, 1, 218), (4, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 15)]],
  [[(6, 2, 112), (4, 5, 47), (4, 8, 35)],
   [(6, 2, 111), (4, 5, 46), (4, 8, 32)],
   [(6, 2, 110), (4, 5, 45), (4, 8, 31)],
   [(6, 2, 110), (4, 5, 45), (4, 8, 29)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 29), (4, 11, 24)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 23)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 22)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 21)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 21), (4, 14, 18)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 21), (4, 14, 17)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 21), (4, 14, 17)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 21), (4, 14, 17)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 21), (4, 14, 17), (4, 17, 15)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 21), (4, 14, 17), (4, 17, 15)],
   [(6, 2, 109), (4, 5, 44), (4, 8, 28), (4, 11, 21), (4, 14, 17), (4, 17, 15)]],
  [[(6, 3, 74), (4, 6, 39), (4, 9, 30)],
   [(6, 3, 74), (4, 6, 38), (4, 9, 28)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 27)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 26)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 22)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 20)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 20)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 19)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 19), (4, 15, 17)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 19), (4, 15, 16)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 19), (4, 15, 16)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 19), (4, 15, 16)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 19), (4, 15, 16), (4, 18, 15)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 19), (4, 15, 16), (4, 18, 14)],
   [(6, 3, 73), (4, 6, 37), (4, 9, 25), (4, 12, 19), (4, 15, 16), (4, 18, 15)]],
  [[(6, 4, 56), (4, 7, 33), (4, 10, 27)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 25)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 24)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 20)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 19)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 16)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 15)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 15)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 15)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 15), (4, 19, 14)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 16), (4, 19, 14)],
   [(6, 4, 55), (4, 7, 32), (4, 10, 23), (4, 13, 18), (4, 16, 16), (4, 19, 14)]]]

/-- A row's levels. -/
def toLevels (row : List (Nat × Nat × Nat)) : List Whir.Level := row.map fun x ↦ ⟨x.1, x.2.1, x.2.2⟩

/-- The table is `Whir.ladder` on the window. -/
theorem ladder_table : ∀ μ < 31, ∀ r < 5, Whir.Admissible μ r →
    Whir.ladder μ r = some (toLevels ((ladderTable.getD (r - 1) []).getD (μ - 16) [])) := by
  decide +kernel

theorem ladder_ok_table : ∀ μ < 31, ∀ r < 5, Whir.Admissible μ r →
    LadderOk μ (toLevels ((ladderTable.getD (r - 1) []).getD (μ - 16) [])) := by
  decide +kernel

theorem ladderTable_shape : ladderTable.length = 4 ∧ ∀ rows ∈ ladderTable, rows.length = 15 := by
  decide +kernel

theorem Admissible.bounds {μ r : Nat} (h : Whir.Admissible μ r) : 16 ≤ μ ∧ μ ≤ 30 ∧ 1 ≤ r ∧ r ≤ 4 :=
  h

/-- **What the opening needs of a ladder**: it holds on the whole window. -/
theorem ladder_ok {μ r : Nat} (hadm : Whir.Admissible μ r) {L : List Whir.Level}
    (h : Whir.ladder μ r = some L) : LadderOk μ L := by
  have hb := Admissible.bounds hadm
  rw [ladder_table μ (by omega) r (by omega) hadm, Option.some.injEq] at h
  exact h ▸ ladder_ok_table μ (by omega) r (by omega) hadm

/-! ## A row's words -/

/-- (fold, rate, queries) per level, flattened. -/
def triples : List (Nat × Nat × Nat) → List Nat
  | [] => []
  | x :: xs => x.1 :: x.2.1 :: x.2.2 :: triples xs

/-- The words of a row: its level count, then its levels. -/
def rowWords (row : List (Nat × Nat × Nat)) : List Nat := row.length :: triples row

theorem triples_length : ∀ row : List (Nat × Nat × Nat), (triples row).length = 3 * row.length
  | [] => rfl
  | _ :: xs => by rw [triples, List.length_cons, List.length_cons, List.length_cons,
      triples_length xs, List.length_cons]; omega

theorem triples_get : ∀ (row : List (Nat × Nat × Nat)) (k : Nat) (h : k < row.length),
    (triples row)[3 * k]? = some row[k].1 ∧ (triples row)[3 * k + 1]? = some row[k].2.1 ∧
      (triples row)[3 * k + 2]? = some row[k].2.2
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => ⟨rfl, rfl, rfl⟩
  | x :: xs, k + 1, h => by
    have := triples_get xs k (by simpa using h)
    have e : ∀ n, (triples (x :: xs))[n + 3]? = (triples xs)[n]? := fun _ ↦ rfl
    rw [show 3 * (k + 1) = 3 * k + 3 by omega, show 3 * k + 3 + 1 = 3 * k + 1 + 3 by omega,
      show 3 * k + 3 + 2 = 3 * k + 2 + 3 by omega, e, e, e, List.getElem_cons_succ]
    exact this

/-- A row's words at `p` are its levels' `LevelsAt`, for a row of a ladder. -/
theorem levelsAt_of {mem : UInt64 → Option UInt64} {D : UInt64} {μ : Nat}
    {row : List (Nat × Nat × Nat)}
    (hv : ∀ i w, (rowWords row)[i]? = some w → mem (wd D (0 + i)) = some w.toUInt64)
    (hok : LadderOk μ (toLevels row)) : LevelsAt mem D (toLevels row) := by
  have hl : (toLevels row).length = row.length := List.length_map _
  have hlen := hok.len
  refine ⟨⟨by omega, ?_⟩, fun k hk ↦ ?_⟩
  · rw [hl, ← wd_zero D]
    exact hv 0 _ rfl
  · have hk' : k < row.length := hl ▸ hk
    obtain ⟨t0, t1, t2⟩ := triples_get row k hk'
    have e : (toLevels row)[k] = ⟨row[k].1, row[k].2.1, row[k].2.2⟩ := List.getElem_map ..
    have hf := hok.folds k hk
    have hr := hok.rates k hk
    rw [e] at hf hr ⊢
    refine ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩
    · rw [show 1 + 3 * k = 0 + (3 * k + 1) by omega]
      exact hv _ _ t0
    · rw [show 2 + 3 * k = 0 + (3 * k + 1 + 1) by omega]
      exact hv _ _ t1
    · rw [show 3 + 3 * k = 0 + (3 * k + 2 + 1) by omega]
      exact hv _ _ t2

/-! ## The code -/

/-- Store the words `ws` from word `k` at `r14`. -/
def storeRow : List Nat → Nat → List Stmt
  | [], _ => []
  | w :: ws, k => I (.storei (at_ .r14 (wdisp k)) (Int64.ofNat w)) :: storeRow ws (k + 1)

/-- `bs[j]` when `x` holds `i + j`. -/
def pick (x : Reg64) (i : Nat) : List Stmt → Stmt
  | [] => .skip
  | b :: bs => .ite (.cmp .eq x (.imm (Int64.ofNat i))) b (pick x (i + 1) bs)

/-- **The ladder**: `Whir.ladder μ r` at `r14`, `μ` in `rcx`, `r` in `rdx`. -/
def ladderC : Stmt :=
  pick .rdx 1 (ladderTable.map fun rows ↦ pick .rcx 16 (rows.map fun row ↦ blk (storeRow (rowWords row) 0)))

variable {P F : QState → Prop}

theorem pick_spec (x : Reg64) : ∀ (bs : List Stmt) (i j : Nat) (s : QState) (hj : j < bs.length),
    i + bs.length < 2 ^ 64 → s.reg x = (i + j).toUInt64 → WP bs[j] s P F → WP (pick x i bs) s P F
  | [], _, _, _, hj, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | b :: bs, i, 0, s, _, _, hx, h => by
    refine wp_ite_true ?_ h
    show (s.reg x == (Int64.ofNat i).toUInt64) = true
    rw [hx]
    exact beq_self_eq_true _
  | b :: bs, i, j + 1, s, hj, hb, hx, h => by
    simp only [List.length_cons] at hj hb
    refine wp_ite_false ?_ (pick_spec x bs (i + 1) j s (by omega) (by omega) ?_ h)
    · show (s.reg x == (Int64.ofNat i).toUInt64) = false
      rw [hx, beq_eq_false_iff_ne]
      show (i + (j + 1)).toUInt64 ≠ i.toUInt64
      rw [Ne, toUInt64_inj (by omega) (by omega)]
      omega
    · rw [hx, Nat.add_right_comm, Nat.add_assoc]

theorem storeRow_spec {D : UInt64} : ∀ (ws : List Nat) (k : Nat) (s : QState),
    s.reg .r14 = D → (∀ i < ws.length, (s.mem (wd D (k + i))).isSome) → k + ws.length < 2 ^ 61 →
    WP (blk (storeRow ws k)) s (fun s' ↦ (∀ i w, ws[i]? = some w → s'.mem (wd D (k + i)) = some w.toUInt64) ∧
      ∀ a, (∀ i < ws.length, a ≠ wd D (k + i)) → s'.mem a = s.mem a) F
  | [], _, _, _, _, _ => WP.blk_nil ⟨fun _ _ h ↦ by simp at h, fun _ _ ↦ rfl⟩
  | w :: ws, k, s, h14, hD, hk => by
    simp only [List.length_cons] at hD hk
    refine wp_storei (x := wd D k) (by rw [eval_at, h14, wdisp_toUInt64]; rfl)
      (by simpa using hD 0 (by omega)) ?_
    refine WP.mono (storeRow_spec ws (k + 1) _ h14 (fun i hi ↦ ?_) (by omega)) ?_ (fun _ h ↦ h)
    · rw [isSome_setMem _ _ (by simpa using hD 0 (by omega)), Nat.add_assoc]
      exact hD (1 + i) (by omega)
    · rintro s' ⟨hv, hf⟩
      have hne : ∀ i < ws.length, wd D k ≠ wd D (k + 1 + i) := fun i hi e ↦ by
        rw [wd_inj (by omega) (by omega)] at e
        omega
      refine ⟨fun i v hi ↦ ?_, fun a ha ↦ ?_⟩
      · cases i with
        | zero =>
          obtain rfl : w = v := by simpa using hi
          rw [Nat.add_zero, hf _ hne, QState.setMem_mem]
          split
          · rfl
          · exact absurd rfl ‹_›
        | succ i =>
          rw [List.getElem?_cons_succ] at hi
          rw [show k + (i + 1) = k + 1 + i by omega]
          exact hv i v hi
      · have h0 : a ≠ wd D k := by simpa using ha 0 (by simp)
        rw [hf a (fun i hi ↦ by rw [Nat.add_assoc]; exact ha (1 + i) (by simp; omega)),
          QState.setMem_mem]
        split
        · exact absurd ‹_› h0
        · rfl

theorem ladderC_spec {s : QState} {F : QState → Prop} {μ r : Nat} {D : UInt64}
    (hadm : Whir.Admissible μ r)
    (hcx : s.reg .rcx = μ.toUInt64) (hdx : s.reg .rdx = r.toUInt64) (h14 : s.reg .r14 = D)
    (hD : ∀ k < levelsWords, (s.mem (wd D k)).isSome) :
    WP ladderC s (fun s' ↦ ∃ L, Whir.ladder μ r = some L ∧ LevelsAt s'.mem D L ∧
      ∀ a, (∀ k < levelsWords, a ≠ wd D k) → s'.mem a = s.mem a) F := by
  have hb := Admissible.bounds hadm
  have hrow := ladder_table μ (by omega) r (by omega) hadm
  have hok := ladder_ok hadm hrow
  obtain ⟨h4, h15⟩ := ladderTable_shape
  have hr : r - 1 < ladderTable.length := by omega
  have hm : μ - 16 < ladderTable[r - 1].length := by
    rw [h15 _ (List.getElem_mem hr)]
    omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some,
    List.getElem?_eq_getElem hm] at hrow hok
  refine pick_spec .rdx _ 1 (r - 1) s (by simpa using hr) (by simp; omega)
    (by rw [hdx]; congr 1; omega) ?_
  rw [List.getElem_map]
  refine pick_spec .rcx _ 16 (μ - 16) s (by simpa using hm) (by simp [h15 _ (List.getElem_mem hr)])
    (by rw [hcx]; congr 1; omega) ?_
  rw [List.getElem_map]
  generalize ladderTable[r - 1][μ - 16] = row at hrow hok ⊢
  have hw : levelsWords = 19 := rfl
  have hlen : (rowWords row).length ≤ 19 := by
    have := hok.len
    rw [toLevels, List.length_map] at this
    rw [rowWords, List.length_cons, triples_length]
    omega
  refine WP.mono (storeRow_spec (rowWords row) 0 s h14 (fun i hi ↦ by simpa using hD i (by omega))
    (by omega)) ?_ (fun _ h ↦ h)
  rintro s' ⟨hv, hf⟩
  exact ⟨_, hrow, levelsAt_of hv hok,
    fun a ha ↦ hf a fun i hi ↦ by rw [Nat.zero_add]; exact ha i (by omega)⟩

end NativeVm.Code.P7
