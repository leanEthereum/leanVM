/-
  LeanVM.Guest.B1.Eq.RsRows

  B1 for `rs_eq_rows__L{n}`, `n ≤ 8`: one row of the telescoped ring-switch product.
-/

module

public import LeanVM.Guest.B1.Eq.Meaning

/-!
# `rs_eq_rows` (lean_ethereum.py:1030-1049 at leanVM `40f877dc`)

`rs_eq_rows(row, zs, ps, n)` at `n = 0` returns `row`. Otherwise it reads the `n` coordinates
`zs[i]`, `ps[i]` (`rrHead`), and for each `k < 64` the row word `row[k]`, multiplies it by
`zs[i]^(2^k) + ps[i]` for `i < n` (the Frobenius powers squared along `k`, values `rrZ`), and
stores the product at `row·g^(64 + k)` (`rrRow k`); it returns `row·g^64` (`g^64` the word
`27`). Row `k`'s values start at `rrS n k`, three a coordinate (two in the last row, which
squares nothing). `rrBody n` is equal to each specialization by kernel evaluation.

`rs_eq_rows_holds`: the core IR is `MeaningRsEqRows`; the converse builds the valuation from the
list of honest values `rrVals`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Lists -/

theorem noRetList_append' (a b : List Stmt) :
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b) := by
  induction a with
  | nil => simp [Stmt.noRetList]
  | cons s a ih => simp [Stmt.noRetList, ih, Bool.and_assoc]

theorem noRetList_flatten_range (n : ℕ) (f : ℕ → List Stmt) (h : ∀ i, Stmt.noRetList (f i) = true) :
    Stmt.noRetList ((List.range n).map f).flatten = true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.flatten_append, noRetList_append', ih]; simp [h]

/-- A word of a run of lists, all of one length before the `k`-th. -/
theorem getD_flatMap_range {α : Type} (len : ℕ) (d : α) :
    ∀ (k : ℕ) (f : ℕ → List α) (m o : ℕ), k < m → (∀ i < k, (f i).length = len) →
      o < (f k).length → ((List.range m).flatMap f).getD (k * len + o) d = (f k).getD o d := by
  intro k
  induction k with
  | zero =>
    intro f m o hm _ ho
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, Nat.zero_mul, Nat.zero_add,
      List.getD_append _ _ _ _ ho]
  | succ k ih =>
    intro f m o hm hf ho
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.getD_append_right _ _ _ _ (by rw [hf 0 (by omega)]; rw [Nat.succ_mul]; omega),
      hf 0 (by omega), show (k + 1) * len + o - len = k * len + o by rw [Nat.succ_mul]; omega]
    exact ih (fun i ↦ f (i + 1)) m o (by omega) (fun i hi ↦ hf (i + 1) (by omega)) ho

theorem length_flatMap_range {α : Type} (len : ℕ) (f : ℕ → List α) :
    ∀ m, (∀ i < m, (f i).length = len) → ((List.range m).flatMap f).length = m * len
  | 0, _ => by simp
  | m + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      length_flatMap_range len f m (fun i hi ↦ h i (by omega)), List.flatMap_singleton, h m (by omega),
      Nat.succ_mul]

/-! ## The template -/

/-- Row `k`'s first value: its word. -/
def rrS (n k : ℕ) : ℕ := 3 + 2 * n + k * (1 + 3 * n)

/-- Values a coordinate in row `k`: the factor, the product, the next power (none in the last). -/
def rrStride (k : ℕ) : ℕ := if k < 63 then 3 else 2

/-- `zs[i]^(2^k)`'s value. -/
def rrZ (n : ℕ) : ℕ → ℕ → ℕ
  | 0, i => 3 + 2 * i
  | k + 1, i => rrS n k + 3 + 3 * i

/-- Row `k`'s product after `i` coordinates. -/
def rrAcc (n k : ℕ) : ℕ → ℕ
  | 0 => rrS n k
  | i + 1 => rrS n k + 2 + rrStride k * i

/-- Coordinate `i` of row `k`. -/
def rrCoord (n k i : ℕ) : List Stmt :=
  [.atom (.add (.n (rrS n k + 1 + rrStride k * i)) (.n (rrZ n k i)) (.n (4 + 2 * i))),
    .atom (.mul (.n (rrS n k + 2 + rrStride k * i)) (.n (rrAcc n k i))
      (.n (rrS n k + 1 + rrStride k * i)))] ++
  (if k < 63 then [.atom (.mul (.n (rrS n k + 3 + 3 * i)) (.n (rrZ n k i)) (.n (rrZ n k i)))]
    else [])

/-- Row `k`: its word, the coordinates, the product stored. -/
def rrRow (n k : ℕ) : List Stmt :=
  [.atom (.load (.n (rrS n k)) (.n 0) k)] ++ ((List.range n).map (rrCoord n k)).flatten ++
    [.atom (.load (.n (rrAcc n k n)) (.n 0) (64 + k))]

/-- The coordinates' reads. -/
def rrHeadBlk (i : ℕ) : List Stmt :=
  [.atom (.load (.n (3 + 2 * i)) (.n 1) i), .atom (.load (.n (4 + 2 * i)) (.n 2) i)]

/-- The return's first value. -/
def rrT (n : ℕ) : ℕ := rrS n 63 + 1 + 2 * n

/-- The expansion of `rs_eq_rows__L{n}`, `n ≥ 1`. -/
def rrBody (n : ℕ) : List Stmt :=
  ((List.range n).map rrHeadBlk).flatten ++ ((List.range 64).map (rrRow n)).flatten ++
    [.atom (.const (.n (rrT n)) (word 27 0 0)), .atom (.mul (.n (rrT n + 1)) (.n 0) (.n (rrT n))),
      .atom (.copy (.n (rrT n + 2)) (.n (rrT n + 1))), .ret [.n (rrT n + 2)]]

theorem core81_body : Fn.body Data.core81 = [.atom (.copy (.n 3) (.n 0)), .ret [.n 3]] :=
  stmtsEqb_sound (by decide +kernel)
theorem core82_body : Fn.body Data.core82 = rrBody 1 := stmtsEqb_sound (by decide +kernel)
theorem core83_body : Fn.body Data.core83 = rrBody 2 := stmtsEqb_sound (by decide +kernel)
theorem core84_body : Fn.body Data.core84 = rrBody 3 := stmtsEqb_sound (by decide +kernel)
theorem core85_body : Fn.body Data.core85 = rrBody 4 := stmtsEqb_sound (by decide +kernel)
theorem core86_body : Fn.body Data.core86 = rrBody 5 := stmtsEqb_sound (by decide +kernel)
theorem core87_body : Fn.body Data.core87 = rrBody 6 := stmtsEqb_sound (by decide +kernel)
theorem core88_body : Fn.body Data.core88 = rrBody 7 := stmtsEqb_sound (by decide +kernel)
theorem core418_body : Fn.body Data.core411 = rrBody 8 := stmtsEqb_sound (by decide +kernel)

/-! ## The conditions -/

/-- Coordinate `i` of row `k`'s conditions. -/
def RrCoordOk (σ : Val) (n k i : ℕ) : Prop :=
  σ (.n (rrS n k + 1 + rrStride k * i)) = σ (.n (rrZ n k i)) + σ (.n (4 + 2 * i)) ∧
    σ (.n (rrS n k + 2 + rrStride k * i)) =
      σ (.n (rrAcc n k i)) * σ (.n (rrS n k + 1 + rrStride k * i)) ∧
    (k < 63 → σ (.n (rrS n k + 3 + 3 * i)) = σ (.n (rrZ n k i)) * σ (.n (rrZ n k i)))

theorem rrCoord_noRet (n k i : ℕ) : Stmt.noRetList (rrCoord n k i) = true := by
  unfold rrCoord; split <;> rfl

theorem holds_rrCoord {C : CallRel} {rd : Reader} {σ : Val} (n k i : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (rrCoord n k i) True kret ↔ RrCoordOk σ n k i := by
  unfold rrCoord RrCoordOk
  split <;> simp_all [Stmt.HoldsList, Stmt.Holds, Atom.Holds]

/-- Row `k`'s conditions. -/
def RrRowOk (rd : Reader) (σ : Val) (n k : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) k (σ (.n (rrS n k))) ∧ (∀ i < n, RrCoordOk σ n k i) ∧
    LoadHolds rd (σ (.n 0)) (64 + k) (σ (.n (rrAcc n k n)))

theorem rrRow_noRet (n k : ℕ) : Stmt.noRetList (rrRow n k) = true := by
  rw [rrRow, noRetList_append', noRetList_append', noRetList_flatten_range _ _ (rrCoord_noRet n k)]
  rfl

theorem holds_rrRow {C : CallRel} {rd : Reader} {σ : Val} (n k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (rrRow n k) True kret ↔ RrRowOk rd σ n k := by
  rw [rrRow, holdsList_append, holdsList_append,
    holdsList_range_flatten n (rrCoord n k) (rrCoord_noRet n k)]
  simp only [holds_rrCoord, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, RrRowOk]

theorem holds_rrHeadBlk {C : CallRel} {rd : Reader} {σ : Val} (i : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (rrHeadBlk i) True kret ↔
      LoadHolds rd (σ (.n 1)) i (σ (.n (3 + 2 * i))) ∧
        LoadHolds rd (σ (.n 2)) i (σ (.n (4 + 2 * i))) := by
  simp only [rrHeadBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The body of `rs_eq_rows__L{n}`, unfolded to its conditions. -/
theorem rr_unfold {name : String} {f : Fn} (n : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = rrBody n) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2)] = args ∧
      (∀ i < n, LoadHolds rd (σ (.n 1)) i (σ (.n (3 + 2 * i))) ∧
        LoadHolds rd (σ (.n 2)) i (σ (.n (4 + 2 * i)))) ∧
      (∀ k < 64, RrRowOk rd σ n k) ∧ σ (.n (rrT n)) = word 27 0 0 ∧
      σ (.n (rrT n + 1)) = σ (.n 0) * σ (.n (rrT n)) ∧
      σ (.n (rrT n + 2)) = σ (.n (rrT n + 1)) ∧ [σ (.n (rrT n + 2))] = rets := by
  rw [rel_iff_sem hfind, hbody, hparams, rrBody]
  simp only [holdsList_append, holdsList_range_flatten n rrHeadBlk (fun _ ↦ rfl),
    holdsList_range_flatten 64 (rrRow n) (rrRow_noRet n), holds_rrHeadBlk, holds_rrRow,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]

/-! ## Soundness -/

theorem ringRow_take_succ (c : E) (zs ps : List E) (k i : ℕ) (hz : i < zs.length)
    (hp : i < ps.length) :
    ringRow c (zs.take (i + 1)) (ps.take (i + 1)) k =
      ringRow c (zs.take i) (ps.take i) k * (zs[i] ^ 2 ^ k + ps[i]) := by
  rw [ringRow, ringRow, List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hz,
    List.getElem?_eq_getElem hp]
  simp only [Option.toList_some]
  rw [List.zipWith_append (by simp; omega), List.foldl_append]
  rfl

theorem ringRow_nil (c : E) (zs ps : List E) (k : ℕ) : ringRow c (zs.take 0) (ps.take 0) k = c := by
  simp [ringRow]

theorem rrZ_pow {rd : Reader} {σ : Val} {n : ℕ} (h : ∀ k < 64, RrRowOk rd σ n k) :
    ∀ k < 64, ∀ i < n, σ (.n (rrZ n k i)) = σ (.n (3 + 2 * i)) ^ 2 ^ k
  | 0, _, i, _ => by simp [rrZ]
  | k + 1, hk, i, hi => by
    rw [rrZ, ((h k (by omega)).2.1 i hi).2.2 (by omega), rrZ_pow h k (by omega) i hi, ← pow_add,
      ← two_mul, ← pow_succ']

theorem rrAcc_eq {rd : Reader} {σ : Val} {n : ℕ} (h : ∀ k < 64, RrRowOk rd σ n k) (k : ℕ)
    (hk : k < 64) :
    ∀ i ≤ n, σ (.n (rrAcc n k i)) = ringRow (σ (.n (rrS n k)))
      (((List.range n).map fun i ↦ σ (.n (3 + 2 * i))).take i)
      (((List.range n).map fun i ↦ σ (.n (4 + 2 * i))).take i) k
  | 0, _ => by rw [ringRow_nil]; rfl
  | i + 1, hi => by
    obtain ⟨e1, e2, -⟩ := (h k hk).2.1 i (by omega)
    rw [ringRow_take_succ _ _ _ _ _ (by simp; omega) (by simp; omega), ← rrAcc_eq h k hk i (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [show rrAcc n k (i + 1) = rrS n k + 2 + rrStride k * i from rfl, e2, e1,
      rrZ_pow h k hk i (by omega)]

/-! ## The honest values -/

/-- Coordinate `i` of row `k`: the factor, the product, the next power (not in the last row). -/
def rrCoordVals (zs ps : List E) (c : E) (k i : ℕ) : List E :=
  [zs.getD i 0 ^ 2 ^ k + ps.getD i 0, ringRow c (zs.take (i + 1)) (ps.take (i + 1)) k] ++
    (if k < 63 then [zs.getD i 0 ^ 2 ^ (k + 1)] else [])

theorem length_rrCoordVals (zs ps : List E) (c : E) (k i : ℕ) :
    (rrCoordVals zs ps c k i).length = rrStride k := by
  unfold rrCoordVals rrStride; split <;> rfl

/-- Row `k`: its word, then its coordinates. -/
def rrRowVals (n : ℕ) (zs ps c : List E) (k : ℕ) : List E :=
  c.getD k 0 :: (List.range n).flatMap (rrCoordVals zs ps (c.getD k 0) k)

theorem length_rrRowVals (n : ℕ) (zs ps c : List E) (k : ℕ) :
    (rrRowVals n zs ps c k).length = 1 + n * rrStride k := by
  rw [rrRowVals, List.length_cons, length_flatMap_range (rrStride k) _ n
    (fun i _ ↦ length_rrCoordVals zs ps _ k i)]
  omega

/-- The honest values of `rs_eq_rows__L{n}`. -/
def rrVals (n : ℕ) (row z p : E) (zs ps c : List E) : List E :=
  [row, z, p] ++ (List.range n).flatMap (fun i ↦ [zs.getD i 0, ps.getD i 0]) ++
    (List.range 64).flatMap (rrRowVals n zs ps c) ++
    [word 27 0 0, row * word 27 0 0, row * word 27 0 0]

theorem length_rrHeadVals (n : ℕ) (zs ps : List E) :
    ((List.range n).flatMap (fun i ↦ [zs.getD i 0, ps.getD i 0])).length = n * 2 :=
  length_flatMap_range 2 _ n (fun _ _ ↦ rfl)

theorem length_rrRowsVals (n : ℕ) (zs ps c : List E) :
    ((List.range 64).flatMap (rrRowVals n zs ps c)).length = 63 * (1 + 3 * n) + (1 + 2 * n) := by
  rw [List.range_succ, List.flatMap_append, List.length_append,
    length_flatMap_range (1 + 3 * n) _ 63 (fun i hi ↦ by
      rw [length_rrRowVals, rrStride, ite_pos' hi, Nat.mul_comm]),
    List.flatMap_singleton, length_rrRowVals, rrStride, ite_neg' (by omega)]
  omega

section vals
variable (n : ℕ) (row z p : E) (zs ps c : List E)

theorem length_rrPre :
    ([row, z, p] ++ (List.range n).flatMap (fun i ↦ [zs.getD i 0, ps.getD i 0])).length =
      3 + 2 * n := by
  rw [List.length_append, length_rrHeadVals]; simp; omega

theorem length_rrPreRows :
    ([row, z, p] ++ (List.range n).flatMap (fun i ↦ [zs.getD i 0, ps.getD i 0]) ++
      (List.range 64).flatMap (rrRowVals n zs ps c)).length = rrT n := by
  rw [List.length_append, length_rrPre, length_rrRowsVals, rrT, rrS]; omega

theorem rrVals_head (i : ℕ) (hi : i < n) :
    (rrVals n row z p zs ps c).getD (3 + 2 * i) 0 = zs.getD i 0 ∧
      (rrVals n row z p zs ps c).getD (4 + 2 * i) 0 = ps.getD i 0 := by
  have hA := length_rrPre n row z p zs ps
  have hB := length_rrPreRows n row z p zs ps c
  have hT : 3 + 2 * n ≤ rrT n := by unfold rrT rrS; omega
  have g := fun o (ho : o < 2) ↦ getD_flatMap_range 2 (0 : E) i
    (fun i ↦ [zs.getD i 0, ps.getD i 0]) n o hi (fun _ _ ↦ rfl) (by simpa using ho)
  unfold rrVals
  constructor
  · rw [List.getD_append _ _ _ _ (by rw [hB]; omega), List.getD_append _ _ _ _ (by rw [hA]; omega),
      List.getD_append_right _ _ _ _ (by simp),
      show 3 + 2 * i - [row, z, p].length = i * 2 + 0 by simp; omega, g 0 (by omega)]
    rfl
  · rw [List.getD_append _ _ _ _ (by rw [hB]; omega), List.getD_append _ _ _ _ (by rw [hA]; omega),
      List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega),
      show 4 + 2 * i - [row, z, p].length = i * 2 + 1 by simp; omega, g 1 (by omega)]
    rfl

theorem rrVals_row (k o : ℕ) (hk : k < 64) (ho : o < 1 + n * rrStride k) :
    (rrVals n row z p zs ps c).getD (rrS n k + o) 0 = (rrRowVals n zs ps c k).getD o 0 := by
  have hA := length_rrPre n row z p zs ps
  have hB := length_rrPreRows n row z p zs ps c
  have hk' : k * (1 + 3 * n) + o < 63 * (1 + 3 * n) + (1 + 2 * n) := by
    rcases Nat.lt_or_ge k 63 with h | h
    · have : rrStride k = 3 := by simp [rrStride, h]
      rw [this] at ho
      have := Nat.mul_le_mul_right (1 + 3 * n) (show k + 1 ≤ 63 by omega)
      rw [Nat.succ_mul] at this
      omega
    · have : rrStride k = 2 := by simp [rrStride]; omega
      rw [this] at ho
      obtain rfl : k = 63 := by omega
      omega
  have hlt : rrS n k + o < rrT n := by unfold rrT rrS; omega
  have hge : 3 + 2 * n ≤ rrS n k + o := by unfold rrS; omega
  unfold rrVals
  rw [List.getD_append _ _ _ _ (by rw [hB]; exact hlt), List.getD_append_right _ _ _ _ (by
    rw [hA]; exact hge), hA, show rrS n k + o - (3 + 2 * n) = k * (1 + 3 * n) + o by
      unfold rrS; omega]
  exact getD_flatMap_range (1 + 3 * n) 0 k _ 64 o hk (fun i hi ↦ by
    rw [length_rrRowVals, rrStride, ite_pos' (by omega), Nat.mul_comm]) (by
      rw [length_rrRowVals]; exact ho)

theorem rrRowVals_coord (k i s : ℕ) (hi : i < n) (hs : s < rrStride k) :
    (rrRowVals n zs ps c k).getD (1 + rrStride k * i + s) 0 =
      (rrCoordVals zs ps (c.getD k 0) k i).getD s 0 := by
  rw [rrRowVals, show 1 + rrStride k * i + s = (i * rrStride k + s) + 1 by ring,
    List.getD_cons_succ]
  exact getD_flatMap_range (rrStride k) 0 i _ n s hi
    (fun j _ ↦ length_rrCoordVals zs ps _ k j) (by rw [length_rrCoordVals]; exact hs)

theorem rrVals_tail (t : ℕ) (ht : t < 3) :
    (rrVals n row z p zs ps c).getD (rrT n + t) 0 =
      [word 27 0 0, row * word 27 0 0, row * word 27 0 0].getD t 0 := by
  have hB := length_rrPreRows n row z p zs ps c
  unfold rrVals
  rw [List.getD_append_right _ _ _ _ (by rw [hB]; omega), hB, Nat.add_sub_cancel_left]

end vals

/-! ## The theorem -/

/-- The two halves of `ReadsAt` on a list of `n` words by index. -/
theorem readsAt_range {rd : Reader} {p : E} {n : ℕ} {f : ℕ → E}
    (h : ∀ i < n, LoadHolds rd p i (f i)) : ReadsAt rd p ((List.range n).map f) := fun i hi ↦ by
  simp only [List.length_map, List.length_range] at hi
  simpa using h i hi

theorem readsAt_getD {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {i : ℕ}
    (hi : i < xs.length) : LoadHolds rd p i (xs.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h i hi

theorem ringRow_take_length (c : E) (zs ps : List E) (k : ℕ) (n : ℕ) (hz : zs.length = n)
    (hp : ps.length = n) : ringRow c (zs.take n) (ps.take n) k = ringRow c zs ps k := by
  rw [← hz, List.take_length, show zs.length = ps.length by omega, List.take_length]

theorem rr_iff {name : String} {f : Fn} (n : ℕ) (hn : 0 < n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = rrBody n) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningRsEqRows n rd args rets := by
  rw [rr_unfold n hfind hparams hbody]
  have hk27 : K.ofBits 27 = K.ofBits 2 ^ 64 := by decide +kernel
  have w27 : word 27 0 0 = gen ^ 64 := by
    rw [word_eOfNat, show gen = ofK (K.ofBits 2) from rfl, ← ofK_pow, ← hk27]
    rfl
  constructor
  · rintro ⟨σ, hp, hh, hr, hT, hT1, hT2, hret⟩
    subst hp hret
    right
    refine ⟨hn, (List.range n).map (fun i ↦ σ (.n (3 + 2 * i))),
      (List.range n).map (fun i ↦ σ (.n (4 + 2 * i))), (List.range 64).map (fun k ↦ σ (.n (rrS n k))),
      by simp, by simp, by simp, readsAt_range fun i hi ↦ (hh i hi).1,
      readsAt_range fun i hi ↦ (hh i hi).2, readsAt_range fun k hk ↦ (hr k hk).1, fun k hk ↦ ?_, ?_⟩
    · have := (hr k hk).2.2
      rw [rrAcc_eq hr k hk n le_rfl, ringRow_take_length _ _ _ _ n (by simp) (by simp)] at this
      convert this using 2
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
      rfl
    · rw [hT2, hT1, hT, w27]
  · intro hm
    obtain ⟨row, z, p, rfl⟩ : ∃ row z p, args = [row, z, p] := by
      match args, hm with
      | [row, z, p], _ => exact ⟨row, z, p, rfl⟩
    rcases hm with ⟨h0, -⟩ | ⟨-, zs, ps, c, hz, hpl, hc, rz, rp, rc, hrow, rfl⟩
    · omega
    -- the honest valuation
    let σ : Val := fun v ↦ (rrVals n row z p zs ps c).getD v.idx 0
    have ev : ∀ j, σ (.n j) = (rrVals n row z p zs ps c).getD j 0 := fun _ ↦ rfl
    have eh := rrVals_head n row z p zs ps c
    have er : ∀ k o, k < 64 → o < 1 + n * rrStride k →
        σ (.n (rrS n k + o)) = (rrRowVals n zs ps c k).getD o 0 :=
      fun k o hk ho ↦ (ev _).trans (rrVals_row n row z p zs ps c k o hk ho)
    have hst : ∀ k, 2 ≤ rrStride k := fun k ↦ by unfold rrStride; split <;> omega
    -- values of a coordinate
    have ec : ∀ k i s, k < 64 → i < n → s < rrStride k →
        σ (.n (rrS n k + (1 + rrStride k * i + s))) =
          (rrCoordVals zs ps (c.getD k 0) k i).getD s 0 := fun k i s hk hi hs ↦ by
      have h1 : rrStride k * (i + 1) ≤ rrStride k * n := Nat.mul_le_mul_left _ hi
      rw [Nat.mul_succ] at h1
      rw [er k _ hk (by rw [Nat.mul_comm n]; omega),
        rrRowVals_coord n zs ps c k i s hi hs]
    have ez : ∀ k < 64, ∀ i < n, σ (.n (rrZ n k i)) = zs.getD i 0 ^ 2 ^ k := by
      intro k hk i hi
      cases k with
      | zero => rw [rrZ, ev, (eh i hi).1, pow_zero, pow_one]
      | succ k =>
        have h63 : k < 63 := by omega
        rw [rrZ, show rrS n k + 3 + 3 * i = rrS n k + (1 + rrStride k * i + 2) by
          simp [rrStride, h63]; omega, ec k i 2 (by omega) hi (by simp [rrStride, h63])]
        simp [rrCoordVals, h63]
    have ea : ∀ k < 64, ∀ i ≤ n, σ (.n (rrAcc n k i)) =
        ringRow (c.getD k 0) (zs.take i) (ps.take i) k := by
      intro k hk i hi
      cases i with
      | zero =>
        rw [rrAcc, ringRow_nil, show rrS n k = rrS n k + 0 from rfl, er k 0 hk (by omega)]
        rfl
      | succ i =>
        rw [rrAcc, show rrS n k + 2 + rrStride k * i = rrS n k + (1 + rrStride k * i + 1) by ring,
          ec k i 1 hk (by omega) (by have := hst k; omega)]
        rfl
    have e0 : σ (.n 0) = row := rfl
    refine ⟨σ, rfl, fun i hi ↦ ⟨?_, ?_⟩, fun k hk ↦ ⟨?_, fun i hi ↦ ⟨?_, ?_, fun h63 ↦ ?_⟩, ?_⟩,
      ?_, ?_, ?_, ?_⟩
    · rw [ev (3 + 2 * i), (eh i hi).1]; exact readsAt_getD rz (by omega)
    · rw [ev (4 + 2 * i), (eh i hi).2]; exact readsAt_getD rp (by omega)
    · rw [show rrS n k = rrS n k + 0 from rfl, er k 0 hk (by omega)]
      exact readsAt_getD rc (by omega)
    · rw [show rrS n k + 1 + rrStride k * i = rrS n k + (1 + rrStride k * i + 0) by ring,
        ec k i 0 hk hi (by have := hst k; omega), ez k hk i hi, ev, (eh i hi).2]
      rfl
    · rw [show rrS n k + 2 + rrStride k * i = rrS n k + (1 + rrStride k * i + 1) by ring,
        show rrS n k + 1 + rrStride k * i = rrS n k + (1 + rrStride k * i + 0) by ring,
        ec k i 1 hk hi (by have := hst k; omega), ec k i 0 hk hi (by have := hst k; omega),
        ea k hk i (by omega)]
      simp only [rrCoordVals, List.getD_cons_succ, List.getD_cons_zero, List.cons_append]
      rw [ringRow_take_succ _ _ _ _ _ (show i < zs.length by omega) (show i < ps.length by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < zs.length by omega),
        List.getElem?_eq_getElem (show i < ps.length by omega), Option.getD_some]
    · rw [show rrS n k + 3 + 3 * i = rrS n k + (1 + rrStride k * i + 2) by
          simp [rrStride, h63]; omega, ec k i 2 hk hi (by simp [rrStride, h63]), ez k hk i hi]
      simp only [rrCoordVals, ite_pos' h63, List.cons_append, List.getD_cons_succ,
        List.getD_cons_zero, List.nil_append]
      rw [← pow_add, ← two_mul, ← pow_succ']
    · rw [ea k hk n le_rfl, ringRow_take_length _ _ _ _ n hz hpl, e0]
      exact hrow k hk
    · rw [ev, show rrT n = rrT n + 0 from rfl, rrVals_tail n row z p zs ps c 0 (by omega)]; rfl
    · rw [ev (rrT n + 1), rrVals_tail n row z p zs ps c 1 (by omega),
        show rrT n = rrT n + 0 from rfl, ev (rrT n + 0), rrVals_tail n row z p zs ps c 0 (by omega)]
      rfl
    · rw [ev (rrT n + 2), ev (rrT n + 1), rrVals_tail n row z p zs ps c 2 (by omega),
        rrVals_tail n row z p zs ps c 1 (by omega)]
      rfl
    · rw [ev, rrVals_tail n row z p zs ps c 2 (by omega), w27]; rfl

theorem rr0_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "rs_eq_rows__L0" args rets ↔ MeaningRsEqRows 0 rd args rets := by
  rw [rel_iff_sem (Program.find?_of_indexOf? (j := 81) (by decide +kernel) rfl), core81_body,
    show Fn.params Data.core81 = [.n 0, .n 1, .n 2] from rfl]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, h3, hret⟩
    subst hp hret
    exact Or.inl ⟨rfl, by rw [h3]⟩
  · intro hm
    obtain ⟨row, z, p, rfl, rfl⟩ : ∃ row z p, args = [row, z, p] ∧ rets = [row] := by
      match args, hm with
      | [row, z, p], Or.inl ⟨_, h⟩ => exact ⟨row, z, p, rfl, h⟩
      | [_, _, _], Or.inr ⟨h, _⟩ => omega
    exact ⟨setl (Val.ofArgs [row, z, p]) 3 [row], rfl, by b1_look, by b1_look⟩

set_option maxRecDepth 100000 in
/-- **`rs_eq_rows__L{n}`'s core IR is its meaning**, `n ≤ 8`. -/
theorem rs_eq_rows_holds : rs_eq_rows_Spec := by
  intro n hn rd args rets
  interval_cases n
  · exact rr0_iff rd args rets
  · exact rr_iff 1 (by decide) (Program.find?_of_indexOf? (j := 82) (by decide +kernel) rfl) rfl
      core82_body rd args rets
  · exact rr_iff 2 (by decide) (Program.find?_of_indexOf? (j := 83) (by decide +kernel) rfl) rfl
      core83_body rd args rets
  · exact rr_iff 3 (by decide) (Program.find?_of_indexOf? (j := 84) (by decide +kernel) rfl) rfl
      core84_body rd args rets
  · exact rr_iff 4 (by decide) (Program.find?_of_indexOf? (j := 85) (by decide +kernel) rfl) rfl
      core85_body rd args rets
  · exact rr_iff 5 (by decide) (Program.find?_of_indexOf? (j := 86) (by decide +kernel) rfl) rfl
      core86_body rd args rets
  · exact rr_iff 6 (by decide) (Program.find?_of_indexOf? (j := 87) (by decide +kernel) rfl) rfl
      core87_body rd args rets
  · exact rr_iff 7 (by decide) (Program.find?_of_indexOf? (j := 88) (by decide +kernel) rfl) rfl
      core88_body rd args rets
  · exact rr_iff 8 (by decide) (Program.find?_of_indexOf? (j := 411) (by decide +kernel) rfl) rfl
      core418_body rd args rets

end
end LeanVM.Guest.B1
