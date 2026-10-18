/-
  LeanVM.Guest.B1.Main.AggLoop99

  `__loop99` (G:3434-3480), one child's matrix weights, read forward.
-/

module

public import LeanVM.Guest.B1.Main.AggSteps
public import LeanVM.Guest.B1.Main.Consts

/-!
# The matrix weights

Iteration `c` of `__loop99` reads the child's fresh claims and carried claim through the rows'
pointers, and accumulates into `w_sums` the weights `U` (`guestU`) of its fresh claim and the eq
product of its carried point with the batched matrix point. `U` is the guest's: the 64 Lagrange
numerators at the skip challenge (`lagNum`, prefix and suffix products over the nodes `phiE`)
against the row `eqtree`, scaled by `LAGRANGE_INV_S`, times the row eq factors, times the slices
against the column `eqtree` times the column eq factors.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## Chains -/

theorem prod_chain {P f : ℕ → E} {n : ℕ} (h0 : P 0 = 1) (hs : ∀ k < n, P (k + 1) = P k * f k) :
    ∀ k ≤ n, P k = ∏ j ∈ Finset.range k, f j := by
  intro k hk
  induction k with
  | zero => simpa using h0
  | succ k ih => rw [hs k (by omega), ih (by omega), Finset.prod_range_succ]

theorem sum_chain {S t : ℕ → E} {n : ℕ} (h0 : S 0 = t 0) (hs : ∀ k, k + 1 < n → S (k + 1) = S k + t (k + 1)) :
    ∀ k < n, S k = ∑ j ∈ Finset.range (k + 1), t j := by
  intro k hk
  induction k with
  | zero => simpa using h0
  | succ k ih => rw [hs k hk, ih (by omega), Finset.sum_range_succ (n := k + 1)]

theorem prod_chain' {P f : ℕ → E} {n : ℕ} {a : E} (h0 : P 0 = a * f 0)
    (hs : ∀ k, k + 1 < n → P (k + 1) = P k * f (k + 1)) :
    ∀ k < n, P k = a * ∏ j ∈ Finset.range (k + 1), f j := by
  intro k hk
  induction k with
  | zero => simpa using h0
  | succ k ih => rw [hs k hk, ih (by omega), Finset.prod_range_succ (n := k + 1), mul_assoc]

/-! ## The guest's weight -/

/-- Node `j` of the skip domain as the data's word. -/
def phiE (j : ℕ) : E := word (phiWords.getD j 0) 0 0

/-- The Lagrange numerator `i` at `z`: the product of `z + node j` over `j ≠ i`, `j < 64`. -/
def lagNum (z : E) (i : ℕ) : E :=
  (∏ j ∈ Finset.range i, (z + phiE j)) * ∏ j ∈ Finset.Ico (i + 1) 64, (z + phiE j)

/-- **The weight of a fresh claim, as the guest computes it**, from the skip challenge `z`, the
row point `zchi`, the reversed column point `lrr`, the slices `zp`, the two `eqtree`s `er`, `ec`
and the batched point `rr`. -/
def guestU (z : E) (zchi lrr zp er ec rr : ℕ → E) : E :=
  (∑ i ∈ Finset.range 64, lagNum z i * er i) * word 11666641484232641359 0 0 *
      (∏ k ∈ Finset.range 8, (1 + zchi k + rr (6 + k))) *
    ((∑ i ∈ Finset.range 64, zp i * ec i) * ∏ j ∈ Finset.range 8, (1 + lrr j + rr (27 - j)))

theorem prod_chain0 {P f : ℕ → E} {n : ℕ} (hs : ∀ k < n, P (k + 1) = P k * f k) :
    ∀ k ≤ n, P k = P 0 * ∏ j ∈ Finset.range k, f j := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih => rw [hs k (by omega), ih (by omega), Finset.prod_range_succ, mul_assoc]

theorem σn_congr (σ : Val) {a b : ℕ} (h : a = b) : σ (.n a) = σ (.n b) := by rw [h]

theorem phiE_zero : phiE 0 = 0 := word_zero

section Blocks

variable {C : CallRel} {σ : Val} (kret : List E → Prop)

theorem holds_l99Pre (k : ℕ) : Stmt.HoldsList C rd σ (l99Pre (k + 1)) True kret ↔
    σ (.n (14 + 3 * k)) = word (phiWords.getD (k + 1) 0) 0 0 ∧
      σ (.n (15 + 3 * k)) = σ (.n 11) + σ (.n (14 + 3 * k)) ∧
      σ (.n (16 + 3 * k)) = σ (.n (preV (k + 1))) * σ (.n (15 + 3 * k)) := by
  simp [l99Pre, Stmt.HoldsList, Stmt.Holds, Atom.Holds]

theorem holds_l99Suf (k : ℕ) : Stmt.HoldsList C rd σ (l99Suf k) True kret ↔
    σ (.n (204 + 3 * k)) = word (phiWords.getD (63 - k) 0) 0 0 ∧
      σ (.n (205 + 3 * k)) = σ (.n 11) + σ (.n (204 + 3 * k)) ∧
      σ (.n (206 + 3 * k)) = σ (.n (if k = 0 then 203 else 203 + 3 * k)) * σ (.n (205 + 3 * k)) := by
  simp [l99Suf, Stmt.HoldsList, Stmt.Holds, Atom.Holds]

theorem holds_l99Row (k : ℕ) : Stmt.HoldsList C rd σ (l99Row (k + 1)) True kret ↔
    LoadHolds rd (σ (.n 3)) (62 + (k + 1)) (σ (.n (460 + 3 * k))) ∧
      σ (.n (461 + 3 * k)) = σ (.n (394 + (k + 1))) * σ (.n (460 + 3 * k)) ∧
      σ (.n (462 + 3 * k)) = σ (.n (if k = 0 then 459 else 459 + 3 * k)) + σ (.n (461 + 3 * k)) := by
  simp [l99Row, Stmt.HoldsList, Stmt.Holds, Atom.Holds]

theorem holds_l99RowEq (k : ℕ) : Stmt.HoldsList C rd σ (l99RowEq k) True kret ↔
    σ (.n (651 + 6 * k)) = 1 ∧ LoadHolds rd (σ (.n 10)) (25 + k) (σ (.n (652 + 6 * k))) ∧
      σ (.n (653 + 6 * k)) = σ (.n (651 + 6 * k)) + σ (.n (652 + 6 * k)) ∧
      LoadHolds rd (σ (.n 4)) (6 + k) (σ (.n (654 + 6 * k))) ∧
      σ (.n (655 + 6 * k)) = σ (.n (653 + 6 * k)) + σ (.n (654 + 6 * k)) ∧
      σ (.n (656 + 6 * k)) = σ (.n (650 + 6 * k)) * σ (.n (655 + 6 * k)) := by
  simp [l99RowEq, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one]

theorem holds_l99Col (k : ℕ) : Stmt.HoldsList C rd σ (l99Col (k + 1)) True kret ↔
    LoadHolds rd (σ (.n 10)) (41 + (k + 1)) (σ (.n (702 + 4 * k))) ∧
      LoadHolds rd (σ (.n 5)) (62 + (k + 1)) (σ (.n (703 + 4 * k))) ∧
      σ (.n (704 + 4 * k)) = σ (.n (702 + 4 * k)) * σ (.n (703 + 4 * k)) ∧
      σ (.n (705 + 4 * k)) = σ (.n (701 + 4 * k)) + σ (.n (704 + 4 * k)) := by
  simp [l99Col, Stmt.HoldsList, Stmt.Holds, Atom.Holds]

theorem holds_l99ColEq (k : ℕ) : Stmt.HoldsList C rd σ (l99ColEq k) True kret ↔
    σ (.n (954 + 6 * k)) = 1 ∧ LoadHolds rd (σ (.n 10)) (33 + k) (σ (.n (955 + 6 * k))) ∧
      σ (.n (956 + 6 * k)) = σ (.n (954 + 6 * k)) + σ (.n (955 + 6 * k)) ∧
      LoadHolds rd (σ (.n 4)) (27 - k) (σ (.n (957 + 6 * k))) ∧
      σ (.n (958 + 6 * k)) = σ (.n (956 + 6 * k)) + σ (.n (957 + 6 * k)) ∧
      σ (.n (959 + 6 * k)) = σ (.n (953 + 6 * k)) * σ (.n (958 + 6 * k)) := by
  simp [l99ColEq, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one]

theorem holds_l99Car (k : ℕ) : Stmt.HoldsList C rd σ (l99Car (k + 1)) True kret ↔
    σ (.n (1010 + 6 * k)) = 1 ∧ LoadHolds rd (σ (.n 1004)) (23 + (k + 1)) (σ (.n (1011 + 6 * k))) ∧
      σ (.n (1012 + 6 * k)) = σ (.n (1010 + 6 * k)) + σ (.n (1011 + 6 * k)) ∧
      LoadHolds rd (σ (.n 4)) (k + 1) (σ (.n (1013 + 6 * k))) ∧
      σ (.n (1014 + 6 * k)) = σ (.n (1012 + 6 * k)) + σ (.n (1013 + 6 * k)) ∧
      σ (.n (1015 + 6 * k)) = σ (.n (1009 + 6 * k)) * σ (.n (1014 + 6 * k)) := by
  simp [l99Car, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one]

end Blocks

set_option maxRecDepth 100000 in
theorem find_loop99 : coreProgram.find? "__loop99" = some Data.core572 :=
  Program.find?_of_indexOf? (j := 572) (by decide +kernel) rfl

/-- **`__loop99` at `x = g^c`**: through the rows' pointers `fp`, `cp`, the weight sums' row
`c + 1` is row `c` plus the lambdas times the fresh claim's weight `U` (`guestU`, `α·U` for `B0`)
and the carried point's eq product with the matrix point. -/
theorem loop99_step {N frow eqR mp eqC crow lamm wsums : E} (x : E)
    (h : coreProgram.Rel rd "__loop99" [x, N, frow, eqR, mp, eqC, crow, lamm, wsums] []) :
    (∀ c, x = gen ^ c → ∃ fp cp : E, LoadHolds rd frow c fp ∧ LoadHolds rd crow c cp ∧
      LoadHolds rd wsums (2 * c + 2) (cellAt rd wsums (2 * c) + cellAt rd lamm (3 * c) *
        guestU (cellAt rd fp 24) (fun k => cellAt rd fp (25 + k)) (fun j => cellAt rd fp (33 + j))
          (fun i => cellAt rd fp (41 + i)) (fun i => cellAt rd eqR (62 + i))
          (fun i => cellAt rd eqC (62 + i)) (fun k => cellAt rd mp k) +
        cellAt rd lamm (3 * c + 1) *
          ∏ k ∈ Finset.range 28, (1 + cellAt rd cp (23 + k) + cellAt rd mp k)) ∧
      LoadHolds rd wsums (2 * c + 3) (cellAt rd wsums (2 * c + 1) +
        cellAt rd lamm (3 * c) * cellAt rd fp 23 *
          guestU (cellAt rd fp 24) (fun k => cellAt rd fp (25 + k)) (fun j => cellAt rd fp (33 + j))
            (fun i => cellAt rd fp (41 + i)) (fun i => cellAt rd eqR (62 + i))
            (fun i => cellAt rd eqC (62 + i)) (fun k => cellAt rd mp k) +
        cellAt rd lamm (3 * c + 2) *
          ∏ k ∈ Finset.range 28, (1 + cellAt rd cp (23 + k) + cellAt rd mp k))) ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd "__loop99"
        [x * gen, N, frow, eqR, mp, eqC, crow, lamm, wsums] []) := by
  rw [rel_iff_sem find_loop99] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core572 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8]
    from rfl, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  rw [core572_body, l99Body] at h
  simp only [holdsList_append,
    holdsList_range_flatten 63 (fun i => l99Pre (i + 1)) (fun _ => rfl),
    holdsList_range_flatten 63 l99Suf (fun _ => rfl),
    holdsList_range_flatten 64
      (fun i => [Stmt.atom (.mul (.n (394 + i)) (.n (preAt i)) (.n (sufAt (i + 1))))]) (fun _ => rfl),
    holdsList_range_flatten 63 (fun i => l99Row (i + 1)) (fun _ => rfl),
    holdsList_range_flatten 8 l99RowEq (fun _ => rfl),
    holdsList_range_flatten 63 (fun i => l99Col (i + 1)) (fun _ => rfl),
    holdsList_range_flatten 8 l99ColEq (fun _ => rfl),
    holdsList_range_flatten 27 (fun k => l99Car (k + 1)) (fun _ => rfl)] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen,
    word_one] at h
  obtain ⟨h9, l10, l11, c12, h13, hP, c203, hS, h393, hO, l458, h459, hR, c649, h650, hRE, l699,
    l700, h701, hC, hCE, h1002, h1003, l1004, c1005, l1006, h1007, l1008, h1009, hCar, h1172, h1173,
    h1174, l1175, h1176, h1177, l1178, h1179, h1180, h1181, l1182, h1183, h1184, l1184, l1185, l1186,
    h1187, h1188, h1189, h1190, l1191, h1192, h1193, l1193, c1194, h1195, h1196, c1197, h1198, -,
    hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h1196, h1195, c1194, p0, p1]; exact hne)
    rwa [h1198, c1197, p0, p1, p2, p3, p4, p5, p6, p7, p8] at this
  -- the pointers
  rw [h9, p2, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l10
  rw [h1003, p6, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l1004
  have ez : σ (.n 11) = cellAt rd (σ (.n 10)) 24 := (cellAt_of_load l11).symm
  -- the prefix products
  have hPre : ∀ k ≤ 63, σ (.n (preAt k)) = ∏ j ∈ Finset.range k, (σ (.n 11) + phiE j) := by
    refine prod_chain (by simp [preAt, c12]) fun k hk => ?_
    rcases k with _ | k
    · simp only [preAt, Nat.add_one_ne_zero, ↓reduceIte, phiE_zero, add_zero]
      rw [h13, c12]
    · obtain ⟨q0, q1, q2⟩ := (holds_l99Pre _ k).mp (hP k (by omega))
      rw [show preAt (k + 1 + 1) = 16 + 3 * k by simp [preAt]; omega, q2, q1, q0,
        show preV (k + 1) = preAt (k + 1) by
          rcases k with _ | k <;> simp [preV, preAt]; omega]
      rfl
  -- the suffix products
  have hSuf : ∀ m ≤ 63, σ (.n (sufAt (64 - m))) = ∏ l ∈ Finset.Ico (64 - m) 64, (σ (.n 11) + phiE l) := by
    intro m hm
    induction m with
    | zero => simp [sufAt, c203]
    | succ m ih =>
      obtain ⟨q0, q1, q2⟩ := (holds_l99Suf _ m).mp (hS m (by omega))
      have hs1 : sufAt (64 - (m + 1)) = 206 + 3 * m := by
        simp only [sufAt, show 64 - (m + 1) ≠ 64 by omega, ↓reduceIte]; omega
      have hs2 : (if m = 0 then 203 else 203 + 3 * m) = sufAt (64 - m) := by
        rcases m with _ | m
        · rfl
        · simp only [sufAt, show 64 - (m + 1) ≠ 64 by omega, Nat.add_one_ne_zero, ↓reduceIte]
          omega
      rw [hs1, q2, q1, q0, hs2, ih (by omega),
        Finset.prod_eq_prod_Ico_succ_bot (by omega : 64 - (m + 1) < 64),
        show 64 - (m + 1) + 1 = 64 - m by omega, mul_comm, phiE, show 64 - (m + 1) = 63 - m by omega]
  have hNum : ∀ i < 64, σ (.n (394 + i)) = lagNum (σ (.n 11)) i := by
    intro i hi
    rw [(hO i hi).1, hPre i (by omega), show i + 1 = 64 - (63 - i) by omega, hSuf _ (by omega),
      lagNum, show 64 - (63 - i) = i + 1 by omega]
  -- the row sum, its scale and its eq factors
  have l3 : ∀ {k : ℕ} {v : E}, LoadHolds rd (σ (.n 3)) k v → v = cellAt rd eqR k := fun h => by
    rw [p3] at h; exact (cellAt_of_load h).symm
  have l4 : ∀ {k : ℕ} {v : E}, LoadHolds rd (σ (.n 4)) k v → v = cellAt rd mp k := fun h => by
    rw [p4] at h; exact (cellAt_of_load h).symm
  have l5 : ∀ {k : ℕ} {v : E}, LoadHolds rd (σ (.n 5)) k v → v = cellAt rd eqC k := fun h => by
    rw [p5] at h; exact (cellAt_of_load h).symm
  have lF : ∀ {k : ℕ} {v : E}, LoadHolds rd (σ (.n 10)) k v → v = cellAt rd (σ (.n 10)) k :=
    fun h => (cellAt_of_load h).symm
  have lC : ∀ {k : ℕ} {v : E}, LoadHolds rd (σ (.n 1004)) k v → v = cellAt rd (σ (.n 1004)) k :=
    fun h => (cellAt_of_load h).symm
  have hRow := sum_chain (S := fun k => σ (.n (459 + 3 * k)))
    (t := fun i => lagNum (σ (.n 11)) i * cellAt rd eqR (62 + i)) (n := 64)
    (by simp only [Nat.mul_zero, Nat.add_zero]; rw [h459, hNum 0 (by omega), l3 l458])
    (fun k hk => by
      obtain ⟨q0, q1, q2⟩ := (holds_l99Row _ k).mp (hR k (by omega))
      rw [show 459 + 3 * (k + 1) = 462 + 3 * k by ring, q2, q1, hNum (k + 1) (by omega), ← l3 q0,
        show (if k = 0 then 459 else 459 + 3 * k) = 459 + 3 * k by split_ifs <;> omega])
    63 (by omega)
  have hRowEq := prod_chain0 (P := fun k => σ (.n (650 + 6 * k)))
    (f := fun k => 1 + cellAt rd (σ (.n 10)) (25 + k) + cellAt rd mp (6 + k)) (n := 8)
    (fun k hk => by
      obtain ⟨q0, q1, q2, q3, q4, q5⟩ := (holds_l99RowEq _ k).mp (hRE k (by omega))
      rw [show 650 + 6 * (k + 1) = 656 + 6 * k by ring, q5, q4, q2, q0, ← lF q1, ← l4 q3])
    8 le_rfl
  -- the column sum and its eq factors
  have hCol := sum_chain (S := fun k => σ (.n (701 + 4 * k)))
    (t := fun i => cellAt rd (σ (.n 10)) (41 + i) * cellAt rd eqC (62 + i)) (n := 64)
    (by simp only [Nat.mul_zero, Nat.add_zero]; rw [h701, ← lF l699, ← l5 l700])
    (fun k hk => by
      obtain ⟨q0, q1, q2, q3⟩ := (holds_l99Col _ k).mp (hC k (by omega))
      rw [show 701 + 4 * (k + 1) = 705 + 4 * k by ring, q3, q2, ← lF q0, ← l5 q1])
    63 (by omega)
  have hColEq := prod_chain0 (P := fun k => σ (.n (953 + 6 * k)))
    (f := fun k => 1 + cellAt rd (σ (.n 10)) (33 + k) + cellAt rd mp (27 - k)) (n := 8)
    (fun k hk => by
      obtain ⟨q0, q1, q2, q3, q4, q5⟩ := (holds_l99ColEq _ k).mp (hCE k (by omega))
      rw [show 953 + 6 * (k + 1) = 959 + 6 * k by ring, q5, q4, q2, q0, ← lF q1, ← l4 q3])
    8 le_rfl
  -- the carried claim
  have hCar' := prod_chain' (P := fun k => σ (.n (1009 + 6 * k)))
    (f := fun k => 1 + cellAt rd (σ (.n 1004)) (23 + k) + cellAt rd mp k) (n := 28) (a := 1)
    (by simp only [Nat.mul_zero, Nat.add_zero, one_mul]
        rw [h1009, h1007, c1005, ← lC l1006, ← l4 l1008])
    (fun k hk => by
      obtain ⟨q0, q1, q2, q3, q4, q5⟩ := (holds_l99Car _ k).mp (hCar k (by omega))
      rw [show 1009 + 6 * (k + 1) = 1015 + 6 * k by ring, q5, q4, q2, q0, ← lC q1, ← l4 q3])
    27 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hRow hRowEq hCol hColEq hCar'
  have hU : σ (.n 1002) = guestU (cellAt rd (σ (.n 10)) 24) (fun k => cellAt rd (σ (.n 10)) (25 + k))
      (fun j => cellAt rd (σ (.n 10)) (33 + j)) (fun i => cellAt rd (σ (.n 10)) (41 + i)) (fun i => cellAt rd eqR (62 + i))
      (fun i => cellAt rd eqC (62 + i)) (fun k => cellAt rd mp k) := by
    rw [h1002, hRowEq, hColEq, h650, hRow, c649, hCol, guestU, ← ez]
  -- the tail
  have e1173 : σ (.n 1173) = gen ^ (3 * c) := by rw [h1173, h1172, p0, hx]; ring
  have e1176 : σ (.n 1176) = gen ^ (2 * c) := by rw [h1176, p0, hx]; ring
  rw [h1174, e1173, p7, loadHolds_mul_gen_pow, Nat.add_zero] at l1175
  rw [h1181, e1173, p7, loadHolds_mul_gen_pow] at l1182
  rw [h1190, e1173, p7, loadHolds_mul_gen_pow] at l1191
  rw [h1177, e1176, p8, loadHolds_mul_gen_pow] at l1178 l1184 l1185 l1193
  rw [Nat.add_zero] at l1178
  refine ⟨σ (.n 10), σ (.n 1004), l10, l1004, ?_, ?_⟩
  · rw [h1184, h1183, h1180, h1179, hU, hCar', ← cellAt_of_load l1178, ← cellAt_of_load l1175,
      ← cellAt_of_load l1182, one_mul] at l1184
    exact l1184
  · rw [h1193, h1192, h1189, h1188, h1187, hU, hCar', ← cellAt_of_load l1185,
      ← cellAt_of_load l1175, ← cellAt_of_load l1191, lF l1186, one_mul] at l1193
    exact l1193

end
end LeanVM.Guest.B1.Main
