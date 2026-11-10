/-
  LeanVM.Guest.B1.Whir.RoundComplete

  `opening_round`'s completeness: on its meaning, its honest values make its body hold, its two
  `grind_check__L9` calls on passing words.
-/

module

public import LeanVM.Guest.B1.Whir.Round

/-!
# `opening_round`, honestly

`rdVals as xs`: the honest values of `roundBody` on the arguments `as` and the seven words `xs` at
the cursor, value by value (the sponge's five permutations `rdS1 .. rdS5`). `round_complete`: on
its meaning (`MeaningOpeningRound`), with `xs` the words it reads, the body holds at those values
under any call relation in which `grind_check__L9` holds of a passing word and the tables; the
two grinds' words are cell `1` of the nonces' permutations (`rdVals_24`, `rdVals_69`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The honest values -/

/-- Cell `i` of a state. -/
def rdCell (S : KeccakState) (i : ℕ) : E := cellsOfState S false ⟨i % 13, Nat.mod_lt _ (by omega)⟩

/-- The first nonce's permutation. -/
def rdS1 (as xs : List E) : KeccakState := (⟨as.take 5, []⟩ : Fs).nonceState (xs.getD 0 0)

/-- The four scalars' permutation. -/
def rdS2' (as xs : List E) : KeccakState :=
  (⟨capOf (rdS1 as xs), [(xs.getD 1 0, dsObserve), (xs.getD 2 0, dsObserve),
    (xs.getD 3 0, dsObserve), (xs.getD 4 0, dsObserve)]⟩ : Fs).perm

/-- The second nonce's permutation. -/
def rdS3 (as xs : List E) : KeccakState :=
  (⟨capOf (rdS2' as xs), [(xs.getD 5 0, dsObserve), (xs.getD 6 0, dsPowNonce)]⟩ : Fs).perm

/-- `α`'s permutation. -/
def rdS4 (as xs : List E) : KeccakState := (⟨capOf (rdS3 as xs), []⟩ : Fs).perm

/-- `β`'s permutation. -/
def rdS5 (as xs : List E) : KeccakState := (⟨capOf (rdS4 as xs), []⟩ : Fs).perm

/-- The arithmetic tail's values, from `110`. -/
def rdTail (as xs : List E) : List E :=
  let th := rdCell (rdS1 as xs) 0
  let ga := rdCell (rdS3 as xs) 0
  let al := rdCell (rdS4 as xs) 0
  let be := rdCell (rdS5 as xs) 0
  let u0 := xs.getD 1 0
  let v0 := xs.getD 2 0
  let c0 := xs.getD 3 0
  let v1 := xs.getD 4 0
  let c1 := xs.getD 5 0
  let claim := as.getD 6 0
  let s0 := u0 + al * v0 + be * c0
  let s1 := claim + v0 + th * u0 + al * v1 + be * c1
  [al * v0, u0 + al * v0, be * c0, s0, claim + v0, th * u0, claim + v0 + th * u0, al * v1,
    claim + v0 + th * u0 + al * v1, be * c1, s1,
    rdCell (rdS5 as xs) 8, rdCell (rdS5 as xs) 9, rdCell (rdS5 as xs) 10, rdCell (rdS5 as xs) 11,
    rdCell (rdS5 as xs) 12, word 128 0, as.getD 5 0 * word 128 0, as.getD 5 0 * word 128 0,
    s0 + s1, ga * (s0 + s1), s0 + ga * (s0 + s1)]

/-- **The honest values of `opening_round`**, by index. -/
def rdVals (as xs : List E) (k : ℕ) : E :=
  let wo := word 0 dsObserve
  let wp := word 0 dsPowNonce
  if k < 10 then as.getD k 0
  else if k < 15 then as.getD (k - 10) 0
  else if k < 23 then [xs.getD 0 0, xs.getD 0 0, wp, word 1 0, 0, 0, 0, 0].getD (k - 15) 0
  else if k < 36 then rdCell (rdS1 as xs) (k - 23)
  else if k = 36 then rdCell (rdS1 as xs) 0
  else if k < 49 then [xs.getD 1 0, xs.getD 1 0, wo, xs.getD 2 0, xs.getD 2 0, wo, xs.getD 3 0,
    xs.getD 3 0, wo, xs.getD 4 0, xs.getD 4 0, wo].getD (k - 37) 0
  else if k < 62 then rdCell (rdS2' as xs) (k - 49)
  else if k < 68 then [xs.getD 5 0, xs.getD 5 0, wo, xs.getD 6 0, xs.getD 6 0, wp].getD (k - 62) 0
  else if k < 81 then rdCell (rdS3 as xs) (k - 68)
  else if k = 81 then rdCell (rdS3 as xs) 0
  else if k < 95 then rdCell (rdS4 as xs) (k - 82)
  else if k = 95 then rdCell (rdS4 as xs) 0
  else if k < 109 then rdCell (rdS5 as xs) (k - 96)
  else if k = 109 then rdCell (rdS5 as xs) 0
  else (rdTail as xs).getD (k - 110) 0

theorem rdVals_24 (as xs : List E) : rdVals as xs 24 = rdCell (rdS1 as xs) 1 := by
  simp [rdVals]

theorem rdVals_69 (as xs : List E) : rdVals as xs 69 = rdCell (rdS3 as xs) 1 := by
  simp [rdVals]

theorem rdVals_7 (as xs : List E) : rdVals as xs 7 = as.getD 7 0 := by simp [rdVals]

/-! ## The meaning's sponges -/

theorem foldGrindingBits_eq : _root_.LeanVM.Parameters.Whir.foldGrindingBits = 9 := rfl

theorem rdCell_eq (S : KeccakState) (c : Fin 13) : rdCell S c.val = cellsOfState S false c := by
  unfold rdCell
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt c.isLt)

/-- The meaning's sponges are the honest permutations. -/
theorem rd_sponges (f0 f1 f2 f3 f4 cur claim tabs gp cp n1 u0 v0 c0 v1 c1 n2 : E) :
    let as := [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp]
    let xs := [n1, u0, v0, c0, v1, c1, n2]
    let fs := [f0, f1, f2, f3, f4]
    let m := [u0, v0, c0, v1, c1]
    rdG1 fs n1 = (challengeOf (rdS1 as xs), ⟨capOf (rdS1 as xs), []⟩) ∧
      (⟨fs, []⟩ : Fs).nonceState n1 = rdS1 as xs ∧
      rdS2 fs n1 m = ⟨capOf (rdS2' as xs), [(c1, dsObserve)]⟩ ∧
      (rdS2 fs n1 m).nonceState n2 = rdS3 as xs ∧
      rdG2 fs n1 m n2 = (challengeOf (rdS3 as xs), ⟨capOf (rdS3 as xs), []⟩) ∧
      (rdG2 fs n1 m n2).2.squeeze = (challengeOf (rdS4 as xs), ⟨capOf (rdS4 as xs), []⟩) ∧
      (rdG2 fs n1 m n2).2.squeeze.2.squeeze =
        (challengeOf (rdS5 as xs), ⟨capOf (rdS5 as xs), []⟩) := by
  intro as xs fs m
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have e1 : rdG1 fs n1 = (challengeOf (rdS1 as xs), ⟨capOf (rdS1 as xs), []⟩) := by
    rw [rdG1, Fs.grindSqueeze_pos _ hb]; rfl
  have es : rdS2 fs n1 m = ⟨capOf (rdS2' as xs), [(c1, dsObserve)]⟩ := by
    rw [rdS2, e1, absorbAll_five]; rfl
  have en : (rdS2 fs n1 m).nonceState n2 = rdS3 as xs := by
    rw [es]; simp [Fs.nonceState, Fs.absorb, rateScalars, rdS3, xs]
  have e2 : rdG2 fs n1 m n2 = (challengeOf (rdS3 as xs), ⟨capOf (rdS3 as xs), []⟩) := by
    rw [rdG2, Fs.grindSqueeze_pos _ hb, en]
  refine ⟨e1, rfl, es, en, e2, ?_, ?_⟩
  · rw [e2]; rfl
  · rw [e2]; rfl

/-! ## The body holds -/

theorem roundBody_split : roundBody = roundBody.dropLast ++ [.ret [.n 121, .n 122, .n 123,
    .n 124, .n 125, .n 128, .n 131]] := by
  rfl

/-- **`opening_round`'s body holds at its honest values** on its meaning, under a call relation
in which `grind_check__L9` holds of a passing word and the tables. -/
theorem round_complete {C : CallRel} {rd : Reader} {args rets : List E}
    (hm : MeaningOpeningRound rd args rets)
    (hg : ∀ w : E, (w.limb 0).lane.toNat % 2 ^ 9 = 0 → C "grind_check__L9" [w, args.getD 7 0] []) :
    ∃ xs : List E, xs.length = 7 ∧ ReadsAt rd (args.getD 5 0) xs ∧
      ((rdCell (rdS1 args xs) 1).limb 0).lane.toNat % 2 ^ 9 = 0 ∧
      ((rdCell (rdS3 args xs) 1).limb 0).lane.toNat % 2 ^ 9 = 0 ∧
      (Fn.params Data.core7).map (fun v ↦ rdVals args xs v.idx) = args ∧
      Stmt.HoldsList C rd (fun v ↦ rdVals args xs v.idx) roundBody False (fun rs ↦ rs = rets) := by
  obtain ⟨f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp, rfl⟩ :
      ∃ f0 f1 f2 f3 f4 cur claim tabs gp cp, args = [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp] := by
    match args, hm with
    | [a, b, c, d, e, f, g, h, i, j], _ => exact ⟨a, b, c, d, e, f, g, h, i, j, rfl⟩
  obtain ⟨n1, u0, v0, c0, v1, c1, n2, hrd, g1, g2, lg, la, lb, lt, hret⟩ := hm
  obtain ⟨e1, en1, es, en2, e2, e3, e4⟩ := rd_sponges f0 f1 f2 f3 f4 cur claim tabs gp cp n1 u0 v0 c0
    v1 c1 n2
  set as := [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp] with has
  set xs := [n1, u0, v0, c0, v1, c1, n2] with hxs
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have p1 := (grindOk_iff hb n1).mp g1
  have p2 := (grindOk_iff hb n2).mp g2
  rw [en1, foldGrindingBits_eq] at p1
  rw [en2, foldGrindingBits_eq] at p2
  rw [← rdCell_eq _ 1] at p1 p2
  replace p1 : ((rdCell (rdS1 as xs) 1).limb 0).lane.toNat % 2 ^ 9 = 0 := p1
  replace p2 : ((rdCell (rdS3 as xs) 1).limb 0).lane.toNat % 2 ^ 9 = 0 := p2
  refine ⟨xs, rfl, hrd, p1, p2, by simp [core7_params, rdVals, List.range_succ, has], ?_⟩
  set σ : Val := fun v ↦ rdVals as xs v.idx with hσ
  have ev : ∀ k, σ (.n k) = rdVals as xs k := fun _ ↦ rfl
  rw [e1, Keccak.challengeOf_cells, ← rdCell_eq _ 0] at lt
  rw [e2, Keccak.challengeOf_cells, ← rdCell_eq _ 0] at lg
  rw [e3, Keccak.challengeOf_cells, ← rdCell_eq _ 0] at la
  rw [e4, Keccak.challengeOf_cells, ← rdCell_eq _ 0] at lb
  rw [roundBody_split, holdsList_flat_ret _ (by decide)]
  have h1 : rdS1 as xs = (⟨[f0, f1, f2, f3, f4], [(n1, dsPowNonce)]⟩ : Fs).perm := by
    simp [rdS1, Fs.nonceState, Fs.absorb, rateScalars, as, xs]
  have k1 : permOf ([V.n 16, .n 17, .n 19, .n 19, .n 19, .n 20, .n 21, .n 22, .n 10, .n 11, .n 12,
      .n 13, .n 14].map σ) = rdS1 as xs := by
    rw [h1, perm_eq_cells _ (by simp)]; rfl
  have k2 : permOf ([V.n 38, .n 39, .n 41, .n 42, .n 44, .n 45, .n 47, .n 48, .n 31, .n 32, .n 33,
      .n 34, .n 35].map σ) = rdS2' as xs := by
    rw [rdS2', perm_eq_cells _ (by simp)]; rfl
  have k3 : permOf ([V.n 63, .n 64, .n 66, .n 67, .n 19, .n 20, .n 21, .n 22, .n 57, .n 58, .n 59,
      .n 60, .n 61].map σ) = rdS3 as xs := by
    rw [rdS3, perm_eq_cells _ (by simp)]; rfl
  have k4 : permOf ([V.n 19, .n 19, .n 19, .n 19, .n 19, .n 20, .n 21, .n 22, .n 76, .n 77, .n 78,
      .n 79, .n 80].map σ) = rdS4 as xs := by
    rw [rdS4, perm_eq_cells _ (by simp)]; rfl
  have k5 : permOf ([V.n 19, .n 19, .n 19, .n 19, .n 19, .n 20, .n 21, .n 22, .n 90, .n 91, .n 92,
      .n 93, .n 94].map σ) = rdS5 as xs := by
    rw [rdS5, perm_eq_cells _ (by simp)]; rfl
  have l0 : LoadHolds rd cur 0 n1 := hrd 0 (by simp [xs])
  have l1 : LoadHolds rd cur 1 u0 := hrd 1 (by simp [xs])
  have l2 : LoadHolds rd cur 2 v0 := hrd 2 (by simp [xs])
  have l3 : LoadHolds rd cur 3 c0 := hrd 3 (by simp [xs])
  have l4 : LoadHolds rd cur 4 v1 := hrd 4 (by simp [xs])
  have l5 : LoadHolds rd cur 5 c1 := hrd 5 (by simp [xs])
  have l6 : LoadHolds rd cur 6 n2 := hrd 6 (by simp [xs])
  clear hrd
  refine ⟨?_, ?_⟩
  · simp only [roundBody, fsNonceT, fsNextT, fsPackT, padRunT, challengeT, permIns, osRun, keccakA,
      osLd, osMul, osAdd, osCp, osCst, List.range_succ, List.range_zero, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, List.take, List.dropLast_cons_cons,
      List.dropLast_singleton, Nat.reduceAdd]
    repeat' (first | exact allOk_nil | refine allOk_cons.mpr ⟨?_, ?_⟩)
    all_goals first
      | (simp only [stmtOk_atom, holds_load, ev]
         simp (config := {decide := true}) only [rdVals, Fin.val_zero, ↓reduceIte,
           Nat.reduceSub] at lg la lb lt ⊢
         simp only [has, hxs, List.getD_cons_zero, List.getD_cons_succ] at lg la lb lt ⊢
         first
           | with_reducible exact l0
           | with_reducible exact l1
           | with_reducible exact l2
           | with_reducible exact l3
           | with_reducible exact l4
           | with_reducible exact l5
           | with_reducible exact l6
           | with_reducible exact lg
           | with_reducible exact la
           | with_reducible exact lb
           | with_reducible exact lt)
      | (rw [stmtOk_call]
         simp only [List.map_cons, List.map_nil, ev, rdVals_24, rdVals_69, rdVals_7]
         first | with_reducible exact hg _ p1 | with_reducible exact hg _ p2)
      | (rw [stmtOk_atom]
         refine keccakA_of rfl rfl ?_
         first | rw [k1] | rw [k2] | rw [k3] | rw [k4] | rw [k5]
         funext c
         fin_cases c <;> rfl)
      | (simp only [stmtOk_atom, holds_const, holds_copy, holds_add, holds_mul, ev]
         simp [rdVals, rdTail, word_zero])
  · have hw : word 128 0 = gen ^ 7 := word_two_pow (a := 7) (by decide)
    rw [hret, e4, e3, e2, e1]
    simp only [Keccak.challengeOf_cells, ← rdCell_eq _ 0, Fin.val_zero, capOf, ← rdCell_eq _ 8,
      ← rdCell_eq _ 9, ← rdCell_eq _ 10, ← rdCell_eq _ 11, ← rdCell_eq _ 12]
    simp (config := {decide := true}) only [List.map_cons, List.map_nil, ev, rdVals, rdTail,
      ↓reduceIte, Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ, List.cons_append,
      List.nil_append, hw, roundClaim]
    rfl

end
end LeanVM.Guest.B1.Whir
