/-
  LeanVM.Guest.B1.Whir.RoundComplete

  `opening_round`'s completeness: on its meaning, its honest values make its body hold, its
  `grind_check__L7` call on a passing word.
-/

module

public import LeanVM.Guest.B1.Whir.Round

/-!
# `opening_round`, honestly

`rdVals as xs`: the honest values of `roundBody` on the arguments `as` and the five words `xs` at
the cursor, value by value (the sponge's three permutations `rdS1`, `rdS3`, `rdS4`).
`round_complete`: on its meaning (`MeaningOpeningRound`), with `xs` the words it reads, the body
holds at those values under any call relation in which `grind_check__L7` holds of a passing word
and the tables; the grind's word is cell `1` of the nonce's permutation (`rdVals_52`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The honest values -/

/-- Cell `i` of a state. -/
def rdCell (S : KeccakState) (i : ℕ) : E := cellsOfState S false ⟨i % 13, Nat.mod_lt _ (by omega)⟩

/-- The four scalars' permutation. -/
def rdS1 (as xs : List E) : KeccakState :=
  (⟨as.take 5, [(xs.getD 0 0, dsObserve), (xs.getD 1 0, dsObserve), (xs.getD 2 0, dsObserve),
    (xs.getD 3 0, dsObserve)]⟩ : Fs).perm

/-- The nonce's permutation. -/
def rdS3 (as xs : List E) : KeccakState :=
  (⟨capOf (rdS1 as xs), [(xs.getD 4 0, dsPowNonce)]⟩ : Fs).perm

/-- `β`'s permutation. -/
def rdS4 (as xs : List E) : KeccakState := (⟨capOf (rdS3 as xs), []⟩ : Fs).perm

/-- The arithmetic tail's values, from `76`. -/
def rdTail (as xs : List E) : List E :=
  let al := rdCell (rdS3 as xs) 0
  let be := rdCell (rdS4 as xs) 0
  let u0 := xs.getD 0 0
  let w := xs.getD 1 0
  let c0 := xs.getD 2 0
  let c1 := xs.getD 3 0
  let claim := as.getD 6 0
  let a := u0 + claim + al * w + be * (c0 + c1)
  [be * c0, u0 + be * c0, u0 + claim, al * w, u0 + claim + al * w, c0 + c1, be * (c0 + c1), a,
    al * a, u0 + be * c0 + al * a,
    rdCell (rdS4 as xs) 8, rdCell (rdS4 as xs) 9, rdCell (rdS4 as xs) 10, rdCell (rdS4 as xs) 11,
    rdCell (rdS4 as xs) 12, word 32 0, as.getD 5 0 * word 32 0, as.getD 5 0 * word 32 0,
    u0 + be * c0 + al * a]

/-- **The honest values of `opening_round`**, by index. -/
def rdVals (as xs : List E) (k : ℕ) : E :=
  let wo := word 0 dsObserve
  let wp := word 0 dsPowNonce
  if k < 10 then as.getD k 0
  else if k < 15 then as.getD (k - 10) 0
  else if k < 27 then [xs.getD 0 0, xs.getD 0 0, wo, xs.getD 1 0, xs.getD 1 0, wo, xs.getD 2 0,
    xs.getD 2 0, wo, xs.getD 3 0, xs.getD 3 0, wo].getD (k - 15) 0
  else if k < 40 then rdCell (rdS1 as xs) (k - 27)
  else if k < 43 then [xs.getD 4 0, xs.getD 4 0, wp].getD (k - 40) 0
  else if k < 48 then [word 1 0, 0, 0, 0, 0].getD (k - 43) 0
  else if k < 61 then rdCell (rdS3 as xs) (k - 48)
  else if k = 61 then rdCell (rdS3 as xs) 0
  else if k < 75 then rdCell (rdS4 as xs) (k - 62)
  else if k = 75 then rdCell (rdS4 as xs) 0
  else (rdTail as xs).getD (k - 76) 0

theorem rdVals_49 (as xs : List E) : rdVals as xs 49 = rdCell (rdS3 as xs) 1 := by
  simp [rdVals]

theorem rdVals_7 (as xs : List E) : rdVals as xs 7 = as.getD 7 0 := by simp [rdVals]

/-! ## The meaning's sponges -/

theorem foldGrindingBits_eq : _root_.LeanVM.Parameters.Whir.foldGrindingBits = 7 := rfl

theorem rdCell_eq (S : KeccakState) (c : Fin 13) : rdCell S c.val = cellsOfState S false c := by
  unfold rdCell
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt c.isLt)

/-- The meaning's sponges are the honest permutations. -/
theorem rd_sponges (f0 f1 f2 f3 f4 cur claim tabs gp cp u0 w c0 c1 n2 : E) :
    let as := [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp]
    let xs := [u0, w, c0, c1, n2]
    let fs := [f0, f1, f2, f3, f4]
    let m := [u0, w, c0, c1]
    (rdS2 fs m).nonceState n2 = rdS3 as xs ∧
      rdG2 fs m n2 = (challengeOf (rdS3 as xs), ⟨capOf (rdS3 as xs), []⟩) ∧
      (rdG2 fs m n2).2.squeeze = (challengeOf (rdS4 as xs), ⟨capOf (rdS4 as xs), []⟩) := by
  intro as xs fs m
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have es : rdS2 fs m = ⟨fs, [(u0, dsObserve), (w, dsObserve), (c0, dsObserve), (c1, dsObserve)]⟩ := by
    rw [rdS2, absorbAll_four]
  have en : (rdS2 fs m).nonceState n2 = rdS3 as xs := by
    rw [es]; simp [Fs.nonceState, Fs.absorb, rateScalars, rdS3, rdS1, xs, as, fs]
  have e2 : rdG2 fs m n2 = (challengeOf (rdS3 as xs), ⟨capOf (rdS3 as xs), []⟩) := by
    rw [rdG2, Fs.grindSqueeze_pos _ hb, en]
  refine ⟨en, e2, ?_⟩
  rw [e2]; rfl

/-! ## The body holds -/

theorem roundBody_split : roundBody = roundBody.dropLast ++ [.ret [.n 86, .n 87, .n 88,
    .n 89, .n 90, .n 93, .n 94]] := by
  rfl

/-- **`opening_round`'s body holds at its honest values** on its meaning, under a call relation
in which `grind_check__L7` holds of a passing word and the tables. -/
theorem round_complete {C : CallRel} {rd : Reader} {args rets : List E}
    (hm : MeaningOpeningRound rd args rets)
    (hg : ∀ w : E, (w.limb 0).lane.toNat % 2 ^ 7 = 0 → C "grind_check__L7" [w, args.getD 7 0] []) :
    ∃ xs : List E, xs.length = 5 ∧ ReadsAt rd (args.getD 5 0) xs ∧
      ((rdCell (rdS3 args xs) 1).limb 0).lane.toNat % 2 ^ 7 = 0 ∧
      (Fn.params Data.core7).map (fun v ↦ rdVals args xs v.idx) = args ∧
      Stmt.HoldsList C rd (fun v ↦ rdVals args xs v.idx) roundBody False (fun rs ↦ rs = rets) := by
  obtain ⟨f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp, rfl⟩ :
      ∃ f0 f1 f2 f3 f4 cur claim tabs gp cp, args = [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp] := by
    match args, hm with
    | [a, b, c, d, e, f, g, h, i, j], _ => exact ⟨a, b, c, d, e, f, g, h, i, j, rfl⟩
  obtain ⟨u0, w, c0, c1, n2, hrd, g2, lg, la, lb, hret⟩ := hm
  obtain ⟨en2, e2, e3⟩ := rd_sponges f0 f1 f2 f3 f4 cur claim tabs gp cp u0 w c0 c1 n2
  set as := [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp] with has
  set xs := [u0, w, c0, c1, n2] with hxs
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have p2 := (grindOk_iff hb n2).mp g2
  rw [en2, foldGrindingBits_eq] at p2
  rw [← rdCell_eq _ 1] at p2
  replace p2 : ((rdCell (rdS3 as xs) 1).limb 0).lane.toNat % 2 ^ 7 = 0 := p2
  refine ⟨xs, rfl, hrd, p2, by simp [core7_params, rdVals, List.range_succ, has], ?_⟩
  set σ : Val := fun v ↦ rdVals as xs v.idx with hσ
  have ev : ∀ k, σ (.n k) = rdVals as xs k := fun _ ↦ rfl
  rw [e2, Keccak.challengeOf_cells, ← rdCell_eq _ 0] at lg la
  rw [e3, Keccak.challengeOf_cells, ← rdCell_eq _ 0] at lb
  rw [roundBody_split, holdsList_flat_ret _ (by decide)]
  have k1 : permOf ([V.n 16, .n 17, .n 19, .n 20, .n 22, .n 23, .n 25, .n 26, .n 10, .n 11, .n 12,
      .n 13, .n 14].map σ) = rdS1 as xs := by
    rw [rdS1, perm_eq_cells _ (by simp)]; rfl
  have k3 : permOf ([V.n 41, .n 42, .n 44, .n 44, .n 44, .n 45, .n 46, .n 47, .n 35, .n 36, .n 37,
      .n 38, .n 39].map σ) = rdS3 as xs := by
    rw [rdS3, perm_eq_cells _ (by simp)]; rfl
  have k4 : permOf ([V.n 44, .n 44, .n 44, .n 44, .n 44, .n 45, .n 46, .n 47, .n 56, .n 57, .n 58,
      .n 59, .n 60].map σ) = rdS4 as xs := by
    rw [rdS4, perm_eq_cells _ (by simp)]; rfl
  have l0 : LoadHolds rd cur 0 u0 := hrd 0 (by simp [xs])
  have l1 : LoadHolds rd cur 1 w := hrd 1 (by simp [xs])
  have l2 : LoadHolds rd cur 2 c0 := hrd 2 (by simp [xs])
  have l3 : LoadHolds rd cur 3 c1 := hrd 3 (by simp [xs])
  have l4 : LoadHolds rd cur 4 n2 := hrd 4 (by simp [xs])
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
           Nat.reduceSub] at lg la lb ⊢
         simp only [has, hxs, List.getD_cons_zero, List.getD_cons_succ] at lg la lb ⊢
         first
           | with_reducible exact l0
           | with_reducible exact l1
           | with_reducible exact l2
           | with_reducible exact l3
           | with_reducible exact l4
           | with_reducible exact lg
           | with_reducible exact la
           | with_reducible exact lb)
      | (rw [stmtOk_call]
         simp only [List.map_cons, List.map_nil, ev, rdVals_49, rdVals_7]
         with_reducible exact hg _ p2)
      | (rw [stmtOk_atom]
         refine keccakA_of rfl rfl ?_
         first | rw [k1] | rw [k3] | rw [k4]
         funext c
         fin_cases c <;> rfl)
      | (simp only [stmtOk_atom, holds_const, holds_copy, holds_add, holds_mul, ev]
         simp [rdVals, rdTail, word_zero])
  · have hw : word 32 0 = gen ^ 5 := word_two_pow (a := 5) (by decide)
    rw [hret, e3, e2]
    simp only [Keccak.challengeOf_cells, ← rdCell_eq _ 0, Fin.val_zero, capOf, ← rdCell_eq _ 8,
      ← rdCell_eq _ 9, ← rdCell_eq _ 10, ← rdCell_eq _ 11, ← rdCell_eq _ 12]
    simp (config := {decide := true}) only [List.map_cons, List.map_nil, ev, rdVals, rdTail,
      ↓reduceIte, Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ, List.cons_append,
      List.nil_append, hw, roundClaim]
    rfl

end
end LeanVM.Guest.B1.Whir
