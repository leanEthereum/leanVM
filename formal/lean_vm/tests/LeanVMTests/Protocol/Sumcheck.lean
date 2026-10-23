import LeanVM.Protocol.ToArkLib.Sumcheck
import LeanVM.Protocol.ToArkLib.Oracles
import LeanVM.Protocol.Field
import LeanVM.Protocol.Spine.Errors
import LeanVM.Protocol.Spine.Slots
import LeanVM.Protocol.Spine.Toy

/-!
# Sumcheck tests

Over `E`, with no public data and no oracle, on a summand of degree two in two variables, the
product of two tables' extensions.

* **The plain sumcheck, by hand.** The claim is the sum of the summand over the cube; each honest
  round polynomial passes the check and evaluates to the next claim; the first challenge is the
  highest coordinate, so the claim after one round sums over the low coordinate with the high
  one at the challenge; the honest values pass the final check, and the output relation holds.
* **The normalized sumcheck, by hand.** The same with the weights of an equality polynomial: the
  claim is `Σ_x eq(p, x) · summand(x)`, the round check weighs `q(0)` and `q(1)` by `1 - p_k` and
  `p_k`, and the final claim is the summand at the challenges, with no equality factor.
* **What is rejected.** A round polynomial with one coefficient changed, a wrong claim, and
  values that are not the tables' at the final point.
* **The wire.** The Rust verifier's decoding of a round (`sumcheck_round_poly`,
  `crates/verifier/src/transcript.rs:186-202` at leanVM `127510d1`): the plain round drops
  `c_1`, recomputed as `claim + c_2 + … + c_d`; the normalized round drops `c_0`, recomputed as
  `claim + r · (c_1 + … + c_d)`. `decodeWire` agrees with both on honest messages of degree two
  and three, and returns the honest message from the wire of `d` values; a round read on the wire
  keeps its security at the same errors (`transport`).
* **The final check is load-bearing.** Without it the last message has no security at any error,
  whatever the extractor: a statement whose claim is not the summand at its point is carried
  into the output relation by the true values.
* **Degree in each variable.** A summand of the table sumcheck's shape, a padding coordinate times
  an equality factor in another coordinate times a constraint of degree two on a lifted table, has
  degree three in each variable, though its factors' degrees add up to four.
* **The slot.** The table sumcheck's slot `tableSlot` takes the batching challenge followed by the
  rounds and the last message of a plain sumcheck of degree three, by definitional equality.
* **Completeness** has an inhabitant for both variants.
* **Knowledge soundness** has an inhabitant for both variants, at the slot's unit, as plain
  definitions that compute at `E`; the rounds of a cubic plain sumcheck over the toy's stack meet
  the table slot's per-round error `overE 3`; without its check, a round of the family has no
  knowledge error below one.

A plain file, so `#guard` evaluates the compiled definitions. Values of `E` written with numerals
are named as definitions before a guard uses them.
-/

namespace LeanVMTests.Protocol.Sumcheck

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Sumcheck CompPoly CMlPolynomialEval
  OracleComp OracleSpec

/-- No oracle. -/
def noO : ∀ i, NoOracle i := fun i ↦ i.elim0

/-- Values of `E`. -/
def a : E := y
def b : E := y + 1
def c : E := y * y + y
def one : E := 1
def zero : E := 0

/-- Two tables on two variables. -/
def t₁ : CMlPolynomialEval E 2 := #v[a, b, c, 1]
def t₂ : CMlPolynomialEval E 2 := #v[b, 1, a, c]

/-- The virtual polynomial `t₁ · t₂`. -/
def V : Virtual E Unit NoOracle Unit 2 2 where
  tables := fun _ ↦ ![t₁, t₂]
  formula := fun _ _ v ↦ v[0] * v[1]

/-- The context: no public data, no oracle, no witness. -/
def ctx : SumcheckRound.Ctx Unit NoOracle Unit := (((), noO), ())

/-- No side condition. -/
def noSide : SumcheckRound.Ctx Unit NoOracle Unit → Prop := fun _ ↦ True

/-- Three distinct nodes. -/
def nodes : Fin 3 → E := ![0, 1, y]

/-- Unit weights on two coordinates. -/
def wtOne : CoordWeights E Unit 2 := unitWeights

/-! ## The plain sumcheck, by hand -/

/-- The claimed sum. -/
def T : E := weightedSum V wtOne ctx

-- The claim is the sum of `t₁ · t₂` over the cube.
#guard T = a * b + b * 1 + c * a + 1 * c

def s0 : SumcheckRound.Stmt Unit E 0 := ((), (#v[], T))
def q0 : SumcheckRound.Message E 2 := roundPoly V wtOne nodes ctx 0 #v[]

-- The honest polynomial passes the check `q(0) + q(1) = T`.
#guard SumcheckRound.check 0 (domain wtOne) s0 q0
#guard SumcheckRound.evaluate 2 q0 0 + SumcheckRound.evaluate 2 q0 1 = T

def r0 : E := c
def s1 : SumcheckRound.Stmt Unit E 1 :=
  SumcheckRound.next 0 s0 (SumcheckRound.evaluate 2 q0 r0) r0

-- The first challenge is the highest coordinate: the new claim sums over coordinate 0 with
-- coordinate 1 at `r0`.
#guard s1.2.2 = V.summand ctx #v[0, r0] + V.summand ctx #v[1, r0]
#guard s1.2.2 = claim V wtOne ctx 1 #v[r0]

def q1 : SumcheckRound.Message E 2 := roundPoly V wtOne nodes ctx 1 s1.2.1

#guard SumcheckRound.check 1 (domain wtOne) s1 q1

def r1 : E := a + 1
def s2 : SumcheckRound.Stmt Unit E 2 :=
  SumcheckRound.next 1 s1 (SumcheckRound.evaluate 2 q1 r1) r1

-- The final claim is the summand at the final point `(r1, r0)`, coordinate 0 the last challenge.
#guard s2.2.2 = V.summand ctx #v[r1, r0]

/-- The honest values at the final point. -/
def vals : Vector E 2 := V.values ctx s2.2.1.reverse

#guard finalCheck V s2 vals
#guard (finalOut s2 vals).2.1.toList = [r1, r0]
-- The output relation: each value is its table's extension at the point.
#guard V.values ((((finalOut s2 vals).1, noO), ())) (finalOut s2 vals).2.1 = (finalOut s2 vals).2.2
#guard vals[0] = evalMle t₁ #v[r1, r0] ∧ vals[1] = evalMle t₂ #v[r1, r0]

/-! ## What is rejected -/

-- A round polynomial with its top coefficient changed.
#guard ¬ SumcheckRound.check 0 (domain wtOne) s0 (q0.set 2 (q0[2] + 1))
-- A wrong claim.
#guard ¬ SumcheckRound.check 0 (domain wtOne) ((), (#v[], T + 1)) q0
-- Values other than the tables' at the final point.
#guard ¬ finalCheck V s2 (vals.set 0 (vals[0] + 1))

/-! ## The normalized sumcheck, by hand -/

/-- The point of the equality polynomial. -/
def p : Vector E 2 := #v[a, c]

/-- The weights of `eq(p, ·)`. -/
def wtEq : CoordWeights E Unit 2 := eqWeights fun _ ↦ p

def Tn : E := weightedSum V wtEq ctx

-- The claim is `Σ_x eq(p, x) · t₁(x) t₂(x)`, coordinate 0 the low bit.
#guard Tn = (1 - a) * (1 - c) * (a * b) + a * (1 - c) * (b * 1) + (1 - a) * c * (c * a) +
  a * c * (1 * c)

def n0 : SumcheckRound.Stmt Unit E 0 := ((), (#v[], Tn))
def h0 : SumcheckRound.Message E 2 := roundPoly V wtEq nodes ctx 0 #v[]

-- The round binds coordinate 1 first: the check weighs `h(0)` and `h(1)` by `1 - p_1`, `p_1`.
#guard SumcheckRound.check 0 (domain wtEq) n0 h0
#guard (1 - c) * SumcheckRound.evaluate 2 h0 0 + c * SumcheckRound.evaluate 2 h0 1 = Tn

def n1 : SumcheckRound.Stmt Unit E 1 :=
  SumcheckRound.next 0 n0 (SumcheckRound.evaluate 2 h0 r0) r0
def h1 : SumcheckRound.Message E 2 := roundPoly V wtEq nodes ctx 1 n1.2.1

#guard SumcheckRound.check 1 (domain wtEq) n1 h1
#guard ¬ SumcheckRound.check 1 (domain wtEq) n1 (h1.set 0 (h1[0] + 1))

def n2 : SumcheckRound.Stmt Unit E 2 :=
  SumcheckRound.next 1 n1 (SumcheckRound.evaluate 2 h1 r1) r1

-- The final claim is the summand at the challenges, with no equality factor.
#guard n2.2.2 = V.summand ctx #v[r1, r0]
#guard finalCheck V n2 (V.values ctx n2.2.1.reverse)

/-! ## The wire -/

-- The wire carries `d` of the `d + 1` coefficients. With unit weights the check does not see
-- `c_0` in characteristic two (its weight is `1 + 1 = 0`), so the plain round drops `c_1`, whose
-- weight is `1`; with the weights `1 - r, r` the weight of `c_0` is `1`, so the normalized round
-- drops `c_0`.
#guard coeffWeight (domain wtOne () 0) 0 = 0 ∧ coeffWeight (domain wtOne () 0) 1 = 1
#guard coeffWeight (domain wtEq () 0) 0 = 1

-- The plain round's wire is `c_0, c_2`; the decoder recomputes `c_1 = claim + c_2` (the Rust's
-- `claim + sum_from(2)`) and returns the honest message.
#guard encodeWire 1 q0 = #v[q0[0], q0[2]]
#guard decodeWire (domain wtOne () 0) 1 T #v[q0[0], q0[2]] = q0
#guard (decodeWire (domain wtOne () 0) 1 T #v[q0[0], q0[2]])[1] = T + q0[2]
-- The normalized round's wire is `c_1, c_2`; `c_0 = claim + r·(c_1 + c_2)` with `r = p_1`, the
-- coordinate the first round binds (the Rust's `claim + r * sum_from(1)`).
#guard decodeWire (domain wtEq () 0) 0 Tn #v[h0[1], h0[2]] = h0
#guard (decodeWire (domain wtEq () 0) 0 Tn #v[h0[1], h0[2]])[0] = Tn + c * (h0[1] + h0[2])
-- Any wire decodes to a message that passes the check, and the wire is read back unchanged.
#guard SumcheckRound.check 0 (domain wtOne) s0 (decodeWire (domain wtOne () 0) 1 T #v[a, b])
#guard encodeWire 1 (decodeWire (domain wtOne () 0) 1 T #v[a, b]) = #v[a, b]
-- A wrong wire decodes to a message other than the honest one.
#guard decodeWire (domain wtOne () 0) 1 T #v[q0[0], q0[2] + 1] ≠ q0

/-- A third table, for a cubic summand like the table sumcheck's. -/
def t₃ : CMlPolynomialEval E 2 := #v[c, a, 1, b]

/-- The cubic virtual polynomial `t₁ · t₂ · t₃`. -/
def V3 : Virtual E Unit NoOracle Unit 2 3 where
  tables := fun _ ↦ ![t₁, t₂, t₃]
  formula := fun _ _ v ↦ v[0] * v[1] * v[2]

/-- Four distinct nodes. -/
def nodes4 : Fin 4 → E := ![0, 1, y, y + 1]

def T3 : E := weightedSum V3 wtOne ctx
def k0 : SumcheckRound.Message E 3 := roundPoly V3 wtOne nodes4 ctx 0 #v[]

-- The cubic round, as the table sumcheck sends it: the wire is `c_0, c_2, c_3`, and the decoder
-- recomputes `c_1 = claim + c_2 + c_3`.
#guard SumcheckRound.check 0 (domain wtOne) ((), (#v[], T3)) k0
#guard decodeWire (domain wtOne () 0) 1 T3 #v[k0[0], k0[2], k0[3]] = k0
#guard (decodeWire (domain wtOne () 0) 1 T3 #v[k0[0], k0[2], k0[3]])[1] = T3 + k0[2] + k0[3]

/-! ## The slot of the table sumcheck -/

/-- The public data of the table sumcheck after its batching challenge. -/
abbrev TableX : Type := (Toy.toy.Stmt × BusOut Toy.toy) × E

/-- A plain virtual polynomial of degree three over the toy's stack: the three columns of its
table, lifted to `E`, under a formula of the shape of a constraint. -/
def Vtoy : Virtual E TableX (TheOracle Toy.toy) Unit Toy.toy.τmax Toy.toy.tableColumns where
  tables := fun ctx i ↦ CMlPolynomialEval.map (algebraMap K E)
    (Toy.slice (ctx.1.2 0) ⟨0, ⟨i.val, i.isLt⟩⟩).values
  formula := fun _ _ v ↦ v[2] * v[2] + v[2]

/-- The table phase's output, here the public statement and the values: the last message's output
map makes the phase's own statement, not the sumcheck's. -/
def tableOut (s : SumcheckRound.Stmt TableX E Toy.toy.τmax) (v : Vector E Toy.toy.tableColumns) :
    Toy.toy.Stmt × Vector E Toy.toy.tableColumns :=
  (s.1.1.1, v)

/-- The table sumcheck's shape, at the table slot by definitional equality: the batching
challenge, then the rounds and the last message of the plain sumcheck. -/
def tableShape : Typed.Def (TheOracle Toy.toy) (Toy.toy.Stmt × BusOut Toy.toy) Unit
    (Toy.toy.Stmt × Vector E Toy.toy.tableColumns) Unit (tableSlot Toy.toy) :=
  ((Typed.sampleChallenge (TheOracle Toy.toy) E (fun _ ↦ true)
      fun s ξ ↦ (((s, ξ), (#v[], 0)) : SumcheckRound.Stmt TableX E 0)).append
    (rounds Vtoy unitWeights nodes4)).append (final Vtoy tableOut)

/-! ## Completeness -/

theorem y_ne_zero : y ≠ 0 := by
  intro h
  have h3 := y_pow_three
  rw [h] at h3
  simp at h3

theorem y_ne_one : y ≠ 1 := by
  intro h
  have h3 := y_pow_three
  rw [h] at h3
  simp at h3

theorem nodes_injective : Function.Injective nodes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [nodes, y_ne_zero, y_ne_one, y_ne_zero.symm, y_ne_one.symm]

theorem V_degree : ∀ ctx, IndividualDegreeLE (V.summand ctx) 2 := fun ctx k ↦ by
  have e : V.summand ctx = fun z ↦ evalMle t₁ z * evalMle t₂ z := by
    funext z
    simp only [Virtual.summand, Virtual.values, V, Vector.getElem_ofFn]
    rfl
  rw [e]
  exact (DegreeLEAt.evalMle t₁).mul (DegreeLEAt.evalMle t₂)

/-! ## Degree in each variable -/

/-- A table on the low coordinate, lifted to two: it ignores the high coordinate. -/
def tLift : CMlPolynomialEval E 2 := #v[a, b, a, b]

/-- The summand of the table sumcheck's shape on two variables, for a table of height one joining
in the second round: the padding `z_1`, the equality factor `eq(a, z_0)`, and the constraint
`v² + v` on the lifted table. -/
def tableShaped (z : Vector E 2) : E :=
  z[1] * ((1 - a) * (1 - z[0]) + a * z[0]) *
    (evalMle tLift z * evalMle tLift z + evalMle tLift z)

-- The factors' degrees in every variable add up to `1 + 1 + 2 = 4`, but in each variable the
-- summand has degree three: the padding and the equality factor are in different variables.
theorem tableShaped_degree : IndividualDegreeLE tableShaped 3 := by
  intro k
  have hc : DegreeLEAt (fun z : Vector E 2 ↦
      evalMle tLift z * evalMle tLift z + evalMle tLift z) k 2 :=
    ((DegreeLEAt.evalMle tLift).mul (DegreeLEAt.evalMle tLift)).add
      ((DegreeLEAt.evalMle tLift).mono (by omega))
  by_cases hk : k < 2
  · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · -- In `z_0`: the padding has degree `0`, the equality factor `1`, the constraint `2`.
      have hz : DegreeLEAt (fun z : Vector E 2 ↦ z[0]) 0 1 := DegreeLEAt.coord_self (by omega)
      have he : DegreeLEAt (fun z : Vector E 2 ↦ (1 - a) * (1 - z[0]) + a * z[0]) 0 1 :=
        (((DegreeLEAt.const (1 - a)).mul
            (((DegreeLEAt.const 1).mono (Nat.zero_le 1)).sub hz)).mono (by omega)).add
          (((DegreeLEAt.const a).mul hz).mono (by omega))
      exact (((DegreeLEAt.coord_ne (n := 2) (by omega) (by omega)).mul he).mul hc).mono
        (by omega)
    · -- In `z_1`: the padding has degree `1`, the equality factor `0`, the constraint `2`.
      have he : DegreeLEAt (fun z : Vector E 2 ↦ (1 - a) * (1 - z[0]) + a * z[0]) 1 0 :=
        DegreeLEAt.of_set_eq fun z hk x ↦ by
          rw [Vector.getElem_set_ne hk (by omega) (by omega)]
      exact (((DegreeLEAt.coord_self (n := 2) (by omega)).mul he).mul hc).mono (by omega)
  · exact fun _ hk' ↦ absurd hk' hk

/-! ## The final check is load-bearing -/

-- For every statement, the one with its claim moved off the summand at its point has no
-- security for the last message without its check, at any error: the true values carry it into
-- the output relation.
example {err : Typed.Errors (Typed.sayTree (Vector E 2)) (Typed.sayRoles _)}
    (S : Typed.Security (Typed.sendChecked NoOracle (Vector E 2)
      (fun p ↦ V.values (SumcheckRound.ctxOf p) p.1.1.2.1.reverse) (fun _ _ ↦ true)
      (finalOut (X := Unit) (F := E) (n := 2) (m := 2)))
      (SumcheckRound.rel (family V wtOne nodes noSide) 2) (relOut V noSide) err)
    (s : SumcheckRound.Stmt Unit E 2) : False :=
  Typed.sendChecked_no_security S ((), (s.2.1, V.summand ctx s.2.1.reverse + 1)) noO
    (fun _ h ↦ one_ne_zero (add_eq_left.mp ((mem_rel_self V wtOne nodes noSide _).mp h).2))
    (V.values ctx s.2.1.reverse) rfl ()
    ⟨rfl, trivial⟩

-- Completeness of both variants on `t₁ · t₂`.
theorem completePlain :
    Typed.Complete (plain V nodes) (relIn V unitWeights noSide) (relOut V noSide) :=
  weightedComplete V unitWeights nodes noSide V_degree nodes_injective

theorem completeNormalized :
    Typed.Complete (normalized V (fun _ ↦ p) nodes) (relIn V wtEq noSide) (relOut V noSide) :=
  weightedComplete V (eqWeights fun _ ↦ p) nodes noSide V_degree nodes_injective

/-- A side condition: the first entry of the first table is `a`. The sumcheck carries it, in its
input and output relations, without reading it. -/
def firstIsA : SumcheckRound.Ctx Unit NoOracle Unit → Prop := fun ctx ↦ (V.tables ctx 0)[0] = a

-- The honest statement meets the input relation with the side condition, which holds of `t₁`.
example : ((((), (#v[], T)), noO), ()) ∈ relIn V wtOne firstIsA := ⟨rfl, rfl⟩

-- Completeness carries the side condition into the output relation.
theorem completeSide :
    Typed.Complete (plain V nodes) (relIn V unitWeights firstIsA) (relOut V firstIsA) :=
  weightedComplete V unitWeights nodes firstIsA V_degree nodes_injective

/-! ## Knowledge soundness -/

open scoped NNReal

/-- Knowledge soundness of the plain sumcheck on `t₁ · t₂`, at `overE 2` per round; a plain
definition, so it computes. -/
def securityPlain :
    Typed.Security (plain V nodes) (relIn V unitWeights noSide) (relOut V noSide)
      (Typed.Errors.append (Typed.roundsSlot E 2 2).tree (Typed.roundsSlot E 2 2).roles
        (Typed.roundsErrors E 2 (overE 2) 2) (Typed.sayErrors (Vector E 2))) :=
  (weightedSecurity V unitWeights nodes noSide V_degree nodes_injective).mono
    (Typed.Errors.Le.append _ _ (Typed.roundsErrors_le E 2
      (le_of_eq (natCast_div_card_eq_overE 2)) 2) (Typed.Errors.Le.refl _ _ _))

/-- Knowledge soundness of the normalized sumcheck on `t₁ · t₂` against `eq(p, ·)`. -/
def securityNormalized :
    Typed.Security (normalized V (fun _ ↦ p) nodes) (relIn V wtEq noSide) (relOut V noSide)
      (Typed.Errors.append (Typed.roundsSlot E 2 2).tree (Typed.roundsSlot E 2 2).roles
        (Typed.roundsErrors E 2 (overE 2) 2) (Typed.sayErrors (Vector E 2))) :=
  (weightedSecurity V (eqWeights fun _ ↦ p) nodes noSide V_degree nodes_injective).mono
    (Typed.Errors.Le.append _ _ (Typed.roundsErrors_le E 2
      (le_of_eq (natCast_div_card_eq_overE 2)) 2) (Typed.Errors.Le.refl _ _ _))

theorem y_add_one_ne_zero : y + 1 ≠ 0 := by
  intro h
  have h3 := y_pow_three
  rw [h] at h3
  exact y_ne_zero (pow_eq_zero_iff (by norm_num) |>.mp h3)

theorem nodes4_injective : Function.Injective nodes4 := by
  have h1 : y + 1 ≠ 1 := fun h ↦ y_ne_zero (add_eq_right.mp h)
  have h2 : y + 1 ≠ y := fun h ↦ one_ne_zero (add_eq_left.mp h)
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [nodes4, y_ne_zero, y_ne_one, y_ne_zero.symm, y_ne_one.symm, y_add_one_ne_zero,
      y_add_one_ne_zero.symm, h1.symm, h2.symm]

theorem Vtoy_degree : ∀ ctx, IndividualDegreeLE (Vtoy.summand ctx) 3 := fun ctx k ↦ by
  have h2 : 2 < Toy.toy.tableColumns := by decide
  have e : Vtoy.summand ctx = fun z ↦
      evalMle (Vtoy.tables ctx ⟨2, h2⟩) z * evalMle (Vtoy.tables ctx ⟨2, h2⟩) z +
        evalMle (Vtoy.tables ctx ⟨2, h2⟩) z := by
    funext z
    simp only [Virtual.summand, Virtual.values, Vtoy, Vector.getElem_ofFn]
  have hv := DegreeLEAt.evalMle (Vtoy.tables ctx ⟨2, h2⟩) (k := k)
  rw [e]
  exact ((hv.mul hv).add (hv.mono (by omega))).mono (by omega)

/-- The rounds of the cubic plain sumcheck over the toy's stack meet the table slot's per-round
error, `overE 3`. -/
def tableRoundsSecurity :
    Typed.Security (rounds Vtoy unitWeights nodes4) (relIn Vtoy unitWeights fun _ ↦ True)
      (SumcheckRound.rel (family Vtoy unitWeights nodes4 fun _ ↦ True) Toy.toy.τmax)
      (Typed.roundsErrors E 3 (overE 3) Toy.toy.τmax) :=
  (roundsSecurity Vtoy unitWeights nodes4 _ Vtoy_degree nodes4_injective).mono
    (Typed.roundsErrors_le E 3 (le_of_eq (natCast_div_card_eq_overE 3)) _)

/-- The family of the plain sumcheck on `t₁ · t₂`. -/
abbrev Φ : SumcheckRound.Family E Unit NoOracle Unit 2 := family V wtOne nodes noSide

/-- The first round's next statement, from a recorded polynomial and a challenge. -/
def nextClaim (p : SumcheckRound.MidStmt Unit E 0 2) (c : E) : SumcheckRound.Stmt Unit E 1 :=
  SumcheckRound.next 0 p.1 (SumcheckRound.evaluate 2 p.2 c) c

/-- The round check is load-bearing: the first round's challenge drawn without checking the
polynomial has no knowledge error below one, whatever the extractor, since from a running claim
off by one the honest polynomial is carried into the next relation at every challenge. -/
theorem unchecked_round_one_le {e : ℝ≥0}
    (S : Typed.Security (Typed.sampleChallenge NoOracle E (fun _ ↦ true) nextClaim)
      (SumcheckRound.relMid Φ 0) (SumcheckRound.rel Φ 1) (Typed.drawErrors E e)) : 1 ≤ e :=
  Typed.sampleChallenge_one_le S
    (((), (#v[], Φ.claim ctx 0 #v[] + 1)), Φ.poly ctx 0 #v[]) noO
    (fun _ h ↦ one_ne_zero (add_eq_left.mp h.1.2)) rfl fun c ↦
      ⟨(), trivial, (family_honest V wtOne nodes noSide V_degree nodes_injective).next ctx 0 #v[] c
        (by decide)⟩

/-- The wire: a round read on the wire, `d` of its coefficients, keeps the round's security at
the same errors. -/
example (S : Typed.Security (SumcheckRound.round Φ.poly 0 Φ.weight) (SumcheckRound.rel Φ 0)
      (SumcheckRound.rel Φ 1) (Typed.roundErrors E 2 (overE 2))) :
    Nonempty (Typed.Security ((SumcheckRound.round Φ.poly 0 Φ.weight).decode
        (fun s w ↦ decodeWire (Φ.weight s.1 0) 1 s.2.2 w) fun _ q ↦ encodeWire 1 q)
      (SumcheckRound.rel Φ 0) (SumcheckRound.rel Φ 1) fun _ ↦ Typed.drawErrors E (overE 2)) :=
  ⟨transport S 1⟩

end LeanVMTests.Protocol.Sumcheck
