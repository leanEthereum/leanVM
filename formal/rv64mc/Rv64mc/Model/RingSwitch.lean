module

public import Rv64mc.Model.Transcript

/-!
# `ring_switch.rs` as the Rust computes it

Mirrors of `crates/verifier/src/ring_switch.rs`: `frobenius_8`, `ring_psi`, `ring_target`,
`ring_coefficients`, `ring_weight`, `RingWeight::evaluate` and `ring_switch`, each proved equal to
its counterpart in `Statement/LeanVmVerifier.lean` (`ring_switch` simulating `ringSwitch`).
Conventions as in `Model.Multilinear`: an `E` is the statement's, `E::square` is `squareE`, a
`usize` loop bound is `ℕ` (it never wraps here: `8 p` for `p < 8`). An `assert!` is an `Option`;
the mirror may return anything where the Rust panics (`f[p]` past the end is `getD`), and fails
only where the Rust fails.
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `E::square` iterated `n` times, the fold of `frobenius_8`. -/
theorem foldl_squareE (n : ℕ) (v : E) :
    (List.range n).foldl (fun v _ ↦ squareE v) v = v ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, squareE_eq,
      ← pow_mul, pow_succ]

/-- `frobenius_8(value, p)`: `(0..RING_MAP_WIDTH * p).fold(value, |v, _| v.square())`. -/
def frobenius8Rust (value : E) (p : ℕ) : E := (List.range (8 * p)).foldl (fun v _ ↦ squareE v) value

theorem frobenius8Rust_eq (value : E) (p : ℕ) : frobenius8Rust value p = frobenius8 value p :=
  foldl_squareE _ _

/-- `ring_psi(value, g)`: `psi += g_b * power; power = power.square()` from `(ZERO, value)`. -/
def ringPsiRust (value : E) (g : List E) : E :=
  (g.foldl (fun (acc : E × E) gB ↦ (acc.1 + gB * acc.2, squareE acc.2)) (0, value)).1

theorem ringPsiRust_eq (value : E) (g : List E) : ringPsiRust value g = ringPsi value g := by
  simp only [ringPsiRust, ringPsi, squareE_eq, sq]

/-- `ring_target(s, f, g)`: the images, then for `p` in `(0..8).rev()`, `z = frobenius_8(z, 1)` and
`target += f[p] * frobenius_8(poly_eval(&images, z), p)`, from `(ZERO, GEN)`. -/
def ringTargetRust (s f g : List E) : E :=
  let images := s.map (ringPsiRust · g)
  ((List.range 8).reverse.foldl (fun (acc : E × E) p ↦
    let z := frobenius8Rust acc.2 1
    (acc.1 + f.getD p 0 * frobenius8Rust (polyEvalRust images z) p, z)) (0, gen)).1

theorem ringTargetRust_eq (s f g : List E) : ringTargetRust s f g = ringTarget s f g := by
  simp only [ringTargetRust, ringTarget, frobenius8Rust_eq, polyEvalRust_eq, ringPsiRust_eq,
    ringMapWidth]

/-- `ring_coefficients(f, g)`: per `f_p`, extend by `f_p * g_b` over the powers, then raise every
power by `frobenius_8(·, 1)`. -/
def ringCoefficientsRust (f g : List E) : List E :=
  (f.foldl (fun (acc : List E × List E) fP ↦
    (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8Rust · 1))) ([], g)).1

theorem ringCoefficientsRust_eq (f g : List E) :
    ringCoefficientsRust f g = ringCoefficients f g := by
  simp only [ringCoefficientsRust, ringCoefficients, frobenius8Rust_eq]

/-- `ring_weight`'s inner loop over `frobenius.iter_mut().zip(r_prime)`: `product *= ONE + *value +
challenge`, then `*value = value.square()`; the product and the updated `frobenius`. -/
def ringWeightInner : E → List E → List E → E × List E
  | product, value :: values, challenge :: challenges =>
    let rest := ringWeightInner (product * (1 + value + challenge)) values challenges
    (rest.1, squareE value :: rest.2)
  | product, values, _ => (product, values)

/-- One coefficient of `ring_weight`: `total += product` after the inner loop from `c`. -/
def ringWeightPass (rPrime : List E) (acc : E × List E) (c : E) : E × List E :=
  let inner := ringWeightInner c acc.2 rPrime
  (acc.1 + inner.1, inner.2)

/-- `ring_weight(r, r_prime, coefficients)`: `assert_eq!` of the lengths, then a pass per
coefficient from `(ZERO, r.to_vec())`. -/
def ringWeightRust (r rPrime coefficients : List E) : Option E :=
  if r.length = rPrime.length then some (coefficients.foldl (ringWeightPass rPrime) (0, r)).1
  else none

theorem ringWeightInner_eq : ∀ (product : E) (values rPrime : List E),
    values.length = rPrime.length →
    ringWeightInner product values rPrime =
      ((List.zip values rPrime).foldl (fun product (value, challenge) ↦
        product * (1 + value + challenge)) product, values.map fun value ↦ value * value)
  | _, [], [], _ => rfl
  | product, v :: vs, c :: cs, h => by
    rw [ringWeightInner, ringWeightInner_eq _ vs cs (by simpa using h), squareE_eq, sq]
    rfl

/-- **`ring_weight` is `ringWeight`**, for a point and an opening point of one length (the
weight's point and the opening's, both of the stack's or the window's variables). -/
theorem ringWeightRust_eq {r rPrime : List E} (h : r.length = rPrime.length) (coefficients : List E) :
    ringWeightRust r rPrime coefficients = some (ringWeight r rPrime coefficients) := by
  rw [ringWeightRust, ite_eq_left h, ringWeight, Option.some.injEq]
  suffices ∀ (acc : E × List E), acc.2.length = rPrime.length →
      coefficients.foldl (ringWeightPass rPrime) acc =
        coefficients.foldl (fun (acc : E × List E) c ↦
          let product := (List.zip acc.2 rPrime).foldl
            (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
          (acc.1 + product, acc.2.map fun value ↦ value * value)) acc from
    congrArg Prod.fst (this (0, r) h)
  induction coefficients with
  | nil => intro acc _; rfl
  | cons c cs ih =>
    intro acc hacc
    rw [List.foldl_cons, List.foldl_cons, ringWeightPass, ringWeightInner_eq _ _ _ hacc]
    exact ih _ (by simpa using hacc)

/-- `RingWeight { point, coefficients }`. -/
structure RingWeightRust where
  /-- `point`. -/
  point : List E
  /-- `coefficients`. -/
  coefficients : List E

/-- `RingWeight::evaluate(r_prime)`. -/
def RingWeightRust.evaluate (w : RingWeightRust) (rPrime : List E) : Option E :=
  ringWeightRust w.point rPrime w.coefficients

/-- `ring_switch(point, s, transcript)`: `grind_check(BATCH_GRINDING_BITS)?`, sixteen samples
split at eight, the coefficients and the target. -/
def ringSwitchRust (point s : List E) : TM (E × RingWeightRust) := do
  TM.grindCheck 13
  let challenges ← TM.samples 16
  let f := challenges.take 8
  let g := challenges.drop 8
  let coefficients := ringCoefficientsRust f g
  let target := ringTargetRust s f g
  Pure.pure (target, ⟨point, coefficients⟩)

/-- **`ring_switch` runs `ringSwitch`**: the same target, and a weight that evaluates, at every
opening point of the claim point's length, to the statement's. -/
theorem SimR.ringSwitch (point s : List E) :
    SimR (ringSwitchRust point s) (ringSwitch point s) fun a b ↦
      a.1 = b.1 ∧ ∀ x, x.length = point.length → a.2.evaluate x = some (b.2 x) := by
  unfold ringSwitchRust LeanVM.Protocol.Verifier.ringSwitch
  refine SimR.bindEq (Sim.grindCheck _) fun _ ↦ SimR.bindEq (Sim.samples _) fun ch ↦
    SimR.pure ⟨?_, fun x hx ↦ ?_⟩
  · simp only [ringTargetRust_eq, ringMapWidth]
  · simp only [RingWeightRust.evaluate, ringWeightRust_eq hx.symm, ringCoefficientsRust_eq,
      ringMapWidth]

end

end Rv64mc.Model
