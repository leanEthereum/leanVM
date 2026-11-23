module

public import NativeVm.Model.RingSwitch

/-!
# Ring switching's functions, as the Rust computes them

The sum of `E` elements (limb-wise `xor`) is commutative and associative with `0`
(`EW.zero_add'`, `EW.add_comm'`, `EW.add_assoc'`). `ring_psi`'s loop is a left fold over `g`
(`ringPsi_toArray`), one element at a time (`psi_take_succ`).
-/

namespace NativeRustcVm.Ring

open NativeVm.Model

@[expose] public section

/-- A turn of `ringPsi`'s loop: the term `g_b · v^(2^b)` added, the power squared. -/
def psiStep (acc : EW × EW) (gB : EW) : EW × EW := (acc.1 + gB * acc.2, acc.2 * acc.2)

/-- A turn of `ringCoefficients`' loop: the row `f_p · G`, then `G`'s Frobenius images. -/
def coeffStep (acc : Array EW × Array EW) (fP : EW) : Array EW × Array EW :=
  (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8 · 1))

/-- The point of `ringTarget`'s turn `8 − n`: `gen` squared `8 n` times. -/
def zz : Nat → EW
  | 0 => gen
  | n + 1 => EW.sqIter 8 (zz n)

/-- `ringTarget`'s term `p`: `f_p · (Σ_i z^i Ψ(s_i))^(2^(8p))`, `z` the turn's point. -/
def tTerm (images f : Array EW) (p : Nat) : EW :=
  f.getD p 0 * EW.sqIter (8 * p) (polyEval images (zz (8 - p)))

/-- `ringCoefficients`' loop after `p` turns. -/
def rcAt (f : List EW) (g : Array EW) (p : Nat) : Array EW × Array EW :=
  (f.take p).foldl coeffStep (#[], g)

end

public section

theorem EW.add_def (x y : EW) : x + y = ⟨x.c0 ^^^ y.c0, x.c1 ^^^ y.c1⟩ := rfl

theorem EW.zero_add' (x : EW) : (0 : EW) + x = x := by
  rw [EW.add_def]
  show (⟨0 ^^^ x.c0, 0 ^^^ x.c1⟩ : EW) = x
  simp

theorem EW.add_comm' (x y : EW) : x + y = y + x := by
  rw [EW.add_def, EW.add_def, UInt64.xor_comm x.c0, UInt64.xor_comm x.c1]

theorem EW.add_assoc' (x y z : EW) : x + y + z = x + (y + z) := by
  simp only [EW.add_def, UInt64.xor_assoc]

theorem ringPsi_toArray (v : EW) (g : List EW) :
    ringPsi v g.toArray = (g.foldl psiStep (0, v)).1 := by
  simp only [ringPsi, List.foldl_toArray']
  rfl

theorem psi_take_succ (v : EW) (g : List EW) {j : Nat} (hj : j < g.length) :
    (g.take (j + 1)).foldl psiStep (0, v) = psiStep ((g.take j).foldl psiStep (0, v)) g[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.foldl_append]
  rfl

theorem frobenius8_one (x : EW) : frobenius8 x 1 = EW.sqIter 8 x := rfl

/-- **`ringTarget`, unrolled**: its terms from `p = 7` down to `0`. -/
theorem ringTarget_eq (s f g : Array EW) :
    ringTarget s f g = let images := s.map (ringPsi · g)
      0 + tTerm images f 7 + tTerm images f 6 + tTerm images f 5 + tTerm images f 4 +
        tTerm images f 3 + tTerm images f 2 + tTerm images f 1 + tTerm images f 0 := by
  have hr : (Array.range LeanVM.Protocol.Verifier.ringMapWidth).reverse.toList = [7, 6, 5, 4, 3, 2, 1, 0] := by
    rw [Array.toList_reverse, Array.toList_range]
    rfl
  simp only [ringTarget, ← Array.foldl_toList, hr, List.foldl_cons, List.foldl_nil]
  rfl

theorem ringCoefficients_toArray (f : List EW) (g : Array EW) :
    ringCoefficients f.toArray g = (f.foldl coeffStep (#[], g)).1 := by
  simp only [ringCoefficients, List.foldl_toArray']
  rfl

theorem rcAt_succ (f : List EW) (g : Array EW) {p : Nat} (hp : p < f.length) :
    rcAt f g (p + 1) = coeffStep (rcAt f g p) f[p] := by
  unfold rcAt
  rw [List.take_add_one, List.getElem?_eq_getElem hp, List.foldl_append]
  rfl

theorem rcAt_zero (f : List EW) (g : Array EW) : rcAt f g 0 = (#[], g) := rfl

theorem rcAt_length (f : List EW) (g : Array EW) :
    (rcAt f g f.length).1 = ringCoefficients f.toArray g := by
  rw [ringCoefficients_toArray, rcAt, List.take_length]

theorem rcAt_size2 (f : List EW) (g : Array EW) : ∀ p, p ≤ f.length → (rcAt f g p).2.size = g.size
  | 0, _ => rfl
  | p + 1, hp => by
    rw [rcAt_succ f g (by omega)]
    simp only [coeffStep, Array.size_map]
    exact rcAt_size2 f g p (by omega)

theorem rcAt_size1 (f : List EW) (g : Array EW) : ∀ p, p ≤ f.length →
    (rcAt f g p).1.size = g.size * p
  | 0, _ => rfl
  | p + 1, hp => by
    rw [rcAt_succ f g (by omega)]
    simp only [coeffStep, Array.size_append, Array.size_map]
    rw [rcAt_size1 f g p (by omega), rcAt_size2 f g p (by omega), Nat.mul_succ]

theorem ringCoefficients_size (f : List EW) (g : Array EW) :
    (ringCoefficients f.toArray g).size = g.size * f.length := by
  rw [← rcAt_length, rcAt_size1 f g _ (le_refl _)]

/-- **`ringSwitch` when the grind fails.** -/
theorem ringSwitch_none {point s : Array EW} {t : TState}
    (h : (grind LeanVM.Parameters.Whir.batchGrindingBits).run t = none) :
    (ringSwitch point s).run t = none := by
  simp [ringSwitch, StateT.run_bind, h]

/-- **`ringSwitch` when the grind succeeds**: the challenges' first `8` are `f`, the rest `g`. -/
theorem ringSwitch_some {point s xs : Array EW} {t t1 t2 : TState}
    (h1 : (grind LeanVM.Parameters.Whir.batchGrindingBits).run t = some ((), t1))
    (h2 : (sampleChallenges 16).run t1 = some (xs, t2)) :
    (ringSwitch point s).run t = some ((ringTarget s (xs.extract 0 8) (xs.extract 8 xs.size),
      point, ringCoefficients (xs.extract 0 8) (xs.extract 8 xs.size)), t2) := by
  simp [ringSwitch, StateT.run_bind, h1, h2, LeanVM.Protocol.Verifier.ringMapWidth]

end

end NativeRustcVm.Ring
