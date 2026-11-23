module

public import NativeVm.Model.Claims

/-!
# `ringWeight` turn by turn

`ringWeight r r' c` folds `wStep r'` over the coefficients from `(0, r)`: after `k` of them
(`accW r r' c k`) the total and the powers `r_n^(2^k)`, their number `|r|` (`size_accW`). A
turn's product is `prodOf`, factor by factor `prodPart` (`prodPart_succ`), `c` itself when
`r'` is empty (`prodOf_nil`); with `r` empty the total is the coefficients' sum (`accW_nil`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeVm.Model

@[expose] public section

/-- The factor of a turn's product: `p · (1 + v + ch)`. -/
def fac (p : EW) (vc : EW × EW) : EW := p * (1 + vc.1 + vc.2)

/-- A turn's product: `c · Π_n (1 + P_n + r'_n)`. -/
def prodOf (P r' : Array EW) (c : EW) : EW := (P.zip r').foldl fac c

/-- The product's first `i` factors. -/
def prodPart (P r' : Array EW) (c : EW) (i : Nat) : EW := ((P.zip r').toList.take i).foldl fac c

/-- A turn: the product added to the total, the powers squared. -/
def wStep (r' : Array EW) (acc : EW × Array EW) (c : EW) : EW × Array EW :=
  (acc.1 + prodOf acc.2 r' c, acc.2.map fun v ↦ v * v)

/-- The total and the powers after the first `k` coefficients. -/
def accW (r r' c : Array EW) (k : Nat) : EW × Array EW := (c.toList.take k).foldl (wStep r') (0, r)

end

public section

variable {r r' c P : Array EW} {k i : Nat} {c' : EW}

theorem ringWeight_eq : ringWeight r r' c = (accW r r' c c.size).1 := by
  unfold accW
  rw [← Array.length_toList, List.take_length, Array.foldl_toList]
  rfl

theorem accW_succ (hk : k < c.size) : accW r r' c (k + 1) = wStep r' (accW r r' c k) c[k] := by
  unfold accW
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simpa using hk)]
  simp

theorem accW_zero : accW r r' c 0 = (0, r) := rfl

theorem size_accW : (accW r r' c k).2.size = r.size := by
  unfold accW
  generalize c.toList.take k = l
  suffices ∀ acc : EW × Array EW, (l.foldl (wStep r') acc).2.size = acc.2.size from this _
  induction l with
  | nil => intro acc; rfl
  | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp [wStep]

theorem prodPart_zero : prodPart P r' c' 0 = c' := rfl

theorem prodPart_succ {c' : EW} (hi : i < P.size) (hi' : i < r'.size) :
    prodPart P r' c' (i + 1) = prodPart P r' c' i * (1 + P[i] + r'[i]) := by
  unfold prodPart
  rw [List.take_add_one, List.foldl_append,
    List.getElem?_eq_getElem (by simp [Array.length_toList]; omega)]
  simp [fac]

theorem prodOf_eq {c' : EW} : prodOf P r' c' = prodPart P r' c' (min P.size r'.size) := by
  unfold prodOf prodPart
  rw [← Array.foldl_toList]
  congr
  rw [List.take_of_length_le]
  simp

theorem prodOf_nil {c' : EW} : prodOf P #[] c' = c' := by
  unfold prodOf
  rw [← Array.foldl_toList, Array.toList_zip]
  simp

theorem wStep_nil {acc : EW × Array EW} {c' : EW} (h : acc.2 = #[]) :
    wStep r' acc c' = (acc.1 + c', #[]) := by
  obtain ⟨t, p⟩ := acc
  simp only at h
  subst h
  unfold wStep prodOf
  rw [← Array.foldl_toList, Array.toList_zip]
  simp

/-- With `r` empty: the coefficients' sum. -/
theorem accW_nil (hk : k ≤ c.size) :
    accW #[] r' c k = ((c.toList.take k).foldl (· + ·) 0, #[]) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [accW_succ (by omega), ih (by omega), wStep_nil rfl, List.take_add_one, List.foldl_append,
      List.getElem?_eq_getElem (by simp; omega)]
    simp

end

end NativeRustcVmArm.Ring.Weight
