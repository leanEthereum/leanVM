module

public import LeanVM.Cost.Spec
public import LeanVM.Cost.Encoding
public import LeanVM.Cost.FieldMul

/-!
# The compiler's rules

One lemma per Lean construct the compiler translates: from runs of the parts (their code and
price are whatever the compiler found for them) to a run of the whole, its value the encoding of
the Lean expression. The compiler (`Cost/Compiler.lean`) applies them by unification on the Lean
expression, so the code and the price of the whole are what the rule's conclusion names.

* `machineCost`: the price of a function's run, when it has one (`machineCost_eq`: every run has
  that price), the time function of every compiled definition;
* the rules for variables, literals, `let`, constructors, fields, `match` on `Option`, `List`,
  `Bool` and pairs, `if`, and the primitives on `ℕ`, `UInt64`, `K` and `Bool`.
-/

namespace LeanVM.Cost

open LeanVM.Parameters
open LeanVM.Protocol.Verifier (carryless)

@[expose] public section

/-! ## Limbs -/

/-- A word-sized number is one limb. -/
theorem limbs_of_lt {n : ℕ} (h : n < 2 ^ 64) : limbCount n = 1 := by
  unfold limbCount
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 hn)).2 h
    omega

theorem one_le_limbs (n : ℕ) : 1 ≤ limbCount n := by unfold limbCount; omega

/-- At most `L` limbs: below `2^(64 L)`. -/
theorem limbs_le_iff {n L : ℕ} (hL : 1 ≤ L) : limbCount n ≤ L ↔ n < 2 ^ (64 * L) := by
  unfold limbCount
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.log2_zero, Nat.zero_div, Nat.zero_add, hL, Nat.two_pow_pos]
  · rw [← Nat.log2_lt (Nat.pos_iff_ne_zero.1 hn)]; omega

theorem lt_two_pow_limbs (n : ℕ) : n < 2 ^ (64 * limbCount n) :=
  (limbs_le_iff (one_le_limbs n)).1 le_rfl

theorem limbs_mono {a b : ℕ} (h : a ≤ b) : limbCount a ≤ limbCount b :=
  (limbs_le_iff (one_le_limbs b)).2 (Nat.lt_of_le_of_lt h (lt_two_pow_limbs b))

/-- Two limbs: from `2^64` to below `2^128`. -/
theorem limbs_two {n : ℕ} (h : 2 ^ 64 ≤ n) (h' : n < 2 ^ 128) : limbCount n = 2 := by
  have h2 := (limbs_le_iff (n := n) (L := 2) (by omega)).2 h'
  have h1 : ¬ limbCount n ≤ 1 := fun e ↦ absurd ((limbs_le_iff (L := 1) le_rfl).1 e) (by omega)
  omega

theorem limbs_le_max_left {r a : ℕ} {b : ℕ} (h : r ≤ a) :
    limbCount r ≤ max (limbCount a) (limbCount b) :=
  Nat.le_trans (limbs_mono h) (Nat.le_max_left _ _)

theorem limbs_le_mul_left {r a : ℕ} {b : ℕ} (h : r ≤ a) : limbCount r ≤ limbCount a * limbCount b :=
  Nat.le_trans (limbs_mono h) (Nat.le_mul_of_pos_right _ (one_le_limbs b))

theorem limbs_or_le (a b : ℕ) : limbCount (a ||| b) ≤ max (limbCount a) (limbCount b) := by
  have hL : 1 ≤ max (limbCount a) (limbCount b) := Nat.le_trans (one_le_limbs a) (Nat.le_max_left _ _)
  refine (limbs_le_iff hL).2 (Nat.or_lt_two_pow ?_ ?_)
  · exact Nat.lt_of_lt_of_le (lt_two_pow_limbs a)
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.le_max_left _ _)))
  · exact Nat.lt_of_lt_of_le (lt_two_pow_limbs b)
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.le_max_right _ _)))

theorem limbs_xor_le (a b : ℕ) : limbCount (a ^^^ b) ≤ max (limbCount a) (limbCount b) := by
  have hL : 1 ≤ max (limbCount a) (limbCount b) := Nat.le_trans (one_le_limbs a) (Nat.le_max_left _ _)
  refine (limbs_le_iff hL).2 (Nat.xor_lt_two_pow ?_ ?_)
  · exact Nat.lt_of_lt_of_le (lt_two_pow_limbs a)
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.le_max_left _ _)))
  · exact Nat.lt_of_lt_of_le (lt_two_pow_limbs b)
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.le_max_right _ _)))

theorem max_limbs_one (n : ℕ) : max (limbCount n) 1 = limbCount n := Nat.max_eq_left (one_le_limbs n)

theorem max_one_limbs (n : ℕ) : max 1 (limbCount n) = limbCount n := Nat.max_eq_right (one_le_limbs n)

/-- A linear operation whose result has no more limbs than its operands: their larger count. -/
theorem linearlyPriced_le {r a b : ℕ} (h : limbCount r ≤ max (limbCount a) (limbCount b)) :
    linearlyPricedResult r a b = some (.nat r, max (limbCount a) (limbCount b)) := by
  simp [linearlyPricedResult, Nat.max_eq_right h]

/-- A quadratic operation whose result has no more limbs than the product of the operands'. -/
theorem quadraticallyPriced_le {r a b : ℕ} (h : limbCount r ≤ limbCount a * limbCount b) :
    quadraticallyPricedResult r a b = some (.nat r, limbCount a * limbCount b) := by
  simp [quadraticallyPricedResult, Nat.max_eq_right h]

/-- A linear operation on words: `1`. -/
theorem linearlyPriced_one {r a b : ℕ} (hr : r < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    linearlyPricedResult r a b = some (.nat r, 1) := by
  simp [linearlyPricedResult, limbs_of_lt hr, limbs_of_lt ha, limbs_of_lt hb]

theorem u8_lt (x : UInt8) : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le x.toNat_lt (by decide)

theorem uint64_toNat_not (a : UInt64) : (~~~a).toNat = a.toNat ^^^ 18446744073709551615 := by
  rw [← UInt64.toNat_toBitVec, UInt64.toBitVec_not, ← BitVec.xor_allOnes, BitVec.toNat_xor,
    BitVec.toNat_allOnes, UInt64.toNat_toBitVec]

theorem uint64_or_two_pow (a : UInt64) : a.toNat ||| 2 ^ 64 = a.toNat + 2 ^ 64 := by
  have := Nat.two_pow_add_eq_or_of_lt a.toNat_lt 1
  rw [Nat.mul_one] at this
  rw [Nat.or_comm, ← this, Nat.add_comm]

theorem uint64_shiftLeft_eq (a b : UInt64) :
    (a.toNat + 2 ^ 64) <<< (b.toNat &&& 63) &&& 18446744073709551615 = (a <<< b).toNat := by
  rw [UInt64.toNat_shiftLeft, show (18446744073709551615 : ℕ) = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (63 : ℕ) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.add_mul, Nat.mul_comm (2 ^ 64), Nat.add_mul_mod_self_right]

/-! ## The price of a run -/

/-- The price of function `f`'s run on `vs`, if it has one; `0` otherwise. -/
noncomputable def machineCost (P : MachineProgram) (f : ℕ) (vs : List MachineValue) : ℕ :=
  open Classical in
  if h : ∃ r : MachineValue × ℕ, ∃ n, evaluateFunctionBody P n f vs = some r then (Classical.choose h).2 else 0

theorem RunsBody.unique {P : MachineProgram} {f : ℕ} {vs : List MachineValue} {v v' : MachineValue} {c c' : ℕ}
    (h : RunsBody P f vs v c) (h' : RunsBody P f vs v' c') : v = v' ∧ c = c' := by
  obtain ⟨n, h⟩ := h
  obtain ⟨n', h'⟩ := h'
  have e := (evalBody_le (le_max_left n n') h).symm.trans (evalBody_le (le_max_right n n') h')
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  exact e

/-- **Every run has the machine's price.** -/
theorem machineCost_eq {P : MachineProgram} {f : ℕ} {vs : List MachineValue} {v : MachineValue} {c : ℕ}
    (h : RunsBody P f vs v c) : machineCost P f vs = c := by
  have hex : ∃ r : MachineValue × ℕ, ∃ n, evaluateFunctionBody P n f vs = some r := ⟨(v, c), h⟩
  simp only [machineCost, hex, ↓reduceDIte]
  have hs := Classical.choose_spec hex
  exact (RunsBody.unique (v := (Classical.choose hex).1) (c := (Classical.choose hex).2) hs h).2

theorem RunsBody.withMachineCost {P : MachineProgram} {f : ℕ} {vs : List MachineValue} {v : MachineValue} {c : ℕ}
    (h : RunsBody P f vs v c) : RunsBody P f vs v (machineCost P f vs) := by
  rw [machineCost_eq h]; exact h

/-- **Specs by strong induction**: if each run's step uses the spec only at arguments of smaller
measure, the spec holds at every argument, at the machine's price. -/
theorem RunsBody.induction {P : MachineProgram} {i : ℕ} {α : Type} (args : α → List MachineValue) (val : α → MachineValue)
    (m : α → ℕ)
    (step : ∀ x, (∀ y, m y < m x → RunsBody P i (args y) (val y) (machineCost P i (args y))) →
      ∃ c, RunsBody P i (args x) (val x) c) :
    ∀ x, RunsBody P i (args x) (val x) (machineCost P i (args x)) := by
  intro x
  induction h : m x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    obtain ⟨c, hc⟩ := step x fun y hy ↦ ih (m y) (h ▸ hy) y rfl
    exact hc.withMachineCost

/-! ## Closures -/

/-- The price of applying the closure `v` to `vs`: its function's price on its values and `vs`,
and its values put in front of `vs`. -/
noncomputable def appCost (P : MachineProgram) : MachineValue → List MachineValue → ℕ
  | .closure j us, vs => machineCost P j (us ++ vs) + us.length
  | _, _ => 0

/-- The closure `v` applied to `vs` returns `w`. -/
def RunsApp (P : MachineProgram) (v : MachineValue) (vs : List MachineValue) (w : MachineValue) : Prop :=
  ∃ j us, v = .closure j us ∧ RunsBody P j (us ++ vs) w (machineCost P j (us ++ vs))

theorem RunsApp.of_spec {P : MachineProgram} {j : ℕ} {us vs : List MachineValue} {w : MachineValue}
    (h : RunsBody P j (us ++ vs) w (machineCost P j (us ++ vs))) : RunsApp P (.closure j us) vs w :=
  ⟨j, us, rfl, h⟩

/-! ## Encodings -/

section MachineEncoding

variable {α β : Type} [MachineEncoding α] [MachineEncoding β]

@[simp] theorem enc_none : encodeValue (none : Option α) = .constructor 0 [] := rfl
@[simp] theorem enc_some (a : α) : encodeValue (some a) = .constructor 1 [encodeValue a] := rfl
@[simp] theorem enc_nil : encodeValue ([] : List α) = .constructor 0 [] := rfl
@[simp] theorem enc_cons (a : α) (l : List α) : encodeValue (a :: l) = .constructor 1 [encodeValue a, encodeValue l] := rfl
@[simp] theorem enc_pair (a : α) (b : β) : encodeValue (a, b) = .constructor 0 [encodeValue a, encodeValue b] := rfl
@[simp] theorem enc_true : encodeValue true = .constructor 1 [] := rfl
@[simp] theorem enc_false : encodeValue false = .constructor 0 [] := rfl
@[simp] theorem enc_nat (n : ℕ) : encodeValue n = .nat n := rfl
@[simp] theorem enc_word (x : UInt64) : encodeValue x = .nat x.toNat := rfl
@[simp] theorem enc_u8 (x : UInt8) : encodeValue x = .nat x.toNat := rfl
@[simp] theorem enc_k (x : K) : encodeValue x = .nat x.lane.toNat := rfl
@[simp] theorem enc_array (a : Array α) : encodeValue a = .array (a.map encodeValue) := rfl

theorem enc_bool (b : Bool) : encodeValue b = MachineValue.ofBool b := rfl

end MachineEncoding

/-! ## Rules -/

/-! ## Dependent functions of `Fin 3`

The leanSPHINCS signature's layers are a function of the layer whose values' types depend on it
(`(layer : Sphincs.Layer) → Sphincs.LayerSignature layer`); the statement encodes it as the array of
its values (`Statement/LeanVmGuest.lean`). A compiled reader builds it from its three values by
`depFin3`, whose run is the array of their runs (`Rule.depFin3`). -/

/-- A dependent function of `Fin 3`, from its values at `0`, `1` and `2`. -/
def depFin3 {β : Fin 3 → Type} (a : β 0) (b : β 1) (c : β 2) : (i : Fin 3) → β i
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/-- A dependent function of a finite domain: the array of its values, as the statement encodes the
leanSPHINCS signature's layers (low priority: a function whose values' type does not depend on the
argument is the statement's `Fin n → α`, the same array). -/
instance (priority := low) depFinEncoding {n : ℕ} {β : Fin n → Type} [∀ i, MachineEncoding (β i)] :
    MachineEncoding ((i : Fin n) → β i) :=
  ⟨fun f ↦ .array (Array.ofFn fun i ↦ encodeValue (f i))⟩

namespace Rule

variable {P : MachineProgram} {env : List MachineValue} {α β γ : Type} [MachineEncoding α] [MachineEncoding β] [MachineEncoding γ]

theorem var {i : ℕ} {x : α} (h : env[i]? = some (encodeValue x)) : Runs P env (.position i) (encodeValue x) 1 :=
  Runs.var h

theorem natLit (n : ℕ) : Runs P env (.literal (.nat n)) (encodeValue n) 1 := Runs.val _

theorem boolLit (b : Bool) : Runs P env (.literal (MachineValue.ofBool b)) (encodeValue b) 1 := Runs.val _

theorem letIn {t b : Term} {v : α} {f : α → β} {c : ℕ} {d : α → ℕ} (h : Runs P env t (encodeValue v) c)
    (hb : ∀ x, x = v → Runs P (encodeValue x :: env) b (encodeValue (f x)) (d x)) :
    Runs P env (.letIn t b) (encodeValue (f v)) (c + d v + 1) :=
  Runs.letIn h (hb v rfl)

/-- `let`, the body run with the value itself in front of the environment. -/
theorem letV {t b : Term} {v : α} {w : β} {c d : ℕ} (h : Runs P env t (encodeValue v) c)
    (hb : Runs P (encodeValue v :: env) b (encodeValue w) d) : Runs P env (.letIn t b) (encodeValue w) (c + d + 1) :=
  Runs.letIn h hb

/-! ### Constructors and fields -/

theorem none : Runs P env (.constructor 0 []) (encodeValue (none : Option α)) 1 :=
  (Runs.ctor (k := 0) RunsList.nil).cost_eq (by simp)

theorem some {t : Term} {a : α} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.constructor 1 [t]) (encodeValue (some a)) (c + 2) :=
  (Runs.ctor (k := 1) (RunsList.cons h RunsList.nil)).cost_eq (by simp)

theorem nil : Runs P env (.constructor 0 []) (encodeValue ([] : List α)) 1 :=
  (Runs.ctor (k := 0) RunsList.nil).cost_eq (by simp)

theorem cons {t u : Term} {a : α} {l : List α} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hl : Runs P env u (encodeValue l) d) : Runs P env (.constructor 1 [t, u]) (encodeValue (a :: l)) (c + d + 3) :=
  (Runs.ctor (k := 1) (RunsList.cons h (RunsList.cons hl RunsList.nil))).cost_eq (by simp)

theorem pair {t u : Term} {a : α} {b : β} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.constructor 0 [t, u]) (encodeValue (a, b)) (c + d + 3) :=
  (Runs.ctor (k := 0) (RunsList.cons h (RunsList.cons hb RunsList.nil))).cost_eq (by simp)

theorem fst {t : Term} {p : α × β} {c : ℕ} (h : Runs P env t (encodeValue p) c) :
    Runs P env (.field 0 t) (encodeValue p.1) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue p.1, encodeValue p.2]) h rfl

theorem snd {t : Term} {p : α × β} {c : ℕ} (h : Runs P env t (encodeValue p) c) :
    Runs P env (.field 1 t) (encodeValue p.2) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue p.1, encodeValue p.2]) h rfl

/-! ### Matches -/

theorem caseOption {t a b : Term} {o : Option α} {e₀ : β} {e₁ : α → β} {c c₀ : ℕ} {c₁ : α → ℕ}
    (h : Runs P env t (encodeValue o) c) (h₀ : o = .none → Runs P env a (encodeValue e₀) c₀)
    (h₁ : ∀ x, o = .some x → Runs P (encodeValue x :: env) b (encodeValue (e₁ x)) (c₁ x)) :
    Runs P env (.case t [a, b]) (encodeValue (Option.casesOn (motive := fun _ ↦ β) o e₀ e₁))
      (c + Option.casesOn (motive := fun _ ↦ ℕ) o c₀ (fun x ↦ c₁ x + 1) + 1) := by
  cases o with
  | none => exact Runs.case0 (k := 0) h rfl (h₀ rfl)
  | some x =>
    exact (Runs.case (k := 1) (fs := [encodeValue x]) (alts := [a, b]) h rfl (h₁ x rfl)).cost_eq
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem caseList {t a b : Term} {l : List α} {e₀ : β} {e₁ : α → List α → β} {c c₀ : ℕ}
    {c₁ : α → List α → ℕ} (h : Runs P env t (encodeValue l) c) (h₀ : l = [] → Runs P env a (encodeValue e₀) c₀)
    (h₁ : ∀ x xs, l = x :: xs → Runs P (encodeValue x :: encodeValue xs :: env) b (encodeValue (e₁ x xs)) (c₁ x xs)) :
    Runs P env (.case t [a, b]) (encodeValue (List.casesOn (motive := fun _ ↦ β) l e₀ e₁))
      (c + List.casesOn (motive := fun _ ↦ ℕ) l c₀ (fun x xs ↦ c₁ x xs + 2) + 1) := by
  cases l with
  | nil => exact Runs.case0 (k := 0) h rfl (h₀ rfl)
  | cons x xs =>
    exact (Runs.case (k := 1) (fs := [encodeValue x, encodeValue xs]) (alts := [a, b]) h rfl (h₁ x xs rfl)).cost_eq
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem casePair {t b : Term} {p : α × β} {e : α → β → γ} {c : ℕ} {c₁ : α → β → ℕ}
    (h : Runs P env t (encodeValue p) c)
    (h₁ : ∀ x y, p = (x, y) → Runs P (encodeValue x :: encodeValue y :: env) b (encodeValue (e x y)) (c₁ x y)) :
    Runs P env (.case t [b]) (encodeValue (Prod.casesOn (motive := fun _ ↦ γ) p e))
      (c + Prod.casesOn (motive := fun _ ↦ ℕ) p c₁ + 3) := by
  obtain ⟨x, y⟩ := p
  exact (Runs.case (k := 0) (fs := [encodeValue x, encodeValue y]) (alts := [b]) h rfl (h₁ x y rfl)).cost_eq
    (by simp only [List.length_cons, List.length_nil])

theorem ite {tc ta tb : Term} {p : Prop} [Decidable p] {a b : α} {c ca cb : ℕ}
    (h : Runs P env tc (encodeValue (decide p)) c) (ha : p → Runs P env ta (encodeValue a) ca)
    (hb : ¬p → Runs P env tb (encodeValue b) cb) :
    Runs P env (.case tc [tb, ta]) (encodeValue (if p then a else b)) (c + (if p then ca else cb) + 1) := by
  by_cases hp : p
  · exact Runs.case0 (k := 1) (by simpa [hp] using h) rfl (by simpa [hp] using ha hp)
  · exact Runs.case0 (k := 0) (by simpa [hp] using h) rfl (by simpa [hp] using hb hp)

theorem dite {tc ta tb : Term} {p : Prop} [Decidable p] {a : p → α} {b : ¬p → α} {c : ℕ}
    {ca : p → ℕ} {cb : ¬p → ℕ}
    (h : Runs P env tc (encodeValue (decide p)) c) (ha : ∀ hp : p, Runs P env ta (encodeValue (a hp)) (ca hp))
    (hb : ∀ hp : ¬p, Runs P env tb (encodeValue (b hp)) (cb hp)) :
    Runs P env (.case tc [tb, ta]) (encodeValue (if hp : p then a hp else b hp))
      (c + (if hp : p then ca hp else cb hp) + 1) := by
  by_cases hp : p
  · exact Runs.case0 (k := 1) (by simpa [hp] using h) rfl (by simpa [hp] using ha hp)
  · exact Runs.case0 (k := 0) (by simpa [hp] using h) rfl (by simpa [hp] using hb hp)

theorem cond {tc ta tb : Term} {b : Bool} {x y : α} {c ca cb : ℕ}
    (h : Runs P env tc (encodeValue b) c) (ha : b = true → Runs P env ta (encodeValue x) ca)
    (hb : b = false → Runs P env tb (encodeValue y) cb) :
    Runs P env (.case tc [tb, ta]) (encodeValue (bif b then x else y))
      (c + (bif b then ca else cb) + 1) := by
  cases b
  · exact Runs.case0 (k := 0) h rfl (by simpa using hb rfl)
  · exact Runs.case0 (k := 1) h rfl (by simpa using ha rfl)

theorem caseNat {t a b : Term} {n : ℕ} {e₀ : α} {e₁ : ℕ → α} {c c₀ : ℕ} {c₁ : ℕ → ℕ}
    (h : Runs P env t (encodeValue n) c) (h₀ : n = 0 → Runs P env a (encodeValue e₀) c₀)
    (h₁ : ∀ k, n = k + 1 → Runs P (encodeValue k :: env) b (encodeValue (e₁ k)) (c₁ k)) :
    Runs P env (.case (.primitive .equal [t, .literal (.nat 0)]) [.letIn (.primitive .truncatedSubtract [t, .literal (.nat 1)]) b, a])
      (encodeValue (Nat.casesOn (motive := fun _ ↦ α) n e₀ e₁))
      (c + 1 + limbCount n +
        Nat.casesOn (motive := fun _ ↦ ℕ) n c₀ (fun k ↦ c + 1 + limbCount n + c₁ k + 1) + 1) := by
  have hz : Runs P env (.primitive .equal [t, .literal (.nat 0)]) (encodeValue (decide (n = 0)))
      (c + 1 + limbCount n) :=
    (Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil))
      (d := max (limbCount n) (limbCount 0))
      (by simp [PrimitiveOperation.apply, enc_bool, MachineValue.ofBool])).cost_eq
      (by simp only [show limbCount 0 = 1 from rfl, max_limbs_one])
  cases n with
  | zero => exact Runs.case0 (k := 1) (by simpa using hz : Runs P env _ (.constructor 1 []) (c + 1 + limbCount 0)) rfl (h₀ rfl)
  | succ k =>
    have hs : Runs P env (.primitive .truncatedSubtract [t, .literal (.nat 1)]) (encodeValue k)
        (c + 1 + limbCount (k + 1)) :=
      (Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil))
        (d := max (limbCount (k + 1)) (limbCount 1)) (by
          simp only [enc_nat, PrimitiveOperation.apply]
          exact linearlyPriced_le (limbs_le_max_left (Nat.sub_le (k + 1) 1)))).cost_eq
        (by simp only [show limbCount 1 = 1 from rfl, max_limbs_one])
    exact Runs.case0 (k := 0) (by simpa using hz : Runs P env _ (.constructor 0 []) (c + 1 + limbCount (k + 1))) rfl
      (Runs.letIn hs (h₁ k rfl))

/-- A closure of function `j` with the values of `ts`. -/
theorem closure {j : ℕ} {ts : List Term} {vs : List MachineValue} {c : ℕ} (h : RunsList P env ts vs c) :
    Runs P env (.closure j ts) (.closure j vs) (c + vs.length + 1) := Runs.closure h

/-- A closure applied to the values of `ts`. -/
theorem applyClosure {t : Term} {ts : List Term} {f : MachineValue} {vs : List MachineValue} {w : MachineValue} {c d : ℕ}
    (h : Runs P env t f c) (hl : RunsList P env ts vs d) (ha : RunsApp P f vs w) :
    Runs P env (.applyClosure t ts) w (c + d + appCost P f vs + 1) := by
  obtain ⟨j, us, rfl, hb⟩ := ha
  exact (Runs.applyClosure h hl hb).cost_eq (by simp only [appCost]; omega)

/-- A raw value of the environment. -/
theorem rawVar {i : ℕ} {v : MachineValue} (h : env[i]? = .some v) : Runs P env (.position i) v 1 := Runs.var h

/-- A call of a function on the encodings of its arguments. -/
theorem call {f : ℕ} {ts : List Term} {vs : List MachineValue} {w : MachineValue} {c d : ℕ}
    (h : RunsList P env ts vs c) (hb : RunsBody P f vs w d) :
    Runs P env (.call f ts) w (c + d + 1) := Runs.call h hb

/-- `a || b`, short-circuit. -/
theorem boolOr {t u : Term} {a b : Bool} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : a = false → Runs P env u (encodeValue b) d) :
    Runs P env (.case t [u, .constructor 1 []]) (encodeValue (a
        || b)) (c + (if a then 1 else d) + 1) := by
  cases a
  · exact Runs.case0 (k := 0) h rfl (by simpa using hb rfl)
  · exact Runs.case0 (k := 1) h rfl (by simpa using (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil))

/-- `a && b`, short-circuit. -/
theorem boolAnd {t u : Term} {a b : Bool} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : a = true → Runs P env u (encodeValue b) d) :
    Runs P env (.case t [.constructor 0 [], u]) (encodeValue (a && b)) (c + (if a
        then d else 1) + 1) := by
  cases a
  · exact Runs.case0 (k := 0) h rfl (by simpa using (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil))
  · exact Runs.case0 (k := 1) h rfl (by simpa using hb rfl)

theorem boolNot {t : Term} {a : Bool} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.case t [.constructor 1 [], .constructor 0 []]) (encodeValue (!a)) (c + 1 + 1) := by
  cases a
  · exact Runs.case0 (k := 0) h rfl (by simpa using (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil))
  · exact Runs.case0 (k := 1) h rfl (by simpa using (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil))

/-! ### Primitives -/

/-- A primitive of two arguments, from the runs of its arguments. -/
theorem op₂ {o : PrimitiveOperation} {t u : Term} {a : α} {b : β} {v : MachineValue} {c d e : ℕ}
    (h : Runs P env t (encodeValue a) c) (hb : Runs P env u (encodeValue b) d)
    (ho : o.apply [encodeValue a, encodeValue b] = .some (v, e)) : Runs P env (.primitive o [t, u]) v (c + d + e) :=
  (Runs.op (RunsList.cons h (RunsList.cons hb RunsList.nil)) ho).cost_eq (by omega)

/-- A primitive of one argument. -/
theorem op₁ {o : PrimitiveOperation} {t : Term} {a : α} {v : MachineValue} {c e : ℕ} (h : Runs P env t (encodeValue a) c)
    (ho : o.apply [encodeValue a] = .some (v, e)) : Runs P env (.primitive o [t]) v (c + e) :=
  (Runs.op (RunsList.cons h RunsList.nil) ho).cost_eq (by omega)

/-! ### Natural numbers

A rule's price is the primitive's (`linearlyPricedResult`, `quadraticallyPricedResult`), simplified where the
result has no more limbs than the operands (`−`, `and`, `or`, `xor`, `>>>`, `/`, `%`). -/

theorem natAdd {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .add [t, u]) (encodeValue (a + b))
      (c + d + max (limbCount (a + b)) (max (limbCount a) (limbCount b))) :=
  op₂ h hb rfl

theorem natSub {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .truncatedSubtract [t, u]) (encodeValue (a - b)) (c + d + max (limbCount a) (limbCount b)) :=
  op₂ h hb (linearlyPriced_le (limbs_le_max_left (Nat.sub_le a b)))

theorem natMul {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .multiply [t, u]) (encodeValue (a * b))
      (c + d + max (limbCount (a * b)) (limbCount a * limbCount b)) :=
  op₂ h hb rfl

theorem natDiv {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .divide [t, u]) (encodeValue (a / b)) (c + d + limbCount a *
        limbCount b) :=
  op₂ h hb (quadraticallyPriced_le (limbs_le_mul_left (Nat.div_le_self a b)))

theorem natMod {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .modulo [t, u]) (encodeValue (a % b)) (c + d + limbCount a *
        limbCount b) :=
  op₂ h hb (quadraticallyPriced_le (limbs_le_mul_left (Nat.mod_le a b)))

theorem natLt {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .lessThan [t, u]) (encodeValue (decide (a < b))) (c + d + max (limbCount a) (limbCount b)) :=
  op₂ h hb rfl

/-- `a ≤ b`: `¬ b < a`. -/
theorem natLe {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.case (.primitive .lessThan [u, t]) [.constructor 1 [], .constructor 0 []]) (encodeValue (decide (a ≤ b)))
      (c + d + max (limbCount a) (limbCount b) + 2) := by
  have hlt : Runs P env (.primitive .lessThan [u, t]) (encodeValue (decide (b < a)))
      (d + c + max (limbCount b) (limbCount a)) := op₂ hb h rfl
  by_cases hab : b < a
  · have := Runs.case0 (k := 1) (alts := [.constructor 1 [], .constructor 0 []])
      (by simpa [hab] using hlt) rfl
      (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil)
    refine (by simpa [Nat.not_le.2 hab, enc_bool, MachineValue.ofBool] using this : Runs P env _ _ _).cost_eq ?_
    rw [Nat.max_comm]; omega
  · have := Runs.case0 (k := 0) (alts := [.constructor 1 [], .constructor 0 []])
      (by simpa [hab] using hlt) rfl
      (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil)
    refine (by simpa [Nat.le_of_not_lt hab, enc_bool, MachineValue.ofBool] using this : Runs P env _ _ _).cost_eq ?_
    rw [Nat.max_comm]; omega

theorem natEq {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .equal [t, u]) (encodeValue (decide (a = b))) (c + d + max (limbCount a) (limbCount b)) :=
  op₂ h hb (by simp [PrimitiveOperation.apply, enc_bool, MachineValue.ofBool])

theorem natBEq {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .equal [t, u]) (encodeValue (a == b)) (c + d + max (limbCount a) (limbCount b)) :=
  op₂ h hb (by simp [PrimitiveOperation.apply, enc_bool, MachineValue.ofBool])

theorem natAnd {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .bitwiseAnd [t, u]) (encodeValue (a &&& b)) (c + d + max (limbCount a) (limbCount b)) :=
  op₂ h hb (linearlyPriced_le (limbs_le_max_left Nat.and_le_left))

theorem natOr {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .bitwiseOr [t, u]) (encodeValue (a ||| b)) (c + d + max (limbCount a) (limbCount b)) :=
  op₂ h hb (linearlyPriced_le (limbs_or_le a b))

theorem natXor {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .bitwiseXor [t, u]) (encodeValue (a ^^^ b)) (c + d + max (limbCount a) (limbCount b)) :=
  op₂ h hb (linearlyPriced_le (limbs_xor_le a b))

theorem natShiftRight {t u : Term} {a k : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue k) d) :
    Runs P env (.primitive .shiftRight [t, u]) (encodeValue (a >>> k)) (c + d + max (limbCount a) (limbCount k)) :=
  op₂ h hb (linearlyPriced_le (limbs_le_max_left (Nat.shiftRight_le a k)))

theorem natShiftLeft {t u : Term} {a k : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue k) d) :
    Runs P env (.primitive .shiftLeft [t, u]) (encodeValue (a <<< k))
      (c + d + max (limbCount (a <<< k)) (max (limbCount a) (limbCount k))) :=
  op₂ h hb rfl

/-! ### Words

`UInt64`, `UInt8` and `K` are natural numbers below `2^64`, one limb: their operations are
natural-number code, wrap-arounds masked, each at a constant price (the limb counts of the
operands, the masks and the results proved `1`, or `2` where an operand is a two-limb mask). -/

theorem wordLit (x : UInt64) {n : ℕ} (hn : x.toNat = n) : Runs P env (.literal (.nat n)) (encodeValue x) 1 :=
  hn ▸ Runs.val _

theorem kLit (x : K) {n : ℕ} (hn : x.lane.toNat = n) : Runs P env (.literal (.nat n)) (encodeValue x) 1 :=
  hn ▸ Runs.val _

theorem u8Lit (x : UInt8) {n : ℕ} (hn : x.toNat = n) : Runs P env (.literal (.nat n)) (encodeValue x) 1 :=
  hn ▸ Runs.val _

/-- A primitive of two numbers. -/
theorem nat₂ {o : PrimitiveOperation} {t u : Term} {x y : ℕ} {v : MachineValue} {c d e : ℕ}
    (h : Runs P env t (.nat x) c) (hb : Runs P env u (.nat y) d)
    (ho : o.apply [.nat x, .nat y] = .some (v, e)) : Runs P env (.primitive o [t, u]) v (c + d
        + e) :=
  (Runs.op (RunsList.cons h (RunsList.cons hb RunsList.nil)) ho).cost_eq (by omega)

/-- A one-limb operation of two words: price `1`. -/
theorem word₂ {o : PrimitiveOperation} {t u : Term} {x y : ℕ} {v : MachineValue} {c d : ℕ}
    (h : Runs P env t (.nat x) c) (hb : Runs P env u (.nat y) d)
    (ho : o.apply [.nat x, .nat y] = .some (v, 1)) : Runs P env (.primitive o [t, u]) v (c + d
        + 1) :=
  (Runs.op (RunsList.cons h (RunsList.cons hb RunsList.nil)) ho).cost_eq (by omega)

theorem wXor {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .bitwiseXor [t, u]) (encodeValue (a ^^^ b)) (c + d + 1) :=
  word₂ h hb (by
    simp only [PrimitiveOperation.apply, enc_word, UInt64.toNat_xor]
    exact linearlyPriced_one (UInt64.toNat_xor a b ▸ (a ^^^ b).toNat_lt) a.toNat_lt b.toNat_lt)

theorem wAnd {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .bitwiseAnd [t, u]) (encodeValue (a &&& b)) (c + d + 1) :=
  word₂ h hb (by
    simp only [PrimitiveOperation.apply, enc_word, UInt64.toNat_and]
    exact linearlyPriced_one (UInt64.toNat_and a b ▸ (a &&& b).toNat_lt) a.toNat_lt b.toNat_lt)

theorem wOr {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .bitwiseOr [t, u]) (encodeValue (a ||| b)) (c + d + 1) :=
  word₂ h hb (by
    simp only [PrimitiveOperation.apply, enc_word, UInt64.toNat_or]
    exact linearlyPriced_one (UInt64.toNat_or a b ▸ (a ||| b).toNat_lt) a.toNat_lt b.toNat_lt)

/-- `~~~a`: `a ^^^ (2^64 - 1)`. -/
theorem wNot {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.primitive .bitwiseXor [t, .literal (.nat 18446744073709551615)]) (encodeValue (~~~a)) (c + 1 + 1) :=
  word₂ h (Runs.val _) (by
    simp only [PrimitiveOperation.apply, enc_word, uint64_toNat_not]
    exact linearlyPriced_one (uint64_toNat_not a ▸ (~~~a).toNat_lt) a.toNat_lt (by decide))

/-- `a <<< b`: `((a ||| 2^64) <<< (b &&& 63)) &&& (2^64 - 1)`, the bit `2^64` making each step's
limb counts constant (`2`). -/
theorem wShl {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .bitwiseAnd [.primitive .shiftLeft [.primitive .bitwiseOr [t, .literal (.nat 18446744073709551616)],
        .primitive .bitwiseAnd [u, .literal (.nat 63)]], .literal (.nat 18446744073709551615)])
      (encodeValue (a <<< b)) (c + d + 10) := by
  have ha := a.toNat_lt
  have hs : b.toNat &&& 63 < 64 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hor : a.toNat ||| 2 ^ 64 = a.toNat + 2 ^ 64 := uint64_or_two_pow a
  have h1 : Runs P env (.primitive .bitwiseOr [t, .literal (.nat 18446744073709551616)]) (.nat (a.toNat + 2 ^ 64))
      (c + 1 + 2) :=
    Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil)) (by
      simp only [enc_word, PrimitiveOperation.apply, linearlyPricedResult]
      rw [show (18446744073709551616 : ℕ) = 2 ^ 64 from rfl, hor,
        limbs_two (by omega) (by omega), limbs_of_lt ha, limbs_two (by decide) (by decide)]; rfl)
  have h2 : Runs P env (.primitive .bitwiseAnd [u, .literal (.nat 63)]) (.nat (b.toNat &&& 63)) (d +
      1 + 1) :=
    Runs.op (RunsList.cons hb (RunsList.cons (Runs.val _) RunsList.nil)) (by
      simp only [enc_word, PrimitiveOperation.apply]
      exact linearlyPriced_one (by omega) b.toNat_lt (by decide))
  have hlo : 2 ^ 64 ≤ (a.toNat + 2 ^ 64) <<< (b.toNat &&& 63) := by
    rw [Nat.shiftLeft_eq]; exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hhi : (a.toNat + 2 ^ 64) <<< (b.toNat &&& 63) < 2 ^ 128 := by
    rw [Nat.shiftLeft_eq]
    have h65 : a.toNat + 2 ^ 64 < 2 ^ 65 := by
      have : (2 : ℕ) ^ 65 = 2 ^ 64 + 2 ^ 64 := by norm_num
      omega
    calc (a.toNat + 2 ^ 64) * 2 ^ (b.toNat &&& 63) < 2 ^ 65 * 2 ^ 63 :=
          Nat.mul_lt_mul_of_lt_of_le h65 (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.two_pow_pos _)
      _ = 2 ^ 128 := by norm_num
  have h3 : Runs P env (.primitive .shiftLeft [.primitive .bitwiseOr [t, .literal (.nat
      18446744073709551616)],
      .primitive .bitwiseAnd [u, .literal (.nat 63)]]) (.nat ((a.toNat + 2 ^ 64) <<< (b.toNat
          &&& 63)))
      (c + 1 + 2 + (d + 1 + 1) + 2) :=
    nat₂ h1 h2 (by
      show PrimitiveOperation.apply .shiftLeft [.nat (a.toNat + 2 ^ 64), .nat (b.toNat &&& 63)] = _
      simp only [PrimitiveOperation.apply, linearlyPricedResult]
      rw [limbs_two hlo hhi, limbs_two (by omega) (by omega), limbs_of_lt (by omega)]; rfl)
  refine (nat₂ (e := 2) h3 (Runs.val _) ?_).cost_eq
    (show c + 1 + 2 + (d + 1 + 1) + 2 + 1 + 2 = c + d + 10 by omega)
  simp only [PrimitiveOperation.apply, linearlyPricedResult, enc_word]
  have hv : (a.toNat + 2 ^ 64) <<< (b.toNat &&& 63) &&& 18446744073709551615 = (a <<< b).toNat :=
    uint64_shiftLeft_eq a b
  rw [hv, limbs_of_lt (a <<< b).toNat_lt, limbs_two hlo hhi, limbs_of_lt (by decide)]; rfl

/-- `a >>> b`: `a >>> (b &&& 63)`. -/
theorem wShr {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .shiftRight [t, .primitive .bitwiseAnd [u, .literal (.nat 63)]]) (encodeValue (a >>> b)) (c + d + 3) := by
  have h2 : Runs P env (.primitive .bitwiseAnd [u, .literal (.nat 63)]) (.nat (b.toNat &&& 63)) (d +
      1 + 1) :=
    Runs.op (RunsList.cons hb (RunsList.cons (Runs.val _) RunsList.nil)) (by
      simp only [enc_word, PrimitiveOperation.apply]
      exact linearlyPriced_one (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) b.toNat_lt (by decide))
  refine (word₂ h h2 ?_).cost_eq (by omega)
  simp only [PrimitiveOperation.apply, enc_word]
  have hv : a.toNat >>> (b.toNat &&& 63) = (a >>> b).toNat := by
    rw [UInt64.toNat_shiftRight, show (63 : ℕ) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [hv]
  exact linearlyPriced_one (a >>> b).toNat_lt a.toNat_lt (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))

theorem wordLt {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .lessThan [t, u]) (encodeValue (decide (a < b))) (c + d + 1) :=
  word₂ h hb (by
    simp only [PrimitiveOperation.apply, limbs_of_lt a.toNat_lt, limbs_of_lt b.toNat_lt, max_self,
      enc_bool, UInt64.lt_iff_toNat_lt])

theorem wordEq {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .equal [t, u]) (encodeValue (decide (a = b))) (c + d + 1) :=
  word₂ h hb (by
    simp [PrimitiveOperation.apply, limbs_of_lt a.toNat_lt, limbs_of_lt b.toNat_lt, enc_bool,
      MachineValue.ofBool, UInt64.toNat_inj])

theorem wordBEq {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.primitive .equal [t, u]) (encodeValue (a == b)) (c + d + 1) :=
  word₂ h hb (by
    simp [PrimitiveOperation.apply, limbs_of_lt a.toNat_lt, limbs_of_lt b.toNat_lt, enc_bool,
      MachineValue.ofBool, UInt64.toNat_inj])

/-- `UInt64.toNat`: the same number. -/
theorem wToNat {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env t (encodeValue a.toNat) c := h

/-- `n.toUInt64`: `n &&& (2^64 - 1)`. -/
theorem natToUInt64 {t : Term} {n : ℕ} {c : ℕ} (h : Runs P env t (encodeValue n) c) :
    Runs P env (.primitive .bitwiseAnd [t, .literal (.nat 18446744073709551615)]) (encodeValue
        n.toUInt64)
      (c + 1 + limbCount n) :=
  op₂ (b := (18446744073709551615 : ℕ)) h (natLit _) (by
    simp only [enc_nat, enc_word, PrimitiveOperation.apply, linearlyPricedResult, Nat.toUInt64_eq,
      UInt64.toNat_ofNat', show (18446744073709551615 : ℕ) = 2 ^ 64 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, limbs_of_lt (Nat.mod_lt n (Nat.two_pow_pos 64)),
      limbs_of_lt (show 2 ^ 64 - 1 < 2 ^ 64 by decide), max_limbs_one, max_one_limbs])

/-- `UInt64.ofNat n`: `n &&& (2^64 - 1)`. -/
theorem uint64OfNat {t : Term} {n : ℕ} {c : ℕ} (h : Runs P env t (encodeValue n) c) :
    Runs P env (.primitive .bitwiseAnd [t, .literal (.nat 18446744073709551615)]) (encodeValue (UInt64.ofNat n))
      (c + 1 + limbCount n) :=
  natToUInt64 h

/-- `K.lane`: the same number. -/
theorem kLane {t : Term} {a : K} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env t (encodeValue a.lane) c := h

/-- `K.ofLane`: the same number. -/
theorem kOfLane {t : Term} {w : UInt64} {c : ℕ} (h : Runs P env t (encodeValue w) c) :
    Runs P env t (encodeValue (K.ofLane w)) c := h

theorem kAdd {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.primitive .bitwiseXor [t, u]) (encodeValue (a + b)) (c + d + 1) :=
  wXor (a := a.lane) (b := b.lane) h hb

theorem kSub {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.primitive .bitwiseXor [t, u]) (encodeValue (a - b)) (c + d + 1) :=
  wXor (a := a.lane) (b := b.lane) h hb

theorem kEq {t u : Term} {a b : K} {inst : Decidable (a = b)} {c d : ℕ}
    (h : Runs P env t (encodeValue a) c) (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .equal [t, u]) (encodeValue (@decide (a = b) inst)) (c + d + 1) := by
  have : @decide (a = b) inst = decide (a.lane = b.lane) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact ⟨fun e ↦ e ▸ rfl, fun e ↦ by
      rw [← show K.ofLane a.lane = a from rfl, ← show K.ofLane b.lane = b from rfl, e]⟩
  rw [this]
  exact wordEq (a := a.lane) (b := b.lane) h hb

theorem kBEq {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.primitive .equal [t, u]) (encodeValue (a == b)) (c + d + 1) := by
  have : (a == b) = (a.lane == b.lane) := by
    obtain ⟨x⟩ := a
    obtain ⟨y⟩ := b
    by_cases hxy : x = y
    · subst hxy; simp [K.lane]
    · have h1 : (⟨x⟩ : UInt64) ≠ ⟨y⟩ := fun e ↦ hxy (by cases e; rfl)
      have h2 : ((⟨x⟩ : K) == ⟨y⟩) = false := by
        show (x == y) = false
        simp [hxy]
      simp [K.lane, h1, h2]
  rw [this]
  exact wordBEq (a := a.lane) (b := b.lane) h hb

/-! ### The product in `K`

`mulKNat` (`Cost/FieldMul.lean`): the carry-less product `p` of the lanes, then Barrett's
reduction by the modulus `M = x^64 + x^4 + x^3 + x + 1`. Its price is constant once `p` has two
limbs (`2` per primitive); when `p < 2^64` the reduction is the identity, and the code returns `p`
after a padding of the same price, so that the product's price is a constant, `24`, as a word
operation's (`kMulPadding`). -/

/-- The modulus's literal. -/
abbrev kModulus : ℕ := 0x1000000000000001B

theorem carryless_zero_modulus : carryless 0 kModulus = 0 := by
  rw [carryless_modulus]; simp [timesTail]

/-- **A nonzero word times the modulus has two limbs.** -/
theorem modulus_product_bounds {x : ℕ} (h1 : 1 ≤ x) (hx : x < 2 ^ 64) :
    2 ^ 64 ≤ carryless x kModulus ∧ carryless x kModulus < 2 ^ 128 := by
  refine ⟨?_, carryless_lt (n := 64) (m := 65) hx (by norm_num)⟩
  rw [carryless_modulus]
  have hs : timesTail x >>> 64 < 2 ^ 4 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    exact timesTail_lt hx
  have hq : (timesTail x ^^^ x <<< 64) >>> 64 = timesTail x >>> 64 ^^^ x := by
    rw [Nat.shiftRight_xor_distrib, Nat.shiftLeft_shiftRight]
  have hne : timesTail x >>> 64 ^^^ x ≠ 0 := by
    intro h0
    have he : timesTail x >>> 64 = x := by simpa using h0
    by_cases hsmall : x < 2 ^ 60
    · have : timesTail x >>> 64 = 0 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_eq_of_lt (timesTail_lt (n := 60) hsmall)
      omega
    · omega
  have : 1 ≤ (timesTail x ^^^ x <<< 64) >>> 64 := by rw [hq]; omega
  rw [Nat.shiftRight_eq_div_pow] at this
  exact (Nat.le_div_iff_mul_le (by positivity)).1 this |>.trans_eq' (by ring)

/-- The padding of the product's short case: `p` at price `17`. -/
theorem kMulPadding {env : List MachineValue} {p : ℕ} :
    Runs P (.nat p :: env) (.letIn (.primitive .arrayReplicate [.literal (.nat 12), .literal (.nat
        0)]) (.position 1))
      (.nat p) 17 :=
  (Runs.letIn (Runs.op (RunsList.cons (Runs.val _) (RunsList.cons (Runs.val _) RunsList.nil))
    (v := .array (Array.replicate 12 (.nat 0))) (d := 13) (by simp [PrimitiveOperation.apply]))
    (Runs.var rfl)).cost_eq (by norm_num)

/-- **`a * b` in `K`**: the carry-less product, then Barrett's reduction (or, below `2^64`, a
padding), at a constant price. -/
theorem kMul {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.letIn (.primitive .carrylessMultiply [t, u])
      (.case (.primitive .lessThan [.position 0, .literal (.nat 18446744073709551616)])
        [.primitive .bitwiseXor [.position 0, .primitive .carrylessMultiply [.primitive .shiftRight
            [.primitive .carrylessMultiply
          [.primitive .shiftRight [.position 0, .literal (.nat 64)], .literal (.nat 0x1000000000000001B)], .literal (.nat 64)],
          .literal (.nat 0x1000000000000001B)]],
         .letIn (.primitive .arrayReplicate [.literal (.nat 12), .literal (.nat 0)])
             (.position 1)]))
      (encodeValue (a * b)) (c + d + 24) := by
  have hA := a.lane.toNat_lt
  have hB := b.lane.toNat_lt
  have hres := mulKNat_lt a b
  have hval : encodeValue (a * b) = .nat (mulKNat a.lane.toNat b.lane.toNat) := by
    rw [mulKNat_eq]; rfl
  rw [hval]
  rw [enc_k] at h hb
  generalize a.lane.toNat = A at *
  generalize b.lane.toNat = B at *
  have hp127 : carryless A B < 2 ^ 127 := carryless_lt (n := 64) (m := 64) hA hB
  have hmul : mulKNat A B = carryless A B ^^^ carryless (carryless (carryless A B >>> 64) kModulus >>> 64)
      kModulus := rfl
  rw [hmul] at hres ⊢
  have hP : Runs P env (.primitive .carrylessMultiply [t, u]) (.nat (carryless A B)) (c + d + limbCount (carryless A B)) :=
    nat₂ h hb (by
      simp only [PrimitiveOperation.apply, quadraticallyPricedResult, limbs_of_lt hA, limbs_of_lt hB,
        Nat.mul_one, max_limbs_one])
  generalize carryless A B = p at *
  have hM : limbCount kModulus = 2 := limbs_two (by norm_num) (by norm_num)
  have h64 : limbCount 18446744073709551616 = 2 := limbs_two (by norm_num) (by norm_num)
  have hp2 : limbCount p ≤ 2 := (limbs_le_iff (by omega)).2 (by omega)
  have hcmp : Runs P (.nat p :: env) (.primitive .lessThan [.position 0, .literal (.nat
      18446744073709551616)])
      (.ofBool (decide (p < 2 ^ 64))) (1 + 1 + 2) :=
    nat₂ (Runs.var rfl) (Runs.val _) (by
      simp only [PrimitiveOperation.apply, h64, Nat.max_eq_right hp2]; rfl)
  by_cases hlt : p < 2 ^ 64
  · have hh : p >>> 64 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hlt
    rw [hh, carryless_zero_modulus, Nat.zero_shiftRight, carryless_zero_modulus, Nat.xor_zero]
    have hc : Runs P (.nat p :: env) (.primitive .lessThan [.position 0, .literal (.nat
        18446744073709551616)])
        (.constructor 1 []) (1 + 1 + 2) := by
      rw [show MachineValue.constructor 1 [] = .ofBool (decide (p < 2 ^ 64)) by simp [MachineValue.ofBool, show p < 18446744073709551616 from hlt]]
      exact hcmp
    refine (Runs.letIn hP (Runs.case0 (k := 1) hc rfl kMulPadding)).cost_eq ?_
    rw [limbs_of_lt hlt]
  · have hp1 : limbCount p = 2 := limbs_two (by omega) (by omega)
    have hh1 : 1 ≤ p >>> 64 := by
      rw [Nat.shiftRight_eq_div_pow]; exact (Nat.le_div_iff_mul_le (by positivity)).2 (by omega)
    have hh2 : p >>> 64 < 2 ^ 64 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]; omega
    obtain ⟨ht1, ht2⟩ := modulus_product_bounds hh1 hh2
    obtain ⟨x, hx⟩ : ∃ x, p >>> 64 = x := ⟨_, rfl⟩
    rw [hx] at hh1 hh2 ht1 ht2 hres ⊢
    obtain ⟨y, hy⟩ : ∃ y, carryless x kModulus = y := ⟨_, rfl⟩
    rw [hy] at ht1 ht2 hres ⊢
    have hq1 : 1 ≤ y >>> 64 := by
      rw [Nat.shiftRight_eq_div_pow]; exact (Nat.le_div_iff_mul_le (by positivity)).2 (by omega)
    have hq2 : y >>> 64 < 2 ^ 64 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]; omega
    obtain ⟨hu1, hu2⟩ := modulus_product_bounds hq1 hq2
    obtain ⟨z, hz⟩ : ∃ z, y >>> 64 = z := ⟨_, rfl⟩
    rw [hz] at hq1 hq2 hu1 hu2 hres ⊢
    obtain ⟨w, hw⟩ : ∃ w, carryless z kModulus = w := ⟨_, rfl⟩
    rw [hw] at hu1 hu2 hres ⊢
    have hc : Runs P (.nat p :: env) (.primitive .lessThan [.position 0, .literal (.nat
        18446744073709551616)])
        (.constructor 0 []) (1 + 1 + 2) := by
      rw [show MachineValue.constructor 0 [] = .ofBool (decide (p < 2 ^ 64)) by simp [MachineValue.ofBool, show ¬ p < 18446744073709551616 from hlt]]
      exact hcmp
    have l64 : limbCount 64 = 1 := limbs_of_lt (by norm_num)
    have r1 : Runs P (.nat p :: env) (.primitive .shiftRight [.position 0, .literal (.nat 64)]) (.nat x) (1 + 1 + 2) :=
      nat₂ (Runs.var rfl) (Runs.val _) (by
        simp only [PrimitiveOperation.apply, linearlyPricedResult, hx, limbs_of_lt hh2, hp1, l64]; rfl)
    have r2 : Runs P (.nat p :: env) (.primitive .carrylessMultiply [.primitive .shiftRight [.position 0, .literal (.nat 64)],
        .literal (.nat 0x1000000000000001B)]) (.nat y) (1 + 1 + 2 + 1 + 2) :=
      nat₂ r1 (Runs.val _) (by
        simp only [PrimitiveOperation.apply, quadraticallyPricedResult, hy, limbs_of_lt hh2,
          limbs_two ht1 ht2]
        rw [hM]; rfl)
    have r3 : Runs P (.nat p :: env) (.primitive .shiftRight [.primitive .carrylessMultiply
        [.primitive .shiftRight
        [.position 0, .literal (.nat 64)], .literal (.nat 0x1000000000000001B)], .literal (.nat
            64)]) (.nat z)
        (1 + 1 + 2 + 1 + 2 + 1 + 2) :=
      nat₂ r2 (Runs.val _) (by
        simp only [PrimitiveOperation.apply, linearlyPricedResult, hz, limbs_of_lt hq2,
          limbs_two ht1 ht2, l64]; rfl)
    have r4 : Runs P (.nat p :: env) (.primitive .carrylessMultiply [.primitive .shiftRight [.primitive .carrylessMultiply
        [.primitive .shiftRight [.position 0, .literal (.nat 64)], .literal (.nat 0x1000000000000001B)], .literal (.nat 64)],
        .literal (.nat 0x1000000000000001B)]) (.nat w) (1 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 2) :=
      nat₂ r3 (Runs.val _) (by
        simp only [PrimitiveOperation.apply, quadraticallyPricedResult, hw, limbs_of_lt hq2,
          limbs_two hu1 hu2]
        rw [hM]; rfl)
    have r5 := nat₂ (o := .bitwiseXor) (e := 2) (Runs.var (P := P) (env := .nat p :: env) (i := 0) rfl) r4 (by
        simp only [PrimitiveOperation.apply, linearlyPricedResult, limbs_of_lt hres, hp1,
          limbs_two hu1 hu2]; rfl)
    exact (Runs.letIn hP (Runs.case0 (k := 0) hc rfl r5)).cost_eq (by rw [hp1])


/-- The product in `K` as a function, compiled once (`Cost/Library.lean`, `kMulC`): its body is
`kMul`'s code on the two arguments (`kMulBody`), and every product is a call of it (`kMulCall`). -/
def kMulFn (a b : K) : K := a * b

/-- `kMul`'s code on the arguments `0` and `1`. -/
def kMulBody : Term :=
  .letIn (.primitive .carrylessMultiply [.position 0, .position 1])
    (.case (.primitive .lessThan [.position 0, .literal (.nat 18446744073709551616)])
      [.primitive .bitwiseXor [.position 0, .primitive .carrylessMultiply [.primitive .shiftRight
          [.primitive .carrylessMultiply
        [.primitive .shiftRight [.position 0, .literal (.nat 64)], .literal (.nat 0x1000000000000001B)], .literal (.nat 64)],
        .literal (.nat 0x1000000000000001B)]],
       .letIn (.primitive .arrayReplicate [.literal (.nat 12), .literal (.nat 0)]) (.position 1)])

theorem kMulBody_runs (a b : K) :
    Runs P [encodeValue a, encodeValue b] kMulBody (encodeValue (a * b)) 26 :=
  kMul (Runs.var rfl) (Runs.var rfl)

/-- **`a * b` in `K`**: a call of the product's body (`kMulBody`) at `j`, at a constant price. -/
theorem kMulCall {t u : Term} {a b : K} {c d j : ℕ} {body : Term} (hP : Includes P [(j, body)])
    (hbody : body = kMulBody) (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.call j [t, u]) (encodeValue (a * b)) (c + d + 27) := by
  subst hbody
  exact (Runs.call (RunsList.cons h (RunsList.cons hb RunsList.nil))
    (RunsBody.intro (hP.get List.mem_cons_self) (kMulBody_runs a b))).cost_eq (by omega)

theorem u8Xor {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.primitive .bitwiseXor [t, u]) (encodeValue (a ^^^ b)) (c + d + 1) :=
  word₂ h hb (by
    simp only [PrimitiveOperation.apply, enc_u8, UInt8.toNat_xor]
    exact linearlyPriced_one (UInt8.toNat_xor a b ▸ u8_lt (a ^^^ b)) (u8_lt a) (u8_lt b))

theorem u8And {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.primitive .bitwiseAnd [t, u]) (encodeValue (a &&& b)) (c + d + 1) :=
  word₂ h hb (by
    simp only [PrimitiveOperation.apply, enc_u8, UInt8.toNat_and]
    exact linearlyPriced_one (UInt8.toNat_and a b ▸ u8_lt (a &&& b)) (u8_lt a) (u8_lt b))

theorem u8Or {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.primitive .bitwiseOr [t, u]) (encodeValue (a ||| b)) (c + d + 1) :=
  word₂ h hb (by
    simp only [PrimitiveOperation.apply, enc_u8, UInt8.toNat_or]
    exact linearlyPriced_one (UInt8.toNat_or a b ▸ u8_lt (a ||| b)) (u8_lt a) (u8_lt b))

/-- A byte as a word: the same number. -/
theorem u8ToUInt64 {t : Term} {a : UInt8} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env t (encodeValue a.toUInt64) c := by
  rw [enc_word, UInt8.toNat_toUInt64]; exact h

/-- A word's low byte: `&&& 255`. -/
theorem u64ToUInt8 {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.primitive .bitwiseAnd [t, .literal (.nat 255)]) (encodeValue a.toUInt8) (c + 1
        + 1) :=
  word₂ h (Runs.val _) (by
    simp only [PrimitiveOperation.apply, enc_u8, UInt64.toNat_toUInt8,
      show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact linearlyPriced_one (by have := Nat.mod_lt a.toNat (Nat.two_pow_pos 8); omega) a.toNat_lt (by decide))

/-- A byte's number: the same number. -/
theorem uint8ToNat {t : Term} {x : UInt8} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env t (encodeValue x.toNat) c := h

theorem uint8Eq {t u : Term} {a b : UInt8} {inst : Decidable (a = b)} {c d : ℕ}
    (h : Runs P env t (encodeValue a) c) (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .equal [t, u]) (encodeValue (@decide (a = b) inst)) (c + d + 1) :=
  word₂ h hb (by
    have : decide (a.toNat = b.toNat) = @decide (a = b) inst := by
      by_cases hab : a = b
      · simp [hab]
      · have : a.toNat ≠ b.toNat := fun e ↦ hab (UInt8.toNat_inj.1 e)
        simp [hab, this]
    simp only [PrimitiveOperation.apply, limbs_of_lt (u8_lt a), limbs_of_lt (u8_lt b), max_self,
      enc_bool, this])

theorem u8Lt {t u : Term} {a b : UInt8} {inst : Decidable (a < b)} {c d : ℕ}
    (h : Runs P env t (encodeValue a) c) (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .lessThan [t, u]) (encodeValue (@decide (a < b) inst)) (c + d + 1) :=
  word₂ h hb (by
    have : decide (a.toNat < b.toNat) = @decide (a < b) inst := by
      by_cases hab : a < b
      · simp [hab, UInt8.lt_iff_toNat_lt.1 hab]
      · simp [hab, show ¬ a.toNat < b.toNat from fun e ↦ hab (UInt8.lt_iff_toNat_lt.2 e)]
    simp only [PrimitiveOperation.apply, limbs_of_lt (u8_lt a), limbs_of_lt (u8_lt b), max_self,
      enc_bool, this])
/-- `decide (b = true)` is `b`. -/
theorem decideEqTrue {t : Term} {b : Bool} {c : ℕ} (h : Runs P env t (encodeValue b) c) :
    Runs P env t (encodeValue (decide (b = true))) c := by
  cases b <;> exact h

/-- `decide (p ∧ q)`, short-circuit. -/
theorem decideAnd {t u : Term} {p q : Prop} [Decidable p] [Decidable q] {inst : Decidable (p ∧ q)}
    {c d : ℕ} (h : Runs P env t (encodeValue (decide p)) c) (hq : p → Runs P env u (encodeValue (decide q)) d) :
    Runs P env (.case t [.constructor 0 [], u]) (encodeValue (@decide (p ∧ q) inst))
      (c + (if p then d else 1) + 1) := by
  by_cases hp : p
  · have := Runs.case0 (k := 1) (alts := [.constructor 0 [], u]) (by simpa [hp] using h) rfl (hq hp)
    simpa [hp] using this
  · have := Runs.case0 (k := 0) (alts := [.constructor 0 [], u]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, MachineValue.ofBool] using this

/-- `decide (p ∨ q)`, short-circuit. -/
theorem decideOr {t u : Term} {p q : Prop} [Decidable p] [Decidable q] {inst : Decidable (p ∨ q)}
    {c d : ℕ} (h : Runs P env t (encodeValue (decide p)) c) (hq : ¬p → Runs P env u (encodeValue (decide q)) d) :
    Runs P env (.case t [u, .constructor 1 []]) (encodeValue (@decide (p ∨ q) inst))
      (c + (if p then 1 else d) + 1) := by
  by_cases hp : p
  · have := Runs.case0 (k := 1) (alts := [u, .constructor 1 []]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, MachineValue.ofBool] using this
  · have := Runs.case0 (k := 0) (alts := [u, .constructor 1 []]) (by simpa [hp] using h) rfl (hq hp)
    simpa [hp] using this

/-- `decide ¬p`. -/
theorem decideNot {t : Term} {p : Prop} [Decidable p] {inst : Decidable ¬p} {c : ℕ}
    (h : Runs P env t (encodeValue (decide p)) c) :
    Runs P env (.case t [.constructor 1 [], .constructor 0 []]) (encodeValue (@decide (¬p) inst)) (c + 1 + 1) := by
  by_cases hp : p
  · have := Runs.case0 (k := 1) (alts := [.constructor 1 [], .constructor 0 []])
      (by simpa [hp] using h) rfl
      (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, MachineValue.ofBool] using this
  · have := Runs.case0 (k := 0) (alts := [.constructor 1 [], .constructor 0 []])
      (by simpa [hp] using h) rfl
      (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, MachineValue.ofBool] using this

/-! ### Arrays -/

theorem arrSize {t : Term} {a : Array α} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.primitive .arraySize [t]) (encodeValue a.size) (c + 1) := op₁ h (by simp [PrimitiveOperation.apply])

theorem arrAppend {t u : Term} {a b : Array α} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.primitive .arrayAppend [t, u]) (encodeValue (a ++ b)) (c + d + (a.size + b.size
        + 1)) :=
  op₂ h hb (by simp [PrimitiveOperation.apply])

theorem arrReplicate {t u : Term} {n : ℕ} {x : α} {c d : ℕ} (h : Runs P env t (encodeValue n) c)
    (hb : Runs P env u (encodeValue x) d) :
    Runs P env (.primitive .arrayReplicate [t, u]) (encodeValue (Array.replicate n x)) (c + d + (n
        + 1)) :=
  op₂ h hb (by simp [PrimitiveOperation.apply])

theorem arrToList {t : Term} {a : Array α} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.primitive .arrayToList [t]) (encodeValue a.toList) (c + (3 * a.size + 1)) :=
  op₁ h (by simp [PrimitiveOperation.apply]; rfl)

theorem valToList_ofList (l : List MachineValue) : MachineValue.toList? (.ofList l) = .some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [MachineValue.ofList, MachineValue.toList?, ih]

theorem listToArray {t : Term} {l : List α} {c : ℕ} (h : Runs P env t (encodeValue l) c) :
    Runs P env (.primitive .arrayOfList [t]) (encodeValue l.toArray) (c + (l.length + 1)) :=
  op₁ h (by
    show PrimitiveOperation.apply .arrayOfList [.ofList (l.map encodeValue)] = _
    simp [PrimitiveOperation.apply, valToList_ofList])

theorem arrGetD {t u w : Term} {a : Array α} {i : ℕ} {x : α} {c d e : ℕ}
    (h : Runs P env t (encodeValue a) c) (hi : Runs P env u (encodeValue i) d) (hx : Runs P env w (encodeValue x) e) :
    Runs P env (.primitive .arrayGet [t, u, w]) (encodeValue (a.getD i x)) (c + d + e + 1) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hx RunsList.nil)))
    (v := encodeValue (a.getD i x)) (d := 1) (by
      simp only [enc_array, enc_nat, PrimitiveOperation.apply, Option.some.injEq, Prod.mk.injEq, and_true]
      simp [Array.getD_eq_getD_getElem?])).cost_eq (by omega)

theorem arrGetElem? {t u : Term} {a : Array α} {i : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hi : Runs P env u (encodeValue i) d) :
    Runs P env (.case (.primitive .lessThan [u, .primitive .arraySize [t]]) [.constructor 0 [], .constructor 1 [.primitive .arrayGet [t, u, .literal (.constructor 0 [])]]])
      (encodeValue a[i]?) (d + (c + 1) + max (limbCount i) (limbCount a.size) +
        (if i < a.size then c + d + 1 + 1 + 2 else 1) + 1) := by
  have hlt := natLt hi (arrSize h)
  by_cases hia : i < a.size
  · have hg : Runs P env (.primitive .arrayGet [t, u, .literal (.constructor 0 [])]) (encodeValue a[i]) (c + d + 1 + 1) :=
      (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
        (v := encodeValue a[i]) (d := 1) (by simp [PrimitiveOperation.apply, hia])).cost_eq (by omega)
    have := Runs.case0 (k := 1) (alts := [.constructor 0 [], .constructor 1 [.primitive .arrayGet [t, u, .literal (.constructor 0 [])]]])
      (by simpa [hia] using hlt) rfl (some hg)
    simpa [hia, Array.getElem?_eq_getElem hia] using this
  · have := Runs.case0 (k := 0) (alts := [.constructor 0 [], .constructor 1 [.primitive .arrayGet [t, u, .literal (.constructor 0 [])]]])
      (by simpa [hia] using hlt) rfl (none (P := P) (env := env) (α := α))
    simpa [hia, Array.getElem?_eq_none (Nat.le_of_not_lt hia)] using this

/-- A subtype's value: the same value. -/
theorem subtypeVal {t : Term} {p : α → Prop} {x : Subtype p} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env t (encodeValue x.val) c := h

/-- A subtype's element: the same value. -/
theorem subtypeMk {t : Term} {p : α → Prop} {x : α} {hx : p x} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env t (encodeValue (⟨x, hx⟩ : Subtype p)) c := h

/-- `a[i]'h`: an entry in bounds. -/
theorem arrGetElem {t u : Term} {a : Array α} {i : ℕ} {h : i < a.size} {c d : ℕ}
    (ha : Runs P env t (encodeValue a) c) (hi : Runs P env u (encodeValue i) d) :
    Runs P env (.primitive .arrayGet [t, u, .literal (.constructor 0 [])]) (encodeValue (a[i]'h)) (c
        + d + 1 + 1) :=
  (Runs.op (RunsList.cons ha (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
    (v := encodeValue (a[i]'h)) (d := 1) (by simp [PrimitiveOperation.apply, h])).cost_eq (by omega)

/-- A function of a finite domain at `i`: entry `i` of its array. -/
theorem finFunApp {t u : Term} {n : ℕ} {f : Fin n → α} {i : Fin n} {c d : ℕ}
    (h : Runs P env t (encodeValue f) c) (hi : Runs P env u (encodeValue i) d) :
    Runs P env (.primitive .arrayGet [t, u, .literal (.constructor 0 [])]) (encodeValue (f i)) (c +
        d + 1 + 1) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
    (v := encodeValue (f i)) (d := 1) (by
      show PrimitiveOperation.apply .arrayGet [.array (Array.ofFn fun j ↦ encodeValue (f j)), .nat i.val, _] = _
      simp [PrimitiveOperation.apply])).cost_eq (by omega)

/-- **`depFin3 a b c`**: the array of the three values' runs, built from the list of them. -/
theorem depFin3 {β : Fin 3 → Type} [∀ i, MachineEncoding (β i)] {ta tb tc : Term} {a : β 0}
    {b : β 1} {c : β 2} {ca cb cc : ℕ} (ha : Runs P env ta (encodeValue a) ca)
    (hb : Runs P env tb (encodeValue b) cb) (hc : Runs P env tc (encodeValue c) cc) :
    Runs P env (.primitive .arrayOfList [.constructor 1 [ta, .constructor 1 [tb,
        .constructor 1 [tc, .constructor 0 []]]]])
      (encodeValue (LeanVM.Cost.depFin3 a b c)) (ca + cb + cc + 14) := by
  have hn : Runs P env (.constructor 0 []) (MachineValue.ofList []) 1 :=
    (Runs.ctor (k := 0) RunsList.nil).cost_eq (by simp)
  have h3 := (Runs.ctor (k := 1) (RunsList.cons hc (RunsList.cons hn RunsList.nil)))
  have h2 := (Runs.ctor (k := 1) (RunsList.cons hb (RunsList.cons h3 RunsList.nil)))
  have h1 := (Runs.ctor (k := 1) (RunsList.cons ha (RunsList.cons h2 RunsList.nil)))
  refine (Runs.op (RunsList.cons h1 RunsList.nil) (v := encodeValue (LeanVM.Cost.depFin3 a b c))
    (d := 4) ?_).cost_eq (by simp; omega)
  show PrimitiveOperation.apply .arrayOfList [MachineValue.ofList [encodeValue a, encodeValue b,
    encodeValue c]] = Option.some (MachineValue.array (Array.ofFn fun i ↦
      encodeValue (LeanVM.Cost.depFin3 a b c i)), 4)
  have e : (Array.ofFn fun i ↦ encodeValue (LeanVM.Cost.depFin3 a b c i)) =
      [encodeValue a, encodeValue b, encodeValue c].toArray := by
    apply Array.ext'
    simp [List.ofFn_succ, LeanVM.Cost.depFin3]
  rw [e]
  simp [PrimitiveOperation.apply, valToList_ofList]

/-- A function of a finite domain as data: the array of its values. -/
theorem finFunOfArray {t : Term} {n : ℕ} {f : Fin n → α} {c : ℕ}
    (h : Runs P env t (encodeValue (Array.ofFn f)) c) : Runs P env t (encodeValue f) c := by
  have : encodeValue (Array.ofFn f) = encodeValue f := by
    show MachineValue.array ((Array.ofFn f).map encodeValue) = MachineValue.array (Array.ofFn fun i ↦ encodeValue (f i))
    rw [Array.map_ofFn]; rfl
  exact this ▸ h

/-- A vector's `get`: its array. -/
theorem vecGet {t : Term} {n : ℕ} {v : Vector α n} {c : ℕ} (h : Runs P env t (encodeValue v) c) :
    Runs P env t (encodeValue v.get) c := by
  have : encodeValue v.get = encodeValue v := by
    show MachineValue.array (Array.ofFn fun i ↦ encodeValue (v.get i)) = MachineValue.array (v.toArray.map encodeValue)
    congr 1
    apply Array.ext
    · simp
    · intro i h1 h2; simp [Vector.get]
  rw [this]; exact h

/-- A vector's array: the same value. -/
theorem vecToArray {t : Term} {n : ℕ} {v : Vector α n} {c : ℕ} (h : Runs P env t (encodeValue v) c) :
    Runs P env t (encodeValue v.toArray) c := h

/-- `v[i]'h` of a vector: an entry in bounds. -/
theorem vecGetElem {t u : Term} {n : ℕ} {v : Vector α n} {i : ℕ} {h : i < n} {c d : ℕ}
    (hv : Runs P env t (encodeValue v) c) (hi : Runs P env u (encodeValue i) d) :
    Runs P env (.primitive .arrayGet [t, u, .literal (.constructor 0 [])]) (encodeValue (v[i]'h)) (c
        + d + 1 + 1) :=
  (Runs.op (RunsList.cons hv (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
    (v := encodeValue (v[i]'h)) (d := 1) (by
      show PrimitiveOperation.apply .arrayGet [.array (v.toArray.map encodeValue), .nat i, _] = _
      simp [PrimitiveOperation.apply, h])).cost_eq (by omega)

/-- Limb `i` of a word of `E`: field `i`. -/
theorem eLimb0 {t : Term} {x : E} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env (.field 0 t) (encodeValue (x.limb 0)) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue (x.limb 0), encodeValue (x.limb 1), encodeValue (x.limb 2)]) h rfl
theorem eLimb1 {t : Term} {x : E} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env (.field 1 t) (encodeValue (x.limb 1)) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue (x.limb 0), encodeValue (x.limb 1), encodeValue (x.limb 2)]) h rfl
theorem eLimb2 {t : Term} {x : E} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env (.field 2 t) (encodeValue (x.limb 2)) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue (x.limb 0), encodeValue (x.limb 1), encodeValue (x.limb 2)]) h rfl

/-- A word of `E` from its limbs. -/
theorem eOfLimbs {ta tb tc : Term} {a b c : K} {ca cb cc : ℕ} (ha : Runs P env ta (encodeValue a) ca)
    (hb : Runs P env tb (encodeValue b) cb) (hc : Runs P env tc (encodeValue c) cc) :
    Runs P env (.constructor 0 [ta, tb, tc]) (encodeValue (E.ofLimbs a b c)) (ca + cb + cc + 4) :=
  (Runs.ctor (k := 0) (RunsList.cons ha (RunsList.cons hb (RunsList.cons hc RunsList.nil)))).cost_eq
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem vecToList {t : Term} {n : ℕ} {v : Vector α n} {c : ℕ} (h : Runs P env t (encodeValue v) c) :
    Runs P env (.primitive .arrayToList [t]) (encodeValue v.toList) (c + (3 * v.toArray.size
        + 1)) :=
  op₁ h (by
    show PrimitiveOperation.apply .arrayToList [.array (v.toArray.map encodeValue)] = _
    simp [PrimitiveOperation.apply, Vector.toList]
    rfl)

/-- A vector of an array: the same value. -/
theorem vecMk {t : Term} {n : ℕ} {a : Array α} {ha : a.size = n} {c : ℕ}
    (h : Runs P env t (encodeValue a) c) : Runs P env t (encodeValue (Vector.mk a ha)) c := h

theorem arrPush {t u : Term} {a : Array α} {x : α} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hx : Runs P env u (encodeValue x) d) :
    Runs P env (.primitive .arrayPush [t, u]) (encodeValue (a.push x)) (c + d + (a.size + 2)) :=
  op₂ h hx (by simp [PrimitiveOperation.apply])

theorem arrayMk {t : Term} {l : List α} {c : ℕ} (h : Runs P env t (encodeValue l) c) :
    Runs P env (.primitive .arrayOfList [t]) (encodeValue (Array.mk l)) (c + (l.length + 1)) := listToArray h

theorem arrSetIfInBounds {t u w : Term} {a : Array α} {i : ℕ} {x : α} {c d e : ℕ}
    (h : Runs P env t (encodeValue a) c) (hi : Runs P env u (encodeValue i) d) (hx : Runs P env w (encodeValue x) e) :
    Runs P env (.primitive .arraySet [t, u, w]) (encodeValue (a.setIfInBounds i x)) (c + d + e + (a.size + 1)) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hx RunsList.nil)))
    (v := encodeValue (a.setIfInBounds i x)) (d := a.size + 1) (by
      simp [PrimitiveOperation.apply, Array.map_setIfInBounds])).cost_eq (by omega)

theorem arrExtract {t u w : Term} {a : Array α} {i j : ℕ} {c d e : ℕ}
    (h : Runs P env t (encodeValue a) c) (hi : Runs P env u (encodeValue i) d) (hj : Runs P env w (encodeValue j) e) :
    Runs P env (.primitive .arrayExtract [t, u, w]) (encodeValue (a.extract i j))
      (c + d + e + ((a.extract i j).size + 1)) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hj RunsList.nil)))
    (v := encodeValue (a.extract i j)) (d := (a.extract i j).size + 1) (by
      simp [PrimitiveOperation.apply])).cost_eq (by omega)

/-- `Fin.val`: the same number. -/
theorem finVal {t : Term} {n : ℕ} {i : Fin n} {c : ℕ} (h : Runs P env t (encodeValue i) c) :
    Runs P env t (encodeValue i.val) c := h

/-- `Fin.mk`: the same number. -/
theorem finMk {t : Term} {n i : ℕ} {hi : i < n} {c : ℕ} (h : Runs P env t (encodeValue i) c) :
    Runs P env t (encodeValue (⟨i, hi⟩ : Fin n)) c := h

/-- An array of numbers given by a list, as a literal of the program: its encoding (`Term.literal`),
written through the list (`List.map`, which the kernel evaluates structurally where it measures
the program, unlike `Array.map`). The compiler applies it to the constants the rules table lists
(the guest decoder's tables), whose encodings are far smaller than their code. -/
theorem literalNats (l : List ℕ) :
    Runs P env (.literal (.array (l.map encodeValue).toArray)) (encodeValue l.toArray) 1 := by
  have h : encodeValue l.toArray = MachineValue.array (l.map encodeValue).toArray := by
    show MachineValue.array (l.toArray.map encodeValue) = _
    simp
  rw [h]; exact Runs.val _

/-- An array of arrays of numbers given by a list of lists, as a literal of the program. -/
theorem literalNatArrays (l : List (List ℕ)) :
    Runs P env (.literal (.array (l.map fun r ↦ MachineValue.array (r.map
        encodeValue).toArray).toArray))
      (encodeValue (l.map List.toArray).toArray) 1 := by
  have h : encodeValue (l.map List.toArray).toArray =
      MachineValue.array (l.map fun r ↦ MachineValue.array (r.map
          encodeValue).toArray).toArray := by
    show MachineValue.array ((l.map List.toArray).toArray.map encodeValue) = _
    simp only [List.map_toArray, List.map_map]
    congr 2
    apply List.map_congr_left
    intro r _
    show MachineValue.array (r.toArray.map encodeValue) = _
    simp
  rw [h]; exact Runs.val _

/-! ### Bit vectors, encoded as their number

The statement's encoding of `BitVec w` (`Statement/CostMachine.lean`) is `.nat v.toNat`; it is not
imported here, so each rule takes the encoding as an instance with its defining equation, which
the compiler proves by `rfl`. -/

/-- `BitVec.ofFin`: the same number. -/
theorem bvOfFin {w : ℕ} [MachineEncoding (BitVec w)] (henc : ∀ v : BitVec w, encodeValue v = .nat v.toNat)
    {t : Term} {i : Fin (2 ^ w)} {c : ℕ} (h : Runs P env t (encodeValue i) c) :
    Runs P env t (encodeValue (BitVec.ofFin i)) c := by
  rw [henc]; exact h

/-- `BitVec.toNat`: the same number. -/
theorem bvToNat {w : ℕ} [MachineEncoding (BitVec w)] (henc : ∀ v : BitVec w, encodeValue v = .nat v.toNat)
    {t : Term} {v : BitVec w} {c : ℕ} (h : Runs P env t (encodeValue v) c) :
    Runs P env t (encodeValue v.toNat) c := by
  rw [henc] at h; exact h

/-- `BitVec.toFin`: the same number. -/
theorem bvToFin {w : ℕ} [MachineEncoding (BitVec w)] (henc : ∀ v : BitVec w, encodeValue v = .nat v.toNat)
    {t : Term} {v : BitVec w} {c : ℕ} (h : Runs P env t (encodeValue v) c) :
    Runs P env t (encodeValue v.toFin) c := by
  rw [henc] at h; exact h

/-- `BitVec.ofNat w n`: `n &&& (2^w - 1)`. -/
theorem bvOfNat {w : ℕ} [MachineEncoding (BitVec w)] (henc : ∀ v : BitVec w, encodeValue v = .nat v.toNat)
    {t : Term} {n : ℕ} {c : ℕ} (h : Runs P env t (encodeValue n) c) :
    Runs P env (.primitive .bitwiseAnd [t, .literal (.nat (2 ^ w - 1))]) (encodeValue
        (BitVec.ofNat w n))
      (c + 1 + max (limbCount n) (limbCount (2 ^ w - 1))) := by
  rw [henc, BitVec.toNat_ofNat, ← Nat.and_two_pow_sub_one_eq_mod]
  exact op₂ (b := 2 ^ w - 1) h (natLit (2 ^ w - 1)) (linearlyPriced_le (limbs_le_max_left Nat.and_le_left))

end Rule

/-! ## Rewrites: library functions compiled through equal forms -/

namespace Rewrite

theorem arrayZipWith {α β γ : Type} (f : α → β → γ) (a : Array α) (b : Array β) :
    Array.zipWith f a b = (List.zipWith f a.toList b.toList).toArray := by
  apply Array.ext'
  simp [Array.toList_zipWith]

theorem natTwoPow (k : ℕ) : 2 ^ k = 1 <<< k := by simp [Nat.shiftLeft_eq]

/-- Equality of lists, decided by their elements' equality. -/
theorem decideEqList {α : Type} [DecidableEq α] (l₁ l₂ : List α) {inst : Decidable (l₁ = l₂)} :
    @decide (l₁ = l₂) inst = @List.beq α instBEqOfDecidableEq l₁ l₂ := by
  rw [show @List.beq α instBEqOfDecidableEq l₁ l₂ = (l₁ == l₂) from rfl]
  by_cases h : l₁ = l₂ <;> simp [h]

/-- A cast along an equation with a constant motive (a literal pattern's `h ▸`): the value. -/
theorem eqNdrecConst {α β : Sort _} {a b : α} (x : β) (h : a = b) :
    @Eq.ndrec α a (fun _ ↦ β) x b h = x := by
  subst h; rfl

/-- The last element: the head of the reversal (`List.getLast` carries a proof). -/
theorem listGetLastD {α : Type} (l : List α) (d : α) : l.getLastD d = l.reverse.headD d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_head?_reverse, List.headD_eq_head?_getD]

theorem uint64Default : (default : UInt64) = 0 := rfl

theorem uint8Default : (default : UInt8) = 0 := rfl

/-- `K.ofBits`: the word of the number modulo `2^64`. -/
theorem kOfBits (n : ℕ) : K.ofBits n = K.ofLane n.toUInt64 := rfl

/-- Addition in `E`, limb by limb. -/
theorem eAdd (x y : E) : x + y =
    E.ofLimbs (x.limb 0 + y.limb 0) (x.limb 1 + y.limb 1) (x.limb 2 + y.limb 2) := by
  rw [← ofLimbs_limb x, ← ofLimbs_limb y, add_limbs]; simp

/-- Multiplication in `E`: nine products of limbs, `y^3 = y + 1`. -/
theorem eMul (x y : E) : x * y =
    let x0 := x.limb 0; let x1 := x.limb 1; let x2 := x.limb 2
    let y0 := y.limb 0; let y1 := y.limb 1; let y2 := y.limb 2
    let c3 := x1 * y2 + x2 * y1; let c4 := x2 * y2
    E.ofLimbs (x0 * y0 + c3) (x0 * y1 + x1 * y0 + c3 + c4) (x0 * y2 + x1 * y1 + x2 * y0 + c4) := by
  conv_lhs => rw [← ofLimbs_limb x, ← ofLimbs_limb y, mul_limbs]
  simp only []
  congr 1 <;> ring

theorem eZero : (0 : E) = E.ofLimbs 0 0 0 := by
  apply E.ext; intro i; fin_cases i <;> simp [limb_zero]

theorem eOfK (a : K) : ofK a = E.ofLimbs a 0 0 := ofK_eq_ofLimbs a

/-- `1` of `E`: the limbs `1, 0, 0` (as `E`'s encoding reads it; the generic constructor path does
not). -/
theorem eOne : (1 : E) = E.ofLimbs 1 0 0 := by
  apply E.ext; intro i
  rw [limb_ofLimbs]
  have h := CompPoly.Extension.Ext.coeff_one (P := BF64.ext3Params) i
  fin_cases i <;> exact h

/-- Equality in `E`: of the limbs. -/
theorem decideEqE (x y : E) {inst : Decidable (x = y)} :
    @decide (x = y) inst = decide (x.limb 0 = y.limb 0 ∧ x.limb 1 = y.limb 1 ∧ x.limb 2 = y.limb 2) := by
  have : x = y ↔ (x.limb 0 = y.limb 0 ∧ x.limb 1 = y.limb 1 ∧ x.limb 2 = y.limb 2) := by
    constructor
    · rintro rfl; simp
    · rintro ⟨h0, h1, h2⟩; apply E.ext; intro i; fin_cases i <;> assumption
  simp only [this]

/-- The values `f i, …, f (n - 1)`. -/
def ofFnFrom {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) : List α :=
  if h : i < n then f ⟨i, h⟩ :: ofFnFrom f (i + 1) else []
termination_by n - i

theorem ofFnFrom_eq {α : Type} {n : ℕ} (f : Fin n → α) :
    ∀ k i, n - i = k → ofFnFrom f i = (List.ofFn f).drop i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    rw [ofFnFrom, dite_eq_right_iff.2 (fun h ↦ absurd h (by omega))]
    simp [show n ≤ i by omega]
  | succ k ih =>
    intro i hi
    have hin : i < n := by omega
    rw [ofFnFrom]
    simp only [hin, ↓reduceDIte]
    rw [ih (i + 1) (by omega)]
    have hl : i < (List.ofFn f).length := by simp; omega
    rw [List.drop_eq_getElem_cons hl]
    simp

/-- The indices `i, …, n - 1` of `Fin n` (`List.finRange`'s, without a type parameter: its
element type depends on `n`). -/
def finRangeFrom (n i : ℕ) : List (Fin n) :=
  if h : i < n then ⟨i, h⟩ :: finRangeFrom n (i + 1) else []
termination_by n - i

theorem finRangeFrom_eq (n : ℕ) : ∀ i, finRangeFrom n i = ofFnFrom (fun j : Fin n ↦ j) i := by
  intro i
  induction h : n - i generalizing i with
  | zero =>
    rw [finRangeFrom, ofFnFrom]
    simp [show ¬ i < n by omega]
  | succ k ih =>
    rw [finRangeFrom, ofFnFrom]
    simp only [show i < n by omega, ↓reduceDIte, ih (i + 1) (by omega)]

theorem listFinRange (n : ℕ) : List.finRange n = finRangeFrom n 0 := by
  rw [finRangeFrom_eq, ofFnFrom_eq _ n 0 (by omega), List.drop_zero, List.finRange]

/-- `Array.ofFn` through a list. -/
theorem arrOfFn {α : Type} {n : ℕ} (f : Fin n → α) : Array.ofFn f = (ofFnFrom f 0).toArray := by
  apply Array.ext'
  rw [Array.toList_ofFn, List.toList_toArray, ofFnFrom_eq f n 0 (by omega), List.drop_zero]

/-- `Nat.log2` by halving. -/
def log2Rec (n : ℕ) : ℕ := if 2 ≤ n then log2Rec (n / 2) + 1 else 0
termination_by n
decreasing_by omega

theorem natLog2 (n : ℕ) : Nat.log2 n = log2Rec n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.log2_def, log2Rec]
    split
    · rw [ih (n / 2) (by omega)]
    · rfl

/-- The product `f 0 * … * f (n - 1)`, from the left. -/
def prodRange {M : Type} [CommMonoid M] (f : ℕ → M) : ℕ → M
  | 0 => 1
  | n + 1 => prodRange f n * f n

/-- A product over `range n`: `prodRange`. -/
theorem finsetProdRange {M : Type} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∏ v ∈ Finset.range n, f v = prodRange f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.prod_range_succ, ih, prodRange]

theorem listOfFn {α : Type} {n : ℕ} (f : Fin n → α) : List.ofFn f = ofFnFrom f 0 := by
  rw [ofFnFrom_eq f n 0 (by omega), List.drop_zero]

theorem vecOfFn {α : Type} {n : ℕ} (f : Fin n → α) : Vector.ofFn f = ⟨Array.ofFn f, by simp⟩ := rfl

theorem arrMap {α β : Type} (f : α → β) (a : Array α) : a.map f = (a.toList.map f).toArray := by
  apply Array.ext'; simp

theorem arrFoldl {α β : Type} (f : β → α → β) (b : β) (a : Array α) :
    a.foldl f b = a.toList.foldl f b := by simp [Array.foldl_toList]

theorem arrFoldr {α β : Type} (f : α → β → β) (b : β) (a : Array α) :
    a.foldr f b = a.toList.foldr f b := by simp [Array.foldr_toList]

theorem arrFilter {α : Type} (p : α → Bool) (a : Array α) :
    a.filter p = (a.toList.filter p).toArray := by
  apply Array.ext'; simp

theorem arrIsEqv {α : Type} [BEq α] (a b : Array α) (r : α → α → Bool) :
    a.isEqv b r = a.toList.isEqv b.toList r := (Array.isEqv_toList a b).symm

theorem arrBEq {α : Type} [BEq α] (a b : Array α) : (a == b) = (a.toList == b.toList) :=
  (Array.beq_toList a b).symm

theorem arrAny {α : Type} (p : α → Bool) (a : Array α) : a.any p = a.toList.any p := by simp

theorem arrAll {α : Type} (p : α → Bool) (a : Array α) : a.all p = a.toList.all p := by simp

theorem arrZipIdx {α : Type} (a : Array α) (k : ℕ) : a.zipIdx k = (a.toList.zipIdx k).toArray := by
  apply Array.ext'; simp

theorem arrMapIdx {α β : Type} (f : ℕ → α → β) (a : Array α) :
    a.mapIdx f = ((a.toList.zipIdx).map fun p ↦ f p.2 p.1).toArray := by
  apply Array.ext'; simp [List.mapIdx_eq_zipIdx_map]

theorem listMapIdx {α β : Type} (f : ℕ → α → β) (l : List α) :
    l.mapIdx f = (l.zipIdx).map fun p ↦ f p.2 p.1 := List.mapIdx_eq_zipIdx_map

/-- `a ^ n` by squaring. -/
def powSq {M : Type} [Monoid M] (a : M) (n : ℕ) : M :=
  if n = 0 then 1 else
    let r := powSq (a * a) (n / 2)
    if n % 2 = 1 then a * r else r
termination_by n
decreasing_by omega

theorem powSq_eq {M : Type} [Monoid M] : ∀ (n : ℕ) (a : M), powSq a n = a ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a
    rw [powSq]
    by_cases h : n = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [ih (n / 2) (by omega), ← pow_two, ← pow_mul]
      conv_rhs => rw [← Nat.mod_add_div n 2]
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h2, pow_succ', pow_add]

theorem pow_eq_powSq {M : Type} [Monoid M] (a : M) (n : ℕ) : a ^ n = powSq a n :=
  (powSq_eq n a).symm

theorem natSucc (n : ℕ) : Nat.succ n = n + 1 := rfl

/-- A limb of `E` at a variable index: from the list of the three. -/
theorem eLimbVar (x : E) (i : Fin 3) : x.limb i = [x.limb 0, x.limb 1, x.limb 2].getD i.val 0 := by
  fin_cases i <;> rfl

/-- An `if` of functions, applied: each branch applied. -/
theorem iteApp {α β : Type} (c : Prop) [Decidable c] (f g : α → β) (x : α) :
    (if c then f else g) x = if c then f x else g x := by
  split <;> rfl

theorem diteApp {α β : Type} (c : Prop) [Decidable c] (f : c → α → β) (g : ¬c → α → β) (x : α) :
    (if h : c then f h else g h) x = if h : c then f h x else g h x := by
  split <;> rfl

/-- Equality of a subtype's elements: of their values. -/
theorem decideEqSubtype {α : Type} {p : α → Prop} [DecidableEq α] (a b : Subtype p)
    {inst : Decidable (a = b)} : @decide (a = b) inst = decide (a.val = b.val) := by
  simp only [Subtype.ext_iff]

/-- A statement for every `i : Fin n`, decided by `Array.all` over the indices. -/
theorem decideForallFin {n : ℕ} (p : Fin n → Prop) [DecidablePred p] {inst : Decidable (∀ i, p i)} :
    @decide (∀ i, p i) inst = (Array.ofFn (n := n) id).all fun i ↦ decide (p i) := by
  rw [Bool.eq_iff_iff, Array.all_iff_forall]
  simp only [Array.size_ofFn, Array.getElem_ofFn, id, decide_eq_true_eq]
  exact ⟨fun h i hi _ ↦ h _, fun h i ↦ h i.val i.isLt ⟨Nat.zero_le _, i.isLt⟩⟩

/-- Equality in `Fin n`: of the values. -/
theorem decideEqFin {n : ℕ} (a b : Fin n) {inst : Decidable (a = b)} :
    @decide (a = b) inst = decide (a.val = b.val) :=
  decide_eq_decide.2 Fin.val_inj.symm

/-- A statement for every member of a list, decided by `List.all`. -/
theorem decideBAll {α : Type} (l : List α) (p : α → Prop) [DecidablePred p]
    {inst : Decidable (∀ x ∈ l, p x)} : @decide (∀ x ∈ l, p x) inst = l.all fun x ↦ decide (p x) := by
  rw [Bool.eq_iff_iff]; simp [List.all_eq_true]

/-- Membership in a list, decided by `List.elem`. -/
theorem decideMemList {α : Type} [BEq α] [LawfulBEq α] (a : α) (l : List α)
    {inst : Decidable (a ∈ l)} : @decide (a ∈ l) inst = l.elem a := by
  rw [Bool.eq_iff_iff]; simp

/-- Equality of arrays, decided by their lists. -/
theorem decideEqArray {α : Type} [DecidableEq α] (a b : Array α) {inst : Decidable (a = b)} :
    @decide (a = b) inst = @List.beq α instBEqOfDecidableEq a.toList b.toList := by
  rw [show @List.beq α instBEqOfDecidableEq a.toList b.toList = (a.toList == b.toList) from rfl]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

end Rewrite

end

end LeanVM.Cost
