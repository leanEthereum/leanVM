/-
  LeanVM.Guest.B1.Tables.VerifyTablesPoly

  Straight-line arithmetic by reflection: a run of atoms executed symbolically, and polynomial
  normal forms compared by the kernel.
-/

module

public import LeanVM.Guest.B1.Tables.GkrBase

/-!
# Straight-line arithmetic by reflection

`verify_tables` computes its bus decomposition and its table forms in thousands of additions
and products. A run of atoms is executed symbolically (`symExec`): each value an atom defines
becomes an expression (`Ex`) over the values it does not define, the loads of a given table
(`LoadTab`) replaced by their known expressions. When the atoms hold, every value equals its
expression (`symExec_sound`). Expressions are compared through their normal forms as
polynomials with coefficients in `K` (`Ex.norm`): equal normal forms give equal values
(`Ex.eval_eq_of_norm`), and the kernel computes and compares the forms.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1

@[expose] public section

theorem ofK_add' (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_mul' (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem word_ofK (c : ℕ) : word c 0 0 = ofK (K.ofBits c) := by rw [word_eOfNat]; rfl

/-! ## Expressions -/

/-- An expression over the values (by number) and named quantities (`ext`), with coefficients
in `K`. -/
inductive Ex where
  | var (k : ℕ)
  | ext (k : ℕ)
  | lit (c : K)
  | add (a b : Ex)
  | mul (a b : Ex)
  deriving Inhabited

/-- An expression's value, the values given by `ρ` and the named quantities by `χ`. -/
def Ex.eval (ρ χ : ℕ → E) : Ex → E
  | .var k => ρ k
  | .ext k => χ k
  | .lit c => ofK c
  | .add a b => a.eval ρ χ + b.eval ρ χ
  | .mul a b => a.eval ρ χ * b.eval ρ χ

/-! ## Symbolic execution -/

/-- The loads with a known value: `((pointer, offset), expression)`. -/
abbrev LoadTab : Type := List ((ℕ × ℕ) × Ex)

/-- The expressions bound so far: `(value, expression)`, the latest first. -/
abbrev Binds : Type := List (ℕ × Ex)

/-- The expression of value `k`: its latest binding, or itself. -/
def Binds.get (m : Binds) (k : ℕ) : Ex :=
  match m.find? (·.1 = k) with
  | some (_, e) => e
  | none => .var k

/-- One atom, symbolically: the value it defines gets its expression (a constant in `K`, a sum,
a product, a copy, a load of the table). Other atoms leave the bindings as they are. -/
def symStep (L : LoadTab) (m : Binds) : Atom → Binds
  | .const ⟨[], 0, d⟩ c => if c.limb 1 = 0 ∧ c.limb 2 = 0 then (d, .lit (c.limb 0)) :: m else m
  | .add ⟨[], 0, d⟩ ⟨[], 0, a⟩ ⟨[], 0, b⟩ => (d, .add (m.get a) (m.get b)) :: m
  | .mul ⟨[], 0, d⟩ ⟨[], 0, a⟩ ⟨[], 0, b⟩ => (d, .mul (m.get a) (m.get b)) :: m
  | .copy ⟨[], 0, d⟩ ⟨[], 0, a⟩ => (d, m.get a) :: m
  | .load ⟨[], 0, d⟩ ⟨[], 0, p⟩ off =>
    match L.find? (·.1 = (p, off)) with
    | some (_, e) => (d, e) :: m
    | none => m
  | _ => m

/-- A run of atoms, symbolically. -/
def symExec (L : LoadTab) (m : Binds) (atoms : List Atom) : Binds := atoms.foldl (symStep L) m

/-- Every binding is the value it names. -/
def Binds.Sound (ρ χ : ℕ → E) (m : Binds) : Prop := ∀ p ∈ m, ρ p.1 = p.2.eval ρ χ

theorem Binds.get_sound {ρ χ : ℕ → E} {m : Binds} (h : m.Sound ρ χ) (k : ℕ) :
    ρ k = (m.get k).eval ρ χ := by
  unfold Binds.get
  split
  · next e he =>
    have hm := List.mem_of_find?_eq_some he
    have hk := List.find?_some he
    simp only [decide_eq_true_eq] at hk
    have := h _ hm
    rw [hk] at this
    exact this
  · rfl

/-- Every entry of a load table is the word its load reads. -/
def LoadTab.Sound (rd : Reader) (σ : Val) (χ : ℕ → E) (L : LoadTab) : Prop :=
  ∀ q ∈ L, ∀ w, LoadHolds rd (σ (.n q.1.1)) q.1.2 w → w = q.2.eval (fun k => σ (.n k)) χ

theorem symStep_sound {rd : Reader} {σ : Val} {χ : ℕ → E} {L : LoadTab} (hL : L.Sound rd σ χ)
    {m : Binds} (hm : m.Sound (fun k => σ (.n k)) χ) {a : Atom} (ha : a.Holds rd σ) :
    (symStep L m a).Sound (fun k => σ (.n k)) χ := by
  intro p hp
  unfold symStep at hp
  split at hp
  · next d c =>
    split_ifs at hp with hc
    · rcases List.mem_cons.mp hp with rfl | hp
      · simp only [Ex.eval]
        have h' : σ (.n d) = c := ha
        rw [h']
        exact eq_ofK_limb hc
      · exact hm p hp
    · exact hm p hp
  · next d x y =>
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [Ex.eval]
      rw [← Binds.get_sound hm x, ← Binds.get_sound hm y]; exact ha
    · exact hm p hp
  · next d x y =>
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [Ex.eval]
      rw [← Binds.get_sound hm x, ← Binds.get_sound hm y]; exact ha
    · exact hm p hp
  · next d x =>
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [← Binds.get_sound hm x]; exact ha
    · exact hm p hp
  · next d q off =>
    split at hp
    · next e he =>
      rcases List.mem_cons.mp hp with rfl | hp
      · have hq := List.find?_some he
        simp only [decide_eq_true_eq] at hq
        exact hL _ (List.mem_of_find?_eq_some he) _ (by rw [hq]; exact ha)
      · exact hm p hp
    · exact hm p hp
  · exact hm p hp

/-! ## Polynomials -/

/-- A polynomial: monomials (lists of value numbers, sorted) with their coefficients. -/
abbrev Poly : Type := List (List ℕ × K)

/-- A monomial's value. -/
def monoVal (ρ : ℕ → E) (m : List ℕ) : E := (m.map ρ).prod

/-- A polynomial's value. -/
def Poly.eval (ρ : ℕ → E) (p : Poly) : E := (p.map fun t => ofK t.2 * monoVal ρ t.1).sum

/-- The environment of normal forms: value `k` is variable `2k`, quantity `k` is `2k + 1`. -/
def envOf (ρ χ : ℕ → E) (j : ℕ) : E := if j % 2 = 0 then ρ (j / 2) else χ (j / 2)

/-- Lexicographic order on monomials. -/
def monoLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && monoLt as bs)

/-- The sorted merge of two monomials: their product. -/
def monoMul : List ℕ → List ℕ → List ℕ
  | [], q => q
  | a :: p, q => monoMulAux a p (monoMul p) q
where
  monoMulAux (a : ℕ) (p : List ℕ) (rec : List ℕ → List ℕ) : List ℕ → List ℕ
    | [] => a :: p
    | b :: q => if a ≤ b then a :: rec (b :: q) else b :: monoMulAux a p rec q

/-- The sorted merge of two polynomials: their sum, like monomials combined, zeros dropped. -/
def polyAdd : Poly → Poly → Poly
  | [], q => q
  | t :: p, q => polyAddAux t p (polyAdd p) q
where
  polyAddAux (t : List ℕ × K) (p : Poly) (rec : Poly → Poly) : Poly → Poly
    | [] => t :: p
    | u :: q =>
      if t.1 = u.1 then (if t.2 + u.2 = 0 then rec q else (t.1, t.2 + u.2) :: rec q)
      else if monoLt t.1 u.1 then t :: rec (u :: q) else u :: polyAddAux t p rec q

/-- A product of coefficients, free when one of them is `1`. -/
def kMul (a b : K) : K := if a = 1 then b else if b = 1 then a else a * b

/-- A polynomial times a term. -/
def polyMulTerm (t : List ℕ × K) (q : Poly) : Poly :=
  q.foldr (fun u acc => polyAdd [(monoMul t.1 u.1, kMul t.2 u.2)] acc) []

/-- The product of two polynomials. -/
def polyMul (p q : Poly) : Poly := p.foldr (fun t acc => polyAdd (polyMulTerm t q) acc) []

/-- An expression's normal form. -/
def Ex.norm : Ex → Poly
  | .var k => [([2 * k], 1)]
  | .ext k => [([2 * k + 1], 1)]
  | .lit c => if c = 0 then [] else [([], c)]
  | .add a b => polyAdd a.norm b.norm
  | .mul a b => polyMul a.norm b.norm

theorem Poly.eval_nil (ρ : ℕ → E) : Poly.eval ρ [] = 0 := rfl

theorem Poly.eval_cons (ρ : ℕ → E) (t : List ℕ × K) (p : Poly) :
    Poly.eval ρ (t :: p) = ofK t.2 * monoVal ρ t.1 + Poly.eval ρ p := by
  simp [Poly.eval]

theorem monoVal_cons (ρ : ℕ → E) (a : ℕ) (m : List ℕ) : monoVal ρ (a :: m) = ρ a * monoVal ρ m := by
  simp [monoVal]

theorem monoMul_eval (ρ : ℕ → E) : ∀ p q, monoVal ρ (monoMul p q) = monoVal ρ p * monoVal ρ q
  | [], q => by simp [monoMul, monoVal]
  | a :: p, q => by
    have ih := monoMul_eval ρ p
    show monoVal ρ (monoMul.monoMulAux a p (monoMul p) q) = _
    induction q with
    | nil => simp [monoMul.monoMulAux, monoVal]
    | cons b q ihq =>
      simp only [monoMul.monoMulAux]
      split_ifs
      · rw [monoVal_cons, ih]; simp only [monoVal_cons]; ring
      · rw [monoVal_cons, ihq]; simp only [monoVal_cons]; ring

theorem polyAdd_eval (ρ : ℕ → E) : ∀ p q, Poly.eval ρ (polyAdd p q) = Poly.eval ρ p + Poly.eval ρ q
  | [], q => by simp [polyAdd, Poly.eval_nil]
  | t :: p, q => by
    have ih := polyAdd_eval ρ p
    show Poly.eval ρ (polyAdd.polyAddAux t p (polyAdd p) q) = _
    induction q with
    | nil => simp [polyAdd.polyAddAux, Poly.eval_nil]
    | cons u q ihq =>
      simp only [polyAdd.polyAddAux]
      split_ifs with h1 h2 h3
      · rw [ih]
        simp only [Poly.eval_cons]
        rw [← h1]
        have : ofK t.2 * monoVal ρ t.1 + ofK u.2 * monoVal ρ t.1 = 0 := by
          rw [← add_mul, ← ofK_add', h2, ofK_zero, zero_mul]
        linear_combination (-1 : E) * this
      · simp only [Poly.eval_cons]
        rw [ih, ← h1, ofK_add']
        ring
      · simp only [Poly.eval_cons]
        rw [ih]
        simp only [Poly.eval_cons]
        ring
      · simp only [Poly.eval_cons] at ihq ⊢
        rw [ihq]
        ring

theorem kMul_eq (a b : K) : kMul a b = a * b := by
  unfold kMul; split_ifs with h1 h2
  · rw [h1, one_mul]
  · rw [h2, mul_one]
  · rfl

theorem polyMulTerm_eval (ρ : ℕ → E) (t : List ℕ × K) (q : Poly) :
    Poly.eval ρ (polyMulTerm t q) = ofK t.2 * monoVal ρ t.1 * Poly.eval ρ q := by
  induction q with
  | nil => simp [polyMulTerm, Poly.eval_nil]
  | cons u q ih =>
    simp only [polyMulTerm, List.foldr_cons] at ih ⊢
    rw [polyAdd_eval, ih, Poly.eval_cons, Poly.eval_cons, Poly.eval_nil, monoMul_eval, kMul_eq,
      ofK_mul']
    ring

theorem polyMul_eval (ρ : ℕ → E) (p q : Poly) :
    Poly.eval ρ (polyMul p q) = Poly.eval ρ p * Poly.eval ρ q := by
  induction p with
  | nil => simp [polyMul, Poly.eval_nil]
  | cons t p ih =>
    simp only [polyMul, List.foldr_cons] at ih ⊢
    rw [polyAdd_eval, ih, polyMulTerm_eval, Poly.eval_cons]; ring

theorem Ex.norm_eval (ρ χ : ℕ → E) : ∀ e : Ex, Poly.eval (envOf ρ χ) e.norm = e.eval ρ χ
  | .var k => by simp [Ex.norm, Ex.eval, Poly.eval, monoVal, envOf]
  | .ext k => by
    simp only [Ex.norm, Ex.eval, Poly.eval, monoVal, envOf, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, ofK_one]
    rw [ite_neg' (by omega), show (2 * k + 1) / 2 = k by omega]
    ring
  | .lit c => by
    simp only [Ex.norm, Ex.eval]
    split_ifs with h
    · rw [h, ofK_zero]; rfl
    · simp [Poly.eval, monoVal]
  | .add a b => by
    simp only [Ex.norm, Ex.eval, polyAdd_eval, Ex.norm_eval ρ χ a, Ex.norm_eval ρ χ b]
  | .mul a b => by
    simp only [Ex.norm, Ex.eval, polyMul_eval, Ex.norm_eval ρ χ a, Ex.norm_eval ρ χ b]

/-- **Equal normal forms, equal values.** -/
theorem Ex.eval_eq_of_norm {a b : Ex} (h : a.norm = b.norm) (ρ χ : ℕ → E) :
    a.eval ρ χ = b.eval ρ χ := by
  rw [← Ex.norm_eval ρ χ a, ← Ex.norm_eval ρ χ b, h]

/-! ## Windows of a body -/

/-- A statement's atom, if it is one. -/
def atomOf : Stmt → Option Atom
  | .atom a => some a
  | _ => none

theorem symExec_sound {rd : Reader} {σ : Val} {χ : ℕ → E} {L : LoadTab} (hL : L.Sound rd σ χ) :
    ∀ (atoms : List Atom) (m : Binds), m.Sound (fun k => σ (.n k)) χ →
      (∀ a ∈ atoms, a.Holds rd σ) → (symExec L m atoms).Sound (fun k => σ (.n k)) χ
  | [], _, hm, _ => hm
  | a :: rest, _, hm, h =>
    symExec_sound hL rest _ (symStep_sound hL hm (h a (List.mem_cons_self ..)))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The atoms of a block without `ret` hold, once the block does. -/
theorem atoms_hold {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt), Stmt.noRetList ss = true → Stmt.HoldsList C rd σ ss True kret →
      ∀ a ∈ ss.filterMap atomOf, a.Holds rd σ
  | [], _, _ => by simp
  | s :: ss, hnr, h => by
    simp only [Stmt.noRetList, Bool.and_eq_true] at hnr
    simp only [Stmt.HoldsList] at h
    rw [holds_noRet s hnr.1] at h
    intro a ha
    cases s with
    | atom b =>
      simp only [List.filterMap_cons, atomOf, List.mem_cons] at ha
      rcases ha with rfl | ha
      · simpa [Stmt.Holds] using h.1
      · exact atoms_hold ss hnr.2 h.2 a ha
    | _ =>
      simp only [List.filterMap_cons, atomOf] at ha
      exact atoms_hold ss hnr.2 h.2 a ha

/-- **A value of a window of a body, by reflection**: the value `k` the atoms of statements
`n .. n + len` define is the expression `e`, when their normal forms agree. -/
theorem window_eval {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {pre : List Stmt}
    (hnr : Stmt.noRetList pre = true) (h : Stmt.HoldsList C rd σ pre True kret) {χ : ℕ → E}
    {L : LoadTab} (hL : L.Sound rd σ χ) (n len k : ℕ) (e : Ex)
    (heq : ((symExec L [] (((pre.drop n).take len).filterMap atomOf)).get k).norm = e.norm) :
    σ (.n k) = e.eval (fun k => σ (.n k)) χ := by
  have hs := symExec_sound hL (((pre.drop n).take len).filterMap atomOf) [] (fun _ h => by simp at h)
    (fun a ha => atoms_hold pre hnr h a (List.mem_filterMap.mpr (by
      obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp ha
      exact ⟨s, List.mem_of_mem_drop (List.mem_of_mem_take hs), hsa⟩)))
  rw [Binds.get_sound hs k]
  exact Ex.eval_eq_of_norm heq _ _

end
end LeanVM.Guest.B1.VerifySub
