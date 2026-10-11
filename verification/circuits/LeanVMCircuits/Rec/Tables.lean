module

public import LeanVMCircuits.Rec.Ext
public import Clean.Circuit.Subcircuit
public import Clean.Circuit.Loops
public import Clean.Utils.Tactics

@[expose] public section

/-!
The recursion machine's tables over `K`: each slot's four limbs as degree-two forms of a row's columns, and each
table's identities.

A form is data in the shape the Rust prover reads (`leaf::Coord`), its constants `K` elements written as their
coefficient words. `Form.expr` reads it as a Clean expression; the identities are a Clean assertion per table. The
theorems state what the limbs are: `E = K[y] / (y^3 + y + 1)` arithmetic for `EMUL` and `EXK`, the Merkle mux for
`HASH`, a word's bits for `SPLIT`, and views of four words for `CAST`.
-/

namespace LeanVMCircuits.Rec

open Polynomial

/-! Forms over a row's columns. -/

/-- A degree-two form of a row's columns, as the prover's `leaf::Coord` writes one. -/
inductive Form where
  /-- The constant whose coefficient word is `w`. -/
  | const (w : ℕ)
  | col (c : ℕ)
  | prod (a b : ℕ)
  | sum (terms : List Form)
  deriving Repr

mutual
/-- The form's value on a row. -/
noncomputable def Form.eval (row : ℕ → K) : Form → K
  | .const w => ofWord w
  | .col c => row c
  | .prod a b => row a * row b
  | .sum terms => Form.evalSum row terms

noncomputable def Form.evalSum (row : ℕ → K) : List Form → K
  | [] => 0
  | t :: ts => t.eval row + Form.evalSum row ts
end

mutual
/-- The form as a Clean expression of the column variables. -/
noncomputable def Form.expr : Form → Expression K
  | .const w => .const (ofWord w)
  | .col c => var ⟨c⟩
  | .prod a b => var ⟨a⟩ * var ⟨b⟩
  | .sum terms => Form.exprSum terms

noncomputable def Form.exprSum : List Form → Expression K
  | [] => .const 0
  | t :: ts => t.expr + Form.exprSum ts
end

/-- The Clean environment of a row. -/
def rowEnv (row : ℕ → K) : Environment K := { get := row, data := fun _ _ => #[] }

mutual
theorem Form.eval_expr (row : ℕ → K) : (form : Form) → form.expr.eval (rowEnv row) = form.eval row
  | .const w => rfl
  | .col c => rfl
  | .prod a b => rfl
  | .sum terms => by rw [Form.expr, Form.eval]; exact Form.evalSum_exprSum row terms

theorem Form.evalSum_exprSum (row : ℕ → K) : (terms : List Form) →
    (Form.exprSum terms).eval (rowEnv row) = Form.evalSum row terms
  | [] => rfl
  | t :: ts => by
    rw [Form.exprSum, Form.evalSum]
    show t.expr.eval (rowEnv row) + (Form.exprSum ts).eval (rowEnv row) = _
    rw [Form.eval_expr row t, Form.evalSum_exprSum row ts]
end

theorem ofWord_zero : ofWord 0 = 0 := by simp [ofWord, ev_zero]

def Form.zero : Form := .const 0

def kSlot (c : ℕ) : List Form := [.col c, .zero, .zero, .zero]
def eSlot (c : ℕ) : List Form := [.col c, .col (c + 1), .col (c + 2), .zero]
def dSlot (c : ℕ) : List Form := [.col c, .col (c + 1), .col (c + 2), .col (c + 3)]

/-- The `E` element of a slot's first three limbs. -/
noncomputable def slotE (row : ℕ → K) (slot : List Form) : E :=
  toE ((slot.getD 0 .zero).eval row) ((slot.getD 1 .zero).eval row) ((slot.getD 2 .zero).eval row)

/-! `EMUL`: columns `a0..a2, b0..b2, d0..d2`; slots `a`, `b`, `d`, `c = a·b + d`. -/

/-- `p_i = sum_{j + l = i} a_j b_l`, `j` ascending. -/
def emulProduct (i : ℕ) : List Form :=
  ((List.range 3).filter fun j => j ≤ i ∧ i - j < 3).map fun j => .prod j (3 + i - j)

def emulLimb (parts : List ℕ) (d : ℕ) : Form := .sum (parts.flatMap emulProduct ++ [.col d])

def emul : List (List Form) :=
  [eSlot 0, eSlot 3, eSlot 6, [emulLimb [0, 3] 6, emulLimb [1, 3, 4] 7, emulLimb [2, 4] 8, .zero]]

theorem emul_eq : emul = [eSlot 0, eSlot 3, eSlot 6,
    [.sum [.prod 0 3, .prod 1 5, .prod 2 4, .col 6], .sum [.prod 0 4, .prod 1 3, .prod 1 5, .prod 2 4, .prod 2 5, .col 7],
      .sum [.prod 0 5, .prod 1 4, .prod 2 3, .prod 2 5, .col 8], .zero]] := rfl

theorem emul_spec (row : ℕ → K) :
    slotE row (emul.getD 3 []) = slotE row (emul.getD 0 []) * slotE row (emul.getD 1 []) +
      slotE row (emul.getD 2 []) ∧ ((emul.getD 3 []).getD 3 .zero).eval row = 0 := by
  rw [emul_eq]
  refine ⟨?_, by simp [Form.zero, Form.eval, ofWord_zero]⟩
  simp only [slotE, eSlot, List.getD_cons_succ, List.getD_cons_zero, Form.eval, Form.evalSum, toE_mul, toE_add]
  simp only [toE, emb_add, emb_mul, emb_zero]
  ring

/-! `EXK`: columns `a0..a2, k, d0..d2`; slots `a`, `k`, `d`, `c = a·k + d`. -/

def exk : List (List Form) :=
  [eSlot 0, kSlot 3, eSlot 4, [.sum [.prod 0 3, .col 4], .sum [.prod 1 3, .col 5], .sum [.prod 2 3, .col 6], .zero]]

theorem exk_spec (row : ℕ → K) :
    slotE row (exk.getD 3 []) = slotE row (exk.getD 0 []) * emb (((exk.getD 1 []).getD 0 .zero).eval row) +
      slotE row (exk.getD 2 []) ∧ ((exk.getD 3 []).getD 3 .zero).eval row = 0 := by
  refine ⟨?_, by simp [exk, Form.zero, Form.eval, ofWord_zero]⟩
  simp only [exk, slotE, eSlot, kSlot, List.getD_cons_succ, List.getD_cons_zero, Form.eval, Form.evalSum,
    toE_smul, toE_add]
  simp only [toE, emb_add, emb_mul, emb_zero]
  ring

/-! `HASH`: its 18 ports (`t`, `f`, `h0..h3`, `m0..m7`, `o0..o3` at columns 0, 1, 2, 6, 14) and the mux bit at 18. -/

def hashT : ℕ := 0
def hashF : ℕ := 1
def hashH : ℕ := 2
def hashM : ℕ := 6
def hashO : ℕ := 14
def hashSel : ℕ := 18

/-- Limb `i` of the Merkle mux: `m_i` at `b = 0`, `m_{4+i}` at `b = 1`. -/
def muxLimb (i : ℕ) : Form := .sum [.col (hashM + i), .prod hashSel (hashM + i), .prod hashSel (hashM + 4 + i)]

def hash : List (List Form) :=
  [dSlot hashH, [.col hashT, .col hashF, .zero, .zero], (List.range 4).map muxLimb, kSlot hashSel,
    eSlot (hashM + 4), kSlot (hashM + 7), dSlot hashO, eSlot hashO] ++
  (List.range 8).map fun i => kSlot (hashM + i)

/-! Identities: forms of a row's columns that vanish, with `K` coefficients. -/

/-- `sum_c w_c · col_c + sum w · col_a · col_b`, coefficients as words. -/
structure Identity where
  linear : List (ℕ × ℕ)
  prods : List (ℕ × ℕ × ℕ)
  deriving Repr

noncomputable def Identity.eval (row : ℕ → K) (id : Identity) : K :=
  (id.linear.map fun (c, w) => ofWord w * row c).sum + (id.prods.map fun (a, b, w) => ofWord w * (row a * row b)).sum

/-- `c^2 + c`, which vanishes exactly when column `c` is 0 or 1. -/
def boolean (c : ℕ) : Identity := { linear := [(c, 1)], prods := [(c, c, 1)] }

theorem ofWord_one : ofWord 1 = 1 := by simp [ofWord, ev_one]

theorem add_eq_zero_iff_eq (a b : K) : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, neg_eq_self]

theorem boolean_spec (row : ℕ → K) (c : ℕ) : (boolean c).eval row = 0 ↔ row c = 0 ∨ row c = 1 := by
  simp only [Identity.eval, boolean, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ofWord_one, one_mul,
    add_zero]
  constructor
  · intro h
    have h' : row c * (row c + 1) = 0 := by rw [mul_add, mul_one, add_comm]; exact h
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr ((add_eq_zero_iff_eq _ _).mp h1)
  · rintro (h | h) <;> rw [h] <;> simp [← two_mul, two_K]

def hashIdentities : List Identity := [boolean hashSel]

theorem hash_mux (row : ℕ → K) (hid : ∀ id ∈ hashIdentities, id.eval row = 0) (i : ℕ) (hi : i < 4) :
    (((hash.getD 2 []).getD i .zero).eval row = if row hashSel = 0 then row (hashM + i) else row (hashM + 4 + i)) ∧
      (row hashSel = 0 ∨ row hashSel = 1) := by
  have hb := (boolean_spec row hashSel).mp (hid _ (by simp [hashIdentities]))
  refine ⟨?_, hb⟩
  have hlimb : (hash.getD 2 []).getD i .zero = muxLimb i := by
    simp [hash, List.getD_eq_getElem?_getD, hi]
  rw [hlimb]
  simp only [muxLimb, Form.eval, Form.evalSum, add_zero]
  rcases hb with h | h <;> rw [h] <;> simp
  rw [← add_assoc, ← two_mul, two_K, zero_mul, zero_add]

/-! `SPLIT`: a word at column 0 and its 64 bits at 1..64, every slot one column. -/

def split : List (List Form) := (List.range 65).map kSlot

/-- `w + sum_i x^i b_i`, which vanishes when `w` is the sum of its bits' monomials. -/
def splitWord : Identity := { linear := (0, 1) :: (List.range 64).map (fun i => (1 + i, 2 ^ i)), prods := [] }

def splitIdentities : List Identity := splitWord :: (List.range 64).map (fun i => boolean (1 + i))

/-- The bits read off the bit columns. -/
noncomputable def bitsOf (row : ℕ → K) (i : ℕ) : ZMod 2 := if row (1 + i) = 1 then 1 else 0

theorem list_sum_range (f : ℕ → K) (m : ℕ) : ((List.range m).map f).sum = ∑ i : Fin m, f i := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_castSucc]; simp

theorem split_spec (row : ℕ → K) (hid : ∀ id ∈ splitIdentities, id.eval row = 0) :
    (∀ i < 64, row (1 + i) = 0 ∨ row (1 + i) = 1) ∧ toWord (row 0) = num (bitsOf row) 64 := by
  have hbits : ∀ i < 64, row (1 + i) = 0 ∨ row (1 + i) = 1 := fun i hi =>
    (boolean_spec row (1 + i)).mp (hid _ (by simp [splitIdentities]; exact Or.inr ⟨i, hi, rfl⟩))
  refine ⟨hbits, ?_⟩
  have hw := hid splitWord (by simp [splitIdentities])
  set n := num (bitsOf row) 64
  have hn : n < 2 ^ 64 := num_lt _ _
  have hpow : ∀ i < 64, ofWord (2 ^ i) = root ^ i := by
    intro i hi
    rw [ofWord, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi), show 2 ^ i = 2 ^ i * 1 by ring,
      ev_two_pow_mul, ev_one, mul_one]
  have hterm : ∀ i < 64, ofWord (2 ^ i) * row (1 + i) = bitZ n i • root ^ i := by
    intro i hi
    have hb : bitZ n i = bitsOf row i := by
      unfold bitZ
      rw [testBit_num _ _ _ hi]
      rcases zmod2_cases (bitsOf row i) with h | h <;> simp [h]
    rw [hpow i hi, hb, bitsOf]
    rcases hbits i hi with h | h <;> simp [h]
  have hsum : (List.map (fun i => ofWord (2 ^ i) * row (1 + i)) (List.range 64)).sum = ev n := by
    rw [ev_eq_sum 64 n hn, list_sum_range]
    exact Finset.sum_congr rfl fun i _ => hterm i i.isLt
  have hrow : row 0 = ev n := by
    simp only [Identity.eval, splitWord, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
      ofWord_one, one_mul, List.map_map] at hw
    rw [← hsum]
    exact (add_eq_zero_iff_eq _ _).mp hw
  rw [hrow]
  have := toWord_ofWord n hn
  rwa [ofWord, Nat.mod_eq_of_lt hn] at this

/-! `CAST`: four words as a digest, an `E` element, two halves and four `K` words. -/

def cast : List (List Form) :=
  [dSlot 0, eSlot 0, [.col 0, .col 1, .zero, .zero], [.col 2, .col 3, .zero, .zero], kSlot 0, kSlot 1, kSlot 2,
    kSlot 3]

/-! Slot indices: where the builder places each wire of a row, printed into Rust as the indices it writes. -/

/-- `EMUL`'s and `EXK`'s slots: `a`, then `b` (`k`), then `d`, then `c = a·b + d`. -/
def arithA : ℕ := 0
def arithB : ℕ := 1
def arithD : ℕ := 2
def arithC : ℕ := 3

/-- `HASH`'s slots: chaining value, counter and finalization, mux, mux bit, `x`, `ds`, output, challenge, then the
eight message words. -/
def hashSlotH : ℕ := 0
def hashSlotTF : ℕ := 1
def hashSlotMux : ℕ := 2
def hashSlotSel : ℕ := 3
def hashSlotX : ℕ := 4
def hashSlotDs : ℕ := 5
def hashSlotOut : ℕ := 6
def hashSlotCh : ℕ := 7
def hashSlotM : ℕ := 8

/-- `SPLIT`'s slots: the word, then its 64 bits. -/
def splitSlotWord : ℕ := 0
def splitSlotBits : ℕ := 1

/-- `CAST`'s slots: the digest, the element, the two halves, then the four words. -/
def castDigest : ℕ := 0
def castElement : ℕ := 1
def castHalves : ℕ := 2
def castWords : ℕ := 4

/-! The identities as a Clean assertion over a row. -/

/-- The identity as a Clean expression of the row's column variables. -/
noncomputable def Identity.expr {n : ℕ} (row : Vector (Expression K) n) (id : Identity) : Expression K :=
  (id.linear.map fun (c, w) => Expression.const (ofWord w) * row.getD c (.const 0)).foldr (· + ·) (.const 0) +
    (id.prods.map fun (a, b, w) =>
      Expression.const (ofWord w) * (row.getD a (.const 0) * row.getD b (.const 0))).foldr (· + ·) (.const 0)

theorem foldr_eval (env : Environment K) (l : List (Expression K)) :
    (l.foldr (· + ·) (Expression.const 0)).eval env = (l.map (Expression.eval env)).sum := by
  induction l with
  | nil => rfl
  | cons e l ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ← ih]; rfl

theorem Identity.eval_expr {n : ℕ} (env : Environment K) (row : Vector (Expression K) n) (id : Identity) :
    (id.expr row).eval env = id.eval fun c => (row.getD c (.const 0)).eval env := by
  show (Expression.eval env _ + Expression.eval env _) = _
  rw [foldr_eval, foldr_eval, Identity.eval, List.map_map, List.map_map]
  rfl

/-- Assert every identity of a row. -/
noncomputable def assertAll {n : ℕ} (row : Vector (Expression K) n) : List Identity → Circuit K Unit
  | [] => pure ()
  | id :: ids => do
    assertZero (id.expr row)
    assertAll row ids

theorem assertAll_localLength {n : ℕ} (row : Vector (Expression K) n) (ids : List Identity) (offset : ℕ) :
    (assertAll row ids).localLength offset = 0 := by
  induction ids generalizing offset with
  | nil => rfl
  | cons id ids ih => simp only [assertAll, circuit_norm] at ih ⊢; exact ih _

theorem assertAll_holds {n : ℕ} (env : Environment K) (row : Vector (Expression K) n) (ids : List Identity)
    (offset : ℕ) :
    ConstraintsHold.Soundness env ((assertAll row ids).operations offset) ↔
      ∀ id ∈ ids, (id.expr row).eval env = 0 := by
  induction ids generalizing offset with
  | nil => simp [assertAll, circuit_norm]
  | cons id ids ih =>
    simp only [assertAll, circuit_norm] at ih ⊢
    rw [ih]
    simp

theorem assertAll_complete {n : ℕ} (env : ProverEnvironment K) (row : Vector (Expression K) n)
    (ids : List Identity) (offset : ℕ) :
    ConstraintsHold.Completeness env ((assertAll row ids).operations offset) ↔
      ∀ id ∈ ids, (id.expr row).eval env = 0 := by
  induction ids generalizing offset with
  | nil => simp [assertAll, circuit_norm]
  | cons id ids ih =>
    simp only [assertAll, circuit_norm] at ih ⊢
    rw [ih]
    simp

theorem assertAll_consistent {n : ℕ} (row : Vector (Expression K) n) (ids : List Identity) (offset : ℕ) :
    ((assertAll row ids).operations offset).SubcircuitsConsistent offset := by
  induction ids generalizing offset with
  | nil => simp [assertAll, circuit_norm]
  | cons id ids ih =>
    simp only [assertAll, circuit_norm] at ih ⊢
    simp_all

theorem assertAll_channels {n : ℕ} (row : Vector (Expression K) n) (ids : List Identity) (offset : ℕ) :
    ((assertAll row ids).operations offset).ChannelsLawful [] := by
  induction ids generalizing offset with
  | nil => simp [assertAll, circuit_norm]
  | cons id ids ih =>
    simp only [assertAll, circuit_norm] at ih ⊢
    simp_all

theorem assertAll_requirements {n : ℕ} (row : Vector (Expression K) n) (ids : List Identity) (offset : ℕ) :
    ((assertAll row ids).operations offset).RequirementsChannelsLawful [] [] := by
  induction ids generalizing offset with
  | nil => simp [assertAll, circuit_norm]
  | cons id ids ih =>
    simp only [assertAll, circuit_norm] at ih ⊢
    simp_all

theorem assertAll_exposed {n : ℕ} (row : Vector (Expression K) n) (ids : List Identity) (offset : ℕ) :
    ((assertAll row ids).operations offset).ExposedChannelsLawful [] := by
  induction ids generalizing offset with
  | nil => simp [assertAll, circuit_norm]
  | cons id ids ih =>
    simp only [assertAll, circuit_norm] at ih ⊢

theorem getD_eval {n : ℕ} (env : Environment K) (row : Vector (Expression K) n) (c : ℕ) :
    (row.getD c (.const 0)).eval env = (eval env row : Vector K n).getD c 0 := by
  simp only [circuit_norm, Vector.getD]
  by_cases hc : c < n
  · simp [hc]
  · simp [hc, Expression.eval]

theorem assertAll_requirementsHold {n : ℕ} (row : Vector (Expression K) n) (ids : List Identity) (offset : ℕ)
    (env : Environment K) : Operations.Requirements env ((assertAll row ids).operations offset) := by
  induction ids generalizing offset with
  | nil => simp [assertAll, circuit_norm]
  | cons id ids ih =>
    simp only [assertAll, circuit_norm] at ih ⊢
    simp_all

/-- A table's identities as a Clean assertion on its `n` columns: it holds exactly when every identity vanishes. -/
noncomputable def identities (n : ℕ) (ids : List Identity) : FormalAssertion K (fields n) where
  main row := assertAll row ids
  elaborated := {
    localLength _ := 0
    localLength_eq row offset := assertAll_localLength row ids offset
    subcircuitsConsistent row offset := assertAll_consistent row ids offset
    channelsLawful := fun row offset => assertAll_channels row ids offset }
  Spec row := ∀ id ∈ ids, id.eval (fun c => row.getD c 0) = 0
  soundness := by
    intro offset env row_var row h_eval _ h_holds
    rw [assertAll_holds] at h_holds
    refine ⟨fun id hid => ?_, by simpa [circuit_norm] using assertAll_requirementsHold row_var ids offset env⟩
    have := h_holds id hid
    rw [Identity.eval_expr] at this
    rw [← h_eval]
    convert this using 2
    funext c
    exact (getD_eval env row_var c).symm
  completeness := by
    intro offset env row_var _ row h_eval _ h_spec
    rw [assertAll_complete]
    intro id hid
    rw [Identity.eval_expr]
    have := h_spec id hid
    have h_eval' : eval env.toEnvironment row_var = row := by rw [← h_eval]; simp [circuit_norm]
    rw [← h_eval'] at this
    convert this using 2
    funext c
    exact getD_eval env.toEnvironment row_var c
  exposedChannels_eq row offset := assertAll_exposed row ids offset
  requirementsChannelsLawful row offset := assertAll_requirements row ids offset

end LeanVMCircuits.Rec
