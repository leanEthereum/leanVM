module

public import LeanVMCircuits.Multiply.Replay
public import LeanVMCircuits.Netlist

@[expose] public section

/-!
The multiplier's gates, as `Multiplier::build` emits them.

Local wire 0 is `g`, the one product before the steps. Then every row's bit, row by row, then five wires per position
per step and per position of the ripple addition: at a step, `x + z`, `y + z`, their product where the plan puts one,
the carry, the sum; at the ripple, the same with the carry in for `z`. A wire a position does not need is the zero,
which costs nothing; the products are exactly the plan's, in its order. Each wire's gate mirrors the bit it carries
in `LeanVMCircuits.Multiply.Replay`, so any assignment satisfying the gates carries those bits.
-/

namespace LeanVMCircuits.Multiply

open LeanVMCircuits Netlist

/-- Input `a_k` is input `k`, `b_k` input `64 + k`. -/
def aIn (k : ℕ) : Aff := .input k
def bIn (k : ℕ) : Aff := .input (64 + k)

/-- Row `r`'s bit at position `p` before any step, as an affine of the inputs and `g`. -/
def cellAff (n r p : ℕ) : Aff :=
  if r < 64 then
    if r ≤ p + 1 ∧ p + 1 - r < 64 then .xor (bIn (p + 1 - r)) (.xor (aIn r) .one)
    else if p = 0 ∧ r = 2 then .one else if p = 0 ∧ r = 3 then .loc 0 else .zero
  else if r = aRow then
    if p < 63 then .xor (aIn (p + 1)) .one else if p < 127 then aIn (p - 63) else if n = 128 ∧ p = 127 then .one
    else .zero
  else if r = bRow then
    if p < 63 then .xor (bIn (p + 1)) .one else if p < 127 then bIn (p - 63) else .zero
  else .zero

/-- Where the step wires start: after `g` and the rows' bits. -/
def cellsEnd (n : ℕ) : ℕ := 1 + nRows * n

def stepBase (n k : ℕ) : ℕ := cellsEnd n + 5 * n * k

/-- The rows' bits before step `k`. -/
def rowAff (n : ℕ) (steps : List Csa) : ℕ → ℕ → ℕ → Aff
  | 0, r, p => if r < nRows ∧ p < n then .loc (1 + r * n + p) else .zero
  | k + 1, r, p =>
    let s := steps.getD k default
    let base := stepBase n k
    if r = s.x then (if p < n then .loc (base + 5 * p + 4) else .zero)
    else if r = s.y then
      if 0 < p ∧ p < n ∧ bit s.products (p - 1) then .loc (base + 5 * (p - 1) + 3)
      else if p < n ∧ (bit s.moveZ p || bit s.moveY p) then .loc (base + 5 * p + 3) else .zero
    else rowAff n steps k r p

/-- The five wires of position `p` at a step on rows with bits `X`, `Y`, `Z`, from wire `w`. -/
def stepGate (s : Csa) (X Y Z : Aff) (w p j : ℕ) : Gate :=
  match j with
  | 0 => .define (if !bit s.products p && (bit s.moveZ p || bit s.moveY p) then .zero else .xor X Z)
  | 1 => .define (if bit s.products p then .xor Y Z else .zero)
  | 2 => if bit s.products p then .product (.loc w) (.loc (w + 1)) else .define .zero
  | 3 => .define (if bit s.products p then .xor (.loc (w + 2)) Z else if bit s.moveZ p then Z
      else if bit s.moveY p then Y else .zero)
  | _ => .define (if bit s.moveZ p then .xor X Y else if bit s.moveY p then X else .xor (.loc w) Y)

/-- The ripple's wires start after the steps'. -/
def rippleBase (n S : ℕ) : ℕ := stepBase n S

/-- The carry into position `p` of the ripple. -/
def cinAff (cm rbase p : ℕ) : Aff := if 0 < p ∧ bit cm (p - 1) then .loc (rbase + 5 * (p - 1) + 3) else .zero

/-- The five wires of position `p` of the ripple on bits `X`, `Y` and carry `C`, from wire `w`. -/
def rippleGate (cm : ℕ) (X Y C : Aff) (w p j : ℕ) : Gate :=
  match j with
  | 0 => .define (if bit cm p then .xor X C else .xor X Y)
  | 1 => .define (if bit cm p then .xor Y C else .zero)
  | 2 => if bit cm p then .product (.loc w) (.loc (w + 1)) else .define .zero
  | 3 => .define (if bit cm p then .xor (.loc (w + 2)) C else .zero)
  | _ => .define (if bit cm p then .xor (.loc w) Y else .xor (.loc w) C)

/-- The multiplier's plan and last rows for width `n`. -/
structure Layout where
  n : ℕ
  steps : List Csa
  lx : ℕ
  ly : ℕ
  cm : ℕ

def layout (n : ℕ) : Layout :=
  let steps := (plan n).1
  let live := liveAfter steps (List.range nRows)
  let present := presentFrom steps (initialPresent n)
  { n, steps, lx := live.getD 0 0, ly := live.getD 1 0,
    cm := carries n (present (live.getD 0 0)) (present (live.getD 1 0)) }

/-- Gate `i`, decoded from its index. -/
def Layout.gateAt (L : Layout) (i : ℕ) : Gate :=
  let n := L.n
  let S := L.steps.length
  if i = 0 then .product (.xor (aIn 0) .one) (.xor (bIn 0) .one)
  else if i < cellsEnd n then .define (cellAff n ((i - 1) / n) ((i - 1) % n))
  else if i < stepBase n S then
    let k := (i - cellsEnd n) / (5 * n)
    let p := ((i - cellsEnd n) % (5 * n)) / 5
    let j := (i - cellsEnd n) % 5
    let s := L.steps.getD k default
    let row := rowAff n L.steps k
    stepGate s (row s.x p) (row s.y p) (row s.z p) (stepBase n k + 5 * p) p j
  else
    let rbase := rippleBase n S
    let p := (i - rbase) / 5
    let j := (i - rbase) % 5
    let row := rowAff n L.steps S
    rippleGate L.cm (row L.lx p) (row L.ly p) (cinAff L.cm rbase p) (rbase + 5 * p) p j

def Layout.total (L : Layout) : ℕ := rippleBase L.n L.steps.length + 5 * L.n

def Layout.gates (L : Layout) : List Gate := (List.range L.total).map L.gateAt


/-! What the gates make every wire carry. -/

theorem eval_cellAff (n : ℕ) (inp loc : ℕ → Bit) (hg : loc 0 = g (fun k => inp k) (fun k => inp (64 + k)))
    (r p : ℕ) : (cellAff n r p).eval inp loc = cell n (fun k => inp k) (fun k => inp (64 + k)) r p := by
  unfold cellAff cell
  split_ifs <;> simp_all [Aff.eval, aIn, bIn, e, cbit, add_comm]

theorem rowsFrom_append (l : List Csa) (s : Csa) (rows : ℕ → ℕ → Bit) :
    rowsFrom (l ++ [s]) rows = stepRows s (rowsFrom l rows) := by
  induction l generalizing rows with
  | nil => rfl
  | cons t l ih => exact ih (stepRows t rows)

theorem rowsFrom_take_succ (l : List Csa) (k : ℕ) (hk : k < l.length) (rows : ℕ → ℕ → Bit) :
    rowsFrom (l.take (k + 1)) rows = stepRows (l.getD k default) (rowsFrom (l.take k) rows) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, rowsFrom_append,
    List.getD_eq_getElem _ _ hk]


/-- A checked plan's steps never put a product and a move at one position. -/
theorem not_move_of_check (n : ℕ) : ∀ (steps : List Csa) (live : List ℕ) (present : ℕ → ℕ),
    checkFrom n steps live present = true → ∀ s ∈ steps, ∀ p, bit s.products p = true →
      bit s.moveZ p = false ∧ bit s.moveY p = false
  | [], _, _, _, _, hs, _, _ => absurd hs List.not_mem_nil
  | t :: steps, live, present, hc, s, hs, p, hp => by
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases List.mem_cons.mp hs with rfl | hs
    · have hlt : p < 128 := by
        by_contra h
        rw [bit_lt _ p hc.1.1.1.1.2 (by omega)] at hp
        exact Bool.false_ne_true hp
      have := List.all_eq_true.mp hc.1.2 p (List.mem_range.mpr hlt)
      simp only [hp, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_true, Bool.and_false,
        Bool.or_false] at this
      constructor
      · cases h : bit s.moveZ p <;> simp_all
      · cases h : bit s.moveY p <;> simp_all
    · exact not_move_of_check n steps _ _ hc.2 s hs p hp

/-- What a step's five wires at a position carry. -/
theorem stepGate_values (s : Csa) (X Y Z : Aff) (w p : ℕ) (inp loc : ℕ → Bit)
    (hold : ∀ j, j < 5 → (stepGate s X Y Z w p j).Holds inp loc (w + j)) :
    loc (w + 4) = sumRow s (fun _ => X.eval inp loc) (fun _ => Y.eval inp loc) (fun _ => Z.eval inp loc) p ∧
      (bit s.products p = true → loc (w + 3) = maj (X.eval inp loc) (Y.eval inp loc) (Z.eval inp loc)) ∧
      (bit s.products p = false → bit s.moveZ p = true → loc (w + 3) = Z.eval inp loc) ∧
      (bit s.products p = false → bit s.moveZ p = false → bit s.moveY p = true → loc (w + 3) = Y.eval inp loc) := by
  have h0 := hold 0 (by omega); have h1 := hold 1 (by omega); have h2 := hold 2 (by omega)
  have h3 := hold 3 (by omega); have h4 := hold 4 (by omega)
  simp only [stepGate] at h0 h1 h2 h3 h4
  simp only [Nat.add_zero] at h0
  refine ⟨?_, fun hp => ?_, fun hp hz => ?_, fun hp hz hy => ?_⟩
  · unfold sumRow
    cases hz : bit s.moveZ p <;> cases hy : bit s.moveY p <;> cases hpr : bit s.products p <;>
      simp_all [Gate.Holds, Aff.eval] <;> ring
  · cases hpr : bit s.products p <;> simp_all [Gate.Holds, Aff.eval, maj]
  · simp_all [Gate.Holds, Aff.eval]
  · simp_all [Gate.Holds, Aff.eval]


/-! Decoding the gates' indices. -/

theorem gateAt_zero (L : Layout) : L.gateAt 0 = .product (.xor (aIn 0) .one) (.xor (bIn 0) .one) := by
  simp [Layout.gateAt]

theorem gateAt_cell (L : Layout) (hn : 0 < L.n) (r p : ℕ) (hr : r < nRows) (hp : p < L.n) :
    L.gateAt (1 + r * L.n + p) = .define (cellAff L.n r p) := by
  have hlt : 1 + r * L.n + p < cellsEnd L.n := by
    unfold cellsEnd
    have : r * L.n + p < nRows * L.n := by nlinarith
    omega
  have hdiv : (r * L.n + p) / L.n = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hp, Nat.zero_add]
  have hmod : (r * L.n + p) % L.n = p := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  simp only [Layout.gateAt, show ¬ (1 + r * L.n + p = 0) by omega, if_false, if_pos hlt,
    show 1 + r * L.n + p - 1 = r * L.n + p by omega, hdiv, hmod]

theorem gateAt_step (L : Layout) (hn : 0 < L.n) (k p j : ℕ) (hk : k < L.steps.length) (hp : p < L.n)
    (hj : j < 5) :
    L.gateAt (stepBase L.n k + 5 * p + j) =
      stepGate (L.steps.getD k default) (rowAff L.n L.steps k (L.steps.getD k default).x p)
        (rowAff L.n L.steps k (L.steps.getD k default).y p) (rowAff L.n L.steps k (L.steps.getD k default).z p)
        (stepBase L.n k + 5 * p) p j := by
  have hidx : stepBase L.n k + 5 * p + j - cellsEnd L.n = 5 * L.n * k + (5 * p + j) := by
    unfold stepBase; omega
  have hsmall : 5 * p + j < 5 * L.n := by omega
  have hlt : stepBase L.n k + 5 * p + j < stepBase L.n L.steps.length := by
    unfold stepBase
    have : 5 * L.n * k + 5 * L.n ≤ 5 * L.n * L.steps.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk
    omega
  have h5 : 0 < 5 * L.n := by omega
  have hdiv : (5 * L.n * k + (5 * p + j)) / (5 * L.n) = k := by
    rw [Nat.mul_add_div h5, Nat.div_eq_of_lt hsmall, Nat.add_zero]
  have hmod : (5 * L.n * k + (5 * p + j)) % (5 * L.n) = 5 * p + j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]
  have hp5 : (5 * p + j) / 5 = p := by omega
  have hj5 : (5 * L.n * k + (5 * p + j)) % 5 = j := by
    rw [show 5 * L.n * k + (5 * p + j) = 5 * (L.n * k + p) + j by ring, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  simp only [Layout.gateAt, show ¬ (stepBase L.n k + 5 * p + j = 0) by unfold stepBase cellsEnd; omega, if_false,
    show ¬ (stepBase L.n k + 5 * p + j < cellsEnd L.n) by unfold stepBase; omega, if_pos hlt, hidx, hdiv, hmod, hp5,
    hj5]

theorem gateAt_ripple (L : Layout) (p j : ℕ) (hj : j < 5) :
    L.gateAt (rippleBase L.n L.steps.length + 5 * p + j) =
      rippleGate L.cm (rowAff L.n L.steps L.steps.length L.lx p) (rowAff L.n L.steps L.steps.length L.ly p)
        (cinAff L.cm (rippleBase L.n L.steps.length) p) (rippleBase L.n L.steps.length + 5 * p) p j := by
  have hp5 : (5 * p + j) / 5 = p := by omega
  have hj5 : (5 * p + j) % 5 = j := by omega
  simp only [Layout.gateAt, rippleBase, show ¬ (stepBase L.n L.steps.length + 5 * p + j = 0) by
      unfold stepBase cellsEnd; omega, if_false,
    show ¬ (stepBase L.n L.steps.length + 5 * p + j < cellsEnd L.n) by unfold stepBase; omega,
    show ¬ (stepBase L.n L.steps.length + 5 * p + j < stepBase L.n L.steps.length) by omega,
    show stepBase L.n L.steps.length + 5 * p + j - stepBase L.n L.steps.length = 5 * p + j by omega, hp5, hj5]


/-! Every wire carries its bit. -/

/-- The inputs' bits. -/
def aBits (inp : ℕ → Bit) (k : ℕ) : Bit := inp k
def bBits (inp : ℕ → Bit) (k : ℕ) : Bit := inp (64 + k)

theorem total_gt_cells (L : Layout) (r p : ℕ) (hr : r < nRows) (hp : p < L.n) : 1 + r * L.n + p < L.total := by
  unfold Layout.total rippleBase stepBase cellsEnd
  have : r * L.n + p < nRows * L.n := by nlinarith
  omega

theorem total_gt_step (L : Layout) (k p j : ℕ) (hk : k < L.steps.length) (hp : p < L.n) (hj : j < 5) :
    stepBase L.n k + 5 * p + j < L.total := by
  unfold Layout.total rippleBase stepBase
  have : 5 * L.n * k + 5 * L.n ≤ 5 * L.n * L.steps.length := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk
  omega

theorem total_gt_ripple (L : Layout) (p j : ℕ) (hp : p < L.n) (hj : j < 5) :
    rippleBase L.n L.steps.length + 5 * p + j < L.total := by
  unfold Layout.total; omega

theorem rows_values (L : Layout) (hn : 0 < L.n) (inp loc : ℕ → Bit)
    (hold : ∀ i, i < L.total → (L.gateAt i).Holds inp loc i)
    (hdis : ∀ k, k < L.steps.length → ∀ p, bit (L.steps.getD k default).products p = true →
      bit (L.steps.getD k default).moveZ p = false ∧ bit (L.steps.getD k default).moveY p = false) :
    ∀ k, k ≤ L.steps.length → ∀ r p, p < L.n →
      (rowAff L.n L.steps k r p).eval inp loc = rowsFrom (L.steps.take k) (cellN L.n (aBits inp) (bBits inp)) r p := by
  have hg : loc 0 = g (aBits inp) (bBits inp) := by
    have := hold 0 (by unfold Layout.total rippleBase stepBase cellsEnd; omega)
    rw [gateAt_zero] at this
    simpa [Gate.Holds, Aff.eval, aIn, bIn, g, cbit, aBits, bBits, add_comm] using this
  intro k
  induction k with
  | zero =>
    intro _ r p hp
    simp only [rowAff, List.take_zero, rowsFrom, cellN, if_pos hp]
    by_cases hr : r < nRows
    · rw [if_pos ⟨hr, hp⟩]
      have := hold _ (total_gt_cells L r p hr hp)
      rw [gateAt_cell L hn r p hr hp] at this
      simp only [Gate.Holds] at this
      show loc (1 + r * L.n + p) = _
      rw [this, eval_cellAff L.n inp loc hg]
      rfl
    · rw [if_neg (fun h => hr h.1)]
      simp only [Aff.eval]
      unfold cell
      rw [if_neg (by simp [nRows] at hr; omega), if_neg (by simp [nRows, aRow] at hr ⊢; omega),
        if_neg (by simp [nRows, bRow] at hr ⊢; omega)]
  | succ k ih =>
    intro hk r p hp
    have hk' : k < L.steps.length := by omega
    have ih' := ih (by omega)
    rw [rowsFrom_take_succ _ _ hk']
    set st := L.steps.getD k default with hst
    -- Position `q`'s five wires at this step.
    have hslot : ∀ q, q < L.n → ∀ j, j < 5 →
        (stepGate st (rowAff L.n L.steps k st.x q) (rowAff L.n L.steps k st.y q) (rowAff L.n L.steps k st.z q)
          (stepBase L.n k + 5 * q) q j).Holds inp loc (stepBase L.n k + 5 * q + j) := by
      intro q hq j hj
      have := hold _ (total_gt_step L k q j hk' hq hj)
      rwa [gateAt_step L hn k q j hk' hq hj] at this
    have hv := fun q (hq : q < L.n) => stepGate_values st _ _ _ _ q inp loc (hslot q hq)
    have hval : ∀ q, q < L.n → ∀ r', (rowAff L.n L.steps k r' q).eval inp loc =
        rowsFrom (L.steps.take k) (cellN L.n (aBits inp) (bBits inp)) r' q := fun q hq r' => ih' r' q hq
    simp only [rowAff, ← hst]
    unfold stepRows
    by_cases hx : r = st.x
    · rw [if_pos hx, if_pos hx, if_pos hp]
      simp only [Aff.eval]
      rw [(hv p hp).1]
      unfold sumRow
      simp only [hval p hp]
    · rw [if_neg hx, if_neg hx]
      by_cases hy : r = st.y
      · rw [if_pos hy, if_pos hy]
        unfold carryRow
        by_cases hpr : 0 < p ∧ bit st.products (p - 1) = true
        · rw [if_pos ⟨hpr.1, hp, hpr.2⟩, if_pos hpr]
          simp only [Aff.eval]
          have hq : p - 1 < L.n := by omega
          have := (hv (p - 1) hq).2.1 hpr.2
          rw [show stepBase L.n k + 5 * (p - 1) + 3 = stepBase L.n k + 5 * (p - 1) + 3 from rfl, this]
          simp only [hval (p - 1) hq]
        · rw [if_neg (fun h => hpr ⟨h.1, h.2.2⟩), if_neg hpr]
          by_cases hm : bit st.moveZ p = true ∨ bit st.moveY p = true
          · have hprod : bit st.products p = false := by
              cases h : bit st.products p
              · rfl
              · have := hdis k hk' p h; simp_all
            rw [if_pos ⟨hp, by simpa [Bool.or_eq_true] using hm⟩]
            simp only [Aff.eval]
            by_cases hz : bit st.moveZ p = true
            · rw [(hv p hp).2.2.1 hprod hz, if_pos hz, hval p hp]
            · have hy' : bit st.moveY p = true := by simpa [hz] using hm
              rw [(hv p hp).2.2.2 hprod (by simpa using hz) hy', if_neg hz, if_pos hy', hval p hp]
          · rw [if_neg (fun h => hm (by simpa [Bool.or_eq_true] using h.2))]
            simp only [Aff.eval]
            push Not at hm
            rw [if_neg (by simp [hm.1]), if_neg (by simp [hm.2])]
      · rw [if_neg hy, if_neg hy]
        exact ih' r p hp


/-- The ripple's wires carry the carries and the sum bits. -/
theorem ripple_values (L : Layout) (inp loc : ℕ → Bit) (hold : ∀ i, i < L.total → (L.gateAt i).Holds inp loc i)
    (X Y : ℕ → Bit) (hX : ∀ p, p < L.n → (rowAff L.n L.steps L.steps.length L.lx p).eval inp loc = X p)
    (hY : ∀ p, p < L.n → (rowAff L.n L.steps L.steps.length L.ly p).eval inp loc = Y p) :
    ∀ p, p < L.n → (cinAff L.cm (rippleBase L.n L.steps.length) p).eval inp loc = cin L.cm X Y p ∧
      loc (rippleBase L.n L.steps.length + 5 * p + 4) = ripple L.cm X Y p := by
  set rb := rippleBase L.n L.steps.length
  have hslot : ∀ p, p < L.n → ∀ j, j < 5 → (rippleGate L.cm (rowAff L.n L.steps L.steps.length L.lx p)
      (rowAff L.n L.steps L.steps.length L.ly p) (cinAff L.cm rb p) (rb + 5 * p) p j).Holds inp loc (rb + 5 * p + j) :=
    fun p hp j hj => by
      have := hold _ (total_gt_ripple L p j hp hj)
      rwa [gateAt_ripple L p j hj] at this
  intro p
  induction p with
  | zero =>
    intro hp
    have hc : (cinAff L.cm rb 0).eval inp loc = cin L.cm X Y 0 := by simp [cinAff, Aff.eval, cin]
    refine ⟨hc, ?_⟩
    have h0 := hslot 0 hp 0 (by omega); have h4 := hslot 0 hp 4 (by omega)
    simp only [rippleGate, Gate.Holds, Nat.add_zero, Nat.mul_zero] at h0 h4
    unfold ripple
    rw [h4]
    cases hcm : bit L.cm 0 <;> simp_all [Aff.eval]
    ring
  | succ p ih =>
    intro hp
    obtain ⟨hcp, -⟩ := ih (by omega)
    have h0 := hslot p (by omega) 0 (by omega); have h1 := hslot p (by omega) 1 (by omega)
    have h2 := hslot p (by omega) 2 (by omega); have h3 := hslot p (by omega) 3 (by omega)
    have hc : (cinAff L.cm rb (p + 1)).eval inp loc = cin L.cm X Y (p + 1) := by
      simp only [cinAff, Nat.succ_pos, true_and, Nat.add_sub_cancel, cin]
      by_cases hcm : bit L.cm p = true
      · rw [if_pos hcm, if_pos hcm]
        simp only [rippleGate, hcm, if_true, Gate.Holds] at h0 h1 h2 h3
        simp only [Aff.eval]
        rw [h3]
        simp only [Aff.eval, Nat.add_zero] at h0 h1 h2 ⊢
        rw [h2, h0, h1, hcp, hX p (by omega), hY p (by omega)]
        rfl
      · rw [if_neg hcm, if_neg hcm]; rfl
    refine ⟨hc, ?_⟩
    have g0 := hslot (p + 1) hp 0 (by omega); have g4 := hslot (p + 1) hp 4 (by omega)
    simp only [rippleGate, Gate.Holds, Nat.add_zero] at g0 g4
    unfold ripple
    rw [g4]
    cases hcm : bit L.cm (p + 1) <;> simp_all [Aff.eval]
    ring


theorem finalSum_layout (n : ℕ) (a b : ℕ → Bit) :
    finalSum n (plan n).1 (List.range nRows) (initialPresent n) (cellN n a b) =
      ripple (layout n).cm (rowsFrom (layout n).steps (cellN n a b) (layout n).lx)
        (rowsFrom (layout n).steps (cellN n a b) (layout n).ly) := rfl

/-- Any assignment satisfying the multiplier's gates outputs `a b` modulo `2^n`. -/
theorem gates_product (n : ℕ) (hn : n = 64 ∨ n = 128) (hc : check n = true) (inp loc : ℕ → Bit)
    (hold : ∀ i, i < (layout n).total → ((layout n).gateAt i).Holds inp loc i) :
    ∃ k : ℤ, rowValue n (fun p => loc (rippleBase n (plan n).1.length + 5 * p + 4)) =
      word (aBits inp) * word (bBits inp) + 2 ^ n * k := by
  have hn0 : 0 < (layout n).n := by show 0 < n; omega
  have hdis : ∀ k, k < (layout n).steps.length → ∀ p, bit ((layout n).steps.getD k default).products p = true →
      bit ((layout n).steps.getD k default).moveZ p = false ∧ bit ((layout n).steps.getD k default).moveY p = false := by
    intro k hk
    rw [List.getD_eq_getElem _ _ hk]
    have hc' : checkFrom n (plan n).1 (List.range nRows) (initialPresent n) = true := by
      simp only [check, Bool.and_eq_true] at hc; exact hc.1
    exact not_move_of_check n _ _ _ hc' _ (List.getElem_mem hk)
  have hrows := rows_values (layout n) hn0 inp loc hold hdis (layout n).steps.length le_rfl
  rw [List.take_length] at hrows
  have hrip := ripple_values (layout n) inp loc hold
    (rowsFrom (layout n).steps (cellN n (aBits inp) (bBits inp)) (layout n).lx)
    (rowsFrom (layout n).steps (cellN n (aBits inp) (bBits inp)) (layout n).ly)
    (fun p hp => hrows (layout n).lx p hp) (fun p hp => hrows (layout n).ly p hp)
  obtain ⟨k, hk⟩ := product_value n hn hc (aBits inp) (bBits inp)
  refine ⟨k, ?_⟩
  rw [← hk, finalSum_layout]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p < (layout n).n := Finset.mem_range.mp hp
  show 2 ^ p * iv (loc (rippleBase (layout n).n (layout n).steps.length + 5 * p + 4)) = _
  rw [(hrip p hp').2]


/-! Every gate names only earlier wires. -/

theorem wellOrdered_map (f : ℕ → Gate) : ∀ (m i : ℕ), (∀ k, k < m → (f (i + k)).within (i + k) = true) →
    wellOrdered i ((List.range' i m).map f) = true
  | 0, _, _ => rfl
  | m + 1, i, h => by
    simp only [List.range'_succ, List.map_cons, wellOrdered, Bool.and_eq_true]
    exact ⟨by simpa using h 0 (by omega), wellOrdered_map f m (i + 1) fun k hk => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h (k + 1) (by omega)⟩

theorem Aff.within_mono (a : Aff) {m m' : ℕ} (h : a.within m = true) (hm : m ≤ m') : a.within m' = true := by
  induction a with
  | loc i => simp only [Aff.within, decide_eq_true_eq] at h ⊢; omega
  | xor l r ihl ihr => simp only [Aff.within, Bool.and_eq_true] at h ⊢; exact ⟨ihl h.1, ihr h.2⟩
  | _ => rfl

theorem rowAff_within (n : ℕ) (steps : List Csa) : ∀ k r p, (rowAff n steps k r p).within (stepBase n k) = true
  | 0, r, p => by
    simp only [rowAff]
    split
    · rename_i h
      simp only [Aff.within, stepBase, cellsEnd]
      have : r * n + p < nRows * n := by nlinarith [h.1, h.2]
      exact decide_eq_true (by omega)
    · rfl
  | k + 1, r, p => by
    simp only [rowAff]
    have hb : stepBase n k + 5 * n = stepBase n (k + 1) := by unfold stepBase; ring
    split
    · split
      · simp only [Aff.within]; exact decide_eq_true (by omega)
      · rfl
    · split
      · split
        · rename_i h; simp only [Aff.within]; exact decide_eq_true (by omega)
        · split
          · rename_i h; simp only [Aff.within]; exact decide_eq_true (by omega)
          · rfl
      · exact Aff.within_mono _ (rowAff_within n steps k r p) (by unfold stepBase; nlinarith)


theorem cellAff_within (n r p i : ℕ) (hi : 0 < i) : (cellAff n r p).within i = true := by
  unfold cellAff
  split_ifs <;> simp [Aff.within, aIn, bIn, hi]

theorem cinAff_within (cm rb p : ℕ) : (cinAff cm rb p).within (rb + 5 * p) = true := by
  unfold cinAff
  split
  · simp only [Aff.within]; exact decide_eq_true (by omega)
  · rfl

theorem stepGate_within (s : Csa) (X Y Z : Aff) (w p j m : ℕ) (hX : X.within m = true) (hY : Y.within m = true)
    (hZ : Z.within m = true) (hm : m ≤ w) :
    (stepGate s X Y Z w p j).within (w + j) = true := by
  have hX' := fun k => Aff.within_mono X hX (show m ≤ w + k by omega)
  have hX0 : X.within w = true := Aff.within_mono X hX hm
  have hY' := fun k => Aff.within_mono Y hY (show m ≤ w + k by omega)
  have hY0 : Y.within w = true := Aff.within_mono Y hY hm
  have hZ' := fun k => Aff.within_mono Z hZ (show m ≤ w + k by omega)
  have hZ0 : Z.within w = true := Aff.within_mono Z hZ hm
  match j with
  | 0 => simp only [stepGate, Gate.within]; split <;> simp_all [Aff.within]
  | 1 => simp only [stepGate, Gate.within]; split <;> simp_all [Aff.within]
  | 2 => simp only [stepGate]; split <;> simp_all [Gate.within, Aff.within]
  | 3 => simp only [stepGate, Gate.within]; split_ifs <;> simp_all [Aff.within]
  | j + 4 => simp only [stepGate, Gate.within]; split_ifs <;> simp_all [Aff.within]

theorem rippleGate_within (cm : ℕ) (X Y C : Aff) (w p j m : ℕ) (hX : X.within m = true) (hY : Y.within m = true)
    (hC : C.within w = true) (hm : m ≤ w) :
    (rippleGate cm X Y C w p j).within (w + j) = true := by
  have hX' := fun k => Aff.within_mono X hX (show m ≤ w + k by omega)
  have hX0 : X.within w = true := Aff.within_mono X hX hm
  have hY' := fun k => Aff.within_mono Y hY (show m ≤ w + k by omega)
  have hY0 : Y.within w = true := Aff.within_mono Y hY hm
  have hC' := fun k => Aff.within_mono C hC (show w ≤ w + k by omega)
  match j with
  | 0 => simp only [rippleGate, Gate.within]; split <;> simp_all [Aff.within]
  | 1 => simp only [rippleGate, Gate.within]; split <;> simp_all [Aff.within]
  | 2 => simp only [rippleGate]; split <;> simp_all [Gate.within, Aff.within]
  | 3 => simp only [rippleGate, Gate.within]; split_ifs <;> simp_all [Aff.within]
  | j + 4 => simp only [rippleGate, Gate.within]; split_ifs <;> simp_all [Aff.within]


theorem gateAt_within (L : Layout) (hn : 0 < L.n) (i : ℕ) (hi : i < L.total) : (L.gateAt i).within i = true := by
  by_cases h0 : i = 0
  · subst h0; simp [Layout.gateAt, Gate.within, Aff.within, aIn, bIn]
  by_cases hc : i < cellsEnd L.n
  · simp only [Layout.gateAt, if_neg h0, if_pos hc, Gate.within]
    exact cellAff_within _ _ _ _ (by omega)
  by_cases hs : i < stepBase L.n L.steps.length
  · have h5 : 0 < 5 * L.n := by omega
    obtain ⟨k, q, hq, hik⟩ : ∃ k q, q < 5 * L.n ∧ i - cellsEnd L.n = 5 * L.n * k + q :=
      ⟨_, _, Nat.mod_lt _ h5, (Nat.div_add_mod (i - cellsEnd L.n) (5 * L.n)).symm⟩
    have hk : k < L.steps.length := by
      by_contra hk
      have : 5 * L.n * L.steps.length ≤ 5 * L.n * k := Nat.mul_le_mul_left _ (by omega)
      unfold stepBase at hs
      omega
    have hi' : i = stepBase L.n k + 5 * (q / 5) + q % 5 := by
      have := Nat.div_add_mod q 5
      unfold stepBase; omega
    have hp : q / 5 < L.n := by omega
    have hj : q % 5 < 5 := Nat.mod_lt _ (by omega)
    rw [hi', gateAt_step L hn k (q / 5) (q % 5) hk hp hj]
    exact stepGate_within _ _ _ _ _ _ _ _ (rowAff_within _ _ _ _ _) (rowAff_within _ _ _ _ _)
      (rowAff_within _ _ _ _ _) (by omega)
  · have hi' : i = rippleBase L.n L.steps.length + 5 * ((i - rippleBase L.n L.steps.length) / 5) +
        (i - rippleBase L.n L.steps.length) % 5 := by
      have := Nat.div_add_mod (i - rippleBase L.n L.steps.length) 5
      unfold rippleBase; omega
    rw [hi', gateAt_ripple L _ _ (Nat.mod_lt _ (by omega))]
    exact rippleGate_within _ _ _ _ _ _ _ _ (rowAff_within _ _ _ _ _) (rowAff_within _ _ _ _ _)
      (cinAff_within _ _ _) (by unfold rippleBase; omega)

theorem layout_wellOrdered (L : Layout) (hn : 0 < L.n) : wellOrdered 0 L.gates = true := by
  unfold Layout.gates
  rw [List.range_eq_range']
  exact wellOrdered_map L.gateAt L.total 0 fun k hk => by simpa using gateAt_within L hn k hk

end LeanVMCircuits.Multiply
