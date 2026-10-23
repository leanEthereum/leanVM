/-
  LeanVM.Protocol.EndToEnd.Front.WalkFaithfulWords

  The forward walk's word gadgets simulate the circuit builder's: run side by side, the walk
  writes at each gate's position the values of the gate's two forms against the column weights,
  and returns the values of the builder's output word.
-/

module

public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.ToArkLib.Flock.Words

/-!
# The walk's word gadgets against the builder's

The verifier's forward walk (`Verifier.addW`, `Verifier.add3W`, transcribed from
`blake2s_row_values` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`python-verifier/verifier.py:1179-1288`) carries, for every bit of a word, one field element:
the value of the bit's linear form against the column weights `cw`. The builder
(`ProductCircuit.addW`, `ProductCircuit.add3W`) carries the forms themselves and records each
gate `(a, b)` at the next free position.

* `formVal cw L`: the value of the form `L`, `Σ_{j ∈ L} cw[j]`. It is additive over XOR in
  characteristic two (`formVal_xor`), so the walk's XORs and rotations are the builder's.
* `writeRows cw s new`: the row vectors `s` with every recorded gate `(k, (a, b))` of `new` written
  as `(formVal a, formVal b)` at `k`.
* `Sim cw n k mb mw R`: run from position `n`, the builder `mb` records exactly `k` gates at
  `n, …, n + k - 1`, the walk `mw` writes exactly those gates' rows, and the results are related by
  `R`. It composes through `bind` (`sim_bind`).
* `sim_addW`, `sim_add3W`: the ripple adder (31 rows) and the fused three-operand adder (61 rows)
  of the walk simulate the builder's, the output word's values being the value word of the
  builder's output.

Nothing here transcribes a source: it relates two transcriptions.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.ProductCircuit

@[expose] public section

namespace WalkSim

variable {m : ℕ}

/-! ## Values of forms -/

/-- The value of a form against the column weights: the sum of the weights at its positions. -/
def formVal (cw : Array E) (L : Form m) : E :=
  ∑ j : Pos m, if L.getLsbD j then weightAt cw j else 0

theorem formVal_xor (cw : Array E) (L M : Form m) :
    formVal cw (L ^^^ M) = formVal cw L + formVal cw M := by
  unfold formVal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [BitVec.getLsbD_xor]
  cases L.getLsbD j <;> cases M.getLsbD j <;> simp [CharTwo.add_self_eq_zero]

theorem formVal_zero (cw : Array E) : formVal cw (0 : Form m) = 0 := by
  simp [formVal]

theorem formVal_var (cw : Array E) (k : Pos m) : formVal cw (Form.var k) = weightAt cw k := by
  unfold formVal
  rw [Finset.sum_eq_single k]
  · simp [getLsbD_var]
  · intro j _ hj
    rw [getLsbD_var, decide_eq_false (fun h ↦ hj (Fin.ext h).symm)]
    rfl
  · simp

/-- The value word of a word of forms. -/
def wordVal (cw : Array E) (x : Word m) : Array E := Array.ofFn fun i : Fin 32 ↦ formVal cw x[i]

theorem size_wordVal (cw : Array E) (x : Word m) : (wordVal cw x).size = 32 := by
  simp [wordVal]

theorem getD_wordVal (cw : Array E) (x : Word m) {i : ℕ} (hi : i < 32) :
    (wordVal cw x).getD i 0 = formVal cw x[i] := by
  simp [wordVal, Array.getD_eq_getD_getElem?, hi]

/-- The walk's XOR of value words is the value word of the XOR. -/
theorem xorW_wordVal (cw : Array E) (x y : Word m) :
    Verifier.xorW (wordVal cw x) (wordVal cw y) = wordVal cw (ProductCircuit.xorW x y) := by
  apply Array.ext
  · simp [Verifier.xorW, wordVal]
  · intro i h1 h2
    simp only [Verifier.xorW, Array.size_zipWith, size_wordVal] at h1
    simp only [Verifier.xorW, Array.getElem_zipWith, wordVal, Array.getElem_ofFn,
      ProductCircuit.xorW, Fin.getElem_fin, Vector.getElem_ofFn, formVal_xor]

/-- The walk's rotation of a value word is the value word of the rotation. -/
theorem rotateRightW_wordVal (cw : Array E) (x : Word m) (n : ℕ) :
    rotateRightW (wordVal cw x) n = wordVal cw (rotrW x n) := by
  apply Array.ext
  · simp [rotateRightW, wordVal]
  · intro i h1 h2
    simp only [rotateRightW, Array.size_ofFn] at h1
    simp only [rotateRightW, wordVal, Array.getElem_ofFn, rotrW, Fin.getElem_fin,
      Vector.getElem_ofFn]
    exact getD_wordVal cw x (Nat.mod_lt _ (by decide))

/-- The walk's input word is the value word of the builder's, in range. -/
theorem slotsW_wordVal (cw : Array E) {b : ℕ} (hb : b + 32 ≤ 2 ^ m) :
    slotsW cw b = wordVal cw (inW (m := m) b) := by
  apply Array.ext
  · simp [slotsW, wordVal]
  · intro i h1 h2
    simp only [slotsW, Array.size_ofFn] at h1
    simp only [slotsW, wordVal, Array.getElem_ofFn, inW, Fin.getElem_fin, Vector.getElem_ofFn,
      formVal_var]
    rw [pos_val (by omega)]

/-- The walk's literal is the value word of the builder's, through the constant position. -/
theorem literalW_wordVal (cw : Array E) {cpos : Pos m} (hc : (cpos : ℕ) = blake2sConstantColumn)
    (c : UInt32) : literalW cw c.toNat = wordVal cw (litW cpos c) := by
  apply Array.ext
  · simp [literalW, wordVal]
  · intro i h1 h2
    simp only [literalW, wordVal, Array.getElem_ofFn, litW, Fin.getElem_fin, Vector.getElem_ofFn]
    split_ifs
    · rw [formVal_var, hc]
    · rw [formVal_zero]

/-! ## Writing rows -/

/-- Write the row of one gate: the values of its two forms at its position. -/
def writeRow (cw : Array E) (s : Array E × Array E) (g : Pos m × Gate m) : Array E × Array E :=
  (s.1.set! g.1 (formVal cw g.2.a), s.2.set! g.1 (formVal cw g.2.b))

/-- Write the rows of a list of gates, in order. -/
def writeRows (cw : Array E) (s : Array E × Array E) (l : List (Pos m × Gate m)) :
    Array E × Array E :=
  l.foldl (writeRow cw) s

theorem writeRows_nil (cw : Array E) (s : Array E × Array E) :
    writeRows cw s ([] : List (Pos m × Gate m)) = s := rfl

theorem writeRows_cons (cw : Array E) (s : Array E × Array E) (g : Pos m × Gate m)
    (l : List (Pos m × Gate m)) : writeRows cw s (g :: l) = writeRows cw (writeRow cw s g) l := rfl

theorem writeRows_append (cw : Array E) (s : Array E × Array E) (l l' : List (Pos m × Gate m)) :
    writeRows cw s (l ++ l') = writeRows cw (writeRows cw s l) l' := by
  simp [writeRows]

/-! ## The simulation -/

/-- Run from position `n` (with room for `k` gates), the builder `mb` records exactly `k` gates at
`n, …, n + k - 1`, the walk `mw` writes exactly those gates' rows into any row vectors, and the
results are related by `R`. -/
def Sim {α β : Type} (cw : Array E) (n k : ℕ) (mb : Builder m α) (mw : RowM β)
    (R : α → β → Prop) : Prop :=
  n + k ≤ 2 ^ m → ∀ σ : BuildState m, σ.next = n → ∀ s : Array E × Array E,
    ∃ new : List (Pos m × Gate m),
      (mb.run σ).2 = { next := n + k, gates := σ.gates ++ new.toArray } ∧
      new.map (fun g ↦ (g.1 : ℕ)) = List.range' n k ∧
      (mw.run s).2 = writeRows cw s new ∧ R (mb.run σ).1 (mw.run s).1

theorem run_bind_builder {α β : Type} (mb : Builder m α) (f : α → Builder m β)
    (σ : BuildState m) : (mb >>= f).run σ = (f (mb.run σ).1).run (mb.run σ).2 := rfl

theorem run_bind_rowM {α β : Type} (mw : RowM α) (g : α → RowM β) (s : Array E × Array E) :
    (mw >>= g).run s = (g (mw.run s).1).run (mw.run s).2 := rfl

theorem sim_bind {α β γ δ : Type} {cw : Array E} {n k₁ k₂ : ℕ} {mb : Builder m α}
    {f : α → Builder m γ} {mw : RowM β} {g : β → RowM δ} {R : α → β → Prop}
    {Q : γ → δ → Prop} (h1 : Sim cw n k₁ mb mw R)
    (h2 : ∀ a b, R a b → Sim cw (n + k₁) k₂ (f a) (g b) Q) :
    Sim cw n (k₁ + k₂) (mb >>= f) (mw >>= g) Q := by
  intro hle σ hσ s
  obtain ⟨new1, hb1, hp1, hw1, hr1⟩ := h1 (by omega) σ hσ s
  obtain ⟨new2, hb2, hp2, hw2, hr2⟩ :=
    h2 _ _ hr1 (by omega) (mb.run σ).2 (by rw [hb1]) (mw.run s).2
  refine ⟨new1 ++ new2, ?_, ?_, ?_, ?_⟩
  · rw [run_bind_builder, hb2, hb1]
    simp [Nat.add_assoc]
  · rw [List.map_append, hp1, hp2, ← List.range'_append, Nat.one_mul]
  · rw [run_bind_rowM, hw2, hw1, writeRows_append]
  · exact hr2

theorem sim_pure {α β : Type} {cw : Array E} {n : ℕ} {a : α} {b : β} {R : α → β → Prop}
    (h : R a b) : Sim (m := m) cw n 0 (pure a) (pure b) R := by
  intro _ σ hσ s
  refine ⟨[], ?_, rfl, rfl, h⟩
  show σ = _
  cases σ
  simp_all

theorem sim_cast {α β : Type} {cw : Array E} {n k k' : ℕ} {mb : Builder m α} {mw : RowM β}
    {R : α → β → Prop} (h : Sim cw n k mb mw R) (hk : k = k') : Sim cw n k' mb mw R :=
  hk ▸ h

theorem sim_mono {α β : Type} {cw : Array E} {n k : ℕ} {mb : Builder m α} {mw : RowM β}
    {R R' : α → β → Prop} (h : Sim cw n k mb mw R) (hR : ∀ a b, R a b → R' a b) :
    Sim cw n k mb mw R' := by
  intro hle σ hσ s
  obtain ⟨new, h1, h2, h3, h4⟩ := h hle σ hσ s
  exact ⟨new, h1, h2, h3, hR _ _ h4⟩

/-! ## Loops -/

theorem run_setRow (i : ℕ) (l r : E) (s : Array E × Array E) :
    (setRow i l r).run s = ((), (s.1.set! i l, s.2.set! i r)) := rfl

/-- One gate written at position `p < 2 ^ m` is one `setRow`. -/
theorem writeRow_pos (cw : Array E) (s : Array E × Array E) {p : ℕ} (hp : p < 2 ^ m)
    (a b : Form m) :
    writeRow cw s (pos p, ⟨a, b⟩) = (s.1.set! p (formVal cw a), s.2.set! p (formVal cw b)) := by
  simp [writeRow, pos_val hp]

theorem run_forIn_cons {β α : Type} (a : α) (l : List α) (b : β)
    (f : α → β → RowM (ForInStep β)) (s : Array E × Array E) :
    (forIn (a :: l) b f).run s =
      match (f a b).run s with
      | (ForInStep.done b', s') => (b', s')
      | (ForInStep.yield b', s') => (forIn l b' f).run s' := by
  rw [List.forIn_cons]
  show (match ((f a b).run s).1 with
    | ForInStep.done b => pure b
    | ForInStep.yield b => forIn l b f).run ((f a b).run s).2 = _
  rcases (f a b).run s with ⟨r, s'⟩
  cases r <;> rfl

theorem run_forIn_nil {β α : Type} (b : β) (f : α → β → RowM (ForInStep β))
    (s : Array E × Array E) : (forIn ([] : List α) b f).run s = (b, s) := rfl

/-! ## The ripple adder -/

private theorem run_addCarries_zero (x y : Word m) (c : Form m) (σ : BuildState m) :
    (addCarries x y 0 c).run σ = ([c], σ) := rfl

private theorem run_addCarries_succ (x y : Word m) (n : ℕ) (c : Form m) (σ : BuildState m) :
    (addCarries x y (n + 1) c).run σ =
      let r := (addCarries x y n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push
            (pos σ.next, ⟨x[30 - n]'(by omega) ^^^ c, y[30 - n]'(by omega) ^^^ c⟩) }
      (c :: r.1, r.2) := rfl

/-- The ripple adder's loop, from bit `31 - n`: given the walk's step (`hf`, a row
`(x_i + c, y_i + c)` at `base + i` for `i < 31`) and the walk's operand values (`hx`, `hy`), the
walk writes the builder's carry gates and outputs `x_i + y_i + c_i`. -/
theorem addW_loop (cw : Array E) (x y : Word m) (base : ℕ) (xv yv : ℕ → E)
    (hx : ∀ i (h : i < 32), xv i = formVal cw x[i]) (hy : ∀ i (h : i < 32), yv i = formVal cw y[i])
    (f : ℕ → E × Array E → RowM (ForInStep (E × Array E)))
    (hf : ∀ bit c out s, (f bit (c, out)).run s =
      if bit < 31 then
        (ForInStep.yield (c + weightAt cw (base + bit), out.push (xv bit + yv bit + c)),
          (s.1.set! (base + bit) (xv bit + c), s.2.set! (base + bit) (yv bit + c)))
      else (ForInStep.yield (c, out.push (xv bit + yv bit + c)), s))
    (hbase : base + 31 ≤ 2 ^ m) :
    ∀ n, n ≤ 31 → ∀ (c : Form m) (out : Array E) (σ : BuildState m) (s : Array E × Array E),
      σ.next = base + (31 - n) →
      ∃ new : List (Pos m × Gate m),
        ((addCarries x y n c).run σ).2 = { next := σ.next + n, gates := σ.gates ++ new.toArray } ∧
        new.map (fun g ↦ (g.1 : ℕ)) = List.range' σ.next n ∧
        ((forIn (List.range' (31 - n) (n + 1)) (formVal cw c, out) f).run s).2 =
          writeRows cw s new ∧
        ((forIn (List.range' (31 - n) (n + 1)) (formVal cw c, out) f).run s).1.2.toList =
          out.toList ++ List.ofFn fun j : Fin (n + 1) ↦
            xv (31 - n + j) + yv (31 - n + j) +
              formVal cw (((addCarries x y n c).run σ).1.getD j 0) := by
  intro n
  induction n with
  | zero =>
    intro _ c out σ s _
    refine ⟨[], ?_, rfl, ?_, ?_⟩
    · rw [run_addCarries_zero]; cases σ; simp
    · rw [show List.range' (31 - 0) (0 + 1) = [31] from rfl, run_forIn_cons, hf]
      rfl
    · rw [show List.range' (31 - 0) (0 + 1) = [31] from rfl, run_forIn_cons, hf]
      exact Array.toList_push
  | succ n ih =>
    intro hn c out σ s hσ
    have hi : 30 - n < 31 := by omega
    have hrange : List.range' (31 - (n + 1)) (n + 1 + 1) =
        (30 - n) :: List.range' (31 - n) (n + 1) := by
      rw [List.range'_succ, show 31 - (n + 1) = 30 - n by omega,
        show 30 - n + 1 = 31 - n by omega]
    have hpos : σ.next < 2 ^ m := by omega
    obtain ⟨new, h1, h2, h3, h4⟩ := ih (by omega) (c ^^^ Form.var (pos σ.next))
      (out.push (xv (30 - n) + yv (30 - n) + formVal cw c))
      { next := σ.next + 1,
        gates := σ.gates.push
          (pos σ.next, ⟨x[30 - n]'(by omega) ^^^ c, y[30 - n]'(by omega) ^^^ c⟩) }
      (s.1.set! (base + (30 - n)) (xv (30 - n) + formVal cw c),
        s.2.set! (base + (30 - n)) (yv (30 - n) + formVal cw c)) (by dsimp only; omega)
    have hc' : formVal cw (c ^^^ Form.var (pos σ.next)) =
        formVal cw c + weightAt cw (base + (30 - n)) := by
      rw [formVal_xor, formVal_var, pos_val hpos, hσ]
      congr 2
      omega
    refine ⟨(pos σ.next, ⟨x[30 - n]'(by omega) ^^^ c, y[30 - n]'(by omega) ^^^ c⟩) :: new,
      ?_, ?_, ?_, ?_⟩
    · rw [run_addCarries_succ]
      dsimp only
      rw [h1]
      simp [Nat.add_assoc, Nat.add_comm 1 n]
    · rw [List.map_cons, h2, pos_val hpos, List.range'_succ]
    · rw [hrange, run_forIn_cons, hf]
      simp only [hi, ↓reduceIte]
      rw [← hc', h3, writeRows_cons, writeRow_pos cw s hpos, formVal_xor, formVal_xor,
        ← hx _ (by omega), ← hy _ (by omega), hσ, show base + (31 - (n + 1)) = base + (30 - n) by
          omega]
    · rw [hrange, run_forIn_cons, hf]
      simp only [hi, ↓reduceIte]
      rw [← hc', h4, run_addCarries_succ]
      have e1 : 31 - (n + 1) + 0 = 30 - n := by omega
      have e2 : 31 - (n + 1) + (0 + 1) = 31 - n + 0 := by omega
      have e3 : ∀ i : ℕ, 31 - (n + 1) + (i + 1 + 1) = 31 - n + (i + 1) := fun i ↦ by omega
      simp only [Array.toList_push, List.append_assoc, List.ofFn_succ, Fin.val_zero,
        Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ, e1, e2, e3, List.singleton_append]

private theorem run_addW (x y : Word m) (σ : BuildState m) :
    (ProductCircuit.addW x y).run σ =
      (sumW x y ((addCarries x y 31 0).run σ).1, ((addCarries x y 31 0).run σ).2) := by
  rw [ProductCircuit.addW, StateT.run_map]
  rfl

/-- The ripple adder against a walk loop with the walk's step. -/
theorem sim_addW_of (cw : Array E) (x y : Word m) (n : ℕ)
    {f : ℕ → E × Array E → RowM (ForInStep (E × Array E))}
    (hf : ∀ bit c out s, (f bit (c, out)).run s =
      if bit < 31 then
        (ForInStep.yield (c + weightAt cw (n + bit),
            out.push ((wordVal cw x).getD bit 0 + (wordVal cw y).getD bit 0 + c)),
          (s.1.set! (n + bit) ((wordVal cw x).getD bit 0 + c),
            s.2.set! (n + bit) ((wordVal cw y).getD bit 0 + c)))
      else
        (ForInStep.yield (c, out.push ((wordVal cw x).getD bit 0 + (wordVal cw y).getD bit 0 + c)),
          s)) :
    Sim cw n 31 (ProductCircuit.addW x y)
      (forIn (List.range 32) ((0 : E), (#[] : Array E)) f >>= fun r ↦ pure r.2)
      (fun o oa ↦ oa = wordVal cw o) := by
  intro hle σ hσ s
  have hloop := addW_loop cw x y n (fun i ↦ (wordVal cw x).getD i 0)
    (fun i ↦ (wordVal cw y).getD i 0) (fun i h ↦ getD_wordVal cw x h)
    (fun i h ↦ getD_wordVal cw y h) f hf hle 31 le_rfl 0 #[] σ s (by omega)
  rw [formVal_zero, show List.range' (31 - 31) (31 + 1) = List.range 32 from
    (List.range_eq_range' ..).symm] at hloop
  obtain ⟨new, h1, h2, h3, h4⟩ := hloop
  refine ⟨new, ?_, ?_, h3, ?_⟩
  · rw [run_addW]; dsimp only; rw [h1, hσ]
  · rw [h2, hσ]
  · rw [run_addW]
    apply Array.toList_inj.mp
    refine h4.trans ?_
    simp only [List.nil_append]
    conv_rhs => rw [wordVal, Array.toList_ofFn]
    refine congrArg List.ofFn (funext fun j ↦ ?_)
    rw [getD_wordVal cw x (by omega), getD_wordVal cw y (by omega), sumW, Fin.getElem_fin,
      Vector.getElem_ofFn, formVal_xor, formVal_xor]
    simp

/-- **The ripple adder**: the walk's `add(x, y, base)` writes the builder's 31 carry gates at
`base, …, base + 30` and returns the value word of the builder's sum. -/
theorem sim_addW (cw : Array E) (x y : Word m) (n : ℕ) :
    Sim cw n 31 (ProductCircuit.addW x y) (Verifier.addW cw (wordVal cw x) (wordVal cw y) n)
      (fun o oa ↦ oa = wordVal cw o) := by
  refine sim_addW_of cw x y n ?_
  intro bit c out s
  split_ifs <;> rfl

/-! ## The fused three-operand adder -/

private theorem run_majorities_zero (x y z : Word m) (σ : BuildState m) :
    (majorities x y z 0).run σ = ([], σ) := rfl

private theorem run_majorities_succ (x y z : Word m) (n : ℕ) (σ : BuildState m) :
    (majorities x y z (n + 1)).run σ =
      let r := (majorities x y z n).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next,
            ⟨x[30 - n]'(by omega) ^^^ z[30 - n]'(by omega),
              y[30 - n]'(by omega) ^^^ z[30 - n]'(by omega)⟩) }
      ((Form.var (pos σ.next) ^^^ z[30 - n]'(by omega)) :: r.1, r.2) := rfl

/-- The majority loop, from bit `31 - n`: the walk writes the builder's majority gates
`(x_i + z_i, y_i + z_i)` and collects the values of the majorities `g_i + z_i`. -/
theorem majorities_loop (cw : Array E) (x y z : Word m) (base : ℕ) (xv yv zv : ℕ → E)
    (hx : ∀ i (h : i < 32), xv i = formVal cw x[i]) (hy : ∀ i (h : i < 32), yv i = formVal cw y[i])
    (hz : ∀ i (h : i < 32), zv i = formVal cw z[i])
    (f : ℕ → Array E → RowM (ForInStep (Array E)))
    (hf : ∀ bit maj s, (f bit maj).run s =
      (ForInStep.yield (maj.push (weightAt cw (base + bit) + zv bit)),
        (s.1.set! (base + bit) (xv bit + zv bit), s.2.set! (base + bit) (yv bit + zv bit))))
    (hbase : base + 31 ≤ 2 ^ m) :
    ∀ n, n ≤ 31 → ∀ (maj : Array E) (σ : BuildState m) (s : Array E × Array E),
      σ.next = base + (31 - n) →
      ∃ new : List (Pos m × Gate m),
        ((majorities x y z n).run σ).2 = { next := σ.next + n, gates := σ.gates ++ new.toArray } ∧
        new.map (fun g ↦ (g.1 : ℕ)) = List.range' σ.next n ∧
        ((forIn (List.range' (31 - n) n) maj f).run s).2 = writeRows cw s new ∧
        ((forIn (List.range' (31 - n) n) maj f).run s).1.toList =
          maj.toList ++ ((majorities x y z n).run σ).1.map (formVal cw) := by
  intro n
  induction n with
  | zero =>
    intro _ maj σ s _
    refine ⟨[], ?_, rfl, rfl, ?_⟩
    · rw [run_majorities_zero]; cases σ; simp
    · simp [run_majorities_zero]
      rfl
  | succ n ih =>
    intro hn maj σ s hσ
    have hrange : List.range' (31 - (n + 1)) (n + 1) = (30 - n) :: List.range' (31 - n) n := by
      rw [List.range'_succ, show 31 - (n + 1) = 30 - n by omega,
        show 30 - n + 1 = 31 - n by omega]
    have hpos : σ.next < 2 ^ m := by omega
    have hi : 30 - n < 32 := by omega
    obtain ⟨new, h1, h2, h3, h4⟩ := ih (by omega)
      (maj.push (weightAt cw (base + (30 - n)) + zv (30 - n)))
      { next := σ.next + 1,
        gates := σ.gates.push (pos σ.next,
          ⟨x[30 - n]'hi ^^^ z[30 - n]'hi, y[30 - n]'hi ^^^ z[30 - n]'hi⟩) }
      (s.1.set! (base + (30 - n)) (xv (30 - n) + zv (30 - n)),
        s.2.set! (base + (30 - n)) (yv (30 - n) + zv (30 - n))) (by dsimp only; omega)
    have hb : σ.next = base + (30 - n) := by omega
    refine ⟨(pos σ.next, ⟨x[30 - n]'hi ^^^ z[30 - n]'hi, y[30 - n]'hi ^^^ z[30 - n]'hi⟩) :: new,
      ?_, ?_, ?_, ?_⟩
    · rw [run_majorities_succ]
      dsimp only
      rw [h1]
      simp [Nat.add_assoc, Nat.add_comm 1 n]
    · rw [List.map_cons, h2, pos_val hpos, List.range'_succ]
    · rw [hrange, run_forIn_cons, hf]
      rw [h3, writeRows_cons, writeRow_pos cw s hpos, formVal_xor, formVal_xor,
        ← hx _ hi, ← hy _ hi, ← hz _ hi, hb]
    · rw [hrange, run_forIn_cons, hf]
      rw [h4, run_majorities_succ]
      have hpos' : base + (30 - n) < 2 ^ m := by omega
      simp only [Array.toList_push, List.append_assoc, List.map_cons, List.singleton_append,
        formVal_xor, formVal_var, hb, pos_val hpos', ← hz _ hi]

private theorem run_rippleCarries_zero (p q : Word m) (c : Form m) (σ : BuildState m) :
    (rippleCarries p q 0 c).run σ = ([c], σ) := rfl

private theorem run_rippleCarries_gate (p q : Word m) (n : ℕ) (c : Form m) (σ : BuildState m)
    (h : 1 ≤ 30 - n) :
    (rippleCarries p q (n + 1) c).run σ =
      let r := (rippleCarries p q n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push
            (pos σ.next, ⟨p[30 - n]'(by omega) ^^^ c, q[30 - n]'(by omega) ^^^ c⟩) }
      (c :: r.1, r.2) := by
  simp only [rippleCarries, h, ↓reduceIte]
  rfl

/-- The ripple loop of `add3W`, from bit `31 - n ≥ 1`: the walk writes the builder's ripple gates
`(p_i + c, q_i + c)` at `rb + i - 1` and outputs `p_i + c_i + q_i`. -/
theorem ripple_loop (cw : Array E) (p q : Word m) (rb : ℕ) (pv qv : ℕ → E)
    (hp : ∀ i (h : i < 32), pv i = formVal cw p[i]) (hq : ∀ i (h : i < 32), qv i = formVal cw q[i])
    (f : ℕ → E × Array E → RowM (ForInStep (E × Array E)))
    (hf : ∀ bit c out s, (f bit (c, out)).run s =
      if 1 ≤ bit ∧ bit ≤ 30 then
        (ForInStep.yield (c + weightAt cw (rb + bit - 1), out.push (pv bit + c + qv bit)),
          (s.1.set! (rb + bit - 1) (pv bit + c), s.2.set! (rb + bit - 1) (qv bit + c)))
      else (ForInStep.yield (c, out.push (pv bit + c + qv bit)), s))
    (hrb : rb + 30 ≤ 2 ^ m) :
    ∀ n, n ≤ 30 → ∀ (c : Form m) (out : Array E) (σ : BuildState m) (s : Array E × Array E),
      σ.next = rb + (30 - n) →
      ∃ new : List (Pos m × Gate m),
        ((rippleCarries p q n c).run σ).2 =
          { next := σ.next + n, gates := σ.gates ++ new.toArray } ∧
        new.map (fun g ↦ (g.1 : ℕ)) = List.range' σ.next n ∧
        ((forIn (List.range' (31 - n) (n + 1)) (formVal cw c, out) f).run s).2 =
          writeRows cw s new ∧
        ((forIn (List.range' (31 - n) (n + 1)) (formVal cw c, out) f).run s).1.2.toList =
          out.toList ++ List.ofFn fun j : Fin (n + 1) ↦
            pv (31 - n + j) + formVal cw (((rippleCarries p q n c).run σ).1.getD j 0) +
              qv (31 - n + j) := by
  intro n
  induction n with
  | zero =>
    intro _ c out σ s _
    refine ⟨[], ?_, rfl, ?_, ?_⟩
    · rw [run_rippleCarries_zero]; cases σ; simp
    · rw [show List.range' (31 - 0) (0 + 1) = [31] from rfl, run_forIn_cons, hf]
      rfl
    · rw [show List.range' (31 - 0) (0 + 1) = [31] from rfl, run_forIn_cons, hf]
      exact Array.toList_push
  | succ n ih =>
    intro hn c out σ s hσ
    have hi : 1 ≤ 30 - n ∧ 30 - n ≤ 30 := by omega
    have hrange : List.range' (31 - (n + 1)) (n + 1 + 1) =
        (30 - n) :: List.range' (31 - n) (n + 1) := by
      rw [List.range'_succ, show 31 - (n + 1) = 30 - n by omega,
        show 30 - n + 1 = 31 - n by omega]
    have hpos : σ.next < 2 ^ m := by omega
    have hb : σ.next = rb + (30 - n) - 1 := by omega
    obtain ⟨new, h1, h2, h3, h4⟩ := ih (by omega) (c ^^^ Form.var (pos σ.next))
      (out.push (pv (30 - n) + formVal cw c + qv (30 - n)))
      { next := σ.next + 1,
        gates := σ.gates.push
          (pos σ.next, ⟨p[30 - n]'(by omega) ^^^ c, q[30 - n]'(by omega) ^^^ c⟩) }
      (s.1.set! (rb + (30 - n) - 1) (pv (30 - n) + formVal cw c),
        s.2.set! (rb + (30 - n) - 1) (qv (30 - n) + formVal cw c)) (by dsimp only; omega)
    have hc' : formVal cw (c ^^^ Form.var (pos σ.next)) =
        formVal cw c + weightAt cw (rb + (30 - n) - 1) := by
      rw [formVal_xor, formVal_var, pos_val hpos, hb]
    refine ⟨(pos σ.next, ⟨p[30 - n]'(by omega) ^^^ c, q[30 - n]'(by omega) ^^^ c⟩) :: new,
      ?_, ?_, ?_, ?_⟩
    · rw [run_rippleCarries_gate _ _ _ _ _ hi.1]
      dsimp only
      rw [h1]
      simp [Nat.add_assoc, Nat.add_comm 1 n]
    · rw [List.map_cons, h2, pos_val hpos, List.range'_succ]
    · rw [hrange, run_forIn_cons, hf]
      simp only [hi, and_self, ↓reduceIte]
      rw [← hc', h3, writeRows_cons, writeRow_pos cw s hpos, formVal_xor, formVal_xor,
        ← hp _ (by omega), ← hq _ (by omega), hb]
    · rw [hrange, run_forIn_cons, hf]
      simp only [hi, and_self, ↓reduceIte]
      rw [← hc', h4, run_rippleCarries_gate _ _ _ _ _ hi.1]
      have e1 : 31 - (n + 1) + 0 = 30 - n := by omega
      have e2 : 31 - (n + 1) + (0 + 1) = 31 - n + 0 := by omega
      have e3 : ∀ i : ℕ, 31 - (n + 1) + (i + 1 + 1) = 31 - n + (i + 1) := fun i ↦ by omega
      simp only [Array.toList_push, List.append_assoc, List.ofFn_succ, Fin.val_zero,
        Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ, e1, e2, e3, List.singleton_append]

private theorem run_rippleCarries_skip (p q : Word m) (n : ℕ) (c : Form m) (σ : BuildState m)
    (h : ¬ 1 ≤ 30 - n) :
    (rippleCarries p q (n + 1) c).run σ =
      let r := (rippleCarries p q n c).run σ
      (c :: r.1, r.2) := by
  simp only [rippleCarries, h, ↓reduceIte]
  rfl

private theorem run_add3W (x y z : Word m) (σ : BuildState m) :
    (ProductCircuit.add3W x y z).run σ =
      let r1 := (majorities x y z 31).run σ
      let r2 := (rippleCarries (xor3W x y z) (shiftW r1.1) 31 0).run r1.2
      (sumW (xor3W x y z) (shiftW r1.1) r2.1, r2.2) := by
  rw [ProductCircuit.add3W, StateT.run_bind]
  simp only [StateT.run_map]
  rfl

theorem getD_map_formVal (cw : Array E) (l : List (Form m)) (i : ℕ) :
    (l.map (formVal cw)).getD i 0 = formVal cw (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, formVal_zero]

theorem array_getD_eq_toList_getD (a : Array E) (k : ℕ) : a.getD k 0 = a.toList.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- The fused three-operand adder against walk loops with the walk's steps. -/
theorem sim_add3W_of (cw : Array E) (x y z : Word m) (n : ℕ)
    {f₁ : ℕ → Array E → RowM (ForInStep (Array E))}
    {f₂ : Array E → ℕ → E × Array E → RowM (ForInStep (E × Array E))}
    (hf₁ : ∀ bit maj s, (f₁ bit maj).run s =
      (ForInStep.yield (maj.push (weightAt cw (n + bit) + (wordVal cw z).getD bit 0)),
        (s.1.set! (n + bit) ((wordVal cw x).getD bit 0 + (wordVal cw z).getD bit 0),
          s.2.set! (n + bit) ((wordVal cw y).getD bit 0 + (wordVal cw z).getD bit 0))))
    (hf₂ : ∀ maj bit c out s, (f₂ maj bit (c, out)).run s =
      let pv := (wordVal cw x).getD bit 0 + (wordVal cw y).getD bit 0 + (wordVal cw z).getD bit 0
      let qv := if bit = 0 then 0 else maj.getD (bit - 1) 0
      if 1 ≤ bit ∧ bit ≤ 30 then
        (ForInStep.yield (c + weightAt cw (n + 31 + bit - 1), out.push (pv + c + qv)),
          (s.1.set! (n + 31 + bit - 1) (pv + c), s.2.set! (n + 31 + bit - 1) (qv + c)))
      else (ForInStep.yield (c, out.push (pv + c + qv)), s)) :
    Sim cw n 61 (ProductCircuit.add3W x y z)
      (forIn (List.range 31) (#[] : Array E) f₁ >>= fun maj ↦
        forIn (List.range 32) ((0 : E), (#[] : Array E)) (f₂ maj) >>= fun r ↦ pure r.2)
      (fun o oa ↦ oa = wordVal cw o) := by
  intro hle σ hσ s
  -- the majorities
  have hmaj := majorities_loop cw x y z n (fun i ↦ (wordVal cw x).getD i 0)
    (fun i ↦ (wordVal cw y).getD i 0) (fun i ↦ (wordVal cw z).getD i 0)
    (fun i h ↦ getD_wordVal cw x h) (fun i h ↦ getD_wordVal cw y h)
    (fun i h ↦ getD_wordVal cw z h) f₁ hf₁ (by omega) 31 le_rfl #[] σ s (by omega)
  rw [show List.range' (31 - 31) 31 = List.range 31 from (List.range_eq_range' ..).symm] at hmaj
  obtain ⟨new1, h1, h2, h3, h4⟩ := hmaj
  set r1 := (majorities x y z 31).run σ with hr1
  set maj := ((forIn (List.range 31) (#[] : Array E) f₁).run s).1 with hmaj
  set s1 := ((forIn (List.range 31) (#[] : Array E) f₁).run s).2 with hs1
  -- the ripple, from bit 1
  have hq : ∀ i (h : i < 32), (if i = 0 then 0 else maj.getD (i - 1) 0) =
      formVal cw (shiftW r1.1)[i] := by
    intro i h
    rw [shiftW, Vector.getElem_ofFn]
    split_ifs
    · rw [formVal_zero]
    · rw [array_getD_eq_toList_getD, h4, List.nil_append, getD_map_formVal]
  have hp : ∀ i (h : i < 32), (wordVal cw x).getD i 0 + (wordVal cw y).getD i 0 +
      (wordVal cw z).getD i 0 = formVal cw (xor3W x y z)[i] := by
    intro i h
    rw [xor3W, Vector.getElem_ofFn, formVal_xor, formVal_xor, getD_wordVal cw x h,
      getD_wordVal cw y h, getD_wordVal cw z h]
    rfl
  have hrip := ripple_loop cw (xor3W x y z) (shiftW r1.1) (n + 31) _ _ hp hq (f₂ maj)
    (fun bit c out s ↦ hf₂ maj bit c out s) (by omega) 30 le_rfl 0
    (#[].push ((wordVal cw x).getD 0 0 + (wordVal cw y).getD 0 0 + (wordVal cw z).getD 0 0 +
      0 + 0)) r1.2 s1 (by rw [h1]; dsimp only; omega)
  obtain ⟨new2, h1', h2', h3', h4'⟩ := hrip
  have hloop : (forIn (List.range 32) ((0 : E), (#[] : Array E)) (f₂ maj)).run s1 =
      (forIn (List.range' (31 - 30) (30 + 1))
        (formVal cw (0 : Form m), #[].push ((wordVal cw x).getD 0 0 + (wordVal cw y).getD 0 0 +
          (wordVal cw z).getD 0 0 + 0 + 0)) (f₂ maj)).run s1 := by
    rw [show List.range 32 = 0 :: List.range' (31 - 30) (30 + 1) from rfl, run_forIn_cons, hf₂,
      formVal_zero]
    rfl
  refine ⟨new1 ++ new2, ?_, ?_, ?_, ?_⟩
  · rw [run_add3W]
    dsimp only
    rw [run_rippleCarries_skip _ _ 30 _ _ (by decide)]
    dsimp only
    rw [h1', h1]
    simp [hσ, Nat.add_assoc]
  · rw [List.map_append, h2, h2', h1, hσ]
    exact List.range'_append (s := n) (m := 31) (n := 30) (step := 1)
  · rw [run_bind_rowM, run_bind_rowM, writeRows_append, ← h3, ← h3']
    exact congrArg Prod.snd hloop
  · rw [run_add3W]
    dsimp only
    rw [run_rippleCarries_skip _ _ 30 _ _ (by decide)]
    dsimp only
    rw [run_bind_rowM, run_bind_rowM]
    show (((forIn (List.range 32) ((0 : E), (#[] : Array E)) (f₂ maj)).run s1).1.2) = _
    rw [hloop]
    apply Array.toList_inj.mp
    refine h4'.trans ?_
    conv_rhs => rw [wordVal, Array.toList_ofFn]
    rw [List.ofFn_succ (n := 31)]
    simp only [Array.toList_push, List.nil_append, List.singleton_append,
      sumW, Fin.getElem_fin, Vector.getElem_ofFn, formVal_xor, Fin.val_zero, Fin.val_succ,
      List.getD_cons_zero, List.getD_cons_succ, formVal_zero, ← hp _ (by omega : 0 < 32)]
    refine congrArg₂ List.cons ?_ ?_
    · rw [← hq 0 (by omega)]; simp
    · refine congrArg List.ofFn (funext fun j ↦ ?_)
      have e : 31 - 30 + (j : ℕ) = (j : ℕ) + 1 := by omega
      simp only [e]
      rw [hp _ (by omega), hq _ (by omega), add_right_comm]

/-- **The fused three-operand adder**: the walk's `add3(x, y, z, base)` writes the builder's 31
majority gates at `base, …, base + 30` and its 30 ripple gates at `base + 31, …, base + 60`, and
returns the value word of the builder's sum. -/
theorem sim_add3W (cw : Array E) (x y z : Word m) (n : ℕ) :
    Sim cw n 61 (ProductCircuit.add3W x y z)
      (Verifier.add3W cw (wordVal cw x) (wordVal cw y) (wordVal cw z) n)
      (fun o oa ↦ oa = wordVal cw o) := by
  refine sim_add3W_of cw x y z n (fun bit maj s ↦ rfl) ?_
  intro maj bit c out s
  dsimp only
  split_ifs <;> rfl

end WalkSim

end
end LeanVM.Protocol.EndToEnd.Front
