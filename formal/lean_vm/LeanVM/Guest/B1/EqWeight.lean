/-
  LeanVM.Guest.B1.EqWeight

  The guest's `@inline eq_weight` as an expanded block, and its meaning: one entry of the
  equality kernel.
-/

module

public import LeanVM.Guest.B1.Log2

/-!
# `eq_weight` (TRIAGE #19)

`eq_weight(ch, count, idx, msb_span)` (G:743-760) multiplies, for `c < count`, the factor
`ch[c]` (bit set) or `1 + ch[c]` (bit clear), where the bit is bit `c` of `idx` (`msb_span = 0`)
or bit `msb_span - 1 - c`; the product starts at `1`, so the first factor is folded. Its
expansion `ewGo ch bitf c n b w` (from coordinate `c`, `n` coordinates, its first value `b`, the
running product `w`) has a shape that depends on the bits: `ewStep` per coordinate. `EwOk` is
what it asks (`holds_ewGo`), `ewOk_value` its meaning (the product of the factors over the words
read at `ch`), `ewOk_of_vals` that the honest values `ewVals` satisfy it. Over the full width,
the product is the entry of `eqKernel` (V:676) at `idx` (`eqKernel_getD`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The template -/

/-- The bit of coordinate `c`: bit `c` of `idx`, or bit `msb - 1 - c` for an MSB-first walk. -/
def ewBit (idx msb c : ℕ) : Bool := if msb = 0 then idx.testBit c else idx.testBit (msb - 1 - c)

/-- One coordinate at its first value `b`, the running product `w` (`none` before the first). -/
def ewStep (ch : V) (c : ℕ) (bit : Bool) (b : ℕ) : Option V → List Stmt × ℕ × V
  | none => if bit then ([.atom (.load (.n b) ch c)], b + 1, .n b) else
      ([.atom (.load (.n b) ch c), .atom (.const (.n (b + 1)) (word 1 0 0)),
        .atom (.add (.n (b + 2)) (.n (b + 1)) (.n b))], b + 3, .n (b + 2))
  | some w => if bit then ([.atom (.load (.n b) ch c), .atom (.mul (.n (b + 1)) w (.n b))], b + 2,
        .n (b + 1)) else
      ([.atom (.load (.n b) ch c), .atom (.const (.n (b + 1)) (word 1 0 0)),
        .atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)), .atom (.mul (.n (b + 3)) w (.n (b + 2)))],
        b + 4, .n (b + 3))

/-- Coordinates `c .. c + n - 1`: the statements, the next value, the product. -/
def ewGo (ch : V) (bitf : ℕ → Bool) : ℕ → ℕ → ℕ → Option V → List Stmt × ℕ × Option V
  | _, 0, b, w => ([], b, w)
  | c, n + 1, b, w =>
    ((ewStep ch c (bitf c) b w).1 ++
        (ewGo ch bitf (c + 1) n (ewStep ch c (bitf c) b w).2.1 (some (ewStep ch c (bitf c) b w).2.2)).1,
      (ewGo ch bitf (c + 1) n (ewStep ch c (bitf c) b w).2.1 (some (ewStep ch c (bitf c) b w).2.2)).2)

/-- `eq_weight(ch, count, idx, msb)` at its first value `b`. -/
def eqWeightT (ch : V) (count idx msb b : ℕ) : List Stmt × ℕ × Option V :=
  ewGo ch (ewBit idx msb) 0 count b none

/-! ## What it asks -/

/-- What one coordinate asks. -/
def EwStepOk (rd : Reader) (σ : Val) (ch : V) (c : ℕ) (bit : Bool) (b : ℕ) : Option V → Prop
  | none => LoadHolds rd (σ ch) c (σ (.n b)) ∧
      (bit = false → σ (.n (b + 1)) = 1 ∧ σ (.n (b + 2)) = σ (.n (b + 1)) + σ (.n b))
  | some w => LoadHolds rd (σ ch) c (σ (.n b)) ∧
      (bit = true → σ (.n (b + 1)) = σ w * σ (.n b)) ∧
      (bit = false → σ (.n (b + 1)) = 1 ∧ σ (.n (b + 2)) = σ (.n (b + 1)) + σ (.n b) ∧
        σ (.n (b + 3)) = σ w * σ (.n (b + 2)))

theorem holds_ewStep (ch : V) (c : ℕ) (bit : Bool) (b : ℕ) (w : Option V) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ewStep ch c bit b w).1 next kret ↔ EwStepOk rd σ ch c bit b w ∧ next := by
  cases w <;> cases bit <;>
    simp only [ewStep, EwStepOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one, ↓reduceIte,
      Bool.false_eq_true, Bool.true_eq_false, true_implies, false_implies, true_and, and_assoc]

/-- What the coordinates ask. -/
def EwOk (rd : Reader) (σ : Val) (ch : V) (bitf : ℕ → Bool) : ℕ → ℕ → ℕ → Option V → Prop
  | _, 0, _, _ => True
  | c, n + 1, b, w => EwStepOk rd σ ch c (bitf c) b w ∧
      EwOk rd σ ch bitf (c + 1) n (ewStep ch c (bitf c) b w).2.1 (some (ewStep ch c (bitf c) b w).2.2)

theorem holds_ewGo (ch : V) (bitf : ℕ → Bool) (next : Prop) (kret : List E → Prop) :
    ∀ n c b w, Stmt.HoldsList C rd σ (ewGo ch bitf c n b w).1 next kret ↔
      EwOk rd σ ch bitf c n b w ∧ next
  | 0, _, _, _ => by simp [ewGo, EwOk, Stmt.HoldsList]
  | n + 1, c, b, w => by
    rw [ewGo, holdsList_append, holds_ewStep, holds_ewGo ch bitf next kret n, EwOk]
    tauto

/-! ## The product -/

/-- Coordinate `c`'s factor over the word `x` read at it. -/
def ewFac (bit : Bool) (x : E) : E := if bit then x else 1 + x

/-- The value of the running product: `1` before the first factor. -/
def wvOf (σ : Val) : Option V → E
  | none => 1
  | some w => σ w

theorem ewStep_value {ch : V} {c : ℕ} {bit : Bool} {b : ℕ} {w : Option V}
    (h : EwStepOk rd σ ch c bit b w) :
    σ (ewStep ch c bit b w).2.2 = wvOf σ w * ewFac bit (σ (.n b)) := by
  cases w <;> cases bit <;> simp_all [ewStep, EwStepOk, wvOf, ewFac]

theorem ewStepOk_load {ch : V} {c : ℕ} {bit : Bool} {b : ℕ} {w : Option V}
    (h : EwStepOk rd σ ch c bit b w) : LoadHolds rd (σ ch) c (σ (.n b)) := by
  cases w <;> exact h.1

theorem ewOk_value (ch : V) (bitf : ℕ → Bool) (r : ℕ → E) :
    ∀ n c b w, (∀ k < n, LoadHolds rd (σ ch) (c + k) (r (c + k))) → EwOk rd σ ch bitf c n b w →
      wvOf σ (ewGo ch bitf c n b w).2.2 = wvOf σ w * ∏ k ∈ Finset.range n, ewFac (bitf (c + k)) (r (c + k))
  | 0, _, _, _, _, _ => by simp [ewGo]
  | n + 1, c, b, w, hl, ⟨hs, hrest⟩ => by
    have hv := ewStep_value hs
    have hr : σ (.n b) = r c := loadHolds_unique (ewStepOk_load hs) (by simpa using hl 0 (by omega))
    rw [ewGo, ewOk_value ch bitf r n (c + 1) _ _ (fun k hk => by
      rw [show c + 1 + k = c + (k + 1) by omega]; exact hl (k + 1) (by omega)) hrest, wvOf, hv, hr,
      Finset.prod_range_succ' (n := n), Nat.add_zero]
    simp only [show ∀ k, c + 1 + k = c + (k + 1) from fun k => by omega, Nat.add_zero]
    ring

/-! ## The honest values -/

/-- The number of values one coordinate makes. -/
def ewLen (bit : Bool) : Bool → ℕ
  | false => if bit then 1 else 3
  | true => if bit then 2 else 4

theorem ewStep_next (ch : V) (c : ℕ) (bit : Bool) (b : ℕ) (w : Option V) :
    (ewStep ch c bit b w).2.1 = b + ewLen bit w.isSome := by
  cases w <;> cases bit <;> rfl

/-- The honest values of one coordinate over the word `x`, the running product `w0`. -/
def ewStepVals (bit : Bool) (x : E) : Option E → ℕ → E
  | none, i => (if bit then [x] else [x, 1, 1 + x]).getD i 0
  | some w0, i => (if bit then [x, w0 * x] else [x, 1, 1 + x, w0 * (1 + x)]).getD i 0

theorem ewStep_result (ch : V) (c : ℕ) (bit : Bool) (b : ℕ) (w : Option V) :
    (ewStep ch c bit b w).2.2 = .n (b + (ewLen bit w.isSome - 1)) := by
  cases w <;> cases bit <;> rfl

theorem ewStepVals_last (bit : Bool) (x : E) (wval : Option E) :
    ewStepVals bit x wval (ewLen bit wval.isSome - 1) = wval.getD 1 * ewFac bit x := by
  cases wval <;> cases bit <;> simp [ewStepVals, ewLen, ewFac]

theorem ewLen_pos (bit s : Bool) : 0 < ewLen bit s := by cases bit <;> cases s <;> simp [ewLen]

/-- The honest value at `k` of the coordinates from `c`, their first value `b`, over the words
`r`. -/
def ewEval (r : ℕ → E) (bitf : ℕ → Bool) : ℕ → ℕ → ℕ → Option E → ℕ → E
  | _, 0, _, _, _ => 0
  | c, n + 1, b, w, k =>
    if k < b + ewLen (bitf c) w.isSome then ewStepVals (bitf c) (r c) w (k - b)
    else ewEval r bitf (c + 1) n (b + ewLen (bitf c) w.isSome)
      (some (w.getD 1 * ewFac (bitf c) (r c))) k

/-- The first value after the coordinates. -/
def ewEnd (bitf : ℕ → Bool) : ℕ → ℕ → ℕ → Bool → ℕ
  | _, 0, b, _ => b
  | c, n + 1, b, s => ewEnd bitf (c + 1) n (b + ewLen (bitf c) s) true

theorem ewGo_next (ch : V) (bitf : ℕ → Bool) :
    ∀ n c b w, (ewGo ch bitf c n b w).2.1 = ewEnd bitf c n b w.isSome
  | 0, _, _, _ => rfl
  | n + 1, c, b, w => by rw [ewGo, ewGo_next ch bitf n, ewStep_next]; rfl

theorem le_ewEnd (bitf : ℕ → Bool) : ∀ n c b s, b ≤ ewEnd bitf c n b s
  | 0, _, _, _ => le_rfl
  | n + 1, c, _, _ => le_trans (Nat.le_add_right _ _) (le_ewEnd bitf n (c + 1) _ true)

/-- **The honest values satisfy the block**: a valuation agreeing with `ewEval` on the block's
values, with the words `r` in memory at `ch`, meets every atom. -/
theorem ewOk_of_eval (ch : V) (bitf : ℕ → Bool) (r : ℕ → E) :
    ∀ n c b (w : Option V) (wval : Option E), w.isSome = wval.isSome →
      (∀ v, w = some v → σ v = wval.getD 1) →
      (∀ k < n, LoadHolds rd (σ ch) (c + k) (r (c + k))) →
      (∀ k, b ≤ k → k < ewEnd bitf c n b w.isSome → σ (.n k) = ewEval r bitf c n b wval k) →
      EwOk rd σ ch bitf c n b w
  | 0, _, _, _, _, _, _, _, _ => trivial
  | n + 1, c, b, w, wval, hs, hw, hl, hv => by
    have hend := le_ewEnd bitf n (c + 1) (b + ewLen (bitf c) w.isSome) true
    have hstep : ∀ i < ewLen (bitf c) w.isSome, σ (.n (b + i)) = ewStepVals (bitf c) (r c) wval i :=
      fun i hi => by
        rw [hv (b + i) (by omega) (by simp only [ewEnd]; omega), ewEval, ite_pos' (by rw [← hs]; omega),
          Nat.add_sub_cancel_left]
    have hl0 : LoadHolds rd (σ ch) c (r c) := by simpa using hl 0 (by omega)
    refine ⟨?_, ?_⟩
    · cases w with
      | none =>
        cases wval with
        | some _ => simp at hs
        | none =>
          have h0 := hstep 0 (by cases bitf c <;> simp [ewLen])
          simp only [Nat.add_zero, ewStepVals] at h0
          cases hb : bitf c
          · have h1 := hstep 1 (by simp [ewLen, hb])
            have h2 := hstep 2 (by simp [ewLen, hb])
            simp only [ewStepVals, hb] at h0 h1 h2
            refine ⟨by rw [h0]; exact hl0, fun _ => ⟨h1, by rw [h2, h1, h0]; rfl⟩⟩
          · simp only [hb, ↓reduceIte] at h0
            refine ⟨by rw [h0]; exact hl0, fun h => absurd h (by simp)⟩
      | some v =>
        cases wval with
        | none => simp at hs
        | some w0 =>
          have hwv : σ v = w0 := hw v rfl
          have h0 := hstep 0 (by cases bitf c <;> simp [ewLen])
          simp only [Nat.add_zero, ewStepVals] at h0
          cases hb : bitf c
          · have h1 := hstep 1 (by simp [ewLen, hb])
            have h2 := hstep 2 (by simp [ewLen, hb])
            have h3 := hstep 3 (by simp [ewLen, hb])
            simp only [ewStepVals, hb] at h0 h1 h2 h3
            refine ⟨by rw [h0]; exact hl0, fun h => absurd h (by simp), fun _ =>
              ⟨h1, by rw [h2, h1, h0]; rfl, by rw [h3, hwv, h2]; rfl⟩⟩
          · have h1 := hstep 1 (by simp [ewLen, hb])
            simp only [ewStepVals, hb] at h0 h1
            refine ⟨by rw [h0]; exact hl0, fun _ => by rw [h1, hwv, h0]; rfl,
              fun h => absurd h (by simp)⟩
    · refine ewOk_of_eval ch bitf r n (c + 1) _ _ (some (wval.getD 1 * ewFac (bitf c) (r c))) rfl
        (fun v hv' => ?_) (fun k hk => by
          rw [show c + 1 + k = c + (k + 1) by omega]; exact hl (k + 1) (by omega)) (fun k hk1 hk2 => ?_)
      · obtain rfl := Option.some.inj hv'
        have hpos := ewLen_pos (bitf c) w.isSome
        rw [ewStep_result, hstep _ (by omega), hs, ewStepVals_last]
        rfl
      · rw [hv k (by have := ewStep_next ch c (bitf c) b w; rw [this] at hk1; omega) (by
          simp only [ewEnd]; rw [ewStep_next] at hk2; exact hk2), ewEval, ite_neg' (by
          rw [ewStep_next, hs] at hk1; omega), ← hs]
        rw [ewStep_next]

theorem ewGo_isSome (ch : V) (bitf : ℕ → Bool) :
    ∀ n c b w, 0 < n → ((ewGo ch bitf c n b w).2.2).isSome = true
  | 0, _, _, _, h => absurd h (by omega)
  | 1, _, _, _, _ => rfl
  | n + 2, c, b, w, _ => by
    rw [ewGo]
    exact ewGo_isSome ch bitf (n + 1) (c + 1) _ _ (by omega)

theorem ewOk_loads (ch : V) (bitf : ℕ → Bool) :
    ∀ n c b w, EwOk rd σ ch bitf c n b w → ∀ k < n, ∃ v, LoadHolds rd (σ ch) (c + k) v
  | 0, _, _, _, _, _, hk => absurd hk (by omega)
  | n + 1, c, b, w, ⟨hs, hr⟩, k, hk => by
    cases k with
    | zero => exact ⟨_, ewStepOk_load hs⟩
    | succ k =>
      obtain ⟨v, hv⟩ := ewOk_loads ch bitf n (c + 1) _ _ hr k (by omega)
      exact ⟨v, by rwa [show c + 1 + k = c + (k + 1) by omega] at hv⟩

/-! ## The equality kernel -/

theorem eqKernel_append (rs : List E) (r : E) :
    eqKernel (rs ++ [r]) = (eqKernel rs).map (· * (1 + r)) ++ (eqKernel rs).map (· * r) := by
  simp [eqKernel, List.foldl_append]

theorem length_eqKernel (rs : List E) : (eqKernel rs).length = 2 ^ rs.length := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [eqKernel_append, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

/-- **Entry `i` of `eqKernel rs`** (V:676) is the product over the coordinates of `rs[c]` (bit `c`
of `i` set) or `1 + rs[c]`. -/
theorem eqKernel_getD (rs : List E) (i : ℕ) (hi : i < 2 ^ rs.length) :
    (eqKernel rs).getD i 0 = ∏ c ∈ Finset.range rs.length, ewFac (i.testBit c) (rs.getD c 0) := by
  induction rs using List.reverseRecOn generalizing i with
  | nil =>
    simp only [List.length_nil, pow_zero, Nat.lt_one_iff] at hi
    subst hi
    rfl
  | append_singleton rs r ih =>
    have hl := length_eqKernel rs
    simp only [List.length_append, List.length_singleton] at hi ⊢
    have hgr : ∀ c < rs.length, (rs ++ [r]).getD c 0 = rs.getD c 0 := fun c hc => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hc]
    have hgn : (rs ++ [r]).getD rs.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    rw [Finset.prod_range_succ, hgn, Finset.prod_congr rfl fun c hc => by
      rw [hgr c (Finset.mem_range.mp hc)], eqKernel_append, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i (2 ^ rs.length) with h | h
    · rw [List.getElem?_append_left (by simp [hl, h]), List.getElem?_map,
        List.getElem?_eq_getElem (by rw [hl]; exact h)]
      simp only [Option.map_some, Option.getD_some]
      have := ih i h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact h),
        Option.getD_some] at this
      rw [this, Nat.testBit_lt_two_pow h]
      simp [ewFac]
    · obtain ⟨j, rfl⟩ : ∃ j, i = 2 ^ rs.length + j := ⟨i - 2 ^ rs.length, by omega⟩
      have hj : j < 2 ^ rs.length := by rw [pow_succ] at hi; omega
      rw [List.getElem?_append_right (by simp [hl]), List.getElem?_map, List.length_map, hl,
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem (by rw [hl]; exact hj)]
      simp only [Option.map_some, Option.getD_some]
      have := ih j hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; exact hj),
        Option.getD_some] at this
      rw [this, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj]
      congr 1
      refine Finset.prod_congr rfl fun c hc => ?_
      rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hc)]

end
end LeanVM.Guest.B1
