module

public import NativeVm.Code.Phase7.RingLoops

/-!
# Loops that write lists of `E`

* `sqLoop`: each of the `r15` elements at `r13` squared in place;
* `copyLoop`: the `r15` elements at `r13` copied to `r8`.

Each writes only its destination's words (`∀ a, (∀ k < 2 n, a ≠ ew q k) → s'.mem a = s.mem a`).
`WP.withDom` and `WP.withWrites` add what every run keeps, the words that exist and the registers
the statement never writes.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier

variable {s : QState} {F : QState → Prop}

/-! ## What every run keeps -/

/-- A run keeps which words exist. -/
theorem WP.withDom {c : Stmt} {P : QState → Prop} (h : WP c s P F) :
    WP c s (fun s' ↦ P s' ∧ ∀ a, (s'.mem a).isSome = (s.mem a).isSome) F := by
  obtain ⟨o, hx, ho⟩ := h
  refine ⟨o, hx, ?_⟩
  cases o with
  | ok s' => exact ⟨ho, Exec.mem_isSome hx⟩
  | err s' => exact ho

/-- A run keeps the registers the statement never writes. -/
theorem WP.withWrites {c : Stmt} {P : QState → Prop} (h : WP c s P F) :
    WP c s (fun s' ↦ P s' ∧ ∀ r, c.writes r = false → s'.reg r = s.reg r) F := by
  obtain ⟨o, hx, ho⟩ := h
  refine ⟨o, hx, ?_⟩
  cases o with
  | ok s' => exact ⟨ho, fun r hr ↦ Exec.reg_frame hx hr⟩
  | err s' => exact ho

/-! ## Two stores -/

theorem setMem_mem_fun (s : QState) (a v : UInt64) :
    (s.setMem a v).mem = fun a' ↦ if a' = a then some v else s.mem a' :=
  funext fun a' ↦ QState.setMem_mem s a v a'

/-- Element `k` of a list at `q`, after element `i ≠ k` is written. -/
theorem EW_store_ne {mem : UInt64 → Option UInt64} {q : UInt64} {i k : Nat} {x : E}
    {v0 v1 : UInt64} (hi : i < 2 ^ 59) (hk : k < 2 ^ 59) (hik : k ≠ i) (h : EW mem q k x) :
    EW (fun a ↦ if a = ew q (2 * i + 1) then some v1 else if a = ew q (2 * i) then some v0
      else mem a) q k x := by
  have m0 : ew q (2 * k) ≠ ew q (2 * i) := ew_ne _ (by omega) (by omega) (by omega)
  have m1 : ew q (2 * k) ≠ ew q (2 * i + 1) := ew_ne _ (by omega) (by omega) (by omega)
  have m2 : ew q (2 * k + 1) ≠ ew q (2 * i) := ew_ne _ (by omega) (by omega) (by omega)
  have m3 : ew q (2 * k + 1) ≠ ew q (2 * i + 1) := ew_ne _ (by omega) (by omega) (by omega)
  simp only [EW, m0, m1, m2, m3, ite_false]
  exact h

/-- Element `i` of a list at `q`, written. -/
theorem EW_store_eq {mem : UInt64 → Option UInt64} {q : UInt64} {i : Nat} {x : E} {v0 v1 : UInt64}
    (hi : i < 2 ^ 59) (h0 : v0 = (x.limb 0).lane) (h1 : v1 = (x.limb 1).lane) :
    EW (fun a ↦ if a = ew q (2 * i + 1) then some v1 else
      if a = ew q (2 * i) then some v0 else mem a) q i x := by
  have n01 : ew q (2 * i) ≠ ew q (2 * i + 1) := ew_ne _ (by omega) (by omega) (by omega)
  simp only [EW, n01, ite_false, ite_true, h0, h1]
  exact ⟨trivial, trivial⟩

/-- An element of another list, apart from the words written. -/
theorem EW_store_apart {mem : UInt64 → Option UInt64} {q p : UInt64} {i k : Nat} {x : E}
    {v0 v1 : UInt64} (h0 : ∀ l < 2, ew q (2 * i + l) ≠ ew p (2 * k))
    (h1 : ∀ l < 2, ew q (2 * i + l) ≠ ew p (2 * k + 1)) (h : EW mem p k x) :
    EW (fun a ↦ if a = ew q (2 * i + 1) then some v1 else if a = ew q (2 * i) then some v0
      else mem a) p k x := by
  have m0 := Ne.symm (h0 0 (by omega))
  have m1 := Ne.symm (h0 1 (by omega))
  have m2 := Ne.symm (h1 0 (by omega))
  have m3 := Ne.symm (h1 1 (by omega))
  simp only [Nat.add_zero] at m0 m2
  simp only [EW, m0, m1, m2, m3, ite_false]
  exact h

/-- The words outside a list at `q` of `n` elements, after element `i < n` is written. -/
theorem frame_store {mem mem0 : UInt64 → Option UInt64} {q : UInt64} {i n : Nat} {v0 v1 : UInt64}
    (hi : i < n) (hF : ∀ a, (∀ k < 2 * n, a ≠ ew q k) → mem a = mem0 a) :
    ∀ a, (∀ k < 2 * n, a ≠ ew q k) →
      (if a = ew q (2 * i + 1) then some v1 else if a = ew q (2 * i) then some v0 else mem a) =
        mem0 a := by
  intro a ha
  simp only [ha (2 * i + 1) (by omega), ha (2 * i) (by omega), ite_false]
  exact hF a ha

/-! ## `sqLoop` -/

/-- Square the `r15` elements at `r13` in place. -/
def sqLoop : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .r9 (at_ .r13 0)), I (.load .r10 (at_ .r13 8)), esq,
  I (.store (at_ .r13 0) .r9), I (.store (at_ .r13 8) .r10), I (.addi .r13 16), I (.subi .r15 1)])

/-- **`sqLoop` squares a list in place.** -/
theorem sqLoop_spec {V : List E} {p : UInt64} (h13 : s.reg .r13 = p) (hV : EArr s.mem p V)
    (hn : s.reg .r15 = V.length.toUInt64) (hlen : V.length < 2 ^ 59) :
    WP sqLoop s (fun s' ↦ EArr s'.mem p (V.map fun v ↦ v * v) ∧
      (∀ a, (∀ k < 2 * V.length, a ≠ ew p k) → s'.mem a = s.mem a)) F := by
  set n := V.length with hn_def
  rw [EArr_iff_EW] at hV
  unfold sqLoop
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r13 = ew p (2 * i) ∧ t.reg .r15 = (n - i).toUInt64 ∧
      (∀ k < i, EW t.mem p k (V.getD k 0 * V.getD k 0)) ∧
      (∀ k, i ≤ k → k < n → EW t.mem p k (V.getD k 0)) ∧
      (∀ a, (∀ k < 2 * n, a ≠ ew p k) → t.mem a = s.mem a))
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, fun k hk ↦ absurd hk (Nat.not_lt_zero _),
      fun k _ hk ↦ hV k hk, fun _ _ ↦ rfl⟩
    · rw [h13, Nat.mul_zero, ew_zero]
    · rw [hn, Nat.sub_zero]
  · intro t ⟨i, hi, t13, t15, hD, hS, hF⟩ hc
    have hin : i < n := cnt_lt (t15 ▸ cond_test_true hc)
    obtain ⟨a0, a1⟩ := hS i le_rfl hin
    refine WP.load_at (by rw [t13, int64Zero_toUInt64, ew_zero']; exact a0) ?_
    refine WP.load_at (by rsimp; rw [t13, ew_one]; exact a1) ?_
    refine WP.then (esq_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1 e2
    have k : ∀ r ∉ sqRegs, t₁.reg r = t.reg r := fun r hr ↦ by
      rw [e3 r hr]
      simp only [sqRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.2.2.2.2.1, hr.2.2.2.2.2]
    have w0 : t₁.reg .r13 + 0 = ew p (2 * i) := by
      rw [k .r13 (by decide), t13, ew_zero']
    have w1 : t₁.reg .r13 + 8 = ew p (2 * i + 1) := by
      rw [k .r13 (by decide), t13, ew_one]
    refine WP.store_at (by rw [int64Zero_toUInt64, w0, e2]; simp [a0]) ?_
    refine WP.store_at (by
      rsimp; rw [w1]; exact isSome_setMem (by rw [e2]; simp [a1]) _ _) ?_
    fstep; fstep; fdone
    rw [w0, w1]
    simp only [setMem_mem_fun, e2]
    have hv : eOf (t₁.reg .r9) (t₁.reg .r10) = V.getD i 0 * V.getD i 0 := by
      rw [e1, eOf_lanes, sq]
    obtain ⟨v0, v1⟩ := eOf_eq_iff.mp hv
    refine ⟨⟨i + 1, hin, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [k .r13 (by decide), t13, ew_step]
    · rw [k .r15 (by decide), t15, cnt_succ hin]
    · intro q hq
      rcases Nat.lt_or_ge q i with hqi | hqi
      · exact EW_store_ne (i := i) (by omega) (by omega) (by omega) (hD q hqi)
      · obtain rfl : q = i := by omega
        exact EW_store_eq (by omega) v0 v1
    · intro q hq hqn
      exact EW_store_ne (i := i) (by omega) (by omega) (by omega) (hS q (by omega) hqn)
    · exact frame_store hin hF
    · rw [k .r15 (by decide), t15, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, t15, hD, _, hF⟩ hc
    obtain rfl : i = n := cnt_eq (by omega) hi (t15 ▸ cond_test_false hc)
    refine ⟨?_, hF⟩
    rw [EArr_iff_EW, List.length_map]
    intro q hq
    have e : (V.map fun v ↦ v * v).getD q 0 = V.getD q 0 * V.getD q 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    rw [e]
    exact hD q hq

/-! ## `copyLoop` -/

/-- Copy the `r15` elements at `r13` to `r8`. -/
def copyLoop : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .r9 (at_ .r13 0)), I (.load .r10 (at_ .r13 8)),
  I (.store (at_ .r8 0) .r9), I (.store (at_ .r8 8) .r10),
  I (.addi .r13 16), I (.addi .r8 16), I (.subi .r15 1)])

/-- **`copyLoop` copies a list** to words apart from it. -/
theorem copyLoop_spec {xs : List E} {p q : UInt64} (h13 : s.reg .r13 = p) (h8 : s.reg .r8 = q)
    (hx : EArr s.mem p xs) (hn : s.reg .r15 = xs.length.toUInt64) (hlen : xs.length < 2 ^ 59)
    (hdom : ∀ k < 2 * xs.length, (s.mem (ew q k)).isSome)
    (hsep : ∀ k < 2 * xs.length, ∀ j < 2 * xs.length, ew q k ≠ ew p j) :
    WP copyLoop s (fun s' ↦ EArr s'.mem q xs ∧
      (∀ a, (∀ k < 2 * xs.length, a ≠ ew q k) → s'.mem a = s.mem a)) F := by
  set n := xs.length with hn_def
  rw [EArr_iff_EW] at hx
  unfold copyLoop
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r13 = ew p (2 * i) ∧ t.reg .r8 = ew q (2 * i) ∧
      t.reg .r15 = (n - i).toUInt64 ∧ (∀ k < i, EW t.mem q k (xs.getD k 0)) ∧
      (∀ k < 2 * n, (t.mem (ew q k)).isSome) ∧
      (∀ a, (∀ k < 2 * n, a ≠ ew q k) → t.mem a = s.mem a))
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, fun k hk ↦ absurd hk (Nat.not_lt_zero _), hdom,
      fun _ _ ↦ rfl⟩
    · rw [h13, Nat.mul_zero, ew_zero]
    · rw [h8, Nat.mul_zero, ew_zero]
    · rw [hn, Nat.sub_zero]
  · intro t ⟨i, hi, t13, t8, t15, hD, hW, hF⟩ hc
    have hin : i < n := cnt_lt (t15 ▸ cond_test_true hc)
    have src : ∀ j < 2 * n, t.mem (ew p j) = s.mem (ew p j) := fun j hj ↦
      hF _ fun k hk e ↦ hsep k hk j hj e.symm
    obtain ⟨a0, a1⟩ := hx i hin
    refine WP.load_at (by rw [t13, int64Zero_toUInt64, ew_zero', src _ (by omega)]; exact a0) ?_
    refine WP.load_at (by rsimp; rw [t13, ew_one, src _ (by omega)]; exact a1) ?_
    have w0 : t.reg .r8 + 0 = ew q (2 * i) := by rw [t8, ew_zero']
    have w1 : t.reg .r8 + 8 = ew q (2 * i + 1) := by rw [t8, ew_one]
    refine WP.store_at (by rsimp; rw [w0]; exact hW _ (by omega)) ?_
    refine WP.store_at (by
      rsimp; rw [w1]; exact isSome_setMem (hW _ (by omega)) _ _) ?_
    fstep; fstep; fstep; fdone
    rw [w0, w1]
    simp only [setMem_mem_fun, QState.setReg_mem]
    refine ⟨⟨i + 1, hin, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [t13, ew_step]
    · rw [t8, ew_step]
    · rw [t15, cnt_succ hin]
    · intro k hk
      rcases Nat.lt_or_ge k i with hki | hki
      · exact EW_store_ne (i := i) (by omega) (by omega) (by omega) (hD k hki)
      · obtain rfl : k = i := by omega
        exact EW_store_eq (by omega) rfl rfl
    · intro k hk
      split
      · rfl
      · split
        · rfl
        · exact hW k hk
    · exact frame_store hin hF
    · rw [t15, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, _, t15, hD, _, hF⟩ hc
    obtain rfl : i = n := cnt_eq (by omega) hi (t15 ▸ cond_test_false hc)
    exact ⟨(EArr_iff_EW).mpr hD, hF⟩

end NativeVm.Code.Ring
