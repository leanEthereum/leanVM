module

public import NativeVm.Code.Phase7.RingWabove

/-!
# `weightRing`'s third part: the sum over the coefficients

`kBody` takes coefficient `k` (at the coefficients' address, word `0`, index `rsi = 2k`): its
product with `eqEval` of the squared point (the buffer's elements from word `8`) and the opening
point's first `m` coordinates (`eqLoop`), added to the sum (words `4`, `5`), then the point squared
in place (`sqLoop`). `KInv` is the loop's invariant after `k` coefficients: the sum and the point
are `ringWeight`'s fold (`rwStep`) over the first `k`.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64 wp_load wp_store wp_storei)

variable {s : QState} {F : QState → Prop}

/-- One coefficient of `ringWeight`. -/
def kBody : Stmt := blk [
  I (.load .r13 (at_ .rbp (wdisp 0))),
  I (.load .r9 { base := .r13, idx := some (.rsi, .W64), disp := wdisp 0 }),
  I (.load .r10 { base := .r13, idx := some (.rsi, .W64), disp := wdisp 1 }),
  I (.lea .r13 (at_ .rbp (wdisp 8))), I (.load .r14 (at_ .rbp (wdisp 2))),
  I (.load .r15 (at_ .rbp (wdisp 3))),
  eqLoop,
  I (.load .rdx (at_ .rbp (wdisp 4))), I (.xor .r9 .rdx), I (.load .rdx (at_ .rbp (wdisp 5))),
  I (.xor .r10 .rdx),
  I (.store (at_ .rbp (wdisp 4)) .r9), I (.store (at_ .rbp (wdisp 5)) .r10),
  I (.lea .r13 (at_ .rbp (wdisp 8))), I (.load .r15 (at_ .rbp (wdisp 3))),
  sqLoop,
  I (.addi .rsi 2), I (.load .rax (at_ .rbp (wdisp 1)))]

/-- `ringWeight`'s fold after `k` coefficients. -/
def rwAt (R C rP : List E) (k : Nat) : E × List E := (C.take k).foldl (rwStep rP) (0, R)

theorem rwAt_succ (R C rP : List E) {k : Nat} (hk : k < C.length) :
    rwAt R C rP (k + 1) = rwStep rP (rwAt R C rP k) (C.getD k 0) := by
  rw [rwAt, take_succ_getD C hk, List.foldl_append]
  rfl

theorem rwAt_length (R C rP : List E) (k : Nat) : (rwAt R C rP k).2.length = R.length :=
  rwStep_foldl_length rP _ _

/-- The loop's invariant after `k` coefficients. -/
structure KInv (s0 t : QState) (b cp xp : UInt64) (R C X : List E) (vc m k : Nat) (e : E) :
    Prop where
  k_le : k ≤ C.length
  rbp : t.reg .rbp = b
  rsi : t.reg .rsi = (2 * k).toUInt64
  rax : t.reg .rax = (2 * C.length).toUInt64
  words : ∀ j < 4, t.mem (ew b j) = some ((setupWords cp xp C.length m).getD j 0)
  tot : EW t.mem b 2 (rwAt R C (X.take vc) k).1
  above : EW t.mem b 3 e
  rs : EArr t.mem (ew b 8) ((rwAt R C (X.take vc) k).2.take m)
  frame : ∀ a, (∀ j < bufWords, a ≠ ew b j) → t.mem a = s0.mem a
  dom : ∀ j < bufWords, (t.mem (ew b j)).isSome

/-- The point's squares against the opening point, cut to the common length. -/
theorem eqEval_cut (V X : List E) {vc m : Nat} (hm : m = min (min V.length vc) X.length) :
    eqEval V (X.take vc) = eqEval (V.take m) (X.take m) := by
  rw [eqEval_take_min V (X.take vc) (k := m) (by
    rw [List.length_take]; omega), List.take_take, Nat.min_eq_left (by omega)]

theorem setupWords_get (cp xp : UInt64) (n m : Nat) :
    (setupWords cp xp n m).getD 0 0 = cp ∧ (setupWords cp xp n m).getD 1 0 = (2 * n).toUInt64 ∧
      (setupWords cp xp n m).getD 2 0 = xp ∧ (setupWords cp xp n m).getD 3 0 = m.toUInt64 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem mem_two_stores (t : QState) (b v w : UInt64) {j : Nat} (hj : j < 2 ^ 61) (h4 : j ≠ 4)
    (h5 : j ≠ 5) : ((t.setMem (ew b 4) v).setMem (ew b 5) w).mem (ew b j) = t.mem (ew b j) := by
  rw [setMem_ew _ _ _ _ _ (by omega) hj, setMem_ew _ _ _ _ _ (by omega) hj]
  simp [h4, h5]

/-- The body's tail: the point squared in place, the next index. -/
def kTail : List Stmt := [
  I (.lea .r13 (at_ .rbp (wdisp 8))), I (.load .r15 (at_ .rbp (wdisp 3))),
  sqLoop,
  I (.addi .rsi 2), I (.load .rax (at_ .rbp (wdisp 1)))]

theorem kTail_spec {s0 u : QState} {b cp xp : UInt64} {R C X V : List E} {vc m k : Nat} {e : E}
    (hk : k < C.length) (hm36 : m ≤ 36) (hVm : m ≤ V.length)
    (hbp : u.reg .rbp = b) (hsi : u.reg .rsi = (2 * k).toUInt64)
    (hw : ∀ j < 4, u.mem (ew b j) = some ((setupWords cp xp C.length m).getD j 0))
    (htot : EW u.mem b 2 (rwAt R C (X.take vc) (k + 1)).1) (habove : EW u.mem b 3 e)
    (hrs : EArr u.mem (ew b 8) (V.take m))
    (hV : (rwAt R C (X.take vc) (k + 1)).2 = V.map fun v ↦ v * v)
    (hframe : ∀ a, (∀ j < bufWords, a ≠ ew b j) → u.mem a = s0.mem a)
    (hdom : ∀ j < bufWords, (u.mem (ew b j)).isSome) :
    WP (blk kTail) u (fun t' ↦ KInv s0 t' b cp xp R C X vc m (k + 1) e) F := by
  obtain ⟨g0, g1, g2, g3⟩ := setupWords_get cp xp C.length m
  have hl : (V.take m).length = m := by rw [List.length_take]; omega
  unfold kTail
  fstep
  rw [at_wdisp, hbp]
  refine wp_load (eval_w (by rsimp; exact hbp) 3) (by rsimp; rw [hw 3 (by decide), g3]) ?_
  refine WP.then (WP.withDom (WP.withWrites (sqLoop_spec (V := V.take m) (p := ew b 8) (by rsimp)
    (by rsimp; exact hrs) (by rsimp; rw [hl]) (by omega)))) fun t1 ⟨⟨⟨h1, f1⟩, r1⟩, d1⟩ ↦ ?_
  have off : ∀ j < 8, ∀ i < 2 * (V.take m).length, ew b j ≠ ew (ew b 8) i := fun j hj i hi ↦ by
    rw [ew8]; exact ew_ne _ (by omega) (by rw [hl] at hi; omega) (by omega)
  have keep : ∀ j < 8, t1.mem (ew b j) = u.mem (ew b j) := fun j hj ↦ by
    rw [f1 _ (off j hj)]; rfl
  have t1bp : t1.reg .rbp = b := by rw [r1 .rbp (by decide)]; rsimp; exact hbp
  have t1si : t1.reg .rsi = (2 * k).toUInt64 := by rw [r1 .rsi (by decide)]; rsimp; exact hsi
  fstep
  refine wp_load (eval_w (by rsimp; exact t1bp) 1) (by rsimp; rw [keep 1 (by decide),
    hw 1 (by decide), g1]) ?_
  fdone
  have hrs' : (rwAt R C (X.take vc) (k + 1)).2.take m = (V.take m).map fun v ↦ v * v := by
    rw [hV, List.map_take]
  refine ⟨by omega, by rsimp; exact t1bp, ?_, by rsimp, fun j hj ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rsimp
    rw [t1si, show (2 * (k + 1)).toUInt64 = (2 * k).toUInt64 + 2 by
      simp [Nat.toUInt64_eq, UInt64.ofNat_add, Nat.mul_add]]
  · rsimp; rw [keep j (by omega)]; exact hw j hj
  · exact EW_congr (by rsimp; rw [keep (2 * 2) (by decide)])
      (by rsimp; rw [keep (2 * 2 + 1) (by decide)]) htot
  · exact EW_congr (by rsimp; rw [keep (2 * 3) (by decide)])
      (by rsimp; rw [keep (2 * 3 + 1) (by decide)]) habove
  · rw [hrs']; exact h1
  · intro a ha
    rsimp
    rw [f1 a fun i hi ↦ by
      rw [ew8]; exact ha _ (by rw [hl] at hi; unfold bufWords; omega)]
    exact hframe a ha
  · intro j hj
    rsimp
    rw [d1]
    rsimp
    exact hdom j hj


/-- **One coefficient.** -/
theorem kBody_spec {s0 t : QState} {b cp xp : UInt64} {R C X : List E} {vc m k : Nat} {e : E}
    (hI : KInv s0 t b cp xp R C X vc m k e) (hk : k < C.length)
    (hm : m = min (min R.length vc) X.length) (hRl : R.length ≤ 36)
    (hC : EArr s0.mem cp C) (hX : EArr s0.mem xp X)
    (hsC : ∀ j < bufWords, ∀ i < 2 * C.length, ew b j ≠ ew cp i)
    (hsX : ∀ j < bufWords, ∀ i < 2 * X.length, ew b j ≠ ew xp i) :
    WP kBody t (fun t' ↦ KInv s0 t' b cp xp R C X vc m (k + 1) e) F := by
  obtain ⟨g0, g1, g2, g3⟩ := setupWords_get cp xp C.length m
  have w0 : t.mem (ew b 0) = some cp := by rw [hI.words 0 (by decide), g0]
  have w1 : t.mem (ew b 1) = some (2 * C.length).toUInt64 := by rw [hI.words 1 (by decide), g1]
  have w2 : t.mem (ew b 2) = some xp := by rw [hI.words 2 (by decide), g2]
  have w3 : t.mem (ew b 3) = some m.toUInt64 := by rw [hI.words 3 (by decide), g3]
  set V := (rwAt R C (X.take vc) k).2 with hV
  have hVl : V.length = R.length := rwAt_length R C _ k
  have hVm : (V.take m).length = m := by rw [List.length_take]; omega
  have hXm : (X.take m).length = m := by rw [List.length_take]; omega
  have hCt : EArr t.mem cp C := EArr_apart hI.frame hsC hC
  have hXt : EArr t.mem xp X := EArr_apart hI.frame hsX hX
  obtain ⟨c0, c1⟩ := (EArr_iff_EW.mp hCt) k hk
  unfold kBody
  refine wp_load (eval_w hI.rbp 0) w0 ?_
  refine wp_load (eval_idx (i := 2 * k) (by rsimp) (by rsimp; exact hI.rsi)) c0 ?_
  refine wp_load (eval_idx (i := 2 * k) (by rsimp) (by rsimp; exact hI.rsi)) c1 ?_
  fstep
  rw [at_wdisp]
  rsimp
  rw [hI.rbp]
  refine wp_load (eval_w (by rsimp; exact hI.rbp) 2) (by rsimp; exact w2) ?_
  refine wp_load (eval_w (by rsimp; exact hI.rbp) 3) (by rsimp; exact w3) ?_
  refine WP.then (eqLoop_spec (xs := V.take m) (ys := X.take m) (p := ew b 8) (q := xp)
    (by rsimp) (by rsimp) (by rsimp; exact hI.rs) (by rsimp; exact Ring.EArr.take hXt m)
    (by rw [hVm, hXm]) (by rsimp; rw [hVm]) (by omega)) fun t5 ⟨e5, _, _, m5, f5⟩ ↦ ?_
  rsimp at e5 m5
  have r5bp : t5.reg .rbp = b := by rw [f5 .rbp (by simp)]; rsimp; exact hI.rbp
  have r5si : t5.reg .rsi = (2 * k).toUInt64 := by rw [f5 .rsi (by simp)]; rsimp; exact hI.rsi
  obtain ⟨o0, o1⟩ := hI.tot
  refine wp_load (eval_w r5bp 4) (by rw [m5]; exact o0) ?_
  fstep
  refine wp_load (eval_w (by rsimp; exact r5bp) 5) (by rsimp; rw [m5]; exact o1) ?_
  fstep
  refine wp_store (eval_w (by rsimp; exact r5bp) 4) (by rsimp; rw [m5]; exact hI.dom 4 (by decide)) ?_
  refine wp_store (eval_w (by rsimp; exact r5bp) 5)
    (isSome_setMem (by rsimp; rw [m5]; exact hI.dom 5 (by decide)) _ _) ?_
  rsimp
  have hv : eOf (t5.reg .r9 ^^^ ((rwAt R C (X.take vc) k).1.limb 0).lane)
      (t5.reg .r10 ^^^ ((rwAt R C (X.take vc) k).1.limb 1).lane) =
      (rwAt R C (X.take vc) (k + 1)).1 := by
    rw [eOf_add, e5, eOf_lanes, eOf_lanes, rwAt_succ R C _ hk]
    simp only [rwStep]
    rw [eqEval_cut V X (vc := vc) (m := m) (by rw [hVl]; exact hm)]
    ring
  obtain ⟨v0, v1⟩ := eOf_eq_iff.mp hv
  have hm36 : m ≤ 36 := by omega
  refine kTail_spec (V := V) hk hm36 (by omega) (by rsimp; exact r5bp) (by rsimp; exact r5si)
    (fun j hj ↦ ?_) ?_ ?_ ?_ ?_ (fun a ha ↦ ?_) (fun j hj ↦ ?_)
  · rw [mem_two_stores _ _ _ _ (by omega) (by omega) (by omega)]
    rsimp
    rw [m5]
    exact hI.words j hj
  · constructor
    · simp (disch := omega) only [setMem_ew, Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte]
      rw [v0]
    · simp (disch := omega) only [setMem_ew, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte]
      rw [v1]
  · refine EW_congr ?_ ?_ hI.above
    · rw [mem_two_stores _ _ _ _ (by omega) (by omega) (by omega)]; rsimp; rw [m5]
    · rw [mem_two_stores _ _ _ _ (by omega) (by omega) (by omega)]; rsimp; rw [m5]
  · refine EArr_congr (fun j hj ↦ ?_) hI.rs
    rw [hVm] at hj
    rw [ew8, mem_two_stores _ _ _ _ (by omega) (by omega) (by omega)]
    rsimp
    rw [m5]
  · rw [rwAt_succ R C _ hk]
    rfl
  · simp only [QState.setMem_mem, ha 4 (by decide), ha 5 (by decide), ↓reduceIte,
      QState.setReg_mem, m5]
    exact hI.frame a ha
  · refine isSome_setMem (isSome_setMem ?_ _ _) _ _
    rsimp
    rw [m5]
    exact hI.dom j hj

end NativeVm.Code.Ring
