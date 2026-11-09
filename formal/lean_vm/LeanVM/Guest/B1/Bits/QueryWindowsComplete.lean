/-
  LeanVM.Guest.B1.Bits.QueryWindowsComplete

  `decode_query_windows` is complete: on the honest run's values, every atom of its template holds.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsHonest

/-!
# `decode_query_windows`, complete (lean_ethereum.py:798-909 at 40f877dc)

**The honest valuation** is built block by block along the template `qwBody d cd`, each block
appending the words of the values it defines (`QwStab l P`: `P` holds of every valuation extending
the words `l`, so later blocks keep it): the window cells hold `g^`(the window's bits)
(`qwRunW`), a range check's helper `g^(2^w - 1 - n)` and the two words it reads below `2^7`, a
table read the pattern `n` (`WinTabs`), a split window's two runs `g^(n mod 2^a)`, `g^(n / 2^a)`,
the sums as the soundness proof computes them (`qwLoT`, `qwHiT`), each position's store
`qwPosOf d w j`, its window pointer `run·g^(j·qwN)`.

`qwAK rd Q σ ss`: every atom of the block holds, and is one of the kinds a placed proof needs
(`QwEnv.Ok`): a load through `positions` or `win_ptrs` below `192 / d`, or through `tabs·g^e`,
`e < 128`; a `frameAddr` of a run from `.n r`, `5 ≤ r < 61`, at `run·g^(r - 5)`; no `HeapBuf`.

**`qw_holds`** (generic in the shape, `QwShape`): on a reader defined below `2^7` (the range
checks), holding the window table at `tabs`, the honest windows at `run` (where it holds a word,
`FrameRun`), the positions at `positions` and the pointers `run·g^(j·qwN)` at `win_ptrs`, some
valuation takes the parameters to `[w, positions, win_ptrs, tabs]` and makes the body hold,
returning `[]` (`decode_query_windows_complete_Spec`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Stable facts -/

/-- `P` holds of every valuation extending the words `l`. -/
def QwStab (l : List E) (P : Val → Prop) : Prop := ∀ t, P (Val.ofArgs (l ++ t))

theorem QwStab.ext {l : List E} {P : Val → Prop} (h : QwStab l P) (m : List E) : QwStab (l ++ m) P :=
  fun t ↦ by rw [List.append_assoc]; exact h (m ++ t)

theorem QwStab.and {l : List E} {P R : Val → Prop} (h : QwStab l P) (h' : QwStab l R) :
    QwStab l fun σ ↦ P σ ∧ R σ := fun t ↦ ⟨h t, h' t⟩

theorem QwStab.mono {l : List E} {P R : Val → Prop} (h : QwStab l P) (hPR : ∀ σ, P σ → R σ) :
    QwStab l R := fun t ↦ hPR _ (h t)

/-- The words a block appends, at their values. -/
theorem qwOaN {l m t : List E} {k N : ℕ} (hl : l.length = k) (hm : m.length = N) {i : ℕ}
    (h1 : k ≤ i) (h2 : i < k + N) : Val.ofArgs (l ++ m ++ t) (.n i) = m.getD (i - k) 0 := by
  rw [ofArgs_n, List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    List.getElem?_append_left (by omega), hl, ← List.getD_eq_getElem?_getD]

/-- **Some words extend `l` to `k'` values, making `P` stable.** -/
def QwExt (l : List E) (k' : ℕ) (P : Val → Prop) : Prop := ∃ m, (l ++ m).length = k' ∧ QwStab (l ++ m) P

theorem QwExt.mono {l : List E} {k' : ℕ} {P R : Val → Prop} (h : QwExt l k' P) (hPR : ∀ σ, P σ → R σ) :
    QwExt l k' R :=
  let ⟨m, hm, hs⟩ := h
  ⟨m, hm, hs.mono hPR⟩

/-- **Blocks in sequence**: the next block runs on what the first appended. -/
theorem QwExt.bind {l : List E} {k1 k2 : ℕ} {P1 P2 : Val → Prop} (h1 : QwExt l k1 P1)
    (h2 : ∀ m, (l ++ m).length = k1 → QwStab (l ++ m) P1 → QwExt (l ++ m) k2 P2) :
    QwExt l k2 fun σ ↦ P1 σ ∧ P2 σ := by
  obtain ⟨m1, hl1, hs1⟩ := h1
  obtain ⟨m2, hl2, hs2⟩ := h2 m1 hl1 hs1
  refine ⟨m1 ++ m2, by rw [← List.append_assoc, hl2], fun t ↦ ⟨?_, ?_⟩⟩
  · have := hs1 (m2 ++ t)
    simp only [List.append_assoc] at this ⊢
    exact this
  · have := hs2 t
    simp only [List.append_assoc] at this ⊢
    exact this

theorem QwExt.nil {l : List E} {k : ℕ} {P : Val → Prop} (hl : l.length = k) (h : QwStab l P) :
    QwExt l k P := ⟨[], by simp [hl], by simpa using h⟩

/-! ## The atoms' kinds -/

/-- What a placed proof needs of the values. -/
structure QwEnv where
  pos : E
  ptrs : E
  tabs : E
  run : E
  np : ℕ

/-- **An atom of a kind a placed proof covers**: its loads through `positions` or `win_ptrs` below
`np`, or through `tabs·g^e`, `e < 128`; its `frameAddr`s of runs from `.n r`, `5 ≤ r < 61`, at
`run·g^(r - 5)`; no `HeapBuf`. -/
def QwEnv.Ok (Q : QwEnv) (σ : Val) : Atom → Prop
  | .load _ q off => (σ q = Q.pos ∧ off < Q.np) ∨ (σ q = Q.ptrs ∧ off < Q.np) ∨
      ∃ e < 128, σ q = Q.tabs * gen ^ e ∧ off = 0
  | .frameAddr q (r :: _) => r = .n r.idx ∧ 5 ≤ r.idx ∧ r.idx < 61 ∧ σ q = Q.run * gen ^ (r.idx - 5)
  | .frameAddr _ [] => False
  | .hint (.alloc ..) => False
  | .hint (.allocDyn ..) => False
  | _ => True

/-- Every atom of the block holds and is of a covered kind. -/
def qwAK (rd : Reader) (Q : QwEnv) (σ : Val) (ss : List Stmt) : Prop :=
  ∀ a, Stmt.atom a ∈ ss → a.Holds rd σ ∧ Q.Ok σ a

theorem qwAK_append {rd : Reader} {Q : QwEnv} {σ : Val} {xs ys : List Stmt} :
    qwAK rd Q σ (xs ++ ys) ↔ qwAK rd Q σ xs ∧ qwAK rd Q σ ys := by
  simp only [qwAK, List.mem_append]
  exact ⟨fun h ↦ ⟨fun a ha ↦ h a (Or.inl ha), fun a ha ↦ h a (Or.inr ha)⟩,
    fun h a ha ↦ ha.elim (h.1 a) (h.2 a)⟩

theorem qwAK_cons {rd : Reader} {Q : QwEnv} {σ : Val} {a : Atom} {ss : List Stmt} :
    qwAK rd Q σ (.atom a :: ss) ↔ (a.Holds rd σ ∧ Q.Ok σ a) ∧ qwAK rd Q σ ss := by
  simp only [qwAK, List.mem_cons, Stmt.atom.injEq]
  exact ⟨fun h ↦ ⟨h a (Or.inl rfl), fun b hb ↦ h b (Or.inr hb)⟩,
    fun h b hb ↦ hb.elim (fun e ↦ e ▸ h.1) (h.2 b)⟩

theorem qwAK_nil {rd : Reader} {Q : QwEnv} {σ : Val} : qwAK rd Q σ [] ↔ True := by simp [qwAK]

theorem qwAK.ah {rd : Reader} {Q : QwEnv} {σ : Val} {ss : List Stmt} (h : qwAK rd Q σ ss) :
    qwAH rd σ ss := fun a ha ↦ (h a ha).1

theorem QwExt.and_stab {l : List E} {k : ℕ} {P R : Val → Prop} (h : QwExt l k P) (h' : QwStab l R) :
    QwExt l k fun σ ↦ P σ ∧ R σ :=
  let ⟨m, hm, hs⟩ := h
  ⟨m, hm, hs.and (h'.ext m)⟩

/-! ## Squares, scaling, sums -/

theorem qwSquares_complete {rd : Reader} {Q : QwEnv} : ∀ (a : ℕ) {l : List E} {k : ℕ},
    l.length = k → ∀ {x : V} {X : E}, QwStab l (fun σ ↦ σ x = X) →
      QwExt l (k + a) fun σ ↦ qwAK rd Q σ (qwSquares x a k).1 ∧ σ (qwSquares x a k).2 = X ^ (2 ^ a)
  | 0, l, k, hl, x, X, h => QwExt.nil (by simpa using hl) (h.mono fun σ hx ↦ by
      simp only [qwSquares, qwAK_nil, true_and, pow_zero, pow_one]; exact hx)
  | a + 1, l, k, hl, x, X, h => by
    have h1 : QwExt l (k + 1) fun σ ↦ qwAK rd Q σ [.atom (.mul (.n k) x x)] ∧ σ (.n k) = X * X := by
      refine ⟨[X * X], by simp [hl], fun t ↦ ?_⟩
      have hx := h ([X * X] ++ t)
      rw [← List.append_assoc] at hx
      have e : Val.ofArgs (l ++ [X * X] ++ t) (.n k) = X * X := by
        rw [qwOaN hl (m := [X * X]) (N := 1) rfl le_rfl (by omega)]; simp
      simp only [qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, e, hx]
      simp
    have h2 := h1.bind fun m hm hs ↦
      qwSquares_complete (rd := rd) (Q := Q) a hm (x := .n k) (X := X * X) (hs.mono fun σ h ↦ h.2)
    rw [show k + (a + 1) = k + 1 + a by omega]
    refine h2.mono fun σ ⟨⟨ha, _⟩, hr, hv⟩ ↦ ?_
    simp only [qwSquares, qwAK_cons]
    refine ⟨⟨(qwAK_cons.mp ha).1, hr⟩, ?_⟩
    rw [hv, ← sq, ← pow_mul, ← pow_succ']

theorem qwScale_complete {rd : Reader} {Q : QwEnv} {l : List E} {k : ℕ} (hl : l.length = k)
    {x : V} {X : E} (c : ℕ) (h : QwStab l fun σ ↦ σ x = X) :
    QwExt l (qwScale x c k).2.1 fun σ ↦
      qwAK rd Q σ (qwScale x c k).1 ∧ σ (qwScale x c k).2.2 = X * cbWord c := by
  by_cases hc : c = 0
  · subst hc
    exact QwExt.nil (by simp [qwScale, hl]) (h.mono fun σ hx ↦ by
      simp [qwScale, qwAK_nil, hx, cbWord_zero'])
  · refine ⟨[cbWord c, X * cbWord c], by simp [qwScale, hc, hl], fun t ↦ ?_⟩
    have hx := h ([cbWord c, X * cbWord c] ++ t)
    rw [← List.append_assoc] at hx
    have hm : [cbWord c, X * cbWord c].length = 2 := rfl
    simp only [qwScale, hc, ↓reduceIte, qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true]
    simp (disch := omega) only [qwOaN hl hm, Nat.add_sub_cancel_left, Nat.sub_self,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hx]
    simp

theorem qwAcc_complete {rd : Reader} {Q : QwEnv} {l : List E} {k : ℕ} (hl : l.length = k)
    {acc : Option V} {tv : V} {A T : E} (h : QwStab l fun σ ↦ qwOpt σ acc = A ∧ σ tv = T) :
    QwExt l (qwAcc acc tv k).2.1 fun σ ↦
      qwAK rd Q σ (qwAcc acc tv k).1 ∧ qwOpt σ (qwAcc acc tv k).2.2 = A + T := by
  cases acc with
  | none =>
    exact QwExt.nil (by simp [qwAcc, hl]) (h.mono fun σ ⟨ha, ht⟩ ↦ by
      simp only [qwAcc, qwAK_nil, true_and, qwOpt] at ha ⊢
      rw [← ha, ht, zero_add])
  | some a =>
    refine ⟨[A + T], by simp [qwAcc, hl], fun t ↦ ?_⟩
    obtain ⟨ha, ht⟩ := h ([A + T] ++ t)
    rw [← List.append_assoc] at ha ht
    have e : Val.ofArgs (l ++ [A + T] ++ t) (.n k) = A + T := by
      rw [qwOaN hl (m := [A + T]) (N := 1) rfl le_rfl (by omega)]; simp
    simp only [qwOpt] at ha
    simp only [qwAcc, qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, qwOpt, e, ha, ht]
    simp

/-! ## Reads below `2^7` -/

/-- The word at `g^e`, or `0`. -/
noncomputable def qwRd (rd : Reader) (e : ℕ) : E := (rd (Parameters.addressOfIndex e)).getD 0

theorem qw_limb_gen_pow (e : ℕ) : (gen ^ e).limb 0 = Parameters.addressOfIndex e := by
  rw [gen_pow_eq_ofK, limb_ofK]; rfl

theorem qw_lh {rd : Reader} (hlow : ∀ i < 128, (rd (Parameters.addressOfIndex i)).isSome) {e : ℕ}
    (he : e < 128) : LoadHolds rd (gen ^ e) 0 (qwRd rd e) := by
  refine ⟨gen_pow_isInK e, ?_⟩
  have h0 : Parameters.addressOfIndex 0 = 1 := by simp [Parameters.addressOfIndex]
  rw [qw_limb_gen_pow, h0, mul_one, qwRd]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hlow e he)
  rw [hv]; rfl

theorem qw_gen_pow_bound {w n : ℕ} (hw : w ≤ 7) (hn : n < 2 ^ w) :
    qwBound w = gen ^ n * gen ^ (2 ^ w - 1 - n) := by
  rw [qwBound_eq hw, ← pow_add, gen_pow_eq_ofK]
  congr 2; omega

section reads

variable {rd : Reader} {Q : QwEnv} (hT : WinTabs rd Q.tabs)
  (hlow : ∀ i < 128, (rd (Parameters.addressOfIndex i)).isSome)
include hT hlow

omit hlow in
theorem qw_tabs {n : ℕ} (hn : n < 128) : LoadHolds rd (Q.tabs * gen ^ n) 0 (eOfNat n) :=
  (loadHolds_mul_gen_pow rd Q.tabs n 0 _).mpr (hT n hn)

/-! ## A window read -/

theorem qwRead_complete {l : List E} {k : ℕ} (hl : l.length = k) {c : V} {start w n : ℕ}
    (hw : w ≤ 7) (hn : n < 2 ^ w) (hpre : QwStab l fun σ ↦ σ c = gen ^ n ∧ σ (.n 3) = Q.tabs) :
    QwExt l (qwRead c start w k).2.1 fun σ ↦
      qwAK rd Q σ (qwRead c start w k).1 ∧ σ (qwRead c start w k).2.2 = eOfNat n := by
  have h2w : 2 ^ w ≤ 128 := le_trans (Nat.pow_le_pow_right (n := 2) (by decide) hw) (by decide)
  refine ⟨[qwBound w, gen ^ (2 ^ w - 1 - n), qwRd rd n, qwRd rd (2 ^ w - 1 - n), Q.tabs * gen ^ n,
    eOfNat n], by simp [qwRead, hl], fun t ↦ ?_⟩
  obtain ⟨hc, h3⟩ := hpre (_ ++ t)
  rw [← List.append_assoc] at hc h3
  have hm : List.length [qwBound w, gen ^ (2 ^ w - 1 - n), qwRd rd n, qwRd rd (2 ^ w - 1 - n),
    Q.tabs * gen ^ n, eOfNat n] = 6 := rfl
  simp only [qwRead, qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true]
  simp (disch := omega) only [qwOaN hl hm, Nat.add_sub_cancel_left, Nat.sub_self, List.getD_cons_zero,
    List.getD_cons_succ]
  rw [hc, h3]
  exact ⟨⟨trivial, trivial, ⟨qw_lh hlow (by omega), qw_gen_pow_bound hw hn, qw_lh hlow (by omega)⟩, rfl,
    qw_tabs hT (by omega), Or.inr (Or.inr ⟨n, by omega, rfl⟩)⟩, trivial⟩

/-! ## A split window -/

/-- The split's first statements: the two runs hinted, range checked. -/
def qwSplitA (start a w k : ℕ) : List Stmt :=
  [.atom (.hint (.windowsExp (.n 0) start a 1 (.stack [.n k]))),
    .atom (.hint (.windowsExp (.n 0) (start + a) (w - a) 1 (.stack [.n (k + 1)]))),
    .atom (.const (.n (k + 2)) (qwBound a)),
    .atom (.rangeCheck (.n k) (.n (k + 3)) (.n (k + 4)) (.n (k + 5)) (.n (k + 2))),
    .atom (.const (.n (k + 6)) (qwBound (w - a))),
    .atom (.rangeCheck (.n (k + 1)) (.n (k + 7)) (.n (k + 8)) (.n (k + 9)) (.n (k + 6)))]

/-- The split's last statements: the join, the two table reads. -/
def qwSplitC (c : V) (a k : ℕ) (sq : V) : List Stmt :=
  [.atom (.mul c (.n k) sq), .atom (.mul (.n (k + 10 + a)) (.n 3) (.n k)),
    .atom (.load (.n (k + 11 + a)) (.n (k + 10 + a)) 0),
    .atom (.mul (.n (k + 12 + a)) (.n 3) (.n (k + 1))),
    .atom (.load (.n (k + 13 + a)) (.n (k + 12 + a)) 0)]

omit hT hlow in
theorem qwSplit_eq (c : V) (start a w k : ℕ) : qwSplit c start a w k =
    (qwSplitA start a w k ++ (qwSquares (.n (k + 1)) a (k + 10)).1 ++
      qwSplitC c a k (qwSquares (.n (k + 1)) a (k + 10)).2, k + 14 + a, .n (k + 11 + a),
      .n (k + 13 + a)) := rfl

omit hT in
theorem qwSplitA_complete {l : List E} {k : ℕ} (hl : l.length = k) {start a w n1 n2 : ℕ}
    (ha : a ≤ 7) (hwa : w - a ≤ 7) (hn1 : n1 < 2 ^ a) (hn2 : n2 < 2 ^ (w - a)) :
    QwExt l (k + 10) fun σ ↦ qwAK rd Q σ (qwSplitA start a w k) ∧ σ (.n k) = gen ^ n1 ∧
      σ (.n (k + 1)) = gen ^ n2 := by
  have h2a : 2 ^ a ≤ 128 := le_trans (Nat.pow_le_pow_right (n := 2) (by decide) ha) (by decide)
  have h2b : 2 ^ (w - a) ≤ 128 :=
    le_trans (Nat.pow_le_pow_right (n := 2) (by decide) hwa) (by decide)
  refine ⟨[gen ^ n1, gen ^ n2, qwBound a, gen ^ (2 ^ a - 1 - n1), qwRd rd n1,
    qwRd rd (2 ^ a - 1 - n1), qwBound (w - a), gen ^ (2 ^ (w - a) - 1 - n2), qwRd rd n2,
    qwRd rd (2 ^ (w - a) - 1 - n2)], by simp [hl], fun t ↦ ?_⟩
  have hm : List.length [gen ^ n1, gen ^ n2, qwBound a, gen ^ (2 ^ a - 1 - n1), qwRd rd n1,
    qwRd rd (2 ^ a - 1 - n1), qwBound (w - a), gen ^ (2 ^ (w - a) - 1 - n2), qwRd rd n2,
    qwRd rd (2 ^ (w - a) - 1 - n2)] = 10 := rfl
  simp only [qwSplitA, qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true]
  simp (disch := omega) only [qwOaN hl hm, Nat.add_sub_cancel_left, Nat.sub_self,
    List.getD_cons_zero, List.getD_cons_succ]
  repeat' first
    | exact qw_lh hlow (by omega)
    | exact qw_gen_pow_bound (by omega) (by omega)
    | trivial
    | refine ⟨?_, ?_⟩

omit hlow in
theorem qwSplitC_complete {l : List E} {k a : ℕ} (hl : l.length = k + 10 + a) {c sq : V}
    {n1 n2 : ℕ} (hn1 : n1 < 128) (hn2 : n2 < 128)
    (hpre : QwStab l fun σ ↦ σ c = gen ^ n1 * (gen ^ n2) ^ 2 ^ a ∧ σ (.n k) = gen ^ n1 ∧
      σ (.n (k + 1)) = gen ^ n2 ∧ σ sq = (gen ^ n2) ^ 2 ^ a ∧ σ (.n 3) = Q.tabs) :
    QwExt l (k + 14 + a) fun σ ↦ qwAK rd Q σ (qwSplitC c a k sq) ∧
      σ (.n (k + 11 + a)) = eOfNat n1 ∧ σ (.n (k + 13 + a)) = eOfNat n2 := by
  refine ⟨[Q.tabs * gen ^ n1, eOfNat n1, Q.tabs * gen ^ n2, eOfNat n2], by simp [hl]; omega,
    fun t ↦ ?_⟩
  obtain ⟨hc, hk, hk1, hsq, h3⟩ := hpre ([Q.tabs * gen ^ n1, eOfNat n1, Q.tabs * gen ^ n2,
    eOfNat n2] ++ t)
  rw [← List.append_assoc] at hc hk hk1 hsq h3
  have hm : List.length [Q.tabs * gen ^ n1, eOfNat n1, Q.tabs * gen ^ n2, eOfNat n2] = 4 := rfl
  have e0 := qwOaN (t := t) hl hm (i := k + 10 + a) (by omega) (by omega)
  have e1 := qwOaN (t := t) hl hm (i := k + 11 + a) (by omega) (by omega)
  have e2 := qwOaN (t := t) hl hm (i := k + 12 + a) (by omega) (by omega)
  have e3 := qwOaN (t := t) hl hm (i := k + 13 + a) (by omega) (by omega)
  rw [show k + 10 + a - (k + 10 + a) = 0 by omega] at e0
  rw [show k + 11 + a - (k + 10 + a) = 1 by omega] at e1
  rw [show k + 12 + a - (k + 10 + a) = 2 by omega] at e2
  rw [show k + 13 + a - (k + 10 + a) = 3 by omega] at e3
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3
  simp only [qwSplitC, qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true, e0, e1, e2, e3, hc, hk,
    hk1, hsq, h3]
  repeat' first
    | exact qw_tabs hT (by omega)
    | exact Or.inr (Or.inr ⟨_, by omega, rfl⟩)
    | trivial
    | refine ⟨?_, ?_⟩

theorem qwSplit_complete {l : List E} {k : ℕ} (hl : l.length = k) {c : V} {start a w n1 n2 : ℕ}
    (ha1 : 1 ≤ a) (ha : a < w) (hw : w ≤ 7) (hn1 : n1 < 2 ^ a) (hn2 : n2 < 2 ^ (w - a))
    (hpre : QwStab l fun σ ↦ σ c = gen ^ (n1 + 2 ^ a * n2) ∧ σ (.n 3) = Q.tabs) :
    QwExt l (qwSplit c start a w k).2.1 fun σ ↦ qwAK rd Q σ (qwSplit c start a w k).1 ∧
      σ (qwSplit c start a w k).2.2.1 = eOfNat n1 ∧ σ (qwSplit c start a w k).2.2.2 = eOfNat n2 := by
  have h2a : 2 ^ a ≤ 128 :=
    le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (show a ≤ 7 by omega)) (by decide)
  have h2b : 2 ^ (w - a) ≤ 128 :=
    le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (show w - a ≤ 7 by omega)) (by decide)
  rw [qwSplit_eq]
  have h := (qwSplitA_complete (Q := Q) hlow hl (start := start) (w := w) (show a ≤ 7 by omega)
    (show w - a ≤ 7 by omega) hn1 hn2).bind fun m1 hm1 hs1 ↦
    (qwSquares_complete (rd := rd) (Q := Q) a hm1 (x := .n (k + 1)) (X := gen ^ n2)
      (hs1.mono fun σ h ↦ h.2.2)).bind fun m2 hm2 hs2 ↦
      qwSplitC_complete hT (k := k) (c := c) hm2 (show n1 < 128 by omega) (show n2 < 128 by omega)
        ((((hpre.ext m1).ext m2).and ((hs1.ext m2).and hs2)).mono fun σ ⟨⟨hc, h3⟩, ⟨_, hk, hk1⟩, _, hsq⟩ ↦
          ⟨by rw [hc, pow_add, ← pow_mul, mul_comm n2], hk, hk1, hsq, h3⟩)
  exact h.mono fun σ ⟨⟨hA, _, _⟩, ⟨hB, _⟩, hC, h1, h2⟩ ↦
    ⟨qwAK_append.mpr ⟨qwAK_append.mpr ⟨hA, hB⟩, hC⟩, h1, h2⟩

/-! ## A window -/

theorem qwWindow_complete {l : List E} {k : ℕ} (hl : l.length = k) {d cd base cut at0 i : ℕ}
    {lo hi : Option V} {n : ℕ} {LO HI : E} (hw : (qwWin d cd i).2 ≤ 7)
    (hn : n < 2 ^ (qwWin d cd i).2)
    (hpre : QwStab l fun σ ↦ σ (.n (5 + at0 + i)) = gen ^ n ∧ σ (.n 3) = Q.tabs ∧
      qwOpt σ lo = LO ∧ qwOpt σ hi = HI) :
    QwExt l (qwWindow d cd base cut at0 i k lo hi).2.1 fun σ ↦
      qwAK rd Q σ (qwWindow d cd base cut at0 i k lo hi).1 ∧
      qwOpt σ (qwWindow d cd base cut at0 i k lo hi).2.2.1 =
        LO + qwLoT (qwWin d cd i).1 (qwWin d cd i).2 cut n ∧
      qwOpt σ (qwWindow d cd base cut at0 i k lo hi).2.2.2 =
        HI + qwHiT (qwWin d cd i).1 (qwWin d cd i).2 cut n := by
  set off := (qwWin d cd i).1
  set w := (qwWin d cd i).2
  unfold qwWindow
  simp only
  by_cases h1 : off + w ≤ cut
  · rw [ite_pos' h1]
    have h := ((qwRead_complete hT hlow hl (c := .n (5 + at0 + i)) (start := base + off) hw hn
      (hpre.mono fun σ h ↦ ⟨h.1, h.2.1⟩)).bind fun m1 hm1 hs1 ↦
      (qwScale_complete (rd := rd) (Q := Q) hm1 off (hs1.mono fun σ h ↦ h.2)).bind fun m2 hm2 hs2 ↦
        qwAcc_complete (rd := rd) (Q := Q) hm2 (acc := lo)
          ((((hpre.ext m1).ext m2).and hs2).mono fun σ h ↦ ⟨h.1.2.2.1, h.2.2⟩)).and_stab hpre
    refine h.mono fun σ ⟨⟨⟨hr, _⟩, ⟨hs, _⟩, ha, hav⟩, _, _, _, hhi⟩ ↦ ⟨?_, ?_, ?_⟩
    · exact qwAK_append.mpr ⟨qwAK_append.mpr ⟨hr, hs⟩, ha⟩
    · rw [hav, qwLoT, ite_pos' h1]
    · rw [hhi, qwHiT, ite_pos' h1, add_zero]
  · rw [ite_neg' h1]
    by_cases h2 : off < cut
    · rw [ite_pos' h2]
      have hlt : n % 2 ^ (cut - off) < 2 ^ (cut - off) := Nat.mod_lt _ (by positivity)
      have hdl : n / 2 ^ (cut - off) < 2 ^ (w - (cut - off)) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        exact hn
      have h := ((qwSplit_complete hT hlow hl (c := .n (5 + at0 + i)) (start := base + off)
        (show 1 ≤ cut - off by omega) (show cut - off < w by omega) hw hlt hdl
        (hpre.mono fun σ h ↦ ⟨by rw [h.1, Nat.mod_add_div], h.2.1⟩)).bind fun m1 hm1 hs1 ↦
        (qwScale_complete (rd := rd) (Q := Q) hm1 off (hs1.mono fun σ h ↦ h.2.1)).bind
          fun m2 hm2 hs2 ↦
          (qwAcc_complete (rd := rd) (Q := Q) hm2 (acc := lo)
            ((((hpre.ext m1).ext m2).and hs2).mono fun σ h ↦ ⟨h.1.2.2.1, h.2.2⟩)).bind
            fun m3 hm3 hs3 ↦
            qwAcc_complete (rd := rd) (Q := Q) hm3 (acc := hi)
              ((((hpre.ext m1).ext m2).ext m3).and ((hs1.ext m2).ext m3) |>.mono
                fun σ h ↦ ⟨h.1.2.2.2, h.2.2.2⟩))
      refine h.mono fun σ ⟨⟨hr, _⟩, ⟨hs, _⟩, ⟨ha, hav⟩, hb, hbv⟩ ↦ ⟨?_, ?_, ?_⟩
      · exact qwAK_append.mpr ⟨qwAK_append.mpr ⟨qwAK_append.mpr ⟨hr, hs⟩, ha⟩, hb⟩
      · rw [hav, qwLoT, ite_neg' h1, ite_pos' h2]
      · rw [hbv, qwHiT, ite_neg' h1, ite_pos' h2]
    · rw [ite_neg' h2]
      have h := ((qwRead_complete hT hlow hl (c := .n (5 + at0 + i)) (start := base + off) hw hn
        (hpre.mono fun σ h ↦ ⟨h.1, h.2.1⟩)).bind fun m1 hm1 hs1 ↦
        (qwScale_complete (rd := rd) (Q := Q) hm1 (off - cut) (hs1.mono fun σ h ↦ h.2)).bind
          fun m2 hm2 hs2 ↦
          qwAcc_complete (rd := rd) (Q := Q) hm2 (acc := hi)
            ((((hpre.ext m1).ext m2).and hs2).mono fun σ h ↦ ⟨h.1.2.2.2, h.2.2⟩)).and_stab hpre
      refine h.mono fun σ ⟨⟨⟨hr, _⟩, ⟨hs, _⟩, ha, hav⟩, _, _, hlo, _⟩ ↦ ⟨?_, ?_, ?_⟩
      · exact qwAK_append.mpr ⟨qwAK_append.mpr ⟨hr, hs⟩, ha⟩
      · rw [hlo, qwLoT, ite_neg' h1, ite_neg' h2, add_zero]
      · rw [hav, qwHiT, ite_neg' h1, ite_neg' h2]

/-! ## A position's windows -/

theorem qwWindows_complete {d cd base cut at0 : ℕ} {ns : ℕ → ℕ} : ∀ (i m : ℕ) {l : List E} {k : ℕ},
    l.length = k → ∀ {lo hi : Option V} {LO HI : E},
    (∀ t < m, (qwWin d cd (i + t)).2 ≤ 7 ∧ ns (i + t) < 2 ^ (qwWin d cd (i + t)).2) →
    QwStab l (fun σ ↦ (∀ t < m, σ (.n (5 + at0 + (i + t))) = gen ^ ns (i + t)) ∧ σ (.n 3) = Q.tabs ∧
      qwOpt σ lo = LO ∧ qwOpt σ hi = HI) →
    QwExt l (qwWindows d cd base cut at0 i m k lo hi).2.1 fun σ ↦
      qwAK rd Q σ (qwWindows d cd base cut at0 i m k lo hi).1 ∧
      qwOpt σ (qwWindows d cd base cut at0 i m k lo hi).2.2.1 = LO +
        ∑ t ∈ Finset.range m, qwLoT (qwWin d cd (i + t)).1 (qwWin d cd (i + t)).2 cut (ns (i + t)) ∧
      qwOpt σ (qwWindows d cd base cut at0 i m k lo hi).2.2.2 = HI +
        ∑ t ∈ Finset.range m, qwHiT (qwWin d cd (i + t)).1 (qwWin d cd (i + t)).2 cut (ns (i + t))
  | _, 0, l, k, hl, lo, hi, LO, HI, _, h => QwExt.nil (by simp [qwWindows, hl]) (h.mono fun σ h ↦ by
      simp [qwWindows, qwAK_nil, h.2.2.1, h.2.2.2])
  | i, m + 1, l, k, hl, lo, hi, LO, HI, hb, h => by
    simp only [qwWindows]
    have hb0 := hb 0 (by omega)
    simp only [Nat.add_zero] at hb0
    have h1 := qwWindow_complete hT hlow hl (base := base) (cut := cut) (at0 := at0) (lo := lo)
      (hi := hi) hb0.1 hb0.2 (h.mono fun σ h' ↦ ⟨by simpa using h'.1 0 (by omega), h'.2.1, h'.2.2.1,
        h'.2.2.2⟩)
    have e : ∀ t, i + 1 + t = i + (t + 1) := fun t ↦ by omega
    have h2 := h1.bind fun m1 hm1 hs1 ↦
      qwWindows_complete (ns := ns) (base := base) (cut := cut) (i + 1) m hm1
      (fun t ht ↦ by rw [e]; exact hb (t + 1) (by omega))
      (((h.ext m1).and hs1).mono fun σ ⟨⟨hc, h3, _, _⟩, _, hlo, hhi⟩ ↦
        ⟨fun t ht ↦ by rw [e]; exact hc (t + 1) (by omega), h3, hlo, hhi⟩)
    refine h2.mono fun σ ⟨⟨hw, _, _⟩, hr, elo, ehi⟩ ↦ ⟨qwAK_append.mpr ⟨hw, hr⟩, ?_, ?_⟩
    · simp only [e] at elo
      rw [elo, Finset.sum_range_succ', Nat.add_zero]; ring
    · simp only [e] at ehi
      rw [ehi, Finset.sum_range_succ', Nat.add_zero]; ring

/-! ## A position's store and pointer -/

omit hT hlow in
theorem qwPos_eq {P cut d : ℕ} (hP : P < 2 ^ d) (hc : cut < d) (hd26 : d ≤ 26) :
    eOfNat (P % 2 ^ cut) + cbWord cut * eOfNat (P / 2 ^ cut) = eOfNat P := by
  have hY : P / 2 ^ cut < 2 ^ (d - cut) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, Nat.sub_add_cancel hc.le]
    exact hP
  have hX : P % 2 ^ cut < 2 ^ cut := Nat.mod_lt _ (by positivity)
  rw [mul_comm, eOfNat_mul_cbWord hY (by omega) (by omega), add_comm, eOfNat_add_of_lt hX,
    Nat.div_add_mod]

omit hT hlow in
theorem qwPr_complete {l : List E} {k : ℕ} (hl : l.length = k) {j base cut d : ℕ} {lo hi : V}
    {recon : Option V} {P : ℕ} {R : E} (hrec : recon = none → base = 0) (hP : P < 2 ^ d)
    (hd : 1 ≤ d) (hd26 : d ≤ 26) (hbase : base + d ≤ 192) (hcut : cut = 64 - base % 64)
    (hj : j < Q.np) (hpos : LoadHolds rd Q.pos j (eOfNat P))
    (hpre : QwStab l fun σ ↦ σ lo = eOfNat (P % 2 ^ cut) ∧ (cut < d → σ hi = eOfNat (P / 2 ^ cut)) ∧
      σ (.n 1) = Q.pos ∧ qwOpt σ recon = R) :
    QwExt l (qwPr j base cut d k lo hi recon).2.1 fun σ ↦
      qwAK rd Q σ (qwPr j base cut d k lo hi recon).1 ∧
      qwOpt σ (qwPr j base cut d k lo hi recon).2.2 = R + eOfNat192 (2 ^ base * P) := by
  suffices h : QwExt l (qwPr j base cut d k lo hi recon).2.1 fun σ ↦
      qwAK rd Q σ (qwPr j base cut d k lo hi recon).1 by
    refine (h.and_stab hpre).mono fun σ ⟨hA, hlo, hhi, _, hR⟩ ↦ ⟨hA, ?_⟩
    rw [(qwPr_sound hA.ah hrec hP hd hd26 hbase hcut hlo hhi).2, hR]
  unfold qwPr
  by_cases hc : cut < d
  · rw [ite_pos' hc]
    have hb0 : base ≠ 0 := by intro h0; rw [h0] at hcut; omega
    obtain ⟨rc, rfl⟩ : ∃ rc, recon = some rc := by
      cases recon with
      | none => exact absurd (hrec rfl) hb0
      | some rc => exact ⟨rc, rfl⟩
    have hpE := qwPos_eq hP hc hd26
    refine ⟨[cbWord cut, cbWord cut * eOfNat (P / 2 ^ cut),
      eOfNat (P % 2 ^ cut) + cbWord cut * eOfNat (P / 2 ^ cut), cbWord base,
      cbWord base * eOfNat (P % 2 ^ cut), cbWord (base + cut),
      cbWord (base + cut) * eOfNat (P / 2 ^ cut),
      cbWord base * eOfNat (P % 2 ^ cut) + cbWord (base + cut) * eOfNat (P / 2 ^ cut),
      R + (cbWord base * eOfNat (P % 2 ^ cut) + cbWord (base + cut) * eOfNat (P / 2 ^ cut))],
      by simp [hl], fun t ↦ ?_⟩
    obtain ⟨hlo, hhi, h1, hR⟩ := hpre ([cbWord cut, cbWord cut * eOfNat (P / 2 ^ cut),
      eOfNat (P % 2 ^ cut) + cbWord cut * eOfNat (P / 2 ^ cut), cbWord base,
      cbWord base * eOfNat (P % 2 ^ cut), cbWord (base + cut),
      cbWord (base + cut) * eOfNat (P / 2 ^ cut),
      cbWord base * eOfNat (P % 2 ^ cut) + cbWord (base + cut) * eOfNat (P / 2 ^ cut),
      R + (cbWord base * eOfNat (P % 2 ^ cut) + cbWord (base + cut) * eOfNat (P / 2 ^ cut))] ++ t)
    rw [← List.append_assoc] at hlo hhi h1 hR
    have hm : List.length [cbWord cut, cbWord cut * eOfNat (P / 2 ^ cut),
      eOfNat (P % 2 ^ cut) + cbWord cut * eOfNat (P / 2 ^ cut), cbWord base,
      cbWord base * eOfNat (P % 2 ^ cut), cbWord (base + cut),
      cbWord (base + cut) * eOfNat (P / 2 ^ cut),
      cbWord base * eOfNat (P % 2 ^ cut) + cbWord (base + cut) * eOfNat (P / 2 ^ cut),
      R + (cbWord base * eOfNat (P % 2 ^ cut) + cbWord (base + cut) * eOfNat (P / 2 ^ cut))] = 9 := rfl
    simp only [qwOpt] at hR
    simp only [qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true, Option.getD_some]
    simp (disch := omega) only [qwOaN hl hm, Nat.add_sub_cancel_left, Nat.sub_self,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hlo, hhi hc, h1, hR, hpE]
    repeat' first
      | exact hpos
      | exact Or.inl ⟨rfl, hj⟩
      | trivial
      | refine ⟨?_, ?_⟩
  · rw [ite_neg' hc]
    have hPc : P < 2 ^ cut := lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (by omega))
    cases recon with
    | none =>
      refine QwExt.nil (by simp [hl]) (hpre.mono fun σ ⟨hlo, _, h1, _⟩ ↦ ?_)
      simp only [qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true]
      rw [hlo, h1, Nat.mod_eq_of_lt hPc]
      exact ⟨hpos, Or.inl ⟨rfl, hj⟩⟩
    | some rc =>
      refine ⟨[cbWord base, cbWord base * eOfNat (P % 2 ^ cut),
        R + cbWord base * eOfNat (P % 2 ^ cut)], by simp [hl], fun t ↦ ?_⟩
      obtain ⟨hlo, _, h1, hR⟩ := hpre ([cbWord base, cbWord base * eOfNat (P % 2 ^ cut),
        R + cbWord base * eOfNat (P % 2 ^ cut)] ++ t)
      rw [← List.append_assoc] at hlo h1 hR
      have hm : List.length [cbWord base, cbWord base * eOfNat (P % 2 ^ cut),
        R + cbWord base * eOfNat (P % 2 ^ cut)] = 3 := rfl
      simp only [qwOpt] at hR
      simp only [qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true]
      simp (disch := omega) only [qwOaN hl hm, Nat.add_sub_cancel_left, Nat.sub_self,
        List.getD_cons_zero, List.getD_cons_succ]
      rw [hlo, h1, hR]
      rw [Nat.mod_eq_of_lt hPc] at *
      repeat' first
        | exact hpos
        | exact Or.inl ⟨rfl, hj⟩
        | trivial
        | refine ⟨?_, ?_⟩

/-- What every position reads of the frame's first values: the arguments, the `wins` run's
address and the words of the run where the memory holds them. -/
def QwBase (rd : Reader) (Q : QwEnv) (σ : Val) : Prop :=
  σ (.n 1) = Q.pos ∧ σ (.n 2) = Q.ptrs ∧ σ (.n 3) = Q.tabs ∧ σ (.n 4) = Q.run ∧ IsInK Q.run ∧
    ∀ x < 56, ∀ v, rd (Q.run.limb 0 * Parameters.addressOfIndex x) = some v → v = σ (.n (5 + x))

omit hT hlow in
theorem qwPtr_complete {l : List E} {k : ℕ} (hl : l.length = k) {j n : ℕ} (hn : 1 ≤ n)
    (hjn : j * n + n ≤ 56) (hj : j < Q.np) (hptr : LoadHolds rd Q.ptrs j (Q.run * gen ^ (j * n)))
    (hpre : QwStab l (QwBase rd Q)) :
    QwExt l (qwPtr j n k).2.1 fun σ ↦ qwAK rd Q σ (qwPtr j n k).1 := by
  unfold qwPtr
  by_cases hj0 : j = 0
  · subst hj0
    simp only [↓reduceIte]
    refine QwExt.nil hl (hpre.mono fun σ ⟨_, h2, _, h4, _⟩ ↦ ?_)
    simp only [qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true]
    rw [h2, h4]
    simp only [Nat.zero_mul, pow_zero, mul_one] at hptr
    exact ⟨hptr, by simp [hj]⟩
  · simp only [hj0, ↓reduceIte]
    obtain ⟨r, hr⟩ : ∃ r, 56 - j * n = r + 1 := ⟨56 - j * n - 1, by omega⟩
    refine ⟨[Q.run * gen ^ (j * n)], by simp [hl], fun t ↦ ?_⟩
    obtain ⟨_, h2, _, _, hrun, hfr⟩ := hpre ([Q.run * gen ^ (j * n)] ++ t)
    rw [← List.append_assoc] at h2 hfr
    have e : Val.ofArgs (l ++ [Q.run * gen ^ (j * n)] ++ t) (.n k) = Q.run * gen ^ (j * n) := by
      rw [qwOaN hl (m := [Q.run * gen ^ (j * n)]) (N := 1) rfl le_rfl (by omega)]; simp
    rw [hr, List.range_succ_eq_map, List.map_cons]
    simp only [qwAK_cons, qwAK_nil, Atom.Holds, QwEnv.Ok, and_true, e, h2]
    refine ⟨⟨⟨isInK_mul hrun (gen_pow_isInK _), fun x hx v hv ↦ ?_⟩, ?_⟩, hptr, by simp [hj]⟩
    · have hx' : x < 56 - j * n := by simpa [hr] using hx
      rw [gen_pow_eq_ofK, limb0_mul_ofK hrun, mul_assoc, Parameters.addressOfIndex,
        Parameters.addressOfIndex, ← pow_add, ← Parameters.addressOfIndex] at hv
      rw [hfr (j * n + x) (by omega) v hv]
      rcases x with _ | x
      · simp
      · simp [Nat.add_assoc]
    · exact ⟨trivial, by omega, by omega, by rw [show 5 + j * n + 0 - 5 = j * n by omega]⟩

/-! ## A position -/

theorem qwPos_complete {l : List E} {k : ℕ} (hl : l.length = k) {d cd : ℕ} (hs : QwShape d cd)
    {j : ℕ} (hj : j < 192 / d) {recon : Option V} {R : E} (hrec : recon = none → j = 0) {P : ℕ}
    (hP : P < 2 ^ d) (hnp : Q.np = 192 / d) (hpos : LoadHolds rd Q.pos j (eOfNat P))
    (hptr : LoadHolds rd Q.ptrs j (Q.run * gen ^ (j * qwN d cd)))
    (hpre : QwStab l fun σ ↦ (∀ i < qwN d cd, σ (.n (5 + j * qwN d cd + i)) = gen ^ qwVal d cd P i) ∧
      QwBase rd Q σ ∧ qwOpt σ recon = R) :
    QwExt l (qwPos d cd j k recon).2.1 fun σ ↦ qwAK rd Q σ (qwPos d cd j k recon).1 ∧
      qwOpt σ (qwPos d cd j k recon).2.2 = R + eOfNat192 (2 ^ (j * d) * P) ∧
      (qwPos d cd j k recon).2.2.isSome = true := by
  have hd14 := hs.1
  have hd26 := hs.2.1
  have hwin := hs.2.2.2.2.2.1
  have hN1 : 1 ≤ qwN d cd := by unfold qwN; omega
  have hbase : j * d + d ≤ 192 := by
    have := Nat.div_mul_le_self 192 d
    have : (j + 1) * d ≤ 192 / d * d := Nat.mul_le_mul_right _ hj
    nlinarith
  have hjn : j * qwN d cd + qwN d cd ≤ 56 := by
    have := hs.2.2.1
    have : (j + 1) * qwN d cd ≤ 192 / d * qwN d cd := Nat.mul_le_mul_right _ hj
    nlinarith
  simp only [qwPos]
  set cut := 64 - j * d % 64 with hcut
  have hcut64 : cut ≤ 64 := by omega
  have hns : ∀ t < qwN d cd, qwVal d cd P t < 2 ^ (qwWin d cd t).2 := fun t _ ↦ qwVal_lt _ _ _ _
  obtain ⟨sl, sh⟩ := qwSums hs hcut64 hns (qwN d cd) le_rfl
  rw [qw_pos_tS hs hP] at sl sh
  have hlos := (qwWindows_isSome (d := d) (cd := cd) (base := j * d) (cut := cut)
    (at0 := j * qwN d cd) 0 (qwN d cd) k none none).1 (Or.inr ⟨0, hN1, by
      rw [Nat.zero_add, ← qwOff_lt (by omega), hs.2.2.2.1]; omega⟩)
  have hhis : cut < d → _ := fun hc ↦ (qwWindows_isSome (d := d) (cd := cd) (base := j * d)
    (cut := cut) (at0 := j * qwN d cd) 0 (qwN d cd) k none none).2 (Or.inr ⟨qwN d cd - 1,
      by omega, by
        obtain ⟨-, -, he, -⟩ := hwin (qwN d cd - 1) (by omega)
        rw [Nat.zero_add, ← qwOff_lt (by omega), he, Nat.sub_add_cancel hN1, qwOff_top]
        exact hc⟩)
  have hW := qwWindows_complete hT hlow (ns := qwVal d cd P) (base := j * d) (cut := cut)
    (at0 := j * qwN d cd) 0 (qwN d cd) hl (lo := none) (hi := none) (LO := 0) (HI := 0)
    (fun t ht ↦ by rw [Nat.zero_add]; exact ⟨(hwin t ht).2.1, hns t ht⟩)
    (hpre.mono fun σ ⟨hc, hb, _⟩ ↦ ⟨fun t ht ↦ by rw [Nat.zero_add]; exact hc t ht, hb.2.2.1,
      rfl, rfl⟩)
  have h := (hW.bind fun m1 hm1 hs1 ↦
    (qwPr_complete hm1 (j := j) (base := j * d) (cut := cut) (d := d) (recon := recon) (P := P)
      (R := R)
      (lo := ((qwWindows d cd (j * d) cut (j * qwN d cd) 0 (qwN d cd) k none none).2.2.1.getD (.n 0)))
      (hi := ((qwWindows d cd (j * d) cut (j * qwN d cd) 0 (qwN d cd) k none none).2.2.2.getD (.n 0)))
      (fun h0 ↦ by rw [hrec h0, Nat.zero_mul]) hP (by omega) hd26 hbase rfl (by omega) hpos
      (((hpre.ext m1).and hs1).mono fun σ ⟨⟨_, hb, hR⟩, _, elo, ehi⟩ ↦
        ⟨?_, fun hc ↦ ?_, hb.1, hR⟩)).bind
      fun m2 hm2 hs2 ↦ qwPtr_complete hm2 hN1 hjn (by omega) hptr
        ((((hpre.ext m1).ext m2)).mono fun σ h ↦ h.2.1))
  · refine h.mono fun σ ⟨⟨hw, _, _⟩, ⟨hp, hpv⟩, hq⟩ ↦ ⟨?_, hpv, ?_⟩
    · exact qwAK_append.mpr ⟨qwAK_append.mpr ⟨hw, hp⟩, hq⟩
    · unfold qwPr; split
      · rfl
      · split <;> rfl
  · rw [qwOpt_getD (σ := σ) hlos, elo]
    simp only [zero_add] at sl ⊢
    rw [sl]
  · rw [qwOpt_getD (σ := σ) (hhis hc), ehi]
    simp only [zero_add] at sh ⊢
    rw [sh]

/-! ## The positions -/

theorem qwPositions_complete {d cd : ℕ} (hs : QwShape d cd) {Ps : ℕ → ℕ}
    (hPs : ∀ j < 192 / d, Ps j < 2 ^ d) (hnp : Q.np = 192 / d)
    (hrd : ∀ j < 192 / d, LoadHolds rd Q.pos j (eOfNat (Ps j)) ∧
      LoadHolds rd Q.ptrs j (Q.run * gen ^ (j * qwN d cd))) :
    ∀ (j m : ℕ) {l : List E} {k : ℕ}, l.length = k → ∀ {recon : Option V} {R : E},
    j + m ≤ 192 / d → (recon = none → j = 0) →
    QwStab l (fun σ ↦ (∀ j' < 192 / d, ∀ i < qwN d cd,
        σ (.n (5 + j' * qwN d cd + i)) = gen ^ qwVal d cd (Ps j') i) ∧
      QwBase rd Q σ ∧ qwOpt σ recon = R) →
    QwExt l (qwPositions d cd j m k recon).2.1 fun σ ↦ qwAK rd Q σ (qwPositions d cd j m k recon).1 ∧
      qwOpt σ (qwPositions d cd j m k recon).2.2 =
        R + ∑ t ∈ Finset.range m, eOfNat192 (2 ^ ((j + t) * d) * Ps (j + t)) ∧
      (recon.isSome = true ∨ 1 ≤ m → (qwPositions d cd j m k recon).2.2.isSome = true)
  | _, 0, l, k, hl, recon, R, _, _, h => QwExt.nil (by simp [qwPositions, hl]) (h.mono fun σ h ↦ by
      refine ⟨by simp [qwPositions, qwAK_nil], by simp [qwPositions, h.2.2], fun h' ↦ ?_⟩
      rcases h' with h' | h'
      · exact h'
      · omega)
  | j, m + 1, l, k, hl, recon, R, hjm, hrec, h => by
    simp only [qwPositions]
    have h1 := qwPos_complete hT hlow hl hs (j := j) (by omega) hrec (hPs j (by omega)) hnp
      (hrd j (by omega)).1 (hrd j (by omega)).2
      (h.mono fun σ ⟨hc, hb, hR⟩ ↦ ⟨hc j (by omega), hb, hR⟩)
    have e : ∀ t, j + 1 + t = j + (t + 1) := fun t ↦ by omega
    have h2 := h1.bind fun m1 hm1 hs1 ↦ qwPositions_complete hs hPs hnp hrd (j + 1) m hm1
      (by omega) (fun h0 ↦ by
        have := (hs1 []).2.2
        rw [h0] at this
        exact absurd this (by decide))
      (((h.ext m1).and hs1).mono fun σ ⟨⟨hc, hb, _⟩, _, hv, _⟩ ↦ ⟨hc, hb, hv⟩)
    refine h2.mono fun σ ⟨⟨hp, _, hsome⟩, hr, ev, esome⟩ ↦ ⟨qwAK_append.mpr ⟨hp, hr⟩, ?_,
      fun _ ↦ esome (Or.inl hsome)⟩
    simp only [e] at ev
    rw [ev, Finset.sum_range_succ', Nat.add_zero]; ring

/-! ## The rest windows -/

theorem qwRest_complete {d cd : ℕ} (hs : QwShape d cd) {rs : ℕ → ℕ}
    (hrs : ∀ r < qwRestN d, rs r < 2 ^ (qwRestWin d r).2) :
    ∀ (i m : ℕ) {l : List E} {k : ℕ}, l.length = k → ∀ {recon : Option V} {R : E},
    i + m ≤ qwRestN d → QwStab l (fun σ ↦ σ (.n 3) = Q.tabs ∧ qwOpt σ recon = R) →
    QwExt l (qwRest d i m k recon).2.1 fun σ ↦ qwAK rd Q σ (qwRest d i m k recon).1 ∧
      qwOpt σ (qwRest d i m k recon).2.2 =
        R + ∑ t ∈ Finset.range m, eOfNat192 (2 ^ (qwRestWin d (i + t)).1 * rs (i + t)) ∧
      (recon.isSome = true → (qwRest d i m k recon).2.2.isSome = true)
  | _, 0, l, k, hl, recon, R, _, h => QwExt.nil (by simp [qwRest, hl]) (h.mono fun σ h ↦
      ⟨by simp [qwRest, qwAK_nil], by simp [qwRest, h.2], fun h' ↦ h'⟩)
  | i, m + 1, l, k, hl, recon, R, him, h => by
    simp only [qwRest]
    obtain ⟨-, -, hw1, hw7, h192, h64⟩ := hs.2.2.2.2.2.2.1 i (by omega)
    have h0 : QwExt l (k + 1) fun σ ↦ σ (.n k) = gen ^ rs i :=
      ⟨[gen ^ rs i], by simp [hl], fun t ↦ by
        beta_reduce
        rw [qwOaN hl (m := [gen ^ rs i]) (N := 1) rfl le_rfl (by omega)]; simp⟩
    have e : ∀ t, i + 1 + t = i + (t + 1) := fun t ↦ by omega
    have h2 := h0.bind fun m0 hm0 hs0 ↦
      (qwRead_complete hT hlow hm0 (c := .n k) (start := (qwRestWin d i).1) hw7 (hrs i (by omega))
        (((h.ext m0).and hs0).mono fun σ ⟨⟨h3, _⟩, hk⟩ ↦ ⟨hk, h3⟩)).bind fun m1 hm1 hs1 ↦
        (qwScale_complete (rd := rd) (Q := Q) hm1 (qwRestWin d i).1 (hs1.mono fun σ h ↦ h.2)).bind
          fun m2 hm2 hs2 ↦
          (qwAcc_complete (rd := rd) (Q := Q) hm2 (acc := recon)
            ((((h.ext m0).ext m1).ext m2).and hs2 |>.mono fun σ h ↦ ⟨h.1.2, h.2.2⟩)).bind
            fun m3 hm3 hs3 ↦ qwRest_complete hs hrs (i + 1) m hm3 (by omega)
              ((((h.ext m0).ext m1).ext m2).ext m3 |>.and hs3 |>.mono fun σ h ↦ ⟨h.1.1, h.2.2⟩)
    refine h2.mono fun σ ⟨_, ⟨hr, _⟩, ⟨hsc, _⟩, ⟨ha, _⟩, hrest, ev, esome⟩ ↦
      ⟨qwAK_append.mpr ⟨qwAK_append.mpr ⟨qwAK_append.mpr ⟨hr, hsc⟩, ha⟩, hrest⟩, ?_,
        fun _ ↦ esome (qwAcc_isSome _ _ _)⟩
    have hst : (qwRestWin d i).1 < 192 := by omega
    have hm : 2 ^ ((qwRestWin d i).1 % 64) * rs i < 2 ^ 64 :=
      calc 2 ^ ((qwRestWin d i).1 % 64) * rs i < 2 ^ ((qwRestWin d i).1 % 64) * 2 ^ (qwRestWin d i).2 :=
            Nat.mul_lt_mul_of_pos_left (hrs i (by omega)) (by positivity)
        _ = 2 ^ ((qwRestWin d i).1 % 64 + (qwRestWin d i).2) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h64
    simp only [e] at ev
    rw [ev, mul_comm (eOfNat (rs i)), cbWord_eq', coordBasis_mul_eOfNat hst hm, Finset.sum_range_succ',
      Nat.add_zero]
    ring

end reads

/-! ## The body -/

/-- The honest frame's first `61` words: the arguments, the `wins` run's address, the run (the
honest windows `qwRunW`, then whatever the memory holds there). -/
noncomputable def qwFrame0 (rd : Reader) (d cd : ℕ) (w pos ptrs tabs run : E) : List E :=
  [w, pos, ptrs, tabs, run] ++ (List.range 56).map fun x ↦
    if x < 192 / d * qwN d cd then qwRunW d cd w x
    else (rd (run.limb 0 * Parameters.addressOfIndex x)).getD 0

theorem qwRun_eq : qwRun = .n 5 :: (List.range 55).map (fun i ↦ V.n (5 + (i + 1))) := rfl

theorem qwRun_getElem {x : ℕ} (hx : x < qwRun.length) : qwRun[x] = .n (5 + x) := by
  simp [qwRun]

/-- **`decode_query_windows` is complete, at a shape of its template**: on a reader defined below
`2^7`, holding the window table at `tabs`, the honest windows in the run at `run` where it holds a
word, the positions at `pos` and the pointers `run·g^(j·qwN)` at `ptrs`, the honest valuation
takes the parameters to `[w, pos, ptrs, tabs]`, every atom of the body holds and is of a covered
kind, and the body returns `[]`. -/
theorem qw_holds {d cd : ℕ} (hs : QwShape d cd) {rd : Reader} {w pos ptrs tabs run : E}
    (hlow : ∀ i < 128, (rd (Parameters.addressOfIndex i)).isSome) (hT : WinTabs rd tabs)
    (hrun : FrameRun rd run (192 / d * qwN d cd) (qwRunW d cd w))
    (hrd : ∀ j < 192 / d, LoadHolds rd pos j (eOfNat (qwPosOf d w j)) ∧
      LoadHolds rd ptrs j (run * gen ^ (j * qwN d cd))) :
    ∃ σ : Val, [V.n 0, .n 1, .n 2, .n 3].map σ = [w, pos, ptrs, tabs] ∧
      qwAK rd ⟨pos, ptrs, tabs, run, 192 / d⟩ σ (qwBody d cd) ∧
      ∀ C : CallRel, Stmt.HoldsList C rd σ (qwBody d cd) False (fun rs ↦ rs = []) := by
  set Q : QwEnv := ⟨pos, ptrs, tabs, run, 192 / d⟩ with hQ
  have hT' : WinTabs rd Q.tabs := hT
  have hd14 := hs.1
  have hper : 192 / d * d ≤ 192 := Nat.div_mul_le_self 192 d
  have hper1 : 1 ≤ 192 / d := (Nat.le_div_iff_mul_le (by omega)).mpr (by have := hs.2.1; omega)
  have hM : 192 / d * qwN d cd ≤ 56 := hs.2.2.1
  set l0 := qwFrame0 rd d cd w pos ptrs tabs run with hl0d
  have hl0 : l0.length = 61 := by simp [l0, qwFrame0]
  have hl5 : [w, pos, ptrs, tabs, run].length = 5 := rfl
  have hrl : ((List.range 56).map fun x ↦
      if x < 192 / d * qwN d cd then qwRunW d cd w x
      else (rd (run.limb 0 * Parameters.addressOfIndex x)).getD 0).length = 56 := by simp
  -- the run's words
  have g : ∀ t x, x < 56 → Val.ofArgs (l0 ++ t) (.n (5 + x)) =
      if x < 192 / d * qwN d cd then qwRunW d cd w x
      else (rd (run.limb 0 * Parameters.addressOfIndex x)).getD 0 := fun t x hx ↦ by
    rw [hl0d, qwFrame0, qwOaN hl5 hrl (by omega) (by omega), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hx)]
    simp
  have hfr : QwStab l0 fun σ ↦ ∀ x < 56, ∀ v, rd (run.limb 0 * Parameters.addressOfIndex x) = some v →
      v = σ (.n (5 + x)) := fun t x hx v hv ↦ by
    rw [g t x hx]
    split_ifs with h
    · exact hrun.2 x h v hv
    · rw [hv]; rfl
  have hbase : QwStab l0 (QwBase rd Q) := fun t ↦
    ⟨rfl, rfl, rfl, rfl, hrun.1, hfr t⟩
  have hcells : QwStab l0 fun σ ↦ ∀ j' < 192 / d, ∀ i < qwN d cd,
      σ (.n (5 + j' * qwN d cd + i)) = gen ^ qwVal d cd (qwPosOf d w j') i := fun t j' hj' i hi ↦ by
    have hx : j' * qwN d cd + i < 192 / d * qwN d cd := by
      have : (j' + 1) * qwN d cd ≤ 192 / d * qwN d cd := Nat.mul_le_mul_right _ hj'
      nlinarith
    rw [Nat.add_assoc, g t _ (by omega), ite_pos' hx, qwRunW_at w hi]
  have hw0 : QwStab l0 fun σ ↦ σ (.n 0) = w := fun _ ↦ rfl
  have hFA : QwStab l0 fun σ ↦ qwAK rd Q σ [.atom (.frameAddr (.n 4) qwRun)] := fun t ↦ by
    obtain ⟨_, _, _, h4, hrK, hf⟩ := hbase t
    rw [qwAK_cons, qwAK_nil, and_true]
    refine ⟨⟨by rw [h4]; exact hrK, fun x hx v hv ↦ ?_⟩, ?_⟩
    · rw [qwRun_getElem hx]
      rw [h4] at hv
      exact hf x (by simpa [qwRun] using hx) v hv
    · rw [qwRun_eq]
      exact ⟨rfl, le_rfl, by decide, by rw [h4]; simp⟩
  -- the positions, the rest
  have hpos := qwPositions_complete (Q := Q) hT' hlow hs (Ps := qwPosOf d w)
    (fun j _ ↦ qwPosOf_lt d w j) rfl hrd 0 (192 / d) hl0 (recon := none) (R := 0) (by omega)
    (fun _ ↦ rfl) ((hcells.and hbase).mono fun σ h ↦ ⟨h.1, h.2, rfl⟩)
  have hall := (hpos.bind fun m1 hm1 hs1 ↦
    qwRest_complete (Q := Q) hT' hlow hs (rs := qwRestOf d w) (fun r _ ↦ qwRestOf_lt d w r) 0
      (qwRestN d) hm1 (recon := (qwPositions d cd 0 (192 / d) 61 none).2.2) (by omega)
      (((hbase.ext m1).and hs1).mono fun σ h ↦ ⟨h.1.2.2.1, h.2.2.1⟩)).and_stab
    ((hFA.and hw0).and hbase)
  obtain ⟨m, -, hst⟩ := hall
  have H := hst []
  rw [List.append_nil] at H
  set σ := Val.ofArgs (l0 ++ m)
  obtain ⟨⟨⟨hpA, -, hpsome⟩, hrA, hrv, hrsome⟩, ⟨hfa, hσ0⟩, hb⟩ := H
  -- the reconstruction is the word
  set N := 192 / d
  set Vd := qwDigit d w
  have htop : ∀ t ≤ N, qwTop d t = t * d := fun t ht ↦ by
    unfold qwTop
    split_ifs with h
    · rfl
    · rw [show t = N by omega, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      exact Nat.min_eq_right hper
  have hrw := hs.2.2.2.2.2.2.1
  have ht : Tiled (qwTop d) Vd (N + qwRestN d) := fun t ht ↦ by
    by_cases h : t < N
    · rw [htop t h.le, htop (t + 1) h]
      refine ⟨Nat.mul_le_mul_right _ (by omega), ?_⟩
      simp only [Vd, qwDigit, show t < 192 / d from h, ↓reduceIte]
      rw [show (t + 1) * d - t * d = d by rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]]
      exact qwPosOf_lt d w t
    · obtain ⟨e1, e2, -, -, -, -⟩ := hrw (t - N) (by omega)
      rw [show N + (t - N) = t by omega] at e1 e2
      rw [← e1, ← e2]
      refine ⟨by omega, ?_⟩
      simp only [Vd, qwDigit, show ¬ t < 192 / d from h, ↓reduceIte]
      rw [Nat.add_sub_cancel_left]
      exact qwRestOf_lt d w _
  have htot : qwOpt σ (qwRest d 0 (qwRestN d) (qwPositions d cd 0 N 61 none).2.1
      (qwPositions d cd 0 N 61 none).2.2).2.2 = w := by
    have hrec : eOfNat192 (tS (qwTop d) Vd (N + qwRestN d)) = w := by
      rw [qw_recon hs w, eOfNat192_eToNat]
    rw [hrv]
    conv_rhs => rw [← hrec]
    rw [← eOfNat192_tS ht _ le_rfl, Finset.sum_range_add]
    simp only [zero_add]
    congr 1
    · exact Finset.sum_congr rfl fun t htt ↦ by
        have := Finset.mem_range.mp htt
        simp only [Vd, qwDigit, show t < 192 / d from this, ↓reduceIte, htop t this.le]
    · exact Finset.sum_congr rfl fun t htt ↦ by
        have := Finset.mem_range.mp htt
        obtain ⟨e1, -⟩ := hrw t this
        simp only [Vd, qwDigit, show ¬ N + t < 192 / d by omega, ↓reduceIte]
        rw [show N + t - 192 / d = t from Nat.add_sub_cancel_left N t, e1]
  have hsome := hrsome (hpsome (Or.inr hper1))
  have hassert : σ ((qwRest d 0 (qwRestN d) (qwPositions d cd 0 N 61 none).2.1
      (qwPositions d cd 0 N 61 none).2.2).2.2.getD (.n 0)) + σ (.n 0) = 0 := by
    rw [qwOpt_getD (σ := σ) hsome, htot, hσ0]
    exact e_add_eq_zero_iff.mpr rfl
  have hAK : qwAK rd Q σ (qwBody d cd) := by
    unfold qwBody
    simp only
    rw [qwAK_append, qwAK_append, qwAK_append]
    refine ⟨⟨⟨hfa, hpA⟩, hrA⟩, fun a ha ↦ ?_⟩
    simp only [List.mem_cons, Stmt.atom.injEq, List.mem_nil_iff, or_false, reduceCtorEq] at ha
    subst ha
    exact ⟨hassert, trivial⟩
  refine ⟨σ, ?_, hAK, fun C ↦ ?_⟩
  · simp only [List.map_cons, List.map_nil, hσ0, hb.1, hb.2.1, hb.2.2.1]
    rfl
  · have hA := hAK
    unfold qwBody at hA ⊢
    simp only at hA ⊢
    rw [holdsList_append, holdsList_atoms (allAtoms_of_all (qwBody_atoms d cd))]
    rw [qwAK_append] at hA
    refine ⟨fun a ha ↦ (hA.1 a ha).1, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_nil]
    exact ⟨hassert, trivial⟩


/-! ## The relation -/

/-- **`decode_query_windows__L{d}_L{cd}` is complete**: on every reader defined below `2^7` (its
range checks), holding the window table at `tabs`, the honest windows in the run at `run` (where it
holds a word), the word's positions at `pos` and the pointers `run·g^(j·qwN)` at `ptrs`, the
function relates `[w, pos, ptrs, tabs]` to `[]`. -/
def decode_query_windows_complete_Spec (name : String) (d cd : ℕ) : Prop :=
  ∀ (rd : Reader) (w pos ptrs tabs run : E),
    (∀ i < 128, (rd (Parameters.addressOfIndex i)).isSome) → WinTabs rd tabs →
    FrameRun rd run (192 / d * qwN d cd) (qwRunW d cd w) →
    (∀ j < 192 / d, LoadHolds rd pos j (eOfNat (qwPosOf d w j)) ∧
      LoadHolds rd ptrs j (run * gen ^ (j * qwN d cd))) →
    coreProgram.Rel rd name [w, pos, ptrs, tabs] []

/-- Every deployed specialization. -/
def decode_query_windows_complete_all_Spec : Prop :=
  ∀ p ∈ queryWindowsShapes, decode_query_windows_complete_Spec p.1 p.2.1 p.2.2

/-- **`decode_query_windows` is complete** at a shape of the template. -/
theorem qw_complete {name : String} {d cd : ℕ} (hs : QwShape d cd) (hq : QwIs name (qwBody d cd)) :
    decode_query_windows_complete_Spec name d cd := by
  intro rd w pos ptrs tabs run hlow hT hrun hrd
  obtain ⟨fn, hfind, hps, hbody⟩ := hq
  obtain ⟨σ, hp, -, hh⟩ := qw_holds hs hlow hT hrun hrd
  rw [rel_iff_sem hfind]
  exact ⟨σ, by rw [hps]; exact hp, by rw [hbody]; exact hh _⟩

end
end LeanVM.Guest.B1
