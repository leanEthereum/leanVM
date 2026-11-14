module

public import LeanVM.Guest.Mode.Abs
public import LeanVM.Guest.Mode.Frame
public import LeanVM.Prover.ExecuteCompleteLog

/-!
# What the mode walk's state means

At an executor state `s`, relative to its frame `s.fp`: a base's word (`BaseVal`), a product's
(`MonoVal`; `hp q d` is the word of the cell `[q]·g^d` names), an exponent's value (`IdxVal`: a base whose word is `g^e`, `e < 2^62`, plus a
constant), and the facts of `Abs` (`Holds`): written frame cells, known words, nonzero cells,
known heap words (`HVF`), written heap cells (`HW`) and runs (`RW`), exponents in order (`LTF`),
the last products (`PrF`), and runs of pointers (`PW`, each cell holding a word whose given cells
past the cell it names are written, `PtrW`). Every fact is existential in the words it reads, so it survives every
step that keeps the frame (`Holds.mono`). `covered_sound`: a heap cell the walk knows written is,
whatever word names it.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec (St Mem maxCells gpow_inj Mem.le_trans Mem.get_of_written)

@[expose] public section

/-! ## Evaluation order

Each strict form is the plain one. -/

theorem Abs.force_eq {β : Type} (A : Abs) (k : Abs → β) : A.force k = k A := by
  obtain ⟨w, v, nz, hv, h, r, lt, pr, xs, p⟩ := A
  simp only [Abs.force, Exec.Trie.seq_eq]

theorem foldlA_eq {α : Type} (f : Abs → α → Abs) : ∀ (A : Abs) (l : List α), foldlA f A l = l.foldl f A
  | _, [] => rfl
  | A, x :: l => by
    show (f A x).force (foldlA f · l) = _
    rw [Abs.force_eq, foldlA_eq f _ l, List.foldl_cons]

theorem foldlT_eq : ∀ (t : Exec.Trie Unit) (l : List ℕ),
    foldlT t l = l.foldl (fun t o ↦ t.set () Exec.envDepth o) t
  | _, [] => rfl
  | t, o :: l => by
    show (t.set () Exec.envDepth o).seq (foldlT · l) = _
    rw [Exec.Trie.seq_eq, foldlT_eq _ l, List.foldl_cons]

theorem listSeq_id {α β : Type} (l : List α) (k : List α → β) : Exec.listSeq l k = k l :=
  Exec.listSeq_eq l k

theorem Abs.interS_eq (A B : Abs) : A.interS B = A.inter B := by
  unfold Abs.interS
  generalize A.inter B = C
  obtain ⟨w, v, nz, hv, h, r, lt, pr, xs, p⟩ := C
  simp only [listSeq_id]

/-! ## Words -/

/-- Word `v` names cell `x`. -/
def Names (v : E) (x : ℕ) : Prop := v.limb 0 = g ^ x ∧ x < maxCells

/-- Base `b`'s word. -/
def BaseVal (s : St) : Base → E → Prop
  | .fr o, v => s.mem.get (s.fp + o) = some v
  | .hp q d, v => ∃ p x, s.mem.get (s.fp + q) = some p ∧ Names (p * ofK (g ^ d)) x ∧
    s.mem.get x = some v

/-- A base list's product. -/
def BsVal (s : St) : List (Base × ℕ) → E → Prop
  | [], v => v = 1
  | (b, e) :: bs, v => ∃ u w, BaseVal s b u ∧ BsVal s bs w ∧ v = u ^ e * w

/-- A product's word. -/
def MonoVal (s : St) (m : Mono) (v : E) : Prop :=
  ∃ w, BsVal s m.bs w ∧ v = ofK (g ^ s.fp) ^ m.fp * ofK (g ^ m.k) * w

/-- An exponent's value. -/
def IdxVal (s : St) : Idx → ℕ → Prop
  | .num n, x => x = n
  | .ex b c, x => ∃ v e, BaseVal s b v ∧ v = ofK (g ^ e) ∧ e < 2 ^ 62 ∧ x = e + c

/-- A known word's meaning. -/
def ValOk (s : St) : Val → E → Prop
  | .m x, v => MonoVal s x v
  | .imm k0 k1, v => v = OffsetInstruction.immediateWord k0 k1
  | .tab x d, v => ∃ u c, MonoVal s ⟨0, d, [(x, 1)]⟩ u ∧ Names u c ∧ s.mem.get c = some v

/-- The heap cell `k` names holds a word `x` means. -/
def HVF (s : St) (k : Mono) (x : Val) : Prop :=
  ∃ v c w, MonoVal s k v ∧ Names v c ∧ s.mem.get c = some w ∧ ValOk s x w

/-- The heap cell `k` names is written. -/
def HW (s : St) (k : Mono) : Prop :=
  ∃ v x, MonoVal s k v ∧ Names v x ∧ s.mem.written x = true

/-- Run `r`'s cells are written. -/
def RW (s : St) (r : Rng) : Prop :=
  ∃ vq xlo xhi, MonoVal s r.q vq ∧ IdxVal s r.lo xlo ∧ IdxVal s r.hi xhi ∧
    ∀ j, xlo ≤ j → j < xhi → ∃ x, Names (vq * ofK (g ^ (r.S * j + r.d))) x ∧ s.mem.written x = true

/-- Cell `x` holds a word naming a cell whose cells `os` past it are written. -/
def PtrW (m : Mem) (x : ℕ) (os : List ℕ) : Prop :=
  ∃ p, m.get x = some p ∧ ∀ o ∈ os, ∃ y, Names (p * ofK (g ^ o)) y ∧ m.written y = true

/-- Run `r`'s cells hold pointers, each with the cells `os` past the cell it names written. -/
def PW (s : St) (r : Rng) (os : List ℕ) : Prop :=
  ∃ vq xlo xhi, MonoVal s r.q vq ∧ IdxVal s r.lo xlo ∧ IdxVal s r.hi xhi ∧
    ∀ j, xlo ≤ j → j < xhi → ∃ x, Names (vq * ofK (g ^ (r.S * j + r.d))) x ∧ PtrW s.mem x os

/-- Exponent `a` is below exponent `b`. -/
def LTF (s : St) (a b : Idx) : Prop := ∃ xa xb, IdxVal s a xa ∧ IdxVal s b xb ∧ xa < xb

/-- Frame cell `c` holds the product of frame cells `a` and `b`. -/
def PrF (s : St) (a b c : ℕ) : Prop :=
  ∃ va vb, s.mem.get (s.fp + a) = some va ∧ s.mem.get (s.fp + b) = some vb ∧
    s.mem.get (s.fp + c) = some (va * vb)

/-- Frame cell `c` holds the sum of frame cells `a` and `b`. -/
def XorF (s : St) (a b c : ℕ) : Prop :=
  ∃ va vb, s.mem.get (s.fp + a) = some va ∧ s.mem.get (s.fp + b) = some vb ∧
    s.mem.get (s.fp + c) = some (va + vb)

/-- Facts under a condition: the base has a word, and, when its exponent is the condition's, they
hold. -/
def CndHolds (s : St) (c : Cnd) : Prop :=
  (∃ v, BaseVal s c.x v) ∧ (IdxVal s (.ex c.x 0) c.j → (∀ k ∈ c.h, HW s k) ∧ (∀ r ∈ c.r, RW s r) ∧
    (∀ q ∈ c.p, PW s q.1 q.2) ∧ (∀ p ∈ c.lt, LTF s p.1 p.2) ∧ ∀ p ∈ c.hv, HVF s p.1 p.2)

/-- **The state's memory has what the walk knows.** -/
structure Holds (s : St) (A : Abs) : Prop where
  w : ∀ o, A.w.get o = some () → s.mem.written (s.fp + o) = true
  v : ∀ o x, A.v.get o = some x → ∃ u, s.mem.get (s.fp + o) = some u ∧ ValOk s x u
  nz : ∀ o, A.nz.get o = some () → ∃ u, s.mem.get (s.fp + o) = some u ∧ u ≠ 0
  hv : ∀ p ∈ A.hv, HVF s p.1 p.2
  h : ∀ k ∈ A.h, HW s k
  r : ∀ r ∈ A.r, RW s r
  lt : ∀ p ∈ A.lt, LTF s p.1 p.2
  pr : ∀ p ∈ A.pr, PrF s p.1 p.2.1 p.2.2
  xs : ∀ c a b, A.xs.get c = some (a, b) → XorF s a b c
  p : ∀ q ∈ A.p, PW s q.1 q.2
  c : ∀ q ∈ A.c, CndHolds s q

/-- What the program's table holds: the jump table's cells, written with their targets' powers. -/
def EnvOk (s : St) (E : Env) : Prop :=
  E.pows.Ok ∧ E.jtHi ≤ maxCells ∧ ∀ d e, E.jtLo ≤ d → d < E.jtHi → E.jt.get d = some e → s.mem.get d = some (ofK (g ^ e))

/-! ## Words are functions of the memory -/

theorem names_inj {v : E} {x y : ℕ} (h1 : Names v x) (h2 : Names v y) : x = y :=
  gpow_inj (by have := h1.2; unfold maxCells at this; omega)
    (by have := h2.2; unfold maxCells at this; omega) (h1.1.symm.trans h2.1)

theorem Base.beq_eq {a b : Base} (h : a.beq b = true) : a = b := by
  cases a <;> cases b <;> simp_all [Base.beq]

theorem BaseVal.unique {s : St} {b : Base} {u u' : E} (h : BaseVal s b u) (h' : BaseVal s b u') :
    u = u' := by
  cases b with
  | fr o => exact Option.some.inj (h.symm.trans h')
  | hp q d =>
    obtain ⟨p, x, h1, h2, h3⟩ := h
    obtain ⟨p', x', h1', h2', h3'⟩ := h'
    obtain rfl := Option.some.inj (h1.symm.trans h1')
    obtain rfl := names_inj h2 h2'
    exact Option.some.inj (h3.symm.trans h3')

theorem BsVal.unique {s : St} : ∀ {bs : List (Base × ℕ)} {v v' : E}, BsVal s bs v → BsVal s bs v' →
    v = v'
  | [], _, _, h, h' => h.trans h'.symm
  | (_, _) :: _, _, _, ⟨u, w, h1, h2, h3⟩, ⟨u', w', h1', h2', h3'⟩ => by
    rw [h3, h3', h1.unique h1', h2.unique h2']

theorem MonoVal.unique {s : St} {m : Mono} {v v' : E} (h : MonoVal s m v) (h' : MonoVal s m v') :
    v = v' := by
  obtain ⟨w, h1, h2⟩ := h
  obtain ⟨w', h1', h2'⟩ := h'
  rw [h2, h2', h1.unique h1']

theorem ofK_gpow_inj {e e' : ℕ} (he : e < 2 ^ 63) (he' : e' < 2 ^ 63)
    (h : ofK (g ^ e) = ofK (g ^ e')) : e = e' :=
  gpow_inj he he' (ofK_injective h)

theorem IdxVal.unique {s : St} {i : Idx} {x x' : ℕ} (h : IdxVal s i x) (h' : IdxVal s i x') : x = x' := by
  cases i with
  | num => exact h.trans h'.symm
  | ex b c =>
    obtain ⟨v, e, h1, h2, h3, h4⟩ := h
    obtain ⟨v', e', h1', h2', h3', h4'⟩ := h'
    have := h1.unique h1'
    subst this
    rw [h4, h4', ofK_gpow_inj (by omega) (by omega) (h2.symm.trans h2')]

/-! ## Monotonicity -/

section mono

variable {s s' : St} (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp)
include hle hfp

theorem BaseVal.mono {b : Base} {v : E} (h : BaseVal s b v) : BaseVal s' b v := by
  cases b with
  | fr o => show s'.mem.get (s'.fp + o) = some _; rw [hfp]; exact hle.get _ _ h
  | hp q d =>
    obtain ⟨p, x, h1, h2, h3⟩ := h
    exact ⟨p, x, by rw [hfp]; exact hle.get _ _ h1, h2, hle.get _ _ h3⟩

theorem BsVal.mono : ∀ {bs : List (Base × ℕ)} {v : E}, BsVal s bs v → BsVal s' bs v
  | [], _, h => h
  | (_, _) :: _, _, ⟨u, w, h1, h2, h3⟩ => ⟨u, w, h1.mono hle hfp, h2.mono, h3⟩

theorem MonoVal.mono {m : Mono} {v : E} (h : MonoVal s m v) : MonoVal s' m v := by
  obtain ⟨w, h1, h2⟩ := h
  exact ⟨w, h1.mono hle hfp, by rw [hfp]; exact h2⟩

theorem IdxVal.mono {i : Idx} {x : ℕ} (h : IdxVal s i x) : IdxVal s' i x := by
  cases i with
  | num => exact h
  | ex b c =>
    obtain ⟨v, e, h1, h2⟩ := h
    exact ⟨v, e, h1.mono hle hfp, h2⟩

theorem ValOk.mono {x : Val} {v : E} (h : ValOk s x v) : ValOk s' x v := by
  cases x with
  | m => exact MonoVal.mono hle hfp h
  | imm => exact h
  | tab b d =>
    obtain ⟨u, c, h1, h2, h3⟩ := h
    exact ⟨u, c, h1.mono hle hfp, h2, hle.get _ _ h3⟩

omit hfp in
theorem written_le {c : ℕ} (h : s.mem.written c = true) : s'.mem.written c = true :=
  written_mono hle h

omit hfp in
theorem PtrW.mono {x : ℕ} {os : List ℕ} (h : PtrW s.mem x os) : PtrW s'.mem x os := by
  obtain ⟨p, h1, h2⟩ := h
  exact ⟨p, hle.get _ _ h1, fun o ho ↦ (h2 o ho).elim fun y hy ↦ ⟨y, hy.1, written_le hle hy.2⟩⟩

theorem PW.mono {r : Rng} {os : List ℕ} (h : PW s r os) : PW s' r os := by
  obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := h
  exact ⟨vq, xlo, xhi, h1.mono hle hfp, h2.mono hle hfp, h3.mono hle hfp,
    fun j a b ↦ (h4 j a b).elim fun x hx ↦ ⟨x, hx.1, hx.2.mono hle⟩⟩

theorem HW.mono {k : Mono} (h : HW s k) : HW s' k := by
  obtain ⟨v, x, h1, h2, h3⟩ := h
  exact ⟨v, x, h1.mono hle hfp, h2, written_le hle h3⟩

theorem RW.mono {r : Rng} (h : RW s r) : RW s' r := by
  obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := h
  exact ⟨vq, xlo, xhi, h1.mono hle hfp, h2.mono hle hfp, h3.mono hle hfp,
    fun j a b ↦ (h4 j a b).elim fun x hx ↦ ⟨x, hx.1, written_le hle hx.2⟩⟩

theorem LTF.mono {a b : Idx} (h : LTF s a b) : LTF s' a b := by
  obtain ⟨xa, xb, h1, h2, h3⟩ := h
  exact ⟨xa, xb, h1.mono hle hfp, h2.mono hle hfp, h3⟩

theorem HVF.mono {k : Mono} {x : Val} (h : HVF s k x) : HVF s' k x := by
  obtain ⟨v, c, w, h1, h2, h3, h4⟩ := h
  exact ⟨v, c, w, h1.mono hle hfp, h2, hle.get _ _ h3, h4.mono hle hfp⟩

theorem CndHolds.mono {c : Cnd} (h : CndHolds s c) : CndHolds s' c := by
  obtain ⟨⟨v, hv⟩, h⟩ := h
  refine ⟨⟨v, hv.mono hle hfp⟩, fun hi ↦ ?_⟩
  have hi' : IdxVal s (.ex c.x 0) c.j := by
    obtain ⟨v', e, h1, h2, h3, h4⟩ := hi
    exact ⟨v', e, by rw [(hv.mono hle hfp).unique h1] at hv; exact hv, h2, h3, h4⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h hi'
  exact ⟨fun k hk ↦ (h1 k hk).mono hle hfp, fun r hr ↦ (h2 r hr).mono hle hfp,
    fun q hq ↦ (h3 q hq).mono hle hfp, fun p hp ↦ (h4 p hp).mono hle hfp, fun p hp ↦ (h5 p hp).mono hle hfp⟩

theorem Holds.mono {A : Abs} (h : Holds s A) : Holds s' A where
  w o ho := by rw [hfp]; exact written_le hle (h.w o ho)
  v o x hx := by
    obtain ⟨u, h1, h2⟩ := h.v o x hx
    exact ⟨u, by rw [hfp]; exact hle.get _ _ h1, h2.mono hle hfp⟩
  nz o ho := by
    obtain ⟨u, h1, h2⟩ := h.nz o ho
    exact ⟨u, by rw [hfp]; exact hle.get _ _ h1, h2⟩
  hv p hp := by
    obtain ⟨v, c, w, h1, h2, h3, h4⟩ := h.hv p hp
    exact ⟨v, c, w, h1.mono hle hfp, h2, hle.get _ _ h3, h4.mono hle hfp⟩
  h k hk := by
    obtain ⟨v, x, h1, h2, h3⟩ := h.h k hk
    exact ⟨v, x, h1.mono hle hfp, h2, written_le hle h3⟩
  r r hr := by
    obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := h.r r hr
    exact ⟨vq, xlo, xhi, h1.mono hle hfp, h2.mono hle hfp, h3.mono hle hfp,
      fun j a b ↦ (h4 j a b).elim fun x hx ↦ ⟨x, hx.1, written_le hle hx.2⟩⟩
  lt p hp := by
    obtain ⟨a, b, h1, h2, h3⟩ := h.lt p hp
    exact ⟨a, b, h1.mono hle hfp, h2.mono hle hfp, h3⟩
  pr p hp := by
    obtain ⟨a, b, h1, h2, h3⟩ := h.pr p hp
    exact ⟨a, b, by rw [hfp]; exact hle.get _ _ h1, by rw [hfp]; exact hle.get _ _ h2,
      by rw [hfp]; exact hle.get _ _ h3⟩
  xs c a b hc := by
    obtain ⟨va, vb, h1, h2, h3⟩ := h.xs c a b hc
    exact ⟨va, vb, by rw [hfp]; exact hle.get _ _ h1, by rw [hfp]; exact hle.get _ _ h2,
      by rw [hfp]; exact hle.get _ _ h3⟩
  p q hq := (h.p q hq).mono hle hfp
  c q hq := (h.c q hq).mono hle hfp

omit hfp in
theorem EnvOk.mono {E : Env} (h : EnvOk s E) : EnvOk s' E :=
  ⟨h.1, h.2.1, fun d e h1 h2 h3 ↦ hle.get _ _ (h.2.2 d e h1 h2 h3)⟩

end mono

/-! ## Products -/

theorem BsVal.insert {s : St} {b : Base} {e : ℕ} {u : E} (hb : BaseVal s b u) :
    ∀ {bs : List (Base × ℕ)} {w : E}, BsVal s bs w → BsVal s (insertBs (b, e) bs) (u ^ e * w)
  | [], w, h => ⟨u, 1, hb, rfl, by rw [h]⟩
  | (b', e') :: bs, _, ⟨u', w', h1, h2, h3⟩ => by
    unfold insertBs
    dsimp only
    split_ifs with hq hl
    · obtain rfl := Base.beq_eq hq
      obtain rfl := hb.unique h1
      exact ⟨u, w', hb, h2, by rw [h3, pow_add, mul_assoc]⟩
    · exact ⟨u, u' ^ e' * w', hb, ⟨u', w', h1, h2, rfl⟩, by rw [h3]⟩
    · exact ⟨u', u ^ e * w', h1, BsVal.insert hb h2, by rw [h3]; ring⟩

theorem BsVal.mul {s : St} : ∀ {a b : List (Base × ℕ)} {va vb : E}, BsVal s a va → BsVal s b vb →
    BsVal s (mulBs a b) (va * vb)
  | [], _, _, _, h, h' => by rw [h, one_mul]; exact h'
  | (_, _) :: _, _, _, _, ⟨u, w, h1, h2, h3⟩, h' => by
    rw [h3, mul_assoc]
    exact BsVal.insert h1 (BsVal.mul h2 h')

theorem MonoVal.mul {s : St} {a b : Mono} {va vb : E} (ha : MonoVal s a va) (hb : MonoVal s b vb) :
    MonoVal s (a.mul b) (va * vb) := by
  obtain ⟨wa, h1, h2⟩ := ha
  obtain ⟨wb, h1', h2'⟩ := hb
  refine ⟨wa * wb, BsVal.mul h1 h1', ?_⟩
  rw [h2, h2']
  simp only [Mono.mul, pow_add, ofK_mul]
  ring

theorem MonoVal.shift {s : St} {m : Mono} {v : E} (h : MonoVal s m v) (o : ℕ) :
    MonoVal s (m.shift o) (v * ofK (g ^ o)) := by
  obtain ⟨w, h1, h2⟩ := h
  refine ⟨w, h1, ?_⟩
  rw [h2]
  simp only [Mono.shift, pow_add, ofK_mul]
  ring

theorem MonoVal.root {s : St} {o : ℕ} {v : E} (h : s.mem.get (s.fp + o) = some v) :
    MonoVal s (.root o) v :=
  ⟨v, ⟨v, 1, h, rfl, by rw [pow_one, mul_one]⟩, by simp [Mono.root]⟩

theorem MonoVal.gp {s : St} (e : ℕ) : MonoVal s (.gp e) (ofK (g ^ e)) :=
  ⟨1, rfl, by simp [Mono.gp]⟩

theorem MonoVal.own {s : St} (d : ℕ) : MonoVal s (.own d) (ofK (g ^ (s.fp + d))) :=
  ⟨1, rfl, by simp [Mono.own, pow_add, ofK_mul]⟩

theorem MonoVal.one' {s : St} : MonoVal s .one 1 := ⟨1, rfl, by simp [Mono.one]⟩

theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

theorem limb_mul_ofK (x : E) (a : K) (l : Fin 2) : (x * ofK a).limb l = x.limb l * a := by
  rw [← ofLimbs_limb x, ofK_eq_ofLimbs, mul_limbs]
  fin_cases l <;> simp [ofLimbs_limb]

/-- A word naming `b`, times `g^o`, names `b + o` when that is below `maxCells`. -/
theorem names_shift {v : E} {b o : ℕ} (h : v.limb 0 = g ^ b) (hl : b + o < maxCells) :
    Names (v * ofK (g ^ o)) (b + o) :=
  ⟨by rw [limb_mul_ofK, h, pow_add], hl⟩

/-! ## Exponents -/

theorem Idx.sle_sound {s : St} {a b : Idx} (h : a.sle b = true) {xb : ℕ} (hb : IdxVal s b xb) :
    ∃ xa, IdxVal s a xa ∧ xa ≤ xb := by
  cases a with
  | num n =>
    cases b with
    | num m => exact ⟨n, rfl, by simp only [Idx.sle, decide_eq_true_eq] at h; rw [hb]; exact h⟩
    | ex y c =>
      obtain ⟨v, e, -, -, -, rfl⟩ := hb
      exact ⟨n, rfl, by simp only [Idx.sle, decide_eq_true_eq] at h; omega⟩
  | ex x c =>
    cases b with
    | num => simp [Idx.sle] at h
    | ex y c' =>
      simp only [Idx.sle, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain rfl := Base.beq_eq h.1
      obtain ⟨v, e, h1, h2, h3, rfl⟩ := hb
      exact ⟨e + c, ⟨v, e, h1, h2, h3, rfl⟩, by omega⟩

theorem Idx.succ_val {s : St} {a : Idx} {x : ℕ} (h : IdxVal s a.succ x) :
    ∃ y, IdxVal s a y ∧ x = y + 1 := by
  cases a with
  | num n => exact ⟨n, rfl, h⟩
  | ex b c =>
    obtain ⟨v, e, h1, h2, h3, h4⟩ := h
    exact ⟨e + c, ⟨v, e, h1, h2, h3, rfl⟩, by omega⟩

theorem Idx.shift_val {s : St} {a : Idx} {x : ℕ} (h : IdxVal s a x) (t : ℕ) :
    IdxVal s (a.shift t) (x + t) := by
  cases a with
  | num n => show x + t = n + t; rw [show x = n from h]
  | ex b c =>
    obtain ⟨v, e, h1, h2, h3, h4⟩ := h
    exact ⟨v, e, h1, h2, h3, by omega⟩

theorem Idx.succ_val' {s : St} {a : Idx} {x : ℕ} (h : IdxVal s a x) : IdxVal s a.succ (x + 1) := by
  cases a with
  | num n => show x + 1 = n + 1; rw [show x = n from h]
  | ex b c =>
    obtain ⟨v, e, h1, h2, h3, h4⟩ := h
    exact ⟨v, e, h1, h2, h3, by omega⟩

/-- `p.off a = some t`: `a = p + t`. -/
theorem Idx.off_val {s : St} {p a : Idx} {t : ℕ} (h : p.off a = some t) {xp : ℕ} (hp : IdxVal s p xp) :
    IdxVal s a (xp + t) := by
  cases p with
  | num n =>
    cases a with
    | num m =>
      simp only [Idx.off] at h
      split_ifs at h with h1
      cases h
      show xp + (m - n) = m
      rw [show xp = n from hp]; omega
    | ex => simp [Idx.off] at h
  | ex x c =>
    cases a with
    | num => simp [Idx.off] at h
    | ex y c' =>
      simp only [Idx.off, Bool.and_eq_true, decide_eq_true_eq] at h
      split_ifs at h with h1
      cases h
      obtain rfl := Base.beq_eq h1.1
      obtain ⟨v, e, h2, h3, h4, rfl⟩ := hp
      exact ⟨v, e, h2, h3, h4, by omega⟩

/-- `q.off b = some t`, `b`'s value: `q`'s, `t` below it. -/
theorem Idx.off_val' {s : St} {q b : Idx} {t : ℕ} (h : q.off b = some t) {xb : ℕ} (hb : IdxVal s b xb) :
    ∃ xq, IdxVal s q xq ∧ xb = xq + t := by
  cases q with
  | num n =>
    cases b with
    | num m =>
      simp only [Idx.off] at h
      split_ifs at h with h1
      cases h
      exact ⟨n, rfl, by rw [show xb = m from hb]; omega⟩
    | ex => simp [Idx.off] at h
  | ex x c =>
    cases b with
    | num => simp [Idx.off] at h
    | ex y c' =>
      simp only [Idx.off, Bool.and_eq_true, decide_eq_true_eq] at h
      split_ifs at h with h1
      cases h
      obtain rfl := Base.beq_eq h1.1
      obtain ⟨v, e, h2, h3, h4, rfl⟩ := hb
      exact ⟨e + c, ⟨v, e, h2, h3, h4, rfl⟩, by omega⟩

theorem Abs.le_sound {s : St} {A : Abs} (hA : Holds s A) {a b : Idx} (h : A.le a b = true) {xb : ℕ}
    (hb : IdxVal s b xb) : ∃ xa, IdxVal s a xa ∧ xa ≤ xb := by
  unfold Abs.le at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Idx.sle_sound h hb
  · obtain ⟨⟨p, q⟩, hm, hh⟩ := List.any_eq_true.mp h
    dsimp only at hh
    split at hh
    · rename_i t ht
      obtain ⟨xq, hq, rfl⟩ := Idx.off_val' ht hb
      obtain ⟨xp', xq', hp', hq', hlt⟩ := hA.lt _ hm
      obtain rfl := hq.unique hq'
      obtain ⟨xa, ha, hle⟩ := Idx.sle_sound hh (Idx.shift_val (Idx.succ_val' hp') t)
      exact ⟨xa, ha, by omega⟩
    · simp at hh

theorem Abs.ltI_sound {s : St} {A : Abs} (hA : Holds s A) {a b : Idx} (h : A.ltI a b = true)
    {xb : ℕ} (hb : IdxVal s b xb) : ∃ xa, IdxVal s a xa ∧ xa < xb := by
  unfold Abs.ltI at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨y, hy, hle⟩ := Idx.sle_sound h hb
    obtain ⟨xa, ha, rfl⟩ := Idx.succ_val hy
    exact ⟨xa, ha, by omega⟩
  · obtain ⟨⟨p, q⟩, hm, hh⟩ := List.any_eq_true.mp h
    dsimp only at hh
    obtain ⟨xp, xq, hp, hq, hlt⟩ := hA.lt _ hm
    rcases Bool.or_eq_true_iff.mp hh with hh | hh
    · split at hh
      · rename_i t ht
        obtain ⟨y, hy, hle⟩ := Idx.sle_sound hh hb
        obtain rfl := hy.unique (Idx.shift_val hq t)
        exact ⟨xp + t, Idx.off_val ht hp, by omega⟩
      · simp at hh
    · -- `a + 1 ≤ p < q ≤ b + 1`
      simp only [Bool.and_eq_true] at hh
      obtain ⟨y, hy, hle⟩ := Idx.sle_sound hh.2 (Idx.succ_val' hb)
      obtain rfl := hy.unique hq
      obtain ⟨z, hz, hle'⟩ := Idx.sle_sound hh.1 hp
      obtain ⟨xa, ha, rfl⟩ := Idx.succ_val hz
      exact ⟨xa, ha, by omega⟩

/-! ## Runs -/

theorem bsBeq_eq : ∀ {a b : List (Base × ℕ)}, bsBeq a b = true → a = b
  | [], [], _ => rfl
  | (x, e) :: as, (y, f) :: bs, h => by
    simp only [bsBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [Base.beq_eq h.1.1, h.1.2, bsBeq_eq h.2]
  | [], _ :: _, h => by simp [bsBeq] at h
  | _ :: _, [], h => by simp [bsBeq] at h

theorem Mono.beq_eq {a b : Mono} (h : a.beq b = true) : a = b := by
  obtain ⟨fp, k, bs⟩ := a
  obtain ⟨fp', k', bs'⟩ := b
  simp only [Mono.beq, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.1, h.1.2, bsBeq_eq h.2]

/-- Dividing a base list by `b^e`: the product is `u^e` times the rest's. -/
theorem BsVal.remove {s : St} {b : Base} {e : ℕ} :
    ∀ {bs rest : List (Base × ℕ)} {v : E}, removeBs (b, e) bs = some rest → BsVal s bs v →
      ∃ u w, BaseVal s b u ∧ BsVal s rest w ∧ v = u ^ e * w
  | [], _, _, h, _ => by simp [removeBs] at h
  | (b', e') :: bs, rest, v, h, ⟨u, w, h1, h2, h3⟩ => by
    unfold removeBs at h
    by_cases hq : b.beq b' = true
    · rw [ite_eq_left hq] at h
      by_cases he : (e == e') = true
      · rw [ite_eq_left he] at h
        cases h
        obtain rfl := Base.beq_eq hq
        obtain rfl := beq_iff_eq.mp he
        exact ⟨u, w, h1, h2, h3⟩
      · rw [ite_eq_right he] at h
        cases h
    · rw [ite_eq_right hq] at h
      obtain ⟨rest', hr, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨u2, w2, h4, h5, h6⟩ := BsVal.remove hr h2
      exact ⟨u2, u ^ e' * w2, h4, ⟨u, w2, h1, h5, rfl⟩, by rw [h3, h6]; ring⟩

theorem BsVal.remove_inv {s : St} {b : Base} {e : ℕ} {u : E} (hu : BaseVal s b u) :
    ∀ {bs rest : List (Base × ℕ)} {w : E}, removeBs (b, e) bs = some rest → BsVal s rest w →
      BsVal s bs (u ^ e * w)
  | [], _, _, h, _ => by simp [removeBs] at h
  | (b', e') :: bs, rest, w, h, hw => by
    unfold removeBs at h
    by_cases hq : b.beq b' = true
    · rw [ite_eq_left hq] at h
      by_cases he : (e == e') = true
      · rw [ite_eq_left he] at h
        cases h
        obtain rfl := Base.beq_eq hq
        obtain rfl := beq_iff_eq.mp he
        exact ⟨u, w, hu, hw, rfl⟩
      · rw [ite_eq_right he] at h; cases h
    · rw [ite_eq_right hq] at h
      obtain ⟨rest', hr, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨u', w', h1, h2, rfl⟩ := hw
      exact ⟨u', u ^ e * w', h1, BsVal.remove_inv hu hr h2, by ring⟩

/-- The exponent `idxOf` reads: `k`'s word is the run's at that exponent. -/
theorem Rng.idxOf_sound {s : St} {r : Rng} {k : Mono} {i : Idx} (h : r.idxOf k = some i) {vk vq : E}
    (hk : MonoVal s k vk) (hq : MonoVal s r.q vq) {xi : ℕ} (hi : IdxVal s i xi) :
    vk = vq * ofK (g ^ (r.S * xi + r.d)) := by
  unfold Rng.idxOf at h
  by_cases hc : (k.fp == r.q.fp && decide (r.q.k + r.d ≤ k.k) && (k.k - r.q.k - r.d) % r.S == 0 &&
      decide (0 < r.S)) = true
  swap
  · rw [ite_eq_right hc] at h; cases h
  rw [ite_eq_left hc] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hfp, hkk⟩, hmod⟩, hS⟩ := hc
  obtain ⟨wk, hwk, rfl⟩ := hk
  obtain ⟨wq, hwq, rfl⟩ := hq
  have hkk' : k.k = r.q.k + (r.S * ((k.k - r.q.k - r.d) / r.S) + r.d) := by
    have h5 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    have : r.S * ((k.k - r.q.k - r.d) / r.S) = k.k - r.q.k - r.d := by rw [Nat.mul_comm]; exact h5
    omega
  by_cases hb : bsBeq k.bs r.q.bs = true
  · rw [ite_eq_left hb] at h
    cases h
    rw [bsBeq_eq hb] at hwk
    obtain rfl := hwk.unique hwq
    rw [show xi = (k.k - r.q.k - r.d) / r.S from hi, hfp]
    conv_lhs => rw [hkk']
    simp only [ofK_pow]
    ring
  · rw [ite_eq_right hb] at h
    split at h
    · rename_i x e _
      split at h
      · rename_i rest hr
        by_cases hrq : bsBeq rest r.q.bs = true
        · rw [ite_eq_left hrq] at h
          cases h
          obtain ⟨u, w, hu, hw, rfl⟩ := BsVal.remove hr hwk
          rw [bsBeq_eq hrq] at hw
          obtain rfl := hw.unique hwq
          obtain ⟨v, ex, hv, hv', hex, rfl⟩ := hi
          obtain rfl := hu.unique hv
          rw [hfp, hv']
          conv_lhs => rw [hkk']
          simp only [ofK_pow]
          ring
        · rw [ite_eq_right hrq] at h; cases h
      · cases h
    · cases h

theorem RW.down {s : St} {r : Rng} (h : RW s r) : RW s r.down := by
  obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := h
  refine ⟨vq, xlo + r.d / r.S, xhi + r.d / r.S, h1, Idx.shift_val h2 _, Idx.shift_val h3 _,
    fun j hj1 hj2 ↦ ?_⟩
  have e1 : r.S * (j - r.d / r.S) = r.S * j - r.S * (r.d / r.S) := Nat.mul_sub _ _ _
  have e2 : r.S * (r.d / r.S) ≤ r.S * j := Nat.mul_le_mul_left _ (by omega)
  have e3 : r.S * (r.d / r.S) ≤ r.d := Nat.mul_div_le r.d r.S
  have : r.S * (j - r.d / r.S) + r.d = r.S * j + (r.d - r.S * (r.d / r.S)) := by omega
  have h5 := h4 (j - r.d / r.S) (by omega) (by omega)
  rw [this] at h5
  exact h5

theorem inRng1_sound {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} (hr : RW s r)
    (h : (match r.idxOf k with
      | some i => A.le r.lo i && A.ltI i r.hi
      | none => false) = true) {vk : E} (hk : MonoVal s k vk) :
    ∃ x, Names vk x ∧ s.mem.written x = true := by
  split at h
  · rename_i i hi
    simp only [Bool.and_eq_true] at h
    obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := hr
    obtain ⟨xi, hxi, hlt⟩ := Abs.ltI_sound hA h.2 h3
    obtain ⟨xlo', hlo', hle⟩ := Abs.le_sound hA h.1 hxi
    obtain rfl := h2.unique hlo'
    rw [Rng.idxOf_sound hi hk h1 hxi]
    exact h4 xi hle hlt
  · simp at h

theorem Abs.inRng_sound {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} (hr : RW s r)
    (h : A.inRng k r = true) {vk : E} (hk : MonoVal s k vk) :
    ∃ x, Names vk x ∧ s.mem.written x = true := by
  unfold Abs.inRng at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact inRng1_sound hA hr h hk
  · simp only [Bool.and_eq_true] at h
    exact inRng1_sound hA hr.down h.2 hk

theorem PW.down {s : St} {r : Rng} {os : List ℕ} (h : PW s r os) : PW s r.down os := by
  obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := h
  refine ⟨vq, xlo + r.d / r.S, xhi + r.d / r.S, h1, Idx.shift_val h2 _, Idx.shift_val h3 _,
    fun j hj1 hj2 ↦ ?_⟩
  have e1 : r.S * (j - r.d / r.S) = r.S * j - r.S * (r.d / r.S) := Nat.mul_sub _ _ _
  have e2 : r.S * (r.d / r.S) ≤ r.S * j := Nat.mul_le_mul_left _ (by omega)
  have e3 : r.S * (r.d / r.S) ≤ r.d := Nat.mul_div_le r.d r.S
  have : r.S * (j - r.d / r.S) + r.d = r.S * j + (r.d - r.S * (r.d / r.S)) := by omega
  have h5 := h4 (j - r.d / r.S) (by omega) (by omega)
  rw [this] at h5
  exact h5

theorem inRng1_ptr {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} {os : List ℕ}
    (hr : PW s r os) (h : (match r.idxOf k with
      | some i => A.le r.lo i && A.ltI i r.hi
      | none => false) = true) {vk : E} (hk : MonoVal s k vk) :
    ∃ x, Names vk x ∧ PtrW s.mem x os := by
  split at h
  · rename_i i hi
    simp only [Bool.and_eq_true] at h
    obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := hr
    obtain ⟨xi, hxi, hlt⟩ := Abs.ltI_sound hA h.2 h3
    obtain ⟨xlo', hlo', hle⟩ := Abs.le_sound hA h.1 hxi
    obtain rfl := h2.unique hlo'
    rw [Rng.idxOf_sound hi hk h1 hxi]
    exact h4 xi hle hlt
  · simp at h

/-- **A heap cell a run of pointers holds holds a pointer.** -/
theorem Abs.inRng_ptr {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} {os : List ℕ}
    (hr : PW s r os) (h : A.inRng k r = true) {vk : E} (hk : MonoVal s k vk) :
    ∃ x, Names vk x ∧ PtrW s.mem x os := by
  unfold Abs.inRng at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact inRng1_ptr hA hr h hk
  · simp only [Bool.and_eq_true] at h
    exact inRng1_ptr hA hr.down h.2 hk

/-- A heap cell `coveredHR` knows: the cell its word names is written. -/
theorem Abs.coveredHR_ex {s : St} {A : Abs} (hA : Holds s A) {k : Mono} (h : A.coveredHR k = true)
    {vk : E} (hk : MonoVal s k vk) : ∃ x, Names vk x ∧ s.mem.written x = true := by
  unfold Abs.coveredHR at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨k', hm, hb⟩ := List.any_eq_true.mp h
    obtain rfl := Mono.beq_eq hb
    obtain ⟨v, x, h1, h2, h3⟩ := hA.h _ hm
    obtain rfl := h1.unique hk
    exact ⟨x, h2, h3⟩
  · obtain ⟨r, hm, hb⟩ := List.any_eq_true.mp h
    exact Abs.inRng_sound hA (hA.r r hm) hb hk

theorem Idx.beq_eq {a b : Idx} (h : a.beq b = true) : a = b := by
  cases a <;> cases b <;> simp only [Idx.beq, Bool.and_eq_true, beq_iff_eq] at h
  · rw [h]
  · simp at h
  · simp at h
  · rw [Base.beq_eq h.1, h.2]

theorem MonoVal.unshift {s : St} {m : Mono} {o : ℕ} {v : E} (h : MonoVal s (m.shift o) v) :
    ∃ u, MonoVal s m u ∧ v = u * ofK (g ^ o) := by
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨_, ⟨w, hw, rfl⟩, by simp only [Mono.shift, pow_add, ofK_mul]; ring⟩

theorem minO_le {acc : Option ℕ} {b c x : ℕ} (h : minO acc b = some c) (hb : x ≤ b)
    (hacc : ∀ a, acc = some a → x ≤ a) : x ≤ c := by
  cases acc with
  | none => cases h; exact hb
  | some a => cases h; exact le_min (hacc a rfl) hb

/-- **A bound the walk knows**: the exponent has a value, at most it. -/
theorem Abs.bound_sound {s : St} {A : Abs} (hA : Holds s A) {hi : Idx} {b : ℕ} (h : A.bound hi = some b) :
    ∃ x, IdxVal s hi x ∧ x ≤ b := by
  cases hi with
  | num n => exact ⟨n, rfl, by simp only [Abs.bound, Option.some.injEq] at h; omega⟩
  | ex y c =>
    simp only [Abs.bound] at h
    have key : ∀ (l : List (Idx × Idx)) (acc : Option ℕ), (∀ p ∈ l, p ∈ A.lt) →
        (∀ a, acc = some a → ∃ x, IdxVal s (.ex y c) x ∧ x ≤ a) →
        ∀ b, l.foldl (fun acc p ↦ match p.2, p.1.off (.ex y c) with
          | .num q, some t => minO acc (q + t - 1)
          | _, _ => acc) acc = some b → ∃ x, IdxVal s (.ex y c) x ∧ x ≤ b := by
      intro l
      induction l with
      | nil => intro acc _ hacc b hb; exact hacc b hb
      | cons p l ih =>
        intro acc hl hacc b hb
        rw [List.foldl_cons] at hb
        refine ih _ (fun p' hp' ↦ hl p' (List.mem_cons_of_mem _ hp')) ?_ b hb
        intro a ha
        split at ha
        · rename_i q t hq ht
          obtain ⟨x1, xq, h1, h2, h3⟩ := hA.lt p (hl p (List.mem_cons_self ..))
          rw [hq] at h2
          have hx := Idx.off_val ht h1
          refine ⟨x1 + t, hx, ?_⟩
          have : xq = q := h2
          cases acc with
          | none => cases ha; omega
          | some a0 =>
            cases ha
            obtain ⟨x', hx', hle⟩ := hacc a0 rfl
            obtain rfl := hx'.unique hx
            exact le_min hle (by omega)
        · exact hacc a ha
    exact key A.lt none (fun _ h ↦ h) (fun _ h ↦ by cases h) b h

theorem BsVal.append {s : St} : ∀ {a b : List (Base × ℕ)} {va vb : E}, BsVal s a va → BsVal s b vb →
    BsVal s (a ++ b) (va * vb)
  | [], _, _, _, h, h' => by rw [h, one_mul]; exact h'
  | (_, _) :: _, _, _, _, ⟨u, w, h1, h2, h3⟩, h' => by
    rw [h3, mul_assoc]
    exact ⟨u, _, h1, BsVal.append h2 h', rfl⟩

theorem BsVal.append_inv {s : St} : ∀ {a b : List (Base × ℕ)} {v : E}, BsVal s (a ++ b) v →
    ∃ va vb, BsVal s a va ∧ BsVal s b vb ∧ v = va * vb
  | [], _, v, h => ⟨1, v, rfl, h, by rw [one_mul]⟩
  | (_, _) :: _, _, _, ⟨u, w, h1, h2, h3⟩ => by
    obtain ⟨va, vb, ha, hb, rfl⟩ := BsVal.append_inv h2
    exact ⟨u ^ _ * va, vb, ⟨u, va, h1, ha, rfl⟩, hb, by rw [h3]; ring⟩

/-- **A pin the walk knows**: the base's word is `g` to it. -/
theorem Abs.pin_sound {s : St} {A : Abs} (hA : Holds s A) {b : Base} {c : ℕ} (h : A.pin b = some c) :
    BaseVal s b (ofK (g ^ c)) := by
  unfold Abs.pin at h
  have key : ∀ (l : List (Idx × Idx)) (acc : Option ℕ), (∀ p ∈ l, p ∈ A.lt) →
      (∀ a, acc = some a → BaseVal s b (ofK (g ^ a)) ∧ a < 2 ^ 62) →
      ∀ c, l.foldl (fun acc p ↦ match p with
        | (.ex b' 0, .num q) =>
          if b'.beq b && 0 < q && A.lt.any (fun p' ↦ p'.1.beq (.num (q - 1)) && p'.2.beq (.ex b 1)) then
            minO acc (q - 1)
          else acc
        | _ => acc) acc = some c → BaseVal s b (ofK (g ^ c)) ∧ c < 2 ^ 62 := by
    intro l
    induction l with
    | nil => intro acc _ hacc c hc; exact hacc c hc
    | cons p l ih =>
      intro acc hl hacc c hc
      rw [List.foldl_cons] at hc
      refine ih _ (fun p' hp' ↦ hl p' (List.mem_cons_of_mem _ hp')) ?_ c hc
      intro a ha
      split at ha
      · rename_i b' q
        split_ifs at ha with hc'
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
          obtain ⟨⟨hb, hq⟩, hany⟩ := hc'
          obtain rfl := Base.beq_eq hb
          obtain ⟨⟨p1, p2⟩, hm, hpp⟩ := List.any_eq_true.mp hany
          simp only [Bool.and_eq_true] at hpp
          obtain rfl := Idx.beq_eq hpp.1
          obtain rfl := Idx.beq_eq hpp.2
          obtain ⟨x1, xq, h1, h2, h3⟩ := hA.lt _ (hl _ (List.mem_cons_self ..))
          obtain ⟨y1, y2, h4, h5, h6⟩ := hA.lt _ hm
          obtain ⟨v, e, hv, hve, he, hx1⟩ := h1
          obtain ⟨v', e', hv', hve', he', hy2⟩ := h5
          have hvv := hv.unique hv'
          rw [hve, hve'] at hvv
          have hee := ofK_gpow_inj (by omega) (by omega) hvv
          have hq' : xq = q := h2
          have hy1 : y1 = q - 1 := h4
          have hval : e = q - 1 := by omega
          rw [hve, hval] at hv
          have hlt : q - 1 < 2 ^ 62 := by omega
          cases acc with
          | none => cases ha; exact ⟨hv, hlt⟩
          | some a0 =>
            cases ha
            obtain ⟨h0, h0lt⟩ := hacc a0 rfl
            have := ofK_gpow_inj (by omega) (by omega) (h0.unique hv)
            rw [show min a0 (q - 1) = a0 by omega]
            exact ⟨h0, h0lt⟩
        · exact hacc a ha
      · exact hacc a ha
  exact (key A.lt none (fun _ h ↦ h) (fun _ h ↦ by cases h) c h).1

theorem MonoVal.append {s : St} {m : Mono} {vm : E} (hm : MonoVal s m vm) {p : Base × ℕ} {u : E}
    (hu : BaseVal s p.1 u) : MonoVal s ⟨m.fp, m.k, m.bs ++ [p]⟩ (vm * u ^ p.2) := by
  obtain ⟨w, hw, rfl⟩ := hm
  exact ⟨w * u ^ p.2, BsVal.append hw ⟨u, 1, hu, rfl, by rw [mul_one]⟩, by ring⟩

/-- **Pinned bases**: a product's word is the word of the product with its bases of known exponent
made powers of `g`. -/
theorem Abs.pinned_val {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {v : E} (h : MonoVal s k v) :
    MonoVal s (A.pinned k) v := by
  have key : ∀ (bs : List (Base × ℕ)) (m : Mono) (vm w : E), MonoVal s m vm → BsVal s bs w →
      MonoVal s (bs.foldl A.pinStep m) (vm * w) := by
    intro bs
    induction bs with
    | nil => intro m vm w hm hw; rw [show w = 1 from hw, mul_one]; exact hm
    | cons p bs ih =>
      intro m vm w hm hw
      obtain ⟨u, w', hu, hw', rfl⟩ := hw
      rw [List.foldl_cons, ← mul_assoc]
      refine ih _ _ _ ?_ hw'
      unfold Abs.pinStep
      split
      · rename_i c hc
        obtain rfl := (A.pin_sound hA hc).unique hu
        rw [← ofK_pow, ← pow_mul]
        exact hm.shift _
      · exact hm.append hu
  obtain ⟨w, hw, rfl⟩ := h
  exact key k.bs ⟨k.fp, k.k, []⟩ _ w ⟨1, rfl, by simp⟩ hw

/-- A product whose pinned form has a word has one. -/
theorem Abs.pinned_ex {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {v : E}
    (h : MonoVal s (A.pinned k) v) : ∃ v', MonoVal s k v' := by
  have key : ∀ (bs : List (Base × ℕ)) (m : Mono) (v : E), MonoVal s (bs.foldl A.pinStep m) v →
      (∃ vm, MonoVal s m vm) ∧ ∃ w, BsVal s bs w := by
    intro bs
    induction bs with
    | nil => intro m v h; exact ⟨⟨v, h⟩, 1, rfl⟩
    | cons p bs ih =>
      intro m v h
      rw [List.foldl_cons] at h
      obtain ⟨⟨vm', hm'⟩, w, hw⟩ := ih _ v h
      unfold Abs.pinStep at hm'
      split at hm'
      · rename_i c hc
        obtain ⟨u, hu, -⟩ := hm'.unshift
        exact ⟨⟨u, hu⟩, _, _, w, A.pin_sound hA hc, hw, rfl⟩
      · obtain ⟨w0, hw0, rfl⟩ := hm'
        obtain ⟨va, vb, ha, ⟨u, w1, hu, hw1, rfl⟩, rfl⟩ := BsVal.append_inv hw0
        exact ⟨⟨_, va, ha, rfl⟩, _, u, w, hu, hw, rfl⟩
  obtain ⟨-, w, hw⟩ := key k.bs ⟨k.fp, k.k, []⟩ v h
  exact ⟨_, w, hw, rfl⟩

/-- A product `knownH` knows has a word. -/
theorem Abs.knownH_val {s : St} {A : Abs} (hA : Holds s A) {m : Mono} (h : A.knownH m = true) :
    ∃ v, MonoVal s m v := by
  have key : ∀ (bs : List (Base × ℕ)), (bs.all fun p ↦ match p.1 with
      | .fr o => A.hasW o
      | .hp q d => A.hasW q && A.coveredHR ⟨0, d, [(.fr q, 1)]⟩) = true → ∃ w, BsVal s bs w := by
    intro bs
    induction bs with
    | nil => intro _; exact ⟨1, rfl⟩
    | cons p bs ih =>
      intro h
      simp only [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨w, hw⟩ := ih h.2
      obtain ⟨b, e⟩ := p
      cases b with
      | fr o =>
        obtain ⟨u, hu⟩ := Mem.get_of_written (hA.w o (by
          have := h.1; unfold Abs.hasW at this
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this; cases x; exact hx))
        exact ⟨u ^ e * w, u, w, hu, hw, rfl⟩
      | hp q d =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hq, hc⟩, -⟩ := h
        obtain ⟨pq, hpq⟩ := Mem.get_of_written (hA.w q (by
          unfold Abs.hasW at hq
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hq; cases x; exact hx))
        have hmq : MonoVal s ⟨0, d, [(.fr q, 1)]⟩ (pq * ofK (g ^ d)) :=
          ⟨pq, ⟨pq, 1, hpq, rfl, by rw [pow_one, mul_one]⟩, by simp only [pow_zero, one_mul]; ring⟩
        obtain ⟨x, hx, hwx⟩ := Abs.coveredHR_ex hA hc hmq
        obtain ⟨u, hu⟩ := Mem.get_of_written hwx
        exact ⟨u ^ e * w, u, w, ⟨pq, x, hpq, hx, hu⟩, hw, rfl⟩
  obtain ⟨w, hw⟩ := key m.bs h
  exact ⟨_, w, hw, rfl⟩

/-- **A run another state entails** is written. -/
theorem Abs.entR_sound {s : St} {A : Abs} (hA : Holds s A) {r : Rng} (h : A.entR r = true) : RW s r := by
  unfold Abs.entR at h
  split at h
  · rename_i a b hlo hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hn, hq⟩, hall⟩ := h
    obtain ⟨vq, hvq⟩ := Abs.knownH_val hA hq
    obtain ⟨xhi, hxhi, hle⟩ := Abs.bound_sound hA hb
    refine ⟨vq, a, xhi, hvq, by rw [hlo]; rfl, hxhi, fun j hj1 hj2 ↦ ?_⟩
    have hc := List.all_eq_true.mp hall (j - a) (List.mem_range.mpr (by omega))
    have := Abs.coveredHR_ex hA hc (hvq.shift _)
    rwa [show r.S * (a + (j - a)) + r.d = r.S * j + r.d by congr 2; omega] at this
  · cases h

/-- **An empty run of pointers another state entails** holds. -/
theorem Abs.entP_sound {s : St} {A : Abs} (hA : Holds s A) {r : Rng} (h : A.entP r = true)
    (os : List ℕ) : PW s r os := by
  unfold Abs.entP at h
  split at h
  · rename_i a b hlo hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨vq, hvq⟩ := Abs.knownH_val hA h.2
    obtain ⟨xhi, hxhi, hle⟩ := Abs.bound_sound hA hb
    exact ⟨vq, a, xhi, hvq, by rw [hlo]; rfl, hxhi, fun j hj1 hj2 ↦ absurd hj2 (by omega)⟩
  · cases h

/-- A table read at a bounded index: the run it reads is written, and the cell is one of it. -/
theorem Abs.tabCovered_sound {s : St} {A : Abs} (hA : Holds s A) {k : Mono} (h : A.tabCovered k = true) :
    (∃ vk, MonoVal s k vk) ∧ ∀ vk, MonoVal s k vk → ∃ x, Names vk x ∧ s.mem.written x = true := by
  unfold Abs.tabCovered at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hfp, h⟩ := h
  obtain ⟨⟨b, e⟩, -, h⟩ := List.any_eq_true.mp h
  split at h
  · rename_i rest hr
    obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := Abs.entR_sound hA h
    obtain ⟨u, ex, hu, rfl, hex, hxhi⟩ := h3
    obtain ⟨wq, hwq, rfl⟩ := h1
    have hkv : MonoVal s k (ofK (g ^ k.k) * (ofK (g ^ ex) ^ e * wq)) := by
      refine ⟨_, BsVal.remove_inv hu hr hwq, ?_⟩
      rw [hfp]; ring
    refine ⟨⟨_, hkv⟩, fun vk hk ↦ ?_⟩
    obtain rfl := hk.unique hkv
    have h2' : xlo = 0 := h2
    obtain ⟨x, hx, hw⟩ := h4 ex (by omega) (by omega)
    refine ⟨x, ?_, hw⟩
    have e1 : ofK (g ^ s.fp) ^ (0 : ℕ) * ofK (g ^ (0 : ℕ)) * wq * ofK (g ^ (e * ex + k.k)) =
        ofK (g ^ k.k) * (ofK (g ^ ex) ^ e * wq) := by
      rw [pow_zero, pow_zero, pow_add, ofK_mul, ← ofK_pow, ← pow_mul, mul_comm ex e,
        show ofK (1 : K) = 1 from map_one (algebraMap K E)]
      ring
    rw [← e1]
    exact hx
  · cases h

/-- A product a run names at an exponent with a value has a word. -/
theorem Rng.idxOf_val {s : St} {r : Rng} {k : Mono} {i : Idx} (h : r.idxOf k = some i) {vq : E}
    (hq : MonoVal s r.q vq) {xi : ℕ} (hi : IdxVal s i xi) : ∃ vk, MonoVal s k vk := by
  unfold Rng.idxOf at h
  by_cases hc : (k.fp == r.q.fp && decide (r.q.k + r.d ≤ k.k) && (k.k - r.q.k - r.d) % r.S == 0 &&
      decide (0 < r.S)) = true
  swap
  · rw [ite_eq_right hc] at h; cases h
  rw [ite_eq_left hc] at h
  obtain ⟨wq, hwq, -⟩ := hq
  by_cases hb : bsBeq k.bs r.q.bs = true
  · exact ⟨_, wq, by rw [bsBeq_eq hb]; exact hwq, rfl⟩
  · rw [ite_eq_right hb] at h
    split at h
    · rename_i x e _
      split at h
      · rename_i rest hr
        by_cases hrq : bsBeq rest r.q.bs = true
        · rw [ite_eq_left hrq] at h
          cases h
          obtain ⟨v, ex, hv, -, -, -⟩ := hi
          rw [bsBeq_eq hrq] at hr
          exact ⟨_, _, BsVal.remove_inv hv hr hwq, rfl⟩
        · rw [ite_eq_right hrq] at h; cases h
      · cases h
    · cases h

theorem inRng1_val {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} {vq : E} {xhi : ℕ}
    (h1 : MonoVal s r.q vq) (h3 : IdxVal s r.hi xhi)
    (h : (match r.idxOf k with
      | some i => A.le r.lo i && A.ltI i r.hi
      | none => false) = true) : ∃ vk, MonoVal s k vk := by
  split at h
  · rename_i i hi
    simp only [Bool.and_eq_true] at h
    obtain ⟨xi, hxi, -⟩ := Abs.ltI_sound hA h.2 h3
    exact Rng.idxOf_val hi h1 hxi
  · simp at h

/-- A heap cell a run holds, the run's product and bound having values, has a word. -/
theorem inRng_val' {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} {vq : E} {xhi : ℕ}
    (h1 : MonoVal s r.q vq) (h3 : IdxVal s r.hi xhi) (h : A.inRng k r = true) : ∃ vk, MonoVal s k vk := by
  unfold Abs.inRng at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact inRng1_val hA h1 h3 h
  · simp only [Bool.and_eq_true] at h
    exact inRng1_val (r := r.down) hA h1 (Idx.shift_val h3 _) h.2

/-- A heap cell a known run holds has a word. -/
theorem inRng_valR {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} (hr : RW s r)
    (h : A.inRng k r = true) : ∃ vk, MonoVal s k vk := by
  obtain ⟨vq, xlo, xhi, h1, -, h3, -⟩ := hr
  exact inRng_val' hA h1 h3 h

/-- The cell past a pointer a run of pointers holds. -/
theorem Abs.ptrHp_sound {s : St} {A : Abs} (hA : Holds s A) {o q d : ℕ}
    (h : (A.p.any fun p ↦ p.2.contains o && A.inRng ⟨0, d, [(.fr q, 1)]⟩ p.1) = true) :
    (∃ vk, MonoVal s ⟨0, o, [(.hp q d, 1)]⟩ vk) ∧ ∀ vk, MonoVal s ⟨0, o, [(.hp q d, 1)]⟩ vk →
      ∃ x, Names vk x ∧ s.mem.written x = true := by
  obtain ⟨⟨r, os⟩, hm, hh⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hh
  obtain ⟨vq, xlo, xhi, h1, -, h3, h4⟩ := hA.p _ hm
  have hpv := inRng_val' hA h1 h3 hh.2
  obtain ⟨vkq, hkq⟩ := hpv
  obtain ⟨x, hx, ⟨pw, hpw, hos⟩⟩ := Abs.inRng_ptr hA (hA.p _ hm) hh.2 hkq
  obtain ⟨w, ⟨pq, w1, hpq, hw1, rfl⟩, rfl⟩ := hkq
  rw [show w1 = 1 from hw1] at hx
  have hbase : BaseVal s (.hp q d) pw := ⟨pq, x, hpq, by simpa [mul_comm] using hx, hpw⟩
  have hkv : MonoVal s ⟨0, o, [(.hp q d, 1)]⟩ (ofK (g ^ o) * pw) :=
    ⟨pw, ⟨pw, 1, hbase, rfl, by rw [pow_one, mul_one]⟩, by simp only [pow_zero, one_mul]⟩
  refine ⟨⟨_, hkv⟩, fun vk hk ↦ ?_⟩
  obtain rfl := hk.unique hkv
  obtain ⟨y, hy, hwy⟩ := hos o hh.1
  exact ⟨y, by rwa [mul_comm] at hy, hwy⟩

/-- **What the walk knows written is**: the cell its word names exists and is written. -/
theorem Abs.covered_ex {s : St} {A : Abs} (hA : Holds s A) (hwf : s.mem.WF)
    (hu : s.mem.used ≤ maxCells) {k : Mono} (h : A.covered k = true) {vk : E} (hk : MonoVal s k vk) :
    ∃ x, Names vk x ∧ s.mem.written x = true := by
  unfold Abs.covered at h
  split at h
  · rename_i d hd
    unfold Mono.ownCell at hd
    split_ifs at hd with hc
    cases hd
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, decide_eq_true_eq] at hc
    obtain ⟨fp, kk, bs⟩ := k
    simp only at hc
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hc
    obtain ⟨w, hw, rfl⟩ := hk
    have hv : ofK (g ^ s.fp) ^ 1 * ofK (g ^ kk) * w = ofK (g ^ (s.fp + kk)) := by
      rw [show w = 1 from hw, pow_one, mul_one, ← ofK_mul, ← pow_add]
    rw [hv]
    have hw' := hA.w kk (Option.isSome_iff_exists.mp h |>.elim fun u hu ↦ by cases u; exact hu)
    obtain ⟨u, hu'⟩ := Mem.get_of_written hw'
    have hlt := hwf.get_lt hu'
    exact ⟨s.fp + kk, ⟨by simp, by omega⟩, hw'⟩
  · simp only [Bool.or_eq_true] at h
    rcases h with (((h | h) | h) | h) | h
    · exact Abs.coveredHR_ex hA h hk
    · exact Abs.coveredHR_ex hA h (Abs.pinned_val hA hk)
    · obtain ⟨⟨r, os⟩, hm, hb⟩ := List.any_eq_true.mp h
      obtain ⟨x, hx, ⟨p, hp, -⟩⟩ := Abs.inRng_ptr hA (hA.p _ hm) hb hk
      exact ⟨x, hx, written_of_get hp⟩
    · split at h
      · exact (Abs.ptrHp_sound hA h).2 vk hk
      · cases h
    · exact (Abs.tabCovered_sound hA h).2 vk hk

/-- What the walk knows written is, whatever word names it. -/
theorem Abs.covered_sound {s : St} {A : Abs} (hA : Holds s A) (hwf : s.mem.WF)
    (hu : s.mem.used ≤ maxCells) {k : Mono}
    (h : A.covered k = true) {vk : E} (hk : MonoVal s k vk) {x : ℕ} (hx : Names vk x) :
    s.mem.written x = true := by
  obtain ⟨y, hy, hw⟩ := Abs.covered_ex hA hwf hu h hk
  rwa [names_inj hx hy]

end

end LeanVM.Guest.Mode
