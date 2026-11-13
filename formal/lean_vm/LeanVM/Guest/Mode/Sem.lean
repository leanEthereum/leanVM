module

public import LeanVM.Guest.Mode.Abs
public import LeanVM.Guest.Mode.Frame
public import LeanVM.Prover.ExecuteCompleteLog

/-!
# What the mode walk's state means

At an executor state `s`, relative to its frame `s.fp`: a base's word (`BaseVal`), a product's
(`MonoVal`; `hp q d` is the word of the cell `[q]·g^d` names), an exponent's value (`IdxVal`: a base whose word is `g^e`, `e < 2^62`, plus a
constant), and the facts of `Abs` (`Holds`): written frame cells, known words, nonzero cells,
known heap words (`HVF`), written heap cells (`HW`) and runs (`RW`), exponents in order (`LTF`) and
the last products (`PrF`). Every fact is existential in the words it reads, so it survives every
step that keeps the frame (`Holds.mono`). `covered_sound`: a heap cell the walk knows written is,
whatever word names it.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec (St Mem maxCells gpow_inj Mem.le_trans Mem.get_of_written)

@[expose] public section

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
  ∃ v, MonoVal s k v ∧ ∀ x, Names v x → s.mem.written x = true

/-- Run `r`'s cells are written. -/
def RW (s : St) (r : Rng) : Prop :=
  ∃ vq xlo xhi, MonoVal s r.q vq ∧ IdxVal s r.lo xlo ∧ IdxVal s r.hi xhi ∧
    ∀ j, xlo ≤ j → j < xhi → ∀ x, Names (vq * ofK (g ^ (r.S * j + r.d))) x → s.mem.written x = true

/-- Exponent `a` is below exponent `b`. -/
def LTF (s : St) (a b : Idx) : Prop := ∃ xa xb, IdxVal s a xa ∧ IdxVal s b xb ∧ xa < xb

/-- Frame cell `c` holds the product of frame cells `a` and `b`. -/
def PrF (s : St) (a b c : ℕ) : Prop :=
  ∃ va vb, s.mem.get (s.fp + a) = some va ∧ s.mem.get (s.fp + b) = some vb ∧
    s.mem.get (s.fp + c) = some (va * vb)

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

/-- What the program's table holds: the jump table's cells, written with their targets' powers. -/
def EnvOk (s : St) (E : Env) : Prop :=
  E.pows.Ok ∧ E.jtHi ≤ maxCells ∧ ∀ d e, E.jtLo ≤ d → d < E.jtHi → E.jt.get d = some e → s.mem.get d = some (ofK (g ^ e))

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
    obtain ⟨v, h1, h2⟩ := h.h k hk
    exact ⟨v, h1.mono hle hfp, fun x hx ↦ written_le hle (h2 x hx)⟩
  r r hr := by
    obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := h.r r hr
    exact ⟨vq, xlo, xhi, h1.mono hle hfp, h2.mono hle hfp, h3.mono hle hfp,
      fun j a b x hx ↦ written_le hle (h4 j a b x hx)⟩
  lt p hp := by
    obtain ⟨a, b, h1, h2, h3⟩ := h.lt p hp
    exact ⟨a, b, h1.mono hle hfp, h2.mono hle hfp, h3⟩
  pr p hp := by
    obtain ⟨a, b, h1, h2, h3⟩ := h.pr p hp
    exact ⟨a, b, by rw [hfp]; exact hle.get _ _ h1, by rw [hfp]; exact hle.get _ _ h2,
      by rw [hfp]; exact hle.get _ _ h3⟩

omit hfp in
theorem EnvOk.mono {E : Env} (h : EnvOk s E) : EnvOk s' E :=
  ⟨h.1, h.2.1, fun d e h1 h2 h3 ↦ hle.get _ _ (h.2.2 d e h1 h2 h3)⟩

end mono

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
    split at hh
    · rename_i t ht
      obtain ⟨xp, xq, hp, hq, hlt⟩ := hA.lt _ hm
      obtain ⟨y, hy, hle⟩ := Idx.sle_sound hh hb
      obtain rfl := hy.unique (Idx.shift_val hq t)
      exact ⟨xp + t, Idx.off_val ht hp, by omega⟩
    · simp at hh

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
    fun j hj1 hj2 x hx ↦ h4 (j - r.d / r.S) (by omega) (by omega) x ?_⟩
  have e1 : r.S * (j - r.d / r.S) = r.S * j - r.S * (r.d / r.S) := Nat.mul_sub _ _ _
  have e2 : r.S * (r.d / r.S) ≤ r.S * j := Nat.mul_le_mul_left _ (by omega)
  have e3 : r.S * (r.d / r.S) ≤ r.d := Nat.mul_div_le r.d r.S
  have : r.S * (j - r.d / r.S) + r.d = r.S * j + (r.d - r.S * (r.d / r.S)) := by omega
  rw [this]
  exact hx

theorem inRng1_sound {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} (hr : RW s r)
    (h : (match r.idxOf k with
      | some i => A.le r.lo i && A.ltI i r.hi
      | none => false) = true) {vk : E} (hk : MonoVal s k vk) {x : ℕ} (hx : Names vk x) :
    s.mem.written x = true := by
  split at h
  · rename_i i hi
    simp only [Bool.and_eq_true] at h
    obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := hr
    obtain ⟨xi, hxi, hlt⟩ := Abs.ltI_sound hA h.2 h3
    obtain ⟨xlo', hlo', hle⟩ := Abs.le_sound hA h.1 hxi
    obtain rfl := h2.unique hlo'
    rw [Rng.idxOf_sound hi hk h1 hxi] at hx
    exact h4 xi hle hlt x hx
  · simp at h

theorem Abs.inRng_sound {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} (hr : RW s r)
    (h : A.inRng k r = true) {vk : E} (hk : MonoVal s k vk) {x : ℕ} (hx : Names vk x) :
    s.mem.written x = true := by
  unfold Abs.inRng at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact inRng1_sound hA hr h hk hx
  · simp only [Bool.and_eq_true] at h
    exact inRng1_sound hA hr.down h.2 hk hx

/-- **What the walk knows written is**, whatever word names it. -/
theorem Abs.covered_sound {s : St} {A : Abs} (hA : Holds s A) (hwf : s.mem.WF)
    (hu : s.mem.used ≤ maxCells) {k : Mono}
    (h : A.covered k = true) {vk : E} (hk : MonoVal s k vk) {x : ℕ} (hx : Names vk x) :
    s.mem.written x = true := by
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
    rw [hv] at hx
    have hx' : g ^ (s.fp + kk) = g ^ x := by have := hx.1; simpa using this
    have := hx.2
    have hw' := hA.w kk (Option.isSome_iff_exists.mp h |>.elim fun u hu ↦ by cases u; exact hu)
    obtain ⟨u, hu'⟩ := Mem.get_of_written hw'
    have hlt := hwf.get_lt hu'
    rw [gpow_inj (by unfold maxCells at hu; omega) (by unfold maxCells at this; omega) hx'] at hw'
    exact hw'
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨k', hm, hb⟩ := List.any_eq_true.mp h
      obtain rfl := Mono.beq_eq hb
      obtain ⟨v, h1, h2⟩ := hA.h _ hm
      obtain rfl := h1.unique hk
      exact h2 x hx
    · obtain ⟨r, hm, hb⟩ := List.any_eq_true.mp h
      exact Abs.inRng_sound hA (hA.r r hm) hb hk hx

end

end LeanVM.Guest.Mode
