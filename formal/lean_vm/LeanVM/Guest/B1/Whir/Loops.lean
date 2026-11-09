/-
  LeanVM.Guest.B1.Whir.Loops

  `mul_range` loop helpers whose body is flat (atoms and calls), soundly: every iteration's
  body holds; and the templates' g-power steps.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# Flat loops

A `mul_range` helper (`__loopN`, parameters `x, N, …`) whose body is a flat block `A` (atoms,
calls), then `callIf (x·g + N) self [x·g, N, …]` and `ret []`: `loop_sound_flat`, from its call
relation at `g^k`, the loop ends at some `g^m`, `m > k`, and the body's meaning holds at every
`g^j`, `k ≤ j < m` (the calls inside interpreted by the program's relation, a call at a finite
depth being one of it). `loop_guarded`: entered from `1` at a guard `1 + g^n`, `0 < n < ord g`,
it ran exactly `n` iterations.

`osLoopTail_split`: the templates' loop tail is five atoms, then the conditional call and the
`ret`; `osLoopTailA_val`: the atoms compute `x·g` and the guard. `osPowSteps_val`: the
square-and-multiply steps compute `x^e`, `e` the digits' value.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## Monotone in the call relation -/

theorem stmtOk_mono {C C' : CallRel} (hC : CallRel.Le C C') {σ : Val} :
    ∀ s : Stmt, StmtOk C rd σ s → StmtOk C' rd σ s
  | .atom _, h => h
  | .call _ _ _, h => hC _ _ _ h
  | .callIf _ _ _, h => ⟨h.1, fun hc ↦ hC _ _ _ (h.2 hc)⟩
  | .ite _ _ _, h | .match_ _ _, h | .dispatch _ _ _ _, h | .ret _, h => h

theorem allOk_mono {C C' : CallRel} (hC : CallRel.Le C C') {σ : Val} {ss : List Stmt}
    (h : AllOk C rd σ ss) : AllOk C' rd σ ss := fun s hs ↦ stmtOk_mono hC s (h s hs)

/-! ## Loops -/

/-- **A flat loop, soundly**: from the loop's relation at `g^k`, the loop ends at `g^m`, `m > k`,
first reached there, and the body's meaning `B` holds at every `g^j`, `k ≤ j < m`. -/
theorem loop_sound_flat {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {A : List Stmt} (hflat : A.all Stmt.flat = true) {c : ℕ} {args : List V}
    (hb : fn.body = A ++ [.callIf (.n c) f args, .ret []]) {N : E} {rest : List E}
    {B : E → Prop}
    (hstep : ∀ (σ : Val) (x : E), fn.params.map σ = x :: N :: rest →
      AllOk (coreProgram.Rel rd) rd σ A →
        B x ∧ σ (.n c) = x * gen + N ∧ args.map σ = x * gen :: N :: rest) :
    ∀ k, coreProgram.Rel rd f (gen ^ k :: N :: rest) [] →
      ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  intro k ⟨d, hd⟩
  induction d generalizing k with
  | zero => exact hd.elim
  | succ d ih =>
    rw [relN_succ_iff hf, hb] at hd
    obtain ⟨σ, hp, hd⟩ := hd
    rw [holdsList_append, holdsList_flat _ hflat] at hd
    obtain ⟨hA, hrest⟩ := hd
    simp only [Stmt.HoldsList, Stmt.Holds] at hrest
    obtain ⟨-, hcall, -⟩ := hrest
    obtain ⟨hB, hc, hargs⟩ := hstep σ _ hp (allOk_mono (relN_le_rel coreProgram d) hA)
    rw [hc] at hcall
    by_cases h0 : gen ^ k * gen + N = 0
    · refine ⟨k + 1, by omega, (gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 ↦ by omega,
        fun j h1 h2 ↦ ?_⟩
      rwa [show j = k by omega]
    · have := hcall h0
      rw [hargs, gen_pow_mul_gen] at this
      obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
      refine ⟨m, by omega, hN, fun j h1 h2 ↦ ?_, fun j h1 h2 ↦ ?_⟩
      · rcases Nat.lt_or_ge (k + 1) j with h | h
        · exact hfirst j h h2
        · rw [show j = k + 1 by omega]
          intro he
          exact h0 ((gen_pow_add_eq_zero_iff k).mpr he.symm)
      · rcases Nat.lt_or_ge k j with h | h
        · exact hall j (by omega) h2
        · rwa [show j = k by omega]

/-- **A loop entered from `1` behind its guard `1 + g^n`** (`0 < n < ord g`) ran its body at
every `g^j`, `j < n`. -/
theorem loop_guarded {f : String} {N : E} {rest : List E} {B : E → Prop} {n : ℕ} (hn0 : 0 < n)
    (hn : n < ordG) (hN : N = gen ^ n)
    (hloop : ∀ k, coreProgram.Rel rd f (gen ^ k :: N :: rest) [] →
      ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        ∀ j, k ≤ j → j < m → B (gen ^ j))
    (hg : 1 + N ≠ 0 → coreProgram.Rel rd f (1 :: N :: rest) []) :
    ∀ j < n, B (gen ^ j) := by
  have hne : 1 + N ≠ 0 := by
    intro h
    have h1 : N = 1 := (e_add_eq_zero_iff.mp h).symm
    rw [hN, ← pow_zero gen] at h1
    have := gen_pow_inj hn ordG_pos h1
    omega
  have := hg hne
  rw [← pow_zero gen] at this
  obtain ⟨m, hm, hNm, hfirst, hall⟩ := hloop 0 this
  have hmn : m = n := by
    by_contra hne'
    rcases Nat.lt_or_ge m n with h | h
    · have hmo : m < ordG := by omega
      exact absurd (gen_pow_inj hmo hn (hNm.symm.trans hN)) hne'
    · exact hfirst n hn0 (by omega) hN.symm
  intro j hj
  exact hall j (Nat.zero_le j) (by omega)

/-! ## The templates' loop tail -/

/-- The loop tail's atoms. -/
def osLoopTailA (k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (word 2 0 0)), .atom (.mul (.n (k + 1)) (.n 0) (.n k)),
    .atom (.add (.n (k + 2)) (.n (k + 1)) (.n 1)), .atom (.const (.n (k + 3)) (word 2 0 0)),
    .atom (.mul (.n (k + 4)) (.n 0) (.n (k + 3)))]

theorem osLoopTail_split (name : String) (n k : ℕ) :
    osLoopTail name n k = osLoopTailA k ++
      [.callIf (.n (k + 2)) name (.n (k + 4) :: (List.range (n - 1)).map fun i ↦ .n (i + 1)),
        .ret []] := rfl

theorem osLoopTailA_val {C : CallRel} {σ : Val} {k : ℕ} (h : AllOk C rd σ (osLoopTailA k)) :
    σ (.n (k + 2)) = σ (.n 0) * gen + σ (.n 1) ∧ σ (.n (k + 4)) = σ (.n 0) * gen := by
  simp only [osLoopTailA, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_⟩
  · rw [h2, h1, h0, word_gen]
  · rw [h4, h3, word_gen]

/-! ## Square and multiply -/

/-- The value of digits `ds` read after a leading `acc`. -/
def digitsVal : List Bool → ℕ → ℕ
  | [], acc => acc
  | d :: ds, acc => digitsVal ds (2 * acc + if d then 1 else 0)

/-- **The square-and-multiply steps** compute `x^(digitsVal ds a)` from `acc = x^a`. -/
theorem osPowSteps_val {C : CallRel} {σ : Val} (x : ℕ) :
    ∀ (ds : List Bool) (acc k a : ℕ), σ (.n acc) = σ (.n x) ^ a →
      AllOk C rd σ (osPowSteps x ds acc k).1 →
        σ (.n (osPowSteps x ds acc k).2) = σ (.n x) ^ digitsVal ds a
  | [], acc, k, a, ha, _ => ha
  | d :: ds, acc, k, a, ha, h => by
    cases d with
    | true =>
      simp only [osPowSteps, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds] at h ⊢
      obtain ⟨h0, h1, h⟩ := h
      refine osPowSteps_val x ds (k + 1) (k + 2) (2 * a + 1) ?_ h
      rw [h1, h0, ha]; ring
    | false =>
      simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds] at h ⊢
      obtain ⟨h0, h⟩ := h
      refine osPowSteps_val x ds k (k + 1) (2 * a + 0) ?_ h
      rw [h0, ha]; ring

end
end LeanVM.Guest.B1.Whir
