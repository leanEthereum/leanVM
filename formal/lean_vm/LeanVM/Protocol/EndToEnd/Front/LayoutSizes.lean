/-
  LeanVM.Protocol.EndToEnd.Front.LayoutSizes

  The announced sizes: what the verifier program's first step returns is the verifier's layout at
  sizes admissible for the program, read off eight announced scalars.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Basic
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance

/-!
# The announced sizes

Step 1 of the verifier program (`readSizes`, `verifier.py:1364-1372` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) reads eight scalars, the memory's log-size, the six
tables' row counts and the WHIR rate, checks them, and builds the layout. For the program's bytecode
(`bytecodeWords prog`):

* `readSizes_ret`: what the program checks, on the history it read;
* `readSizes_ret_sizes`: it returns `(layout, ρ)` only after reading `announce s ρ` for sizes
  `s` with `Sizes.Admissible prog s` (the Rust verifier's checks,
  `crates/verifier/src/layout.rs:381-395` and `crates/verifier/src/lib.rs:215-220`; until
  `127510d1` they were `read_public`'s, `crates/lean_vm/src/cpu/mod.rs:157-176` at `a386121f`)
  and a rate with `validRate ρ`, and `layout = verifierLayout prog s`; so its `stackLog` is
  `leanIsaμ prog s` (`stackLog_verifierLayout`) and its placements are the instance's.

The `require`s of `readSizes` are exactly `Sizes.Admissible` and `validRate`: `buildLayout`'s
windows are the memory and row checks (`buildLayout_eq`), and the stacked-size window
`[15, 28]` is the cap `leanIsaμ prog s ≤ 28` (the floor holds by construction).
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa

@[expose] public section

/-- A sequence that returns at once: both parts return. -/
theorem bind_eq_ret {α β : Type} {p : Prog α} {f : α → Prog β} {b : β} (h : p.bind f = .ret b) :
    ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [Prog.bind]

/-- `readN n` returns along exactly the histories of `n` reads, with the values read. -/
theorem after_readN_ret : ∀ (n : ℕ) {l : List Ev} {xs : List E},
    (Prog.readN n).after l = some (.ret xs) → l = xs.map Ev.read ∧ xs.length = n
  | 0, l, xs, h => by
    cases l with
    | nil => simp [Prog.readN, Prog.after] at h; subst h; simp
    | cons e l => cases e <;> simp [Prog.readN, Prog.after] at h
  | n + 1, l, xs, h => by
    cases l with
    | nil => simp [Prog.readN, Prog.readE, Prog.after, Prog.bind] at h
    | cons e l =>
      cases e <;> simp [Prog.readN, Prog.readE, Prog.after, Prog.bind] at h
      rename_i x
      rcases Prog.after_bind_cases _ h with ⟨q, hq, hr⟩ | ⟨ys, l₁, l₂, rfl, h1, h2, h3⟩
      · obtain ⟨ys, rfl, hys⟩ := bind_eq_ret hr.symm
        simp only [Prog.ret.injEq] at hys
        subst hys
        obtain ⟨rfl, hlen⟩ := after_readN_ret n hq
        simp [hlen]
      · cases l₂ with
        | nil => exact absurd rfl h2
        | cons e l₂ => cases e <;> simp [Prog.after] at h3

/-- A word is the word of its integer value. -/
theorem ofBits_kToNat (k : K) : K.ofBits (kToNat k) = k := by
  cases k; simp [K.ofBits, kToNat, BF64.ofBitVec]

/-- A scalar with zero upper limbs is the Python's `E(n)` of its low limb's value. -/
theorem eq_eOfNat_of_limbs {x : E} (h1 : x.limb 1 = 0) (h2 : x.limb 2 = 0) :
    x = eOfNat (kToNat (x.limb 0)) := by
  rw [eOfNat, ofBits_kToNat]
  exact E.ext fun i ↦ by fin_cases i <;> simp [h1, h2]

/-- The eight scalars that announce the sizes `s` and the rate `ρ`, as the Python reads them. -/
def announce (s : Sizes) (ρ : ℕ) : List E := (s.logMem :: List.ofFn s.rows ++ [ρ]).map eOfNat

/-- A program with no event returns only at the empty history. -/
theorem pure_after_ret {α : Type} {p : Prog α} {l : List Ev} {a : α}
    (hp : ∀ b, p ≠ .ret b → p = .fail) (h : p.after l = some (.ret a)) : l = [] ∧ p = .ret a := by
  cases l with
  | nil => simp [Prog.after] at h; exact ⟨rfl, h⟩
  | cons e l =>
    by_cases hr : ∃ b, p = .ret b
    · obtain ⟨b, rfl⟩ := hr; cases e <;> simp [Prog.after] at h
    · simp only [not_exists] at hr
      rw [hp _ (hr a)] at h
      cases e <;> simp [Prog.after] at h

/-- A program with no event: a return or a rejection. -/
def IsPure {α : Type} (p : Prog α) : Prop := (∃ a, p = .ret a) ∨ p = .fail

/-- Sequencing programs with no event. -/
theorem IsPure.bind {α β : Type} {p : Prog α} {f : α → Prog β} (hp : IsPure p)
    (hf : ∀ a, IsPure (f a)) : IsPure (p.bind f) := by
  rcases hp with ⟨a, rfl⟩ | rfl
  · exact hf a
  · exact .inr rfl

/-- `require` has no event. -/
theorem isPure_require (c : Prop) [Decidable c] : IsPure (Prog.require c) := by
  unfold Prog.require; split_ifs
  · exact .inl ⟨_, rfl⟩
  · exact .inr rfl

/-- `liftOption` has no event. -/
theorem isPure_liftOption {α : Type} (o : Option α) : IsPure (Verifier.liftOption o) := by
  cases o
  · exact .inr rfl
  · exact .inl ⟨_, rfl⟩

/-- A program with no event reads no event. -/
theorem IsPure.after_cons {α : Type} {p : Prog α} (hp : IsPure p) (e : Ev) (l : List Ev) :
    p.after (e :: l) = none := by
  rcases hp with ⟨a, rfl⟩ | rfl <;> cases e <;> rfl

/-- A rejection sequenced is a rejection. -/
@[simp] theorem fail_bind' {α β : Type} (f : α → Prog β) :
    (Prog.fail : Prog α).bind f = .fail := rfl

/-- **What `readSizes` returns**: after eight reads whose upper limbs are zero, the rate in
`[1, 4]` from the last, the layout `buildLayout` gives from the first seven, and a stacked size in
the window. -/
theorem readSizes_ret {bytecode : List K} {l : List Ev} {a : Verifier.Layout × ℕ}
    (h : (readSizes bytecode).after l = some (.ret a)) :
    ∃ xs : List E, l = xs.map Ev.read ∧ xs.length = 8 ∧
      (xs.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0) ∧
      1 ≤ a.2 ∧ a.2 ≤ 4 ∧ a.2 = kToNat ((xs.getLastD 0).limb 0) ∧
      buildLayout bytecode (kToNat ((xs.headD 0).limb 0))
        (((xs.drop 1).take 6).map fun value ↦ kToNat (value.limb 0)) = some a.1 ∧
      minStackedLog ≤ a.1.stackLog ∧ a.1.stackLog ≤ maxStackedLog := by
  unfold readSizes at h
  simp only [Prog.bind_eq] at h
  rcases Prog.after_bind_cases _ h with ⟨q, hq, hr⟩ | ⟨xs, l₁, l₂, rfl, h1, h2, h3⟩
  · obtain ⟨xs, rfl, hk⟩ := bind_eq_ret hr.symm
    obtain ⟨rfl, hlen⟩ := after_readN_ret _ hq
    refine ⟨xs, rfl, by simpa [tables] using hlen, ?_⟩
    have ht : tables.length = 6 := rfl
    rw [ht] at hk
    by_cases c1 : (xs.all fun value ↦ decide (value.limb 1 = 0 ∧ value.limb 2 = 0)) = true
    · by_cases c2 : 1 ≤ kToNat ((xs.getLastD 0).limb 0) ∧ kToNat ((xs.getLastD 0).limb 0) ≤ 4
      · cases hb : buildLayout bytecode (kToNat ((xs.headD 0).limb 0))
            (((xs.drop 1).take 6).map fun value ↦ kToNat (value.limb 0)) with
        | none =>
          simp only [Prog.require, c1, c2, hb, Verifier.liftOption, ↓reduceIte, Prog.ret_bind,
            fail_bind'] at hk
          cases hk
        | some layout =>
          by_cases c3 : minStackedLog ≤ layout.stackLog ∧ layout.stackLog ≤ maxStackedLog
          · simp only [Prog.require, c1, c2, hb, c3, Verifier.liftOption, ↓reduceIte, and_self,
              Prog.ret_bind, Prog.pure_eq, Prog.ret.injEq] at hk
            subst hk
            exact ⟨c1, c2.1, c2.2, rfl, rfl, c3⟩
          · simp only [Prog.require, c1, c2, hb, c3, Verifier.liftOption, ↓reduceIte, Prog.ret_bind,
              fail_bind'] at hk
            cases hk
      · simp only [Prog.require, c1, c2, ↓reduceIte, Prog.ret_bind, fail_bind'] at hk
        cases hk
    · simp only [Prog.require, c1, ↓reduceIte, fail_bind', Bool.false_eq_true] at hk
      cases hk
  · exfalso
    have hpure : IsPure ((fun announced : List E ↦
        (Prog.require ((announced.all fun value ↦ decide (value.limb 1 = 0 ∧ value.limb 2 = 0)) =
          true)).bind fun _ ↦
        (Prog.require (1 ≤ kToNat ((announced.getLastD 0).limb 0) ∧
          kToNat ((announced.getLastD 0).limb 0) ≤ 4)).bind fun _ ↦
        (Verifier.liftOption (buildLayout bytecode (kToNat ((announced.headD 0).limb 0))
          (((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)))).bind
            fun layout ↦
          (Prog.require (minStackedLog ≤ layout.stackLog ∧ layout.stackLog ≤ maxStackedLog)).bind
            fun _ ↦ (pure (layout, kToNat ((announced.getLastD 0).limb 0)) : Prog _)) xs) :=
      (isPure_require _).bind fun _ ↦ (isPure_require _).bind fun _ ↦
        (isPure_liftOption _).bind fun _ ↦ (isPure_require _).bind fun _ ↦ .inl ⟨_, rfl⟩
    cases l₂ with
    | nil => exact h2 rfl
    | cons e l₂ => rw [hpure.after_cons] at h3; cases h3

/-- A layout is built only for a memory of at least `2^16` cells. -/
theorem logMem_of_buildLayout {bytecode : List K} {lm : ℕ} {tl : List ℕ} {layout : Verifier.Layout}
    (h : buildLayout bytecode lm tl = some layout) : 16 ≤ lm := by
  unfold buildLayout at h
  split at h
  · cases h
  · split_ifs at h with hc
    exact hc.2.1

/-- **The announced sizes are the instance's**: for the program's bytecode, `readSizes` returns
`(layout, ρ)` only after reading the announcement of sizes `s` admissible for the program and a
valid rate `ρ`, and the layout is then the verifier's layout at `s`. -/
theorem readSizes_ret_sizes (prog : Program) {l : List Ev} {a : Verifier.Layout × ℕ}
    (h : (readSizes (bytecodeWords prog)).after l = some (.ret a)) :
    ∃ s : Sizes, Sizes.Admissible prog s ∧ validRate a.2 ∧ a.1 = verifierLayout prog s ∧
      l = (announce s a.2).map Ev.read := by
  obtain ⟨xs, rfl, hlen, hall, hρ1, hρ2, hρ, hb, hμ1, hμ2⟩ := readSizes_ret h
  match xs, hlen with
  | [x0, x1, x2, x3, x4, x5, x6, x7], _ =>
    have hlm := logMem_of_buildLayout hb
    let s : Sizes := ⟨kToNat (x0.limb 0), by simp at hlm; omega,
      ![kToNat (x1.limb 0), kToNat (x2.limb 0), kToNat (x3.limb 0), kToNat (x4.limb 0),
        kToNat (x5.limb 0), kToNat (x6.limb 0)]⟩
    have htl : tableRows s = ((([x0, x1, x2, x3, x4, x5, x6, x7].drop 1).take 6).map
        fun value ↦ kToNat (value.limb 0)) := by
      simp [tableRows, s, List.ofFn_succ]
    have hb' := buildLayout_eq prog s
    rw [show s.logMem = kToNat (([x0, x1, x2, x3, x4, x5, x6, x7].headD 0).limb 0) from rfl, htl,
      hb] at hb'
    split_ifs at hb' with hok
    · simp only [Option.some.injEq] at hb'
      have hμ : (verifierLayout prog s).stackLog ≤ maxStackedLog := hb' ▸ hμ2
      rw [stackLog_verifierLayout] at hμ
      refine ⟨s, ⟨hok.1, hok.2.1, hok.2.2, hμ⟩, ⟨hρ1, hρ2⟩, hb', ?_⟩
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at hall
      simp only [announce, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.ofFn_succ, List.ofFn_zero]
      rw [hρ]
      simp only [List.getLastD_cons, List.getLastD_nil]
      obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, a7, b7⟩ := hall
      simp only [List.cons.injEq, Ev.read.injEq, and_true]
      exact ⟨eq_eOfNat_of_limbs a0 b0, eq_eOfNat_of_limbs a1 b1, eq_eOfNat_of_limbs a2 b2,
        eq_eOfNat_of_limbs a3 b3, eq_eOfNat_of_limbs a4 b4, eq_eOfNat_of_limbs a5 b5,
        eq_eOfNat_of_limbs a6 b6, eq_eOfNat_of_limbs a7 b7⟩

end
end LeanVM.Protocol.EndToEnd.Front
