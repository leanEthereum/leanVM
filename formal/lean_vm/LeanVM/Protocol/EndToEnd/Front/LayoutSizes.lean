/-
  LeanVM.Protocol.EndToEnd.Front.LayoutSizes

  The announced sizes: what the verifier program's first step returns is the verifier's layout at
  sizes admissible for the program, read off eight announced scalars.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Basic
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance
public import LeanVM.Protocol.Verifier.Phases

/-!
# The announced sizes

Step 1 of the verifier program (`readAnnouncedSizes`, `crates/verifier/src/lib.rs:219-233` at leanVM
`40f877dc`) reads eight scalars, the memory's log-size, the six
tables' row counts and the WHIR rate, checks them, and builds the layout. For the program's bytecode
(`bytecodeWords prog`):

* `readSizes_ret`: what the program checks, on the history it read;
* `readSizes_ret_sizes`: it returns `(layout, ρ)` only after reading `announce s ρ` for sizes
  `s` with `Sizes.Admissible prog s` (the Rust verifier's checks,
  `crates/verifier/src/layout.rs:381-395` and `crates/verifier/src/lib.rs:213-218`; until
  `127510d1` they were `read_public`'s, `crates/lean_vm/src/cpu/mod.rs:157-176` at `a386121f`)
  and a rate with `validRate ρ`, and `layout = verifierLayout prog s`; so its `stackLog` is
  `leanIsaμ prog s` (`stackLog_verifierLayout`) and its placements are the instance's.

The `require`s of `readAnnouncedSizes` are exactly `Sizes.Admissible` and `validRate`:
`buildLayout`'s windows are the memory and row checks (`buildLayout_eq`), and the stacked-size
window
`[15, 28]` is the cap `leanIsaμ prog s ≤ 28` (the floor holds by construction).
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa

@[expose] public section

/-- A sequence that returns at once: both parts return. -/
theorem bind_eq_ret {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β} (h :
    p.bind f = .ret b) :
    ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [VerifierProgram.bind]

/-- `readN n` returns along exactly the histories of `n` reads, with the values read. -/
theorem after_readN_ret : ∀ (n : ℕ) {l : List Ev} {xs : List E},
    (VerifierProgram.readScalars n).after l = some (.ret xs) → l = xs.map Ev.read ∧ xs.length = n
  | 0, l, xs, h => by
    cases l with
    | nil => simp [VerifierProgram.readScalars, VerifierProgram.after] at h; subst h; simp
    | cons e l => cases e <;> simp [VerifierProgram.readScalars, VerifierProgram.after] at h
  | n + 1, l, xs, h => by
    cases l with
    | nil => simp [VerifierProgram.readScalars, VerifierProgram.readScalar, VerifierProgram.after, VerifierProgram.bind] at h
    | cons e l =>
      cases e <;> simp [VerifierProgram.readScalars, VerifierProgram.readScalar,
          VerifierProgram.after, VerifierProgram.bind] at h
      rename_i x
      rcases VerifierProgram.after_bind_cases _ h with ⟨q, hq, hr⟩ | ⟨ys, l₁, l₂, rfl, h1, h2, h3⟩
      · obtain ⟨ys, rfl, hys⟩ := bind_eq_ret hr.symm
        simp only [VerifierProgram.ret.injEq] at hys
        subst hys
        obtain ⟨rfl, hlen⟩ := after_readN_ret n hq
        simp [hlen]
      · cases l₂ with
        | nil => exact absurd rfl h2
        | cons e l₂ => cases e <;> simp [VerifierProgram.after] at h3

/-- A word is the word of its integer value. -/
theorem ofBits_kToNat (k : K) : K.ofBits (kToNat k) = k := by
  cases k; simp [K.ofBits, kToNat, BF64.ofBitVec]

/-- A scalar with a zero upper limb is `eOfNat` of its low limb's value. -/
theorem eq_eOfNat_of_limbs {x : E} (h1 : x.limb 1 = 0) : x = eOfNat (kToNat (x.limb 0)) := by
  rw [eOfNat, ofBits_kToNat]
  exact E.ext fun i ↦ by fin_cases i <;> simp [h1]

/-- The eight scalars that announce the sizes `s` and the rate `ρ`, as the verifier reads them. -/
def announce (s : Sizes) (ρ : ℕ) : List E := (s.logMem :: List.ofFn s.rows ++ [ρ]).map eOfNat

/-- A program with no event: a return or a rejection. -/
def IsPure {α : Type} (p : VerifierProgram α) : Prop := (∃ a, p = .ret a) ∨ p = .fail

/-- Sequencing programs with no event. -/
theorem IsPure.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : IsPure p)
    (hf : ∀ a, IsPure (f a)) : IsPure (p.bind f) := by
  rcases hp with ⟨a, rfl⟩ | rfl
  · exact hf a
  · exact .inr rfl

/-- `require` has no event. -/
theorem isPure_require (c : Prop) [Decidable c] : IsPure (VerifierProgram.require c) := by
  unfold VerifierProgram.require; split_ifs
  · exact .inl ⟨_, rfl⟩
  · exact .inr rfl

/-- `liftOption` has no event. -/
theorem isPure_liftOption {α : Type} (o : Option α) : IsPure (Verifier.liftOption o) := by
  cases o
  · exact .inr rfl
  · exact .inl ⟨_, rfl⟩

/-- A program with no event reads no event. -/
theorem IsPure.after_cons {α : Type} {p : VerifierProgram α} (hp : IsPure p) (e : Ev) (l :
    List Ev) :
    p.after (e :: l) = none := by
  rcases hp with ⟨a, rfl⟩ | rfl <;> cases e <;> rfl

/-- A rejection sequenced is a rejection. -/
@[simp] theorem fail_bind' {α β : Type} (f : α → VerifierProgram β) :
    (VerifierProgram.fail : VerifierProgram α).bind f = .fail := rfl

/-- **What `readAnnouncedSizes` returns**: after eight reads whose upper limb is zero, the rate in
`[1, 4]` from the last, the layout `buildLayout` gives from the first seven, and a stacked size in
the window. -/
theorem readSizes_ret {bytecode : List K} {l : List Ev} {a : Verifier.Layout × ℕ}
    (h : (readAnnouncedSizes bytecode).after l = some (.ret a)) :
    ∃ xs : List E, l = xs.map Ev.read ∧ xs.length = 8 ∧
      (xs.all fun value ↦ value.limb 1 = 0) ∧
      1 ≤ a.2 ∧ a.2 ≤ 4 ∧ a.2 = kToNat ((xs.getLastD 0).limb 0) ∧
      buildLayout bytecode (kToNat ((xs.headD 0).limb 0))
        (((xs.drop 1).take 6).map fun value ↦ kToNat (value.limb 0)) = some a.1 ∧
      Whir.minLogStack ≤ a.1.stackLog ∧ a.1.stackLog ≤ Whir.maxLogStack := by
  rw [readAnnouncedSizes_eq] at h
  simp only [VerifierProgram.bind_eq] at h
  rcases VerifierProgram.after_bind_cases _ h with ⟨q, hq, hr⟩ | ⟨xs, l₁, l₂, rfl, h1, h2, h3⟩
  · obtain ⟨xs, rfl, hk⟩ := bind_eq_ret hr.symm
    obtain ⟨rfl, hlen⟩ := after_readN_ret _ hq
    have ho : sizesOf bytecode xs = some a := by
      cases ho : sizesOf bytecode xs with
      | none => rw [ho] at hk; cases hk
      | some y => rw [ho] at hk; cases hk; rfl
    have s := sizesOf_spec ho
    exact ⟨xs, rfl, by simpa [tables] using hlen, s.limbs, s.rate_ge, s.rate_le, s.rate, s.layout,
      s.stack_ge, s.stack_le⟩
  · exfalso
    have hpure : IsPure ((fun announced : List E ↦ Verifier.liftOption (sizesOf bytecode announced)) xs) :=
      isPure_liftOption _
    cases l₂ with
    | nil => exact h2 rfl
    | cons e l₂ => rw [hpure.after_cons] at h3; cases h3

/-- A layout is built only for a memory of at least `2` cells. -/
theorem logMem_of_buildLayout {bytecode : List K} {lm : ℕ} {tl : List ℕ} {layout : Verifier.Layout}
    (h : buildLayout bytecode lm tl = some layout) : 1 ≤ lm := by
  unfold buildLayout at h
  split at h
  · cases h
  · split_ifs at h with hc
    exact hc.2.1

/-- **The announced sizes are the instance's**: for the program's bytecode, `readAnnouncedSizes`
returns
`(layout, ρ)` only after reading the announcement of sizes `s` admissible for the program and a
valid rate `ρ`, and the layout is then the verifier's layout at `s`. -/
theorem readSizes_ret_sizes (prog : LeanIsaProgram) {l : List Ev} {a : Verifier.Layout × ℕ}
    (h : (readAnnouncedSizes (bytecodeWords prog)).after l = some (.ret a)) :
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
      have hμ : (verifierLayout prog s).stackLog ≤ Whir.maxLogStack := hb' ▸ hμ2
      rw [stackLog_verifierLayout] at hμ
      refine ⟨s, ⟨hok.1, hok.2.1, hok.2.2, hμ⟩, ⟨hρ1, hρ2⟩, hb', ?_⟩
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at hall
      simp only [announce, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.ofFn_succ, List.ofFn_zero]
      rw [hρ]
      simp only [List.getLastD_cons, List.getLastD_nil]
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hall
      simp only [List.cons.injEq, Ev.read.injEq, and_true]
      exact ⟨eq_eOfNat_of_limbs a0, eq_eOfNat_of_limbs a1, eq_eOfNat_of_limbs a2,
        eq_eOfNat_of_limbs a3, eq_eOfNat_of_limbs a4, eq_eOfNat_of_limbs a5,
        eq_eOfNat_of_limbs a6, eq_eOfNat_of_limbs a7⟩

end
end LeanVM.Protocol.EndToEnd.Front
