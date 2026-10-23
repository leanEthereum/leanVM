import LeanVM.Protocol.Compile.SpecRules.Leaves
import LeanVM.Protocol.Compile.SpecRules.Cert

/-!
# Specification calculus tests

A small verifier program: read a scalar `x`, sample `c`, check a three-bit proof of work, sample
`d`, and accept iff `c = x` or `d = x`. Its specification is assembled from the leaves and
`Spec.bind` alone: doom is "`c ≠ x`", then "`c ≠ x ∧ d ≠ x`"; the first group escapes with
probability `|E|⁻¹`, the second too, discounted by the proof of work. The doom certificate it
gives has every discounted escape bound at most `|E|⁻¹ = 2^-192`, and its doom holds at the
start and after the prover's scalar.

Then the load-bearing checks:

* the follower's allowance is charged where a sub-program returns in doom (`retDoom`): a proof of
  work followed by a lead of `1` admits no specification with `εmax = 0`;
* the counterexample to the earlier rule, which charged the follower's lead on every return
  within a group: `p` reads a scalar and returns a challenge `x` (`Post`: `x ≠ 0`), `f x` accepts
  iff `x = 0` (`Q`: never), with the follower's lead `1`. The earlier `bind` rule had no
  composite with `εmax = |E|⁻¹`; `Spec.bind` gives one.
-/

namespace LeanVMTests.Protocol.Compile.Spec

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Prog

noncomputable section

/-- The escape bound of one challenge. -/
def ε0 : ENNReal := (Fintype.card E : ENNReal)⁻¹

theorem ε0_eq : ε0 = (2 ^ 192 : ENNReal)⁻¹ := by
  unfold ε0; rw [card_E]; norm_num

/-- At most one challenge is bad. -/
theorem le_ε0 {s : Finset E} (hs : ∀ a ∈ s, ∀ b ∈ s, a = b) :
    (Fintype.card E : ENNReal)⁻¹ * (s.card : ENNReal) ≤ ε0 := by
  calc (Fintype.card E : ENNReal)⁻¹ * (s.card : ENNReal)
      ≤ (Fintype.card E : ENNReal)⁻¹ * 1 := by
        gcongr; exact_mod_cast Finset.card_le_one.2 hs
    _ = ε0 := mul_one _

/-! ## Statement locks -/

example {α β : Type} {p : Prog α} {f : α → Prog β} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {Q : β → List Ev → Prop} {εmax Lp Lf T : ENNReal}
    (S : Spec p Pre Post εmax Lp Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T) :
    Spec (p.bind f) Pre Q εmax Lp T :=
  S.bind F

example {Pre : List Ev → Prop} {Post : Unit → List Ev → Prop} {εmax T : ENNReal} (b : ℕ)
    (h : ∀ h₀, Pre h₀ → Post () (h₀ ++ [Ev.grind b])) (hT : (2 : ENNReal)⁻¹ ^ b * T ≤ εmax) :
    Spec (grindP b) Pre Post εmax 0 T :=
  Spec.grindP b h hT

open Classical in
example {Pre : List Ev → Prop} {Post : E → List Ev → Prop} {εmax T : ENNReal} (e : ENNReal)
    (h : ∀ h₀, Pre h₀ → (Fintype.card E : ENNReal)⁻¹ *
      ((Finset.univ.filter fun c ↦ ¬ Post c (h₀ ++ [Ev.sample c])).card : ENNReal) ≤ e) :
    Spec sampleE Pre Post εmax (e + T) T :=
  Spec.sampleE e h

example {α : Type} {p : Prog α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
    {εmax T e : ENNReal} (hnm : ∀ {h₀ l q}, p.Reach h₀ l → p.after l = some q → ¬ q.IsMove)
    (he : e < 1) (h : ∀ h₀, Pre h₀ → escRet Post h₀ [] p ≤ e) :
    Spec p Pre Post εmax (e + T) T :=
  Spec.ofNoMove hnm he h

example {P : Prog Bool} {εmax L : ENNReal}
    (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0)
    (hstart : S.D [] [] → S.V [] [] ≤ εmax) (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ grindBits h * S.toCert.ε h ≤ εmax ∧ S.toCert.D = S.D [] :=
  ⟨S.toCert_bound hstart h, S.toCert_D⟩

/-! ## A program and its certificate -/

open Classical in
/-- After `d`: accept iff `c = x ∨ d = x`. -/
def tailP (x c d : E) : Prog Bool := do
  Prog.require (c = x ∨ d = x)
  return true

/-- The second group: sample `d`. -/
def secondP (x c : E) : Prog Bool := do
  let d ← sampleE
  tailP x c d

/-- The proof of work, then the second group. -/
def afterP (x c : E) : Prog Bool := do
  grindP 3
  secondP x c

/-- The first group: sample `c`. -/
def firstP (x : E) : Prog Bool := do
  let c ← sampleE
  afterP x c

/-- Read `x`, sample `c`, a three-bit proof of work, sample `d`; accept iff `c = x ∨ d = x`. -/
def prog : Prog Bool := do
  let x ← readE
  firstP x

/-- The verdict: rejection. -/
abbrev Rej (b : Bool) (_ : List Ev) : Prop := b = false

/-- After `d`: the program rejects. -/
def tail (x c d : E) : Spec (tailP x c d) (fun _ ↦ c ≠ x ∧ d ≠ x) Rej ε0 0 0 :=
  (Spec.require (Post := fun _ _ ↦ False) fun _ ⟨h1, h2⟩ h ↦ h.elim (fun e ↦ h1 e)
      (fun e ↦ h2 e)).bind'
    fun _ ↦ (Spec.ret true).mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The second group: `d` misses `x`. -/
def second (x c : E) : Spec (secondP x c) (fun _ ↦ c ≠ x) Rej ε0 ε0 0 :=
  ((Spec.sampleE (Post := fun d _ ↦ c ≠ x ∧ d ≠ x) (T := 0) ε0 fun _ hc ↦ le_ε0 fun a ha b hb ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at ha hb
      rw [ha hc, hb hc]).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind'
    (tail x c)

/-- The proof of work and the second group. -/
def afterC (x c : E) : Spec (afterP x c) (fun _ ↦ c ≠ x) Rej ε0 0 0 :=
  (Spec.grindP (Post := fun _ _ ↦ c ≠ x) 3 (fun _ h ↦ h)
      (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le (by norm_num)))).bind'
    fun _ ↦ second x c

/-- The first group: `c` misses `x`. -/
def first (x : E) : Spec (firstP x) (fun _ ↦ True) Rej ε0 ε0 0 :=
  ((Spec.sampleE (Post := fun c _ ↦ c ≠ x) (T := 0) ε0 fun _ _ ↦ le_ε0 fun a ha b hb ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha hb
      rw [ha, hb]).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind'
    (afterC x)

/-- The specification of the program from the empty history. -/
def spec : Spec prog (fun h ↦ h = []) Rej ε0 0 0 :=
  (Spec.readE (Post := fun _ _ ↦ True) (fun _ _ _ ↦ trivial) le_rfl).bind' first

/-- The doom certificate of the program. -/
def cert : Cert prog := spec.toCertOfLead

/-- Every escape bound of the certificate, discounted by the proof of work before its group, is
at most `2^-192`. -/
theorem cert_bound (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ grindBits h * cert.ε h ≤ (2 ^ 192 : ENNReal)⁻¹ :=
  ε0_eq ▸ spec.toCertOfLead_bound zero_le h

/-- The certificate's doom holds at the start. -/
theorem cert_D_nil : cert.D [] := by
  rw [cert, Spec.toCertOfLead_D]
  exact spec.start_D [] rfl

/-- The certificate's doom holds after the prover's scalar. -/
theorem cert_D_read (x : E) : cert.D [Ev.read x] :=
  cert.read (h := []) x .nil (by simp [prog, readE, after]; rfl) cert_D_nil

/-! ## The follower's allowance is charged at returns in doom -/

/-- A proof of work followed by a lead of `1` has no specification with `εmax = 0`. -/
theorem no_grind_spec :
    Spec (grindP 0) (fun _ ↦ True) (fun _ _ ↦ True) 0 0 1 → False := by
  intro S
  have ha0 : (grindP 0).after [] = some (.grind 0 (.ret ())) := rfl
  have hr : (grindP 0).Reach [] ([] ++ [Ev.grind 0]) := .grind .nil ha0
  have ha1 : (grindP 0).after ([] ++ [Ev.grind 0]) = some (.ret ()) := by simp [grindP, after]
  have hD := S.grind .nil ha0 (S.start_D [] trivial)
  have hV := S.retDoom hr ha1 hD
  have hb := S.bound hr (by simp) (by simp [EndsMove]) hD
  simp only [List.nil_append, grindBits, List.getLast?_singleton, pow_zero, one_mul,
    nonpos_iff_eq_zero] at hb
  simp [hb] at hV

/-! ## The counterexample to the earlier `bind` rule -/

/-- Read a scalar, return a challenge. -/
def p : Prog E := do let _ ← readE; sampleE

open Classical in
/-- Accept iff the challenge is `0`. -/
def f (x : E) : Prog Unit := if x = 0 then .ret () else .fail

/-- The specification of `p`: the challenge misses `0`, with the follower's lead `0`; the
challenge's escape is charged at the boundary after the read. -/
def specP : Spec p (fun _ ↦ True) (fun x _ ↦ x ≠ 0) ε0 0 0 :=
  (Spec.readE (Post := fun _ _ ↦ True) (fun _ _ _ ↦ trivial) le_rfl).bind' fun _ ↦
    (Spec.sampleE (Post := fun x _ ↦ x ≠ 0) (T := 0) ε0 fun _ _ ↦ le_ε0 fun a ha b hb ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha hb
      rw [ha, hb]).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

/-- The specification of `f x` from `x ≠ 0`, with lead `0` and the follower's lead `1`. -/
def specF (x : E) : Spec (f x) (fun _ ↦ x ≠ 0) (fun _ _ ↦ False) ε0 0 1 :=
  Spec.ite (fun h ↦ Spec.dead.mono (fun _ hx ↦ hx h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
    fun _ ↦ Spec.fail

/-- The composite: `εmax = |E|⁻¹` with the follower's lead `1`. -/
def specPF : Spec (p.bind f) (fun _ ↦ True) (fun _ _ ↦ False) ε0 0 1 :=
  specP.bind specF

end

end LeanVMTests.Protocol.Compile.Spec
