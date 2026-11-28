/-
  LeanVM.Protocol.Compile.Moves

  The prover moves a verifier program allows: a structural predicate on programs of the verifier
  language (the bits of its proofs of work, whether it reads commitments, what it returns, and
  that a challenge follows each proof of work), and its rules.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Grind
public import LeanVM.Protocol.Compile.Spec

/-!
# The prover moves of a verifier program

`Moves g c Q G p` says that every proof of work `p` checks has its bits in `g` and is followed at
once by a challenge, inside `p` or, where `p` returns right after it a value satisfying `G`, by
the follower; that `p` reads a commitment only if `c` holds; and that every value `p` returns
satisfies `Q`. It is structural, with no arithmetic, and composes through `bind` (`Moves.seq`):
the follower of a return right after a proof of work must start with a challenge
(`VerifierProgram.StartsSample`). It survives along histories (`Moves.after`). A packed message
constrains nothing but its continuations. Its uses:

* `Moves.grindThenSample`: a whole program whose returns need no follower (`G := False`) has
  `GrindThenSample`, the property the random-oracle theorem's grind step reads
  (`LeanVM.Protocol.Compile.Prog`): the challenge after a proof of work is drawn by the grind's own
  permutation;
* `Moves.reach_commits`: a sub-program that reads no commitment (`c := False`) adds none to a run,
  so the words its openings answer from are the ones committed before it;
* `Moves.grindBits_le`: on a program whose proofs of work have at most `B` bits, every reachable
  history ends with a proof of work of at most `B` bits.

The instances on leanVM's verifier program were proved for the bus era (tag
`formal-bus-archive`, `Protocol/EndToEnd/Sound/Moves.lean`).
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Protocol.Verifier VerifierProgram

@[expose] public section

variable {α β : Type}


/-! ## The predicate -/

/-- Every prover move of `p` is allowed, every proof of work followed by a challenge, and every
return satisfies `Q`: see the module docstring. -/
def Moves (g : ℕ → Prop) (c : Prop) (Q G : α → Prop) : VerifierProgram α → Prop
  | .ret a => Q a
  | .fail => True
  | .read k => ∀ x, Moves g c Q G (k x)
  | .sample k => ∀ x, Moves g c Q G (k x)
  | .readPacked _ k => ∀ xs, Moves g c Q G (k xs)
  | .samplePacked _ k => ∀ xs, Moves g c Q G (k xs)
  | .grind b k => g b ∧ k.StartsSample G ∧ Moves g c Q G k
  | .commit _ _ k => c ∧ Moves g c Q G k
  | .query _ _ k => ∀ rows, Moves g c Q G (k rows)

/-- The moves of a phase that returns anything and may end on a proof of work. -/
abbrev MovesOK (g : ℕ → Prop) (c : Prop) (p : VerifierProgram α) : Prop :=
  Moves g c (fun _ ↦ True) (fun _ ↦ True) p

namespace Moves

variable {g : ℕ → Prop} {c : Prop} {Q G : α → Prop}

/-- Monotonicity. -/
theorem mono {g' : ℕ → Prop} {c' : Prop} {Q' G' : α → Prop} (hg : ∀ b, g b → g' b)
    (hc : c → c') (hQ : ∀ a, Q a → Q' a) (hG : ∀ a, G a → G' a) :
    ∀ {p : VerifierProgram α}, Moves g c Q G p → Moves g' c' Q' G' p
  | .ret a, h => hQ a h
  | .fail, _ => trivial
  | .read _, h => fun x ↦ mono hg hc hQ hG (h x)
  | .sample _, h => fun x ↦ mono hg hc hQ hG (h x)
  | .readPacked _ _, h => fun xs ↦ mono hg hc hQ hG (h xs)
  | .samplePacked _ _, h => fun xs ↦ mono hg hc hQ hG (h xs)
  | .grind b _, h => ⟨hg b h.1, h.2.1.mono hG, mono hg hc hQ hG h.2.2⟩
  | .commit _ _ _, h => ⟨hc h.1, mono hg hc hQ hG h.2⟩
  | .query _ _ _, h => fun rows ↦ mono hg hc hQ hG (h rows)

/-- **Sequencing**: the follower runs on every value `p` returns, and starts with a challenge
where `p` returns right after a proof of work. -/
theorem bind {Q' G' : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : Moves g c Q G p) (hf : ∀ a, Q a → Moves g c Q' G' (f a))
    (hs : ∀ a, Q a → G a → (f a).StartsSample G') : Moves g c Q' G' (p.bind f) := by
  induction p with
  | ret a => exact hf a hp
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | readPacked n k ih => exact fun xs ↦ ih xs (hp xs)
  | samplePacked n k ih => exact fun xs ↦ ih xs (hp xs)
  | grind b k ih =>
    refine ⟨hp.1, ?_, ih hp.2.2⟩
    obtain ⟨-, hk, hm⟩ := hp
    cases k with
    | sample k' => trivial
    | samplePacked n k' => exact hk
    | ret a => exact hs a hm hk
    | _ => exact hk.elim
  | commit ht w k ih => exact ⟨hp.1, ih hp.2⟩
  | query i ps k ih => exact fun rows ↦ ih rows (hp rows)

/-- Sequencing in `do` notation. -/
theorem seq {Q' G' : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : Moves g c Q G p) (hf : ∀ a, Q a → Moves g c Q' G' (f a))
    (hs : ∀ a, Q a → G a → (f a).StartsSample G') : Moves g c Q' G' (p >>= f) :=
  bind hp hf hs

/-- Sequencing after a part that never returns right after a proof of work. -/
theorem seq' {Q' G' : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : Moves g c Q (fun _ ↦ False) p) (hf : ∀ a, Q a → Moves g c Q' G' (f a)) :
    Moves g c Q' G' (p >>= f) :=
  bind hp hf fun _ _ h ↦ h.elim

theorem fail : Moves g c Q G (VerifierProgram.fail : VerifierProgram α) := trivial

theorem pure {a : α} (h : Q a) : Moves g c Q G (Pure.pure a : VerifierProgram α) := h

theorem ret {a : α} (h : Q a) : Moves g c Q G (VerifierProgram.ret a) := h

theorem readE {G : E → Prop} : Moves g c (fun _ ↦ True) G readScalar := fun _ ↦ trivial

theorem sampleE {G : E → Prop} : Moves g c (fun _ ↦ True) G sampleChallenge := fun _ ↦ trivial

/-- `n` reads, `n` values. -/
theorem readN : ∀ n, Moves g c (fun xs ↦ xs.length = n) (fun _ ↦ False) (readScalars n)
  | 0 => rfl
  | n + 1 => seq' readE fun _ _ ↦ seq' (readN n) fun xs hxs ↦ by
      change (_ :: xs).length = n + 1
      rw [List.length_cons, hxs]

/-- `n` samples, `n` values. -/
theorem sampleN : ∀ n, Moves g c (fun xs ↦ xs.length = n) (fun _ ↦ False) (sampleChallenges n)
  | 0 => rfl
  | n + 1 => seq' sampleE fun _ _ ↦ seq' (sampleN n) fun xs hxs ↦ by
      change (_ :: xs).length = n + 1
      rw [List.length_cons, hxs]

/-- A packed message. -/
theorem readPackedE {G : List E → Prop} (n : ℕ) :
    Moves g c (fun _ ↦ True) G (readScalarsPacked n) := fun _ ↦ trivial

/-- A packed draw. -/
theorem samplePackedE {G : List E → Prop} (n : ℕ) :
    Moves g c (fun _ ↦ True) G (sampleChallengesPacked n) := fun _ ↦ trivial

/-- A check. -/
theorem require (q : Prop) [Decidable q] :
    Moves g c (fun _ ↦ q) (fun _ ↦ False) (VerifierProgram.require q) := by
  unfold VerifierProgram.require
  split
  · exact ‹q›
  · trivial

/-- A pure step that may fail returns the option's value. -/
theorem liftOption (o : Option α) : Moves g c (fun a ↦ o = some a) (fun _ ↦ False)
    (Verifier.liftOption o) := by
  cases o
  · trivial
  · rfl

/-- A pure step that may fail, its value unconstrained. -/
theorem liftAny (o : Option α) : Moves g c (fun _ ↦ True) G (Verifier.liftOption o) :=
  (liftOption o).mono (fun _ h ↦ h) id (fun _ _ ↦ trivial) (fun _ h ↦ h.elim)

/-- A proof of work. -/
theorem grindP {b : ℕ} (hb : b ≠ 0 → g b) :
    Moves g c (fun _ ↦ True) (fun _ ↦ True) (grindProofOfWork b) := by
  unfold grindProofOfWork
  split_ifs with h
  · trivial
  · exact ⟨hb h, trivial, trivial⟩

/-- A commitment. -/
theorem commitP (hc : c) (ht w : ℕ) :
    Moves g c (fun _ ↦ True) (fun _ ↦ False) (readCommitment ht w) := ⟨hc, trivial⟩

/-- An opening. -/
theorem queryP (i : ℕ) (ps : List ℕ) :
    Moves g c (fun _ ↦ True) (fun _ ↦ False) (queryOpenings i ps) := fun _ ↦ trivial

/-- A conditional. -/
theorem ite {q : Prop} [Decidable q] {p p' : VerifierProgram α} (hp : q → Moves g c Q G p)
    (hp' : ¬ q → Moves g c Q G p') : Moves g c Q G (if q then p else p') := by
  split
  · exact hp ‹_›
  · exact hp' ‹_›

/-! ## Challenges first -/

theorem startsSample_sampleChallenge {R : β → Prop} (k : E → VerifierProgram β) :
    (sampleChallenge >>= k).StartsSample R := trivial

theorem startsSample_sampleChallengesPacked {R : β → Prop} {n : ℕ} (hn : n ≠ 0)
    (k : List E → VerifierProgram β) : (sampleChallengesPacked n >>= k).StartsSample R :=
  Nat.pos_of_ne_zero hn

theorem startsSample_sampleChallenges {R : β → Prop} {n : ℕ} (hn : n ≠ 0)
    (k : List E → VerifierProgram β) : (sampleChallenges n >>= k).StartsSample R := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  trivial

/-! ## Along histories -/

/-- The program after a history of an allowed program is allowed. -/
theorem after {p : VerifierProgram α} (hp : Moves g c Q G p) :
    ∀ {l : List Ev} {q : VerifierProgram α}, p.after l = some q → Moves g c Q G q := by
  induction p with
  | ret a | fail =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp [VerifierProgram.after] at h
  | readPacked n k ih | samplePacked n k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
      split at h
      · exact ih _ (hp _) h
      · cases h
  | read k ih | sample k ih | query i ps k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
      exact ih _ (hp _) h
  | grind b k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
      split at h
      · exact ih hp.2.2 h
      · cases h
  | commit ht w k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
      split at h
      · exact ih hp.2 h
      · cases h

/-- **A challenge follows every proof of work** of a program that never returns right after one. -/
theorem grindThenSample {P : VerifierProgram α} (hP : Moves g c Q (fun _ ↦ False) P) :
    GrindThenSample P := by
  intro l b k h
  have hs := (hP.after h).2.1
  cases k with
  | sample k' => exact .inl ⟨k', rfl⟩
  | samplePacked n k' =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hs)
    exact .inr ⟨m, k', rfl⟩
  | ret a => exact hs.elim
  | _ => exact hs.elim

/-- The commitments of a history extended by one event. -/
private theorem commits_snoc (l : List Ev) (e : Ev) :
    commits (l ++ [e]) = commits l ++ commits [e] := by
  induction l with
  | nil => rfl
  | cons e' l ih => cases e' <;> simp [commits, ih]

/-- A program without commitments commits nothing along a run. -/
theorem reach_commits {p : VerifierProgram α} (hp : Moves g False Q G p) {h₀ l : List Ev}
    (hl : p.Reach h₀ l) : commits l = [] := by
  induction hl with
  | nil => rfl
  | read x _ _ ih => simp [commits_snoc, ih, commits]
  | sample c _ _ ih => simp [commits_snoc, ih, commits]
  | grind _ _ ih => simp [commits_snoc, ih, commits]
  | commit word _ ha _ _ => exact ((hp.after ha).1).elim
  | query _ _ _ ih => simp [commits_snoc, ih, commits]
  | readPacked _ _ _ _ ih => simp [commits_snoc, ih, commits]
  | samplePacked _ _ _ _ ih => simp [commits_snoc, ih, commits]

/-- Along a reachable history, the last proof of work's bits are at most `B`. -/
theorem grindBits_le {B : ℕ} {P : VerifierProgram α} (hP : Moves (· ≤ B) c Q G P) {h : List Ev}
    (hh : P.Reachable h) : grindBits h ≤ B := by
  cases hh with
  | nil => simp [grindBits]
  | read x _ _ => simp [grindBits]
  | sample x _ _ => simp [grindBits]
  | grind _ ha => simpa [grindBits] using (hP.after ha).1
  | commit word _ _ _ => simp [grindBits]
  | query _ _ _ => simp [grindBits]
  | readPacked _ _ _ _ => simp [grindBits]
  | samplePacked _ _ _ _ => simp [grindBits]

end Moves

/-! ## The grinds' widths -/

/-- A grind of `grindingBits N` bits has at most `64` bits for `N ≤ 2^67`. -/
theorem grindingBits_le_sixtyFour {N : ℕ} (hN : N ≤ 2 ^ 67) : grindingBits N ≤ 64 := by
  unfold grindingBits
  split_ifs with h
  · omega
  · have : Nat.log2 (N - 1) < 67 := (Nat.log2_lt (by omega)).2 (by omega)
    simp only [securityBits]
    omega

/-- The proofs of work the leanVM verifier checks: at most `64` bits. -/
abbrev G64 : ℕ → Prop := (· ≤ 64)

/-- A grind of `grindingBits N` bits has at most `B` bits for `N ≤ 2^(B+3)`. -/
theorem grindingBits_le_of {N B : ℕ} (hN : N ≤ 2 ^ (B + 3)) : grindingBits N ≤ B := by
  unfold grindingBits
  split_ifs with h
  · omega
  · have : Nat.log2 (N - 1) < B + 3 := (Nat.log2_lt (by omega)).2 (by omega)
    simp only [securityBits]
    omega

end
end LeanVM.Protocol.Compile
