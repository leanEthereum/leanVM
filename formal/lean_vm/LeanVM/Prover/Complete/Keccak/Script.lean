/-
  LeanVM.Prover.Complete.Keccak.Script

  Scripts that make the same moves, and winning scripts move by move: the tools the Keccak
  reduction's completeness is assembled from.
-/

module

public import LeanVM.Prover.Complete.Wins

/-!
# Scripts and winning moves

* `Corr R S H`: the scripts `S` and `H` make the same moves, each challenge and each answer to an
  opening given to both, and end in results related by `R`. `Wins.corr`: a script making the moves
  of a winning one wins too; this relates the executable prover to a specification written for
  the proof.
* `Wins.alongside`: `Script.alongside P S` wins `P` where `S` does, and returns `P`'s value.
* The moves one at a time, from a clear sponge (`g = false`): reading scalars, sampling
  challenges, a proof of work and the challenge after it, and a check that holds.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Keccak

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Prover

variable {α β γ δ : Type}

/-! ## Scripts -/

theorem sbind_eq (p : Script α) (f : α → Script β) : p >>= f = p.bind f := rfl

theorem spure_eq (a : α) : (pure a : Script α) = .ret a := rfl

theorem sret_bind (a : α) (f : α → Script β) : (Script.ret a).bind f = f a := rfl

theorem sbind_ret (p : Script α) : p.bind .ret = p := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [Script.bind, ih]
  | sample k ih => simp only [Script.bind, ih]
  | sendPacked xs k ih => simp only [Script.bind, ih]
  | samplePacked n k ih => simp only [Script.bind, ih]
  | grind o k ih => simp only [Script.bind, ih]
  | commit w k ih => simp only [Script.bind, ih]
  | query k ih => simp only [Script.bind, ih]

theorem sbind_assoc (p : Script α) (f : α → Script β) (g : β → Script γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [Script.bind, ih]
  | sample k ih => simp only [Script.bind, ih]
  | sendPacked xs k ih => simp only [Script.bind, ih]
  | samplePacked n k ih => simp only [Script.bind, ih]
  | grind o k ih => simp only [Script.bind, ih]
  | commit w k ih => simp only [Script.bind, ih]
  | query k ih => simp only [Script.bind, ih]

/-! ## Scripts that make the same moves -/

/-- **The scripts make the same moves**, and end in results related by `R`. -/
def Corr (R : α → β → Prop) : Script α → Script β → Prop
  | .ret a, .ret b => R a b
  | .send x k, .send y k' => x = y ∧ Corr R k k'
  | .sample k, .sample k' => ∀ c, Corr R (k c) (k' c)
  | .sendPacked xs k, .sendPacked ys k' => xs = ys ∧ Corr R k k'
  | .samplePacked n k, .samplePacked m k' => n = m ∧ ∀ cs, Corr R (k cs) (k' cs)
  | .grind o k, .grind o' k' => o = o' ∧ Corr R k k'
  | .commit w k, .commit w' k' => w = w' ∧ Corr R k k'
  | .query k, .query k' => ∀ rows, Corr R (k rows) (k' rows)
  | _, _ => False

namespace Corr

/-- A script makes its own moves. -/
theorem refl : ∀ H : Script α, Corr (· = ·) H H
  | .ret _ => rfl
  | .send _ k => ⟨rfl, refl k⟩
  | .sample k => fun c ↦ refl (k c)
  | .sendPacked _ k => ⟨rfl, refl k⟩
  | .samplePacked _ k => ⟨rfl, fun c ↦ refl (k c)⟩
  | .grind _ k => ⟨rfl, refl k⟩
  | .commit _ k => ⟨rfl, refl k⟩
  | .query k => fun rows ↦ refl (k rows)

/-- **The relation composes along `bind`.** -/
theorem bind {R : α → β → Prop} {S : γ → δ → Prop} {f : α → Script γ} {g : β → Script δ}
    (hk : ∀ a b, R a b → Corr S (f a) (g b)) :
    ∀ (H₁ : Script α) (H₂ : Script β), Corr R H₁ H₂ → Corr S (H₁.bind f) (H₂.bind g) := by
  intro H₁
  induction H₁ with
  | ret a => intro H₂ h; cases H₂ <;> simp only [Corr] at h; exact hk _ _ h
  | send x k ih =>
    intro H₂ h; cases H₂ <;> simp only [Corr] at h; exact ⟨h.1, ih _ h.2⟩
  | sample k ih =>
    intro H₂ h; cases H₂ <;> simp only [Corr] at h; exact fun c ↦ ih c _ (h c)
  | sendPacked xs k ih =>
    intro H₂ h; cases H₂ <;> simp only [Corr] at h; exact ⟨h.1, ih _ h.2⟩
  | samplePacked n k ih =>
    intro H₂ h; cases H₂ <;> simp only [Corr] at h; exact ⟨h.1, fun c ↦ ih c _ (h.2 c)⟩
  | grind o k ih =>
    intro H₂ h; cases H₂ <;> simp only [Corr] at h; exact ⟨h.1, ih _ h.2⟩
  | commit w k ih =>
    intro H₂ h; cases H₂ <;> simp only [Corr] at h; exact ⟨h.1, ih _ h.2⟩
  | query k ih =>
    intro H₂ h; cases H₂ <;> simp only [Corr] at h; exact fun rows ↦ ih rows _ (h rows)

/-- A weaker relation on the results. -/
theorem mono {R R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) (H₁ : Script α) (H₂ : Script β)
    (h : Corr R H₁ H₂) : Corr R' H₁ H₂ := by
  have := bind (f := Script.ret) (g := Script.ret) (S := R') (fun a b hab ↦ hR a b hab) H₁ H₂ h
  rwa [sbind_ret, sbind_ret] at this

/-- `bind` in `do` notation. -/
theorem bind' {R : α → β → Prop} {S : γ → δ → Prop} {f : α → Script γ} {g : β → Script δ}
    {H₁ : Script α} {H₂ : Script β} (h : Corr R H₁ H₂)
    (hk : ∀ a b, R a b → Corr S (f a) (g b)) : Corr S (H₁ >>= f) (H₂ >>= g) :=
  bind hk H₁ H₂ h

/-- The same moves, then a script related to the second's continuation. -/
theorem bind_same {S : γ → δ → Prop} {f : α → Script γ} {g : α → Script δ} (H : Script α)
    (hk : ∀ a, Corr S (f a) (g a)) : Corr S (H.bind f) (H.bind g) :=
  bind (R := (· = ·)) (fun a _ h ↦ h ▸ hk a) H H (refl H)

/-- Two results related. -/
theorem ret_ret {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Corr R (Script.ret a) (Script.ret b) := h

end Corr

/-! ## Winning, through the same moves -/

namespace Wins

variable {B : ℕ}

/-- **A script making the moves of a winning script wins too**, its result related to the
other's. -/
theorem corr {Q : α → β → Bool → List Committed → Prop} {R : γ → β → Prop} :
    ∀ (S : Script γ) (P : VerifierProgram α) (H : Script β) (g : Bool) (cs : List Committed),
      Corr R S H → Wins B Q P H g cs →
        Wins B (fun a s g cs ↦ ∃ b, R s b ∧ Q a b g cs) P S g cs := by
  intro S
  induction S with
  | ret s =>
    intro P H g cs hc hw
    cases H <;> simp only [Corr] at hc
    cases P <;> simp only [Wins] at hw ⊢
    exact ⟨_, hc, hw⟩
  | send x k ih =>
    intro P H g cs hc hw
    cases H <;> simp only [Corr] at hc
    obtain ⟨rfl, hc⟩ := hc
    cases P <;> simp only [Wins] at hw ⊢
    exact ⟨hw.1, ih _ _ _ _ hc hw.2⟩
  | sample k ih =>
    intro P H g cs hc hw
    cases H <;> simp only [Corr] at hc
    cases P <;> simp only [Wins] at hw ⊢
    exact fun c ↦ ih c _ _ _ _ (hc c) (hw c)
  | sendPacked xs k ih =>
    intro P H g cs hc hw
    cases H <;> simp only [Corr] at hc
    obtain ⟨rfl, hc⟩ := hc
    cases P <;> simp only [Wins] at hw ⊢
    exact ⟨hw.1, hw.2.1, ih _ _ _ _ hc hw.2.2⟩
  | samplePacked n k ih =>
    intro P H g cs hc hw
    cases H <;> simp only [Corr] at hc
    obtain ⟨rfl, hc⟩ := hc
    cases P <;> simp only [Wins] at hw ⊢
    exact fun ys hys ↦ ih ys _ _ _ _ (hc ys) (hw ys hys)
  | grind o k ih =>
    intro P H g cs hc hw
    cases H <;> simp only [Corr] at hc
    obtain ⟨rfl, hc⟩ := hc
    cases P <;> simp only [Wins] at hw ⊢
    exact ⟨hw.1, hw.2.1, ih _ _ _ _ hc hw.2.2⟩
  | commit w k ih =>
    intro P H g cs hc hw
    cases H <;> simp only [Corr] at hc
    obtain ⟨rfl, hc⟩ := hc
    cases P <;> simp only [Wins] at hw ⊢
    exact ⟨hw.1, hw.2.1, ih _ _ _ _ hc hw.2.2⟩
  | query k ih =>
    intro P H g cs hc hw
    cases H <;> simp only [Corr] at hc
    cases P <;> simp only [Wins] at hw ⊢
    obtain ⟨c, hc', hw⟩ := hw
    exact ⟨c, hc', ih _ _ _ _ _ (hc _) hw⟩

/-- **The script beside the program** (`Script.alongside`) wins where the script does, and
returns the program's value. -/
theorem alongside [Inhabited α] {Q : α → β → Bool → List Committed → Prop} :
    ∀ (P : VerifierProgram α) (S : Script β) (g : Bool) (cs : List Committed),
      Wins B Q P S g cs →
        Wins B (fun a a' g cs ↦ a' = a ∧ ∃ b, Q a b g cs) P (Script.alongside P S) g cs := by
  intro P
  induction P with
  | ret a =>
    intro S g cs hw
    cases S <;> simp only [Wins] at hw
    exact ⟨rfl, _, hw⟩
  | fail => intro S g cs hw; cases S <;> simp only [Wins] at hw
  | read k ih =>
    intro S g cs hw
    cases S <;> simp only [Wins] at hw
    exact ⟨hw.1, ih _ _ _ _ hw.2⟩
  | sample k ih =>
    intro S g cs hw
    cases S <;> simp only [Wins] at hw
    exact fun c ↦ ih c _ _ _ (hw c)
  | readPacked n k ih =>
    intro S g cs hw
    cases S <;> simp only [Wins] at hw
    exact ⟨hw.1, hw.2.1, ih _ _ _ _ hw.2.2⟩
  | samplePacked n k ih =>
    intro S g cs hw
    cases S <;> simp only [Wins] at hw
    exact fun ys hys ↦ ih ys _ _ _ (hw ys hys)
  | grind b k ih =>
    intro S g cs hw
    cases S <;> simp only [Wins] at hw
    exact ⟨hw.1, hw.2.1, ih _ _ _ hw.2.2⟩
  | commit h w k ih =>
    intro S g cs hw
    cases S <;> simp only [Wins] at hw
    exact ⟨hw.1, hw.2.1, ih _ _ _ hw.2.2⟩
  | query i ps k ih =>
    intro S g cs hw
    cases S <;> simp only [Wins] at hw
    obtain ⟨c, hc, hw⟩ := hw
    exact ⟨c, hc, ih _ _ _ _ hw⟩

/-! ## The moves -/

/-- Sending a list meets reading as many scalars. -/
theorem sendList_readScalars (cs : List Committed) :
    ∀ xs : List E, Wins B (fun a _ g' cs' ↦ a = xs ∧ g' = false ∧ cs' = cs)
      (VerifierProgram.readScalars xs.length) (Script.sendList xs) false cs
  | [] => ⟨rfl, rfl, rfl⟩
  | x :: xs => by
    show Wins B _ (VerifierProgram.readScalar.bind fun x ↦
      (VerifierProgram.readScalars xs.length).bind fun xs ↦ .ret (x :: xs))
      ((Script.send x (.ret ())).bind fun _ ↦ Script.sendList xs) false cs
    refine ⟨rfl, ?_⟩
    have h := LeanVM.Prover.Wins.bind (B := B) (R := fun a _ g' cs' ↦ a = xs ∧ g' = false ∧ cs' = cs)
      (Q := fun a _ g' cs' ↦ a = x :: xs ∧ g' = false ∧ cs' = cs)
      (f := fun ys ↦ VerifierProgram.ret (x :: ys)) (t := Script.ret)
      (fun a _ g' cs' h ↦ by obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩) _ _ _ _
      (sendList_readScalars cs xs)
    rwa [sbind_ret] at h

/-- Sending a scalar meets reading it. -/
theorem sendE_readScalar (x : E) (cs : List Committed) :
    Wins B (fun a _ g' cs' ↦ a = x ∧ g' = false ∧ cs' = cs) VerifierProgram.readScalar
      (Script.sendE x) false cs :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Receiving a challenge meets sampling it. -/
theorem sampleE (g : Bool) (cs : List Committed) :
    Wins B (fun a b g' cs' ↦ a = b ∧ g' = false ∧ cs' = cs) VerifierProgram.sampleChallenge
      Script.sampleE g cs :=
  fun _ ↦ ⟨rfl, rfl, rfl⟩

/-- Receiving `n` challenges meets sampling them. -/
theorem sampleN (cs : List Committed) :
    ∀ n : ℕ, Wins B (fun a b g' cs' ↦ a = b ∧ a.length = n ∧ g' = false ∧ cs' = cs)
      (VerifierProgram.sampleChallenges n) (Script.sampleN n) false cs
  | 0 => ⟨rfl, rfl, rfl, rfl⟩
  | n + 1 => by
    show Wins B _ (VerifierProgram.sampleChallenge.bind fun x ↦
      (VerifierProgram.sampleChallenges n).bind fun xs ↦ .ret (x :: xs))
      (Script.sampleE.bind fun x ↦ (Script.sampleN n).bind fun xs ↦ .ret (x :: xs)) false cs
    refine LeanVM.Prover.Wins.bind (fun a b g' cs' h ↦ ?_) _ _ _ _ (sampleE false cs)
    obtain ⟨rfl, rfl, hcs⟩ := h
    subst hcs
    refine LeanVM.Prover.Wins.bind (fun a' b' g'' cs'' h ↦ ?_) _ _ _ _ (sampleN cs' n)
    obtain ⟨rfl, hl, rfl, rfl⟩ := h
    exact ⟨rfl, by simp [hl], rfl, rfl⟩

/-- A proof of work of `bits ≤ B` bits. -/
theorem grindBits {bits : ℕ} (hb : bits ≤ B) (cs : List Committed) :
    Wins B (fun _ _ g' cs' ↦ (bits = 0 → g' = false) ∧ cs' = cs)
      (VerifierProgram.grindProofOfWork bits) (Script.grindBits bits) false cs := by
  unfold VerifierProgram.grindProofOfWork Script.grindBits
  split_ifs with h
  · exact ⟨fun _ ↦ rfl, rfl⟩
  · exact ⟨rfl, hb, fun h' ↦ absurd h' h, rfl⟩

/-- A proof of work of `bits ≤ B` bits, then its challenge (`grind_sample`). -/
theorem grindSample {bits : ℕ} (hb : bits ≤ B) (cs : List Committed) :
    Wins B (fun a b g' cs' ↦ a = b ∧ g' = false ∧ cs' = cs)
      (VerifierProgram.grindProofOfWork bits >>= fun _ ↦ VerifierProgram.sampleChallenge)
      (Script.grindSample bits) false cs := by
  unfold VerifierProgram.grindProofOfWork Script.grindSample
  split_ifs with h
  · exact fun _ ↦ ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, hb, fun _ ↦ ⟨rfl, rfl, rfl⟩⟩

/-- A proof of work of `bits ≤ B` bits, its challenge, then winning continuations. -/
theorem grindSample_bind {Q : α → β → Bool → List Committed → Prop} {bits : ℕ} (hb : bits ≤ B)
    {k : E → VerifierProgram α} {t : E → Script β} {cs : List Committed}
    (h : ∀ s, Wins B Q (k s) (t s) false cs) :
    Wins B Q (VerifierProgram.grindProofOfWork bits >>= fun _ ↦ VerifierProgram.sampleChallenge >>= k)
      ((Script.grindSample bits).bind t) false cs := by
  unfold VerifierProgram.grindProofOfWork Script.grindSample
  split_ifs
  · exact fun c ↦ h c
  · exact ⟨rfl, hb, fun c ↦ h c⟩

/-- A check that holds, beside nothing. -/
theorem require {c : Prop} [Decidable c] (hc : c) (g : Bool) (cs : List Committed) :
    Wins B (fun _ b g' cs' ↦ b = () ∧ g' = g ∧ cs' = cs) (VerifierProgram.require c)
      (Script.ret ()) g cs := by
  unfold VerifierProgram.require
  split_ifs
  exact ⟨rfl, rfl, rfl⟩

end Wins

end LeanVM.Prover.Complete.Keccak

end
