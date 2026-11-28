/-
  LeanVM.Prover.Complete.Follows

  A script follows a program: it wins with a relation on the two results and no proof of work's
  challenge left waiting. The form the bus era's WHIR completeness proof was written in.
-/

module

public import LeanVM.Prover.Complete.Prefix

/-!
# Following a program

`FollowsG g R H P cs`: the script `H` wins the program `P` from the flag `g` (`Wins`, proofs of work
of at most `17` bits), ending with no challenge waiting and the results related by `R` at the
commitments then made. `Follows` is from `g = false`. The moves of the bus era's simulation
(`formal-bus-archive`'s `Whir/Complete/Script.lean`) hold for it, with the proof of work's
discipline made explicit: a grind is followed by a draw (`grindBits_then`), so the draw lemmas
hold from either flag (`sampleE_sampleE`, `sampleN_sampleN`).
-/

@[expose] public section

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Prover LeanVM.Protocol.Verifier

variable {α β γ δ : Type}

/-- **The script `H` follows the program `P`** from the flag `g` and the commitments `cs`. -/
def FollowsG (g : Bool) (R : List Committed → α → β → Prop) (H : Script α)
    (P : VerifierProgram β) (cs : List Committed) : Prop :=
  Wins 17 (fun b a g' cs' ↦ g' = false ∧ R cs' a b) P H g cs

/-- `FollowsG` from no waiting challenge. -/
abbrev Follows (R : List Committed → α → β → Prop) (H : Script α) (P : VerifierProgram β)
    (cs : List Committed) : Prop :=
  FollowsG false R H P cs

namespace Follows

/-- A weaker result relation. -/
theorem mono {g : Bool} {R R' : List Committed → α → β → Prop}
    (hR : ∀ cs a b, R cs a b → R' cs a b) {H : Script α} {P : VerifierProgram β}
    {cs : List Committed} (h : FollowsG g R H P cs) : FollowsG g R' H P cs :=
  Wins.mono (fun _ _ _ _ h ↦ ⟨h.1, hR _ _ _ h.2⟩) P H g cs h

/-- **Simulations compose along `bind`.** -/
theorem bind {g : Bool} {R' : List Committed → α → β → Prop} {R : List Committed → γ → δ → Prop}
    {F : α → Script γ} {G : β → VerifierProgram δ}
    (hk : ∀ cs a b, R' cs a b → Follows R (F a) (G b) cs) (H : Script α) (P : VerifierProgram β)
    (cs : List Committed) (h : FollowsG g R' H P cs) : FollowsG g R (H.bind F) (P.bind G) cs :=
  Wins.bind (fun b a g' cs' h' ↦ by
    obtain ⟨rfl, h'⟩ := h'
    exact hk cs' a b h') P H g cs h

/-- `bind` in `do` notation. -/
theorem bind_of {g : Bool} {R' : List Committed → α → β → Prop} {R : List Committed → γ → δ → Prop}
    {F : α → Script γ} {G : β → VerifierProgram δ} {H : Script α} {P : VerifierProgram β}
    {cs : List Committed} (h : FollowsG g R' H P cs)
    (hk : ∀ cs a b, R' cs a b → Follows R (F a) (G b) cs) :
    FollowsG g R (H >>= F) (P >>= G) cs :=
  bind hk H P cs h

theorem ret_ret {R : List Committed → α → β → Prop} {a : α} {b : β} {cs : List Committed}
    (h : R cs a b) : Follows R (Script.ret a) (VerifierProgram.ret b) cs := ⟨rfl, h⟩

/-- Sending a scalar meets reading it. -/
theorem sendE_readE (x : E) (cs : List Committed) :
    Follows (fun cs' _ b ↦ cs' = cs ∧ b = x) (Script.sendE x) VerifierProgram.readScalar cs :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Sending a list meets reading as many scalars. -/
theorem sendList_readN (cs : List Committed) :
    ∀ (xs : List E), Follows (fun cs' _ b ↦ cs' = cs ∧ b = xs) (Script.sendList xs)
      (VerifierProgram.readScalars xs.length) cs
  | [] => ⟨rfl, rfl, rfl⟩
  | x :: xs => by
    rw [List.length_cons, ← VerifierProgram.bind_ret (VerifierProgram.readScalars _),
      readScalars_succ_bind]
    refine ⟨rfl, ?_⟩
    rw [← Script.bind_ret (Script.sendList xs)]
    exact bind (fun cs' _ b h ↦ by obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩) _ _ _
      (sendList_readN cs xs)

/-- Receiving a challenge meets sampling it, from either flag. -/
theorem sampleE_sampleE {g : Bool} (cs : List Committed) :
    FollowsG g (fun cs' a b ↦ cs' = cs ∧ a = b) Script.sampleE VerifierProgram.sampleChallenge cs :=
  fun _ ↦ ⟨rfl, rfl, rfl⟩

/-- Receiving `n` challenges meets sampling them, from either flag when `n ≥ 1`. -/
theorem sampleN_sampleN (cs : List Committed) :
    ∀ (n : ℕ) {g : Bool}, (g = true → 1 ≤ n) →
      FollowsG g (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.length = n) (Script.sampleN n)
        (VerifierProgram.sampleChallenges n) cs
  | 0, g, hg => by
    cases g
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact absurd (hg rfl) (by omega)
  | n + 1, _, _ => by
    simp only [Script.sampleN, VerifierProgram.sampleChallenges]
    refine bind_of (sampleE_sampleE cs) ?_
    rintro cs' a b ⟨rfl, rfl⟩
    refine bind_of (sampleN_sampleN cs' n (by simp)) ?_
    rintro cs'' a' b' ⟨rfl, rfl, hl⟩
    exact ⟨rfl, rfl, rfl, by simp [hl]⟩

/-- **A proof of work, then a script that starts with a draw.** -/
theorem grindBits_then {R : List Committed → γ → δ → Prop} {F : Unit → Script γ}
    {G : Unit → VerifierProgram δ} {bits : ℕ} (h0 : bits ≠ 0) (hb : bits ≤ 17)
    {cs : List Committed} (hk : FollowsG true R (F ()) (G ()) cs) :
    Follows R (Script.grindBits bits >>= F) (VerifierProgram.grindProofOfWork bits >>= G) cs := by
  simp only [Script.grindBits, VerifierProgram.grindProofOfWork, h0, ↓reduceIte, Script.grindS,
    Script.bind_eq, VerifierProgram.bind_eq]
  exact Wins.grind hb hk

/-- Committing a word of the announced width meets reading the commitment. -/
theorem commitS_commitP {ht w : ℕ} {W : Word} (hW : WellShaped w W) (cs : List Committed) :
    Follows (fun cs' _ _ ↦ cs' = cs ++ [⟨ht, w, W⟩]) (Script.commitS W)
      (VerifierProgram.readCommitment ht w) cs :=
  ⟨rfl, hW, rfl, rfl⟩

/-- Receiving rows meets an opening of a commitment made. -/
theorem queryS_queryP {i : ℕ} {ps : List ℕ} {cs : List Committed} {c : Committed}
    (h : cs[i]? = some c) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = c.rows ps ∧ b = c.rows ps) Script.queryS
      (VerifierProgram.queryOpenings i ps) cs :=
  ⟨c, h, rfl, rfl, rfl, rfl⟩

/-- A `require` that holds is met by stopping. -/
theorem ret_require {R : List Committed → α → Unit → Prop} {a : α} {c : Prop} [Decidable c]
    {cs : List Committed} (hc : c) (h : R cs a ()) :
    Follows R (Script.ret a) (VerifierProgram.require c) cs := by
  simp only [VerifierProgram.require, hc, ↓reduceIte]
  exact ⟨rfl, h⟩

end Follows

end LeanVM.Protocol.Whir.Complete

end
