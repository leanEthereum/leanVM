/-
  LeanVM.Wire.HonestScript

  Every word the honest script commits has rows of one length, at most `wireMaxLeafWords`: the
  stack's level-0 word (`64` words a row) and each deeper WHIR level's (`2 · 2^fold` words, at most
  `32`).
-/

module

public import LeanVM.Wire.HonestShape

/-!
# The honest script's committed words

`WordsOK (honestScript W ρ publicInput)` (`wordsOK_honestScript`). The script commits twice over:
the stack (`stackWordFast`, the `64` lanes' codeword entries at a position) and each non-final WHIR
level's folded lane (`levelWordFast`, `2^fold` lanes of two limbs). The phases it runs beside the
verifier's (`Script.alongside`) commit nothing, since the verifier's phase commits nothing there
(`NoOpenA`): `alongside` commits only where the program does. The deeper levels fold at most `4`
variables (`ladder_tailFolds`, decided over the admissible ladders).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Prover

variable {α β γ : Type}

/-! ## Programs that commit and open nothing -/

/-- No `commit` and no `query` on any path. -/
def NoOpenA : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoOpenA (k x)
  | .sample k => ∀ x, NoOpenA (k x)
  | .readPacked _ k => ∀ xs, NoOpenA (k xs)
  | .samplePacked _ k => ∀ xs, NoOpenA (k xs)
  | .grind _ k => NoOpenA k
  | .commit _ _ _ => False
  | .query _ _ _ => False

theorem NoOpenA.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoOpenA p)
    (hf : ∀ a, NoOpenA (f a)) : NoOpenA (p >>= f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | readPacked m k ih => exact fun x ↦ ih x (hp x)
  | samplePacked m k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ih hp
  | commit _ _ _ _ => exact hp.elim
  | query _ _ _ _ => exact hp.elim

theorem noOpenA_of_cost {p : VerifierProgram α} {n : ℕ} (h : CostLE p n) : NoOpenA p := by
  induction p generalizing n with
  | ret a => trivial
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (h.2 x)
  | sample k ih => exact fun x ↦ ih x (h x)
  | readPacked m k ih => exact fun x ↦ ih x (h.2 x)
  | samplePacked m k ih => exact fun x ↦ ih x (h x)
  | grind b k ih => exact ih h.2
  | commit _ _ _ _ => exact h.elim
  | query _ _ _ _ => exact h.elim

theorem noOpenA_keccakLayers (logSteps : ℕ) (steps : List ℕ) (claim : KeccakClaim) :
    NoOpenA (keccakLayers logSteps steps claim) :=
  noOpenA_of_cost (keccakLayersP logSteps steps claim)

theorem noOpenA_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    NoOpenA (keccakOpen logSteps claim first count value) :=
  noOpenA_of_cost (keccakOpenP logSteps claim first count value)

/-- A search for `NoOpenA` through binds, the primitives, matches and `if`s. -/
macro "no_open" : tactic => `(tactic| repeat (first
  | exact noOpenA_of_cost (CostLE.ret' _ 0)
  | exact noOpenA_of_cost (CostLE.pure' _ 0)
  | exact noOpenA_of_cost CostLE.readE
  | exact noOpenA_of_cost CostLE.sampleE
  | exact noOpenA_of_cost (CostLE.readN _)
  | exact noOpenA_of_cost (CostLE.sampleN _)
  | exact noOpenA_of_cost (CostLE.readPackedP _)
  | exact noOpenA_of_cost (CostLE.samplePackedP _)
  | exact noOpenA_of_cost (CostLE.grindP _)
  | exact noOpenA_of_cost (CostLE.require _)
  | exact noOpenA_of_cost (CostLE.liftOptionP _)
  | exact noOpenA_of_cost (CostLE.sumcheckP _ _ _)
  | exact noOpenA_of_cost (computedSplitP _ _ _)
  | exact noOpenA_keccakLayers _ _ _
  | exact noOpenA_keccakOpen _ _ _ _ _
  | (exact (trivial : NoOpenA (VerifierProgram.fail : VerifierProgram _)))
  | (refine NoOpenA.bind ?_ fun _ ↦ ?_)
  | split
  | (intro _)))

theorem noOpenA_verifyLink (layout : Layout) : NoOpenA (verifyLink computedSplit layout) := by
  rw [Defers.verifyLink_split]
  refine NoOpenA.bind (noOpenA_of_cost (linkPreP layout)) fun y ↦ ?_
  refine NoOpenA.bind (noOpenA_of_cost (computedSplitP _ _ _)) fun split ↦ ?_
  unfold Defers.linkSuf Defers.linkSufOf
  no_open

theorem noOpenA_bindPublicInput (layout : Layout) (publicInput : Digest) :
    NoOpenA (bindPublicInput layout publicInput) :=
  noOpenA_of_cost (bindPublicInputP layout publicInput)

theorem noOpenA_keccakValidity (layout : Layout) (link : LinkEnd) :
    NoOpenA (keccakValidity layout link) :=
  noOpenA_of_cost (keccakValidityP' layout link)

/-! ## Scripts whose words are well shaped -/

theorem WordsOK.bind {s : Script α} {f : α → Script β} (hs : WordsOK s)
    (hf : ∀ a, WordsOK (f a)) : WordsOK (s >>= f) := by
  induction s with
  | ret a => exact hf a
  | send x k ih => exact ih hs
  | sample k ih => exact fun c ↦ ih c (hs c)
  | sendPacked xs k ih => exact ih hs
  | samplePacked n k ih => exact fun cs ↦ ih cs (hs cs)
  | grind o k ih => exact ih hs
  | commit w k ih => exact ⟨hs.1, ih hs.2⟩
  | query k ih => exact fun rows ↦ ih rows (hs rows)

theorem wordsOK_ret (a : α) : WordsOK (Script.ret a) := trivial

theorem wordsOK_pure (a : α) : WordsOK (pure a : Script α) := trivial

theorem wordsOK_sendList : ∀ xs : List E, WordsOK (Script.sendList xs)
  | [] => trivial
  | _ :: xs => wordsOK_sendList xs

theorem wordsOK_sendE (x : E) : WordsOK (Script.sendE x) := trivial

theorem wordsOK_sampleE : WordsOK Script.sampleE := fun _ ↦ trivial

theorem wordsOK_sampleN : ∀ n, WordsOK (Script.sampleN n)
  | 0 => trivial
  | n + 1 => WordsOK.bind wordsOK_sampleE fun _ ↦ WordsOK.bind (wordsOK_sampleN n) fun _ ↦
      trivial

theorem wordsOK_samplePackedS (n : ℕ) : WordsOK (Script.samplePackedS n) := fun _ ↦ trivial

theorem wordsOK_queryS : WordsOK Script.queryS := fun _ ↦ trivial

theorem wordsOK_grindBits (bits : ℕ) : WordsOK (Script.grindBits bits) := by
  unfold Script.grindBits
  split <;> trivial

theorem wordsOK_commitS {w : Word} {L : ℕ} (hL : L ≤ wireMaxLeafWords)
    (hw : ∀ p, (w p).length = L) : WordsOK (Script.commitS w) :=
  ⟨⟨L, hL, hw⟩, trivial⟩

/-- `alongside` commits only where the program does: beside a program that commits and opens
nothing, any script's words are well shaped. -/
theorem wordsOK_alongside [Inhabited α] :
    ∀ (P : VerifierProgram α) (S : Script β), NoOpenA P → WordsOK (Script.alongside P S) := by
  intro P
  induction P with
  | ret a => intro S _; trivial
  | fail => intro S _; cases S <;> trivial
  | read k ih =>
    intro S h
    cases S with
    | send x S => exact ih x S (h x)
    | _ => trivial
  | sample k ih =>
    intro S h
    cases S with
    | sample S => exact fun c ↦ ih c (S c) (h c)
    | _ => trivial
  | readPacked n k ih =>
    intro S h
    cases S with
    | sendPacked xs S => exact ih xs S (h xs)
    | _ => trivial
  | samplePacked n k ih =>
    intro S h
    cases S with
    | samplePacked m S => exact fun cs ↦ ih cs (S cs) (h cs)
    | _ => trivial
  | grind b k ih =>
    intro S h
    cases S with
    | grind o S => exact ih S h
    | _ => trivial
  | commit _ _ _ _ => intro _ h; exact h.elim
  | query _ _ _ _ => intro _ h; exact h.elim

/-- A search for `WordsOK` through binds, the primitives, matches and `if`s. -/
macro "words_ok" : tactic => `(tactic| repeat (first
  | exact wordsOK_ret _
  | exact wordsOK_pure _
  | exact wordsOK_sendList _
  | exact wordsOK_sendE _
  | exact wordsOK_sampleE
  | exact wordsOK_sampleN _
  | exact wordsOK_samplePackedS _
  | exact wordsOK_queryS
  | exact wordsOK_grindBits _
  | (refine WordsOK.bind ?_ fun _ ↦ ?_)
  | split
  | (intro _)))

/-! ## The WHIR prover -/

theorem wordsOK_foldRoundsA : ∀ (n s : ℕ) (f w : Array E), WordsOK (foldRoundsA n s f w)
  | 0, _, _, _ => trivial
  | n + 1, s, f, w => by
    unfold foldRoundsA foldRoundA
    refine WordsOK.bind ?_ fun x ↦ ?_
    · words_ok
    · obtain ⟨f', w'⟩ := x
      exact wordsOK_foldRoundsA n _ _ _

theorem wordsOK_sampleQueriesS (depth : ℕ) : ∀ (fuel remaining : ℕ),
    WordsOK (sampleQueriesS depth fuel remaining)
  | 0, _ => trivial
  | fuel + 1, remaining => by
    unfold sampleQueriesS
    split
    · trivial
    · exact WordsOK.bind wordsOK_sampleE fun _ ↦ WordsOK.bind
        (wordsOK_sampleQueriesS depth fuel _) fun _ ↦ trivial

theorem wordsOK_sumcheckBy {σ : Type} (round : σ → List E) (fold : σ → E → σ) :
    ∀ (modes : List (Option E)) (st : σ), WordsOK (sumcheckBy round fold modes st)
  | [], _ => trivial
  | _ :: modes, st => by
    unfold sumcheckBy
    exact WordsOK.bind (wordsOK_sendList _) fun _ ↦ WordsOK.bind (wordsOK_grindBits _) fun _ ↦
      WordsOK.bind wordsOK_sampleE fun _ ↦ WordsOK.bind (wordsOK_sumcheckBy round fold modes _)
        fun _ ↦ trivial

theorem wordsOK_tailA (mu : ℕ) (w g : Array E) : WordsOK (tailA mu w g) :=
  WordsOK.bind (wordsOK_sumcheckBy _ _ _ _) fun _ ↦ trivial

theorem length_levelWord (κ k R : ℕ) (g : Array E) (p : ℕ) :
    (levelWordFast κ k R g p).length = 2 * 2 ^ k := by
  simp [levelWordFast, levelWordFast.levelWordOf, Nat.mul_comm]

theorem length_stackWord (μ R : ℕ) (stack : Array K) (p : ℕ) :
    (stackWordFast μ R stack p).length = 64 := by
  simp [stackWordFast, stackWordFast.stackWordOf]

/-- The deeper levels' folds give words of at most `wireMaxLeafWords` words a row. -/
def TailFoldsOK (levels : List Whir.Level) : Prop := ∀ l ∈ levels.tail, 2 * 2 ^ l.fold ≤ 64

instance (levels : List Whir.Level) : Decidable (TailFoldsOK levels) :=
  inferInstanceAs (Decidable (∀ l ∈ levels.tail, _))

/-- **Every admissible ladder's deeper levels fold at most `4` variables**, decided over the
admissible pairs. -/
theorem ladder_tailFolds (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) : TailFoldsOK levels := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels → TailFoldsOK levels := by
      decide +kernel
    exact key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2) hadm
      levels h
  · simp [Whir.ladder, hadm] at h

theorem wordsOK_levelsA : ∀ (levels : List Whir.Level) (mu : ℕ) (f w : Array E),
    TailFoldsOK levels → WordsOK (levelsA mu levels f w)
  | [], _, _, _, _ => trivial
  | level :: rest, mu, f, w, ht => by
    unfold levelsA
    refine WordsOK.bind (wordsOK_foldRoundsA _ _ _ _) fun x ↦ ?_
    obtain ⟨p, w'⟩ := x
    cases rest with
    | nil =>
      exact WordsOK.bind (wordsOK_sendList _) fun _ ↦ WordsOK.bind (wordsOK_grindBits _) fun _ ↦
        WordsOK.bind (wordsOK_sampleQueriesS _ _ _) fun _ ↦ WordsOK.bind wordsOK_queryS fun _ ↦
          wordsOK_tailA _ _ _
    | cons next rest' =>
      have hn : 2 * 2 ^ next.fold ≤ 64 := ht next (by simp)
      refine WordsOK.bind (wordsOK_commitS hn (length_levelWord _ _ _ _)) fun _ ↦ ?_
      refine WordsOK.bind (wordsOK_sendList _) fun _ ↦ WordsOK.bind (wordsOK_grindBits _)
        fun _ ↦ WordsOK.bind (wordsOK_sampleN _) fun _ ↦ WordsOK.bind (wordsOK_sendE _) fun _ ↦
          WordsOK.bind (wordsOK_grindBits _) fun _ ↦ WordsOK.bind (wordsOK_sampleQueriesS _ _ _)
            fun _ ↦ WordsOK.bind wordsOK_sampleE fun _ ↦ WordsOK.bind wordsOK_queryS fun _ ↦ ?_
      refine wordsOK_levelsA (next :: rest') _ _ _ fun l hl ↦ ht l ?_
      simp only [List.tail_cons] at hl ⊢
      exact List.mem_cons_of_mem _ hl

theorem wordsOK_openingFast (μ R : ℕ) (stack : Array K) (claims : List ClaimDesc)
    (batching : E) : WordsOK (openingFast μ R stack claims batching) := by
  unfold openingFast
  split
  · trivial
  · next config hc => exact wordsOK_levelsA _ _ _ _ (ladder_tailFolds _ _ _ hc)

/-! ## The honest script -/

theorem wordsOK_oodFast (μ : ℕ) (stack : Array K) : WordsOK (oodFast μ stack) :=
  WordsOK.bind (wordsOK_grindBits _) fun _ ↦ WordsOK.bind (wordsOK_sampleN _) fun _ ↦
    WordsOK.bind (wordsOK_sendE _) fun _ ↦ trivial

theorem wordsOK_ringFast (merging : Bool) : WordsOK (ringFast merging) :=
  WordsOK.bind (wordsOK_grindBits _) fun _ ↦ WordsOK.bind (wordsOK_samplePackedS _) fun _ ↦
    trivial

/-- **Every word the honest script commits is well shaped.** -/
theorem wordsOK_honestScript (W : Witness) (ρ : ℕ) (publicInput : Digest) :
    WordsOK (honestScript W ρ publicInput) := by
  unfold honestScript
  refine WordsOK.bind (wordsOK_sendList _) fun _ ↦ ?_
  refine WordsOK.bind (wordsOK_commitS (le_refl 64) (length_stackWord _ _ _)) fun _ ↦ ?_
  refine WordsOK.bind (wordsOK_oodFast _ _) fun _ ↦ ?_
  refine WordsOK.bind (wordsOK_alongside _ _ (noOpenA_verifyLink _)) fun link ↦ ?_
  refine WordsOK.bind (wordsOK_alongside _ _ (noOpenA_bindPublicInput _ _)) fun _ ↦ ?_
  refine WordsOK.bind (wordsOK_alongside _ _ (noOpenA_keccakValidity _ _)) fun x ↦ ?_
  obtain ⟨outputs, keccakPoint, keccakSlices⟩ := x
  refine WordsOK.bind (wordsOK_ringFast _) fun _ ↦ ?_
  exact wordsOK_openingFast _ _ _ _ _

end LeanVM.Wire

end
