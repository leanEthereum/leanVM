/-
  LeanVM.Prover.Complete.Wins

  A script that wins against a verifier program: along every choice of the challenges, the
  script's moves are the program's, the program never rejects, and its result satisfies a
  postcondition. The relation each phase of the honest prover is proved to satisfy.
-/

module

public import LeanVM.Protocol.Compile.Prog

/-!
# Winning scripts

`Wins B Q p s g cs`: the script `s` plays the program `p` (`Statement/Prover/Script.lean`) and
wins, whatever the challenges: at every node the script makes the program's move (a scalar at a
`read`, a packed message of the asked length at a `readPacked`, a proof of work at a `grind` of at
most `B` bits, a matrix of the announced width at a `commit`), the program reaches no `fail`, every
opening names a commitment made, and every value `a` the program returns, with the script's value
`b` there, satisfies `Q a b g' cs'`. The flag `g` says that a proof of work's challenge waits in the
sponge (the verifier rejects an absorption then, `run`), `cs` the matrices committed so far
(`Committed`: height, width, word), whose rows answer the openings as the honest run's trees do
(`Committed.rows`).

`Wins.bind` composes it along the two languages' `bind`, which is how the honest prover's phases are
assembled; `Wins.mono` weakens the postcondition.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- A matrix the honest run has committed: its tree's height, its rows' width, and its rows. -/
structure Committed where
  /-- The tree's height. -/
  height : ℕ
  /-- The rows' width. -/
  width : ℕ
  /-- The rows. -/
  word : Word

/-- The rows the honest run answers an opening at `ps` with: each position's low `height` bits
(`runFrom`'s `query`). -/
def Committed.rows (c : Committed) (ps : List ℕ) : List (List K) :=
  ps.map fun q ↦ c.word (q % 2 ^ c.height)

variable {α β γ δ : Type}

/-- **The script wins against the program** (see the module docstring). -/
def Wins (B : ℕ) (Q : α → β → Bool → List Committed → Prop) :
    VerifierProgram α → Script β → Bool → List Committed → Prop
  | .ret a, .ret b, g, cs => Q a b g cs
  | .read k, .send x s, g, cs => g = false ∧ Wins B Q (k x) s false cs
  | .sample k, .sample s, _, cs => ∀ c, Wins B Q (k c) (s c) false cs
  | .readPacked n k, .sendPacked xs s, g, cs =>
    g = false ∧ xs.length = n ∧ Wins B Q (k xs) s false cs
  | .samplePacked n k, .samplePacked _ s, g, cs =>
    ∀ ys : List E, ys.length = n → Wins B Q (k ys) (s ys) (g && n == 0) cs
  | .grind bits k, .grind _ s, g, cs => g = false ∧ bits ≤ B ∧ Wins B Q k s true cs
  | .commit ht w k, .commit word s, g, cs =>
    g = false ∧ WellShaped w word ∧ Wins B Q k s false (cs ++ [⟨ht, w, word⟩])
  | .query i ps k, .query s, g, cs =>
    ∃ c, cs[i]? = some c ∧ Wins B Q (k (c.rows ps)) (s (c.rows ps)) g cs
  | _, _, _, _ => False

namespace Wins

variable {B : ℕ}

/-- **A weaker postcondition.** -/
theorem mono {Q R : α → β → Bool → List Committed → Prop}
    (hQR : ∀ a b g cs, Q a b g cs → R a b g cs) :
    ∀ (p : VerifierProgram α) (s : Script β) (g : Bool) (cs : List Committed),
      Wins B Q p s g cs → Wins B R p s g cs
  | .ret _, .ret _, _, _, h => hQR _ _ _ _ h
  | .read k, .send x s, _, _, h => ⟨h.1, mono hQR (k x) s _ _ h.2⟩
  | .sample k, .sample s, _, _, h => fun c ↦ mono hQR (k c) (s c) _ _ (h c)
  | .readPacked _ k, .sendPacked xs s, _, _, h => ⟨h.1, h.2.1, mono hQR (k xs) s _ _ h.2.2⟩
  | .samplePacked _ k, .samplePacked _ s, _, _, h => fun ys hys ↦
    mono hQR (k ys) (s ys) _ _ (h ys hys)
  | .grind _ k, .grind _ s, _, _, h => ⟨h.1, h.2.1, mono hQR k s _ _ h.2.2⟩
  | .commit _ _ k, .commit _ s, _, _, h => ⟨h.1, h.2.1, mono hQR k s _ _ h.2.2⟩
  | .query _ _ k, .query s, _, cs, h => by
    obtain ⟨c, hc, h⟩ := h
    exact ⟨c, hc, mono hQR _ _ _ _ h⟩
  | .ret _, .send _ _, _, _, h | .ret _, .sample _, _, _, h | .ret _, .sendPacked _ _, _, _, h
  | .ret _, .samplePacked _ _, _, _, h | .ret _, .grind _ _, _, _, h
  | .ret _, .commit _ _, _, _, h | .ret _, .query _, _, _, h => h.elim
  | .fail, _, _, _, h => h.elim
  | .read _, .ret _, _, _, h | .read _, .sample _, _, _, h | .read _, .sendPacked _ _, _, _, h
  | .read _, .samplePacked _ _, _, _, h | .read _, .grind _ _, _, _, h
  | .read _, .commit _ _, _, _, h | .read _, .query _, _, _, h => h.elim
  | .sample _, .ret _, _, _, h | .sample _, .send _ _, _, _, h
  | .sample _, .sendPacked _ _, _, _, h | .sample _, .samplePacked _ _, _, _, h
  | .sample _, .grind _ _, _, _, h | .sample _, .commit _ _, _, _, h
  | .sample _, .query _, _, _, h => h.elim
  | .readPacked _ _, .ret _, _, _, h | .readPacked _ _, .send _ _, _, _, h
  | .readPacked _ _, .sample _, _, _, h | .readPacked _ _, .samplePacked _ _, _, _, h
  | .readPacked _ _, .grind _ _, _, _, h | .readPacked _ _, .commit _ _, _, _, h
  | .readPacked _ _, .query _, _, _, h => h.elim
  | .samplePacked _ _, .ret _, _, _, h | .samplePacked _ _, .send _ _, _, _, h
  | .samplePacked _ _, .sample _, _, _, h | .samplePacked _ _, .sendPacked _ _, _, _, h
  | .samplePacked _ _, .grind _ _, _, _, h | .samplePacked _ _, .commit _ _, _, _, h
  | .samplePacked _ _, .query _, _, _, h => h.elim
  | .grind _ _, .ret _, _, _, h | .grind _ _, .send _ _, _, _, h | .grind _ _, .sample _, _, _, h
  | .grind _ _, .sendPacked _ _, _, _, h | .grind _ _, .samplePacked _ _, _, _, h
  | .grind _ _, .commit _ _, _, _, h | .grind _ _, .query _, _, _, h => h.elim
  | .commit _ _ _, .ret _, _, _, h | .commit _ _ _, .send _ _, _, _, h
  | .commit _ _ _, .sample _, _, _, h | .commit _ _ _, .sendPacked _ _, _, _, h
  | .commit _ _ _, .samplePacked _ _, _, _, h | .commit _ _ _, .grind _ _, _, _, h
  | .commit _ _ _, .query _, _, _, h => h.elim
  | .query _ _ _, .ret _, _, _, h | .query _ _ _, .send _ _, _, _, h
  | .query _ _ _, .sample _, _, _, h | .query _ _ _, .sendPacked _ _, _, _, h
  | .query _ _ _, .samplePacked _ _, _, _, h | .query _ _ _, .grind _ _, _, _, h
  | .query _ _ _, .commit _ _, _, _, h => h.elim

/-- **Sequencing.** A script that wins `p` with postcondition `R`, followed by scripts that win the
program's continuations from every outcome `R` allows, wins the sequence. -/
theorem bind {R : α → β → Bool → List Committed → Prop} {Q : γ → δ → Bool → List Committed → Prop}
    {f : α → VerifierProgram γ} {t : β → Script δ}
    (hk : ∀ a b g cs, R a b g cs → Wins B Q (f a) (t b) g cs) :
    ∀ (p : VerifierProgram α) (s : Script β) (g : Bool) (cs : List Committed),
      Wins B R p s g cs → Wins B Q (p.bind f) (s.bind t) g cs
  | .ret _, .ret _, _, _, h => hk _ _ _ _ h
  | .read k, .send x s, _, _, h => ⟨h.1, bind hk (k x) s _ _ h.2⟩
  | .sample k, .sample s, _, _, h => fun c ↦ bind hk (k c) (s c) _ _ (h c)
  | .readPacked _ k, .sendPacked xs s, _, _, h => ⟨h.1, h.2.1, bind hk (k xs) s _ _ h.2.2⟩
  | .samplePacked _ k, .samplePacked _ s, _, _, h => fun ys hys ↦
    bind hk (k ys) (s ys) _ _ (h ys hys)
  | .grind _ k, .grind _ s, _, _, h => ⟨h.1, h.2.1, bind hk k s _ _ h.2.2⟩
  | .commit _ _ k, .commit _ s, _, _, h => ⟨h.1, h.2.1, bind hk k s _ _ h.2.2⟩
  | .query _ _ k, .query s, _, cs, h => by
    obtain ⟨c, hc, h⟩ := h
    exact ⟨c, hc, bind hk _ _ _ _ h⟩
  | .ret _, .send _ _, _, _, h | .ret _, .sample _, _, _, h | .ret _, .sendPacked _ _, _, _, h
  | .ret _, .samplePacked _ _, _, _, h | .ret _, .grind _ _, _, _, h
  | .ret _, .commit _ _, _, _, h | .ret _, .query _, _, _, h => h.elim
  | .fail, _, _, _, h => h.elim
  | .read _, .ret _, _, _, h | .read _, .sample _, _, _, h | .read _, .sendPacked _ _, _, _, h
  | .read _, .samplePacked _ _, _, _, h | .read _, .grind _ _, _, _, h
  | .read _, .commit _ _, _, _, h | .read _, .query _, _, _, h => h.elim
  | .sample _, .ret _, _, _, h | .sample _, .send _ _, _, _, h
  | .sample _, .sendPacked _ _, _, _, h | .sample _, .samplePacked _ _, _, _, h
  | .sample _, .grind _ _, _, _, h | .sample _, .commit _ _, _, _, h
  | .sample _, .query _, _, _, h => h.elim
  | .readPacked _ _, .ret _, _, _, h | .readPacked _ _, .send _ _, _, _, h
  | .readPacked _ _, .sample _, _, _, h | .readPacked _ _, .samplePacked _ _, _, _, h
  | .readPacked _ _, .grind _ _, _, _, h | .readPacked _ _, .commit _ _, _, _, h
  | .readPacked _ _, .query _, _, _, h => h.elim
  | .samplePacked _ _, .ret _, _, _, h | .samplePacked _ _, .send _ _, _, _, h
  | .samplePacked _ _, .sample _, _, _, h | .samplePacked _ _, .sendPacked _ _, _, _, h
  | .samplePacked _ _, .grind _ _, _, _, h | .samplePacked _ _, .commit _ _, _, _, h
  | .samplePacked _ _, .query _, _, _, h => h.elim
  | .grind _ _, .ret _, _, _, h | .grind _ _, .send _ _, _, _, h | .grind _ _, .sample _, _, _, h
  | .grind _ _, .sendPacked _ _, _, _, h | .grind _ _, .samplePacked _ _, _, _, h
  | .grind _ _, .commit _ _, _, _, h | .grind _ _, .query _, _, _, h => h.elim
  | .commit _ _ _, .ret _, _, _, h | .commit _ _ _, .send _ _, _, _, h
  | .commit _ _ _, .sample _, _, _, h | .commit _ _ _, .sendPacked _ _, _, _, h
  | .commit _ _ _, .samplePacked _ _, _, _, h | .commit _ _ _, .grind _ _, _, _, h
  | .commit _ _ _, .query _, _, _, h => h.elim
  | .query _ _ _, .ret _, _, _, h | .query _ _ _, .send _ _, _, _, h
  | .query _ _ _, .sample _, _, _, h | .query _ _ _, .sendPacked _ _, _, _, h
  | .query _ _ _, .samplePacked _ _, _, _, h | .query _ _ _, .grind _ _, _, _, h
  | .query _ _ _, .commit _ _, _, _, h => h.elim

/-- `bind` in `do` notation. -/
theorem bind' {R : α → β → Bool → List Committed → Prop} {Q : γ → δ → Bool → List Committed → Prop}
    {p : VerifierProgram α} {s : Script β} {f : α → VerifierProgram γ} {t : β → Script δ}
    {g : Bool} {cs : List Committed} (h : Wins B R p s g cs)
    (hk : ∀ a b g cs, R a b g cs → Wins B Q (f a) (t b) g cs) :
    Wins B Q (p >>= f) (s >>= t) g cs :=
  bind hk p s g cs h

/-- A larger bound on the proofs of work. -/
theorem mono_bits {B B' : ℕ} (hB : B ≤ B') {Q : α → β → Bool → List Committed → Prop} :
    ∀ (p : VerifierProgram α) (s : Script β) (g : Bool) (cs : List Committed),
      Wins B Q p s g cs → Wins B' Q p s g cs
  | .ret _, .ret _, _, _, h => h
  | .read k, .send x s, _, _, h => ⟨h.1, mono_bits hB (k x) s _ _ h.2⟩
  | .sample k, .sample s, _, _, h => fun c ↦ mono_bits hB (k c) (s c) _ _ (h c)
  | .readPacked _ k, .sendPacked xs s, _, _, h => ⟨h.1, h.2.1, mono_bits hB (k xs) s _ _ h.2.2⟩
  | .samplePacked _ k, .samplePacked _ s, _, _, h => fun ys hys ↦
    mono_bits hB (k ys) (s ys) _ _ (h ys hys)
  | .grind _ k, .grind _ s, _, _, h => ⟨h.1, h.2.1.trans hB, mono_bits hB k s _ _ h.2.2⟩
  | .commit _ _ k, .commit _ s, _, _, h => ⟨h.1, h.2.1, mono_bits hB k s _ _ h.2.2⟩
  | .query _ _ k, .query s, _, cs, h => by
    obtain ⟨c, hc, h⟩ := h
    exact ⟨c, hc, mono_bits hB _ _ _ _ h⟩
  | .ret _, .send _ _, _, _, h | .ret _, .sample _, _, _, h | .ret _, .sendPacked _ _, _, _, h
  | .ret _, .samplePacked _ _, _, _, h | .ret _, .grind _ _, _, _, h
  | .ret _, .commit _ _, _, _, h | .ret _, .query _, _, _, h => h.elim
  | .fail, _, _, _, h => h.elim
  | .read _, .ret _, _, _, h | .read _, .sample _, _, _, h | .read _, .sendPacked _ _, _, _, h
  | .read _, .samplePacked _ _, _, _, h | .read _, .grind _ _, _, _, h
  | .read _, .commit _ _, _, _, h | .read _, .query _, _, _, h => h.elim
  | .sample _, .ret _, _, _, h | .sample _, .send _ _, _, _, h
  | .sample _, .sendPacked _ _, _, _, h | .sample _, .samplePacked _ _, _, _, h
  | .sample _, .grind _ _, _, _, h | .sample _, .commit _ _, _, _, h
  | .sample _, .query _, _, _, h => h.elim
  | .readPacked _ _, .ret _, _, _, h | .readPacked _ _, .send _ _, _, _, h
  | .readPacked _ _, .sample _, _, _, h | .readPacked _ _, .samplePacked _ _, _, _, h
  | .readPacked _ _, .grind _ _, _, _, h | .readPacked _ _, .commit _ _, _, _, h
  | .readPacked _ _, .query _, _, _, h => h.elim
  | .samplePacked _ _, .ret _, _, _, h | .samplePacked _ _, .send _ _, _, _, h
  | .samplePacked _ _, .sample _, _, _, h | .samplePacked _ _, .sendPacked _ _, _, _, h
  | .samplePacked _ _, .grind _ _, _, _, h | .samplePacked _ _, .commit _ _, _, _, h
  | .samplePacked _ _, .query _, _, _, h => h.elim
  | .grind _ _, .ret _, _, _, h | .grind _ _, .send _ _, _, _, h | .grind _ _, .sample _, _, _, h
  | .grind _ _, .sendPacked _ _, _, _, h | .grind _ _, .samplePacked _ _, _, _, h
  | .grind _ _, .commit _ _, _, _, h | .grind _ _, .query _, _, _, h => h.elim
  | .commit _ _ _, .ret _, _, _, h | .commit _ _ _, .send _ _, _, _, h
  | .commit _ _ _, .sample _, _, _, h | .commit _ _ _, .sendPacked _ _, _, _, h
  | .commit _ _ _, .samplePacked _ _, _, _, h | .commit _ _ _, .grind _ _, _, _, h
  | .commit _ _ _, .query _, _, _, h => h.elim
  | .query _ _ _, .ret _, _, _, h | .query _ _ _, .send _ _, _, _, h
  | .query _ _ _, .sample _, _, _, h | .query _ _ _, .sendPacked _ _, _, _, h
  | .query _ _ _, .samplePacked _ _, _, _, h | .query _ _ _, .grind _ _, _, _, h
  | .query _ _ _, .commit _ _, _, _, h => h.elim

/-! ### The moves, one at a time -/

theorem ret {Q : α → β → Bool → List Committed → Prop} {a : α} {b : β} {g : Bool}
    {cs : List Committed} (h : Q a b g cs) : Wins B Q (.ret a) (.ret b) g cs := h

theorem read {Q : α → β → Bool → List Committed → Prop} {k : E → VerifierProgram α} {x : E}
    {s : Script β} {cs : List Committed} (h : Wins B Q (k x) s false cs) :
    Wins B Q (.read k) (.send x s) false cs := ⟨rfl, h⟩

theorem sample {Q : α → β → Bool → List Committed → Prop} {k : E → VerifierProgram α}
    {s : E → Script β} {g : Bool} {cs : List Committed}
    (h : ∀ c, Wins B Q (k c) (s c) false cs) : Wins B Q (.sample k) (.sample s) g cs := h

theorem grind {Q : α → β → Bool → List Committed → Prop} {bits : ℕ} {k : VerifierProgram α}
    {o : Bool} {s : Script β} {cs : List Committed} (hb : bits ≤ B)
    (h : Wins B Q k s true cs) : Wins B Q (.grind bits k) (.grind o s) false cs := ⟨rfl, hb, h⟩

end Wins

end LeanVM.Prover

end
