/-
  LeanVM.Protocol.Whir.Complete.Script

  Honest provers as scripts: a program of the prover's moves that mirrors a verifier program,
  the strategy that replays it along a history, and the simulation relation under which the
  verifier's interactive run against that strategy succeeds.
-/

module

public import LeanVM.Protocol.Compile.Prover
public import Statement.Prover.Script

/-!
# Honest prover scripts

An interactive prover (`LeanVM.Protocol.Compile.Strategy`) is a pair of functions of the
history. Writing one directly means recovering, at every `read` node, the prover's state from
the events so far. A `Script` is the prover written the other way round, as a program of its own
moves: it sends a scalar (`send`), receives a challenge (`sample`), passes a proof of work
(`grind`), commits a word (`commit`) and receives opened rows (`query`), in the order the
verifier reads them, carrying whatever state it needs in ordinary bindings.

* `Script.walk` follows a local history through a script; `Script.msgAt` and `Script.wordAt` are
  the scalar and the word the script sends where the walk ends.
* `Strategy.ofScript H n` is the strategy that replays `H` along the events after the first `n`.
* `Follows R H P cs`: the script `H` answers every move of the verifier program `P`, run with the
  commitments `cs` already in place: a `send` meets a `read` (and `P` continues with the scalar
  sent), a commitment meets a commitment with a word of the announced width, an opening is
  answered from the commitments, and where `P` returns, `H` returns too with results related by
  `R` (which sees the commitments at that point). `P` never fails: there is no node of a script
  that meets `VerifierProgram.fail`, so a `require` must hold.
* `Follows.bind`: simulations compose along `bind`, which is how a whole verifier's honest prover
  is assembled from its phases.
* `runFrom_of_follows`: if `H` follows `P` from the commitments of a history `h`, every strategy
  that agrees with the replay of `H` after `h` runs `P` from `h` to a result related by `R`, for
  every challenge function, and commits well-shaped words on the way.

Nothing here is specific to WHIR: the module is generic over verifier programs and is a candidate
for `LeanVM.Protocol.Compile`, next to `Strategy`, for the honest provers of the other phases.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile

@[expose] public section

/-! ## Scripts

The type `Script` and its moves are the statement's (`Statement/Prover/Script.lean`); the replay
along a history and the simulation are proofs. -/

end

end LeanVM.Protocol.Whir.Complete

namespace LeanVM.Prover.Script

open LeanVM.Parameters LeanVM.Protocol.Compile

@[expose] public section

variable {α β : Type}

@[simp] theorem pure_eq (a : α) : (pure a : Script α) = ret a := rfl

@[simp] theorem bind_eq (p : Script α) (f : α → Script β) : p >>= f = p.bind f := rfl

@[simp] theorem ret_bind (a : α) (f : α → Script β) : (ret a).bind f = f a := rfl

/-- `ret` is a right unit. -/
theorem bind_ret (p : Script α) : p.bind ret = p := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | grind k ih => simp only [bind, ih]
  | commit w k ih => simp only [bind, ih]
  | query k ih => simp only [bind, ih]

/-! ### Replay along a history -/

/-- One event of a history, read by a script node of the matching kind. -/
def step : Script α → Ev → Option (Script α)
  | send _ k, Ev.read _ => some k
  | sample k, Ev.sample c => some (k c)
  | grind k, Ev.grind _ => some k
  | commit _ k, Ev.commit _ _ _ => some k
  | query k, Ev.query rows => some (k rows)
  | _, _ => none

/-- The script after a local history. -/
def walk (H : Script α) : List Ev → Option (Script α)
  | [] => some H
  | e :: es => (H.step e).bind fun H' ↦ H'.walk es

/-- Walking one more event is one more `step`. -/
theorem walk_append (H : Script α) (l : List Ev) (e : Ev) :
    H.walk (l ++ [e]) = (H.walk l).bind fun H' ↦ H'.step e := by
  induction l generalizing H with
  | nil => simp [walk]
  | cons e' l ih =>
    simp only [List.cons_append, walk]
    cases H.step e' <;> simp [ih]

/-- The scalar the script sends after a local history (`0` if it is not at a `send`). -/
def msgAt (H : Script α) (l : List Ev) : E :=
  match H.walk l with
  | some (send x _) => x
  | _ => 0

/-- The word the script commits after a local history (empty rows if it is not at a
`commit`). -/
def wordAt (H : Script α) (l : List Ev) : Word :=
  match H.walk l with
  | some (commit w _) => w
  | _ => fun _ ↦ []

end

end LeanVM.Prover.Script

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Prover

@[expose] public section

/-- The strategy that replays the script `H` along the events after the first `n`. -/
def Strategy.ofScript {α : Type} (H : Script α) (n : ℕ) : Strategy where
  msg h := H.msgAt (h.drop n)
  word h := H.wordAt (h.drop n)

/-! ## Simulation -/

/-- The commitments of a history in the form `commits` lists them. -/
abbrev Commits : Type := List (ℕ × ℕ × Word)

/-- The rows the `i`-th of the commitments `cs` holds at `positions`: `answer` on a list of
commitments. -/
def answerOf (cs : Commits) (i : ℕ) (positions : List ℕ) : Option (List (List K)) :=
  cs[i]?.map fun c ↦ positions.map fun p ↦ c.2.2 (p % 2 ^ c.1)

/-- `answer` reads the commitments of the history. -/
theorem answer_eq_answerOf (h : List Ev) (i : ℕ) (ps : List ℕ) :
    answer h i ps = answerOf (commits h) i ps := rfl

/-- **The script `H` follows the program `P`** from the commitments `cs`: it meets every move of
`P` with a move of the same kind (a committed word of the announced width, an opening answered
from the commitments), and where `P` returns it returns too, the results related by `R` at the
commitments then in place. `P` never fails. -/
def Follows {α β : Type} (R : Commits → α → β → Prop) :
    Script α → VerifierProgram β → Commits → Prop
  | .ret a, .ret b, cs => R cs a b
  | .send x k, .read k', cs => Follows R k (k' x) cs
  | .sample k, .sample k', cs => ∀ c, Follows R (k c) (k' c) cs
  | .grind k, .grind _ k', cs => Follows R k k' cs
  | .commit W k, .commit ht w k', cs => WellShaped w W ∧ Follows R k k' (cs ++ [(ht, w, W)])
  | .query k, .query i ps k', cs =>
    ∃ rows, answerOf cs i ps = some rows ∧ Follows R (k rows) (k' rows) cs
  | _, _, _ => False

namespace Follows

variable {α β γ δ : Type}

/-- A weaker result relation. -/
theorem mono {R R' : Commits → α → β → Prop} (hR : ∀ cs a b, R cs a b → R' cs a b) :
    ∀ (H : Script α) (P : VerifierProgram β) (cs : Commits), Follows R H P cs → Follows R' H P
        cs := by
  intro H
  induction H with
  | ret a => intro P cs h; cases P <;> simp_all [Follows]
  | send x k ih => intro P cs h; cases P <;> simp_all [Follows]
  | sample k ih => intro P cs h; cases P <;> simp_all [Follows]
  | grind k ih => intro P cs h; cases P <;> simp_all [Follows]
  | commit W k ih => intro P cs h; cases P <;> simp_all [Follows]
  | query k ih =>
    intro P cs h
    cases P <;> simp only [Follows] at h ⊢
    obtain ⟨rows, h1, h2⟩ := h
    exact ⟨rows, h1, ih _ _ _ h2⟩

/-- **Simulations compose along `bind`.** -/
theorem bind {R' : Commits → α → β → Prop} {R : Commits → γ → δ → Prop}
    {F : α → Script γ} {G : β → VerifierProgram δ}
    (hk : ∀ cs a b, R' cs a b → Follows R (F a) (G b) cs) :
    ∀ (H : Script α) (P : VerifierProgram β) (cs : Commits), Follows R' H P cs →
      Follows R (H.bind F) (P.bind G) cs := by
  intro H
  induction H with
  | ret a =>
    intro P cs h
    cases P <;> simp only [Follows] at h
    exact hk _ _ _ h
  | send x k ih =>
    intro P cs h
    cases P <;> simp only [Follows] at h
    exact ih _ _ h
  | sample k ih =>
    intro P cs h
    cases P <;> simp only [Follows] at h
    exact fun c ↦ ih c _ _ (h c)
  | grind k ih =>
    intro P cs h
    cases P <;> simp only [Follows] at h
    exact ih _ _ h
  | commit W k ih =>
    intro P cs h
    cases P <;> simp only [Follows] at h
    exact ⟨h.1, ih _ _ h.2⟩
  | query k ih =>
    intro P cs h
    cases P <;> simp only [Follows] at h
    obtain ⟨rows, h1, h2⟩ := h
    exact ⟨rows, h1, ih _ _ _ h2⟩

/-- Bind with the intermediate commitments and results pinned down. -/
theorem bind_of {R' : Commits → α → β → Prop} {R : Commits → γ → δ → Prop}
    {F : α → Script γ} {G : β → VerifierProgram δ} {H : Script α} {P : VerifierProgram β} {cs :
        Commits}
    (h : Follows R' H P cs) (hk : ∀ cs a b, R' cs a b → Follows R (F a) (G b) cs) :
    Follows R (H >>= F) (P >>= G) cs :=
  bind hk H P cs h

/-! ### The moves -/

theorem ret_ret {R : Commits → α → β → Prop} {a : α} {b : β} {cs : Commits} (h : R cs a b) :
    Follows R (Script.ret a) (VerifierProgram.ret b) cs := h

/-- Sending a scalar meets reading it. -/
theorem sendE_readE (x : E) (cs : Commits) :
    Follows (fun cs' _ b ↦ cs' = cs ∧ b = x) (Script.sendE x) VerifierProgram.readScalar cs := by
  simp [Follows, Script.sendE, VerifierProgram.readScalar]

/-- Sending a list meets reading as many scalars. -/
theorem sendList_readN (cs : Commits) :
    ∀ (xs : List E), Follows (fun cs' _ b ↦ cs' = cs ∧ b = xs) (Script.sendList xs)
      (VerifierProgram.readScalars xs.length) cs
  | [] => by simp [Follows, Script.sendList, VerifierProgram.readScalars]
  | x :: xs => by
    simp only [Script.sendList, List.length_cons, VerifierProgram.readScalars,
        VerifierProgram.readScalar, VerifierProgram.bind_eq,
      VerifierProgram.bind, Follows]
    rw [← Script.bind_ret (Script.sendList xs)]
    exact bind (fun cs' _ b h ↦ by rcases h with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) _ _ _
      (sendList_readN cs xs)

/-- Receiving a challenge meets sampling it. -/
theorem sampleE_sampleE (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b) Script.sampleE VerifierProgram.sampleChallenge cs := by
  simp [Follows, Script.sampleE, VerifierProgram.sampleChallenge]

/-- Receiving `n` challenges meets sampling them. -/
theorem sampleN_sampleN (cs : Commits) :
    ∀ n, Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.length = n) (Script.sampleN n)
      (VerifierProgram.sampleChallenges n) cs
  | 0 => by simp [Follows, Script.sampleN, VerifierProgram.sampleChallenges]
  | n + 1 => by
    simp only [Script.sampleN, VerifierProgram.sampleChallenges]
    refine bind_of (sampleE_sampleE cs) ?_
    rintro cs' a b ⟨rfl, rfl⟩
    refine bind_of (sampleN_sampleN cs' n) ?_
    rintro cs'' a' b' ⟨rfl, rfl, hl⟩
    simp [Follows, hl]

/-- Passing a proof of work meets checking it, a `0`-bit one being nothing on either side. -/
theorem grindBits_grindP (bits : ℕ) (cs : Commits) :
    Follows (fun cs' _ _ ↦ cs' = cs) (Script.grindBits bits)
      (VerifierProgram.grindProofOfWork bits) cs := by
  by_cases h : bits = 0 <;>
    simp [Follows, Script.grindBits, Script.grindS, VerifierProgram.grindProofOfWork, h]

/-- Committing a word of the announced width meets reading the commitment. -/
theorem commitS_commitP {ht w : ℕ} {W : Word} (hW : WellShaped w W) (cs : Commits) :
    Follows (fun cs' _ _ ↦ cs' = cs ++ [(ht, w, W)]) (Script.commitS W) (VerifierProgram.readCommitment ht w) cs := by
  simp [Follows, Script.commitS, VerifierProgram.readCommitment, hW]

/-- Receiving rows meets an opening answered from the commitments. -/
theorem queryS_queryP {i : ℕ} {ps : List ℕ} {cs : Commits} {rows : List (List K)}
    (h : answerOf cs i ps = some rows) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = rows ∧ b = rows) Script.queryS (VerifierProgram.queryOpenings i ps) cs := by
  simp [Follows, Script.queryS, VerifierProgram.queryOpenings, h]

/-- A `require` that holds is met by stopping. -/
theorem ret_require {R : Commits → α → Unit → Prop} {a : α} {c : Prop} [Decidable c] {cs : Commits}
    (hc : c) (h : R cs a ()) : Follows R (Script.ret a) (VerifierProgram.require c) cs := by
  simp [VerifierProgram.require, hc, Follows, h]

end Follows

/-! ## The run against a replayed script -/

/-- **The run against a script.** If `H₀` followed along the local history `e` is at `H`, and `H`
follows `P` from the commitments of `h₀ ++ e`, then every strategy that sends what `H₀` sends
after `h₀` runs `P` from `h₀ ++ e` to a result related by `R` to one of the script's, against every
challenge function, and commits well-shaped words on the way. -/
theorem runFrom_of_follows {α β : Type} {R : Commits → α → β → Prop} (S : Strategy)
    (chal : List Ev → E) (H₀ : Script α) (h₀ : List Ev)
    (hS : ∀ e, S.msg (h₀ ++ e) = H₀.msgAt e ∧ S.word (h₀ ++ e) = H₀.wordAt e) :
    ∀ (H : Script α) (P : VerifierProgram β) (e : List Ev), H₀.walk e = some H →
      Follows R H P (commits (h₀ ++ e)) →
      (∃ b, S.runFrom chal P (h₀ ++ e) = some b ∧ ∃ cs a, R cs a b) ∧
        S.ShapedFrom chal P (h₀ ++ e) := by
  intro H
  induction H with
  | ret a =>
    intro P e _ hf
    cases P <;> simp only [Follows] at hf
    exact ⟨⟨_, rfl, _, a, hf⟩, trivial⟩
  | send x k ih =>
    intro P e hw hf
    cases P with
    | read k' =>
      simp only [Follows] at hf
      have hx : S.msg (h₀ ++ e) = x := by rw [(hS e).1, Script.msgAt, hw]
      have hw' : H₀.walk (e ++ [Ev.read x]) = some k := by
        rw [Script.walk_append, hw]; rfl
      have hc : commits (h₀ ++ (e ++ [Ev.read x])) = commits (h₀ ++ e) := by
        simp [← List.append_assoc, commits_append, commits]
      have := ih (k' x) (e ++ [Ev.read x]) hw' (hc ▸ hf)
      simp only [← List.append_assoc] at this
      simpa only [Strategy.runFrom, Strategy.ShapedFrom, hx] using this
    | _ => simp [Follows] at hf
  | sample k ih =>
    intro P e hw hf
    cases P with
    | sample k' =>
      simp only [Follows] at hf
      set c := chal (h₀ ++ e)
      have hw' : H₀.walk (e ++ [Ev.sample c]) = some (k c) := by
        rw [Script.walk_append, hw]; rfl
      have hc : commits (h₀ ++ (e ++ [Ev.sample c])) = commits (h₀ ++ e) := by
        simp [← List.append_assoc, commits_append, commits]
      have := ih c (k' c) (e ++ [Ev.sample c]) hw' (hc ▸ hf c)
      simp only [← List.append_assoc] at this
      simpa only [Strategy.runFrom, Strategy.ShapedFrom] using this
    | _ => simp [Follows] at hf
  | grind k ih =>
    intro P e hw hf
    cases P with
    | grind b k' =>
      simp only [Follows] at hf
      have hw' : H₀.walk (e ++ [Ev.grind b]) = some k := by
        rw [Script.walk_append, hw]; rfl
      have hc : commits (h₀ ++ (e ++ [Ev.grind b])) = commits (h₀ ++ e) := by
        simp [← List.append_assoc, commits_append, commits]
      have := ih k' (e ++ [Ev.grind b]) hw' (hc ▸ hf)
      simp only [← List.append_assoc] at this
      simpa only [Strategy.runFrom, Strategy.ShapedFrom] using this
    | _ => simp [Follows] at hf
  | commit W k ih =>
    intro P e hw hf
    cases P with
    | commit ht w k' =>
      simp only [Follows] at hf
      have hW : S.word (h₀ ++ e) = W := by rw [(hS e).2, Script.wordAt, hw]
      have hw' : H₀.walk (e ++ [Ev.commit ht w W]) = some k := by
        rw [Script.walk_append, hw]; rfl
      have hc : commits (h₀ ++ (e ++ [Ev.commit ht w W])) = commits (h₀ ++ e) ++ [(ht, w, W)] := by
        simp [← List.append_assoc, commits_append, commits]
      have := ih k' (e ++ [Ev.commit ht w W]) hw' (hc ▸ hf.2)
      simp only [← List.append_assoc] at this
      simp only [Strategy.runFrom, Strategy.ShapedFrom, hW]
      exact ⟨this.1, hf.1, this.2⟩
    | _ => simp [Follows] at hf
  | query k ih =>
    intro P e hw hf
    cases P with
    | query i ps k' =>
      simp only [Follows] at hf
      obtain ⟨rows, hrows, hf⟩ := hf
      have hw' : H₀.walk (e ++ [Ev.query rows]) = some (k rows) := by
        rw [Script.walk_append, hw]; rfl
      have hc : commits (h₀ ++ (e ++ [Ev.query rows])) = commits (h₀ ++ e) := by
        simp [← List.append_assoc, commits_append, commits]
      have := ih rows (k' rows) (e ++ [Ev.query rows]) hw' (hc ▸ hf)
      simp only [← List.append_assoc] at this
      simp only [Strategy.runFrom, Strategy.ShapedFrom, answer_eq_answerOf, hrows]
      exact this
    | _ => simp [Follows] at hf

/-- The replay of a script after `n` events sends what the script sends. -/
theorem ofScript_agrees {α : Type} (H : Script α) (h₀ : List Ev) (e : List Ev) :
    (Strategy.ofScript H h₀.length).msg (h₀ ++ e) = H.msgAt e ∧
      (Strategy.ofScript H h₀.length).word (h₀ ++ e) = H.wordAt e := by
  simp [Strategy.ofScript]

/-- **A followed program runs to completion** from a history whose commitments the script was
followed from, for every challenge function, against every strategy that agrees with the
script's replay after that history. -/
theorem runFrom_of_follows' {α β : Type} {R : Commits → α → β → Prop} (S : Strategy)
    (chal : List Ev → E) {H : Script α} {P : VerifierProgram β} {h₀ : List Ev}
    (hS : ∀ e, S.msg (h₀ ++ e) = H.msgAt e ∧ S.word (h₀ ++ e) = H.wordAt e)
    (hf : Follows R H P (commits h₀)) :
    (∃ b, S.runFrom chal P h₀ = some b ∧ ∃ cs a, R cs a b) ∧ S.ShapedFrom chal P h₀ := by
  have := runFrom_of_follows S chal H h₀ hS H P [] rfl (by simpa using hf)
  simpa using this

end
end LeanVM.Protocol.Whir.Complete
