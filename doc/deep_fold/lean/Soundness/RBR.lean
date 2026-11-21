/-
Round-by-round soundness of a public-coin protocol, abstractly.

This is the definition recalled in Section 2.2 of the paper (that of the leanVM specification,
after Canetti, Chen, Holmgren, Lombardi, Rothblum, Rothblum and Rothblum 2019) and the fact that
the interactive soundness error is then at most the sum of the errors, for a protocol given as a
transition system.

A protocol is seen from the outside: a *position* is what the messages so far determine (the
partial transcript, or any function of it that fixes the rest of the protocol), at a position the
prover sends a message and the verifier answers with a uniform element of a finite type, and the
two lead to the next position. Nothing is assumed about how positions are represented, so the
types of the messages may depend on the position. A protocol that has ended stays where it is.

Nothing here knows of polynomials. `Soundness/ProtocolD.lean` instantiates it.
-/
import Protocol.Potential

open Finset
open scoped Classical

namespace Soundness

open Protocol (avg dens avg_mono avg_add avg_const dens_eq_avg avg_nonneg)

universe u v w

/-- A public-coin protocol as a transition system. `Pos` are the positions (partial transcripts
that end with a verifier message, or the empty one), `Msg s` the messages the prover may send at
`s`, `Chal s` the verifier's messages at `s`, of which it sends a uniform one, and `next` the
position they lead to. -/
structure PublicCoin where
  /-- The positions. -/
  Pos : Type u
  /-- The prover's messages at a position. -/
  Msg : Pos → Type v
  /-- The verifier's messages at a position, sampled uniformly. -/
  Chal : Pos → Type w
  /-- The verifier's messages at a position are finitely many. -/
  [chalFintype : ∀ s, Fintype (Chal s)]
  /-- The position after one round. -/
  next : ∀ s, Msg s → Chal s → Pos

attribute [instance] PublicCoin.chalFintype

namespace PublicCoin

variable (Γ : PublicCoin.{u, v, w})

/-- A prover strategy for `n` rounds from the position `s`: a message at `s` and, for every
verifier message, a strategy for the `n - 1` rounds that follow. It is deterministic and may
depend on everything the verifier has sent. -/
def Strategy : ℕ → Γ.Pos → Type (max v w)
  | 0, _ => PUnit
  | n + 1, s => (p : Γ.Msg s) × (∀ c : Γ.Chal s, Strategy n (Γ.next s p c))

/-- The probability, over the verifier's `n` messages, that the position reached from `s` by the
strategy `σ` satisfies `win`. -/
noncomputable def winProb (win : Γ.Pos → Prop) : ∀ (n : ℕ) (s : Γ.Pos), Γ.Strategy n s → ℚ
  | 0, s, _ => if win s then 1 else 0
  | n + 1, s, σ => avg (fun c => winProb win n (Γ.next s σ.1 c) (σ.2 c))

theorem winProb_zero (win : Γ.Pos → Prop) (s : Γ.Pos) (σ : Γ.Strategy 0 s) :
    Γ.winProb win 0 s σ = if win s then 1 else 0 := rfl

theorem winProb_succ (win : Γ.Pos → Prop) (n : ℕ) (s : Γ.Pos) (σ : Γ.Strategy (n + 1) s) :
    Γ.winProb win (n + 1) s σ = avg (fun c => Γ.winProb win n (Γ.next s σ.1 c) (σ.2 c)) := rfl

theorem winProb_nonneg (win : Γ.Pos → Prop) :
    ∀ (n : ℕ) (s : Γ.Pos) (σ : Γ.Strategy n s), 0 ≤ Γ.winProb win n s σ
  | 0, s, σ => by
      rw [winProb_zero]
      split_ifs <;> norm_num
  | n + 1, s, σ => by
      rw [winProb_succ]
      exact avg_nonneg fun c => winProb_nonneg win n _ _

theorem winProb_le_one (win : Γ.Pos → Prop) :
    ∀ (n : ℕ) (s : Γ.Pos) (σ : Γ.Strategy n s), Γ.winProb win n s σ ≤ 1
  | 0, s, σ => by
      rw [winProb_zero]
      split_ifs <;> norm_num
  | n + 1, s, σ => by
      rw [winProb_succ]
      rcases isEmpty_or_nonempty (Γ.Chal s) with hemp | hne
      · simp [avg]
      · exact (avg_mono fun c => winProb_le_one win n _ _).trans_eq (avg_const 1)

/-- A larger winning condition is won at least as often. -/
theorem winProb_mono {win win' : Γ.Pos → Prop} (h : ∀ s, win s → win' s) :
    ∀ (n : ℕ) (s : Γ.Pos) (σ : Γ.Strategy n s), Γ.winProb win n s σ ≤ Γ.winProb win' n s σ
  | 0, s, σ => by
      rw [winProb_zero, winProb_zero]
      by_cases hw : win s
      · simp [hw, h s hw]
      · simp only [hw, ite_false]
        split_ifs <;> norm_num
  | n + 1, s, σ => by
      rw [winProb_succ, winProb_succ]
      exact avg_mono fun c => winProb_mono h n _ _

/-- Strategies exist: if a set `R` of positions is closed under the rounds and the prover has a
message at each of its positions, then from every position of `R` there is a strategy for every
number of rounds. So a bound "for every strategy" from such a position is not about an empty
set. -/
theorem strategy_nonempty (R : Γ.Pos → Prop) (hmsg : ∀ s, R s → Nonempty (Γ.Msg s))
    (hnext : ∀ s (p : Γ.Msg s) (c : Γ.Chal s), R s → R (Γ.next s p c)) :
    ∀ (n : ℕ) (s : Γ.Pos), R s → Nonempty (Γ.Strategy n s)
  | 0, _, _ => ⟨PUnit.unit⟩
  | n + 1, s, hs => by
      obtain ⟨p⟩ := hmsg s hs
      exact ⟨⟨p, fun c => (strategy_nonempty R hmsg hnext n _ (hnext s p c hs)).some⟩⟩

end PublicCoin

/-- **A state function** of a public-coin protocol (Section 2.2 of the paper): the predicate
`doomed` on positions, with its value `doomedP` after a prover message, is a round-by-round state
function for the starting condition `start`, the winning condition `win` and the errors `err`, one
for the verifier message sent from each position, if

- (i) a starting position is doomed (in the leanVM specification: "on a false statement, the
  invariant holds before any message is sent");
- (ii) no prover message leaves the doomed set;
- (iii) from a doomed position, the verifier's message leaves the doomed set with probability at
  most the error of that message;
- (iv) at a doomed position the prover has not won (in the leanVM specification: "if it survives
  to the end of the interaction, the verifier rejects"; `win` is false at positions where the
  protocol has not ended). -/
structure StateFunction (Γ : PublicCoin.{u, v, w}) (start win : Γ.Pos → Prop) (err : Γ.Pos → ℚ)
    (doomed : Γ.Pos → Prop) (doomedP : ∀ s, Γ.Msg s → Prop) : Prop where
  /-- (i) -/
  start_doomed : ∀ s, start s → doomed s
  /-- (ii) -/
  prover_doomed : ∀ s (p : Γ.Msg s), doomed s → doomedP s p
  /-- (iii) -/
  verifier_doomed : ∀ s (p : Γ.Msg s), doomedP s p →
    dens (fun c : Γ.Chal s => ¬ doomed (Γ.next s p c)) ≤ err s
  /-- (iv) -/
  doomed_not_win : ∀ s, doomed s → ¬ win s

/-- **Round-by-round soundness** (Section 2.2 of the paper): the protocol has a state function for
the starting condition, the winning condition and the errors. -/
def RBRSound (Γ : PublicCoin.{u, v, w}) (start win : Γ.Pos → Prop) (err : Γ.Pos → ℚ) : Prop :=
  ∃ (doomed : Γ.Pos → Prop) (doomedP : ∀ s, Γ.Msg s → Prop),
    StateFunction Γ start win err doomed doomedP

/-- A mean is at most the probability of an event plus `b`, if the function is at most `1 + b`
on the event and at most `b` off it. -/
theorem avg_le_dens_add {α : Type*} [Fintype α] [Nonempty α] (f : α → ℚ) (p : α → Prop) (b : ℚ)
    (h1 : ∀ a, p a → f a ≤ 1 + b) (h2 : ∀ a, ¬ p a → f a ≤ b) : avg f ≤ dens p + b := by
  rw [dens_eq_avg, ← avg_const (α := α) b, ← avg_add]
  refine avg_mono fun a => ?_
  by_cases hp : p a
  · simp only [hp, ite_true]
    exact h1 a hp
  · simp only [hp, ite_false, zero_add]
    exact h2 a hp

variable {Γ : PublicCoin.{u, v, w}} {start win : Γ.Pos → Prop} {err : Γ.Pos → ℚ}

/-- A state function whose value does not change with the prover's message: (ii) holds by
definition, and (iii) reads "from a doomed position, whatever the prover sends". This is the shape
of the state of Section 5.3 of the paper, every condition of which is "a function of the transcript
up to the last verifier message". -/
theorem StateFunction.of_positions {doomed : Γ.Pos → Prop} (h1 : ∀ s, start s → doomed s)
    (h3 : ∀ s (p : Γ.Msg s), doomed s →
      dens (fun c : Γ.Chal s => ¬ doomed (Γ.next s p c)) ≤ err s)
    (h4 : ∀ s, doomed s → ¬ win s) :
    StateFunction Γ start win err doomed (fun s _ => doomed s) :=
  ⟨h1, fun _ _ h => h, h3, h4⟩

/-- A state function for smaller errors and a larger winning condition is one for larger errors
and a smaller winning condition. -/
theorem StateFunction.mono {doomed : Γ.Pos → Prop} {doomedP : ∀ s, Γ.Msg s → Prop}
    (h : StateFunction Γ start win err doomed doomedP) {win' : Γ.Pos → Prop} {err' : Γ.Pos → ℚ}
    (hw : ∀ s, win' s → win s) (he : ∀ s, err s ≤ err' s) :
    StateFunction Γ start win' err' doomed doomedP :=
  ⟨h.start_doomed, h.prover_doomed, fun s p hp => (h.verifier_doomed s p hp).trans (he s),
    fun s hd hwin => h.doomed_not_win s hd (hw s hwin)⟩

/-- **The union bound over the rounds.** Let `doomed` be a state function with errors `err`, and
let `E n s` be a budget for `n` rounds from `s`: nonnegative, and at least the error of the
message sent from `s` plus the budget of the position that follows, whatever is sent. Then from a
doomed position every prover strategy wins the `n`-round game with probability at most `E n s`. -/
theorem StateFunction.winProb_le {doomed : Γ.Pos → Prop} {doomedP : ∀ s, Γ.Msg s → Prop}
    (h : StateFunction Γ start win err doomed doomedP) (E : ℕ → Γ.Pos → ℚ)
    (hE0 : ∀ n s, 0 ≤ E n s)
    (hE : ∀ n s (p : Γ.Msg s) (c : Γ.Chal s), err s + E n (Γ.next s p c) ≤ E (n + 1) s) :
    ∀ (n : ℕ) (s : Γ.Pos) (σ : Γ.Strategy n s), doomed s → Γ.winProb win n s σ ≤ E n s
  | 0, s, σ, hd => by
      rw [PublicCoin.winProb_zero]
      simp only [h.doomed_not_win s hd, ite_false]
      exact hE0 0 s
  | n + 1, s, σ, hd => by
      rw [PublicCoin.winProb_succ]
      rcases isEmpty_or_nonempty (Γ.Chal s) with hemp | hne
      · have h0 : avg (fun c => Γ.winProb win n (Γ.next s σ.1 c) (σ.2 c)) = 0 := by
          simp [avg]
        rw [h0]
        exact hE0 (n + 1) s
      · obtain ⟨c₀⟩ := id hne
        have hv := h.verifier_doomed s σ.1 (h.prover_doomed s σ.1 hd)
        have hb : 0 ≤ E (n + 1) s - err s := by
          linarith [hE n s σ.1 c₀, hE0 n (Γ.next s σ.1 c₀)]
        refine (avg_le_dens_add _ (fun c : Γ.Chal s => ¬ doomed (Γ.next s σ.1 c))
          (E (n + 1) s - err s) ?_ ?_).trans (by linarith)
        · intro c _
          linarith [Γ.winProb_le_one win n _ (σ.2 c)]
        · intro c hdc
          linarith [StateFunction.winProb_le h E hE0 hE n _ (σ.2 c) (not_not.mp hdc),
            hE n s σ.1 c]

/-- **Round-by-round soundness gives soundness.** If the protocol is round-by-round sound with
errors `err` and `E` is a budget (as in `StateFunction.winProb_le`), then from every starting
position every prover strategy wins the `n`-round game with probability at most `E n s`. -/
theorem RBRSound.winProb_le (h : RBRSound Γ start win err) (E : ℕ → Γ.Pos → ℚ)
    (hE0 : ∀ n s, 0 ≤ E n s)
    (hE : ∀ n s (p : Γ.Msg s) (c : Γ.Chal s), err s + E n (Γ.next s p c) ≤ E (n + 1) s)
    (n : ℕ) (s : Γ.Pos) (σ : Γ.Strategy n s) (hs : start s) : Γ.winProb win n s σ ≤ E n s := by
  obtain ⟨doomed, doomedP, hsf⟩ := h
  exact hsf.winProb_le E hE0 hE n s σ (hsf.start_doomed s hs)

/-- The same when every message has error at most `ε`: at most `n ε` after `n` rounds. -/
theorem RBRSound.winProb_le_mul (h : RBRSound Γ start win err) {ε : ℚ} (hε : 0 ≤ ε)
    (herr : ∀ s, err s ≤ ε) (n : ℕ) (s : Γ.Pos) (σ : Γ.Strategy n s) (hs : start s) :
    Γ.winProb win n s σ ≤ n * ε := by
  refine h.winProb_le (fun n _ => n * ε) (fun n _ => by positivity) (fun n s p c => ?_) n s σ hs
  have := herr s
  push_cast
  linarith

end Soundness
