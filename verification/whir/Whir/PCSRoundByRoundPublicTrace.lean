import Whir.PCSRoundByRoundTranscriptReplay
import Whir.RingPCSGame

/-! A public verifier-message boundary contains the observed ring prefix, the
observed challenge coordinates, and strictly prior prover replies. Future
coordinates are absent, not hidden fields of a stored tape. -/
namespace Whir.PCSRoundByRoundTranscriptState
open Concrete Protocol CausalGame CausalProbability CausalPositions

set_option autoImplicit false

structure PublicTrace (c : Config) where
  ring : Option RingPCSGame.Prefix
  samples : (q : Coordinate c) → Option (Sample q)
  answers : Array Reply

def PublicTrace.initial (c : Config) : PublicTrace c :=
  ⟨none, fun _ => none, #[]⟩

def PublicTrace.tape {c : Config} (trace : PublicTrace c) : Tape c :=
  (coordinates c).symm (fun q => (trace.samples q).getD 0)

@[simp] theorem PublicTrace.get_tape {c : Config} (trace : PublicTrace c)
    (q : Coordinate c) : get q trace.tape = (trace.samples q).getD 0 := by
  change ((coordinates c) ((coordinates c).symm _)) q = _
  rw [Equiv.apply_symm_apply]

def priorAnswers (answers : Array Reply) (length : Nat) : Array Reply :=
  Array.ofFn (fun n : Fin length => answers[n.val]!)

@[simp] theorem priorAnswers_get (answers : Array Reply) (length n : Nat)
    (bound : n < length) : (priorAnswers answers length)[n]! = answers[n]! := by
  simp [priorAnswers, getElem!_pos, bound]

def snapshot {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q : Coordinate c) : PublicTrace c :=
  ⟨some ring, (fun r => if position r ≤ position q then some (get r t) else none),
    priorAnswers answers (position q)⟩

@[simp] theorem snapshot_ring {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q : Coordinate c) : (snapshot ring t answers q).ring = some ring := rfl

theorem snapshot_observed {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q r : Coordinate c) (observed : position r ≤ position q) :
    get r (snapshot ring t answers q).tape = get r t := by
  simp [snapshot, observed]

theorem snapshot_unobserved {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q r : Coordinate c) (future : position q < position r) :
    (snapshot ring t answers q).samples r = none := by
  simp [snapshot, Nat.not_le.mpr future]

theorem snapshot_reply {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q : Coordinate c) (n : Nat) (prior : n < position q) :
    (snapshot ring t answers q).answers[n]! = answers[n]! :=
  priorAnswers_get answers (position q) n prior

theorem prefix_event_congr {c : Config} (event : Tape c → Prop) (q : Coordinate c)
    (invariant : ∀ r t (x : Sample r), position q < position r →
      (event (set r t x) ↔ event t))
    (t u : Tape c) (same : ∀ r, position r ≤ position q → get r t = get r u) :
    event t ↔ event u := by
  let predicate := fun f : (r : Coordinate c) → Sample r => event ((coordinates c).symm f)
  have step : ∀ f r, ¬ position r ≤ position q → ∀ x,
      predicate (Function.update f r x) ↔ predicate f := by
    intro f r future x
    have replaced : (coordinates c).symm (Function.update f r x) =
        set r ((coordinates c).symm f) x := by
      simp only [CausalProbability.set, Equiv.apply_symm_apply]
    dsimp only [predicate]
    rw [replaced]
    exact invariant r _ x (Nat.lt_of_not_ge future)
  have result := CausalPrefix.finite_pred_congr predicate (fun r => position r ≤ position q)
    step (coordinates c t) (coordinates c u) same
  simpa only [predicate, Equiv.symm_apply_apply] using result

#print axioms PublicTrace.get_tape
#print axioms priorAnswers_get
#print axioms snapshot_observed
#print axioms snapshot_unobserved
#print axioms snapshot_reply
#print axioms prefix_event_congr
end Whir.PCSRoundByRoundTranscriptState
