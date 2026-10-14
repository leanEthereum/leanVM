import Whir.PCSBCSSourceFrozenAccessor

/-! Full strict source prefixes use a separately validated accessor for each
query/root role. Chronological Pending storage and schedule arrays are built
once; there is no current/future reply padding and no oracle warming. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceFrozenReplies
open Concrete Protocol CausalGame CausalProbability WHIRHistory FiatShamirGame
open PCSBCSSourceReplyInversion PCSBCSSourceFrozenAccessor AnchoredHeaderCodec

variable {c : Config}

def inverseIndexed (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (stages : Array (Coordinate c)) (chronological : Array Pending) (n : Nat) :
    Option Inverted := do
  let q ← stages[n]?
  let m ← chronological[n+1]?
  let accessor ← build current saved registry messages past q m
  inverse (oracles accessor) q (stage q) m

def collect (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (stages : Array (Coordinate c)) (chronological : Array Pending) :
    Nat → Nat → Array Reply → Option (Array Reply)
  | 0, _, out => some out
  | count+1, n, out => do
    let reply ← inverseIndexed current saved registry messages past stages chronological n
    collect current saved registry messages past stages chronological count (n+1) (out.push reply.reply)

def replies (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current) : Option (Array Reply) :=
  collect current saved registry messages past (schedule c).toArray messages.reverse.toArray
    (position current) 0 #[]

/-- The cached-array inverse is literally the validated source accessor path. -/
theorem inverseIndexed_eq (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current) (n : Nat) :
    inverseIndexed current saved registry messages past (schedule c).toArray
      messages.reverse.toArray n =
      PCSBCSSourceFrozenAccessor.inverseAt current saved registry messages past n := by
  simp only [inverseIndexed,PCSBCSSourceFrozenAccessor.inverseAt,List.getElem?_toArray]

/-- A malformed earlier reply fails the actual whole-prefix constructor. -/
theorem collect_rejects_first (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (stages : Array (Coordinate c)) (chronological : Array Pending) (count n : Nat)
    (out : Array Reply)
    (missing : inverseIndexed current saved registry messages past stages chronological n = none) :
    collect current saved registry messages past stages chronological (count+1) n out = none := by
  simp only [collect,missing]
  rfl

/-- Successful assembly retains exactly the requested earlier reply count. -/
theorem collect_size (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (stages : Array (Coordinate c)) (chronological : Array Pending) (count n : Nat)
    (out result : Array Reply)
    (collected : collect current saved registry messages past stages chronological count n out = some result) :
    result.size = out.size+count := by
  induction count generalizing n out with
  | zero => cases Option.some.inj collected; omega
  | succ count ih =>
    simp only [collect] at collected
    obtain ⟨reply,_,rest⟩ := Option.bind_eq_some_iff.mp collected
    have size := ih (n+1) (out.push reply.reply) rest
    simp only [Array.size_push] at size
    omega

theorem replies_size (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (result : Array Reply) (parsed : replies current saved registry messages past = some result) :
    result.size = position current := by
  have size := collect_size current saved registry messages past (schedule c).toArray
    messages.reverse.toArray (position current) 0 #[] result parsed
  simpa only [Array.size_empty,Nat.zero_add] using size

/-- Assembly never replaces an already retained reply. -/
theorem collect_preserves (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (stages : Array (Coordinate c)) (chronological : Array Pending) (count n : Nat)
    (out result : Array Reply)
    (parsed : collect current saved registry messages past stages chronological count n out = some result)
    (j : Nat) (earlier : j < out.size) : result[j]? = out[j]? := by
  induction count generalizing n out result with
  | zero =>
    simp only [collect] at parsed
    cases Option.some.inj parsed
    rfl
  | succ count ih =>
    cases hi : inverseIndexed current saved registry messages past stages chronological n with
    | none => simp [collect,hi] at parsed
    | some reply =>
      have continued : collect current saved registry messages past stages chronological count
          (n+1) (out.push reply.reply) = some result := by
        simpa [collect,hi] using parsed
      have indexBound : j < (out.push reply.reply).size := by
        simp only [Array.size_push]
        omega
      rw [ih (n+1) (out.push reply.reply) result continued indexBound]
      simp [Array.getElem?_push,Nat.ne_of_lt earlier]

/-- Every appended reply is the checked inverse at its chronological protocol
index, including repeated query positions. -/
theorem collect_index (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (stages : Array (Coordinate c)) (chronological : Array Pending) (count n : Nat)
    (out result : Array Reply)
    (parsed : collect current saved registry messages past stages chronological count n out = some result)
    (j : Nat) (earlier : j < count) :
    (inverseIndexed current saved registry messages past stages chronological (n+j)).map Inverted.reply =
      result[out.size+j]? := by
  induction count generalizing n out result j with
  | zero => omega
  | succ count ih =>
    cases hi : inverseIndexed current saved registry messages past stages chronological n with
    | none => simp [collect,hi] at parsed
    | some reply =>
      have continued : collect current saved registry messages past stages chronological count
          (n+1) (out.push reply.reply) = some result := by
        simpa [collect,hi] using parsed
      cases j with
      | zero =>
        simp only [Nat.add_zero,hi,Option.map_some]
        rw [collect_preserves current saved registry messages past stages chronological count
          (n+1) (out.push reply.reply) result continued out.size (by simp)]
        simp
      | succ j =>
        have before : j < count := by omega
        simpa only [Array.size_push,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          ih (n+1) (out.push reply.reply) result continued j before

theorem replies_index (current : Coordinate c) (saved : Record) (registry : Captures)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (result : Array Reply) (parsed : replies current saved registry messages past = some result)
    (j : Nat) (earlier : j < position current) :
    (PCSBCSSourceFrozenAccessor.inverseAt current saved registry messages past j).map Inverted.reply =
      result[j]? := by
  have index := collect_index current saved registry messages past (schedule c).toArray
    messages.reverse.toArray (position current) 0 #[] result parsed j earlier
  simpa only [Array.size_empty,Nat.zero_add,inverseIndexed_eq] using index

#print axioms collect_preserves
#print axioms collect_index
#print axioms replies_index

#print axioms inverseIndexed_eq
#print axioms collect_rejects_first
#print axioms collect_size
#print axioms replies_size
end Whir.PCSBCSSourceFrozenReplies
