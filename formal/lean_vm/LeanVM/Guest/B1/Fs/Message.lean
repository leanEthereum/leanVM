/-
  LeanVM.Guest.B1.Fs.Message

  The interface of the opening's Fiat-Shamir functions: a message of stream words then a
  permutation, with or without a grinding nonce, and runs of challenges; what each computes on the
  carried sponge, the statement that its core IR computes it, and the Spec runs they are.
-/

module

public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Bits.MeaningP

/-!
# Messages and challenge runs (TRIAGE G, `opening_message`, `squeeze_point_from`)

The functions of `crates/rec_aggregation/guests/lean_ethereum.py` (G below) that WHIR's levels and
the level-0 OOD sample call:

| function | meaning |
| --- | --- |
| `opening_message__L{n}_L{nonce}` | `n` stream words read, absorbed and stored at `out`, then (`nonce = 1`) a grinding nonce, then the permutation; it returns that permutation's cells `0` (the next challenge) and `1` (its proof of work), its capacity and the cursor (`MeaningOpeningMessage`) |
| `squeeze_point_from__L{n}` | the first challenge given (a message's permutation drew it), `n - 1` more (`MeaningSqueezePointFrom`) |

The Spec runs (`omRun`, `omGrind_run`, `squeezePoint_run`): a message without a nonce, then a
sample, is `readScalars n` then `sampleChallenge`; with a nonce, `readScalars n` then a grind
leaves the challenge ground (`RunsToG`), which the next sample returns (`runsFromG_sample`); the
caller checks the proof of work (`grind_check` on cell `1`, `grindOk_iff`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `opening_message` -/

/-- The permutation a message's last step takes: after the words `xs` absorbed on the capacity
`cap`, the nonce's (`Fs.nonceState`), or, without one, the plain permutation of what waits. -/
def omState (cap xs : List E) (nonce : Option E) : KeccakState :=
  match nonce with
  | some nn => ((⟨cap, []⟩ : Fs).absorbAll xs dsObserve).nonceState nn
  | none => ((⟨cap, []⟩ : Fs).absorbAll xs dsObserve).perm

/-- **`opening_message(fs0..fs4, cursor, out, n, nonce)`**: the `n` stream words at the cursor,
also stored at `out`, absorbed on the carried capacity; with `nonce = 1` the word after them is a
grinding nonce, absorbed with `dsPowNonce`; then the permutation `S` (`omState`). It returns
`S`'s cells `0` and `1`, its capacity and the cursor past what it read. -/
def MeaningOpeningMessage (n nonce : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, out], rets =>
      ∃ xs : List E, xs.length = n ∧ ReadsAt rd cur xs ∧ ReadsAt rd out xs ∧
        ∃ nn : E, (nonce = 1 → LoadHolds rd cur n nn) ∧
          rets = [cellsOfState (omState [f0, f1, f2, f3, f4] xs (if nonce = 1 then some nn else none))
              false 0,
            cellsOfState (omState [f0, f1, f2, f3, f4] xs (if nonce = 1 then some nn else none))
              false 1] ++
            capOf (omState [f0, f1, f2, f3, f4] xs (if nonce = 1 then some nn else none)) ++
            [cur * gen ^ (n + nonce)]
  | _, _ => False

/-- The deployed messages: `(n, nonce)` of every `opening_message__L{n}_L{nonce}`. -/
def omDeployed : List (ℕ × ℕ) := [(1, 1), (6, 1), (8, 1), (12, 1), (20, 1), (36, 1)]

/-- `opening_message__L{n}_L{nonce}`. -/
def omName : ℕ × ℕ → String
  | (1, 1) => "opening_message__L1_L1"
  | (6, 1) => "opening_message__L6_L1"
  | (8, 1) => "opening_message__L8_L1"
  | (12, 1) => "opening_message__L12_L1"
  | (20, 1) => "opening_message__L20_L1"
  | (36, 1) => "opening_message__L36_L1"
  | _ => "opening_message"

/-- `P`'s relation at `opening_message__L{n}_L{nonce}` is its meaning, for every deployed
message. -/
def opening_message_SpecP (P : Program) : Prop :=
  ∀ p ∈ omDeployed, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (omName p) args rets ↔ MeaningOpeningMessage p.1 p.2 rd args rets

/-! ## `squeeze_point_from` -/

/-- **`squeeze_point_from(fs0..fs4, first, point, n)`**: the challenge `first`, which a
permutation already drew, then `n - 1` more from the carried capacity, stored at `point`; it
returns the capacity after them. -/
def MeaningSqueezePointFrom (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, first, point], rets =>
      ReadsAt rd point (first :: ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN (n - 1)).1) ∧
        rets = ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN (n - 1)).2.cap
  | _, _ => False

/-- The deployed `squeeze_point_from__L{n}`. -/
def spfDeployed : List ℕ := (List.range 25).map (· + 6)

/-- `squeeze_point_from__L{n}`, from `n = 6`. -/
def spfName (n : ℕ) : String :=
  ["squeeze_point_from__L6", "squeeze_point_from__L7", "squeeze_point_from__L8", "squeeze_point_from__L9", "squeeze_point_from__L10", "squeeze_point_from__L11", "squeeze_point_from__L12", "squeeze_point_from__L13", "squeeze_point_from__L14", "squeeze_point_from__L15", "squeeze_point_from__L16", "squeeze_point_from__L17", "squeeze_point_from__L18", "squeeze_point_from__L19", "squeeze_point_from__L20", "squeeze_point_from__L21", "squeeze_point_from__L22", "squeeze_point_from__L23", "squeeze_point_from__L24", "squeeze_point_from__L25", "squeeze_point_from__L26", "squeeze_point_from__L27", "squeeze_point_from__L28", "squeeze_point_from__L29", "squeeze_point_from__L30"].getD (n - 6) ""

/-- `P`'s relation at `squeeze_point_from__L{n}` is its meaning, for every deployed `n`. -/
def squeeze_point_from_SpecP (P : Program) : Prop :=
  ∀ n ∈ spfDeployed, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (spfName n) args rets ↔ MeaningSqueezePointFrom n rd args rets

/-! ## The Spec runs -/

/-- **A message without a nonce, then a sample**: the words read and absorbed, then the
permutation's challenge (`omState … none`). -/
theorem omRun (cap xs : List E) :
    RunsTo (do
        let ws ← VerifierProgram.readScalars xs.length
        let c ← VerifierProgram.sampleChallenge
        return (ws, c)) ⟨cap, []⟩ xs (xs, challengeOf (omState cap xs none))
      ⟨capOf (omState cap xs none), []⟩ := by
  have h := (runsTo_readN ⟨cap, []⟩ xs).bind (f := fun ws ↦ do
      let c ← VerifierProgram.sampleChallenge
      return (ws, c))
    ((runsTo_sampleE _).bind (f := fun c ↦ (pure (xs, c) : VerifierProgram (List E × E)))
      (runsTo_ret _ _))
  exact h.of_eq rfl (by simp) rfl rfl

/-- **A message with a nonce**: the words read and absorbed, then a grind of `bits ≠ 0` whose
proof of work passes; the permutation's challenge is left ground (`RunsToG`) at its capacity. -/
theorem omGrind_run (cap xs : List E) (nn : E) {bits : ℕ} (hb : bits ≠ 0)
    (hok : powOk bits (Keccak.lane (omState cap xs (some nn)) 2) = true) :
    RunsToG (do
        let ws ← VerifierProgram.readScalars xs.length
        VerifierProgram.grindProofOfWork bits
        return ws) ⟨cap, []⟩ (xs ++ [nn]) xs (capOf (omState cap xs (some nn)))
      (challengeOf (omState cap xs (some nn))) := by
  have h := (runsTo_readN ⟨cap, []⟩ xs).bindG (f := fun ws ↦ do
      VerifierProgram.grindProofOfWork bits
      return ws)
    (fun sp hs rest os roots ↦ by
      obtain ⟨sp', hc, e⟩ := runsToG_grind hb _ nn hok sp hs rest os roots
      refine ⟨sp', hc, ?_⟩
      rw [prog_bind_eq, run_bind, e]
      rfl)
  exact h

/-- **`n` samples** from a carried sponge (`runsTo_sampleN`), the run `squeeze_point_from`'s squeezes mirror. -/
theorem squeezePoint_run (n : ℕ) (s : Fs) :
    RunsTo (VerifierProgram.sampleChallenges n) s [] (s.squeezeN n).1 (s.squeezeN n).2 :=
  runsTo_sampleN n s

end
end LeanVM.Guest.B1
