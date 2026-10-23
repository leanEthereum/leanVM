import LeanVM.Protocol.Compile.Prover

/-!
# Honest prover tests

A tiny verifier program: read one scalar, commit a two-row matrix of two-word rows, check a
three-bit proof of work, sample a challenge, open the matrix at the position the challenge's
first limb names, and accept iff the opened row is the strategy's row at that position. The
honest prover at BLAKE2s produces a proof the compiled verifier accepts (`#guard`, compiled), and
the completeness theorem, instantiated with the interactive completeness and shape proofs of the
strategy, says so for every proof the prover can produce. Then the load-bearing checks: a
tampered leaf, a tampered sibling, the other row, a tampered root scalar, an opening missing and
an extra scalar are rejected, and so is the honest proof of a strategy that loses
interactively; a fuel too small for the proof-of-work search makes the prover fail, while a
zero-bit proof of work needs no fuel; the nonce found is the smallest that passes.
-/

namespace LeanVMTests.Protocol.Compile.Prover

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Blake2sHash

/-- The word `n`. -/
def w (n : ℕ) : K := K.ofBits n

/-- The committed matrix: two rows of two words, read modulo two. -/
def word0 : Word := fun p ↦ if p % 2 = 0 then [w 5, w 6] else [w 7, w 8]

/-- The position a challenge names: its first limb as a number. -/
def pos (c : E) : ℕ := (c.limb 0).toBitVec.toNat

/-- The verifier after the proof of work, with `bits` bits of work. -/
def prog (bits : ℕ) : Prog Bool :=
  .read fun _ ↦ .commit 1 2 (.grind bits (.sample fun c ↦
    .query 0 [pos c] fun rows ↦ .ret (decide (rows = [word0 (pos c % 2)]))))

/-- The honest strategy: the scalar `3`, then `word0`. -/
def strat : Strategy where
  msg := fun _ ↦ E.ofLimbs (w 3) 0 0
  word := fun _ ↦ word0

/-- The seed of the chain. -/
def seed : Digest := blake2sBytes [0x6c, 0x65, 0x61, 0x6e]

/-! ## Interactive completeness -/

theorem complete (bits : ℕ) (chal : List Ev → E) : runI (prog bits) strat chal = some true := by
  simp [runI, Strategy.runFrom, prog, strat, answer, commits]

theorem shaped (bits : ℕ) (chal : List Ev → E) : shapedI (prog bits) strat chal := by
  simp only [shapedI, Strategy.ShapedFrom, prog, strat, answer]
  refine ⟨fun p ↦ ?_, trivial⟩
  unfold word0
  split <;> rfl

/-! ## The honest proof is accepted -/

/-- The honest proof with a three-bit proof of work and a search of at most 1000 nonces. -/
def proof? : Option Proof := prove blake2sBytes (prog 3) strat seed 1000

/-- Accept a possibly missing proof. -/
def accepts (bits : ℕ) : Option Proof → Bool
  | some π => runProof (m := Id) blake2sBytes (prog bits) seed π
  | none => false

#guard proof?.isSome
#guard accepts 3 proof?
#guard proof?.map (·.stream.length) = some 4
#guard proof?.map (·.openings.length) = some 1

/-- Completeness at BLAKE2s: every proof the prover produces is accepted. -/
theorem proof_accepted {π : Proof} (h : proof? = some π) :
    runProof (m := Id) blake2sBytes (prog 3) seed π = true :=
  runProof_prove blake2sBytes (prog 3) strat seed 1000 (complete 3) (shaped 3) h

/-! ## The nonce is the smallest that passes -/

/-- The chain state at the proof of work: after the scalar and the root's two scalars. -/
def grindState (π : Proof) : Digest :=
  π.stream.take 3 |>.foldl (fun cv x ↦ blake2sBytes (digestBytes cv ++ blockOf x 1)) seed

/-- The nonce is the first `m` below the fuel that passes, and every smaller `m` fails. -/
def smallestNonce (π : Proof) : Bool :=
  let ok := fun m ↦ powOk 3 (nonceOf m) (powDigest blake2sBytes (grindState π) (nonceOf m))
  match (List.range 1000).find? ok with
  | some m => π.stream[3]? == some (nonceOf m) && ok m && (List.range m).all (! ok ·)
  | none => false

#guard proof?.map smallestNonce == some true

/-! ## Mutations rejected -/

/-- Replace the first opening. -/
def mapOpening (f : Opening → Opening) (π : Proof) : Proof :=
  { π with openings := π.openings.modifyHead f }

/- A tampered leaf word. -/
#guard !accepts 3 (proof?.map (mapOpening fun o ↦ { o with leaf := o.leaf.modifyHead (· + 1) }))

/- A tampered sibling. -/
#guard !accepts 3 (proof?.map (mapOpening fun o ↦
  { o with path := o.path.modifyHead fun d ↦ d.set 0 (d[0] + 1) }))

/- The other row in place of the opened one, with the opened row's path. -/
#guard !accepts 3 (proof?.map (mapOpening fun o ↦
  { o with leaf := if o.leaf = word0 0 then word0 1 else word0 0 }))

/-- A strategy that commits another matrix: interactively it loses, since the row it opens is not
`word0`'s. -/
def badStrat : Strategy where
  msg := strat.msg
  word := fun _ _ ↦ [w 9, w 9]

/- Its honest proof authenticates, and the verdict rejects. -/
#guard (prove blake2sBytes (prog 3) badStrat seed 1000).isSome
#guard !accepts 3 (prove blake2sBytes (prog 3) badStrat seed 1000)

/- A tampered root scalar. -/
#guard !accepts 3 (proof?.map fun π ↦ { π with stream := π.stream.modify 1 (· + 1) })

/- An opening missing. -/
#guard !accepts 3 (proof?.map fun π ↦ { π with openings := [] })

/- An extra scalar at the end. -/
#guard !accepts 3 (proof?.map fun π ↦ { π with stream := π.stream ++ [0] })

/-! ## When the prover fails -/

/- No nonce below the fuel: the three-bit search with no fuel fails. -/
#guard (prove blake2sBytes (prog 3) strat seed 0).isNone

/- A zero-bit proof of work needs no fuel: the nonce is `0`. -/
#guard accepts 0 (prove blake2sBytes (prog 0) strat seed 0)

/-- The search fails exactly when no nonce below the fuel passes. -/
example (cv : Digest) : findNonce blake2sBytes 3 cv 0 = none :=
  (findNonce_eq_none_iff blake2sBytes 3 cv 0).mpr ⟨by decide, fun _ h ↦ absurd h (by omega)⟩

end LeanVMTests.Protocol.Compile.Prover
