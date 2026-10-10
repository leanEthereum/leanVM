import EthCryptographySpecs.Xmss.KeyGen

/-!
# `Xmss.Sign`

Signing.

Signing is deterministic: same key, message and epoch => same signature.

A key must never sign two different messages at one epoch.

Signing is stateless, so tracking spent epochs is the caller's job.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Grinding the randomizer -/

/-- The randomizer of one attempt: the first 24 bytes of the tweakable hash.

The seed is in the hash input, so the randomizer stays secret until signed. -/
def randomizer (pp : PublicParam) (seed : Seed) (msg : Message) (epoch : Epoch)
    (trial : Nat) : Randomness :=
  -- The attempt number sits where other call sites put a chain or level.
  (tweakHashFull pp .randomizer (UInt32.ofNat trial) epoch
    (packBytes seed ++ packBytes msg)).take RANDOMNESS_LEN

namespace Internal

/-- Try the attempts from `trial` onward, at most `fuel` of them.

Returns the first admissible randomizer with its digits. -/
def findRandomness (pp : PublicParam) (seed : Seed) (msg : Message)
    (epoch : Epoch) (trial fuel : Nat) :
    Option (Randomness × Vector (Fin CHAIN_LENGTH) V) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let rnd := randomizer pp seed msg epoch trial
    match wotsEncode pp msg rnd epoch with
    -- The first admissible attempt wins.
    | some x => some (rnd, x)
    -- Otherwise move on to the next attempt.
    | none => findRandomness pp seed msg epoch (trial + 1) fuel

end Internal

/-! ## Signing -/

/-- Sign a message at an epoch of the key's range.

# Warning

Never sign two different messages at one epoch with one secret key.

The two signatures reveal chains at two heights, which lets anyone forge.

# Errors

- The epoch is outside the key's range.
- No attempt encodes the message, which happens with low probability. -/
def sign (sk : SecretKey) (msg : Message) (epoch : Epoch) :
    Except XmssError Signature :=
  let tree := sk.tree
  let pp := tree.publicParam
  if epoch < sk.epochStart || sk.epochEnd < epoch then
    .error (.epochOutOfRange epoch sk.epochStart sk.epochEnd)
  else
    -- Step 1: grind the randomizer until the message encodes.
    let found :=
      Internal.findRandomness pp sk.seed msg epoch 0 MAX_RANDOMIZER_TRIALS
    match found with
    | none => .error (.noAdmissibleEncoding epoch)
    | some (rnd, x) => .ok {
        -- Step 2: reveal each chain at the height its digit names.
        chainElements := otsReveal pp epoch (otsSecretKey pp sk.seed epoch) x
        randomness := rnd
        -- Step 3: the co-path of the epoch's leaf.
        merklePath := tree.authPath sk.leaves epoch }

end EthCryptographySpecs.Xmss
