module

public import LeanVMCircuits.Rec.Statement
public import LeanVMCircuits.Xmss.Circuit

@[expose] public section

/-!
# leanXMSS verification over 64-bit words

The specification's `verify`, restated over the words the circuit carries: every hash is `hashWords` (RFC 7693's
BLAKE2s-256 of the little-endian bytes of whole 64-bit words) of `tweak || parameter || payload`, truncated to its
first two words. `Xmss.Spec` proves this is the specification's `verify` on the bytes of these words; `Xmss.Sound`
and `Xmss.Complete` prove the circuit accepts exactly what this accepts.
-/

namespace LeanVMCircuits.Xmss.Words

open LeanVMCircuits.Rec

abbrev W := BitVec 64

/-- A 16-byte digest as its two little-endian words. -/
abbrev Dig := W × W

/-- A tweak's first word. -/
def tweak0 (ty pos : ℕ) : W := BitVec.ofNat 64 (Circuit.tweak0 ty pos)

/-- A tweak's second word: the index in bytes 12 to 15. -/
def tweak1 (idx : ℕ) : W := BitVec.ofNat 64 (idx % 2 ^ 32 * 2 ^ 32)

/-- The tweak hash of `payload` at type `ty`, position `pos`, index `idx`, under parameter `pp`: the first two words of
BLAKE2s-256 of `tweak || pp || payload`. -/
def th (ty pos idx : ℕ) (pp : Dig) (payload : List W) : Dig :=
  let d := digest (hashWords ([tweak0 ty pos, tweak1 idx, pp.1, pp.2] ++ payload))
  (d 0, d 1)

/-- Digit `r` of a word: its bits `3r`, `3r + 1`, `3r + 2`. -/
def digit (w : W) (r : ℕ) : ℕ := w.toNat / 2 ^ (3 * r) % 8

/-- The 42 digits of a digest: 21 from each word. -/
def digits (d : Dig) : List ℕ :=
  (List.range 42).map fun i => digit (if i < 21 then d.1 else d.2) (i % 21)

/-- The message's encoding: its digits when bit 63 of both words is zero and they sum to 195. -/
def encode (pp : Dig) (msg : W × W × W × W) (rho : W × W × W) (epoch : ℕ) : Option (List ℕ) :=
  let d := th 4 0 epoch pp [msg.1, msg.2.1, msg.2.2.1, msg.2.2.2, rho.1, rho.2.1, rho.2.2, 0]
  if d.1.getLsbD 63 = false ∧ d.2.getLsbD 63 = false ∧ (digits d).sum = 195 then some (digits d) else none

/-- One step of chain `i`, leaving position `s`. -/
def chainStep (i s epoch : ℕ) (pp v : Dig) : Dig := th 1 (8 * i + s) epoch pp [v.1, v.2]

/-- Chain `i` from position `start` to position 7. -/
def chainFrom (i epoch : ℕ) (pp : Dig) (start : ℕ) (v : Dig) : Dig :=
  (List.range' start (7 - start)).foldl (fun v s => chainStep i s epoch pp v) v

/-- The leaf of the chains' ends. -/
def leaf (epoch : ℕ) (pp : Dig) (ends : List Dig) : Dig :=
  th 2 0 epoch pp (ends.flatMap fun d => [d.1, d.2])

/-- The parent at level `l + 1` of `cur` and its sibling `sib`, bit `l` of the epoch naming the side of `cur`. -/
def parent (epoch l : ℕ) (pp cur sib : Dig) : Dig :=
  if epoch.testBit l then th 3 (l + 1) (epoch / 2 ^ (l + 1)) pp [sib.1, sib.2, cur.1, cur.2]
  else th 3 (l + 1) (epoch / 2 ^ (l + 1)) pp [cur.1, cur.2, sib.1, sib.2]

/-- The root a path climbs to from a leaf, leaf first. -/
def climb (epoch : ℕ) (pp : Dig) (path : Fin 32 → Dig) (leaf : Dig) : Dig :=
  (List.finRange 32).foldl (fun cur (l : Fin 32) => parent epoch l.val pp cur (path l)) leaf

/-- A signature as words. -/
structure Sig where
  tips : Fin 42 → Dig
  rho : W × W × W
  path : Fin 32 → Dig

/-- Verification over words: the encoding exists and the chains' leaf climbs to the root. -/
def verify (pp root : Dig) (msg : W × W × W × W) (epoch : ℕ) (sig : Sig) : Bool :=
  match encode pp msg sig.rho epoch with
  | none => false
  | some x =>
    let ends := List.ofFn fun i : Fin 42 => chainFrom i epoch pp (x.getD i 0) (sig.tips i)
    climb epoch pp sig.path (leaf epoch pp ends) == root

end LeanVMCircuits.Xmss.Words
