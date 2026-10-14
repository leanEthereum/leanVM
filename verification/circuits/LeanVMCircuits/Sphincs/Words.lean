module

public import LeanVMCircuits.Rec.Statement
public import LeanVMCircuits.Sphincs.Circuit
public import LeanVMCircuits.Xmss.Words

@[expose] public section

/-!
# leanSPHINCS verification over 64-bit words

The specification's `LeanSphincs.verify`, restated over the words the circuit carries: every hash but the encoding
is `hashWords` (RFC 7693's BLAKE2s-256 of the little-endian bytes of whole 64-bit words) of
`tweak || parameter || payload`, truncated to its first two words; the encoding is BLAKE2s-256 of the first 52 bytes
of `tweak || parameter || message || counter`, one block, with the counter's word below `2^32`. A later module is to
prove this is the specification's `verify` on the bytes of these words, and others that the circuit
`Sphincs.Circuit.circuit` accepts exactly what this accepts.
-/

namespace LeanVMCircuits.Sphincs.Words

open LeanVMCircuits.Rec
open LeanVMCircuits.Xmss.Words (W Dig)

/-- A tweak as its two words: `1 | type << 8 | lay << 16 | p << 32` and `tau | j << 32`. -/
def tweak (ty lay tau p j : ℕ) : W × W :=
  (BitVec.ofNat 64 (Circuit.tweak0 ty lay p), BitVec.ofNat 64 (tau % 2 ^ 32 + j % 2 ^ 32 * 2 ^ 32))

/-- The tweak hash of `payload` under tweak `tw` and parameter `pp`: the first two words of BLAKE2s-256 of
`tw || pp || payload`. -/
def th (tw : W × W) (pp : Dig) (payload : List W) : Dig :=
  let d := digest (hashWords ([tw.1, tw.2, pp.1, pp.2] ++ payload))
  (d 0, d 1)

/-! ## The message digest and the few-time key -/

/-- The message digest: BLAKE2s-256 of `tweak(12) || pp || rho || root || msg`, its first three words as one
number, of which bits `0 .. 25` are the index and bits `26 + 10 kappa .. 35 + 10 kappa` leaf index `kappa`. -/
def messageDigest (pp root rho : Dig) (msg : W × W × W × W) : ℕ × (ℕ → ℕ) :=
  let d := digest (hashWords ([(tweak 12 0 0 0 0).1, (tweak 12 0 0 0 0).2, pp.1, pp.2, rho.1, rho.2, root.1, root.2,
    msg.1, msg.2.1, msg.2.2.1, msg.2.2.2]))
  let value := (d 0).toNat + 2 ^ 64 * (d 1).toNat + 2 ^ 128 * (d 2).toNat
  (value % 2 ^ 26, fun kappa => value / 2 ^ (26 + 10 * kappa) % 2 ^ 10)

/-- The parent at level `l + 1` of `cur` and its sibling `sib` in tree `tau` of type `ty` and layer or tree `lay`,
bit `l` of the leaf index `e` naming the side of `cur`. -/
def parent (ty lay tau e l : ℕ) (pp cur sib : Dig) : Dig :=
  let tw := tweak ty lay tau (l + 1) (e / 2 ^ (l + 1))
  if e.testBit l then th tw pp [sib.1, sib.2, cur.1, cur.2] else th tw pp [cur.1, cur.2, sib.1, sib.2]

/-- The root a path of `h` siblings climbs to from a leaf, leaf first. -/
def climb (ty lay tau e h : ℕ) (pp : Dig) (path : Fin h → Dig) (leaf : Dig) : Dig :=
  (List.finRange h).foldl (fun cur (l : Fin h) => parent ty lay tau e l.val pp cur (path l)) leaf

/-- Few-time tree `kappa`'s root: the leaf of its secret climbed ten levels. -/
def ftsRoot (idx kappa u : ℕ) (pp secret : Dig) (path : Fin 10 → Dig) : Dig :=
  climb 10 kappa idx u 10 pp path (th (tweak 9 kappa idx 0 u) pp [secret.1, secret.2])

/-! ## The layers -/

/-- Layer `lay`'s tree height. -/
def height (lay : Fin 3) : ℕ := Circuit.height lay.val

/-- Layer `lay`'s tree, `idx >> SUFFIX[lay]`. -/
def tau (idx : ℕ) (lay : Fin 3) : ℕ := idx / 2 ^ Circuit.suffix lay.val

/-- Layer `lay`'s leaf, `(idx >> SUFFIX[lay + 1]) mod 2^h`. -/
def leafIndex (idx : ℕ) (lay : Fin 3) : ℕ := idx / 2 ^ Circuit.suffix (lay.val + 1) % 2 ^ height lay

/-- The encoding's digest: the first two words of BLAKE2s-256 of the 52 bytes `tw || pp || msg || ctr`, one
block, the bytes of `ctr`'s word past its fourth its padding. -/
def encDigest (tw : W × W) (pp msg : Dig) (ctr : W) : Dig :=
  let d := digest (blake2s256 52 (block [tw.1, tw.2, pp.1, pp.2, msg.1, msg.2, ctr] 0) [])
  (d 0, d 1)

/-- Layer `lay`'s encoding of `msg` under the counter `ctr`: its digits when `ctr` is below `2^32`, bit 63 of both
digest words is zero, and the digits sum to 191. -/
def encode (lay tau e : ℕ) (pp msg : Dig) (ctr : W) : Option (List ℕ) :=
  let d := encDigest (tweak 4 lay tau 0 e) pp msg ctr
  let x := Xmss.Words.digits d
  if ctr.toNat < 2 ^ 32 ∧ d.1.getLsbD 63 = false ∧ d.2.getLsbD 63 = false ∧ x.sum = 191 then some x else none

/-- One step of chain `i`, leaving position `s`. -/
def chainStep (lay tau e i s : ℕ) (pp v : Dig) : Dig := th (tweak 1 lay tau (8 * i + s) e) pp [v.1, v.2]

/-- Chain `i` from position `start` to position 7. -/
def chainFrom (lay tau e i : ℕ) (pp : Dig) (start : ℕ) (v : Dig) : Dig :=
  (List.range' start (7 - start)).foldl (fun v s => chainStep lay tau e i s pp v) v

/-- The one-time leaf of the chains' ends. -/
def otsLeaf (lay tau e : ℕ) (pp : Dig) (ends : List Dig) : Dig :=
  th (tweak 2 lay tau 0 e) pp (ends.flatMap fun d => [d.1, d.2])

/-- A signature as words. -/
structure Sig where
  rho : Dig
  secrets : Fin 14 → Dig
  ftsPaths : Fin 14 → Fin 10 → Dig
  counters : Fin 3 → W
  tips : Fin 3 → Fin 42 → Dig
  paths : (lay : Fin 3) → Fin (height lay) → Dig

/-- Layer `lay`'s root from the message `msg` it signs, or nothing if its counter gives `msg` no codeword. -/
def layerRoot (pp : Dig) (idx : ℕ) (sig : Sig) (msg : Dig) (lay : Fin 3) : Option Dig :=
  let t := tau idx lay
  let e := leafIndex idx lay
  match encode lay t e pp msg (sig.counters lay) with
  | none => none
  | some x =>
    let ends := List.ofFn fun i : Fin 42 => chainFrom lay t e i pp (x.getD i 0) (sig.tips lay i)
    some (climb 3 lay t e (height lay) pp (sig.paths lay) (otsLeaf lay t e pp ends))

/-- Verification over words: the last leaf index is zero, layers 2, 1, 0 each encode the message below them (the
few-time key, then each layer's root), and the top layer's root is the key's. -/
def verify (root pp : Dig) (msg : W × W × W × W) (sig : Sig) : Bool :=
  let (idx, u) := messageDigest pp root sig.rho msg
  if u 14 ≠ 0 then false
  else
    let roots := List.ofFn fun kappa : Fin 14 => ftsRoot idx kappa (u kappa) pp (sig.secrets kappa) (sig.ftsPaths kappa)
    let key := th (tweak 11 0 idx 0 0) pp (roots.flatMap fun d => [d.1, d.2])
    match [2, 1, 0].foldlM (layerRoot pp idx sig) key with
    | none => false
    | some top => top == root

end LeanVMCircuits.Sphincs.Words
