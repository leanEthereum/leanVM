module

public import LeanVMCircuits.Xmss.Circuit

@[expose] public section

/-!
# The leanSPHINCS verifier on the recursion machine

The circuit that verifies `n` leanSPHINCS signatures in one recursion proof, written against the model of the
builder (`LeanVMCircuits.Rec.Model`), in the shape of `LeanVMCircuits.Xmss.Circuit`, whose gadgets for digests,
statement words, digit indicators and the digit product it reuses.

Every hash of the scheme is BLAKE2s-256 over `tweak || parameter || payload`. All but the encoding are whole 64-bit
words, so each is one `chain` of words, its digest truncated to its first two words (the message digest keeps three
words). A 16-byte digest travels as an `E` wire whose first two limbs are its words, so that a selection between two
digests is arithmetic in `E`. A tweak is two words: the first, `1 | type << 8 | lay << 16 | p << 32`, a constant; the
second, `tau | j << 32`, packed from the index's bits.

Per signature, the statement is four `E` words, exposed in the order the guest commits them: the key's root
`[r0, r1, 0]`, its public parameter `[p0, p1, 0]`, and the message's first and last two words `[m0, m1, 0]` and
`[m2, m3, 0]`. The signature is the prover's: the randomizer, 14 secrets with 10 siblings each, and per layer a
counter, 42 chain elements and its siblings.

* The message digest hashes `tweak(12) || p || rho || r || m`, two blocks, and splits the digest's words 0, 1 and 2
  (word 3 holds no index bit). Bits `0 .. 25` are the index `idx`, bits `26 + 10 kappa ..` leaf index `u_kappa`,
  and the bits of `u_14` are held zero.
* Few-time tree `kappa < 14` hashes its leaf `tweak(9, kappa, idx, 0, u_kappa) || p || secret` and climbs ten levels:
  level `l` hashes `tweak(10, kappa, idx, l + 1, u_kappa >> (l + 1)) || p || left || right`, the current node on the
  side bit `l` of `u_kappa` names, `left = cur + b·(cur + sib)`, `right = left + cur + sib`. The few-time key hashes
  `tweak(11, 0, idx) || p || root_0 || .. || root_13`, four blocks.
* Layers 2, 1, 0 in turn sign the message below them (the few-time key, then each layer's root). Layer `lay` uses
  the tree `tau = idx >> SUFFIX[lay]` and leaf `e = (idx >> SUFFIX[lay + 1]) mod 2^h`, `SUFFIX = [26, 14, 7, 0]`,
  `h = [12, 7, 7][lay]`.
  * The encoding hashes the 52 bytes `tweak(4, lay, tau, 0, e) || p || msg || ctr` in one `leafBlock` from the
    parameter IV with the byte count 52: the message words `[tw0, tw1, p0, p1, m0, m1, ctr, 0]`, the counter's bits
    32 to 63 held zero, so that the block's bytes past 52 are zero as BLAKE2s pads them. Bit 63 of both digest
    words is zero, digit `i` is bits `3r .. 3r+2` of word `i / 21`, `r = i % 21`, and the digits sum to 191: the
    product over every digit bit `b` of weight `2^k` of `X^(2^k)` to the power `b` is `X^191` in `K`, and `X` has
    order above 294.
  * Chain `i` hashes seven steps at positions `8i + s`, `s < 7`, the input of step `s > 0` the chain element when
    the digit is `s` and the previous step's output otherwise. The chain's end is the chain element when the digit
    is 7, the last output otherwise.
  * The leaf hashes `tweak(2, lay, tau, 0, e) || p || end_0 || .. || end_41`, eleven blocks.
  * Level `l` of the path hashes `tweak(3, lay, tau, l + 1, e >> (l + 1)) || p || left || right`, the side bit `l`
    of `e`.
* The top layer's root is the statement's.
-/

namespace LeanVMCircuits.Sphincs.Circuit

open LeanVMCircuits.Rec.Model
open LeanVMCircuits.Xmss.Circuit (words statementWords digitProduct indicators)

/-- A tweak's first word: the domain separator 1 in byte 0, the type in byte 1, the layer or tree in byte 2, the
position `p` in bytes 4 to 7. -/
def tweak0 (ty lay p : ℕ) : ℕ := 1 + ty * 2 ^ 8 + lay * 2 ^ 16 + p * 2 ^ 32

/-- `X^191` in `K` as a word: the product the digits' bits must reach. -/
def targetWord : ℕ := 0x8000000000000ed6

/-- Layer `lay`'s tree height. -/
def height (lay : ℕ) : ℕ := [12, 7, 7].getD lay 0

/-- The height of everything below layer `lay`'s top. -/
def suffix (lay : ℕ) : ℕ := [26, 14, 7, 0].getD lay 0

/-- A tweak's second word `tau | j << 32` from the bits of `tau` and `j`, low first; the constant zero when both
have none. -/
def indexWord (tau j : List ℕ) : M ℕ := do
  let z ← kConst 0
  if tau.isEmpty && j.isEmpty then pure z
  else pack (tau ++ List.replicate (32 - tau.length) z ++ j)

/-- The digest wire of the hash of `tw0 || tw1 || p || payload`, `tw0` a constant. -/
def th (tw0 tw1 : ℕ) (pp payload : List ℕ) : M ℕ := do
  let t ← kConst tw0
  chain ([t, tw1] ++ pp ++ payload)

/-- One tree level: the parent of `node` (a digest wire) and the sibling, `bit` naming the side of `node`. -/
def level (tw0 tw1 bit node : ℕ) (pp : List ℕ) : M ℕ := do
  let (cur, _) ← dToEAndK node
  let sib ← wire
  let diff ← add cur sib
  let left ← mulKAdd diff bit cur
  let right ← add left diff
  let (l0, l1, _) ← words left
  let (r0, r1, _) ← words right
  th tw0 tw1 pp [l0, l1, r0, r1]

/-- `fold`: leaf `leaf` (a digest wire) climbed up a tree of type `ty`, layer or tree `lay`, tree `tau` (its bits),
to its root, the leaf index's bits `jBits` low first; `top` is the tweak's second word at the top, `tau` alone. -/
def fold (ty lay : ℕ) (tauBits jBits : List ℕ) (top : ℕ) (pp : List ℕ) (leaf : ℕ) : M ℕ := do
  let mut node := leaf
  for l in List.range jBits.length do
    let tw1 ← if l + 1 < jBits.length then indexWord tauBits (jBits.drop (l + 1)) else pure top
    node ← level (tweak0 ty lay (l + 1)) tw1 (jBits.getD l 0) node pp
  pure node

/-- Chain `i` of layer `lay` from its element `tip` (an `E` wire) under the digit's indicators `ind`, the key's tweak
word `tw1`: its end's two words. -/
def chainEnd (lay i tw1 tip : ℕ) (pp ind : List ℕ) : M (ℕ × ℕ) := do
  let (t0, t1, _) ← words tip
  let d ← th (tweak0 1 lay (8 * i)) tw1 pp [t0, t1]
  let (o, _) ← dToEAndK d
  let mut cur := o
  for s in List.range' 1 6 do
    let diff ← add tip cur
    let m ← mulAdd (ind.getD s 0) diff cur
    let (v0, v1, _) ← words m
    let d ← th (tweak0 1 lay (8 * i + s)) tw1 pp [v0, v1]
    let (o, _) ← dToEAndK d
    cur := o
  let diff ← add tip cur
  let e ← mulAdd (ind.getD 7 0) diff cur
  let (n0, n1, _) ← words e
  pure (n0, n1)

/-- The few-time key the openings reach, the index's bits `idxBits`, the leaf indices' bits `us`, and `top` the
tweak word of `idx` alone. -/
def fts (idxBits : List ℕ) (us : List (List ℕ)) (top : ℕ) (pp : List ℕ) : M ℕ := do
  let mut roots := []
  for kappa in List.range 14 do
    let ub := us.getD kappa []
    let secret ← wire
    let (s0, s1, _) ← words secret
    let tw1 ← indexWord idxBits ub
    let leaf ← th (tweak0 9 kappa 0) tw1 pp [s0, s1]
    let root ← fold 10 kappa idxBits ub top pp leaf
    let rs ← dToK root
    roots := roots ++ [rs.getD 0 0, rs.getD 1 0]
  th (tweak0 11 0 0) top pp roots

/-- Layer `lay`'s root, from the message `msg` (a digest wire) it signs and the index's bits `idxBits`. -/
def layer (lay : ℕ) (idxBits : List ℕ) (pp : List ℕ) (msg : ℕ) : M ℕ := do
  let tauBits := idxBits.drop (suffix lay)
  let eBits := (idxBits.drop (suffix (lay + 1))).take (height lay)
  let z ← kConst 0
  let key ← indexWord tauBits eBits
  let top ← indexWord tauBits []
  -- The encoding.
  let ms ← dToK msg
  let ctr ← wire
  let cb ← split ctr
  for k in cb.drop 32 do
    eqConstK k 0
  let tw0 ← kConst (tweak0 4 lay 0)
  let h ← dConst paramIVLimbs
  let d ← leafBlock h ([tw0, key] ++ pp ++ [ms.getD 0 0, ms.getD 1 0, ctr, z]) 52 true
  let ks ← dToK d
  let lo ← split (ks.getD 0 0)
  let hi ← split (ks.getD 1 0)
  eqConstK (lo.getD 63 0) 0
  eqConstK (hi.getD 63 0) 0
  let digitBits := lo.take 63 ++ hi.take 63
  let prod ← digitProduct digitBits
  eqConstE prod targetWord 0 0
  -- The chains.
  let mut ends := []
  for i in List.range 42 do
    let tip ← wire
    let ind ← indicators (digitBits.getD (3 * i) 0) (digitBits.getD (3 * i + 1) 0) (digitBits.getD (3 * i + 2) 0)
    let (n0, n1) ← chainEnd lay i key tip pp ind
    ends := ends ++ [n0, n1]
  -- The leaf and the path.
  let leaf ← th (tweak0 2 lay 0) key pp ends
  fold 3 lay tauBits eBits top pp leaf

/-- One signature's verification. -/
def signature : M Unit := do
  let root ← statementWords 1
  let pp ← statementWords 1
  let mlo ← statementWords 1
  let mhi ← statementWords 1
  let z ← kConst 0
  -- The message digest.
  let rho ← wire
  let (r0, r1, _) ← words rho
  let d ← th (tweak0 12 0 0) z pp ([r0, r1] ++ root ++ mlo ++ mhi)
  let ks ← dToK d
  let w0 ← split (ks.getD 0 0)
  let w1 ← split (ks.getD 1 0)
  let w2 ← split (ks.getD 2 0)
  let bits := w0 ++ w1 ++ w2
  let idxBits := bits.take 26
  let us := (List.range 15).map fun kappa => (bits.drop (26 + 10 * kappa)).take 10
  for k in us.getD 14 [] do
    eqConstK k 0
  -- The few-time key, then the layers.
  let top ← indexWord idxBits []
  let mut msg ← fts idxBits us top pp
  for lay in [2, 1, 0] do
    msg ← layer lay idxBits pp msg
  let rs ← dToK msg
  union (rs.getD 0 0) (root.getD 0 0)
  union (rs.getD 1 0) (root.getD 1 0)

/-- The circuit verifying `n` signatures. -/
def circuit (n : ℕ) : M Unit := do
  for _ in List.range n do
    signature

end LeanVMCircuits.Sphincs.Circuit
