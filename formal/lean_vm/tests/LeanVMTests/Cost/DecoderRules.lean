import LeanVM.Cost.FastLib
import LeanVM.Guest.Fast.Sphincs
import Statement.Theorems

/-!
# Tests: the compiler's support for the guest decoder

The rules and rewrites the guest decoder's readers need, each on a small function compiled and
run: `|||` and `Nat.lor` on `ℕ`, `(1 : E)`, bit vectors (encoded as their number, the statement's
encoding), and the witness types under the statement's encodings (`Statement/LeanVmGuest.lean`:
constructors and fields, so that a compiled decoder's output is the statement's `encodeValue` of its
value), the guest's value names `V` and `Seg`.
-/

namespace LeanVMTests.Cost.DecoderRules

open LeanVM.Cost LeanVM.Parameters LeanVM.Node

def orNat (a b : ℕ) : ℕ := a ||| b
cost_compile orNat := orNat

def lorNat (a b : ℕ) : ℕ := Nat.lor a b
cost_compile lorNat := lorNat

def plusOne (x : E) : E := x + 1
cost_compile plusOne := plusOne

def genPow (k : ℕ) : E := LeanVM.Protocol.Verifier.gen ^ k
cost_compile genPow := genPow

def bvOf (n : ℕ) : BitVec 128 := BitVec.ofNat 128 n
cost_compile bvOf := bvOf

def bvNat (v : BitVec 128) : ℕ := v.toNat + 1
cost_compile bvNat := bvNat

def bvFin (n : ℕ) (h : n < 2 ^ 128) : BitVec 128 := BitVec.ofFin ⟨n, h⟩
cost_compile bvFin := bvFin

def mkKey (r p : BitVec 128) : HashSig.PublicKey := ⟨r, p⟩
cost_compile mkKey := mkKey

def keyRoot (k : HashSig.PublicKey) : ℕ := k.root.toNat
cost_compile keyRoot := keyRoot

def mkSpKey (s r : BitVec 128) : Sphincs.PublicKey := ⟨s, r⟩
cost_compile mkSpKey := mkSpKey

def mkStatement (xs : List LeanXmssClaim) (ss : List LeanSphincsClaim) (d : LeanVM.Protocol.Digest)
    (c : DeferredClaim) : NodeStatement := ⟨⟨xs, ss, d⟩, c⟩
cost_compile mkStatement := mkStatement

def mkChild (s : NodeStatement) (f : LeanVM.Protocol.Verifier.BytecodeClaim)
    (π : LeanVM.Protocol.Compile.Proof) : Child := ⟨s, f, π⟩
cost_compile mkChild := mkChild

def raws (c : LeanXmssClaim) (σ : LeanXmss.Signature) : List (LeanXmssClaim × LeanXmss.Signature) :=
  [(c, σ), (c, σ)]
cost_compile raws := raws

def mkDa (r : LeanVM.Protocol.Digest) (z : E) (rows : List (List K)) :
    Option (DaClaim × LeanVM.Da.MatrixWitness) := some (⟨r, z⟩, ⟨rows⟩)
cost_compile mkDa := mkDa

def mkWitness (cs : List Child) (xs : List (LeanXmssClaim × LeanXmss.Signature))
    (ss : List (LeanSphincsClaim × Sphincs.Signature)) (d : Option (DaClaim × LeanVM.Da.MatrixWitness))
    (m : List (E × E)) (v : E) : NodeWitness := ⟨cs, xs, ss, d, ⟨m, v⟩⟩
cost_compile mkWitness := mkWitness

def mkDecoded (seed : LeanVM.Protocol.Digest) (s : NodeStatement) (w : NodeWitness) :
    SeedStatementAndWitness := ⟨seed, s, w⟩
cost_compile mkDecoded := mkDecoded

def layerSwap (r : BitVec 128) (σ : LeanXmss.LayerSignature) : LeanXmss.LayerSignature :=
  ⟨r, σ.chainValues, σ.authenticationPath⟩
cost_compile layerSwap := layerSwap

def xmssLeaf (σ : LeanXmss.Signature) : ℕ := σ.leafIndex.val
cost_compile xmssLeaf := xmssLeaf

def sphincsRandomizer (σ : Sphincs.Signature) : ℕ := σ.randomizer.toNat
cost_compile sphincsRandomizer := sphincsRandomizer

def slayerOf (n : ℕ) (r : BitVec 128) (l : Sphincs.Layer) : Sphincs.LayerSignature l :=
  ⟨BitVec.ofNat 32 (n + l.val), fun _ ↦ r, fun j ↦ BitVec.ofNat 128 j.val⟩
cost_compile slayerOf := slayerOf

/-- A signature whose layers are built as the reader builds them (`depFin3`). -/
def mkSphincsSig (n : ℕ) (r p : BitVec 128) : Sphincs.Signature :=
  ⟨BitVec.ofNat 128 77, fun _ ↦ ⟨p, fun _ ↦ r⟩,
    LeanVM.Cost.depFin3 (slayerOf n r 0) (slayerOf n r 1) (slayerOf n r 2)⟩
cost_compile mkSphincsSig := mkSphincsSig

def vIdx (v : LeanVM.Guest.Core.V) : ℕ := v.idx + v.path.length
cost_compile vIdx := vIdx

/-- A compiled function's value on `vs`, in the program of the bodies its spec needs. -/
def runOn (deps : List (ℕ × Term)) (i : ℕ) (vs : List MachineValue) : Option MachineValue :=
  (evaluateFunctionBody (MachineProgram.ofList deps) 100 i vs).map (·.1)

#guard runOn orNat.costDeps orNat.costIdx [encodeValue (12 : ℕ), encodeValue (5 : ℕ)] == some (encodeValue (orNat 12 5))
#guard runOn lorNat.costDeps lorNat.costIdx
  [encodeValue (2 ^ 70 : ℕ), encodeValue (3 : ℕ)] == some (encodeValue (lorNat (2 ^ 70) 3))

def x : E := E.ofLimbs (K.ofLane 0x0123456789abcdef) (K.ofLane 7)
#guard runOn plusOne.costDeps plusOne.costIdx [encodeValue x] == some (encodeValue (plusOne x))
#guard runOn genPow.costDeps genPow.costIdx [encodeValue (0 : ℕ)] == some (encodeValue (genPow 0))
#guard runOn genPow.costDeps genPow.costIdx [encodeValue (5 : ℕ)] == some (encodeValue (genPow 5))

#guard runOn bvOf.costDeps bvOf.costIdx [encodeValue (2 ^ 130 + 9 : ℕ)] == some (encodeValue (bvOf (2 ^ 130 + 9)))
#guard runOn bvOf.costDeps bvOf.costIdx [encodeValue (2 ^ 130 + 9 : ℕ)] == some (.nat 9)

def r : BitVec 128 := BitVec.ofNat 128 (2 ^ 100 + 3)
def m : BitVec 256 := BitVec.ofNat 256 (2 ^ 200 + 5)
def p : BitVec 128 := BitVec.ofNat 128 77
#guard runOn bvNat.costDeps bvNat.costIdx [encodeValue r] == some (encodeValue (bvNat r))
#guard runOn bvFin.costDeps bvFin.costIdx [encodeValue (2 ^ 100 + 3 : ℕ)] == some (encodeValue r)
#guard runOn mkKey.costDeps mkKey.costIdx [encodeValue r, encodeValue p] == some (encodeValue (mkKey r p))
#guard runOn keyRoot.costDeps keyRoot.costIdx [encodeValue (mkKey r p)] == some (encodeValue (2 ^ 100 + 3 : ℕ))
#guard runOn mkSpKey.costDeps mkSpKey.costIdx [encodeValue p, encodeValue r] == some (encodeValue (mkSpKey p r))

def digest : LeanVM.Protocol.Digest := #v[1, 2, 3, 4]
def claim : DeferredClaim := ⟨[x, x], x⟩
def stmt : NodeStatement := mkStatement [(mkKey r p, m)] [(mkSpKey p r, m)] digest claim
#guard runOn mkStatement.costDeps mkStatement.costIdx
  [encodeValue [(mkKey r p, m)], encodeValue [(mkSpKey p r, m)], encodeValue digest, encodeValue claim] ==
  some (encodeValue stmt)

def proof : LeanVM.Protocol.Compile.Proof := ⟨[x], [[⟨3, [K.ofLane 5], [digest]⟩]]⟩
def child : Child := mkChild stmt claim proof
#guard runOn mkChild.costDeps mkChild.costIdx [encodeValue stmt, encodeValue claim, encodeValue proof] == some (encodeValue child)

def layer : LeanXmss.LayerSignature := ⟨r, fun _ ↦ p, fun i ↦ BitVec.ofNat 128 i.val⟩
def xsig : LeanXmss.Signature := ⟨⟨12345, by decide⟩, fun _ ↦ layer⟩
#guard runOn raws.costDeps raws.costIdx [encodeValue (mkKey r p, m), encodeValue xsig] ==
  some (encodeValue (raws (mkKey r p, m) xsig))

def da : Option (DaClaim × LeanVM.Da.MatrixWitness) := mkDa digest x [[K.ofLane 1]]
#guard runOn mkDa.costDeps mkDa.costIdx [encodeValue digest, encodeValue x, encodeValue [[K.ofLane 1]]] ==
  some (encodeValue da)

def witness : NodeWitness := mkWitness [child] (raws (mkKey r p, m) xsig) [] da [(x, x)] x
#guard runOn mkWitness.costDeps mkWitness.costIdx
  [encodeValue [child], encodeValue (raws (mkKey r p, m) xsig),
  encodeValue ([] : List (LeanSphincsClaim × Sphincs.Signature)),
  encodeValue da, encodeValue [(x, x)], encodeValue x] == some (encodeValue witness)

def decoded : SeedStatementAndWitness := mkDecoded digest stmt witness
#guard runOn mkDecoded.costDeps mkDecoded.costIdx
  [encodeValue digest, encodeValue stmt, encodeValue witness] == some (encodeValue decoded)

#guard runOn layerSwap.costDeps layerSwap.costIdx
  [encodeValue p, encodeValue layer] == some (encodeValue (layerSwap p layer))
#guard runOn xmssLeaf.costDeps xmssLeaf.costIdx [encodeValue xsig] == some (encodeValue (12345 : ℕ))

def ssig : Sphincs.Signature :=
  ⟨BitVec.ofNat 128 77, fun _ ↦ ⟨p, fun _ ↦ r⟩, fun l ↦ slayerOf 99 r l⟩
#guard runOn sphincsRandomizer.costDeps sphincsRandomizer.costIdx [encodeValue ssig] ==
  some (encodeValue (77 : ℕ))
-- the layers built by `depFin3`, encoded as the statement encodes a signature's layers
#guard runOn mkSphincsSig.costDeps mkSphincsSig.costIdx
  [encodeValue (99 : ℕ), encodeValue r, encodeValue p] == some (encodeValue ssig)

def v : LeanVM.Guest.Core.V := ⟨[.s 1, .i "main" 2, .t], 0, 7⟩
#guard runOn vIdx.costDeps vIdx.costIdx [encodeValue v] == some (encodeValue (10 : ℕ))

/-- info: 'LeanVMTests.Cost.DecoderRules.mkWitness.costSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mkWitness.costSpec

end LeanVMTests.Cost.DecoderRules
