module

public import Statement.RandomPermutation

@[expose] public section

/-!
# The sponge over byte states

The definitions the proofs of the random-permutation model are written in (formerly part of
`Statement/RandomPermutation.lean`): the sponge over a permutation of a state `(Dg × E) × C`
(digest part, rest of the rate, capacity) with a padding and its decoder (`spongeWith`,
`Padding`); the Keccak state as `200` bytes, `32 + 104 + 64` (`KState`, byte `8i + k` byte `k`
of lane `i`), its blocks and Keccak-256's padding (`keccakPadding`); the real world of the
indifferentiability game (`realGame`), the model's oracles on byte states (`KSpecB`,
`permCallsB`, `runKB`); and the simulator's bookkeeping replayed from a transcript of
permutation queries (`pathsOf`). The statement's own model is on lanes (`KState` of
`Statement/RandomPermutation.lean`); `Common/Lanes.lean` relates the two.
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace Common

/-! ## The sponge over a permutation; Keccak-256's state, blocks and padding -/

/-- Byte vectors XOR bytewise: absorbing a block XORs it into the state. -/
instance (n : ℕ) : XorOp (Vector UInt8 n) where
  xor a b := Vector.zipWith (· ^^^ ·) a b

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]

/-- The state of a sponge with digest part `Dg`, rest of the rate `E` and capacity `C`. -/
abbrev SpState (Dg E C : Type) := (Dg × E) × C

/-- The digest part of a state: the first component of the rate. -/
abbrev SpState.out (s : SpState Dg E C) : Dg := s.1.1

/-- XOR on the rate, componentwise. -/
def rxor (a b : Dg × E) : Dg × E := (a.1 ^^^ b.1, a.2 ^^^ b.2)

/-- Absorbing a block: XOR it into the rate, keep the capacity. -/
def absorb (s : SpState Dg E C) (B : Dg × E) : SpState Dg E C := (rxor s.1 B, s.2)

/-- The block that takes the state `s` to the state `x` with the same capacity. -/
def blockTo (s x : SpState Dg E C) : Dg × E := rxor s.1 x.1

/-- Absorb the blocks `bs` from the state `s`: XOR each into the rate and permute with `π`. -/
def absorbAll {m : Type → Type} [Monad m] (π : SpState Dg E C → m (SpState Dg E C)) :
    SpState Dg E C → List (Dg × E) → m (SpState Dg E C)
  | s, [] => pure s
  | s, B :: bs => do
    let y ← π (absorb s B)
    absorbAll π y bs


/-- A sponge padding: messages to lists of blocks, with a decoder. The statement uses only `pad`
and `unpad`; the laws (`Padding.Lawful`: the decoder recognises exactly the paddings, which are
nonempty) are proved for `keccakPadding` in `common`. -/
structure Padding (Msg Blk : Type) where
  /-- The padded message, as a list of blocks. -/
  pad : Msg → List Blk
  /-- The decoder: the message whose padding is the given block list, if any. -/
  unpad : List Blk → Option Msg

/-- **The sponge.** Absorb the padded message from the initial state `iv` with `π`, and output the
digest part of the final state. -/
def spongeWith {Msg : Type} {m : Type → Type} [Monad m] (P : Padding Msg (Dg × E))
    (iv : SpState Dg E C) (π : SpState Dg E C → m (SpState Dg E C)) (msg : Msg) : m Dg :=
  SpState.out <$> absorbAll π iv (P.pad msg)

/-- The rate bytes of the Keccak state after the digest: bytes 32 to 135. -/
abbrev KRest := Vector UInt8 104

/-- The capacity of the Keccak state: bytes 136 to 199 (512 bits). -/
abbrev KCap := Vector UInt8 64

/-- The Keccak-f[1600] state as 200 bytes, split into digest, rest of the rate and capacity.
Byte `i` of the state is byte `i % 8` of lane `i / 8`, little-endian, as in `keccak_hash`. -/
abbrev KState := SpState DigestBytes KRest KCap

/-- A Keccak-256 block: the 136 rate bytes. -/
abbrev KBlock := DigestBytes × KRest

/-- The 200 bytes of a Keccak state, in order. -/
def KState.toBytes (s : KState) : List UInt8 := s.1.1.toList ++ s.1.2.toList ++ s.2.toList

/-- The Keccak state of 200 bytes (missing bytes read as zero). -/
def KState.ofBytes (bs : List UInt8) : KState :=
  ((Vector.ofFn fun i : Fin 32 ↦ bs.getD i 0, Vector.ofFn fun i : Fin 104 ↦ bs.getD (32 + i) 0),
    Vector.ofFn fun i : Fin 64 ↦ bs.getD (136 + i) 0)

/-- The all-zero initial state. -/
def KState.zero : KState := ((Vector.replicate 32 0, Vector.replicate 104 0), Vector.replicate 64 0)

/-- The block of the 136 bytes `bs` (missing bytes read as zero). -/
def KBlock.ofBytes (bs : List UInt8) : KBlock :=
  (Vector.ofFn fun i : Fin 32 ↦ bs.getD i 0, Vector.ofFn fun i : Fin 104 ↦ bs.getD (32 + i) 0)

/-- The 136 bytes of a block. -/
def KBlock.toBytes (B : KBlock) : List UInt8 := B.1.toList ++ B.2.toList

/-- The padded message: `msg ‖ 0x01 ‖ 0^* ‖ 0x80`, with `0x01` and `0x80` merged into `0x81` when
`msg` leaves one byte in its last block; the length is the next multiple of 136. -/
def keccakPadBytes (msg : List UInt8) : List UInt8 :=
  if msg.length % 136 = 135 then msg ++ [0x81]
  else msg ++ [0x01] ++ List.replicate (134 - msg.length % 136) 0 ++ [0x80]

/-- Split a byte list into 136-byte blocks. -/
def toBlocks : List UInt8 → List KBlock
  | [] => []
  | b :: bs => KBlock.ofBytes ((b :: bs).take 136) :: toBlocks ((b :: bs).drop 136)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The bytes of a block list. -/
def blocksToBytes (β : List KBlock) : List UInt8 := β.flatMap KBlock.toBytes

/-- Undo the padding of a padded byte list (arbitrary on other inputs). -/
def stripPad (bs : List UInt8) : List UInt8 :=
  match bs.reverse with
  | 0x81 :: rest => rest.reverse
  | _ :: rest => (((rest.dropWhile (· = 0)).drop 1)).reverse
  | [] => []

/-- The Keccak-256 padding of a message into blocks. -/
def keccakPad (msg : List UInt8) : List KBlock := toBlocks (keccakPadBytes msg)

/-- The Keccak-256 decoder: strip the padding, and accept when it pads back. -/
def keccakUnpad (β : List KBlock) : Option (List UInt8) :=
  let msg := stripPad (blocksToBytes β)
  if keccakPad msg = β then some msg else none


/-- **The Keccak-256 padding**, with its decoder. -/
def keccakPadding : Padding (List UInt8) KBlock := ⟨keccakPad, keccakUnpad⟩

/-! ## Keccak-256 over the random permutation -/

/-- A hash `Msg → Dg` as an oracle. -/
abbrev roSpec (Msg Dg : Type) : OracleSpec Msg := Msg →ₒ Dg

/-- The distinguisher's oracles: uniform coins, the hash `H : Msg → Dg`, and the permutation
`π` and its inverse. -/
abbrev dSpec (Msg Dg St : Type) := unifSpec + (roSpec Msg Dg + permutationOracleSpec St)

variable [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpState Dg E C)

/-- The real world: coins forwarded, `H` the sponge over the lazy random permutation, `π` and
`π⁻¹` the lazy random permutation. -/
noncomputable def realImpl (P : Padding Msg (Dg × E)) (iv : SpState Dg E C) :
    QueryImpl (dSpec Msg Dg (SpState Dg E C)) (StateT (PermutationEdges (SpState Dg E C)) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl m) => (spongeWith P iv (fun x ↦ lazyRandomPermutation (.forward x)) m :
      StateT (PermutationEdges (SpState Dg E C)) ProbComp Dg)
  | .inr (.inr q) => lazyRandomPermutation q

/-- **The real world** run of a distinguisher, from the empty permutation. -/
noncomputable def realGame (P : Padding Msg (Dg × E)) (iv : SpState Dg E C) {α : Type}
    (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) : ProbComp α :=
  (simulateQ (realImpl P iv) D).run' []

/-- **The oracles of the random-permutation model on byte states**: coins, Keccak-256 `H`, `π`
and `π⁻¹` (`RandomPermutationOracles` of the statement, its states read as bytes). -/
abbrev KSpecB := dSpec (List UInt8) DigestBytes KState

/-- Calls of the permutation, on byte states (`permutationCallCost`). -/
def permCallsB : KSpecB.Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => m.length / 136 + 1
  | .inr (.inr _) => 1

/-- A game on byte states, run against the lazily sampled random permutation, Keccak-256 the
sponge over it (`runK` of the statement, its states read as bytes). -/
noncomputable def runKB {α : Type} (G : OracleComp KSpecB α) : ProbComp α :=
  realGame keccakPadding KState.zero G

/-- The simulator's state: the edges it has answered, newest first, and the rooted states with
their paths, newest first, ending with the initial state and the empty path. -/
structure SimState (Dg E C : Type) where
  /-- The answered edges `(x, π x)`, newest first. -/
  edges : PermutationEdges (SpState Dg E C)
  /-- The rooted states with their block paths, newest first. -/
  chains : List (SpState Dg E C × List (Dg × E))

/-- The initial simulator state: no edges, and the initial state rooted at the empty path. -/
def SimState.init (iv : SpState Dg E C) : SimState Dg E C := ⟨[], [(iv, [])]⟩

/-- The rooted state whose capacity is that of `x`, with its path: the first such chain. -/
def chainOf (VC : List (SpState Dg E C × List (Dg × E))) (x : SpState Dg E C) :
    Option (SpState Dg E C × List (Dg × E)) :=
  VC.find? fun p ↦ decide (p.1.2 = x.2)

/-! ## The Keccak-256 evaluations a transcript of permutation queries contains -/

/-- One step of the simulator's bookkeeping, replayed from a query and its answer. -/
def replayStep (σ : SimState Dg E C) :
    PermutationQuery (SpState Dg E C) × SpState Dg E C → SimState Dg E C
  | (.forward x, y) =>
    match forwardLookup σ.edges x with
    | some _ => σ
    | none =>
      match chainOf σ.chains x with
      | some (s, β) => ⟨(x, y) :: σ.edges, (y, β ++ [blockTo s x]) :: σ.chains⟩
      | none => ⟨(x, y) :: σ.edges, σ.chains⟩
  | (.inverse y, x) =>
    match inverseLookup σ.edges y with
    | some _ => σ
    | none => ⟨(x, y) :: σ.edges, σ.chains⟩

/-- The simulator's bookkeeping replayed from a transcript of permutation queries and answers,
oldest first. -/
def replay (log : List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) : SimState Dg E C :=
  log.foldl replayStep (SimState.init iv)

/-- The hash queries whose whole sponge paths a simulator state has rooted, with the digests of
the paths' ends. -/
def simPaths (σ : SimState Dg E C) : List (Msg × Dg) :=
  σ.chains.filterMap fun p ↦ (P.unpad p.2).map fun m ↦ (m, p.1.1.1)

/-- **The hash queries of a permutation transcript**: the messages whose whole padded sponge path
the transcript (oldest first) contains as a chain of forward queries from the initial state,
each with the digest part of the path's last answer. -/
def pathsOf (log : List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) : List (Msg × Dg) :=
  simPaths P (replay iv log)

/-! ## A digest's bytes as a number -/

/-- A byte as its residue modulo `256`. -/
def uInt8EquivFin : UInt8 ≃ Fin 256 where
  toFun b := b.toFin
  invFun f := UInt8.ofFin f
  left_inv _ := rfl
  right_inv _ := rfl

namespace SufCma

/-- **The digest bytes as a bit vector**, little endian: byte `i` is bits `8 i … 8 i + 7`
(`digestBitVec_extract`); the statement's schemes read Keccak-256's digest so
(`HashSig.OverPermutation.keccakHash`, `digestBytesEquivBitVec_apply`). -/
def digestBytesEquivBitVec : DigestBytes ≃ BitVec 256 :=
  (arrayVectorEquivFin UInt8 32).trans <|
    (Equiv.arrowCongr (Equiv.refl _) uInt8EquivFin).trans <|
      finFunctionFinEquiv.trans <| (finCongr (show 256 ^ 32 = 2 ^ 256 by norm_num)).trans
        ⟨BitVec.ofFin, BitVec.toFin, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The little-endian number of a list of bytes is the sum of its bytes' weights. -/
theorem foldr_bytes_eq_sum : ∀ l : List UInt8,
    l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      ∑ i ∈ Finset.range l.length, (l.getD i 0).toNat * 256 ^ i
  | [] => rfl
  | b :: l => by
    rw [List.foldr_cons, foldr_bytes_eq_sum l, List.length_cons, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring

/-- **`digestBytesEquivBitVec` is the bytes' little-endian number**, the fold the statement's
`keccakHash` reads. -/
theorem digestBytesEquivBitVec_apply (d : DigestBytes) :
    digestBytesEquivBitVec d =
      BitVec.ofNat 256 (d.toList.foldr (fun b acc ↦ b.toNat + 256 * acc) 0) := by
  have hval : (digestBytesEquivBitVec d).toNat =
      ∑ i : Fin 32, (d[(i : ℕ)]).toNat * 256 ^ (i : ℕ) := by
    change ((finFunctionFinEquiv
      (fun i : Fin 32 ↦ uInt8EquivFin (d[(i : ℕ)])) : Fin (256 ^ 32)) : ℕ) = _
    rw [finFunctionFinEquiv_apply]
    rfl
  have hsum : ∑ i : Fin 32, (d[(i : ℕ)]).toNat * 256 ^ (i : ℕ) =
      ∑ i ∈ Finset.range d.toList.length, (d.toList.getD i 0).toNat * 256 ^ i := by
    rw [Vector.length_toList,
      ← Fin.sum_univ_eq_sum_range (fun i ↦ (d.toList.getD i 0).toNat * 256 ^ i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [List.getD_eq_getElem?_getD]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, foldr_bytes_eq_sum, ← hsum, ← hval,
    Nat.mod_eq_of_lt (digestBytesEquivBitVec d).isLt]

end SufCma

end Common
