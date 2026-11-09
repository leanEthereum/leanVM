module

public import LeanVM.Cost.Encoding
public import Statement.Theorems

/-!
# The encoding of a guest decoding is injective

`GuestKnowledgeSoundness` (`Statement/LeanVmGuest.lean`) asks the guest decoder program to output the
encoding (`encodeValue`) of a decoding: a seed, a statement and a witness. That the output
determines the decoding is **`encodeValue_decoded_injective`**, from a left inverse:
`decodeDecoded`, a parse of each type of a decoding by its `MachineDecoding` instance (here, not in
the statement), and
`LawfulMachineDecoding α`, that `MachineDecoding α` inverts `MachineEncoding α`, for each:
**`decodeDecoded_enc`**, `decodeDecoded (encodeValue d) = some d`.
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ## A parse of each type of a decoding -/

/-! `MachineDecoding α` parses a value as an `α`, the inverse of `MachineEncoding α`: a linear
parse, no search, no check beyond the shape (a constructor's tag and arity, an array's length for
a `Vector` or a function of a finite domain, a natural number's bound for `Fin n`); a bit vector
of `w` bits is its number
modulo `2^w` (`BitVec.ofNat`). `none` on anything else. -/

/-- A machine decoding of `α`: the `α` a value encodes, or `none`. -/
class MachineDecoding (α : Type) where
  /-- The `α` the value encodes, or `none`. -/
  decodeValue : MachineValue → Option α

export MachineDecoding (decodeValue)

/-- A word: its number modulo `2^64`. -/
instance : MachineDecoding UInt64 where
  decodeValue | .nat n => some n.toUInt64 | _ => none

instance : MachineDecoding ℕ where
  decodeValue | .nat n => some n | _ => none

instance {n : ℕ} : MachineDecoding (Fin n) where
  decodeValue | .nat i => if h : i < n then some ⟨i, h⟩ else none | _ => none

instance : MachineDecoding Bool where
  decodeValue | .constructor 0 [] => some false | .constructor 1 [] => some true | _ => none

instance {w : ℕ} : MachineDecoding (BitVec w) where
  decodeValue | .nat n => some (BitVec.ofNat w n) | _ => none

/-- An element of `K`: the word of its number modulo `2^64`. -/
instance : MachineDecoding K where
  decodeValue | .nat a => some (K.ofLane a.toUInt64) | _ => none

instance : MachineDecoding E := ⟨decodeExtensionElement⟩

instance {α : Type} [MachineDecoding α] : MachineDecoding (List α) :=
  ⟨fun v ↦ (MachineValue.toList? v).bind (·.mapM decodeValue)⟩

instance {α β : Type} [MachineDecoding α] [MachineDecoding β] : MachineDecoding (α × β) where
  decodeValue | .constructor 0 [a, b] => do pure (← decodeValue a, ← decodeValue b) | _ => none

instance {α : Type} [MachineDecoding α] : MachineDecoding (Option α) where
  decodeValue
    | .constructor 0 [] => some none
    | .constructor 1 [a] => (decodeValue a).map some
    | _ => none

instance {α : Type} [MachineDecoding α] {n : ℕ} : MachineDecoding (Vector α n) where
  decodeValue
    | .array xs =>
      match xs.toList.mapM decodeValue with
      | some ys => if h : ys.length = n then some ⟨ys.toArray, by simpa using h⟩ else none
      | none => none
    | _ => none

/-- A function of a finite domain from the array of its values. -/
def decodeFiniteFunction {α : Type} [MachineDecoding α] {n : ℕ} : MachineValue → Option (Fin n → α)
  | .array xs =>
    match xs.toList.mapM decodeValue with
    | some ys =>
      if h : ys.length = n then some fun i ↦ ys[i.val]'(by rw [h]; exact i.isLt) else none
    | none => none
  | _ => none

instance {α : Type} [MachineDecoding α] {n : ℕ} : MachineDecoding (Fin n → α) :=
  ⟨decodeFiniteFunction⟩

instance : MachineDecoding Opening where
  decodeValue
    | .constructor 0 [i, l, p] => do pure ⟨← decodeValue i, ← decodeValue l, ← decodeValue p⟩
    | _ => none

instance : MachineDecoding Proof where
  decodeValue | .constructor 0 [s, o] => do pure ⟨← decodeValue s, ← decodeValue o⟩ | _ => none

instance : MachineDecoding HashSig.PublicKey where
  decodeValue | .constructor 0 [r, p] => do pure ⟨← decodeValue r, ← decodeValue p⟩ | _ => none

instance : MachineDecoding Sphincs.PublicKey where
  decodeValue | .constructor 0 [r, p] => do pure ⟨← decodeValue r, ← decodeValue p⟩ | _ => none

instance : MachineDecoding LeanXmss.LayerSignature where
  decodeValue
    | .constructor 0 [r, c, p] =>
      do pure ⟨← decodeValue r, ← decodeValue c, ← decodeValue p⟩
    | _ => none

instance : MachineDecoding LeanXmss.Signature where
  decodeValue | .constructor 0 [i, l] => do pure ⟨← decodeValue i, ← decodeValue l⟩ | _ => none

instance : MachineDecoding Sphincs.ForsTreeOpening where
  decodeValue | .constructor 0 [s, p] => do pure ⟨← decodeValue s, ← decodeValue p⟩ | _ => none

instance (layer : Sphincs.Layer) : MachineDecoding (Sphincs.LayerSignature layer) where
  decodeValue
    | .constructor 0 [c, v, p] => do pure ⟨← decodeValue c, ← decodeValue v, ← decodeValue p⟩
    | _ => none

/-- The three layers' signatures, bottom first, as a dependent function of the layer. -/
def sphincsLayers (bottom : Sphincs.LayerSignature 0) (middle : Sphincs.LayerSignature 1)
    (top : Sphincs.LayerSignature 2) : (layer : Sphincs.Layer) → Sphincs.LayerSignature layer :=
  fun layer => match layer with
    | ⟨0, _⟩ => bottom
    | ⟨1, _⟩ => middle
    | ⟨2, _⟩ => top

instance : MachineDecoding Sphincs.Signature where
  decodeValue
    | .constructor 0 [r, f, .array ls] =>
      match ls.toList with
      | [l0, l1, l2] => do
        pure ⟨← decodeValue r, ← decodeValue f,
          sphincsLayers (← decodeValue l0) (← decodeValue l1) (← decodeValue l2)⟩
      | _ => none
    | _ => none

instance : MachineDecoding BytecodeClaim where
  decodeValue | .constructor 0 [p, v] => do pure ⟨← decodeValue p, ← decodeValue v⟩ | _ => none

instance : MachineDecoding DaClaim where
  decodeValue | .constructor 0 [r, v] => do pure ⟨← decodeValue r, ← decodeValue v⟩ | _ => none

instance : MachineDecoding Da.MatrixWitness where
  decodeValue | .constructor 0 [r] => do pure ⟨← decodeValue r⟩ | _ => none

instance : MachineDecoding NodeClaims where
  decodeValue
    | .constructor 0 [x, s, d] =>
      do pure ⟨← decodeValue x, ← decodeValue s, ← decodeValue d⟩
    | _ => none

instance : MachineDecoding NodeStatement where
  decodeValue | .constructor 0 [c, d] => do pure ⟨← decodeValue c, ← decodeValue d⟩ | _ => none

instance : MachineDecoding Child where
  decodeValue
    | .constructor 0 [s, f, p] =>
      do pure ⟨← decodeValue s, ← decodeValue f, ← decodeValue p⟩
    | _ => none

instance : MachineDecoding BatchingHints where
  decodeValue | .constructor 0 [m, v] => do pure ⟨← decodeValue m, ← decodeValue v⟩ | _ => none

instance : MachineDecoding NodeWitness where
  decodeValue
    | .constructor 0 [c, x, s, d, h] =>
      do pure ⟨← decodeValue c, ← decodeValue x, ← decodeValue s, ← decodeValue d, ← decodeValue h⟩
    | _ => none

instance : MachineDecoding SeedStatementAndWitness where
  decodeValue
    | .constructor 0 [s, t, w] =>
      do pure ⟨← decodeValue s, ← decodeValue t, ← decodeValue w⟩
    | _ => none

/-- **A decoding from its encoding**: a seed, a statement and a witness; `none` on anything
else. -/
def decodeDecoded : MachineValue → Option SeedStatementAndWitness := decodeValue

/-! ## The parse inverts the encoding -/

/-- **`MachineDecoding α` inverts `MachineEncoding α`.** -/
class LawfulMachineDecoding (α : Type) [MachineEncoding α] [MachineDecoding α] : Prop where
  decodeValue_encodeValue : ∀ a : α, decodeValue (encodeValue a) = some a

export LawfulMachineDecoding (decodeValue_encodeValue)

attribute [simp] decodeValue_encodeValue

instance : LawfulMachineDecoding UInt64 := ⟨fun x ↦ by
  show some x.toNat.toUInt64 = some x; simp [Nat.toUInt64_eq]⟩
instance : LawfulMachineDecoding ℕ := ⟨fun _ ↦ rfl⟩
instance {n : ℕ} : LawfulMachineDecoding (Fin n) := ⟨fun i ↦ by
  show (if h : i.val < n then some (⟨i.val, h⟩ : Fin n) else none) = some i
  simp [i.isLt]⟩
instance : LawfulMachineDecoding Bool := ⟨fun b ↦ by cases b <;> rfl⟩

instance {w : ℕ} : LawfulMachineDecoding (BitVec w) :=
  ⟨fun v ↦ by show some (BitVec.ofNat w v.toNat) = some v; simp⟩

instance : LawfulMachineDecoding K := ⟨fun a ↦ by
  show some (K.ofLane a.lane.toNat.toUInt64) = some a
  simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat]; rfl⟩
instance : LawfulMachineDecoding E := ⟨decodeE_enc⟩

theorem mapM_decodeValue_map_encodeValue {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] (l : List α) :
    (l.map encodeValue).mapM (decodeValue (α := α)) = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih]

theorem toList?_ofList (l : List MachineValue) : MachineValue.toList? (MachineValue.ofList l) = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [MachineValue.ofList, MachineValue.toList?, ih]

instance {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] : LawfulMachineDecoding (List α) :=
  ⟨fun l ↦ by
    show (MachineValue.toList? (MachineValue.ofList (l.map encodeValue))).bind (·.mapM decodeValue) = some l
    rw [toList?_ofList, Option.bind_some, mapM_decodeValue_map_encodeValue]⟩

instance {α β : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] [MachineEncoding β] [MachineDecoding β] [LawfulMachineDecoding β] :
    LawfulMachineDecoding (α × β) :=
  ⟨fun ⟨a, b⟩ ↦ by
    show (do pure ((← decodeValue (encodeValue a)), (← decodeValue (encodeValue b))) : Option (α × β)) = _
    simp⟩

instance {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] :
    LawfulMachineDecoding (Option α) :=
  ⟨fun o ↦ by
    cases o with
    | none => rfl
    | some a => show (decodeValue (encodeValue a)).map some = _; simp⟩

theorem mapM_decodeValue_toList_map {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] (xs : Array α) :
    (xs.map encodeValue).toList.mapM (decodeValue (α := α)) = some xs.toList := by
  rw [Array.toList_map, mapM_decodeValue_map_encodeValue]

instance {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] {n : ℕ} : LawfulMachineDecoding (Vector α n) :=
  ⟨fun ⟨xs, h⟩ ↦ by
    show (match (xs.map encodeValue).toList.mapM decodeValue with
      | some ys => if h : ys.length = n then some ⟨ys.toArray, by simpa using h⟩ else none
      | none => none : Option (Vector α n)) = _
    rw [mapM_decodeValue_toList_map]
    simp [h]⟩

instance {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] {n : ℕ} : LawfulMachineDecoding (Fin n → α) :=
  ⟨fun f ↦ by
    have hm : (Array.ofFn fun i ↦ encodeValue (f i)).toList.mapM (decodeValue (α := α)) = some (List.ofFn f) := by
      have : (List.ofFn fun i ↦ encodeValue (f i)) = (List.ofFn f).map encodeValue := by
        rw [List.map_ofFn]; rfl
      rw [Array.toList_ofFn, this, mapM_decodeValue_map_encodeValue]
    show decodeFiniteFunction (.array (Array.ofFn fun i ↦ encodeValue (f i))) = some f
    simp only [decodeFiniteFunction]
    rw [hm]
    simp only [List.length_ofFn, ↓reduceDIte, Option.some.injEq]
    funext i
    simp⟩

instance : LawfulMachineDecoding Opening := ⟨fun ⟨i, l, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue i), ← decodeValue (encodeValue l),
    ← decodeValue (encodeValue p)⟩ : Option Opening) = _; simp⟩

instance : LawfulMachineDecoding Proof := ⟨fun ⟨s, o⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue o)⟩ : Option Proof) = _; simp⟩

instance : LawfulMachineDecoding HashSig.PublicKey := ⟨fun ⟨r, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue p)⟩ : Option HashSig.PublicKey) = _; simp⟩

instance : LawfulMachineDecoding Sphincs.PublicKey := ⟨fun ⟨r, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue p)⟩ : Option Sphincs.PublicKey) = _; simp⟩

instance : LawfulMachineDecoding LeanXmss.LayerSignature := ⟨fun ⟨r, c, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue c), ← decodeValue (encodeValue p)⟩ :
    Option LeanXmss.LayerSignature) = _
  simp⟩

instance : LawfulMachineDecoding LeanXmss.Signature := ⟨fun ⟨i, l⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue i), ← decodeValue (encodeValue l)⟩ : Option LeanXmss.Signature) = _; simp⟩

instance : LawfulMachineDecoding Sphincs.ForsTreeOpening := ⟨fun ⟨s, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue p)⟩ : Option Sphincs.ForsTreeOpening) = _; simp⟩

instance (layer : Sphincs.Layer) : LawfulMachineDecoding (Sphincs.LayerSignature layer) :=
  ⟨fun ⟨c, v, p⟩ ↦ by
    show (do pure ⟨← decodeValue (encodeValue c), ← decodeValue (encodeValue v),
      ← decodeValue (encodeValue p)⟩ : Option (Sphincs.LayerSignature layer)) = _
    simp⟩

theorem sphincsLayers_eta (l : (layer : Sphincs.Layer) → Sphincs.LayerSignature layer) :
    sphincsLayers (l 0) (l 1) (l 2) = l := by
  funext layer
  match layer with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

instance : LawfulMachineDecoding Sphincs.Signature := ⟨fun ⟨r, f, l⟩ ↦ by
  have hl : (Array.ofFn fun layer ↦ encodeValue (l layer)).toList =
      [encodeValue (l 0), encodeValue (l 1), encodeValue (l 2)] := by
    rw [Array.toList_ofFn]; rfl
  show (match (Array.ofFn fun layer ↦ encodeValue (l layer)).toList with
    | [l0, l1, l2] => do
      pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue f),
        sphincsLayers (← decodeValue l0) (← decodeValue l1) (← decodeValue l2)⟩
    | _ => none : Option Sphincs.Signature) = _
  rw [hl]
  simp only [decodeValue_encodeValue, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    sphincsLayers_eta]⟩

instance : LawfulMachineDecoding BytecodeClaim := ⟨fun ⟨p, v⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue p), ← decodeValue (encodeValue v)⟩ : Option BytecodeClaim) = _; simp⟩

instance : LawfulMachineDecoding DaClaim := ⟨fun ⟨r, v⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue v)⟩ : Option DaClaim) = _; simp⟩

instance : LawfulMachineDecoding Da.MatrixWitness := ⟨fun ⟨r⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r)⟩ : Option Da.MatrixWitness) = _; simp⟩

instance : LawfulMachineDecoding NodeClaims := ⟨fun ⟨x, s, d⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue x), ← decodeValue (encodeValue s), ← decodeValue (encodeValue d)⟩ : Option NodeClaims) = _
  simp⟩

instance : LawfulMachineDecoding NodeStatement := ⟨fun ⟨c, d⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue c), ← decodeValue (encodeValue d)⟩ : Option NodeStatement) = _; simp⟩

instance : LawfulMachineDecoding Child := ⟨fun ⟨s, f, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue f), ← decodeValue (encodeValue p)⟩ : Option Child) = _
  simp⟩

instance : LawfulMachineDecoding BatchingHints := ⟨fun ⟨m, v⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue m), ← decodeValue (encodeValue v)⟩ : Option BatchingHints) = _; simp⟩

instance : LawfulMachineDecoding NodeWitness := ⟨fun ⟨c, x, s, d, h⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue c), ← decodeValue (encodeValue x), ← decodeValue (encodeValue s),
    ← decodeValue (encodeValue d), ← decodeValue (encodeValue h)⟩ : Option NodeWitness) = _
  simp⟩

instance : LawfulMachineDecoding SeedStatementAndWitness := ⟨fun ⟨s, t, w⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue t), ← decodeValue (encodeValue w)⟩ : Option SeedStatementAndWitness) = _
  simp⟩

/-- **Decoding a decoding inverts its encoding.** -/
theorem decodeDecoded_enc (d : SeedStatementAndWitness) : decodeDecoded (encodeValue d) = some d := decodeValue_encodeValue d

/-- **The encoding of a decoding is injective**: the guest decoder program's output determines the
decoding `GuestKnowledgeSoundness` names. -/
theorem encodeValue_decoded_injective : Function.Injective (encodeValue : SeedStatementAndWitness → MachineValue) :=
  fun a b h ↦ Option.some.inj (by rw [← decodeDecoded_enc a, h, decodeDecoded_enc])

end

end LeanVM.Cost
