import Whir.PCSBCSMerkleQueryLog
import Whir.PCSBCSMerkleLeafImages

/-! At the commitment/oracle-message boundary, first registration freezes the
CURRENT public-query prefix and its full extracted table. This API is called by
the causal caller, not with a final transcript log. The address includes the CV,
height, full leaf-image width and occupied width: identical untagged preimages
at different shapes are not collisions. Same-address clones retain the literal
prefix and table; later
queries do not fill absent rows retroactively. Opening transport additionally
requires derived registry provenance and authentic captured-prefix evidence. -/
namespace Whir.PCSBCSMerkleRootCache
open Concrete FiatShamirGame PublicMerkleLog MerkleQueryLogExtraction PCSBCSMerkleQueryLog
open PCSBCSMerkleLeafImages

structure Shape where
  height : Nat
  leafWords : Nat
  occupied : Nat

structure Frozen where
  shape : Shape
  queryPrefix : PublicLog
  cells : Array ImageCell
  raw : Array (Array K)

abbrev CacheKey := Key × Nat × Nat × Nat

def cacheKey (root : Digest32) (shape : Shape) : CacheKey :=
  (key root, shape.height, shape.leafWords, shape.occupied)

theorem cacheKey_injective {root other : Digest32} {shape requested : Shape}
    (same : cacheKey root shape = cacheKey other requested) :
    root = other ∧ shape = requested := by
  have digest := congrArg Prod.fst same
  have height := congrArg (fun address : CacheKey => address.2.1) same
  have imageWidth := congrArg (fun address : CacheKey => address.2.2.1) same
  have occupied := congrArg (fun address : CacheKey => address.2.2.2) same
  refine ⟨key_injective digest, ?_⟩
  cases shape
  cases requested
  dsimp only [cacheKey] at height imageWidth occupied
  cases height
  cases imageWidth
  cases occupied
  rfl

abbrev Registry := Std.ExtHashMap CacheKey Frozen

/-- `queryPrefix` is already public at the announcement. It is retained by
reference, not recopied; extraction never consults later answers. -/
def freeze (queryPrefix : PublicLog) (root : Digest32) (shape : Shape) : Frozen :=
  let cells := sourceCells queryPrefix root shape.height shape.leafWords shape.occupied
  ⟨shape,queryPrefix,cells,compactTable cells⟩

theorem freeze_prefix (queryPrefix : PublicLog) (root : Digest32) (shape : Shape) :
    (freeze queryPrefix root shape).queryPrefix = queryPrefix := rfl

/-- Runtime branches BEFORE invoking extraction. Only the identical
CV/height/leafWords/occupied address reuses an earlier extraction. -/
def register (registry : Registry) (log : PublicLog) (root : Digest32) (shape : Shape) : Registry :=
  let address := cacheKey root shape
  match registry[address]? with
  | some _ => registry
  | none => registry.insert address (freeze log root shape)

theorem register_existing (registry : Registry) (log : PublicLog) (root : Digest32)
    (shape : Shape) (frozen : Frozen) (known : registry[cacheKey root shape]? = some frozen) :
    register registry log root shape = registry := by simp [register,known]

theorem register_preserves (registry : Registry) (log : PublicLog) (root other : Digest32)
    (shape requested : Shape) (frozen : Frozen)
    (known : registry[cacheKey root shape]? = some frozen) :
    (register registry log other requested)[cacheKey root shape]? = some frozen := by
  unfold register
  dsimp only
  split
  next => exact known
  next miss =>
    rw [Std.ExtHashMap.getElem?_insert]
    split
    next eq =>
      have hk : cacheKey other requested = cacheKey root shape := by simpa using eq
      rw [hk,known] at miss
      contradiction
    next => exact known

theorem register_first (registry : Registry) (log : PublicLog) (root : Digest32)
    (shape : Shape) (absent : registry[cacheKey root shape]? = none) :
    (register registry log root shape)[cacheKey root shape]? = some (freeze log root shape) := by
  simp [register,absent]

/-- Derived provenance, not an assumption that preimages are available. -/
def WellFormed (registry : Registry) : Prop :=
  ∀ root shape frozen, registry[cacheKey root shape]? = some frozen →
    frozen = freeze frozen.queryPrefix root shape

theorem empty_wellFormed : WellFormed (∅ : Registry) := by
  simp [WellFormed]

theorem register_wellFormed (registry : Registry) (log : PublicLog) (root : Digest32)
    (shape : Shape) (valid : WellFormed registry) :
    WellFormed (register registry log root shape) := by
  unfold register
  dsimp only
  split
  next => exact valid
  next miss =>
    intro other requested frozen known
    rw [Std.ExtHashMap.getElem?_insert] at known
    split at known
    next eq =>
      have same : cacheKey root shape = cacheKey other requested := by simpa using eq
      obtain ⟨rfl,rfl⟩ := cacheKey_injective same
      have value := Option.some.inj known
      rw [← value]
      rfl
    next => exact valid other requested frozen known

theorem lookup_shape (registry : Registry) (valid : WellFormed registry)
    (root : Digest32) (shape : Shape) (frozen : Frozen)
    (known : registry[cacheKey root shape]? = some frozen) : frozen.shape = shape := by
  exact congrArg Frozen.shape (valid root shape frozen known)

theorem freeze_shape (log : PublicLog) (root : Digest32) (shape : Shape)
    (fits : shape.occupied ≤ shape.leafWords) :
    (freeze log root shape).raw.size = 2^shape.height ∧
    ∀ row ∈ (freeze log root shape).raw.toList, row.size = shape.occupied := by
  exact compactTable_shape log root shape.height shape.leafWords shape.occupied fits

end Whir.PCSBCSMerkleRootCache
