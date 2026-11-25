-- Ordered and hashed maps and sets, assumed: the types and the operations the extractions call are opaque.
module
public import Aeneas
public import CoreModels
public import CoreModelsExt.Strings
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-! Dictionaries exist at every type: the witnesses `opaque` needs, nothing more. -/

/-- Some `Ord` dictionary exists at every type: the witness `opaque` needs, nothing more. -/
local instance {X : Type} : Inhabited (core.cmp.Ord X) :=
  let eq : core.cmp.PartialEq X X := { eq := fun _ _ => ok true, ne := fun _ _ => ok false }
  ⟨{ EqInst := { PartialEqInst := eq }
     PartialOrdInst :=
       { PartialEqInst := eq, partial_cmp := fun _ _ => ok .None, lt := fun _ _ => ok false,
         le := fun _ _ => ok true, gt := fun _ _ => ok false, ge := fun _ _ => ok true }
     cmp := fun _ _ => ok .Equal }⟩

local instance {X : Type} : Inhabited (core.hash.Hash X) := ⟨{ hash := fun _ _ h => ok h }⟩

local instance {X : Type} : Inhabited (core.default.Default X) := ⟨{ default := default }⟩

local instance {X Y : Type} : Inhabited (core.borrow.Borrow X Y) := ⟨{ borrow := fun _ => default }⟩

/-! ## `BTreeMap` -/

/-- `Clone` for the global allocator, the `A: Allocator + Clone` bound of `BTreeMap`'s methods. -/
def alloc.alloc.Global.Insts.CoreAllocAllocatorClone : core.clone.Clone alloc.alloc.Global where
  clone := fun g => ok g
  clone_from := fun _ g => ok g

/-- `Ord` for `Vec<T, A>`, lexicographic: the order of `BTreeMap`'s keys. -/
opaque alloc.vec.Vec.Insts.CoreCmpOrd (A : Type) {T : Type} (OrdInst : core.cmp.Ord T) :
    core.cmp.Ord (alloc.vec.Vec T)

opaque alloc.collections.btree.map.BTreeMap (K V A : Type) : Type

opaque alloc.collections.btree.map.Iter (K V : Type) : Type

opaque alloc.collections.btree.map.entry.Entry (K V A : Type) : Type

/-- `BTreeMap::new`, the empty map. -/
opaque alloc.collections.btree.map.BTreeMapKVGlobal.new (K V : Type) :
    RustM (alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global)

opaque alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreDefaultDefault.default
    (K V : Type) : RustM (alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global)

opaque alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreConvertFromArrayPairN.from
    {K V : Type} {N : Std.Usize} (OrdInst : core.cmp.Ord K) (entries : Aeneas.Std.Array (K × V) N) :
    RustM (alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global)

opaque alloc.collections.btree.map.BTreeMap.Insts.CoreCloneClone.clone {K V A : Type}
    (CloneK : core.clone.Clone K) (CloneV : core.clone.Clone V) (CloneA : core.clone.Clone A)
    (self : alloc.collections.btree.map.BTreeMap K V A) :
    RustM (alloc.collections.btree.map.BTreeMap K V A)

opaque alloc.collections.btree.map.BTreeMap.iter {K V A : Type} (CloneA : core.clone.Clone A)
    (self : alloc.collections.btree.map.BTreeMap K V A) :
    RustM (alloc.collections.btree.map.Iter K V)

opaque alloc.SharedABTreeMap.Insts.CoreIterTraitsCollectIntoIteratorPairSharedAKSharedAVIter.into_iter
    {K V A : Type} (CloneA : core.clone.Clone A) (self : alloc.collections.btree.map.BTreeMap K V A) :
    RustM (alloc.collections.btree.map.Iter K V)

opaque alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next
    {K V : Type} (self : alloc.collections.btree.map.Iter K V) :
    RustM (core.option.Option (K × V) × alloc.collections.btree.map.Iter K V)

/-- The `Iterator` of `btree_map::Iter`, over its entries in key order. -/
@[reducible]
def alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV
    (K V : Type) :
    core.iter.traits.iterator.Iterator (alloc.collections.btree.map.Iter K V) (K × V) where
  next := alloc.collections.btree.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next

opaque alloc.collections.btree.map.BTreeMap.entry {K V A : Type} (CloneA : core.clone.Clone A)
    (OrdInst : core.cmp.Ord K) (self : alloc.collections.btree.map.BTreeMap K V A) (key : K) :
    RustM (alloc.collections.btree.map.entry.Entry K V A ×
      (alloc.collections.btree.map.entry.Entry K V A → alloc.collections.btree.map.BTreeMap K V A))

opaque alloc.collections.btree.map.entry.Entry.or_default {K V A : Type} (OrdInst : core.cmp.Ord K)
    (DefaultInst : core.default.Default V) (CloneA : core.clone.Clone A)
    (self : alloc.collections.btree.map.entry.Entry K V A) :
    RustM (V × (V → alloc.collections.btree.map.entry.Entry K V A))

/-! ## Hashing -/

/-- `core::hash::BuildHasher`, a dictionary whose methods are not modelled: the hashed
collections' operations that would call them are opaque. -/
structure core.hash.BuildHasher (Self : Type) where

/-- `Hash` for `String`, its bytes then `0xff`. -/
opaque alloc.string.String.Insts.CoreHashHash : core.hash.Hash alloc.string.String

/-- `Hash` for `str`, its bytes then `0xff`. -/
opaque core.Str.Insts.CoreHashHash : core.hash.Hash Str

/-- `std::hash::RandomState`, the default hasher builder. -/
opaque std.hash.random.RandomState : Type

/-- `RandomState: Default`, freshly seeded keys. -/
opaque std.hash.random.RandomState.Insts.CoreDefaultDefault :
  core.default.Default std.hash.random.RandomState

/-- `RandomState: Clone`. -/
def std.hash.random.RandomState.Insts.CoreCloneClone : core.clone.Clone std.hash.random.RandomState where
  clone := fun s => ok s
  clone_from := fun _ s => ok s

/-- `RandomState: BuildHasher<Hasher = DefaultHasher>`. -/
def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher :
  core.hash.BuildHasher std.hash.random.RandomState := {}

/-! ## `HashMap` and `HashSet` -/

opaque std.collections.hash.map.HashMap (K V S A : Type) : Type

opaque std.collections.hash.set.HashSet (T S A : Type) : Type

/-- `HashMap::default`, the empty map. -/
opaque std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault.default {S : Type}
    (K V : Type) (DefaultS : core.default.Default S) :
    RustM (std.collections.hash.map.HashMap K V S alloc.alloc.Global)

/-- `HashMap: Clone`, entry by entry. -/
opaque std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone {K V S A : Type}
    (CloneK : core.clone.Clone K) (CloneV : core.clone.Clone V) (CloneS : core.clone.Clone S)
    (CloneA : core.clone.Clone A) (self : std.collections.hash.map.HashMap K V S A) :
    RustM (std.collections.hash.map.HashMap K V S A)

/-- `HashMap::get`: the value at a key, if any. -/
opaque std.collections.hash.map.HashMap.get {K V S Q : Type} (EqK : core.cmp.Eq K)
    (HashK : core.hash.Hash K) (BuildS : core.hash.BuildHasher S) (BorrowKQ : core.borrow.Borrow K Q)
    (HashQ : core.hash.Hash Q) (EqQ : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S alloc.alloc.Global) (k : Q) :
    RustM (core.option.Option V)

/-- `HashMap::get_mut`: the value at a key, if any, and the map with it written back. -/
opaque std.collections.hash.map.HashMap.get_mut {K V S Q : Type} (EqK : core.cmp.Eq K)
    (HashK : core.hash.Hash K) (BuildS : core.hash.BuildHasher S) (BorrowKQ : core.borrow.Borrow K Q)
    (HashQ : core.hash.Hash Q) (EqQ : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S alloc.alloc.Global) (k : Q) :
    RustM (core.option.Option V ×
      (core.option.Option V → std.collections.hash.map.HashMap K V S alloc.alloc.Global))

/-- `map[k]`: the value at a key, panicking when it is absent. -/
opaque std.collections.hash.map.HashMap.Insts.CoreOpsIndexIndexShared0QV.index {K V S Q : Type}
    (EqK : core.cmp.Eq K) (HashK : core.hash.Hash K) (BorrowKQ : core.borrow.Borrow K Q)
    (EqQ : core.cmp.Eq Q) (HashQ : core.hash.Hash Q) (BuildS : core.hash.BuildHasher S)
    (self : std.collections.hash.map.HashMap K V S alloc.alloc.Global) (k : Q) : RustM V

end CoreModels
