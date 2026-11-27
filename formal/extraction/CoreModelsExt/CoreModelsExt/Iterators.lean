-- `Iterator` methods beyond `next`, and iterators CoreModels lacks.
module
public import Aeneas
public import CoreModels
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-! ## `fold` -/

/-- `Iterator::fold`, projected from the dictionary; CoreModels' `Iterator` carries only `next`. -/
abbrev core.iter.traits.iterator.Iterator.fold {Self Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Item) {B F : Type}
    (FnInst : core.ops.function.FnMut F (B × Item) B) (self : Self) (init : B) (f : F) :
    RustM B :=
  core.iter.traits.iterator.Iterator.fold.default IteratorInst FnInst self init f

/-- `Zip::fold`, the default `fold` over the zipped pairs. -/
abbrev core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.fold
    {I1 I2 A B Acc G : Type} (Inst1 : core.iter.traits.iterator.Iterator I1 A)
    (Inst2 : core.iter.traits.iterator.Iterator I2 B)
    (FoldFnInst : core.ops.function.FnMut G (Acc × (A × B)) Acc) :=
  core.iter.traits.iterator.Iterator.fold.default
    (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair Inst1 Inst2) FoldFnInst

/-- `Rev::fold`: the default fold over the items `Rev::next` yields, back to front. -/
abbrev core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
    {I Item B F : Type}
    (BackInst : core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (FnInst : core.ops.function.FnMut F (B × Item) B)
    (self : core.iter.adapters.rev.Rev I) (init : B) (f : F) : RustM B :=
  core.iter.traits.iterator.Iterator.fold.default
    (core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator BackInst) FnInst self init f

/-! ## `RangeInclusive` -/

/-- `Iterator::next` of `RangeInclusive`: `start` until it reaches `end`, then `end` once
more, setting `exhausted`; `None` once exhausted or when `start > end`. -/
def core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next {A : Type}
    (StepInst : core.iter.range.Step A) (self : core.ops.range.RangeInclusive A) :
    RustM (core.option.Option A × core.ops.range.RangeInclusive A) := do
  let nonempty ← StepInst.corecmpPartialOrdInst.le self.start_ self.end_
  if self.exhausted || !nonempty then ok (.None, self)
  else
    let before ← StepInst.corecmpPartialOrdInst.lt self.start_ self.end_
    let current ← StepInst.cloneCloneInst.clone self.start_
    if before then
      let next ← StepInst.forward_unchecked current 1#usize
      ok (.Some self.start_, { self with start_ := next })
    else ok (.Some current, { self with exhausted := true })

end CoreModels
