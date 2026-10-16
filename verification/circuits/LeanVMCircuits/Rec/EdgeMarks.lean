module

public import LeanVMCircuits.Rec.Dump
public import LeanVMCircuits.Rec.Edges

@[expose] public section

/-!
The edge marks of a dump (`edge` lines: a statement's layout, a child's statement words, the claims a reduction takes), as `checkedges` reads them from dumps and `checkdesign` from the design summaries.
-/

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec

/-- A list given as its length, then its numbers, at the head of `ws`, and what follows it. -/
def takeList (ws : List String) : Except String (List ℕ × List String) := do
  let n ← Dump.nat (ws.headD "")
  let xs := ws.tail.take n
  unless xs.length = n do .error "a list shorter than its length"
  return (← Dump.nats xs, ws.tail.drop n)

def lastList (ws : List String) : Except String (List ℕ) := do
  let (xs, rest) ← takeList ws
  unless rest.isEmpty do .error "words after a list"
  return xs

/-- A dump's edge marks. -/
structure Marks where
  layout : Option Layout := none
  children : Array (ℕ × List ℕ) := #[]
  dense : Array (Dense ℕ) := #[]
  matrices : Array (Matrix ℕ) := #[]

def coef (s : String) : Except String (Coef ℕ) :=
  match s with
  | "zero" => pure .zero
  | "one" => pure .one
  | _ => return .of (← Dump.nat s)

def Marks.add (m : Marks) (ws : List String) : Except String Marks := do
  match ws with
  | "layout" :: nD :: nP :: nM :: nF :: rest =>
    let (nDense, nPolys, nMatrix, nFlocks) := (← Dump.nat nD, ← Dump.nat nP, ← Dump.nat nM, ← Dump.nat nF)
    let dims ← Dump.nats rest
    unless dims.length = nPolys + nFlocks do .error "a layout's prefixes"
    if m.layout.isSome then .error "two layouts"
    return { m with layout := some { nDense, nPolys, nMatrix, nFlocks, vars := dims.take nPolys,
                                     klog := dims.drop nPolys } }
  | "child" :: i :: rest => return { m with children := m.children.push (← Dump.nat i, ← lastList rest) }
  | "dense" :: poly :: rest => return { m with dense := m.dense.push ⟨← Dump.nat poly, ← lastList rest, []⟩ }
  | "term" :: nLow :: bits :: bitsLen :: scale :: value :: rest =>
    let scale ← if scale = "none" then pure none else some <$> Dump.nat scale
    let t : Term ℕ := ⟨← Dump.nat nLow, ← Dump.nat bits, ← Dump.nat bitsLen, ← lastList rest, scale, ← Dump.nat value⟩
    let some d := m.dense.back? | .error "a term before its claim"
    return { m with dense := m.dense.pop.push { d with terms := d.terms ++ [t] } }
  | ["matrix", circuit, a, b, value] =>
    return { m with matrices := m.matrices.push ⟨← Dump.nat circuit, .point [], .point [], (← coef a, ← coef b),
                                                 ← Dump.nat value⟩ }
  | "row" :: kind :: rest =>
    let row ← match kind, rest with
      | "skip", z :: rest => do pure (RowW.skip (← Dump.nat z) (← lastList rest))
      | "point", rest => do pure (RowW.point (← lastList rest))
      | _, _ => .error "a row weight"
    let some x := m.matrices.back? | .error "a row before its claim"
    return { m with matrices := m.matrices.pop.push { x with row } }
  | "col" :: kind :: rest =>
    let col ← match kind with
      | "slices" => do
        let (s, rest) ← takeList rest
        pure (ColW.slices s (← lastList rest))
      | "point" => do pure (ColW.point (← lastList rest))
      | _ => .error "a column weight"
    let some x := m.matrices.back? | .error "a column before its claim"
    return { m with matrices := m.matrices.pop.push { x with col } }
  | _ => .error s!"an edge mark: {" ".intercalate ws |>.take 80}"

end LeanVMCircuits.Rec.Edges
