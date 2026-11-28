module

public import Kraken.X64.Syntax

/-!
# The bytes of a data label of an ingested program

`dataAt l P`: the bytes of the `.byteArray` directives after the label `l` in `P`, up to the next
non-byte directive.
-/

namespace NativeRustcX64

@[expose] public section

/-- The bytes of the `.byteArray` directives at the head of `ds`. -/
def collect : List Directive → List UInt8
  | .byteArray b :: ds => b.data.toList ++ collect ds
  | _ => []

/-- The bytes after the first label `l` of `P`. -/
def dataAt (l : Label) : List Directive → Option (List UInt8)
  | [] => none
  | .label l' :: ds => if l' = l then some (collect ds) else dataAt l ds
  | _ :: ds => dataAt l ds

end

end NativeRustcX64
