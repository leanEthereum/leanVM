module

public import NativeRustcArm.Sym

/-!
# The frame's symbolic state

`frameS k`: the frame (region 0, 2752 bytes, aligned), SP its base, X29 the saved registers at
2656, the registers `k` known. Kept apart so the executor's runs can use it at compile time.
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustcArm.Sym

@[expose] public section

/-- The frame (region 0), SP its base, X29 the saved registers, the registers `k`. -/
def frameS (k : List (XReg × Sym)) : SState :=
  init [(2752, true)] (.ptr 0 0) ((.X29, .ptr 0 2656) :: k)

/-- A literal 64-bit word in the frame. -/
def litW (off v : Nat) : Write := ⟨0, off, 8, .lit v⟩

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

end

end NativeRustcArm.WotsLeafProof
