module

public import NativeRustcX64.Sym

/-!
# What the x86-64 proofs of `whir.rs`'s functions share

Runs from a block's end state (`after`, `after_eq`, `exec_after`).
-/

namespace NativeRustcVmX64.Whir

open NativeRustcX64 NativeRustcX64.Sym

public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
@[expose] def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

end

end NativeRustcVmX64.Whir
