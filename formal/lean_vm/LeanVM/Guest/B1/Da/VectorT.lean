/-
  LeanVM.Guest.B1.Da.VectorT

  The templates of `da_vector_cell__L0` and `__L1` (G:3045-3076), checked against the core IR.
-/

module

public import LeanVM.Guest.B1.Digest.Statement
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Value `r` (`2 ≤ r < 27`) of weight pair `p`, numbered as `sdPair`'s. -/
abbrev vxv (p r : ℕ) : V := .n (258 + 25 * p + r)

/-- Weight pair `p`: its two entries split and packed into three cells. -/
def vxPair (p : ℕ) : List Atom :=
  [.hint (.limbs (.n (2 * p + 4)) [vxv p 2, vxv p 3]),
   .hint (.limbs (.n (2 * p + 1 + 4)) [vxv p 4, vxv p 5]),
   .assertInK (vxv p 2) (vxv p 3), .const (vxv p 6) wY, .mul (vxv p 7) (vxv p 6) (vxv p 3),
   .add (vxv p 8) (vxv p 2) (vxv p 7), .add (vxv p 9) (.n (2 * p + 4)) (vxv p 2),
   .const (vxv p 10) wYi, .mul (vxv p 11) (vxv p 9) (vxv p 10), .add (vxv p 12) (vxv p 11) (vxv p 3),
   .const (vxv p 13) wYi, .mul (vxv p 14) (vxv p 12) (vxv p 13), .assertInK (vxv p 14) (vxv p 4),
   .const (vxv p 15) wY, .mul (vxv p 16) (vxv p 15) (vxv p 4), .add (vxv p 17) (vxv p 14) (vxv p 16),
   .add (vxv p 18) (.n (2 * p + 1 + 4)) (vxv p 4), .const (vxv p 19) wYi,
   .mul (vxv p 20) (vxv p 18) (vxv p 19), .add (vxv p 21) (vxv p 20) (vxv p 5), .const (vxv p 22) wYi,
   .mul (vxv p 23) (vxv p 21) (vxv p 22), .assertInK (vxv p 5) (vxv p 23), .const (vxv p 24) wY,
   .mul (vxv p 25) (vxv p 24) (vxv p 23), .add (vxv p 26) (vxv p 5) (vxv p 25)]

/-- The value of packed cell `q`: cell `q % 3` of pair `q / 3`. -/
def vxQ (q : ℕ) : ℕ := 258 + 25 * (q / 3) + (8 + 9 * (q % 3))

/-- The first value of window `w`'s blocks. -/
def vxK (w : ℕ) : ℕ := 3470 + 132 * w

/-- The counter word window `w`'s blocks offset. -/
def vxBase (w : ℕ) : ℕ := if w = 0 then 3465 else if w = 1 then 3469 else 3601

/-- The counter word ending window `w`. -/
def vxEnd (w : ℕ) : ℕ := if w = 0 then 3469 else if w = 1 then 3601 else 3733

/-- The state after `j` blocks (its first cell). -/
def vxSt (final : Bool) (j : ℕ) : ℕ :=
  if j = 0 then 3460 else if final = true ∧ j = 96 then 3860 else
  if (j - 1) % 32 = 31 then vxK ((j - 1) / 32) + 124 else vxK ((j - 1) / 32) + 4 * ((j - 1) % 32) + 2

/-- Block `j`'s metadata word. -/
def vxMdI (final : Bool) (j : ℕ) : ℕ :=
  if j % 32 = 31 then (if final = true ∧ j = 95 then 3859 else vxEnd (j / 32)) else
  vxK (j / 32) + 4 * (j % 32) + 1

/-- `MD_FINAL`. -/
abbrev mdF : E := word 0 4294967295 0

/-- Block `j` (`w = j / 32`, `b = j % 32`): its metadata, then its compression. -/
def vxBlk (final : Bool) (j : ℕ) : List Atom :=
  if j % 32 = 31 then
    (if final = true ∧ j = 95 then [.const (.n 3858) mdF, .add (.n 3859) (.n 3733) (.n 3858)] else []) ++
    [.blake2s (.n (vxQ (4 * j))) (.n (vxQ (4 * j + 1))) (.n (vxQ (4 * j + 2))) (.n (vxQ (4 * j + 3)))
      (.n (vxSt final j)) (.n (vxSt final j + 1)) (.n (vxSt final (j + 1))) (.n (vxSt final (j + 1) + 1))
      (.n (vxMdI final j))]
  else
    [.const (.n (vxK (j / 32) + 4 * (j % 32))) (word (64 * (j % 32 + 1)) 0 0),
     .add (.n (vxK (j / 32) + 4 * (j % 32) + 1)) (.n (vxBase (j / 32))) (.n (vxK (j / 32) + 4 * (j % 32))),
     .blake2s (.n (vxQ (4 * j))) (.n (vxQ (4 * j + 1))) (.n (vxQ (4 * j + 2))) (.n (vxQ (4 * j + 3)))
      (.n (vxSt final j)) (.n (vxSt final j + 1)) (.n (vxSt final (j + 1))) (.n (vxSt final (j + 1) + 1))
      (.n (vxMdI final j))]

/-- Window `0`'s counter words, read at `counters·xb³` and the next cell. -/
def vxPre0 : List Atom :=
  [.mul (.n 3462) (.n 0) (.n 0), .mul (.n 3463) (.n 3462) (.n 0), .mul (.n 3464) (.n 3) (.n 3463),
   .load (.n 3465) (.n 3464) 0, .mul (.n 3466) (.n 0) (.n 0), .mul (.n 3467) (.n 3466) (.n 0),
   .mul (.n 3468) (.n 3) (.n 3467), .load (.n 3469) (.n 3468) 1]

/-- Window `w ≥ 1`'s end counter word, read at `counters·xb³·g^w` and the next cell. -/
def vxPre (w : ℕ) : List Atom :=
  [.mul (.n (vxK w - 6)) (.n 0) (.n 0), .mul (.n (vxK w - 5)) (.n (vxK w - 6)) (.n 0),
   .const (.n (vxK w - 4)) (word (2 ^ w) 0 0), .mul (.n (vxK w - 3)) (.n (vxK w - 5)) (.n (vxK w - 4)),
   .mul (.n (vxK w - 2)) (.n 3) (.n (vxK w - 3)), .load (.n (vxK w - 1)) (.n (vxK w - 2)) 1]

/-- The weights' frame address. -/
def vxF (final : Bool) : ℕ := if final then 3862 else 3860

/-- `da_vector_cell__L{final}`'s atoms. -/
def vxAtoms (final : Bool) : List Atom :=
  [.hint (.witness "da_weights" (.stack ((List.range 256).map fun i => .n (i + 4))))] ++
    (List.range 128).flatMap vxPair ++ [.copy (.n 3460) (.n 1), .copy (.n 3461) (.n 2)] ++ vxPre0 ++
    (List.range 32).flatMap (vxBlk final) ++ vxPre 1 ++
    (List.range 32).flatMap (fun b => vxBlk final (32 + b)) ++ vxPre 2 ++
    (List.range 32).flatMap (fun b => vxBlk final (64 + b)) ++
    [.frameAddr (.n (vxF final)) ((List.range 256).map fun i => .n (i + 4)),
     .copy (.n (vxF final + 1)) (.n (vxSt final 96)), .copy (.n (vxF final + 2)) (.n (vxSt final 96 + 1)),
     .copy (.n (vxF final + 3)) (.n (vxF final))]

/-- `da_vector_cell__L{final}`'s body. -/
def vxBody (final : Bool) : List Stmt :=
  (vxAtoms final).map .atom ++ [.ret [.n (vxF final + 1), .n (vxF final + 2), .n (vxF final + 3)]]

/-- The specialization's name. -/
def vxName (final : Bool) : String := if final then "da_vector_cell__L1" else "da_vector_cell__L0"

open scoped LeanVM.Guest.B1.Sig.Dec in
theorem vx1_eq : Data.core547.body = vxBody true := by decide +kernel

open scoped LeanVM.Guest.B1.Sig.Dec in
theorem vx0_eq : Data.core548.body = vxBody false := by decide +kernel

set_option maxRecDepth 100000 in
theorem find_vx1 : coreProgram.find? "da_vector_cell__L1" =
    some ⟨"da_vector_cell__L1", [.n 0, .n 1, .n 2, .n 3], vxBody true⟩ := by
  rw [Program.find?_of_indexOf? (j := 547) (by decide +kernel) rfl, ← vx1_eq]
  rfl

set_option maxRecDepth 100000 in
theorem find_vx0 : coreProgram.find? "da_vector_cell__L0" =
    some ⟨"da_vector_cell__L0", [.n 0, .n 1, .n 2, .n 3], vxBody false⟩ := by
  rw [Program.find?_of_indexOf? (j := 548) (by decide +kernel) rfl, ← vx0_eq]
  rfl

theorem find_vx (final : Bool) : coreProgram.find? (vxName final) =
    some ⟨vxName final, [.n 0, .n 1, .n 2, .n 3], vxBody final⟩ := by
  cases final
  · exact find_vx0
  · exact find_vx1

end
end LeanVM.Guest.B1.Digest
