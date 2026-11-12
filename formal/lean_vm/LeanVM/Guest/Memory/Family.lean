/-
  LeanVM.Guest.Memory.Family

  A family of static certificates of the guest by core index, checked by the kernel in ranges of
  the core IR, one pass over each (`RangeOk`), its call sites' certificates found through the
  callees' indices (`calleeIdx`).
-/

module

public import LeanVM.Guest.Memory.StaticVec
public import LeanVM.Guest.Memory.Walk
public import LeanVM.Guest.Memory.GuestCallees
public import LeanVM.Guest.CoreData

/-!
# Certificate families

A family gives each function of the guest's core IR, by index, a certificate and a frame weight.
The kernel checks it in ranges of functions, walking the function list once per range
(`RangeOk`: `walkOk` over `(coreProgram.drop a).take n`), never indexing it; ranges join
(`RangeOk.append`) into the whole program. A call site names its callee: `calleeIdx j g` finds it
among function `j`'s callees by index (`Data.calleesJ`), its name read off `Data.nameT`, both
generated (`Memory/GuestCallees`) and checked once (`FamilySound.calleeIdx_spec`), so no check
encodes a name. `lookV` and `lookS`, `omLookS` look the certificates and weights up by it; the
checks of a vector family (`chkV`, the instruction counts by opcode) and of a scalar one
(`chkS`, the words) are `chkFnV` and `chkFn` with them.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- **The `n` functions from the `a`-th pass `chk`**, in one walk of the core IR. -/
def RangeOk (chk : ℕ → Fn → Bool) (a n : ℕ) : Prop :=
  walkOk chk a ((coreProgram.drop a).take n) = true

/-- The index of function `j`'s callee `g`. -/
def calleeIdx (j : ℕ) (g : String) : Option ℕ :=
  (Data.calleesJ j).find? fun k => decide (Data.nameT.find k = some g)

/-- A vector family's certificates of function `j`'s callees, by name. -/
def lookV (cert : ℕ → CertV) (j : ℕ) (g : String) : CertV :=
  match calleeIdx j g with
  | some k => cert k
  | none => .none

/-- A scalar family's certificates of function `j`'s callees, by name. -/
def lookS (cert : ℕ → Cert) (j : ℕ) (g : String) : Cert :=
  match calleeIdx j g with
  | some k => cert k
  | none => .none

/-- A scalar family's frame weights of function `j`'s callees, by name. -/
def omLookS (om : ℕ → ℕ) (j : ℕ) (g : String) : Option ℕ := (calleeIdx j g).map om

/-- The check of function `j` in a vector family. -/
noncomputable def chkV (cert : ℕ → CertV) (om : ℕ → Vec) (j : ℕ) (fn : Fn) : Bool :=
  chkFnV (lookV cert j) (cert j) (om j) fn

/-- The check of function `j` in a scalar family, counting words if `α`. -/
noncomputable def chkS (α : Bool) (cert : ℕ → Cert) (om : ℕ → ℕ) (j : ℕ) (fn : Fn) : Bool :=
  chkFn (lookS cert j) (omLookS om j) α (cert j) (om j) fn

/-! ## Ranges -/

/-- Two adjacent ranges are one. -/
theorem RangeOk.append {chk : ℕ → Fn → Bool} {a n m : ℕ} (h1 : RangeOk chk a n)
    (h2 : RangeOk chk (a + n) m) : RangeOk chk a (n + m) := by
  unfold RangeOk at *
  rw [List.take_add, walkOk_append, h1, Bool.true_and]
  by_cases hl : ((coreProgram.drop a).take n).length = n
  · rw [hl, List.drop_drop]; exact h2
  · have hs : (coreProgram.drop a).length < n := by
      rw [List.length_take] at hl; omega
    rw [List.drop_eq_nil_of_le (Nat.le_of_lt hs), List.take_nil]
    rfl

theorem RangeOk.get {chk : ℕ → Fn → Bool} {a n j : ℕ} {fn : Fn} (h : RangeOk chk a n) (h1 : a ≤ j)
    (h2 : j < a + n) (hj : coreProgram[j]? = some fn) : chk j fn = true := by
  have hk : ((coreProgram.drop a).take n)[j - a]? = some fn := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_cancel' h1, hj]
  have := walkOk_get h hk
  rwa [Nat.add_sub_cancel' h1] at this

/-- **Every function passes** a check whose ranges cover the core IR. -/
theorem RangeOk.all {chk : ℕ → Fn → Bool} (h : RangeOk chk 0 coreProgram.length) {j : ℕ}
    (hj : j < coreProgram.length) : chk j coreProgram[j] = true :=
  h.get (Nat.zero_le j) (by omega) (List.getElem?_eq_getElem hj)

end
end LeanVM.Guest.Memory
