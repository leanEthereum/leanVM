/-
  LeanVM.Guest.Memory.GuestCntWS.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestCntWS.Data
public import LeanVM.Guest.Memory.StaticSplit
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def kushandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def kuschkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => kushandJ.any (·.1 == j) ||
      ((kuslnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (kuslookJ j) (kusomLookJ j) false (kuscertJ j) (kusomegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def kusStaticRange (a n : ℕ) : Prop := (List.range' a n).all kuschkIdx = true

/-- **A function checked in ranges of its body**, its certificate a bound. -/
theorem kuschkIdx_of_split {j : ℕ} {fn : Fn} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} {R : Acc}
    (hfn : coreProgram[j]? = some fn) (hc : kuscertJ j = .stat pre b ks) (hh : kushandJ.any (·.1 == j) = false)
    (hb : blockB (kuslookJ j) (kusomLookJ j) false ks fn.params fn.name ([], []) fn.body = some R)
    (hl : (kuslnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true)
    (hle : (Aff.leB ⟨kusomegaJ j + R.1.c, R.1.cs⟩ b && R.2.all (· ∈ pre)) = true) : kuschkIdx j = true := by
  unfold kuschkIdx
  rw [hfn]
  simp only [hh, hl, Bool.true_and, Bool.false_or]
  unfold chkFn
  rw [hc]
  simp only
  rw [blockR_eq, hb]
  exact hle

theorem kusStaticRange.get {a n j : ℕ} (h : kusStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    kuschkIdx j = true := by
  unfold kusStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
