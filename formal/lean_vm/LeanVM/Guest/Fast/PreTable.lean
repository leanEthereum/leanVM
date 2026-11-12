module

public import LeanVM.Guest.Fast.PreSig
public import LeanVM.Guest.Glob
public meta import LeanVM.Guest.KernelLit

/-!
# The functions' preconditions, a literal table

`preTable`: entry `j` is function `j`'s precondition as its test reads it (`fnPreOf (glob.sig j)`,
`Fast/PreSig.lean`), for the guest's `1602` functions (`nFns`), written out by the kernel (`kernel_lit`:
`preTable_eq`, the kernel's check that it is the table computed from the certificates, in one pass
over them, `preOfCert`). The
decoder's compiled precondition test reads this literal (`Cost/Decoder/PreTable.lean`), not the
certificates.

A slow module (the kernel reads every certificate's tables), importing only the definitions it
evaluates (`Fast/Firewall.lean` checks it).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Check

@[expose] public section

/-- What `fnPreOf (glob.sig j)` reads of function `j`'s certificate. -/
noncomputable def preOfCert (c : Cert) : Option FnPre :=
  bif (envChecks c.facts.env).isEmpty && c.pre.isEmpty && c.mem.isEmpty then none
  else some ⟨envChecks c.facts.env, c.pre, c.mem⟩

theorem fnPreOf_sig (j : ℕ) : fnPreOf (glob.sig j) = preOfCert (listElementOrDefault Data.certs j default) := by
  show fnPreOf (sigOf j) = _
  unfold sigOf certOf
  generalize listElementOrDefault Data.certs j default = c
  obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _, _, _, _, _, _, _, _, _, _⟩ := c
  rfl

theorem pre_nth {α : Type} : ∀ (l : List α) (n : ℕ) (d : α), listElementOrDefault l n d = l.getD n d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, n + 1, d => pre_nth as n d

theorem certs_length : nFns ≤ Data.certs.length := by decide +kernel

/-- **The functions' preconditions**, entry `j` function `j`'s. -/
kernel_lit preTable : Array (Option FnPre) :=
  ((Data.certs.take nFns).map preOfCert).toArray

/-- Entry `j < nFns` of the table is function `j`'s precondition. -/
theorem preTable_getD {j : ℕ} (hj : j < nFns) : preTable.getD j none = fnPreOf (glob.sig j) := by
  have hl : j < Data.certs.length := Nat.lt_of_lt_of_le hj certs_length
  rw [← preTable_eq, fnPreOf_sig, pre_nth]
  simp [Array.getD, List.getD_eq_getElem?_getD, hj, hl]

end

end LeanVM.Guest.Fast
