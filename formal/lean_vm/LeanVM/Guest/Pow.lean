/-
  LeanVM.Guest.Pow

  Powers of `g` for the kernel: `g^e` as the product of five table entries, one per hexadecimal
  digit of `e`, and the check of a search tree of powers by it.
-/

module

public import LeanVM.Guest.Exec
public import LeanVM.Guest.Data.Pows

/-!
# Powers of `g` by digits

The kernel evaluates `gpow e` by square-and-multiply, some thirty products of `K` for an
exponent of the guest's code size. `gpowW e` takes five, one per hexadecimal digit of `e < 2^20`,
from the table `Data.gtab` of the words `g^(d·16^w)` (`gw_eq`, decided once), so that
`PowTree.OkW`, the check of every pair of a search tree by `gpowW`, costs a fraction of
`PowTree.Ok`, which it implies (`PowTree.ok_of_okW`).
-/

namespace LeanVM.Guest.Pow

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- `g^(d·16^w)`, from the table. -/
def gw (w d : ℕ) : K := K.ofBits (nth (nth Data.gtab w []) d 0)

/-- `g^e` for `e < 2^20`, by the hexadecimal digits of `e`. -/
def gpowW (e : ℕ) : K :=
  gw 0 (e % 16) * gw 1 (e / 16 % 16) * gw 2 (e / 256 % 16) * gw 3 (e / 4096 % 16) *
    gw 4 (e / 65536 % 16)

theorem gw_eq : ∀ w < 5, ∀ d < 16, gw w d = gpow (d * 16 ^ w) := by decide +kernel

theorem gpowW_eq {e : ℕ} (h : e < 2 ^ 20) : gpowW e = gpow e := by
  unfold gpowW
  rw [gw_eq 0 (by decide) _ (Nat.mod_lt _ (by decide)), gw_eq 1 (by decide) _ (Nat.mod_lt _ (by decide)),
    gw_eq 2 (by decide) _ (Nat.mod_lt _ (by decide)), gw_eq 3 (by decide) _ (Nat.mod_lt _ (by decide)),
    gw_eq 4 (by decide) _ (Nat.mod_lt _ (by decide)), gpow, gpow, gpow, gpow, gpow, gpow,
    ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

end
end LeanVM.Guest.Pow

namespace LeanVM.Guest.Exec

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Pow

@[expose] public section

/-- Every pair of the tree is a power of `g` below `2^20`, by digits. -/
def PowTree.OkW : PowTree → Prop
  | .leaf => True
  | .node k e l r => e < 2 ^ 20 ∧ K.ofBits k = gpowW e ∧ l.OkW ∧ r.OkW

/-- `PowTree.OkW` is decided pair by pair. -/
def PowTree.decOkW : (t : PowTree) → Decidable t.OkW
  | .leaf => isTrue trivial
  | .node k e l r =>
    haveI := PowTree.decOkW l
    haveI := PowTree.decOkW r
    inferInstanceAs (Decidable (e < 2 ^ 20 ∧ K.ofBits k = gpowW e ∧ l.OkW ∧ r.OkW))

instance (t : PowTree) : Decidable t.OkW := PowTree.decOkW t

theorem PowTree.ok_of_okW : ∀ {t : PowTree}, t.OkW → t.Ok
  | .leaf, _ => trivial
  | .node _ _ _ _, ⟨he, hk, hl, hr⟩ => ⟨hk.trans (gpowW_eq he), ok_of_okW hl, ok_of_okW hr⟩

end
end LeanVM.Guest.Exec
