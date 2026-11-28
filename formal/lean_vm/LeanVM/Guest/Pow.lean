/-
  LeanVM.Guest.Pow

  Powers of `g` for the kernel: `g^e` as the product of five table entries, one per hexadecimal
  digit of `e`, and the check of a search tree of powers by it.
-/

module

public import LeanVM.Guest.ExecCore
public import LeanVM.Guest.Data.Pows
public import LeanVM.Guest.Data.GTab
public import LeanVM.Guest.PowWords

/-!
# Powers of `g` by digits

The kernel evaluates `gpow e` by square-and-multiply, some thirty products of `K` for an
exponent of the guest's code size. `gpowW e` takes five, one per hexadecimal digit of `e < 2^20`,
from the table `Data.gtab` of the words `g^(d·16^w)` (`gw_eq`, decided once), so that
`PowTree.OkW`, the check of every pair of a search tree by `gpowW`, costs a fraction of
`PowTree.Ok`, which it implies (`PowTree.ok_of_okW`). Its products are on words in `ℕ`
(`PowWords.lean`).
-/

namespace LeanVM.Guest.Pow

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- `g^(d·16^w)`, from the table. -/
def gw (w d : ℕ) : K := K.ofBits (listElementOrDefault (listElementOrDefault Data.gtab w []) d 0)

/-- `g^e` for `e < 2^20`, by the hexadecimal digits of `e`. -/
def gpowW (e : ℕ) : K :=
  gw 0 (e % 16) * gw 1 (e / 16 % 16) * gw 2 (e / 256 % 16) * gw 3 (e / 4096 % 16) *
    gw 4 (e / 65536 % 16)

theorem gw_eq : ∀ w < 5, ∀ d < 16, gw w d = addressOfIndex (d * 16 ^ w) := by decide +kernel

theorem gpowW_eq {e : ℕ} (h : e < 2 ^ 20) : gpowW e = addressOfIndex e := by
  unfold gpowW
  rw [gw_eq 0 (by decide) _ (Nat.mod_lt _ (by decide)), gw_eq 1 (by decide) _ (Nat.mod_lt _ (by decide)),
    gw_eq 2 (by decide) _ (Nat.mod_lt _ (by decide)), gw_eq 3 (by decide) _ (Nat.mod_lt _ (by decide)),
    gw_eq 4 (by decide) _ (Nat.mod_lt _ (by decide)), addressOfIndex, addressOfIndex, addressOfIndex, addressOfIndex, addressOfIndex, addressOfIndex,
    ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

/-- `gw` as a word in `ℕ`. -/
def gwN (w d : ℕ) : ℕ := listElementOrDefault (listElementOrDefault Data.gtab w []) d 0

/-- `gpowW` on words in `ℕ`. -/
def gpowN (e : ℕ) : ℕ :=
  mulN (mulN (mulN (mulN (gwN 0 (e % 16)) (gwN 1 (e / 16 % 16))) (gwN 2 (e / 256 % 16)))
    (gwN 3 (e / 4096 % 16))) (gwN 4 (e / 65536 % 16))

/-- **`gpowN` is `gpowW`.** -/
theorem ofBits_gpowN (e : ℕ) : K.ofBits (gpowN e) = gpowW e := by
  simp only [gpowN, ofBits_mulN]
  rfl

/-! ## Powers by one product

`gpowM e` is `g^e` for `e < 2^20` by one product, of `g^(e % 1024)` and `g^(1024·(e / 1024))` from
the tables `Data.gtabLo` and `Data.gtabHi`, each checked once as a chain of products (`tabs_ok`). -/

/-- Entry `d` of a table in rows of 32. -/
def tabN (t : List (List ℕ)) (d : ℕ) : ℕ :=
  listElementOrDefault (listElementOrDefault t (d / 32) []) (d % 32) 0

/-- Entries `1` to `n` of a table are each the one before times `s` (`s` first: `mulN` loops over its first
factor's bits). -/
def chainN (t : List (List ℕ)) (s : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => Nat.beq (tabN t (n + 1)) (mulN s (tabN t n)) && chainN t s n

theorem chainN_pow {t : List (List ℕ)} {s : ℕ} : ∀ {n : ℕ}, chainN t s n = true → ∀ d ≤ n,
    K.ofBits (tabN t d) = K.ofBits (tabN t 0) * K.ofBits s ^ d
  | 0, _, d, hd => by rw [Nat.le_zero.mp hd, pow_zero, mul_one]
  | n + 1, h, d, hd => by
    simp only [chainN, Bool.and_eq_true, Nat.beq_eq] at h
    rcases Nat.lt_or_ge d (n + 1) with hlt | hge
    · exact chainN_pow h.2 d (by omega)
    · rw [show d = n + 1 by omega, h.1, ofBits_mulN, chainN_pow h.2 n le_rfl, pow_succ]
      ring

/-- The tables start at `g^0` and `g^1024 = g^1023 · g`, and each is a chain. -/
theorem tabs_ok : (Nat.beq (tabN Data.gtabLo 0) (gwN 0 0) && Nat.beq (tabN Data.gtabHi 0) (gwN 0 0) &&
    Nat.beq (tabN Data.gtabHi 1) (mulN (tabN Data.gtabLo 1023) (gwN 0 1)) &&
    chainN Data.gtabLo (gwN 0 1) 1023 && chainN Data.gtabHi (tabN Data.gtabHi 1) 1023) = true := by
  decide +kernel

theorem gwN_eq {w d : ℕ} (hw : w < 5) (hd : d < 16) : K.ofBits (gwN w d) = addressOfIndex (d * 16 ^ w) :=
  gw_eq w hw d hd

theorem gLoN_eq {d : ℕ} (hd : d < 1024) : K.ofBits (tabN Data.gtabLo d) = addressOfIndex d := by
  have h := tabs_ok
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  rw [chainN_pow h.1.2 d (by omega), h.1.1.1.1, gwN_eq (w := 0) (d := 0) (by decide) (by decide),
    gwN_eq (w := 0) (d := 1) (by decide) (by decide)]
  simp only [addressOfIndex, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem gHiN_eq {d : ℕ} (hd : d < 1024) : K.ofBits (tabN Data.gtabHi d) = addressOfIndex (1024 * d) := by
  have h := tabs_ok
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h1 : K.ofBits (tabN Data.gtabHi 1) = addressOfIndex 1024 := by
    rw [h.1.1.2, ofBits_mulN, gLoN_eq (by decide), gwN_eq (w := 0) (d := 1) (by decide) (by decide)]
    simp only [addressOfIndex, ← pow_add]
    norm_num
  rw [chainN_pow h.2 d (by omega), h.1.1.1.2, gwN_eq (w := 0) (d := 0) (by decide) (by decide), h1]
  simp only [addressOfIndex, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- `g^e` for `e < 2^20`, one product. -/
def gpowM (e : ℕ) : ℕ := mulN (tabN Data.gtabLo (e % 1024)) (tabN Data.gtabHi (e / 1024))

/-- **`gpowM` is `g^e`.** -/
theorem ofBits_gpowM {e : ℕ} (he : e < 2 ^ 20) : K.ofBits (gpowM e) = addressOfIndex e := by
  rw [gpowM, ofBits_mulN, gLoN_eq (Nat.mod_lt _ (by decide)), gHiN_eq (by omega)]
  simp only [addressOfIndex, ← pow_add]
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

/-- `PowTree.OkW` as a `Bool`, on words in `ℕ` (`gpowN`). -/
def PowTree.okWB : PowTree → Bool
  | .leaf => true
  | .node k e l r => Nat.blt e 1048576 && Nat.beq k (gpowN e) && l.okWB && r.okWB

/-- A pair checked on words is a power of `g` by digits. -/
theorem gpowW_of_beq {k e : ℕ} (h : Nat.beq k (gpowN e) = true) : K.ofBits k = gpowW e := by
  rw [Nat.eq_of_beq_eq_true h, ofBits_gpowN]

/-- **`PowTree.OkW`, decided on words.** -/
theorem PowTree.okW_of_okWB : ∀ {t : PowTree}, t.okWB = true → t.OkW
  | .leaf, _ => trivial
  | .node _ _ _ _, h => by
    simp only [okWB, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨he, hk⟩, hl⟩, hr⟩ := h
    exact ⟨he, gpowW_of_beq hk, okW_of_okWB hl, okW_of_okWB hr⟩

/-- `PowTree.OkW` as a `Bool`, one product a pair (`gpowM`). -/
def PowTree.okMB : PowTree → Bool
  | .leaf => true
  | .node k e l r => Nat.blt e 1048576 && Nat.beq k (gpowM e) && l.okMB && r.okMB

/-- **`PowTree.OkW`, decided by one product a pair.** -/
theorem PowTree.okW_of_okMB : ∀ {t : PowTree}, t.okMB = true → t.OkW
  | .leaf, _ => trivial
  | .node _ _ _ _, h => by
    simp only [okMB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨he, rfl⟩, hl⟩, hr⟩ := h
    exact ⟨he, (ofBits_gpowM he).trans (gpowW_eq he).symm, okW_of_okMB hl, okW_of_okMB hr⟩

theorem PowTree.ok_of_okW : ∀ {t : PowTree}, t.OkW → t.Ok
  | .leaf, _ => trivial
  | .node _ _ _ _, ⟨he, hk, hl, hr⟩ => ⟨hk.trans (gpowW_eq he), ok_of_okW hl, ok_of_okW hr⟩

end
end LeanVM.Guest.Exec
