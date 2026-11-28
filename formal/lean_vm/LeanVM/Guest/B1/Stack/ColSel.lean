/-
  LeanVM.Guest.B1.Stack.ColSel

  B1 of `column_selector`: a block's selector, the eq of its offset's bits above its kappa.
-/

module

public import LeanVM.Guest.B1.Stack.SelMath
public import LeanVM.Guest.B1.Stack.CertifyR
public import LeanVM.Guest.B1.Whir.Names
import LeanVM.Guest.Value.FieldBits

/-!
# `column_selector`

`column_selector(offset, sel_eq, sel_g, n_nib, kappa)` (`guests/lean_ethereum.py`), every
specialization `__L{n}_L{κ}` (`cselName`): it hints the offset's nibbles `j` from `κ / 4` to `n - 1`
as `g^e_j`, range checks each below `g^16`, reads nibble `j`'s `selector_tables` entry at `e_j`
(the first one at the level of its width `4 j + 4 - κ`) and its share `g^(e_j·16^j)`, multiplies
them, and asserts the shares' product is the offset (`cselBody`). On a `2^κ`-aligned offset `g^idx`,
`idx < 2^(4n)`, the hinted digits are `idx`'s nibbles and the selector is
`Π_{κ ≤ t < 4n} (idx bit t ? point_t : point1_t)` (`MeaningColumnSelector`, `csel_sound`).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- `column_selector`'s specialization at `n` nibbles and the kappa `κ`. -/
def cselName (n κ : ℕ) : String := "column_selector__L" ++ natStr n ++ "_L" ++ natStr κ

/-- **`column_selector(offset, sel_eq, sel_g)`** at `n` nibbles and `κ`: on `selector_tables`'
entries at `sel_eq`, the nibble shares at `sel_g` and the offset `g^idx`, `idx < 2^(4n)` a multiple
of `2^κ`, it returns `Π_{κ ≤ t < 4n} selBit p p1 idx t`. -/
def MeaningColumnSelector (n κ : ℕ) (rd : Reader) : List E → List E → Prop
  | [off, se, sg], rets => ∀ (p p1 : ℕ → E) (idx : ℕ),
      (∀ j < n, ∀ w < 4, ∀ k < 2 ^ (w + 1),
        LoadHolds rd se (32 * j + selOff w + k * 2 ^ (3 - w)) (selLev p p1 j w k)) →
      (∀ j < 9, ∀ u < 16, LoadHolds rd sg (16 * j + u) (gen ^ (u * 16 ^ j))) →
      off = gen ^ idx → idx < 2 ^ (4 * n) → 2 ^ κ ∣ idx →
      rets = [∏ t ∈ Finset.Ico κ (4 * n), selBit p p1 idx t]
  | _, _ => False

/-! ## The template -/

/-- Digit `i`'s value base, at `c` digits. -/
def cselB (c i : ℕ) : ℕ := if i = 0 then 3 + c else c + 1 + 10 * i

/-- The running selector after digit `i`. -/
def cselSel (c i : ℕ) : ℕ := if i = 0 then c + 8 else c + 7 + 10 * i

/-- The running rebuilt offset after digit `i`. -/
def cselReb (c i : ℕ) : ℕ := if i = 0 then c + 10 else c + 10 + 10 * i

/-- Digit `i` of `c`, nibble `j0 + i`, at `κ`. -/
def cselDigit (j0 κ c i : ℕ) : List Stmt :=
  let b := cselB c i
  let j := j0 + i
  if i = 0 then
    [osCst b (csW 15), csRc (3 + i) (b + 1) b, osMul (b + 4) 1 (3 + i),
      .atom (.load (.n (b + 5)) (.n (b + 4)) (32 * j + selOff (4 * j0 + 3 - κ))),
      osMul (b + 6) 2 (3 + i), .atom (.load (.n (b + 7)) (.n (b + 6)) (16 * j))]
  else
    [osCst b (csW 15), csRc (3 + i) (b + 1) b, osMul (b + 4) 1 (3 + i),
      .atom (.load (.n (b + 5)) (.n (b + 4)) (32 * j + 16)), osMul (b + 6) (cselSel c (i - 1)) (b + 5),
      osMul (b + 7) 2 (3 + i), .atom (.load (.n (b + 8)) (.n (b + 7)) (16 * j)),
      osMul (b + 9) (cselReb c (i - 1)) (b + 8)]

/-- The statements of `column_selector__L{n}_L{κ}` before its return, and the returned value. -/
def cselBodyA (n κ : ℕ) : List Stmt × ℕ :=
  if n ≤ κ / 4 then
    ([.atom (.hint (.digitsExp (.n 0) (4 * n) 0 4 (4 * (κ / 4)) none (.stack []))),
      osCst 3 (word 1 0), .atom (.assertEq (.n 3) (.n 0)), osCst 4 (word 1 0)], 4)
  else
    let c := n - κ / 4
    ([.atom (.hint (.digitsExp (.n 0) (4 * n) c 4 (4 * (κ / 4)) none
        (.stack ((List.range c).map fun i ↦ .n (3 + i)))))] ++
      ((List.range c).map (cselDigit (κ / 4) κ c)).flatten ++
      [.atom (.assertEq (.n (cselReb c (c - 1))) (.n 0)),
        .atom (.copy (.n (cselB c c)) (.n (cselSel c (c - 1))))], cselB c c)

/-- **The expansion of `column_selector__L{n}_L{κ}`.** -/
def cselBody (n κ : ℕ) : List Stmt := (cselBodyA n κ).1 ++ [.ret [.n (cselBodyA n κ).2]]

/-! ## Soundness -/

variable {C : CallRel} {σ : Val}

theorem cselBodyA_flat (n κ : ℕ) : (cselBodyA n κ).1.all Stmt.flat = true := by
  unfold cselBodyA
  split
  · simp [osCst, Stmt.flat]
  · simp only [List.all_append, List.all_flatten, List.all_map, Bool.and_eq_true, List.all_eq_true,
      List.mem_range, Function.comp_apply]
    refine ⟨⟨by simp [Stmt.flat], fun i _ ↦ ?_⟩, by simp [Stmt.flat]⟩
    unfold cselDigit
    split <;> simp [Stmt.flat, osMul, osCst, csRc]

/-- A digit's range check: `g^e`, `e < 16`. -/
theorem cselRc {m : ℕ} (hm : m ≤ 32) (hm6 : 6 ≤ m) (L : MemoryImage m) {d b : ℕ}
    (h0 : StmtOk C L.read σ (osCst b (csW 15))) (h1 : StmtOk C L.read σ (csRc d (b + 1) b)) :
    ∃ e < 16, σ (.n d) = gen ^ e := by
  simp only [StmtOk, Atom.Holds] at h0
  exact csRc_gen hm L (x := d) (h := b + 1) (k := b) (K := 16) (by decide)
    (le_trans (show 16 ≤ 2 ^ 6 by decide) (Nat.pow_le_pow_right (by decide) hm6))
    (by rw [h0, csW_eq (by decide), gen_pow_eq_ofK]) h1

theorem cselDigit0_ok {m : ℕ} (hm : m ≤ 32) (hm6 : 6 ≤ m) (L : MemoryImage m) {j0 κ c : ℕ}
    (h : AllOk C L.read σ (cselDigit j0 κ c 0)) :
    ∃ e < 16, σ (.n 3) = gen ^ e ∧
      LoadHolds L.read (σ (.n 1)) (e + (32 * j0 + selOff (4 * j0 + 3 - κ))) (σ (.n (cselSel c 0))) ∧
      LoadHolds L.read (σ (.n 2)) (e + 16 * j0) (σ (.n (cselReb c 0))) := by
  simp only [cselDigit, ↓reduceIte, allOk_cons, allOk_nil, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨e, he, hd⟩ := cselRc hm hm6 L h0 h1
  simp only [StmtOk, Atom.Holds, Nat.add_zero] at h2 h3 h4 h5
  rw [h2, hd, loadHolds_mul_gen_pow] at h3
  rw [h4, hd, loadHolds_mul_gen_pow] at h5
  refine ⟨e, he, hd, ?_, ?_⟩
  · simpa [cselSel, cselB, show 3 + c + 5 = c + 8 by omega] using h3
  · simpa [cselReb, cselB, show 3 + c + 7 = c + 10 by omega] using h5

theorem cselDigitS_ok {m : ℕ} (hm : m ≤ 32) (hm6 : 6 ≤ m) (L : MemoryImage m) {j0 κ c i : ℕ}
    (hi : i ≠ 0) (h : AllOk C L.read σ (cselDigit j0 κ c i)) :
    ∃ e < 16, σ (.n (3 + i)) = gen ^ e ∧
      (∃ v, LoadHolds L.read (σ (.n 1)) (e + (32 * (j0 + i) + 16)) v ∧
        σ (.n (cselSel c i)) = σ (.n (cselSel c (i - 1))) * v) ∧
      ∃ u, LoadHolds L.read (σ (.n 2)) (e + 16 * (j0 + i)) u ∧
        σ (.n (cselReb c i)) = σ (.n (cselReb c (i - 1))) * u := by
  simp only [cselDigit, hi, ↓reduceIte, allOk_cons, allOk_nil, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  obtain ⟨e, he, hd⟩ := cselRc hm hm6 L h0 h1
  simp only [StmtOk, Atom.Holds] at h2 h3 h4 h5 h6 h7
  rw [h2, hd, loadHolds_mul_gen_pow] at h3
  rw [h5, hd, loadHolds_mul_gen_pow] at h6
  have hs : cselSel c i = cselB c i + 6 := by simp [cselSel, cselB, hi]; omega
  have hr : cselReb c i = cselB c i + 9 := by simp [cselReb, cselB, hi]; omega
  exact ⟨e, he, hd, ⟨_, h3, by rw [hs, h4]⟩, ⟨_, h6, by rw [hr, h7]⟩⟩

/-- **`column_selector__L{n}_L{κ}` gives its meaning**, from its template. -/
theorem csel_sound {m : ℕ} (hm : m ≤ 32) (hm6 : 6 ≤ m) (L : MemoryImage m) {name : String} {f : Fn}
    (n κ : ℕ) (hn : n ≤ 8) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = cselBody n κ) (args rets : List E)
    (h : coreProgram.Rel L.read name args rets) : MeaningColumnSelector n κ L.read args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem hfind args rets).mp h
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [hbody, cselBody, holdsList_flat_ret _ (cselBodyA_flat n κ)] at hb
  obtain ⟨hA, hret⟩ := hb
  intro p p1 idx htab hsh hoff hidx hal
  simp only [List.map_cons, List.map_nil] at hret
  by_cases hnk : n ≤ κ / 4
  · -- no nibble: the selector is one
    simp only [cselBodyA, hnk, ↓reduceIte, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
      osCst] at hA hret
    obtain ⟨-, -, -, h4⟩ := hA
    rw [← hret, h4, word_one, Finset.Ico_eq_empty (by omega), Finset.prod_empty]
  · set j0 := κ / 4 with hj0
    set c := n - j0 with hc
    have hc1 : 1 ≤ c := by omega
    simp only [cselBodyA, hnk, ↓reduceIte, ← hj0, ← hc, allOk_append, allOk_cons, allOk_nil, and_true,
      allOk_flatten, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hA hret
    obtain ⟨⟨-, hdig⟩, hassert, hcopy⟩ := hA
    simp only [StmtOk, Atom.Holds] at hassert hcopy
    -- the digits
    have hex : ∀ i < c, ∃ e < 16, σ (.n (3 + i)) = gen ^ e := fun i hi ↦ by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; obtain ⟨e, he, hd, -⟩ := cselDigit0_ok hm hm6 L (hdig 0 hi); exact ⟨e, he, hd⟩
      · obtain ⟨e, he, hd, -⟩ := cselDigitS_ok hm hm6 L (by omega) (hdig i hi); exact ⟨e, he, hd⟩
    choose! e he hd using hex
    have hj9 : ∀ i < c, j0 + i < 9 := fun i hi ↦ by omega
    -- the rebuilt offset
    have hreb : ∀ i < c, σ (.n (cselReb c i)) = gen ^ nibSum e j0 (i + 1) := by
      intro i
      induction i with
      | zero =>
        intro h0
        obtain ⟨e', he', hd', -, hl⟩ := cselDigit0_ok hm hm6 L (hdig 0 h0)
        have : e' = e 0 := gen_pow_inj (by omega) (by have := he 0 h0; omega)
          (by rw [← hd', hd 0 h0])
        subst this
        rw [Nat.add_comm, Nat.add_comm] at hl
        rw [loadHolds_unique hl (by rw [Nat.add_comm]; exact hsh j0 (hj9 0 h0) (e 0) (he 0 h0))]
        simp [nibSum]
      | succ i ih =>
        intro hi
        obtain ⟨e', he', hd', -, u, hl, hr⟩ := cselDigitS_ok hm hm6 L (by omega) (hdig (i + 1) hi)
        have : e' = e (i + 1) := gen_pow_inj (by omega) (by have := he (i + 1) hi; omega)
          (by rw [← hd', hd (i + 1) hi])
        subst this
        rw [hr, Nat.add_sub_cancel, ih (by omega),
          loadHolds_unique hl (by rw [Nat.add_comm]; exact hsh _ (hj9 _ hi) _ (he _ hi)), ← pow_add]
        rfl
    -- the offset is the rebuilt one
    have hidx' : idx = nibSum e j0 c := by
      have hrb := hreb (c - 1) (by omega)
      rw [Nat.sub_add_cancel hc1] at hrb
      have hlt := nibSum_lt e j0 c (fun i hi ↦ he i hi)
      have h16 : 16 ^ (j0 + c) ≤ 2 ^ 32 := by
        rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
      have hn32 : 2 ^ (4 * n) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
      refine gen_pow_inj (by omega) (by omega) ?_
      rw [← hoff, ← hrb]
      exact (e_add_eq_zero_iff.mp hassert).symm
    have hnib : ∀ i < c, nibOf idx (j0 + i) = e i := fun i hi ↦ by
      rw [hidx']; exact nibSum_digit e j0 c (fun i hi ↦ he i hi) i hi
    -- the selector
    have hsel : ∀ i < c, σ (.n (cselSel c i)) =
        ∏ t ∈ Finset.Ico κ (4 * (j0 + i) + 4), selBit p p1 idx t := by
      intro i
      induction i with
      | zero =>
        intro h0
        obtain ⟨e', he', hd', hl, -⟩ := cselDigit0_ok hm hm6 L (hdig 0 h0)
        have : e' = e 0 := gen_pow_inj (by omega) (by have := he 0 h0; omega)
          (by rw [← hd', hd 0 h0])
        subst this
        set lo := κ - 4 * j0 with hlo
        have hlo4 : lo < 4 := by omega
        have hdv : 2 ^ lo ∣ e 0 := by
          rw [← hnib 0 h0, Nat.add_zero, nibOf, Nat.shiftRight_eq_div_pow]
          obtain ⟨q, hq⟩ := hal
          rw [hq, show κ = 4 * j0 + lo by omega, pow_add, mul_assoc,
            Nat.mul_div_cancel_left _ (by positivity),
            show (16 : ℕ) = 2 ^ lo * 2 ^ (4 - lo) by rw [← pow_add, show lo + (4 - lo) = 4 by omega]; rfl,
            Nat.mul_mod_mul_left]
          exact dvd_mul_right _ _
        obtain ⟨k, hk⟩ := hdv
        have hw : 4 * j0 + 3 - κ = 3 - lo := by omega
        have hkk : k * 2 ^ lo = nibOf idx j0 := by rw [← Nat.add_zero j0, hnib 0 h0, hk, mul_comm]
        have hk16 : k < 2 ^ (3 - lo + 1) := by
          have := he 0 h0; rw [hk] at this
          rw [show 3 - lo + 1 = 4 - lo by omega]
          have h2 : 2 ^ lo * k < 2 ^ lo * 2 ^ (4 - lo) := by
            rw [← pow_add, show lo + (4 - lo) = 4 by omega]; exact this
          exact Nat.lt_of_mul_lt_mul_left h2
        have ht := htab j0 (by omega) (3 - lo) (by omega) k hk16
        rw [show 3 - (3 - lo) = lo by omega, show 32 * j0 + selOff (3 - lo) + k * 2 ^ lo =
          e 0 + (32 * j0 + selOff (4 * j0 + 3 - κ)) by rw [hw, hk]; ring] at ht
        rw [loadHolds_unique hl ht, selLev_nib p p1 idx j0 lo k hlo4 hkk, Nat.add_zero,
          show 4 * j0 + lo = κ by omega]
        simp only [Nat.add_zero]
      | succ i ih =>
        intro hi
        obtain ⟨e', he', hd', ⟨v, hl, hs⟩, -⟩ := cselDigitS_ok hm hm6 L (by omega) (hdig (i + 1) hi)
        have : e' = e (i + 1) := gen_pow_inj (by omega) (by have := he (i + 1) hi; omega)
          (by rw [← hd', hd (i + 1) hi])
        subst this
        have ht := htab (j0 + (i + 1)) (by omega) 3 (by decide) (e (i + 1)) (by have := he (i + 1) hi; simpa using this)
        simp only [selOff, List.getD_cons_succ, List.getD_cons_zero, Nat.sub_self, pow_zero,
          mul_one] at ht
        rw [show 32 * (j0 + (i + 1)) + 16 + e (i + 1) = e (i + 1) + (32 * (j0 + (i + 1)) + 16) by ring] at ht
        rw [hs, Nat.add_sub_cancel, ih (by omega), loadHolds_unique hl ht,
          selLev_nib p p1 idx (j0 + (i + 1)) 0 (e (i + 1)) (by decide) (by rw [pow_zero, mul_one, hnib _ hi]),
          Nat.add_zero, show 4 * (j0 + (i + 1)) = 4 * (j0 + i) + 4 by ring,
          Finset.prod_Ico_consecutive _ (by omega) (by omega)]
    rw [← hret, hcopy, hsel (c - 1) (by omega), show 4 * (j0 + (c - 1)) + 4 = 4 * n by omega]

end
end LeanVM.Guest.B1.Stack
