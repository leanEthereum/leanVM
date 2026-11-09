/-
  LeanVM.Guest.Budget.Static

  Static bounds at honest arguments: a loop helper's weight or words run from `1 = g^0` to `g^e`,
  and a loop's guard `1 + g^e` entered only at `e ≠ 0`.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **A loop helper's weight per iteration** (G7-cnt's `Count.LoopWeightLe`): a valid tree from
`g^a` to `g^e` weighs at most `(e - a) · K`. -/
def LoopW (ω : String → ℕ) (f : String) (K : ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E) (a e : ℕ), t.name = f →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram → args.getD 0 0 = ofK
        (addressOfIndex a) →
    args.getD 1 0 = ofK (addressOfIndex e) → a < e → e < 2 ^ 64 - 1 → t.weight ω ≤ (e - a) * K

/-- **A loop helper's words per iteration** (G7-cnt's `Count.LoopTotalLe`). -/
def LoopT (fs : String → ℕ) (f : String) (K : ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E) (a e : ℕ), t.name = f →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram → args.getD 0 0 = ofK
        (addressOfIndex a) →
    args.getD 1 0 = ofK (addressOfIndex e) → a < e → e < 2 ^ 64 - 1 → t.total fs ≤ (e - a) * K

/-- A loop's guard `1 + g^e` is nonzero only at `e ≠ 0` (characteristic `2`). -/
theorem ne_zero_of_guard {e : ℕ} (h : (1 : E) + gen ^ e ≠ 0) : e ≠ 0 := by
  rintro rfl
  exact h (by rw [pow_zero]; exact Value.e_add_eq_zero_iff.mpr rfl)

theorem one_eq_ofK : (1 : E) = ofK (addressOfIndex 0) := by
  rw [← Value.gen_pow_eq_ofK, pow_zero]

/-- **A loop from `1` to `g^e`, entered, weighs at most `e · K`.** -/
theorem LoopW.at {ω : String → ℕ} {f : String} {K : ℕ} (h : LoopW ω f K) {rd : Reader} {t : Tree}
    {args rets : List E} {e : ℕ} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (h0 : args.getD 0 0 = 1) (h1 : args.getD 1 0 = gen ^ e)
    (he0 : e ≠ 0) (he : e < 2 ^ 64 - 1) : t.weight ω ≤ e * K := by
  have := h rd t args rets 0 e hn hv hb (by rw [h0, one_eq_ofK]) (by rw [h1, Value.gen_pow_eq_ofK])
    (by omega) he
  simpa using this

/-- **A loop from `1` to `g^e`, entered, allocates at most `e · K` words.** -/
theorem LoopT.at {fs : String → ℕ} {f : String} {K : ℕ} (h : LoopT fs f K) {rd : Reader} {t : Tree}
    {args rets : List E} {e : ℕ} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (h0 : args.getD 0 0 = 1) (h1 : args.getD 1 0 = gen ^ e)
    (he0 : e ≠ 0) (he : e < 2 ^ 64 - 1) : t.total fs ≤ e * K := by
  have := h rd t args rets 0 e hn hv hb (by rw [h0, one_eq_ofK]) (by rw [h1, Value.gen_pow_eq_ofK])
    (by omega) he
  simpa using this

end
end LeanVM.Guest.Budget
