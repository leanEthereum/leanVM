/-
  LeanVM.Guest.B1.Da.Factors

  `da_factors`' template and its meaning (G:4443-4451).
-/

module

public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Da.VectorMath

/-!
# `da_factors` (G:4443-4451)

`da_factors(zs, top, D, at)` (`da_factors__L14_L7_L0`, `core404`; `da_factors__L7_L8_L128`,
`core406`): a heap run `factors` (`.n 1`, `256` words); at each depth `d < D` the power
`zs[top - d]` loaded into `.n (facB d)`, and for each node `2^d + y` the constant
`Ŵ_(top-d)(y · 2^(top-d+1))` (`DA_VHAT[at + 2^d + y]`, here `facC top d y`, read off `wK`), its
product with the power, plus one, written to `factors[2^d + y]` (`facNodeA`). The body is the
template `facT top D` (`facOk`, checked by kernel evaluation in `FactorsChk`), which gives the
meaning (`da_factors_val`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)
open LeanVM.Guest.B1.Digest

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The value of depth `d`'s power. -/
def facB (d : ℕ) : ℕ := 2 + d + 4 * (2 ^ d - 1)

/-- The constant of node `2^d + y`: `Ŵ_(top-d)` at the bits above `top - d`, as a word. -/
def facC (top d y : ℕ) : ℕ := (wK (top - d) (y * 2 ^ (top - d + 1))).toBitVec.toNat

/-- Node `2^d + y`'s atoms. -/
def facNodeA (top d y : ℕ) : List Atom :=
  let v := facB d + 1 + 4 * y
  [.const (.n v) (word (facC top d y) 0), .mul (.n (v + 1)) (.n (facB d)) (.n v),
    .const (.n (v + 2)) (word 1 0), .add (.n (v + 3)) (.n (v + 1)) (.n (v + 2)),
    .load (.n (v + 3)) (.n 1) (2 ^ d + y)]

/-- Depth `d`'s atoms: its power, then its nodes. -/
def facDepthA (top d : ℕ) : List Atom :=
  .load (.n (facB d)) (.n 0) (top - d) :: (List.range (2 ^ d)).flatMap (facNodeA top d)

/-- **`da_factors`' atoms**: the run, the depths, the returned copy. -/
def facT (top D : ℕ) : List Atom :=
  .hint (.alloc (.n 1) 256) :: (List.range D).flatMap (facDepthA top) ++ [.copy (.n (facB D)) (.n 1)]

/-- **`da_factors`' body, checked.** -/
def facOk (fn : Fn) (top D : ℕ) : Bool :=
  decide (fn.params = [.n 0]) &&
  match splitBody fn.body with
  | some (A, vs) => decide (vs = [.n (facB D)]) && atomsEqb A (facT top D)
  | none => false

theorem facC_word (top d y : ℕ) : word (facC top d y) 0 = ofK (wK (top - d) (y * 2 ^ (top - d + 1))) := by
  rw [word_eOfNat, eOfNat, facC]
  congr 1
  simp [K.ofBits]

/-- **A node's facts.** -/
theorem fac_node {top D d y : ℕ} (hd : d < D) (hy : y < 2 ^ d) (hat : ∀ a ∈ facT top D, a.Holds rd σ) :
    LoadHolds rd (σ (.n 0)) (top - d) (σ (.n (facB d))) ∧
      LoadHolds rd (σ (.n 1)) (2 ^ d + y)
        (σ (.n (facB d)) * ofK (wK (top - d) (y * 2 ^ (top - d + 1))) + 1) := by
  have hdep : ∀ a ∈ facDepthA top d, a.Holds rd σ := fun a ha ↦
    hat a (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hd, ha⟩)))
  refine ⟨hdep _ (List.mem_cons_self ..), ?_⟩
  have hn : ∀ a ∈ facNodeA top d y, a.Holds rd σ := fun a ha ↦
    hdep a (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨y, List.mem_range.mpr hy, ha⟩))
  simp only [facNodeA, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Atom.Holds] at hn
  obtain ⟨c, m, c1, a, l⟩ := hn
  rw [a, m, c, c1, facC_word, word_one] at l
  exact l

/-- **`da_factors`' body gives its meaning.** -/
theorem da_factors_val {fn : Fn} {top D : ℕ} (hok : facOk fn top D = true) (hD : D ≤ top + 1)
    {C : CallRel} {args rets : List E} (hpar : fn.params.map σ = args)
    (hb : Stmt.HoldsList C rd σ fn.body False (fun rs ↦ rs = rets)) :
    MeaningDaFactors top D rd args rets := by
  unfold facOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, htm⟩ := hok
    rw [splitBody_eq hsp, holdsList_atoms_ret] at hb
    obtain ⟨hat, hrets⟩ := hb
    rw [atomsEqb_sound htm] at hat
    rw [hparams] at hpar
    subst hpar hrets
    have hcp : σ (.n (facB D)) = σ (.n 1) := by
      have := hat (.copy (.n (facB D)) (.n 1)) (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_singleton_self _)))
      exact this
    simp only [List.map_cons, List.map_nil, MeaningDaFactors]
    refine ⟨fun j ↦ σ (.n (facB (top - j))), fun d hd ↦ ?_, fun n hn1 hn2 ↦ ?_⟩
    · beta_reduce
      rw [show top - (top - d) = d by omega]
      exact (fac_node hd (Nat.two_pow_pos d) hat).1
    · rw [hcp]
      have hl : Nat.log 2 n < D := by
        have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hn2
        exact this
      have hy : n - 2 ^ Nat.log 2 n < 2 ^ Nat.log 2 n := by
        have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
        rw [pow_succ] at h1
        omega
      have hn : n = 2 ^ Nat.log 2 n + (n - 2 ^ Nat.log 2 n) := by
        have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
        omega
      rw [hn, factorAt_node _ hy]
      rw [show top - (top - Nat.log 2 n) = Nat.log 2 n by omega]
      exact (fac_node hl hy hat).2
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Da
