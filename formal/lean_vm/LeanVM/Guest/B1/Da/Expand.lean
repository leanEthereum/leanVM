/-
  LeanVM.Guest.B1.Da.Expand

  `da_expand`'s template and its meaning (G:4454-4467).
-/

module

public import LeanVM.Guest.B1.Da.Factors

/-!
# `da_expand` (G:4454-4467)

`da_expand(root, factors, zs, shifts, top, D)` (`da_expand__L7_L8`, `core402`; `da_expand__L14_L7`,
`core405`): the tree's nodes are values, node `1` the root (`.n 4`); depth `d` loads its power and
shift (`.n (expB d)`, `.n (expB d + 1)`), and node `2^d + y` its factor (`.n s`,
`s = expB d + 2 + 5y`), adds the shift, and makes its children `node · (factor + shift)` (`s + 2`)
and that plus `node · z` (`s + 4`) (`expDepthA`). The nodes are the frame run `nodes` (a fresh word,
the nodes in heap order, fresh words up to `512`), and the function returns `nodes · g^(2^D)`, its
leaves (`expT`, `expOk`, checked by kernel evaluation in `ExpandChk`). `exp_node`: node `2^d + y` is
`expandLeaf … d y`; `da_expand_val`: the meaning.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)
open LeanVM.Guest.B1.Digest

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The first value of depth `d`: its power, then its shift. -/
def expB (d : ℕ) : ℕ := 5 + 2 * d + 5 * (2 ^ d - 1)

/-- The value of node `2^d + y`. -/
def nodeAt : ℕ → ℕ → ℕ
  | 0, _ => 4
  | d + 1, y => expB d + 4 + 5 * (y / 2) + 2 * (y % 2)

/-- Node `2^d + y`'s atoms. -/
def expNodeA (d y : ℕ) : List Atom :=
  let s := expB d + 2 + 5 * y
  [.load (.n s) (.n 1) (2 ^ d + y), .add (.n (s + 1)) (.n s) (.n (expB d + 1)),
    .mul (.n (s + 2)) (.n (nodeAt d y)) (.n (s + 1)), .mul (.n (s + 3)) (.n (nodeAt d y)) (.n (expB d)),
    .add (.n (s + 4)) (.n (s + 2)) (.n (s + 3))]

/-- Depth `d`'s atoms. -/
def expDepthA (top d : ℕ) : List Atom :=
  .load (.n (expB d)) (.n 2) (top - d) :: .load (.n (expB d + 1)) (.n 3) (top - d) ::
    (List.range (2 ^ d)).flatMap (expNodeA d)

/-- The nodes of depths below `D`, in heap order. -/
def nodesBelow (D : ℕ) : List V := (List.range D).flatMap fun d ↦ (List.range (2 ^ d)).map (V.n ∘ nodeAt d)

/-- The frame run `nodes`: a fresh word, the nodes, fresh words up to `512`. -/
def expRun (D : ℕ) : List V :=
  .n (expB D + 1) :: nodesBelow (D + 1) ++ (List.range (512 - 2 ^ (D + 1))).map fun i ↦ .n (expB D + 2 + i)

/-- The value of the leaves' offset. -/
def expC (D : ℕ) : ℕ := expB D + 2 + (512 - 2 ^ (D + 1))

/-- `da_expand`'s computing atoms: the root's copy, then the depths. -/
def expBodyA (top D : ℕ) : List Atom := .copy (.n 4) (.n 0) :: (List.range D).flatMap (expDepthA top)

/-- **`da_expand`'s atoms**, `W` the word of `g^(2^D)`. -/
def expT (top D W : ℕ) : List Atom :=
  expBodyA top D ++
    [.frameAddr (.n (expB D)) (expRun D), .const (.n (expC D)) (word W 0 0),
      .mul (.n (expC D + 1)) (.n (expB D)) (.n (expC D))]

/-- **`da_expand`'s body, checked.** -/
def expOk (fn : Fn) (top D W : ℕ) : Bool :=
  decide (fn.params = [.n 0, .n 1, .n 2, .n 3]) && decide (K.ofBits W = addressOfIndex (2 ^ D)) &&
  match splitBody fn.body with
  | some (A, vs) => decide (vs = [.n (expC D + 1)]) && atomsEqb A (expT top D W)
  | none => false

theorem length_nodesBelow : ∀ D, (nodesBelow D).length = 2 ^ D - 1
  | 0 => rfl
  | D + 1 => by
    rw [nodesBelow, List.range_succ, List.flatMap_append, List.length_append, ← nodesBelow,
      length_nodesBelow D]
    simp only [List.flatMap_singleton, List.length_map, List.length_range, pow_succ]
    have := Nat.one_le_two_pow (n := D)
    omega

/-- The run's word `2^D + k` is leaf `k`'s value. -/
theorem expRun_leaf {D k : ℕ} (hk : k < 2 ^ D) (h : 2 ^ D + k < (expRun D).length) :
    (expRun D)[2 ^ D + k] = .n (nodeAt D k) := by
  have h1 : (nodesBelow D).length = 2 ^ D - 1 := length_nodesBelow D
  have hp := Nat.one_le_two_pow (n := D)
  have hsplit : nodesBelow (D + 1) = nodesBelow D ++ (List.range (2 ^ D)).map (V.n ∘ nodeAt D) := by
    rw [nodesBelow, List.range_succ, List.flatMap_append, ← nodesBelow]
    simp
  have h? : (expRun D)[2 ^ D + k]? = some (.n (nodeAt D k)) := by
    rw [show 2 ^ D + k = (2 ^ D - 1 + k) + 1 by omega, expRun, List.cons_append,
      List.getElem?_cons_succ, hsplit,
      List.append_assoc, List.getElem?_append_right (by omega),
      show 2 ^ D - 1 + k - (nodesBelow D).length = k by omega,
      List.getElem?_append_left (by simp; omega)]
    simp [hk]
  rw [List.getElem?_eq_getElem h] at h?
  exact Option.some.inj h?

/-- **A depth's facts**: the power and the shift it loads, and the children of each node. -/
theorem exp_depth {top D d y : ℕ} (hd : d < D) (hy : y < 2 ^ d)
    (hat : ∀ a ∈ expBodyA top D, a.Holds rd σ) :
    LoadHolds rd (σ (.n 2)) (top - d) (σ (.n (expB d))) ∧
      LoadHolds rd (σ (.n 3)) (top - d) (σ (.n (expB d + 1))) ∧
      LoadHolds rd (σ (.n 1)) (2 ^ d + y) (memAt rd (σ (.n 1)) (2 ^ d + y)) ∧
      ∀ b < 2, σ (.n (nodeAt (d + 1) (2 * y + b))) = σ (.n (nodeAt d y)) *
        (memAt rd (σ (.n 1)) (2 ^ d + y) + σ (.n (expB d + 1)) + if b = 1 then σ (.n (expB d)) else 0) := by
  have hdep : ∀ a ∈ expDepthA top d, a.Holds rd σ := fun a ha ↦
    hat a (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hd, ha⟩))
  have hn : ∀ a ∈ expNodeA d y, a.Holds rd σ := fun a ha ↦
    hdep a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨y, List.mem_range.mpr hy, ha⟩)))
  refine ⟨hdep _ (List.mem_cons_self ..), hdep _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
  simp only [expNodeA, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Atom.Holds] at hn
  obtain ⟨l, a1, m2, m3, a4⟩ := hn
  have hf := memAt_of_load l
  refine ⟨by rw [hf]; exact l, fun b hb ↦ ?_⟩
  have hv : nodeAt (d + 1) (2 * y + b) = expB d + 2 + 5 * y + 2 + 2 * b := by
    simp only [nodeAt]
    rw [show (2 * y + b) / 2 = y by omega, show (2 * y + b) % 2 = b by omega]
    omega
  rw [hv, hf]
  interval_cases b
  · simp only [Nat.mul_zero, show (0 : ℕ) ≠ 1 by decide, ite_false, add_zero]
    rw [m2, a1]
  · simp only [ite_true, Nat.mul_one]
    rw [show expB d + 2 + 5 * y + 2 + 2 = expB d + 2 + 5 * y + 4 by omega, a4, m2, m3, a1]
    ring

/-- **Node `2^d + y` is `expandLeaf … d y`**, the factors read at `factors`, the powers and shifts
at `zs` and `shifts`. -/
theorem exp_node {top D : ℕ} (hat : ∀ a ∈ expBodyA top D, a.Holds rd σ) (hD : D ≤ top + 1) :
    ∀ d ≤ D, ∀ y < 2 ^ d, σ (.n (nodeAt d y)) =
      expandLeaf (σ (.n 0)) (memAt rd (σ (.n 1))) (fun j ↦ σ (.n (expB (top - j))))
        (fun j ↦ σ (.n (expB (top - j) + 1))) top d y
  | 0, _, y, _ => by
    have h4 : σ (.n 4) = σ (.n 0) := hat _ (List.mem_cons_self ..)
    rw [show nodeAt 0 y = 4 from rfl, h4, expandLeaf, List.range_zero, List.map_nil, List.prod_nil,
      mul_one]
  | d + 1, hd, y, hy => by
    have hy2 : y / 2 < 2 ^ d := by rw [pow_succ] at hy; omega
    have ih := exp_node hat hD d (by omega) (y / 2) hy2
    obtain ⟨-, -, -, hc⟩ := exp_depth (show d < D by omega) hy2 hat
    have hc' := hc (y % 2) (Nat.mod_lt _ (by norm_num))
    rw [show 2 * (y / 2) + y % 2 = y by omega] at hc'
    rw [hc', ih, expandLeaf, expandLeaf, List.range_succ, List.map_append, List.prod_append,
      mul_assoc]
    refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) ?_ ?_)
    · refine congrArg List.prod (List.map_congr_left fun k hk ↦ ?_)
      have hk' := List.mem_range.mp hk
      rw [show d + 1 - k = (d - k) + 1 by omega, Nat.shiftRight_add, Nat.shiftRight_one,
        show d + 1 - 1 - k = (d - 1 - k) + 1 by omega, ← Nat.testBit_div_two]
      have : (y / 2) >>> (d - k) = y >>> (d - k) / 2 := by
        simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, mul_comm]
      rw [this]
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        show d + 1 - d = 1 by omega, Nat.shiftRight_one, show d + 1 - 1 - d = 0 by omega,
        Nat.testBit_zero, show top - (top - d) = d by omega]
      rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]

/-- **`da_expand`'s body gives its meaning.** -/
theorem da_expand_val {fn : Fn} {top D W : ℕ} (hok : expOk fn top D W = true) (hD : D ≤ top + 1)
    (hD9 : D ≤ 8) {C : CallRel} {args rets : List E} (hpar : fn.params.map σ = args)
    (hb : Stmt.HoldsList C rd σ fn.body False (fun rs ↦ rs = rets)) :
    MeaningDaExpand top D rd args rets := by
  unfold expOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hparams, hW⟩, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, htm⟩ := hok
    rw [splitBody_eq hsp, holdsList_atoms_ret] at hb
    obtain ⟨hat, hrets⟩ := hb
    rw [atomsEqb_sound htm] at hat
    rw [hparams] at hpar
    subst hpar hrets
    have hatB : ∀ a ∈ expBodyA top D, a.Holds rd σ := fun a ha ↦ hat a (List.mem_append_left _ ha)
    have hend : ∀ a ∈ [Atom.frameAddr (.n (expB D)) (expRun D), .const (.n (expC D)) (word W 0 0),
        .mul (.n (expC D + 1)) (.n (expB D)) (.n (expC D))], a.Holds rd σ := fun a ha ↦
      hat a (List.mem_append_right _ ha)
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      Atom.Holds] at hend
    obtain ⟨⟨hfk, hfr⟩, hcst, hmul⟩ := hend
    simp only [List.map_cons, List.map_nil, MeaningDaExpand]
    refine ⟨memAt rd (σ (.n 1)), fun j ↦ σ (.n (expB (top - j))),
      fun j ↦ σ (.n (expB (top - j) + 1)), fun n hn1 hn2 ↦ ?_, fun d hd ↦ ?_, fun d hd ↦ ?_, ?_⟩
    · have hl : Nat.log 2 n < D := Nat.log_lt_of_lt_pow (by omega) hn2
      have hy : n - 2 ^ Nat.log 2 n < 2 ^ Nat.log 2 n := by
        have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
        rw [pow_succ] at h1
        omega
      have hn : n = 2 ^ Nat.log 2 n + (n - 2 ^ Nat.log 2 n) := by
        have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
        omega
      rw [hn]
      exact (exp_depth hl hy hatB).2.2.1
    · beta_reduce
      rw [show top - (top - d) = d by omega]
      exact (exp_depth hd (Nat.two_pow_pos d) hatB).1
    · beta_reduce
      rw [show top - (top - d) = d by omega]
      exact (exp_depth hd (Nat.two_pow_pos d) hatB).2.1
    · have hw : word W 0 0 = ofK (addressOfIndex (2 ^ D)) := by
        rw [word_eOfNat, eOfNat, hW]
      rw [hmul, hcst, hw]
      refine ⟨isInK_mul hfk (ofK_isInK _), fun k hk w hr ↦ ?_⟩
      rw [limb0_mul_ofK hfk, mul_assoc, addressOfIndex, addressOfIndex, ← pow_add] at hr
      have hlen : (expRun D).length = 512 := by
        simp only [expRun, List.length_cons, List.length_append, List.length_map, List.length_range,
          length_nodesBelow]
        have : 2 ^ (D + 1) ≤ 512 := by
          calc 2 ^ (D + 1) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 512 := by norm_num
        have := Nat.one_le_two_pow (n := D + 1)
        omega
      have hidx : 2 ^ D + k < (expRun D).length := by
        rw [hlen]
        have : 2 ^ D ≤ 256 := by
          calc 2 ^ D ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hD9
            _ = 256 := by norm_num
        omega
      rw [hfr (2 ^ D + k) hidx w (by rw [addressOfIndex]; exact hr), expRun_leaf hk hidx]
      exact exp_node hatB hD D le_rfl k hk
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Da
