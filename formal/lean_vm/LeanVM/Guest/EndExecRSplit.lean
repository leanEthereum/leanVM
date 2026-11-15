/-
  LeanVM.Guest.EndExecRSplit

  The frames' splits (`Res.splits`) at the honest frames: `rs_eq_run`'s,
  `shared_selector_tables`' and `verify_keccak`'s `g`-power, rebuilt from its hinted bits.
-/

module

public import LeanVM.Guest.EndExecRS
public import LeanVM.Guest.B1.Exact.RsEqRun
public import LeanVM.Guest.B1.Exact.SharedTables
public import LeanVM.Guest.EndExecRVk

/-!
# The splits

`rs_eq_run` hints the six bits of its argument `[3] = g^c` and asserts `[3] = [37]^8·[23]`, `[23]`
and `[37]` the products of the low and the high three bits' factors (`B1.rsBody`); booleanity
pins each bit, so `[23] = g^b`, `[37] = g^a`, `a, b < 8` (`Value.prod_gen_pow_of_bool`), and
`[3] = g^(8a + b)`. `shared_selector_tables` likewise, `[5] = [39]^4·[20]`, two low bits and four
high ones. On an honest frame the path holds on the reference and names those values, so the
frame holds them (`TopAt.cell`): `SplitAt` (`split_rs`, `split_sst`, `splits_ok`). `verify_keccak`'s
`y_g = step_g^8·rem_g` is `split_vk`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value
open LeanVM.Guest.B2C (cellJ fsN namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

section

variable {σ : Core.Val}

/-- **A top-level atom before any `ret` is on a returning path.** -/
theorem ev_of_get {body : List Stmt} {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs) {k i : ℕ}
    (hk : Memory.Stmt.noRetListS (body.take k) = true) (hi : i < k) {a : Atom}
    (hg : body[i]? = some (.atom a)) : Ev.atom a ∈ es := by
  have hm : Stmt.atom a ∈ body.take k := List.mem_iff_getElem?.mpr ⟨i, by rw [List.getElem?_take, ite_eq_left hi, hg]⟩
  rw [← List.take_append_drop k body, Memory.walk_append] at hw
  rcases Memory.walk_noRet (σ := σ) _ hk with ⟨es1, h1⟩ | h1
  · rw [h1] at hw
    cases h2 : walk σ (body.drop k) with
    | fall _ => rw [h2] at hw; simp [Out.seq, Out.pre] at hw
    | ret es2 _ =>
      rw [h2] at hw
      simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
      rw [← hw.1]
      exact List.mem_append_left _ (Memory.atom_on_path hk h1 hm)
    | stuck => rw [h2] at hw; simp [Out.seq, Out.pre] at hw
  · rw [h1] at hw; simp [Out.seq] at hw

/-- The product of Boolean bits' factors is a power of `g` below `2^n`. -/
theorem bits_gpow {n : ℕ} {b : ℕ → E} (hb : ∀ j < n, b j * b j = b j) :
    ∃ e < 2 ^ n, ∏ j ∈ Finset.range n, (1 + b j * (gen ^ 2 ^ j + 1)) = gen ^ e :=
  ⟨_, bitsVal_lt _ _, prod_gen_pow_of_bool hb⟩

end

variable {A : String → FnAl}

/-- **`rs_eq_run`'s split**: `[3] = [37]^8·[23]`. -/
theorem split_rs : SplitAt A (fn_idx% «rs_eq_run») (.n 37) (.n 23) (.n 3) 8 := by
  intro r K i e hr t
  obtain ⟨vs, hw, hF, hev⟩ := t.events hr
  have hbody : (coreOf (fn_idx% «rs_eq_run»)).body = B1.rsBody := B1.rs_eq_run_body
  have h : Stmt.HoldsList (fun _ _ _ => True) r.img.read e.σ B1.rsBody False (fun _ => True) := by
    rw [← hbody]
    exact holdsList_of_walk _ (by rw [hw]; exact ⟨fun ev he => ⟨hev ev he, fun _ _ _ _ => trivial⟩, trivial⟩)
  obtain ⟨w3, w5, w17⟩ := B1.rs_consts
  simp only [B1.rsBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, -⟩ := h
  have hlo : ∀ j < 3, e.σ (.n (4 + j)) * e.σ (.n (4 + j)) = e.σ (.n (4 + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hhi : ∀ j < 3, e.σ (.n (7 + j)) * e.σ (.n (7 + j)) = e.σ (.n (7 + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : e.σ (.n 23) = ∏ j ∈ Finset.range 3, (1 + e.σ (.n (4 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, B1.word_one]
  have qg : e.σ (.n 37) = ∏ j ∈ Finset.range 3, (1 + e.σ (.n (7 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, B1.word_one]
  obtain ⟨bb, hbb, hb⟩ := bits_gpow (b := fun j ↦ e.σ (.n (4 + j))) hlo
  obtain ⟨aa, haa, hab⟩ := bits_gpow (b := fun j ↦ e.σ (.n (7 + j))) hhi
  replace rg := rg.trans hb
  replace qg := qg.trans hab
  have h3 : e.σ (.n 3) = gen ^ (8 * aa + bb) := by
    rw [← e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, pow_add, pow_mul']
    ring
  have hc : 2 ≤ cellJ (fn_idx% «rs_eq_run») (.n 37) ∧ cellJ (fn_idx% «rs_eq_run») (.n 37) < fsN (fn_idx% «rs_eq_run») ∧
      2 ≤ cellJ (fn_idx% «rs_eq_run») (.n 23) ∧ cellJ (fn_idx% «rs_eq_run») (.n 23) < fsN (fn_idx% «rs_eq_run») ∧
      2 ≤ cellJ (fn_idx% «rs_eq_run») (.n 3) ∧ cellJ (fn_idx% «rs_eq_run») (.n 3) < fsN (fn_idx% «rs_eq_run») := by
    decide +kernel
  have hk : Memory.Stmt.noRetListS ((coreOf (fn_idx% «rs_eq_run»)).body.take 43) = true := by decide +kernel
  have n37 : Ev.atom (.mul (.n 37) (.n 32) (.n 36)) ∈ e.pre ++ e.es :=
    ev_of_get hw hk (i := 34) (by omega) (by rw [hbody]; rfl)
  have n23 : Ev.atom (.mul (.n 23) (.n 18) (.n 22)) ∈ e.pre ++ e.es :=
    ev_of_get hw hk (i := 17) (by omega) (by rw [hbody]; rfl)
  refine ⟨aa, bb, ?_, ?_, ?_, by omega⟩
  · rw [t.cell hr hF (namedOf_atom n37 (by simp [atomUses])) hc.1 hc.2.1, qg, gen_pow_eq_ofK]
  · rw [t.cell hr hF (namedOf_atom n23 (by simp [atomUses])) hc.2.2.1 hc.2.2.2.1, rg, gen_pow_eq_ofK]
  · rw [t.cell hr hF (List.mem_append_left _ (List.mem_append_left _ (by decide +kernel))) hc.2.2.2.2.1
      hc.2.2.2.2.2, h3, gen_pow_eq_ofK]

/-- **`shared_selector_tables`' split**: `[5] = [39]^4·[20]`. -/
theorem split_sst : SplitAt A (fn_idx% «shared_selector_tables») (.n 39) (.n 20) (.n 5) 4 := by
  intro r K i e hr t
  obtain ⟨vs, hw, hF, hev⟩ := t.events hr
  have hbody : (coreOf (fn_idx% «shared_selector_tables»)).body = Fn.«shared_selector_tables».core.body := rfl
  have h : Stmt.HoldsList (fun _ _ _ => True) r.img.read e.σ Fn.«shared_selector_tables».core.body False
      (fun _ => True) := by
    rw [← hbody]
    exact holdsList_of_walk _ (by rw [hw]; exact ⟨fun ev he => ⟨hev ev he, fun _ _ _ _ => trivial⟩, trivial⟩)
  have w3 := B1.word_gpow_one 0 (by norm_num) 3 (by decide)
  have w5 := B1.word_gpow_one 1 (by norm_num) 5 (by decide)
  have w17 := B1.word_gpow_one 2 (by norm_num) 17 (by decide)
  have w257 := B1.word_gpow_one 3 (by norm_num) 257 (by decide)
  simp only [Fn.«shared_selector_tables».core.body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨m6, m7, m8, m9, m10, m11, c12, c13, h14, h15, c16, c17, h18, h19, h20, c21, c22, h23, h24, c25, c26, h27,
    h28, h29, c30, c31, h32, h33, h34, c35, c36, h37, h38, h39, h40, h41, h42, ha, -⟩ := h
  have hlo : ∀ j < 2, e.σ (.n (6 + j)) * e.σ (.n (6 + j)) = e.σ (.n (6 + j)) := by
    intro j hj; interval_cases j
    exacts [m6.symm, m7.symm]
  have hhi : ∀ j < 4, e.σ (.n (8 + j)) * e.σ (.n (8 + j)) = e.σ (.n (8 + j)) := by
    intro j hj; interval_cases j
    exacts [m8.symm, m9.symm, m10.symm, m11.symm]
  have rg : e.σ (.n 20) = ∏ j ∈ Finset.range 2, (1 + e.σ (.n (6 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h20, h15, h19, c12, h14, c13, c16, h18, c17, w3, w5, B1.word_one]
  have qg : e.σ (.n 39) = ∏ j ∈ Finset.range 4, (1 + e.σ (.n (8 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h39, h34, h29, h24, h28, h33, h38, c21, h23, c22, c25, h27, c26, c30, h32, c31, c35, h37, c36, w3, w5, w17,
      w257, B1.word_one]
  obtain ⟨bb, hbb, hb⟩ := bits_gpow (b := fun j ↦ e.σ (.n (6 + j))) hlo
  obtain ⟨aa, haa, hab⟩ := bits_gpow (b := fun j ↦ e.σ (.n (8 + j))) hhi
  replace rg := rg.trans hb
  replace qg := qg.trans hab
  have h5 : e.σ (.n 5) = gen ^ (4 * aa + bb) := by
    rw [← e_add_eq_zero_iff.mp ha, h42, h41, h40, qg, rg, pow_add, pow_mul']
    ring
  have hc : 2 ≤ cellJ (fn_idx% «shared_selector_tables») (.n 39) ∧
      cellJ (fn_idx% «shared_selector_tables») (.n 39) < fsN (fn_idx% «shared_selector_tables») ∧
      2 ≤ cellJ (fn_idx% «shared_selector_tables») (.n 20) ∧
      cellJ (fn_idx% «shared_selector_tables») (.n 20) < fsN (fn_idx% «shared_selector_tables») ∧
      2 ≤ cellJ (fn_idx% «shared_selector_tables») (.n 5) ∧
      cellJ (fn_idx% «shared_selector_tables») (.n 5) < fsN (fn_idx% «shared_selector_tables») := by
    decide +kernel
  have hk : Memory.Stmt.noRetListS ((coreOf (fn_idx% «shared_selector_tables»)).body.take 42) = true := by
    decide +kernel
  have n39 : Ev.atom (.mul (.n 39) (.n 34) (.n 38)) ∈ e.pre ++ e.es :=
    ev_of_get hw hk (i := 34) (by omega) (by rw [hbody]; rfl)
  have n20 : Ev.atom (.mul (.n 20) (.n 15) (.n 19)) ∈ e.pre ++ e.es :=
    ev_of_get hw hk (i := 15) (by omega) (by rw [hbody]; rfl)
  refine ⟨aa, bb, ?_, ?_, ?_, by omega⟩
  · rw [t.cell hr hF (namedOf_atom n39 (by simp [atomUses])) hc.1 hc.2.1, qg, gen_pow_eq_ofK]
  · rw [t.cell hr hF (namedOf_atom n20 (by simp [atomUses])) hc.2.2.1 hc.2.2.2.1, rg, gen_pow_eq_ofK]
  · rw [t.cell hr hF (List.mem_append_left _ (List.mem_append_left _ (by decide +kernel))) hc.2.2.2.2.1
      hc.2.2.2.2.2, h5, gen_pow_eq_ofK]

/-- **The frames' splits at the honest frames.** -/
theorem splits_ok : ∀ p ∈ Res.splits, SplitAt A p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  simp only [Res.splits, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨split_rs, split_sst, split_vk⟩

end

end LeanVM.Guest.EndExec
