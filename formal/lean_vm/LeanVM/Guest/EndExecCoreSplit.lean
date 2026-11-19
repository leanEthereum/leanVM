/-
  LeanVM.Guest.EndExecCoreSplit

  The `split` family (`CoreMode.splitFam`) sound: `rs_eq_run`'s and `shared_selector_tables`'
  `g`-powers split from their hinted bits on every returning path, and the residuals a split gives.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.HeapCSound
public import LeanVM.Guest.B1.Exact.RsEqRun
public import LeanVM.Guest.B1.Exact.SharedTables

/-!
# Split `g`-powers

`rs_eq_run` hints the six bits of its `count = g^c` and asserts `count = q^8·r`, `q` and `r` the products of the high
and the low three bits' factors; booleanity pins each bit, so `q = g^a`, `r = g^b`, `a, b < 8` and `c = 8a + b`
(`splitW_rs`). `shared_selector_tables` likewise, `len = q^4·r`, four high bits and two low ones (`splitW_sst`). The
monomials the heap certificate names `q` and `r` by are the products of the factors' values (`SplitC.q`, `SplitC.r`).

`splitRes_sound`: at such a valuation, a split's residuals hold: exponent bounds from `a < A`, `b < S`; under the arm
`j` of the selector `r`, `b = j`, so `q^S·g^c` is below `n = g^(S·a + b)` for `c < j`; the loop's strided runs
`[base]·g^i·g^(S·[0, a))`, `i < S`, are cells `i + S·j' < S·a ≤ S·a + b` of `[base]·[0, e(n))`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CRes CCond CCell CRun CIdx LtF rep_of capE idxC vw prodW SplitC splitsC powB splitRes
  splitFam)
open LeanVM.Protocol.Verifier (gen)

public section

/-- **A split at a valuation**: `q` names `g^a`, `r` and `rv` name `g^b`, `n` names `g^(S·a + b)`, `a < A`,
`b < S`. -/
structure SplitV (sp : SplitC) (σ : Val) (a b : ℕ) : Prop where
  ha : a < sp.A
  hb : b < sp.S
  hcap : sp.S * a + b < capE
  hq : prodW (vw σ) sp.q = gen ^ a
  hr : prodW (vw σ) sp.r = gen ^ b
  hrv : σ (V.n sp.rv) = gen ^ b
  hn : σ (V.n sp.n) = gen ^ (sp.S * a + b)

/-- **A function's split**: on every returning path whose events hold, the split at its valuation. -/
def SplitW (fn : Fn) (sp : SplitC) : Prop :=
  ∀ (rd : Reader) (σ : Val) (es : List Ev) (vs : List V), walk σ fn.body = .ret es vs →
    (∀ ev ∈ es, ev.Holds rd σ) → ∃ a b, SplitV sp σ a b

/-- The product of Boolean bits' factors is a power of `g` below `2^n`. -/
theorem split_bits_gpow {n : ℕ} {b : ℕ → E} (hb : ∀ j < n, b j * b j = b j) :
    ∃ e < 2 ^ n, ∏ j ∈ Finset.range n, (1 + b j * (gen ^ 2 ^ j + 1)) = gen ^ e :=
  ⟨_, Value.bitsVal_lt _ _, Value.prod_gen_pow_of_bool hb⟩

/-- **`rs_eq_run`'s split**: `[3] = q^8·[23]`, `q = [27]·[31]·[36]` (its value `37`), `[23] = [13]·[17]·[22]`. -/
theorem splitW_rs : SplitW (fn% «rs_eq_run») ⟨[(27, 1), (31, 1), (36, 1)], [(13, 1), (17, 1), (22, 1)], 23, 3, 8, 8⟩ := by
  intro rd σ es vs hw hev
  obtain ⟨w3, w5, w17⟩ := B1.rs_consts
  have h : Stmt.HoldsList (fun _ _ _ => True) rd σ (fn% «rs_eq_run»).body False (fun _ => True) :=
    holdsList_of_walk _ (by rw [hw]; exact ⟨fun e he => ⟨hev e he, fun _ _ _ _ => trivial⟩, trivial⟩)
  rw [B1.rs_eq_run_body, B1.rsBody] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, -⟩ := h
  have hlo : ∀ j < 3, σ (.n (4 + j)) * σ (.n (4 + j)) = σ (.n (4 + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hhi : ∀ j < 3, σ (.n (7 + j)) * σ (.n (7 + j)) = σ (.n (7 + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n 23) = ∏ j ∈ Finset.range 3, (1 + σ (.n (4 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, B1.word_one]
  have qg : σ (.n 37) = ∏ j ∈ Finset.range 3, (1 + σ (.n (7 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, B1.word_one]
  obtain ⟨bb, hbb, hb⟩ := split_bits_gpow (b := fun j ↦ σ (.n (4 + j))) hlo
  obtain ⟨aa, haa, hab⟩ := split_bits_gpow (b := fun j ↦ σ (.n (7 + j))) hhi
  replace rg := rg.trans hb
  replace qg := qg.trans hab
  have h3 : σ (.n 3) = gen ^ (8 * aa + bb) := by
    rw [← Value.e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, pow_add, pow_mul']
    ring
  have haa' : aa < 8 := by simpa using haa
  have hbb' : bb < 8 := by simpa using hbb
  refine ⟨aa, bb, ⟨haa', hbb', show 8 * aa + bb < capE by unfold capE; omega, ?_, ?_, rg, h3⟩⟩
  · simp only [CoreMode.prodW, vw, pow_one, mul_one]
    rw [← qg, h37, h32, mul_assoc]
  · simp only [CoreMode.prodW, vw, pow_one, mul_one]
    rw [← rg, h23, h18, mul_assoc]

/-- **`shared_selector_tables`' split**: `[5] = q^4·[20]`, `q = [24]·[28]·[33]·[38]` (its value `39`),
`[20] = [15]·[19]`. -/
theorem splitW_sst : SplitW (fn% «shared_selector_tables»)
    ⟨[(24, 1), (28, 1), (33, 1), (38, 1)], [(15, 1), (19, 1)], 20, 5, 4, 16⟩ := by
  intro rd σ es vs hw hev
  have h : Stmt.HoldsList (fun _ _ _ => True) rd σ (fn% «shared_selector_tables»).body False (fun _ => True) :=
    holdsList_of_walk _ (by rw [hw]; exact ⟨fun e he => ⟨hev e he, fun _ _ _ _ => trivial⟩, trivial⟩)
  have hbody : (fn% «shared_selector_tables»).body = Fn.«shared_selector_tables».core.body := rfl
  rw [hbody] at h
  have w3 := B1.word_gpow_one 0 (by norm_num) 3 (by decide)
  have w5 := B1.word_gpow_one 1 (by norm_num) 5 (by decide)
  have w17 := B1.word_gpow_one 2 (by norm_num) 17 (by decide)
  have w257 := B1.word_gpow_one 3 (by norm_num) 257 (by decide)
  simp only [Fn.«shared_selector_tables».core.body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨m6, m7, m8, m9, m10, m11, c12, c13, h14, h15, c16, c17, h18, h19, h20, c21, c22, h23, h24, c25, c26, h27,
    h28, h29, c30, c31, h32, h33, h34, c35, c36, h37, h38, h39, h40, h41, h42, ha, -⟩ := h
  have hlo : ∀ j < 2, σ (.n (6 + j)) * σ (.n (6 + j)) = σ (.n (6 + j)) := by
    intro j hj; interval_cases j
    exacts [m6.symm, m7.symm]
  have hhi : ∀ j < 4, σ (.n (8 + j)) * σ (.n (8 + j)) = σ (.n (8 + j)) := by
    intro j hj; interval_cases j
    exacts [m8.symm, m9.symm, m10.symm, m11.symm]
  have rg : σ (.n 20) = ∏ j ∈ Finset.range 2, (1 + σ (.n (6 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h20, h15, h19, c12, h14, c13, c16, h18, c17, w3, w5, B1.word_one]
  have qg : σ (.n 39) = ∏ j ∈ Finset.range 4, (1 + σ (.n (8 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h39, h34, h29, h24, h28, h33, h38, c21, h23, c22, c25, h27, c26, c30, h32, c31, c35, h37, c36, w3, w5, w17,
      w257, B1.word_one]
  obtain ⟨bb, hbb, hb⟩ := split_bits_gpow (b := fun j ↦ σ (.n (6 + j))) hlo
  obtain ⟨aa, haa, hab⟩ := split_bits_gpow (b := fun j ↦ σ (.n (8 + j))) hhi
  replace rg := rg.trans hb
  replace qg := qg.trans hab
  have h5 : σ (.n 5) = gen ^ (4 * aa + bb) := by
    rw [← Value.e_add_eq_zero_iff.mp ha, h42, h41, h40, qg, rg, pow_add, pow_mul']
    ring
  have haa' : aa < 16 := by simpa using haa
  have hbb' : bb < 4 := by simpa using hbb
  refine ⟨aa, bb, ⟨haa', hbb', show 4 * aa + bb < capE by unfold capE; omega, ?_, ?_, rg, h5⟩⟩
  · simp only [CoreMode.prodW, vw, pow_one, mul_one]
    rw [← qg, h39, h34, h29, mul_assoc, mul_assoc]
  · simp only [CoreMode.prodW, vw, pow_one, mul_one]
    rw [← rg, h20]

/-- **The splits hold** at their functions. -/
theorem splitsC_ok : ∀ p ∈ splitsC, ∀ fn, coreProgram.find? p.1 = some fn → SplitW fn p.2 := by
  simp only [splitsC, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨fun fn hf ↦ ?_, fun fn hf ↦ ?_⟩
  · rw [B1.find_rs_eq_run] at hf
    obtain rfl := Option.some.inj hf
    exact splitW_rs
  · rw [B1.find_sst] at hf
    obtain rfl := Option.some.inj hf
    exact splitW_sst

/-! ## The residuals a split gives -/

theorem split_prodW_powB (w : ℕ → E) (k : ℕ) : ∀ bs, prodW w (powB k bs) = prodW w bs ^ k
  | [] => by simp [powB, prodW]
  | (b, e) :: l => by
    have ih := split_prodW_powB w k l
    simp only [powB, List.map_cons, prodW] at ih ⊢
    rw [ih, mul_pow, ← pow_mul, mul_comm k e]

theorem split_valW {w : ℕ → E} {bs : List (ℕ × ℕ)} {a : ℕ} (h : prodW w bs = gen ^ a) (off : ℕ) :
    (⟨bs, off⟩ : CCell).valW w = ofK (addressOfIndex (a + off)) := by
  rw [CCell.valW, h, Value.gen_pow_eq_ofK, ← CoreMode.ofK_mul']
  simp only [addressOfIndex, pow_add]

theorem split_rep {w : ℕ → E} {bs : List (ℕ × ℕ)} {a : ℕ} (h : prodW w bs = gen ^ a) {off : ℕ} (hc : a + off < capE) :
    CoreMode.rep ((⟨bs, off⟩ : CCell).valW w) = some (a + off) := by
  rw [split_valW h]
  exact rep_of hc

theorem splitGen_inj {i j : ℕ} (hi : i < capE) (hj : j < capE) (h : ofK (addressOfIndex i) = ofK (addressOfIndex j)) :
    i = j := by
  have := (rep_of hi).symm.trans (h ▸ rep_of hj)
  exact Option.some.inj this

/-- **A split's residuals hold** at a valuation where the split does and the branch conditions `cs` hold. -/
theorem splitRes_sound {sp : SplitC} {σ : Val} {a b : ℕ} (hs : SplitV sp σ a b) :
    ∀ (x : CRes) (cs : List CCond), (∀ c ∈ cs, c.Holds σ) → splitRes sp cs x = true → x.Holds σ
  | .lt (.mono ⟨bs, off⟩) (.num N), cs, _, h => by
    simp only [splitRes, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hN, (⟨rfl, ho⟩ | ⟨rfl, ho⟩) | ⟨rfl, ho⟩⟩ := h
    · have := hs.ha
      exact ⟨a + off, N, split_rep hs.hq (by omega), CoreMode.rep_const hN, by omega⟩
    · have := hs.ha
      have hq : prodW (vw σ) (powB sp.S sp.q) = gen ^ (sp.S * a) := by rw [split_prodW_powB, hs.hq, ← pow_mul, mul_comm]
      have : sp.S * a ≤ sp.S * (sp.A - 1) := Nat.mul_le_mul_left _ (by omega)
      exact ⟨sp.S * a + off, N, split_rep hq (by omega), CoreMode.rep_const hN, by omega⟩
    · have := hs.hb
      exact ⟨b + off, N, split_rep hs.hr (by omega), CoreMode.rep_const hN, by omega⟩
  | .lt (.mono ⟨bs, off⟩) (.val n), cs, hcs, h => by
    simp only [splitRes, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, c, hc, hcx⟩ := h
    cases c with
    | arm x j =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcx
      obtain ⟨⟨rfl, hoj⟩, hj⟩ := hcx
      have hx : σ (V.n sp.rv) = ofK (addressOfIndex j) := hcs _ hc
      have hbS := hs.hb
      have hbj : b = j := splitGen_inj (by have := hs.hcap; omega) hj
        (by rw [← Value.gen_pow_eq_ofK, ← hs.hrv, hx])
      subst hbj
      have hq : prodW (vw σ) (powB sp.S sp.q) = gen ^ (sp.S * a) := by rw [split_prodW_powB, hs.hq, ← pow_mul, mul_comm]
      have hcap := hs.hcap
      refine ⟨sp.S * a + off, sp.S * a + b, split_rep hq (by omega), ?_, by omega⟩
      simp only [idxC, CoreMode.valW_baseC, vw, hs.hn, Value.gen_pow_eq_ofK]
      exact rep_of hcap
    | zero _ | nonzero _ => simp at hcx
  | .subR ⟨⟨qb, qo⟩, S, ql, qh⟩ r, cs, _, h => by
    simp only [splitRes, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hqo⟩, rfl⟩ := h
    intro x hx
    obtain ⟨ylo, yhi, j, hylo, hyhi, hlj, hjh, rfl⟩ := hx
    have hcap := hs.hcap
    have ha := hs.ha
    have haS : a ≤ sp.S * a := Nat.le_mul_of_pos_left _ (by omega)
    simp only [idxC] at hylo hyhi
    rw [CoreMode.rep_const (by unfold capE; norm_num), Option.some.injEq] at hylo
    rw [show (⟨sp.q, 0⟩ : CCell) = ⟨sp.q, 0⟩ from rfl, split_rep hs.hq (by omega), Option.some.injEq] at hyhi
    subst hylo hyhi
    have hjS : qo + sp.S * j < sp.S * a + b := by
      have h1 : sp.S * (j + 1) ≤ sp.S * a := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, mul_one] at h1
      omega
    refine ⟨0, sp.S * a + b, qo + sp.S * j, CoreMode.rep_const (by unfold capE; norm_num), ?_, by omega, hjS, ?_⟩
    · simp only [idxC, CoreMode.valW_baseC, vw, hs.hn, Value.gen_pow_eq_ofK]
      exact rep_of hcap
    · simp only [CCell.valW, mul_assoc, ← CoreMode.ofK_mul', addressOfIndex, ← pow_add, zero_add, one_mul]
  | .under cs' r, cs, hcs, h => fun hcs' ↦ by
    simp only [splitRes] at h
    exact splitRes_sound hs r (cs ++ cs') (fun c hc ↦ (List.mem_append.mp hc).elim (hcs c) (hcs' c)) h
  | .lt (.val _) _, _, _, h | .lt (.num _) _, _, _, h | .lt (.mono _) (.mono _), _, _, h | .nz _, _, _, h
  | .sub _ _, _, _, h | .subP _ _, _, _, h => by simp [splitRes] at h

/-- **The `split` family holds** along a returning path of a function whose events hold. -/
theorem splitFam_sound {fn : Fn} (hf : coreProgram.find? fn.name = some fn) {rd : Reader} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) {x : CRes}
    (h : splitFam fn x = true) : x.Holds σ := by
  obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hpx
  obtain ⟨hn, hx⟩ := hpx
  obtain ⟨a, b, hs⟩ := splitsC_ok p hp fn (hn ▸ hf) rd σ es vs hw hh
  exact splitRes_sound hs x [] (by simp) hx

end

end LeanVM.Guest.EndExec
