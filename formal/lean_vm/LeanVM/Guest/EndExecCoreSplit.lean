/-
  LeanVM.Guest.EndExecCoreSplit

  The `split` family (`CoreMode.splitRes`) sound: a function's `g`-power split from its hinted bits on every
  returning path (`SplitW`, each function's own: `CoreMode/Fn/<f>/Sound.lean`), and the residuals a split gives.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.HeapCSound

/-!
# Split `g`-powers

A function hints the bits of its `n = g^c` and asserts `n = q^S·r`, `q` and `r` the products of the high and the low
bits' factors; booleanity pins each bit, so `q = g^a`, `r = g^b`, `a < A`, `b < S` and `c = S·a + b` (`SplitW`, each
function's own: `rs_eq_run`'s, `shared_selector_tables`'). The monomials the heap certificate names `q` and `r` by are
the products of the factors' values (`SplitC.q`, `SplitC.r`).

`splitRes_sound`: at such a valuation, a split's residuals hold: exponent bounds from `a < A`, `b < S`; under the arm
`j` of the selector `r`, `b = j`, so `q^S·g^c` is below `n = g^(S·a + b)` for `c < j`; the loop's strided runs
`[base]·g^i·g^(S·[0, a))`, `i < S`, are cells `i + S·j' < S·a ≤ S·a + b` of `[base]·[0, e(n))`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CRes CCond CCell CRun CIdx LtF rep_of capE idxC vw prodW SplitC powB splitRes)
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
@[expose] def SplitW (fn : Fn) (sp : SplitC) : Prop :=
  ∀ (rd : Reader) (σ : Val) (es : List Ev) (vs : List V), walk σ fn.body = .ret es vs →
    (∀ ev ∈ es, ev.Holds rd σ) → ∃ a b, SplitV sp σ a b

/-- The product of Boolean bits' factors is a power of `g` below `2^n`. -/
theorem split_bits_gpow {n : ℕ} {b : ℕ → E} (hb : ∀ j < n, b j * b j = b j) :
    ∃ e < 2 ^ n, ∏ j ∈ Finset.range n, (1 + b j * (gen ^ 2 ^ j + 1)) = gen ^ e :=
  ⟨_, Value.bitsVal_lt _ _, Value.prod_gen_pow_of_bool hb⟩

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

end

end LeanVM.Guest.EndExec
