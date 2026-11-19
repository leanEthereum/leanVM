/-
  LeanVM.Guest.EndExecCoreRes

  The core route's residual families (`CoreMode.resFam`) sound at the honest instances: each makes
  its residual true at the instance's valuation, from its path's events holding on the reference or
  from what its callers hand it.
-/

module

public import LeanVM.Guest.EndExecRF
public import LeanVM.Guest.EndExecRCs
public import LeanVM.Guest.CoreMode.Fam.CsQ
public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.HeapCSound
public import LeanVM.Guest.CoreMode.Fam.ExpQv
public import LeanVM.Guest.EndExecCoreSplit

/-!
# The residual families, sound

`resLt_sound`: on a memory of at most `2^28` words, along a returning path whose events hold, the
path's families hold at the valuation: a range checked value's exponent below the check's bound
(`rcBound_sound`, its atoms on every returning path, `topAtoms_on_path`), a top-level selector's below
its arms (`topSels_sound`).

`cs_holds` (`cs`): at an honest instance of `column_selector__L{κ}`, its callers hand it an offset
`g^o`, `2^κ ∣ o`, and the nibble shares (`csQ_all`), so its lowest digit is `g^(2^(4-w)·q)`, `q < 2^w`
(`cs_digit`), the read `[sel_eq]·[digit₀]·g^off` the `q`-th cell of the strided table.

`exp_lt` (`exp`): a parameter `g^e`, `e < 2^62` (`ExpW`), the quotient of two addresses the path
dereferences, has `e < 2^28`.

`splitFam_inst` (`split`, `EndExecCoreSplit`): a split `g`-power's residuals from its bits on the instance's path.

`resFam_inst`: at an honest instance (a `node` of the honest tree), in a frame holding its parameters
whose entry runs' exponent cells are powers, every residual of a family holds at its valuation; `resOk_inst`: every residual of a heap certificate whose residuals are of families
(`CoreMode.resOk`), which `HonF.res` asks of the core route's honest valuations.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam resOk idxC baseC vw csSub)

public section

/-- An exponent bound `e(x) < n` from `σ x = g^e`, `e < n < 2^62`. -/
theorem ltF_of_pow {σ : Val} {x n e : ℕ} (hn : n < capE) (he : e < n) (hσ : σ (V.n x) = ofK (addressOfIndex e)) :
    LtF (vw σ) (idxC (.val x)) (idxC (.num n)) := by
  refine ⟨e, n, ?_, CoreMode.rep_const hn, he⟩
  simp only [idxC, CoreMode.valW_baseC, vw, hσ]
  exact rep_of (by omega)

/-- A word read at offset `0` through `p` (on a memory of at most `2^28` words) is `p = g^i`, `i < 2^μ`. -/
theorem expLd_addr {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {σ : Val} {as : List Atom}
    (hh : ∀ a ∈ as, a.Holds Lm.read σ) {p : V} (h : CoreMode.expDiff.expLd as p = true) :
    ∃ i < 2 ^ μ, σ p = ofK (addressOfIndex i) := by
  simp only [CoreMode.expDiff.expLd, List.any_eq_true] at h
  obtain ⟨a, ha, hl⟩ := h
  cases a with
  | load d p' off =>
    cases off with
    | zero =>
      simp only [decide_eq_true_eq] at hl
      subst hl
      obtain ⟨hk, hr⟩ := hh _ ha
      exact Exec.deref0_addr (by omega) hk hr
    | succ => simp at hl
  | _ => simp at hl

/-- **A quotient of two dereferenced addresses** (`exp`): `x = g^e`, `e < 2^62`, and `q = b·x` with
`b`, `q` addresses of a memory of at most `2^28` words make `e` their difference, below `2^28`. -/
theorem exp_lt {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {σ : Val} {as : List Atom}
    (hh : ∀ a ∈ as, a.Holds Lm.read σ) {x e : ℕ} (he : e < 2 ^ 62) (hσx : σ (V.n x) = ofK (Parameters.g ^ e))
    (hd : CoreMode.expDiff as (V.n x) = true) : e < 2 ^ 28 := by
  simp only [CoreMode.expDiff, List.any_eq_true] at hd
  obtain ⟨a, ha, hm⟩ := hd
  cases a with
  | mul q a1 b1 =>
    have hq : σ q = σ a1 * σ b1 := hh _ ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hm
    -- the other factor `o` and the product, addresses
    obtain ⟨o, ho, hqo⟩ : ∃ o, CoreMode.expDiff.expLd as o = true ∧ σ q = σ o * σ (V.n x) := by
      rcases hm with ⟨⟨rfl, h1⟩, -⟩ | ⟨⟨rfl, h1⟩, -⟩
      · exact ⟨a1, h1, hq⟩
      · exact ⟨b1, h1, by rw [hq, mul_comm]⟩
    have hql : CoreMode.expDiff.expLd as q = true := by rcases hm with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h
    obtain ⟨i, hi, hσo⟩ := expLd_addr hμ Lm hh ho
    obtain ⟨k, hk, hσq⟩ := expLd_addr hμ Lm hh hql
    have h28 : (2 : ℕ) ^ μ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hμ
    rw [hσq, hσo, hσx, show (Parameters.g : K) ^ e = addressOfIndex e from rfl, ← ofK_mul] at hqo
    have hke : k = i + e := CoreMode.gpow_inj_lt (by omega) (by omega)
      (by rw [hqo, addressOfIndex, addressOfIndex, addressOfIndex, pow_add])
    omega
  | _ => simp at hm

/-- A `DEREF` through `p` at offset `0` (`load` or `touch`) on a memory of at most `2^28` words: `p = g^i`,
`i < 2^μ`. -/
theorem derefAt_addr {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {σ : Val} {as : List Atom}
    (hh : ∀ a ∈ as, a.Holds Lm.read σ) {p : V} (h : CoreMode.derefAt as p = true) :
    ∃ i < 2 ^ μ, σ p = ofK (addressOfIndex i) := by
  simp only [CoreMode.derefAt, List.any_eq_true] at h
  obtain ⟨a, ha, hl⟩ := h
  cases a with
  | load d p' off =>
    cases off with
    | zero =>
      simp only [decide_eq_true_eq] at hl
      subst hl
      obtain ⟨hk, hr⟩ := hh _ ha
      exact Exec.deref0_addr (by omega) hk hr
    | succ => simp at hl
  | touch t p' =>
    simp only [decide_eq_true_eq] at hl
    subst hl
    obtain ⟨hk, hr⟩ := hh _ ha
    exact Exec.deref0_addr (by omega) hk hr
  | _ => simp at hl

theorem mulOf_mem {as : List Atom} {x a b : V} (h : CoreMode.mulOf as x = some (a, b)) : Atom.mul x a b ∈ as := by
  unfold CoreMode.mulOf at h
  obtain ⟨t, ht, hf⟩ := List.exists_of_findSome?_eq_some h
  cases t with
  | mul d a' b' =>
    simp only at hf
    split_ifs at hf with hd
    cases hf
    rw [← hd]; exact ht
  | _ => simp at hf

/-- **A bit's power** (`bitPow`): `x = g^e`, `e ≤ m`. -/
theorem bitPow_sound {rd : Reader} {σ : Val} {as : List Atom} (hh : ∀ a ∈ as, a.Holds rd σ) {x : V} {m : ℕ}
    (h : CoreMode.bitPow as x = some m) : ∃ e ≤ m, σ x = ofK (addressOfIndex e) := by
  unfold CoreMode.bitPow at h
  obtain ⟨t, ht, hf⟩ := List.exists_of_findSome?_eq_some h
  cases t with
  | add d o y =>
    simp only at hf
    split_ifs at hf with hd
    obtain ⟨rfl, ho⟩ := hd
    have hx : σ d = σ o + σ y := hh _ ht
    have ho1 : σ o = 1 := hh _ (constOf_sound ho)
    cases hm : CoreMode.mulOf as y with
    | none => rw [hm] at hf; simp at hf
    | some p =>
      obtain ⟨b, w⟩ := p
      rw [hm] at hf
      simp only at hf
      split_ifs at hf with hb
      cases hc : Res.constOf as w with
      | none => rw [hc] at hf; simp at hf
      | some c =>
        rw [hc] at hf
        simp only [Option.bind_some] at hf
        have hy : σ y = σ b * σ w := hh _ (mulOf_mem hm)
        have hbb : σ b = σ b * σ b := hh _ hb
        have hw : σ w = c := hh _ (constOf_sound hc)
        have hcm := powOf_sound hf
        rcases IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (σ b) from hbb.symm) with h0 | h1
        · refine ⟨0, Nat.zero_le _, ?_⟩
          rw [hx, ho1, hy, h0, zero_mul, add_zero, addressOfIndex, pow_zero, Exec.ofK_one]
        · refine ⟨m, le_rfl, ?_⟩
          rw [hx, ho1, hy, h1, one_mul, hw, add_comm, hcm]
  | _ => simp at hf

/-- **An exponent's bound** (`expM`): `x = g^e`, `e ≤ M`, from atoms that hold on a memory of at most `2^28`
words. -/
theorem expM_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {σ : Val} {as : List Atom}
    (hh : ∀ a ∈ as, a.Holds Lm.read σ) : ∀ (f : ℕ) (x : V) {M : ℕ}, CoreMode.expM as f x = some M →
      ∃ e ≤ M, σ x = ofK (addressOfIndex e)
  | 0, x, M, h => by simp [CoreMode.expM] at h
  | f + 1, x, M, h => by
    unfold CoreMode.expM at h
    split_ifs at h with hd
    · cases h
      obtain ⟨i, hi, hσ⟩ := derefAt_addr hμ Lm hh hd
      have : (2 : ℕ) ^ μ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hμ
      exact ⟨i, by omega, hσ⟩
    · cases hm : CoreMode.mulOf as x with
      | some p =>
        obtain ⟨a, b⟩ := p
        rw [hm] at h
        simp only at h
        cases ha : CoreMode.expM as f a with
        | none => rw [ha] at h; simp at h
        | some ma =>
          cases hb : CoreMode.expM as f b with
          | none => rw [ha, hb] at h; simp at h
          | some mb =>
            rw [ha, hb] at h
            simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨ea, hea, hσa⟩ := expM_sound hμ Lm hh f a ha
            obtain ⟨eb, heb, hσb⟩ := expM_sound hμ Lm hh f b hb
            have hx : σ x = σ a * σ b := hh _ (mulOf_mem hm)
            refine ⟨ea + eb, by omega, ?_⟩
            rw [hx, hσa, hσb, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
      | none =>
        rw [hm] at h
        simp only at h
        cases hp : CoreMode.bitPow as x with
        | some m =>
          rw [hp] at h
          cases h
          exact bitPow_sound hh hp
        | none =>
          rw [hp] at h
          simp only at h
          cases hc : Res.constOf as x with
          | none => rw [hc] at h; simp at h
          | some c =>
            rw [hc] at h
            simp only [Option.bind_some] at h
            refine ⟨M, le_rfl, ?_⟩
            rw [hh _ (constOf_sound hc), powOf_sound h]

/-- **The exponent bound families hold** (`rc`, `sel`, `exp`) at a valuation along a returning path of
the function whose events hold on a memory of at most `2^28` words, its frame's parameter cells holding
its parameters and its entry runs' exponent cells powers of `g` (`ExpW`). -/
theorem resLt_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {xc : List ℕ} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) {fp : ℕ}
    (hx : CoreMode.ExpW Lm xc fp)
    (hpar : ∀ k < fn.params.length, CoreMode.Rd Lm fp (2 + k) = some (σ (V.n k))) {x n : ℕ}
    (h : resFam fn xc (.lt (.val x) (.num n)) = true) : (CRes.lt (.val x) (.num n)).Holds σ := by
  simp only [resFam, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨hn, ((h | ⟨p, hp, hpx⟩) | ⟨⟨⟨hn28, hxp⟩, hxc⟩, hd⟩) | hM⟩ := h
  · split at h
    · rename_i N hN
      simp only [decide_eq_true_eq] at h
      have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds Lm.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
      obtain ⟨e, he, hσ⟩ := rcBound_sound (by omega) Lm hall hN
      exact ltF_of_pow (e := e) hn (by omega) (by rw [hσ, Value.gen_pow_eq_ofK])
    · cases h
  · obtain ⟨h1, h2⟩ := hpx
    obtain ⟨e, he, hσ⟩ := topSels_sound hw (x := p.1) (n := p.2) hp
    rw [h1] at hσ
    exact ltF_of_pow (e := e) hn (by omega) hσ
  · obtain ⟨e, he, hr⟩ := hx _ hxc
    have hσx : σ (V.n x) = ofK (Parameters.g ^ e) := Option.some.inj ((hpar x hxp).symm.trans hr)
    have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds Lm.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
    have := exp_lt hμ Lm hall he hσx hd
    exact ltF_of_pow (e := e) hn (by omega) hσx
  · obtain ⟨M, hM, hMn⟩ : ∃ M, CoreMode.expM (Res.topAtoms fn.body) CoreMode.expFuel (V.n x) = some M ∧ M < n := by
      cases hm : CoreMode.expM (Res.topAtoms fn.body) CoreMode.expFuel (V.n x) with
      | none => simp [hm] at hM
      | some M => simp only [hm, Option.any_some, decide_eq_true_eq] at hM; exact ⟨M, rfl, hM⟩
    have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds Lm.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
    obtain ⟨e, he, hσ⟩ := expM_sound hμ Lm hall _ _ hM
    exact ltF_of_pow (e := e) hn (by omega) hσ

/-- **The `rcv` family holds** (`e(x) < e(p·g)`, `x` range checked against `p`) at a valuation along a returning
path of the function whose events hold on a memory of at most `2^28` words. -/
theorem resLtM_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {xc : List ℕ} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) {x : ℕ} {c : CoreMode.CCell}
    (h : resFam fn xc (.lt (.val x) (.mono c)) = true) : (CRes.lt (.val x) (.mono c)).Holds σ := by
  simp only [resFam] at h
  split at h
  · rename_i p hb ho
    obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp h
    have hal : a.Holds Lm.read σ := hh _ (topAtoms_on_path hw ha)
    cases a with
    | rangeCheck x' y t1 t2 k =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨⟨hxK, hxr⟩, hk, ⟨hyK, hyr⟩⟩ := hal
      obtain ⟨i, hi, hσx⟩ := Exec.deref0_addr (by omega) hxK hxr
      obtain ⟨j, hj, hσy⟩ := Exec.deref0_addr (by omega) hyK hyr
      have h28 : (2 : ℕ) ^ μ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hμ
      have hcap : (2 : ℕ) ^ 28 + 2 ^ 28 + 1 < capE := by unfold capE; norm_num
      refine ⟨i, i + j + 1, ?_, ?_, by omega⟩
      · simp only [idxC, CoreMode.valW_baseC, vw, hσx]
        exact rep_of (by omega)
      · obtain ⟨cb, co⟩ := c
        simp only at hb ho
        subst hb ho
        have : CoreMode.CCell.valW (vw σ) ⟨[(p, 1)], 1⟩ = ofK (addressOfIndex (i + j + 1)) := by
          have e1 : CoreMode.CCell.valW (vw σ) ⟨[(p, 1)], 1⟩ = σ (V.n p) * ofK (addressOfIndex 1) := by
            simp [CoreMode.CCell.valW, CoreMode.prodW, vw]
          rw [e1, hk, hσx, hσy, ← ofK_mul, ← ofK_mul]
          congr 1
          simp only [addressOfIndex, ← pow_add]
        simp only [idxC]
        rw [this]
        exact rep_of (by omega)
    | _ => simp at hm
  · cases h

/-- **The `rcn` family holds** (`e(x) < e(p)`, `x` range checked against `p·g⁻¹`) at a valuation along a returning
path of the function whose events hold on a memory of at most `2^28` words: `x = g^i`, the check's other factor
`g^j`, so `p = g^(i + j + 1)`. -/
theorem resLtV_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {xc : List ℕ} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) {x p : ℕ}
    (h : resFam fn xc (.lt (.val x) (.val p)) = true) : (CRes.lt (.val x) (.val p)).Holds σ := by
  have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds Lm.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  simp only [resFam, List.any_eq_true] at h
  obtain ⟨a, ha, hm⟩ := h
  cases a with
  | rangeCheck x' y t1 t2 k =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hm
    obtain ⟨rfl, b, hb, hbm⟩ := hm
    obtain ⟨⟨hxK, hxr⟩, hk, ⟨hyK, hyr⟩⟩ := hall _ ha
    obtain ⟨i, hi, hσx⟩ := Exec.deref0_addr (by omega) hxK hxr
    obtain ⟨j, hj, hσy⟩ := Exec.deref0_addr (by omega) hyK hyr
    have h28 : (2 : ℕ) ^ μ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hμ
    have hcap : (2 : ℕ) ^ 28 + 2 ^ 28 + 1 < capE := by unfold capE; norm_num
    cases b with
    | mul k' p' w =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hbm
      obtain ⟨⟨rfl, rfl⟩, hw'⟩ := hbm
      split at hw'
      · rename_i w' hc
        simp only [CoreMode.invG, decide_eq_true_eq] at hw'
        have hσw : σ w = w' := hall _ (EndExec.constOf_sound hc)
        have hmul : σ k' = σ (V.n p) * σ w := hall _ hb
        have hσp : σ (V.n p) = ofK (addressOfIndex (i + j + 1)) := by
          have e1 : σ (V.n p) = σ k' * ofK (addressOfIndex 1) := by
            rw [hmul, hσw, mul_assoc, hw', mul_one]
          rw [e1, hk, hσx, hσy, ← ofK_mul, ← ofK_mul]
          congr 1
          simp only [addressOfIndex, ← pow_add]
        refine ⟨i, i + j + 1, ?_, ?_, by omega⟩
        · simp only [idxC, CoreMode.valW_baseC, vw, hσx]
          exact rep_of (by omega)
        · simp only [idxC, CoreMode.valW_baseC, vw, hσp]
          exact rep_of (by omega)
      · cases hw'
    | _ => simp at hbm
  | _ => simp at hm

/-- **The `sel` and `rc` families of a value times a power of `g` hold** (`e(x·g^c) < n`, `x` a top-level selector
of `m` arms, `m + c ≤ n`, or range checked against `g^(N - 1)`, `N + c ≤ n`) at a valuation along a returning path
of the function whose events hold on a memory of at most `2^28` words. -/
theorem resSelM_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {xc : List ℕ} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ)
    {c : CoreMode.CCell} {n : ℕ} (h : resFam fn xc (.lt (.mono c) (.num n)) = true) :
    (CRes.lt (.mono c) (.num n)).Holds σ := by
  obtain ⟨cb, k⟩ := c
  simp only [resFam] at h
  split at h
  · rename_i _ x
    have e1 : CoreMode.CCell.valW (vw σ) ⟨[(x, 1)], k⟩ = σ (V.n x) * ofK (addressOfIndex k) := by
      simp [CoreMode.CCell.valW, CoreMode.prodW, vw]
    have fin : ∀ e, e + k < n → σ (V.n x) = ofK (addressOfIndex e) → n < capE →
        (CRes.lt (.mono ⟨[(x, 1)], k⟩) (.num n)).Holds σ := fun e hek hσ hn ↦ by
      refine ⟨e + k, n, ?_, CoreMode.rep_const hn, hek⟩
      simp only [idxC]
      rw [e1, hσ, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add]
      exact rep_of (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true] at h
    obtain ⟨hn, ⟨p, hp, hpx, hpk⟩ | h⟩ := h
    · obtain ⟨e, he, hσ⟩ := topSels_sound hw (x := p.1) (n := p.2) hp
      rw [hpx] at hσ
      exact fin e (by omega) hσ hn
    · split at h
      · rename_i N hN
        simp only [decide_eq_true_eq] at h
        have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds Lm.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
        obtain ⟨e, he, hσ⟩ := rcBound_sound (by omega) Lm hall hN
        exact fin e (by omega) (by rw [hσ, Value.gen_pow_eq_ofK]) hn
      · cases h
  · cases h

theorem find_name' {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  unfold Program.find? at h
  have := List.find?_some h
  simpa using this

/-- **`column_selector`'s lowest digit at an honest instance** (`cs`): the read lies in its strided
table. -/
theorem cs_holds {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {κ : ℕ} (hκ : κ < 31) (hname : fn.name = B1.Tables.lName "column_selector" κ) :
    (csSub κ).Holds σ := by
  have hκ28 : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hfn : f = B1.Tables.lName "column_selector" κ := by rw [← find_name' hf, hname]
  obtain ⟨fn', hfc, hps, hbody⟩ := B1.Tables.csFound hκ
  rw [← hfn] at hfc
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hfc)
  -- the caller's facts
  have hH := csQ_all hr I hI f σ bufs kids ht κ hκ hfn _ hf
  rw [hps] at hH
  obtain ⟨o, ho, hal, h0, hG⟩ := hH
  -- the body at the instance's valuation
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hf
  rw [hbody, holdsList_append, holdsList_noRet _ (B1.Tables.csPre_noRet κ)] at hb
  obtain ⟨u, hu, hd, hdv⟩ := cs_digit hκ (by omega) r.img hb.1 hG ho hal h0
  rw [csW_sub] at hdv
  -- the run
  set w := B1.Tables.csW κ 0 with hw'
  have hw4 := B1.Tables.csW_bounds κ 0
  obtain ⟨q, rfl⟩ := hdv
  have hq : q < 2 ^ w := by
    have h16 : 2 ^ (4 - w) * 2 ^ w = 16 := by rw [← pow_add, show 4 - w + w = 4 by omega]; rfl
    by_contra hc
    have := Nat.mul_le_mul_left (2 ^ (4 - w)) (not_lt.mp hc)
    omega
  have hcap : 2 ^ w < capE := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hw4.2) (by decide)
  have hcap0 : 0 < capE := by unfold capE; omega
  rw [csSub]
  show CoreMode.RunSet (vw σ) _ _ _ _ _
  refine ⟨0, 2 ^ w, q, CoreMode.rep_const hcap0, CoreMode.rep_const hcap, Nat.zero_le _, hq, ?_⟩
  have key : ∀ off : ℕ, CoreMode.CCell.valW (vw σ) ⟨[(1, 1), (3, 1)], off⟩ =
      CoreMode.CCell.valW (vw σ) ⟨[(1, 1)], off⟩ * ofK (addressOfIndex (2 ^ (4 - w) * q)) := fun off ↦ by
    simp only [CoreMode.CCell.valW, CoreMode.prodW, vw, hd, Value.gen_pow_eq_ofK, pow_one, mul_one]
    ring
  unfold CoreMode.CCell.addrW
  rw [key]

/-- **A run of constant bounds inside one of the same bases** (`subRC`) at any valuation. -/
theorem subRC_holds {q r : CoreMode.CRun} (h : CoreMode.subRC q r = true) (σ : Val) : (CRes.subR q r).Holds σ := by
  obtain ⟨⟨qb, qo⟩, S, ql, qh⟩ := q
  obtain ⟨⟨rb, ro⟩, S', rl, rh⟩ := r
  unfold CoreMode.subRC at h
  split at h
  · rename_i l hh l' h' hql hqh hrl hrh
    simp only at hql hqh hrl hrh
    subst hql hqh hrl hrh
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hS⟩, hS0⟩, hro⟩, hdv⟩, hl⟩, hh'⟩, hlc⟩, hhc⟩, hlc'⟩, hhc'⟩ := h
    subst hS
    have hb' := CoreMode.basesBeq_eq hb
    subst hb'
    intro x hx
    obtain ⟨ylo, yhi, j, hylo, hyhi, hlj, hjh, rfl⟩ := hx
    simp only [idxC] at hylo hyhi
    rw [CoreMode.rep_const hlc, Option.some.injEq] at hylo
    rw [CoreMode.rep_const hhc, Option.some.injEq] at hyhi
    subst hylo hyhi
    obtain ⟨k, hk⟩ : ∃ k, qo - ro = S * k := ⟨(qo - ro) / S, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdv)).symm⟩
    have hkS : (qo - ro) / S = k := by rw [hk, Nat.mul_div_cancel_left _ hS0]
    rw [hkS] at hl hh'
    refine ⟨l', h', j + k, (by simp only [idxC]; exact CoreMode.rep_const hlc'),
      (by simp only [idxC]; exact CoreMode.rep_const hhc'), by omega, by omega, ?_⟩
    simp only [CoreMode.CCell.valW, mul_assoc, ← CoreMode.ofK_mul', addressOfIndex, ← pow_add]
    rw [show qo + S * j = ro + S * (j + k) by rw [Nat.mul_add]; omega]
  · cases h

/-- **The `sel` family below a selector's word times a power of `g`** (`g^j` below `x·g^c`, `j < c`, `x` a top-level
selector of `m` arms, `m + c < 2^62`). -/
theorem resSelN_sound {fn : Fn} {xc : List ℕ} {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) {c : CoreMode.CCell} {j : ℕ} (h : resFam fn xc (.lt (.num j) (.mono c)) = true) :
    (CRes.lt (.num j) (.mono c)).Holds σ := by
  obtain ⟨cb, k⟩ := c
  simp only [resFam] at h
  split at h
  · rename_i _ x
    have e1 : CoreMode.CCell.valW (vw σ) ⟨[(x, 1)], k⟩ = σ (V.n x) * ofK (addressOfIndex k) := by
      simp [CoreMode.CCell.valW, CoreMode.prodW, vw]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨hjk, p, hp, hpx, hpk⟩ := h
    obtain ⟨e, he, hσ⟩ := topSels_sound hw (x := p.1) (n := p.2) hp
    rw [hpx] at hσ
    refine ⟨j, e + k, CoreMode.rep_const (by omega), ?_, by omega⟩
    simp only [idxC]
    rw [e1, hσ, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add]
    exact rep_of (by omega)
  · cases h

/-- The top-level atoms of a block falling through are among its events. -/
theorem topAtoms_on_fall {σ : Val} : ∀ {ss : List Stmt} {es : List Ev},
    walk σ ss = .fall es → ∀ {a : Atom}, a ∈ Res.topAtoms ss → Ev.atom a ∈ es
  | [], _, _, _, h => by simp [Res.topAtoms] at h
  | s :: ss, es, hw, a, ha => by
    rw [walk] at hw
    obtain ⟨es1, es2, h1, h2, rfl⟩ : ∃ es1 es2, walk1 σ s = .fall es1 ∧ walk σ ss = .fall es2 ∧ es = es1 ++ es2 := by
      cases h1 : walk1 σ s with
      | fall es1 =>
        rw [h1] at hw
        cases h2 : walk σ ss with
        | fall es2 => rw [h2] at hw; exact ⟨es1, es2, rfl, rfl, (Out.fall.inj hw).symm⟩
        | ret _ _ => rw [h2] at hw; cases hw
        | stuck => rw [h2] at hw; cases hw
      | ret _ _ => rw [h1] at hw; cases hw
      | stuck => rw [h1] at hw; cases hw
    cases s with
    | atom b =>
      simp only [Res.topAtoms, List.mem_cons] at ha
      simp only [walk1, Out.fall.injEq] at h1
      subst h1
      rcases ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_append_right _ (topAtoms_on_fall h2 ha)
    | _ =>
      simp only [Res.topAtoms] at ha
      split_ifs at ha
      · exact List.mem_append_right _ (topAtoms_on_fall h2 ha)
      · simp at ha

/-- **The atoms of the arm a nonzero condition takes** (`CoreMode.nzAtoms`) are on a returning path. -/
theorem nzAtoms_on_path {σ : Val} {c : V} (hc : σ c ≠ 0) : ∀ {ss : List Stmt} {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → ∀ {a : Atom}, a ∈ CoreMode.nzAtoms c ss → Ev.atom a ∈ es
  | [], _, _, _, _, h => by simp [CoreMode.nzAtoms] at h
  | s :: ss, es, vs, hw, a, ha => by
    simp only [CoreMode.nzAtoms, List.mem_append] at ha
    rcases ha with ha | ha
    · cases s with
      | ite c' z n =>
        simp only at ha
        split_ifs at ha with hcn
        · obtain ⟨rfl, hn⟩ := hcn
          obtain ⟨es1, es2, h1, -, rfl⟩ := Res.walk_cons_noRet (by rw [← Memory.noRetR_eq]; exact hn) hw
          simp only [walk1, hc, ↓reduceIte] at h1
          cases hn' : walk σ n with
          | fall esn =>
            rw [hn'] at h1
            simp only [Out.pre, Out.fall.injEq] at h1
            subst h1
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (topAtoms_on_fall hn' ha))
          | ret _ _ => rw [hn'] at h1; cases h1
          | stuck => rw [hn'] at h1; cases h1
        · simp at ha
      | _ => simp at ha
    · split_ifs at ha with hn
      · obtain ⟨es1, es2, -, h2, rfl⟩ := Res.walk_cons_noRet (by rw [← Memory.noRetR_eq]; exact hn) hw
        exact List.mem_append_right _ (nzAtoms_on_path hc h2 ha)
      · simp at ha

/-- **The `neg` family holds** (`e(x·v·g^off) < n`, `CoreMode.negPair`) where its condition `k` is nonzero, along a
returning path whose events hold on a memory of at most `2^28` words: `x = g^e` and `y = x·g^off = g^(e + off)`
range checked, `e ≠ 0` (else `k = y + g^off = 0`), `v·g = 1`, so `x·v·g^off = g^(e + off - 1)`. -/
theorem negPair_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) {k x v off n : ℕ}
    (hk : σ (V.n k) ≠ 0) (h : CoreMode.negPair fn k x v off n = true) :
    ∃ y, σ (V.n x) * σ (V.n v) * ofK (addressOfIndex off) = ofK (addressOfIndex y) ∧ y < n := by
  have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds Lm.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  simp only [CoreMode.negPair, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨hoff, N1, hN1⟩, ⟨av, hav, hv⟩⟩, ⟨aa, haa, hadd⟩⟩ := h
  -- `x = g^e`
  obtain ⟨e, he, hσx⟩ := rcBound_sound (by omega) Lm hall hN1
  have hN1b : N1 ≤ 2 ^ 33 := by
    unfold Res.rcBound at hN1
    obtain ⟨a, -, hf⟩ := List.exists_of_findSome?_eq_some hN1
    cases a with
    | rangeCheck _ _ _ _ _ =>
      simp only at hf
      split_ifs at hf
      split at hf
      · split_ifs at hf with hb
        cases hf
        omega
      · cases hf
    | _ => cases hf
  -- `v = g⁻¹`
  cases av with
  | const d w =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨rfl, hinv⟩ := hv
    have hσv : σ (V.n v) = w := hh _ (nzAtoms_on_path hk hw hav)
    simp only [CoreMode.invG, decide_eq_true_eq] at hinv
    -- `k = y + w0`, `y = x·w0`
    cases aa with
    | add d y o =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hadd
      obtain ⟨rfl, am, ham, hmul⟩ := hadd
      cases am with
      | mul y' x' b =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmul
        obtain ⟨⟨⟨rfl, rfl⟩, hc⟩, hy⟩ := hmul
        split at hc
        · rename_i w0 w0' ho hb
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨rfl, hw0⟩ := hc
          split at hy
          · rename_i N2 hN2
            simp only [decide_eq_true_eq] at hy
            have hσo : σ o = w0 := hall _ (EndExec.constOf_sound ho)
            have hσb : σ b = w0 := hall _ (EndExec.constOf_sound hb)
            have hσk : σ (V.n k) = σ y' + σ o := hall _ haa
            have hσy : σ y' = σ (V.n x) * σ b := hall _ ham
            obtain ⟨e2, he2, hσy2⟩ := rcBound_sound (by omega) Lm hall hN2
            have hN2b : N2 ≤ 2 ^ 33 := by
              unfold Res.rcBound at hN2
              obtain ⟨a, -, hf⟩ := List.exists_of_findSome?_eq_some hN2
              cases a with
              | rangeCheck _ _ _ _ _ =>
                simp only at hf
                split_ifs at hf
                split at hf
                · split_ifs at hf with hb
                  cases hf
                  omega
                · cases hf
              | _ => cases hf
            rw [Value.gen_pow_eq_ofK] at hσx hσy2
            -- `e ≠ 0`
            have he0 : e ≠ 0 := by
              rintro rfl
              apply hk
              rw [hσk, hσy, hσx, hσb, hσo, show addressOfIndex 0 = 1 from pow_zero _,
                show ofK (1 : K) = 1 from map_one (algebraMap K E), one_mul, CharTwo.add_self_eq_zero]
            -- `y = g^(e + off)`
            have hyy : e + off = e2 := by
              have h1 : ofK (addressOfIndex (e + off)) = ofK (addressOfIndex e2) := by
                rw [← hσy2, hσy, hσx, hσb, hw0, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add]
              exact LeanVM.Prover.Exec.gpow_inj (by omega) (by omega) (ofK_injective h1)
            refine ⟨e2 - 1, ?_, by omega⟩
            have h1 : ofK (addressOfIndex e) * ofK (addressOfIndex off) =
                ofK (addressOfIndex (e2 - 1)) * ofK (addressOfIndex 1) := by
              rw [← ofK_mul, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add,
                ← pow_add, show e + off = e2 - 1 + 1 by omega]
            rw [hσx, hσv]
            calc ofK (addressOfIndex e) * w * ofK (addressOfIndex off)
                = (ofK (addressOfIndex e) * ofK (addressOfIndex off)) * w := by ring
              _ = ofK (addressOfIndex (e2 - 1)) * (w * ofK (addressOfIndex 1)) := by rw [h1]; ring
              _ = _ := by rw [hinv, mul_one]
          · cases hy
        · cases hc
      | _ => simp at hmul
    | _ => simp at hadd
  | _ => simp at hv

/-- **The `neg` family holds** where its branch condition does (`CoreMode.negFam`). -/
theorem negFam_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) {cs : List CoreMode.CCond}
    (hcs : ∀ c ∈ cs, c.Holds σ) : ∀ {r : CRes}, CoreMode.negFam fn cs r = true → r.Holds σ
  | .lt (.mono c) (.num n), h => by
    simp only [CoreMode.negFam, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨hn, cd, hcd, hc⟩ := h
    cases cd with
    | nonzero k =>
      have hk : σ (V.n k) ≠ 0 := hcs _ hcd
      obtain ⟨cb, off⟩ := c
      simp only at hc
      split at hc
      · rename_i a b
        have hv : ∀ x v, CoreMode.negPair fn k x v off n = true →
            σ (V.n a) * σ (V.n b) * ofK (addressOfIndex off) = σ (V.n x) * σ (V.n v) * ofK (addressOfIndex off) →
            (CRes.lt (.mono ⟨[(a, 1), (b, 1)], off⟩) (.num n)).Holds σ := fun x v hp he ↦ by
          obtain ⟨y, hy, hyn⟩ := negPair_sound hμ Lm hw hh hk hp
          refine ⟨y, n, ?_, CoreMode.rep_const hn, hyn⟩
          have e1 : CoreMode.CCell.valW (vw σ) ⟨[(a, 1), (b, 1)], off⟩ =
              σ (V.n a) * σ (V.n b) * ofK (addressOfIndex off) := by
            simp [CoreMode.CCell.valW, CoreMode.prodW, vw, mul_assoc]
          simp only [idxC]
          rw [e1, he, hy]
          exact rep_of (by omega)
        rcases Bool.or_eq_true_iff.mp hc with hp | hp
        · exact hv a b hp rfl
        · exact hv b a hp (by ring)
      · cases hc
    | _ => simp at hc
  | .lt (.val _) _, h | .lt (.num _) _, h | .lt (.mono _) (.val _), h | .lt (.mono _) (.mono _), h
  | .nz _, h | .sub _ _, h | .subR _ _, h | .subP _ _, h | .under _ _, h => by simp [CoreMode.negFam] at h

/-- **A residual of a family holds** at an honest instance's valuation, in a frame `fp` holding its
parameters whose entry runs' exponent cells are powers of `g` (`ExpW`). -/
theorem resFam_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {xc : List ℕ} {fp : ℕ} (hx : CoreMode.ExpW r.img xc fp)
    (hpar : ∀ k < fn.params.length, CoreMode.Rd r.img fp (2 + k) = some (σ (V.n k))) :
    ∀ x : CRes, resFam fn xc x = true → x.Holds σ
  | .lt (.val x) (.num n), h => by
    obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    exact resLt_sound (logMemorySize_le_28 (e := r.exec) hr.size) r.img hw hh hx hpar h
  | .sub c q, h => by
    simp only [resFam, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨κ, hκ, hname, heq⟩ := h
    rw [heq]
    exact cs_holds hr hI ht hf hκ hname
  | .lt (.val x) (.mono c), h => by
    obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    exact resLtM_sound (logMemorySize_le_28 (e := r.exec) hr.size) r.img hw hh h
  | .lt (.mono c) (.num n), h => by
    obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    exact resSelM_sound (logMemorySize_le_28 (e := r.exec) hr.size) r.img hw hh h
  | .lt (.num j) (.mono c), h => by
    obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    exact resSelN_sound hw h
  | .under cs r', h => fun hcs ↦ by
    simp only [resFam, Bool.or_eq_true] at h
    rcases h with h | h
    · exact resFam_inst hr hI ht hf hx hpar r' h
    · obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
      obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
      exact negFam_sound (logMemorySize_le_28 (e := r.exec) hr.size) r.img hw hh hcs h
  | .subR q r', h => by
    simp only [resFam] at h
    exact subRC_holds h σ
  | .lt (.val x) (.val p), h => by
    obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    exact resLtV_sound (logMemorySize_le_28 (e := r.exec) hr.size) r.img hw hh h
  | .lt (.num _) (.num _), h | .lt (.num _) (.val _), h | .lt (.mono _) (.val _), h
  | .lt (.mono _) (.mono _), h | .nz _, h | .subP _ _, h => by simp [resFam] at h

/-! ## The instance's exponent and dimension facts (`expQ`, `dim`) -/

theorem loadAt_mem {as : List Atom} {x p : V} {k : ℕ} (h : CoreMode.loadAt as x p k = true) :
    Atom.load x p k ∈ as := by
  unfold CoreMode.loadAt CoreMode.ldOf at h
  rw [decide_eq_true_eq] at h
  obtain ⟨a, ha, h⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | load d p' k' =>
    by_cases hd : d = x
    · subst hd
      simp only [decide_true, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ha
    · simp [hd] at h
  | _ => simp at h

theorem loadHolds_det {rd : Reader} {p : E} {k : ℕ} {a b : E} (ha : LoadHolds rd p k a) (hb : LoadHolds rd p k b) :
    a = b :=
  Option.some.inj (ha.2.symm.trans hb.2)

section
open LeanVM.Protocol.Verifier (gen)
variable {r : Ref} {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fn : Fn}

/-- **A value of an exponent fact** (`expQ1`) is `g^e` below its bound, at an instance with the facts. -/
theorem expQ1_sound (hE : ExpQ r I) (ht : I.t = .node f σ bufs kids) (hf : coreProgram.find? f = some fn)
    (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) {x : V} {b : ℕ} (h : CoreMode.expQ1 fn x = some b) :
    ∃ e < b, σ x = gen ^ e := by
  unfold CoreMode.expQ1 at h
  obtain ⟨c, hc, hcf⟩ := List.exists_of_findSome?_eq_some h
  by_cases hn : (c.1 == fn.name) = true
  · simp only [hn, ↓reduceIte] at hcf
    have hn' : c.1 = f := by rw [beq_iff_eq] at hn; rw [hn]; exact find_name' hf
    rcases hp : fn.params[c.2.1]? with _ | p
    · rw [hp] at hcf; simp at hcf
    · have hH := hE f σ bufs kids ht fn hf c hc hn' p hp
      rcases ho : c.2.2.1 with _ | k
      · rw [hp, ho] at hcf
        simp only at hcf
        split_ifs at hcf with hpx
        obtain rfl := Option.some.inj hcf
        rw [ho] at hH
        subst hpx
        exact hH
      · rw [hp, ho] at hcf
        simp only at hcf
        split_ifs at hcf with hl
        obtain rfl := Option.some.inj hcf
        rw [ho] at hH
        obtain ⟨e, he, hld⟩ := hH
        have hx : (Atom.load x p k).Holds r.img.read σ := hall _ (loadAt_mem hl)
        exact ⟨e, he, loadHolds_det hx hld⟩
  · simp [hn] at hcf

/-- **`check_opening_terminal`'s word `gmv`** (`termGm`) is `g^sl`, `sl ≤ 30`. -/
theorem termGm_sound (hT : TermQ r I) (ht : I.t = .node f σ bufs kids) (hf : coreProgram.find? f = some fn)
    {x : V} (h : CoreMode.termGm fn x = true) : ∃ e < 31, σ x = gen ^ e := by
  simp only [CoreMode.termGm, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hn, hx⟩ := h
  have hf' : f = name% «check_opening_terminal» := by rw [← find_name' hf, hn]
  subst hf'
  have hF := hT _ σ bufs kids ht rfl fn hf
  rw [term_fn hf] at hF hx
  simp only [B1.VerifySub.termParams, List.map_cons, List.map_nil, Res.TermFront] at hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, sl, hsl, hgm⟩ := hF
  simp only [B1.VerifySub.termParams, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx
  subst hx
  exact ⟨sl, by omega, hgm⟩

/-- **A value of an exponent fact or a product of one and a constant power** (`expQB`) is `g^e` below its
bound. -/
theorem expQB_sound (hT : TermQ r I) (hE : ExpQ r I) (ht : I.t = .node f σ bufs kids)
    (hf : coreProgram.find? f = some fn)
    (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) {x : V} {b : ℕ} (h : CoreMode.expQB fn x = some b) :
    ∃ e < b, σ x = gen ^ e := by
  unfold CoreMode.expQB at h
  rcases h1 : CoreMode.expQ1 fn x with _ | b'
  · rw [h1] at h
    simp only at h
    cases hg : CoreMode.termGm fn x
    swap
    · rw [hg, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact termGm_sound hT ht hf hg
    rw [hg, Bool.cond_false] at h
    obtain ⟨a, ha, haf⟩ := List.exists_of_findSome?_eq_some h
    cases a with
    | mul d a w =>
      simp only at haf
      split_ifs at haf with hd
      subst hd
      rcases hb1 : CoreMode.expQ1 fn a with _ | b1
      · rw [hb1] at haf; simp at haf
      · rcases hc : (Res.constOf (Res.topAtoms fn.body) w).bind Res.powOf with _ | c
        · rw [hb1, hc] at haf; simp at haf
        · rw [hb1, hc] at haf
          simp only [Option.some.injEq] at haf
          subst haf
          obtain ⟨e, he, hσa⟩ := expQ1_sound hE ht hf hall hb1
          obtain ⟨w0, hw0, hpw⟩ := Option.bind_eq_some_iff.mp hc
          have hσw : σ w = w0 := hall _ (constOf_sound hw0)
          have hmul : σ d = σ a * σ w := hall _ ha
          refine ⟨e + c, by omega, ?_⟩
          rw [hmul, hσa, hσw, powOf_sound hpw, ← Value.gen_pow_eq_ofK, pow_add]
    | _ => simp at haf
  · rw [h1] at h
    obtain rfl := Option.some.inj h
    exact expQ1_sound hE ht hf hall h1

theorem rep_val_gen {x e : ℕ} (hσ : σ (V.n x) = gen ^ e) (h : e < capE) :
    CoreMode.rep ((idxC (.val x)).valW (vw σ)) = some e := by
  simp only [idxC, CoreMode.valW_baseC, vw, hσ, Value.gen_pow_eq_ofK]
  exact rep_of h

theorem rep_mono_gen {x c e : ℕ} (hσ : σ (V.n x) = gen ^ e) (h : e + c < capE) :
    CoreMode.rep ((idxC (.mono ⟨[(x, 1)], c⟩)).valW (vw σ)) = some (e + c) := by
  have e1 : CoreMode.CCell.valW (vw σ) ⟨[(x, 1)], c⟩ = σ (V.n x) * ofK (addressOfIndex c) := by
    simp [CoreMode.CCell.valW, CoreMode.prodW, vw]
  simp only [idxC]
  rw [e1, hσ, Value.gen_pow_eq_ofK, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add]
  exact rep_of h

/-- **A dimension fact's word** (`dimLt`): `x = g^e` and `p = g^m`, `e + t < m + u`, both below `2^34`. -/
theorem dimLt_sound (hD : DimQ r I) (ht : I.t = .node f σ bufs kids) (hf : coreProgram.find? f = some fn)
    (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) {x p t u : ℕ}
    (h : CoreMode.dimLt fn (V.n x) t (V.n p) u = true) :
    ∃ e m, σ (V.n x) = gen ^ e ∧ σ (V.n p) = gen ^ m ∧ e + t < m + u ∧ m + u < 2 ^ 34 := by
  simp only [CoreMode.dimLt, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨hu, c, hc, hcn, hm⟩ := h
  have hn' : c.1 = f := by rw [beq_iff_eq] at hcn; rw [hcn]; exact find_name' hf
  split at hm
  · rename_i kb gb hkb hgb
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hm
    obtain ⟨rfl, q, hq, hl, htq⟩ := hm
    obtain ⟨m, hm33, hgm, hps⟩ := hD f σ bufs kids ht fn hf c hc hn' kb (V.n p) hkb hgb
    obtain ⟨e, hld, hem⟩ := hps q hq
    have hx : (Atom.load (V.n x) kb q.1).Holds r.img.read σ := hall _ (loadAt_mem hl)
    exact ⟨e, m, loadHolds_det hx hld, hgm, by omega, by omega⟩
  · simp at hm

/-- **The `expQ` and `dim` families hold** at an instance with the exponent and dimension facts. -/
theorem resQ_sound (hT : TermQ r I) (hE : ExpQ r I) (hD : DimQ r I) (ht : I.t = .node f σ bufs kids)
    (hf : coreProgram.find? f = some fn) (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) :
    ∀ x : CRes, CoreMode.resQ fn x = true → x.Holds σ
  | .lt (.val x) (.num n), h => by
    simp only [CoreMode.resQ, Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
    obtain ⟨hn, b, hb, hbn⟩ := h
    obtain ⟨e, he, hσ⟩ := expQB_sound hT hE ht hf hall hb
    exact ⟨e, n, rep_val_gen hσ (by omega), CoreMode.rep_const hn, by omega⟩
  | .lt (.mono c) (.num n), h => by
    obtain ⟨cb, k⟩ := c
    simp only [CoreMode.resQ] at h
    split at h
    · rename_i x _
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
      obtain ⟨hn, b, hb, hbn⟩ := h
      obtain ⟨e, he, hσ⟩ := expQB_sound hT hE ht hf hall hb
      exact ⟨e + k, n, rep_mono_gen hσ (by omega), CoreMode.rep_const hn, by omega⟩
    · cases h
  | .lt (.num j) (.mono c), h => by
    obtain ⟨cb, k⟩ := c
    simp only [CoreMode.resQ] at h
    split at h
    · rename_i x _
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
      obtain ⟨hjk, b, hb, hbk⟩ := h
      obtain ⟨e, he, hσ⟩ := expQB_sound hT hE ht hf hall hb
      exact ⟨j, e + k, CoreMode.rep_const (by omega), rep_mono_gen hσ (by omega), by omega⟩
    · cases h
  | .lt (.val x) (.mono c), h => by
    obtain ⟨cb, u⟩ := c
    simp only [CoreMode.resQ] at h
    split at h
    · rename_i p _
      obtain ⟨e, m, hσx, hσp, hlt, hmu⟩ := dimLt_sound hD ht hf hall h
      have hcap : (2 : ℕ) ^ 34 ≤ capE := by rw [CoreMode.capE_eq]; norm_num
      exact ⟨e, m + u, rep_val_gen hσx (by omega), rep_mono_gen hσp (by omega), by omega⟩
    · cases h
  | .lt (.mono a) (.mono c), h => by
    obtain ⟨ab, t⟩ := a
    obtain ⟨cb, u⟩ := c
    simp only [CoreMode.resQ] at h
    split at h
    · rename_i x p _ _
      obtain ⟨e, m, hσx, hσp, hlt, hmu⟩ := dimLt_sound hD ht hf hall h
      have hcap : (2 : ℕ) ^ 34 ≤ capE := by rw [CoreMode.capE_eq]; norm_num
      exact ⟨e + t, m + u, rep_mono_gen hσx (by omega), rep_mono_gen hσp (by omega), by omega⟩
    · cases h
  | .lt (.val _) (.val _), h | .lt (.num _) (.num _), h | .lt (.num _) (.val _), h | .lt (.mono _) (.val _), h
  | .nz _, h | .sub _ _, h | .subR _ _, h | .subP _ _, h | .under _ _, h => by simp [CoreMode.resQ] at h

end

/-- **The `expQ` and `dim` families hold at an honest instance**: its exponent facts from what its callers hand it
(`termQ_all`, `expQv_all`), its dimension facts from `check_opening_terminal`'s (`dimQ_of_termQ`). -/
theorem resQ_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.resQ fn x = true) : x.Holds σ := by
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  have hT := termQ_all hr I hI
  exact resQ_sound hT (expQ_of_termQ hT (expQv_all hr I hI)) (dimQ_of_termQ hT) ht hf hall x h

/-- **The `split` family holds** at an honest instance (`splitFam_sound` on its path). -/
theorem splitFam_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.splitFam fn x = true) : x.Holds σ := by
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  exact splitFam_sound (by rw [find_name' hf]; exact hf) hw hh h

/-- **The residuals of a heap certificate of families hold** at an honest instance of its function, in
a frame holding its parameters whose entry runs' exponent cells are powers of `g`. -/
theorem resOk_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (h : resOk Cf = true) (hml : CoreMode.mlK Cf.fn = none)
    (hst : CoreMode.stK Cf.fn = none) {fp : ℕ}
    (hpar : ∀ k < Cf.fn.params.length, CoreMode.Rd r.img fp (2 + k) = some (σ (V.n k)))
    (hx : CoreMode.ExpW r.img Cf.xc fp) : ResF Cf.H σ := fun x hx' ↦ by
  have := List.all_eq_true.mp h x hx'
  simp only [CoreMode.resFamG, Bool.or_eq_true, Bool.and_eq_true] at this
  rcases this with (⟨(hf' | hq) | hsp, -⟩ | hm) | hs
  · exact resFam_inst hr hI ht hf hx hpar x hf'
  · exact resQ_inst hr hI ht hf hq
  · exact splitFam_inst hr hI ht hf hsp
  · cases x <;> simp [CoreMode.mlSub, hml] at hm
  · cases x <;> simp [CoreMode.stSub, hst] at hs

/-- **The residuals of a heap certificate of families hold** at a valuation `σ'` agreeing below `GB` with an honest
instance's, given its ghost family's (`mlSub`): the others name no ghost (`CRes.holds_congr`). -/
theorem resOk_instG {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (h : resOk Cf = true) {fp : ℕ}
    (hpar : ∀ k < Cf.fn.params.length, CoreMode.Rd r.img fp (2 + k) = some (σ (V.n k)))
    (hx : CoreMode.ExpW r.img Cf.xc fp) {σ' : Val}
    (hag : ∀ m < CoreMode.GB, σ' (V.n m) = σ (V.n m)) (hml : ∀ x, CoreMode.mlSub Cf.fn x = true → x.Holds σ')
    (hst : ∀ x, CoreMode.stSub Cf.fn x = true → x.Holds σ') :
    ResF Cf.H σ' := fun x hx' ↦ by
  have := List.all_eq_true.mp h x hx'
  simp only [CoreMode.resFamG, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at this
  rcases this with (⟨(hf' | hq) | hsp, hv⟩ | hm) | hs
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (resFam_inst hr hI ht hf hx hpar x hf')
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (resQ_inst hr hI ht hf hq)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (splitFam_inst hr hI ht hf hsp)
  · exact hml x hm
  · exact hst x hs

end

end LeanVM.Guest.EndExec
