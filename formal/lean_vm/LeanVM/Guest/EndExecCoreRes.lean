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
public import LeanVM.Guest.EndExecCoreVt
public import LeanVM.Guest.EndExecRVs
public import LeanVM.Guest.EndExecRCp
public import LeanVM.Guest.EndExecCoreDa

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

/-- **`verify_tables`' word `g_zc_n`** (`vtZc`) is `g^n`, `n < 34` (`VtQ`). -/
theorem vtZc_sound (hV : VtQ I) (ht : I.t = .node f σ bufs kids) (hf : coreProgram.find? f = some fn)
    {x : V} (h : CoreMode.vtZc fn x = true) : ∃ e < 34, σ x = gen ^ e := by
  simp only [CoreMode.vtZc, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hn, rfl⟩ := h
  have hf' : f = name% «verify_tables» := by rw [← find_name' hf, hn]
  subst hf'
  obtain ⟨-, n, -, hz, hn34, -⟩ := hV σ bufs kids ht
  exact ⟨n, hn34, hz⟩

/-- **A value of an exponent fact** (`expQ0`) is `g^e` below its bound. -/
theorem expQ0_sound (hT : TermQ r I) (hV : VtQ I) (hE : ExpQ r I) (ht : I.t = .node f σ bufs kids)
    (hf : coreProgram.find? f = some fn)
    (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) {x : V} {b : ℕ} (h : CoreMode.expQ0 fn x = some b) :
    ∃ e < b, σ x = gen ^ e := by
  unfold CoreMode.expQ0 at h
  rcases h1 : CoreMode.expQ1 fn x with _ | b'
  · rw [h1] at h
    simp only at h
    cases hg : CoreMode.termGm fn x
    · rw [hg, Bool.cond_false] at h
      cases hz : CoreMode.vtZc fn x
      · rw [hz, Bool.cond_false] at h; cases h
      · rw [hz, Bool.cond_true, Option.some.injEq] at h
        subst h
        exact vtZc_sound hV ht hf hz
    · rw [hg, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact termGm_sound hT ht hf hg
  · rw [h1] at h
    obtain rfl := Option.some.inj h
    exact expQ1_sound hE ht hf hall h1

/-- **A value of an exponent fact, a product of one and a constant power, or a copy of one** (`expQB`) is `g^e`
below its bound. -/
theorem expQB_sound (hT : TermQ r I) (hV : VtQ I) (hE : ExpQ r I) (ht : I.t = .node f σ bufs kids)
    (hf : coreProgram.find? f = some fn)
    (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) {x : V} {b : ℕ} (h : CoreMode.expQB fn x = some b) :
    ∃ e < b, σ x = gen ^ e := by
  unfold CoreMode.expQB at h
  rcases h1 : CoreMode.expQ0 fn x with _ | b'
  · rw [h1] at h
    simp only at h
    obtain ⟨a, ha, haf⟩ := List.exists_of_findSome?_eq_some h
    cases a with
    | mul d a w =>
      simp only at haf
      split_ifs at haf with hd
      subst hd
      rcases hb1 : CoreMode.expQ0 fn a with _ | b1
      · rw [hb1] at haf; simp at haf
      · rcases hc : (Res.constOf (Res.topAtoms fn.body) w).bind Res.powOf with _ | c
        · rw [hb1, hc] at haf; simp at haf
        · rw [hb1, hc] at haf
          simp only [Option.some.injEq] at haf
          subst haf
          obtain ⟨e, he, hσa⟩ := expQ0_sound hT hV hE ht hf hall hb1
          obtain ⟨w0, hw0, hpw⟩ := Option.bind_eq_some_iff.mp hc
          have hσw : σ w = w0 := hall _ (constOf_sound hw0)
          have hmul : σ d = σ a * σ w := hall _ ha
          refine ⟨e + c, by omega, ?_⟩
          rw [hmul, hσa, hσw, powOf_sound hpw, ← Value.gen_pow_eq_ofK, pow_add]
    | copy d a =>
      simp only at haf
      split_ifs at haf with hd
      subst hd
      obtain ⟨e, he, hσa⟩ := expQ0_sound hT hV hE ht hf hall haf
      have hcp : σ d = σ a := hall _ ha
      exact ⟨e, he, by rw [hcp, hσa]⟩
    | _ => simp at haf
  · rw [h1] at h
    obtain rfl := Option.some.inj h
    exact expQ0_sound hT hV hE ht hf hall h1

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
theorem resQ_sound (hT : TermQ r I) (hV : VtQ I) (hE : ExpQ r I) (hD : DimQ r I) (ht : I.t = .node f σ bufs kids)
    (hf : coreProgram.find? f = some fn) (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) :
    ∀ x : CRes, CoreMode.resQ fn x = true → x.Holds σ
  | .lt (.val x) (.num n), h => by
    simp only [CoreMode.resQ, Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
    obtain ⟨hn, b, hb, hbn⟩ := h
    obtain ⟨e, he, hσ⟩ := expQB_sound hT hV hE ht hf hall hb
    exact ⟨e, n, rep_val_gen hσ (by omega), CoreMode.rep_const hn, by omega⟩
  | .lt (.mono c) (.num n), h => by
    obtain ⟨cb, k⟩ := c
    simp only [CoreMode.resQ] at h
    split at h
    · rename_i x _
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
      obtain ⟨hn, b, hb, hbn⟩ := h
      obtain ⟨e, he, hσ⟩ := expQB_sound hT hV hE ht hf hall hb
      exact ⟨e + k, n, rep_mono_gen hσ (by omega), CoreMode.rep_const hn, by omega⟩
    · cases h
  | .lt (.num j) (.mono c), h => by
    obtain ⟨cb, k⟩ := c
    simp only [CoreMode.resQ] at h
    split at h
    · rename_i x _
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
      obtain ⟨hjk, b, hb, hbk⟩ := h
      obtain ⟨e, he, hσ⟩ := expQB_sound hT hV hE ht hf hall hb
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
  exact resQ_sound hT (vtQ_all hr I hI) (expQ_of_termQ hT (expQv_all hr I hI)) (dimQ_of_termQ hT) ht hf hall x h

/-- **`verify_tables`' reads past its table sumcheck** (`vtStC`) at an honest instance: the last record's cursor
`σ 2652` is `14 + 3n` words past the frame's cursor (`Tables.vt_zc_run`, `vt_cur13`), which `VtQ` puts `p` words into
the stream with room for `1009`. -/
theorem vtStC_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.vtStC fn x = true) : x.Holds σ := by
  match x, h with
  | .sub c q, h =>
    simp only [CoreMode.vtStC, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, hcb⟩, hco⟩, rfl⟩ := h
    have hf' : f = name% «verify_tables» := by rw [← find_name' hf, hn]
    subst hf'
    obtain rfl : fn = fn% «verify_tables» := Option.some.inj (hf.symm.trans B1.VerifySub.find_vt)
    obtain ⟨p, n, e5, hgn, hn34, hroom⟩ := vtQ_all hr I hI σ bufs kids ht
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
    have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
      unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
    obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hf
    obtain ⟨hH, -⟩ := vt_holds (fun _ _ _ h ↦ Res.KidRel.rel h) hf hb
    obtain ⟨-, xs, pts, cl, -, -, -, -, e2652, -⟩ := B1.Tables.vt_zc_run hH hn34 hgn
    have hcur : σ (.n 2652) = σ (.n 20) * Protocol.Verifier.gen ^ (p + 14 + 3 * n) := by
      rw [e2652, vt_cur13 hH, e5]; ring
    have hcap : (8192 : ℕ) < CoreMode.capE := by rw [CoreMode.capE_eq]; norm_num
    refine ⟨0, 8192, p + 14 + 3 * n + c.off, CoreMode.rep_const (by rw [CoreMode.capE_eq]; norm_num),
      CoreMode.rep_const hcap, Nat.zero_le _, by omega, ?_⟩
    obtain ⟨cb, co⟩ := c
    simp only at hcb
    subst hcb
    simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, one_mul, hcur,
      ← Value.gen_pow_eq_ofK, addressOfIndex]
    rw [mul_assoc, ← pow_add]
    ring_nf
  | .lt _ _, h | .nz _, h | .subR _ _, h | .subP _ _, h | .under _ _, h => simp [CoreMode.vtStC] at h

/-! ## A range-checked index, `certify_placement`'s order, `verify_sub`'s exponents -/

/-- **A cell at a range-checked index is one of the points it can be** (`rcPts`): the index `g^e`, `e < N`. -/
theorem rcPts_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.rcPts fn x = true) : x.Holds σ := by
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have key : ∀ {B J o : ℕ} {cs : List CoreMode.CCell}, CoreMode.rcPtsAt fn B J o cs = true →
      ∃ c' ∈ cs, σ (V.n B) * σ (V.n J) * ofK (addressOfIndex o) = CoreMode.CCell.valW (vw σ) c' := by
    intro B J o cs hp
    unfold CoreMode.rcPtsAt at hp
    split at hp
    · rename_i N hN
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        List.contains_iff_mem] at hp
      obtain ⟨-, hc⟩ := hp
      obtain ⟨e, he, hσ⟩ := rcBound_sound (by omega) r.img hall hN
      refine ⟨⟨[(B, 1)], o + e⟩, hc e he, ?_⟩
      simp only [CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, hσ, Value.gen_pow_eq_ofK,
        addressOfIndex, pow_add, CoreMode.ofK_mul']
      ring
    · cases hp
  match x, h with
  | .subP ⟨cb, o⟩ cs, h =>
    simp only [CoreMode.rcPts] at h
    split at h
    · rename_i a b
      rcases Bool.or_eq_true_iff.mp h with h | h
      · obtain ⟨c', hc', he⟩ := key h
        refine ⟨c', hc', ?_⟩
        unfold CoreMode.CCell.addrW
        rw [← he]
        simp only [CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one]
      · obtain ⟨c', hc', he⟩ := key h
        refine ⟨c', hc', ?_⟩
        unfold CoreMode.CCell.addrW
        rw [← he]
        simp only [CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one]
        ring_nf
    · cases h
  | .lt _ _, h | .nz _, h | .sub _ _, h | .subR _ _, h | .under _ _, h => simp [CoreMode.rcPts] at h

/-- **`certify_placement`'s cell `[137]·g^k`, `k < 9`, is one of `[137]·[v]` over its ranks' groups** (`cpPerm`): the
ranks' groups are onto (`cp_onto`). -/
theorem cpPerm_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.cpPerm fn x = true) : x.Holds σ := by
  match x, h with
  | .subP ⟨cb, k⟩ cs, h =>
    simp only [CoreMode.cpPerm, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, hcb⟩, hco⟩, rfl⟩ := h
    subst hcb
    have hf' : f = "certify_placement" := by rw [← find_name' hf, hn]
    subst hf'
    obtain ⟨args0, rets0, hv⟩ := inst_valid' hr hI ht
    obtain ⟨fn0, hfn, hps, hbody⟩ := B1.Tables.cpFound
    obtain rfl : fn = fn0 := Option.some.inj (hf.symm.trans hfn)
    obtain ⟨-, hb⟩ := LeanVM.Guest.Res.holds_of_valid LeanVM.Guest.Res.fs_pos hv hfn
    rw [hbody, holdsList_append, holdsList_noRet _ B1.Tables.cpPre_noRet] at hb
    have htab : B1.ExpTables r.img.read (σ (.n 1)) :=
      (carryQ_all hr I hI _ σ bufs kids ht fn hfn ("certify_placement", 1, .tab) (by decide) rfl (.n 1)
        (by rw [hps]; rfl)).1
    have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
    obtain ⟨hK, hfc, -⟩ := cp_keys (by omega) r.img hb.1 htab
    obtain ⟨π, hπ, hon⟩ := cp_onto hK hfc
    obtain ⟨r0, hr0, hπr⟩ := hon k hco
    have hranks : CoreMode.cpRanks = (List.range 9).map B1.Tables.cpRB := by decide
    refine ⟨⟨[(137, 1), (B1.Tables.cpRB r0, 1)], 0⟩, ?_, ?_⟩
    · rw [hranks, List.map_map]
      exact List.mem_map.mpr ⟨r0, List.mem_range.mpr hr0, rfl⟩
    · simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, hπ r0 hr0, hπr,
        Value.gen_pow_eq_ofK, addressOfIndex, pow_zero, show ofK (1 : Parameters.K) = 1 from map_one (algebraMap Parameters.K Parameters.E)]
  | .lt _ _, h | .nz _, h | .sub _ _, h | .subR _ _, h | .under _ _, h => simp [CoreMode.cpPerm] at h

/-- `verify_sub`'s exponents by value, from its values (`vs_valsI`). -/
def vsE (hs : List ℕ) (d n sl : ℕ) : ℕ → ℕ
  | 86 => hs.getD 0 0
  | 87 => hs.getD 1 0
  | 88 => hs.getD 2 0
  | 89 => hs.getD 3 0
  | 90 => hs.getD 4 0
  | 91 => hs.getD 5 0
  | 583 => hs.getD 5 0
  | 253 => d
  | 579 => n
  | 276 => sl
  | _ => sl - 20

/-- **`verify_sub`'s exponents** (`vsPows`, `vsLes`): each listed value `g^(E v)` within its bounds, the orders, the
cursors. -/
theorem vs_exps {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_sub» σ bufs kids)
    (hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds r.img.read σ) :
    ∃ E : ℕ → ℕ, (∀ v lo hi, (v, lo, hi) ∈ CoreMode.vsPows → lo ≤ E v ∧ E v ≤ hi ∧
        σ (V.n v) = Protocol.Verifier.gen ^ E v) ∧
      (∀ x y c, (x, y, c) ∈ CoreMode.vsLes → E x ≤ E y + c) ∧
      ∃ gK, (∀ x ∈ CoreMode.vsCurs, ∃ gX ≤ gK, σ (V.n x) = σ (.n 25) * Protocol.Verifier.gen ^ gX) ∧
        gK + 207 ≤ 8192 := by
  obtain ⟨hs, lm, sl, d, n, gG, gT, gK, hsL, hs31, hτ9, hτ24, hrd, hsl20, hsl30, e278, e276, hd20, hd34, e253,
    hτn, hnd, e579, e567, e578, e595, hGT, hTK, hroom⟩ := vs_valsI hr hI ht
  -- the dims' words, read at `71`'s cells by the top-level loads
  have hld : ∀ v t, Atom.load (.n v) (.n 71) (t + 1) ∈ Res.topAtoms (fn% «verify_sub»).body → t < 6 →
      σ (.n v) = Protocol.Verifier.gen ^ hs.getD t 0 := by
    intro v t hm ht6
    have hx : (Atom.load (.n v) (.n 71) (t + 1)).Holds r.img.read σ := hall _ hm
    have hy := hrd (t + 1) (by simp [hsL]; omega)
    have := loadHolds_det hx hy
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < hs.length by omega)]
  have hm : ([(86, 0), (87, 1), (88, 2), (89, 3), (90, 4), (91, 5), (583, 5)] : List (ℕ × ℕ)).all
      (fun p ↦ (Res.topAtoms (fn% «verify_sub»).body).contains (Atom.load (.n p.1) (.n 71) (p.2 + 1))) = true := by
    decide +kernel
  have hm' : ∀ v t, (v, t) ∈ ([(86, 0), (87, 1), (88, 2), (89, 3), (90, 4), (91, 5), (583, 5)] : List (ℕ × ℕ)) →
      t < 6 → σ (.n v) = Protocol.Verifier.gen ^ hs.getD t 0 := fun v t hvt ht6 ↦
    hld v t (List.contains_iff_mem.mp (List.all_eq_true.mp hm (v, t) hvt)) ht6
  have h31 : ∀ t < 6, hs.getD t 0 < 31 := fun t ht ↦
    hs31 _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  refine ⟨vsE hs d n sl, fun v lo hi hv ↦ ?_, fun x y c hl ↦ ?_, gK, fun x hx ↦ ?_, hroom⟩
  · simp only [CoreMode.vsPows, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hv
    rcases hv with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨Nat.zero_le _, by have := h31 0 (by omega); show hs.getD 0 0 ≤ 30; omega,
        hm' 86 0 (by simp) (by omega)⟩
    · exact ⟨Nat.zero_le _, by have := h31 1 (by omega); show hs.getD 1 0 ≤ 30; omega,
        hm' 87 1 (by simp) (by omega)⟩
    · exact ⟨Nat.zero_le _, by have := h31 2 (by omega); show hs.getD 2 0 ≤ 30; omega,
        hm' 88 2 (by simp) (by omega)⟩
    · exact ⟨Nat.zero_le _, by have := h31 3 (by omega); show hs.getD 3 0 ≤ 30; omega,
        hm' 89 3 (by simp) (by omega)⟩
    · exact ⟨Nat.zero_le _, by have := h31 4 (by omega); show hs.getD 4 0 ≤ 30; omega,
        hm' 90 4 (by simp) (by omega)⟩
    · exact ⟨show 9 ≤ hs.getD 5 0 by omega, show hs.getD 5 0 ≤ 24 by omega, hm' 91 5 (by simp) (by omega)⟩
    · exact ⟨show 9 ≤ hs.getD 5 0 by omega, show hs.getD 5 0 ≤ 24 by omega, hm' 583 5 (by simp) (by omega)⟩
    · exact ⟨show 20 ≤ d by omega, show d ≤ 33 by omega, e253⟩
    · exact ⟨show 9 ≤ n by omega, show n ≤ 33 by omega, e579⟩
    · exact ⟨show 20 ≤ sl by omega, show sl ≤ 30 by omega, e276⟩
    · exact ⟨Nat.zero_le _, show sl - 20 ≤ 10 by omega, e278⟩
  · simp only [CoreMode.vsLes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hl
    rcases hl with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · show hs.getD 5 0 ≤ n + 0; omega
    · show hs.getD 5 0 ≤ n + 0; omega
    · show sl ≤ sl - 20 + 20; omega
  · simp only [CoreMode.vsCurs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨gG, by omega, e567⟩
    · exact ⟨gT, by omega, e578⟩
    · exact ⟨gK, le_rfl, e595⟩

/-- `verify_sub`'s index as its value times `g^c` (`vsBase`): its word's exponent plus `c`. -/
theorem vsBase_rep {σ : Val} (hM : σ (.n 278) = σ (.n 276) * σ (.n 277)) {i : CIdx} {x c : ℕ}
    (h : CoreMode.vsBase i = some (x, c)) {e : ℕ} (hσ : σ (V.n x) = Protocol.Verifier.gen ^ e) (hc : e + c < capE) :
    CoreMode.rep ((idxC i).valW (vw σ)) = some (e + c) := by
  cases i with
  | num n => simp [CoreMode.vsBase] at h
  | val v =>
    simp only [CoreMode.vsBase, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact rep_val_gen hσ (by omega)
  | mono m =>
    obtain ⟨cb, o⟩ := m
    simp only [CoreMode.vsBase] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact rep_mono_gen hσ hc
    · rename_i a b
      obtain ⟨x', hx', hxe⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      have hm := CoreMode.lookup_memL hx'
      simp only [CoreMode.vsMuls, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
      have := rep_mono_gen (c := o) (x := 278) hσ hc
      simpa [idxC, CoreMode.CCell.valW, CoreMode.prodW, vw, hM, mul_assoc] using this
    · cases h

/-- **`verify_sub`'s exponent family holds** at an honest instance (`vsExp`). -/
theorem vsExp_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.vsExp fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ vsExp_inst hr hI ht hf r' h
  | .lt a b, h => by
    simp only [CoreMode.vsExp, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hn, h⟩ := h
    have hf' : f = name% «verify_sub» := by rw [← find_name' hf, hn]
    subst hf'
    obtain rfl : fn = fn% «verify_sub» := Option.some.inj (hf.symm.trans B1.VerifySub.find_vs)
    obtain ⟨args, rets, fn', hf'', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn% «verify_sub» = fn' := Option.some.inj (B1.VerifySub.find_vs.symm.trans hf'')
    have hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds r.img.read σ :=
      fun a ha ↦ hh _ (topAtoms_on_path hw ha)
    obtain ⟨E, hP, hL, -⟩ := vs_exps hr hI ht hall
    have hM : σ (.n 278) = σ (.n 276) * σ (.n 277) :=
      hall (.mul (.n 278) (.n 276) (.n 277)) (by decide +kernel)
    -- an index's exponent, within its bounds
    have hiv : ∀ i l h', CoreMode.vsIv i = some (l, h') → h' < capE → ∃ y, l ≤ y ∧ y ≤ h' ∧
        CoreMode.rep ((idxC i).valW (vw σ)) = some y ∧ ∀ x c, CoreMode.vsBase i = some (x, c) → y = E x + c := by
      intro i l h' hi hc
      cases i with
      | num n =>
        simp only [CoreMode.vsIv, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        exact ⟨_, le_rfl, le_rfl, CoreMode.rep_const hc, fun x c hb ↦ by simp [CoreMode.vsBase] at hb⟩
      | _ =>
        simp only [CoreMode.vsIv] at hi
        obtain ⟨⟨x, c⟩, hb, hp⟩ := Option.bind_eq_some_iff.mp hi
        obtain ⟨⟨lo, hi'⟩, hl, he⟩ := Option.map_eq_some_iff.mp hp
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h1, h2, hσ⟩ := hP x lo hi' (CoreMode.lookup_memL hl)
        exact ⟨E x + c, by omega, by omega, vsBase_rep hM hb hσ (by omega),
          fun x' c' hb' ↦ by rw [hb] at hb'; cases hb'; rfl⟩
    simp only [CoreMode.vsLt] at h
    split at h
    · rename_i la ha lb hb hia hib
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
      obtain ⟨⟨hca, hcb⟩, h⟩ := h
      obtain ⟨ya, -, hya, hra, hea⟩ := hiv a _ _ hia hca
      obtain ⟨yb, hyb, -, hrb, heb⟩ := hiv b _ _ hib hcb
      refine ⟨ya, yb, hra, hrb, ?_⟩
      rcases h with h | h
      · omega
      · split at h
        · rename_i x ca y cb hba hbb
          obtain ⟨⟨lx, ly, lc⟩, hl, hle⟩ := List.any_eq_true.mp h
          simp only [decide_eq_true_eq] at hle
          obtain ⟨rfl, rfl, hlt⟩ := hle
          have := hL _ _ _ hl
          rw [hea _ _ hba, heb _ _ hbb]
          omega
        · cases h
    · cases h
  | .sub c q, h => by
    simp only [CoreMode.vsExp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn, rfl⟩, hcx⟩, hco⟩ := h
    have hf' : f = name% «verify_sub» := by rw [← find_name' hf, hn]
    subst hf'
    obtain rfl : fn = fn% «verify_sub» := Option.some.inj (hf.symm.trans B1.VerifySub.find_vs)
    obtain ⟨args, rets, fn', hf'', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn% «verify_sub» = fn' := Option.some.inj (B1.VerifySub.find_vs.symm.trans hf'')
    have hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds r.img.read σ :=
      fun a ha ↦ hh _ (topAtoms_on_path hw ha)
    obtain ⟨E, -, -, gK, hC, hroom⟩ := vs_exps hr hI ht hall
    obtain ⟨cb, k⟩ := c
    simp only at hcx hco
    split at hcx
    · rename_i x
      obtain ⟨gX, hgX, hσ⟩ := hC x (List.contains_iff_mem.mp hcx)
      refine (CoreMode.runSet_const (q := ⟨⟨[(25, 1)], 0⟩, 1, .num 0, .num 8192⟩) rfl rfl (by norm_num)
        (by norm_num)).mpr ⟨gX + k, Nat.zero_le _, by omega, ?_⟩
      simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, hσ,
        Value.gen_pow_eq_ofK, addressOfIndex, pow_zero, one_mul, pow_add, CoreMode.ofK_mul',
        show ofK (1 : Parameters.K) = 1 from map_one (algebraMap Parameters.K Parameters.E), mul_one, mul_assoc]
    · cases hcx
  | .nz _, h | .subR _ _, h | .subP _ _, h => by simp [CoreMode.vsExp] at h

/-- **The `split` family holds** at an honest instance (`splitFam_sound` on its path). -/
theorem splitFam_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CRes} (h : CoreMode.splitFam fn x = true) : x.Holds σ := by
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  exact splitFam_sound (by rw [find_name' hf]; exact hf) hw hh h

/-! ## `keccak_layer`'s cursor -/

/-- **`keccak_layer__L{first}` at an honest instance** (`LayQ`, `layer_cur`): its pack rounds' words, its last record's
cursor `p + 48 + 2y` words into its stream, with room for `84 + 2y` words. -/
theorem layCur_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {v : ℕ} (hv : CoreMode.layCur fn = some v) :
    ∃ p y, σ (.n 9) = Protocol.Verifier.gen ^ (y / B1.VerifySub.krStep) ∧
      σ (.n 10) = Protocol.Verifier.gen ^ (y % B1.VerifySub.krStep) ∧ y < 32 ∧
      σ (.n v) = σ (.n 15) * Protocol.Verifier.gen ^ (p + 48 + 2 * y) ∧ p + 84 + 2 * y ≤ 8192 := by
  have hn : ∃ first < 2, fn.name = B1.VerifySub.layerName first ∧ v = B1.VerifySub.layOff first + 744 := by
    simp only [CoreMode.layCur, Bool.cond_eq_ite, beq_iff_eq] at hv
    split_ifs at hv with h0 h1
    · exact ⟨0, by decide, h0, (Option.some.inj hv).symm⟩
    · exact ⟨1, by decide, h1, (Option.some.inj hv).symm⟩
  obtain ⟨first, hfi, hname, rfl⟩ := hn
  have hf' : f = B1.VerifySub.layerName first := by rw [← find_name' hf, hname]
  subst hf'
  obtain ⟨fL, hfL, hbL, -⟩ := layer_found hfi
  obtain rfl : fn = fL := Option.some.inj (hf.symm.trans hfL)
  obtain ⟨p, y, e7, hy, h9, h10, hroom⟩ := layQ_all hr I hI _ σ bufs kids ht first hfi rfl
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
  have hfs : ∀ f', 1 ≤ B2C.fs f' := fun f' ↦ by
    unfold B2C.fs; split <;> simp [B2C.mainFrame, Data.mainCells, Data.jtSlots]
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hf
  obtain ⟨hcur, -⟩ := layer_cur hfi (fun _ _ _ h ↦ Res.KidRel.rel h) hy h9 h10 hbL hb
  refine ⟨p, y, h9, h10, hy, ?_, by omega⟩
  rw [hcur, e7, mul_assoc, ← pow_add]
  ring_nf

/-- **`keccak_layer`'s family holds** at an honest instance (`layQC`): `LayQ` puts its cursor `p` words into its stream
with room for `84 + 2y` words and its pack rounds' words below `32`, its last record's cursor `48 + 2y` words past it
(`layer_cur`). -/
theorem layQC_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.layQC fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ layQC_inst hr hI ht hf r' h
  | .sub c q, h => by
    simp only [CoreMode.layQC, Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
    obtain ⟨⟨⟨v, hv, hcb⟩, hco⟩, rfl⟩ := h
    obtain ⟨p, y, -, -, -, hcur, hroom⟩ := layCur_inst hr hI ht hf hv
    have hcap : (8192 : ℕ) < CoreMode.capE := by rw [CoreMode.capE_eq]; norm_num
    refine ⟨0, 8192, p + 48 + 2 * y + c.off, CoreMode.rep_const (by rw [CoreMode.capE_eq]; norm_num),
      CoreMode.rep_const hcap, Nat.zero_le _, by omega, ?_⟩
    obtain ⟨cb, co⟩ := c
    simp only at hcb
    subst hcb
    simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, one_mul, hcur,
      ← Value.gen_pow_eq_ofK, addressOfIndex]
    rw [mul_assoc, ← pow_add]
    ring_nf
  | .lt (.val x) (.num n), h => by
    simp only [CoreMode.layQC, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, decide_eq_true_eq,
      Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨⟨v, hv⟩, hx⟩, hn⟩, hnc⟩ := h
    obtain ⟨p, y, h9, h10, hy, -⟩ := layCur_inst hr hI ht hf hv
    have hk : 0 < B1.VerifySub.krStep := by decide
    have h8 : B1.VerifySub.krStep ≤ 32 := by decide
    rcases hx with rfl | rfl
    · exact ltF_of_pow (e := y / B1.VerifySub.krStep) hnc (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
        (by rw [h9, Value.gen_pow_eq_ofK])
    · exact ltF_of_pow (e := y % B1.VerifySub.krStep) hnc (by have := Nat.mod_lt y hk; omega)
        (by rw [h10, Value.gen_pow_eq_ofK])
  | .lt (.val _) (.val _), h | .lt (.val _) (.mono _), h | .lt (.num _) _, h | .lt (.mono _) _, h
  | .nz _, h | .subR _ _, h | .subP _ _, h => by simp [CoreMode.layQC] at h

/-- **`verify_tables`' copy loop's read index holds** at an honest instance (`vtCp`): `VtCQ`'s counter `g^i` below its
bound `g^n`, which its last parameter also holds, so the index `x·g^-1/i` is `g^(n - 1 - i)` (`Tables.vt_chi_index`). -/
theorem vtCp_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.vtCp fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ vtCp_inst hr hI ht hf r' h
  | .lt a b, h => by
    simp only [CoreMode.vtCp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨h, rfl⟩, rfl⟩ := h
    have hf' : f = name% «verify_tables_loop1» := by rw [← find_name' hf, h]
    subst hf'
    obtain rfl : fn = fn% «verify_tables_loop1» := Option.some.inj (hf.symm.trans find_l11)
    obtain ⟨ii, n, h0, h1, h4, hin, hn⟩ := vtCQ_all hr I hI σ bufs kids ht
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
    obtain ⟨-, hb⟩ := Res.holds_of_valid hfs_vt hv find_l11
    obtain ⟨fn, hf2, -, hbody⟩ := B1.Tables.l11Found
    obtain rfl : fn = fn% «verify_tables_loop1» := Option.some.inj (hf2.symm.trans find_l11)
    rw [hbody] at hb
    simp only [B1.Tables.l11Body, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hb
    obtain ⟨c5, m6a, m6b, -⟩ := hb
    simp only [Atom.Holds] at c5 m6a m6b
    have hy : Protocol.Verifier.gen ^ n * B1.Tables.vtWInvGen = σ (.n 7) * Protocol.Verifier.gen ^ ii := by
      rw [← h4, ← c5, ← m6a, m6b, h0]
    have e7 := B1.Tables.vt_chi_index hin hy
    have hcap : (34 : ℕ) ≤ capE := by rw [CoreMode.capE_eq]; norm_num
    refine ⟨n - 1 - ii, n, ?_, ?_, by omega⟩
    · simp only [idxC, CoreMode.valW_baseC, vw, e7, Value.gen_pow_eq_ofK]
      exact rep_of (by omega)
    · simp only [idxC, CoreMode.valW_baseC, vw, h1, Value.gen_pow_eq_ofK]
      exact rep_of (by omega)
  | .nz _, h | .subR _ _, h | .subP _ _, h | .sub _ _, h => by simp [CoreMode.vtCp] at h

/-! ## `da_pad`'s gap -/

/-- **`da_pad`'s gap holds** at an honest instance (`daGap`): `DaPadQ`. -/
theorem daGap_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.daGap fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ daGap_inst hr hI ht hf r' h
  | .lt a b, h => by
    simp only [CoreMode.daGap, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hn, rfl⟩, h⟩ := h
    split at h
    · rename_i m
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have hf' : f = name% «da_pad» := by rw [← find_name' hf, hn]
      subst hf'
      obtain ⟨k, hk, e2⟩ := daPadQ_all hr I hI σ bufs kids ht
      exact ltF_of_pow (e := k) h.2 (by omega) (by rw [e2, Value.gen_pow_eq_ofK])
    · cases h
  | .nz _, h | .subR _ _, h | .subP _ _, h | .sub _ _, h => by simp [CoreMode.daGap] at h

/-! ## A range-checked table read -/

theorem ldAt_mem {as : List Atom} {x p : ℕ} (h : CoreMode.ldAt as x = some p) :
    Atom.load (V.n x) (V.n p) 0 ∈ as := by
  unfold CoreMode.ldAt at h
  obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | load v pv o =>
    cases o with
    | zero =>
      simp only at hf
      split at hf
      · rename_i x' p' hx hp
        cases hb : Nat.beq x' x <;> simp only [hb, Bool.cond_true, Bool.cond_false, reduceCtorEq,
          Option.some.injEq] at hf
        subst hf
        rw [CoreMode.vnum_eq hx, CoreMode.vnum_eq hp, Nat.eq_of_beq_eq_true hb] at ha
        exact ha
      · cases hf
    | succ o => simp at hf
  | _ => simp at hf

theorem mulAt_mem {as : List Atom} {p a b : ℕ} (h : CoreMode.mulAt as p = some (a, b)) :
    Atom.mul (V.n p) (V.n a) (V.n b) ∈ as := by
  unfold CoreMode.mulAt at h
  obtain ⟨c, hc, hf⟩ := List.exists_of_findSome?_eq_some h
  cases c with
  | mul d a' b' =>
    simp only at hf
    split at hf
    · rename_i p' a'' b'' hd ha hb
      cases hq : Nat.beq p' p <;> simp only [hq, Bool.cond_true, Bool.cond_false, reduceCtorEq,
        Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      rw [CoreMode.vnum_eq hd, CoreMode.vnum_eq ha, CoreMode.vnum_eq hb, Nat.eq_of_beq_eq_true hq] at hc
      exact hc
    · cases hf
  | _ => simp at hf

theorem stAt_mem {as : List Atom} {T t c : ℕ} (h : CoreMode.stAt as T t = some c) :
    Atom.load (V.n c) (V.n T) t ∈ as := by
  unfold CoreMode.stAt at h
  obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | load v pv o =>
    simp only at hf
    split at hf
    · rename_i c' T' hc hT
      cases hb : (Nat.beq T' T && Nat.beq o t) <;> simp only [hb, Bool.cond_true, Bool.cond_false, reduceCtorEq,
        Option.some.injEq] at hf
      subst hf
      simp only [Bool.and_eq_true] at hb
      rw [CoreMode.vnum_eq hc, CoreMode.vnum_eq hT, Nat.eq_of_beq_eq_true hb.1, Nat.eq_of_beq_eq_true hb.2] at ha
      exact ha
    · cases hf
  | _ => simp at hf

/-- **An index's exponent at a table's row** (`tabEv`): the read `g^k`, the index `g^t`. -/
theorem tabEv_rep {σ : Val} {x J t k u : ℕ} (hx : σ (V.n x) = Protocol.Verifier.gen ^ k) (hJ : σ (V.n J) = Protocol.Verifier.gen ^ t) :
    ∀ {i : CIdx}, CoreMode.tabEv x J t k i = some u → u < capE → CoreMode.rep ((idxC i).valW (vw σ)) = some u
  | .num n, h, hu => by
    simp only [CoreMode.tabEv, Option.some.injEq] at h
    subst h
    exact CoreMode.rep_const hu
  | .val v, h, hu => by
    simp only [CoreMode.tabEv] at h
    rw [idxC, CoreMode.valW_baseC, show vw σ v = σ (V.n v) from rfl]
    cases hb : Nat.beq v x <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
    · cases hb' : Nat.beq v J <;> simp only [hb', Bool.cond_true, Bool.cond_false, reduceCtorEq,
        Option.some.injEq] at h
      subst h
      rw [Nat.eq_of_beq_eq_true hb', hJ, Value.gen_pow_eq_ofK]
      exact rep_of hu
    · simp only [Option.some.injEq] at h
      subst h
      rw [Nat.eq_of_beq_eq_true hb, hx, Value.gen_pow_eq_ofK]
      exact rep_of hu
  | .mono c, h, hu => by
    -- the product's word, `g^u`
    have key : ∀ (bs : List (ℕ × ℕ)) (o u : ℕ), bs.foldr (fun b acc ↦ acc.bind fun a ↦
        (bif Nat.beq b.1 x then some (b.2 * k) else bif Nat.beq b.1 J then some (b.2 * t) else none).map (a + ·))
        (some o) = some u → CoreMode.prodW (vw σ) bs * ofK (addressOfIndex o) = ofK (addressOfIndex u) := by
      intro bs
      induction bs with
      | nil =>
        intro o u h
        simp only [List.foldr_nil, Option.some.injEq] at h
        subst h
        simp [CoreMode.prodW]
      | cons b bs ih =>
        intro o u h
        simp only [List.foldr_cons] at h
        obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp h
        have e1 := ih o a ha
        obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hb
        have hw : vw σ b.1 ^ b.2 = ofK (addressOfIndex d) := by
          rw [show vw σ b.1 = σ (V.n b.1) from rfl]
          cases hx' : Nat.beq b.1 x <;> simp only [hx', Bool.cond_true, Bool.cond_false] at hd
          · cases hJ' : Nat.beq b.1 J <;> simp only [hJ', Bool.cond_true, Bool.cond_false, reduceCtorEq,
              Option.some.injEq] at hd
            subst hd
            rw [Nat.eq_of_beq_eq_true hJ', hJ, Value.gen_pow_eq_ofK, ← CoreMode.ofK_pow', addressOfIndex,
              addressOfIndex, ← pow_mul, Nat.mul_comm]
          · simp only [Option.some.injEq] at hd
            subst hd
            rw [Nat.eq_of_beq_eq_true hx', hx, Value.gen_pow_eq_ofK, ← CoreMode.ofK_pow', addressOfIndex,
              addressOfIndex, ← pow_mul, Nat.mul_comm]
        simp only [CoreMode.prodW]
        rw [mul_assoc, e1, hw, ← CoreMode.ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add,
          Nat.add_comm]
    simp only [CoreMode.tabEv] at h
    simp only [idxC, CoreMode.CCell.valW]
    rw [key c.bases c.off u h]
    exact rep_of hu

/-- **A table read's row** at an honest path: `x = g^(k_t)`, its index `g^t`, `t < N`. -/
theorem tabOf_row {r : Ref} (hr : r.Ok) {fn : Fn} {σ : Val} (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ)
    {x T J N : ℕ} (h : CoreMode.tabOf fn x = some (T, J, N)) :
    ∃ t < N, σ (V.n J) = Protocol.Verifier.gen ^ t ∧ ∀ k, CoreMode.tabK fn T t = some k → σ (V.n x) = Protocol.Verifier.gen ^ k := by
  unfold CoreMode.tabOf at h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨T', J'⟩, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨N', hN, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨t, ht, hJ⟩ := rcBound_sound (by omega) r.img hall hN
  have hld : LoadHolds r.img.read (σ (V.n p)) 0 (σ (V.n x)) := hall _ (ldAt_mem hp)
  have hmul : σ (V.n p) = σ (V.n T') * σ (V.n J') := hall _ (mulAt_mem hm)
  refine ⟨t, ht, hJ, fun k hk ↦ ?_⟩
  unfold CoreMode.tabK at hk
  obtain ⟨c, hc, hk⟩ := Option.bind_eq_some_iff.mp hk
  obtain ⟨w, hw, hpw⟩ := Option.bind_eq_some_iff.mp hk
  have hst : LoadHolds r.img.read (σ (V.n T')) t (σ (V.n c)) := hall _ (stAt_mem hc)
  have hcw : σ (V.n c) = w := hall _ (constOf_sound hw)
  rw [hmul, hJ, B1.Tables.tb_loadHolds_mul_gen_pow, Nat.add_zero] at hld
  rw [B1.loadHolds_unique hld hst, hcw, powOf_sound hpw, Value.gen_pow_eq_ofK]

/-- **A range-checked table read's order holds** at an honest instance (`rcTab`): at the row its index names. -/
theorem rcTab_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.rcTab fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ rcTab_inst hr hI ht hf r' h
  | .lt a b, h => by
    obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
    simp only [CoreMode.rcTab, List.any_eq_true] at h
    obtain ⟨x, -, h⟩ := h
    split at h
    · rename_i T J N hT
      obtain ⟨t, ht', hJ, hk⟩ := tabOf_row hr hall hT
      have h1 := List.all_eq_true.mp h t (List.mem_range.mpr ht')
      split at h1
      · rename_i k hkk
        split at h1
        · rename_i u v hu hv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
          have hx := hk k hkk
          exact ⟨u, v, tabEv_rep hx hJ hu (by omega), tabEv_rep hx hJ hv h1.2, h1.1⟩
        · cases h1
      · cases h1
    · cases h
  | .nz _, h | .subR _ _, h | .subP _ _, h | .sub _ _, h => by simp [CoreMode.rcTab] at h

/-- **The residuals of a heap certificate of families hold** at an honest instance of its function, in
a frame holding its parameters whose entry runs' exponent cells are powers of `g`. -/
theorem resOk_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (h : resOk Cf = true) (hml : CoreMode.mlK Cf.fn = none)
    (hst : CoreMode.stK Cf.fn = none) (hgw : Cf.H.sig.gw = []) {fp : ℕ}
    (hpar : ∀ k < Cf.fn.params.length, CoreMode.Rd r.img fp (2 + k) = some (σ (V.n k)))
    (hx : CoreMode.ExpW r.img Cf.xc fp) : ResF Cf.H σ := fun x hx' ↦ by
  have := List.all_eq_true.mp h x hx'
  simp only [CoreMode.resFamG, Bool.or_eq_true, Bool.and_eq_true] at this
  rcases this with ((⟨(((((((((((hf' | hq) | hsp) | hvt) | hp) | hrc) | hcp) | hvs) | hly) | hvc) | hdg) | htb), -⟩ | hm) |
    hs) | he
  · exact resFam_inst hr hI ht hf hx hpar x hf'
  · exact resQ_inst hr hI ht hf hq
  · exact splitFam_inst hr hI ht hf hsp
  · exact vtStC_inst hr hI ht hf hvt
  · exact vtPerm_inst hr hI ht hf hp
  · exact rcPts_inst hr hI ht hf hrc
  · exact cpPerm_inst hr hI ht hf hcp
  · exact vsExp_inst hr hI ht hf x hvs
  · exact layQC_inst hr hI ht hf x hly
  · exact vtCp_inst hr hI ht hf x hvc
  · exact daGap_inst hr hI ht hf x hdg
  · exact rcTab_inst hr hI ht hf x htb
  · cases x <;> simp [CoreMode.mlSub, hml] at hm
  · cases x <;> simp [CoreMode.stSub, hst] at hs
  · simp [CoreMode.vtExp, hgw, CoreMode.vtGw] at he

/-- **The residuals of a heap certificate of families hold** at a valuation `σ'` agreeing below `GB` with an honest
instance's, given its ghost family's (`mlSub`): the others name no ghost (`CRes.holds_congr`). -/
theorem resOk_instG {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {Cf : CFun}
    (hf : coreProgram.find? f = some Cf.fn) (h : resOk Cf = true) {fp : ℕ}
    (hpar : ∀ k < Cf.fn.params.length, CoreMode.Rd r.img fp (2 + k) = some (σ (V.n k)))
    (hx : CoreMode.ExpW r.img Cf.xc fp) {σ' : Val}
    (hag : ∀ m < CoreMode.GB, σ' (V.n m) = σ (V.n m)) (hml : ∀ x, CoreMode.mlSub Cf.fn x = true → x.Holds σ')
    (hst : ∀ x, CoreMode.stSub Cf.fn x = true → x.Holds σ')
    (hvx : ∀ x, CoreMode.vtExp Cf.fn Cf.H.sig.gw x = true → x.Holds σ') :
    ResF Cf.H σ' := fun x hx' ↦ by
  have := List.all_eq_true.mp h x hx'
  simp only [CoreMode.resFamG, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at this
  rcases this with ((⟨(((((((((((hf' | hq) | hsp) | hvt) | hp) | hrc) | hcp) | hvs) | hly) | hvc) | hdg) | htb), hv⟩ | hm) |
    hs) | he
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (resFam_inst hr hI ht hf hx hpar x hf')
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (resQ_inst hr hI ht hf hq)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (splitFam_inst hr hI ht hf hsp)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (vtStC_inst hr hI ht hf hvt)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (vtPerm_inst hr hI ht hf hp)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (rcPts_inst hr hI ht hf hrc)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (cpPerm_inst hr hI ht hf hcp)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (vsExp_inst hr hI ht hf x hvs)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (layQC_inst hr hI ht hf x hly)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (vtCp_inst hr hI ht hf x hvc)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (daGap_inst hr hI ht hf x hdg)
  · exact (CoreMode.CRes.holds_congr fun m hm ↦ hag m (hv m hm)).mpr (rcTab_inst hr hI ht hf x htb)
  · exact hml x hm
  · exact hst x hs
  · exact hvx x he

end

end LeanVM.Guest.EndExec
