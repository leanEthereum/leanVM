/-
  LeanVM.Guest.EndExecCoreRes

  The core route's residual families (`CoreMode.resFam`) sound at the honest instances: each makes
  its residual true at the instance's valuation, from its path's events holding on the reference or
  from what its callers hand it.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResF
public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.EndExecCoreFn
public import LeanVM.Guest.EndExecCoreSplit
public import LeanVM.Guest.CoreMode.HeapCSound
public import LeanVM.Guest.CoreMode.Fam.ResExp

/-!
# The residual families, sound

`resLt_sound`: on a memory of at most `2^28` words, along a returning path whose events hold, the
path's families hold at the valuation: a range checked value's exponent below the check's bound
(`rcBound_sound`, its atoms on every returning path, `topAtoms_on_path`), a top-level selector's below
its arms (`topSels_sound`).

`exp_lt` (`exp`): a parameter `g^e`, `e < 2^62` (`ExpW`), the quotient of two addresses the path
dereferences, has `e < 2^28`.

`EndExecCoreSplit`'s `splitRes_sound`: a split `g`-power's residuals from its bits on the instance's path.

`resFam_inst`: at an honest instance (a `node` of the honest tree), in a frame holding its parameters
whose entry runs' exponent cells are powers, every residual of a family holds at its valuation; `resOk_inst`: every residual of a heap certificate whose residuals are of families
(`CoreMode.resOk`), which `HonF.res` asks of the core route's honest valuations.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw)

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
          rw [hx, ho1, hy, h0, zero_mul, add_zero, addressOfIndex, pow_zero, LeanVM.Parameters.ofK_one]
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

/-- **A product's bound from the top-level atoms holds** (`CoreMode.topProd`): `Π xᵢ^aᵢ = g^e`, `e ≤ Σ aᵢ·Mᵢ`. -/
theorem topProd_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {σ : Val}
    (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds Lm.read σ) : ∀ {bs : List (ℕ × ℕ)} {M : ℕ},
      CoreMode.topProd fn bs = some M → ∃ e ≤ M, CoreMode.prodW (vw σ) bs = ofK (addressOfIndex e)
  | [], M, h => by
    simp only [CoreMode.topProd, Option.some.injEq] at h
    subst h
    exact ⟨0, le_rfl, by simp [CoreMode.prodW, addressOfIndex]⟩
  | (x, a) :: bs, M, h => by
    simp only [CoreMode.topProd] at h
    cases hx : CoreMode.expM (Res.topAtoms fn.body) CoreMode.expFuel (V.n x) with
    | none => simp [hx] at h
    | some Mx =>
      cases hb : CoreMode.topProd fn bs with
      | none => simp [hx, hb] at h
      | some Mb =>
        simp only [hx, hb, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨e1, he1, h1⟩ := expM_sound hμ Lm hall _ _ hx
        obtain ⟨e2, he2, h2⟩ := topProd_sound hμ Lm hall hb
        refine ⟨a * e1 + e2, Nat.add_le_add (Nat.mul_le_mul_left a he1) he2, ?_⟩
        have hpw : ∀ (y : K) (n : ℕ), ofK y ^ n = ofK (y ^ n) := fun y n ↦ (map_pow (algebraMap K E) y n).symm
        simp only [CoreMode.prodW, vw]
        rw [h1, h2, hpw, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_mul, ← pow_add,
          mul_comm e1 a]

/-- **The `sel` and `rc` families of a value times a power of `g` hold** (`e(x·g^c) < n`, `x` a top-level selector
of `m` arms, `m + c ≤ n`, or range checked against `g^(N - 1)`, `N + c ≤ n`) at a valuation along a returning path
of the function whose events hold on a memory of at most `2^28` words. -/
theorem resSelM_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {xc : List ℕ} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ)
    {c : CoreMode.CCell} {n : ℕ} (h : resFam fn xc (.lt (.mono c) (.num n)) = true) :
    (CRes.lt (.mono c) (.num n)).Holds σ := by
  obtain ⟨cb, k⟩ := c
  simp only [resFam] at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  swap
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hn, hM⟩ := h
    cases hP : CoreMode.topProd fn cb with
    | none => simp [hP] at hM
    | some M =>
      simp only [hP, Option.any_some, decide_eq_true_eq] at hM
      have hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds Lm.read σ := fun a ha ↦ hh _ (topAtoms_on_path hw ha)
      obtain ⟨e, he, hp⟩ := topProd_sound hμ Lm hall hP
      refine ⟨e + k, n, ?_, CoreMode.rep_const hn, by omega⟩
      simp only [idxC, CoreMode.CCell.valW]
      rw [hp, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add]
      exact rep_of (by omega)
  split at h
  · rename_i x _
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
    simp only [CoreMode.CCell.valW, mul_assoc, ← LeanVM.Parameters.ofK_mul, addressOfIndex, ← pow_add]
    rw [show qo + S * j = ro + S * (j + k) by rw [Nat.mul_add]; omega]
  · cases h

/-- **A run of constant bounds inside one of the same bases, its stride a multiple** (`subRCm`) at any valuation. -/
theorem subRCm_holds {q r : CoreMode.CRun} (h : CoreMode.subRCm q r = true) (σ : Val) : (CRes.subR q r).Holds σ := by
  obtain ⟨⟨qb, qo⟩, S, ql, qh⟩ := q
  obtain ⟨⟨rb, ro⟩, S', rl, rh⟩ := r
  unfold CoreMode.subRCm at h
  split at h
  · rename_i l hh l' h' hql hqh hrl hrh
    simp only at hql hqh hrl hrh
    subst hql hqh hrl hrh
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hS0⟩, hSm⟩, hro⟩, hdv⟩, hl⟩, hh'⟩, hlc⟩, hhc⟩, hlc'⟩, hhc'⟩ := h
    have hb' := CoreMode.basesBeq_eq hb
    subst hb'
    intro x hx
    obtain ⟨ylo, yhi, j, hylo, hyhi, hlj, hjh, rfl⟩ := hx
    simp only [idxC] at hylo hyhi
    rw [CoreMode.rep_const hlc, Option.some.injEq] at hylo
    rw [CoreMode.rep_const hhc, Option.some.injEq] at hyhi
    subst hylo hyhi
    obtain ⟨k, hk⟩ : ∃ k, qo - ro = S' * k :=
      ⟨(qo - ro) / S', (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdv)).symm⟩
    obtain ⟨m, hm⟩ : ∃ m, S = S' * m := ⟨S / S', (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hSm)).symm⟩
    have hkS : (qo - ro) / S' = k := by rw [hk, Nat.mul_div_cancel_left _ hS0]
    have hmS : S / S' = m := by rw [hm, Nat.mul_div_cancel_left _ hS0]
    rw [hkS, hmS] at hl hh'
    have hmj : m * j ≤ m * (hh - 1) := Nat.mul_le_mul_left _ (by omega)
    have hml : m * l ≤ m * j := Nat.mul_le_mul_left _ hlj
    refine ⟨l', h', k + m * j, (by simp only [idxC]; exact CoreMode.rep_const hlc'),
      (by simp only [idxC]; exact CoreMode.rep_const hhc'), by omega, by omega, ?_⟩
    simp only [CoreMode.CCell.valW, mul_assoc, ← LeanVM.Parameters.ofK_mul, addressOfIndex, ← pow_add]
    rw [show qo + S * j = ro + S' * (k + m * j) by rw [hm, Nat.mul_add, ← Nat.mul_assoc]; omega]
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

/-- **An arm's exponent bound holds** (`CoreMode.armM`) where its condition is nonzero, along a returning path whose
events hold on a memory of at most `2^28` words (`nzAtoms_on_path`, `rcBound_sound`, `expM_sound`). -/
theorem armM_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) {k x M : ℕ}
    (hk : σ (V.n k) ≠ 0) (h : CoreMode.armM fn k x = some M) : ∃ e ≤ M, σ (V.n x) = ofK (addressOfIndex e) := by
  have hall : ∀ a ∈ CoreMode.nzAtoms (V.n k) fn.body, a.Holds Lm.read σ :=
    fun a ha ↦ hh _ (nzAtoms_on_path hk hw ha)
  unfold CoreMode.armM at h
  split at h
  · rename_i N hN
    cases h
    obtain ⟨e, he, hσ⟩ := rcBound_sound (by omega) Lm hall hN
    exact ⟨e, by omega, by rw [hσ, Value.gen_pow_eq_ofK]⟩
  · exact expM_sound hμ Lm hall _ _ h

/-- **An arm's bound of a product holds** (`CoreMode.armProd`): `Π xᵢ^aᵢ = g^e`, `e ≤ Σ aᵢ·Mᵢ`. -/
theorem armProd_sound {μ : ℕ} (hμ : μ ≤ 28) (Lm : MemoryImage μ) {fn : Fn} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds Lm.read σ) {k : ℕ}
    (hk : σ (V.n k) ≠ 0) : ∀ {bs : List (ℕ × ℕ)} {M : ℕ}, CoreMode.armProd fn k bs = some M →
      ∃ e ≤ M, CoreMode.prodW (vw σ) bs = ofK (addressOfIndex e)
  | [], M, h => by
    simp only [CoreMode.armProd, Option.some.injEq] at h
    subst h
    exact ⟨0, le_rfl, by simp [CoreMode.prodW, addressOfIndex]⟩
  | (x, a) :: bs, M, h => by
    simp only [CoreMode.armProd] at h
    cases hx : CoreMode.armM fn k x with
    | none => simp [hx] at h
    | some Mx =>
      cases hb : CoreMode.armProd fn k bs with
      | none => simp [hx, hb] at h
      | some Mb =>
        simp only [hx, hb, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨e1, he1, h1⟩ := armM_sound hμ Lm hw hh hk hx
        obtain ⟨e2, he2, h2⟩ := armProd_sound hμ Lm hw hh hk hb
        refine ⟨a * e1 + e2, Nat.add_le_add (Nat.mul_le_mul_left a he1) he2, ?_⟩
        have hpw : ∀ (y : K) (n : ℕ), ofK y ^ n = ofK (y ^ n) := fun y n ↦ (map_pow (algebraMap K E) y n).symm
        simp only [CoreMode.prodW, vw]
        rw [h1, h2, hpw, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_mul, ← pow_add,
          mul_comm e1 a]

/-- **The `neg` family holds** where its branch condition does (`CoreMode.negFam`): `negPair`'s, and the bounds the arm
the condition takes gives (`armM_sound`, `armProd_sound`). -/
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
      rcases Bool.or_eq_true_iff.mp hc with hc1 | hc2
      swap
      · cases hM : CoreMode.armProd fn k cb with
        | none => simp [hM] at hc2
        | some M =>
          simp only [hM, Option.any_some, decide_eq_true_eq] at hc2
          obtain ⟨e, he, hp⟩ := armProd_sound hμ Lm hw hh hk hM
          refine ⟨e + off, n, ?_, CoreMode.rep_const hn, by omega⟩
          simp only [idxC, CoreMode.CCell.valW]
          rw [hp, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add]
          exact rep_of (by omega)
      clear hc
      split at hc1
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
        rcases Bool.or_eq_true_iff.mp hc1 with hp | hp
        · exact hv a b hp rfl
        · exact hv b a hp (by ring)
      · cases hc1
    | _ => simp at hc
  | .lt (.val x) (.num n), h => by
    simp only [CoreMode.negFam, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨hn, cd, hcd, hc⟩ := h
    cases cd with
    | nonzero k =>
      have hk : σ (V.n k) ≠ 0 := hcs _ hcd
      cases hM : CoreMode.armM fn k x with
      | none => simp [hM] at hc
      | some M =>
        simp only [hM, Option.any_some, decide_eq_true_eq] at hc
        obtain ⟨e, he, hσ⟩ := armM_sound hμ Lm hw hh hk hM
        exact ltF_of_pow (e := e) hn (by omega) hσ
    | _ => simp at hc
  | .lt (.val _) (.val _), h | .lt (.val _) (.mono _), h | .lt (.num _) _, h | .lt (.mono _) (.val _), h
  | .lt (.mono _) (.mono _), h | .nz _, h | .sub _ _, h | .subR _ _, h | .subP _ _, h | .under _ _, h => by
    simp [CoreMode.negFam] at h

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
    simp only [resFam, Bool.or_eq_true] at h
    rcases h with h | h
    · exact subRC_holds h σ
    · exact subRCm_holds h σ
  | .lt (.val x) (.val p), h => by
    obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    exact resLtV_sound (logMemorySize_le_28 (e := r.exec) hr.size) r.img hw hh h
  | .lt (.num _) (.num _), h | .lt (.num _) (.val _), h | .lt (.mono _) (.val _), h
  | .lt (.mono _) (.mono _), h | .nz _, h | .sub _ _, h | .subP _ _, h => by simp [resFam] at h

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

/-- **A listed value** (`expVal`) is `g^e` below its bound, at an instance with the listed values' facts. -/
theorem expVal_sound (hV : ExpVQ I) (ht : I.t = .node f σ bufs kids) (hf : coreProgram.find? f = some fn) {x : V}
    {b : ℕ} (h : CoreMode.expVal fn x = some b) : ∃ e < b, σ x = gen ^ e := by
  unfold CoreMode.expVal at h
  obtain ⟨c, hc, hcx⟩ := List.exists_of_findSome?_eq_some h
  cases hb : (c.1 == fn.name && decide (x = V.n c.2.1))
  · rw [hb, Bool.cond_false] at hcx; cases hcx
  · rw [hb, Bool.cond_true, Option.some.injEq] at hcx
    subst hcx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
    obtain ⟨hn, rfl⟩ := hb
    exact hV f σ bufs kids ht c hc (by rw [hn]; exact find_name' hf)

/-- **A value of an exponent fact** (`expQ0`) is `g^e` below its bound. -/
theorem expQ0_sound (hV : ExpVQ I) (hE : ExpQ r I) (ht : I.t = .node f σ bufs kids)
    (hf : coreProgram.find? f = some fn)
    (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) {x : V} {b : ℕ} (h : CoreMode.expQ0 fn x = some b) :
    ∃ e < b, σ x = gen ^ e := by
  unfold CoreMode.expQ0 at h
  rcases h1 : CoreMode.expQ1 fn x with _ | b'
  · rw [h1] at h
    exact expVal_sound hV ht hf h
  · rw [h1] at h
    obtain rfl := Option.some.inj h
    exact expQ1_sound hE ht hf hall h1

/-- **A value of an exponent fact, a product of one and a constant power, or a copy of one** (`expQB`) is `g^e`
below its bound. -/
theorem expQB_sound (hV : ExpVQ I) (hE : ExpQ r I) (ht : I.t = .node f σ bufs kids)
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
          obtain ⟨e, he, hσa⟩ := expQ0_sound hV hE ht hf hall hb1
          obtain ⟨w0, hw0, hpw⟩ := Option.bind_eq_some_iff.mp hc
          have hσw : σ w = w0 := hall _ (constOf_sound hw0)
          have hmul : σ d = σ a * σ w := hall _ ha
          refine ⟨e + c, by omega, ?_⟩
          rw [hmul, hσa, hσw, powOf_sound hpw, ← Value.gen_pow_eq_ofK, pow_add]
    | copy d a =>
      simp only at haf
      split_ifs at haf with hd
      subst hd
      obtain ⟨e, he, hσa⟩ := expQ0_sound hV hE ht hf hall haf
      have hcp : σ d = σ a := hall _ ha
      exact ⟨e, he, by rw [hcp, hσa]⟩
    | _ => simp at haf
  · rw [h1] at h
    obtain rfl := Option.some.inj h
    exact expQ0_sound hV hE ht hf hall h1

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
theorem resQ_sound (hV : ExpVQ I) (hE : ExpQ r I) (hD : DimQ r I) (ht : I.t = .node f σ bufs kids)
    (hf : coreProgram.find? f = some fn) (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ) :
    ∀ x : CRes, CoreMode.resQ fn x = true → x.Holds σ
  | .lt (.val x) (.num n), h => by
    simp only [CoreMode.resQ, Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
    obtain ⟨hn, b, hb, hbn⟩ := h
    obtain ⟨e, he, hσ⟩ := expQB_sound hV hE ht hf hall hb
    exact ⟨e, n, rep_val_gen hσ (by omega), CoreMode.rep_const hn, by omega⟩
  | .lt (.mono c) (.num n), h => by
    obtain ⟨cb, k⟩ := c
    simp only [CoreMode.resQ] at h
    split at h
    · rename_i x _
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
      obtain ⟨hn, b, hb, hbn⟩ := h
      obtain ⟨e, he, hσ⟩ := expQB_sound hV hE ht hf hall hb
      exact ⟨e + k, n, rep_mono_gen hσ (by omega), CoreMode.rep_const hn, by omega⟩
    · cases h
  | .lt (.num j) (.mono c), h => by
    obtain ⟨cb, k⟩ := c
    simp only [CoreMode.resQ] at h
    split at h
    · rename_i x _
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true] at h
      obtain ⟨hjk, b, hb, hbk⟩ := h
      obtain ⟨e, he, hσ⟩ := expQB_sound hV hE ht hf hall hb
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
  | .under _ r', h => fun _ ↦ resQ_sound hV hE hD ht hf hall r' h
  | .lt (.val _) (.val _), h | .lt (.num _) (.num _), h | .lt (.num _) (.val _), h | .lt (.mono _) (.val _), h
  | .nz _, h | .sub _ _, h | .subR _ _, h | .subP _ _, h => by simp [CoreMode.resQ] at h

end

/-! ## A split `g`-power -/

/-- **A split's residuals hold** at an honest instance of a function with that split (`SplitW`, `splitRes_sound` on
its path). -/
theorem splitRes_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {sp : CoreMode.SplitC} (hs : SplitW fn sp) {x : CRes}
    (h : CoreMode.splitRes sp [] x = true) : x.Holds σ := by
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  obtain ⟨a, b, hv⟩ := hs r.img.read σ es vs hw hh
  exact splitRes_sound hv x [] (by simp) h

/-! ## A range-checked index -/

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
        addressOfIndex, pow_add, LeanVM.Parameters.ofK_mul]
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

/-- **An index's exponent at a table's row** (`tabEv`): each value's word `g^e` for the exponent `ev` gives. -/
theorem tabEv_rep {σ : Val} {ev : ℕ → Option ℕ}
    (hev : ∀ v e, ev v = some e → σ (V.n v) = Protocol.Verifier.gen ^ e) :
    ∀ {i : CIdx} {u : ℕ}, CoreMode.tabEv ev i = some u → u < capE → CoreMode.rep ((idxC i).valW (vw σ)) = some u
  | .num n, _, h, hu => by
    simp only [CoreMode.tabEv, Option.some.injEq] at h
    subst h
    exact CoreMode.rep_const hu
  | .val v, _, h, hu => by
    simp only [CoreMode.tabEv] at h
    rw [idxC, CoreMode.valW_baseC, show vw σ v = σ (V.n v) from rfl, hev v _ h, Value.gen_pow_eq_ofK]
    exact rep_of hu
  | .mono c, u, h, hu => by
    -- the product's word, `g^u`
    have key : ∀ (bs : List (ℕ × ℕ)) (o u : ℕ), bs.foldr (fun b acc ↦ acc.bind fun a ↦ (ev b.1).map (b.2 * · + a))
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
        have hw : vw σ b.1 ^ b.2 = ofK (addressOfIndex (b.2 * d)) := by
          rw [show vw σ b.1 = σ (V.n b.1) from rfl, hev _ _ hd, Value.gen_pow_eq_ofK, ← LeanVM.Parameters.ofK_pow,
            addressOfIndex, addressOfIndex, ← pow_mul, Nat.mul_comm]
        simp only [CoreMode.prodW]
        rw [mul_assoc, e1, hw, ← LeanVM.Parameters.ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
    simp only [CoreMode.tabEv] at h
    simp only [idxC, CoreMode.CCell.valW]
    rw [key c.bases c.off u h]
    exact rep_of hu

/-- **A table read at a row** at an honest path: its index `g^t`, then `x` the row's entry `g^(k_t)`. -/
theorem tabOf_at {r : Ref} {fn : Fn} {σ : Val} (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ)
    {x T J N t : ℕ} (h : CoreMode.tabOf fn x = some (T, J, N)) (hJ : σ (V.n J) = Protocol.Verifier.gen ^ t) :
    ∀ k, CoreMode.tabK fn T t = some k → σ (V.n x) = Protocol.Verifier.gen ^ k := by
  unfold CoreMode.tabOf at h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨T', J'⟩, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨N', -, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hld : LoadHolds r.img.read (σ (V.n p)) 0 (σ (V.n x)) := hall _ (ldAt_mem hp)
  have hmul : σ (V.n p) = σ (V.n T') * σ (V.n J') := hall _ (mulAt_mem hm)
  intro k hk
  unfold CoreMode.tabK at hk
  obtain ⟨c, hc, hk⟩ := Option.bind_eq_some_iff.mp hk
  obtain ⟨w, hw, hpw⟩ := Option.bind_eq_some_iff.mp hk
  have hst : LoadHolds r.img.read (σ (V.n T')) t (σ (V.n c)) := hall _ (stAt_mem hc)
  have hcw : σ (V.n c) = w := hall _ (constOf_sound hw)
  rw [hmul, hJ, LeanVM.Guest.B1.loadHolds_mul_gen_pow, Nat.add_zero] at hld
  rw [B1.loadHolds_unique hld hst, hcw, powOf1_sound hpw, Value.gen_pow_eq_ofK]

/-- **A table read's row** at an honest path: its index `g^t`, `t < N`. -/
theorem tabOf_row {r : Ref} (hr : r.Ok) {fn : Fn} {σ : Val} (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ)
    {x T J N : ℕ} (h : CoreMode.tabOf fn x = some (T, J, N)) : ∃ t < N, σ (V.n J) = Protocol.Verifier.gen ^ t := by
  unfold CoreMode.tabOf at h
  obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨T', J'⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨N', hN, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  exact rcBound_sound (by omega) r.img hall hN

/-- **The exponents at a table's row** (`tabRowEv`) are the words' at an honest path whose index is `g^t`. -/
theorem tabRowEv_sound {r : Ref} {fn : Fn} {σ : Val} (hall : ∀ a ∈ Res.topAtoms fn.body, a.Holds r.img.read σ)
    {J t : ℕ} (hJ : σ (V.n J) = Protocol.Verifier.gen ^ t) :
    ∀ v e, CoreMode.tabRowEv fn J t v = some e → σ (V.n v) = Protocol.Verifier.gen ^ e := by
  intro v e h
  unfold CoreMode.tabRowEv at h
  cases hb : Nat.beq v J with
  | true =>
    rw [hb, Bool.cond_true, Option.some.injEq] at h
    rw [Nat.eq_of_beq_eq_true hb, hJ, h]
  | false =>
    rw [hb, Bool.cond_false] at h
    split at h
    · rename_i T J' N' hT
      cases hb' : Nat.beq J' J with
      | true =>
        rw [hb', Bool.cond_true] at h
        exact tabOf_at hall hT (by rw [Nat.eq_of_beq_eq_true hb', hJ]) e h
      | false => rw [hb', Bool.cond_false] at h; cases h
    · cases h

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
      obtain ⟨t, ht', hJ⟩ := tabOf_row hr hall hT
      have h1 := List.all_eq_true.mp h t (List.mem_range.mpr ht')
      have hev := tabRowEv_sound hall hJ
      split at h1
      · rename_i u v hu hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        exact ⟨u, v, tabEv_rep hev hu (by omega), tabEv_rep hev hv h1.2, h1.1⟩
      · cases h1
    · cases h
  | .nz _, h | .subR _ _, h | .subP _ _, h | .sub _ _, h => by simp [CoreMode.rcTab] at h


end

end LeanVM.Guest.EndExec
