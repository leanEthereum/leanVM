/-
  LeanVM.Guest.B1.Terminal.Support

  What `check_opening_terminal`'s head computes, from its callees' meanings: the prefix chains,
  the public input's chain, the column selectors.
-/

module

public import LeanVM.Guest.B1.Terminal.Claims
public import LeanVM.Guest.B1.Terminal.PiChain
public import LeanVM.Guest.B1.Terminal.Body

/-!
# The head's values

* `chain_value`: `eq_prefix_chain(chain, 1, a, point1, g^|A|)` over the words `A` at `a` makes
  `chain[m]` the weight of `A`'s first `m` words against `x`'s (`chain_value_seed`: seeded with
  `s`, `s` times it);
* `sel_value`: committed column `c`'s selector is `selProd` of its offset's bits above its size,
  the offset a multiple of `2^κ`;
* the sizes of `columnKappas` (`kappas_qkeccak`, `kappas_lane`, `kappas_memory`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

variable {rd : Reader}

theorem readsAt_unique {p : E} {xs ys : List E} (h1 : ReadsAt rd p xs) (h2 : ReadsAt rd p ys)
    (hl : xs.length = ys.length) : xs = ys :=
  List.ext_getElem hl fun k hk _ ↦ loadHolds_unique (h1 k hk) (h2 k (by omega))

theorem readsAt_take {p : E} {xs : List E} (h : ReadsAt rd p xs) (n : ℕ) :
    ReadsAt rd p (xs.take n) := fun k hk ↦ by
  simp only [List.getElem_take]; exact h k (by simp at hk; omega)

theorem readsAt_getD {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem x1_getD {x : List E} (hx : x.length ≤ termPointCap) {i : ℕ} (hi : i < termPointCap) :
    ((padPoint x).map (1 + ·)).getD i 0 = 1 + x.getD i 0 := by
  rw [getD_map_one (by rw [padPoint_length hx]; exact hi), padPoint_getD]

theorem prefixProd_seed (s : E) (as bs : List E) (j : ℕ) :
    prefixProd s as bs j = s * prefixProd 1 as bs j := by
  rw [prefixProd, prefixProd, foldl_mul_eq, foldl_mul_eq, one_mul]

/-- **A prefix chain's values**, seeded with `s`. -/
theorem chain_value_seed {chain s a b1 cg : E} {A x : List E}
    (h : MeaningEqPrefixChain rd [chain, s, a, b1, cg] []) (hcg : cg = gen ^ A.length)
    (hA : A.length ≤ 40) (hAr : ReadsAt rd a A) (hx : x.length ≤ termPointCap)
    (hx1 : ReadsAt rd b1 ((padPoint x).map (1 + ·))) :
    ∀ m ≤ A.length, m ≤ x.length → valOf rd chain m = s * eqEval (A.take m) (x.take m) := by
  obtain ⟨-, -, n, hn, hcg', as, bs, hal, hbl, har, hbr, hch⟩ := h
  have hnA : n = A.length := gen_pow_inj_le (by omega) (by omega) (hcg'.symm.trans hcg)
  subst hnA
  have hasA : as = A := readsAt_unique har hAr hal
  subst hasA
  intro m hm hmx
  rw [valOf_eq (hch m hm), prefixProd_seed]
  refine congrArg (s * ·) (prefixProd_eq hm (by omega) hmx fun i hi ↦ ?_)
  have hpl : ((padPoint x).map (1 + ·)).length = termPointCap := by simp [padPoint_length hx]
  have hi40 : i < ((padPoint x).map (1 + ·)).length := by
    rw [hpl]; simp only [termPointCap] at hx ⊢; omega
  have e := loadHolds_unique (readsAt_getD hbr (by omega)) (readsAt_getD hx1 hi40)
  rw [e, x1_getD hx (by rw [hpl] at hi40; exact hi40)]

/-- **A prefix chain's values.** -/
theorem chain_value {chain a b1 cg : E} {A x : List E}
    (h : MeaningEqPrefixChain rd [chain, 1, a, b1, cg] []) (hcg : cg = gen ^ A.length)
    (hA : A.length ≤ 40) (hAr : ReadsAt rd a A) (hx : x.length ≤ termPointCap)
    (hx1 : ReadsAt rd b1 ((padPoint x).map (1 + ·))) :
    ∀ m ≤ A.length, m ≤ x.length → valOf rd chain m = eqEval (A.take m) (x.take m) := by
  obtain ⟨-, -, n, hn, hcg', as, bs, hal, hbl, har, hbr, hch⟩ := h
  have hnA : n = A.length := gen_pow_inj_le (by omega) (by omega) (hcg'.symm.trans hcg)
  subst hnA
  have hasA : as = A := readsAt_unique har hAr hal
  subst hasA
  intro m hm hmx
  rw [valOf_eq (hch m hm)]
  refine prefixProd_eq hm (by omega) hmx fun i hi ↦ ?_
  have hpl : ((padPoint x).map (1 + ·)).length = termPointCap := by simp [padPoint_length hx]
  have hi40 : i < ((padPoint x).map (1 + ·)).length := by
    rw [hpl]; simp only [termPointCap] at hx ⊢; omega
  have e := loadHolds_unique (readsAt_getD hbr (by omega)) (readsAt_getD hx1 hi40)
  rw [e, x1_getD hx (by rw [hpl] at hi40; exact hi40)]

/-! ## The sizes -/

theorem kappas_getD_eq {lm lb h0 h1 h2 h3 h4 h5 : ℕ} {g : ℕ} :
    (columnKappas lm lb [h0, h1, h2, h3, h4, h5]).getD g 0 =
      ([lm, lm, lm, lb, h5 + 6] ++ List.replicate 13 h0 ++ List.replicate 13 h1 ++
        List.replicate 7 h2 ++ List.replicate 14 h3 ++ List.replicate 14 h4 ++
        List.replicate 92 h5).getD g 0 := by
  rw [Tables.columnKappas_eq]

theorem six_of_length {hs : List ℕ} (hl : hs.length = 6) :
    ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ => exact ⟨h0, h1, h2, h3, h4, h5, rfl⟩

/-- `KECCAK`'s columns (global `66 .. 157`) have its log-height. -/
theorem kappas_keccak {lm lb : ℕ} {hs : List ℕ} (hl : hs.length = 6) {g : ℕ} (h1 : 66 ≤ g)
    (h2 : g < 158) : (columnKappas lm lb hs).getD g 0 = hs.getD 5 0 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ := six_of_length hl
  rw [kappas_getD_eq, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_append, List.length_cons,
      List.length_nil, List.length_replicate]; omega), List.getElem?_replicate]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  split
  · rfl
  · omega

theorem kappas_small {lm lb : ℕ} {hs : List ℕ} (hl : hs.length = 6) :
    (columnKappas lm lb hs).take 5 = [lm, lm, lm, lb, hs.getD 5 0 + 6] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ := six_of_length hl
  rw [Tables.columnKappas_eq]
  rfl

theorem committedKappas_small {kappas : List ℕ} (hl : kappas.length = 158) {c : ℕ} (hc : c < 66) :
    (Tables.committedKappas kappas).getD c 0 = kappas.getD c 0 := by
  have hlen : c < (Tables.committedCols 158).length := by
    rw [Tables.committedCols_158_length]; show c < 94; omega
  rw [Tables.committedKappas, hl, List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hlen, committedCols_getD (show c < 94 by omega)]
  simp [colOfCommitted, hc]

theorem stackOffsets_length (sizes : List ℕ) : (stackOffsets sizes).1.length = sizes.length := by
  unfold stackOffsets
  simp only
  have : ∀ (order : List ℕ) (acc : List ℕ × ℕ),
      (order.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ sizes.getD i 0))
        acc).1.length = acc.1.length := by
    intro order
    induction order with
    | nil => intro acc; rfl
    | cons k order ih => intro acc; rw [List.foldl_cons, ih, List.length_set]
  rw [this]; simp

/-! ## The selectors -/

/-- **Committed column `c`'s selector**, its `g^κ` at `kb[src]·g^adj`, its offset `g^o` with `o` a
multiple of `2^κ` (`stackOffsets` lays the blocks out largest first). -/
theorem sel_value (hcs : Tables.column_selector_Spec) (hst : Tables.selector_tables_Spec)
    {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
    {σ : Val} {c κ o L : ℕ} {x : List E} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel Lm.read) Lm.read σ (selBlockT c) True kret)
    (hstc : coreProgram.Rel Lm.read "selector_tables" [σ (.n 13), σ (.n 14)] [σ (.n 43)])
    (hgt : Tables.GTabsAt Lm.read (σ (.n 0) * gen ^ 34))
    (hkap : σ (.n (kbV (Tables.colKappaSrc c))) * gen ^ Tables.colKappaAdj c = gen ^ κ)
    (hoff : LoadHolds Lm.read (σ (.n 10)) c (gen ^ o)) (hdvd : 2 ^ κ ∣ o)
    (hκ : κ ≤ L) (hL : L ≤ 28) (ho : o < 2 ^ L) (hx : x.length = L)
    (hpt : ReadsAt Lm.read (σ (.n 13)) (padPoint x))
    (hpt1 : ReadsAt Lm.read (σ (.n 14)) ((padPoint x).map (1 + ·))) :
    σ (.n (selV c)) = selProd o κ (L - κ) x := by
  have hadj : Tables.colKappaAdj c < 64 := by unfold Tables.colKappaAdj; split_ifs <;> omega
  simp only [selBlockT, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨loff, h⟩ := h
  obtain ⟨hkv, h⟩ := kapT_sound (src := Tables.colKappaSrc c) (r := selStart c + 1) (rest := [])
    hadj (by rw [List.append_nil]; exact h)
  simp only [Stmt.HoldsList, List.map_cons, List.map_nil] at h
  obtain ⟨c34, m35, ⟨j, hj, hkj, hcall⟩, -⟩ := h
  have hjl : j < 29 := by simpa [colSelNames] using hj
  have hkv' : σ (.n (selKap c).2.1) = gen ^ κ := hkv.trans hkap
  rw [hkv', ← gen_pow_eq_ofK] at hkj
  have hjκ : κ = j := gen_pow_inj_le (by omega) (by omega) hkj
  subst hjκ
  simp only [colSelNames, List.getElem_map, List.getElem_range] at hcall
  have hsg : σ (.n ((selKap c).2.2 + 1)) = σ (.n 0) * gen ^ 34 := by
    rw [m35, c34, show (17179869184 : ℕ) = 2 ^ 34 from rfl, word_two_pow (by decide)]
  rw [hsg] at hcall
  have hout := hcs κ hjl μ hμ Lm _ _ hcall
  have hxl : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  have hpl : (padPoint x).length = termPointCap := padPoint_length hxl
  have htabs := hst Lm.read _ _ hstc ((padPoint x).take 28) (((padPoint x).map (1 + ·)).take 28)
    (by simp [hpl, termPointCap]) (by simp [hpl, termPointCap]) (readsAt_take hpt 28)
    (readsAt_take hpt1 28)
  obtain ⟨o', ho', -, hoff', hsel⟩ := hout hgt
  have e := loadHolds_unique loff hoff
  rw [e] at hoff'
  have ho2 : o < 2 ^ 28 := lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide) hL)
  have hoo : o = o' :=
    gen_pow_inj (lt_trans ho2 (by norm_num)) (lt_trans ho' (by norm_num)) hoff'
  subst hoo
  rw [hsel hdvd _ _ (by simp [hpl, termPointCap]) (by simp [hpl, termPointCap]) htabs,
    bitsEq_sel o (by omega) hxl, selProd_pad hx ho hκ (by omega)]

end
end LeanVM.Guest.B1.VerifySub
