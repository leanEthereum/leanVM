/-
  LeanVM.Guest.B1.VerifySub.C.Sizes

  `verify_sub`'s sizes (G:3364-3383), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Reads
public import LeanVM.Guest.Hints

/-!
# The sizes, honestly

`vsSizesT_complete`: with the rate exponent `lir ∈ [1, 4]` and the memory's log `logMem ∈ [16, 32]`
as the words read (`112`, `29`), `g_power_of_word`'s returns `g^lir`, `g^logMem` (the calls in
`C`), the memory defined below `2^κ` (`6 ≤ κ`), and `dims_g`, `kappa_base` holding their honest
words (`g^logMem`, then the heights as `count`; `1`, `g^logMem`, the heights), `vsSizesT` holds:
`kb` in the frame (`140 .. 147`: `1`, a copy of `g^logMem`, the heights read from `dims_g`) and
stored into `kappa_base`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

theorem count_eq_gen {n : ℕ} (h : n < 2 ^ 64) : Hints.count n = gen ^ n := by
  rw [Hints.count, gpowE, gpowK_eq (by unfold u128Bound; omega), gen_pow_eq_ofK]

theorem gen_pow_div {a b : ℕ} (h : b ≤ a) : gen ^ a * (gen ^ b)⁻¹ = gen ^ (a - b) := by
  rw [← pow_sub₀ _ gen_ne_zero h]

theorem gen_defined {κ : ℕ} {rd : Reader} (hlow : LowDef κ rd) {a : ℕ} (ha : a < 2 ^ κ) :
    (rd ((gen ^ a).limb 0 * Parameters.addressOfIndex 0)).isSome := by
  rw [gen_pow_eq_ofK, show Parameters.addressOfIndex 0 = 1 from pow_zero _, mul_one]
  simp only [limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte]
  exact hlow a ha

/-- A range check of `g^a` against `g^c`, with `g^b = g^c / g^a` (`b` the complement), honestly. -/
theorem rc_holds {κ : ℕ} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} (hlow : LowDef κ rd)
    {x y t1 t2 k : V} (hk : k.idx < y.idx) {a b : ℕ} (ha : a < 2 ^ κ) (hb : b < 2 ^ κ)
    (hx : σ x = gen ^ a) (hy : σ y = gen ^ b) (hg : Good rd S w σ (.rangeCheck x y t1 t2 k)) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd σ := by
  have hs : Side rd S σ (.rangeCheck x y t1 t2 k) := by
    simp only [Side]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hk), hx, hy]
    exact ⟨gen_pow_isInK a, gen_defined hlow ha, gen_pow_isInK b, gen_defined hlow hb,
      pow_ne_zero _ gen_ne_zero⟩
  exact holds_of_good hg hs

theorem good_mul_old {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : V}
    (hd : ¬ (x.idx < d.idx ∧ y.idx < d.idx)) (hg : Good rd S w σ (.mul d x y)) :
    σ x = σ d * (σ y)⁻¹ := by
  simp only [Good] at hg
  rwa [ite_eq_right_of_eq_false _ _ (eq_false hd)] at hg

theorem good_rc_y {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {x y t1 t2 k : V}
    (hk : k.idx < y.idx) (hg : Good rd S w σ (.rangeCheck x y t1 t2 k)) :
    σ y = σ k * (σ x)⁻¹ := by
  simp only [Good] at hg
  rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hg
  exact hg.2.2

/-- A read of a word the memory holds, on an evaluated valuation. -/
theorem good_read {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {off : ℕ} {v : E}
    (hg : Good rd S w σ (.load d p off)) (hS : Atom.load d p off ∉ S)
    (hm : LoadHolds rd (σ p) off v) : σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  simp only [Good] at hg
  have e : σ d = v := by rw [hg.resolve_left hS, rdAt, hm.2]; rfl
  exact ⟨e, by show LoadHolds rd _ _ _; rw [e]; exact hm⟩

theorem vsSizesT_noNe : vsSizesT.all noNeB = true := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsSizesT_good (hl : args.length = 6) :
    ∀ s ∈ vsSizesT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 89) (blk := vsSizesT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsSizesT_noNe s hs)] at h

/-- **The sizes, honestly.** -/
theorem vsSizesT_complete (hl : args.length = 6) {κ : ℕ} (hκ6 : 6 ≤ κ) (hlow : LowDef κ rd)
    {lir logMem : ℕ} (hl1 : 1 ≤ lir) (hl4 : lir ≤ 4) (hlm1 : 1 ≤ logMem) (hm32 : logMem ≤ 32)
    (e112 : vsσ rd w args (.n 110) = eOfNat lir) (e29 : vsσ rd w args (.n 27) = eOfNat logMem)
    (e122 : vsσ rd w args (.n 120) = gen ^ lir) (e130 : vsσ rd w args (.n 128) = gen ^ logMem)
    {hs : List ℕ} (hsl : hs.length = 6)
    (hdims : ReadsAt rd (vsσ rd w args (.n 127)) (gen ^ logMem :: hs.map Hints.count))
    (hkb : ReadsAt rd (vsσ rd w args (.n 139)) (1 :: gen ^ logMem :: hs.map Hints.count))
    {C : CallRel} (hC1 : C "g_power_of_word" [eOfNat lir] [gen ^ lir])
    (hC2 : C "g_power_of_word" [eOfNat logMem] [gen ^ logMem])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    (∀ s < 8, vsσ rd w args (.n (140 + s)) = (1 :: gen ^ logMem :: hs.map Hints.count).getD s 0) ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsSizesT next kret := by
  have hG := vsSizesT_good (rd := rd) (w := w) hl
  have m1 : ∀ s ∈ [vsCall "g_power_of_word" [110] [120], vsConst 121 (word 2 0 0), vsMul 120 122 121,
      vsConst 123 (word 8 0 0), vsRange 122 124 125 126 123, vsAlloc 127 7,
      vsCall "g_power_of_word" [27] [128], vsConst 129 (word (2 ^ 32) 0 0),
      vsRange 128 130 131 132 129, vsConst 133 (word (2 ^ 32) 0 0), vsConst 134 (word 2 0 0),
      vsMul 128 135 134, vsRange 135 136 137 138 133, vsLd 128 127 0,
      .atom (.hint (.witness "table_logs" (.heap (.n 127) 1 6))), vsAlloc 139 8,
      vsConst 140 (word 1 0 0), .atom (.copy (.n 141) (.n 128))], s ∈ vsSizesT :=
    fun s hs ↦ by rw [vsSizesT]; exact List.mem_append_left _ (List.mem_append_left _ hs)
  have m2 : ∀ t < 6, vsLd (142 + t) 127 (1 + t) ∈ vsSizesT := fun t ht ↦ by
    rw [vsSizesT]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩))
  generalize hσ : vsσ rd w args = σ at *
  have g : ∀ a, Stmt.atom a ∈ vsSizesT → Good rd vsSL w σ a := fun a h ↦ hG _ h
  have mm := fun s (h : s ∈ _) ↦ m1 s h
  -- the constants
  have v121 : σ (.n 121) = gen := by
    have := g _ (mm (vsConst 121 (word 2 0 0)) (by simp)); simp only [Good] at this
    rw [this, word_gen]
  have v123 : σ (.n 123) = gen ^ 3 := by
    have := g _ (mm (vsConst 123 (word 8 0 0)) (by simp)); simp only [Good] at this
    rw [this, show (8 : ℕ) = 2 ^ 3 from rfl, word_two_pow (by norm_num)]
  have v129 : σ (.n 129) = gen ^ 32 := by
    have := g _ (mm (vsConst 129 (word (2 ^ 32) 0 0)) (by simp)); simp only [Good] at this
    rw [this, word_two_pow (by norm_num)]
  have v133 : σ (.n 133) = gen ^ 32 := by
    have := g _ (mm (vsConst 133 (word (2 ^ 32) 0 0)) (by simp)); simp only [Good] at this
    rw [this, word_two_pow (by norm_num)]
  have v134 : σ (.n 134) = gen ^ 1 := by
    have := g _ (mm (vsConst 134 (word 2 0 0)) (by simp)); simp only [Good] at this
    rw [this, pow_one, word_gen]
  have v140 : σ (.n 140) = 1 := by
    have := g _ (mm (vsConst 140 (word 1 0 0)) (by simp)); simp only [Good] at this
    rw [this, word_one]
  have v141 : σ (.n 141) = gen ^ logMem := by
    have := g _ (mm (.atom (.copy (.n 141) (.n 128))) (by simp)); simp only [Good] at this
    rw [this, e130]
  have hκ : 64 ≤ 2 ^ κ := by
    calc 64 = 2 ^ 6 := rfl
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ6
  -- the rate
  have v122 : σ (.n 122) = gen ^ (lir - 1) := by
    rw [good_mul_old (by decide) (g _ (mm (vsMul 120 122 121) (by simp))), e122, v121]
    have : gen ^ lir = gen ^ (lir - 1) * gen := by rw [← pow_succ]; congr 1; omega
    rw [this, mul_assoc, mul_inv_cancel₀ gen_ne_zero, mul_one]
  have v124 : σ (.n 124) = gen ^ (3 - (lir - 1)) := by
    rw [good_rc_y (by decide) (g _ (mm (vsRange 122 124 125 126 123) (by simp))), v123, v122,
      gen_pow_div (by omega)]
  have r1 := rc_holds hlow (by decide) (by omega) (by omega) v122 v124
    (g _ (mm (vsRange 122 124 125 126 123) (by simp)))
  -- the memory's log
  have v130 : σ (.n 130) = gen ^ (32 - logMem) := by
    rw [good_rc_y (by decide) (g _ (mm (vsRange 128 130 131 132 129) (by simp))), v129, e130,
      gen_pow_div hm32]
  have r2 := rc_holds hlow (by decide) (by omega) (by omega) e130 v130
    (g _ (mm (vsRange 128 130 131 132 129) (by simp)))
  have v135 : σ (.n 135) = gen ^ (logMem - 1) := by
    rw [good_mul_old (by decide) (g _ (mm (vsMul 128 135 134) (by simp))), e130, v134,
      gen_pow_div hlm1]
  have v136 : σ (.n 136) = gen ^ (32 - (logMem - 1)) := by
    rw [good_rc_y (by decide) (g _ (mm (vsRange 135 136 137 138 133) (by simp))), v133, v135,
      gen_pow_div (by omega)]
  have r3 := rc_holds hlow (by decide) (by omega) (by omega) v135 v136
    (g _ (mm (vsRange 135 136 137 138 133) (by simp)))
  -- the products
  have p120 : σ (.n 120) = σ (.n 122) * σ (.n 121) := by
    rw [e122, v122, v121, ← pow_succ]; congr 1; omega
  have p128 : σ (.n 128) = σ (.n 135) * σ (.n 134) := by
    rw [e130, v135, v134, ← pow_add]; congr 1; omega
  -- the reads and the stores
  have hd : ∀ k (hk : k < 7), LoadHolds rd (σ (.n 127)) k
      ((gen ^ logMem :: hs.map Hints.count)[k]'(by simp [hsl]; omega)) := fun k hk ↦ hdims k _
  have hb : ∀ k (hk : k < 8), LoadHolds rd (σ (.n 139)) k
      ((1 :: gen ^ logMem :: hs.map Hints.count)[k]'(by simp [hsl]; omega)) := fun k hk ↦ hkb k _
  have s0 : LoadHolds rd (σ (.n 127)) 0 (σ (.n 128)) := by rw [e130]; exact hd 0 (by norm_num)
  have notS : ∀ t < 6, Atom.load (.n (142 + t)) (.n 127) (1 + t) ∉ vsSL := by decide +kernel
  have hv : ∀ t (ht : t < 6), σ (.n (142 + t)) = Hints.count (hs[t]'(by omega)) := by
    intro t ht
    have hgl := g _ (m2 t ht)
    simp only [Good] at hgl
    rw [hgl.resolve_left (notS t ht), rdAt, (hd (1 + t) (by omega)).2]
    simp [List.getElem_cons, show 1 + t - 1 = t by omega]
  have lt : ∀ t (ht : t < 6), LoadHolds rd (σ (.n 127)) (1 + t) (σ (.n (142 + t))) := by
    intro t ht
    rw [hv t ht]
    have := hd (1 + t) (by omega)
    simpa [List.getElem_cons, show 1 + t ≠ 0 by omega, show 1 + t - 1 = t by omega] using this
  have st : ∀ t (ht : t < 6), LoadHolds rd (σ (.n 139)) (2 + t) (σ (.n (142 + t))) := by
    intro t ht
    rw [hv t ht]
    have := hb (2 + t) (by omega)
    simpa [List.getElem_cons, show 2 + t ≠ 0 by omega, show 2 + t - 1 = 1 + t by omega,
      show 1 + t ≠ 0 by omega, show 1 + t - 1 = t by omega] using this
  have st0 : LoadHolds rd (σ (.n 139)) 0 (σ (.n 140)) := by rw [v140]; exact hb 0 (by norm_num)
  have st1 : LoadHolds rd (σ (.n 139)) 1 (σ (.n 141)) := by rw [v141]; exact hb 1 (by norm_num)
  have kc : ∀ (d : ℕ) (c : E), vsConst d c ∈ vsSizesT → (Atom.const (.n d) c).Holds rd σ :=
    fun d c h ↦ g _ h
  refine ⟨fun s hs8 ↦ ?_, ?_⟩
  · rcases (show s = 0 ∨ s = 1 ∨ 2 ≤ s by omega) with rfl | rfl | h2
    · simpa using v140
    · simpa using v141
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 + t := ⟨s - 2, by omega⟩
      rw [show 140 + (2 + t) = 142 + t by omega, hv t (by omega), show 2 + t = t + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_eq_getElem _ _ (by simp [hsl]; omega), List.getElem_map]
  rw [vsSizesT, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl,
    show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, vsCall, vsConst, vsMul, vsRange, vsAlloc, vsLd]
  rw [e112, e122, e29, e130]
  exact ⟨hC1, kc 121 _ (mm _ (by simp)), p120, kc 123 _ (mm _ (by simp)), r1, trivial, hC2,
    kc 129 _ (mm _ (by simp)), r2, kc 133 _ (mm _ (by simp)), kc 134 _ (mm _ (by simp)), p128, r3,
    s0, trivial, trivial, kc 140 _ (mm _ (by simp)), show σ (.n 141) = σ (.n 128) by rw [v141, e130],
    lt 0 (by norm_num), lt 1 (by norm_num), lt 2 (by norm_num), lt 3 (by norm_num),
    lt 4 (by norm_num), lt 5 (by norm_num), st0, st1,
    st 0 (by norm_num), st 1 (by norm_num), st 2 (by norm_num), st 3 (by norm_num),
    st 4 (by norm_num), st 5 (by norm_num), hn⟩

end
end LeanVM.Guest.B1.VerifySub
