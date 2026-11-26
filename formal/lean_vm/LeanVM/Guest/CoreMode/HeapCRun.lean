/-
  LeanVM.Guest.CoreMode.HeapCRun

  The heap check's soundness, its parts: words over slots, exponents, runs and facts, monomials at a site.
-/

module

public import LeanVM.Guest.CoreMode.HeapC
public import LeanVM.Guest.CoreMode.HeapSound

/-!
# Words, exponents, runs and monomials

The first part of `heapOkC_sound` (`HeapCSound.lean`): monomials' words over slots (`valW`), exponents (`rep`), a witness of a cell or a run written from a run in scope and the facts (`ptRun_ok`, `runRun_ok`), and a signature at a site as the cells and runs at the slots' words.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq natSeq_eq)
open LeanVM.Guest.Check (getF setF getF_eq setF_eq)

@[expose] public section

/-! ## Words -/

section Words

variable {w w' : ℕ → E}

theorem prodB_eq (σ : Val) : ∀ l, prodB σ l = prodW (vw σ) l
  | [] => rfl
  | (b, e) :: l => by rw [prodB, prodW, prodB_eq σ l]; rfl

theorem val_eq (σ : Val) (c : CCell) : c.val σ = c.valW (vw σ) := by
  rw [CCell.val, CCell.valW, prodB_eq]

theorem addr_eq (σ : Val) (c : CCell) : c.addr σ = c.addrW (vw σ) := by
  rw [CCell.addr, CCell.addrW, val_eq]

/-- A valuation whose values `V.n k` have the words `w k`. -/
def lift (w : ℕ → E) : Val := fun v ↦ w v.idx

theorem vw_lift (w : ℕ → E) : vw (lift w) = w := funext fun _ ↦ rfl

theorem ofK_pow' (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

theorem valW_mul (a b : CCell) : (a.mul b).valW w = a.valW w * b.valW w := by
  have := val_mul (lift w) a b
  rwa [val_eq, val_eq, val_eq, vw_lift] at this

theorem prodW_pow (e : ℕ) : ∀ l : List (ℕ × ℕ), prodW w (l.map fun b ↦ (b.1, b.2 * e)) = prodW w l ^ e
  | [] => by simp [prodW]
  | (b, x) :: l => by
    simp only [List.map_cons, prodW, prodW_pow e l, mul_pow, pow_mul]

theorem valW_pow (c : CCell) (e : ℕ) : (c.pow e).valW w = c.valW w ^ e := by
  rw [CCell.pow, CCell.valW, CCell.valW, prodW_pow, mul_pow, ← ofK_pow', addressOfIndex, addressOfIndex,
    ← pow_mul]

theorem valW_shift (c : CCell) (o : ℕ) : (c.shift o).valW w = c.valW w * ofK (addressOfIndex o) := by
  simp only [CCell.shift, CCell.valW, addressOfIndex, pow_add, ofK_mul', mul_assoc]

theorem valW_baseC (k : ℕ) : (baseC k).valW w = w k := by
  have := val_baseC (lift w) k
  rwa [val_eq, vw_lift] at this

theorem valW_const (n : ℕ) : (⟨[], n⟩ : CCell).valW w = ofK (addressOfIndex n) := by
  simp [CCell.valW, prodW]

theorem valW_nil {c : CCell} (h : c.bases.isEmpty = true) : c.valW w = ofK (addressOfIndex c.off) := by
  obtain ⟨bs, o⟩ := c
  cases bs with
  | nil => exact valW_const o
  | cons _ _ => simp at h

theorem prodW_congr {c : List (ℕ × ℕ)} (h : ∀ b ∈ c, w b.1 = w' b.1) : prodW w c = prodW w' c := by
  induction c with
  | nil => rfl
  | cons b l ih =>
    obtain ⟨b, e⟩ := b
    rw [prodW, prodW, h _ List.mem_cons_self, ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]

theorem valW_congr {c : CCell} (h : ∀ b ∈ c.bases, w b.1 = w' b.1) : c.valW w = c.valW w' := by
  rw [CCell.valW, CCell.valW, prodW_congr h]

end Words

/-! ## Exponents -/

section Rep

theorem capE_eq : capE = 2 ^ 62 := by norm_num [capE]

theorem gpow_inj_lt {a b : ℕ} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63)
    (h : ofK (addressOfIndex a) = ofK (addressOfIndex b)) : a = b :=
  gpow_injOn (show a < 2 ^ 64 - 1 by omega) (show b < 2 ^ 64 - 1 by omega) (ofK_injective h)

theorem rep_spec {x : E} {y : ℕ} (h : rep x = some y) : y < capE ∧ x = ofK (addressOfIndex y) := by
  unfold rep at h
  split_ifs at h with hx
  cases h
  exact Classical.choose_spec hx

theorem rep_of {y : ℕ} (hy : y < capE) : rep (ofK (addressOfIndex y)) = some y := by
  have hx : ∃ y', y' < capE ∧ ofK (addressOfIndex y) = ofK (addressOfIndex y') := ⟨y, hy, rfl⟩
  unfold rep
  split_ifs
  obtain ⟨h1, h2⟩ := Classical.choose_spec hx
  have e := capE_eq
  exact congrArg some (gpow_inj_lt (by omega) (by omega) h2).symm

theorem rep_const {w : ℕ → E} {n : ℕ} (h : n < capE) : rep ((⟨[], n⟩ : CCell).valW w) = some n := by
  rw [valW_const, rep_of h]

theorem rep_nil {w : ℕ → E} {c : CCell} (hc : c.bases.isEmpty = true) (h : c.off < capE) :
    rep (c.valW w) = some c.off := by
  rw [valW_nil hc, rep_of h]

/-- The exponent read off a power `g^z` is at most `z`. -/
theorem rep_le {x : E} {y z : ℕ} (h : rep x = some y) (hz : x = ofK (addressOfIndex z)) : y ≤ z := by
  obtain ⟨hy, hx⟩ := rep_spec h
  rw [capE_eq] at hy
  by_contra hlt
  have := gpow_inj_lt (a := y) (b := z) (by omega) (by omega) (hx.symm.trans hz)
  omega

/-- The exponent of a word times `g`: one more, while below the bound. -/
theorem rep_succ {x : E} {y : ℕ} (h : rep x = some y) (hy : y + 1 < capE) :
    rep (x * ofK (addressOfIndex 1)) = some (y + 1) := by
  obtain ⟨-, rfl⟩ := rep_spec h
  rw [← ofK_mul', addressOfIndex, addressOfIndex, ← pow_add, ← addressOfIndex, rep_of hy]

theorem ofK_gpow_ne_zero (n : ℕ) : ofK (addressOfIndex n) ≠ 0 := fun h ↦
  pow_ne_zero n g_ne_zero (ofK_injective (h.trans (map_zero (algebraMap K E)).symm))

/-- The exponent of a word, one less than that of the word times `g` when that is positive. -/
theorem rep_of_shift {w : ℕ → E} {c : CCell} {y : ℕ} (h : rep ((c.shift 1).valW w) = some y) (hy : 0 < y) :
    rep (c.valW w) = some (y - 1) := by
  obtain ⟨hyc, hv⟩ := rep_spec h
  rw [valW_shift] at hv
  have : c.valW w = ofK (addressOfIndex (y - 1)) := by
    refine mul_right_cancel₀ (ofK_gpow_ne_zero 1) (hv.trans ?_)
    rw [← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, Nat.sub_add_cancel hy]
  rw [this, rep_of (by omega)]

end Rep

/-! ## Runs and facts -/

section Runs

variable {w w' : ℕ → E} {W W' : K → Prop}

theorem runSet_congr {b b' lo lo' hi hi' : CCell} {S : ℕ} (hb : b.valW w = b'.valW w')
    (hl : lo.valW w = lo'.valW w') (hh : hi.valW w = hi'.valW w') {x : K} :
    RunSet w b S lo hi x ↔ RunSet w' b' S lo' hi' x := by
  simp only [RunSet, hb, hl, hh]

theorem runF_congr {b b' lo lo' hi hi' : CCell} {S : ℕ} (hb : b.valW w = b'.valW w')
    (hl : lo.valW w = lo'.valW w') (hh : hi.valW w = hi'.valW w') :
    RunF W w b S lo hi ↔ RunF W w' b' S lo' hi' := by
  simp only [RunF, runSet_congr hb hl hh]

theorem RunF.mono {b lo hi : CCell} {S : ℕ} (hw : ∀ x, W x → W' x) (h : RunF W w b S lo hi) :
    RunF W' w b S lo hi :=
  fun x hx ↦ hw x (h x hx)

theorem runSet_of {b lo hi : CCell} {S ylo yhi j : ℕ} (hl : rep (lo.valW w) = some ylo)
    (hh : rep (hi.valW w) = some yhi) (h1 : ylo ≤ j) (h2 : j < yhi) :
    RunSet w b S lo hi ((b.valW w * ofK (addressOfIndex (S * j))).limb 0) :=
  ⟨ylo, yhi, j, hl, hh, h1, h2, rfl⟩

/-- Facts true at `w`. -/
def FOk (w : ℕ → E) (F : List (CCell × CCell)) : Prop := ∀ p ∈ F, LtF w p.1 p.2

theorem hasF_ok {F : List (CCell × CCell)} (hF : FOk w F) {a b : CCell} (h : hasF F a b = true) : LtF w a b := by
  obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hq
  rw [← CCell.beq_eq hq.1, ← CCell.beq_eq hq.2]
  exact hF p hp

theorem hasFC_ok {F : List (CCell × CCell)} (hF : FOk w F) {k : ℕ} {b : CCell} (h : hasFC F k b = true) :
    ∃ yb, rep (b.valW w) = some yb ∧ k < yb := by
  obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hq
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hq
  obtain ⟨ya, yb, ha, hb, hab⟩ := hF p hp
  rw [rep_nil h1 h3, Option.some.injEq] at ha
  rw [CCell.beq_eq h4] at hb
  exact ⟨yb, hb, by omega⟩

/-- **A cell of a run at an index**: `c = base · J^S`, `J` below the upper bound by a fact, past the
lower one. -/
theorem ptIdx_ok {F : List (CCell × CCell)} (hF : FOk w F) {R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) {c J : CCell} (h : ptIdx F R c J = true) : W (c.addrW w) := by
  unfold ptIdx at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨yj, yhi, hyj, hyhi, hab⟩ := hasF_ok hF h2
  have hcap := (rep_spec hyhi).1
  obtain ⟨ylo, hylo, hle⟩ : ∃ ylo, rep (R.lo.valW w) = some ylo ∧ ylo ≤ yj := by
    rcases h3 with (⟨h4, h5⟩ | h4) | h4
    · have h5 := Nat.eq_of_beq_eq_true h5
      have := rep_nil (w := w) h4 (by rw [h5]; norm_num [capE])
      rw [h5] at this
      exact ⟨0, this, Nat.zero_le _⟩
    · exact ⟨yj, by rw [CCell.beq_eq h4]; exact hyj, le_rfl⟩
    · obtain ⟨yl, yj1, hyl, hyj1, hlt⟩ := hasF_ok hF h4
      rw [valW_shift, rep_succ hyj (by omega), Option.some.injEq] at hyj1
      exact ⟨yl, hyl, by omega⟩
  refine hR _ ⟨ylo, yhi, yj, hylo, hyhi, hle, hab, ?_⟩
  rw [CCell.addrW, CCell.beq_eq h1, valW_mul, valW_pow, (rep_spec hyj).2, ← ofK_pow', addressOfIndex,
    addressOfIndex, ← pow_mul, mul_comm yj]

/-- **A cell some indices below the upper bound**: written. -/
theorem ptBack_ok {F : List (CCell × CCell)} (hF : FOk w F) {R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) {c : CCell} (h : ptBack F R c = true) : W (c.addrW w) := by
  unfold ptBack at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨hk, hc⟩, hlb⟩, hlc⟩, hf⟩ := h
  set k := backK R c
  obtain ⟨yh, hyh, hlt⟩ := hasFC_ok hF hf
  have hhv := (rep_spec hyh).2
  have hcv : c.valW w * ofK (addressOfIndex (R.stride * k)) =
      R.base.valW w * ofK (addressOfIndex (R.stride * yh)) := by
    rw [← valW_shift, CCell.beq_eq hc, valW_mul, valW_pow, hhv, ← ofK_pow', addressOfIndex, addressOfIndex,
      ← pow_mul, mul_comm yh]
  have hne : ofK (addressOfIndex (R.stride * k)) ≠ 0 := fun h ↦
    pow_ne_zero _ g_ne_zero (ofK_injective (h.trans (map_zero (algebraMap K E)).symm))
  refine hR _ ⟨R.lo.off, yh, yh - k, rep_nil hlb hlc, hyh, by omega, by omega, ?_⟩
  have hv : c.valW w = R.base.valW w * ofK (addressOfIndex (R.stride * (yh - k))) := by
    refine mul_right_cancel₀ hne ?_
    rw [hcv, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, ← Nat.mul_add,
      Nat.sub_add_cancel (by omega : k ≤ yh)]
  rw [CCell.addrW, hv]

/-- **A cell of a run**: a run written, the facts true, `ptRun` gives the cell written. -/
theorem ptRun_ok {F : List (CCell × CCell)} (hF : FOk w F) {R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) {c : CCell} (h : ptRun F R c = true) : W (c.addrW w) := by
  unfold ptRun at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  rcases Bool.or_eq_true_iff.mp h with h | h
  rcases Bool.or_eq_true_iff.mp h with h | h
  pick_goal 2
  · exact ptIdx_ok hF hR h
  pick_goal 2
  · exact ptBack_ok hF hR h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ylo, yhi, hylo, hyhi, hab⟩ := hasF_ok hF h2
    refine hR _ ⟨ylo, yhi, ylo, hylo, hyhi, le_rfl, hab, ?_⟩
    rw [CCell.addrW, CCell.beq_eq h1, valW_mul, valW_pow, (rep_spec hylo).2, ← ofK_pow', addressOfIndex,
      addressOfIndex, ← pow_mul, mul_comm ylo]
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hb, hoff⟩, -⟩, hmod⟩, hlo⟩, hlc⟩, hk⟩, hhi⟩ := h
    have hmod := Nat.eq_of_beq_eq_true hmod
    set k := (c.off - R.base.off) / R.stride with hkdef
    obtain ⟨yhi, hyhi, hlt⟩ : ∃ yhi, rep (R.hi.valW w) = some yhi ∧ k < yhi := by
      rcases hhi with ⟨⟨h1, h2⟩, h3⟩ | h
      · exact ⟨R.hi.off, rep_nil h1 h2, h3⟩
      · exact hasFC_ok hF h
    refine hR _ ⟨R.lo.off, yhi, k, rep_nil hlo hlc, hyhi, hk, hlt, ?_⟩
    have hc : c.off = R.base.off + R.stride * k := by
      rw [hkdef]
      have := Nat.div_add_mod (c.off - R.base.off) R.stride
      omega
    rw [CCell.addrW, CCell.valW, CCell.valW, basesBeq_eq hb, hc, addressOfIndex, addressOfIndex, addressOfIndex,
      pow_add, ofK_mul', mul_assoc]

theorem eqR_ok {p : CCell × CCell} (hp : p.1.valW w = p.2.valW w) {x y : CCell} (h : eqR p x y = true) :
    x.valW w = y.valW w := by
  unfold eqR at h
  simp only [Bool.and_eq_true] at h
  rw [CCell.beq_eq h.1, CCell.beq_eq h.2, valW_pow, valW_pow, hp]

/-- **Two monomials with one word** by the equations. -/
theorem eqV_ok {E : List (CCell × CCell)} (hE : ∀ p ∈ E, p.1.valW w = p.2.valW w) {x y : CCell}
    (h : eqV E x y = true) : x.valW w = y.valW w := by
  unfold eqV at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [CCell.beq_eq h]
  · obtain ⟨p, hp, h⟩ := List.any_eq_true.mp h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact eqR_ok (hE p hp) h
    · exact eqR_ok (p := (p.2, p.1)) (hE p hp).symm h

theorem eqM_ok {p : CCell × CCell} (hp : p.1.valW w = p.2.valW w) {x y : CCell} (h : eqM p x y = true) :
    x.valW w = y.valW w := by
  unfold eqM at h
  simp only [Bool.and_eq_true] at h
  rw [CCell.beq_eq h.1, CCell.beq_eq h.2, valW_mul, valW_mul, valW_pow, valW_pow, hp]

/-- **Two monomials with one word**, a common factor allowed. -/
theorem eqVM_ok {E : List (CCell × CCell)} (hE : ∀ p ∈ E, p.1.valW w = p.2.valW w) {x y : CCell}
    (h : eqVM E x y = true) : x.valW w = y.valW w := by
  unfold eqVM at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact eqV_ok hE h
  · obtain ⟨p, hp, h⟩ := List.any_eq_true.mp h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact eqM_ok (hE p hp) h
    · exact eqM_ok (p := (p.2, p.1)) (hE p hp).symm h

/-- **A run inside a run**: a run written, the facts true, `runRun` gives the run written. -/
theorem runRun_ok {F : List (CCell × CCell)} (hF : FOk w F) {E : List (CCell × CCell)}
    (hE : ∀ p ∈ E, p.1.valW w = p.2.valW w) {Q R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) (h : runRun F E Q R = true) : RunF W w Q.base Q.stride Q.lo Q.hi := by
  unfold runRun at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hb, hS⟩, hlo⟩, hhi⟩ := h
  have hb := CCell.beq_eq hb
  have hS := Nat.eq_of_beq_eq_true hS
  rintro x ⟨ql, qh, j, hql, hqh, h1, h2, hx⟩
  have lo : ∃ rl, rep (R.lo.valW w) = some rl ∧ rl ≤ ql := by
    unfold loOk at hlo
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hlo
    rcases hlo with (h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨h1, h2⟩
    · exact ⟨ql, by rw [← eqV_ok hE h]; exact hql, le_rfl⟩
    · rw [rep_nil h1 h4, Option.some.injEq] at hql
      exact ⟨R.lo.off, rep_nil h2 (by omega), by omega⟩
    · obtain ⟨ya, yb, ha, hb', hab⟩ := hasF_ok hF h2
      have := (rep_spec hb').1
      rw [CCell.beq_eq h1, valW_shift, rep_succ ha (by omega), Option.some.injEq] at hql
      exact ⟨ya, ha, by omega⟩
  have hi : ∃ rh, rep (R.hi.valW w) = some rh ∧ qh ≤ rh := by
    unfold hiOk at hhi
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hhi
    rcases hhi with (((((h | h) | ⟨h0, h⟩) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨h1, h2⟩, h3⟩) | h)
    · exact ⟨qh, by rw [← eqV_ok hE h]; exact hqh, le_rfl⟩
    · obtain ⟨ya, yb, ha, hb', hab⟩ := hasF_ok hF h
      rw [hqh, Option.some.injEq] at ha
      exact ⟨yb, hb', by omega⟩
    · obtain ⟨ya, yb, ha, hb', hab⟩ := hasF_ok hF h
      have hyb := (rep_spec hb').1
      have hq : Q.hi = (⟨Q.hi.bases, Q.hi.off - 1⟩ : CCell).shift 1 := by
        simp only [CCell.shift]; rw [Nat.sub_add_cancel h0]
      rw [hq, valW_shift, rep_succ ha (by omega), Option.some.injEq] at hqh
      exact ⟨yb, hb', by omega⟩
    · rw [rep_nil h1 (by omega), Option.some.injEq] at hqh
      exact ⟨R.hi.off, rep_nil h2 h4, by omega⟩
    · obtain ⟨yb, hb', hkb⟩ := hasFC_ok hF h3
      rw [rep_nil h1 h2, Option.some.injEq] at hqh
      exact ⟨yb, hb', by omega⟩
    · obtain ⟨ya, yb, ha, hb', hab⟩ := hasF_ok hF h
      rw [hqh, Option.some.injEq] at ha
      exact ⟨yb - 1, rep_of_shift hb' (by omega), by omega⟩
  obtain ⟨rl, hrl, hl⟩ := lo
  obtain ⟨rh, hrh, hh⟩ := hi
  rw [hb, hS] at hx
  exact hR x ⟨rl, rh, j, hrl, hrh, by omega, by omega, hx⟩

theorem hasExp_ok {F : List (CCell × CCell)} (hF : FOk w F) {m : CCell} (h : hasExp F m = true) :
    ∃ y, rep (m.valW w) = some y := by
  unfold hasExp at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | hf
  · exact ⟨_, rep_nil h1 (Nat.blt_eq.mp h2)⟩
  · obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hf
    obtain ⟨ya, yb, ha, hb, -⟩ := hF p hp
    simp only [Bool.or_eq_true] at hpe
    rcases hpe with he | he
    · rw [CCell.beq_eq he] at ha; exact ⟨_, ha⟩
    · rw [CCell.beq_eq he] at hb; exact ⟨_, hb⟩


/-- **A run rebased is written** where the run is: its cells are the run's. -/
theorem shiftR_ok {Q R R2 : PRun} (h : shiftR Q R = some R2) (hR : RunF W w R.base R.stride R.lo R.hi) :
    RunF W w R2.base R2.stride R2.lo R2.hi := by
  unfold shiftR at h
  simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq] at h
  split_ifs at h with hc
  cases h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hS0, hS⟩, hb⟩, hoff⟩, hmod⟩, hql⟩, hrl⟩, hle⟩, hcap⟩ := hc
  have hb' := basesBeq_eq hb
  have hdvd : Q.stride ∣ R.base.off - Q.base.off := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨t, ht⟩ := hdvd
  have htd : (R.base.off - Q.base.off) / Q.stride = t := by rw [ht, Nat.mul_div_cancel_left _ hS0]
  rw [htd] at hle
  rintro x ⟨ylo, yhi, j, hylo, hyhi, h1, h2, rfl⟩
  simp only at hylo hyhi h1 h2 ⊢
  rw [rep_nil hql hcap, Option.some.injEq] at hylo
  subst hylo
  apply hR
  refine ⟨R.lo.off, yhi, j - t, rep_nil hrl (by omega), hyhi, by omega, by omega, ?_⟩
  have htj : t ≤ j := by omega
  have hj : Q.stride * j = Q.stride * t + Q.stride * (j - t) := by rw [← Nat.mul_add, Nat.add_sub_cancel' htj]
  have hR' : R.base = ⟨Q.base.bases, Q.base.off + Q.stride * t⟩ := by
    have e1 : R.base.off = Q.base.off + Q.stride * t := by omega
    cases hRB : R.base with
    | mk rb ro =>
      rw [hRB] at hb' e1
      simp only at hb' e1
      rw [hb', e1]
  rw [hR', ← hS]
  simp only [CCell.valW, addressOfIndex, mul_assoc, ← ofK_mul', ← pow_add]
  rw [hj, Nat.add_assoc]

/-- **A run inside a run rebased** (`runRunS`). -/
theorem runRunS_ok {F : List (CCell × CCell)} (hF : FOk w F) {E : List (CCell × CCell)}
    (hE : ∀ p ∈ E, p.1.valW w = p.2.valW w) {Q R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) (h : runRunS F E Q R = true) : RunF W w Q.base Q.stride Q.lo Q.hi := by
  unfold runRunS at h
  split at h
  · rename_i R2 hR2
    exact runRun_ok hF hE (shiftR_ok hR2 hR) h
  · cases h

/-- **A cell of a run extended by the point before it**: the point written, the run written, the cell
written. -/
theorem prep_ok {F : List (CCell × CCell)} (hF : FOk w F) {R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) {c : CCell} (h : prepIdx F R c = true)
    (hq : W ((prepQ R).addrW w)) : W (c.addrW w) := by
  unfold prepIdx at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨hS, hlb⟩, hl0⟩, hc⟩, h⟩ := h
  set J := idxOf (prepQ R) c R.stride with hJ
  have hl0 := Nat.eq_of_beq_eq_true hl0
  have hbase : R.base = (prepQ R).shift R.stride := by
    simp only [prepQ, CCell.shift]
    rw [Nat.sub_add_cancel hS]
  rcases h with ⟨⟨⟨⟨hbb, hoff⟩, hd⟩, hexh⟩, hexj⟩ | hf
  swap
  · -- `J` below the upper bound's next: the point (`J = g^0`) or a cell of the run
    obtain ⟨yj, yb, hyj, hyb, hlt⟩ := hasF_ok hF hf
    obtain ⟨hyjc, hjv⟩ := rep_spec hyj
    obtain ⟨hybc, hbv⟩ := rep_spec hyb
    have hhv : R.hi.valW w = ofK (addressOfIndex (yb - 1)) := by
      rw [valW_shift] at hbv
      refine mul_right_cancel₀ (ofK_gpow_ne_zero 1) (hbv.trans ?_)
      rw [← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, Nat.sub_add_cancel (by omega)]
    have hcv : c.valW w = (prepQ R).valW w * ofK (addressOfIndex (R.stride * yj)) := by
      rw [CCell.beq_eq hc, valW_mul, valW_pow, hjv, ← ofK_pow', addressOfIndex, addressOfIndex, ← pow_mul,
        mul_comm yj]
    rcases Nat.eq_zero_or_pos yj with h0 | hpos
    · rw [CCell.addrW, hcv, h0, Nat.mul_zero, show addressOfIndex 0 = 1 from pow_zero _,
        show ofK (1 : K) = 1 from _root_.map_one (algebraMap K E), mul_one]
      exact hq
    · obtain ⟨k, rfl⟩ : ∃ k, yj = k + 1 := ⟨yj - 1, by omega⟩
      refine hR _ ⟨0, yb - 1, k, ?_, ?_, Nat.zero_le _, by omega, ?_⟩
      · have := rep_nil (w := w) hlb (by rw [hl0]; norm_num [capE])
        rwa [hl0] at this
      · rw [hhv, rep_of (by omega)]
      · rw [CCell.addrW, hcv, hbase, valW_shift, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex,
          addressOfIndex, ← pow_add, Nat.mul_succ, Nat.add_comm (R.stride * k)]
  obtain ⟨yh, hyh⟩ := hasExp_ok hF hexh
  -- `hi = J·g^d`
  have hhi : R.hi.valW w = J.valW w * ofK (addressOfIndex (R.hi.off - J.off)) := by
    rw [CCell.valW, CCell.valW, basesBeq_eq hbb, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex,
      addressOfIndex, ← pow_add, Nat.add_sub_cancel' hoff]
  obtain ⟨yj, hyj⟩ : ∃ yj, rep (J.valW w) = some yj := by
    rcases hexj with he | he
    · rw [CCell.beq_eq he]; exact ⟨_, hyh⟩
    · exact hasExp_ok hF he
  obtain ⟨hyjc, hjv⟩ := rep_spec hyj
  obtain ⟨hyhc, hhv⟩ := rep_spec hyh
  have hyhj : yh = yj + (R.hi.off - J.off) := by
    rw [capE_eq] at hyjc hyhc hd
    refine gpow_inj_lt (by omega) (by omega) ?_
    rw [← hhv, hhi, hjv, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
  have hcv : c.valW w = (prepQ R).valW w * ofK (addressOfIndex (R.stride * yj)) := by
    rw [CCell.beq_eq hc, valW_mul, valW_pow, hjv, ← ofK_pow', addressOfIndex, addressOfIndex, ← pow_mul,
      mul_comm yj]
  rcases Nat.eq_zero_or_pos yj with h0 | hpos
  · rw [CCell.addrW, hcv, h0, Nat.mul_zero, show addressOfIndex 0 = 1 from pow_zero _,
      show ofK (1 : K) = 1 from _root_.map_one (algebraMap K E), mul_one]
    exact hq
  · obtain ⟨k, rfl⟩ : ∃ k, yj = k + 1 := ⟨yj - 1, by omega⟩
    refine hR _ ⟨0, yh, k, ?_, hyh, Nat.zero_le _, by omega, ?_⟩
    · have := rep_nil (w := w) hlb (by rw [hl0]; norm_num [capE])
      rwa [hl0] at this
    · rw [CCell.addrW, hcv, hbase, valW_shift, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex,
        addressOfIndex, ← pow_add, Nat.mul_succ, Nat.add_comm (R.stride * k)]

/-- **A cell of a run extended by its point after it**: in the run, or that point. -/
theorem app_ok {F : List (CCell × CCell)} (hF : FOk w F) {R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) {c : CCell} (h : appIdx F R c = true)
    (hq : W ((appQ R).addrW w)) : W (c.addrW w) := by
  unfold appIdx at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hlb, hl0⟩, hc⟩, hf⟩ := h
  set J := idxOf R.base c R.stride with hJ
  have hl0 := Nat.eq_of_beq_eq_true hl0
  obtain ⟨yj, yb, hyj, hyb, hlt⟩ := hasF_ok hF hf
  obtain ⟨hyjc, hjv⟩ := rep_spec hyj
  obtain ⟨hybc, hbv⟩ := rep_spec hyb
  -- `hi = g^(yb - 1)`
  have hhv : R.hi.valW w = ofK (addressOfIndex (yb - 1)) := by
    rw [valW_shift] at hbv
    refine mul_right_cancel₀ (ofK_gpow_ne_zero 1) (hbv.trans ?_)
    rw [← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, Nat.sub_add_cancel (by omega)]
  have hcv : c.valW w = R.base.valW w * ofK (addressOfIndex (R.stride * yj)) := by
    rw [CCell.beq_eq hc, valW_mul, valW_pow, hjv, ← ofK_pow', addressOfIndex, addressOfIndex, ← pow_mul,
      mul_comm yj]
  rcases Nat.lt_or_ge yj (yb - 1) with hin | hge
  · refine hR _ ⟨0, yb - 1, yj, ?_, ?_, Nat.zero_le _, hin, ?_⟩
    · have := rep_nil (w := w) hlb (by rw [hl0]; norm_num [capE])
      rwa [hl0] at this
    · rw [hhv, rep_of (by omega)]
    · rw [CCell.addrW, hcv]
  · have hj : yj = yb - 1 := by omega
    rw [CCell.addrW, hcv, hj]
    have : (appQ R).valW w = R.base.valW w * ofK (addressOfIndex (R.stride * (yb - 1))) := by
      rw [appQ, valW_mul, valW_pow, hhv, ← ofK_pow', addressOfIndex, addressOfIndex, ← pow_mul, mul_comm (yb - 1)]
    rw [← this]
    exact hq

/-- **A cell of a run of lower bound `g^1` extended by its two points before it** (`prepIdx2`): the point
`base·g^-stride` (index `0`), the base (index `1`), or a cell of the run. -/
theorem prep2_ok {F : List (CCell × CCell)} (hF : FOk w F) {R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) {c : CCell} (h : prepIdx2 F R c = true)
    (hq : W ((prepQ R).addrW w)) (hq2 : W (R.base.addrW w)) : W (c.addrW w) := by
  unfold prepIdx2 at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hS, hlb⟩, hl1⟩, hc⟩, hbb⟩, hoff⟩, hd⟩, hexh⟩, hexj⟩ := h
  set J := idxOf (prepQ R) c R.stride with hJ
  have hl1 := Nat.eq_of_beq_eq_true hl1
  obtain ⟨yh, hyh⟩ := hasExp_ok hF hexh
  have hhi : R.hi.valW w = J.valW w * ofK (addressOfIndex (R.hi.off - J.off)) := by
    rw [CCell.valW, CCell.valW, basesBeq_eq hbb, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex,
      addressOfIndex, ← pow_add, Nat.add_sub_cancel' hoff]
  obtain ⟨yj, hyj⟩ : ∃ yj, rep (J.valW w) = some yj := by
    rcases hexj with he | he
    · rw [CCell.beq_eq he]; exact ⟨_, hyh⟩
    · exact hasExp_ok hF he
  obtain ⟨hyjc, hjv⟩ := rep_spec hyj
  obtain ⟨hyhc, hhv⟩ := rep_spec hyh
  have hyhj : yh = yj + (R.hi.off - J.off) := by
    rw [capE_eq] at hyjc hyhc hd
    refine gpow_inj_lt (by omega) (by omega) ?_
    rw [← hhv, hhi, hjv, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
  have hcv : c.valW w = (prepQ R).valW w * ofK (addressOfIndex (R.stride * yj)) := by
    rw [CCell.beq_eq hc, valW_mul, valW_pow, hjv, ← ofK_pow', addressOfIndex, addressOfIndex, ← pow_mul,
      mul_comm yj]
  have hbase : R.base = (prepQ R).shift R.stride := by
    simp only [prepQ, CCell.shift]
    rw [Nat.sub_add_cancel hS]
  rcases yj with _ | _ | k
  · rw [CCell.addrW, hcv, Nat.mul_zero, show addressOfIndex 0 = 1 from pow_zero _,
      show ofK (1 : K) = 1 from _root_.map_one (algebraMap K E), mul_one]
    exact hq
  · have he : c.addrW w = R.base.addrW w := by
      rw [CCell.addrW, CCell.addrW, hcv, hbase, valW_shift, Nat.zero_add, Nat.mul_one]
    rw [he]
    exact hq2
  · refine hR _ ⟨1, yh, k + 1, ?_, hyh, by omega, by omega, ?_⟩
    · have := rep_nil (w := w) hlb (by rw [hl1]; norm_num [capE])
      rwa [hl1] at this
    · rw [CCell.addrW, hcv, hbase, valW_shift, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex,
        addressOfIndex, ← pow_add, Nat.mul_succ, Nat.add_comm (R.stride * (k + 1))]

end Runs

/-! ## Monomials at a site -/

section Inst

variable {w w' : ℕ → E}

/-- **Slot monomials `ms` naming the slot words `w'`**: each `ms[b]`'s word is `w' b`. -/
def MsOk (w : ℕ → E) (ms : List CCell) (w' : ℕ → E) : Prop := ∀ b m, nth ms b = some m → m.valW w = w' b

theorem instB_ok {ms : List CCell} (h : MsOk w ms w') : ∀ (l : List (ℕ × ℕ)) (acc c' : CCell),
    instB ms l acc = some c' → c'.valW w = acc.valW w * prodW w' l
  | [], acc, c', hc => by
    simp only [instB, Option.some.injEq] at hc
    subst hc
    simp [prodW]
  | (b, e) :: l, acc, c', hc => by
    simp only [instB] at hc
    cases hm : nth ms b with
    | none => rw [hm] at hc; cases hc
    | some m =>
      rw [hm] at hc
      rw [instB_ok h l _ c' hc, valW_mul, valW_pow, h b m hm, prodW]
      ring

theorem instC_ok {ms : List CCell} (h : MsOk w ms w') {c c' : CCell} (hc : instC ms c = some c') :
    c'.valW w = c.valW w' := by
  rw [instB_ok h c.bases ⟨[], c.off⟩ c' hc, valW_const, CCell.valW]
  ring

theorem instI_ok {ms : List CCell} (h : MsOk w ms w') {i : CIdx} {m : CCell} (hi : instI ms i = some m) :
    m.valW w = (idxC i).valW w' := by
  cases i with
  | num n =>
    simp only [instI, Option.some.injEq] at hi
    subst hi
    rw [idxC, valW_const, valW_const]
  | val v => rw [idxC, valW_baseC]; exact h v m hi
  | mono c => rw [idxC]; exact instC_ok h hi

theorem instR_ok {ms : List CCell} (h : MsOk w ms w') {r : CRun} {q : PRun} (hr : instR ms r = some q) :
    q.base.valW w = r.base.valW w' ∧ q.stride = r.stride ∧ q.lo.valW w = (idxC r.lo).valW w' ∧
      q.hi.valW w = (idxC r.hi).valW w' := by
  unfold instR at hr
  cases hb : instC ms r.base with
  | none => simp [hb] at hr
  | some b =>
    cases hl : instI ms r.lo with
    | none => simp [hb, hl] at hr
    | some l =>
      cases hh : instI ms r.hi with
      | none => simp [hb, hl, hh] at hr
      | some hi =>
        simp only [hb, hl, hh, Option.some.injEq] at hr
        subst hr
        exact ⟨instC_ok h hb, rfl, instI_ok h hl, instI_ok h hh⟩

/-- A signature run at a site is written as the pass-level run is. -/
theorem instR_runF {ms : List CCell} (h : MsOk w ms w') {r : CRun} {q : PRun} (hr : instR ms r = some q)
    {W : K → Prop} : RunF W w q.base q.stride q.lo q.hi ↔ r.F W w' := by
  obtain ⟨h1, h2, h3, h4⟩ := instR_ok h hr
  rw [h2]
  exact runF_congr h1 h3 h4

theorem instR_set {ms : List CCell} (h : MsOk w ms w') {r : CRun} {q : PRun} (hr : instR ms r = some q)
    {x : K} : RunSet w q.base q.stride q.lo q.hi x ↔ r.Set w' x := by
  obtain ⟨h1, h2, h3, h4⟩ := instR_ok h hr
  rw [h2]
  exact runSet_congr h1 h3 h4

theorem instAll_ok {ms : List CCell} : ∀ {cs cs' : List CCell}, instAll ms cs = some cs' →
    ∀ c' ∈ cs', ∃ c ∈ cs, instC ms c = some c'
  | [], cs', h, c', hc => by simp only [instAll, Option.some.injEq] at h; subst h; simp at hc
  | c :: cs, cs', h, c', hc => by
    simp only [instAll] at h
    cases h1 : instC ms c with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : instAll ms cs with
      | none => simp [h1, h2] at h
      | some l =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨c, List.mem_cons_self, h1⟩
        · obtain ⟨d, hd, hd'⟩ := instAll_ok h2 c' hc
          exact ⟨d, List.mem_cons_of_mem _ hd, hd'⟩

theorem instAllR_ok {ms : List CCell} : ∀ {rs : List CRun} {qs : List PRun}, instAllR ms rs = some qs →
    ∀ q ∈ qs, ∃ r ∈ rs, instR ms r = some q
  | [], qs, h, q, hq => by simp only [instAllR, Option.some.injEq] at h; subst h; simp at hq
  | r :: rs, qs, h, q, hq => by
    simp only [instAllR] at h
    cases h1 : instR ms r with
    | none => simp [h1] at h
    | some q1 =>
      cases h2 : instAllR ms rs with
      | none => simp [h1, h2] at h
      | some l =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨r, List.mem_cons_self, h1⟩
        · obtain ⟨d, hd, hd'⟩ := instAllR_ok h2 q hq
          exact ⟨d, List.mem_cons_of_mem _ hd, hd'⟩

theorem nth_eq {α : Type} : ∀ (l : List α) (n : ℕ), nth l n = l[n]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => nth_eq l n

theorem nth_append {α : Type} : ∀ (l1 l2 : List α) (b : ℕ),
    nth (l1 ++ l2) b = if b < l1.length then nth l1 b else nth l2 (b - l1.length)
  | [], l2, b => by simp
  | a :: l1, l2, 0 => by simp [nth]
  | a :: l1, l2, b + 1 => by
    simp only [List.cons_append, nth, nth_append l1 l2 b, List.length_cons, Nat.add_lt_add_iff_right,
      Nat.add_sub_add_right]

theorem slotW_append (ws1 ws2 : List E) (b : ℕ) :
    slotW (ws1 ++ ws2) b = if b < ws1.length then slotW ws1 b else slotW ws2 (b - ws1.length) := by
  unfold slotW
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega)]

theorem msOk_append {ms1 ms2 : List CCell} {ws1 ws2 : List E} (h1 : MsOk w ms1 (slotW ws1))
    (h2 : MsOk w ms2 (slotW ws2)) (hl : ms1.length = ws1.length) : MsOk w (ms1 ++ ms2) (slotW (ws1 ++ ws2)) := by
  intro b m hb
  rw [nth_append] at hb
  rw [slotW_append, ← hl]
  split_ifs at hb ⊢
  · exact h1 b m hb
  · exact h2 _ m hb

theorem monos_ok {σ : Val} {env : Trie CCell} (he : EnvOk σ env) : ∀ (vs : List V) (ms : List CCell),
    monos env vs = some ms → MsOk (vw σ) ms (slotW (vs.map σ)) ∧ ms.length = vs.length
  | [], ms, h => by
    simp only [monos, Option.some.injEq] at h
    subst h
    exact ⟨fun b m hm ↦ by simp [nth] at hm, rfl⟩
  | v :: vs, ms, h => by
    simp only [monos] at h
    cases hm : monoOf env v with
    | none => simp [hm] at h
    | some m =>
      cases hms : monos env vs with
      | none => simp [hm, hms] at h
      | some ms' =>
        simp only [hm, hms, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := monos_ok he vs ms' hms
        refine ⟨fun b m' hb ↦ ?_, by simp [h2]⟩
        cases b with
        | zero =>
          simp only [nth, Option.some.injEq] at hb
          subst hb
          rw [← val_eq, ← monoOf_ok he hm]
          rfl
        | succ b =>
          simp only [nth] at hb
          rw [h1 b m' hb]
          rfl

/-- Monomials over values, as they are: their words. -/
theorem msOk_map {σ : Val} (ms : List CCell) : MsOk (vw σ) ms (slotW (ms.map fun c ↦ c.valW (vw σ))) := by
  intro b m hb
  rw [nth_eq] at hb
  unfold slotW
  simp [List.getD_eq_getElem?_getD, hb]

/-- The parameters' words, slot by slot: `V.n b`'s word below their count. -/
theorem slotW_params {σ : Val} {m b : ℕ} (hb : b < m) : slotW ((List.range m).map fun k ↦ σ (V.n k)) b = vw σ b := by
  unfold slotW vw
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hb]

theorem setNth_length {α : Type} : ∀ (l : List α) (n : ℕ) (b : α), (setNth l n b).length = l.length
  | [], _, _ => rfl
  | _ :: l, 0, _ => rfl
  | _ :: l, n + 1, b => by simp [setNth, setNth_length l n b]

theorem nth_setNth {α : Type} : ∀ (l : List α) (n k : ℕ) (b : α),
    nth (setNth l n b) k = if k = n ∧ n < l.length then some b else nth l k
  | [], _, _, _ => by simp [setNth, nth]
  | _ :: l, 0, 0, _ => by simp [setNth, nth]
  | _ :: l, 0, k + 1, _ => by simp [setNth, nth]
  | _ :: l, n + 1, 0, _ => by simp [setNth, nth]
  | _ :: l, n + 1, k + 1, b => by simp [setNth, nth, nth_setNth l n k b]

theorem slotW_setNth : ∀ (l : List E) (n k : ℕ) (b : E),
    slotW (setNth l n b) k = if k = n ∧ n < l.length then b else slotW l k
  | [], _, _, _ => by simp [setNth, slotW]
  | _ :: l, 0, 0, _ => by simp [setNth, slotW]
  | _ :: l, 0, k + 1, _ => by simp [setNth, slotW]
  | _ :: l, n + 1, 0, _ => by simp [setNth, slotW]
  | _ :: l, n + 1, k + 1, b => by
    have := slotW_setNth l n k b
    simp only [slotW] at this ⊢
    rw [setNth, List.getD_cons_succ, List.getD_cons_succ, this]
    simp

theorem msOk_setNth {ms : List CCell} {ws : List E} (h : MsOk w ms (slotW ws)) (hl : ms.length = ws.length)
    {n : ℕ} {m : CCell} {v : E} (hm : m.valW w = v) : MsOk w (setNth ms n m) (slotW (setNth ws n v)) := by
  intro b m' hb
  rw [nth_setNth] at hb
  rw [slotW_setNth, ← hl]
  split_ifs at hb ⊢ with h1
  · cases hb; exact hm
  · exact h b m' hb

theorem msOk_setRM {ms : List CCell} {ws : List E} (h : MsOk w ms (slotW ws)) (hl : ms.length = ws.length) :
    ∀ {l : List (ℕ × CCell)}, (∀ k m, (k, m) ∈ l → k < ws.length → m.valW w = slotW ws k) →
      MsOk w (setRM ms l) (slotW ws) ∧ (setRM ms l).length = ws.length
  | [], _ => ⟨h, hl⟩
  | (k, m) :: l, hl' => by
    obtain ⟨h1, h2⟩ := msOk_setRM h hl (fun k' m' h ↦ hl' k' m' (List.mem_cons_of_mem _ h))
    refine ⟨fun b m' hb ↦ ?_, by rw [setRM, setNth_length, h2]⟩
    rw [setRM, nth_setNth] at hb
    split_ifs at hb with hbk
    · cases hb; rw [hbk.1]; exact hl' k m List.mem_cons_self (by rw [← h2]; exact hbk.2)
    · exact h1 b m' hb

theorem slotW_map_of {σ : Val} {rets : List V} {j : ℕ} {r : V} (h : rets[j]? = some r) :
    slotW (rets.map σ) j = σ r := by
  simp [slotW, List.getD_eq_getElem?_getD, h]

end Inst

end

end LeanVM.Guest.CoreMode
