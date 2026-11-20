/-
  LeanVM.Guest.CoreMode.HeapCSound

  The heap check with calls and loops is sound on the path: every event's needs are written
  before it, and the guarantees at return are written.
-/

module

public import LeanVM.Guest.CoreMode.HeapC
public import LeanVM.Guest.CoreMode.HeapSound
public import LeanVM.Guest.CoreMode.Fam.LoopTree

/-!
# The heap check with calls and loops is sound

`heapOkC_sound`: for a function passing `heapOkC`, a valuation `σ` whose path returns, its events
holding and each entered call's callee guarantees' runs having their exponents, given its entry
facts (`EntryF`: its preconditions' runs' exponents, its termination facts) and its residuals
(`ResF`): every event's needs are written before it (`ReadsOkC`) and its guarantees at return are
written (`PostOkC`).

The proof follows milestone 1's (`HeapSound.lean`): the pass's state is valid on the path
(`StOk rd W`: the environment's monomials are the values' words, the scope's cells and runs written in
`W`, the runs' exponents existing), `W` the preconditions and the writes so far; a witness of a cell
or a run gives it written (`ptOk_ok`, `rnOk_ok`, by `ptRun_ok` and `runRun_ok` from the run's
exponents and the facts); a signature at a site is the cells and runs at the slots' words
(`instC_ok`, `MsOk`). A loop's tail (`tailC_ok`) splits on its condition: entered, the next
iteration's guarantees at its words (`EvW`, the same cells when not over the counter, the run from
one further); not entered, the next counter is the end (`Res.loop_path`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq natSeq_eq)
open LeanVM.Guest.Check (getF setF getF_eq setF_eq)

public section

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
@[expose] def lift (w : ℕ → E) : Val := fun v ↦ w v.idx

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

/-! ## The pass's invariant -/

section Inv

variable {σ : Val} {rd : Reader} {W W' : K → Prop}

/-- **The run scope is written**: each run's cells are in `W`. -/
def RsOk (W : K → Prop) (σ : Val) (rs : Trie PRun) : Prop :=
  ∀ r R, getF rs r = some R → RunF W (vw σ) R.base R.stride R.lo R.hi

/-- **The sums seen hold**: each value the sum of its operands' monomials' words. -/
def AdOk (σ : Val) (ad : Trie (CCell × CCell)) : Prop :=
  ∀ k p, getF ad k = some p → σ (V.n k) = p.1.valW (vw σ) + p.2.valW (vw σ)

/-- **The words stored are in memory**: each load event's word, at its cell. -/
def SvOk (rd : Reader) (σ : Val) (sv : Trie (CCell × CCell)) : Prop :=
  ∀ n p, getF sv n = some p → rd (p.1.addr σ) = some (p.2.valW (vw σ))

/-- **The values loaded are in memory**: each value's word at the cell it was loaded from. -/
def SrcOk (rd : Reader) (σ : Val) (src : Trie CCell) : Prop :=
  ∀ k c, getF src k = some c → rd (c.addr σ) = some (σ (V.n k))

/-- **The pointer facts in scope are written**: past the word at each fact's cell. -/
def PfOk (rd : Reader) (W : K → Prop) (σ : Val) (pf : Trie (CCell × List ℕ)) : Prop :=
  ∀ n p, getF pf n = some p → ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W x

/-- **The pointer runs in scope are written**: past the word at each cell of each run. -/
def PrOk (rd : Reader) (W : K → Prop) (σ : Val) (pr : Trie (PRun × List ℕ)) : Prop :=
  ∀ n p, getF pr n = some p → ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W x

/-- **A dispatch arm's guarantees hold**: written. -/
def CdAOk (rd : Reader) (W : K → Prop) (σ : Val) (e : CdA) : Prop :=
  (∀ c ∈ e.cs, W (c.addr σ)) ∧ (∀ q ∈ e.rs, RunF W (vw σ) q.base q.stride q.lo q.hi) ∧
    (∀ p ∈ e.ps, ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W x) ∧
    ∀ p ∈ e.prs, ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W x

/-- **The guarantees under selectors hold**: a dispatch's arm `j`'s where the selector's word is `g^j`. -/
def CdOk (rd : Reader) (W : K → Prop) (σ : Val) (cd : List CdE) : Prop :=
  ∀ e ∈ cd, ∀ j a, nth e.arms j = some a → e.mx.valW (vw σ) = ofK (addressOfIndex j) → CdAOk rd W σ a

theorem CdOk.mono (hw : ∀ x, W x → W' x) {cd : List CdE} (h : CdOk rd W σ cd) : CdOk rd W' σ cd :=
  fun e he j a ha hj ↦ let ⟨h1, h2, h3, h4⟩ := h e he j a ha hj
    ⟨fun c hc ↦ hw _ (h1 c hc), fun q hq ↦ (h2 q hq).mono hw, fun p hp x hx ↦ hw _ (h3 p hp x hx),
      fun p hp a ha x hx ↦ hw _ (h4 p hp a ha x hx)⟩

/-- **The equations hold**: each one's sides one word. -/
def EqsOk (σ : Val) (E : List (CCell × CCell)) : Prop := ∀ p ∈ E, p.1.valW (vw σ) = p.2.valW (vw σ)

/-- **The runs at words are written**: at each cell holding a word, the run at that word. -/
def DqOk (rd : Reader) (W : K → Prop) (σ : Val) (dq : List (CCell × PRun)) : Prop :=
  ∀ p ∈ dq, ∀ w, rd (p.1.addr σ) = some w → ∀ x, RunSetB (vw σ) w p.2.base p.2.stride p.2.lo p.2.hi x → W x

/-- **The state is valid**: its monomials, its written cells and runs, its sums, its stored words,
the cells its values were loaded from, its pointer facts and runs, its guarantees under selectors. -/
structure StOk (rd : Reader) (W : K → Prop) (σ : Val) (st : CSt) : Prop where
  env : EnvOk σ st.env
  sc : ScOk W σ st.sc
  rs : RsOk W σ st.rs
  ad : AdOk σ st.ad
  sv : SvOk rd σ st.sv
  src : SrcOk rd σ st.src
  pf : PfOk rd W σ st.pf
  pr : PrOk rd W σ st.pr
  cd : CdOk rd W σ st.cd
  eqs : EqsOk σ st.eqs
  dq : DqOk rd W σ st.dq

theorem StOk.mono (hw : ∀ x, W x → W' x) {st : CSt} (h : StOk rd W σ st) : StOk rd W' σ st :=
  ⟨h.env, h.sc.mono hw, fun r R hr ↦ (h.rs r R hr).mono hw, h.ad, h.sv, h.src,
    fun n p hp x hx ↦ hw _ (h.pf n p hp x hx), fun n p hp a ha x hx ↦ hw _ (h.pr n p hp a ha x hx),
    h.cd.mono hw, h.eqs, fun p hp w hw' x hx ↦ hw _ (h.dq p hp w hw' x hx)⟩

theorem StOk.cnt {st : CSt} (h : StOk rd W σ st) (s : CSt) : StOk rd W σ (st.cnt s) :=
  ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩

theorem StOk.nextC {st : CSt} (h : StOk rd W σ st) : StOk rd W σ st.nextC :=
  ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩

theorem StOk.nextT {st : CSt} (h : StOk rd W σ st) : StOk rd W σ st.nextT :=
  ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩

theorem CSt.seq_eq {β : Type} (st : CSt) (k : CSt → β) : st.seq k = k st := by
  simp only [CSt.seq, Trie.seq_eq, natSeq_eq]

theorem PRun.seq_eq {β : Type} (r : PRun) (k : PRun → β) : r.seq k = k r := by
  simp only [PRun.seq, CCell.seq_eq, natSeq_eq]

theorem push_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {c : CCell} (hc : W' (c.addr σ)) :
    StOk rd W' σ (st.push c) := by
  have hs' := hs.mono hw
  obtain ⟨h1, h2⟩ := push_ok (W := W') (st := st.toH) hs'.sc hc
  exact ⟨by rw [CSt.push, CSt.ofH]; exact h1 ▸ hs.env, h2, hs'.rs, hs.ad, hs.sv, hs.src, hs'.pf, hs'.pr, hs'.cd, hs.eqs, hs'.dq⟩

theorem def_stOk {st : CSt} (hs : StOk rd W σ st) {k : ℕ} {c : CCell} (hc : σ (V.n k) = c.val σ) :
    StOk rd W σ (st.def k c) :=
  ⟨(def_ok (st := st.toH) hs.env hc).1, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, hs.cd, hs.eqs, hs.dq⟩

theorem pushV_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {c m : CCell} (hc : W' (c.addr σ))
    (hm : rd (c.addr σ) = some (m.valW (vw σ))) : StOk rd W' σ (st.pushV c m) := by
  unfold CSt.pushV
  rw [CCell.seq_eq, Trie.seq_eq, CSt.seq_eq]
  have h := push_stOk hs hw hc
  refine ⟨h.env, h.sc, h.rs, h.ad, fun n p hp ↦ ?_, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩
  change getF (setF (c, m) Exec.indexDepth st.sv st.n) n = some p at hp
  rcases getF_setF hp with ⟨-, rfl⟩ | hp
  · exact hm
  · exact hs.sv n p hp

theorem srcPut_stOk {st : CSt} (hs : StOk rd W σ st) {d : V} {c : CCell} (hd : rd (c.addr σ) = some (σ d)) :
    StOk rd W σ (st.srcPut d c) := by
  unfold CSt.srcPut
  cases hk : vnum d with
  | none => exact hs
  | some k =>
    dsimp only
    cases hc : getF st.src k with
    | some _ => exact hs
    | none =>
      dsimp only
      rw [Trie.seq_eq]
      refine ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, fun k' c' hk' ↦ ?_, hs.pf, hs.pr, hs.cd, hs.eqs, hs.dq⟩
      change getF (setF c Exec.indexDepth st.src k) k' = some c' at hk'
      rcases getF_setF hk' with ⟨rfl, rfl⟩ | hk'
      · rw [hd, vnum_eq hk]
      · exact hs.src k' c' hk'

theorem pushP_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {p : CCell × List ℕ}
    (hp : ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W' x) : StOk rd W' σ (st.pushP p) := by
  unfold CSt.pushP
  rw [CCell.seq_eq, Trie.seq_eq]
  have h := hs.mono hw
  refine ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, fun n q hq ↦ ?_, h.pr, h.cd, h.eqs, h.dq⟩
  change getF (setF (p.1, p.2) Exec.indexDepth st.pf st.n) n = some q at hq
  rcases getF_setF hq with ⟨-, rfl⟩ | hq
  · exact hp
  · exact h.pf n q hq

theorem pushPR_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {p : PRun × List ℕ}
    (hp : ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W' x) :
    StOk rd W' σ (st.pushPR p) := by
  unfold CSt.pushPR
  rw [PRun.seq_eq, Trie.seq_eq]
  have h := hs.mono hw
  refine ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, h.pf, fun n q hq ↦ ?_, h.cd, h.eqs, h.dq⟩
  change getF (setF (p.1, p.2) Exec.indexDepth st.pr st.nr) n = some q at hq
  rcases getF_setF hq with ⟨-, rfl⟩ | hq
  · exact hp
  · exact h.pr n q hq

theorem pushPL_ok : ∀ {W W' : K → Prop} {ps : List (CCell × List ℕ)} {st : CSt}, StOk rd W σ st →
    (∀ x, W x → W' x) → (∀ p ∈ ps, ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W' x) → StOk rd W' σ (pushPL ps st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, p :: ps, st, hs, hw, hp => by
    rw [pushPL, CSt.seq_eq]
    exact pushPL_ok (pushP_stOk hs hw (hp p List.mem_cons_self)) (fun _ h ↦ h)
      fun p' h ↦ hp p' (List.mem_cons_of_mem _ h)

theorem pushPRL_ok : ∀ {W W' : K → Prop} {ps : List (PRun × List ℕ)} {st : CSt}, StOk rd W σ st →
    (∀ x, W x → W' x) →
    (∀ p ∈ ps, ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W' x) →
    StOk rd W' σ (pushPRL ps st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, p :: ps, st, hs, hw, hp => by
    rw [pushPRL, CSt.seq_eq]
    exact pushPRL_ok (pushPR_stOk hs hw (hp p List.mem_cons_self)) (fun _ h ↦ h)
      fun p' h ↦ hp p' (List.mem_cons_of_mem _ h)

theorem pushL_ok : ∀ {W W' : K → Prop} {cs : List CCell} {st : CSt}, StOk rd W σ st → (∀ x, W x → W' x) →
    (∀ c ∈ cs, W' (c.addr σ)) → StOk rd W' σ (pushL cs st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, c :: cs, st, hs, hw, hc => by
    rw [pushL, CCell.seq_eq, CSt.seq_eq]
    exact pushL_ok (push_stOk hs hw (hc c List.mem_cons_self)) (fun _ h ↦ h)
      fun c' h ↦ hc c' (List.mem_cons_of_mem _ h)

theorem pushR_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {q : PRun}
    (hq : RunF W' (vw σ) q.base q.stride q.lo q.hi) : StOk rd W' σ (st.pushR q) := by
  have h := hs.mono hw
  unfold CSt.pushR
  rw [Trie.seq_eq]
  refine ⟨h.env, h.sc, fun r R hr ↦ ?_, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩
  change getF (setF q Exec.indexDepth st.rs st.nr) r = some R at hr
  rcases getF_setF hr with ⟨-, rfl⟩ | hr
  · exact hq
  · exact h.rs r R hr

theorem pushRL_ok : ∀ {W W' : K → Prop} {qs : List PRun} {st : CSt}, StOk rd W σ st → (∀ x, W x → W' x) →
    (∀ q ∈ qs, RunF W' (vw σ) q.base q.stride q.lo q.hi) → StOk rd W' σ (pushRL qs st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, q :: qs, st, hs, hw, hq => by
    rw [pushRL, PRun.seq_eq, CSt.seq_eq]
    exact pushRL_ok (pushR_stOk hs hw (hq q List.mem_cons_self)) (fun _ h ↦ h)
      fun q' h ↦ hq q' (List.mem_cons_of_mem _ h)

/-- **What the pass reads, valid**: milestone 1's, the signatures, the parameters, the residuals,
and the facts true at the instance. -/
structure XOk (sigOf : String → HSig) (H : HCert) (rd : Reader) (f : Fn) (σ : Val) (X : CX) : Prop where
  R : X.R = H.readT
  pre : ∀ k c, getF X.pre k = some c → c ∈ H.sig.pre
  pows : X.pows.Ok
  sigOf : X.sigOf = sigOf
  ga : X.ga = H.gargs
  sig : X.sig = H.sig
  params : X.params = f.params
  res : ∀ i c, getF X.res i = some c → c ∈ H.res
  term : ∀ p ∈ H.sig.term, LtF (vw σ) (idxC p.1) (idxC p.2)
  resF : ResF H σ
  path : ∀ c ∈ X.path, c.Holds σ
  fas : X.fas = H.fas
  ders : X.ders = H.ders
  der : DerOk H rd σ
  gw : GwOk H.sig rd σ

/-- The site under further branch conditions that hold. -/
theorem XOk.ext {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X) {l : List CCond}
    (hl : ∀ c ∈ l, c.Holds σ) : XOk sigOf H rd f σ (X.ext l) :=
  ⟨hX.R, hX.pre, hX.pows, hX.sigOf, hX.ga, hX.sig, hX.params, hX.res, hX.term, hX.resF,
    fun c hc ↦ (List.mem_append.mp hc).elim (hl c) (hX.path c), hX.fas, hX.ders, hX.der, hX.gw⟩

theorem CCond.beq_eq : ∀ {a b : CCond}, CCond.beq a b = true → a = b
  | .arm x j, .arm x' j', h => by
    simp only [CCond.beq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2]
  | .zero c, .zero c', h => by rw [Nat.eq_of_beq_eq_true h]
  | .nonzero c, .nonzero c', h => by rw [Nat.eq_of_beq_eq_true h]
  | .arm .., .zero _, h | .arm .., .nonzero _, h | .zero _, .arm .., h | .zero _, .nonzero _, h
  | .nonzero _, .arm .., h | .nonzero _, .zero _, h => by simp [CCond.beq] at h

theorem onPath_ok {path g : List CCond} (h : onPath path g = true) (hp : ∀ c ∈ path, c.Holds σ) :
    ∀ c ∈ g, c.Holds σ := fun c hc ↦ by
  obtain ⟨c', hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h c hc)
  rw [CCond.beq_eq he]
  exact hp c' hc'

theorem unU_ok {path : List CCond} (hp : ∀ c ∈ path, c.Holds σ) : ∀ {r0 r : CRes}, unU path r0 = some r →
    r0.Holds σ → r.Holds σ
  | .under g r0, r, h, h0 => by
    simp only [unU] at h
    cases hb : onPath path g with
    | false => rw [hb] at h; cases h
    | true => rw [hb, Bool.cond_true] at h; exact unU_ok hp h (h0 (onPath_ok hb hp))
  | .lt .., _, h, h0 | .nz _, _, h, h0 | .sub .., _, h, h0 | .subR .., _, h, h0 | .subP .., _, h, h0 => by
    simp only [unU, Option.some.injEq] at h
    subst h
    exact h0

/-- **A residual at the site holds.** -/
theorem resAt_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X) {i : ℕ}
    {r : CRes} (h : resAt X i = some r) : r.Holds σ := by
  unfold resAt at h
  cases hg : getF X.res i with
  | none => rw [hg] at h; cases h
  | some r0 => rw [hg] at h; exact unU_ok hX.path h (hX.resF r0 (hX.res i r0 hg))

theorem czero_ok {c : V} (h : σ c = 0) : ∀ d ∈ czero c, d.Holds σ := fun d hd ↦ by
  unfold czero at hd
  cases hk : vnum c with
  | none => rw [hk] at hd; cases hd
  | some k => rw [hk] at hd; rw [List.mem_singleton.mp hd]; show σ (V.n k) = 0; rw [← vnum_eq hk]; exact h

theorem cnz_ok {c : V} (h : σ c ≠ 0) : ∀ d ∈ cnz c, d.Holds σ := fun d hd ↦ by
  unfold cnz at hd
  cases hk : vnum c with
  | none => rw [hk] at hd; cases hd
  | some k => rw [hk] at hd; rw [List.mem_singleton.mp hd]; show σ (V.n k) ≠ 0; rw [← vnum_eq hk]; exact h

theorem carm_ok {x : V} {j : ℕ} (h : σ x = ofK (addressOfIndex j)) : ∀ d ∈ carm x j, d.Holds σ := fun d hd ↦ by
  unfold carm at hd
  cases hk : vnum x with
  | none => rw [hk] at hd; cases hd
  | some k =>
    rw [hk] at hd; rw [List.mem_singleton.mp hd]; show σ (V.n k) = _; rw [← vnum_eq hk]; exact h

theorem idxF_val {env : Trie CCell} (he : EnvOk σ env) (i : CIdx) : (idxF env i).valW (vw σ) = (idxC i).valW (vw σ) := by
  cases i with
  | num n => rfl
  | val k =>
    rw [idxC, valW_baseC, idxF]
    cases hk : getF env k with
    | none => rw [Option.getD_none, valW_baseC]
    | some c => rw [Option.getD_some, ← val_eq, ← he k c hk]; rfl
  | mono c => rfl

theorem ltF_congr {w w' : ℕ → E} {a a' b b' : CCell} (ha : a.valW w = a'.valW w') (hb : b.valW w = b'.valW w') :
    LtF w a b ↔ LtF w' a' b' := by
  simp only [LtF, ha, hb]

theorem expFacts_ok {w : ℕ → E} {m : CCell} {e : ℕ} (hm : m.valW w = ofK (addressOfIndex e)) :
    FOk w (expFacts m e) := by
  unfold expFacts
  cases hb : Nat.blt (e + 1) capE with
  | false => intro p hp; simp at hp
  | true =>
    have he := Nat.blt_eq.mp hb
    have hr : rep (m.valW w) = some e := by rw [hm]; exact rep_of (by omega)
    rw [Bool.cond_true]
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · cases h0 : Nat.beq e 0 with
      | true => rw [h0] at hp; cases hp
      | false =>
        rw [h0] at hp
        rw [List.mem_singleton.mp hp]
        have := Nat.ne_of_beq_eq_false h0
        exact ⟨e - 1, e, rep_const (by omega), hr, by omega⟩
    · rw [List.mem_singleton.mp hp]
      exact ⟨e, e + 1, hr, rep_const he, by omega⟩

theorem baseFacts_ok {w : ℕ → E} {m : CCell} {j : ℕ} (hm : m.valW w = ofK (addressOfIndex j)) :
    FOk w (baseFacts m j) := by
  obtain ⟨bs, t⟩ := m
  unfold baseFacts
  dsimp only
  split
  · rename_i _ b
    cases hle : Nat.ble t j with
    | false => intro p hp; simp at hp
    | true =>
      rw [Bool.cond_true]
      have hle := Nat.le_of_ble_eq_true hle
      refine expFacts_ok ?_
      have hne : ofK (addressOfIndex t) ≠ 0 := fun h ↦
        pow_ne_zero t g_ne_zero (ofK_injective (h.trans (map_zero (algebraMap K E)).symm))
      refine mul_right_cancel₀ hne ?_
      rw [valW_baseC]
      have : w b * ofK (addressOfIndex t) = (⟨[(b, 1)], t⟩ : CCell).valW w := by
        simp [CCell.valW, prodW]
      rw [this, hm, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, Nat.sub_add_cancel hle]
  · intro p hp; simp at hp

/-- **A path's facts hold** where its conditions do. -/
theorem pathF_ok {env : Trie CCell} (he : EnvOk σ env) : ∀ {path : List CCond}, (∀ c ∈ path, c.Holds σ) →
    FOk (vw σ) (pathF env path)
  | [], _ => fun p hp ↦ by simp [pathF] at hp
  | .zero _ :: l, hp => by
    simp only [pathF]; exact pathF_ok he fun c hc ↦ hp c (List.mem_cons_of_mem _ hc)
  | .nonzero _ :: l, hp => by
    simp only [pathF]; exact pathF_ok he fun c hc ↦ hp c (List.mem_cons_of_mem _ hc)
  | .arm x j :: l, hp => by
    have hl := pathF_ok he fun c hc ↦ hp c (List.mem_cons_of_mem _ hc)
    have hx : (idxF env (.val x)).valW (vw σ) = ofK (addressOfIndex j) := by
      rw [idxF_val he, idxC, valW_baseC]; exact hp _ List.mem_cons_self
    simp only [pathF]
    intro p hp'
    rcases List.mem_append.mp hp' with hp' | hp'
    rcases List.mem_append.mp hp' with hp' | hp'
    · exact expFacts_ok hx p hp'
    · exact baseFacts_ok hx p hp'
    · exact hl p hp'

theorem facts_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    {env : Trie CCell} (he : EnvOk σ env) (res : List ℕ) : FOk (vw σ) (facts X env res) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [hX.sig] at hq
    exact (ltF_congr (idxF_val he _) (idxF_val he _)).mpr (hX.term q hq)
  · obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hp
    cases hr : resAt X i with
    | none => rw [hr] at hi; cases hi
    | some c =>
      rw [hr] at hi
      cases c with
      | lt a b =>
        cases hi
        exact (ltF_congr (idxF_val he _) (idxF_val he _)).mpr (resAt_ok hX hr)
      | nz => cases hi
      | sub => cases hi
      | subR => cases hi
      | under => cases hi
      | subP => cases hi
  · exact pathF_ok he hX.path p hp

theorem PRun.beq_eq {a b : PRun} (h : a.beq b = true) : a = b := by
  unfold PRun.beq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h
  obtain ⟨b1, s1, l1, h1⟩ := a
  obtain ⟨b2, s2, l2, h2⟩ := b
  simp only at e1 e2 e3 e4
  rw [CCell.beq_eq e1, Nat.eq_of_beq_eq_true e2, CCell.beq_eq e3, CCell.beq_eq e4]

theorem runF_set {env : Trie CCell} (he : EnvOk σ env) (r : CRun) {x : K} :
    RunSet (vw σ) (runF env r).base (runF env r).stride (runF env r).lo (runF env r).hi x ↔ r.Set (vw σ) x :=
  runSet_congr rfl (idxF_val he _) (idxF_val he _)

/-- **A residual placing a cell in a written run**: the cell written. -/
theorem subPt_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    {env : Trie CCell} (he : EnvOk σ env) {F : List (CCell × CCell)} (hF : FOk (vw σ) F) {res : List ℕ}
    {R : PRun} {c : CCell} (hR : RunF W (vw σ) R.base R.stride R.lo R.hi) (h : subPt X F env res R c = true) :
    W (c.addr σ) := by
  obtain ⟨i, -, hb⟩ := List.any_eq_true.mp h
  split at hb
  · rename_i c' r' hi
    simp only [Bool.and_eq_true] at hb
    rw [← PRun.beq_eq hb.2] at hR
    rw [addr_eq, ← CCell.beq_eq hb.1]
    exact hR _ ((runF_set he r').mpr (resAt_ok (r := .sub c' r') hX hi))
  · rename_i q r' hi
    simp only [Bool.and_eq_true] at hb
    rw [← PRun.beq_eq hb.1] at hR
    have hq := ptRun_ok (W := fun x ↦ RunSet (vw σ) (runF env q).base (runF env q).stride (runF env q).lo
      (runF env q).hi x) hF (fun _ hx ↦ hx) hb.2
    rw [addr_eq]
    exact hR _ ((runF_set he r').mpr (resAt_ok (r := .subR q r') hX hi _ ((runF_set he q).mp hq)))
  · cases hb

/-- **A residual placing a run in a written run**: the run written. -/
theorem subRun_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    {env : Trie CCell} (he : EnvOk σ env) {res : List ℕ} {Q R : PRun}
    (hR : RunF W (vw σ) R.base R.stride R.lo R.hi) (h : subRun X env res Q R = true) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  obtain ⟨i, -, hb⟩ := List.any_eq_true.mp h
  split at hb
  · rename_i q r' hi
    simp only [Bool.and_eq_true] at hb
    rw [← PRun.beq_eq hb.1]
    rw [← PRun.beq_eq hb.2] at hR
    exact fun x hx ↦ hR _ ((runF_set he r').mpr (resAt_ok (r := .subR q r') hX hi _ ((runF_set he q).mp hx)))
  · cases hb

/-- The cell the word under a cell was loaded from: that word at it. -/
theorem srcOf_ok {st : CSt} (hs : StOk rd W σ st) {c a : CCell} (h : srcOf st c = some a) :
    ∃ w, rd (a.addr σ) = some w ∧ c.addr σ = w.limb 0 * addressOfIndex c.off := by
  obtain ⟨bs, o⟩ := c
  unfold srcOf at h
  split at h
  · rename_i b e hb
    simp only at hb
    subst hb
    cases he : Nat.beq e 1 with
    | false => rw [he] at h; cases h
    | true =>
      rw [he, Bool.cond_true] at h
      have he1 := Nat.eq_of_beq_eq_true he
      subst he1
      refine ⟨σ (V.n b), hs.src b a h, ?_⟩
      simp only [CCell.addr, CCell.val, prodB, pow_one, mul_one, limb0_mul_ofK]
  · cases h

/-- A run with constant bounds, the upper at most the lower: no cell. -/
theorem emptyR_ok {w : ℕ → E} {Q : PRun} (h : emptyR Q = true) {x : K} :
    ¬ RunSet w Q.base Q.stride Q.lo Q.hi x := by
  unfold emptyR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hl, hh⟩, hle⟩, hlc⟩ := h
  have hle := Nat.le_of_ble_eq_true hle
  have hlc := Nat.blt_eq.mp hlc
  rintro ⟨ylo, yhi, j, h1, h2, h3, h4, -⟩
  rw [rep_nil hl hlc, Option.some.injEq] at h1
  rw [rep_nil hh (by omega), Option.some.injEq] at h2
  omega

/-- A run with no cell (`emptyE`), the kept equations holding. -/
theorem emptyE_ok {w : ℕ → E} {L : List (CCell × CCell)} (hE : ∀ p ∈ L, p.1.valW w = p.2.valW w) {Q : PRun}
    (h : emptyE L Q = true) {x : K} : ¬ RunSet w Q.base Q.stride Q.lo Q.hi x := by
  unfold emptyE at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact emptyR_ok h
  · rintro ⟨ylo, yhi, j, h1, h2, h3, h4, -⟩
    rw [← eqV_ok hE h, h2, Option.some.injEq] at h1
    omega

theorem ptrSet_sub {a : K} {offs o : List ℕ} (h : subL offs o = true) {x : K} (hx : PtrSet rd a offs x) :
    PtrSet rd a o x := by
  obtain ⟨w, hw, o', ho', rfl⟩ := hx
  obtain ⟨o'', ho'', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h o' ho')
  exact ⟨w, hw, o'', ho'', by rw [Nat.eq_of_beq_eq_true he]⟩

theorem permW_ok {st : CSt} (hs : StOk rd W σ st) : ∀ {cs : List CCell} {ns : List ℕ}, permW st cs ns = true →
    ∀ c ∈ cs, W (c.addr σ)
  | [], [], _, c, hc => by simp at hc
  | c :: cs, n :: ns, h, c0, hc0 => by
    simp only [permW, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hc0 with rfl | hc0
    · cases hn : getF st.sc n with
      | none => rw [hn] at h1; cases h1
      | some c' => rw [hn] at h1; rw [← CCell.beq_eq h1]; exact hs.sc n c' hn
    · exact permW_ok hs h2 c0 hc0
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => by simp [permW] at h

theorem evsW_ok {st : CSt} (hs : StOk rd W σ st) {Q : CCell} {n : ℕ} :
    ∀ {k : ℕ}, evsW st Q n k = true → ∀ t < k, W ((Q.shift t).addr σ)
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | k + 1, h, t, ht => by
    simp only [evsW, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · exact evsW_ok hs h.1 t ht
    · cases hn : getF st.sc (n + t) with
      | none => rw [hn] at h; exact absurd h.2 (by simp)
      | some c' => rw [hn] at h; rw [← CCell.beq_eq h.2]; exact hs.sc _ c' hn

/-- **The run of consecutive write events** written. -/
theorem evs_run {st : CSt} (hs : StOk rd W σ st) {Q : CCell} {n k : ℕ} (h : evsW st Q n k = true)
    (hk : k < capE) : RunF W (vw σ) (evsR Q k).base (evsR Q k).stride (evsR Q k).lo (evsR Q k).hi := by
  rintro x ⟨ylo, yhi, j, -, hhi, -, h2, hx⟩
  rw [show (evsR Q k).hi = ⟨[], k⟩ from rfl, rep_const hk, Option.some.injEq] at hhi
  have := evsW_ok hs h j (by omega)
  rw [addr_eq, CCell.addrW, valW_shift] at this
  rw [hx, show (evsR Q k).base = Q from rfl, show (evsR Q k).stride = 1 from rfl, one_mul]
  exact this

theorem backW_ok {st : CSt} (hs : StOk rd W σ st) {R : PRun} {k : ℕ} :
    ∀ {y0 : ℕ} {ns : List ℕ}, backW st R k y0 ns = true → ∀ i < ns.length,
      R.stride * k ≤ R.base.off + R.stride * (y0 + i) ∧
        W ((⟨R.base.bases, R.base.off + R.stride * (y0 + i) - R.stride * k⟩ : CCell).addr σ)
  | _, [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | y0, n :: ns, h, i, hi => by
    simp only [backW, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases i with
    | zero =>
      refine ⟨by simpa using h1, ?_⟩
      cases hn : getF st.sc n with
      | none => rw [hn] at h2; cases h2
      | some c' => rw [hn] at h2; rw [Nat.add_zero, ← CCell.beq_eq h2]; exact hs.sc n c' hn
    | succ i =>
      have := backW_ok hs h3 i (by simp only [List.length_cons] at hi; omega)
      rwa [show y0 + 1 + i = y0 + (i + 1) by omega] at this

/-- **A cell some indices below a run's upper bound**: in the run, or one of the write events. -/
theorem back_ok {st : CSt} (hs : StOk rd W σ st) {F : List (CCell × CCell)} (hF : FOk (vw σ) F) {R : PRun}
    (hR : RunF W (vw σ) R.base R.stride R.lo R.hi) {c : CCell} {ns : List ℕ} (h : backC F R c ns = true)
    (hw : backW st R (backK R c) 0 ns = true) : W (c.addr σ) := by
  unfold backC at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨hk, hc⟩, hlb⟩, hlc⟩, hex⟩, hlen⟩ := h
  have hlen := Nat.eq_of_beq_eq_true hlen
  set k := backK R c
  obtain ⟨yh, hyh⟩ := hasExp_ok hF hex
  have hhv := (rep_spec hyh).2
  have hcv : c.valW (vw σ) * ofK (addressOfIndex (R.stride * k)) =
      R.base.valW (vw σ) * ofK (addressOfIndex (R.stride * yh)) := by
    rw [← valW_shift, CCell.beq_eq hc, valW_mul, valW_pow, hhv, ← ofK_pow', addressOfIndex, addressOfIndex,
      ← pow_mul, mul_comm yh]
  have hne := ofK_gpow_ne_zero (R.stride * k)
  rcases Nat.lt_or_ge yh (R.lo.off + k) with hlt | hge
  · obtain ⟨hle, hW⟩ := backW_ok hs hw yh (by omega)
    rw [Nat.zero_add] at hle hW
    have hv : c.valW (vw σ) =
        (⟨R.base.bases, R.base.off + R.stride * yh - R.stride * k⟩ : CCell).valW (vw σ) := by
      refine mul_right_cancel₀ hne ?_
      rw [hcv]
      simp only [CCell.valW, mul_assoc, ← ofK_mul', addressOfIndex, ← pow_add]
      rw [Nat.sub_add_cancel hle]
    rw [addr_eq, CCell.addrW, hv, ← CCell.addrW, ← addr_eq]
    exact hW
  · rw [addr_eq]
    refine hR _ ⟨R.lo.off, yh, yh - k, rep_nil hlb hlc, hyh, by omega, by omega, ?_⟩
    have hv : c.valW (vw σ) = R.base.valW (vw σ) * ofK (addressOfIndex (R.stride * (yh - k))) := by
      refine mul_right_cancel₀ hne ?_
      rw [hcv, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, ← Nat.mul_add,
        Nat.sub_add_cancel (by omega : k ≤ yh)]
    rw [CCell.addrW, hv]

/-- **A cell's witness**: the cell written. -/
theorem ptOk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {c : CCell} {w : Wit}
    (h : ptOk X st c w = true) : W (c.addr σ) := by
  induction w generalizing c with
  | ev n =>
    simp only [ptOk] at h
    cases hn : getF st.sc n with
    | none => rw [hn] at h; cases h
    | some c' => rw [hn] at h; rw [← CCell.beq_eq h]; exact hs.sc n c' hn
  | pre k =>
    simp only [ptOk] at h
    cases hk : getF X.pre k with
    | none => rw [hk] at h; cases h
    | some c' => rw [hk] at h; rw [← CCell.beq_eq h]; exact hpre c' (hX.pre k c' hk)
  | run r res =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · rw [addr_eq]
        exact ptRun_ok (facts_ok hX hs.env res) (hs.rs r R hr) h
      · exact subPt_ok hX hs.env (facts_ok hX hs.env res) (hs.rs r R hr) h
  | pf n =>
    simp only [ptOk] at h
    cases hn : getF st.pf n with
    | none => simp [hn] at h
    | some p =>
      cases ha : srcOf st c with
      | none => simp [hn, ha] at h
      | some a =>
        simp only [hn, ha, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨w, hw, hc⟩ := srcOf_ok hs ha
        obtain ⟨o, ho, ho'⟩ := List.any_eq_true.mp h2
        refine hs.pf n p hn _ ⟨w, ?_, o, ho, ?_⟩
        · rw [← CCell.beq_eq h1]; exact hw
        · rw [hc, Nat.eq_of_beq_eq_true ho']
  | pfr r res =>
    simp only [ptOk] at h
    cases hr : getF st.pr r with
    | none => simp [hr] at h
    | some p =>
      cases ha : srcOf st c with
      | none => simp [hr, ha] at h
      | some a =>
        simp only [hr, ha, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨w, hw, hc⟩ := srcOf_ok hs ha
        obtain ⟨o, ho, ho'⟩ := List.any_eq_true.mp h2
        have hR := ptRun_ok (W := fun x ↦ RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi x)
          (facts_ok hX hs.env res) (fun _ hx ↦ hx) h1
        rw [← addr_eq] at hR
        refine hs.pr r p hr _ hR _ ⟨w, hw, o, ho, ?_⟩
        rw [hc, Nat.eq_of_beq_eq_true ho']
  | res => simp [ptOk] at h
  | word => simp [ptOk] at h
  | pts => simp [ptOk] at h
  | empty => simp [ptOk] at h
  | skip => simp [ptOk] at h
  | cat => simp [ptOk] at h
  | mrg => simp [ptOk] at h
  | vp => simp [ptOk] at h
  | catM => simp [ptOk] at h
  | mrgE => simp [ptOk] at h
  | ab => simp [ptOk] at h
  | abx => simp [ptOk] at h
  | perm k ns =>
    simp only [ptOk] at h
    cases hk : resAt X k with
    | none => rw [hk] at h; cases h
    | some r =>
      rw [hk] at h
      cases r with
      | subP c' cs =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨c0, hc0, he⟩ := (resAt_ok hX hk : CRes.Holds σ (.subP c' cs))
        rw [← CCell.beq_eq h1, addr_eq, he, ← addr_eq]
        exact permW_ok hs h2 c0 hc0
      | _ => simp at h
  | prep r q res ih =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.and_eq_true] at h
      rw [addr_eq]
      exact prep_ok (facts_ok hX hs.env res) (hs.rs r R hr) h.1 (by rw [← addr_eq]; exact ih h.2)
  | app r q res ih =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.and_eq_true] at h
      rw [addr_eq]
      exact app_ok (facts_ok hX hs.env res) (hs.rs r R hr) h.1 (by rw [← addr_eq]; exact ih h.2)
  | keep => simp [ptOk] at h
  | prep2 r q q2 res ih ih2 =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.and_eq_true] at h
      rw [addr_eq]
      exact prep2_ok (facts_ok hX hs.env res) (hs.rs r R hr) h.1.1 (by rw [← addr_eq]; exact ih h.1.2)
        (by rw [← addr_eq]; exact ih2 h.2)
  | back r ns res =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.and_eq_true] at h
      exact back_ok hs (facts_ok hX hs.env res) (hs.rs r R hr) h.1 h.2
  | evs n k res =>
    simp only [ptOk] at h
    cases hn : getF st.sc n with
    | none => rw [hn] at h; cases h
    | some Q =>
      rw [hn] at h
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨⟨hk, he⟩, h⟩ := h
      have hR := evs_run hs he hk
      rcases Bool.or_eq_true_iff.mp h with h | h
      · rw [addr_eq]
        exact ptRun_ok (facts_ok hX hs.env res) hR h
      · exact subPt_ok hX hs.env (facts_ok hX hs.env res) hR h
  | der => simp [ptOk] at h
  | wnil => simp [ptOk] at h
  | wcons => simp [ptOk] at h
  | drv => simp [ptOk] at h

/-- **A run's witness**: the run written. -/
theorem rnOk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    {st : CSt} (hs : StOk rd W σ st) {Q : PRun} {w : Wit} (h : rnOk X st Q w = true) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  cases w with
  | run r res =>
    simp only [rnOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact runRun_ok (facts_ok hX hs.env res) hs.eqs (hs.rs r R hr) h
      · exact subRun_ok hX hs.env (hs.rs r R hr) h
      · exact runRunS_ok (facts_ok hX hs.env res) hs.eqs (hs.rs r R hr) h
  | empty =>
    simp only [rnOk] at h
    exact fun x hx ↦ absurd hx (emptyE_ok hs.eqs h)
  | ev => simp [rnOk] at h
  | pre => simp [rnOk] at h
  | res => simp [rnOk] at h
  | pf => simp [rnOk] at h
  | pfr => simp [rnOk] at h
  | word => simp [rnOk] at h
  | pts => simp [rnOk] at h
  | skip => simp [rnOk] at h
  | cat => simp [rnOk] at h
  | mrg => simp [rnOk] at h
  | perm => simp [rnOk] at h
  | prep => simp [rnOk] at h
  | app => simp [rnOk] at h
  | keep => simp [rnOk] at h

  | prep2 => simp [rnOk] at h
  | vp => simp [rnOk] at h
  | catM => simp [rnOk] at h
  | mrgE => simp [rnOk] at h
  | ab => simp [rnOk] at h
  | abx => simp [rnOk] at h
  | evs => simp [rnOk] at h
  | back => simp [rnOk] at h
  | der => simp [rnOk] at h
  | wnil => simp [rnOk] at h
  | wcons => simp [rnOk] at h
  | drv => simp [rnOk] at h

/-- The cells past a word, each witnessed: written. -/
theorem ptsW_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {m : CCell} :
    ∀ {offs : List ℕ} {wl wl' : List Wit}, ptsW X st m offs wl = some wl' → ∀ o ∈ offs, W ((m.shift o).addr σ)
  | [], _, _, _, o, ho => by simp at ho
  | o :: os, [], _, h, _, _ => by simp [ptsW] at h
  | o :: os, w :: wl, wl', h, o0, ho0 => by
    simp only [ptsW] at h
    cases hp : ptOk X st (m.shift o) w with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp, Bool.cond_true] at h
      rcases List.mem_cons.mp ho0 with rfl | ho0
      · exact ptOk_ok hX hpre hs hp
      · exact ptsW_ok hX hpre hs h o0 ho0

theorem lt_offHi {offs : List ℕ} : ∀ {o : ℕ}, o ∈ offs → o < offHi offs := by
  induction offs with
  | nil => intro o ho; cases ho
  | cons a l ih =>
    intro o ho
    have h := @ih o
    simp only [offHi, List.foldr_cons] at h ⊢
    rcases List.mem_cons.mp ho with rfl | ho
    · omega
    · have := h ho; omega

/-- The cells past a word, each witnessed or inside one run witnessed: written. -/
theorem ptsWR_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {m : CCell} {offs : List ℕ}
    {wl wl' : List Wit} (h : ptsWR X st m offs wl = some wl') : ∀ o ∈ offs, W ((m.shift o).addr σ) := by
  rcases wl with _ | ⟨w0, _ | ⟨w, wl⟩⟩
  · exact ptsW_ok hX hpre hs (by simpa only [ptsWR] using h)
  · exact ptsW_ok hX hpre hs (by simpa only [ptsWR] using h)
  · simp only [ptsWR] at h
    cases hb : (w0.isPts && !offs.isEmpty) with
    | false => rw [hb, Bool.cond_false] at h; exact ptsW_ok hX hpre hs h
    | true =>
      rw [hb, Bool.cond_true] at h
      cases hr : (Nat.blt (offHi offs) capE && rnOk X st ⟨m, 1, ⟨[], 0⟩, ⟨[], offHi offs⟩⟩ w) with
      | false => rw [hr] at h; simp at h
      | true =>
        simp only [Bool.and_eq_true, Nat.blt_eq] at hr
        have hR := rnOk_ok hX hs hr.2
        intro o ho
        have hlt := lt_offHi ho
        have hx := hR _ (runSet_of (S := 1) (rep_const (by rw [capE_eq]; norm_num)) (rep_const hr.1) (Nat.zero_le o) hlt)
        rw [addr_eq, CCell.addrW, valW_shift]; simpa only [Nat.one_mul] using hx

/-- **A pointer fact's witness**: the cells past the word at the cell written. -/
theorem ptrOk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {c : CCell} {offs : List ℕ}
    {wl wl' : List Wit} (h : ptrOk X st c offs wl = some wl') : ∀ x, PtrSet rd (c.addr σ) offs x → W x := by
  cases wl with
  | nil => simp [ptrOk] at h
  | cons w wl =>
    cases w
    case pf n =>
      simp only [ptrOk] at h
      cases hn : getF st.pf n with
      | none => simp [hn] at h
      | some p =>
        simp only [hn] at h
        cases hb : (p.1.beq c && subL offs p.2) with
        | false => rw [hb] at h; simp at h
        | true =>
          simp only [Bool.and_eq_true] at hb
          intro x hx
          refine hs.pf n p hn x ?_
          rw [CCell.beq_eq hb.1]
          exact ptrSet_sub hb.2 hx
    case pfr r res =>
      simp only [ptrOk] at h
      cases hr : getF st.pr r with
      | none => simp [hr] at h
      | some p =>
        simp only [hr] at h
        cases hb : (ptRun (facts X st.env res) p.1 c && subL offs p.2) with
        | false => rw [hb] at h; simp at h
        | true =>
          simp only [Bool.and_eq_true] at hb
          have hR := ptRun_ok (W := fun x ↦ RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi x)
            (facts_ok hX hs.env res) (fun _ hx ↦ hx) hb.1
          rw [← addr_eq] at hR
          exact fun x hx ↦ hs.pr r p hr _ hR x (ptrSet_sub hb.2 hx)
    case word m =>
      simp only [ptrOk] at h
      cases hm : getF st.sv m with
      | none => simp [hm] at h
      | some p =>
        simp only [hm] at h
        cases hb : p.1.beq c with
        | false => rw [hb] at h; simp at h
        | true =>
          rw [hb, Bool.cond_true] at h
          have hrd := hs.sv m p hm
          rw [CCell.beq_eq hb] at hrd
          have hcells := ptsWR_ok hX hpre hs h
          rintro x ⟨w, hw, o, ho, rfl⟩
          rw [hrd, Option.some.injEq] at hw
          subst hw
          have := hcells o ho
          rwa [addr_eq, CCell.addrW, valW_shift, limb0_mul_ofK] at this
    all_goals simp [ptrOk] at h

/-- Pointer facts witnessed at a run's cells: written. -/
theorem ptrPts_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {b : CCell} {S : ℕ}
    {offs : List ℕ} : ∀ {j n : ℕ} {wl wl' : List Wit}, ptrPts X st b S offs j n wl = some wl' →
      ∀ i, j ≤ i → i < j + n → ∀ x, PtrSet rd ((b.shift (S * i)).addr σ) offs x → W x
  | _, 0, _, _, _, i, h1, h2 => by omega
  | j, n + 1, wl, wl', h, i, h1, h2 => by
    simp only [ptrPts] at h
    cases hp : ptrOk X st (b.shift (S * j)) offs wl with
    | none => rw [hp] at h; cases h
    | some wl1 =>
      rw [hp] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact ptrOk_ok hX hpre hs hp
      · exact ptrPts_ok hX hpre hs h i (by omega) (by omega)

/-- **A pointer run's witness**: the cells past the word at each of its cells written. -/
theorem ptrROk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {Q : PRun} {offs : List ℕ}
    {wl wl' : List Wit} (h : ptrROk X st Q offs wl = some wl') :
    ∀ a, RunSet (vw σ) Q.base Q.stride Q.lo Q.hi a → ∀ x, PtrSet rd a offs x → W x := by
  cases wl with
  | nil => simp [ptrROk] at h
  | cons w wl =>
    cases w
    case pfr r res =>
      simp only [ptrROk] at h
      cases hr : getF st.pr r with
      | none => simp [hr] at h
      | some p =>
        simp only [hr] at h
        cases hb : (runRun (facts X st.env res) st.eqs Q p.1 && subL offs p.2) with
        | false => rw [hb] at h; simp at h
        | true =>
          simp only [Bool.and_eq_true] at hb
          have hQ := runRun_ok (W := fun a ↦ RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a)
            (facts_ok hX hs.env res) hs.eqs (fun _ hx ↦ hx) hb.1
          exact fun a ha x hx ↦ hs.pr r p hr a (hQ a ha) x (ptrSet_sub hb.2 hx)
    case empty =>
      simp only [ptrROk] at h
      cases hb : emptyE st.eqs Q with
      | false => rw [hb] at h; simp at h
      | true => exact fun a ha ↦ absurd ha (emptyE_ok hs.eqs hb)
    case pts =>
      simp only [ptrROk] at h
      cases hb : constR Q with
      | false => rw [hb] at h; simp at h
      | true =>
        rw [hb, Bool.cond_true] at h
        unfold constR at hb
        simp only [Bool.and_eq_true] at hb
        obtain ⟨⟨⟨hl, hh⟩, hlc⟩, hhc⟩ := hb
        rintro a ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ x hx
        rw [rep_nil hl (Nat.blt_eq.mp hlc), Option.some.injEq] at h1
        rw [rep_nil hh (Nat.blt_eq.mp hhc), Option.some.injEq] at h2
        subst h1 h2
        have := ptrPts_ok hX hpre hs h j h3 (by omega) x
        rw [addr_eq, CCell.addrW, valW_shift] at this
        exact this hx
    all_goals simp [ptrROk] at h

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX}

theorem reqP_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {cs : List CCell} {wl wl' : List Wit}, reqP X st ms cs wl = some wl' → ∀ c ∈ cs, W (c.addrW (slotW ws))
  | [], _, _, _, c, hc => by simp at hc
  | c :: cs, [], _, h, _, _ => by simp [reqP] at h
  | c :: cs, w :: wl, wl', h, c0, hc0 => by
    simp only [reqP] at h
    cases hi : instC ms c with
    | none => rw [hi] at h; cases h
    | some c' =>
      simp only [hi] at h
      cases hp : ptOk X st c' w with
      | false => rw [hp] at h; cases h
      | true =>
        rw [hp, Bool.cond_true] at h
        rcases List.mem_cons.mp hc0 with rfl | hc0
        · have := ptOk_ok hX hpre hs hp
          rwa [addr_eq, CCell.addrW, instC_ok hms hi] at this
        · exact reqP_ok hX hpre hs hms h c0 hc0

/-- Points witnessed at a run's cells: written. -/
theorem ptsRun_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {b : CCell} {S : ℕ} : ∀ {j n : ℕ} {wl wl' : List Wit},
      ptsRun X st b S j n wl = some wl' → ∀ i, j ≤ i → i < j + n → W ((b.shift (S * i)).addr σ)
  | _, 0, _, _, _, i, h1, h2 => by omega
  | j, n + 1, [], _, h, _, _, _ => by simp [ptsRun] at h
  | j, n + 1, w :: wl, wl', h, i, h1, h2 => by
    simp only [ptsRun] at h
    cases hp : ptOk X st (b.shift (S * j)) w with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp, Bool.cond_true] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact ptOk_ok hX hpre hs hp
      · exact ptsRun_ok hX hpre hs h i (by omega) (by omega)

/-- A run's part's witnesses: written. -/
theorem runOk1_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOk1 X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  cases wl with
  | nil => simp [runOk1] at h
  | cons w wl =>
    by_cases hw : w = .pts
    · subst hw
      simp only [runOk1] at h
      cases hb : constR Q with
      | false => rw [hb] at h; simp at h
      | true =>
        rw [hb, Bool.cond_true] at h
        unfold constR at hb
        simp only [Bool.and_eq_true] at hb
        obtain ⟨⟨⟨hl, hh⟩, hlc⟩, hhc⟩ := hb
        rintro a ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩
        rw [rep_nil hl (Nat.blt_eq.mp hlc), Option.some.injEq] at h1
        rw [rep_nil hh (Nat.blt_eq.mp hhc), Option.some.injEq] at h2
        subst h1 h2
        have := ptsRun_ok hX hpre hs h j h3 (by omega)
        rwa [addr_eq, CCell.addrW, valW_shift] at this
    · have h' : (bif rnOk X st Q w then some wl else none) = some wl' := by
        cases w <;> first | exact absurd rfl hw | exact h
      cases hp : rnOk X st Q w with
      | false => rw [hp] at h'; cases h'
      | true => exact rnOk_ok hX hs hp

theorem mrgW_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {S : ℕ} {lo hi : CCell} : ∀ {r n : ℕ} {wl wl' : List Wit},
      mrgW X st Q S lo hi r n wl = some wl' → ∀ r', r ≤ r' → r' < r + n →
        RunF W (vw σ) (mrgPart Q S r' lo hi).base (mrgPart Q S r' lo hi).stride lo hi
  | _, 0, _, _, _, r', h1, h2 => by omega
  | r, n + 1, wl, wl', h, r', h1, h2 => by
    simp only [mrgW] at h
    cases hp : runOk1 X st (mrgPart Q S r lo hi) wl with
    | none => rw [hp] at h; cases h
    | some ws' =>
      rw [hp] at h
      by_cases hr : r' = r
      · subst hr
        exact runOk1_ok hX hpre hs hp
      · exact mrgW_ok hX hpre hs h r' (by omega) (by omega)

/-- **A merge**: a run of stride `S'` whose cells are those of its `S` residue runs of stride `S'·S`, its
lower bound a constant multiple of `S`, its upper bound the `S`-th power of a root with an exponent (the
upper bound's exponent is at most `S` times the root's). -/
theorem mrg_le {Q : PRun} {S : ℕ} {R : CCell} (hS : 0 < S) (hlb : Q.lo.bases.isEmpty = true) (hlc : Q.lo.off < capE)
    {yr : ℕ} (hyr : rep (R.valW (vw σ)) = some yr) (hle : ∀ y, rep (Q.hi.valW (vw σ)) = some y → y ≤ yr * S)
    (hparts : ∀ r < S, RunF W (vw σ) (mrgPart Q S r ⟨[], Q.lo.off / S⟩ R).base
      (mrgPart Q S r ⟨[], Q.lo.off / S⟩ R).stride ⟨[], Q.lo.off / S⟩ R) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  rintro x ⟨ylo, yhi, i, h1, h2, h3, h4, rfl⟩
  rw [rep_nil hlb hlc, Option.some.injEq] at h1
  subst h1
  have hle := hle yhi h2
  have hi : i % S + S * (i / S) = i := Nat.mod_add_div i S
  have hj : i / S < yr := (Nat.div_lt_iff_lt_mul hS).mpr (by omega)
  have hj0 : Q.lo.off / S ≤ i / S := Nat.div_le_div_right h3
  refine hparts (i % S) (Nat.mod_lt _ hS) _ ⟨Q.lo.off / S, yr, i / S, rep_const (by
    have := Nat.div_le_self Q.lo.off S; omega), hyr, hj0, hj, ?_⟩
  simp only [mrgPart]
  rw [valW_shift, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add,
    Nat.mul_assoc, ← Nat.mul_add, hi]

theorem mrg_ok {Q : PRun} {S : ℕ} {R : CCell} (hS : 0 < S) (hlb : Q.lo.bases.isEmpty = true) (hlc : Q.lo.off < capE)
    (hroot : Q.hi.valW (vw σ) = R.valW (vw σ) ^ S) {yr : ℕ} (hyr : rep (R.valW (vw σ)) = some yr)
    (hparts : ∀ r < S, RunF W (vw σ) (mrgPart Q S r ⟨[], Q.lo.off / S⟩ R).base
      (mrgPart Q S r ⟨[], Q.lo.off / S⟩ R).stride ⟨[], Q.lo.off / S⟩ R) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  rintro x ⟨ylo, yhi, i, h1, h2, h3, h4, rfl⟩
  rw [rep_nil hlb hlc, Option.some.injEq] at h1
  subst h1
  have hhi : Q.hi.valW (vw σ) = ofK (addressOfIndex (yr * S)) := by
    rw [hroot, (rep_spec hyr).2, ← ofK_pow', addressOfIndex, addressOfIndex, ← pow_mul]
  have hle := rep_le h2 hhi
  have hi : i % S + S * (i / S) = i := Nat.mod_add_div i S
  have hj : i / S < yr := (Nat.div_lt_iff_lt_mul hS).mpr (by omega)
  have hj0 : Q.lo.off / S ≤ i / S := Nat.div_le_div_right h3
  refine hparts (i % S) (Nat.mod_lt _ hS) _ ⟨Q.lo.off / S, yr, i / S, rep_const (by
    have := Nat.div_le_self Q.lo.off S; omega), hyr, hj0, hj, ?_⟩
  simp only [mrgPart]
  rw [valW_shift, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add,
    Nat.mul_assoc, ← Nat.mul_add, hi]

/-- **A run's witnesses, one level**: the run written. -/
theorem runOk0_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOk0 X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  cases wl with
  | nil => simp [runOk0, runOk1] at h
  | cons w wl =>
    by_cases hw : ∃ k, w = .cat k
    · obtain ⟨k, rfl⟩ := hw
      simp only [runOk0] at h
      cases hk : Nat.blt k capE with
      | false => rw [hk] at h; simp at h
      | true =>
        rw [hk, Bool.cond_true] at h
        split at h
        · rename_i ws1 h1
          have R1 := runOk1_ok hX hpre hs h1
          have R2 := runOk1_ok hX hpre hs h
          have hkc := Nat.blt_eq.mp hk
          rintro x ⟨ylo, yhi, j, h1', h2', h3, h4, rfl⟩
          by_cases hj : j < k
          · exact R1 _ ⟨ylo, k, j, h1', rep_const hkc, h3, hj, rfl⟩
          · exact R2 _ ⟨k, yhi, j, rep_const hkc, h2', by omega, h4, rfl⟩
        · cases h
    · by_cases hm : ∃ S res, w = .mrg S res
      · obtain ⟨S, res, rfl⟩ := hm
        simp only [runOk0] at h
        cases hb : (Nat.blt 0 S && Q.lo.bases.isEmpty && Nat.beq (Q.lo.off % S) 0 && Nat.blt Q.lo.off capE &&
            ((rootC Q.hi S).pow S).beq Q.hi && hasExp (facts X st.env res) (rootC Q.hi S)) with
        | false => rw [hb] at h; simp at h
        | true =>
          rw [hb, Bool.cond_true] at h
          simp only [Bool.and_eq_true] at hb
          obtain ⟨⟨⟨⟨⟨hS, hlb⟩, -⟩, hlc⟩, hroot⟩, hex⟩ := hb
          obtain ⟨yr, hyr⟩ : ∃ yr, rep ((rootC Q.hi S).valW (vw σ)) = some yr := by
            unfold hasExp at hex
            simp only [Bool.or_eq_true, Bool.and_eq_true] at hex
            rcases hex with ⟨h1, h2⟩ | hf
            · exact ⟨_, rep_nil h1 (Nat.blt_eq.mp h2)⟩
            · obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hf
              obtain ⟨ya, yb, ha, hb, -⟩ := facts_ok hX hs.env res p hp
              simp only [Bool.or_eq_true] at hpe
              rcases hpe with he | he
              · rw [CCell.beq_eq he] at ha
                exact ⟨_, ha⟩
              · rw [CCell.beq_eq he] at hb
                exact ⟨_, hb⟩
          exact mrg_ok (Nat.blt_eq.mp hS) hlb (Nat.blt_eq.mp hlc)
            (((valW_pow _ _).symm.trans (congrArg _ (CCell.beq_eq hroot))).symm) hyr
            fun r hr ↦ mrgW_ok hX hpre hs h r (Nat.zero_le _) (by omega)
      · by_cases he : ∃ S r res, w = .mrgE S r res
        · obtain ⟨S, R, res, rfl⟩ := he
          simp only [runOk0] at h
          cases hb : (Nat.blt 0 S && Q.lo.bases.isEmpty && Nat.beq (Q.lo.off % S) 0 && Nat.blt Q.lo.off capE &&
              (eqV st.eqs (R.pow S) Q.hi || hasF (facts X st.env res) Q.hi ((R.pow S).shift 1)) &&
              hasExp (facts X st.env res) R) with
          | false => rw [hb] at h; simp at h
          | true =>
            rw [hb, Bool.cond_true] at h
            simp only [Bool.and_eq_true] at hb
            obtain ⟨⟨⟨⟨⟨hS, hlb⟩, -⟩, hlc⟩, hroot⟩, hex⟩ := hb
            obtain ⟨yr, hyr⟩ := hasExp_ok (facts_ok hX hs.env res) hex
            have hparts := fun r (hr : r < S) ↦ mrgW_ok hX hpre hs h r (Nat.zero_le _) (by omega)
            rcases Bool.or_eq_true_iff.mp hroot with hroot | hroot
            · exact mrg_ok (Nat.blt_eq.mp hS) hlb (Nat.blt_eq.mp hlc)
                (by rw [← eqV_ok hs.eqs hroot, valW_pow]) hyr hparts
            · refine mrg_le (Nat.blt_eq.mp hS) hlb (Nat.blt_eq.mp hlc) hyr (fun y hy ↦ ?_) hparts
              obtain ⟨ya, yb, ha, hb2, hab⟩ := hasF_ok (facts_ok hX hs.env res) hroot
              rw [hy, Option.some.injEq] at ha
              subst ha
              obtain ⟨-, hrv⟩ := rep_spec hyr
              have h2 : ((R.pow S).shift 1).valW (vw σ) = ofK (addressOfIndex (yr * S + 1)) := by
                rw [valW_shift, valW_pow, hrv, ← ofK_pow', ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex,
                  ← pow_mul, ← pow_add]
              have := rep_le hb2 h2
              omega
        · have h' : runOk1 X st Q (w :: wl) = some wl' := by
            cases w <;> first | exact absurd ⟨_, rfl⟩ hw | exact absurd ⟨_, _, rfl⟩ hm | exact absurd ⟨_, _, _, rfl⟩ he | exact h
          exact runOk1_ok hX hpre hs h'

/-- **A split at a symbolic index**: the upper bound's word `k·h`, `k`'s and `h`'s exponents existing, the part
below `k` and the part from `k` (base `base·k^S`, from `g^0` to `h`) written: the run written. -/
theorem catM_ok {w : ℕ → E} {Q : PRun} {k h : CCell} (hkh : (k.mul h).valW w = Q.hi.valW w) {yk yh : ℕ}
    (hyk : rep (k.valW w) = some yk) (hyh : rep (h.valW w) = some yh)
    (R1 : RunF W w Q.base Q.stride Q.lo k) (R2 : RunF W w (Q.base.mul (k.pow Q.stride)) Q.stride ⟨[], 0⟩ h) :
    RunF W w Q.base Q.stride Q.lo Q.hi := by
  rintro x ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩
  have hk := (rep_spec hyk)
  have hh := (rep_spec hyh)
  have hhi : Q.hi.valW w = ofK (addressOfIndex (yk + yh)) := by
    rw [← hkh, valW_mul, hk.2, hh.2, ← ofK_mul', addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
  have hle : yhi = yk + yh := by
    have h2' := h2
    rw [hhi] at h2'
    have := rep_spec h2'
    rw [capE_eq] at hk hh
    rw [capE_eq] at this
    exact (gpow_inj_lt (by omega) (by omega) this.2).symm
  by_cases hj : j < yk
  · exact R1 _ ⟨ylo, yk, j, h1, hyk, h3, hj, rfl⟩
  · refine R2 _ ⟨0, yh, j - yk, rep_const (by rw [capE_eq]; norm_num), hyh, Nat.zero_le _, by omega, ?_⟩
    have e : (Q.base.mul (k.pow Q.stride)).valW w * ofK (addressOfIndex (Q.stride * (j - yk))) =
        Q.base.valW w * ofK (addressOfIndex (Q.stride * j)) := by
      rw [valW_mul, valW_pow, hk.2, ← ofK_pow', mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex,
        addressOfIndex, ← pow_mul, ← pow_add, show yk * Q.stride + Q.stride * (j - yk) = Q.stride * j by
          rw [Nat.mul_comm yk, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)]]
    rw [e]

/-- **A run's witnesses**: the run written. -/
theorem runOkL_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOkL X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  by_cases hc : ∃ k h res wl1, wl = .catM k h res :: wl1
  · obtain ⟨k, hh, res, wl1, rfl⟩ := hc
    simp only [runOkL] at h
    cases hb : (eqV st.eqs (k.mul hh) Q.hi && hasExp (facts X st.env res) k && hasExp (facts X st.env res) hh) with
    | false => rw [hb] at h; simp at h
    | true =>
      rw [hb, Bool.cond_true] at h
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨he, hk⟩, hh'⟩ := hb
      obtain ⟨yk, hyk⟩ := hasExp_ok (facts_ok hX hs.env res) hk
      obtain ⟨yh, hyh⟩ := hasExp_ok (facts_ok hX hs.env res) hh'
      cases h1 : runOk0 X st ⟨Q.base, Q.stride, Q.lo, k⟩ wl1 with
      | none => rw [h1] at h; cases h
      | some ws' =>
        rw [h1] at h
        have R1 := runOk0_ok hX hpre hs h1
        have R2 := runOk0_ok hX hpre hs h
        exact catM_ok (eqV_ok hs.eqs he) hyk hyh R1 R2
  · have h' : runOk0 X st Q wl = some wl' := by
      cases wl with
      | nil => exact h
      | cons w wl1 =>
        cases w <;> first | exact absurd ⟨_, _, _, _, rfl⟩ hc | exact h
    exact runOk0_ok hX hpre hs h'

theorem runOk_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOk X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  by_cases hc : ∃ k h res wl1, wl = .catM k h res :: wl1
  · obtain ⟨k, hh, res, wl1, rfl⟩ := hc
    simp only [runOk] at h
    cases hb : (eqV st.eqs (k.mul hh) Q.hi && hasExp (facts X st.env res) k && hasExp (facts X st.env res) hh) with
    | false => rw [hb] at h; simp at h
    | true =>
      rw [hb, Bool.cond_true] at h
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨he, hk⟩, hh'⟩ := hb
      obtain ⟨yk, hyk⟩ := hasExp_ok (facts_ok hX hs.env res) hk
      obtain ⟨yh, hyh⟩ := hasExp_ok (facts_ok hX hs.env res) hh'
      cases h1 : runOk0 X st ⟨Q.base, Q.stride, Q.lo, k⟩ wl1 with
      | none => rw [h1] at h; cases h
      | some ws' =>
        rw [h1] at h
        have R1 := runOk0_ok hX hpre hs h1
        have R2 := runOkL_ok hX hpre hs h
        exact catM_ok (eqV_ok hs.eqs he) hyk hyh R1 R2
  · have h' : runOk0 X st Q wl = some wl' := by
      cases wl with
      | nil => exact h
      | cons w wl1 =>
        cases w <;> first | exact absurd ⟨_, _, _, _, rfl⟩ hc | exact h
    exact runOk0_ok hX hpre hs h'

/-- **A read's witness** (`ptOkD`): the cell written. -/
theorem ptOkD_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {c : CCell} {w : Wit} (h : ptOkD X st c w = true) : W (c.addr σ) := by
  cases w with
  | der b S lo hi res ws =>
    simp only [ptOkD, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i hr
      rw [addr_eq]
      exact ptRun_ok (facts_ok hX hs.env res) (runOk_ok hX hpre hs hr) h1
    · cases h2
  | _ => exact ptOk_ok hX hpre hs h

/-- **A run needed's witnesses** (`runOkD`): the run written. -/
theorem runOkD_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOkD X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  by_cases hc : ∃ b S lo hi res wl1, wl = .drv b S lo hi res :: wl1
  · obtain ⟨b, S, lo, hi, res, wl1, rfl⟩ := hc
    simp only [runOkD] at h
    split at h
    · rename_i ws' hr
      have hR := runOk_ok hX hpre hs hr
      cases hb : (runRun (facts X st.env res) st.eqs Q ⟨b, S, lo, hi⟩ || subRun X st.env res Q ⟨b, S, lo, hi⟩) with
      | false => rw [hb] at h; cases h
      | true =>
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact runRun_ok (facts_ok hX hs.env res) hs.eqs hR hb
        · exact subRun_ok hX hs.env hR hb
    · cases h
  · have h' : runOk X st Q wl = some wl' := by
      cases wl with
      | nil => exact h
      | cons w wl1 =>
        cases w <;> first | exact absurd ⟨_, _, _, _, _, _, rfl⟩ hc | exact h
    exact runOk_ok hX hpre hs h'

theorem reqR_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {rs : List CRun} {wl wl' : List Wit}, reqR X st ms rs wl = some wl' → ∀ r ∈ rs, r.F W (slotW ws)
  | [], _, _, _, r, hr => by simp at hr
  | r :: rs, wl, wl', h, r0, hr0 => by
    simp only [reqR] at h
    cases hi : instR ms r with
    | none => simp [hi] at h
    | some q =>
      simp only [hi] at h
      cases hp : runOkD X st q wl with
      | none => simp [hp] at h
      | some wl1 =>
        simp only [hp] at h
        rcases List.mem_cons.mp hr0 with rfl | hr0
        · exact (instR_runF hms hi).mp (runOkD_ok hX hpre hs hp)
        · exact reqR_ok hX hpre hs hms h r0 hr0

theorem reqPP_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {ps : List (CCell × List ℕ)} {wl wl' : List Wit}, reqPP X st ms ps wl = some wl' →
      ∀ p ∈ ps, ∀ x, PtrSet rd (p.1.addrW (slotW ws)) p.2 x → W x
  | [], _, _, _, p, hp => by simp at hp
  | p :: ps, wl, wl', h, p0, hp0 => by
    simp only [reqPP] at h
    cases hi : instC ms p.1 with
    | none => simp [hi] at h
    | some c =>
      simp only [hi] at h
      cases hq : ptrOk X st c p.2 wl with
      | none => simp [hq] at h
      | some wl1 =>
        simp only [hq] at h
        rcases List.mem_cons.mp hp0 with rfl | hp0
        · have hc := ptrOk_ok hX hpre hs hq
          rwa [addr_eq, CCell.addrW, instC_ok hms hi] at hc
        · exact reqPP_ok hX hpre hs hms h p0 hp0

theorem reqPR_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {ps : List (CRun × List ℕ)} {wl wl' : List Wit}, reqPR X st ms ps wl = some wl' →
      ∀ p ∈ ps, ∀ a, p.1.Set (slotW ws) a → ∀ x, PtrSet rd a p.2 x → W x
  | [], _, _, _, p, hp => by simp at hp
  | p :: ps, wl, wl', h, p0, hp0 => by
    simp only [reqPR] at h
    cases hi : instR ms p.1 with
    | none => simp [hi] at h
    | some q =>
      simp only [hi] at h
      cases hq : ptrROk X st q p.2 wl with
      | none => simp [hq] at h
      | some wl1 =>
        simp only [hq] at h
        rcases List.mem_cons.mp hp0 with rfl | hp0
        · exact fun a ha ↦ ptrROk_ok hX hpre hs hq a ((instR_set hms hi).mpr ha)
        · exact reqPR_ok hX hpre hs hms h p0 hp0

/-- Pointer facts and runs at the slots, witnessed: written. -/
theorem ptrOk_of {ps : List (CCell × List ℕ)} {prs : List (CRun × List ℕ)} {ws : List E}
    (h1 : ∀ p ∈ ps, ∀ x, PtrSet rd (p.1.addrW (slotW ws)) p.2 x → W x)
    (h2 : ∀ p ∈ prs, ∀ a, p.1.Set (slotW ws) a → ∀ x, PtrSet rd a p.2 x → W x) : PtrOk W rd ps prs ws := by
  rintro x (⟨p, hp, hx⟩ | ⟨p, hp, a, ha, hx⟩)
  · exact h1 p hp x hx
  · exact h2 p hp a ha x hx

theorem reqS_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {G : HSig} {wl wl' : List Wit}
    (h : reqS X st ms G wl = some wl') : SigOk W G.pre G.preR ws ∧ PtrOk W rd G.preP G.prePR ws := by
  unfold reqS at h
  cases h1 : reqP X st ms G.pre wl with
  | none => rw [h1] at h; cases h
  | some wl1 =>
    rw [h1] at h
    dsimp only at h
    cases h2 : reqR X st ms G.preR wl1 with
    | none => rw [h2] at h; cases h
    | some wl2 =>
      rw [h2] at h
      dsimp only at h
      cases h3 : reqPP X st ms G.preP wl2 with
      | none => rw [h3] at h; cases h
      | some wl3 =>
        rw [h3] at h
        exact ⟨⟨reqP_ok hX hpre hs hms h1, reqR_ok hX hpre hs hms h2⟩,
          ptrOk_of (reqPP_ok hX hpre hs hms h3) (reqPR_ok hX hpre hs hms h)⟩

/-- The cells of the words at cells, each witnessed: written. -/
theorem derWs_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) : ∀ {ks : List ℕ} {wl wl' : List Wit}, derWs X st ks wl = some wl' →
      ∀ k ∈ ks, ∀ c, H.ders[k]? = some c → W (c.addrW (vw σ))
  | [], _, _, _, k, hk, _, _ => by simp at hk
  | k :: ks, wl, wl', h, k', hk', c', hc' => by
    cases wl with
    | nil => simp [derWs] at h
    | cons w wl =>
      simp only [derWs] at h
      cases hn : nth X.ders k with
      | none => rw [hn] at h; cases h
      | some c =>
        rw [hn] at h
        dsimp only at h
        cases hb : ptOk X st c w with
        | false => rw [hb] at h; cases h
        | true =>
          rw [hb, Bool.cond_true] at h
          rcases List.mem_cons.mp hk' with rfl | hk'
          · rw [hX.ders, nth_eq, hc', Option.some.injEq] at hn
            subst hn
            rw [← addr_eq]
            exact ptOk_ok hX hpre hs hb
          · exact derWs_ok hX hpre hs h k' hk' c' hc'

/-- A word at a cell, loaded from its cell (`src`), the cell in memory. -/
theorem setSrc_stOk {st : CSt} (hs : StOk rd W σ st) {k : ℕ} {c : CCell} (hd : rd (c.addr σ) = some (σ (V.n k))) :
    StOk rd W σ (st.setSrc k c) := by
  unfold CSt.setSrc
  rw [Trie.seq_eq]
  refine ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, fun k' c' hk' ↦ ?_, hs.pf, hs.pr, hs.cd, hs.eqs, hs.dq⟩
  change getF (setF c Exec.indexDepth st.src k) k' = some c' at hk'
  rcases getF_setF hk' with ⟨rfl, rfl⟩ | hk'
  · exact hd
  · exact hs.src k' c' hk'

/-- **The words at cells loaded from their cells**, those cells in memory. -/
theorem derSt_ok (hX : XOk sigOf H rd f σ X) : ∀ {ks : List ℕ} {st : CSt}, StOk rd W σ st →
    (∀ k ∈ ks, ∀ c, H.ders[k]? = some c → (rd (c.addrW (vw σ))).isSome) → StOk rd W σ (derSt X ks st)
  | [], _, hs, _ => hs
  | k :: ks, st, hs, hd => by
    simp only [derSt]
    have hd' : ∀ k ∈ ks, ∀ c, H.ders[k]? = some c → (rd (c.addrW (vw σ))).isSome :=
      fun k hk ↦ hd k (List.mem_cons_of_mem _ hk)
    cases hn : nth X.ders k with
    | none => exact derSt_ok hX hs hd'
    | some c =>
      dsimp only
      rw [CSt.seq_eq]
      refine derSt_ok hX (setSrc_stOk hs ?_) hd'
      have hc : H.ders[k]? = some c := by rw [← hX.ders, ← nth_eq]; exact hn
      have hsome := hd k List.mem_cons_self c hc
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
      rw [addr_eq, hw]
      exact congrArg some (hX.der k c hc w hw).symm

/-- **A callee's preconditions at a call**, witnessed: the cells its ghost words read written, and, those in
memory, its preconditions written, at its arguments and ghost words. -/
theorem reqG_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ma : List CCell} {args : List V} (hma : MsOk (vw σ) ma (slotW (args.map σ))) (hla : ma.length = args.length)
    {g : String} {wl wl' : List Wit} (h : reqG X st ma g args wl = some wl') : CallReq sigOf H rd σ W g args := by
  unfold reqG at h
  rw [hX.ga] at h
  cases hb : Nat.beq (gargsOf H.gargs g args).length (X.sigOf g).ghosts with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb, Bool.cond_true] at h
    rw [hX.sigOf] at h hb
    cases hw : derWs X st (derKs (gargsOf H.gargs g args)) wl with
    | none => rw [hw] at h; cases h
    | some wl1 =>
      rw [hw] at h
      dsimp only at h
      refine ⟨derWs_ok hX hpre hs hw, fun hd ↦ ?_⟩
      have hms := msOk_append hma (msOk_map (σ := σ) (gargsOf H.gargs g args)) (by simpa using hla)
      exact ⟨Nat.eq_of_beq_eq_true hb, reqS_ok hX hpre (derSt_ok hX hs hd) hms h⟩

/-- A dispatch arm left out: the selector is not its power of `g`. -/
theorem armSkip_ok (hX : XOk sigOf H rd f σ X) {st : CSt} (hs : StOk rd W σ st) {mx : CCell} {j : ℕ}
    {wl wl' : List Wit} (h : armSkip X st mx j wl = some wl') : mx.valW (vw σ) ≠ ofK (addressOfIndex j) := by
  cases wl with
  | nil => simp [armSkip] at h
  | cons w wl =>
    cases w
    case skip res =>
      simp only [armSkip] at h
      cases hb : (Nat.blt j capE && hasFU (facts X st.env res) mx j) with
      | false => rw [hb] at h; simp at h
      | true =>
        simp only [Bool.and_eq_true] at hb
        obtain ⟨hj, hu⟩ := hb
        obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp hu
        simp only [Bool.and_eq_true] at hq
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hq
        obtain ⟨ya, yb, ha, hb', hlt⟩ := facts_ok hX hs.env res p hp
        rw [CCell.beq_eq h1] at ha
        rw [rep_nil h2 (Nat.blt_eq.mp h4), Option.some.injEq] at hb'
        intro he
        rw [he, rep_of (Nat.blt_eq.mp hj), Option.some.injEq] at ha
        have := Nat.le_of_ble_eq_true h3
        omega
    all_goals simp [armSkip] at h

/-- **Guarantees under a selector, pushed**: valid when the selector's word is `g^j`. -/
theorem condSt_ok {mx : CCell} {j : ℕ} (hj : mx.valW (vw σ) = ofK (addressOfIndex j)) {cd : List CdE}
    (hcd : CdOk rd W σ cd) : ∀ (l : List CdE), (∀ e ∈ l, e ∈ cd) → ∀ {st : CSt}, StOk rd W σ st →
      StOk rd W σ (condSt mx j l st)
  | [], _, _, hs => hs
  | e :: l, hl, st, hs => by
    simp only [condSt]
    cases hb : e.mx.beq mx with
    | false => exact condSt_ok hj hcd l (fun e' h ↦ hl e' (List.mem_cons_of_mem _ h)) hs
    | true =>
      rw [Bool.cond_true]
      cases ha : nth e.arms j with
      | none => exact condSt_ok hj hcd l (fun e' h ↦ hl e' (List.mem_cons_of_mem _ h)) hs
      | some a =>
        simp only [CSt.seq_eq]
        obtain ⟨h1, h2, h3, h4⟩ := hcd e (hl e List.mem_cons_self) j a ha
          (by rw [CCell.beq_eq hb]; exact hj)
        exact condSt_ok hj hcd l (fun e' h ↦ hl e' (List.mem_cons_of_mem _ h))
          (pushPRL_ok (pushRL_ok (pushPL_ok (pushL_ok hs (fun _ h ↦ h) h1) (fun _ h ↦ h) h3) (fun _ h ↦ h) h2)
            (fun _ h ↦ h) h4)

end Inv

/-! ## Covered events -/

section Cov

variable {sigOf : String → HSig} {H : HCert} {σ : Val} {rd : Reader}

/-- An address an event of `es` writes. -/
def EW (sigOf : String → HSig) (rd : Reader) (σ : Val) (es : List Ev) (x : K) : Prop := ∃ e ∈ es, EvW sigOf rd σ e x

/-- **The needs of `es` are covered**: each event's in `W` or written by the events before it, once the calls
before it have their callees' returned words (`EvM`, a property of the calls already made). -/
def CovC (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (W : K → Prop) (es : List Ev) : Prop :=
  ∀ es1 e es2, es = es1 ++ e :: es2 → (∀ e' ∈ es1, EvM sigOf rd σ e') →
    ReqOk sigOf H rd σ (fun x ↦ W x ∨ EW sigOf rd σ es1 x) e

/-- The events hold, and each entered call's callee's returned words' monomials (`EvM`). -/
def EvsOk (sigOf : String → HSig) (rd : Reader) (σ : Val) (es : List Ev) : Prop :=
  ∀ e ∈ es, e.Holds rd σ ∧ EvM sigOf rd σ e

/-- The own guarantees written in `W` at the parameters' words `ws0` and the returned `vs`, the
returned words' monomials, and the words at return. -/
def PostW0 (_sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (W : K → Prop)
    (vs : List V) : Prop :=
  SigOk W H.sig.post H.sig.postR (ws0 ++ vs.map σ) ∧ PtrOk W rd H.sig.postP H.sig.postPR (ws0 ++ vs.map σ) ∧
    RetMOk H.sig ws0 (vs.map σ) ∧ RetVOk rd H.sig (ws0 ++ vs.map σ) ∧ RetEqOk H.sig (ws0 ++ vs.map σ) ∧
    (∀ x, QSet rd H.sig.postQ (ws0 ++ vs.map σ) x → W x) ∧
    SigOk W H.sig.postN H.sig.postRN (H.sig.nv.map (vw σ))

/-- **The frame run cells the certificate guarantees at return** (`HCert.fas`), at `σ`. -/
def FAX (H : HCert) (σ : Val) (x : K) : Prop := ∃ p ∈ H.fas, x = cellAt σ (V.n p.1) p.2

/-- `PostW0` in `W` or among the frame run cells guaranteed at return. -/
def PostW (_sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (W : K → Prop) (vs : List V) :
    Prop :=
  PostW0 _sigOf H rd σ ws0 (fun x ↦ W x ∨ FAX H σ x) vs

theorem SigOk.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) {cs : List CCell} {rs : List CRun} {ws : List E}
    (h : SigOk W cs rs ws) : SigOk W' cs rs ws :=
  ⟨fun c hc ↦ hw _ (h.1 c hc), fun r hr ↦ (h.2 r hr).mono hw⟩

theorem ReqOk.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) : ∀ {e : Ev}, ReqOk sigOf H rd σ W e →
    ReqOk sigOf H rd σ W' e
  | .atom _, h => fun x hx ↦ hw x (h x hx)
  | .call .., h => ⟨fun k hk c hc ↦ hw _ (h.1 k hk c hc), fun hd ↦
      ⟨(h.2 hd).1, SigOk.mono hw (h.2 hd).2.1, fun x hx ↦ hw _ ((h.2 hd).2.2 x hx)⟩⟩
  | .inK _, _ => trivial
  | .skip .., _ => trivial

theorem CovC.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) {es : List Ev} (h : CovC sigOf H rd σ W es) :
    CovC sigOf H rd σ W' es :=
  fun es1 e es2 he hm ↦ (h es1 e es2 he hm).mono fun x hx ↦ hx.imp_left (hw x)

theorem covC_nil (W : K → Prop) : CovC sigOf H rd σ W [] := fun es1 _ _ he ↦ by simp at he

theorem ew_append_left {es1 es2 : List Ev} {x : K} (h : EW sigOf rd σ es1 x) : EW sigOf rd σ (es1 ++ es2) x :=
  let ⟨e, he, hx⟩ := h
  ⟨e, List.mem_append_left _ he, hx⟩

theorem ew_append_right {es1 es2 : List Ev} {x : K} (h : EW sigOf rd σ es2 x) : EW sigOf rd σ (es1 ++ es2) x :=
  let ⟨e, he, hx⟩ := h
  ⟨e, List.mem_append_right _ he, hx⟩

theorem ew_append {es1 es2 : List Ev} {x : K} (h : EW sigOf rd σ (es1 ++ es2) x) :
    EW sigOf rd σ es1 x ∨ EW sigOf rd σ es2 x := by
  obtain ⟨e, he, hx⟩ := h
  rcases List.mem_append.mp he with he | he
  · exact Or.inl ⟨e, he, hx⟩
  · exact Or.inr ⟨e, he, hx⟩

theorem covC_append {W : K → Prop} {es1 es2 : List Ev} (h1 : CovC sigOf H rd σ W es1)
    (h2 : (∀ e ∈ es1, EvM sigOf rd σ e) → CovC sigOf H rd σ (fun x ↦ W x ∨ EW sigOf rd σ es1 x) es2) :
    CovC sigOf H rd σ W (es1 ++ es2) := by
  intro p e q he hm
  rcases List.append_eq_append_iff.mp he with ⟨a', rfl, h⟩ | ⟨c', rfl, h⟩
  · refine (h2 (fun e he ↦ hm e (List.mem_append_left _ he)) a' e q h
      (fun e he ↦ hm e (List.mem_append_right _ he))).mono fun x hx ↦ ?_
    rcases hx with (hx | hx) | hx
    · exact Or.inl hx
    · exact Or.inr (ew_append_left hx)
    · exact Or.inr (ew_append_right hx)
  · cases c' with
    | nil =>
      simp only [List.nil_append] at h
      refine (h2 (fun e he ↦ hm e (by simpa using he)) [] e q (by rw [← h]; rfl) (by simp)).mono fun x hx ↦ ?_
      rcases hx with hx | ⟨_, hb, _⟩
      · simpa using hx
      · simp at hb
    | cons e' c'' =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h1 p e c'' rfl hm

theorem covC_single {W : K → Prop} {e : Ev} (h : ReqOk sigOf H rd σ W e) : CovC sigOf H rd σ W [e] := by
  intro p b q he _
  cases p with
  | nil =>
    rw [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact h.mono fun x hx ↦ Or.inl hx
  | cons _ p => simp at he

theorem holds_append {es1 es2 : List Ev} (h : ∀ e ∈ es1 ++ es2, e.Holds rd σ) :
    (∀ e ∈ es1, e.Holds rd σ) ∧ ∀ e ∈ es2, e.Holds rd σ :=
  ⟨fun e he ↦ h e (List.mem_append_left _ he), fun e he ↦ h e (List.mem_append_right _ he)⟩

theorem evsOk_of {es : List Ev} (hh : ∀ e ∈ es, e.Holds rd σ) (hm : ∀ e ∈ es, EvM sigOf rd σ e) :
    EvsOk sigOf rd σ es := fun e he ↦ ⟨hh e he, hm e he⟩

theorem evsOk_append {es1 es2 : List Ev} (h : EvsOk sigOf rd σ (es1 ++ es2)) :
    EvsOk sigOf rd σ es1 ∧ EvsOk sigOf rd σ es2 :=
  ⟨fun e he ↦ h e (List.mem_append_left _ he), fun e he ↦ h e (List.mem_append_right _ he)⟩

/-- **What an outcome gives**: its events holding, its needs covered; returning, each call's returned words
given (`EvsOk`), the own guarantees written. -/
def OutC (sigOf : String → HSig) (H : HCert) (σ : Val) (rd : Reader) (ws0 : List E) (W : K → Prop) (o : Out) :
    Prop :=
  (∀ es, o = .fall es → (∀ e ∈ es, e.Holds rd σ) → CovC sigOf H rd σ W es) ∧
  (∀ es vs, o = .ret es vs → (∀ e ∈ es, e.Holds rd σ) →
    CovC sigOf H rd σ W es ∧ (EvsOk sigOf rd σ es → PostW sigOf H rd σ ws0 (fun x ↦ W x ∨ EW sigOf rd σ es x) vs))

/-- **What a block's pass gives on the path**: its outcome's, and, falling through, the state at
its end valid. -/
def BlockC (sigOf : String → HSig) (H : HCert) (σ : Val) (rd : Reader) (ws0 : List E) (W : K → Prop) (o : Out)
    (st' : CSt) : Prop :=
  OutC sigOf H σ rd ws0 W o ∧
    ∀ es, o = .fall es → EvsOk sigOf rd σ es → StOk rd (fun x ↦ W x ∨ EW sigOf rd σ es x) σ st'

theorem PostW0.mono {ws0 : List E} {W W' : K → Prop} (hw : ∀ x, W x → W' x) {vs : List V}
    (h : PostW0 sigOf H rd σ ws0 W vs) : PostW0 sigOf H rd σ ws0 W' vs :=
  ⟨SigOk.mono hw h.1, fun x hx ↦ hw _ (h.2.1 x hx), h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun x hx ↦ hw _ (h.2.2.2.2.2.1 x hx), SigOk.mono hw h.2.2.2.2.2.2⟩

theorem PostW.mono {ws0 : List E} {W W' : K → Prop} (hw : ∀ x, W x → W' x) {vs : List V}
    (h : PostW sigOf H rd σ ws0 W vs) : PostW sigOf H rd σ ws0 W' vs :=
  PostW0.mono (fun x hx ↦ hx.imp_left (hw x)) h

theorem PostW0.toW {ws0 : List E} {W : K → Prop} {vs : List V} (h : PostW0 sigOf H rd σ ws0 W vs) :
    PostW sigOf H rd σ ws0 W vs :=
  h.mono fun _ ↦ Or.inl

theorem outC_pre {ws0 : List E} {W : K → Prop} {o : Out} (h : OutC sigOf H σ rd ws0 W o) (c : V) :
    OutC sigOf H σ rd ws0 W (o.pre [.inK c]) := by
  have key : ∀ es', CovC sigOf H rd σ W es' → CovC sigOf H rd σ W ([Ev.inK c] ++ es') := fun es' hc ↦
    covC_append (covC_single trivial) fun _ ↦ hc.mono fun _ ↦ Or.inl
  have hew : ∀ es' x, (W x ∨ EW sigOf rd σ es' x) → (W x ∨ EW sigOf rd σ ([Ev.inK c] ++ es') x) := fun es' x hx ↦
    hx.imp_right ew_append_right
  refine ⟨fun es hw hh ↦ ?_, fun es vs hw hh ↦ ?_⟩
  · cases o with
    | fall es' =>
      simp only [Out.pre, Out.fall.injEq] at hw
      subst hw
      exact key es' (h.1 es' rfl (holds_append hh).2)
    | ret => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw
  · cases o with
    | ret es' vs' =>
      simp only [Out.pre, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨h1, h2⟩ := h.2 es' vs' rfl (holds_append hh).2
      exact ⟨key es' h1, fun hm ↦ (h2 (evsOk_append hm).2).mono (hew es')⟩
    | fall => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw

/-- **A statement, then a block.** -/
theorem blockC_seq {ws0 : List E} {W : K → Prop} {o1 : Out} {ss : List Stmt} {st' : CSt}
    {W1 : List Ev → K → Prop} (h1 : OutC sigOf H σ rd ws0 W o1)
    (h2 : ∀ es, o1 = .fall es → EvsOk sigOf rd σ es →
      (∀ x, W1 es x → W x ∨ EW sigOf rd σ es x) ∧ BlockC sigOf H σ rd ws0 (W1 es) (walk σ ss) st') :
    BlockC sigOf H σ rd ws0 W (o1.seq (walk σ ss)) st' := by
  cases o1 with
  | fall es1 =>
    have hW : ∀ es2 x, EvsOk sigOf rd σ es1 → (W1 es1 x ∨ EW sigOf rd σ es2 x) →
        (W x ∨ EW sigOf rd σ (es1 ++ es2) x) := fun es2 x hh hx ↦ by
      rcases hx with hx | hx
      · rcases (h2 es1 rfl hh).1 x hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (ew_append_left hx)
      · exact Or.inr (ew_append_right hx)
    have hcov : ∀ es2, (∀ e ∈ es1 ++ es2, e.Holds rd σ) →
        ((∀ e ∈ es1, EvM sigOf rd σ e) → CovC sigOf H rd σ (W1 es1) es2) →
        CovC sigOf H rd σ W (es1 ++ es2) := fun es2 hh hc ↦
      covC_append (h1.1 es1 rfl (holds_append hh).1)
        fun hm ↦ (hc hm).mono fun x hx ↦ (h2 es1 rfl (evsOk_of (holds_append hh).1 hm)).1 x hx
    refine ⟨⟨fun es hw hh ↦ ?_, fun es vs hw hh ↦ ?_⟩, fun es hw hh ↦ ?_⟩
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | fall es2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.fall.injEq] at hw
        subst hw
        exact hcov es2 hh fun hm ↦
          (h2 es1 rfl (evsOk_of (holds_append hh).1 hm)).2.1.1 es2 hk (holds_append hh).2
      | ret => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | ret es2 vs2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.ret.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨hcov es2 hh fun hm ↦
          ((h2 es1 rfl (evsOk_of (holds_append hh).1 hm)).2.1.2 es2 vs2 hk (holds_append hh).2).1, fun he ↦ ?_⟩
        exact (((h2 es1 rfl (evsOk_append he).1).2.1.2 es2 vs2 hk (holds_append hh).2).2
          (evsOk_append he).2).mono fun x hx ↦ hW es2 x (evsOk_append he).1 hx
      | fall => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | fall es2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.fall.injEq] at hw
        subst hw
        exact ((h2 es1 rfl (evsOk_append hh).1).2.2 es2 hk (evsOk_append hh).2).mono
          fun x hx ↦ hW es2 x (evsOk_append hh).1 hx
      | ret => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
  | ret es1 vs1 =>
    refine ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw hh ↦ ?_⟩, fun es hw _ ↦ by simp [Out.seq] at hw⟩
    simp only [Out.seq, Out.ret.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact h1.2 es1 vs1 rfl hh
  | stuck =>
    exact ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw _ ↦ by simp [Out.seq] at hw⟩,
      fun es hw _ ↦ by simp [Out.seq] at hw⟩

end Cov

/-! ## Statements -/

section Stmts

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader} {W : K → Prop}

theorem bitsOk_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {m : CCell} {dst p : V} {off : ℕ} :
    ∀ {k n : ℕ}, bitsOk X st m dst p off k n = true → ∀ k', k ≤ k' → k' < k + n → W ((m.shift (off + k')).addr σ)
  | _, 0, _, k', h1, h2 => by omega
  | k, n + 1, h, k', h1, h2 => by
    simp only [bitsOk, Bool.and_eq_true] at h
    obtain ⟨h0, hr⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · cases hw : readWitT X.R dst p (off + k) with
      | none => rw [hw] at h0; cases h0
      | some w => rw [hw] at h0; exact ptOk_ok hX hpre hs h0
    · exact bitsOk_ok hX hpre hs hr k' (by omega) (by omega)

theorem atomC_other {st : CSt} {a : Atom} (hl : ∀ d p off, a ≠ .load d p off) (ha : ∀ d x y, a ≠ .add d x y)
    (hm : ∀ d x y, a ≠ .mul d x y) (hg : ∀ p off len nb fl dst, a ≠ .hint (.log2Ceil (.heap p off len) nb fl dst)) :
    atomC0 X st a = (atomH X.toH st.toH a).map st.ofH := by
  cases a with
  | hint h =>
    cases h with
    | log2Ceil bits nb fl dst =>
      cases bits with
      | heap p off len => exact absurd rfl (hg p off len nb fl dst)
      | stack _ => rfl
    | _ => rfl
  | _ => first | rfl | exact absurd rfl (hl _ _ _) | exact absurd rfl (ha _ _ _) | exact absurd rfl (hm _ _ _)

/-- A read through a load event of its cell: the word stored there. -/
theorem hvDef_ok {st : CSt} (hs : StOk rd W σ st) {c : CCell} {d : V} (hd : rd (c.addr σ) = some (σ d)) :
    ∀ w, StOk rd W σ (hvDef X st c d w)
  | .ev n => by
    unfold hvDef
    dsimp only
    cases hk : vnum d with
    | none => exact hs
    | some k =>
      dsimp only
      cases hv : getF X.hv k with
      | none => exact hs
      | some _ =>
      cases hn : getF st.sv n with
      | none => exact hs
      | some p =>
        dsimp only
        cases hb : p.1.beq c with
        | false => exact hs
        | true =>
          refine def_stOk hs ?_
          have := hs.sv n p hn
          rw [CCell.beq_eq hb, hd, Option.some.injEq] at this
          rw [← vnum_eq hk, this, val_eq]
  | .pre _ => hs
  | .run _ _ => hs
  | .res _ => hs
  | .pf _ => hs
  | .pfr _ _ => hs
  | .word _ => hs
  | .pts => hs
  | .empty => hs
  | .skip _ => hs
  | .cat _ => hs
  | .mrg _ _ => hs
  | .perm _ _ => hs
  | .prep _ _ _ => hs
  | .app _ _ _ => hs
  | .keep _ _ _ _ => hs

  | .prep2 _ _ _ _ => hs
  | .vp _ _ => hs
  | .catM _ _ _ => hs
  | .mrgE _ _ _ => hs
  | .ab _ _ _ => hs
  | .abx _ _ _ _ _ => hs
  | .evs _ _ _ => hs
  | .back _ _ _ => hs
  | .der _ _ _ _ _ _ => hs
  | .wnil => hs
  | .wcons _ _ => hs
  | .drv _ _ _ _ _ => hs

/-- **The runs at a word read**: the cell `c` holding `m`'s word, its runs at words into the run scope. -/
theorem promoteQ_ok {st : CSt} (hs : StOk rd W σ st) {c m : CCell} (hm : rd (c.addr σ) = some (m.valW (vw σ))) :
    StOk rd W σ (promoteQ c m st) := by
  unfold promoteQ
  refine pushRL_ok hs (fun _ h ↦ h) fun q hq x hx ↦ ?_
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp hq
  cases hb : p.1.beq c with
  | false => rw [hb] at he; cases he
  | true =>
    rw [hb] at he
    simp only [Bool.cond_true, Option.some.injEq] at he
    subst he
    obtain ⟨ylo, yhi, j, h1, h2, h3, h4, h5⟩ := hx
    refine hs.dq p hp _ (by rw [CCell.beq_eq hb]; exact hm) x ⟨ylo, yhi, j, h1, h2, h3, h4, ?_⟩
    rw [h5, valW_mul]

theorem gwDef_ok {G : HSig} (hG : GwOk G rd σ) {st : CSt} (hs : StOk rd W σ st) {c : CCell} {d : V}
    (hd : rd (c.addr σ) = some (σ d)) : StOk rd W σ (gwDef G st c d) := by
  unfold gwDef
  cases hk : vnum d with
  | none => exact hs
  | some k =>
    cases hp : G.gw.find? (fun p ↦ p.1.beq c) with
    | none => exact hs
    | some p =>
      dsimp only
      refine def_stOk hs ?_
      have hb : p.1.beq c = true := List.find?_some (p := fun q : CCell × ℕ ↦ q.1.beq c) hp
      have hm' : (c, p.2) ∈ G.gw := by
        rw [← CCell.beq_eq hb]
        exact List.mem_of_find?_eq_some hp
      rw [addr_eq] at hd
      rw [val_baseC, ← vnum_eq hk]
      exact (hG c p.2 hm' _ hd).symm

theorem loadPush_ok {st : CSt} (hs : StOk rd W σ st) {W' : K → Prop} (hw : ∀ x, W x → W' x) {c : CCell} {d : V}
    (hc : W' (c.addr σ)) (hd : rd (c.addr σ) = some (σ d)) : StOk rd W' σ (loadPush st c d) := by
  unfold loadPush
  cases hm : monoOf st.env d with
  | none =>
    dsimp only
    rw [CSt.seq_eq]
    exact srcPut_stOk (push_stOk hs hw hc) hd
  | some m =>
    dsimp only
    rw [CSt.seq_eq, CSt.seq_eq]
    have hm' : rd (c.addr σ) = some (m.valW (vw σ)) := by rw [hd, monoOf_ok hs.env hm, val_eq]
    exact promoteQ_ok (srcPut_stOk (pushV_stOk hs hw hc hm') hd) hm'

/-- A division's quotient: its word. -/
theorem divOf_ok {st : CSt} (hs : StOk rd W σ st) {d q b : V} (hq : σ d = σ q * σ b) {k : ℕ} {c : CCell}
    (h : divOf X st d q b = some (k, c)) : σ (V.n k) = c.val σ := by
  unfold divOf at h
  cases hkq : vnum q with
  | none => simp [hkq] at h
  | some kq =>
    cases hdv : getF X.dv kq with
    | none => simp [hkq, hdv] at h
    | some u =>
      cases hkd : vnum d with
      | none => simp [hkq, hdv, hkd] at h
      | some kd =>
        cases hmd : getF st.env kd with
        | none => simp [hkq, hdv, hkd, hmd] at h
        | some md =>
          cases hmb : monoOf st.env b with
          | none => simp [hkq, hdv, hkd, hmd, hmb] at h
          | some mb =>
            simp only [hkq, hdv, hkd, hmd, hmb] at h
            cases hc : (mb.bases.isEmpty && Nat.ble mb.off md.off) with
            | false => rw [hc] at h; simp at h
            | true =>
              rw [hc] at h
              simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [Bool.and_eq_true] at hc
              obtain ⟨hb0, hle⟩ := hc
              have hle := Nat.le_of_ble_eq_true hle
              have hdv' : σ d = md.val σ := by rw [vnum_eq hkd]; exact hs.env kd md hmd
              have hbv : σ b = ofK (addressOfIndex mb.off) := by
                rw [monoOf_ok hs.env hmb, val_eq, valW_nil hb0]
              have hsplit : addressOfIndex md.off = addressOfIndex (md.off - mb.off) * addressOfIndex mb.off := by
                simp only [addressOfIndex, ← pow_add, Nat.sub_add_cancel hle]
              rw [← vnum_eq hkq]
              apply mul_right_cancel₀ (ofK_gpow_ne_zero mb.off)
              rw [← hbv, ← hq, hdv', hbv, CCell.val, CCell.val, hsplit, ofK_mul', mul_assoc]

/-- The returned values' monomials: each the word it is. -/
theorem retDefs_ok {rets : List V} : ∀ {l : List (ℕ × CCell)} {st : CSt}, StOk rd W σ st →
    (∀ k m, (k, m) ∈ l → ∀ r, rets[k]? = some r → σ r = m.valW (vw σ)) → StOk rd W σ (retDefs rets l st)
  | [], _, hs, _ => hs
  | (k, m) :: l, st, hs, hl => by
    have hl' : ∀ k m, (k, m) ∈ l → ∀ r, rets[k]? = some r → σ r = m.valW (vw σ) :=
      fun k m h ↦ hl k m (List.mem_cons_of_mem _ h)
    unfold retDefs
    cases hr : nth rets k with
    | none => exact retDefs_ok hs hl'
    | some r =>
      dsimp only
      cases hk : vnum r with
      | none => exact retDefs_ok hs hl'
      | some kr =>
        simp only [CSt.seq_eq]
        refine retDefs_ok (def_stOk hs ?_) hl'
        rw [← vnum_eq hk, val_eq]
        exact hl k m List.mem_cons_self r (by rw [← nth_eq]; exact hr)

/-- A callee's `retM` at the slots `ms` naming its arguments' words: each returned value its word. -/
theorem instRM_ok {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {G : HSig} {rets : List V}
    (hM : RetMOk G ws (rets.map σ)) :
    ∀ k m, (k, m) ∈ instRM ms G.retM → ∀ r, rets[k]? = some r → σ r = m.valW (vw σ) := by
  intro k m hkm r hr
  obtain ⟨⟨k', c⟩, hc, he⟩ := List.mem_filterMap.mp hkm
  cases hi : instC ms c with
  | none => simp [hi] at he
  | some c' =>
    simp only [hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have h1 := hM k' c hc
    rw [List.getElem?_map, hr, Option.map_some, Option.some.injEq] at h1
    rw [h1, instC_ok hms hi]

/-- A `mul`, not a division: milestone 1's. -/
theorem atomH_part (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} {st1 : HSt}
    {a : Atom} (h1 : atomH X.toH st.toH a = some st1) (hs : StOk rd W σ st) (ha : a.Holds rd σ) :
    (∀ x, Reads H σ a x → W x) ∧ StOk rd (fun x ↦ W x ∨ Writes σ a x) σ (st.ofH st1) := by
  obtain ⟨hr, he, hsc⟩ := atomH_ok (X := X.toH) (H := H) (rd := rd) hX.R hX.pre hX.pows hpre h1 hs.env hs.sc ha
  have h := hs.mono (W' := fun x ↦ W x ∨ Writes σ a x) fun _ ↦ Or.inl
  exact ⟨hr, he, hsc, h.rs, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩

theorem addS_fields (st : CSt) (k : ℕ) (a b : CCell) :
    (st.addS k a b).env = st.env ∧ (st.addS k a b).sc = st.sc ∧ (st.addS k a b).rs = st.rs ∧
      (st.addS k a b).sv = st.sv ∧ (st.addS k a b).src = st.src ∧ (st.addS k a b).pf = st.pf ∧
      (st.addS k a b).pr = st.pr ∧ (st.addS k a b).cd = st.cd ∧ (st.addS k a b).eqs = st.eqs ∧
      (st.addS k a b).dq = st.dq := by
  unfold CSt.addS
  cases getF st.ad k <;> simp [Trie.seq_eq]

theorem addS_adOk {σ : Val} {st : CSt} (had : AdOk σ st.ad) {k : ℕ} {a b : CCell}
    (h : σ (V.n k) = a.valW (vw σ) + b.valW (vw σ)) : AdOk σ (st.addS k a b).ad := by
  unfold CSt.addS
  cases hk : getF st.ad k with
  | some _ => exact had
  | none =>
    simp only [Trie.seq_eq]
    intro k' p hp
    rcases getF_setF hp with ⟨rfl, rfl⟩ | hp
    · exact h
    · exact had k' p hp

/-- **An atom of the path**: its reads in `W`, the state after it valid with its writes. -/
theorem atomC0_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {a : Atom}
    (h : atomC0 X st a = some st') (hs : StOk rd W σ st) (ha : a.Holds rd σ) :
    (∀ x, Reads H σ a x → W x) ∧ StOk rd (fun x ↦ W x ∨ Writes σ a x) σ st' := by
  by_cases hl : ∃ d p off, a = .load d p off
  · obtain ⟨d, p, off, rfl⟩ := hl
    have hrd : rd (cellAt σ p off) = some (σ d) := by simp only [Atom.Holds, LoadHolds] at ha; exact ha.2
    simp only [atomC0] at h
    cases hm : monoOf st.env p with
    | none => rw [hm] at h; cases h
    | some m =>
      simp only [hm, CCell.seq_eq] at h
      have hcell := cellAt_shift σ (monoOf_ok hs.env hm) off
      have hrd' : rd ((m.shift off).addr σ) = some (σ d) := by rw [← hcell]; exact hrd
      have hW : (fun x ↦ W x ∨ Writes σ (.load d p off) x) ((m.shift off).addr σ) :=
        Or.inr (by rw [← hcell]; rfl)
      cases hw : readWitT X.R d p off with
      | none =>
        simp only [hw, Option.some.injEq] at h
        subst h
        refine ⟨fun x hx ↦ ?_, loadPush_ok (gwDef_ok (by rw [hX.sig]; exact hX.gw) hs hrd') (fun _ ↦ Or.inl) hW hrd'⟩
        obtain ⟨hr, -⟩ := hx
        unfold HCert.readWit at hr
        rw [← hX.R, hw] at hr
        cases hr
      | some wt =>
        simp only [hw] at h
        cases hp : ptOkD X st (m.shift off) wt with
        | false => rw [hp] at h; cases h
        | true =>
          simp only [hp, Bool.cond_true, CSt.seq_eq, Option.some.injEq] at h
          subst h
          refine ⟨fun x hx ↦ ?_, loadPush_ok (gwDef_ok (by rw [hX.sig]; exact hX.gw) (hvDef_ok hs hrd' wt) hrd') (fun _ ↦ Or.inl) hW hrd'⟩
          obtain ⟨-, rfl⟩ := hx
          rw [hcell]
          exact ptOkD_ok hX hpre hs hp
  by_cases hd : ∃ d x y, a = .add d x y
  · obtain ⟨d, x, y, rfl⟩ := hd
    refine ⟨fun x hx ↦ by simp [Reads] at hx, ?_⟩
    simp only [atomC0] at h
    cases hk : vnum d with
    | none => simp only [hk, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
    | some k =>
      cases hx : monoOf st.env x with
      | none => simp only [hk, hx, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
      | some mx =>
        cases hy : monoOf st.env y with
        | none => simp only [hk, hx, hy, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
        | some my =>
          simp only [hk, hx, hy, Option.some.injEq] at h
          subst h
          obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := addS_fields st k mx my
          have h := hs.mono (W' := fun z ↦ W z ∨ Writes σ (.add d x y) z) fun _ ↦ Or.inl
          refine ⟨e1 ▸ hs.env, e2 ▸ h.sc, e3 ▸ h.rs, addS_adOk hs.ad ?_, e4 ▸ hs.sv, e5 ▸ hs.src, e6 ▸ h.pf,
            e7 ▸ h.pr, e8 ▸ h.cd, e9 ▸ h.eqs, e10 ▸ h.dq⟩
          rw [← vnum_eq hk, show σ d = σ x + σ y from ha, ← val_eq, ← val_eq, ← monoOf_ok hs.env hx,
              ← monoOf_ok hs.env hy]
  by_cases hmu : ∃ d x y, a = .mul d x y
  · obtain ⟨d, x, y, rfl⟩ := hmu
    have hxy : σ d = σ x * σ y := ha
    simp only [atomC0] at h
    cases h1 : divOf X st d x y with
    | some p =>
      obtain ⟨k, c⟩ := p
      rw [h1, Option.some.injEq] at h
      subst h
      refine ⟨fun x hx ↦ by simp [Reads] at hx, (def_stOk hs ?_).mono fun _ ↦ Or.inl⟩
      exact divOf_ok hs hxy h1
    | none =>
      cases h2 : divOf X st d y x with
      | some p =>
        obtain ⟨k, c⟩ := p
        rw [h1, h2, Option.some.injEq] at h
        subst h
        refine ⟨fun x hx ↦ by simp [Reads] at hx, (def_stOk hs ?_).mono fun _ ↦ Or.inl⟩
        exact divOf_ok hs (by rw [hxy, mul_comm]) h2
      | none =>
        rw [h1, h2] at h
        cases h3 : atomH X.toH st.toH (.mul d x y) with
        | none => rw [h3] at h; cases h
        | some st1 =>
          rw [h3, Option.map_some, Option.some.injEq] at h
          subst h
          exact atomH_part hX hpre h3 hs ha
  by_cases hlg : ∃ p off len nb fl dst, a = .hint (.log2Ceil (.heap p off len) nb fl dst)
  · obtain ⟨p, off, len, nb, fl, dst, rfl⟩ := hlg
    simp only [atomC0] at h
    cases hm : monoOf st.env p with
    | none => rw [hm] at h; cases h
    | some m =>
      rw [hm] at h
      dsimp only at h
      cases hb : bitsOk X st m dst p off 0 (min nb len) with
      | false => rw [hb] at h; cases h
      | true =>
        rw [hb, Bool.cond_true, Option.some.injEq] at h
        subst h
        refine ⟨fun x hx ↦ ?_, hs.mono fun _ ↦ Or.inl⟩
        obtain ⟨k, hk, rfl⟩ := hx
        rw [cellAt_shift σ (monoOf_ok hs.env hm)]
        exact bitsOk_ok hX hpre hs hb k (Nat.zero_le _) (by omega)
  · simp only [not_exists] at hl hd hmu hlg
    rw [atomC_other hl hd hmu hlg] at h
    cases h1 : atomH X.toH st.toH a with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1, Option.map_some, Option.some.injEq] at h
      subst h
      exact atomH_part hX hpre h1 hs ha

theorem addEq_ok {st : CSt} (hs : StOk rd W σ st) {p : CCell × CCell} (hp : p.1.valW (vw σ) = p.2.valW (vw σ)) :
    StOk rd W σ (st.addEq p) :=
  ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, hs.cd,
    fun q hq ↦ (List.mem_cons.mp hq).elim (fun h ↦ h ▸ hp) (hs.eqs q), hs.dq⟩

theorem addEqs_ok {st : CSt} (hs : StOk rd W σ st) {l : List (CCell × CCell)}
    (hl : ∀ p ∈ l, p.1.valW (vw σ) = p.2.valW (vw σ)) : StOk rd W σ (st.addEqs l) :=
  ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, hs.cd,
    fun q hq ↦ (List.mem_append.mp hq).elim (hl q) (hs.eqs q), hs.dq⟩

theorem eqPair_ok {st : CSt} (hs : StOk rd W σ st) {a b : V} (hab : σ a = σ b) : StOk rd W σ (eqPair X st a b) := by
  unfold eqPair
  cases hk : vnum a with
  | none => exact hs
  | some k =>
    dsimp only
    cases h1 : getF X.eqk k with
    | none => exact hs
    | some _ =>
      cases h2 : monoOf st.env a with
      | none => exact hs
      | some ma =>
        cases h3 : monoOf st.env b with
        | none => exact hs
        | some mb =>
          refine addEq_ok hs ?_
          rw [← val_eq, ← val_eq, ← monoOf_ok hs.env h2, ← monoOf_ok hs.env h3, hab]

/-- **An atom's equation kept** holds. -/
theorem eqAt_ok {st : CSt} (hs : StOk rd W σ st) {a : Atom} (ha : a.Holds rd σ) : StOk rd W σ (eqAt X st a) := by
  cases a with
  | mul d x y =>
    have hxy : σ d = σ x * σ y := ha
    cases hk : vnum d with
    | none => simp only [eqAt, hk]; exact hs
    | some k =>
      cases h1 : getF X.eqk k with
      | none => simp only [eqAt, hk, h1]; exact hs
      | some _ =>
        cases h2 : getF st.env k with
        | none => simp only [eqAt, hk, h1, h2]; exact hs
        | some md =>
          cases h3 : monoOf st.env x with
          | none => simp only [eqAt, hk, h1, h2, h3]; exact hs
          | some mx =>
            cases h4 : monoOf st.env y with
            | none => simp only [eqAt, hk, h1, h2, h3, h4]; exact hs
            | some my =>
              simp only [eqAt, hk, h1, h2, h3, h4]
              refine addEq_ok hs ?_
              rw [valW_mul, ← val_eq, ← val_eq, ← val_eq, ← monoOf_ok hs.env h3, ← monoOf_ok hs.env h4,
                ← hs.env k md h2, ← vnum_eq hk, hxy]
  | assertEq x y => exact eqPair_ok hs (CoreMode.char2_eq (show σ x + σ y = 0 from ha))
  | copy d s => exact eqPair_ok hs (show σ d = σ s from ha)
  | _ => exact hs

/-- **An atom**: its reads written; the state after it valid with its writes. -/
theorem atomC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {a : Atom}
    (h : atomC X st a = some st') (hs : StOk rd W σ st) (ha : a.Holds rd σ) :
    (∀ x, Reads H σ a x → W x) ∧ StOk rd (fun x ↦ W x ∨ Writes σ a x) σ st' := by
  unfold atomC at h
  rw [CSt.seq_eq] at h
  have hs0 := eqAt_ok (X := X) hs ha
  generalize eqAt X st a = st0 at h hs0
  cases hl : longRun st0 a with
  | none =>
    rw [hl] at h
    exact atomC0_ok hX hpre h hs0 ha
  | some r =>
    rw [hl, Option.some.injEq] at h
    subst h
    cases a with
    | hint hh =>
      cases hd : hintHeap hh with
      | none => simp [longRun, hd] at hl
      | some t =>
        obtain ⟨p, off, len⟩ := t
        cases hb : Nat.ble 2048 len with
        | false => simp [longRun, hd, hb] at hl
        | true =>
          simp only [longRun, hd, hb, Bool.cond_true] at hl
          obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hl
          refine ⟨fun x hx ↦ ?_, pushR_stOk (hs0.mono fun _ ↦ Or.inl) (fun _ h ↦ h) ?_⟩
          · cases hh <;> simp_all [hintHeap, Reads]
          rintro x ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩
          have hj : j < len := by
            obtain ⟨hyc, -⟩ := rep_spec h2
            rcases Nat.lt_or_ge len capE with hl | hl
            · rw [rep_const hl, Option.some.injEq] at h2
              omega
            · omega
          refine Or.inr ⟨p, off, len, hd, j, hj, ?_⟩
          rw [valW_shift, one_mul, mul_assoc, ← ofK_mul', addressOfIndex, addressOfIndex, ← pow_add, ← val_eq,
            ← monoOf_ok hs0.env hm, cellAt, limb0_mul_ofK, addressOfIndex]
    | _ => simp [longRun] at hl

theorem instPP_ok {ms : List CCell} : ∀ {ps l : List (CCell × List ℕ)}, instPP ms ps = some l →
    ∀ p ∈ l, ∃ p0 ∈ ps, instC ms p0.1 = some p.1 ∧ p.2 = p0.2
  | [], l, h, p, hp => by simp only [instPP, Option.some.injEq] at h; subst h; simp at hp
  | p0 :: ps, l, h, p, hp => by
    simp only [instPP] at h
    cases h1 : instC ms p0.1 with
    | none => simp [h1] at h
    | some c =>
      cases h2 : instPP ms ps with
      | none => simp [h1, h2] at h
      | some l' =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨p0, List.mem_cons_self, h1, rfl⟩
        · obtain ⟨p1, hp1, e⟩ := instPP_ok h2 p hp
          exact ⟨p1, List.mem_cons_of_mem _ hp1, e⟩

theorem instPRL_ok {ms : List CCell} : ∀ {ps : List (CRun × List ℕ)} {l : List (PRun × List ℕ)},
    instPRL ms ps = some l → ∀ p ∈ l, ∃ p0 ∈ ps, instR ms p0.1 = some p.1 ∧ p.2 = p0.2
  | [], l, h, p, hp => by simp only [instPRL, Option.some.injEq] at h; subst h; simp at hp
  | p0 :: ps, l, h, p, hp => by
    simp only [instPRL] at h
    cases h1 : instR ms p0.1 with
    | none => simp [h1] at h
    | some q =>
      cases h2 : instPRL ms ps with
      | none => simp [h1, h2] at h
      | some l' =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨p0, List.mem_cons_self, h1, rfl⟩
        · obtain ⟨p1, hp1, e⟩ := instPRL_ok h2 p hp
          exact ⟨p1, List.mem_cons_of_mem _ hp1, e⟩

/-- A pointer fact at a site: the cells past the word at the signature's cell. -/
theorem ptrSet_inst {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {c c0 : CCell}
    (hi : instC ms c0 = some c) {offs : List ℕ} {x : K} :
    PtrSet rd (c.addr σ) offs x ↔ PtrSet rd (c0.addrW (slotW ws)) offs x := by
  rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hms hi]

/-- **A callee's guarantees pushed**: the state valid with them written. -/
theorem pushPost_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {st st' : CSt}
    (hs : StOk rd W σ st) (h : pushPost G ms st = some st') :
    StOk rd (fun x ↦ W x ∨ PostSet rd G ws x) σ st' := by
  unfold pushPost at h
  cases h1 : instAll ms G.post with
  | none => simp [h1] at h
  | some ps =>
    cases h2 : instPP ms G.postP with
    | none => simp [h1, h2] at h
    | some pps =>
      cases h3 : instAllR ms G.postR with
      | none => simp [h1, h2, h3] at h
      | some rs =>
        cases h4 : instPRL ms G.postPR with
        | none => simp [h1, h2, h3, h4] at h
        | some prs =>
          simp only [h1, h2, h3, h4, Option.some.injEq] at h
          subst h
          refine pushPRL_ok (pushRL_ok (pushPL_ok (pushL_ok hs (fun _ ↦ Or.inl) fun c hc ↦ ?_) (fun _ h ↦ h)
            fun p hp x hx ↦ ?_) (fun _ h ↦ h) fun q hq ↦ ?_) (fun _ h ↦ h) fun p hp a ha x hx ↦ ?_
          · obtain ⟨c0, hc0, hi⟩ := instAll_ok h1 c hc
            refine Or.inr (Or.inl (Or.inl ⟨c0, hc0, ?_⟩))
            rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hms hi]
          · obtain ⟨p0, hp0, hi, he⟩ := instPP_ok h2 p hp
            refine Or.inr (Or.inr (Or.inl (Or.inl ⟨p0, hp0, ?_⟩)))
            rw [← he]
            exact (ptrSet_inst hms hi).mp hx
          · obtain ⟨r0, hr0, hi⟩ := instAllR_ok h3 q hq
            exact fun x hx ↦ Or.inr (Or.inl (Or.inr ⟨r0, hr0, (instR_set hms hi).mp hx⟩))
          · obtain ⟨p0, hp0, hi, he⟩ := instPRL_ok h4 p hp
            refine Or.inr (Or.inr (Or.inl (Or.inr ⟨p0, hp0, a, (instR_set hms hi).mp ha, ?_⟩)))
            rw [← he]
            exact hx

theorem pfBeq_eq {p q : CCell × List ℕ} (h : pfBeq p q = true) : p = q := by
  unfold pfBeq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact Prod.ext (CCell.beq_eq h.1) h.2

theorem prBeq_eq {p q : PRun × List ℕ} (h : prBeq p q = true) : p = q := by
  unfold prBeq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact Prod.ext (PRun.beq_eq h.1) h.2

theorem instArmsP_mem {sigOf : String → HSig} {ms : List CCell} : ∀ {gs : List String}
    {ps : List (List (CCell × List ℕ))} {rs : List (List (PRun × List ℕ))}, instArmsP sigOf ms gs = some (ps, rs) →
    ∀ g ∈ gs, ∃ p ∈ ps, ∃ r ∈ rs, instPP ms (sigOf g).postP = some p ∧ instPRL ms (sigOf g).postPR = some r
  | [], ps, rs, _, g, hg => by simp at hg
  | g :: gs, ps, rs, h, g0, hg0 => by
    simp only [instArmsP] at h
    cases h1 : instPP ms (sigOf g).postP with
    | none => simp [h1] at h
    | some p =>
      cases h2 : instPRL ms (sigOf g).postPR with
      | none => simp [h1, h2] at h
      | some r =>
        cases h3 : instArmsP sigOf ms gs with
        | none => simp [h1, h2, h3] at h
        | some pr =>
          obtain ⟨ps', rs'⟩ := pr
          simp only [h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases List.mem_cons.mp hg0 with rfl | hg0
          · exact ⟨p, List.mem_cons_self, r, List.mem_cons_self, h1, h2⟩
          · obtain ⟨p', hp', r', hr', e1, e2⟩ := instArmsP_mem h3 g0 hg0
            exact ⟨p', List.mem_cons_of_mem _ hp', r', List.mem_cons_of_mem _ hr', e1, e2⟩

/-- **The pointer guarantees every arm gives, pushed**: those of the taken arm. -/
theorem pushPtrM_ok {G : String → HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws))
    {gs : List String} {g : String} (hg : g ∈ gs) {W' : K → Prop} {st : CSt} (hs : StOk rd W' σ st)
    (hW : ∀ x, PostSet rd (G g) ws x → W' x) : StOk rd W' σ (pushPtrM (instArmsP G ms gs) st) := by
  cases hi : instArmsP G ms gs with
  | none => exact hs
  | some pr =>
    obtain ⟨ps, rs⟩ := pr
    cases ps with
    | nil => exact hs
    | cons p ps =>
      cases rs with
      | nil => exact hs
      | cons r rs =>
        obtain ⟨pg, hpg, rg, hrg, e1, e2⟩ := instArmsP_mem hi g hg
        simp only [pushPtrM]
        refine pushPRL_ok (pushPL_ok hs (fun _ h ↦ h) fun q hq x hx ↦ ?_) (fun _ h ↦ h) fun q hq a ha x hx ↦ ?_
        · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
          have hqg : q ∈ pg := by
            rcases List.mem_cons.mp hpg with rfl | hpg
            · exact hq1
            · obtain ⟨q', hq', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hq2 pg hpg)
              rwa [← pfBeq_eq he]
          obtain ⟨p0, hp0, hi0, he⟩ := instPP_ok e1 q hqg
          refine hW x (Or.inr (Or.inl (Or.inl ⟨p0, hp0, ?_⟩)))
          rw [← he]
          exact (ptrSet_inst hms hi0).mp hx
        · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
          have hqg : q ∈ rg := by
            rcases List.mem_cons.mp hrg with rfl | hrg
            · exact hq1
            · obtain ⟨q', hq', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hq2 rg hrg)
              rwa [← prBeq_eq he]
          obtain ⟨p0, hp0, hi0, he⟩ := instPRL_ok e2 q hqg
          refine hW x (Or.inr (Or.inl (Or.inr ⟨p0, hp0, a, (instR_set hms hi0).mp ha, ?_⟩)))
          rw [← he]
          exact hx

theorem svPut_ok : ∀ {l : List (ℕ × CCell × CCell)} {st : CSt}, StOk rd W σ st →
    (∀ p ∈ l, rd (p.2.1.addr σ) = some (p.2.2.valW (vw σ))) → StOk rd W σ (svPut l st)
  | [], _, hs, _ => hs
  | p :: l, st, hs, hl => by
    simp only [svPut, Trie.seq_eq]
    refine svPut_ok ⟨hs.env, hs.sc, hs.rs, hs.ad, fun n q hq ↦ ?_, hs.src, hs.pf, hs.pr, hs.cd, hs.eqs, hs.dq⟩
      fun p' hp' ↦ hl p' (List.mem_cons_of_mem _ hp')
    change getF (setF p.2 Exec.indexDepth st.sv p.1) n = some q at hq
    rcases getF_setF hq with ⟨-, rfl⟩ | hq
    · exact hl p List.mem_cons_self
    · exact hs.sv n q hq

/-- A callee's words at return, at a call: in the final memory. -/
theorem postVE_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) (hv : RetVOk rd G ws)
    {n0 : ℕ} : ∀ p ∈ postVE G ms n0, rd (p.2.1.addr σ) = some (p.2.2.valW (vw σ)) := by
  intro p hp
  obtain ⟨⟨i, m⟩, him, hq⟩ := List.mem_filterMap.mp hp
  dsimp only at hq
  cases hc : nth G.post i with
  | none => rw [hc] at hq; cases hq
  | some c =>
    rw [hc] at hq
    dsimp only at hq
    cases hc' : instC ms c with
    | none => rw [hc'] at hq; cases hq
    | some c' =>
      cases hm' : instC ms m with
      | none => rw [hc', hm'] at hq; cases hq
      | some m' =>
        rw [hc', hm', Option.some.injEq] at hq
        subst hq
        obtain ⟨c0, hc0, hr⟩ := hv i m him
        rw [← nth_eq, hc, Option.some.injEq] at hc0
        subst hc0
        rw [addr_eq, CCell.addrW, instC_ok hms hc', instC_ok hms hm']
        exact hr

/-- A run at a word, its base's and bounds' words given. -/
theorem runSetB_congr {v v' : ℕ → E} {w : E} {b b' lo lo' hi hi' : CCell} {S : ℕ} (hb : b.valW v = b'.valW v')
    (hl : lo.valW v = lo'.valW v') (hh : hi.valW v = hi'.valW v') {x : K} :
    RunSetB v w b S lo hi x ↔ RunSetB v' w b' S lo' hi' x := by
  simp only [RunSetB, hb, hl, hh]

theorem instQ_mem {ms : List CCell} : ∀ {qs : List (CCell × CRun)} {p : CCell × PRun}, p ∈ instQ ms qs →
    ∃ q ∈ qs, instC ms q.1 = some p.1 ∧ instR ms q.2 = some p.2
  | [], _, h => by simp [instQ] at h
  | (c, q) :: l, p, h => by
    simp only [instQ] at h
    cases hc : instC ms c with
    | none =>
      simp only [hc] at h
      obtain ⟨q', hq', h1, h2⟩ := instQ_mem h
      exact ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩
    | some c' =>
      cases hq : instR ms q with
      | none =>
        simp only [hc, hq] at h
        obtain ⟨q', hq', h1, h2⟩ := instQ_mem h
        exact ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩
      | some q' =>
        simp only [hc, hq] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨(c, q), List.mem_cons_self, hc, hq⟩
        · obtain ⟨q'', hq'', h1, h2⟩ := instQ_mem h
          exact ⟨q'', List.mem_cons_of_mem _ hq'', h1, h2⟩

/-- **A callee's runs at words**, instantiated: written where its `PostSet` is, wherever their cells are in
memory. -/
theorem instQ_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {W' : K → Prop}
    (hW : ∀ x, PostSet rd G ws x → W' x) : DqOk rd W' σ (instQ ms G.postQ) := by
  intro p hp w hw x hx
  obtain ⟨q, hq, h1, h2⟩ := instQ_mem hp
  obtain ⟨e1, e2, e3, e4⟩ := instR_ok hms h2
  refine hW x (Or.inr (Or.inr ⟨q, hq, w, ?_, ?_⟩))
  · rw [addr_eq, CCell.addrW, instC_ok hms h1] at hw
    exact hw
  · rw [← e2]
    exact (runSetB_congr e1 e3 e4).mp hx

theorem addDq_ok {st : CSt} (hs : StOk rd W σ st) {l : List (CCell × PRun)} (hl : DqOk rd W σ l) :
    StOk rd W σ (st.addDq l) :=
  ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, hs.cd, hs.eqs,
    fun p hp ↦ (List.mem_append.mp hp).elim (hl p) (hs.dq p)⟩

/-- **A call**: its callee's preconditions written; the state after it valid with its writes. -/
theorem callC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {g : String}
    {args rets : List V} (hs : StOk rd W σ st) (h : callC X st g args rets = some st') :
    CallReq sigOf H rd σ W g args ∧
      (EvM sigOf rd σ (.call g args rets) →
        StOk rd (fun x ↦ W x ∨ EvW sigOf rd σ (.call g args rets) x) σ st') := by
  unfold callC at h
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hc : getF X.C st.nc with
    | none => simp [ha, hc] at h
    | some wl =>
      simp only [ha, hc] at h
      obtain ⟨hma, hla⟩ := monos_ok hs.env args ma ha
      cases hq : reqG X st ma g args wl with
      | none => simp [hq] at h
      | some wl' =>
        have hreq := reqG_ok hX hpre hs hma hla hq
        refine ⟨hreq, fun hM ↦ ?_⟩
        cases wl' with
        | cons _ _ => simp [hq] at h
        | nil =>
          simp only [hq, CSt.seq_eq] at h
          have hs1 := retDefs_ok (rets := rets) hs.nextC (instRM_ok (G := X.sigOf g) hma (by rw [hX.sigOf]; exact hM.1))
          generalize retDefs rets (instRM ma (X.sigOf g).retM) st.nextC = st1 at h hs1
          cases hr : monos st1.env rets with
          | none => simp [hr] at h
          | some mr =>
            simp only [hr] at h
            obtain ⟨hmr, -⟩ := monos_ok hs1.env rets mr hr
            have hm := msOk_append hma hmr (by simpa using hla)
            rw [← List.map_append] at hm
            cases hpp : pushPost (X.sigOf g) (ma ++ mr) st1 with
            | none => rw [hpp] at h; cases h
            | some st2 =>
              rw [hpp, Option.map_some, Option.some.injEq] at h
              subst h
              have := pushPost_ok hm hs1 hpp
              rw [hX.sigOf] at this
              refine addDq_ok (addEqs_ok (svPut_ok this (postVE_ok hm (by rw [hX.sigOf]; exact hM.2.1)))
                fun p hp ↦ ?_) (instQ_ok hm fun x hx ↦ Or.inr (by rw [hX.sigOf] at hx; exact hx))
              obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp hp
              cases h1 : instC (ma ++ mr) q.1 with
              | none => simp [h1] at hqe
              | some a =>
                cases h2 : instC (ma ++ mr) q.2 with
                | none => simp [h1, h2] at hqe
                | some b =>
                  simp only [h1, h2, Option.some.injEq] at hqe
                  subst hqe
                  rw [instC_ok hm h1, instC_ok hm h2]
                  rw [hX.sigOf] at hq
                  exact hM.2.2 q hq

/-- An empty run: its bounds one word. -/
theorem runSet_eq {w : ℕ → E} {b lo hi : CCell} {S : ℕ} (h : lo.valW w = hi.valW w) {x : K} :
    ¬ RunSet w b S lo hi x := by
  rintro ⟨ylo, yhi, j, h1, h2, h3, h4, -⟩
  rw [h, h2, Option.some.injEq] at h1
  omega

theorem cond_some {α : Type} {b : Bool} {x : Option α} {y : α} (h : (bif b then x else none) = some y) :
    b = true ∧ x = some y := by
  cases b <;> simp_all

/-- **An `ite`'s zero branch**: the guard `0`, the equation of its sum kept. -/
theorem zeroEq_ok {st : CSt} (hs : StOk rd W σ st) {c : V} (h0 : σ c = 0) : StOk rd W σ (zeroEq st c) := by
  unfold zeroEq
  cases hsum : sumOf st c with
  | none => exact hs
  | some p =>
    refine addEq_ok hs (CoreMode.char2_eq ?_)
    unfold sumOf at hsum
    cases hk : vnum c with
    | none => rw [hk] at hsum; cases hsum
    | some k =>
      rw [hk] at hsum
      rw [← hs.ad k p hsum, ← vnum_eq hk]
      exact h0

theorem keepL_mem {X : CX} {st : CSt} {qs : List PRun} : ∀ {n : ℕ} {wl : List Wit} {ks : List PRun},
    keepL X st qs n wl = some ks → ∀ q ∈ ks, q ∈ qs
  | _, [], ks, h, q, hq => by simp only [keepL, Option.some.injEq] at h; subst h; simp at hq
  | 0, _ :: _, ks, h, q, hq => by simp [keepL] at h
  | n + 1, w :: wl, ks, h, q, hq => by
    cases w with
    | keep j b lo hi =>
      simp only [keepL] at h
      cases hn : nth qs j with
      | none => simp [hn] at h
      | some q0 =>
        simp only [hn] at h
        obtain ⟨-, h⟩ := cond_some h
        split at h
        · rename_i wl1 _
          obtain ⟨ks1, hk1, rfl⟩ := Option.map_eq_some_iff.mp h
          rcases List.mem_cons.mp hq with rfl | hq
          · rw [nth_eq] at hn
            exact List.mem_of_getElem? hn
          · exact keepL_mem hk1 q hq
        · cases h
    | _ => simp [keepL] at h

theorem keepL_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {qs : List PRun} : ∀ {n : ℕ} {wl : List Wit} {ks : List PRun},
    keepL X st qs n wl = some ks → ∀ q ∈ ks, RunF W (vw σ) q.base q.stride q.lo q.hi
  | _, [], ks, h, q, hq => by simp only [keepL, Option.some.injEq] at h; subst h; simp at hq
  | 0, _ :: _, ks, h, q, hq => by simp [keepL] at h
  | n + 1, w :: wl, ks, h, q, hq => by
    cases w with
    | keep j b lo hi =>
      simp only [keepL] at h
      cases hn : nth qs j with
      | none => simp [hn] at h
      | some q0 =>
        simp only [hn] at h
        obtain ⟨he, h⟩ := cond_some h
        simp only [Bool.and_eq_true] at he
        obtain ⟨⟨hb, hl⟩, hh⟩ := he
        cases hr : runOk X st ⟨b, q0.stride, lo, hi⟩ wl with
        | none => simp [hr] at h
        | some wl1 =>
          simp only [hr] at h
          obtain ⟨ks1, hk1, rfl⟩ := Option.map_eq_some_iff.mp h
          rcases List.mem_cons.mp hq with rfl | hq
          · have h1 := runOk_ok (Q := ⟨b, q.stride, lo, hi⟩) hX hpre hs hr
            exact (runF_congr (eqVM_ok hs.eqs hb).symm (eqVM_ok hs.eqs hl).symm (eqVM_ok hs.eqs hh).symm).mp h1
          · exact keepL_ok hX hpre hs hk1 q hq
    | _ => simp [keepL] at h

/-- **A conditional call** `callIf c g args`: its callee's preconditions written; the state after it valid
with its events' writes (`e`, entered or not). -/
theorem callIfC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {c : V}
    {g : String} {args : List V} (hs : StOk rd W σ st) (h : callIfC X st c g args = some st') :
    (σ c ≠ 0 → CallReq sigOf H rd σ W g args) ∧
      StOk rd (fun x ↦ W x ∨ EW sigOf rd σ [.inK c, if σ c = 0 then .skip g args else .call g args []] x) σ st' := by
  unfold callIfC at h
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hc : getF X.C st.nc with
    | none => simp [ha, hc] at h
    | some wl =>
      simp only [ha, hc] at h
      obtain ⟨hma, hla⟩ := monos_ok hs.env args ma ha
      cases hq : reqG (X.ext (cnz c)) st ma g args wl with
      | none => simp [hq] at h
      | some wl' =>
        have hreq := fun h0 ↦ reqG_ok (hX.ext (cnz_ok h0)) hpre hs hma hla hq
        refine ⟨hreq, ?_⟩
        simp only [hq] at h
        -- the guard is the sum of a run's bounds whose bounds are its operands
        have hcs : ∀ p, sumOf st c = some p → ∀ q : PRun, boundsOf p q = true →
            σ c = q.lo.valW (vw σ) + q.hi.valW (vw σ) := fun p hsum q hq2 ↦ by
          unfold sumOf at hsum
          cases hk : vnum c with
          | none => rw [hk] at hsum; cases hsum
          | some k =>
            rw [hk] at hsum
            rw [vnum_eq hk, hs.ad k p hsum]
            unfold boundsOf at hq2
            simp only [Bool.or_eq_true, Bool.and_eq_true] at hq2
            rcases hq2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [CCell.beq_eq h1, CCell.beq_eq h2]
            · rw [CCell.beq_eq h1, CCell.beq_eq h2, add_comm]
        have hcall : σ c ≠ 0 → ∀ x, PostSet rd (sigOf g) (args.map σ) x →
            EW sigOf rd σ [.inK c, if σ c = 0 then .skip g args else .call g args []] x := fun h0 x hx ↦ by
          refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
          rw [ite_eq_right h0]
          simp only [EvW, List.append_nil]
          exact hx
        cases hsum : sumOf st c with
        | none =>
          simp only [hsum] at h
          obtain ⟨-, h⟩ := cond_some h
          simp only [Option.some.injEq] at h; subst h; exact hs.nextC.mono fun _ ↦ Or.inl
        | some p =>
          cases hqs : instAllR ma (X.sigOf g).postR with
          | none =>
            simp only [hsum, hqs] at h
            obtain ⟨-, h⟩ := cond_some h
            simp only [Option.some.injEq] at h; subst h; exact hs.nextC.mono fun _ ↦ Or.inl
          | some qs =>
            cases hps : instPRL ma (X.sigOf g).postPR with
            | none =>
              simp only [hsum, hqs, hps] at h
              obtain ⟨-, h⟩ := cond_some h
              simp only [Option.some.injEq] at h; subst h; exact hs.nextC.mono fun _ ↦ Or.inl
            | some prs =>
            simp only [hsum, hqs, hps] at h
            cases hk : keepL (X.ext (czero c)) (zeroEq st c) qs wl'.length wl' with
            | none => simp [hk] at h
            | some ks =>
            simp only [hk, Option.some.injEq] at h
            subst h
            refine pushPRL_ok (pushRL_ok hs.nextC (fun _ ↦ Or.inl) (fun q hq x hx ↦ ?_)) (fun _ h ↦ h)
              fun q hq a ha x hx ↦ ?_
            · rcases List.mem_append.mp hq with hq | hq
              swap
              · by_cases h0 : σ c = 0
                · exact Or.inl (keepL_ok (hX.ext (czero_ok h0)) hpre (zeroEq_ok hs h0) hk q hq x hx)
                · obtain ⟨r0, hr0, hi⟩ := instAllR_ok hqs q (keepL_mem hk q hq)
                  rw [hX.sigOf] at hr0
                  exact Or.inr (hcall h0 x (Or.inl (Or.inr ⟨r0, hr0, (instR_set hma hi).mp hx⟩)))
              obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
              by_cases h0 : σ c = 0
              · exact absurd hx (runSet_eq (CoreMode.char2_eq (hcs p hsum q hq2 ▸ h0)))
              · obtain ⟨r0, hr0, hi⟩ := instAllR_ok hqs q hq1
                rw [hX.sigOf] at hr0
                exact Or.inr (hcall h0 x (Or.inl (Or.inr ⟨r0, hr0, (instR_set hma hi).mp hx⟩)))
            · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
              by_cases h0 : σ c = 0
              · exact absurd ha (runSet_eq (CoreMode.char2_eq (hcs p hsum q.1 hq2 ▸ h0)))
              · obtain ⟨p0, hp0, hi, he⟩ := instPRL_ok hps q hq1
                rw [hX.sigOf] at hp0
                refine Or.inr (hcall h0 x (Or.inr (Or.inl (Or.inr ⟨p0, hp0, a, (instR_set hma hi).mp ha, ?_⟩))))
                rw [← he]
                exact hx

theorem instArms_mem {sigOf : String → HSig} {ms : List CCell} : ∀ {gs : List String}
    {ps : List (List CCell)} {rs : List (List PRun)}, instArms sigOf ms gs = some (ps, rs) →
    ∀ g ∈ gs, ∃ p ∈ ps, ∃ r ∈ rs, instAll ms (sigOf g).post = some p ∧ instAllR ms (sigOf g).postR = some r
  | [], ps, rs, _, g, hg => by simp at hg
  | g :: gs, ps, rs, h, g0, hg0 => by
    simp only [instArms] at h
    cases h1 : instAll ms (sigOf g).post with
    | none => simp [h1] at h
    | some p =>
      cases h2 : instAllR ms (sigOf g).postR with
      | none => simp [h1, h2] at h
      | some r =>
        cases h3 : instArms sigOf ms gs with
        | none => simp [h1, h2, h3] at h
        | some pr =>
          obtain ⟨ps', rs'⟩ := pr
          simp only [h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases List.mem_cons.mp hg0 with rfl | hg0
          · exact ⟨p, List.mem_cons_self, r, List.mem_cons_self, h1, h2⟩
          · obtain ⟨p', hp', r', hr', e1, e2⟩ := instArms_mem h3 g0 hg0
            exact ⟨p', List.mem_cons_of_mem _ hp', r', List.mem_cons_of_mem _ hr', e1, e2⟩

/-- A callee's guarantees at a site, instantiated: written where its `PostSet` is. -/
theorem postE_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {cs : List CCell}
    {rs : List PRun} {ps : List (CCell × List ℕ)} {prs : List (PRun × List ℕ)} (h1 : instAll ms G.post = some cs)
    (h2 : instAllR ms G.postR = some rs) (h3 : instPP ms G.postP = some ps) (h4 : instPRL ms G.postPR = some prs)
    {W' : K → Prop} (hW : ∀ x, PostSet rd G ws x → W' x) :
    CdAOk rd W' σ ⟨cs, rs, ps, prs⟩ := by
  refine ⟨fun c hc ↦ ?_, fun q hq x hx ↦ ?_, fun p hp x hx ↦ ?_, fun p hp a ha x hx ↦ ?_⟩
  · obtain ⟨c0, hc0, hi⟩ := instAll_ok h1 c hc
    refine hW _ (Or.inl (Or.inl ⟨c0, hc0, ?_⟩))
    rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hms hi]
  · obtain ⟨r0, hr0, hi⟩ := instAllR_ok h2 q hq
    exact hW x (Or.inl (Or.inr ⟨r0, hr0, (instR_set hms hi).mp hx⟩))
  · obtain ⟨p0, hp0, hi, he⟩ := instPP_ok h3 p hp
    refine hW x (Or.inr (Or.inl (Or.inl ⟨p0, hp0, ?_⟩)))
    rw [← he]
    exact (ptrSet_inst hms hi).mp hx
  · obtain ⟨p0, hp0, hi, he⟩ := instPRL_ok h4 p hp
    refine hW x (Or.inr (Or.inl (Or.inr ⟨p0, hp0, a, (instR_set hms hi).mp ha, ?_⟩)))
    rw [← he]
    exact hx

theorem condE_nth {sigOf : String → HSig} {ms : List CCell} : ∀ {gs : List String} {k : ℕ} {a : CdA},
    nth (condE sigOf ms gs) k = some a → ∃ hk : k < gs.length, a = ⟨[], [], [], []⟩ ∨
      (instAll ms (sigOf gs[k]).post = some a.cs ∧ instAllR ms (sigOf gs[k]).postR = some a.rs ∧
      instPP ms (sigOf gs[k]).postP = some a.ps ∧ instPRL ms (sigOf gs[k]).postPR = some a.prs)
  | [], _, _, he => by simp [condE, nth] at he
  | g :: gs, 0, a, he => by
    simp only [condE, nth, Option.some.injEq] at he
    refine ⟨by simp, ?_⟩
    split at he
    · rename_i cs rs ps prs h1 h2 h3 h4
      subst he
      exact Or.inr ⟨h1, h2, h3, h4⟩
    · exact Or.inl he.symm
  | g :: gs, k + 1, a, he => by
    simp only [condE, nth] at he
    obtain ⟨hk, h⟩ := condE_nth he
    exact ⟨by simpa using hk, by simpa using h⟩

theorem addCd_ok {st : CSt} (hs : StOk rd W σ st) {l : List CdE} (hl : CdOk rd W σ l) : StOk rd W σ (st.addCd l) :=
  ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, fun e he ↦ (List.mem_append.mp he).elim (hs.cd e) (hl e), hs.eqs, hs.dq⟩

/-- **A dispatch's returned pointers hold** in `W'`: each returned word `j`'s cells at the offsets. -/
def VpOk (W' : K → Prop) (σ : Val) (rets : List V) (vps : List (ℕ × List ℕ)) : Prop :=
  ∀ j offs, (j, offs) ∈ vps → ∀ o ∈ offs, ∃ r, rets[j]? = some r ∧ W' ((σ r * ofK (addressOfIndex o)).limb 0)

theorem vpPts_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mr : List CCell} {rets : List V} (hmr : MsOk (vw σ) mr (slotW (rets.map σ))) (hl : mr.length = rets.length) :
    ∀ {vps : List (ℕ × List ℕ)} {wl wl' : List Wit}, vpPts X st mr vps wl = some wl' → VpOk W σ rets vps
  | [], _, _, _ => fun j offs h ↦ by simp at h
  | (j, offs) :: l, wl, wl', h => by
    simp only [vpPts] at h
    cases hm : nth mr j with
    | none => rw [hm] at h; cases h
    | some m =>
      rw [hm] at h
      dsimp only at h
      cases hp : ptsW X st m offs wl with
      | none => rw [hp] at h; cases h
      | some ws' =>
        rw [hp] at h
        intro j' offs' hj o ho
        rcases List.mem_cons.mp hj with he | hj
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          have hm' := hm
          rw [nth_eq] at hm'
          obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.mp hm'
          rw [hl] at hjl
          have hr : rets[j']? = some rets[j'] := List.getElem?_eq_getElem hjl
          refine ⟨rets[j'], hr, ?_⟩
          have := ptsW_ok hX hpre hs hp o ho
          rwa [addr_eq, CCell.addrW, valW_shift, hmr j' m hm, slotW_map_of hr] at this
        · exact vpPts_ok hX hpre hs hmr hl h j' offs' hj o ho

/-- **An arm's returned pointers**: written by the caller's events or the arm's call, where the arm's
callee names its returned words (`RetMOk`). -/
theorem vpArm_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ma : List CCell} {args : List V} (hma : MsOk (vw σ) ma (slotW (args.map σ))) (hla : ma.length = args.length)
    {g : String} {rets : List V} {vps : List (ℕ × List ℕ)} {wl wl' : List Wit}
    (h : vpArm X st ma g rets vps wl = some wl') (hM : RetMOk (sigOf g) (args.map σ) (rets.map σ)) :
    VpOk (fun y ↦ W y ∨ EvW sigOf rd σ (.call g args rets) y) σ rets vps := by
  cases vps with
  | nil => intro j offs h; simp at h
  | cons p vps =>
    unfold vpArm at h
    dsimp only at h
    cases hr : monos st.env rets with
    | none => rw [hr] at h; cases h
    | some mr0 =>
      rw [hr] at h
      dsimp only at h
      obtain ⟨hmr0, hl0⟩ := monos_ok hs.env rets mr0 hr
      rw [hX.sigOf] at h
      obtain ⟨hmr, hlr⟩ := msOk_setRM hmr0 (by simpa using hl0) (l := instRM ma (sigOf g).retM)
        fun k m hkm hk ↦ by
          have hk2 : k < rets.length := by simpa using hk
          have hk' : rets[k]? = some rets[k] := List.getElem?_eq_getElem hk2
          rw [slotW_map_of hk']
          exact (instRM_ok hma hM k m hkm _ hk').symm
      have hm := msOk_append hma hmr (by simpa using hla)
      rw [← List.map_append] at hm
      cases hpp : pushPost (sigOf g) (ma ++ setRM mr0 (instRM ma (sigOf g).retM)) st with
      | none => rw [hpp] at h; cases h
      | some S =>
        rw [hpp] at h
        dsimp only at h
        exact vpPts_ok (hX := hX) (hpre := fun c hc ↦ Or.inl (hpre c hc)) (pushPost_ok hm hs hpp) hmr
          (by simpa using hlr) h

/-- **A dispatch arm `j`'s blocks hold** in `W'`: each run `abArmR j e` written. -/
def AbOk (W' : K → Prop) (σ : Val) (j : ℕ) (abs : List AbE) : Prop :=
  ∀ e ∈ abs, RunF W' (vw σ) (abArmR j e).base (abArmR j e).stride (abArmR j e).lo (abArmR j e).hi

/-- A block's base or bound after the dispatch: at the taken arm `i`, arm `i`'s. -/
theorem abBase_valW {w : ℕ → E} {mx : CCell} {i : ℕ} (hmi : mx.valW w = ofK (addressOfIndex i)) (c : CCell) (a : ℕ) :
    (c.shift (a * i)).valW w = (abBase mx c a).valW w := by
  rw [valW_shift]
  unfold abBase
  cases ha : Nat.beq a 0 with
  | true =>
    obtain rfl := Nat.eq_of_beq_eq_true ha
    rw [Bool.cond_true, Nat.zero_mul, addressOfIndex, pow_zero, show ofK (1 : K) = 1 from map_one (algebraMap K E),
      mul_one]
  | false =>
    rw [Bool.cond_false, valW_mul, valW_pow, hmi, ← ofK_pow', addressOfIndex, addressOfIndex, ← pow_mul,
      Nat.mul_comm a i]

theorem abRuns_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {j : ℕ} : ∀ {abs : List AbE} {wl wl' : List Wit},
      abRuns X st j abs wl = some wl' → AbOk W σ j abs
  | [], _, _, _ => fun p hp ↦ by simp at hp
  | e :: l, wl, wl', h => by
    simp only [abRuns] at h
    cases hr : runOk X st (abArmR j e) wl with
    | none => rw [hr] at h; cases h
    | some ws' =>
      rw [hr] at h
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · have R := runOk_ok hX hpre hs hr
        exact R
      · exact abRuns_ok hX hpre hs h p hp

/-- **An arm's blocks**: written by the caller's events or the arm's call. -/
theorem abArm_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ma : List CCell} {args : List V} (hma : MsOk (vw σ) ma (slotW (args.map σ))) (hla : ma.length = args.length)
    {g : String} {rets : List V} {j : ℕ} {abs : List AbE} {wl wl' : List Wit}
    (h : abArm X st ma g rets j abs wl = some wl') (hM : RetMOk (sigOf g) (args.map σ) (rets.map σ)) :
    AbOk (fun y ↦ W y ∨ EvW sigOf rd σ (.call g args rets) y) σ j abs := by
  cases abs with
  | nil => intro p hp; simp at hp
  | cons p abs =>
    unfold abArm at h
    dsimp only at h
    cases hr : monos st.env rets with
    | none => rw [hr] at h; cases h
    | some mr0 =>
      rw [hr] at h
      dsimp only at h
      obtain ⟨hmr0, hl0⟩ := monos_ok hs.env rets mr0 hr
      rw [hX.sigOf] at h
      obtain ⟨hmr, hlr⟩ := msOk_setRM hmr0 (by simpa using hl0) (l := instRM ma (sigOf g).retM)
        fun k m hkm hk ↦ by
          have hk2 : k < rets.length := by simpa using hk
          have hk' : rets[k]? = some rets[k] := List.getElem?_eq_getElem hk2
          rw [slotW_map_of hk']
          exact (instRM_ok hma hM k m hkm _ hk').symm
      have hm := msOk_append hma hmr (by simpa using hla)
      rw [← List.map_append] at hm
      cases hpp : pushPost (sigOf g) (ma ++ setRM mr0 (instRM ma (sigOf g).retM)) st with
      | none => rw [hpp] at h; cases h
      | some S =>
        rw [hpp] at h
        dsimp only at h
        exact abRuns_ok (hX := hX) (hpre := fun c hc ↦ Or.inl (hpre c hc)) (pushPost_ok hm hs hpp) h

theorem reqArmsX_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {ms : List CCell} {args : List V} (hms : MsOk (vw σ) ms (slotW (args.map σ)))
    (hla : ms.length = args.length) {x : V} {mx : CCell} (hmx : mx.valW (vw σ) = σ x)
    {rets : List V} {vps : List (ℕ × List ℕ)} {abs : List AbE} :
    ∀ {j : ℕ} {gs : List String} {wl wl' : List Wit} {kept : List String},
      reqArmsX X st ms args rets vps abs x mx j gs wl = some (wl', kept) → ∀ i (hi : i < gs.length),
        σ x = ofK (addressOfIndex (j + i)) →
        gs[i] ∈ kept ∧ CallReq sigOf H rd σ W gs[i] args ∧
          (RetMOk (sigOf gs[i]) (args.map σ) (rets.map σ) →
            VpOk (fun y ↦ W y ∨ EvW sigOf rd σ (.call gs[i] args rets) y) σ rets vps) ∧
          (RetMOk (sigOf gs[i]) (args.map σ) (rets.map σ) →
            AbOk (fun y ↦ W y ∨ EvW sigOf rd σ (.call gs[i] args rets) y) σ (j + i) abs)
  | _, [], _, _, _, _, i, hi, _ => by simp at hi
  | j, g :: gs, wl, wl', kept, h, i, hi, hy => by
    simp only [reqArmsX] at h
    cases hk : armSkip X st mx j wl with
    | some ws' =>
      rw [hk] at h
      cases i with
      | zero => exact absurd (hmx.trans hy) (armSkip_ok hX hs hk)
      | succ i =>
        obtain ⟨m, r, v, a⟩ := reqArmsX_ok hX hpre hs hms hla hmx h i (by simpa using hi)
          (by rw [hy, show j + (i + 1) = j + 1 + i by omega])
        simp only [List.getElem_cons_succ]
        refine ⟨m, r, v, ?_⟩
        rw [show j + (i + 1) = j + 1 + i by omega]
        exact a
    | none =>
      rw [hk] at h
      dsimp only at h
      cases hr : reqG (X.ext (carm x j)) (condSt mx j st.cd st) ms g args wl with
      | none => rw [hr] at h; cases h
      | some ws' =>
        rw [hr] at h
        dsimp only at h
        cases hv : vpArm (X.ext (carm x j)) (condSt mx j st.cd st) ms g rets vps ws' with
        | none => rw [hv] at h; cases h
        | some ws'' =>
        rw [hv] at h
        dsimp only at h
        cases ha : abArm (X.ext (carm x j)) (condSt mx j st.cd st) ms g rets j abs ws'' with
        | none => rw [ha] at h; cases h
        | some ws3 =>
        rw [ha] at h
        dsimp only at h
        cases h2 : reqArmsX X st ms args rets vps abs x mx (j + 1) gs ws3 with
        | none => rw [h2] at h; cases h
        | some pr =>
          rw [h2] at h
          obtain ⟨wl2, kept2⟩ := pr
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases i with
          | zero =>
            have hX' := hX.ext (carm_ok (by rw [hy, Nat.add_zero]))
            have hs' := condSt_ok (by rw [hmx, hy, Nat.add_zero]) hs.cd st.cd (fun _ h ↦ h) hs
            exact ⟨List.mem_cons_self, reqG_ok hX' hpre hs' hms hla hr, fun hM ↦ vpArm_ok hX' hpre hs' hms hla hv hM,
              fun hM ↦ abArm_ok hX' hpre hs' hms hla ha hM⟩
          | succ i =>
            obtain ⟨m, r, v, a⟩ := reqArmsX_ok hX hpre hs hms hla hmx h2 i (by simpa using hi)
              (by rw [hy, show j + (i + 1) = j + 1 + i by omega])
            simp only [List.getElem_cons_succ]
            refine ⟨List.mem_cons_of_mem _ m, r, v, ?_⟩
            rw [show j + (i + 1) = j + 1 + i by omega]
            exact a

/-- **A dispatch**: every arm's preconditions written; the state after it valid with the taken arm's
writes. -/
theorem wordAt_ok {G : HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws))
    (hv : RetVOk rd G ws) {c m : CCell} (h : wordAt G ms c = some m) : rd (c.addr σ) = some (m.valW (vw σ)) := by
  unfold wordAt at h
  split at h
  · rename_i p hf
    have hp := List.mem_of_find?_eq_some hf
    have hb := List.find?_some hf
    obtain ⟨cc, hcc, hrd⟩ := hv p.1 p.2 hp
    rw [← nth_eq] at hcc
    simp only [hcc] at hb
    cases hi : instC ms cc with
    | none => rw [hi] at hb; cases hb
    | some c' =>
      rw [hi] at hb
      rw [addr_eq, CCell.addrW, ← CCell.beq_eq hb, instC_ok hms hi, instC_ok hms h]
      exact hrd
  · cases h

theorem armsV_ok {sigOf : String → HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws))
    {gs : List String} {g : String} (hg : g ∈ gs) (hv : RetVOk rd (sigOf g) ws) {c m : CCell}
    (h : armsV sigOf ms gs c = some m) : rd (c.addr σ) = some (m.valW (vw σ)) := by
  cases gs with
  | nil => cases h
  | cons g0 gs' =>
    simp only [armsV] at h
    cases h0 : wordAt (sigOf g0) ms c with
    | none => rw [h0] at h; cases h
    | some m0 =>
      rw [h0] at h
      dsimp only at h
      have key : ∀ b : Bool, (bif b then some m0 else none) = some m → b = true ∧ m0 = m := by
        intro b hb; cases b <;> simp_all
      obtain ⟨hall, rfl⟩ := key _ h
      rcases List.mem_cons.mp hg with rfl | hg
      · exact wordAt_ok hms hv h0
      · have := List.all_eq_true.mp hall g hg
        cases hw : wordAt (sigOf g) ms c with
        | none => rw [hw] at this; cases this
        | some m' =>
          rw [hw] at this
          dsimp only at this
          rw [← CCell.beq_eq this]
          exact wordAt_ok hms hv hw

theorem meetVL_ok {sigOf : String → HSig} {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws))
    {gs : List String} {g : String} (hg : g ∈ gs) (hv : RetVOk rd (sigOf g) ws) :
    ∀ (cs : List CCell) (n : ℕ), ∀ q ∈ meetVL sigOf ms gs cs n, rd (q.2.1.addr σ) = some (q.2.2.valW (vw σ))
  | [], _, q, hq => by simp [meetVL] at hq
  | c :: cs, n, q, hq => by
    unfold meetVL at hq
    cases ha : armsV sigOf ms gs c with
    | none => rw [ha] at hq; exact meetVL_ok hms hg hv cs (n + 1) q hq
    | some m =>
      rw [ha] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact armsV_ok hms hg hv ha
      · exact meetVL_ok hms hg hv cs (n + 1) q hq

theorem dispC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt}
    {x : V} {fs : List String} {args rets : List V} (hs : StOk rd W σ st)
    (h : dispC X st x fs args rets = some st') :
    ∀ i (hi : i < fs.length), σ x = ofK (addressOfIndex i) →
      CallReq sigOf H rd σ W fs[i] args ∧
      (EvM sigOf rd σ (.call fs[i] args rets) →
        StOk rd (fun x' ↦ W x' ∨ EvW sigOf rd σ (.call fs[i] args rets) x') σ st') := by
  intro i hi hxi
  unfold dispC at h
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hmx : monoOf st.env x with
    | none => simp [ha, hmx] at h
    | some mx =>
      cases hc : getF X.C st.nc with
      | none => simp [ha, hmx, hc] at h
      | some wl =>
        simp only [ha, hmx, hc] at h
        obtain ⟨hma, hla⟩ := monos_ok hs.env args ma ha
        cases hq : reqArmsX X st ma args rets (vpHead wl).1 (abHead (vpHead wl).2).1 x mx 0 fs
            (abHead (vpHead wl).2).2 with
        | none => simp [hq] at h
        | some pr =>
          obtain ⟨wl', kept⟩ := pr
          obtain ⟨hgk, hreq, hvp, hab⟩ := reqArmsX_ok hX hpre hs hma hla
            (by rw [← val_eq, ← monoOf_ok hs.env hmx]) hq i hi (by simpa using hxi)
          refine ⟨hreq, fun hM ↦ ?_⟩
          have hmxv : mx.valW (vw σ) = σ x := by rw [← val_eq, ← monoOf_ok hs.env hmx]
          have hvp := hvp hM.1
          have hab := hab hM.1
          generalize hgi : fs[i] = g at hgk hM hvp hab ⊢
          cases wl' with
          | cons _ _ => simp [hq] at h
          | nil =>
            cases kept with
            | nil => simp at hgk
            | cons g0 gs =>
            have hg := hgk
            simp only [hq, CSt.seq_eq] at h
            -- the returned words' monomials every arm gives, the taken arm's among them
            have hs1 := retDefs_ok (rets := rets) (l := (instRM ma (X.sigOf g0).retM).filter
                (meetM (gs.map fun g' ↦ instRM ma (X.sigOf g').retM))) hs.nextC fun k m hkm ↦ by
              obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hkm
              have hg' : (k, m) ∈ instRM ma (X.sigOf g).retM := by
                rcases List.mem_cons.mp hg with rfl | hg
                · exact hk1
                · obtain ⟨q, hq', he⟩ := List.any_eq_true.mp
                    (List.all_eq_true.mp hk2 _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
                  simp only [Bool.and_eq_true] at he
                  obtain ⟨e1, e2⟩ := he
                  obtain ⟨k', m'⟩ := q
                  simp only at e1 e2
                  rwa [Nat.eq_of_beq_eq_true e1, CCell.beq_eq e2] at hq'
              exact instRM_ok (G := X.sigOf g) hma (by rw [hX.sigOf]; exact hM.1) k m hg'
            generalize retDefs rets _ st.nextC = st1 at h hs1
            cases hr : monos st1.env rets with
            | none => simp [hr] at h
            | some mr =>
            simp only [hr] at h
            obtain ⟨hmr, -⟩ := monos_ok hs1.env rets mr hr
            have hmr' := hmr
            have hm := msOk_append hma hmr (by simpa using hla)
            rw [← List.map_append] at hm
            cases hi : instArms X.sigOf (ma ++ mr) (g0 :: gs) with
            | none => simp [hi] at h
            | some pr =>
              obtain ⟨ps, rs⟩ := pr
              cases ps with
              | nil => simp [hi] at h
              | cons p ps =>
                cases rs with
                | nil => simp [hi] at h
                | cons r rs =>
                  simp only [hi, Option.some.injEq] at h
                  subst h
                  obtain ⟨pg, hpg, rg, hrg, e1, e2⟩ := instArms_mem hi g hg
                  rw [hX.sigOf] at e1 e2
                  refine addCd_ok ?_ ?_
                  swap
                  · cases hb : Nat.blt fs.length capE with
                    | false => intro e he; simp at he
                    | true =>
                      intro e he k a ha hj
                      rw [Bool.cond_true, List.mem_singleton] at he
                      subst he
                      obtain ⟨hk, ha'⟩ := condE_nth ha
                      have hlt := Nat.blt_eq.mp hb
                      rw [capE_eq] at hlt
                      have hki : k = i := gpow_inj_lt (by omega) (by omega)
                        (by rw [← hj, hmxv, hxi])
                      subst hki
                      rcases ha' with rfl | ⟨e1', e2', e3', e4'⟩
                      · exact ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h, fun _ h ↦ by simp at h,
                          fun _ h ↦ by simp at h⟩
                      rw [hgi, hX.sigOf] at e1' e2' e3' e4'
                      exact postE_ok hm e1' e2' e3' e4' (fun x hx ↦ Or.inr hx)
                  refine pushRL_ok ?_ (fun _ h ↦ h) fun q hq ↦ ?_
                  swap
                  · -- the blocks' runs: the taken arm's, its index the selector's exponent
                    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
                    have hmi : mx.valW (vw σ) = ofK (addressOfIndex i) := by rw [hmxv, hxi]
                    obtain ⟨q0, a, S, h0, b⟩ := e
                    have h1 := hab _ he
                    simp only [abArmR, Nat.zero_add] at h1
                    exact (runF_congr (abBase_valW hmi q0 a) rfl (abBase_valW hmi h0 b)).mp h1
                  refine pushL_ok (pushPtrM_ok hm hg ?_ fun x hx ↦ Or.inr (by rw [← hX.sigOf]; exact hx))
                    (fun _ h ↦ h) fun c hc ↦ ?_
                  swap
                  · -- the returned pointers' cells
                    obtain ⟨⟨j, offs⟩, hp, hc⟩ := List.mem_flatMap.mp hc
                    cases hn : nth mr j with
                    | none => simp [hn] at hc
                    | some m =>
                      simp only [hn] at hc
                      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
                      obtain ⟨r, hr', hw⟩ := hvp j offs hp o ho
                      rwa [addr_eq, CCell.addrW, valW_shift, hmr' j m hn, slotW_map_of hr']
                  refine pushRL_ok (svPut_ok (pushL_ok hs1 (fun _ ↦ Or.inl) fun c hc ↦ ?_) ?_) (fun _ h ↦ h)
                    fun q hq ↦ ?_
                  pick_goal 2
                  · exact meetVL_ok hm hg (by rw [hX.sigOf]; exact hM.2.1) _ _
                  · obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
                    have hcg : c ∈ pg := by
                      rcases List.mem_cons.mp hpg with rfl | hpg
                      · exact hc1
                      · obtain ⟨c', hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc2 pg hpg)
                        rwa [← CCell.beq_eq he]
                    obtain ⟨c0, hc0, hi0⟩ := instAll_ok e1 c hcg
                    refine Or.inr (Or.inl (Or.inl ⟨c0, hc0, ?_⟩))
                    rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hm hi0]
                  · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
                    have hqg : q ∈ rg := by
                      rcases List.mem_cons.mp hrg with rfl | hrg
                      · exact hq1
                      · obtain ⟨q', hq', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hq2 rg hrg)
                        unfold PRun.beq at he
                        simp only [Bool.and_eq_true] at he
                        obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := he
                        obtain ⟨b, s, l, hh⟩ := q
                        obtain ⟨b', s', l', hh'⟩ := q'
                        simp only at e1 e2 e3 e4
                        rwa [CCell.beq_eq e1, Nat.eq_of_beq_eq_true e2, CCell.beq_eq e3, CCell.beq_eq e4] at hq'
                    obtain ⟨r0, hr0, hi0⟩ := instAllR_ok e2 q hqg
                    exact fun x hx ↦ Or.inr (Or.inl (Or.inr ⟨r0, hr0, (instR_set hm hi0).mp hx⟩))

/-- **Runs at words at return**, witnessed: each at the word a load event stored at its cell, written. -/
theorem reqQ_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {qs : List (CCell × CRun)} {wl wl' : List Wit}, reqQ X st ms qs wl = some wl' → ∀ x, QSet rd qs ws x → W x
  | [], _, _, _, x, hx => by obtain ⟨p, hp, -⟩ := hx; cases hp
  | (c, q) :: l, wl, wl', h, x, hx => by
    cases wl with
    | nil => simp [reqQ] at h
    | cons w wl1 =>
      cases w
      all_goals try (simp [reqQ] at h; done)
      rename_i n
      simp only [reqQ] at h
      cases hc : instC ms c with
      | none => simp [hc] at h
      | some c' =>
        cases hq : instR ms q with
        | none => simp [hc, hq] at h
        | some q' =>
          cases hp : getF st.sv n with
          | none => simp [hc, hq, hp] at h
          | some p =>
            simp only [hc, hq, hp] at h
            cases hb : p.1.beq c' with
            | false => simp [hb] at h
            | true =>
              simp only [hb, Bool.cond_true] at h
              cases hr : runOk X st ⟨p.2.mul q'.base, q'.stride, q'.lo, q'.hi⟩ wl1 with
              | none => simp [hr] at h
              | some wl2 =>
                simp only [hr] at h
                obtain ⟨p0, hp0, w0, hw0, hx0⟩ := hx
                rcases List.mem_cons.mp hp0 with rfl | hp0
                · have hsv := hs.sv n p hp
                  have hcw : rd (c.addrW (slotW ws)) = some (p.2.valW (vw σ)) := by
                    rw [← hsv, CCell.beq_eq hb, addr_eq, CCell.addrW, CCell.addrW, instC_ok hms hc]
                  have hw1 : w0 = p.2.valW (vw σ) := by rw [hcw] at hw0; exact (Option.some.inj hw0).symm
                  subst hw1
                  obtain ⟨e1, e2, e3, e4⟩ := instR_ok hms hq
                  apply runOk_ok hX hpre hs hr
                  obtain ⟨ylo, yhi, j, h1, h2, h3, h4, h5⟩ := hx0
                  refine ⟨ylo, yhi, j, by rw [e3]; exact h1, by rw [e4]; exact h2, h3, h4, ?_⟩
                  rw [h5, valW_mul, e1, e2]
                · exact reqQ_ok hX hpre hs hms h x ⟨p0, hp0, w0, hw0, hx0⟩

/-- **A return**: the own guarantees written. -/
theorem retC1_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} {vs : List V}
    (hs : StOk rd W σ st) (h : retC1 X st vs = true) : PostW0 sigOf H rd σ (f.params.map σ) W vs := by
  unfold retC1 at h
  cases hp : monos st.env X.params with
  | none => simp [hp] at h
  | some mp =>
    cases hv : monos st.env vs with
    | none => simp [hp, hv] at h
    | some mv =>
      cases ht : getF X.T st.nt with
      | none => simp [hp, hv, ht] at h
      | some wl =>
        simp only [hp, hv, ht] at h
        obtain ⟨hmp, hlp⟩ := monos_ok hs.env _ mp hp
        obtain ⟨hmv, hlv⟩ := monos_ok hs.env vs mv hv
        have hmp' := hmp
        have hm := msOk_append hmp hmv (by simpa using hlp)
        rw [← List.map_append, hX.params] at hm
        cases h1 : reqP X st (mp ++ mv) X.sig.post wl with
        | none => simp [h1] at h
        | some wl' =>
          simp only [h1] at h
          cases h2 : reqR X st (mp ++ mv) X.sig.postR wl' with
          | none => simp [h2] at h
          | some wl2 =>
          simp only [h2] at h
          cases h3 : reqPP X st (mp ++ mv) X.sig.postP wl2 with
          | none => simp [h3] at h
          | some wl3 =>
          simp only [h3] at h
          cases h4 : reqPR X st (mp ++ mv) X.sig.postPR wl3 with
          | none => simp [h4] at h
          | some wl4 =>
          simp only [h4] at h
          cases h5 : reqQ X st (mp ++ mv) X.sig.postQ wl4 with
          | none => simp [h5] at h
          | some wl5 =>
          simp only [h5] at h
          cases h6 : reqN X st wl5 with
          | none => simp [h6] at h
          | some wl'' =>
            have hN : SigOk W H.sig.postN H.sig.postRN (H.sig.nv.map (vw σ)) := by
              unfold reqN at h6
              split at h6
              · rename_i mn hmn
                rw [hX.sig] at hmn h6
                have hmn' : MsOk (vw σ) mn (slotW (H.sig.nv.map (vw σ))) := by
                  have := (monos_ok hs.env _ mn hmn).1
                  rwa [List.map_map] at this
                cases h7 : reqP X st mn H.sig.postN wl5 with
                | none => rw [h7] at h6; cases h6
                | some wl7 =>
                  rw [h7] at h6
                  exact ⟨reqP_ok hX hpre hs hmn' h7, reqR_ok hX hpre hs hmn' h6⟩
              · cases h6
            rw [hX.sig] at h1 h2 h3 h4 h5
            rw [List.map_append] at hm
            cases wl'' with
            | cons _ _ => rw [h6] at h; simp at h
            | nil =>
            rw [hX.sig, h6] at h
            dsimp only at h
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨hM, hV⟩, hQ⟩ := h
            refine ⟨⟨reqP_ok hX hpre hs hm h1, reqR_ok hX hpre hs hm h2⟩,
              ptrOk_of (reqPP_ok hX hpre hs hm h3) (reqPR_ok hX hpre hs hm h4), fun k c hkc ↦ ?_, fun i m him ↦ ?_,
              fun p hp ↦ ?_, reqQ_ok hX hpre hs hm h5, hN⟩
            pick_goal 3
            · unfold retEqC at hQ
              have hq := List.all_eq_true.mp hQ p hp
              cases ha : instC (mp ++ mv) p.1 with
              | none => rw [ha] at hq; cases hq
              | some a =>
                cases hb : instC (mp ++ mv) p.2 with
                | none => rw [ha, hb] at hq; cases hq
                | some b =>
                  rw [ha, hb] at hq
                  rw [← instC_ok hm ha, ← instC_ok hm hb]
                  exact eqV_ok hs.eqs hq
            · unfold retMC at hM
              have hkc' := List.all_eq_true.mp hM (k, c) hkc
              dsimp only at hkc'
              cases hmk : nth mv k with
              | none => rw [hmk] at hkc'; cases hkc'
              | some m =>
                cases hic : instC mp c with
                | none => rw [hmk, hic] at hkc'; cases hkc'
                | some c' =>
                  rw [hmk, hic] at hkc'
                  have hk : k < vs.length := by
                    rw [← hlv]; rw [nth_eq] at hmk; exact (List.getElem?_eq_some_iff.mp hmk).1
                  rw [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq]
                  have h1 := hmv k m hmk
                  rw [slotW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
                    Option.map_some, Option.getD_some] at h1
                  rw [← h1, CCell.beq_eq hkc', instC_ok hmp' hic, hX.params]
            · unfold retVC at hV
              have hi := List.all_eq_true.mp hV (i, m) him
              dsimp only at hi
              cases hc : nth H.sig.post i with
              | none => rw [hc] at hi; cases nth wl i <;> simp at hi
              | some c =>
                obtain ⟨n, hw⟩ : ∃ n, nth wl i = some (.ev n) := by
                  cases hw : nth wl i with
                  | none => rw [hw, hc] at hi; simp at hi
                  | some w => cases w <;> first | exact ⟨_, rfl⟩ | (rw [hw, hc] at hi; simp at hi)
                rw [hw, hc] at hi
                dsimp only at hi
                cases hq : getF st.sv n with
                | none => rw [hq] at hi; simp at hi
                | some q =>
                  cases hc' : instC (mp ++ mv) c with
                  | none => rw [hq, hc'] at hi; simp at hi
                  | some c' =>
                    cases hm' : instC (mp ++ mv) m with
                    | none => rw [hq, hc', hm'] at hi; simp at hi
                    | some m' =>
                      rw [hq, hc', hm'] at hi
                      simp only [Bool.and_eq_true] at hi
                      refine ⟨c, by rw [← nth_eq, hc], ?_⟩
                      have := hs.sv n q hq
                      rw [CCell.beq_eq hi.1, CCell.beq_eq hi.2, addr_eq, CCell.addrW, instC_ok hm hc',
                        instC_ok hm hm'] at this
                      exact this

/-- The frame run cells pushed at a return are among those the certificate guarantees. -/
theorem faCells_ok (hX : XOk sigOf H rd f σ X) {env : Trie CCell} (he : EnvOk σ env) :
    ∀ c ∈ faCells env X.fas, FAX H σ (c.addr σ) := by
  intro c hc
  simp only [faCells, List.mem_map] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  refine ⟨p, hX.fas ▸ hp, ?_⟩
  have hm : monoOf env (V.n p.1) = some ((getF env p.1).getD (baseC p.1)) := by simp [monoOf, vnum]
  exact (cellAt_shift σ (monoOf_ok he hm) p.2).symm

/-- **A return**: the frame run cells guaranteed at return pushed, then the own guarantees written, in `W`
or among those cells. -/
theorem retC_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} {vs : List V}
    (hs : StOk rd W σ st) (h : retC X st vs = true) : PostW sigOf H rd σ (f.params.map σ) W vs := by
  unfold retC at h
  rw [CSt.seq_eq] at h
  exact retC1_ok hX (fun c hc ↦ Or.inl (hpre c hc))
    (pushL_ok hs (fun _ ↦ Or.inl) fun c hc ↦ Or.inr (faCells_ok hX hs.env c hc)) h

end Stmts

/-! ## Blocks -/

section Pass

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader}

theorem pick_cases (x : V) (args rets : List V) : ∀ (fs : List String) (j : ℕ),
    pick σ x args rets j fs = .stuck ∨ ∃ g ∈ fs, pick σ x args rets j fs = .fall [.call g args rets]
  | [], _ => Or.inl rfl
  | g :: fs, j => by
    unfold pick
    split_ifs
    · exact Or.inr ⟨g, List.mem_cons_self, rfl⟩
    · rcases pick_cases x args rets fs (j + 1) with h | ⟨g', hg', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', h⟩

theorem pick_idx (x : V) (args rets : List V) : ∀ (fs : List String) (j : ℕ),
    pick σ x args rets j fs = .stuck ∨ ∃ i, ∃ hi : i < fs.length, σ x = ofK (addressOfIndex (j + i)) ∧
      pick σ x args rets j fs = .fall [.call fs[i] args rets]
  | [], _ => Or.inl rfl
  | g :: fs, j => by
    unfold pick
    split_ifs with hx
    · exact Or.inr ⟨0, by simp, by simpa using hx, rfl⟩
    · rcases pick_idx x args rets fs (j + 1) with h | ⟨i, hi, hx', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i + 1, by simpa using hi, by rw [show j + (i + 1) = j + 1 + i by omega]; exact hx',
          by simpa using h⟩

/-! ### Joins -/

/-- A block returning at its top level never falls through. -/
theorem endsRet_walk : ∀ (ss : List Stmt), endsRet ss = true → ∀ es, walk σ ss ≠ .fall es
  | [], h, _, _ => by simp [endsRet] at h
  | s :: ss, h, es, hw => by
    rw [walk] at hw
    cases s with
    | ret vs => simp [walk1, Out.seq] at hw
    | _ =>
      all_goals
        simp only [endsRet] at h
        cases h1 : walk1 σ _ with
        | fall es1 =>
          rw [h1, Out.seq] at hw
          cases h2 : walk σ ss with
          | fall es2 => exact endsRet_walk ss h es2 h2
          | ret => rw [h2] at hw; simp [Out.pre] at hw
          | stuck => rw [h2] at hw; simp [Out.pre] at hw
        | ret => rw [h1] at hw; simp [Out.seq] at hw
        | stuck => rw [h1] at hw; simp [Out.seq] at hw

theorem endsRet_false {ss : List Stmt} {es : List Ev} (h : walk σ ss = .fall es) : endsRet ss = false := by
  cases he : endsRet ss with
  | false => rfl
  | true => exact absurd h (endsRet_walk ss he es)

theorem rng_mem {α : Type} {t : Trie α} : ∀ {lo n : ℕ} {p : ℕ × α}, p ∈ rng t lo n → getF t p.1 = some p.2
  | _, 0, _, h => by simp [rng] at h
  | lo, n + 1, p, h => by
    simp only [rng] at h
    cases hg : getF t lo with
    | none => rw [hg] at h; exact rng_mem h
    | some a =>
      rw [hg] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hg
      · exact rng_mem h

/-- **A join's entries hold** where those of a block that can fall through do. -/
theorem joinE_ok {α : Type} {beq : α → α → Bool} (hbeq : ∀ a b, beq a b = true → a = b) {Q : α → Prop}
    {ls : List (Bool × List (ℕ × α))} {l : List (ℕ × α)} (hl : (false, l) ∈ ls) (hq : ∀ p ∈ l, Q p.2) :
    ∀ p ∈ joinE beq ls, Q p.2 := by
  intro p hp
  unfold joinE at hp
  have hf : (false, l) ∈ ls.filter fun l ↦ !l.1 := List.mem_filter.mpr ⟨hl, rfl⟩
  generalize ls.filter (fun l ↦ !l.1) = F at hp hf
  cases F with
  | nil => simp at hf
  | cons l0 rest =>
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
    rcases List.mem_cons.mp hf with h0 | hr
    · rw [← h0] at hp1
      exact hq p hp1
    · obtain ⟨q, hq', hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp hp2 _ hr)
      rw [← hbeq _ _ hb]
      exact hq q hq'

theorem insL_ok {α : Type} {Q : α → Prop} : ∀ {l : List (ℕ × α)} {t : Trie α}, (∀ k a, getF t k = some a → Q a) →
    (∀ p ∈ l, Q p.2) → ∀ k a, getF (insL l t) k = some a → Q a
  | [], _, ht, _, k, a, h => ht k a h
  | p :: l, t, ht, hl, k, a, h => by
    simp only [insL, Trie.seq_eq] at h
    refine insL_ok (fun k' a' h' ↦ ?_) (fun p' hp' ↦ hl p' (List.mem_cons_of_mem _ hp')) k a h
    rcases getF_setF h' with ⟨-, rfl⟩ | h'
    · exact hl p List.mem_cons_self
    · exact ht k' a' h'

/-- **The state after a join is valid** where the state before is and the end of a block taken that
falls through is. -/
theorem joinSt_ok {W : K → Prop} {st s : CSt} {bs : List (Bool × CSt × CSt)} (hs : StOk rd W σ st)
    {b : Bool × CSt × CSt} (hb : b ∈ bs) (hb1 : b.1 = false) (hbs : StOk rd W σ b.2.2) :
    StOk rd W σ (joinSt bs st s) := by
  have hm : ∀ {α : Type} (g : Bool × CSt × CSt → List (ℕ × α)),
      (false, g b) ∈ bs.map fun b ↦ (b.1, g b) := fun g ↦ List.mem_map.mpr ⟨b, hb, by rw [hb1]⟩
  have h1 : ScOk W σ (insL (joinE CCell.beq (bs.map fun b ↦ (b.1, rng b.2.2.sc b.2.1.n (b.2.2.n - b.2.1.n)))) st.sc) :=
    insL_ok (Q := fun c : CCell ↦ W (c.addr σ)) hs.sc (joinE_ok (Q := fun c : CCell ↦ W (c.addr σ)) (fun _ _ h ↦ CCell.beq_eq h)
      (hm fun b ↦ rng b.2.2.sc b.2.1.n (b.2.2.n - b.2.1.n)) fun p hp ↦ hbs.sc _ _ (rng_mem hp))
  have h2 : RsOk W σ (insL (joinE PRun.beq (bs.map fun b ↦ (b.1, rng b.2.2.rs b.2.1.nr (b.2.2.nr - b.2.1.nr))))
      st.rs) :=
    insL_ok (Q := fun R : PRun ↦ RunF W (vw σ) R.base R.stride R.lo R.hi) hs.rs (joinE_ok (Q := fun R : PRun ↦ RunF W (vw σ) R.base R.stride R.lo R.hi) (fun _ _ h ↦ PRun.beq_eq h)
      (hm fun b ↦ rng b.2.2.rs b.2.1.nr (b.2.2.nr - b.2.1.nr)) fun p hp ↦ hbs.rs _ _ (rng_mem hp))
  have h3 : PfOk rd W σ (insL (joinE pfBeq (bs.map fun b ↦ (b.1, rng b.2.2.pf b.2.1.n (b.2.2.n - b.2.1.n)))) st.pf) :=
    insL_ok (Q := fun p : CCell × List ℕ ↦ ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W x) hs.pf (joinE_ok (Q := fun p : CCell × List ℕ ↦ ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W x) (fun _ _ h ↦ pfBeq_eq h)
      (hm fun b ↦ rng b.2.2.pf b.2.1.n (b.2.2.n - b.2.1.n)) fun p hp ↦ hbs.pf _ _ (rng_mem hp))
  have h4 : PrOk rd W σ (insL (joinE prBeq (bs.map fun b ↦ (b.1, rng b.2.2.pr b.2.1.nr (b.2.2.nr - b.2.1.nr))))
      st.pr) :=
    insL_ok (Q := fun p : PRun × List ℕ ↦ ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W x)
      hs.pr (joinE_ok (Q := fun p : PRun × List ℕ ↦ ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W x) (fun _ _ h ↦ prBeq_eq h) (hm fun b ↦ rng b.2.2.pr b.2.1.nr (b.2.2.nr - b.2.1.nr))
      fun p hp ↦ hbs.pr _ _ (rng_mem hp))
  unfold joinSt
  exact ⟨hs.env, h1, h2, hs.ad, hs.sv, hs.src, h3, h4, hs.cd, hs.eqs, hs.dq⟩

/-- A call, then a block: the call's needs, then the block's pass from the state after it. -/
theorem blockC_call {W : K → Prop} (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ))
    {g : String} {args rets : List V} {ss : List Stmt} {st1 st' : CSt}
    (hreq : CallReq sigOf H rd σ W g args)
    (hpost : EvM sigOf rd σ (.call g args rets) →
      StOk rd (fun x ↦ W x ∨ EvW sigOf rd σ (.call g args rets) x) σ st1)
    (hss : ∀ {W' : K → Prop}, (∀ c ∈ H.sig.pre, W' (c.addr σ)) → StOk rd W' σ st1 →
      BlockC sigOf H σ rd (f.params.map σ) W' (walk σ ss) st') :
    BlockC sigOf H σ rd (f.params.map σ) W ((Out.fall [.call g args rets]).seq (walk σ ss)) st' := by
  refine blockC_seq (W1 := fun _ x ↦ W x ∨ EvW sigOf rd σ (.call g args rets) x)
    ⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp at hw⟩ fun es hw hh ↦ ?_
  · simp only [Out.fall.injEq] at hw
    subst hw
    exact covC_single hreq
  · simp only [Out.fall.injEq] at hw
    subst hw
    exact ⟨fun x hx ↦ hx.imp_right fun hx ↦ ⟨_, List.mem_singleton_self _, hx⟩,
      hss (fun c hc ↦ Or.inl (hpre c hc)) (hpost (hh _ List.mem_cons_self).2)⟩

mutual
/-- **The pass over a block, on the path.** -/
theorem chkC_ok {X : CX} (hX : XOk sigOf H rd f σ X) : ∀ (ss : List Stmt) {st st' : CSt} {W : K → Prop},
    (∀ c ∈ H.sig.pre, W (c.addr σ)) → chkC X ss st = some st' → StOk rd W σ st →
      BlockC sigOf H σ rd (f.params.map σ) W (walk σ ss) st'
  | [], st, st', W, _, h, hs => by
    simp only [chkC, Option.some.injEq] at h
    subst h
    refine ⟨⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp [walk] at hw⟩, fun es hw _ ↦ ?_⟩
    · simp only [walk, Out.fall.injEq] at hw
      subst hw
      exact covC_nil W
    · simp only [walk, Out.fall.injEq] at hw
      subst hw
      exact hs.mono fun _ ↦ Or.inl
  | .atom a :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases ha : atomC X st a with
    | none => rw [ha] at h; cases h
    | some st1 =>
      rw [ha] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      refine blockC_seq (W1 := fun _ x ↦ W x ∨ Writes σ a x)
        ⟨fun es hw hh ↦ ?_, fun es vs hw _ ↦ by simp [walk1] at hw⟩ fun es hw hh ↦ ?_
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        exact covC_single (atomC_ok hX hpre ha hs (hh _ List.mem_cons_self)).1
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        obtain ⟨-, hs1⟩ := atomC_ok hX hpre ha hs (hh _ List.mem_cons_self).1
        exact ⟨fun x hx ↦ hx.imp_right fun hx ↦ ⟨.atom a, List.mem_singleton_self _, hx⟩,
          chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h hs1⟩
  | .ite c z n :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : chkC (X.ext (czero c)) z (zeroEq st c) with
    | none => rw [h1] at h; cases h
    | some s1 =>
      simp only [h1] at h
      cases h2 : chkC (X.ext (cnz c)) n (st.cnt s1) with
      | none => simp [h2] at h
      | some s2 =>
        simp only [h2, CSt.seq_eq] at h
        rw [walk]
        refine blockC_seq (W1 := fun es x ↦ W x ∨ EW sigOf rd σ es x) ?_ fun es hw hh ↦
          ⟨fun x hx ↦ hx, chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h ?_⟩
        · simp only [walk1]
          refine outC_pre ?_ c
          by_cases hc : σ c = 0
          · rw [ite_eq_left hc]
            exact (chkC_ok (hX.ext (czero_ok hc)) z hpre h1 (zeroEq_ok hs hc)).1
          · rw [ite_eq_right hc]
            exact (chkC_ok (hX.ext (cnz_ok hc)) n hpre h2 (hs.cnt s1)).1
        · have hW : ∀ es', es = [Ev.inK c] ++ es' → ∀ x, (W x ∨ EW sigOf rd σ es' x) → W x ∨ EW sigOf rd σ es x :=
            fun es' he x hx ↦ by rw [he]; exact hx.imp_right ew_append_right
          simp only [walk1] at hw
          by_cases hc : σ c = 0
          · rw [ite_eq_left hc] at hw
            cases hz : walk σ z with
            | fall es' =>
              rw [hz] at hw
              simp only [Out.pre, Out.fall.injEq] at hw
              subst hw
              exact joinSt_ok (hs.mono fun _ ↦ Or.inl) List.mem_cons_self (endsRet_false hz)
                (((chkC_ok (hX.ext (czero_ok hc)) z hpre h1 (zeroEq_ok hs hc)).2 es' hz (evsOk_append hh).2).mono
                  (hW es' rfl))
            | ret => rw [hz] at hw; simp [Out.pre] at hw
            | stuck => rw [hz] at hw; simp [Out.pre] at hw
          · rw [ite_eq_right hc] at hw
            cases hn : walk σ n with
            | fall es' =>
              rw [hn] at hw
              simp only [Out.pre, Out.fall.injEq] at hw
              subst hw
              exact joinSt_ok (hs.mono fun _ ↦ Or.inl) (List.mem_cons_of_mem _ List.mem_cons_self) (endsRet_false hn)
                (((chkC_ok (hX.ext (cnz_ok hc)) n hpre h2 (hs.cnt s1)).2 es' hn (evsOk_append hh).2).mono
                  (hW es' rfl))
            | ret => rw [hn] at hw; simp [Out.pre] at hw
            | stuck => rw [hn] at hw; simp [Out.pre] at hw
  | .match_ x arms :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : chkArmsC X x 0 arms st with
    | none => rw [h1] at h; cases h
    | some bs =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      obtain ⟨ho, hb⟩ := chkArmsC_ok hX x arms hpre h1 hs
      refine blockC_seq (W1 := fun es x ↦ W x ∨ EW sigOf rd σ es x) ho fun es hw hh ↦
        ⟨fun x hx ↦ hx, chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h ?_⟩
      obtain ⟨b, hb, hb1, hbs⟩ := hb es hw hh
      exact joinSt_ok (hs.mono fun _ ↦ Or.inl) hb hb1 hbs
  | .call g args rets :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : callC X st g args rets with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      obtain ⟨hreq, hpost⟩ := callC_ok hX hpre hs h1
      exact blockC_call hpre hreq hpost fun hp hs' ↦ chkC_ok hX ss hp h hs'
  | .callIf c g args :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : callIfC X st c g args with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      obtain ⟨hreq, hs1⟩ := callIfC_ok hX hpre hs h1
      rw [walk]
      refine blockC_seq (W1 := fun es x ↦ W x ∨ EW sigOf rd σ es x)
        ⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp [walk1] at hw⟩ fun es hw _ ↦ ?_
      swap
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        exact ⟨fun x hx ↦ hx, chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h hs1⟩
      simp only [walk1, Out.fall.injEq] at hw
      subst hw
      show CovC sigOf H rd σ W ([Ev.inK c] ++ [_])
      refine covC_append (covC_single trivial) fun _ ↦ covC_single ?_
      by_cases hc : σ c = 0
      · rw [ite_eq_left hc]; trivial
      · rw [ite_eq_right hc]; exact ReqOk.mono (e := .call g args []) (fun _ ↦ Or.inl) (hreq hc)
  | .dispatch x fs args rets :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : dispC X st x fs args rets with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      simp only [walk1]
      rcases pick_idx x args rets fs 0 with hp | ⟨i, hi, hx, hp⟩
      · rw [hp]
        exact ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw _ ↦ by simp [Out.seq] at hw⟩,
          fun es hw _ ↦ by simp [Out.seq] at hw⟩
      · rw [hp]
        obtain ⟨hreq, hpost⟩ := dispC_ok hX hpre hs h1 i hi (by simpa using hx)
        exact blockC_call hpre hreq hpost fun hp hs' ↦ chkC_ok hX ss hp h hs'
  | .ret vs :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases hr : retC X st vs with
    | false => rw [hr] at h; cases h
    | true =>
      refine ⟨⟨fun es hw _ ↦ by simp [walk, walk1, Out.seq] at hw, fun es vs' hw _ ↦ ?_⟩,
        fun es hw _ ↦ by simp [walk, walk1, Out.seq] at hw⟩
      simp only [walk, walk1, Out.seq, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨covC_nil W, fun _ ↦ (retC_ok hX hpre hs hr).mono fun _ ↦ Or.inl⟩

/-- **The pass over the arms, on the path**: the outcome's, and, falling through, an arm that can fall
through whose end state is valid. -/
theorem chkArmsC_ok {X : CX} (hX : XOk sigOf H rd f σ X) (x : V) : ∀ {j : ℕ} (arms : List (List Stmt)) {st : CSt}
    {bs : List (Bool × CSt × CSt)} {W : K → Prop},
    (∀ c ∈ H.sig.pre, W (c.addr σ)) → chkArmsC X x j arms st = some bs → StOk rd W σ st →
      OutC sigOf H σ rd (f.params.map σ) W (walkArms σ x j arms) ∧
        ∀ es, walkArms σ x j arms = .fall es → EvsOk sigOf rd σ es →
          ∃ b ∈ bs, b.1 = false ∧ StOk rd (fun y ↦ W y ∨ EW sigOf rd σ es y) σ b.2.2
  | j, [], _, _, _, _, _, _ => ⟨⟨fun es hw _ ↦ by simp [walkArms] at hw, fun es vs hw _ ↦ by simp [walkArms] at hw⟩,
      fun es hw _ ↦ by simp [walkArms] at hw⟩
  | j, a :: as, st, bs, W, hpre, h, hs => by
    simp only [chkArmsC] at h
    cases h1 : chkC (X.ext (carm x j)) a st with
    | none => rw [h1] at h; cases h
    | some s1 =>
      simp only [h1] at h
      cases h2 : chkArmsC X x (j + 1) as (st.cnt s1) with
      | none => rw [h2] at h; cases h
      | some l =>
        simp only [h2, Option.some.injEq] at h
        subst h
        rw [walkArms]
        split_ifs with hxj
        · refine ⟨(chkC_ok (hX.ext (carm_ok hxj)) a hpre h1 hs).1, fun es hw hh ↦
            ⟨_, List.mem_cons_self, endsRet_false hw, ?_⟩⟩
          exact (chkC_ok (hX.ext (carm_ok hxj)) a hpre h1 hs).2 es hw hh
        · obtain ⟨ho, hb⟩ := chkArmsC_ok hX x as hpre h2 (hs.cnt s1)
          refine ⟨ho, fun es hw hh ↦ ?_⟩
          obtain ⟨b, hb, hb1, hbs⟩ := hb es hw hh
          exact ⟨b, List.mem_cons_of_mem _ hb, hb1, hbs⟩
end

end Pass

/-! ## A loop's tail -/

section Tail

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader} {W : K → Prop}

theorem CIdx.beq_eq : ∀ {a b : CIdx}, CIdx.beq a b = true → a = b
  | .num a, .num b, h => by rw [Nat.eq_of_beq_eq_true h]
  | .val a, .val b, h => by rw [Nat.eq_of_beq_eq_true h]
  | .mono a, .mono b, h => by rw [CCell.beq_eq h]
  | .num _, .val _, h => by simp [CIdx.beq] at h
  | .val _, .num _, h => by simp [CIdx.beq] at h
  | .num _, .mono _, h => by simp [CIdx.beq] at h
  | .mono _, .num _, h => by simp [CIdx.beq] at h
  | .val _, .mono _, h => by simp [CIdx.beq] at h
  | .mono _, .val _, h => by simp [CIdx.beq] at h

theorem slotW_cons_ne {a a' : E} {l : List E} {b : ℕ} (hb : b ≠ 0) : slotW (a :: l) b = slotW (a' :: l) b := by
  cases b with
  | zero => exact absurd rfl hb
  | succ b => rfl

theorem valW_cons_noSlot0 {c : CCell} (hc : noSlot0 c = true) (a a' : E) (l : List E) :
    c.valW (slotW (a :: l)) = c.valW (slotW (a' :: l)) := by
  refine valW_congr fun b hb ↦ slotW_cons_ne ?_
  have := List.all_eq_true.mp hc b hb
  simp only [Bool.not_eq_true'] at this
  exact Nat.ne_of_beq_eq_false this

theorem idx_cons_noSlot0 {i : CIdx} (hi : noSlot0I i = true) (a a' : E) (l : List E) :
    (idxC i).valW (slotW (a :: l)) = (idxC i).valW (slotW (a' :: l)) := by
  cases i with
  | num n => rfl
  | val v =>
    rw [idxC, valW_baseC, valW_baseC]
    simp only [noSlot0I, Bool.not_eq_true'] at hi
    exact slotW_cons_ne (Nat.ne_of_beq_eq_false hi)
  | mono c => exact valW_cons_noSlot0 hi a a' l

theorem set_cons_noSlot0 {r : CRun} (hr : noSlot0R r = true) (a a' : E) (l : List E) {x : K} :
    r.Set (slotW (a :: l)) x ↔ r.Set (slotW (a' :: l)) x := by
  simp only [noSlot0R, Bool.and_eq_true] at hr
  exact runSet_congr (valW_cons_noSlot0 hr.1.1 a a' l) (idx_cons_noSlot0 hr.1.2 a a' l)
    (idx_cons_noSlot0 hr.2 a a' l)

theorem endOf_noSlot0 {ei : CIdx} {endc : Option ℕ} (h : endOf ei = some endc) : noSlot0I ei = true := by
  cases ei with
  | num => rfl
  | val v =>
    cases v with
    | zero => simp [endOf] at h
    | succ v => rfl
  | mono => simp [endOf] at h

theorem tailP_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} : ∀ {cs : List CCell} {wl wl' : List Wit}, tailP X st mp mx ex cs wl = some wl' →
      ∀ c ∈ cs, W (c.addrW (slotW ws)) ∨ (ex = true ∧ noSlot0 c = true ∧ W (c.addrW (slotW wx)))
  | [], _, _, _, c, hc => by simp at hc
  | c :: cs, [], _, h, _, _ => by simp [tailP] at h
  | c :: cs, w :: wl, wl', h, c0, hc0 => by
    simp only [tailP] at h
    obtain ⟨hb, h⟩ := cond_some h
    rcases List.mem_cons.mp hc0 with rfl | hc0
    · rcases Bool.or_eq_true_iff.mp hb with h1 | h1
      · left
        split at h1
        · rename_i c' hi
          have := ptOk_ok hX hpre hs h1
          rwa [addr_eq, CCell.addrW, instC_ok hmp hi] at this
        · cases h1
      · simp only [Bool.and_eq_true] at h1
        obtain ⟨⟨h1, h2⟩, h3⟩ := h1
        refine Or.inr ⟨h1, h2, ?_⟩
        split at h3
        · rename_i c' hi
          have := ptOk_ok hX hpre hs h3
          rwa [addr_eq, CCell.addrW, instC_ok hmx hi] at this
        · cases h3
    · exact tailP_ok hX hpre hs hmp hmx h c0 hc0

theorem tailR_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} {ei : CIdx} : ∀ {rs : List CRun} {wl wl' : List Wit}, tailR X st mp mx ex ei rs wl = some wl' →
      ∀ r ∈ rs, r.F W (slotW ws) ∨ (ex = true ∧ noSlot0R r = true ∧ r.F W (slotW wx)) ∨
        (r.lo = .val 0 ∧ r.hi = ei ∧ noSlot0 r.base = true ∧ ∃ b m0, instC mp r.base = some b ∧
          nth mp 0 = some m0 ∧ W ((b.mul (m0.pow r.stride)).addr σ))
  | [], _, _, _, r, hr => by simp at hr
  | r :: rs, [], _, h, _, _ => by simp [tailR] at h
  | r :: rs, w :: wl, wl', h, r0, hr0 => by
    simp only [tailR] at h
    cases hb : tailR1 X st mp mx ex ei r w with
    | false =>
      rw [hb, Bool.cond_false] at h
      obtain ⟨he, h⟩ := cond_some h
      simp only [Bool.and_eq_true] at he
      cases hq : instR mx r with
      | none => rw [hq] at h; cases h
      | some q =>
        simp only [hq] at h
        cases hw : runOk X st q (w :: wl) with
        | none => simp [hw] at h
        | some wl1 =>
          simp only [hw] at h
          rcases List.mem_cons.mp hr0 with rfl | hr0
          · exact Or.inr (Or.inl ⟨he.1, he.2, (instR_runF hmx hq).mp (runOk_ok hX hpre hs hw)⟩)
          · exact tailR_ok hX hpre hs hmp hmx h r0 hr0
    | true =>
      rw [hb, Bool.cond_true] at h
      unfold tailR1 at hb
      rcases List.mem_cons.mp hr0 with rfl | hr0
      · rcases Bool.or_eq_true_iff.mp hb with h1 | h1
        · rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
          · left
            split at h1
            · rename_i q hi
              exact (instR_runF hmp hi).mp (rnOk_ok hX hs h1)
            · cases h1
          · simp only [Bool.and_eq_true] at h1
            obtain ⟨⟨h1, h2⟩, h3⟩ := h1
            refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
            split at h3
            · rename_i q hi
              exact (instR_runF hmx hi).mp (rnOk_ok hX hs h3)
            · cases h3
        · simp only [Bool.and_eq_true] at h1
          obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h1
          refine Or.inr (Or.inr ⟨CIdx.beq_eq e1, CIdx.beq_eq e2, e3, ?_⟩)
          split at e4
          · rename_i b m0 hb' hm
            exact ⟨b, m0, hb', hm, ptOk_ok hX hpre hs e4⟩
          · cases e4
      · exact tailR_ok hX hpre hs hmp hmx h r0 hr0

theorem tailPP_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} : ∀ {ps : List (CCell × List ℕ)} {wl wl' : List Wit}, tailPP X st mp mx ex ps wl = some wl' →
      ∀ p ∈ ps, (∀ x, PtrSet rd (p.1.addrW (slotW ws)) p.2 x → W x) ∨
        (ex = true ∧ noSlot0 p.1 = true ∧ ∀ x, PtrSet rd (p.1.addrW (slotW wx)) p.2 x → W x)
  | [], _, _, _, p, hp => by simp at hp
  | p :: ps, wl, wl', h, p0, hp0 => by
    simp only [tailPP] at h
    have key : ∀ {ms : List CCell} {w' : List E}, MsOk (vw σ) ms (slotW w') → ∀ {wl1 : List Wit},
        (match instC ms p.1 with
          | some c => ptrOk X st c p.2 wl
          | none => none) = some wl1 → ∀ x, PtrSet rd (p.1.addrW (slotW w')) p.2 x → W x := by
      intro ms w' hms wl1 h1
      cases hi : instC ms p.1 with
      | none => rw [hi] at h1; cases h1
      | some c =>
        rw [hi] at h1
        exact fun x hx ↦ ptrOk_ok hX hpre hs h1 x ((ptrSet_inst hms hi).mpr hx)
    split at h
    · next wl1 h1 =>
      rcases List.mem_cons.mp hp0 with rfl | hp0
      · exact Or.inl (key hmp h1)
      · exact tailPP_ok hX hpre hs hmp hmx h p0 hp0
    · cases hb : (ex && noSlot0 p.1) with
      | false => rw [hb] at h; cases h
      | true =>
        rw [hb, Bool.cond_true] at h
        simp only [Bool.and_eq_true] at hb
        split at h
        · next c hi =>
          split at h
          · next wl2 h2 =>
            have h2' : (match instC mx p.1 with
                | some c => ptrOk X st c p.2 wl
                | none => none) = some wl2 := by rw [hi]; exact h2
            rcases List.mem_cons.mp hp0 with rfl | hp0
            · exact Or.inr ⟨hb.1, hb.2, key hmx h2'⟩
            · exact tailPP_ok hX hpre hs hmp hmx h p0 hp0
          · cases h
        · cases h

theorem tailPR_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} {ei : CIdx} : ∀ {ps : List (CRun × List ℕ)} {wl wl' : List Wit},
      tailPR X st mp mx ex ei ps wl = some wl' →
      ∀ p ∈ ps, (∀ a, p.1.Set (slotW ws) a → ∀ x, PtrSet rd a p.2 x → W x) ∨
        (ex = true ∧ noSlot0R p.1 = true ∧ ∀ a, p.1.Set (slotW wx) a → ∀ x, PtrSet rd a p.2 x → W x) ∨
        (p.1.lo = .val 0 ∧ p.1.hi = ei ∧ noSlot0 p.1.base = true ∧ ∃ b m0, instC mp p.1.base = some b ∧
          nth mp 0 = some m0 ∧ ∀ x, PtrSet rd ((b.mul (m0.pow p.1.stride)).addr σ) p.2 x → W x)
  | [], _, _, _, p, hp => by simp at hp
  | p :: ps, wl, wl', h, p0, hp0 => by
    simp only [tailPR] at h
    have key : ∀ {ms : List CCell} {w' : List E}, MsOk (vw σ) ms (slotW w') → ∀ {wl1 : List Wit},
        (match instR ms p.1 with
          | some q => ptrROk X st q p.2 wl
          | none => none) = some wl1 → ∀ a, p.1.Set (slotW w') a → ∀ x, PtrSet rd a p.2 x → W x := by
      intro ms w' hms wl1 h1
      cases hi : instR ms p.1 with
      | none => rw [hi] at h1; cases h1
      | some q =>
        rw [hi] at h1
        exact fun a ha ↦ ptrROk_ok hX hpre hs h1 a ((instR_set hms hi).mpr ha)
    split at h
    · next wl1 h1 =>
      rcases List.mem_cons.mp hp0 with rfl | hp0
      · exact Or.inl (key hmp h1)
      · exact tailPR_ok hX hpre hs hmp hmx h p0 hp0
    · split at h
      · next wl2 h2 =>
        cases hb : (ex && noSlot0R p.1) with
        | false => rw [hb] at h2; cases h2
        | true =>
          rw [hb, Bool.cond_true] at h2
          simp only [Bool.and_eq_true] at hb
          rcases List.mem_cons.mp hp0 with rfl | hp0
          · exact Or.inr (Or.inl ⟨hb.1, hb.2, key hmx h2⟩)
          · exact tailPR_ok hX hpre hs hmp hmx h p0 hp0
      · cases hb : (CIdx.beq p.1.lo (.val 0) && CIdx.beq p.1.hi ei && noSlot0 p.1.base) with
        | false => rw [hb] at h; cases h
        | true =>
          rw [hb, Bool.cond_true] at h
          simp only [Bool.and_eq_true] at hb
          obtain ⟨⟨e1, e2⟩, e3⟩ := hb
          split at h
          · next b m0 hib hm0 =>
            split at h
            · next wl3 h3 =>
              rcases List.mem_cons.mp hp0 with rfl | hp0
              · exact Or.inr (Or.inr ⟨CIdx.beq_eq e1, CIdx.beq_eq e2, e3, b, m0, hib, hm0,
                  ptrOk_ok hX hpre hs h3⟩)
              · exact tailPR_ok hX hpre hs hmp hmx h p0 hp0
            · cases h
          · cases h

/-- **A loop's tail**: after its body (`W`, the state `st`), its tail call `callIf c self (i' :: ps)` and
its `ret []`, the guarantees written: by the path; or, entered, by the next iteration (a guarantee not
over the counter is its own instance there), not entered, by the path at the exit (the next counter
is the end); or a run `[counter, end)` accumulated: the counter's point by the path, the rest by the
next iteration, none at the exit. -/
theorem tailC_ok (hX : XOk sigOf H rd f σ X) (hself : sigOf f.name = H.sig) (hrm : H.sig.retM = [])
    (hpv : H.sig.postV = []) (hre : H.sig.retEq = []) (hpq : H.sig.postQ = [])
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ))
    {st : CSt} (hs : StOk rd W σ st) {ei : CIdx} (hterm : (CIdx.val 0, ei) ∈ H.sig.term) {endc : Option ℕ}
    (hend : endOf ei = some endc) {m : ℕ} (hpar : f.params = (List.range m).map V.n)
    (hover : idxOver m ei = true) {ps : List V} (hps : f.params = V.n 0 :: ps) {c i' : V}
    (hi' : σ i' = σ (V.n 0) * ofK (addressOfIndex 1))
    (hc : σ c = σ (V.n 0) * ofK (addressOfIndex 1) + Res.endVal σ f endc)
    (h : tailC X st (i' :: ps) ei = true) :
    PostW0 sigOf H rd σ (f.params.map σ)
      (fun x ↦ W x ∨ EW sigOf rd σ [.inK c, if σ c = 0 then .skip f.name (i' :: ps) else .call f.name (i' :: ps) []] x)
      [] := by
  set e : Ev := if σ c = 0 then .skip f.name (i' :: ps) else .call f.name (i' :: ps) [] with he
  have hws0' : f.params.map σ = σ (V.n 0) :: ps.map σ := by rw [hps, List.map_cons]
  have hm0 : 0 < m := by
    have := congrArg List.length (hpar.symm.trans hps)
    simp at this
    omega
  have hslot : ∀ b < m, slotW (f.params.map σ) b = vw σ b := fun b hb ↦ by
    rw [hpar, List.map_map]; exact slotW_params hb
  have hei : (idxC ei).valW (slotW (f.params.map σ)) = (idxC ei).valW (vw σ) := by
    cases ei with
    | num n => rfl
    | val v => rw [idxC, valW_baseC, valW_baseC]; exact hslot v (by simpa [idxOver] using hover)
    | mono => simp [endOf] at hend
  have hendv : Res.endVal σ f endc = (idxC ei).valW (vw σ) := by
    cases ei with
    | num n =>
      simp only [endOf, Option.some.injEq] at hend
      subst hend
      rw [idxC, valW_const]
      rfl
    | val v =>
      cases v with
      | zero => simp [endOf] at hend
      | succ v =>
        cases v with
        | succ => simp [endOf] at hend
        | zero =>
          simp only [endOf, Option.some.injEq] at hend
          subst hend
          have hm : 1 < m := by simpa [idxOver] using hover
          obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
          rw [idxC, valW_baseC]
          simp only [Res.endVal, hpar, List.range_succ_eq_map, List.map_cons, List.map_map]
          rfl
    | mono => simp [endOf] at hend
  have hexit : σ c = 0 → σ (V.n 0) * ofK (addressOfIndex 1) = (idxC ei).valW (vw σ) := fun h0 ↦ by
    rw [← hendv]
    exact CoreMode.char2_eq (by rw [← hc, h0])
  have hcall : σ c ≠ 0 → ∀ x, PostSet rd H.sig ((i' :: ps).map σ) x →
      EW sigOf rd σ [.inK c, e] x := fun h0 x hx ↦ by
    refine ⟨e, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    rw [he, ite_eq_right h0]
    simp only [EvW]
    rw [hself, List.append_nil]
    exact hx
  unfold tailC at h
  cases hmp : monos st.env X.params with
  | none => simp [hmp] at h
  | some mp =>
    cases ht : getF X.T st.nt with
    | none => simp [hmp, ht] at h
    | some wl =>
      cases hmi : monoOf st.env i' with
      | none => simp [hmp, ht, hmi] at h
      | some mi =>
        simp only [hmp, ht, hmi] at h
        obtain ⟨hmp', hlp⟩ := monos_ok hs.env _ mp hmp
        rw [hX.params] at hmp' hlp
        have hmx := msOk_setNth (n := 1) hmp' (by simpa using hlp) (show mi.valW (vw σ) = σ i' by
          rw [← val_eq, ← monoOf_ok hs.env hmi])
        have hwx0 : ei = .val 1 → σ c = 0 → slotW (setNth (f.params.map σ) 1 (σ i')) = slotW (f.params.map σ) :=
          fun he1 h0 ↦ funext fun b ↦ by
            rw [slotW_setNth]
            split_ifs with hb
            · obtain ⟨rfl, -⟩ := hb
              rw [hi', hexit h0, he1, idxC, valW_baseC]
              exact (hslot 1 (by subst he1; simpa [idxOver] using hover)).symm
            · rfl
        -- a run `[counter, end)`: the counter's cell, or, entered, the next iteration's run
        have hacc : ∀ (r : CRun) (b m0 : CCell), r.lo = .val 0 → r.hi = ei → noSlot0 r.base = true →
            instC mp r.base = some b → nth mp 0 = some m0 → ∀ a, r.Set (slotW (f.params.map σ)) a →
            a = (b.mul (m0.pow r.stride)).addr σ ∨ (σ c ≠ 0 ∧ r.Set (slotW ((i' :: ps).map σ)) a) := by
          intro r b m0 hlo hhi hnb hb hm0' a ha
          have hl0 : (idxC r.lo).valW (slotW (f.params.map σ)) = vw σ 0 := by
            rw [hlo, idxC, valW_baseC]; exact hslot 0 hm0
          have hh0 : (idxC r.hi).valW (slotW (f.params.map σ)) = (idxC ei).valW (vw σ) := by
            rw [hhi]; exact hei
          obtain ⟨ylo, yhi, j, hylo, hyhi, h3, h4, rfl⟩ := ha
          rw [hl0] at hylo
          rw [hh0] at hyhi
          have hcap := (rep_spec hyhi).1
          rcases Nat.eq_or_lt_of_le h3 with rfl | h3
          · left
            have hb' := instC_ok hmp' hb
            have hm0'' := hmp' 0 m0 hm0'
            have hcell : (b.mul (m0.pow r.stride)).addr σ =
                (r.base.valW (slotW (f.params.map σ)) * ofK (addressOfIndex (r.stride * ylo))).limb 0 := by
              rw [addr_eq, CCell.addrW, valW_mul, valW_pow, hb', hm0'', hslot 0 hm0, (rep_spec hylo).2,
                ← ofK_pow']
              simp only [addressOfIndex, ← pow_mul, mul_comm]
            exact hcell.symm
          · by_cases h0 : σ c = 0
            · exfalso
              have hx := hexit h0
              rw [show σ (V.n 0) = vw σ 0 from rfl, (rep_spec hylo).2, ← ofK_mul', addressOfIndex,
                addressOfIndex, ← pow_add, ← addressOfIndex] at hx
              rw [← hx, rep_of (by omega), Option.some.injEq] at hyhi
              omega
            · refine Or.inr ⟨h0, ylo + 1, yhi, j, ?_, ?_, by omega, h4, ?_⟩
              · rw [hlo, idxC, valW_baseC, List.map_cons]
                show rep (σ i') = some (ylo + 1)
                rw [hi']
                exact rep_succ hylo (by omega)
              · rw [hhi, List.map_cons, idx_cons_noSlot0 (endOf_noSlot0 hend) (σ i') (σ (V.n 0)), ← hws0',
                  hei]
                exact hyhi
              · rw [List.map_cons, valW_cons_noSlot0 hnb (σ i') (σ (V.n 0)), ← hws0']
        cases hp : tailP X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) X.sig.post wl with
        | none => simp [hp] at h
        | some wl1 =>
          simp only [hp] at h
          cases hr : tailR X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) ei X.sig.postR wl1 with
          | none => simp [hr] at h
          | some wl2 =>
          simp only [hr] at h
          cases hpp : tailPP X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) X.sig.postP wl2 with
          | none => simp [hpp] at h
          | some wl3 =>
          simp only [hpp] at h
          cases hpr : tailPR X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) ei X.sig.postPR wl3 with
          | none => simp [hpr] at h
          | some wl'' =>
            have hNN : H.sig.postN = [] ∧ H.sig.postRN = [] := by
              rw [hpr] at h
              rcases wl'' with _ | ⟨_, _⟩
              · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
                rw [← hX.sig]; exact h
              · simp at h
            rw [hX.sig] at hp hr hpp hpr
            have HP := tailP_ok hX hpre hs hmp' hmx hp
            have HR := tailR_ok hX hpre hs hmp' hmx hr
            have HPP := tailPP_ok hX hpre hs hmp' hmx hpp
            have HPR := tailPR_ok hX hpre hs hmp' hmx hpr
            unfold PostW0
            rw [List.map_nil, List.append_nil]
            refine ⟨⟨fun c0 hc0 ↦ ?_, fun r hr0 ↦ ?_⟩, ptrOk_of (fun p hp0 ↦ ?_) (fun p hp0 ↦ ?_),
              fun k c hkc ↦ (by rw [hrm] at hkc; cases hkc), fun i m h ↦ (by rw [hpv] at h; cases h),
              fun p h ↦ (by rw [hre] at h; cases h), fun x ⟨p, h, _⟩ ↦ (by rw [hpq] at h; cases h), by
                rw [hNN.1, hNN.2]; exact ⟨fun _ hc ↦ (by cases hc), fun _ hr ↦ (by cases hr)⟩⟩
            · rcases HP c0 hc0 with h1 | ⟨hex, hns, h1⟩
              · exact Or.inl h1
              · have hei1 : ei = .val 1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · exact Or.inl (by rw [← hwx0 hei1 h0]; exact h1)
                · refine Or.inr (hcall h0 _ (Or.inl (Or.inl ⟨c0, hc0, ?_⟩)))
                  rw [CCell.addrW, CCell.addrW, hws0', List.map_cons, valW_cons_noSlot0 hns]
            · rcases HR r hr0 with h1 | ⟨hex, hns, h1⟩ | ⟨hlo, hhi, hnb, b, m0, hb, hm0', h1⟩
              · exact h1.mono fun _ ↦ Or.inl
              · have hei1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · rw [← hwx0 hei1 h0]; exact h1.mono fun _ ↦ Or.inl
                · refine fun x hx ↦ Or.inr (hcall h0 x (Or.inl (Or.inr ⟨r, hr0, ?_⟩)))
                  rw [List.map_cons]
                  rw [hws0'] at hx
                  exact (set_cons_noSlot0 hns _ _ _).mp hx
              · intro x hx
                rcases hacc r b m0 hlo hhi hnb hb hm0' x hx with rfl | ⟨h0, hx'⟩
                · exact Or.inl h1
                · exact Or.inr (hcall h0 _ (Or.inl (Or.inr ⟨r, hr0, hx'⟩)))
            · rcases HPP p hp0 with h1 | ⟨hex, hns, h1⟩
              · exact fun x hx ↦ Or.inl (h1 x hx)
              · have hei1 : ei = .val 1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · exact fun x hx ↦ Or.inl (h1 x (by rw [hwx0 hei1 h0]; exact hx))
                · refine fun x hx ↦ Or.inr (hcall h0 x (Or.inr (Or.inl (Or.inl ⟨p, hp0, ?_⟩))))
                  rw [CCell.addrW, List.map_cons, valW_cons_noSlot0 hns _ (σ (V.n 0)), ← hws0']
                  exact hx
            · rcases HPR p hp0 with h1 | ⟨hex, hns, h1⟩ | ⟨hlo, hhi, hnb, b, m0, hb, hm0', h1⟩
              · exact fun a ha x hx ↦ Or.inl (h1 a ha x hx)
              · have hei1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · exact fun a ha x hx ↦ Or.inl (h1 a (by rw [hwx0 hei1 h0]; exact ha) x hx)
                · refine fun a ha x hx ↦ Or.inr (hcall h0 x (Or.inr (Or.inl (Or.inr ⟨p, hp0, a, ?_, hx⟩))))
                  rw [List.map_cons]
                  rw [hws0'] at ha
                  exact (set_cons_noSlot0 hns _ _ _).mp ha
              · intro a ha x hx
                rcases hacc p.1 b m0 hlo hhi hnb hb hm0' a ha with rfl | ⟨h0, ha'⟩
                · exact Or.inl (h1 x hx)
                · exact Or.inr (hcall h0 x (Or.inr (Or.inl (Or.inr ⟨p, hp0, a, ha', hx⟩))))

end Tail

/-! ## The function -/

section Main

/-- A precondition's address at the parameters' words (then any words) is its address at the values
`V.n b`. -/
theorem addr_pre {σ : Val} {f : Fn} {pre : List CCell} (hpar : f.params = (List.range f.params.length).map V.n)
    (hpov : preOver f.params.length pre = true) {c : CCell} (hc : c ∈ pre) (ws : List E) :
    c.addrW (slotW (f.params.map σ ++ ws)) = c.addr σ := by
  have hv : c.valW (vw σ) = c.valW (slotW (f.params.map σ ++ ws)) := valW_congr fun b hb ↦ by
    have := Nat.blt_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hpov c hc) b hb)
    rw [slotW_append, ite_eq_left (by rw [List.length_map]; exact this), hpar, List.map_map]
    exact (slotW_params this).symm
  rw [addr_eq, CCell.addrW, CCell.addrW, hv]

theorem loopBody_of {fn : Fn} {pre : List Stmt} {a b : Stmt} (h : fn.body = pre ++ [a, b]) : loopBody fn = pre := by
  simp [loopBody, h]

theorem idxOver_val {σ : Val} {f : Fn} {m : ℕ} (hpar : f.params = (List.range m).map V.n) {i : CIdx}
    (h : idxOver m i = true) : (idxC i).valW (slotW (f.params.map σ)) = (idxC i).valW (vw σ) := by
  cases i with
  | num n => rfl
  | val v =>
    rw [idxC, valW_baseC, valW_baseC, hpar, List.map_map]
    exact slotW_params (by simpa [idxOver] using h)
  | mono c =>
    rw [idxC]
    refine valW_congr fun b hb ↦ ?_
    have := List.all_eq_true.mp h b hb
    rw [hpar, List.map_map]
    exact slotW_params (Nat.blt_eq.mp this)

theorem paramEnv_get : ∀ (m k : ℕ) (c : CCell), getF (paramEnv m) k = some c → c = baseC k
  | 0, k, c, h => by simp [paramEnv, getF_nil] at h
  | m + 1, k, c, h => by
    simp only [paramEnv, Trie.seq_eq, id] at h
    rcases getF_setF h with ⟨rfl, rfl⟩ | h
    · rfl
    · exact paramEnv_get m k c h

theorem paramEnv_ok (σ : Val) (m : ℕ) : EnvOk σ (paramEnv m) := fun k c h ↦ by
  rw [paramEnv_get m k c h, val_baseC]

/-- The own ghosts' monomials name the own ghost words. -/
theorem ghostMs_ok (σ : Val) (G : HSig) : MsOk (vw σ) (ghostMs G.ghosts) (slotW (ownG G σ)) := by
  intro b m hb
  rw [nth_eq, ghostMs, List.getElem?_map] at hb
  by_cases h : b < G.ghosts
  · simp only [List.getElem?_range h, Option.map_some, Option.some.injEq] at hb
    subst hb
    unfold slotW ownG
    simp [List.getD_eq_getElem?_getD, List.getElem?_range h, valW_baseC]
  · rw [List.getElem?_eq_none (by simpa using h)] at hb
    cases hb

theorem initC_ok {X : CX} {σ : Val} {rd : Reader} {st0 : CSt} (h : initC X = some st0) :
    StOk rd (fun x ↦ PreSet rd X.sig (X.params.map σ ++ ownG X.sig σ) x) σ st0 := by
  unfold initC at h
  cases hd : dersOk X.ders with
  | false => simp [hd] at h
  | true =>
  simp only [hd, Bool.not_true, Bool.cond_false] at h
  rw [Trie.seq_eq] at h
  cases hm : monos (paramEnv X.params.length) X.params with
  | none => simp [hm] at h
  | some mp =>
    simp only [hm] at h
    cases h1 : instPP (mp ++ ghostMs X.sig.ghosts) X.sig.preP with
    | none => simp [h1] at h
    | some pps =>
      cases hr : instAllR (mp ++ ghostMs X.sig.ghosts) X.sig.preR with
      | none => simp [h1, hr] at h
      | some rs =>
        cases h2 : instPRL (mp ++ ghostMs X.sig.ghosts) X.sig.prePR with
        | none => simp [h1, hr, h2] at h
        | some prs =>
          simp only [h1, hr, h2, Option.some.injEq] at h
          subst h
          obtain ⟨hmp0, hlp⟩ := monos_ok (paramEnv_ok σ _) _ mp hm
          have hmp := msOk_append hmp0 (ghostMs_ok σ X.sig) (by simpa using hlp)
          refine pushPRL_ok (pushRL_ok (pushPL_ok ⟨paramEnv_ok σ _, fun n c h ↦ by simp [getF_nil] at h,
            fun r R h ↦ by simp [getF_nil] at h, fun k p h ↦ by simp [getF_nil] at h,
            fun n p h ↦ by simp [getF_nil] at h, fun n p h ↦ by simp [getF_nil] at h,
            fun n p h ↦ by simp [getF_nil] at h, fun n p h ↦ by simp [getF_nil] at h, fun e he ↦ by simp at he,
            fun p hp ↦ by simp at hp, fun p hp ↦ by simp at hp⟩ (fun _ h ↦ h)
            fun p hp x hx ↦ ?_) (fun _ h ↦ h) fun q hq ↦ ?_) (fun _ h ↦ h) fun p hp a ha x hx ↦ ?_
          · obtain ⟨p0, hp0, hi, he⟩ := instPP_ok h1 p hp
            refine Or.inr (Or.inl ⟨p0, hp0, ?_⟩)
            rw [← he]
            exact (ptrSet_inst hmp hi).mp hx
          · obtain ⟨r, hr0, hi⟩ := instAllR_ok hr q hq
            exact (instR_runF hmp hi).mpr fun x hx ↦ Or.inl (Or.inr ⟨r, hr0, hx⟩)
          · obtain ⟨p0, hp0, hi, he⟩ := instPRL_ok h2 p hp
            refine Or.inr (Or.inr ⟨p0, hp0, a, (instR_set hmp hi).mp ha, ?_⟩)
            rw [← he]
            exact hx

/-- A loop helper's path, its tail's events named: its body's, the tail's guard, then its tail call. -/
theorem walk_tail {σ : Val} {pre : List Stmt} {c i' : V} {g : String} {ps : List V} {es1 : List Ev}
    (h : walk σ pre = .fall es1) :
    walk σ (pre ++ [.callIf c g (i' :: ps), .ret []]) =
      .ret (es1 ++ [.inK c, if σ c = 0 then .skip g (i' :: ps) else .call g (i' :: ps) []]) [] := by
  rw [walk_append, h]
  simp [walk, walk1, Out.seq, Out.pre]

/-- **A top-level atom before the first `ret` is on every path that returns.** -/
theorem topAtoms_on_path {σ : Val} : ∀ {body : List Stmt} {es : List Ev} {vs : List V},
    walk σ body = .ret es vs → ∀ a ∈ topAtoms body, Ev.atom a ∈ es
  | [], _, _, _, a, ha => by simp [topAtoms] at ha
  | s :: ss, es, vs, h, a, ha => by
    unfold topAtoms at ha
    cases hn : Memory.Stmt.noRet s with
    | false => rw [hn] at ha; simp at ha
    | true =>
      rw [hn, Bool.cond_true] at ha
      rw [walk] at h
      rcases walk1_noRet (σ := σ) s hn with ⟨es1, h1⟩ | h1
      · rw [h1] at h
        simp only [Out.seq] at h
        cases h2 : walk σ ss with
        | fall _ => rw [h2] at h; simp [Out.pre] at h
        | stuck => rw [h2] at h; simp [Out.pre] at h
        | ret es2 vs2 =>
          rw [h2] at h
          simp only [Out.pre, Out.ret.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have ih := topAtoms_on_path h2 a
          cases s with
          | atom b =>
            simp only at ha
            rcases List.mem_cons.mp ha with rfl | ha
            · simp only [walk1, Out.fall.injEq] at h1
              subst h1
              exact List.mem_append_left _ List.mem_cons_self
            · exact List.mem_append_right _ (ih ha)
          | ite _ _ _ => exact List.mem_append_right _ (ih ha)
          | match_ _ _ => exact List.mem_append_right _ (ih ha)
          | call _ _ _ => exact List.mem_append_right _ (ih ha)
          | callIf _ _ _ => exact List.mem_append_right _ (ih ha)
          | dispatch _ _ _ _ => exact List.mem_append_right _ (ih ha)
          | ret _ => simp [Memory.Stmt.noRet] at hn
      · rw [h1] at h; simp [Out.seq] at h

theorem getF_keysT : ∀ (l : List ℕ) (t : Trie Unit) {k : ℕ}, (getF (keysT l t) k).isSome = true →
    k ∈ l ∨ (getF t k).isSome = true
  | [], _, _, h => Or.inr h
  | a :: l, t, k, h => by
    rw [keysT, Trie.seq_eq] at h
    rcases getF_keysT l _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
      rcases getF_setF hu with ⟨rfl, -⟩ | hu
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (by rw [hu]; rfl)

/-- **The frame run cells a certificate guarantees at return**: each a cell of a `frameAddr` among the atoms,
its value defined by one of them, or past a nonempty run. -/
theorem faOk_spec {as : List Atom} : ∀ {fas : List (ℕ × ℕ)}, faOk as (dstKeys as) fas = true →
    ∀ p ∈ fas, (∃ run v, Atom.frameAddr (V.n p.1) run ∈ as ∧ run[p.2]? = some v ∧ ∃ a ∈ as, v ∈ atomDst a) ∨
      ∃ run, Atom.frameAddr (V.n p.1) run ∈ as ∧ run ≠ [] ∧ run.length ≤ p.2
  | [], _, p, hp => by simp at hp
  | (kp, i) :: l, h, p, hp => by
    simp only [faOk, Bool.and_eq_true, List.any_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨a, ha, hfa⟩ := h.1
      cases a with
      | frameAddr q run =>
        simp only [faAt, Bool.and_eq_true, Bool.or_eq_true] at hfa
        obtain ⟨hq, hv⟩ := hfa
        cases hqn : vnum q with
        | none => rw [hqn] at hq; cases hq
        | some k =>
          rw [hqn] at hq
          have hk : k = kp := Nat.eq_of_beq_eq_true hq
          subst hk
          rw [vnum_eq hqn] at ha
          rcases hv with hv | hv
          · left
            cases hri : run[i]? with
            | none => rw [hri] at hv; cases hv
            | some v =>
              simp only [hri] at hv
              cases hvn : vnum v with
              | none => simp only [hvn] at hv; cases hv
              | some k' =>
                simp only [hvn] at hv
                rcases getF_keysT _ _ hv with hm | hm
                · obtain ⟨v', hv', hv'n⟩ := List.mem_filterMap.mp hm
                  obtain ⟨a', ha', hva'⟩ := List.mem_flatMap.mp hv'
                  refine ⟨run, v, ha, hri, a', ha', ?_⟩
                  rw [vnum_eq hvn, ← vnum_eq hv'n]
                  exact hva'
                · simp [getF_nil] at hm
          · right
            simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, Nat.ble_eq] at hv
            exact ⟨run, ha, hv.1, hv.2⟩
      | _ => simp [faAt] at hfa
    · exact faOk_spec h.2 p hp

/-- No frame run cell guaranteed (`HCert.fas` empty), none among them. -/
theorem noFAX {H : HCert} (hn : H.fas = []) {σ : Val} {x : K} : ¬ FAX H σ x := by
  rintro ⟨p, hp, -⟩
  rw [hn] at hp
  cases hp

/-- The frame run cells the certificate guarantees at return are frame run cells of the path. -/
theorem fax_faw {σ : Val} {H : HCert} {f : Fn} {es : List Ev} {vs : List V}
    (hfa : faOk (topAtoms f.body) (dstKeys (topAtoms f.body)) H.fas = true) (hw : walk σ f.body = .ret es vs)
    {x : K} (h : FAX H σ x) : FAW σ H.fas es x := by
  obtain ⟨p, hp, rfl⟩ := h
  rcases faOk_spec hfa p hp with ⟨run, v, hfr, hv, a, ha, hva⟩ | ⟨run, hfr, hne, hle⟩
  · exact Or.inl ⟨V.n p.1, run, p.2, v, topAtoms_on_path hw _ hfr, hv, ⟨a, topAtoms_on_path hw _ ha, hva⟩, rfl⟩
  · exact Or.inr ⟨p.1, p.2, run, hp, topAtoms_on_path hw _ hfr, hne, hle, rfl⟩

/-- **The heap check with calls and loops is sound, call by call**: on a path of a function passing `heapOkC`
that returns, its events holding, given its entry facts and its residuals, every event's needs are written before
it once the calls before it have their callees' returned words (`ReadsOkP`), and, every call having them, its
guarantees are written at return. A loop helper's own signature is `sigOf`'s for its name. -/
theorem out_seq_assocC : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_appendC (σ : Val) : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_appendC σ l l', out_seq_assocC]

theorem out_pre_seqC (es : List Ev) : ∀ (o k : Out), (o.pre es).seq k = (o.seq k).pre es
  | .fall es', k => by cases k <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .ret es' vs, k => by simp [Out.seq, Out.pre]
  | .stuck, k => by simp [Out.seq, Out.pre]

theorem out_seq_nilC : ∀ (o : Out), o.seq (.fall []) = o
  | .fall es => by simp [Out.seq, Out.pre]
  | .ret _ _ => rfl
  | .stuck => rfl

/-- **The body the pass reads walks as the body**: an `ite`'s continuation in each branch is one walk. -/
theorem walk_dupB (σ : Val) (ds : List ℕ) : ∀ ss : List Stmt, walk σ (dupB ds ss) = walk σ ss
  | [] => rfl
  | s :: ss => by
    cases s with
    | ite c z n =>
      simp only [dupB]
      cases dupC ds c with
      | false => simp only [Bool.cond_false, walk, walk_dupB σ ds ss]
      | true =>
        simp only [Bool.cond_true, walk, walk1, walk_appendC, out_seq_nilC]
        rw [out_pre_seqC]
        split_ifs <;> rfl
    | atom a => simp only [dupB, walk, walk_dupB σ ds ss]
    | match_ x arms => simp only [dupB, walk, walk_dupB σ ds ss]
    | call g args rets => simp only [dupB, walk, walk_dupB σ ds ss]
    | callIf c g args => simp only [dupB, walk, walk_dupB σ ds ss]
    | dispatch x fs args rets => simp only [dupB, walk, walk_dupB σ ds ss]
    | ret vs => simp only [dupB, walk, walk_dupB σ ds ss]

theorem walk_bodyC (σ : Val) (ds : List ℕ) (ss : List Stmt) : walk σ (bodyC ds ss) = walk σ ss := by
  unfold bodyC
  cases ds.isEmpty
  · exact walk_dupB σ ds ss
  · rfl

theorem heapOkC_soundP {pows : PowTree} (hp : pows.Ok) {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOkC pows sigOf f H = true) (hself : sigOf f.name = H.sig) {σ : Val} {rd : Reader}
    {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) (hD : DerOk H rd σ) (hG : GwOk H.sig rd σ) :
    ReadsOkP sigOf H rd σ (f.params.map σ) es ∧ ((∀ e ∈ es, EvM sigOf rd σ e) →
      (PostOkC sigOf H rd σ (f.params.map σ) es vs ∧ (H.fas = [] → PostOkW sigOf H rd σ (f.params.map σ) es vs)) ∧
      RetMOk H.sig (f.params.map σ) (vs.map σ) ∧ RetVOk rd H.sig (f.params.map σ ++ vs.map σ) ∧
      RetEqOk H.sig (f.params.map σ ++ vs.map σ)) := by
  unfold heapOkC at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨hpar, hpov⟩, hto⟩, -⟩, hfa⟩, hc⟩ := hok
  simp only [Trie.seq_eq] at hc
  have hpar' : f.params = (List.range f.params.length).map V.n := by
    rw [List.range_eq_range']; exact paramsN_eq _ 0 hpar
  generalize hXdef : (⟨pows, H.readT, trieFrom H.sig.pre 0 .nil, trieFrom H.calls 0 .nil, trieFrom H.rets 0 .nil,
    trieFrom H.res 0 .nil, keysT H.divs .nil, keysT H.hvs .nil, H.gargs, sigOf, H.sig, f.params, [],
    keysT H.eqs .nil, H.fas, H.ders⟩ : CX) = X at hc
  have hX : XOk sigOf H rd f σ X := by
    subst hXdef
    exact { R := rfl
            pre := fun k c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])
            pows := hp
            sigOf := rfl
            ga := rfl
            sig := rfl
            params := rfl
            res := fun i c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])
            term := fun q hq ↦ by
              have ho := List.all_eq_true.mp hto q hq
              simp only [Bool.and_eq_true] at ho
              exact (ltF_congr (idxOver_val hpar' ho.1) (idxOver_val hpar' ho.2)).mp (hE q hq)
            resF := hR
            path := fun c hc ↦ by simp at hc
            fas := rfl
            ders := rfl
            der := hD
            gw := hG }
  set W0 : K → Prop := fun x ↦ PreSet rd H.sig (f.params.map σ ++ ownG H.sig σ) x with hW0
  have hpreW : ∀ c ∈ H.sig.pre, W0 (c.addr σ) := fun c hc ↦
    Or.inl (Or.inl ⟨c, hc, addr_pre hpar' hpov hc _⟩)
  have fin : CovC sigOf H rd σ W0 es → ((∀ e ∈ es, EvM sigOf rd σ e) →
      PostW sigOf H rd σ (f.params.map σ) (fun x ↦ W0 x ∨ EW sigOf rd σ es x) vs) →
      ReadsOkP sigOf H rd σ (f.params.map σ) es ∧ ((∀ e ∈ es, EvM sigOf rd σ e) →
        (PostOkC sigOf H rd σ (f.params.map σ) es vs ∧
          (H.fas = [] → PostOkW sigOf H rd σ (f.params.map σ) es vs)) ∧
        RetMOk H.sig (f.params.map σ) (vs.map σ) ∧ RetVOk rd H.sig (f.params.map σ ++ vs.map σ) ∧
          RetEqOk H.sig (f.params.map σ ++ vs.map σ)) :=
    fun h1 h2 ↦ ⟨fun es1 e es2 he hm ↦ h1 es1 e es2 he hm, fun hM ↦
      ⟨⟨⟨(h2 hM).1.mono fun x hx ↦ hx.imp_right (fax_faw hfa hw),
        fun x hx ↦ ((h2 hM).2.1 x hx).imp_right (fax_faw hfa hw),
        fun x hx ↦ ((h2 hM).2.2.2.2.2.1 x hx).imp_right (fax_faw hfa hw),
        (h2 hM).2.2.2.2.2.2.mono fun x hx ↦ hx.imp_right (fax_faw hfa hw)⟩,
        fun hn ↦ ⟨(h2 hM).1.mono fun x hx ↦ hx.resolve_right (noFAX hn),
          fun x hx ↦ ((h2 hM).2.1 x hx).resolve_right (noFAX hn),
          fun x hx ↦ ((h2 hM).2.2.2.2.2.1 x hx).resolve_right (noFAX hn),
          (h2 hM).2.2.2.2.2.2.mono fun x hx ↦ hx.resolve_right (noFAX hn)⟩⟩,
      (h2 hM).2.2.1, (h2 hM).2.2.2.1, (h2 hM).2.2.2.2.1⟩⟩
  cases hi : initC X with
  | none => simp [hi] at hc
  | some st0 =>
    simp only [hi] at hc
    have hs0 : StOk rd W0 σ st0 := by
      have := initC_ok (X := X) (σ := σ) (rd := rd) hi
      rwa [hX.sig, hX.params] at this
    split at hc
    · obtain ⟨st', hst⟩ := Option.isSome_iff_exists.mp hc
      have hw' : walk σ (bodyC H.dups f.body) = .ret es vs := by rw [walk_bodyC]; exact hw
      exact fin ((chkC_ok hX _ hpreW hst hs0).1.2 es vs hw' hh).1
        fun hM ↦ ((chkC_ok hX _ hpreW hst hs0).1.2 es vs hw' hh).2 (evsOk_of hh hM)
    · rename_i ei hterm
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨hrm, hpv⟩, hre⟩, hpq⟩, hc⟩ := hc
      have hrm : H.sig.retM = [] := List.isEmpty_iff.mp hrm
      have hpv : H.sig.postV = [] := List.isEmpty_iff.mp hpv
      have hre : H.sig.retEq = [] := List.isEmpty_iff.mp hre
      have hpq : H.sig.postQ = [] := List.isEmpty_iff.mp hpq
      unfold loopC at hc
      split at hc
      · rename_i endc c0 g args rest hend hrev
        split at hc
        · rename_i pre hls
          split at hc
          · rename_i st1 hst1
            split at hc
            · rename_i st2 hst2
              obtain ⟨c, i', p0, prest, hps, hbody, -, -⟩ := loopShape_spec hls
              have hlb := loopBody_of hbody
              -- the tail's statement, read off the reversed body
              have htl : Stmt.callIf c0 g args = .callIf c f.name (i' :: prest) := by
                have := congrArg List.reverse hbody
                rw [hrev] at this
                simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
                  List.cons_append, List.cons.injEq] at this
                exact this.2.1
              simp only [Stmt.callIf.injEq] at htl
              obtain ⟨h1, h2, h3⟩ := htl
              subst c0 g args
              -- the parameters
              have hp0 : p0 = V.n 0 ∧ f.params = V.n 0 :: prest := by
                have h1 := hpar'.symm.trans hps
                cases hm : f.params.length with
                | zero => rw [hm] at h1; simp at h1
                | succ k =>
                  rw [hm, List.range_succ_eq_map, List.map_cons] at h1
                  obtain ⟨h2, -⟩ := List.cons.inj h1
                  exact ⟨h2.symm, by rw [hps, ← h2]⟩
              obtain ⟨rfl, hps'⟩ := hp0
              -- the path
              obtain ⟨p0', prest', c', i'', es1, hps2, hw1, hes, hi'', hc''⟩ :=
                Res.loop_path (rd := rd) (by rw [hlb]; exact hls) hw hh
              rw [hlb] at hw1
              have hw2 := walk_tail (c := c) (g := f.name) (i' := i') (ps := prest) hw1
              rw [← hbody, hw] at hw2
              simp only [Out.ret.injEq] at hw2
              obtain ⟨hes2, rfl⟩ := hw2
              rw [hps', List.cons.injEq] at hps2
              obtain ⟨rfl, rfl⟩ := hps2
              rw [hes2] at hes
              simp only [List.append_cancel_left_eq, List.cons.injEq, Ev.inK.injEq, and_true] at hes
              obtain ⟨rfl, hee⟩ := hes
              have hi'eq : i'' = i' := by
                split_ifs at hee <;>
                  simp only [Ev.skip.injEq, Ev.call.injEq, List.cons.injEq, true_and, and_true] at hee <;>
                  exact hee.symm
              subst hi'eq
              subst hes2
              -- the body, then the tail
              have hh1 := (holds_append hh).1
              have hb1 := chkC_ok (rd := rd) hX pre hpreW hst1 hs0
              have hcov1 := hb1.1.1 es1 hw1 hh1
              have hpre1 : ∀ c ∈ H.sig.pre, (fun x ↦ W0 x ∨ EW sigOf rd σ es1 x) (c.addr σ) :=
                fun c hc ↦ Or.inl (hpreW c hc)
              have htl := fun hm1 : (∀ e ∈ es1, EvM sigOf rd σ e) ↦
                callIfC_ok hX hpre1 (hb1.2 es1 hw1 (evsOk_of hh1 hm1)) hst2
              have hterm' : (CIdx.val 0, ei) ∈ H.sig.term := by rw [hterm]; exact List.mem_singleton_self _
              have hover : idxOver f.params.length ei = true := by
                have := List.all_eq_true.mp hto _ hterm'
                simp only [Bool.and_eq_true] at this
                exact this.2
              refine fin (covC_append hcov1 fun hm1 ↦ ?_) fun hM ↦ PostW0.toW (((tailC_ok hX hself hrm hpv hre hpq
                (fun c hc ↦ Or.inl (hpre1 c hc)) (htl fun e he ↦ hM e (List.mem_append_left _ he)).2 hterm' hend
                hpar' hover hps' hi'' hc'' hc)).mono fun x hx ↦ ?_)
              · show CovC sigOf H rd σ _ ([Ev.inK c] ++ [_])
                refine covC_append (covC_single trivial) fun _ ↦ covC_single ?_
                split_ifs with h0
                · trivial
                · exact ReqOk.mono (fun _ ↦ Or.inl) ((htl hm1).1 h0)
              · rcases hx with ((hx | hx) | hx) | hx
                · exact Or.inl hx
                · exact Or.inr (ew_append_left hx)
                · exact Or.inr (ew_append_right hx)
                · exact Or.inr (ew_append_right hx)
            · cases hc
          · cases hc
        · cases hc
      · cases hc
    · cases hc

/-- **The heap check with calls and loops is sound**: on a path of a function passing `heapOkC` that
returns, its events holding and each entered call's callee guarantees' runs having their exponents,
given its entry facts and its residuals, every event's needs are written before it and its
guarantees are written at return. A loop helper's own signature is `sigOf`'s for its name. -/
theorem heapOkC_sound {pows : PowTree} (hp : pows.Ok) {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOkC pows sigOf f H = true) (hself : sigOf f.name = H.sig) {σ : Val} {rd : Reader}
    {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hM : ∀ e ∈ es, EvM sigOf rd σ e) (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) (hD : DerOk H rd σ)
    (hG : GwOk H.sig rd σ) :
    ReadsOkC sigOf H rd σ (f.params.map σ) es ∧ PostOkC sigOf H rd σ (f.params.map σ) es vs ∧
      RetMOk H.sig (f.params.map σ) (vs.map σ) ∧ RetVOk rd H.sig (f.params.map σ ++ vs.map σ) ∧
      RetEqOk H.sig (f.params.map σ ++ vs.map σ) :=
  have h := heapOkC_soundP hp hok hself hw hh hE hR hD hG
  ⟨readsOkC_of_P h.1 hM, (h.2 hM).1.1, (h.2 hM).2⟩

/-- `heapOkC_sound` with no frame run cell guaranteed (`HCert.fas` empty): the guarantees written by the
events. -/
theorem heapOkC_soundW {pows : PowTree} (hp : pows.Ok) {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOkC pows sigOf f H = true) (hself : sigOf f.name = H.sig) {σ : Val} {rd : Reader}
    {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hM : ∀ e ∈ es, EvM sigOf rd σ e) (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) (hD : DerOk H rd σ)
    (hG : GwOk H.sig rd σ) (hn : H.fas = []) : PostOkW sigOf H rd σ (f.params.map σ) es vs :=
  ((heapOkC_soundP hp hok hself hw hh hE hR hD hG).2 hM).1.2 hn

end Main

/-- **Constant preconditions** (`main`'s public input cells): a precondition of a signature whose preconditions
are cells only, each constant (`⟨[], k⟩`), is the address `g^k` of one of them, whatever the words. -/
theorem preSet_const {rd : Reader} {G : HSig} {ws : List E} {x : K} (hR : G.preR = []) (hP : G.preP = [])
    (hPR : G.prePR = []) (hc : ∀ c ∈ G.pre, c.bases = []) (h : PreSet rd G ws x) :
    ∃ c ∈ G.pre, x = addressOfIndex c.off := by
  rcases h with (⟨c, hc', rfl⟩ | ⟨r, hr, -⟩) | (⟨p, hp, -⟩ | ⟨p, hp, -⟩)
  · refine ⟨c, hc', ?_⟩
    rw [CCell.addrW, valW_nil (by simp [hc c hc'])]
    simp
  · rw [hR] at hr; cases hr
  · rw [hP] at hp; cases hp
  · rw [hPR] at hp; cases hp

/-! ## Milestone 1's statement -/

/-- **Milestone 1's statement, a special case**: on a path entering no call, of a function with no
precondition run or pointer fact, `ReadsOkC` is `ReadsWritten`. -/
theorem readsWritten_of_C {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {f : Fn}
    (hpar : f.params = (List.range f.params.length).map V.n) (hpov : preOver f.params.length H.sig.pre = true)
    (hR : H.sig.preR = []) (hP : H.sig.preP = []) (hPR : H.sig.prePR = []) {es : List Ev}
    (hnc : ∀ g a r, Ev.call g a r ∉ es)
    (h : ReadsOkC sigOf H rd σ (f.params.map σ) es) : ReadsWritten H σ es := by
  intro es1 a es2 x he hr
  rcases h es1 (.atom a) es2 he x hr with ((⟨c, hc, hx⟩ | ⟨r, hr', -⟩) | (⟨p, hp, -⟩ | ⟨p, hp, -⟩)) |
    ⟨e, he1, hx⟩
  · exact Or.inl ⟨c, hc, by rw [← addr_pre hpar hpov hc _, hx]⟩
  · rw [hR] at hr'; simp at hr'
  · rw [hP] at hp; simp at hp
  · rw [hPR] at hp; simp at hp
  · cases e with
    | atom b => exact Or.inr ⟨b, he1, hx⟩
    | call g a' r => exact absurd (by rw [he]; exact List.mem_append_left _ he1) (hnc g a' r)
    | inK _ => exact hx.elim
    | skip _ _ => exact hx.elim

end

end LeanVM.Guest.CoreMode
