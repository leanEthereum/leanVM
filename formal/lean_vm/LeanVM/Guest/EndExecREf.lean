/-
  LeanVM.Guest.EndExecREf

  The exponent facts' families (`Res.efFamB`), sound on a reference frame whose bases satisfy the
  facts.
-/

module

public import LeanVM.Guest.Mode.ResFam
public import LeanVM.Guest.Res.EfDefs
public import LeanVM.Guest.Value.Bits

/-!
# The exponent facts' families, sound

`EFactsOk M fp F`: the facts `F` hold of the reference `M` at frame `fp` (`EPowOk`, `ELeOk`,
`ECurOk`). `efHi_le`, `efLo_le`: an exponent's value lies within the bounds; `efLeB_le`: the
ordered exponents' values are ordered, and the first has one. `efFam_sound`: each family's
residual, its bases having words (`RIn`), holds.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Guest.Res (EFacts efPow efHi efLo efLeB efLtB efRunB efPtB efTileB efCurRes efCurB efFamB)
open LeanVM.Prover.Exec
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- A listed power: the base's word is `g^x`, `lo ≤ x ≤ hi`, `x < 2^62`. -/
def EPowOk (M : ℕ → E) (fp : ℕ) (p : Base × ℕ × ℕ) : Prop :=
  ∀ v, RBase M fp p.1 v → ∃ x, v = ofK (g ^ x) ∧ p.2.1 ≤ x ∧ x ≤ p.2.2 ∧ x < 2 ^ 62

/-- A listed order: `X`'s word is `g^x`, and `Y`'s, `g^y` with `x ≤ y + c`. -/
def ELeOk (M : ℕ → E) (fp : ℕ) (l : Base × Base × ℕ) : Prop :=
  ∀ vx, RBase M fp l.1 vx → ∃ x, vx = ofK (g ^ x) ∧ x < 2 ^ 62 ∧
    ∀ vy, RBase M fp l.2.1 vy → ∃ y, vy = ofK (g ^ y) ∧ y < 2 ^ 62 ∧ x ≤ y + l.2.2

/-- A listed cursor: its word is the stream's times `g^p`, room for `n` words past it. -/
def ECurOk (M : ℕ → E) (fp : ℕ) (c : Base × Base × ℕ) : Prop :=
  ∀ v s, RBase M fp c.1 v → RBase M fp c.2.1 s → ∃ p, v = s * ofK (g ^ p) ∧ p + c.2.2 ≤ 8192

/-- **The facts hold** of the reference `M` at frame `fp`. -/
structure EFactsOk (M : ℕ → E) (fp : ℕ) (F : EFacts) : Prop where
  pows : ∀ p ∈ F.pows, EPowOk M fp p
  les : ∀ l ∈ F.les, ELeOk M fp l
  curs : ∀ c ∈ F.curs, ECurOk M fp c

section

variable {M : ℕ → E} {fp : ℕ} {F : EFacts}

theorem efPow_mem {B : Base} {lo hi : ℕ} (h : efPow F B = some (lo, hi)) : (B, lo, hi) ∈ F.pows := by
  unfold efPow at h
  obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hp
  have hB : p.1 = B := by simpa using List.find?_some hp
  obtain ⟨B', lo', hi'⟩ := p
  simp only at hpe hB
  subst hB
  rw [hpe] at hm
  exact hm

theorem efPow_val (hF : EFactsOk M fp F) {B : Base} {lo hi : ℕ} (h : efPow F B = some (lo, hi)) {v : E}
    (hv : RBase M fp B v) : ∃ x, v = ofK (g ^ x) ∧ lo ≤ x ∧ x ≤ hi ∧ x < 2 ^ 62 :=
  hF.pows _ (efPow_mem h) v hv

/-- An exponent's word as a listed power. -/
theorem ridx_pow {B : Base} {c y x : ℕ} {v : E} (hv : RBase M fp B v) (hx : v = ofK (g ^ x)) (hx62 : x < 2 ^ 62)
    (hy : RIdx M fp (.ex B c) y) : y = x + c := by
  obtain ⟨v', e', hv', hve, he', rfl⟩ := hy
  rw [← rbase_uniq hv hv', hx] at hve
  have := ofK_gpow_inj (by omega) (by omega) hve
  omega

theorem efHi_le (hF : EFactsOk M fp F) {a : Mode.Idx} {x : ℕ} (h : efHi F a = some x) {y : ℕ} (hy : RIdx M fp a y) :
    y ≤ x := by
  cases a with
  | num n => simp only [efHi, Option.some.injEq] at h; change y = n at hy; omega
  | ex B c =>
    simp only [efHi] at h
    obtain ⟨⟨lo, hi⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v, e', hv, hve, he', rfl⟩ := hy
    obtain ⟨z, hz, -, hzh, hz62⟩ := efPow_val hF hp hv
    rw [hz] at hve
    have := ofK_gpow_inj (by omega) (by omega) hve
    simp only
    omega

theorem efLo_le (hF : EFactsOk M fp F) {a : Mode.Idx} {x : ℕ} (h : efLo F a = some x) {y : ℕ} (hy : RIdx M fp a y) :
    x ≤ y := by
  cases a with
  | num n => simp only [efLo, Option.some.injEq] at h; change y = n at hy; omega
  | ex B c =>
    simp only [efLo] at h
    obtain ⟨⟨lo, hi⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v, e', hv, hve, he', rfl⟩ := hy
    obtain ⟨z, hz, hzl, -, hz62⟩ := efPow_val hF hp hv
    rw [hz] at hve
    have := ofK_gpow_inj (by omega) (by omega) hve
    simp only
    omega

/-- An exponent the bounds name has a value, once its base has a word. -/
theorem efHi_ex (hF : EFactsOk M fp F) {a : Mode.Idx} {x : ℕ} (h : efHi F a = some x) (hin : RIdxIn M fp a) :
    ∃ y, RIdx M fp a y := by
  cases a with
  | num n => exact ⟨n, rfl⟩
  | ex B c =>
    simp only [efHi] at h
    obtain ⟨⟨lo, hi⟩, hp, -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v, hv⟩ := hin
    obtain ⟨z, hz, -, -, hz62⟩ := efPow_val hF hp hv
    exact ⟨z + c, v, z, hv, hz, hz62, rfl⟩

theorem efLo_ex (hF : EFactsOk M fp F) {a : Mode.Idx} {x : ℕ} (h : efLo F a = some x) (hin : RIdxIn M fp a) :
    ∃ y, RIdx M fp a y := by
  cases a with
  | num n => exact ⟨n, rfl⟩
  | ex B c =>
    simp only [efLo] at h
    obtain ⟨⟨lo, hi⟩, hp, -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v, hv⟩ := hin
    obtain ⟨z, hz, -, -, hz62⟩ := efPow_val hF hp hv
    exact ⟨z + c, v, z, hv, hz, hz62, rfl⟩

/-- **Ordered exponents**: the first has a value once its base has a word, and every value of it is
at most every value of the second. -/
theorem efLeB_le (hF : EFactsOk M fp F) {a b : Mode.Idx} (h : efLeB F a b = true) (hin : RIdxIn M fp a) :
    (∃ y, RIdx M fp a y) ∧ ∀ y1 y2, RIdx M fp a y1 → RIdx M fp b y2 → y1 ≤ y2 := by
  unfold efLeB at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · cases ha : efHi F a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases hb : efLo F b with
      | none => rw [ha, hb] at h; simp at h
      | some z =>
        rw [ha, hb] at h
        have hxz := of_decide_eq_true h
        exact ⟨efHi_ex hF ha hin, fun y1 y2 h1 h2 ↦
          (efHi_le hF ha h1).trans (hxz.trans (efLo_le hF hb h2))⟩
  · cases a with
    | num => simp at h
    | ex X c1 =>
      cases b with
      | num => simp at h
      | ex Y c2 =>
        simp only [List.any_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨X', Y', c⟩, hl, rfl, rfl, hc⟩ := h
        have hL := hF.les _ hl
        obtain ⟨vx, hvx⟩ := hin
        obtain ⟨x, hx, hx62, -⟩ := hL vx hvx
        refine ⟨⟨x + c1, vx, x, hvx, hx, hx62, rfl⟩, fun y1 y2 h1 h2 ↦ ?_⟩
        obtain ⟨vx', e1, hvx', he1, he1', rfl⟩ := h1
        obtain ⟨vy, e2, hvy, he2, he2', rfl⟩ := h2
        obtain ⟨x', hx', hx'62, hY⟩ := hL vx' hvx'
        obtain ⟨y, hy, hy62, hxy⟩ := hY vy hvy
        rw [hx'] at he1
        rw [hy] at he2
        have h1e := ofK_gpow_inj (by omega) (by omega) he1
        have h2e := ofK_gpow_inj (by omega) (by omega) he2
        simp only at hc hxy
        subst h1e h2e
        omega

/-- A product with a base appended: its word is the product's times the base's. -/
theorem efRbs_snoc {Y : Base} : ∀ {l : List (Base × ℕ)} {w : E}, RBs M fp (l ++ [(Y, 1)]) w →
    ∃ u w', RBase M fp Y u ∧ RBs M fp l w' ∧ w = w' * u
  | [], w, ⟨u, w', hu, hw', hw⟩ => ⟨u, 1, hu, rfl, by rw [hw, show w' = 1 from hw']; ring⟩
  | (b, e) :: l, w, ⟨u, w', hu, hw', hw⟩ => by
    obtain ⟨u2, w2, hu2, hw2, rfl⟩ := efRbs_snoc hw'
    exact ⟨u2, u ^ e * w2, hu2, ⟨u, w2, hu, hw2, rfl⟩, by rw [hw]; ring⟩

theorem efLt_sound (hF : EFactsOk M fp F) {x : Mode.Res} (hx : efLtB F x = true) (hin : RIn M fp x) : RRes M fp x := by
  match x, hx with
  | .lt a b, hx =>
    simp only [efLtB] at hx
    cases ha : efHi F a with
    | none => rw [ha] at hx; simp at hx
    | some xa =>
      cases hb : efLo F b with
      | none => rw [ha, hb] at hx; simp at hx
      | some xb =>
        rw [ha, hb] at hx
        have hlt := of_decide_eq_true hx
        obtain ⟨y1, h1⟩ := efHi_ex hF ha hin.1
        have hb' : ∃ x, efHi F b = some x := by
          cases b with
          | num n => exact ⟨n, rfl⟩
          | ex B c =>
            simp only [efLo] at hb
            obtain ⟨⟨lo, hi⟩, hp, -⟩ := Option.map_eq_some_iff.mp hb
            exact ⟨hi + c, by simp only [efHi, hp, Option.map_some]⟩
        obtain ⟨_, hb2⟩ := hb'
        obtain ⟨y2, h2⟩ := efHi_ex hF hb2 hin.2
        exact ⟨y1, y2, h1, h2, by have := efHi_le hF ha h1; have := efLo_le hF hb h2; omega⟩
  | .sub _ _, hx => simp [efLtB] at hx
  | .nz _, hx => simp [efLtB] at hx
  | .name _, hx => simp [efLtB] at hx

theorem efRun_sound (hF : EFactsOk M fp F) {x : Mode.Res} (hx : efRunB F x = true) (hin : RIn M fp x) :
    RRes M fp x := by
  match x, hx with
  | .sub a [b], hx =>
    simp only [efRunB, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨hq, hal, hbl, haS, hbS, hd⟩, hle⟩ := hx
    obtain ⟨⟨xh, hxh⟩, hle'⟩ := efLeB_le hF hle hin.2
    refine ⟨0, xh, by rw [hal]; rfl, hxh, fun vq hvq jj _ hjj ↦
      ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hy ↦ ⟨jj, ?_, ?_, ?_⟩⟩⟩
    · rw [hbl] at hlo; change ylo = 0 at hlo; omega
    · have := hle' _ _ hxh hy; omega
    · rw [hq] at hvq
      rw [rmono_uniq hvq hvb, haS, hbS, hd]
  | .sub _ [], hx => simp [efRunB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [efRunB] at hx
  | .lt _ _, hx => simp [efRunB] at hx
  | .nz _, hx => simp [efRunB] at hx
  | .name _, hx => simp [efRunB] at hx

theorem efOfKg (n : ℕ) : ofK (g ^ n) = gen ^ n := by rw [LeanVM.Guest.Value.gen_pow_eq_ofK]

/-- The point `Q·X·g^k` at offset `d` inside `Q`'s run from offset `d'`. -/
theorem efPt_core {a b : Mode.Rng} {X : Base} (hal : a.lo = .num 0)
    (hah : a.hi = .num 1) (hbl : b.lo = .num 0) (hbS : b.S = 1) (hbd : b.d ≤ a.q.k + a.d)
    (hle : efLeB F (.ex X (a.q.k + a.d - b.d + 1)) b.hi = true) (hF : EFactsOk M fp F)
    (hq : ∀ vq vb, RMono M fp a.q vq → RMono M fp b.q vb → ∃ u, RBase M fp X u ∧ vq = vb * u * gen ^ a.q.k) :
    RSub M fp a [b] := by
  refine ⟨0, 1, by rw [hal]; rfl, by rw [hah]; rfl, fun vq hvq jj _ hjj ↦
    ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hy ↦ ?_⟩⟩
  obtain rfl : jj = 0 := by omega
  rw [hbl] at hlo
  change ylo = 0 at hlo
  obtain ⟨u, hu, hqe⟩ := hq vq vb hvq hvb
  obtain ⟨⟨_, hy0⟩, hle'⟩ := efLeB_le hF hle ⟨u, hu⟩
  obtain ⟨vX, x, hvX, hxe, hx62, -⟩ := hy0
  have hxy := hle' _ yhi ⟨vX, x, hvX, hxe, hx62, rfl⟩ hy
  refine ⟨x + (a.q.k + a.d - b.d), by omega, by omega, ?_⟩
  rw [rbase_uniq hu hvX, hxe] at hqe
  rw [hqe, hbS, show 1 * (x + (a.q.k + a.d - b.d)) + b.d = x + a.q.k + a.d by omega]
  simp only [efOfKg, mul_zero, zero_add]
  ring

theorem efPt_sound (hF : EFactsOk M fp F) {x : Mode.Res} (hx : efPtB F x = true) : RRes M fp x := by
  match x, hx with
  | .sub a [b], hx =>
    simp only [efPtB] at hx
    cases hh : a.q.bs.head? with
    | none => rw [hh] at hx; simp at hx
    | some p =>
      cases hl : a.q.bs.getLast? with
      | none => rw [hh, hl] at hx; simp at hx
      | some p' =>
        obtain ⟨X, ex⟩ := p
        obtain ⟨Y, ey⟩ := p'
        rw [hh, hl] at hx
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hx
        obtain ⟨⟨hfp, hbk, hal, hah, hbl, -, hbS, hbd⟩, h⟩ := hx
        rcases h with ⟨⟨rfl, hbs⟩, hle⟩ | ⟨⟨rfl, hbs⟩, hle⟩
        · refine efPt_core hal hah hbl hbS hbd hle hF (fun vq vb hvq hvb ↦ ?_)
          obtain ⟨w, hw, rfl⟩ := hvq
          obtain ⟨w', hw', rfl⟩ := hvb
          rw [hbs] at hw
          obtain ⟨u, w2, hu, hw2, rfl⟩ := hw
          refine ⟨u, hu, ?_⟩
          rw [rbs_uniq hw2 hw', hfp, hbk]
          simp only [efOfKg, pow_one]
          ring
        · refine efPt_core hal hah hbl hbS hbd hle hF (fun vq vb hvq hvb ↦ ?_)
          obtain ⟨w, hw, rfl⟩ := hvq
          obtain ⟨w', hw', rfl⟩ := hvb
          rw [hbs] at hw
          obtain ⟨u, w2, hu, hw2, rfl⟩ := efRbs_snoc hw
          refine ⟨u, hu, ?_⟩
          rw [rbs_uniq hw2 hw', hfp, hbk]
          simp only [efOfKg]
          ring
  | .sub _ [], hx => simp [efPtB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [efPtB] at hx
  | .lt _ _, hx => simp [efPtB] at hx
  | .nz _, hx => simp [efPtB] at hx
  | .name _, hx => simp [efPtB] at hx

theorem efTile_sound (hF : EFactsOk M fp F) {x : Mode.Res} (hx : efTileB F x = true) (hin : RIn M fp x) :
    RRes M fp x := by
  match x, hx with
  | .sub a [b1, b2, b3], hx =>
    simp only [efTileB] at hx
    cases hah : a.hi with
    | num => rw [hah] at hx; simp at hx
    | ex X c =>
      cases hb1 : b1.hi with
      | ex => rw [hah, hb1] at hx; simp at hx
      | num c0 =>
        rw [hah, hb1] at hx
        simp only [Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq] at hx
        obtain ⟨⟨⟨lo, hi⟩, hp⟩, hal, haS, rfl, rfl, rfl⟩ := hx
        have hin2 := hin.2
        rw [hah] at hin2
        obtain ⟨v, hv⟩ := hin2
        obtain ⟨z, hz, -, -, hz62⟩ := efPow_val hF hp hv
        refine ⟨0, z + c, by rw [hal]; rfl, by rw [hah]; exact ⟨v, z, hv, hz, hz62, rfl⟩,
          fun vq hvq jj _ hjj ↦ ?_⟩
        by_cases h1 : jj < c0
        · refine ⟨_, List.mem_cons_self, fun vb ylo yhi hvb hlo hy ↦ ⟨jj, ?_, ?_, ?_⟩⟩
          · change ylo = 0 at hlo; omega
          · change yhi = c0 at hy; omega
          · rw [rmono_uniq hvq hvb, haS]
        by_cases h2 : jj < z
        · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun vb ylo yhi hvb hlo hy ↦ ⟨jj, ?_, ?_, ?_⟩⟩
          · change ylo = c0 at hlo; omega
          · have := ridx_pow hv hz hz62 hy; omega
          · rw [rmono_uniq hvq hvb, haS]
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
            fun vb ylo yhi hvb hlo hy ↦ ⟨jj - z, ?_, ?_, ?_⟩⟩
          · change ylo = 0 at hlo; omega
          · change yhi = c at hy; omega
          · obtain ⟨w, hw, rfl⟩ := hvq
            obtain ⟨w', hw', rfl⟩ := hvb
            obtain ⟨u, w2, hu, hw2, rfl⟩ := efRbs_snoc hw'
            rw [rbs_uniq hw2 hw, rbase_uniq hu hv, hz, haS]
            simp only [efOfKg]
            rw [show 1 * jj + a.d = z + (1 * (jj - z) + a.d) by omega]
            ring
  | .sub _ [], hx => simp [efTileB] at hx
  | .sub _ [_], hx => simp [efTileB] at hx
  | .sub _ [_, _], hx => simp [efTileB] at hx
  | .sub _ (_ :: _ :: _ :: _ :: _), hx => simp [efTileB] at hx
  | .lt _ _, hx => simp [efTileB] at hx
  | .nz _, hx => simp [efTileB] at hx
  | .name _, hx => simp [efTileB] at hx

theorem efCur_sound (hF : EFactsOk M fp F) {x : Mode.Res} (hx : efCurB F x = true) : RRes M fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [efCurB, List.any_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨B, St, n⟩, hl, hc, hxe⟩ := hx
    rw [hxe]
    have hC := hF.curs _ hl
    refine ⟨0, 1, rfl, rfl, fun vq hvq jj _ hjj ↦ ⟨_, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hy ↦ ?_⟩⟩
    obtain rfl : jj = 0 := by omega
    change ylo = 0 at hlo
    change yhi = 8192 at hy
    obtain ⟨w, ⟨u, w2, hu, hw2, rfl⟩, rfl⟩ := hvq
    obtain ⟨w', ⟨s, w3, hs, hw3, rfl⟩, rfl⟩ := hvb
    change w2 = 1 at hw2
    change w3 = 1 at hw3
    obtain ⟨p, hp, hpn⟩ := hC u s hu hs
    simp only at hc hpn
    refine ⟨p + a.q.k, by omega, by omega, ?_⟩
    rw [hp, hw2, hw3]
    simp only [efOfKg]
    ring
  | .lt _ _, hx => simp [efCurB] at hx
  | .nz _, hx => simp [efCurB] at hx
  | .name _, hx => simp [efCurB] at hx

/-- **The exponent facts' families hold** where the facts do. -/
theorem efFam_sound (hF : EFactsOk M fp F) {x : Mode.Res} (hx : efFamB F x = true) (hin : RIn M fp x) :
    RRes M fp x := by
  simp only [efFamB, Bool.or_eq_true] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx
  · exact efLt_sound hF hx hin
  · exact efRun_sound hF hx hin
  · exact efPt_sound hF hx
  · exact efTile_sound hF hx hin
  · exact efCur_sound hF hx

end

end

end LeanVM.Guest.EndExec
