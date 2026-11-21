module

public import NativeVm.Code.Phase7.RingBuf

/-!
# Ring switching's coefficients

`coeffK fO gO cO`: `ringCoefficients f g` (`c_(8p+b) = g_b^(2^(8p)) · f_p`) from `f` at work words
`fO` and `g` at `gO` (eight elements each) to `cO`, `rbp` the working area: one `cStep p` per
challenge `f_p`, its row by `mfRow p` (each `g_b` raised by `esqn`, then times `f_p` in `B`).
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64 wp_load wp_store wp_storei)

variable {s : QState} {F : QState → Prop}

/-- `dst[i] := frobenius8 src[i] p · B`, `src` at `r14`, `dst` at `rsi`, `r15` elements. -/
def mfRow (p : Nat) : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .r9 (at_ .r14 0)), I (.load .r10 (at_ .r14 8)), I (.movi .rdx (Int64.ofNat (8 * p))),
  esqn, emul, I (.store (at_ .rsi 0) .r9), I (.store (at_ .rsi 8) .r10),
  I (.addi .r14 16), I (.addi .rsi 16), I (.subi .r15 1)])

theorem toNat_ofNat8 {p : Nat} (hp : p < 2 ^ 59) : (Int64.ofNat (8 * p)).toUInt64.toNat = 8 * p := by
  rw [show (Int64.ofNat (8 * p)).toUInt64 = (8 * p).toUInt64 by rfl, toNat_toUInt64 (by omega)]

theorem esqn_frob {x : E} {p : Nat} : x ^ 2 ^ (8 * p) = frobenius8 x p := by
  rw [frobenius8, ringMapWidth]

/-- **`mfRow p` writes `src.map (frobenius8 · p · b)`.** -/
theorem mfRow_spec {G : List E} {p : Nat} {q d : UInt64} (hp : p < 2 ^ 32)
    (h14 : s.reg .r14 = q) (hsi : s.reg .rsi = d) (hG : EArr s.mem q G)
    (hn : s.reg .r15 = G.length.toUInt64) (hlen : G.length < 2 ^ 59)
    (hdom : ∀ k < 2 * G.length, (s.mem (ew d k)).isSome)
    (hsep : ∀ k < 2 * G.length, ∀ j < 2 * G.length, ew d k ≠ ew q j) :
    WP (mfRow p) s (fun s' ↦
      EArr s'.mem d (G.map fun x ↦ frobenius8 x p * eOf (s.reg .r11) (s.reg .r12)) ∧
      (∀ a, (∀ k < 2 * G.length, a ≠ ew d k) → s'.mem a = s.mem a) ∧
      s'.reg .rbp = s.reg .rbp ∧ s'.reg .r13 = s.reg .r13 ∧ s'.reg .r11 = s.reg .r11 ∧
      s'.reg .r12 = s.reg .r12) F := by
  set n := G.length with hn_def
  set b := eOf (s.reg .r11) (s.reg .r12) with hb
  rw [EArr_iff_EW] at hG
  unfold mfRow
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r14 = ew q (2 * i) ∧ t.reg .rsi = ew d (2 * i) ∧
      t.reg .r15 = (n - i).toUInt64 ∧
      (∀ k < i, EW t.mem d k (frobenius8 (G.getD k 0) p * b)) ∧
      (∀ k < 2 * n, (t.mem (ew d k)).isSome) ∧
      (∀ a, (∀ k < 2 * n, a ≠ ew d k) → t.mem a = s.mem a) ∧
      t.reg .rbp = s.reg .rbp ∧ t.reg .r13 = s.reg .r13 ∧ t.reg .r11 = s.reg .r11 ∧
      t.reg .r12 = s.reg .r12)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, fun k hk ↦ absurd hk (Nat.not_lt_zero _), hdom,
      fun _ _ ↦ rfl, rfl, rfl, rfl, rfl⟩
    · rw [h14, Nat.mul_zero, ew_zero]
    · rw [hsi, Nat.mul_zero, ew_zero]
    · rw [hn, Nat.sub_zero]
  · intro t ⟨i, hi, t14, tsi, t15, hD, hW, hF, tbp, t13, t11, t12⟩ hc
    have hin : i < n := cnt_lt (t15 ▸ cond_test_true hc)
    have src : ∀ j < 2 * n, t.mem (ew q j) = s.mem (ew q j) := fun j hj ↦
      hF _ fun k hk e ↦ hsep k hk j hj e.symm
    obtain ⟨a0, a1⟩ := hG i hin
    refine WP.load_at (by rw [t14, int64Zero_toUInt64, ew_zero', src _ (by omega)]; exact a0) ?_
    refine WP.load_at (by rsimp; rw [t14, ew_one, src _ (by omega)]; exact a1) ?_
    fstep
    refine WP.then (esqn_spec _) fun t1 ⟨e1, _, m1, f1⟩ ↦ ?_
    rsimp at e1 m1
    refine WP.then (emul_spec _) fun t2 ⟨e2, m2, f2⟩ ↦ ?_
    have k2 : ∀ r ∉ eRegs, t2.reg r = t.reg r := fun r hr ↦ by
      rw [f2 r hr, f1 r hr]
      simp only [eRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rsimp
      simp [hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
    have hv : eOf (t2.reg .r9) (t2.reg .r10) = frobenius8 (G.getD i 0) p * b := by
      rw [e2, e1, eOf_lanes, toNat_ofNat8 (by omega), esqn_frob, f1 .r11 (by decide),
        f1 .r12 (by decide)]
      rsimp
      rw [t11, t12]
    obtain ⟨v0, v1⟩ := eOf_eq_iff.mp hv
    have w0 : t2.reg .rsi + 0 = ew d (2 * i) := by rw [k2 .rsi (by decide), tsi, ew_zero']
    have w1 : t2.reg .rsi + 8 = ew d (2 * i + 1) := by rw [k2 .rsi (by decide), tsi, ew_one]
    refine WP.store_at (by rw [int64Zero_toUInt64, w0, m2, m1]; exact hW _ (by omega)) ?_
    refine WP.store_at (by
      rsimp; rw [w1]; exact isSome_setMem (by rw [m2, m1]; exact hW _ (by omega)) _ _) ?_
    fstep; fstep; fstep; fdone
    rw [w0, w1]
    simp only [setMem_mem_fun, m2, m1]
    refine ⟨⟨i + 1, hin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [k2 .r14 (by decide), t14, ew_step]
    · rw [k2 .rsi (by decide), tsi, ew_step]
    · rw [k2 .r15 (by decide), t15, cnt_succ hin]
    · intro k hk
      rcases Nat.lt_or_ge k i with hki | hki
      · exact EW_store_ne (i := i) (by omega) (by omega) (by omega) (hD k hki)
      · obtain rfl : k = i := by omega
        exact EW_store_eq (by omega) v0 v1
    · intro k hk
      split
      · rfl
      · split
        · rfl
        · exact hW k hk
    · exact frame_store hin hF
    · rw [k2 .rbp (by decide), tbp]
    · rw [k2 .r13 (by decide), t13]
    · rw [f2 .r11 (by decide), f1 .r11 (by decide)]; rsimp; exact t11
    · rw [f2 .r12 (by decide), f1 .r12 (by decide)]; rsimp; exact t12
    · rw [k2 .r15 (by decide), t15, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, _, t15, hD, _, hF, tbp, t13, t11, t12⟩ hc
    obtain rfl : i = n := cnt_eq (by omega) hi (t15 ▸ cond_test_false hc)
    refine ⟨?_, hF, tbp, t13, t11, t12⟩
    rw [EArr_iff_EW, List.length_map]
    intro k hk
    have e : (G.map fun x ↦ frobenius8 x p * b).getD k 0 = frobenius8 (G.getD k 0) p * b := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rw [e]
    exact hD k hk

/-! ## Unrolled loops over indices -/

theorem WP.blk_range' (f : Nat → Stmt) (Inv : Nat → QState → Prop) (n : Nat)
    (hstep : ∀ k < n, ∀ s, Inv k s → WP (f k) s (Inv (k + 1)) F) :
    ∀ (m k : Nat) (s : QState), k + m ≤ n → Inv k s →
      WP (blk ((List.range' k m).map f)) s (Inv (k + m)) F
  | 0, k, s, _, h => WP.blk_nil h
  | m + 1, k, s, hk, h => by
    rw [List.range'_succ, List.map_cons]
    refine WP.blk_cons (WP.mono (hstep k (by omega) s h) (fun s₁ h₁ ↦ ?_) fun _ h ↦ h)
    have := WP.blk_range' f Inv n hstep m (k + 1) s₁ (by omega) h₁
    rwa [show k + 1 + m = k + (m + 1) by omega] at this

/-- **A block of `f 0, …, f (n - 1)`**, each taking the invariant one step. -/
theorem WP.blk_range (f : Nat → Stmt) (Inv : Nat → QState → Prop) (n : Nat)
    (hstep : ∀ k < n, ∀ s, Inv k s → WP (f k) s (Inv (k + 1)) F) (h0 : Inv 0 s) :
    WP (blk ((List.range n).map f)) s (Inv n) F := by
  have := WP.blk_range' f Inv n hstep n 0 s (by omega) h0
  rw [Nat.zero_add] at this
  rwa [List.range_eq_range']

/-! ## The coefficients -/

/-- Challenge `f_p`'s row of coefficients. -/
def cStep (fO gO cO p : Nat) : Stmt := blk [
  I (.load .r11 (at_ .rbp (wdisp (fO + 2 * p)))), I (.load .r12 (at_ .rbp (wdisp (fO + 2 * p + 1)))),
  I (.lea .r14 (at_ .rbp (wdisp gO))), I (.lea .rsi (at_ .rbp (wdisp (cO + 16 * p)))),
  I (.movi .r15 8), mfRow p]

/-- `ringCoefficients f g` at work words `cO`. -/
def coeffK (fO gO cO : Nat) : Stmt := blk ((List.range 8).map (cStep fO gO cO))

theorem ringCoefficients_take_succ (f g : List E) {k : Nat} (hk : k < f.length) :
    ringCoefficients (f.take (k + 1)) g =
      ringCoefficients (f.take k) g ++ g.map (fun x ↦ frobenius8 x k * f.getD k 0) := by
  rw [take_succ_getD f hk, ringCoefficients_snoc, List.length_take, Nat.min_eq_left (by omega),
    List.map_map]
  rfl

theorem EArr_word {mem : UInt64 → Option UInt64} {p : UInt64} {L : List E} (h : EArr mem p L)
    {k : Nat} (hk : k < L.length) :
    mem (ew p (2 * k)) = some ((L.getD k 0).limb 0).lane ∧
      mem (ew p (2 * k + 1)) = some ((L.getD k 0).limb 1).lane :=
  (EArr_iff_EW.mp h) k hk

/-- **`coeffK` writes `ringCoefficients`.** -/
theorem coeffK_spec {W : UInt64} {fO gO cO : Nat} {Fl Gl : List E} (hbp : s.reg .rbp = W)
    (hF : EArr s.mem (ew W fO) Fl) (hFl : Fl.length = 8) (hG : EArr s.mem (ew W gO) Gl)
    (hGl : Gl.length = 8) (hdom : ∀ k < 128, (s.mem (ew W (cO + k))).isSome)
    (hfc : cO + 128 ≤ fO ∨ fO + 16 ≤ cO) (hgc : cO + 128 ≤ gO ∨ gO + 16 ≤ cO)
    (hb : fO + 16 < 2 ^ 59 ∧ gO + 16 < 2 ^ 59 ∧ cO + 128 < 2 ^ 59) :
    WP (coeffK fO gO cO) s (fun s' ↦ s'.reg .rbp = W ∧
      EArr s'.mem (ew W cO) (ringCoefficients Fl Gl) ∧
      ∀ a, (∀ k < 128, a ≠ ew W (cO + k)) → s'.mem a = s.mem a) F := by
  have hRun := WP.blk_range (F := F) (s := s) (cStep fO gO cO) (fun k t ↦ t.reg .rbp = W ∧
      EArr t.mem (ew W cO) (ringCoefficients (Fl.take k) Gl) ∧
      (∀ j < 128, (t.mem (ew W (cO + j))).isSome) ∧
      ∀ a, (∀ j < 128, a ≠ ew W (cO + j)) → t.mem a = s.mem a) 8 ?_
    ⟨hbp, by simp [ringCoefficients, EArr.nil], hdom, fun _ _ ↦ rfl⟩
  · refine WP.mono hRun (fun s' ⟨h1, h2, _, h4⟩ ↦ ⟨h1, ?_, h4⟩) fun _ h ↦ h
    rwa [List.take_of_length_le (by omega)] at h2
  intro k hk t ⟨tbp, tC, tW, tF⟩
  have outC : ∀ j, (j < cO ∨ cO + 128 ≤ j) → j < 2 ^ 60 → t.mem (ew W j) = s.mem (ew W j) :=
    fun j hj hj' ↦ tF _ fun i hi e ↦ by
      have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega
  obtain ⟨f0, f1⟩ := EArr_word hF (k := k) (by omega)
  have hGt : EArr t.mem (ew W gO) Gl := EArr_congr (fun j hj ↦ by
    rw [ew_ew, outC _ (by omega) (by omega), ← ew_ew]) hG
  unfold cStep
  refine wp_load (v := ((Fl.getD k 0).limb 0).lane) (eval_w tbp _) (by
    rw [outC _ (by omega) (by omega), ← ew_ew]; exact f0) ?_
  refine wp_load (v := ((Fl.getD k 0).limb 1).lane) (eval_w (by rsimp; exact tbp) _) (by
    rsimp
    rw [outC _ (by omega) (by omega), show fO + 2 * k + 1 = fO + (2 * k + 1) by omega, ← ew_ew]
    exact f1) ?_
  fstep; fstep; fstep
  rw [at_wdisp, at_wdisp]
  rsimp
  rw [tbp]
  refine WP.then (WP.withDom (mfRow_spec (F := F) (G := Gl) (p := k) (q := ew W gO)
    (d := ew W (cO + 16 * k)) (by omega) (by rsimp) (by rsimp) (by rsimp; exact hGt)
    (by rsimp; rw [hGl]; rfl) (by omega) (fun j hj ↦ ?_) (fun j hj i hi ↦ ?_)))
    fun t1 ⟨⟨h1, f1', bp1, _, _, _⟩, d1⟩ ↦ ?_
  · rsimp; rw [ew_ew, Nat.add_assoc]; exact tW (16 * k + j) (by omega)
  · rw [ew_ew, ew_ew]
    exact fun e ↦ by have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega
  rsimp at h1 f1' bp1
  have hfk : eOf ((Fl.getD k 0).limb 0).lane ((Fl.getD k 0).limb 1).lane = Fl.getD k 0 :=
    eOf_lanes _
  rw [hfk] at h1
  have keepC : ∀ j < 16 * k, t1.mem (ew W (cO + j)) = t.mem (ew W (cO + j)) := fun j hj ↦
    f1' _ fun i hi e ↦ by
      rw [ew_ew] at e; have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega
  apply WP.blk_nil
  refine ⟨by rw [bp1]; exact tbp, ?_, fun j hj ↦ ?_, fun a ha ↦ ?_⟩
  · rw [ringCoefficients_take_succ Fl Gl (by omega), EArr.append_iff, ringCoefficients_length,
      List.length_take, Nat.min_eq_left (by omega), hGl, add16, ew_ew]
    refine ⟨EArr_congr (fun j hj ↦ ?_) tC, ?_⟩
    · rw [ringCoefficients_length, List.length_take, Nat.min_eq_left (by omega), hGl] at hj
      rw [ew_ew, keepC _ (by omega)]
    · rwa [show cO + 2 * (k * 8) = cO + 16 * k by ring]
  · rw [d1]; rsimp; exact tW j hj
  · rw [f1' a fun i hi e ↦ ha (16 * k + i) (by rw [hGl] at hi; omega) (by rw [e, ew_ew,
      Nat.add_assoc])]
    exact tF a ha

end NativeVm.Code.Ring
