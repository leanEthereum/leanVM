/-
  LeanVM.Guest.B1.VerifySub.C.Push

  `verify_sub`'s push total and bus depth (G:3386-3390), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Sizes
public import LeanVM.Guest.B1.VerifySub.Mid

/-!
# The push total, honestly

`vsPushT_complete`: with `kb` in the frame (`140 .. 147`) holding `g^κ_s` and the exponent table at
`4`, every push block reads `g_squares[kb[src]·g^adj] = g^(2^κ_b)` and multiplies it in, so `308` is
`g^S` for the push blocks' sum `S`; `log2_ceil_in_the_exponent` (in `C`) returns `g^(log2Ceil S)` at
`309`, the bus point's buffer is allocated by it, and `vsPushT` holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

theorem vsPushT_noNe : vsPushT.all noNeB = true := by decide +kernel

/-- Block `b`'s pointer `g_squares·kb[src]`. -/
def vsPushM (b : ℕ) : ℕ := if b = 0 then 148 else 147 + 3 * b

/-- Block `b`'s read `g^(2^κ_b)`. -/
def vsPushQ (b : ℕ) : ℕ := if b = 0 then 149 else 148 + 3 * b

theorem vsPush_notS : ∀ b < 54,
    Atom.load (.n (vsPushQ b)) (.n (vsPushM b)) (Tables.blockKappaAdj b) ∉ vsSL := by decide +kernel

theorem vsPushStep_eq (b : ℕ) : vsPushStep b =
    [vsMul (vsPushM b) 4 (140 + Tables.blockKappaSrc.getD b 0),
      vsLd (vsPushQ b) (vsPushM b) (Tables.blockKappaAdj b)] ++
    (if b = 0 then [] else [vsMul (vsPV b) (vsPV (b - 1)) (vsPushQ b)]) := by
  by_cases h : b = 0
  · subst h; rfl
  · simp [vsPushStep, vsPushM, vsPushQ, h]

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsPushT_good (hl : args.length = 6) :
    ∀ s ∈ vsPushT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 121) (blk := vsPushT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsPushT_noNe s hs)] at h

theorem vsPushStep_mem {b : ℕ} (hb : b < 54) {s : Stmt} (hs : s ∈ vsPushStep b) : s ∈ vsPushT :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, hs⟩)

/-- The push blocks' running product, honestly. -/
theorem vsPush_loop (hl : args.length = 6) {logMem : ℕ} {hs : List ℕ}
    (hh : ∀ x ∈ hs, x < 33) (hm : logMem ≤ 32)
    (hkbv : ∀ s < 8, vsσ rd w args (.n (140 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    (hexp : B1.ExpTables rd (vsσ rd w args (.n 4)))
    {C : CallRel} {kret : List E → Prop} :
    ∀ n < 54, ∀ {nx : Prop}, nx →
      vsσ rd w args (.n (vsPV n)) =
        gen ^ ((List.range (n + 1)).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧
      Stmt.HoldsList C rd (vsσ rd w args) ((List.range (n + 1)).flatMap vsPushStep) nx kret := by
  have hG := vsPushT_good (rd := rd) (w := w) hl
  generalize hσ : vsσ rd w args = σ at *
  -- block `b`'s product and read
  have rd2 : ∀ b < 54, σ (.n (vsPushQ b)) = gen ^ 2 ^ pushKappa logMem hs b ∧
      (Atom.mul (.n (vsPushM b)) (.n 4) (.n (140 + Tables.blockKappaSrc.getD b 0))).Holds rd σ ∧
      (Atom.load (.n (vsPushQ b)) (.n (vsPushM b)) (Tables.blockKappaAdj b)).Holds rd σ := by
    intro b hb
    have hsrc := blockKappaSrc_lt b (by show b < 153; omega)
    have hM : 147 < vsPushM b := by unfold vsPushM; split <;> omega
    have gm : Good rd vsSL w σ (.mul (.n (vsPushM b)) (.n 4)
        (.n (140 + Tables.blockKappaSrc.getD b 0))) :=
      hG (vsMul (vsPushM b) 4 (140 + Tables.blockKappaSrc.getD b 0))
        (vsPushStep_mem hb (by rw [vsPushStep_eq]; simp))
    simp only [Good] at gm
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by
      generalize Tables.blockKappaSrc.getD b 0 = src at hsrc ⊢
      generalize vsPushM b = m at hM ⊢
      show 4 < m ∧ 140 + src < m; omega))] at gm
    have hq : LoadHolds rd (σ (.n (vsPushM b))) (Tables.blockKappaAdj b)
        (gen ^ 2 ^ pushKappa logMem hs b) := by
      rw [gm, hkbv _ hsrc, loadHolds_mul_gen_pow]
      exact hexp.1 _ (pushKappa_lt hh hm hb)
    have g2 : Good rd vsSL w σ (.load (.n (vsPushQ b)) (.n (vsPushM b)) (Tables.blockKappaAdj b)) :=
      hG (vsLd (vsPushQ b) (vsPushM b) (Tables.blockKappaAdj b))
        (vsPushStep_mem hb (by rw [vsPushStep_eq]; simp))
    have r2 := good_read g2 (vsPush_notS b hb) hq
    exact ⟨r2.1, gm, r2.2⟩
  intro n
  induction n with
  | zero =>
    intro _ nx hn
    obtain ⟨e2, hm1, h2⟩ := rd2 0 (by norm_num)
    refine ⟨by rw [show vsPV 0 = vsPushQ 0 from rfl, e2]; simp, ?_⟩
    rw [show List.range (0 + 1) = [0] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsPushStep_eq, ↓reduceIte,
      List.append_nil, Stmt.HoldsList, Stmt.Holds, vsLd, vsMul]
    exact ⟨hm1, h2, hn⟩
  | succ n ih =>
    intro hn nx hnx
    have hb : n + 1 < 54 := hn
    obtain ⟨e2, hm1, h2⟩ := rd2 (n + 1) hb
    have gp : Good rd vsSL w σ (.mul (.n (vsPV (n + 1))) (.n (vsPV n)) (.n (vsPushQ (n + 1)))) :=
      hG (vsMul (vsPV (n + 1)) (vsPV n) (vsPushQ (n + 1)))
        (vsPushStep_mem hb (by rw [vsPushStep_eq]; simp))
    simp only [Good] at gp
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp [vsPV, vsPushQ]))] at gp
    have hstep : Stmt.HoldsList C rd σ (vsPushStep (n + 1)) nx kret := by
      simp only [vsPushStep_eq, Nat.add_one_ne_zero, ↓reduceIte, List.cons_append, List.nil_append,
        Stmt.HoldsList, Stmt.Holds, vsLd, vsMul, Nat.add_sub_cancel]
      exact ⟨hm1, h2, gp, hnx⟩
    obtain ⟨ep, hp⟩ := ih (by omega) hstep
    refine ⟨?_, ?_⟩
    · rw [gp, ep, e2, ← pow_add, List.range_succ (n := n + 1), List.map_append, List.sum_append]
      simp
    · rw [List.range_succ (n := n + 1), List.flatMap_append, holdsList_append]
      exact hp

/-- **The push total and the bus depth, honestly.** -/
theorem vsPushT_complete (hl : args.length = 6) {logMem : ℕ} {hs : List ℕ}
    (hh : ∀ x ∈ hs, x < 33) (hm : logMem ≤ 32)
    (hkbv : ∀ s < 8, vsσ rd w args (.n (140 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    (hexp : B1.ExpTables rd (vsσ rd w args (.n 4)))
    {C : CallRel} (hC : ∀ r, vsσ rd w args (.n 309) = r →
      C "log2_ceil_in_the_exponent__L0_L34"
        [gen ^ ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum,
          vsσ rd w args (.n 4)] [r])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 308) = gen ^ ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsPushT next kret := by
  have hrest : Stmt.HoldsList C rd (vsσ rd w args)
      [vsCall "log2_ceil_in_the_exponent__L0_L34" [308, 4] [309],
        .atom (.hint (.allocDyn (.n 310) (.n 309)))] next kret := by
    obtain ⟨e308, -⟩ := vsPush_loop (C := C) (kret := kret) hl hh hm hkbv hexp 53 (by norm_num)
      (nx := True) trivial
    simp only [Stmt.HoldsList, Stmt.Holds, vsCall, List.map_cons, List.map_nil]
    rw [show vsPV 53 = 308 from rfl] at e308
    exact ⟨by rw [e308]; exact hC _ rfl, trivial, hn⟩
  obtain ⟨e308, h⟩ := vsPush_loop (C := C) (kret := kret) hl hh hm hkbv hexp 53 (by norm_num) hrest
  refine ⟨e308, ?_⟩
  rw [vsPushT, holdsList_append]
  exact h

end
end LeanVM.Guest.B1.VerifySub
