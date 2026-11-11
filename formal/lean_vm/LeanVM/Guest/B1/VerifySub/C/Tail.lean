/-
  LeanVM.Guest.B1.VerifySub.C.Tail

  `verify_sub`'s tail (G:3534-3557), honestly: the placement, the stack's log and its size
  selector, the dispatch, the terminal, the deferred claim's cells.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Lam
public import LeanVM.Guest.B1.VerifySub.Known

/-!
# The tail, honestly

`vsTailPre_complete` (`vsTailPre`: the tail but its `ret`): with `certify_placement`'s and
`log2_ceil_in_the_exponent`'s calls in `C` returning the stack's log `g^m` (`20 ≤ m ≤ 32`), the
memory defined below `2^κ`, the size's `open_stacked` call (the rate's selector at `122` its first
argument) and the terminal's in `C`, and the deferred claim's cells in memory at `out` (`5`: the
bus point's `19` words, the four bus challenges, the bytecode value), the tail holds and the size
selector is `g^(m - 20)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

/-- The tail before its `ret`. -/
def vsTailPre : List Stmt := vsTailT.dropLast

theorem vsCPre_tail : vsCPre = vsHeadT ++ vsReadsT ++ vsSizesT ++ vsPushT ++
    vsRootsT ++ vsAlphasT ++ vsFpwT ++ vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++ vsTailPre :=
  stmtsEqb_sound (by decide +kernel)

/-- The tail's statements before its `ret`, explicitly. -/
def vsTailHead : List Stmt :=
  [vsCall "certify_placement" [139, 4] [1682, 1683],
    vsCall "log2_ceil_in_the_exponent__L16_L34" [1682, 4] [1684],
    vsConst 1685 (word 14347465658197868555 0 0), vsMul 1686 1684 1685, vsConst 1687 (word 1024 0 0),
    vsRange 1686 1688 1689 1690 1687,
    .dispatch (.n 1686) vsOpenNames
      [.n 122, .n 1100, .n 1101, .n 1102, .n 1103, .n 1104, .n 1681, .n 324, .n 334, .n 656]
      (vsRun 1691 5),
    vsCall "check_opening_terminal" [4, 310, 635, 644, 309, 642, 128, 646, 139, 1111, 1683, 647,
      665, 1692, 1693, 1694, 1695, 1691] []]

theorem vsTailPre_eq : vsTailPre = vsTailHead ++
    (List.range 19).flatMap (fun k ↦ [vsLd (1696 + k) 310 k, vsLd (1696 + k) 5 k]) ++
    (List.range 4).flatMap (fun k ↦ [vsLd (1715 + k) 346 k, vsLd (1715 + k) 5 (19 + k)]) ++
    [vsLd 643 5 23] := stmtsEqb_sound (by decide +kernel)

theorem vsTailPre_noNe : vsTailPre.all noNeB = true := by decide +kernel

theorem vsTail_notS : (∀ k < 19, Atom.load (.n (1696 + k)) (.n 310) k ∉ vsSL) ∧
    ∀ k < 4, Atom.load (.n (1715 + k)) (.n 346) k ∉ vsSL := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsTailPre_good (hl : args.length = 6) :
    ∀ s ∈ vsTailPre, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 1586) (blk := vsTailPre)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsTailPre_noNe s hs)] at h

set_option maxRecDepth 100000 in
/-- **The tail, honestly.** -/
theorem vsTailPre_complete (hl : args.length = 6) {κ : ℕ} (hκ6 : 6 ≤ κ) (hlow : LowDef κ rd)
    {m : ℕ} (hm19 : B1.Whir.minOpenLog ≤ m) (hm30 : m ≤ 30)
    (e1684 : vsσ rd w args (.n 1684) = gen ^ m)
    {zs al : ℕ → E}
    (hzeta : ∀ k < 19, LoadHolds rd (vsσ rd w args (.n 310)) k (zs k))
    (halpha : ∀ k < 4, LoadHolds rd (vsσ rd w args (.n 346)) k (al k))
    (hout : ∀ k < 19, LoadHolds rd (vsσ rd w args (.n 5)) k (zs k))
    (hout' : ∀ k < 4, LoadHolds rd (vsσ rd w args (.n 5)) (19 + k) (al k))
    (hout23 : LoadHolds rd (vsσ rd w args (.n 5)) 23 (vsσ rd w args (.n 643)))
    {C : CallRel}
    (hCcp : C "certify_placement" [vsσ rd w args (.n 139), vsσ rd w args (.n 4)]
      [vsσ rd w args (.n 1682), vsσ rd w args (.n 1683)])
    (hClg : C "log2_ceil_in_the_exponent__L16_L34"
      [vsσ rd w args (.n 1682), vsσ rd w args (.n 4)] [vsσ rd w args (.n 1684)])
    (hD : C (vsOpenNames.getD (m - B1.Whir.minOpenLog) "")
      ([122, 1100, 1101, 1102, 1103, 1104, 1681, 324, 334, 656].map (vsσ rd w args ∘ V.n))
      ((vsRun 1691 5).map (vsσ rd w args)))
    (hCt : C "check_opening_terminal"
      ([4, 310, 635, 644, 309, 642, 128, 646, 139, 1111, 1683, 647, 665, 1692, 1693, 1694, 1695,
        1691].map (vsσ rd w args ∘ V.n)) [])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 1686) = gen ^ (m - B1.Whir.minOpenLog) ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsTailPre next kret := by
  have hG := vsTailPre_good (rd := rd) (w := w) hl
  generalize hσ : vsσ rd w args = σ at *
  have hκ : 64 ≤ 2 ^ κ :=
    calc 64 = 2 ^ 6 := rfl
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ6
  have mem : ∀ s ∈ vsTailHead, s ∈ vsTailPre := fun s hs ↦ by
    rw [vsTailPre_eq]; simp only [List.mem_append]; tauto
  have g : ∀ a, Stmt.atom a ∈ vsTailHead → Good rd vsSL w σ a := fun a h ↦ hG _ (mem _ h)
  have gm : ∀ (d x y : ℕ), vsMul d x y ∈ vsTailHead → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y h hx hy ↦ by
      have := g _ h
      simp only [Good] at this
      rwa [ite_eq_left_of_eq_true _ _ (eq_true ⟨show x < d from hx, show y < d from hy⟩)] at this
  have c1685 : σ (.n 1685) = word 14347465658197868555 0 0 :=
    g _ (show vsConst 1685 (word 14347465658197868555 0 0) ∈ vsTailHead by simp [vsTailHead])
  have c1687 : σ (.n 1687) = gen ^ 10 := by
    rw [show σ (.n 1687) = word 1024 0 0 from g _ (show vsConst 1687 (word 1024 0 0) ∈ vsTailHead by
      simp [vsTailHead]), show (1024 : ℕ) = 2 ^ 10 from rfl, word_two_pow (by norm_num)]
  have m1686 := gm 1686 1684 1685 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have v1686 : σ (.n 1686) = gen ^ (m - B1.Whir.minOpenLog) := by
    rw [m1686, e1684, c1685]
    have : gen ^ m = gen ^ (m - 20) * gen ^ 20 := by
      rw [← pow_add]; congr 1; unfold B1.Whir.minOpenLog at hm19; omega
    rw [this, mul_assoc, mul_comm (gen ^ 20), kn_word_ginv20_mul, mul_one]
  have r1 := rc_holds hlow (by decide) (a := m - B1.Whir.minOpenLog)
    (b := 10 - (m - B1.Whir.minOpenLog)) (by unfold B1.Whir.minOpenLog; omega)
    (by unfold B1.Whir.minOpenLog; omega)
    v1686 (by
      rw [good_rc_y (by decide) (g _ (show vsRange 1686 1688 1689 1690 1687 ∈ vsTailHead by
        simp [vsTailHead])), c1687, v1686, gen_pow_div (by unfold B1.Whir.minOpenLog; omega)])
    (g _ (show vsRange 1686 1688 1689 1690 1687 ∈ vsTailHead by simp [vsTailHead]))
  have hlen : vsOpenNames.length = 11 := by simp [vsOpenNames]
  have hdisp : ∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1686) = ofK (addressOfIndex j) ∧
      C vsOpenNames[j] ([V.n 122, V.n 1100, V.n 1101, V.n 1102, V.n 1103, V.n 1104, V.n 1681,
        V.n 324, V.n 334, V.n 656].map σ) ((vsRun 1691 5).map σ) := by
    refine ⟨m - B1.Whir.minOpenLog, by unfold B1.Whir.minOpenLog; omega,
      by rw [v1686, gen_pow_eq_ofK], ?_⟩
    rw [← List.getD_eq_getElem _ ""]
    simpa using hD
  refine ⟨v1686, ?_⟩
  have k1687 : σ (.n 1687) = word 1024 0 0 :=
    g _ (show vsConst 1687 (word 1024 0 0) ∈ vsTailHead by simp [vsTailHead])
  have memZ : ∀ k < 19, ∀ s ∈ [vsLd (1696 + k) 310 k, vsLd (1696 + k) 5 k], s ∈ vsTailPre :=
    fun k hk s hs ↦ by
      rw [vsTailPre_eq]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hs⟩)))
  have memA : ∀ k < 4, ∀ s ∈ [vsLd (1715 + k) 346 k, vsLd (1715 + k) 5 (19 + k)], s ∈ vsTailPre :=
    fun k hk s hs ↦ by
      rw [vsTailPre_eq]
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hs⟩))
  have L1 : ∀ l : List ℕ, (∀ k ∈ l, k < 19) → ∀ {nx : Prop}, nx →
      Stmt.HoldsList C rd σ (l.flatMap fun k ↦ [vsLd (1696 + k) 310 k, vsLd (1696 + k) 5 k])
        nx kret := by
    intro l
    induction l with
    | nil => intro _ nx h; exact h
    | cons k l ih =>
      intro hl' nx h
      have hk := hl' k List.mem_cons_self
      have r := good_read (w := w) (hG (vsLd (1696 + k) 310 k) (memZ k hk _ (by simp)))
        (vsTail_notS.1 k hk) (hzeta k hk)
      rw [List.flatMap_cons, holdsList_append]
      simp only [Stmt.HoldsList, Stmt.Holds, vsLd]
      refine ⟨r.2, by show LoadHolds rd _ _ _; rw [r.1]; exact hout k hk,
        ih (fun x hx ↦ hl' x (List.mem_cons_of_mem _ hx)) h⟩
  have L2 : ∀ l : List ℕ, (∀ k ∈ l, k < 4) → ∀ {nx : Prop}, nx →
      Stmt.HoldsList C rd σ (l.flatMap fun k ↦ [vsLd (1715 + k) 346 k, vsLd (1715 + k) 5 (19 + k)])
        nx kret := by
    intro l
    induction l with
    | nil => intro _ nx h; exact h
    | cons k l ih =>
      intro hl' nx h
      have hk := hl' k List.mem_cons_self
      have r := good_read (w := w) (hG (vsLd (1715 + k) 346 k) (memA k hk _ (by simp)))
        (vsTail_notS.2 k hk) (halpha k hk)
      rw [List.flatMap_cons, holdsList_append]
      simp only [Stmt.HoldsList, Stmt.Holds, vsLd]
      refine ⟨r.2, by show LoadHolds rd _ _ _; rw [r.1]; exact hout' k hk,
        ih (fun x hx ↦ hl' x (List.mem_cons_of_mem _ hx)) h⟩
  rw [vsTailPre_eq]
  simp only [holdsList_append]
  simp only [vsTailHead, Stmt.HoldsList, Stmt.Holds, vsCall, vsConst, vsMul, vsRange,
    List.map_cons, List.map_nil]
  simp only [List.map_cons, List.map_nil, Function.comp_apply] at hCt
  exact ⟨hCcp, hClg, c1685, m1686, k1687, r1, hdisp, hCt, L1 _ (fun k hk ↦ List.mem_range.1 hk) (L2 _ (fun k hk ↦ List.mem_range.1 hk)
      ⟨hout23, hn⟩)⟩

end
end LeanVM.Guest.B1.VerifySub
