/-
  LeanVM.Guest.B1.VerifySub.C.Tail

  `verify_sub`'s tail (G:3487-3513), honestly: the placement, the stack's log and the candidate,
  the dispatch, the terminal, the deferred claim's cells.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Lam
public import LeanVM.Guest.B1.VerifySub.Known

/-!
# The tail, honestly

`vsTailPre_complete` (`vsTailPre`: the tail but its `ret`): with `certify_placement`'s and
`log2_ceil_in_the_exponent`'s calls in `C` returning the stack's log `g^m` (`22 ≤ m ≤ 28`), the
rate's power `g^(r - 1)` at `122` (`1 ≤ r ≤ 4`), the memory defined below `2^κ`, the candidate's
`open_stacked` call and the terminal's in `C`, and the deferred claim's cells in memory at `out`
(`5`: the bus point's `19` words, the four bus challenges, the bytecode value), the tail holds and
the candidate is `g^(candidate m r)`.
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
    vsCall "log2_ceil_in_the_exponent__L15_L34" [1682, 4] [1684],
    vsConst 1685 (word 8198552432976855044 0 0), vsMul 1686 1684 1685, vsConst 1687 (word 64 0 0),
    vsRange 1686 1688 1689 1690 1687, vsMul 1691 122 122, vsMul 1692 1691 122,
    vsMul 1693 1692 1692, vsMul 1694 1693 122, vsMul 1695 1686 1694,
    vsConst 1696 (word 134217728 0 0), vsRange 1695 1697 1698 1699 1696,
    .dispatch (.n 1695) vsOpenNames
      [.n 1100, .n 1101, .n 1102, .n 1103, .n 1104, .n 1681, .n 324, .n 334, .n 656] (vsRun 1700 5),
    vsCall "check_opening_terminal" [4, 310, 635, 644, 309, 642, 128, 646, 139, 1111, 1683, 647,
      665, 1701, 1702, 1703, 1704, 1700] []]

theorem vsTailPre_eq : vsTailPre = vsTailHead ++
    (List.range 19).flatMap (fun k ↦ [vsLd (1705 + k) 310 k, vsLd (1705 + k) 5 k]) ++
    (List.range 4).flatMap (fun k ↦ [vsLd (1724 + k) 346 k, vsLd (1724 + k) 5 (19 + k)]) ++
    [vsLd 643 5 23] := stmtsEqb_sound (by decide +kernel)

theorem vsTailPre_noNe : vsTailPre.all noNeB = true := by decide +kernel

theorem vsTail_notS : (∀ k < 19, Atom.load (.n (1705 + k)) (.n 310) k ∉ vsSL) ∧
    ∀ k < 4, Atom.load (.n (1724 + k)) (.n 346) k ∉ vsSL := by decide +kernel

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
    {m r : ℕ} (hm22 : 22 ≤ m) (hm28 : m ≤ 28) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (e1890 : vsσ rd w args (.n 1684) = gen ^ m) (e124 : vsσ rd w args (.n 122) = gen ^ (r - 1))
    {zs al : ℕ → E}
    (hzeta : ∀ k < 19, LoadHolds rd (vsσ rd w args (.n 310)) k (zs k))
    (halpha : ∀ k < 4, LoadHolds rd (vsσ rd w args (.n 346)) k (al k))
    (hout : ∀ k < 19, LoadHolds rd (vsσ rd w args (.n 5)) k (zs k))
    (hout' : ∀ k < 4, LoadHolds rd (vsσ rd w args (.n 5)) (19 + k) (al k))
    (hout23 : LoadHolds rd (vsσ rd w args (.n 5)) 23 (vsσ rd w args (.n 643)))
    {C : CallRel}
    (hCcp : C "certify_placement" [vsσ rd w args (.n 139), vsσ rd w args (.n 4)]
      [vsσ rd w args (.n 1682), vsσ rd w args (.n 1683)])
    (hClg : C "log2_ceil_in_the_exponent__L15_L34"
      [vsσ rd w args (.n 1682), vsσ rd w args (.n 4)] [vsσ rd w args (.n 1684)])
    (hD : C (vsOpenNames.getD (B1.Whir.candidate m r) "")
      ([1100, 1101, 1102, 1103, 1104, 1681, 324, 334, 656].map (vsσ rd w args ∘ V.n))
      ((vsRun 1700 5).map (vsσ rd w args)))
    (hCt : C "check_opening_terminal"
      ([4, 310, 635, 644, 309, 642, 128, 646, 139, 1111, 1683, 647, 665, 1701, 1702, 1703, 1704,
        1700].map (vsσ rd w args ∘ V.n)) [])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 1695) = gen ^ B1.Whir.candidate m r ∧
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
  have c1891 : σ (.n 1685) = word 8198552432976855044 0 0 :=
    g _ (show vsConst 1685 (word 8198552432976855044 0 0) ∈ vsTailHead by simp [vsTailHead])
  have c1893 : σ (.n 1687) = gen ^ 6 := by
    rw [show σ (.n 1687) = word 64 0 0 from g _ (show vsConst 1687 (word 64 0 0) ∈ vsTailHead by
      simp [vsTailHead]), show (64 : ℕ) = 2 ^ 6 from rfl, word_two_pow (by norm_num)]
  have c1902 : σ (.n 1696) = gen ^ 27 := by
    rw [show σ (.n 1696) = word 134217728 0 0 from g _ (show vsConst 1696 (word 134217728 0 0) ∈
      vsTailHead by simp [vsTailHead]), show (134217728 : ℕ) = 2 ^ 27 from rfl,
      word_two_pow (by norm_num)]
  have m1892 := gm 1686 1684 1685 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have v1892 : σ (.n 1686) = gen ^ (m - 22) := by
    rw [m1892, e1890, c1891]
    have : gen ^ m = gen ^ (m - 22) * gen ^ 22 := by rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc, mul_comm (gen ^ 22), kn_word_ginv22_mul, mul_one]
  have m1897 := gm 1691 122 122 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have m1898 := gm 1692 1691 122 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have m1899 := gm 1693 1692 1692 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have m1900 := gm 1694 1693 122 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have m1901 := gm 1695 1686 1694 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have v1900 : σ (.n 1694) = gen ^ (7 * (r - 1)) := by
    rw [m1900, m1899, m1898, m1897, e124, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1; ring
  have v1901 : σ (.n 1695) = gen ^ B1.Whir.candidate m r := by
    rw [m1901, v1892, v1900, ← pow_add]; rfl
  have hcand : B1.Whir.candidate m r ≤ 27 := by unfold B1.Whir.candidate; omega
  have r1 := rc_holds hlow (by decide) (a := m - 22) (b := 6 - (m - 22)) (by omega) (by omega)
    v1892 (by
      rw [good_rc_y (by decide) (g _ (show vsRange 1686 1688 1689 1690 1687 ∈ vsTailHead by
        simp [vsTailHead])), c1893, v1892, gen_pow_div (by omega)])
    (g _ (show vsRange 1686 1688 1689 1690 1687 ∈ vsTailHead by simp [vsTailHead]))
  have r2 := rc_holds hlow (by decide) (a := B1.Whir.candidate m r)
    (b := 27 - B1.Whir.candidate m r) (by omega) (by omega) v1901 (by
      rw [good_rc_y (by decide) (g _ (show vsRange 1695 1697 1698 1699 1696 ∈ vsTailHead by
        simp [vsTailHead])), c1902, v1901, gen_pow_div hcand])
    (g _ (show vsRange 1695 1697 1698 1699 1696 ∈ vsTailHead by simp [vsTailHead]))
  have hlen : vsOpenNames.length = 28 := by simp [vsOpenNames]
  have hdisp : ∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1695) = ofK (addressOfIndex j) ∧
      C vsOpenNames[j] ([V.n 1100, V.n 1101, V.n 1102, V.n 1103, V.n 1104, V.n 1681, V.n 324,
        V.n 334, V.n 656].map σ) ((vsRun 1700 5).map σ) := by
    refine ⟨B1.Whir.candidate m r, by omega, by rw [v1901, gen_pow_eq_ofK], ?_⟩
    rw [← List.getD_eq_getElem _ ""]
    simpa using hD
  refine ⟨v1901, ?_⟩
  have k1893 : σ (.n 1687) = word 64 0 0 :=
    g _ (show vsConst 1687 (word 64 0 0) ∈ vsTailHead by simp [vsTailHead])
  have k1902 : σ (.n 1696) = word 134217728 0 0 :=
    g _ (show vsConst 1696 (word 134217728 0 0) ∈ vsTailHead by simp [vsTailHead])
  have memZ : ∀ k < 19, ∀ s ∈ [vsLd (1705 + k) 310 k, vsLd (1705 + k) 5 k], s ∈ vsTailPre :=
    fun k hk s hs ↦ by
      rw [vsTailPre_eq]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hs⟩)))
  have memA : ∀ k < 4, ∀ s ∈ [vsLd (1724 + k) 346 k, vsLd (1724 + k) 5 (19 + k)], s ∈ vsTailPre :=
    fun k hk s hs ↦ by
      rw [vsTailPre_eq]
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hs⟩))
  have L1 : ∀ l : List ℕ, (∀ k ∈ l, k < 19) → ∀ {nx : Prop}, nx →
      Stmt.HoldsList C rd σ (l.flatMap fun k ↦ [vsLd (1705 + k) 310 k, vsLd (1705 + k) 5 k])
        nx kret := by
    intro l
    induction l with
    | nil => intro _ nx h; exact h
    | cons k l ih =>
      intro hl' nx h
      have hk := hl' k List.mem_cons_self
      have r := good_read (w := w) (hG (vsLd (1705 + k) 310 k) (memZ k hk _ (by simp)))
        (vsTail_notS.1 k hk) (hzeta k hk)
      rw [List.flatMap_cons, holdsList_append]
      simp only [Stmt.HoldsList, Stmt.Holds, vsLd]
      refine ⟨r.2, by show LoadHolds rd _ _ _; rw [r.1]; exact hout k hk,
        ih (fun x hx ↦ hl' x (List.mem_cons_of_mem _ hx)) h⟩
  have L2 : ∀ l : List ℕ, (∀ k ∈ l, k < 4) → ∀ {nx : Prop}, nx →
      Stmt.HoldsList C rd σ (l.flatMap fun k ↦ [vsLd (1724 + k) 346 k, vsLd (1724 + k) 5 (19 + k)])
        nx kret := by
    intro l
    induction l with
    | nil => intro _ nx h; exact h
    | cons k l ih =>
      intro hl' nx h
      have hk := hl' k List.mem_cons_self
      have r := good_read (w := w) (hG (vsLd (1724 + k) 346 k) (memA k hk _ (by simp)))
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
  exact ⟨hCcp, hClg, c1891, m1892, k1893, r1, m1897, m1898, m1899, m1900, m1901, k1902, r2,
    hdisp, hCt, L1 _ (fun k hk ↦ List.mem_range.1 hk) (L2 _ (fun k hk ↦ List.mem_range.1 hk)
      ⟨hout23, hn⟩)⟩

end
end LeanVM.Guest.B1.VerifySub
