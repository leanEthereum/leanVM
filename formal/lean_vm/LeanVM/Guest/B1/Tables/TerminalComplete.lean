/-
  LeanVM.Guest.B1.Tables.TerminalComplete

  `check_opening_terminal` complete, its memory and its first segments: the prefix chains, the
  public input's chain by `__loop83`, the column selectors.
-/

module

public import LeanVM.Guest.B1.Tables.Terminal
public import LeanVM.Guest.B1.Tables.FlockCAll
public import LeanVM.Protocol.EndToEnd.Complete.BusStack

/-!
# `check_opening_terminal`'s memory and first segments, complete

`TermMem`: what the honest memory holds at the terminal's `HeapBuf`s: the three prefix chains
and the ring switch's rows as their callees' meanings, and the public input's chain. `c_tpre`,
`loop83_complete`, `c_sel`: the prefix, `__loop83`, the column selectors over it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

/-- **`check_opening_terminal`'s honest memory** at its `HeapBuf` pointers
`[chain_z, chain_r, chain_q, chain_pi, rs_chain]`: the three prefix chains and the ring switch's
rows (their callees' meanings, the rows' first entries `1`), and the public input's chain, its
entry `j` the product of `1 + rm + point[0]` and `1 + point[i]` over `1 ≤ i < j`. -/
def TermMem (rd : Reader) : List E → List E → Prop
  | [p17, p19, p21, p25, p1750],
      [zeta, chi, rm, gmu, gzcn, glm, gtau, _, _, _, _, zvals, _, pt, _, _, _] =>
      MeaningEqPrefixChain rd [p17, 1, zeta, pt, gmu] [] ∧
      MeaningEqPrefixChain rd [p19, 1, chi, pt, gzcn] [] ∧
      MeaningEqPrefixChain rd [p21, 1, chi, pt * gen ^ 8, gtau] [] ∧
      LoadHolds rd p25 0 1 ∧
      (∀ n, glm = gen ^ n → n < 33 → ∀ X : ℕ → E, (∀ k < n, LoadHolds rd pt k (X k)) →
        ∀ j, 1 ≤ j → j ≤ n →
          LoadHolds rd p25 j ((1 + rm + X 0) * ∏ i ∈ Finset.Ico 1 j, (1 + X i))) ∧
      MeaningRsEqRun rd [p1750, zvals, pt, gtau * gen ^ 8] [] ∧ (∀ k < 64, LoadHolds rd p1750 k 1)
  | _, _ => False

/-- Every committed column's offset is aligned to its size. -/
theorem stackOffsets_dvd (sizes : List ℕ) {c : ℕ} (hc : c < sizes.length) :
    2 ^ sizes.getD c 0 ∣ (stackOffsets sizes).1.getD c 0 := by
  have hperm := LeanVM.Protocol.EndToEnd.Complete.perm_stackOrder sizes
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem (hperm.symm.subset (List.mem_range.mpr hc))
  have := LeanVM.Protocol.EndToEnd.Complete.dvd_blockOffset sizes k hk
  rw [he] at this
  exact this

section
variable {rd : Reader}

/-- **`__loop83` holds** over the public input's chain. -/
theorem loop83_complete {chain pt : E} {n : ℕ} (hn1 : 1 < n) (hn : n < 33) {X : ℕ → E}
    (hX : ∀ k < n, LoadHolds rd pt k (X k)) {v1 : E}
    (hc : ∀ j, 1 ≤ j → j ≤ n → LoadHolds rd chain j (v1 * ∏ i ∈ Finset.Ico 1 j, (1 + X i))) :
    coreProgram.Rel rd "__loop83" [gen, gen ^ n, chain, pt] [] := by
  have h := (loop_iff (loop83_step rd (gen ^ n) chain pt) 1).mpr
    ⟨n, hn1, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) (by omega) he; omega,
      fun j h1 h2 => ⟨_, X j, lh_back (hc j h1 (by omega)) (by omega), lh_back (hX j (by omega)) (by omega),
        lh_back (n := j + 1) (by
          have := hc (j + 1) (by omega) (by omega)
          rwa [Finset.prod_Ico_succ_top (by omega), ← mul_assoc] at this) rfl⟩⟩
  rwa [pow_one] at h

/-- A valuation's values at the arguments. -/
def argFix (l : List E) : List (ℕ × E) := (List.range l.length).map fun k => (k, l.getD k 0)

theorem argFix_get {σ : Val} {l : List E} (h : Fixes σ (argFix l)) {k : ℕ} (hk : k < l.length) :
    σ (.n k) = l.getD k 0 :=
  h (k, l.getD k 0) (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

/-- The public input's chain at `n`. -/
def piVal (rm : E) (X : ℕ → E) (n : ℕ) : E := (1 + rm + X 0) * ∏ i ∈ Finset.Ico 1 n, (1 + X i)

/-- **The prefix chains and the public input's chain** (G:2023-2032). -/
theorem c_tpre {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 p17 p19 p21 p25 p1750 : E}
    (hM : TermMem rd [p17, p19, p21, p25, p1750]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16])
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n < 33) (h5 : a5 = gen ^ n) {X : ℕ → E}
    (hX : ∀ k < n, LoadHolds rd a13 k (X k)) (σ : Val)
    (hσ : Fixes σ (argFix [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16])) :
    Completes (coreProgram.Rel rd) rd 17 36 tPre σ
      (fun σ' => Fixes σ' [(17, p17), (19, p19), (21, p21), (35, piVal a2 X n), (25, p25)]) := by
  obtain ⟨c17, c19, c21, h25, hpi, -, -⟩ := hM
  have hc := hpi n h5 hn X hX
  have g : ∀ k (hk : k < 17), σ (.n k) =
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16].getD k 0 :=
    fun k hk => argFix_get hσ (by simpa using hk)
  refine completes_upds [(17, p17), (18, word 1 0 0), (19, p19), (20, word 1 0 0), (21, p21),
    (22, word 1 0 0), (23, word 256 0 0), (24, a13 * word 256 0 0), (25, p25), (26, word 1 0 0),
    (27, word 1 0 0), (28, word 1 0 0 + a2), (29, X 0), (30, word 1 0 0 + a2 + X 0),
    (31, word 2 0 0), (32, word 2 0 0 + a5), (33, word 2 0 0), (34, p25 * a5),
    (35, piVal a2 X n)] (by simp) (fun next kret hn' => ?_) ?_
  · simp only [tPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    vs_ev
    rw [g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega), g 4 (by omega),
      g 5 (by omega), g 6 (by omega), g 13 (by omega)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, true_and, word_one, word_gen, word_g8]
    refine ⟨(eq_prefix_chain_iff _ _ _).mpr c17, (eq_prefix_chain_iff _ _ _).mpr c19,
      (eq_prefix_chain_iff _ _ _).mpr c21, h25, hX 0 (by omega), ?_, ?_, fun hne => ?_, ?_, hn'⟩
    · have := hc 1 le_rfl hn1
      simpa [piVal] using this
    · rw [h5]; exact isInK_add (by simpa using gen_pow_isInK 1) (gen_pow_isInK _)
    · rw [h5] at hne ⊢
      have hn2 : 1 < n := by
        rcases Nat.lt_or_ge 1 n with h | h
        · exact h
        · exfalso; apply hne; rw [show n = 1 by omega, pow_one]; exact e_add_self _
      exact loop83_complete hn2 hn hX hc
    · rw [h5]; exact lh_back (hc n hn1 le_rfl) (by omega)
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [upds_n]

/-- The 29 arms of `column_selector` at once, backward. -/
theorem column_selector_any' {jj : ℕ} (hj : jj < csNames.length) {o p : E} {rets : List E}
    (h : MeaningColumnSelector jj rd [o, p] rets) : coreProgram.Rel rd csNames[jj] [o, p] rets := by
  have hj' : jj < 29 := hj
  interval_cases jj
  · exact (column_selector_L0_iff rd o p rets).mpr h
  · exact (column_selector_L1_iff rd o p rets).mpr h
  · exact (column_selector_L2_iff rd o p rets).mpr h
  · exact (column_selector_L3_iff rd o p rets).mpr h
  · exact (column_selector_L4_iff rd o p rets).mpr h
  · exact (column_selector_L5_iff rd o p rets).mpr h
  · exact (column_selector_L6_iff rd o p rets).mpr h
  · exact (column_selector_L7_iff rd o p rets).mpr h
  · exact (column_selector_L8_iff rd o p rets).mpr h
  · exact (column_selector_L9_iff rd o p rets).mpr h
  · exact (column_selector_L10_iff rd o p rets).mpr h
  · exact (column_selector_L11_iff rd o p rets).mpr h
  · exact (column_selector_L12_iff rd o p rets).mpr h
  · exact (column_selector_L13_iff rd o p rets).mpr h
  · exact (column_selector_L14_iff rd o p rets).mpr h
  · exact (column_selector_L15_iff rd o p rets).mpr h
  · exact (column_selector_L16_iff rd o p rets).mpr h
  · exact (column_selector_L17_iff rd o p rets).mpr h
  · exact (column_selector_L18_iff rd o p rets).mpr h
  · exact (column_selector_L19_iff rd o p rets).mpr h
  · exact (column_selector_L20_iff rd o p rets).mpr h
  · exact (column_selector_L21_iff rd o p rets).mpr h
  · exact (column_selector_L22_iff rd o p rets).mpr h
  · exact (column_selector_L23_iff rd o p rets).mpr h
  · exact (column_selector_L24_iff rd o p rets).mpr h
  · exact (column_selector_L25_iff rd o p rets).mpr h
  · exact (column_selector_L26_iff rd o p rets).mpr h
  · exact (column_selector_L27_iff rd o p rets).mpr h
  · exact (column_selector_L28_iff rd o p rets).mpr h

/-- **Committed column `c`'s selector** (G:2034-2037), its offset `g^O` and log `g^K` read, the
selector at the point's first 28 words `zs`. -/
theorem c_sel {c K O : ℕ} (hK : K ≤ 28) (hO : O < 2 ^ 28) (hdvd : 2 ^ K ∣ O) {a9 a10 a13 : E}
    (lo : LoadHolds rd a9 c (gen ^ O)) (lk : LoadHolds rd a10 c (gen ^ K)) {zs : List E}
    (hzl : zs.length = 28) (hz : ∀ k (hk : k < zs.length), LoadHolds rd a13 k zs[k]) (σ : Val)
    (h9 : σ (.n 9) = a9) (h10 : σ (.n 10) = a10) (h13 : σ (.n 13) = a13) (hc : 13 < 36 + 3 * c) :
    Completes (coreProgram.Rel rd) rd (36 + 3 * c) (36 + 3 * c + 3) (selBlk c) σ (fun _ => True) := by
  have hn : ∀ j < 36 + 3 * c, upds σ [(36 + 3 * c, gen ^ O), (37 + 3 * c, gen ^ K),
      (38 + 3 * c, ({ vars := K, index := O } : Placement).eqAbove zs)] (.n j) = σ (.n j) :=
    fun j hj => upds_of_not_mem σ _ (by simp; omega)
  refine completes_upds [(36 + 3 * c, gen ^ O), (37 + 3 * c, gen ^ K),
    (38 + 3 * c, ({ vars := K, index := O } : Placement).eqAbove zs)] (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> dsimp only <;> omega) (fun next kret hn' => ?_) trivial
  simp only [selBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  rw [hn 9 (by omega), hn 10 (by omega), hn 13 (by omega), h9, h10, h13, selV]
  fl_ev
  refine ⟨lo, lk, ⟨K, by simp [csNames]; omega, by rw [gen_pow_eq_ofK], column_selector_any' _
    ⟨O, zs, hO, hdvd, rfl, hzl, fun k hk _ => hz k hk, rfl⟩⟩, hn'⟩

end

end
end LeanVM.Guest.B1

