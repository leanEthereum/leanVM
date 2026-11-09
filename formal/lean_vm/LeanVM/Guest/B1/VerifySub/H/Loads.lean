/-
  LeanVM.Guest.B1.VerifySub.H.Loads

  Every load of `verify_sub`'s body on an honest child reads the caller's words or its own buffers.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Calls

/-!
# The loads

`vs_loads_class` (by the kernel): `verify_sub`'s loads are through its own buffers' pointers within
their sizes, through `out` (argument `5`) below `24`, through `col_eval_words` (`645`, `verify_tables`'
return) below `159`, or through a push block's square pointer (`g_squares·kb[src]`, `vsPushM`) at
the block's `adj`. `vs_push_ptr`: on the honest valuation a push block's square pointer is
`g_squares·g^κ_src`. `vs_loads`: so every load's address lies in the caller's words or the own
buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol.Verifier

@[expose] public section

/-- The loads' pointers and offsets. -/
def vsLoadOk (q : V × ℕ) : Bool :=
  (q.1 == .n 25 && q.2 < 10) || (q.1 == .n 26 && q.2 < 6) || (q.1 == .n 127 && q.2 < 7) ||
    (q.1 == .n 139 && q.2 < 8) || (q.1 == .n 427 && q.2 < 16) || (q.1 == .n 664 && q.2 < 6) ||
    (q.1 == .n 665 && q.2 < 64) || (q.1 == .n 6 && q.2 < 167) || (q.1 == .n 310 && q.2 < 19) ||
    (q.1 == .n 346 && q.2 < 4) || (q.1 == .n 5 && q.2 < 24) || (q.1 == .n 645 && q.2 < 159) ||
    ((List.range 54).map fun b ↦ (V.n (vsPushM b), Tables.blockKappaAdj b)).contains q

theorem vs_loads_class : (vsCPre.filterMap Stmt.loadS).all vsLoadOk = true := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **A push block's square pointer.** -/
theorem vs_push_ptr (hl : args.length = 6) {logMem : ℕ} {hs : List ℕ}
    (hkbv : ∀ s < 8, vsσ rd w args (.n (140 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    {b : ℕ} (hb : b < 54) :
    vsσ rd w args (.n (vsPushM b)) =
      vsσ rd w args (.n 4) * gen ^ ([0, logMem] ++ hs).getD (Tables.blockKappaSrc.getD b 0) 0 := by
  have hsrc := blockKappaSrc_lt b (by show b < 153; omega)
  have hM : 147 < vsPushM b := by unfold vsPushM; split <;> omega
  have gm : Good rd vsSL w (vsσ rd w args) (.mul (.n (vsPushM b)) (.n 4)
      (.n (140 + Tables.blockKappaSrc.getD b 0))) :=
    vsPushT_good (rd := rd) (w := w) hl (vsMul (vsPushM b) 4 (140 + Tables.blockKappaSrc.getD b 0))
      (vsPushStep_mem hb (by rw [vsPushStep_eq]; simp))
  simp only [Good] at gm
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by
    generalize Tables.blockKappaSrc.getD b 0 = src at hsrc ⊢
    generalize vsPushM b = m at hM ⊢
    show 4 < m ∧ 140 + src < m; omega))] at gm
  rw [gm, hkbv _ hsrc]

/-- **Every load reads the caller's words or the own buffers.** -/
theorem vs_loads {σ : Val} {bs : List ℕ} {own Lin : Main.Layout} {ownW : List (List E)}
    (hown : ∀ k < 13, (bs.getD k 0, ownW.getD k []) ∈ own)
    (hptr : ∀ k < 13, σ (.n (vsAllocVars.getD k 0)) = ofK (addressOfIndex (bs.getD k 0)))
    (hlen : 167 ≤ (ownW.getD 0 []).length ∧ 10 ≤ (ownW.getD 1 []).length ∧
      6 ≤ (ownW.getD 2 []).length ∧ 7 ≤ (ownW.getD 3 []).length ∧ 8 ≤ (ownW.getD 4 []).length ∧
      19 ≤ (ownW.getD 5 []).length ∧ 4 ≤ (ownW.getD 6 []).length ∧
      16 ≤ (ownW.getD 7 []).length ∧ 6 ≤ (ownW.getD 11 []).length ∧
      64 ≤ (ownW.getD 12 []).length)
    {outE sqE : ℕ} {cells : List E} (houtL : (outE, cells) ∈ Lin) (hcl : 24 ≤ cells.length)
    (h6 : σ (.n 5) = ofK (addressOfIndex outE))
    (hsqL : (sqE, expTableWords) ∈ Lin)
    (hcev : ∃ e, σ (.n 645) = ofK (addressOfIndex e) ∧
      ∀ k < 159, Main.RegionL Lin (e + k) ∨ Main.RegionL own (e + k))
    (hpush : ∀ b < 54, ∃ κ, κ + Tables.blockKappaAdj b < 34 ∧
      σ (.n (vsPushM b)) = ofK (addressOfIndex (sqE + κ))) {X : ℕ → Prop} :
    ∀ q ∈ vsCPre.filterMap Stmt.loadS, ∃ i,
      (σ q.1).limb 0 * Parameters.addressOfIndex q.2 = Parameters.addressOfIndex i ∧
      (Main.RegionL Lin i ∨ Main.RegionL own i ∨ X i) := by
  intro q hq
  have hc := List.all_eq_true.mp vs_loads_class q hq
  obtain ⟨p, off⟩ := q
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l11, l12⟩ := hlen
  have own' : ∀ k < 13, ∀ (hk : off < (ownW.getD k []).length), p = .n (vsAllocVars.getD k 0) →
      ∃ i, (σ p).limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧
        (Main.RegionL Lin i ∨ Main.RegionL own i ∨ X i) :=
    fun k hk hoff hp ↦ ⟨bs.getD k 0 + off, by rw [hp, hptr k hk, Main.addr_ofK],
      Or.inr (Or.inl ⟨_, hown k hk, Nat.le_add_right _ _, Nat.add_lt_add_left hoff _⟩)⟩
  simp only [vsLoadOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem, or_assoc] at hc
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · exact own' 1 (by norm_num) (by omega) h1
  · exact own' 2 (by norm_num) (by omega) h1
  · exact own' 3 (by norm_num) (by omega) h1
  · exact own' 4 (by norm_num) (by omega) h1
  · exact own' 7 (by norm_num) (by omega) h1
  · exact own' 11 (by norm_num) (by omega) h1
  · exact own' 12 (by norm_num) (by omega) h1
  · exact own' 0 (by norm_num) (by omega) h1
  · exact own' 5 (by norm_num) (by omega) h1
  · exact own' 6 (by norm_num) (by omega) h1
  · subst h1
    exact ⟨outE + off, by rw [h6, Main.addr_ofK],
      Or.inl ⟨_, houtL, Nat.le_add_right _ _, Nat.add_lt_add_left (by show off < cells.length; omega) _⟩⟩
  · subst h1
    obtain ⟨e, he, hR⟩ := hcev
    exact ⟨e + off, by rw [he, Main.addr_ofK], (hR off h2).elim Or.inl (fun h ↦ Or.inr (Or.inl h))⟩
  · obtain ⟨b, hb, e⟩ := List.mem_map.mp h1
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨κ, hκ, e⟩ := hpush b (List.mem_range.mp hb)
    exact ⟨sqE + (κ + Tables.blockKappaAdj b), by rw [e, Main.addr_ofK, Nat.add_assoc],
      Or.inl ⟨_, hsqL, Nat.le_add_right _ _, Nat.add_lt_add_left (by
        show κ + Tables.blockKappaAdj b < expTableWords.length
        simp [expTableWords, length_etWordsN]; omega) _⟩⟩

end
end LeanVM.Guest.B1.VerifySub
