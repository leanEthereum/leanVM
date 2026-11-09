/-
  LeanVM.Guest.B1.Tables.Kids.BlockSelTab

  `block_selector_tab__L{n}` loads from any region holding its digits and its run's nibble tables.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.B1.Selectors.BlockSelectorTab

/-!
# `block_selector_tab`, loading from a region

Nibble `k` of `block_selector_tab__L{n}` (width `w ≤ 4`) reads its digit `g^u` at `digits·g^k`,
then the eq weight at `eq_tab·g^u` (offset `32k + 2^w - 2`) and the share at `g_tab·g^u` (offset
`16k`): `btNib_ptr`. `block_selector_tab_relIn`: it loads from `R` when the digits' `⌈n/4⌉` words
(each `g^u`, `u < 2^w`, in the memory), the eq tables' `32⌈n/4⌉` and the `g` tables' `16⌈n/4⌉`
lie in `R`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- Nibble `k`'s eq pointer value. -/
def btPe (k : ℕ) : ℕ := btC k + 5

/-- Nibble `k`'s `g` pointer value. -/
def btPg (k : ℕ) : ℕ := if k = 0 then btC k + 7 else btC k + 8

/-- The pointers `block_selector_tab__L{n}` loads through, with their runs. -/
def btTbl (n : ℕ) : List (ℕ × ℕ) :=
  (0, btN n) :: (List.range (btN n)).flatMap fun k ↦
    [(btPe k, 32 * k + 2 ^ btW n k - 1), (btPg k, 16 * k + 1)]

theorem bt_loads : ∀ n < 34, (btPre n).all (loadsViaB (btTbl n)) = true := by decide +kernel

theorem bt_flat : ∀ n < 34, (btPre n).all Stmt.flat = true := by decide +kernel

theorem bt_noLoadIte : ∀ n < 34, (btPre n).all noLoadIte = true := by decide +kernel

theorem bt_noCall : ∀ n < 34, (btPre n).all noCallSB = true := by decide +kernel

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A nibble's pointers**: the eq weight's and the share's, each the table's times its digit. -/
theorem btNib_ptr {n k : ℕ} (h : Stmt.HoldsList C rd σ (btNibT n k) True kret) :
    LoadHolds rd (σ (.n 0)) k (σ (.n (btC k))) ∧ σ (.n (btPe k)) = σ (.n 1) * σ (.n (btC k)) ∧
      σ (.n (btPg k)) = σ (.n 2) * σ (.n (btC k)) := by
  unfold btNibT at h
  rw [tb_holdsList_append_noRet rfl] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  obtain ⟨hld, -, -, hm, -⟩ := h1
  refine ⟨hld, hm, ?_⟩
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h2
    simp only [btPg, ↓reduceIte]
    exact h2.1
  · simp only [hk0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h2
    simp only [btPg, hk0, ↓reduceIte]
    exact h2.2.1

end

/-- **`block_selector_tab__L{n}` loads from `R`**, its digits `g^u`, `u < 2^w`, in the memory. -/
theorem block_selector_tab_relIn {n : ℕ} (hn : n < 34) {rd : Reader} {R : ℕ → Prop}
    {sb eqt gt : E} {rets : List E} (hsb : PtrIn R sb (btN n))
    (hd : ∀ k < btN n, ∃ u < 2 ^ btW n k, LoadHolds rd sb k (gen ^ u))
    (he : PtrIn R eqt (32 * btN n)) (hg : PtrIn R gt (16 * btN n))
    (h : coreProgram.Rel rd (lName "block_selector_tab" n) [sb, eqt, gt] rets) :
    coreProgram.RelIn rd R (lName "block_selector_tab" n) [sb, eqt, gt] rets := by
  obtain ⟨fn, hf, hp, hb⟩ := btFound hn
  refine relIn_of_flatRel (hnl := bt_noLoadIte n hn) hf hb (bt_flat n hn) h fun σ hpar hh ↦ ?_
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, p2⟩ := hpar
  have hnc : ∀ s ∈ btPre n, noCallSB s = true :=
    fun s hs ↦ List.all_eq_true.mp (bt_noCall n hn) s hs
  refine ⟨fun s hs ↦ ?_, loads_via (bt_loads n hn) fun pb hpb ↦ ?_, fun c hc _ ↦ ?_⟩
  · exact dispOk_of_noCall (hnc s hs)
  · rw [hb, holdsList_append, holdsList_noRet _ (btPre_noRet n)] at hh
    obtain ⟨hpre, -⟩ := hh
    simp only [btTbl, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
      or_false] at hpb
    rcases hpb with rfl | ⟨k, hk, hpb | hpb⟩
    · rw [p0]; exact hsb
    all_goals
      have h0 : n ≠ 0 := by intro h0; subst h0; simp [btN] at hk
      simp only [btPre, h0, ↓reduceIte] at hpre
      rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (btNibT_noRet n)),
        tb_holdsList_flatten_range _ _ (btNibT_noRet n)] at hpre
      obtain ⟨hld, he', hg'⟩ := btNib_ptr (hpre.1 k hk)
      obtain ⟨u, hu, hdu⟩ := hd k hk
      rw [p0] at hld
      have hc : σ (.n (btC k)) = gen ^ u := tb_loadHolds_unique hld hdu
      have hw4 := btW_le n k
      have h16 : 2 ^ btW n k ≤ 16 :=
        calc 2 ^ btW n k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hw4
          _ = 16 := by norm_num
      have : k + 1 ≤ btN n := hk
      subst hpb
    · rw [he', p1, hc]
      exact ptrIn_mul (ptrIn_mono he (by omega))
    · rw [hg', p2, hc]
      exact ptrIn_mul (ptrIn_mono hg (by omega))
  · exfalso
    obtain ⟨t, ht, -⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
    have := hnc s hs
    cases s <;> simp_all [noCallSB, Stmt.callSF, Main.Stmt.callS]

end
end LeanVM.Guest.B1.Tables
