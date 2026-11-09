/-
  LeanVM.Guest.B1.VerifySub.C.Calls

  `verify_sub`'s calls of the bus's GKR, the tables and the Keccak reduction (G:3425-3436),
  honestly: the statements around the calls, the calls given.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Maps
public import LeanVM.Guest.B1.KeccakGkr.VkStep
public import LeanVM.Guest.B1.VerifySub.Gw

/-!
# The three calls, honestly

`vsCallsT_complete`: the GKR cursor (`stream·g^10`), `chi`, `z_vals` and `slices` allocated, the
`KECCAK` table's height read from `dims_g`, the output lanes' values in place (`col_eval_words·g^107`), and
the capacity after `verify_keccak` copied, around the three calls (in `C`, at the honest
valuation's words).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

theorem vsCallsT_noNe : vsCallsT.all noNeB = true := by decide +kernel

theorem vsCalls_notS : Atom.load (.n 646) (.n 127) 6 ∉ vsSL := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
/-- **The three calls' section, honestly.** -/
theorem vsCallsT_complete (hl : args.length = 6) {τg : E}
    (hd6 : LoadHolds rd (vsσ rd w args (.n 127)) 6 τg) {C : CallRel}
    (hCg : C "verify_bus_gkr" ([612, 613, 614, 615, 616, 625, 309, 310].map (vsσ rd w args ∘ V.n))
      ((List.range 9).map (vsσ rd w args ∘ V.n ∘ (626 + ·))))
    (hCt : C "verify_tables" ([626, 627, 628, 629, 630, 631, 0, 1, 310, 309, 127, 26, 4, 427, 623, 6,
      635, 632, 633, 634].map (vsσ rd w args ∘ V.n))
      ((List.range 10).map (vsσ rd w args ∘ V.n ∘ (636 + ·))))
    (hCk : C "verify_keccak" ([636, 637, 638, 639, 640, 641, 646, 635, 650, 647, 648].map
      (vsσ rd w args ∘ V.n)) ((List.range 8).map (vsσ rd w args ∘ V.n ∘ (651 + ·))))
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 625) = vsσ rd w args (.n 25) * gen ^ 10 ∧ vsσ rd w args (.n 646) = τg ∧
      vsσ rd w args (.n 650) = vsσ rd w args (.n 645) * gen ^ 107 ∧
      (∀ i < 5, vsσ rd w args (.n (659 + i)) = vsσ rd w args (.n (651 + i))) ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsCallsT next kret := by
  have hG : ∀ s ∈ vsCallsT, GoodS rd vsSL w (vsσ rd w args) s := fun s hs ↦ by
    have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 548) (blk := vsCallsT)
      (by decide +kernel) hs)
    rwa [fixNe_of_noNe (List.all_eq_true.mp vsCallsT_noNe s hs)] at h
  have m : ∀ s, s ∈ [vsConst 624 (word 1024 0 0), vsMul 625 25 624, vsLd 646 127 6,
      vsConst 649 (word 237494511599616 0 0), vsMul 650 645 649] → s ∈ vsCallsT := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rw [vsCallsT]
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp
  have c837 : vsσ rd w args (.n 624) = word 1024 0 0 := hG (vsConst 624 _) (m _ (by simp))
  have c861 : vsσ rd w args (.n 649) = word 237494511599616 0 0 := hG (vsConst 649 _) (m _ (by simp))
  have g838 : Good rd vsSL w (vsσ rd w args) (.mul (.n 625) (.n 25) (.n 624)) :=
    hG (vsMul 625 25 624) (m _ (by simp))
  have g862 : Good rd vsSL w (vsσ rd w args) (.mul (.n 650) (.n 645) (.n 649)) :=
    hG (vsMul 650 645 649) (m _ (by simp))
  simp only [Good] at g838 g862
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show 25 < 625 by norm_num, show 624 < 625 by norm_num⟩)]
    at g838
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show 645 < 650 by norm_num, show 649 < 650 by norm_num⟩)]
    at g862
  have r858 := good_read (w := w) (hG (vsLd 646 127 6) (m _ (by simp))) vsCalls_notS hd6
  have hcp : ∀ i < 5, vsσ rd w args (.n (659 + i)) = vsσ rd w args (.n (651 + i)) := by
    intro i hi
    have := hG (.atom (.copy (.n (659 + i)) (.n (651 + i)))) (by
      rw [vsCallsT]; exact List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
    exact this
  refine ⟨by rw [g838, c837, show (1024 : ℕ) = 2 ^ 10 from rfl, word_two_pow (by norm_num)],
    r858.1, by rw [g862, c861, word_g107], hcp, ?_⟩
  rw [vsCallsT, show List.range 5 = [0, 1, 2, 3, 4] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, vsCall, vsConst, vsMul, vsAlloc, vsLd, Atom.Holds]
  refine ⟨c837, g838, ?_, trivial, ?_, r858.2, trivial, trivial, c861, g862, ?_,
    hcp 0 (by norm_num), hcp 1 (by norm_num), hcp 2 (by norm_num), hcp 3 (by norm_num),
    hcp 4 (by norm_num), hn⟩
  · simpa using hCg
  · simpa using hCt
  · simpa using hCk

end
end LeanVM.Guest.B1.VerifySub
