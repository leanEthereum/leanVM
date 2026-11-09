/-
  LeanVM.Guest.B1.VerifySub.C.Maps

  `verify_sub`'s ring map challenges (G:3444-3450), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Roots

/-!
# The ring map's challenges, honestly

`vsMapsT_complete`: the challenges' and `c_table`'s buffers allocated, the first challenge
(`verify_keccak`'s, `658`) and five squeezed ones stored in the challenges' buffer (holding them).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
/-- **The ring map's challenges, honestly.** -/
theorem vsMapsT_complete (hl : args.length = 6)
    (hz : ∀ i ∈ [8, 9, 10, 11], vsσ rd w args (.n i) = 0)
    (hcap0 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (659 + i))))
    (hM : ∀ k (hk : k < 6), LoadHolds rd (vsσ rd w args (.n 664)) k
      (vsσ rd w args (.n ([658, 685, 705, 725, 745, 765][k]'(by simp; omega)))))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd (vsσ rd w args) vsMapsT next kret := by
  have hm : ∀ s ∈ vsMapsT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 564) (blk := vsMapsT) (by decide +kernel) hs
  have c0 : IsCanonical128 (0 : E) := canonical_zero
  have hz' : ∀ i ∈ [8, 9, 10, 11], IsCanonical128 (vsσ rd w args (.n i)) :=
    fun i hi ↦ by rw [hz i hi]; exact c0
  have hsq : ∀ capb, (∀ i < 5, IsCanonical128 (vsσ rd w args (.n (capb + i)))) →
      AllCanonical (([V.n 8, V.n 8, V.n 8, V.n 8, V.n 8, V.n 9, V.n 10, V.n 11] ++
        vsRun capb 5).map (vsσ rd w args)) := by
    intro capb hc x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    simp only [vsRun, List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
      List.mem_range] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩
    · exact hz' 8 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 9 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 11 (by simp)
    · exact hc i hi
  have mem : ∀ capb o, vsSqzT capb o ⊆ vsMapsT → ∀ s ∈ vsSqzT capb o, s ∈ vsCPre :=
    fun capb o hsub s hs ↦ hm s (hsub hs)
  have sub : ∀ capb o, (capb, o) ∈ [(659, 666), (674, 686), (694, 706), (714, 726), (734, 746)] →
      vsSqzT capb o ⊆ vsMapsT := by
    intro capb o h s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rw [vsMapsT]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [List.mem_append] <;> tauto
  have K := fun capb o (h : (capb, o) ∈ [(659, 666), (674, 686), (694, 706), (714, 726),
      (734, 746)]) hc ↦ kc_complete (C := C) (next := True) (kret := kret) hl (o := o)
    (ins := [V.n 8, V.n 8, V.n 8, V.n 8, V.n 8, V.n 9, V.n 10, V.n 11] ++ vsRun capb 5)
    (mem capb o (sub capb o h)) (hsq capb hc) trivial
  have nx : ∀ o, (∀ k < 13, IsCanonical128 (vsσ rd w args (.n (o + k)))) →
      ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (o + 8 + i))) :=
    fun o h i hi ↦ by have := h (8 + i) (by omega); rwa [← Nat.add_assoc] at this
  have o1 := (K 659 666 (by simp) hcap0).1
  have o2 := (K 674 686 (by simp) (nx 666 o1)).1
  have o3 := (K 694 706 (by simp) (nx 686 o2)).1
  have o4 := (K 714 726 (by simp) (nx 706 o3)).1
  have hlist : vsMapsT = [vsAlloc 664 6, vsAlloc 665 64, vsLd 658 664 0] ++
      (vsSqzT 659 666 ++ ([vsLd 685 664 1] ++ (vsSqzT 674 686 ++ ([vsLd 705 664 2] ++
        (vsSqzT 694 706 ++ ([vsLd 725 664 3] ++ (vsSqzT 714 726 ++ ([vsLd 745 664 4] ++
          (vsSqzT 734 746 ++ [vsLd 765 664 5]))))))))) := by
    rw [vsMapsT]; simp only [List.append_assoc]
  rw [hlist]
  simp only [holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc, vsLd]
  refine ⟨trivial, trivial, hM 0 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 666) (mem 659 666 (sub _ _ (by simp))) (hsq 659 hcap0) ?_).2
  refine ⟨hM 1 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 686) (mem 674 686 (sub _ _ (by simp))) (hsq 674 (nx 666 o1)) ?_).2
  refine ⟨hM 2 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 706) (mem 694 706 (sub _ _ (by simp))) (hsq 694 (nx 686 o2)) ?_).2
  refine ⟨hM 3 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 726) (mem 714 726 (sub _ _ (by simp))) (hsq 714 (nx 706 o3)) ?_).2
  refine ⟨hM 4 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 746) (mem 734 746 (sub _ _ (by simp))) (hsq 734 (nx 726 o4)) ?_).2
  exact ⟨hM 5 (by norm_num), hn⟩

end
end LeanVM.Guest.B1.VerifySub
