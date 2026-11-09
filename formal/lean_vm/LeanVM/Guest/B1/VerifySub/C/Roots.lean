/-
  LeanVM.Guest.B1.VerifySub.C.Roots

  `verify_sub`'s root and bus challenges (G:3394-3418), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Sqz

/-!
# The root and the bus challenges, honestly

`vsRootsT_complete`: the last four announced words absorbed (a `KECCAK` atom on canonical cells),
the root's two words read and packed, `assert_canonical` on them (calls in `C`), `bus_alpha`
allocated. `vsAlphasT_complete`: four squeezes (the first with the root waiting), each challenge
stored in `bus_alpha` (holding them).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

theorem vsRootsT_noNe : vsRootsT.all noNeB = true := by decide +kernel

theorem vsRoots_notS : Atom.load (.n 324) (.n 25) 8 ∉ vsSL ∧ Atom.load (.n 334) (.n 25) 9 ∉ vsSL := by
  decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsRootsT_good (hl : args.length = 6) :
    ∀ s ∈ vsRootsT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 284) (blk := vsRootsT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsRootsT_noNe s hs)] at h

/-- **The root, honestly.** -/
theorem vsRootsT_complete (hl : args.length = 6)
    (hin : ∀ i ∈ [87, 89, 97, 99, 107, 109, 117, 119, 75, 76, 77, 78, 79],
      IsCanonical128 (vsσ rd w args (.n i)))
    {x0 x1 : E} (hw8 : LoadHolds rd (vsσ rd w args (.n 25)) 8 x0)
    (hw9 : LoadHolds rd (vsσ rd w args (.n 25)) 9 x1)
    {C : CallRel} (hC0 : C "assert_canonical" [x0] [vsσ rd w args (.n 344)])
    (hC1 : C "assert_canonical" [x1] [vsσ rd w args (.n 345)])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 324) = x0 ∧ vsσ rd w args (.n 334) = x1 ∧
      (∀ i ∈ [331, 333, 341, 343], IsCanonical128 (vsσ rd w args (.n i))) ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsRootsT next kret := by
  have hG := vsRootsT_good (rd := rd) (w := w) hl
  have hk : Good rd vsSL w (vsσ rd w args)
      (.keccak [V.n 87, V.n 89, V.n 97, V.n 99, V.n 107, V.n 109, V.n 117, V.n 119, V.n 75, V.n 76,
        V.n 77, V.n 78, V.n 79] (vsRun 311 13) false false) :=
    hG (keccakA [V.n 87, V.n 89, V.n 97, V.n 99, V.n 107, V.n 109, V.n 117, V.n 119, V.n 75,
      V.n 76, V.n 77, V.n 78, V.n 79] (vsRun 311 13)) (by simp [vsRootsT])
  have hcan : AllCanonical ([V.n 87, V.n 89, V.n 97, V.n 99, V.n 107, V.n 109, V.n 117, V.n 119,
      V.n 75, V.n 76, V.n 77, V.n 78, V.n 79].map (vsσ rd w args)) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hin 87 (by simp)
    · exact hin 89 (by simp)
    · exact hin 97 (by simp)
    · exact hin 99 (by simp)
    · exact hin 107 (by simp)
    · exact hin 109 (by simp)
    · exact hin 117 (by simp)
    · exact hin 119 (by simp)
    · exact hin 75 (by simp)
    · exact hin 76 (by simp)
    · exact hin 77 (by simp)
    · exact hin 78 (by simp)
    · exact hin 79 (by simp)
  have hK := keccakA_complete hk hcan
  have g8 : ∀ s ∈ fsNextT (.n 25) 8 324, GoodS rd vsSL w (vsσ rd w args) s :=
    fun s hs ↦ hG s (by simp only [vsRootsT, List.mem_append]; tauto)
  have g9 : ∀ s ∈ fsNextT (.n 25) 9 334, GoodS rd vsSL w (vsσ rd w args) s :=
    fun s hs ↦ hG s (by simp only [vsRootsT, List.mem_append]; tauto)
  obtain ⟨e8, c8a, c8b, -, -⟩ := fsNext_complete (C := C) g8
    vsRoots_notS.1 hw8
  obtain ⟨e9, c9a, c9b, -, -⟩ := fsNext_complete (C := C) g9
    vsRoots_notS.2 hw9
  refine ⟨e8, e9, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact c8a
    · exact c8b
    · exact c9a
    · exact c9b
  · rw [vsRootsT, holdsList_append, holdsList_append, holdsList_append]
    simp only [Stmt.HoldsList, Stmt.Holds, keccakA]
    refine ⟨hK, ?_⟩
    refine (fsNext_complete g8 vsRoots_notS.1 hw8).2.2.2.2 ?_
    refine (fsNext_complete g9 vsRoots_notS.2 hw9).2.2.2.2 ?_
    simp only [Stmt.Holds, vsCall, vsAlloc, List.map_cons, List.map_nil]
    rw [e8, e9]
    exact ⟨hC0, hC1, trivial, hn⟩

set_option maxRecDepth 100000 in
/-- **The bus challenges, honestly.** -/
theorem vsAlphasT_complete (hl : args.length = 6)
    (hz : ∀ i ∈ [8, 9, 10, 11], vsσ rd w args (.n i) = 0)
    (hr : ∀ i ∈ [331, 333, 341, 343], IsCanonical128 (vsσ rd w args (.n i)))
    (hcap0 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (319 + i))))
    (hA : ∀ k (hk : k < 4), LoadHolds rd (vsσ rd w args (.n 346)) k
      (vsσ rd w args (.n ([366, 386, 406, 426][k]'(by simp; omega)))))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd (vsσ rd w args) vsAlphasT next kret := by
  have hmem : ∀ s ∈ vsAlphasT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 306) (blk := vsAlphasT) (by decide +kernel) hs
  have c0 : IsCanonical128 (0 : E) := canonical_zero
  have hz' : ∀ i ∈ [8, 9, 10, 11], IsCanonical128 (vsσ rd w args (.n i)) :=
    fun i hi ↦ by rw [hz i hi]; exact c0
  -- a squeeze's inputs: zeros and a capacity
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
  have hc1 : AllCanonical ([V.n 331, V.n 333, V.n 341, V.n 343, V.n 8, V.n 9, V.n 10, V.n 11,
      V.n 319, V.n 320, V.n 321, V.n 322, V.n 323].map (vsσ rd w args)) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hr 331 (by simp)
    · exact hr 333 (by simp)
    · exact hr 341 (by simp)
    · exact hr 343 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 9 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 11 (by simp)
    · exact hcap0 0 (by norm_num)
    · exact hcap0 1 (by norm_num)
    · exact hcap0 2 (by norm_num)
    · exact hcap0 3 (by norm_num)
    · exact hcap0 4 (by norm_num)
  have st : ∀ (d k : ℕ) (v : E), vsσ rd w args (.n d) = v →
      LoadHolds rd (vsσ rd w args (.n 346)) k v → (Atom.load (.n d) (.n 346) k).Holds rd (vsσ rd w args) :=
    fun d k v e h ↦ by show LoadHolds rd _ _ _; rw [e]; exact h
  have hm : ∀ s, s ∈ vsAlphasT → s ∈ vsCPre := hmem
  -- the four permutations
  obtain ⟨o1, -⟩ := kc_complete (C := C) (next := True) (kret := kret) hl (o := 347)
    (fun s hs ↦ hm s (by rw [vsAlphasT]; simp only [List.mem_append]; tauto)) hc1 trivial
  obtain ⟨o2, -⟩ := kc_complete (C := C) (next := True) (kret := kret) hl (o := 367)
    (fun s hs ↦ hm s (by rw [vsAlphasT, vsSqzT]; simp only [List.mem_append]; tauto))
    (hsq 355 (fun i hi ↦ by have := o1 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)) trivial
  obtain ⟨o3, -⟩ := kc_complete (C := C) (next := True) (kret := kret) hl (o := 387)
    (fun s hs ↦ hm s (by rw [vsAlphasT, vsSqzT, vsSqzT]; simp only [List.mem_append]; tauto))
    (hsq 375 (fun i hi ↦ by have := o2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)) trivial
  obtain ⟨o4, -⟩ := kc_complete (C := C) (next := True) (kret := kret) hl (o := 407)
    (fun s hs ↦ hm s (by rw [vsAlphasT, vsSqzT, vsSqzT, vsSqzT]; simp only [List.mem_append]; tauto))
    (hsq 395 (fun i hi ↦ by have := o3 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)) trivial
  have hlist : vsAlphasT = (keccakA [V.n 331, V.n 333, V.n 341, V.n 343, V.n 8, V.n 9, V.n 10,
      V.n 11, V.n 319, V.n 320, V.n 321, V.n 322, V.n 323] (vsRun 347 13) ::
        challengeT (.n 347) (.n (347 + 1)) (347 + 13)) ++ ([vsLd 366 346 0] ++
      (vsSqzT 355 367 ++ ([vsLd 386 346 1] ++ (vsSqzT 375 387 ++ ([vsLd 406 346 2] ++
        (vsSqzT 395 407 ++ [vsLd 426 346 3])))))) := by
    rw [vsAlphasT]; simp only [List.append_assoc]
  rw [hlist]
  simp only [holdsList_append]
  refine (kc_complete hl (o := 347)
    (fun s hs ↦ hm s (by rw [hlist]; exact List.mem_append_left _ hs)) hc1 ?_).2
  refine ⟨(hA 0 (by norm_num)), ?_⟩
  refine (kc_complete hl (o := 367)
    (fun s hs ↦ hm s (by rw [vsAlphasT, vsSqzT]; simp only [List.mem_append]; tauto))
    (hsq 355 (fun i hi ↦ by have := o1 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)) ?_).2
  refine ⟨(hA 1 (by norm_num)), ?_⟩
  refine (kc_complete hl (o := 387)
    (fun s hs ↦ hm s (by rw [vsAlphasT, vsSqzT, vsSqzT]; simp only [List.mem_append]; tauto))
    (hsq 375 (fun i hi ↦ by have := o2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)) ?_).2
  refine ⟨(hA 2 (by norm_num)), ?_⟩
  refine (kc_complete hl (o := 407)
    (fun s hs ↦ hm s (by rw [vsAlphasT, vsSqzT, vsSqzT, vsSqzT]; simp only [List.mem_append]; tauto))
    (hsq 395 (fun i hi ↦ by have := o3 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)) ?_).2
  exact ⟨(hA 3 (by norm_num)), hn⟩

end
end LeanVM.Guest.B1.VerifySub
