/-
  LeanVM.Guest.B1.Sig.XmssSegDigestC

  The prologue and the two message digests of leanXMSS's check inline in `__loop2` complete.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegT
public import LeanVM.Guest.B1.Sig.XmssCore
public import LeanVM.Guest.B1.Sig.MerkleComplete
public import LeanVM.Guest.B1.Sig.CwComplete

/-!
# The prologue and the digests, complete

* `sPrologue_complete`: `P` loaded, the index's shifts and windows hinted, the powers set;
* `sDigest0_complete`: the bottom layer's randomizer hinted, the message's cells loaded, its
  `KECCAK`;
* `sDigest1_complete`: the top layer's index, its randomizer hinted, its `keccak`;
* `sDigest0_nb`, `sDigest1_nb`, `sPrologue_nb`: their values below their ends.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The prologue -/

theorem sPrologue_split : sPrologue = loadS sLxPP sSigner 1 :: ([hintW "lx_index" (runV 67 4),
    hintW "lx_windows" (runV 71 4)] ++ (List.range 13).map (fun s => cst (75 + s) (word (2 ^ s) 0))) := rfl

theorem sPrologue_seq : SeqOK 75 ((List.range 13).map (fun s => cst (75 + s) (word (2 ^ s) 0))) 88 :=
  seqB_ok (by decide +kernel)

theorem sPrologue_nb : NumBelow 88 (Stmt.valsList sPrologue) := numBelow_of_all (by decide +kernel)

/-- **The prologue completes**: `P` loaded, the shifts `his` and the windows' selectors `win`
hinted, the powers set. -/
theorem sPrologue_complete (σ : Val) {P : E} (hld : LoadHolds rd (σ sSigner) 1 P) (his win : Nat → E) :
    Completes C rd 66 88 sPrologue σ
      (fun σ' => σ' sLxPP = P ∧ (∀ w < 4, σ' (sHis w) = his w) ∧ (∀ w < 4, σ' (sWin w) = win w) ∧
        ∀ s < 13, σ' (sPower s) = gen ^ s) := by
  rw [sPrologue_split]
  refine Completes.load ⟨65, by norm_num, rfl⟩ hld (by norm_num) (fun σ1 he1 e1 => ?_)
  set σr := updRun (updRun σ1 67 4 his) 71 4 win with hσr
  have hr1 : Ext 67 71 σ1 (updRun σ1 67 4 his) := updRun_ext σ1 67 4 his
  have hr2 : Ext 71 75 (updRun σ1 67 4 his) σr := updRun_ext _ 71 4 win
  have hext : Ext 67 75 σ1 σr := hr1.trans hr2 (by norm_num) (by norm_num)
  have hhis : ∀ w < 4, σr (sHis w) = his w := fun w hw => by
    rw [show sHis w = V.n (67 + w) from rfl, hr2.apply (Or.inl (by omega))]
    exact updRun_at σ1 67 4 his hw
  have hwin : ∀ w < 4, σr (sWin w) = win w := fun w hw => updRun_at _ 71 4 win hw
  have hPr : σr (.n 66) = P := by rw [hext.apply (Or.inl (by norm_num))]; exact e1
  refine Completes.reload (hext.mono le_rfl (by norm_num)) ?_
  refine Completes.append (m := 75) (by norm_num) (by norm_num)
    (numBelow_of_all (by decide +kernel))
    (completes_atoms (Post := fun σ' => σ' = σr) rfl (Ext.refl _ _ _) rfl (fun a ha => by
      simp only [hintW, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl <;> trivial)) (fun σ2 _ e2 => ?_)
  subst e2
  obtain ⟨σ3, he3, -, hh3⟩ := seq_completes (C := C) (rd := rd) sPrologue_seq σr
  have hh := atomsHold_of_holdsList sPrologue_seq.atoms (hh3 True (fun _ => True) trivial)
  refine ⟨σ3, he3, ⟨?_, fun w hw => ?_, fun w hw => ?_, fun s hs => ?_⟩, hh3⟩
  · rw [show sLxPP = V.n 66 from rfl, he3.apply (Or.inl (by norm_num))]; exact hPr
  · rw [show sHis w = V.n (67 + w) from rfl, he3.apply (Or.inl (by omega))]; exact hhis w hw
  · rw [show sWin w = V.n (71 + w) from rfl, he3.apply (Or.inl (by omega))]; exact hwin w hw
  · have e := hh.atom (a := .const (.n (75 + s)) (word (2 ^ s) 0)) (by
      simp only [List.mem_map, List.mem_range]
      exact ⟨s, hs, rfl⟩)
    simp only [Atom.Holds] at e
    rw [sPower, e, word_two_pow_eq (by omega), Value.gen_pow_eq_ofK]

/-! ## The bottom layer's digest -/

theorem sDigest0_split : sDigest0 88 = [hintW "randomizer" [.n 88]] ++
    ([cst 89 (word (tw 12) 0), addS (.n 90) (sHis 0) (.n 89)] ++
      (loadS (.n 91) sSigner 2 :: loadS (.n 92) sSigner 3 ::
        ((copyS (.n 93) (.n 88) :: cst 94 (word 1 0) :: cst 95 (word 0 0) :: cst 96 (word 0 0) ::
          cst 97 (word (2 ^ 63) 0) ::
          (List.range 5).map (fun k => cst (98 + k) (word (if k = 0 then 1 else 0) 0))) ++
        [kecS [sLxPP, .n 90, .n 91, .n 92, .n 93, .n 94, .n 95, .n 96, .n 97, .n 99, .n 100,
          .n 101, .n 102] (runV 103 1) false false]))) := rfl

theorem sDigest0_nb : NumBelow 104 (Stmt.valsList (sDigest0 88)) := numBelow_of_all (by decide +kernel)

/-- **The bottom layer's digest completes**, its randomizer `rho` hinted, the message's cells `c`,
`d` loaded. -/
theorem sDigest0_complete (σ : Val) {rho c d : E} (hrho : IsCanonical128 rho) (hc : IsCanonical128 c)
    (hd : IsCanonical128 d) (hld2 : LoadHolds rd (σ sSigner) 2 c) (hld3 : LoadHolds rd (σ sSigner) 3 d)
    (hP : IsCanonical128 (σ sLxPP)) (hn0 : IsCanonical128 (σ (sHis 0))) :
    Completes C rd 88 104 (sDigest0 88) σ
      (fun σ' => σ' (.n 88) = rho ∧ σ' (.n 91) = c ∧ σ' (.n 92) = d) := by
  have hext : Ext 88 89 σ (Function.update σ (.n 88) rho) := fun v hv =>
    Function.update_of_ne (hv 88 le_rfl (by norm_num)) _ _
  refine Completes.reload (hext.mono le_rfl (by norm_num)) ?_
  rw [sDigest0_split]
  refine Completes.append (m := 89) (by norm_num) (by norm_num)
    (by rw [valsList_hint]; exact .cons ⟨88, by norm_num, rfl⟩ (.nil _)) (hintKeep_complete _ _ _ _ _)
    (fun σ1 _ e1 => ?_)
  subst e1
  have h88 : Function.update σ (.n 88) rho (.n 88) = rho := Function.update_self ..
  have hlow : ∀ k < 88, Function.update σ (.n 88) rho (.n k) = σ (.n k) := fun k hk =>
    Function.update_of_ne (by simp; omega) _ _
  refine Completes.seq (m := 91) (seqB_ok (by decide +kernel)) (by norm_num) (fun σ2 he2 hh2 => ?_)
  have hag2 := he2.agree
  have e89 : σ2 (.n 89) = word (tw 12) 0 := hh2.atom (a := .const (.n 89) _) (by simp [cst])
  have e90 : σ2 (.n 90) = σ2 (sHis 0) + σ2 (.n 89) :=
    hh2.atom (a := .add (.n 90) (sHis 0) (.n 89)) (by simp [addS])
  have hn02 : σ2 (sHis 0) = σ (sHis 0) := by
    rw [show sHis 0 = V.n 67 from rfl, hag2.apply ⟨67, by norm_num, rfl⟩]; exact hlow 67 (by norm_num)
  refine Completes.load ⟨65, by norm_num, rfl⟩ (w := c)
    (by rw [show sSigner = V.n 65 from rfl, hag2.apply ⟨65, by norm_num, rfl⟩, hlow 65 (by norm_num)]; exact hld2) (by norm_num)
    (fun σ3 he3 e3 => ?_)
  have hag3 := he3.agree
  refine Completes.load ⟨65, by norm_num, rfl⟩ (w := d)
    (by rw [show sSigner = V.n 65 from rfl, hag3.apply ⟨65, by norm_num, rfl⟩, hag2.apply ⟨65, by norm_num, rfl⟩, hlow 65 (by norm_num)]
        exact hld3) (by norm_num) (fun σ4 he4 e4 => ?_)
  have hag4 := he4.agree
  refine Completes.seq (m := 103) (seqB_ok (by decide +kernel)) (by norm_num) (fun σ5 he5 hh5 => ?_)
  have hag5 := he5.agree
  have v1 : σ5 sLxPP = σ sLxPP := by
    rw [show sLxPP = V.n 66 from rfl, hag5.apply ⟨66, by norm_num, rfl⟩, hag4.apply ⟨66, by norm_num, rfl⟩,
      hag3.apply ⟨66, by norm_num, rfl⟩, hag2.apply ⟨66, by norm_num, rfl⟩, hlow 66 (by norm_num)]
  have v90 : σ5 (.n 90) = σ (sHis 0) + word (tw 12) 0 := by
    rw [hag5.apply ⟨90, by norm_num, rfl⟩, hag4.apply ⟨90, by norm_num, rfl⟩,
      hag3.apply ⟨90, by norm_num, rfl⟩, e90, e89, hn02]
  have v91 : σ5 (.n 91) = c := by
    rw [hag5.apply ⟨91, by norm_num, rfl⟩, hag4.apply ⟨91, by norm_num, rfl⟩, e3]
  have v92 : σ5 (.n 92) = d := by rw [hag5.apply ⟨92, by norm_num, rfl⟩, e4]
  have v88 : σ5 (.n 88) = rho := by
    rw [hag5.apply ⟨88, by norm_num, rfl⟩, hag4.apply ⟨88, by norm_num, rfl⟩,
      hag3.apply ⟨88, by norm_num, rfl⟩, hag2.apply ⟨88, by norm_num, rfl⟩, h88]
  have v93 : σ5 (.n 93) = rho := by
    rw [← v88]; exact hh5.atom (a := .copy (.n 93) (.n 88)) (by simp [copyS])
  have vc : ∀ k w, Stmt.atom (.const (.n k) (word w 0)) ∈ (copyS (.n 93) (.n 88) :: cst 94 (word 1 0) ::
      cst 95 (word 0 0) :: cst 96 (word 0 0) :: cst 97 (word (2 ^ 63) 0) ::
      (List.range 5).map (fun k => cst (98 + k) (word (if k = 0 then 1 else 0) 0))) →
      IsCanonical128 (σ5 (.n k)) := fun k w h => by
    rw [show σ5 (.n k) = word w 0 from hh5.atom h]; exact canon_word _ _
  have vm : ∀ k, 0 < k → k < 5 → IsCanonical128 (σ5 (.n (98 + k))) := fun k h0 h5 =>
    vc (98 + k) 0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, List.mem_range.mpr h5,
        by simp [cst, show k ≠ 0 by omega]⟩))))))
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ([sLxPP, .n 90, .n 91, .n 92, .n 93, .n 94, .n 95,
      .n 96, .n 97, .n 99, .n 100, .n 101, .n 102].map σ5) cc) := by
    intro cc
    fin_cases cc <;> simp only [cells13, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ]
    · rw [v1]; exact hP
    · rw [v90]; exact canon_add hn0 (canon_word _ _)
    · rw [v91]; exact hc
    · rw [v92]; exact hd
    · rw [v93]; exact hrho
    · exact vc 94 1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact vc 95 0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact vc 96 0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))
    · exact vc 97 (2 ^ 63) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    · exact vm 1 (by norm_num) (by norm_num)
    · exact vm 2 (by norm_num) (by norm_num)
    · exact vm 3 (by norm_num) (by norm_num)
    · exact vm 4 (by norm_num) (by norm_num)
  refine ((kecS_complete (C := C) (rd := rd) σ5 103 (.inl rfl) rfl (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, by norm_num, rfl⟩) hcan false false).keep
    (Q := fun σ' => σ' (.n 88) = rho ∧ σ' (.n 91) = c ∧ σ' (.n 92) = d) ⟨v88, v91, v92⟩
    (fun σ' he h => ⟨by rw [he.apply (Or.inl (by norm_num))]; exact h.1,
      by rw [he.apply (Or.inl (by norm_num))]; exact h.2.1,
      by rw [he.apply (Or.inl (by norm_num))]; exact h.2.2⟩)).mono le_rfl le_rfl
    (fun σ' h => h.2)

/-! ## The top layer's digest -/

theorem sDigest1_split (b : Nat) (root : V) : sDigest1 b root =
    [cst b (word lxTop 0), addS (.n (b + 1)) (sHis 2) (.n b)] ++ (hintW "randomizer" [.n (b + 2)] ::
      ([cst (b + 3) (word (tw 12) 0), addS (.n (b + 4)) (.n (b + 1)) (.n (b + 3))] ++
        k64 sLxPad sLxPP (.n (b + 4)) root (.n (b + 2)) (b + 5) (b + 5 + 1))) := rfl

/-- **The top layer's index and digest complete**, its randomizer `rho` hinted. -/
theorem sDigest1_complete {b : Nat} {root : V} (σ : Val) {rho : E} (hb : 103 ≤ b) (hroot : NBv b root)
    (hrc : IsCanonical128 (σ root)) (hrho : IsCanonical128 rho) (hP : IsCanonical128 (σ sLxPP))
    (hn2 : IsCanonical128 (σ (sHis 2))) (hpad : PadOK σ sLxPad) :
    Completes C rd b (b + 5 + 2) (sDigest1 b root) σ (fun σ' => σ' (.n (b + 2)) = rho) := by
  rw [sDigest1_split]
  refine Completes.seq (m := b + 2)
    ⟨rfl, ⟨rfl, ⟨69, by omega, rfl⟩, ⟨b, by omega, rfl⟩⟩, rfl⟩ (by omega)
    (fun σ1 he1 hh1 => ?_)
  have hag1 := he1.agree
  have e0 : σ1 (.n b) = word lxTop 0 := hh1.atom (List.mem_cons_self ..)
  have e1 : σ1 (.n (b + 1)) = σ1 (sHis 2) + σ1 (.n b) :=
    hh1.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hext : Ext (b + 2) (b + 3) σ1 (Function.update σ1 (.n (b + 2)) rho) := fun v hv =>
    Function.update_of_ne (hv (b + 2) le_rfl (by omega)) _ _
  refine Completes.reload (hext.mono le_rfl (by omega)) ?_
  refine Completes.append (xs := [hintW "randomizer" [.n (b + 2)]]) (m := b + 3) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b + 2, by omega, rfl⟩ (.nil _)) (hintKeep_complete _ _ _ _ _)
    (fun σ2 _ e2 => ?_)
  subst e2
  have hr2 : Function.update σ1 (.n (b + 2)) rho (.n (b + 2)) = rho := Function.update_self ..
  have hlow : ∀ k < b + 2, Function.update σ1 (.n (b + 2)) rho (.n k) = σ1 (.n k) := fun k hk =>
    Function.update_of_ne (by simp; omega) _ _
  have hs3 : SeqOK (b + 3) [cst (b + 3) (word (tw 12) 0), addS (.n (b + 4)) (.n (b + 1)) (.n (b + 3))]
      (b + 5) := ⟨rfl, ⟨rfl, ⟨b + 1, by omega, rfl⟩, ⟨b + 3, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq (m := b + 5) hs3 (by omega) (fun σ3 he3 hh3 => ?_)
  have hag3 := he3.agree
  have e3 : σ3 (.n (b + 3)) = word (tw 12) 0 := hh3.atom (List.mem_cons_self ..)
  have e4 : σ3 (.n (b + 4)) = σ3 (.n (b + 1)) + σ3 (.n (b + 3)) :=
    hh3.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have tr : ∀ k < b, σ3 (.n k) = σ (.n k) := fun k hk => by
    rw [hag3.apply ⟨k, by omega, rfl⟩, hlow k (by omega), hag1.apply ⟨k, hk, rfl⟩]
  have v1 : σ3 (.n (b + 1)) = σ (sHis 2) + word lxTop 0 := by
    rw [hag3.apply ⟨b + 1, by omega, rfl⟩, hlow (b + 1) (by omega), e1, e0,
      show sHis 2 = V.n 69 from rfl, hag1.apply ⟨_, by omega, rfl⟩]
  have v2 : σ3 (.n (b + 2)) = rho := by rw [hag3.apply ⟨b + 2, by omega, rfl⟩, hr2]
  have hpad3 : PadOK σ3 sLxPad := by
    obtain ⟨q0, q1, q2, q3, q4⟩ := hpad
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [tr _ (by simp [sLxPad]; omega)]
    exacts [q0, q1, q2, q3, q4]
  have hroot3 : σ3 root = σ root := by
    obtain ⟨k, hk, rfl⟩ := hroot; exact tr k hk
  refine ((k64_complete (C := C) (rd := rd) σ3 hpad3 (by simp [sLxPad]; omega) (fun v hv => ?_)).keep
    (Q := fun σ' => σ' (.n (b + 2)) = rho) v2
    (fun σ' he h => by rw [he.apply (Or.inl (by omega))]; exact h)).mono le_rfl le_rfl (fun σ' h => h.2)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨⟨66, by omega, rfl⟩, by rw [show sLxPP = V.n 66 from rfl, tr 66 (by omega)]; exact hP⟩
  · have hc4 : IsCanonical128 (σ3 (.n (b + 4))) := by
      rw [e4, e3, v1]
      exact canon_add (canon_add hn2 (canon_word _ _)) (canon_word _ _)
    exact ⟨⟨b + 4, by omega, rfl⟩, hc4⟩
  · exact ⟨hroot.mono' (by omega), by rw [hroot3]; exact hrc⟩
  · exact ⟨⟨b + 2, by omega, rfl⟩, by rw [v2]; exact hrho⟩

theorem sDigest1_nb {b : Nat} {root : V} (hb : 103 ≤ b) (hroot : NBv b root) :
    NumBelow (b + 7) (Stmt.valsList (sDigest1 b root)) := by
  intro x hx
  rw [sDigest1_split, valsList_append, valsList_cons (hintW "randomizer" [.n (b + 2)]), valsList_append] at hx
  rcases List.mem_append.mp hx with hx | hx
  · simp [cst, addS, Stmt.vals, Atom.vals] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨_, by omega, rfl⟩
  rcases List.mem_append.mp hx with hx | hx
  · simp [hintW, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] at hx
    subst hx
    exact ⟨b + 2, by omega, rfl⟩
  rcases List.mem_append.mp hx with hx | hx
  · simp [cst, addS, Stmt.vals, Atom.vals] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals exact ⟨_, by omega, rfl⟩
  rcases k64_vals _ _ _ _ _ _ _ hx with hx | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨66, by omega, rfl⟩
    · exact ⟨b + 4, by omega, rfl⟩
    · exact NBv.mono' hroot (show b ≤ b + 7 by omega)
    · exact ⟨b + 2, by omega, rfl⟩
  · exact ⟨b + 5, by omega, rfl⟩
  · exact ⟨sLxPad + k, by simp only [sLxPad]; omega, rfl⟩
  · exact ⟨b + 5 + 1 + k, by omega, rfl⟩

end
end LeanVM.Guest.B1.Sig
