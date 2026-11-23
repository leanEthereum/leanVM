/-
  LeanVM.Guest.CoreMode.Fn.open_stacked.Sound

  `open_stacked`'s own residual families, sound (`CoreMode/FnReg.lean`): its rate values pinned on its returning
  paths (`valExpB_sound`), its table read at its rate selector (`topSels_sound`).
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fam.ResF
public import LeanVM.Guest.CoreMode.Fam.ResExpC
public import LeanVM.Guest.CoreMode.Fn.open_stacked.Fam

namespace LeanVM.Guest.CoreMode.Own.open_stacked

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec

public section

section

variable {σ : Val} {rd : Reader} {fn : Fn} {es : List Ev} {vs : List V}

theorem expFam_holds (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) {r : CRes}
    (h : expFam fn r = true) : r.Holds σ := by
  unfold expFam at h
  split at h
  · simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨e, -, he, hσ⟩ := valExpB_sound hw hh h.2
    exact ltF_of_pow h.1 he hσ
  · cases h

theorem selPt_sound (hw : walk σ fn.body = .ret es vs) {B J o : ℕ} {cs : List CCell} (h : selPt fn B J o cs = true) :
    ∃ e, σ (V.n J) = ofK (addressOfIndex e) ∧ (⟨[(B, 1)], o + e⟩ : CCell) ∈ cs := by
  unfold selPt at h
  obtain ⟨p, hp, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hJ, -⟩, hall⟩ := h
  obtain ⟨e, he, hσ⟩ := topSels_sound hw (show (p.1, p.2) ∈ Res.topSels fn.body from hp)
  rw [hJ] at hσ
  exact ⟨e, hσ, by simpa using hall e he⟩

theorem selPts_holds (hw : walk σ fn.body = .ret es vs) {r : CRes} (h : selPts fn r = true) : r.Holds σ := by
  unfold selPts at h
  split at h
  · rename_i a b o cs
    rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨e, he, hm⟩ := selPt_sound hw h
      refine ⟨_, hm, ?_⟩
      simp only [CCell.addrW, CCell.valW, prodW, vw, pow_one, mul_one, he]
      rw [mul_assoc, Exec.ofK_gpow_mul, Nat.add_comm e o]
    · obtain ⟨e, he, hm⟩ := selPt_sound hw h
      refine ⟨_, hm, ?_⟩
      simp only [CCell.addrW, CCell.valW, prodW, vw, pow_one, mul_one, he]
      rw [← Exec.ofK_gpow_mul o e]
      ring
  · cases h

end

/-- **Its families** (`expFam_holds`, `selPts_holds`), on its honest instances' returning paths. -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  intro c hc r hr I hI σ bufs kids ht fn hf x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hc
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
  obtain ⟨fn', hfn', -, es, vs, hw, -, hh, -⟩ := hv
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hfn')
  simp only [Bool.or_eq_true] at hx
  rcases hx with hx | hx
  · exact expFam_holds hw hh hx
  · exact selPts_holds hw hx

end

end LeanVM.Guest.CoreMode.Own.open_stacked
