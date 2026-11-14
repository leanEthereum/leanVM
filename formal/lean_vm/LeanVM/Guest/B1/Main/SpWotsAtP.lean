/-
  LeanVM.Guest.B1.Main.SpWotsAtP

  An honest call of `sp_wots` placed with its pops (`RelAtInP`): its digest's digit words and its chains' values (`Sig.spWotsPops`).
-/

module

public import LeanVM.Guest.B1.Main.RawAtSP

/-!
# `sp_wots`, placed with its pops

`sp_wots_complete_pops`' valuation under the trivial call relation, placed by `relAtInP_of_walk`: it calls nothing, places nothing (`raw4_pure`) and loads nothing (`Lift.spWots_leafOk`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

/-- **An honest call of `sp_wots`, placed, with its pops**: at every frame pointer, in its frame, popping its digest's
digit words and its chains' values. -/
theorem spWots_relAtInP (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} (hm : Sig.MemOK rd 64)
    (publicSeed : HashSig.PublicParameter) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) (digest : HashSig.Digest) (values : Sphincs.ChainIndex → HashSig.Digest)
    (hT : Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits digest)) (R : ℕ → Prop) (fp : ℕ) :
    RelAtInP coreProgram fs cert rd R (fun _ => False) fp (fs "sp_wots") "sp_wots"
      [Sig.cellOf128 publicSeed, (Sig.keyAdrsCells layer.val tree.val leaf.val).1,
        (Sig.keyAdrsCells layer.val tree.val leaf.val).2, Sig.cellOf128 digest]
      [Sig.cellOf128 (Sig.wotsLeafOf publicSeed layer tree leaf digest values)] (Sig.spWotsPops digest values) := by
  obtain ⟨σ, h0, h12, h3, hb, es, vs, hw, hc, hp⟩ :=
    Sig.sp_wots_complete_pops (fun _ _ _ => True) rd publicSeed layer tree leaf digest values hm hT
  have hsat := walk_sat (P := coreProgram) (fn% «sp_wots»).body
    (coreProgram_wf _ (List.mem_of_find?_eq_some Sig.find_sp_wots)) hb
  rw [hw] at hsat
  have hpure := walk_pure (σ := σ) (fn% «sp_wots»).body (raw4_pure _ (by simp) _ Sig.find_sp_wots)
  rw [hw] at hpure
  have hal : allocs σ es = [] := allocs_pure hpure
  have h := relAtInP_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) coreProgram_wf
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (fp := fp) (N := 0) (pss := [])
    (args := [Sig.cellOf128 publicSeed, (Sig.keyAdrsCells layer.val tree.val leaf.val).1,
      (Sig.keyAdrsCells layer.val tree.val leaf.val).2, Sig.cellOf128 digest])
    (rets := [Sig.cellOf128 (Sig.wotsLeafOf publicSeed layer tree leaf digest values)])
    (ps := Sig.spWotsPops digest values) Sig.find_sp_wots (Or.inr hc)
    (by
      rw [Sig.sp_wots_params]
      show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] = _
      rw [h0, h3, ← h12]) hw hsat.2
    (fun e he => (hsat.1 e he).1) (by rw [allocDsts_pure hpure, hal]; rfl)
    (fun q hq => by rw [addrs_pure hpure] at hq; simp at hq)
    (by rw [hc]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_) (fun _ h => h.elim)
    (by rw [splice_nil_of_calls es hc]; exact hp)
  · rw [hal, List.sum_nil, Nat.add_zero, Nat.add_zero] at h; exact h
  · have hall := Lift.walk_leafOk (σ := σ) (fn% «sp_wots»).body Lift.spWots_leafOk
    rw [hw] at hall
    obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    have hok := hall e he
    cases e with
    | atom a =>
      cases a with
      | load => simp [Lift.EvLeafOk, Lift.noLoad] at hok
      | _ => simp [Ev.loadAddr?] at hea
    | _ => simp [Ev.loadAddr?] at hea

end
end LeanVM.Guest.B1.Main
