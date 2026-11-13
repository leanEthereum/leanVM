/-
  LeanVM.Guest.B1.Main.SphincsAtP

  An honest call of `verify_sig_lean_sphincs` placed with its pops (`VerifySigP`), and `main_loop3` placed with its pops without that hypothesis (`rawS_completeAtDP'`).
-/

module

public import LeanVM.Guest.B1.Main.SpWotsAtP

/-!
# `verify_sig_lean_sphincs`, placed with its pops

`Sig.verify_sig_lean_sphincs_complete_vals`' valuation under the trivial call relation, placed by `relAtInP_of_walk`: the body is straight (`sStraight`), so its calls are the three layers' calls of `sp_wots` (`sCalls`), the honest ones (`Sig.SpCallsAt`), each placed by `spWots_relAtInP` (`layer_relAtInP`); it places nothing (`raw4_pure`) and loads the claim and the byte table.

* `verifySigP`: `VerifySigP` in `fs "verify_sig_lean_sphincs" + 3 * fs "sp_wots"` words;
* `rawS_completeAtDP'`: `rawS_completeAtDP` at those words, without the hypothesis.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtDP Returns)

@[expose] public section

/-- `verify_sig_lean_sphincs`'s statements before its return. -/
def sPreR : List Stmt := Sig.sPre ++ [.atom (.assertEq Sig.sLayerT.2.2 Sig.sRoot)]

theorem sBody_straight : (fn% «verify_sig_lean_sphincs»).body = sPreR ++ [.ret []] := by
  rw [Sig.sBody_eq, Sig.sBody_splitC, sPreR, List.append_assoc]
  rfl

theorem sStraight : sPreR.all Stmt.straight = true := by decide +kernel

theorem sCalls : sPreR.filterMap Stmt.callS = [(none, "sp_wots", Sig.sCallArgs 0, [Sig.sLeafOf 0]),
    (none, "sp_wots", Sig.sCallArgs 1, [Sig.sLeafOf 1]), (none, "sp_wots", Sig.sCallArgs 2, [Sig.sLeafOf 2])] := by
  decide +kernel

theorem verify_sig_lean_sphincs_not_loop : coreProgram.loop "verify_sig_lean_sphincs" = false := by decide +kernel

/-- **Layer `L`'s call of `sp_wots`, placed, with its pops**, when it is the honest one. -/
theorem layer_relAtInP (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} (hm : Sig.MemOK rd 64)
    {pk : Sphincs.PublicKey} {m : HashSig.Message} {sig : Sphincs.Signature} {σ : Val} {L : Sphincs.Layer} {S : E}
    (hT : Sphincs.TargetSum.Valid
      (Sphincs.TargetSum.base2bDigits (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig L S))))
    (h : Sig.LayerCallAt pk m sig σ L S) (R : ℕ → Prop) (fp : ℕ) :
    RelAtInP coreProgram fs cert rd R (fun _ => False) fp (fs "sp_wots") "sp_wots" ((Sig.sCallArgs L.val).map σ)
      ([Sig.sLeafOf L.val].map σ) (Sig.spKid pk m sig L S) := by
  have hr := spWots_relAtInP fs cert hm pk.publicSeed L (Sphincs.treeOfIndex L (Sig.digestIdx pk m sig))
    (Sphincs.leafOfIndex L (Sig.digestIdx pk m sig)) (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig L S))
    (sig.layers L).chainValues hT R fp
  rw [Sig.cellOf128_cellVal] at hr
  rw [h.1, List.map_cons, List.map_nil, h.2]
  exact hr

/-- **The three layers' encodings reach the target sum**, for a signature that verifies. -/
theorem sp_layers_valid {pk : Sphincs.PublicKey} {m : HashSig.Message} {sig : Sphincs.Signature}
    (hv : Sphincs.verifyWithKeccak pk m sig = true) :
    Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits
        (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig ⟨0, by decide⟩ (Sig.forsKeyCell pk m sig)))) ∧
      Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits
        (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig ⟨1, by decide⟩ (Sig.sRoot0 pk m sig)))) ∧
      Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits
        (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig ⟨2, by decide⟩ (Sig.sRoot1 pk m sig)))) := by
  obtain ⟨r0, r1, h0, h1, h2⟩ := (Sig.verifyWithKeccak_iff_stages pk m sig).mp hv
  rw [Sig.sForsKeyOf_eq] at h0
  obtain ⟨hV0, hr0⟩ := Sig.layer_cells h0
  rw [hr0] at h1
  obtain ⟨hV1, hr1⟩ := Sig.layer_cells h1
  rw [hr1] at h2
  exact ⟨hV0, hV1, (Sig.layer_cells h2).1⟩

/-- **`verify_sig_lean_sphincs` placed with its pops**, in its frame and its three calls of `sp_wots`. -/
theorem verifySigP (fs : String → ℕ) (cert : String → V → ℕ) :
    VerifySigP fs cert (fs "verify_sig_lean_sphincs" + 3 * fs "sp_wots") := by
  intro rd R p bb pk m sig hm hbb hat hv hreg hregb fp
  obtain ⟨σ, h0, h1, hb, hwk, -, hcs⟩ := Sig.verify_sig_lean_sphincs_complete_vals (fun _ _ _ => True) rd p bb pk m sig
    (fun _ _ _ _ _ _ _ => trivial) hm hbb hat hv
  have hw := walk_straight σ [] sPreR sStraight
  set es := sPreR.flatMap (slEvs σ) with hes
  have hwf := coreProgram_wf _ (List.mem_of_find?_eq_some Sig.find_verify_sig_lean_sphincs)
  have hpu := raw4_pure _ (by simp) _ Sig.find_verify_sig_lean_sphincs
  rw [sBody_straight] at hwf hb hpu
  generalize hB : sPreR ++ [Stmt.ret []] = B at hwf hb hpu hw
  have hsat := walk_sat (P := coreProgram) _ hwf hb
  rw [hw] at hsat
  have hpure := walk_pure (σ := σ) _ hpu
  rw [hw] at hpure
  rw [← hB, ← sBody_straight] at hw
  have hal : allocs σ es = [] := allocs_pure hpure
  have hc : calls es = [⟨"sp_wots", Sig.sCallArgs 0, [Sig.sLeafOf 0], true⟩,
      ⟨"sp_wots", Sig.sCallArgs 1, [Sig.sLeafOf 1], true⟩, ⟨"sp_wots", Sig.sCallArgs 2, [Sig.sLeafOf 2], true⟩] := by
    rw [(straight_parts σ _ sStraight).2.2.2, sCalls]
    rfl
  obtain ⟨hld, hps⟩ := hwk es [] hw
  obtain ⟨hV0, hV1, hV2⟩ := sp_layers_valid hv
  have hm64 : Sig.MemOK rd 64 := fun i hi => hm i (by omega)
  have h := relAtInP_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) coreProgram_wf
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (fp := fp) (N := 3 * fs "sp_wots")
    (args := [p, bb]) (rets := []) (pss := Sig.spKids pk m sig) (ps := Sig.spSegPops pk m sig)
    Sig.find_verify_sig_lean_sphincs (Or.inl verify_sig_lean_sphincs_not_loop)
    (by
      rw [Sig.verify_sig_lean_sphincs_params]
      show [σ (.n 0), σ (.n 1)] = _
      rw [h0, h1]) hw rfl (fun e he => (hsat.1 e he).1) (by rw [allocDsts_pure hpure, hal]; rfl)
    (fun q hq => by rw [addrs_pure hpure] at hq; simp at hq)
    (by
      rw [hc]
      exact ⟨fs "sp_wots", 2 * fs "sp_wots", fun _ => False, fun _ => False, by ring, fun _ h => h.elim,
        layer_relAtInP fs cert hm64 hV0 hcs.1 _ _,
        fs "sp_wots", fs "sp_wots", fun _ => False, fun _ => False, by ring, fun _ h => h.elim,
        layer_relAtInP fs cert hm64 hV1 hcs.2.1 _ _,
        fs "sp_wots", 0, fun _ => False, fun _ => False, rfl, fun _ h => h.elim,
        layer_relAtInP fs cert hm64 hV2 hcs.2.2 _ _, rfl, fun _ h => h.elim⟩)
    (fun A hA => ?_) (fun _ h => h.elim) hps
  · rw [hal, List.sum_nil, Nat.add_zero] at h; exact h
  · rcases hld A hA with ⟨k, hk, rfl⟩ | ⟨v, hv', rfl⟩
    · obtain ⟨i, hi, hR⟩ := hreg k hk
      exact ⟨i, hi, Or.inr (Or.inl hR)⟩
    · obtain ⟨i, hi, hR⟩ := hregb v hv'
      exact ⟨i, hi, Or.inr (Or.inl hR)⟩

/-- **`main_loop3` is complete, placed, with its pops** (`rawS_completeAtDP` with `verifySigP`). -/
theorem rawS_completeAtDP' (fs : String → ℕ) (cert : String → V → ℕ) {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout}
    (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 23) (hnrs : nrs < 2 ^ 34) :
    ∀ j < nrs, CompleteAtDP fs cert 23 name% «main_loop3» Lin
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] (Returns [])
      (fun _ => (List.range' j (nrs - j)).flatMap (l4Pops D)) :=
  rawS_completeAtDP fs cert (verifySigP fs cert) D hY hnrs

end
end LeanVM.Guest.B1.Main
