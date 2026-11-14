/-
  LeanVM.Guest.B1.KeccakGkr.VkHolds

  `verify_keccak`'s core IR computes its meaning: the sections of `vkT`, composed by `vk_runsTo`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkChecks
public import LeanVM.Guest.B1.KeccakGkr.VkBody
public import LeanVM.Guest.B1.KeccakGkr.VkChain
public import LeanVM.Guest.B1.KeccakGkr.VkFirst

/-!
# `verify_keccak`, assembled

The body is `vkT` (`vk_body`); its sections (`vkHeadT_holds`, the copy loop `verify_keccak_loop0`,
`vkFirstT_holds`, `vkStepsT_holds`, `vkOutT_holds`, `vkInT_holds`, `vkFinT_holds`) give the sponge
runs, the reads and the two opening checks (`vk_out_check`, `vk_in_check`), and `vk_runsTo`
composes them into `keccakSeg`'s run.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

theorem find_vk : coreProgram.find? "verify_keccak" = some fn% «verify_keccak» :=
  coreProgram_find?_at (j := idx% «verify_keccak») rfl

theorem readsAt_single {rd : Reader} {p a : E} (h : LoadHolds rd p 0 a) : ReadsAt rd p [a] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  exact h

/-- **`verify_keccak`** on a reader where `keccak_layer` has its meaning. -/
theorem verify_keccak_holds_of (rd : Reader) (hK : keccak_layer_Spec rd) :
    verify_keccak_Spec rd := by
  intro args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_vk args rets).mp hrel
  rw [show (fn% «verify_keccak»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8,
      .n 9,
    .n 10, .n 11] from rfl] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  simp only [MeaningVerifyKeccak]
  intro htabs τ chis outs hτ1 hτ2 htg hchiL hchi houtsL hol
  rw [show Fn.body fn% «verify_keccak» = vkT from vk_body, vkT, holdsList_append, holdsList_append,
      holdsList_append, holdsList_append,
    holdsList_append] at hb
  -- the head
  replace hb := vkHeadT_holds hτ1 hτ2 htg hb
  obtain ⟨h17, -, h33, h47, hzw, hloop11, h64, hsq1, hsq5, h89, hrl, ⟨l191, p191⟩, hb⟩ := hb
  have hzv : ∀ i < 4, LoadHolds rd (σ (.n 9)) i (chis.getD i 0) := by
    intro i hi
    obtain ⟨a, b⟩ := hzw i hi
    rw [List.getD_eq_getElem _ _ (by omega), ← loadHolds_unique a (hchi i (by omega))]
    exact b
  have hne : 1 + σ (.n 18) ≠ 0 := by
    rw [h17]; exact gen_pow_ne_one (by omega) (by unfold ordG; omega)
  have hcp := copyLoop_sound find_copyLoop11 copyLoop_body11 rfl h17 (by unfold ordG; omega)
    (hloop11 hne)
  have hlen4 : ((chis.take τ).drop 4).length = τ - 4 := by simp; omega
  have hptR : ReadsAt rd (σ (.n 61)) ((chis.take τ).drop 4 ++ [σ (.n 86)]) := by
    rw [readsAt_append]
    refine ⟨fun j hj ↦ ?_, ?_⟩
    · obtain ⟨v, hs, hd⟩ := hcp j (by omega)
      rw [loadHolds_mul_gen_pow] at hs
      have e := loadHolds_unique hs (hchi (4 + j) (by omega))
      rw [e] at hd
      simpa using hd
    · rw [hlen4, ← h17, ← h64]
      exact readsAt_single h89
  generalize hrlE : (List.range 5).map (fun i ↦ σ (.n (101 + 14 * i))) = rl at hsq5
  have hrlL : rl.length = 5 := by rw [← hrlE]; simp
  have hrlLoad : ∀ i < 5, LoadHolds rd (σ (.n 87)) i (rl.getD i 0) := by
    intro i hi
    rw [← hrlE, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    exact hrl i hi
  -- the first claim
  replace hb := vkFirstT_holds hτ1 hchiL hzv hrlL hrlLoad h89 hptR houtsL hol hb
  obtain ⟨hcr1, hlanes, hb⟩ := hb
  -- the layers
  have hL0 : ∀ v, LoadHolds rd (σ (.n 234)) 30 v → v = (eqKernel rl).getD 0 0 :=
    fun v hv ↦ loadHolds_unique hv (by simpa using hlanes 0 (by norm_num))
  have hw0 : ∀ z < 64, (vkFirst (chis.take τ) outs (σ (.n 158)) [σ (.n 86)] rl).weights.getD z 0 =
      (eqKernel rl).getD 0 0 * gen ^ z := by
    intro z hz
    rw [vkFirst_weights _ _ _ _ _ (by omega), Nat.div_eq_of_lt hz, Nat.mod_eq_of_lt hz,
      ← gen_pow_eq_eOfNat hz]
  replace hb := vkStepsT_holds hτ1 hτ2 h17 h33 h47 hcr1 hL0 hw0 p191 hK htabs hb
  obtain ⟨xsL, c', hxsL, hrunL, hcr', h3690, hb⟩ := hb
  -- the committed outputs
  replace hb := vkOutT_holds (L := fun lane ↦ (eqKernel rl).getD lane 0) hτ1 hτ2 htg h17
    (fun lane hl v hv ↦ loadHolds_unique hv (hlanes lane (by omega))) h64 h89 hb
  obtain ⟨mO, slotO, hmOL, hmOR, hO, hslotO, h3699, ⟨l3701, p3701⟩, hchk, hcpO, hb⟩ := hb
  have hslotOL : slotO.length = 6 := by
    have := plainRun_length mO (σ (.n 158))
      ⟨[σ (.n 915), σ (.n 916), σ (.n 917), σ (.n 918), σ (.n 919)], []⟩
    rw [hO, hmOL] at this; exact this
  -- the inputs
  replace hb := vkInT_holds htg hcr' p3701 hb
  obtain ⟨mI, mS, low, slotI, hmIL, hmIR, hI, hlow, h3985, h4104, hmSL, hmSR, hS, hslotI, h4107,
    h4115, hslR, hslL, hpl, hpc, h1251, hb⟩ := hb
  have hlowL : low.length = 4 := by
    have := plainRun_length mI c'.value
      ((⟨[σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928)], []⟩ : Fs).absorb
        (σ (.n 931)) dsObserve)
    rw [hI, hmIL] at this; exact this
  have hslotIL : slotI.length = 6 := by
    have := plainRun_length mS (σ (.n 1209))
      ⟨[σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)], []⟩
    rw [hS, hmSL] at this; exact this
  -- the final check
  replace hb := vkFinT_holds hτ1 hτ2 h17 hcr' hslotIL hslotI hslL h1251 hb
  obtain ⟨lanes, loc, -, hlocL, hw, hform, hF, hSh, hpoint, hret⟩ := hb
  generalize hslE : (List.range 64).map (fun z ↦ σ (.n (slB 1345 z))) = slices at hslR hpl hpc
  have hslices : slices.length = 64 := by rw [← hslE]; simp
  have hptL : c'.point.length = τ - 3 := hcr'.2.1
  have hfin : multilinearEval c'.mu low *
      dot ((foldAll slotI (keccakSlotWeights τ c' 0 2)).headD []) slices = σ (.n 1339) := by
    rw [← h4104]
    refine vk_in_check (by omega) hptL hlocL hw hslotIL hslices hF (fun r hr ↦ ?_) hform
    rw [hSh r hr]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    rw [← hslE, List.getD_eq_getElem _ _ (by simpa using hz), List.getElem_map,
      List.getElem_range]
  have habs : (⟨(cap5 152).map σ, []⟩ : Fs).absorb (σ (.n 158)) dsObserve =
      ⟨[σ (.n 152), σ (.n 153), σ (.n 154), σ (.n 155), σ (.n 156)], [(σ (.n 158), dsObserve)]⟩ := by
    simp [Fs.absorb, cap5, rateScalars]
  have hrun := vk_runsTo τ (chis.take τ) outs (by rw [keccakSegmentBits_eq]; exact hsq1)
    (by rw [show keccakLaneBits = 5 from rfl]; exact hsq5) (by rw [habs]; exact hrunL) hmOL hO
    (vk_out_check (chis.take τ) outs (σ (.n 158)) (σ (.n 86)) rl hlen4 hslotOL hchk)
    hmIL hI hmSL hS hslices hfin
  refine ⟨_, _, _, slices, _, _, ?_, hrun, hpl, ?_, ?_, ?_, ?_, ?_, hslices, ?_⟩
  · -- the words read at the cursor
    simp only [List.append_assoc]
    rw [readsAt_append, readsAt_append, readsAt_append, readsAt_append, readsAt_append,
      readsAt_append]
    simp only [List.length_singleton, pow_one, flatMap_pairs_length, hmOL, hmIL, hmSL]
    refine ⟨readsAt_single l191, hxsL, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h3690]; exact hmOR
    · rw [← h3690, show 2 * 6 = 12 from rfl, ← h3699]; exact readsAt_single l3701
    · rw [← h3690, show 2 * 6 = 12 from rfl, ← h3699]; exact hmIR
    · rw [← h3690, show 2 * 6 = 12 from rfl, ← h3699, show 2 * 4 = 8 from rfl, ← h3985]
      exact hmSR
    · rw [← h3690, show 2 * 6 = 12 from rfl, ← h3699, show 2 * 4 = 8 from rfl, ← h3985,
        ← h4115]
      exact hslR
  · -- the committed outputs' point at `z_vals`
    rw [List.take_append_drop, readsAt_append, List.length_take, Nat.min_eq_left hchiL]
    refine ⟨fun k hk ↦ ?_, hslotO⟩
    simp only [List.length_take] at hk
    rw [List.getElem_take]
    by_cases hk4 : k < 4
    · have := hzv k hk4
      rwa [List.getD_eq_getElem _ _ (by omega)] at this
    · obtain ⟨v, h58, h9⟩ := hcpO (k - 4) (by omega)
      have e := loadHolds_unique h58 (hptR (k - 4) (by simp; omega))
      rw [loadHolds_mul_gen_pow, e, List.getElem_append_left (by simp; omega), List.getElem_drop,
        List.getElem_take] at h9
      simp only [show 4 + (k - 4) = k by omega] at h9
      exact h9
  · -- the inputs' point at `z_vals·g^39`
    rw [readsAt_append, readsAt_append, List.length_append, hlowL, List.length_take,
      Nat.min_eq_left (by omega : τ - 4 ≤ c'.point.length)]
    refine ⟨⟨hlow, ?_⟩, ?_⟩
    · intro j hj
      rw [List.length_take] at hj
      obtain ⟨pp, v, hpp, hv, h9⟩ := hpoint j (by omega)
      obtain ⟨pp', hpp', hppR⟩ := hcr'.2.2.2.2.2.1
      rw [loadHolds_unique hpp hpp'] at hv
      rw [List.getElem_take, ← loadHolds_unique hv (hppR j (by omega)), mul_assoc, ← pow_add]
      exact h9
    · have e : σ (.n 9) * gen ^ qkeccakVarsCap * gen ^ (4 + (τ - 4)) = σ (.n 1330) := by
        rw [h4107, show 4 + (τ - 4) = τ by omega]
      rw [e]; exact hslotI
  · -- the slices
    rw [← hslE]
    intro z hz
    simp only [List.length_map, List.length_range] at hz
    rw [List.getElem_map, List.getElem_range]
    exact hslL z hz
  · -- the lengths
    simp only [List.length_append, List.length_take, List.length_drop, hslotOL, qkeccakSlotBits_eq']
    omega
  · simp only [List.length_append, List.length_take, hlowL, hptL, hslotIL, qkeccakSlotBits_eq']
    omega
  · -- the returns
    rw [← hret, hpc]
    simp only [List.length_cons, List.length_nil, List.length_append, flatMap_pairs_length, hmOL, hmIL, hmSL,
      hslices, h4115, h3985, h3699, h3690, List.cons_append, List.nil_append, List.cons.injEq,
      and_true, true_and]
    ring

/-- **`verify_keccak`** (TRIAGE #53): its core IR computes its meaning on a memory
image, given `grind_check`'s meaning at `3` bits (the layers' grind before `s`). -/
theorem verify_keccak_holds {κ : ℕ} (hκ : κ ≤ 32) (hκ' : winTabBits ≤ κ) (L : MemoryImage κ)
    (hg : grind_check_Spec 3) : verify_keccak_Spec L.read :=
  verify_keccak_holds_of L.read (keccak_layer_holds hκ hκ' L hg)

end
end LeanVM.Guest.B1.VerifySub
