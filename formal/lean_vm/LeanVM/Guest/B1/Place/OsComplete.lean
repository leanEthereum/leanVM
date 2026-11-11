/-
  LeanVM.Guest.B1.Place.OsComplete

  open_stacked is complete placed at every stack size and rate: the two statements the guest's
  completeness consumes, from the honest valuation's values.
-/

module

public import LeanVM.Guest.B1.Place.OsArm
public import LeanVM.Guest.B1.Place.OsMeanB
public import LeanVM.Guest.B1.Place.ArmFactsAll
public import LeanVM.Guest.B1.Place.HonestProof
public import LeanVM.Guest.B1.Place.LpProof
public import LeanVM.Guest.B1.Place.LqProof
public import LeanVM.Guest.B1.Place.LrProof
public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.B1.Whir.FactsAll

/-!
# `open_stacked`, placed, every arm

`open_stacked_completeAtO_of`: the arm of `μ`, called on the rate's selector, is complete placed at
an optional words bound (`osBosAt`), from the arms' decided facts (`os_arm_facts`,
`os_kid_shapes`, `ArmFactsAll`), the helpers' placed statements (`level_positions_completeAt`,
`level_queries_completeAt`, `level_residual_completeAt`), the trace's data (`os_helper_facts`),
the named callees (`osCalleesRegD_holds`, `kindDB`), the honest valuation's values
(`os_call_vals_Spec`) and the dispatches on the rate's selector (`OsDispRate`).
`open_stacked_completeAtD_of`, `open_stacked_completeAtB_of`: the two statements.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- Every arm's dispatches are on the rate's selector over its four rates. -/
def OsDispRate : Prop :=
  ∀ m < osArms, ∀ s ∈ osBodyAc (osCfg m), ∀ x fs a r, s = .dispatch x fs a r →
    x = .n osRate ∧ fs.length = 4

/-- **Every arm's dispatches are on the rate's selector**, decided per arm (`ArmBodyP`). -/
theorem os_disp_rate : OsDispRate := fun m hm ↦ dispRate_of (armBody_all m hm).2.2.2.2.2

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

theorem osCalleeNames_rate (m ri : ℕ) : osCalleeNames (osCfgR m ri) = osCalleeNames (osCfg m) := by
  unfold osCalleeNames osCallees; rw [← osBody_rate]

theorem osBos_rate (fs' Bk : String → ℕ) (name : String) (m ri : ℕ) :
    osBos fs' Bk name (osCfgR m ri) = osBos fs' Bk name (osCfg m) := by
  unfold osBos osKidsB osCallees; rw [osSizesL_rate, ← osBody_rate]

/-- The decoders' frame pointers, chosen per `lpTable` name. -/
noncomputable def osLpDfp (hlp : ∀ e ∈ lpTable, ∃ dfp : ℕ → ℕ → ℕ, ∀ Bd : Option ℕ,
    LpAtO fs cert κ e.1 e.2.1 e.2.2.2.1 e.2.2.2.2 dfp Bd) (name : String) : ℕ → ℕ → ℕ :=
  open Classical in
  if h : ∃ e ∈ lpTable, e.1 = name then Classical.choose (hlp h.choose h.choose_spec.1)
  else fun _ _ ↦ 0

theorem osLpDfp_spec (hlp : ∀ e ∈ lpTable, ∃ dfp : ℕ → ℕ → ℕ, ∀ Bd : Option ℕ,
    LpAtO fs cert κ e.1 e.2.1 e.2.2.2.1 e.2.2.2.2 dfp Bd) (hnd : (lpTable.map (·.1)).Nodup) :
    ∀ e ∈ lpTable, ∀ Bd, LpAtO fs cert κ e.1 e.2.1 e.2.2.2.1 e.2.2.2.2 (osLpDfp hlp e.1) Bd := by
  intro e he Bd
  have hex : ∃ e' ∈ lpTable, e'.1 = e.1 := ⟨e, he, rfl⟩
  have key : ∀ e' ∈ lpTable, e'.1 = e.1 → ∀ D : ℕ → ℕ → ℕ,
      (∀ Bd', LpAtO fs cert κ e'.1 e'.2.1 e'.2.2.2.1 e'.2.2.2.2 D Bd') →
      LpAtO fs cert κ e.1 e.2.1 e.2.2.2.1 e.2.2.2.2 D Bd := fun e' he' hn D hD ↦ by
    have := List.inj_on_of_nodup_map hnd he' he hn
    subst this
    exact hD Bd
  unfold osLpDfp
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact key _ hex.choose_spec.1 hex.choose_spec.2 _ (Classical.choose_spec (hlp _ hex.choose_spec.1))

/-- **`open_stacked` is complete placed at an optional words bound.** -/
theorem open_stacked_completeAtO_of (hvals : os_call_vals_Spec) (hdr : OsDispRate) {μ r : ℕ}
    (hμ1 : minOpenLog ≤ μ) (hμ2 : μ ≤ 30) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 7 ≤ κ)
    {Bd : Option (String → ℕ)}
    (hkB : ∀ m < osArms, ∀ f ∈ osCalleeNames (osCfg m), ∀ Bk ∈ Bd,
      TotalLe coreProgram fs f (fun _ ↦ Bk f))
    {S : KeccakState} {root : Digest} {target cur : E} {xs : List E} {os : List (List Opening)}
    {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : NoZeroChallenge μ r target S xs os root) (hcaps : CapsAgree μ r target S xs os root)
    {Lin : Layout} (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs) :
    CompleteAtO fs cert κ (openName μ) Lin
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur])
      (OsOut μ w) (Bd.map fun Bk ↦ osBosAt fs Bk μ) := by
  set m := μ - minOpenLog with hmd
  set ri := r - 1 with hrid
  have hm : m < osArms := by unfold osArms ligNSizes minOpenLog at *; omega
  have hri : ri < 4 := by omega
  have hμ : μ = m + minOpenLog := by omega
  have hr : r = ri + 1 := by omega
  obtain ⟨cfg, hF, -, -⟩ := candB_sound (candB_all m ri (by simpa [osArms] using hm) hri)
  have hA := os_arm_facts m hm ri hri
  obtain ⟨fn, hfind, hp, hb, hloop⟩ := hA.fn
  rw [← hμ] at hfind hloop
  have hK : OsCfgOk (osCfgR m ri) ri :=
    { names := hA.names, shapes := os_kid_shapes m hm ri hri, sizes := hA.sizes, pos := hA.pos,
      tot := hA.tot, posOff := os_posOff m hm ri hri, poN := os_posCap m hm ri hri,
      addrs := hA.allocs, disp := hA.disp,
      rateD := by rw [osBodyAc_rate]; exact hdr m hm,
      per := os_perSq_pos m hm ri hri, qs := os_queries_le_sq m hm ri hri,
      cd := os_capDepth_le m hm ri hri, il := os_rowLo_fit m hm ri hri,
      qend := os_posEnd m hm ri hri, lp := hA.lp, lq := fun l hl ↦ ⟨_, hA.lq l hl⟩, lr := hA.lr }
  have hnamed : ∀ f ∈ osCalleeNames (osCfgR m ri), ∀ K, osKindOf f = some K →
      ∀ (args rets : List E) (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)) := by
    intro f hf K hK args rets L' hreg hpre
    cases Bd with
    | none => exact ((osCalleesRegD_holds κ).kindD hK args rets L' hreg hpre).toO
    | some Bk =>
      have hT := hkB m hm f (by rwa [osCalleeNames_rate] at hf) Bk rfl
      exact ((kindDB (Bnd := Bk) hT hK args rets L' hreg hpre).toCompleteAtB).toO
  have hB : ∀ f ∈ osCalleeNames (osCfgR m ri), BoundsAt fs f (Bd.map (· f)) := fun f hf B hB ↦ by
    obtain ⟨Bk, hBk, rfl⟩ := Option.mem_map.mp hB
    exact hkB m hm f (by rwa [osCalleeNames_rate] at hf) Bk hBk
  have hlpE := level_positions_completeAt fs cert κ hrf hcons hκ
  have hF' : CandFacts (osCfgR m ri) μ r cfg := by rw [hμ, hr]; exact hF
  have h := os_arm_completeAtO (Bd := Bd) hF' hK hfind hp (by rw [hb, osBody_rate]) hloop hnamed hB
    (osLpDfp hlpE) (osLpDfp_spec hlpE hA.lpNodup)
    (fun e he Bd' ↦ level_queries_completeAt fs cert κ hrf hcons hκ e he Bd')
    (fun e he Bd' ↦ level_residual_completeAt fs cert κ hrf hcons hκ e he Bd')
    (fun tr σ0 c0 c2 b0 hl ↦ hvals m hm ri hri tr σ0 c0 c2 b0 hl) hrun hnz
    (fun tr hfit hrunT ↦ os_helper_facts m hm ri hri cfg hF S root target xs os w s' roots'
      (by rw [← hμ, ← hr]; exact hrun) (by rw [← hμ, ← hr]; exact hnz)
      (by rw [← hμ, ← hr]; exact hcaps) tr hfit (by rw [← hμ, ← hr]; exact hrunT)) hLin
  have e : (Bd.map fun Bk ↦ osBos fs Bk (openName μ) (osCfgR m ri)) =
      Bd.map fun Bk ↦ osBosAt fs Bk μ := by
    cases Bd <;> simp [osBosAt, osBos_rate, m]
  rw [e] at h
  exact h

/-- **`open_stacked` is complete placed at every stack log and rate**, given the values. -/
theorem open_stacked_completeAtD_of (hvals : os_call_vals_Spec) (hdr : OsDispRate) :
    open_stacked_completeAtD_Spec := by
  intro μ r hμ1 hμ2 hr1 hr4 fs cert κ hrf hcons hκ S root target cur xs os w s' roots' hrun hnz hcaps
    Lin hLin
  exact (open_stacked_completeAtO_of (Bd := none) hvals hdr hμ1 hμ2 hr1 hr4 hrf hcons hκ
    (fun _ _ _ _ _ h ↦ absurd h (by simp)) hrun hnz hcaps hLin).toD

/-- **`open_stacked` is complete placed within `osBosAt` words**, given the values. -/
theorem open_stacked_completeAtB_of (hvals : os_call_vals_Spec) (hdr : OsDispRate) :
    open_stacked_completeAtB_Spec := by
  intro μ r hμ1 hμ2 hr1 hr4 fs cert κ Bnd hrf hcons hκ hleaf S root target cur xs os w s' roots'
    hrun hnz hcaps Lin hLin
  exact (open_stacked_completeAtO_of (Bd := some Bnd) hvals hdr hμ1 hμ2 hr1 hr4 hrf hcons hκ
    (fun m hm f hf Bk hBk ↦ by cases hBk; exact hleaf m hm f hf) hrun hnz hcaps hLin).toB

end
end LeanVM.Guest.B1
