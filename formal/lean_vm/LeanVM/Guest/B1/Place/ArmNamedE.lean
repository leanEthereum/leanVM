/-
  LeanVM.Guest.B1.Place.ArmNamedE

  An arm of `open_stacked`'s named callees within the bounds of their trees, by trees satisfying `armXT`.
-/

module

public import LeanVM.Guest.B1.Place.ArmXT
public import LeanVM.Guest.B1.Place.OsRoundE
public import LeanVM.Guest.B1.Place.OsMeanB

/-!
# The named callees, exact

`round_total_ge`: a valid tree of `opening_round` takes at least its frame and `grind_check__L7`'s.
`osRound_completeDTBRE_of`: `osRound_completeDTBRE` within any bound of `opening_round`'s valid trees. `kindDBE`:
`kindDB` by trees satisfying `armXT`: `opening_round`'s and the grind checks' exact at every node, the others' for
free (`armExactS_kind`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **A valid tree of `opening_round` takes at least its frame and `grind_check__L7`'s.** -/
theorem round_total_ge {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = "opening_round")
    (hv : t.Valid coreProgram rd args rets) : fs "opening_round" + fs "grind_check__L7" ≤ t.total fs := by
  cases t with
  | phantom => exact hv.elim
  | node g σ bufs kids =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hv
    rw [Whir.find_opening_round, Option.some.injEq] at hf
    subst hf
    rw [Whir.opening_round_body, roundBody_eq, walk_flat σ _ roundPre roundPre_flat (roundPre_disp σ),
      Out.ret.injEq] at hw
    obtain ⟨rfl, -⟩ := hw
    rw [(flat_parts σ roundPre roundPre_flat).2.2.2.1, roundPre_calls] at hkv
    match kids, hkv with
    | [k], ⟨hkn, _, _⟩ =>
      have h1 := le_total (fs := fs) k
      rw [hkn] at h1
      rw [total_node]
      simp only [Tree.totalKids] at *
      exact Nat.le_trans (Nat.add_le_add_left h1 _) (by omega)

/-- **`osRound_completeDTBRE` within any bound of `opening_round`'s valid trees.** -/
theorem osRound_completeDTBRE_of (hκ : 11 ≤ κ) {B : ℕ}
    (hT : TotalLe coreProgram fs "opening_round" fun _ ↦ B) {args rets : List E} {Lin : Layout}
    (hreg : RegPtrs roundSpec args (RegionL Lin))
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin →
      Whir.MeaningOpeningRound rd args rets ∧ WinTabs rd (args.getD 7 0)) :
    CompleteAtDTBR fs cert κ "opening_round" Lin args (Returns rets)
      (fun rd t => osRoundHonest rd t ∧ t.Every (ExactAt coreProgram rd)) B := by
  classical
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  · obtain ⟨rd0, hl0, hL0⟩ := hex
    obtain ⟨t, hn, hv, hb, -⟩ := round_relIn hκ hreg hpre hl0 hL0
    exact (osRound_completeDTBRE hκ hreg hpre).mono ((round_total_ge hn hv).trans (hT rd0 t args rets hn hv hb))
      fun _ _ h ↦ h
  · intro fp
    exact ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL ↦ absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- **A named callee is complete placed on its meaning and regions, within its bound, by a tree satisfying
`armXT`.** -/
theorem kindDBE (hκ : 11 ≤ κ) {B : ℕ} {f : String} (hb : TotalLe coreProgram fs f (fun _ ↦ B))
    {K : OsKind} (hK : osKindOf f = some K) (args rets : List E) (Lin : Layout)
    (hreg : RegPtrs K.spec args (RegionL Lin)) (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → K.Pre rd args rets) :
    CompleteAtDTBR fs cert κ f Lin args (Returns rets) Arm.armXT B := by
  cases hx : K.exactS
  · exact (kindDB (cert := cert) hκ hb hK args rets Lin hreg hpre).toR.monoN le_rfl
      fun _ _ hn _ ↦ Arm.armXT_of_not (by rw [hn]; exact Arm.armExactS_kind hK hx)
  · have he := osKindEntry_ok hK
    cases K with
    | round =>
      simp only [osKindEntryOk, beq_iff_eq] at he
      subst he
      exact (osRound_completeDTBRE_of hκ hb hreg hpre).mono le_rfl fun _ _ h _ ↦ h.2
    | grind b =>
      simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
      obtain ⟨hm, rfl⟩ := he
      exact (grind_check_completeDTBR_of hm hκ hb hpre).mono le_rfl fun _ _ h _ ↦ h.2
    | _ => simp [OsKind.exactS] at hx

end
end LeanVM.Guest.B1
