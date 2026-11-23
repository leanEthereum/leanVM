/-
  LeanVM.Guest.B1.Place.ArmNamedE

  An arm of `open_stacked`'s named callees within the bounds of their trees, by trees satisfying `armXT`.
-/

module

public import LeanVM.Guest.B1.Place.ArmXT
public import LeanVM.Guest.B1.Place.OsMeanB
public import LeanVM.Guest.B1.Place.IsZeroE

/-!
# The named callees, exact

`kindDBE`: `kindDB` by trees satisfying `armXT`: `is_zero`'s (`isZero_every_exact`) exact at every node, the
others' for free (`armExactS_kind`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **`CompleteAtDTBR.mono` knowing the tree's name and validity.** -/
theorem CompleteAtDTBR.monoNV {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    {T T' : Reader → Tree → Prop} {B : ℕ} (h : CompleteAtDTBR fs cert κ f Lin args Out T B)
    (hT : ∀ rd t rets, t.name = f → t.Valid coreProgram rd args rets → T rd t → T' rd t) :
    CompleteAtDTBR fs cert κ f Lin args Out T' B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT'⟩ := hr rd hl hm
    ⟨t, ht, hT rd t rets ht.1 ht.2.1 hT'⟩⟩

/-- **A named callee is complete placed on its meaning and regions, within its bound, by a tree satisfying
`armXT`.** -/
theorem kindDBE {B : ℕ} {f : String} (hb : TotalLe coreProgram fs f (fun _ ↦ B))
    {K : OsKind} (hK : osKindOf f = some K) (args rets : List E) (Lin : Layout)
    (hreg : RegPtrs K.spec args (RegionL Lin)) (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → K.Pre rd args rets) :
    CompleteAtDTBR fs cert κ f Lin args (Returns rets) Arm.armXT B := by
  cases hx : K.exactS
  · exact (kindDB (cert := cert) hb hK args rets Lin hreg hpre).toR.monoN le_rfl
      fun _ _ hn _ ↦ Arm.armXT_of_not (by rw [hn]; exact Arm.armExactS_kind hK hx)
  · have he := osKindEntry_ok hK
    cases K with
    | iz =>
      simp only [osKindEntryOk, beq_iff_eq] at he
      subst he
      exact (kindDB (cert := cert) hb hK args rets Lin hreg hpre).toR.monoNV
        fun _ _ _ hn hv _ _ ↦ isZero_every_exact hn hv
    | _ => simp [OsKind.exactS] at hx

end
end LeanVM.Guest.B1
