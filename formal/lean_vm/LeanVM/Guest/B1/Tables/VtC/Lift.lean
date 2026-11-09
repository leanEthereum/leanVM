/-
  LeanVM.Guest.B1.Tables.VtC.Lift

  `verify_tables`, placed: from its honest valuation on every memory holding its layout, the
  uniform placed form (`CompleteAtD`).
-/

module

public import LeanVM.Guest.B1.Tables.FlatLift
public import LeanVM.Guest.B1.Tables.VtC.RcReads
public import LeanVM.Guest.B1.Tables.VtC.Kids
public import LeanVM.Guest.B1.Tables.VtC.Hon

/-!
# `verify_tables`, placed

`vtFlat`: `verify_tables`' kernel facts as a flat function (`FlatFn`): its evaluation list
`vtEvL`, its range checks' reads `vtAux`, its callees `vtKidS`. `vt_completeAt`: `flat_completeAt`
for it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Kernel facts of the body -/

theorem vt_flat : vtPre.all Stmt.flat = true := by decide +kernel

theorem vt_addrs : vtPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem vt_not_loop : coreProgram.loop "verify_tables" = false := by decide +kernel

theorem vt_callOk : vtPre.all (callOk vtKidS) = true := by decide +kernel

theorem vt_noLoadIte : vtPre.all noLoadIte = true := by decide +kernel

/-- A load of the evaluation list is a statement of the body. -/
theorem vtEvL_load_mem {d p : V} {off : ℕ} (h : Stmt.atom (.load d p off) ∈ vtEvL) :
    Stmt.atom (.load d p off) ∈ vtPre := by
  obtain ⟨s, hs, hfs⟩ := List.mem_map.mp h
  have hs' : s = .atom (.load d p off) := by
    cases s with
    | atom a => cases a <;> simp_all [fixNe]
    | _ => simp_all [fixNe]
  subst hs'
  have key : ∀ ss : List Stmt, ss.all noLoadIte = true →
      Stmt.atom (.load d p off) ∈ flatIte ss → Stmt.atom (.load d p off) ∈ ss := by
    intro ss
    induction ss with
    | nil => simp [flatIte]
    | cons t ts ih =>
      intro hok hm
      simp only [List.all_cons, Bool.and_eq_true] at hok
      cases t with
      | ite c z n =>
        simp only [flatIte, List.mem_append] at hm
        rcases hm with (hm | hm) | hm
        · have := List.all_eq_true.mp hok.1 _ (List.mem_append_left _ hm)
          simp at this
        · have := List.all_eq_true.mp hok.1 _ (List.mem_append_right _ hm)
          simp at this
        · exact List.mem_cons_of_mem _ (ih hok.2 hm)
      | _ =>
        simp only [flatIte, List.mem_cons] at hm
        rcases hm with hm | hm
        · rw [hm]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hok.2 hm)
  exact key vtPre vt_noLoadIte hs

/-- **`verify_tables` as a flat function.** -/
noncomputable def vtFlat : FlatFn where
  name := "verify_tables"
  fn := vtFound.choose
  k := 20
  pre := vtPre
  rets := vtRets
  evL := vtEvL
  aux := vtAux
  kids := vtKidS
  hf := vtFound.choose_spec.1
  hloop := vt_not_loop
  hp := vtFound.choose_spec.2.1
  hb := vtFound.choose_spec.2.2
  hevL := rfl
  hchk := ⟨_, vt_chk⟩
  hdead := vt_dead
  haux := vt_aux
  hflat := vt_flat
  haddrs := vt_addrs
  hiteOk := vt_iteOk
  hcall := vt_callOk
  hpure := vt_kids_pure

/-- The layout of the caller's words and `verify_tables`' buffers at `fp`. -/
abbrev vtL (Lin : Layout) (sizes : List ℕ) (own : ℕ → List (List E)) (fs : String → ℕ) (fp : ℕ) :
    Layout :=
  flatL "verify_tables" Lin sizes own fs fp

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_tables` is complete, placed**, from its honest valuation on every memory holding its
layout and its calls by relations loading from that layout. -/
theorem vt_completeAt {κ : ℕ} (Lin : Layout) (args rets : List E) (hl : args.length = 20)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (w : ℕ → ℕ → E) (bufs : ℕ → List (E × ℕ))
    (hbufs : ∀ fp, ∀ q ∈ bufs fp, ∃ b, q.1 = ofK (addressOfIndex b) ∧
      ∀ i < q.2, RegionL (vtL Lin sizes own fs fp) (b + i))
    (hrun : ∀ fp rd, LowDef κ rd → MemL rd (vtL Lin sizes own fs fp) →
      (∀ s ∈ vtPre, VSH (coreProgram.RelIn rd (RegionL (vtL Lin sizes own fs fp))) rd
        (vtσ rd (w fp) args) s) ∧
      LoadsInBuf (vtσ rd (w fp) args) (bufs fp) vtPre ∧
      (vtPre.filterMap Main.Stmt.allocSz).map
        (fun x => x.2.elim id fun s => logG (vtσ rd (w fp) args s)) = sizes ∧
      ((vtPre.filterMap Main.Stmt.allocSz).map Prod.fst).map (vtσ rd (w fp) args) =
        (bases (fp + fs "verify_tables") sizes).map (fun b => ofK (addressOfIndex b)) ∧
      vtRets.map (vtσ rd (w fp) args) = rets) :
    CompleteAtD fs cert κ "verify_tables" Lin args (Returns rets) :=
  flat_completeAt vtFlat Lin args rets hl sizes own hown w bufs hbufs fun fp rd hlow hL ↦
    let h := hrun fp rd hlow hL
    ⟨h.1, fun d p off hm ↦ h.2.1 d p off (vtEvL_load_mem hm), h.2.2⟩

end
end LeanVM.Guest.B1.Tables
