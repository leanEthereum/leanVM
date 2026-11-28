/-
  LeanVM.Guest.Memory.GuestWordsNode

  The guest's families with hand functions at a node's constants: their facts about `main`,
  `da_verify` and the children's loop, by the kernel (`wh_nodeIdx`, `wz_nodeIdx`), and `main`'s tree
  within its inner bound plus the node's constants in each (`wh_mainCost_le`, `wz_mainCost_le`).
-/

module

public import LeanVM.Guest.Memory.GuestWordsH
public import LeanVM.Guest.Memory.HandNode

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- `NodeIdx.callers` from a check over the indices. -/
theorem callers_of {jm jd jl : ℕ} (h : (List.range coreProgram.length).all (fun j =>
    j == jm || j == jl || (!(Data.calleesJ j).contains jd && !(Data.calleesJ j).contains jl)) = true) :
    ∀ j < coreProgram.length, j ≠ jm → j ≠ jl → jd ∉ Data.calleesJ j ∧ jl ∉ Data.calleesJ j := by
  intro j hj hm hl
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simpa [hm, hl] using this

/-- **The facts about `main`, `da_verify` and the loop, the zero-challenge sum counted**, by the kernel. -/
theorem wh_nodeIdx : NodeIdx Data.whcertJ Data.whhandJ Data.whloopJ Data.whabsJ Data.whidxMain Data.whidxDa
    Data.whidxLoop where
  hm := by rw [coreProgram_length]; decide
  hl := by rw [coreProgram_length]; decide
  nm := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  nd := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  nl := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  callers := callers_of (by rw [coreProgram_length]; decide +kernel)
  loopd := by decide +kernel
  certd := rfl
  certl := rfl
  handd := by decide +kernel
  handm := by decide +kernel
  lhl := by decide +kernel
  absm := by decide +kernel
  lhm := rfl
  absl := by decide +kernel
  topm := by decide +kernel
  sitesd := by decide +kernel
  sitesl := by decide +kernel

/-- **The facts about `main`, `da_verify` and the loop, the zero-challenge sum absent**, by the kernel. -/
theorem wz_nodeIdx : NodeIdx Data.wzcertJ Data.wzhandJ Data.wzloopJ Data.wzabsJ Data.wzidxMain Data.wzidxDa
    Data.wzidxLoop where
  hm := by rw [coreProgram_length]; decide
  hl := by rw [coreProgram_length]; decide
  nm := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  nd := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  nl := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  callers := callers_of (by rw [coreProgram_length]; decide +kernel)
  loopd := by decide +kernel
  certd := rfl
  certl := rfl
  handd := by decide +kernel
  handm := by decide +kernel
  lhl := by decide +kernel
  absm := by decide +kernel
  lhm := rfl
  absl := by decide +kernel
  topm := by decide +kernel
  sitesd := by decide +kernel
  sitesl := by decide +kernel

/-- The loop's frame weight. -/
theorem fsPad_loop : fsPad fsW alW "__loop4_main" = 62 := by
  have h := waomega_eq Data.whidxLoop wh_nodeIdx.hl
  have hn : (coreProgram[Data.whidxLoop]'wh_nodeIdx.hl).name = "__loop4_main" := by
    have := wh_nodeIdx.nl; rw [List.getElem?_eq_getElem wh_nodeIdx.hl] at this; exact Option.some.inj this
  rw [hn] at h
  rw [h]
  decide +kernel

/-- The certificates at the node's constants `C₁` (`da_verify`), `C₂` (the loop), the sum counted. -/
noncomputable def whCertAt (C₁ C₂ : ℕ) (g : String) : Cert :=
  certAt Data.whcertJ Data.whidxDa Data.whidxLoop C₁ C₂ (coreIdx g)
/-- The hands with `main`'s raised by `C₁ + C₂`, the sum counted. -/
noncomputable def whHandAt (C₁ C₂ : ℕ) (g : String) : Option Hand :=
  handAt Data.whhandJ Data.whidxMain (C₁ + C₂) (coreIdx g)
/-- The certificates at the node's constants, the sum absent. -/
noncomputable def wzCertAt (C₁ C₂ : ℕ) (g : String) : Cert :=
  certAt Data.wzcertJ Data.wzidxDa Data.wzidxLoop C₁ C₂ (coreIdx g)
/-- The hands with `main`'s raised, the sum absent. -/
noncomputable def wzHandAt (C₁ C₂ : ℕ) (g : String) : Option Hand :=
  handAt Data.wzhandJ Data.wzidxMain (C₁ + C₂) (coreIdx g)

/-- **The check with hand functions at the node's constants**, the sum counted. -/
theorem wh_checkedH_at (C₁ C₂ : ℕ) :
    CheckedH coreProgram true (whCertAt C₁ C₂) (fsPad fsW alW) (whHandAt C₁ C₂) whOut :=
  checkedH_at wh_all waomega_eq wh_nodeIdx C₁ C₂

/-- **The check with hand functions at the node's constants**, the sum absent. -/
theorem wz_checkedH_at (C₁ C₂ : ℕ) :
    CheckedH coreProgram true (wzCertAt C₁ C₂) (fsPad fsW alW) (wzHandAt C₁ C₂) wzOut :=
  checkedH_at wz_all waomega_eq wz_nodeIdx C₁ C₂

variable {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Tree} {args rets : List E}

/-- **`main`'s tree within its inner bound plus the node's constants**, the zero-challenge sum counted:
every node of its callees but the children's loop with its hand fact at the constants, and the loop's
run within `C₂`. -/
theorem wh_mainCost_le (C₁ C₂ : ℕ)
    (hv : (Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨
      k.Every (HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.whidxLoop]'wh_nodeIdx.hl).params Data.whloopHand 62
        (fun k => k.Every (HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut)) k S ∧ S ≤ C₂)
    (hpre : ArgsPre Data.whmainHand.pre (args ++ Data.whmainHand.vps.map σ)) :
    (Tree.node "main" σ bufs kids).cost coreProgram true (fsPad fsW alW) ≤
      Data.whmainHand.b.eval (args ++ Data.whmainHand.vps.map σ) + (C₁ + C₂) :=
  mainCost_le wh_all waomega_eq wh_nodeIdx C₁ C₂ (h := Data.whmainHand) rfl
    (hl := Data.whloopHand) (endc := none) rfl hv hb hkids (by rw [fsPad_loop]; exact hloop) hpre

/-- **`main`'s tree within its inner bound plus the node's constants**, the zero-challenge sum absent:
no node is a `level_residual_sum__*` (`wzOut` in every hand fact). -/
theorem wz_mainCost_le (C₁ C₂ : ℕ)
    (hv : (Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨
      k.Every (HandFact coreProgram (wzCertAt C₁ C₂) (wzHandAt C₁ C₂) wzOut))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.wzidxLoop]'wz_nodeIdx.hl).params Data.wzloopHand 62
        (fun k => k.Every (HandFact coreProgram (wzCertAt C₁ C₂) (wzHandAt C₁ C₂) wzOut)) k S ∧ S ≤ C₂)
    (hpre : ArgsPre Data.wzmainHand.pre (args ++ Data.wzmainHand.vps.map σ)) :
    (Tree.node "main" σ bufs kids).cost coreProgram true (fsPad fsW alW) ≤
      Data.wzmainHand.b.eval (args ++ Data.wzmainHand.vps.map σ) + (C₁ + C₂) :=
  mainCost_le wz_all waomega_eq wz_nodeIdx C₁ C₂ (h := Data.wzmainHand) rfl
    (hl := Data.wzloopHand) (endc := none) rfl hv hb hkids (by rw [fsPad_loop]; exact hloop) hpre

end
end LeanVM.Guest.Memory
