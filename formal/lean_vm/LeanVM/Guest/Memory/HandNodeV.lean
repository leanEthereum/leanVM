/-
  LeanVM.Guest.Memory.HandNodeV

  `main`'s weight from a vector family with hand functions, coordinate by coordinate: the family's
  facts about `main`, `da_verify` and the children's loop (`NodeIdxV`) give `HandNode`'s at each
  coordinate (`NodeIdxV.proj`), and `main`'s tree weighs at most its inner bound's coordinate plus
  the node's constants (`mainWeight_le`).
-/

module

public import LeanVM.Guest.Memory.FamilyHandV
public import LeanVM.Guest.Memory.HandNode

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The zero bound of `da_verify` and the children's loop in a vector family of six coordinates. -/
abbrev zeroV : Vec := [0, 0, 0, 0, 0, 0]

theorem zeroV_getD (i : ℕ) : zeroV.getD i 0 = 0 := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [zeroV]

/-- **`NodeIdx` of a vector family**: its facts about `main` (`jm`), `da_verify` (`jd`) and the loop
(`jl`), by the kernel. -/
structure NodeIdxV (cert : ℕ → CertV) (hand : ℕ → Option HandV) (lh : ℕ → Option (HandV × Option ℕ))
    (abs : ℕ → Bool) (jm jd jl : ℕ) : Prop where
  hm : jm < coreProgram.length
  hl : jl < coreProgram.length
  nm : (coreProgram[jm]?).map Fn.name = some "main"
  nd : (coreProgram[jd]?).map Fn.name = some "da_verify"
  nl : (coreProgram[jl]?).map Fn.name = some "__loop4_main"
  callers : ∀ j < coreProgram.length, j ≠ jm → j ≠ jl → jd ∉ Data.calleesJ j ∧ jl ∉ Data.calleesJ j
  loopd : jd ∉ Data.calleesJ jl
  certd : cert jd = .stat [] ⟨zeroV, []⟩ []
  certl : cert jl = .stat [] ⟨zeroV, []⟩ []
  handd : (hand jd).isSome = true
  handm : (hand jm).isSome = true
  lhl : (lh jl).isSome = true
  absm : abs jm = false
  lhm : lh jm = none
  absl : abs jl = false
  topm : topSel (coreProgram[jm]'hm).body = none
  sitesd : sitesL (nodeδ 1 0) (coreProgram[jm]'hm).body = 1
  sitesl : sitesL (nodeδ 0 1) (coreProgram[jm]'hm).body = 1

/-- `NodeIdxV.callers` from a check over the indices. -/
theorem callers_ofV {jm jd jl : ℕ} (h : (List.range coreProgram.length).all (fun j =>
    j == jm || j == jl || (!(Data.calleesJ j).contains jd && !(Data.calleesJ j).contains jl)) = true) :
    ∀ j < coreProgram.length, j ≠ jm → j ≠ jl → jd ∉ Data.calleesJ j ∧ jl ∉ Data.calleesJ j := by
  intro j hj hm hl
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simpa [hm, hl] using this

variable {cert : ℕ → CertV} {hand : ℕ → Option HandV} {lh : ℕ → Option (HandV × Option ℕ)}
  {abs : ℕ → Bool} {om : ℕ → Vec} {jm jd jl : ℕ}

theorem certP_zero {j : ℕ} (h : cert j = .stat [] ⟨zeroV, []⟩ []) (i : ℕ) :
    certP cert i j = .stat [] ⟨0, []⟩ [] := by
  simp only [certP, h, CertV.proj, AffV.proj, zeroV_getD, List.map_nil]

/-- **Coordinate `i` of a vector family's node facts.** -/
theorem NodeIdxV.proj (hI : NodeIdxV cert hand lh abs jm jd jl) (i : ℕ) :
    NodeIdx (certP cert i) (handP hand i) (lhP lh i) abs jm jd jl where
  hm := hI.hm
  hl := hI.hl
  nm := hI.nm
  nd := hI.nd
  nl := hI.nl
  callers := hI.callers
  loopd := hI.loopd
  certd := certP_zero hI.certd i
  certl := certP_zero hI.certl i
  handd := by simp only [handP, Option.isSome_map, hI.handd]
  handm := by simp only [handP, Option.isSome_map, hI.handm]
  lhl := by simp only [lhP, Option.isSome_map, hI.lhl]
  absm := hI.absm
  lhm := by simp only [lhP, hI.lhm, Option.map_none]
  absl := hI.absl
  topm := hI.topm
  sitesd := hI.sitesd
  sitesl := hI.sitesl

/-- **`main`'s tree weighs at most coordinate `i` of its inner bound plus the node's constants**:
every node of its callees but the loop with its hand fact at coordinate `i`, and the loop's run within
`C₂`. -/
theorem mainWeight_le (hr : RangeOk (chkHJV cert hand lh abs om) 0 coreProgram.length) (i : ℕ)
    {ω : String → ℕ} (hω : ∀ j (hj : j < coreProgram.length), ω coreProgram[j].name = omP om i j)
    (hI : NodeIdxV cert hand lh abs jm jd jl) (C₁ C₂ : ℕ) {h : HandV} (hh : hand jm = some h) {hl : HandV}
    {endc : Option ℕ} (hlj : lh jl = some (hl, endc)) {rd : Reader} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {args rets : List E}
    (hv : (Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨
      k.Every (HandFact coreProgram (fun g => certAt (certP cert i) jd jl C₁ C₂ (coreIdx g))
        (fun g => handAt (handP hand i) jm (C₁ + C₂) (coreIdx g))
        (fun g => abs (coreIdx g) = true ∨ (lhP lh i (coreIdx g)).isSome = true)))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[jl]'hI.hl).params (hl.proj i) (ω "__loop4_main")
        (fun k => k.Every (HandFact coreProgram (fun g => certAt (certP cert i) jd jl C₁ C₂ (coreIdx g))
          (fun g => handAt (handP hand i) jm (C₁ + C₂) (coreIdx g))
          (fun g => abs (coreIdx g) = true ∨ (lhP lh i (coreIdx g)).isSome = true))) k S ∧ S ≤ C₂)
    (hpre : ArgsPre (h.proj i).pre (args ++ (h.proj i).vps.map σ)) :
    (Tree.node "main" σ bufs kids).weight ω ≤ (h.proj i).b.eval (args ++ (h.proj i).vps.map σ) + (C₁ + C₂) := by
  have := mainCost_le (rangeOk_proj i hr) hω (hI.proj i) C₁ C₂ (h := h.proj i)
    (by simp only [handP, hh, Option.map_some]) (hl := hl.proj i) (endc := endc)
    (by simp only [lhP, hlj, Option.map_some]) hv hb hkids hloop hpre
  rwa [cost_false] at this

end
end LeanVM.Guest.Memory
