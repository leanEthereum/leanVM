module

public import LeanVM.Guest.Complete.CallCompleteA
public import LeanVM.Guest.Complete.Call0

/-!
# Layout-free completeness placed, for callees with no words of their own

A callee whose subtree allocates no `HeapBuf` and takes no `frameAddr` (`Program.PureIn`) is placed
anywhere (`placedA_of_pure`). Proved with no words of its own (`CallCompletes0`), with its loads and
heap hints in the region its caller hands it (`Tree.LoadsR`, `Tree.HintsR`) and its block and end
fixed by its shape, it completes at every position (`callAtA_of_callCompletes0`). A leaf (no calls,
not a loop helper) has block `fs f` and ends at its cursor (`block_endA_leaf`), so it completes
aligned (`callCompletesA_of_callCompletes0_leaf`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Heap hints in a region -/

mutual
/-- Every heap word a hint of the tree writes is in `R`. -/
def Tree.HintsR (P : Core.Program) (R : ℕ → Prop) : Tree → Prop
  | t@(.node _ σ _ kids) => (∀ A ∈ heapHintAddrs σ (t.events P), ∃ i, A = addressOfIndex i ∧ R i) ∧
      Tree.HintsRKids P R kids
  | .phantom .. => True

/-- `Tree.HintsR` of the callees. -/
def Tree.HintsRKids (P : Core.Program) (R : ℕ → Prop) : List Tree → Prop
  | [] => True
  | k :: ks => k.HintsR P R ∧ Tree.HintsRKids P R ks
end

end
end LeanVM.Guest.Memory

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

variable {P : Core.Program} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

mutual
/-- Hints in `R` are hints in `R` and the subtree's data, wherever it is placed. -/
theorem hintsIn_of_hintsR : ∀ (t : Tree) (R : ℕ → Prop) (p : ℕ × ℕ), t.HintsR P R →
    t.HintsIn P fs al cert R p
  | .node f σ bufs kids, R, p, h => by
      rw [Tree.HintsR] at h
      rw [hintsIn_node]
      refine ⟨fun A hA => ?_, hintsInKids_mono kids _ (fun i hi => Or.inr hi)
        (hintsInKids_of_hintsR kids R _ h.2)⟩
      obtain ⟨i, hi, hR⟩ := h.1 A hA
      exact ⟨i, hi, Or.inr hR⟩
  | .phantom .., _, _, _ => hintsIn_phantom

/-- `hintsIn_of_hintsR` for the callees. -/
theorem hintsInKids_of_hintsR : ∀ (ks : List Tree) (R : ℕ → Prop) (ps : List (ℕ × ℕ)),
    Tree.HintsRKids P R ks → Tree.HintsInKids P fs al cert R ps ks
  | [], _, _, _ => hintsInKids_nil
  | _ :: _, _, [], _ => by rw [Tree.HintsInKids]; trivial
  | k :: ks, R, p :: ps, h => by
      rw [Tree.HintsRKids] at h
      rw [hintsInKids_cons]
      exact ⟨hintsIn_of_hintsR k R p h.1, hintsInKids_of_hintsR ks R ps h.2⟩
end

/-! ## The transfer -/

/-- **A pure callee proved with no words of its own completes at any position**, given its block,
end, loads and heap hints on every tree it may have. -/
theorem callAtA_of_callCompletes0 {S : List String} (hS : coreProgram.PureIn S) {k : ℕ} {f : String}
    (hf : f ∈ S) {args rets : List E} {R : ℕ → Prop} {Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    {B fp c e : ℕ} (hce : c ≤ e) (h : CallCompletes0 k f args rets Pre Post)
    (hsh : ∀ rd t, LowDef k rd → Pre rd → t.name = f → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      Post rd t → t.block fs coreProgram.loop = B ∧ t.endA fs coreProgram.loop al c = e ∧
        t.LoadsR coreProgram R ∧ t.HintsR coreProgram R) :
    CallAtA fs al cert k f args rets R (fun _ => False) (fun _ => True) Pre Post B fp c e := by
  refine ⟨[], ⟨by simp, List.Pairwise.nil⟩, hce, fun _ _ => trivial, fun rd hl _ hp => ?_⟩
  obtain ⟨t, hn, hv, hb, hq⟩ := h rd hl hp
  obtain ⟨hB, he, hlo, hhi⟩ := hsh rd t hl hp hn hv hb hq
  exact ⟨t, hn, hv, hb, hB, he, placedA_of_pure hS t hv hb (hn ▸ hf) _, loadsInA_of_loadsR t R _ hlo,
    hintsIn_of_hintsR t R _ hhi, fun _ hi => hi.elim, hq⟩

/-- **A pure leaf's block and end**: no calls and not a loop helper, its block is its frame and its
subtree ends at its cursor. -/
theorem block_endA_leaf {S : List String} (hS : coreProgram.PureIn S) {f : String} (hf : f ∈ S)
    (hlp : coreProgram.loop f = false)
    (hnc : ∀ fn σ es vs, coreProgram.find? f = some fn → walk σ fn.body = .ret es vs → calls es = [])
    {rd : Reader} {args rets : List E} {t : Tree} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (c : ℕ) :
    t.block fs coreProgram.loop = fs f ∧ t.endA fs coreProgram.loop al c = c := by
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn, hfn, _, es, vs, hw, _, _, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    have hpure : ∀ e ∈ es, e.pure S := by
      have := walk_pure (σ := σ) fn.body (hS g hf fn hfn)
      rwa [hw] at this
    rw [Tree.BufsOk, Complete.events_node hfn hw, allocs_pure hpure] at hb
    obtain ⟨rfl, -⟩ := hb
    rw [hnc fn σ es vs hfn hw] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    refine ⟨?_, ?_⟩
    · rw [Tree.block, hlp]; simp
    · rw [endA_node, hlp]; simp [endF_nil]

/-- **A pure leaf proved with no words of its own completes placed** at `(fp, c)`: block `fs f`,
ending at its cursor. -/
theorem callAtA_of_callCompletes0_leaf {S : List String} (hS : coreProgram.PureIn S) {k : ℕ}
    {f : String} (hf : f ∈ S) (hlp : coreProgram.loop f = false)
    (hnc : ∀ fn σ es vs, coreProgram.find? f = some fn → walk σ fn.body = .ret es vs → calls es = [])
    {args rets : List E} {R : ℕ → Prop} {Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    (h : CallCompletes0 k f args rets Pre Post)
    (hR : ∀ rd t, LowDef k rd → Pre rd → t.name = f → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      Post rd t → t.LoadsR coreProgram R ∧ t.HintsR coreProgram R) (fp c : ℕ) :
    CallAtA fs al cert k f args rets R (fun _ => False) (fun _ => True) Pre Post (fs f) fp c c :=
  callAtA_of_callCompletes0 hS hf le_rfl h fun rd t hl hp hn hv hb hq =>
    let hbe := block_endA_leaf (al := al) hS hf hlp hnc hn hv hb c
    ⟨hbe.1, hbe.2, hR rd t hl hp hn hv hb hq⟩

/-- **A pure leaf proved with no words of its own completes aligned**: block `fs f`, ending at its
cursor. -/
theorem callCompletesA_of_callCompletes0_leaf {S : List String} (hS : coreProgram.PureIn S) {k : ℕ}
    {f : String} (hf : f ∈ S) (hlp : coreProgram.loop f = false)
    (hnc : ∀ fn σ es vs, coreProgram.find? f = some fn → walk σ fn.body = .ret es vs → calls es = [])
    {args rets : List E} {R : ℕ → Prop} {Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    (h : CallCompletes0 k f args rets Pre Post)
    (hR : ∀ rd t, LowDef k rd → Pre rd → t.name = f → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      Post rd t → t.LoadsR coreProgram R ∧ t.HintsR coreProgram R) :
    CallCompletesA fs al cert k f args rets R (fun _ _ _ => False) (fun _ => True) Pre Post :=
  ⟨fs f, fun _ c _ => ⟨c, callAtA_of_callCompletes0 hS hf le_rfl h fun rd t hl hp hn hv hb hq =>
    let hbe := block_endA_leaf (al := al) hS hf hlp hnc hn hv hb c
    ⟨hbe.1, hbe.2, hR rd t hl hp hn hv hb hq⟩⟩⟩

end
end LeanVM.Guest.Complete
