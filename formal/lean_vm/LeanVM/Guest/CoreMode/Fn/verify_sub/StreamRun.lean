/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.StreamRun

  A run of `verify_sub`'s body (`B1.VerifySub.VsRun`) at every honest instance of b2c's aligned tree, under the call
  relation of valid trees, which unfolds at a frame map chosen from them.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.CoreMode.Fn.column_selector.CsChain
public import LeanVM.Guest.B1.VerifySub.Phases

/-!
# `verify_sub`'s run at an honest instance

`treeRel P rd`: a call holds when a valid tree of the callee on its words exists; `treeV P rd`, a frame map choosing
one such tree's valuation. `treeRel_unfolds`: the relation unfolds at it (`Res.holds_of_valid`), and lies below
`P.Rel` (`Tree.Valid.rel`). `vsRun_honest`: at an honest instance of `verify_sub`, its body is a `VsRun` on the
reference memory under them, the exponent tables at `g_squares` carried (`carryQ_allA`), so the B1 phases
(`phLink`, `phKeccak`, ...) apply there.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Calls as valid trees**, of any size. -/
def treeRel (P : Core.Program) (rd : Reader) : CallRel :=
  fun g args rets ↦ ∃ t : Tree, t.Valid P rd args rets ∧ t.name = g

open Classical in
/-- **A frame map of valid trees**: the valuation of a chosen valid tree of the call, if any. -/
noncomputable def treeV (P : Core.Program) (rd : Reader) : B1.FrameMap :=
  fun g args rets ↦ if h : treeRel P rd g args rets then (Classical.choose h).val else fun _ ↦ 0

end

public section

theorem kidRel_le_tree {P : Core.Program} {rd : Reader} {fs : String → ℕ} {T : ℕ} :
    CallRel.Le (Res.KidRel P rd fs T) (treeRel P rd) :=
  fun _ _ _ ⟨t, hv, hn, _⟩ ↦ ⟨t, hv, hn⟩

theorem treeRel_le {P : Core.Program} {rd : Reader} : CallRel.Le (treeRel P rd) (P.Rel rd) := by
  rintro _ _ _ ⟨t, hv, rfl⟩
  exact Tree.Valid.rel t hv

/-- **Valid trees unfold** at their chosen valuations. -/
theorem treeRel_unfolds (P : Core.Program) (rd : Reader) : B1.UnfoldsVP P rd (treeRel P rd) (treeV P rd) := by
  intro g args rets h
  have hV : treeV P rd g args rets = (Classical.choose h).val := by simp only [treeV, h, ↓reduceDIte]
  obtain ⟨hv, hn⟩ := Classical.choose_spec h
  rw [hV]
  generalize Classical.choose h = t at hv hn
  cases t with
  | phantom f σ => exact hv.elim
  | node f σ bufs kids =>
    obtain ⟨fn, hf, -⟩ := id hv
    obtain ⟨hp, hb⟩ := Res.holds_of_valid (fs := fun _ ↦ 1) (fun _ ↦ le_rfl) hv hf
    simp only [Tree.name] at hn
    subst hn
    exact ⟨fn, hf, hp, holdsList_mono kidRel_le_tree _ id (fun _ h ↦ h) hb⟩

/-- The stacked program `VsRun` takes: any of its length. -/
noncomputable def vsBytecode0 : List K := List.replicate (2 ^ (B1.Main.bytecodeLog + Protocol.Verifier.bytecodeSlotBits)) 0

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **`verify_sub`'s run at an honest instance**: its body under the valid trees' relation on the reference memory,
the exponent tables at `g_squares`. -/
theorem vsRun_honest (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_sub» σ bufs kids) :
    ∃ rets, B1.VerifySub.VsRun vsBytecode0 r.img (treeRel coreProgram r.img.read) (treeV coreProgram r.img.read)
      σ rets := by
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  have hc := carryQ_allA hR I hI _ σ bufs kids ht (fn% «verify_sub») find_vs (name% «verify_sub», 4, .tab)
    (by decide) rfl (.n 4) rfl
  refine ⟨rets, ⟨by simp [vsBytecode0], by have := hr.log; omega, treeRel_unfolds _ _, treeRel_le,
    holdsList_mono kidRel_le_tree _ id (fun _ h ↦ h) hb, ?_⟩⟩
  rw [show (fn% «verify_sub»).params.map σ = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
    σ (.n 5)] from rfl]
  exact hc

end

end LeanVM.Guest.EndExec
