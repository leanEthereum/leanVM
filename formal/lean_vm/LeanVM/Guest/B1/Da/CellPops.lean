/-
  LeanVM.Guest.B1.Da.CellPops

  A cell check pops its symbols (`da_symbols`), and a callee with no witness hint in its subtree pops nothing.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.B1.Common.NoWitMute
public import LeanVM.Guest.B1.Da.CellComplete
public import LeanVM.Guest.Hints
public import LeanVM.Guest.Memory.Uniform
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_cell»
import LeanVM.Guest.StmtsAppend

/-!
# A cell check's pops

* `kid_pops_mute`: a callee with no witness hint in its subtree pops nothing;
* `cell_pops`: a cell check pops the symbols its valuation holds.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Digest

@[expose] public section

theorem mkCall_f (σ : Val) (o : Option V) (f : String) (args rets : List V) : (Main.mkCall σ (o, f, args, rets)).f = f := by
  cases o <;> rfl

/-- A callee with no witness hint in its subtree pops nothing. -/
theorem kid_pops_mute {rd : Reader} {σ : Val} {c : Call} {k : Memory.Tree}
    (hk : if c.taken then k.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
      else (∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k (c.args.map σ))
    (hn : k.name = c.f) (hs : noWitS c.f = true) : k.pops coreProgram rd = [] := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at hk
    exact Tree.pops_mute noWitS_mute k hk (by rw [hn]; exact hs)
  · rw [ite_eq_right ht] at hk
    obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
    rw [Tree.pops]

theorem splicePops_nil (rd : Reader) (σ : Val) : SplicePops rd σ [] [] [] := ⟨[], rfl, rfl, rfl⟩

/-! ## The cell check -/

/-- The symbols' hint. -/
def symHint : Atom := .hint (.witness "da_symbols" (.stack ((List.range 128).map fun j => V.n (j + (val% «da_verify_cell» "sym[0]")))))

/-- `da_verify_cell` pops its symbols first, then nothing, calling nothing. -/
noncomputable def cellShapeOk : Bool :=
  stmtsEqb ((Fn.body fn% «da_verify_cell»).take (pos% «da_verify_cell» "s@1~0")) [.atom symHint] &&
    Stmt.muteList (fun _ => false) ((Fn.body fn% «da_verify_cell»).drop (pos% «da_verify_cell» "s@1~0"))

theorem cell_shape_ok : cellShapeOk = true := by decide +kernel

/-- The entry of the cell check's hint on `σ`. -/
def cellPop (σ : Val) : Pop := ("da_symbols", (List.range 128).map fun j => σ (.n (j + 1)))

/-- **A cell check pops the symbols its valuation holds.** -/
theorem cell_pops {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}
    (hv : (Memory.Tree.node "da_verify_cell" σ bufs kids).Valid coreProgram rd args rets) :
    (Memory.Tree.node "da_verify_cell" σ bufs kids).pops coreProgram rd = [cellPop σ] := by
  have h := cell_shape_ok
  simp only [cellShapeOk, Bool.and_eq_true] at h
  have hb : Fn.body fn% «da_verify_cell» = [.atom symHint] ⧺ (Fn.body fn% «da_verify_cell»).drop (pos% «da_verify_cell» "s@1~0") := by
    rw [← stmtsEqb_sound h.1, List.take_append_drop]
  have ha : symHint.pops rd σ = [cellPop σ] := by simp [symHint, Atom.pops, Hint.pops, Dest.words, cellPop]
  have hx := FallPops.atom (rd := rd) (σ := σ) symHint
  rw [ha] at hx
  exact Tree.pops_of_prefix_leaf hv find_da_verify_cell hb hx h.2

end
end LeanVM.Guest.B1.Da
