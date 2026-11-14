/-
  LeanVM.Guest.Bridge.WalkPath

  The hint bridge's prototype on `walk_path__L6_L7`: its one witness hint paired with its body's first atom, cell for cell, and its instances' pops that hint's entry.
-/

module

public import LeanVM.Guest.Bridge.Prefix
public import LeanVM.Guest.Pack.«P10».Core
public import LeanVM.Guest.Pack.«P10».Bundle
public import LeanVM.Guest.Data.AdviceHints
public import LeanVM.Guest.Memory.LiftPure

/-!
# The hint bridge on `walk_path__L6_L7`

`walk_path__L6_L7` (a specialization of `walk_path`, compiled function `1599`) pops its Merkle path's `24` children from `merkle_children` before it hashes them. Its ISA hints (`Data.adviceFn1599`): `witnessStack "merkle_children" 7 24` at offset `0` and a `cellAddress` (plumbing) at offset `7`; its first jump is at offset `11`.

* `prefixOk_wp`: it is in the prefix class, under its certificate's cells (`loc`), by the kernel.
* `wp_isaFlow`, `wp_flow`, `wp_cells`: the per-pc pairing: its one ISA flow hint, at offset `0`, compiles its body's first atom, the witness of values `5` to `28`, which sit at cells `7` to `30`.
* `wp_pops`: every instance pops exactly that hint's entry, its values' words.
* `wp_hintOk`: the executor's hint at offset `0` meets `HintOk`, from the stream's next entry being the instance's and the frame holding its values at their cells.
-/

namespace LeanVM.Guest.Bridge.WalkPath

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (Ctx St HintOk StreamNext maxCells)

@[expose] public section

/-- The cells of `walk_path__L6_L7`'s values: its certificate's (`Cert.locs`). -/
noncomputable def loc (i : ℕ) : ℕ := Fn.«walk_path__L6_L7».cert.locs.getD i 0

/-- The children the witness hint pops, values `5` to `28`. -/
def kids : List V := (List.range 24).map fun k ↦ .n (5 + k)

end

public section

/-- **`walk_path__L6_L7` is in the prefix class.** -/
theorem prefixOk_wp : prefixOk loc Fn.«walk_path__L6_L7».core.body Fn.«walk_path__L6_L7».code.code
    Data.adviceFn1599 = true := by
  decide +kernel

/-- Its ISA flow hints: the witness at offset `0`. -/
theorem wp_isaFlow : isaFlow Data.adviceFn1599 = [(0, .witnessStack "merkle_children" 7 24)] := by
  rfl

/-- Its body's leading flow hints: the witness of its children. -/
theorem wp_flow : flowOf (atomPrefix Fn.«walk_path__L6_L7».core.body).1 =
    [.witness "merkle_children" (.stack kids)] := by
  decide +kernel

/-- **The per-pc pairing**: the hint at offset `0` compiles the body's first atom; child `k`,
value `5 + k`, sits at cell `7 + k`. -/
theorem wp_cells : compiles loc (.witness "merkle_children" (.stack kids))
      (.witnessStack "merkle_children" 7 24) = true ∧
    ∀ k < 24, loc (5 + k) = 7 + k := by
  obtain ⟨-, -, -, h⟩ := prefix_pairs prefixOk_wp
  have hc := h 0 (by rw [wp_flow]; decide) (by rw [wp_isaFlow]; decide)
  simp only [wp_flow, wp_isaFlow] at hc
  refine ⟨hc, fun k hk ↦ ?_⟩
  obtain ⟨-, -, hl⟩ := compiles_stack hc
  have := hl k (by simp [kids, hk])
  simpa [kids] using this

/-- **Every instance of `walk_path__L6_L7` pops its children's words**, the entry of its one
witness hint. -/
theorem wp_pops {P : Core.Program} (hf : P.find? "walk_path__L6_L7" = some Fn.«walk_path__L6_L7».core)
    {σ : Val} {bufs : List ℕ} {kids' : List Memory.Tree} {es : List Ev} {vs : List V}
    (hw : walk σ Fn.«walk_path__L6_L7».core.body = .ret es vs) (rd : Reader) :
    (Memory.Tree.node "walk_path__L6_L7" σ bufs kids').pops P rd = [("merkle_children", kids.map σ)] := by
  obtain ⟨hnw, -⟩ := prefix_pairs prefixOk_wp
  obtain ⟨es', h1, h3, hs⟩ := prefix_splice hnw hw rd (Memory.Tree.popsKids P rd kids')
  have hc : calls es' = [] := by
    have hl : Lift.Stmt.leafOkList (fun _ ↦ true) (atomPrefix Fn.«walk_path__L6_L7».core.body).2 = true := by
      decide +kernel
    have := Lift.walk_leafOk (σ := σ) _ hl
    rw [h1] at this
    exact Lift.calls_nil_of_leafOk this
  have he : evPops rd σ es' = [] := by
    have h0 := splice_append_of_calls_nil (rd := rd) (σ := σ) [] [] hc
    rw [List.append_nil, splice_nil_of es' [] h3 (fun _ h ↦ (List.not_mem_nil h).elim)] at h0
    simpa [splice] using h0.symm
  have hr := splice_append_of_calls_nil (rd := rd) (σ := σ) [] (Memory.Tree.popsKids P rd kids') hc
  rw [List.append_nil, he] at hr
  rw [Memory.Tree.pops_node hf hw, hs, hr, wp_flow]
  simp [splice, Core.Hint.pops, Dest.words]

/-- **`HintOk` at offset `0`**: the executor's witness hint there succeeds when the stream's next
entry is the instance's children's words and the frame holds each child at its cell. -/
theorem wp_hintOk {C : Ctx} {M : ℕ → E} {st : St} {σ : Val}
    (hn : StreamNext C st "merkle_children" (kids.map σ))
    (hM : ∀ k < 24, M (st.fp + (7 + k)) = σ (.n (5 + k))) (hc : st.fp + 31 ≤ maxCells) :
    HintOk C M st (.witnessStack "merkle_children" 7 24) := by
  refine hintOk_stack (rd := fun _ ↦ none) wp_cells.1 hn (fun v hv ↦ ?_) (by omega)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
  have hk := List.mem_range.mp hk
  rw [← hM k hk, ← wp_cells.2 k hk]

end

end LeanVM.Guest.Bridge.WalkPath
