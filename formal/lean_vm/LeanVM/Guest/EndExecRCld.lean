/-
  LeanVM.Guest.EndExecRCld

  Paths through a dispatch, `claim_list_digest`'s empty list's branch, and the tile families at the honest frames
  (no function's tiles are listed: `claim_list_digest`, whose count they tiled, is on the core route).
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.EndExecRA
public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.EndExecRTile

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec

public section

theorem pick_cases {σ : Core.Val} {x : V} {args rets : List V} : ∀ (j : ℕ) (fs : List String),
    Memory.pick σ x args rets j fs = .stuck ∨ ∃ g, Memory.pick σ x args rets j fs = .fall [.call g args rets]
  | _, [] => Or.inl rfl
  | j, f :: fs => by
    unfold Memory.pick
    split_ifs
    · exact Or.inr ⟨f, rfl⟩
    · exact pick_cases (j + 1) fs

/-- **A dispatch past atoms calls**, on a returning path. -/
theorem dispatch_call {σ : Core.Val} {bs : List Atom} {x : V} {fs : List String} {args rets : List V}
    {rest : List Stmt} {es : List Ev} {vs : List V}
    (h : Memory.walk σ (bs.map Stmt.atom ++ .dispatch x fs args rets :: rest) = .ret es vs) :
    ∃ g, Ev.call g args rets ∈ es := by
  rw [Bridge.walk_atoms_pre] at h
  obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
  rw [Memory.walk, Memory.walk1] at h'
  rcases pick_cases (σ := σ) (x := x) (args := args) (rets := rets) 0 fs with hp | ⟨g, hp⟩
  · rw [hp] at h'; simp [Out.seq] at h'
  · rw [hp, Out.seq] at h'
    obtain ⟨es'', -, rfl⟩ := Bridge.pre_eq_ret h'
    exact ⟨g, List.mem_append_right _ List.mem_cons_self⟩

/-- The empty list's branch and what follows call nothing. -/
theorem cl_zero_callees : Stmt.blockCallees (B1.Digest.cl23Zero ++
    [.atom (.touch (.n 94) (.n 1)), .atom (.copy (.n 95) (.n 10)), .atom (.copy (.n 96) (.n 11)),
      .ret [.n 95, .n 96]]) = [] := by
  decide +kernel

theorem walk_call_cons {σ : Core.Val} (f : String) (args rets : List V) (ps : List Stmt) :
    Memory.walk σ (.call f args rets :: ps) = (Memory.walk σ ps).pre [.call f args rets] := by
  rw [Memory.walk, Memory.walk1, Out.seq]

/-- **The frames' tiles' sums at the honest frames**: none listed. -/
theorem tiles_ok {A : String → Bridge.FnAl} : ∀ p ∈ Res.tiles, TileAt A p.1 p.2.1 p.2.2 := by
  simp [Res.tiles]

/-- **The tile families at an honest frame.** -/
theorem tileFam_top {A : String → Bridge.FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}
    {w : Res.Wit} (t : TopAt A r K i e j) (hr : r.Ok) (hW : Res.witOk j w = true) {x : Mode.Res}
    (hx : Res.tileFamB j w x = true) : RRes (refMem r.img) e.I.fp x :=
  tileFam_top_of tiles_ok t hr hW hx

end

end LeanVM.Guest.EndExec
