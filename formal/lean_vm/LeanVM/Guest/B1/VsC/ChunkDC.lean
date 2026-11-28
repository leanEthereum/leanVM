/-
  LeanVM.Guest.B1.VsC.ChunkDC

  `chunk_d__L{w}` completes, layout-free: the first of `verify_sub`'s callees in
  `CallCompletes` form.
-/

module

public import LeanVM.Guest.Complete.Compose
public import LeanVM.Guest.Complete.Call0
public import LeanVM.Guest.B1.Link.ChunkD
public import LeanVM.Guest.B1.VsC.LinkShape
import LeanVM.Guest.CoreRef

/-!
# `chunk_d`, complete

`chunk_d__L{w}` sets one word and returns it, `g^d` for `d` the chunk count of a `w`-bit pointer.
`chunk_d_complete`: at every deployed width `19 ≤ w ≤ 24`, on every memory, its call returns
`[g^(chunkCount w)]` by a tree that pops nothing and whose node is exact (`callCompletes_node`, no
words of its own, no callees).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- What `verify_sub` asks of a callee that reads no stream: it pops nothing, every node exact. -/
def PostQuiet (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = [] ∧ t.Every (ExactAt coreProgram rd)

/-- A function setting one constant and returning it completes, popping nothing. -/
theorem callCompletes_const {k : ℕ} {name : String} {f : Fn} {c : E} {Pre : Reader → Prop}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [])
    (hbody : f.body = [.atom (.const (.n 0) c), .ret [.n 0]]) :
    CallCompletes k name [] [c] Pre PostQuiet := by
  refine callCompletes_node fun b ↦ ⟨0, [], fun _ ↦ c, f, [.atom (.const (.n 0) c)], [.n 0], [],
    wordsIn_nil b, hfind, by rw [hparams]; rfl, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hbody]; rfl
  · intro rd _ _ _ e he
    simp only [List.mem_singleton] at he
    subst he
    rfl
  · show KidsCompl k _ _ [] []
    rw [KidsCompl]; trivial
  · intro rd ts _ _ _ hv _
    have hts : ts = [] := by
      cases ts with
      | nil => rfl
      | cons t ts =>
        have e : calls [Ev.atom (Atom.const (V.n 0) c)] = [] := rfl
        rw [e] at hv
        simp [Tree.KidsValid] at hv
    subst hts
    have hev : Tree.events coreProgram (.node name (fun _ ↦ c) (allocs (fun _ ↦ c)
        [.atom (.const (.n 0) c)]) []) = [.atom (.const (.n 0) c)] := by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hbody]; rfl
    refine ⟨?_, ?_⟩
    · rw [Tree.pops, hev]; rfl
    · rw [Tree.every_node]
      refine ⟨fun e he ↦ ?_, by rw [Tree.EveryKids]; trivial⟩
      have he' : e ∈ [Ev.atom (.const (.n 0) c)] := by
        have : Tree.events coreProgram (.node name (fun _ ↦ c) [] []) = [.atom (.const (.n 0) c)] := by
          simp only [Tree.events, Tree.name, Tree.val, hfind, hbody]; rfl
        rwa [this] at he
      simp only [List.mem_singleton] at he'
      subst he'
      trivial

/-- **`callCompletes_const` with no words of its own.** -/
theorem callCompletes0_const {k : ℕ} {name : String} {f : Fn} {c : E} {Pre : Reader → Prop}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [])
    (hbody : f.body = [.atom (.const (.n 0) c), .ret [.n 0]]) :
    CallCompletes0 k name [] [c] Pre PostQuiet := by
  have hw : walk (fun _ ↦ c) f.body = .ret [.atom (.const (.n 0) c)] [.n 0] := by rw [hbody]; rfl
  refine callCompletes0_node fun rd _ _ ↦ ⟨fun _ ↦ c, f, [.atom (.const (.n 0) c)], [.n 0], [], hfind,
    by rw [hparams]; rfl, hw, rfl, ?_, ?_, by rw [Tree.BufsOkKids]; trivial, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    rfl
  · show Tree.KidsValid coreProgram rd _ [] []
    rw [Tree.KidsValid]; trivial
  · have hev : ∀ bufs, Tree.events coreProgram (.node name (fun _ ↦ c) bufs []) =
        [.atom (.const (.n 0) c)] := fun _ ↦ by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw]
    refine ⟨?_, ?_⟩
    · rw [Tree.pops, hev]; rfl
    · rw [Tree.every_node]
      refine ⟨fun e he ↦ ?_, by rw [Tree.EveryKids]; trivial⟩
      rw [hev] at he
      simp only [List.mem_singleton] at he
      subst he
      trivial

theorem chunkD_complete_of {k : ℕ} {name : String} {f : Fn} {w d : ℕ} {Pre : Reader → Prop}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [])
    (hbody : f.body = [.atom (.const (.n 0) (word (2 ^ d) 0)), .ret [.n 0]])
    (hd : chunkCount w = d) (h64 : d < 64) :
    CallCompletes0 k name [] [gen ^ chunkCount w] Pre PostQuiet := by
  rw [hd, ← word_two_pow h64]
  exact callCompletes0_const hfind hparams hbody

/-- **`chunk_d__L{w}` completes** at every deployed width, returning `g^d`, `d` its chunk count. -/
theorem chunk_d_complete (k : ℕ) (Pre : Reader → Prop) :
    CallCompletes0 k "chunk_d__L19" [] [gen ^ chunkCount 19] Pre PostQuiet ∧
    CallCompletes0 k "chunk_d__L20" [] [gen ^ chunkCount 20] Pre PostQuiet ∧
    CallCompletes0 k "chunk_d__L21" [] [gen ^ chunkCount 21] Pre PostQuiet ∧
    CallCompletes0 k "chunk_d__L22" [] [gen ^ chunkCount 22] Pre PostQuiet ∧
    CallCompletes0 k "chunk_d__L23" [] [gen ^ chunkCount 23] Pre PostQuiet ∧
    CallCompletes0 k "chunk_d__L24" [] [gen ^ chunkCount 24] Pre PostQuiet :=
  ⟨chunkD_complete_of (d := 6) (coreProgram_find?_at (j := idx% «chunk_d__L19») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num),
    chunkD_complete_of (d := 6) (coreProgram_find?_at (j := idx% «chunk_d__L20») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num),
    chunkD_complete_of (d := 7) (coreProgram_find?_at (j := idx% «chunk_d__L21») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num),
    chunkD_complete_of (d := 7) (coreProgram_find?_at (j := idx% «chunk_d__L22») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num),
    chunkD_complete_of (d := 8) (coreProgram_find?_at (j := idx% «chunk_d__L23») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num),
    chunkD_complete_of (d := 9) (coreProgram_find?_at (j := idx% «chunk_d__L24») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num)⟩

end
end LeanVM.Guest.B1.VsC
