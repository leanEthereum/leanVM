/-
  LeanVM.Guest.B1.VsC.VsW1

  `verify_sub`'s window 1: the `hint_stream` call filling the stream's buffer.
-/

module

public import LeanVM.Guest.B1.VsC.VsW0
public import LeanVM.Guest.B1.VsC.HintStreamA

/-!
# Window `1`

Statement `36` of `verify_sub` is `hint_stream(.n 55, .n 42)`: the stream's buffer (window `0`'s
`HeapBuf` of `256 p` words) and its chunk count `g^p`. `vsW1_segA`: on `vsVal rd0 w args`, with the
oracle placing the buffer at `s` (`w 55 = ptrAt s`) and the chunk count `w 42 = g^p`, `p < 2^63`,
the statement is a window entering `hint_stream` at the aligned base of the callees' cursor, its
heap hints in `verify_sub`'s own data (`hOwn`: the buffer's cells), its tree popping the chunks of
the words `ws` every memory of the window holds at `s` (`hpre`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Statement `36`. -/
def vsW1s : Stmt := .call "hint_stream" [.n 55, .n 42] []

set_option maxRecDepth 100000 in
theorem vsW1_eq : (vsA.drop 36).take 1 = [vsW1s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vsW1_rcs : vsRcs.lookup (.n 55) = none ∧ vsRcs.lookup (.n 42) = none := by decide +kernel

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- The stream's chunk count, as the oracle gives it. -/
theorem vsVal_42 (ha : args.length = 6) : vsVal rd0 w args (.n 42) = w 42 := by
  have := vsW0_good (rd0 := rd0) (w := w) ha (a := .hint (.witness "stream_chunks" (.stack [.n 42])))
    (by simp [vsW0, vsW0a])
  simp only [Good, List.mem_singleton, forall_eq] at this
  exact this

/-- The stream's buffer, as the oracle places it. -/
theorem vsVal_55 (ha : args.length = 6) : vsVal rd0 w args (.n 55) = w 55 :=
  vsW0_good (rd0 := rd0) (w := w) ha (a := .hint (.allocDyn (.n 55) (.n 54))) (by simp [vsW0, vsW0b])

end

/-- The chunks of the stream popped in order, every node exact. -/
def hsQ (ws : List E) (n : ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = (List.range n).map (fun j => ("stream", chunkOf ws j)) ∧ t.Every (ExactAt coreProgram rd)

set_option maxRecDepth 100000 in
/-- **Window `1`**: statement `36`, `hint_stream` on the stream's buffer at `s` and its chunk count. -/
theorem vsW1_segA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader}
    {w : ℕ → E} {args : List E} (ha : args.length = 6) {p s fp a kc : ℕ} (hp : p < 2 ^ 63)
    (hw42 : w 42 = gen ^ p) (hw55 : w 55 = ptrAt s) (ws : List E) {Own R : ℕ → Prop}
    {Pre O : Reader → Prop} {D : ℕ → Prop} (hOwn : ∀ j < 256 * p, Own (s + j))
    (hpre : ∀ rd, Pre rd → O rd → HsPre (ptrAt s) ws p rd) :
    SegA (fs := fs) (al := al) (cert := cert) k "verify_sub" fp (vsVal rd0 w args) (rdOver (vsVal rd0 w args))
      Own R Pre [vsW1s] [.call "hint_stream" [.n 55, .n 42] []] a a kc
      (allocBase (al hsLoopName) (allocBase (al "hint_stream") kc + fs "hint_stream") + hsB fs p)
      O (fun rd => O rd ∧ True) D (fun i => D i ∨ False) [hsQ ws p] := by
  obtain ⟨r55, r42⟩ := vsW1_rcs
  have hargs : [V.n 55, V.n 42].map (vsVal rd0 w args) = [ptrAt s, gen ^ p] := by
    simp only [List.map_cons, List.map_nil, vsVal_55 ha, vsVal_42 ha, hw55, hw42]
  refine segA_call1 (s := vsW1s) (g := "hint_stream") (args := [.n 55, .n 42]) (rets := [])
    (Bc := fs "hint_stream") (fun rd _ _ _ _ => walk_call _ _ _ _)
    (fun rd _ _ _ _ => ⟨by rw [List.map_cons, List.map_cons, List.map_nil, List.map_cons, List.map_cons,
      List.map_nil, rdOver_eq r55, rdOver_eq r42], List.map_nil.trans List.map_nil.symm⟩)
    (fun i h => Or.inl (Or.inr h)) ?_
  rw [hargs]
  exact (hint_stream_completeA fs al cert k s ws p Own hp hOwn _ _ le_rfl).mono (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (fun rd h => hpre rd h.1 h.2) (fun _ _ _ h => h)

end
end LeanVM.Guest.B1.VsC
