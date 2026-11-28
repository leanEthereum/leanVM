/-
  LeanVM.Guest.B1.VsC.VsW3

  `verify_sub`'s window 3: `g_power_of_word` on the stream's word 7.
-/

module

public import LeanVM.Guest.B1.VsC.VsW2
public import LeanVM.Guest.B1.VsC.GPowerA

/-!
# Window `3`

Statement `69` of `verify_sub` is `g_power_of_word(.n 91)` into `.n 94`: the stream's word `7`
(window `2`'s last load) to its power of `g`. `vsW3_segA`: on `vsVal rd0 w args`, the word `E(n)`,
`n < 64`, and the oracle's return `w 94 = g^n`, the statement is a window entering
`g_power_of_word` at the aligned base of the callees' cursor, touching no memory, quiet.
`vsVal_call_ret`: a call of `vsA` returns the oracle's words.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **A call of `vsA` returns the oracle's words** on the forward valuation. -/
theorem vsVal_call_ret {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {i : ℕ}
    {g : String} {as rs : List V} (h : (vsA.drop i).take 1 = [.call g as rs]) :
    ∀ v ∈ rs, vsVal rd0 w args v = w v.idx := by
  have hm : Stmt.call g as rs ∈ vsA :=
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [h]; exact List.mem_singleton_self _))
  exact vsVal_goodA (rd := rd0) (w := w) ha (fixS (.call g as rs)) (List.mem_map_of_mem hm)

/-- Statement `69`. -/
def vsW3s : Stmt := .call "g_power_of_word" [.n 91] [.n 94]

set_option maxRecDepth 100000 in
theorem vsW3_eq : (vsA.drop 69).take 1 = [vsW3s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vsW3_rcs : vsRcs.lookup (.n 91) = none ∧ vsRcs.lookup (.n 94) = none := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Window `3`**: statement `69`, `g_power_of_word` on `E(n)`, `n < 64`. -/
theorem vsW3_segA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader}
    {w : ℕ → E} {args : List E} (ha : args.length = 6) {n fp a kc : ℕ} (hn : n < 64)
    (h91 : vsVal rd0 w args (.n 91) = eOfNat n) (hw94 : w 94 = gen ^ n) {Own R : ℕ → Prop}
    {Pre O : Reader → Prop} {D : ℕ → Prop} :
    ∃ e, SegA (fs := fs) (al := al) (cert := cert) k "verify_sub" fp (vsVal rd0 w args)
      (rdOver (vsVal rd0 w args)) Own R Pre [vsW3s] [.call "g_power_of_word" [.n 91] [.n 94]] a a kc e
      O (fun rd => O rd ∧ True) D (fun i => D i ∨ False) [PostQuiet] := by
  obtain ⟨r91, r94⟩ := vsW3_rcs
  have h94 : vsVal rd0 w args (.n 94) = gen ^ n :=
    (vsVal_call_ret ha vsW3_eq (.n 94) (List.mem_singleton_self _)).trans hw94
  obtain ⟨B, hB⟩ := g_power_of_word_completeA fs al cert k (fun _ => False) (fun rd => Pre rd ∧ O rd) hn
  obtain ⟨e, he⟩ := hB (allocBase (al "g_power_of_word") kc) (allocBase (al "g_power_of_word") kc + B) le_rfl
  refine ⟨e, segA_call1 (s := vsW3s) (g := "g_power_of_word") (args := [.n 91]) (rets := [.n 94]) (Bc := B)
    (Rc := fun _ => False) (Dc := fun _ => False) (Oc := fun _ => True) (Q := PostQuiet)
    (fun rd _ _ _ _ => walk_call _ _ _ _)
    (fun rd _ _ _ _ => ⟨by rw [List.map_cons, List.map_cons, List.map_nil, List.map_nil, rdOver_eq r91],
      by rw [List.map_cons, List.map_cons, List.map_nil, List.map_nil, rdOver_eq r94]⟩)
    (fun _ h => False.elim h) ?_⟩
  rw [List.map_cons, List.map_nil, List.map_cons, List.map_nil, h91, h94]
  exact he

end
end LeanVM.Guest.B1.VsC
