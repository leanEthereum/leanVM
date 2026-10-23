/-
  LeanVM.Guest.B1.VerifySub.Spec

  The specification's programs, split where `verify_sub` hands a phase to a callee.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Protocol.Compile.Prog

/-!
# The split programs

* `verifyBusBalance_split`: `verifyBusBalance` is its challenges, `gkrPhase` at the push side's
  depth, and `busRest`;
* `verifyWhir_split`: `verifyWhir` is `whirOpen`, then its terminal's check
  (`WhirEnd.Accepts`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem verifyBusBalance_split (ev : Evaluations) (layout : Layout) :
    verifyBusBalance ev layout = (do
      let alphas ← Prog.sampleN busBits
      let beta ← Prog.sampleE
      let r ← gkrPhase (pushDepth layout)
      busRest ev layout alphas beta r.2.1 r.2.2) := by
  simp only [verifyBusBalance, gkrPhase, busRest, pushDepth, Prog.bind_eq, Prog.pure_eq,
    Prog.bind_assoc, Prog.ret_bind]

theorem foldl_add_shift {α : Type} (f : α → E) (a : E) (l : List α) :
    l.foldl (fun w c ↦ w + f c) a = a + l.foldl (fun w c ↦ w + f c) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + f x), zero_add, add_assoc]

theorem bind_congr' {α β : Type} {p : Prog α} {f g : α → Prog β} (h : ∀ a, f a = g a) :
    p.bind f = p.bind g := by rw [funext h]

theorem whirLevels_split (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      whirLevels logN laneFolds eb index levels s =
        (whirLevelsOpen logN laneFolds index levels s).bind fun w ↦ Prog.require (w.Accepts eb)
  | _, [], _ => rfl
  | index, [level], s => by
    rw [whirLevels, whirLevelsOpen]
    simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind, WhirEnd.Accepts]
    repeat refine bind_congr' fun _ ↦ ?_
    rw [foldl_add_shift _ (eb _), add_comm (eb _)]
    congr 1
  | index, level :: next :: rest, s => by
    rw [whirLevels, whirLevelsOpen]
    simp only [Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
      whirLevels_split logN laneFolds eb (index + 1) (next :: rest)]

theorem verifyWhir_split (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    verifyWhir logN logInvRate target eb = (do
      let w ← whirOpen logN logInvRate target
      Prog.require (w.Accepts eb)) := by
  simp only [verifyWhir, whirOpen, Prog.bind_eq, Prog.bind_assoc, whirLevels_split]

end
end LeanVM.Guest.B1.VerifySub
