/-
  LeanVM.Guest.Compiled.Obl.Gkr

  The obligations of `verify_bus_gkr` and its layer loop `verify_bus_gkr_loop0`, from B1's facts
  on the loop's parity words (`B1.Gkr.Parity`).
-/

module

public import LeanVM.Guest.Compiled.Obl.GuestU
public import LeanVM.Guest.B1.Gkr.Parity

/-!
# The layer loop's parity

`verify_bus_gkr_loop0` dispatches on `σ 53`, the word it reads at `σ 17 · g^12`, the parity word
of layer `x`. Its precondition `GkrPar` (`XSpec.gkr`) bounds it:

* fact `(52, .mem (.n 17) 12 4)`: before the dispatch, the word at `σ 17 · g^12`, if read, is
  below `g^4` (`ly_par_parity`);
* `ext` site `196`, the tail call: `GkrPar` at `x·g` (`ly_par_tail`).

`verify_bus_gkr` calls it at statement `280` on `x = σ 420`, set to `1` at statement `279`:
`GkrPar` at `x = 1` (`vbg_par`).
-/

namespace LeanVM.Guest.Compiled.Obl

open LeanVM.Compiler LeanVM.Compiler.Obl LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Tables

@[expose] public section

/-- `verify_bus_gkr_loop0`'s fact: the parity word, if read, below `g^4`. -/
def gkrLoopFacts : List (Nat × Hyp) := [(52, .mem (.n 17) 12 4)]

theorem gkrLoop_body : (coreProgram.getD (idx% verify_bus_gkr_loop0) default).body = lyBody := rfl

theorem gkrLoop_sig : (coreProgram.getD (idx% verify_bus_gkr_loop0) default).name =
      name% verify_bus_gkr_loop0 ∧
    (coreProgram.getD (idx% verify_bus_gkr_loop0) default).params = (List.range 10).map V.n ∧
    (guestTab.sig (name% verify_bus_gkr_loop0)).ext = true ∧
    xSpecOf (name% verify_bus_gkr_loop0) = some .gkr := by
  decide +kernel

theorem gkrLoop_tail : (coreProgram.getD (idx% verify_bus_gkr_loop0) default).body.drop 196 =
    [.callIf (.n 245) (name% verify_bus_gkr_loop0) ((247 :: (List.range' 1 9)).map V.n), .ret []] :=
  tbStmtsEqb_sound (by decide +kernel)

/-- **The analysis accepts `verify_bus_gkr_loop0`** with its fact and its tail call's site. -/
theorem evalGkrLoop :
    chkFnX guestTab gkrLoopFacts [196] (coreProgram.getD (idx% verify_bus_gkr_loop0) default) =
      true := by
  decide +kernel

theorem gkrPar_own {rd : Reader} {σ : Val}
    (h : guestU rd (coreProgram.getD (idx% verify_bus_gkr_loop0) default).name
      ((coreProgram.getD (idx% verify_bus_gkr_loop0) default).params.map σ)) :
    GkrPar rd (σ (.n 3)) (σ (.n 0)) (σ (.n 9)) := by
  obtain ⟨hn, hp, he, hs⟩ := gkrLoop_sig
  have := own_spec h (by rw [hn]; exact he) (by rw [hn]; exact hs)
  rw [hp] at this
  exact this

/-- **`verify_bus_gkr_loop0`'s obligations.** -/
theorem gkrLoop_obl : OblFn (coreProgram.getD (idx% verify_bus_gkr_loop0) default) := by
  refine oblFn_of_chkX evalGkrLoop ?_ ?_
  · intro κ L _ _ C σ _ hpre p hp hl
    simp only [gkrLoopFacts, List.mem_singleton] at hp
    subst hp
    intro v hv
    rw [gkrLoop_body] at hl
    exact ly_par_parity lyBody_take52_noRet hl (by decide +kernel) (gkrPar_own hpre) v hv
  · intro κ L _ _ C σ _ hpre i hi s ss hd hl
    simp only [List.mem_singleton] at hi
    subst hi
    rw [gkrLoop_tail] at hd
    obtain ⟨rfl, -⟩ := List.cons.inj hd
    intro _ _ sp hsp
    rw [gkrLoop_sig.2.2.2] at hsp
    obtain rfl := (Option.some.inj hsp).symm
    rw [gkrLoop_body] at hl
    exact ly_par_tail hl (gkrPar_own hpre)

theorem gkrBus_body :
    (coreProgram.getD (idx% verify_bus_gkr) default).body.take 280 = vbgPre.take 280 := by
  rw [vbgPre, vbgBody, List.take_take]
  rfl

theorem gkrBus_call : (coreProgram.getD (idx% verify_bus_gkr) default).body.drop 280 =
    .callIf (.n 419) (name% verify_bus_gkr_loop0)
      ([420, 165, 417, 173, 8, 176, 52, 187, 6, 53].map V.n) ::
      (coreProgram.getD (idx% verify_bus_gkr) default).body.drop 281 := by
  rw [← List.getElem_cons_drop (by decide +kernel)]
  congr 1

/-- **The analysis accepts `verify_bus_gkr`** with its call of the loop as a site. -/
theorem evalGkrBus : chkFnX guestTab [] [280] (coreProgram.getD (idx% verify_bus_gkr) default) =
    true := by
  decide +kernel

/-- **`verify_bus_gkr`'s obligations.** -/
theorem gkrBus_obl : OblFn (coreProgram.getD (idx% verify_bus_gkr) default) := by
  refine oblFn_of_chkX evalGkrBus (fun _ _ _ _ _ _ _ p hp => absurd hp List.not_mem_nil) ?_
  intro κ L _ h2 C σ _ _ i hi s ss hd hl
  simp only [List.mem_singleton] at hi
  subst hi
  rw [gkrBus_call] at hd
  obtain ⟨rfl, -⟩ := List.cons.inj hd
  intro _ _ sp hsp
  rw [gkrLoop_sig.2.2.2] at hsp
  obtain rfl := (Option.some.inj hsp).symm
  rw [gkrBus_body] at hl
  have hp := vbg_par (h2.trans maxLogMem_le) L hl
  have c420 := tb_holds_atom vbgPre_take280_noRet hl 279 (.const (.n 420) (word 1 0))
    (by decide +kernel)
  simp only [Atom.Holds, Compiler.word_one] at c420
  show GkrPar L.read (σ (.n 173)) (σ (.n 420)) (σ (.n 53))
  rw [c420]
  exact hp

end
end LeanVM.Guest.Compiled.Obl
