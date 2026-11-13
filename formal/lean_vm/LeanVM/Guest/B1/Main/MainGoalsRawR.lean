/-
  LeanVM.Guest.B1.Main.MainGoalsRawR

  `main_loop2` on an honest run within its static bound, by trees popping its iterations' entries (route R).
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsStaticB
public import LeanVM.Guest.B1.Main.RawAtP
public import LeanVM.Guest.Budget.BoundedR

/-!
# `main_loop2` with its pops

`mainGoalL3R`: `mainGoalL3B` by trees popping the raw leanXMSS signatures' entries in order (`rawX_loopP`, `completeAtDTBR_of_relAtInP_on`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtDTBR Returns completeAtDTBR_of_relAtInP_on)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`main_loop2` on an honest run, by trees popping its iterations' entries.** -/
theorem mainGoalL3R (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs name% «main_loop2» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop2» + fs name% «main_loop2»))
    (h0 : (hm fs fp seed s w).nrx ≠ 0) :
    CompleteAtDTBR fs cert 23 name% «main_loop2» (hLmain fs fp seed s w)
      ([1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] ++ lxTagWords) (Returns [])
      (fun rd t => t.pops coreProgram rd =
        (List.range' 0 (hRawX s w).length).flatMap (l2Pops (rawXD fs fp hn ((hRawX s w)[0]'(Nat.pos_of_ne_zero h0)))))
      ((hm fs fp seed s w).nrx * iterK fs SK name% «main_loop2» + fs name% «main_loop2») := by
  have hpos : 0 < (hRawX s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawX s w).length ≤ rX s w := xRaw_le hl.toDeployedLimits
  have hX : s.claims.xmss.length ≤ rX s w := Nat.le_add_right _ _
  have hX' : rX s w ≤ 2 ^ 23 := by omega
  have hr : (hRawX s w).length < 2 ^ 34 := by omega
  have e : l2ArgsAt 0 (hRawX s w).length (rX s w) (hPos seed s w fs fp 2) (hPos seed s w fs fp 0) =
      [1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] ++ lxTagWords := by
    rw [l2ArgsAt, pow_zero]
    rfl
  rw [← e]
  refine completeAtDTBR_of_relAtInP_on (fun fp' => ⟨_, fun rd hlow hL =>
    (rawX_loopP fs cert (rawXD fs fp hn (hRawX s w)[0]) hX' hr hlow hL 0 hpos fp'
      (fp' + ((hRawX s w).length - 0 + 1) * fs name% «main_loop2»)).relAtInP⟩) hT
    (loopPre_pow hpos (by omega) _) ?_
  simp [l2ArgsAt, logG_gen (show (hRawX s w).length < 2 ^ 64 - 1 by omega)]
  rfl

end
end LeanVM.Guest.B1.Main
