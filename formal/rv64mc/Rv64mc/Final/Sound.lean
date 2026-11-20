/-
  Rv64mc.Final.Sound

  `Sound` from `main`'s contract (`sound_of_main`). A loaded image is at `_start`, whose template `Start.tmpl` is
  the lift of function `gs` of machine-checked's functions `fns`; `Start.ok` makes it safe for the verdict at
  Lprog, machine-checked's transfer theorem (`SafeN.of_lift`) carries that to SP1's machine, and `sound_of_safe` to
  the statement's. Every hypothesis but `MainSpec` is a fact about the concrete image that the link step decides:
  `fns` are the image's functions (`FnsIn`, `ProgOk`), `_start` is where the image enters, its lift is the template
  and its call reaches `main` (`Start.Link.WF`), and the environment fits the image (its static data are among the
  image's data, `NEXT` starts at the heap's start, the heap and the stack fit).
-/

import Rv64mc.Final.Start

namespace Rv64mc

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Lift Lprog Lprog.RiscV

/-- **The image is sound if `main` keeps its contract.** -/
theorem sound_of_main {img : Image} {fns : List Fn} {env : Env} {need gs : Nat} {fn : Fn} {L : Start.Link}
    (hok : ProgOk fns) (hfns : FnsIn img fns) (hg : fns[gs]? = some fn)
    (hstart : (liftProg fns)[gs]? = some (Start.tmpl L)) (hentry : L.base = img.entry)
    (hL : L.WF (liftProg fns))
    (hstatic : ∀ m : MachineState, (∀ p ∈ img.data, m.getMem p.1 = p.2) → env.Static m)
    (hnext : (env.nextAddr, heapStart) ∈ img.data) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat)
    (hmain : MainSpec env (liftProg fns) L.main.idx need) : Sound img := by
  apply sound_of_safe
  intro words s hl N
  have ⟨hpc, _, hdata, hin, h10, hcap⟩ := hl
  have hbase : fn.base = L.base := by
    rw [getElem?_liftProg hg] at hstart
    exact congrArg Lfundef.addr (Option.some.inj hstart)
  exact SafeN.of_lift (Q := fun _ => Verdict words) hok hg (by rw [hpc, hbase, hentry])
    (codeAt_of_loaded hfns hl)
    (fun _ => Start.ok env (liftProg fns) gs L hstart hL hstack hheap hmain (hstatic s hdata)
      ⟨h10, hcap, hin, hdata _ hnext⟩)
    (fun _ _ h => h) (fun _ _ _ _ _ h => SafeN.of_true h _)

end Rv64mc

/-- info: 'Rv64mc.sound_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.sound_of_main
