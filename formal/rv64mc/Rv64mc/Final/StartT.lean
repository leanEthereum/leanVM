/-
  Rv64mc.Final.StartT

  `_start` is total, and `HaltsSafely` follows from `main`'s total contract: the counterparts of
  `Final/Start.lean` and `Final/Sound.lean`.

  `Start.total`: over `_start`'s template (`auipc gp; addi gp; li sp, 3; slli sp, sp, 30; addi sp,
  sp, -16; auipc ra; jalr ra (main); li t0, 0; ecall; j .`), from `MainSpecT`, every run from
  `_start`'s entry ends at a halt inside the program with `a0` a verdict (`Ends`): `main` ends it
  with `a0 = 2`, or returns `0` or `1`, which `_start` passes to the halting `ecall` in `a0`. The
  `j .` is never reached: under `stmtCtx` the `ecall` ends the run.

  `haltsSafely_of_main`: from `Start.total`, `halts_of_lift` (`Final/Transfer.lean`) gives a
  halting run of the statement's machine. Its hypotheses are `sound_of_main`'s, but `MainSpecT`
  for `MainSpec`, plus where the windows lie: `NEXT`'s address in the stack window, the heap's
  end at most the first window's end, the static data words in a window, and the image's code
  between the windows, which give `Windows` at `main`'s entry (`HoldsT`'s precondition).
-/

import Rv64mc.Final.MainSpecT
import Rv64mc.Final.Transfer
import Rv64mc.Gen.Tmpl.Start

namespace Rv64mc

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Lift Lprog Lprog.RiscV

/-- One of the guest's verdicts: `0` (accept), `1` (reject), `2` (abort). -/
def IsVerdict (v : Word) : Prop := v = 0 ∨ v = 1 ∨ v = 2

/-- Where the whole run may end: inside the program (not returned from `_start`), with `a0` a verdict. -/
def Ends (s : State rvIsa) : Prop := s.stack ≠ [] ∧ IsVerdict (s.regs .x10)

namespace Start

/-- **`_start` is total**, at Lprog, from `main`'s total contract: from its entry, with an input of fewer than
    `maxInputWords` words in memory and its length in `a0`, `NEXT` at the heap's start, the static data in place and
    the windows where `Windows` says at `main`'s stack top, the run ends inside the program with `a0` a verdict. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Start.Link)
    (hp : p[i]? = some (Gen.Start.tmpl L)) (hL : Gen.Start.Link.WF p L) {need : Nat}
    (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    (hmain : MainSpecT env p L.main.idx need) {words : List Word} (hw : words.length < maxInputWords)
    {regs : Reg → Word} {m : MachineState} (hst : env.Static m) (hpre : MainPre env words regs m)
    (hwin : Windows env stackTop m) {ret top : Word} :
    rvIsa.Total p stmtCtx (WinOk p) Ends ⟨[⟨i, 0, ret, top⟩], regs, m⟩ := by
  obtain ⟨h10, hcap, hin, hnx⟩ := hpre
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine HoldsT.call (hmain words hw) hp rfl (callee_site hL.main hL.s0 (by simp [updReg_apply, Expr.eval]))
    ?_ hst (by rw [hnx]; exact hheap) ⟨by simpa [updReg_apply] using h10, hcap, hin, hnx⟩ ?_ ?_
    (fun _ _ _ _ h2 _ => ⟨nofun, .inr (.inr h2)⟩) ?_
  · simp only [lsym_simp]
    exact hstack
  · simp only [lsym_simp]
    decide
  · simp only [lsym_simp]
    exact hwin
  · intro r' m' _ _ _ _ hret
    refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
    refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
    refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
    refine Total.ext_done hp rfl (by simp [stmtCtx, updReg_apply, Expr.eval, BinOp.eval])
      (WinOk.of_ne hp rfl nofun) ⟨nofun, ?_⟩
    simp only [updReg_apply]
    rcases hret with h | h
    · exact .inl (by simpa using h)
    · exact .inr (.inl (by simpa using h))

end Start

/-- **`HaltsSafely` from `main`'s total contract**, with `sound_of_main`'s facts about the image. -/
theorem haltsSafely_of_main {img : Image} {fns : List Fn} {env : Env} {need gs : Nat} {fn : Fn}
    {L : Gen.Start.Link} (hok : ProgOk fns) (hfns : FnsIn img fns) (hg : fns[gs]? = some fn)
    (hstart : (liftProg fns)[gs]? = some (Gen.Start.tmpl L)) (hentry : L.base = img.entry)
    (hL : Gen.Start.Link.WF (liftProg fns) L)
    (hstatic : ∀ m : MachineState, (∀ p ∈ img.data, m.getMem p.1 = p.2) → env.Static m)
    (hnext : (env.nextAddr, heapStart) ∈ img.data) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat)
    (henv : 0xa0000000 ≤ env.nextAddr.toNat ∧ env.heapEnd.toNat ≤ 0x78000000 ∧ ∀ q ∈ env.data, inWindow q.1 8 = true)
    (hcode : ∀ a, img.codeAt a ≠ none → 0x78000000 ≤ a.toNat ∧ a.toNat < 0xa0000000)
    (hmain : MainSpecT env (liftProg fns) L.main.idx need) : HaltsSafely img := by
  intro words s hw hl
  have ⟨hpc, hc, hdata, hin, h10, hcap⟩ := hl
  have hwin : Windows env stackTop s :=
    ⟨by decide, henv.1, by rw [show env.next s = heapStart from hdata _ hnext]; decide, henv.2.1, henv.2.2,
      fun a ha => hcode a (by rw [← hc]; exact ha)⟩
  have hbase : fn.base = L.base := by
    rw [getElem?_liftProg hg] at hstart
    exact congrArg Lfundef.addr (Option.some.inj hstart)
  exact halts_of_lift hok hg (by rw [hpc, hbase, hentry]) (codeAt_of_loaded hfns hl) (fun _ h => h)
    (Start.total env (liftProg fns) gs L hstart hL hstack hheap hmain hw (hstatic s hdata)
      ⟨h10, hcap, hin, hdata _ hnext⟩ hwin)

end Rv64mc

/-- info: 'Rv64mc.haltsSafely_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.haltsSafely_of_main
