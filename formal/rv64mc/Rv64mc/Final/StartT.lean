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

  Both are instances of `Start.totalWith` and `halts_of_main_with`, over `main`'s stopping set
  `Stop words` and the exit codes `V words` the run may end with (`EndsWith`), given that `V
  words` holds of `0`, of `1` and of `a0` in `Stop words`: `MainSpecB`'s instance gives
  `BoolVerdict` (`Final/Headline.lean`).
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

/-- Where the whole run may end: inside the program (not returned from `_start`), with `a0` in `V`. -/
def EndsWith (V : Word → Prop) (s : State rvIsa) : Prop := s.stack ≠ [] ∧ V (s.regs .x10)

namespace Start

/-- **`_start` is total**, at Lprog, from a total contract of `main` on the input `words` with stopping set
    `Stop`: the run ends inside the program with `a0` in `V`, where `V` holds of `main`'s returns `0` and `1` and of
    `a0` wherever `main` may stop. -/
theorem totalWith (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Start.Link)
    (hp : p[i]? = some (Gen.Start.tmpl L)) (hL : Gen.Start.Link.WF p L) {need : Nat}
    (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    {words : List Word} {Stop : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    {V : Word → Prop} (h0 : V 0) (h1 : V 1) (hV : ∀ regs m r' m', Stop regs m r' m' → V (r' .x10))
    (hmain : HoldsT env p L.main.idx need (MainPre env words) MainPostT (Stop := Stop))
    {regs : Reg → Word} {m : MachineState} (hst : env.Static m) (hpre : MainPre env words regs m)
    (hwin : Windows env stackTop m) {ret top : Word} :
    rvIsa.Total p stmtCtx (WinOk p) (EndsWith V) ⟨[⟨i, 0, ret, top⟩], regs, m⟩ := by
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
  refine HoldsT.call hmain hp rfl (callee_site hL.main hL.s0 (by simp [updReg_apply, Expr.eval]))
    ?_ hst (by rw [hnx]; exact hheap) ⟨by simpa [updReg_apply] using h10, hcap, hin, hnx⟩ ?_ ?_
    (fun _ _ _ _ hs _ => ⟨nofun, hV _ _ _ _ hs⟩) ?_
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
    · simpa [h] using h0
    · simpa [h] using h1

/-- **`_start` is total**, at Lprog, from `main`'s total contract: from its entry, with an input of fewer than
    `maxInputWords` words in memory and its length in `a0`, `NEXT` at the heap's start, the static data in place and
    the windows where `Windows` says at `main`'s stack top, the run ends inside the program with `a0` a verdict. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Start.Link)
    (hp : p[i]? = some (Gen.Start.tmpl L)) (hL : Gen.Start.Link.WF p L) {need : Nat}
    (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    (hmain : MainSpecT env p L.main.idx need) {words : List Word} (hw : words.length < maxInputWords)
    {regs : Reg → Word} {m : MachineState} (hst : env.Static m) (hpre : MainPre env words regs m)
    (hwin : Windows env stackTop m) {ret top : Word} :
    rvIsa.Total p stmtCtx (WinOk p) Ends ⟨[⟨i, 0, ret, top⟩], regs, m⟩ :=
  totalWith env p i L hp hL hstack hheap (.inl rfl) (.inr (.inl rfl)) (fun _ _ _ _ h2 => .inr (.inr h2))
    (hmain words hw) hst hpre hwin

end Start

/-- **Every run ends with `a0` in `V words`**, from a total contract of `main` with stopping set `Stop words` on
    every input of fewer than `maxInputWords` words, with `sound_of_main`'s facts about the image. -/
theorem halts_of_main_with {img : Image} {fns : List Fn} {env : Env} {need gs : Nat} {fn : Fn}
    {L : Gen.Start.Link} (hok : ProgOk fns) (hfns : FnsIn img fns) (hg : fns[gs]? = some fn)
    (hstart : (liftProg fns)[gs]? = some (Gen.Start.tmpl L)) (hentry : L.base = img.entry)
    (hL : Gen.Start.Link.WF (liftProg fns) L)
    (hstatic : ∀ m : MachineState, (∀ p ∈ img.data, m.getMem p.1 = p.2) → env.Static m)
    (hnext : (env.nextAddr, heapStart) ∈ img.data) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat)
    (henv : 0xa0000000 ≤ env.nextAddr.toNat ∧ env.nextAddr.toNat % 8 = 0 ∧ env.heapEnd.toNat ≤ 0x78000000 ∧
      ∀ q ∈ env.data, inWindow q.1 8 = true ∧ q.1.toNat % 8 = 0)
    (hcode : ∀ a, img.codeAt a ≠ none → 0x78000000 ≤ a.toNat ∧ a.toNat < 0xa0000000)
    {Stop : List Word → (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    {V : List Word → Word → Prop} (hV : ∀ words, V words 0 ∧ V words 1)
    (hSV : ∀ words regs m r' m', Stop words regs m r' m' → V words (r' .x10))
    (hmain : ∀ words : List Word, words.length < maxInputWords →
      HoldsT env (liftProg fns) L.main.idx need (MainPre env words) MainPostT (Stop := Stop words))
    {words : List Word} {s : MachineState} (hw : words.length < maxInputWords) (hl : Loaded img words s) :
    ∃ n v, Halts s n v ∧ V words v := by
  have ⟨hpc, hc, hdata, hin, h10, hcap⟩ := hl
  have hwin : Windows env stackTop s :=
    ⟨by decide, henv.1, henv.2.1, by rw [show env.next s = heapStart from hdata _ hnext]; decide, henv.2.2.1,
      henv.2.2.2, fun a ha => hcode a (by rw [← hc]; exact ha)⟩
  have hbase : fn.base = L.base := by
    rw [getElem?_liftProg hg] at hstart
    exact congrArg Lfundef.addr (Option.some.inj hstart)
  exact halts_of_lift hok hg (by rw [hpc, hbase, hentry]) (codeAt_of_loaded hfns hl) (fun _ h => h)
    (Start.totalWith env (liftProg fns) gs L hstart hL hstack hheap (hV words).1 (hV words).2 (hSV words)
      (hmain words hw) (hstatic s hdata) ⟨h10, hcap, hin, hdata _ hnext⟩ hwin)

/-- **`HaltsSafely` from `main`'s total contract**, with `sound_of_main`'s facts about the image. -/
theorem haltsSafely_of_main {img : Image} {fns : List Fn} {env : Env} {need gs : Nat} {fn : Fn}
    {L : Gen.Start.Link} (hok : ProgOk fns) (hfns : FnsIn img fns) (hg : fns[gs]? = some fn)
    (hstart : (liftProg fns)[gs]? = some (Gen.Start.tmpl L)) (hentry : L.base = img.entry)
    (hL : Gen.Start.Link.WF (liftProg fns) L)
    (hstatic : ∀ m : MachineState, (∀ p ∈ img.data, m.getMem p.1 = p.2) → env.Static m)
    (hnext : (env.nextAddr, heapStart) ∈ img.data) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat)
    (henv : 0xa0000000 ≤ env.nextAddr.toNat ∧ env.nextAddr.toNat % 8 = 0 ∧ env.heapEnd.toNat ≤ 0x78000000 ∧
      ∀ q ∈ env.data, inWindow q.1 8 = true ∧ q.1.toNat % 8 = 0)
    (hcode : ∀ a, img.codeAt a ≠ none → 0x78000000 ≤ a.toNat ∧ a.toNat < 0xa0000000)
    (hmain : MainSpecT env (liftProg fns) L.main.idx need) : HaltsSafely img :=
  fun _ _ hw hl => halts_of_main_with hok hfns hg hstart hentry hL hstatic hnext hheap hstack henv hcode
    (Stop := fun _ => MainStopT) (V := fun _ => IsVerdict) (fun _ => ⟨.inl rfl, .inr (.inl rfl)⟩)
    (fun _ _ _ _ _ h2 => .inr (.inr h2)) hmain hw hl

end Rv64mc

/-- info: 'Rv64mc.haltsSafely_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.haltsSafely_of_main

/-- info: 'Rv64mc.halts_of_main_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.halts_of_main_with
