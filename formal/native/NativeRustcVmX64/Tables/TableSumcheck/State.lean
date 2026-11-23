module

public import NativeRustcVmX64.Tables.TableSumcheck.Exec
public import NativeRustcVmX64.Tables.TableSumcheck.Model
public import NativeRustcVm.Tables.Same
public import NativeRustcVmX64.Tables.TableTerms.Lemmas

/-!
# `table_sumcheck`: its states and what every step uses (x86-64)

From the entry `m0`: the 736-byte frame at `fb m0` (`F = 736`, RSP at offset `40` in the body),
the outputs (`outs`: the `TState`, the evaluations' entries), the inputs (heights, bus, powers) as
at the entry in a body (`same_readIn`, `heights_bd`, `bus_bd`), the stack arguments (`arg_word`),
the context for the callees (`ctx`), a block's environment (`E`) and start (`match_body`), the
frame's words (`FW`). The precondition's parts by name (`Pre.*`).
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The function's stack. -/
abbrev N : Nat := tableSumcheckStack

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 736

/-- The stack arguments' address. -/
abbrev argA (m0 : MachineData) : BitVec 64 := rspOf m0 + 8#64

abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev hA (m0 : MachineData) : BitVec 64 := reg m0 .rsi
abbrev bA (m0 : MachineData) : BitVec 64 := reg m0 .rdx
abbrev cpA (m0 : MachineData) : BitVec 64 := reg m0 .rcx
abbrev fpA (m0 : MachineData) : BitVec 64 := reg m0 .r8
abbrev ev (m0 : MachineData) : BitVec 64 := stackArg m0 1

/-- The outputs: the `TState`, the evaluations' entries. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (tA m0) tstateBytes q ∨ NativeRustcVm.InRange (ev m0) tableEvalsBytes q

/-- The regions the function writes, as `ReadIn` lists them. -/
def wsL (m0 : MachineData) : List NativeRustcVm.Region :=
  [⟨tA m0, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩]

/-- The target. -/
def tgt (m0 : MachineData) : EW := ewArg (reg m0 .r9) (stackArg m0 0)

/-- The model's result. -/
def res (s : TState) (heights : Array Nat) (bus : BusResultW) (m0 : MachineData) :
    Option (Array (Array EW × Array EW) × TState) :=
  (tableSumcheck heights bus.forms (arrE m0 (cpA m0) 2) (arrE m0 (fpA m0) 3) bus.point
    (tgt m0)).run s

/-- What `table_sumcheck` reaches. -/
abbrev Goal [Labels] (a : DecArea) (s : TState) (heights : Array Nat) (bus : BusResultW)
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
    TableSumcheckPost a s heights bus m0 st.data

/-- A block's environment: the frame, then `rest`. -/
abbrev E (m0 d : MachineData) (rest : List (BitVec 64 × Nat)) (ret : BitVec 64) : Env :=
  frameEnv m0 d 736 rest (fun _ ↦ 0) ret

/-- The frame's words `L` (offset, value). -/
def FW (m0 d : MachineData) (L : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ L, NativeRustcVm.WordAt d.dmem (off (fb m0) p.1) p.2

end

/-! ## The precondition's parts -/

namespace Pre

public section

variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} (h : TableSumcheckPre a s heights bus m0)
include h

theorem stack : StackOk m0 N := h.1
theorem rc : RcAt m0 N := h.2.1
theorem tables : TablesAt m0 N := h.2.2.1
theorem args : ArgsOk m0 2 := h.2.2.2.1
theorem ts : TStateAt m0.dmem (tA m0) a s := h.2.2.2.2.1
theorem tok : TStateOk m0 (tA m0) a N := h.2.2.2.2.2.1
theorem evs : OutOk m0 (tA m0) a (ev m0) tableEvalsBytes N := h.2.2.2.2.2.2.1
theorem t_arg : NativeRustcVm.Apart (tA m0) tstateBytes (argA m0) 16 := h.2.2.2.2.2.2.2.1
theorem ev_arg : NativeRustcVm.Apart (ev m0) tableEvalsBytes (argA m0) 16 := h.2.2.2.2.2.2.2.2.1
theorem rt : RodataApart (tA m0) tstateBytes := h.2.2.2.2.2.2.2.2.2.1
theorem re : RodataApart (ev m0) tableEvalsBytes := h.2.2.2.2.2.2.2.2.2.2.1
theorem hs : ReadIn m0 (hA m0) 48 N (wsL m0) := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem hts : HeightsAt m0.dmem (hA m0) heights := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bs : ReadIn m0 (bA m0) busBytes N (wsL m0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bw : BusWAt m0.dmem (bA m0) bus := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem cp : ReadIn m0 (cpA m0) 32 N (wsL m0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem fp : ReadIn m0 (fpA m0) 48 N (wsL m0) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem got : GotAt m0 N [(tA m0, tstateBytes), (a.words, 8 * a.len), (ev m0, tableEvalsBytes),
    (argA m0, 16), (hA m0, 48), (bA m0, busBytes), (cpA m0, 32), (fpA m0, 48),
    (rcAddr, 192), (rodataAddr .tables, NativeRustcVm.Data.Item.tables.bytes.length)] ["memcpy"] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end

end Pre

public section

theorem N_ge : 736 + tableTermsStack ≤ N ∧ 720 + sumcheckPlainStack ≤ N ∧
    704 + tableWeightsStack ≤ N := by
  unfold N tableSumcheckStack; omega

theorem slots_le : ∀ p ∈ slots, 688 ≤ p.1 ∧ p.1 + 8 ≤ 736 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

/-- The frame's words of a body kept by a call at offset `o` changing `Ro` and its stack. -/
theorem keepW_call' {m0 d d' : MachineData} {R : BitVec 64 → Prop} {o : Nat}
    (hb : Bd m0 736 N slots R o d) (hst : StackOk m0 N) (ho : o ≤ 736) {n' : Nat}
    (hn : 736 - o + n' ≤ N) {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d n') n' q))
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, o + 8 ≤ p.1 ∧ p.1 + 8 ≤ 744)
    (hRo : ∀ p ∈ L, ∀ i < 8, ¬ Ro (off (fb m0) (p.1 + i))) (h : FW m0 d L) : FW m0 d' L :=
  fun p hp ↦ keepW_call hb hst (by unfold N tableSumcheckStack; omega) ho hn hso (hL p hp).1
    (hL p hp).2 (hRo p hp) (h p hp)

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

theorem ctxF (h : TableSumcheckPre a s heights bus m0) {F : Nat} (hF : F ≤ N) :
    Ctx m0 (tA m0) a N F :=
  ⟨Pre.stack h, Pre.rc h, Pre.tok h, (Pre.ts h).footprint, hF⟩

theorem ctx (h : TableSumcheckPre a s heights bus m0) : Ctx m0 (tA m0) a N 736 :=
  ctxF h (by unfold N tableSumcheckStack; omega)

theorem spN (h : TableSumcheckPre a s heights bus m0) : N ≤ (rspOf m0).toNat := (Pre.stack h).1
theorem sp8 (h : TableSumcheckPre a s heights bus m0) : (rspOf m0).toNat + 8 ≤ 2 ^ 64 :=
  (Pre.stack h).2.1

theorem stack_noWrap (h : TableSumcheckPre a s heights bus m0) :
    NativeRustcVm.NoWrap (stackBelow m0 N) (N + 8) := noWrap_stackBelow (Pre.stack h)

theorem stk (h : TableSumcheckPre a s heights bus m0) :
    (stackBelow m0 N).toNat = (rspOf m0).toNat - N := stackBelow_toNat (spN h)

theorem fb_toNat (h : TableSumcheckPre a s heights bus m0) :
    (fb m0).toNat = (rspOf m0).toNat - 736 :=
  stackBelow_toNat (by have := spN h; unfold N tableSumcheckStack at this; omega)

theorem argA_toNat (h : TableSumcheckPre a s heights bus m0) :
    (argA m0).toNat = (rspOf m0).toNat + 8 := by
  have := (Pre.args h).2
  exact NativeRustcVm.toNat_add_ofNat (by omega)

theorem args_noWrap (h : TableSumcheckPre a s heights bus m0) :
    NativeRustcVm.NoWrap (argA m0) 16 := by
  have := (Pre.args h).2
  unfold NativeRustcVm.NoWrap
  rw [argA_toNat h]
  omega

theorem ev_noWrap (h : TableSumcheckPre a s heights bus m0) :
    NativeRustcVm.NoWrap (ev m0) tableEvalsBytes := (Pre.evs h).2.1

theorem fr_stack (h : TableSumcheckPre a s heights bus m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 736) 736 q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q :=
  inRange_frame_stack (Pre.stack h).2.1 (Pre.stack h).1 (by unfold N tableSumcheckStack; omega) hq

/-- An output is not a byte of the stack or the return address. -/
theorem outs_not_stack (h : TableSumcheckPre a s heights bus m0) {q : BitVec 64}
    (hq : outs m0 q) : ¬ NativeRustcVm.InRange (stackBelow m0 N) (N + 8) q := by
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.tok h).1 (Pre.ts h).footprint.1.2 (stack_noWrap h) hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.evs h).2.2.2.2.1 (ev_noWrap h) (stack_noWrap h) hq

theorem outs_not_stackN (h : TableSumcheckPre a s heights bus m0) {q : BitVec 64}
    (hq : outs m0 q) : ¬ NativeRustcVm.InRange (stackBelow m0 N) N q :=
  fun h' ↦ outs_not_stack h hq (inRange_mono h' (by omega))

/-- An output is not a byte of the frame. -/
theorem outs_not_frame (h : TableSumcheckPre a s heights bus m0) {q : BitVec 64}
    (hq : outs m0 q) : ¬ NativeRustcVm.InRange (fb m0) 744 q := by
  intro hf
  apply outs_not_stack h hq
  have hnw := stack_noWrap h
  have e := stk h
  have ef := fb_toNat h
  have h1 := spN h; have h2 := sp8 h
  have hN : 736 ≤ N := by unfold N tableSumcheckStack; omega
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [ef]; omega), ef] at hf
  rw [inRange_iff' hnw, e]
  omega

/-- An output is not a round constant. -/
theorem outs_not_rc (h : TableSumcheckPre a s heights bus m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange rcAddr 192 q := by
  have c := ctx h
  rcases hq with hq | hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (Pre.evs h) hq

/-- An output is not a byte of an input. -/
theorem outs_not_in (h : TableSumcheckPre a s heights bus m0) {x : BitVec 64} {n : Nat}
    (hr : ReadIn m0 x n N (wsL m0)) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange x n q := by
  intro hx
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange (hr.2.2 ⟨tA m0, tstateBytes⟩ (by simp [wsL])) hr.1.2
      (Pre.ts h).footprint.1.2 hx hq
  · exact NativeRustcVm.Apart.not_inRange (hr.2.2 ⟨ev m0, tableEvalsBytes⟩ (by simp [wsL]))
      hr.1.2 (ev_noWrap h) hx hq

/-- **An input** in a body: its bytes the entry's. -/
theorem same_in (h : TableSumcheckPre a s heights bus m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) o d) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.NoWrap x n) (hst : NativeRustcVm.Apart x n (stackBelow m0 N) (N + 8))
    (hout : ∀ q, outs m0 q → ¬ NativeRustcVm.InRange x n q) : Same m0.dmem d.dmem x n :=
  Same.of_sameOutside hb.same fun j hj hq ↦ by
    have hin : NativeRustcVm.InRange x n (x + BitVec.ofNat 64 j) :=
      NativeRustcVm.inRange_add hj (by unfold NativeRustcVm.NoWrap at hx; omega)
    rcases hq with hq | hq
    · exact hout _ hq hin
    · exact NativeRustcVm.Apart.not_inRange hst hx (stack_noWrap h) hin (inRange_mono hq (by omega))

theorem same_readIn (h : TableSumcheckPre a s heights bus m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) o d) {x : BitVec 64} {n : Nat}
    (hr : ReadIn m0 x n N (wsL m0)) : Same m0.dmem d.dmem x n :=
  same_in h hb hr.1.2 hr.2.1 fun _ hq ↦ outs_not_in h hr hq

/-- **The stack arguments** in a body. -/
theorem args_same (h : TableSumcheckPre a s heights bus m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) o d) : Same m0.dmem d.dmem (argA m0) 16 := by
  refine same_in h hb (args_noWrap h) ?_ fun q hq hx ↦ ?_
  · unfold NativeRustcVm.Apart
    rw [argA_toNat h, stk h]
    have := spN h
    omega
  · rcases hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange (Pre.t_arg h) (Pre.ts h).footprint.1.2
        (args_noWrap h) hq hx
    · exact NativeRustcVm.Apart.not_inRange (Pre.ev_arg h) (ev_noWrap h) (args_noWrap h) hq hx

/-- **Stack argument `j`** in a body. -/
theorem arg_word (h : TableSumcheckPre a s heights bus m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) o d) {j : Nat} (hj : j < 2) :
    (wordOf d.dmem (argA m0 + BitVec.ofNat 64 (8 * j))).toBitVec = stackArg m0 j := by
  have hs := (args_same h hb).sub (o := 8 * j) (k := 8) (by omega)
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ hs i hi]
  unfold stackArg argA
  rw [NativeRustcVm.addr_add_add (rspOf m0) 8 (8 * j)]

/-- The heights in a body. -/
theorem heights_bd (h : TableSumcheckPre a s heights bus m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) o d) : HeightsAt d.dmem (hA m0) heights := by
  have hH := Pre.hts h
  refine ⟨hH.1, hH.2.1, WordsAt.of_same hH.2.2 (same_readIn h hb (Pre.hs h)) ?_⟩
  simp [hH.1, nTables]

/-- The bus's result in a body. -/
theorem bus_bd (h : TableSumcheckPre a s heights bus m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) o d) : BusWAt d.dmem (bA m0) bus :=
  BusWAt.of_same (Pre.bw h) (same_readIn h hb (Pre.bs h))

/-- A region apart from the stack is apart from the frame. -/
theorem frame_ap (h : TableSumcheckPre a s heights bus m0) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 N) (N + 8)) :
    NativeRustcVm.Apart (stackBelow m0 736) (736 + 8) x n :=
  Apart.symm' (apart_frame hx (spN h) (by unfold N tableSumcheckStack; omega))

theorem frame_args (h : TableSumcheckPre a s heights bus m0) :
    NativeRustcVm.Apart (stackBelow m0 736) (736 + 8) (argA m0) 16 := by
  unfold NativeRustcVm.Apart
  rw [argA_toNat h, fb_toNat h]
  have := spN h
  unfold N tableSumcheckStack at this
  omega

theorem wf_nil (h : TableSumcheckPre a s heights bus m0) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} : (E m0 d [] ret).WF :=
  frame_wf' (Pre.stack h) (by unfold N tableSumcheckStack; omega) hk (by simp)
    (List.pairwise_singleton _ _)

theorem wf_one (h : TableSumcheckPre a s heights bus m0) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {x : BitVec 64} {n : Nat} (hm : NativeRustcVm.Mapped m0.dmem x n)
    (hnw : NativeRustcVm.NoWrap x n) (hap : NativeRustcVm.Apart (stackBelow m0 736) (736 + 8) x n)
    {ret : BitVec 64} : (E m0 d [(x, n)] ret).WF :=
  frame_wf' (Pre.stack h) (by unfold N tableSumcheckStack; omega) hk (fun y hy ↦ by
    rw [List.mem_singleton] at hy; subst hy; exact ⟨hm, hnw⟩) (List.pairwise_pair.mpr hap)

/-- **A body block's start**: RSP at the frame's offset `o`, the aliases. -/
theorem match_body {d : MachineData} {R : BitVec 64 → Prop} {o : Nat}
    (hb : Bd m0 736 N slots R o d) {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {sizes : List Nat} {aliases : List (Sym × Nat × Int)}
    (hr : RegionsOk sizes ((stackBelow m0 736, 736 + 8) :: rest))
    (hal : AllOf (fun p ↦ p.1.eval (E m0 d rest ret) =
      (E m0 d rest ret).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Match (E m0 d rest ret) (init sizes [(.rsp, .ptr 0 (o : Int))] [] [] aliases) d :=
  match_ofMachine hr ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial hal

/-- **A block of the body**, its writes in the frame. -/
theorem blockB (h : TableSumcheckPre a s heights bus m0) {d d' : MachineData} {o o' : Nat}
    (hb : Bd m0 736 N slots (outs m0) o d) {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hwf : (E m0 d rest ret).WF) (hm : Match (E m0 d rest ret) Sy d')
    (hmid : MidOk 736 o' slots Sy = true) (hW : WrOk Sy [] = true) :
    Bd m0 736 N slots (outs m0) o' d' ∧
      NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (stackBelow m0 736) 736) := by
  refine ⟨hb.step (Pre.stack h) (by unfold N tableSumcheckStack; omega) hwf hm hmid
    (fun p hp ↦ (slots_le p hp).2) hW nofun, ?_⟩
  exact NativeRustcVm.SameOutside.mono (same_block hwf hm (writesIn_of_mid hmid)
    (belowRet_of_mid hmid) hW (X := fun _ ↦ False) nofun) fun q hq ↦ hq.elim id False.elim

/-- A word of the frame loaded. -/
theorem ld0 {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (off (fb m0) o) w) :
    (Sym.load 0 o 8).eval (E m0 d rest ret) = w.toBitVec :=
  NativeRustcVmX64.Tables.TableTerms.load0 h

/-- A frame word a block wrote. -/
theorem wroteW {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hm : Match (E m0 d rest ret) Sy d') {o : Nat} (hle : o + 8 ≤ 744) {v : Sym}
    (hw : WordW 0 o v Sy) {w : UInt64} (hv : v.eval (E m0 d rest ret) = w.toBitVec) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) o) w :=
  wordAt_written hm (r := 0) rfl hle hw hv

/-- **At a call** from the body at offset `o`. -/
theorem Bd.atO (h : TableSumcheckPre a s heights bus m0) {d : MachineData} {o : Nat} (ho : o ≤ 736)
    (hb : Bd m0 736 N slots (outs m0) o d) : At m0 (736 - o) d :=
  ⟨by rw [hb.rsp_at ho], hb.fr.kept, fun i hi ↦ hb.same _ fun hq ↦ by
    have hin : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
      inRange_off_self hi (by omega)
    rcases hq with hq | hq
    · exact outs_not_rc h hq hin
    · exact (ctx h).not_rc_stack hq hin⟩

theorem got_call (h : TableSumcheckPre a s heights bus m0) {d : MachineData} {o Nc : Nat}
    (hb : Bd m0 736 N slots (outs m0) o d) (ho : o ≤ 736) (hle : 736 - o + Nc ≤ N)
    {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ ["memcpy"], ∀ b ∈ areas, Apart (gotAddr l) 8 b.1 b.2) :
    GotAt d Nc areas ["memcpy"] := by
  refine got_callee (Pre.got h) (got_keep (Pre.got h) (Pre.stack h)
    (writes := [(tA m0, tstateBytes), (ev m0, tableEvalsBytes)])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> simp)
    (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (Pre.ts h).footprint.1.2
      · exact (Pre.evs h).2.1)
    (by simpa [outs, or_assoc] using hb.same))
    (Bd.atO h ho hb).sp (spN h) hle ha

/-- The frame's bytes `lo` to `lo + len` are in the stack. -/
theorem loc_stack (h : TableSumcheckPre a s heights bus m0) {lo len : Nat} (hl : lo + len ≤ 736)
    {q : BitVec 64} (hq : NativeRustcVm.InRange (off (fb m0) lo) len q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q := by
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) (Pre.stack h) (by unfold N tableSumcheckStack; omega)
  refine fr_stack h ?_
  rcases Nat.eq_zero_or_pos len with h0 | h0
  · subst h0; unfold NativeRustcVm.InRange at hq; omega
  have hnw' : NativeRustcVm.NoWrap (off (fb m0) lo) len := by
    unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega
  rw [inRange_iff' hnw', toNat_off (by omega)] at hq
  show NativeRustcVm.InRange (fb m0) 736 q
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
  omega

/-- **A call at offset `o`** whose callee changes outputs, parts of the frame below the slots and
its stack. -/
theorem call_frame (h : TableSumcheckPre a s heights bus m0) {d d' : MachineData} {o : Nat}
    (hb : Bd m0 736 N slots (outs m0) o d) (ho : o ≤ 40) {Nc : Nat} (hn : 736 - o + Nc ≤ N)
    (hs : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64) {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    (hRo : ∀ q, Ro q → outs m0 q ∨
      ∃ lo len, lo + len ≤ 688 ∧ NativeRustcVm.InRange (off (fb m0) lo) len q) :
    Bd m0 736 N slots (outs m0) (o + 8) d' := by
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hnot : ∀ j, 688 ≤ j → j < 744 → ¬ (Ro (off (fb m0) j) ∨
      NativeRustcVm.InRange (stackBelow d Nc) Nc (off (fb m0) j)) := by
    rintro j hj1 hj2 (hq | hq)
    · rcases hRo _ hq with hq | ⟨lo, len, hl, hq⟩
      · exact outs_not_frame h hq (inRange_off_self hj2 (by omega))
      · rcases Nat.eq_zero_or_pos len with h0 | h0
        · subst h0; unfold NativeRustcVm.InRange at hq; omega
        rw [inRange_off_iff (by omega) (by omega)] at hq
        omega
    · exact (hb.callee_in hS (by omega) hn hq).2
        ((inRange_off_iff (by omega) (by omega)).mpr ⟨by omega, by omega⟩)
  refine hb.call_at hs hrsp hso (fun q hq ↦ ?_) (fun p hp i hi ↦ ?_) (fun j hj ↦ ?_)
  · rcases hq with hq | hq
    · rcases hRo q hq with hq | ⟨lo, len, hl, hq⟩
      · exact .inl hq
      · exact .inr (loc_stack h (by omega) hq)
    · exact .inr (hb.callee_in hS (by omega) hn hq).1
  · have := slots_le p hp
    exact hnot _ (by omega) (by omega)
  · exact hnot _ (by omega) (by omega)

end

end

end NativeRustcVmX64.Tables.TableSumcheck
