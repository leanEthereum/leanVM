module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Exec
public import NativeRustcVmX64.Bus.VerifyBusBalance.Model
public import NativeRustcVmX64.Bus.GkrCommon
public import NativeRustcVmX64.Bus.Common
public import NativeRustcVm.Tables.Same
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public import NativeRustcX64.Got

/-!
# `verify_bus_balance`'s frame, its exits (x86-64)

The 5520-byte frame below the entry's RSP (`fb m0`, its byte `j` at `loc m0 j`), the slots from
`5472`; RSP at `104` in the body. The outputs (`outs`): the `TState` (RDI), the bus (R8), the
claims (R9). A state of the body is `St m0 o d` (`Gkr.Fr`: the frame, memory changed only in the
stack and the outputs).

- `St.blk`, `keepB`, `keepC`: a block keeps `St`; a block's or a call's changes keep the frame's
  bytes they miss.
- `test_spec`: a test block (`TestOk`) branching to the failure.
- `exit_spec`, `fail_spec`: the epilogue (`b57`), the failure (`b56`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- The stack `verify_bus_balance` uses. -/
abbrev NN : Nat := verifyBusBalanceStack

/-- The outputs: the `TState` (RDI), the bus (R8), the claims (R9). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨ NativeRustcVm.InRange (reg m0 .r8) busBytes q ∨
    NativeRustcVm.InRange (reg m0 .r9) claimsBytes q

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 5520

/-- The frame's byte `j`. -/
abbrev loc (m0 : MachineData) (j : Nat) : BitVec 64 := off (fb m0) j

/-- A state of the body, RSP at the frame's offset `o`. -/
abbrev St (m0 : MachineData) (o : Nat) (d : MachineData) : Prop :=
  Fr m0 5520 NN slots (outs m0) o d

end

public section

theorem N_ge : 5520 ≤ NN := by decide
theorem le_bl : 5424 + busLayoutStack ≤ NN := by decide
theorem le_len : 5424 + bitLengthStack ≤ NN := by decide
theorem le_grind : 5424 + grindStack ≤ NN := by decide
theorem le_samp : 5424 + sampleChallengesStack ≤ NN := by decide
theorem le_sq : 5424 + squeezeStack ≤ NN := by decide
theorem le_gkr : 5424 + verifyGkrStack ≤ NN := by decide
theorem le_rss : 5424 + readScalarsStack ≤ NN := by decide
theorem le_rs : 5424 + readScalarStack ≤ NN := by decide
theorem le_pc : 5424 + pushClaimStack ≤ NN := by decide
theorem le_share : 5424 + bytecodeShareStack ≤ NN := by decide
theorem le_cbv : 5424 + computedBytecodeValueStack ≤ NN := by decide
theorem le_kpow : 5424 + kpowStack ≤ NN := by decide
theorem le_fp : 5440 + fpClosureStack ≤ NN := by decide
theorem le_acc : 5520 + accumulateSideStack ≤ NN := by decide
theorem le_ext : 5424 + bufEWExtendStack ≤ NN := by decide
theorem le_mem : 5424 + 0 ≤ NN := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 5520 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_ge : ∀ p ∈ slots, 5472 ≤ p.1 := by decide

/-- The slots above a call at `c` and a local `[lo, lo + len)`. -/
theorem slots_call {c lo len : Nat} (h1 : c ≤ 5472) (h2 : lo + len ≤ 5472) :
    ∀ p ∈ slots, c ≤ p.1 ∧ lo + len ≤ p.1 ∧ p.1 + 8 ≤ 5520 := fun p hp ↦
  ⟨by have := slots_ge p hp; omega, by have := slots_ge p hp; omega, slots_le p hp⟩

/-- A block's leading label is the code's directive at the block's index. -/
theorem label_of_infix {F ds : List Directive} {j : Nat} {l : Label} (h : ds.IsInfixAt F j)
    (h0 : ds[0]? = some (.label l)) : F[j]? = some (.label l) := by
  obtain ⟨t, ht⟩ := h
  have hd : ds ≠ [] := fun he ↦ by rw [he] at h0; cases h0
  have : (F.drop j)[0]? = ds[0]? := by
    rw [← ht, List.getElem?_append_left (List.length_pos_of_ne_nil hd)]
  rw [List.getElem?_drop, Nat.add_zero, h0] at this
  exact this

end

/-! ## The precondition's parts -/

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

section
variable (h : VerifyBusBalancePre a s0 L m0)
include h

theorem pre_stack : StackOk m0 NN := h.1
theorem pre_rc : RcAt m0 NN := h.2.1
theorem pre_ro : RodataAt m0 NN := h.2.2.1
theorem pre_ts : TStateAt m0.dmem (reg m0 .rdi) a s0 := h.2.2.2.1
theorem pre_tok : TStateOk m0 (reg m0 .rdi) a NN := h.2.2.2.2.1
theorem pre_lay : LayoutWAt m0.dmem (reg m0 .rsi) L := h.2.2.2.2.2.1
theorem pre_layOk : InOk m0 (reg m0 .rsi) layoutBytes NN := h.2.2.2.2.2.2.1
theorem pre_layT : Apart (reg m0 .rsi) layoutBytes (reg m0 .rdi) tstateBytes :=
  h.2.2.2.2.2.2.2.1
theorem pre_n : L.bytecode.size = (reg m0 .rcx).toNat := h.2.2.2.2.2.2.2.2.1
theorem pre_bc : NativeRustcVm.WordsAt m0.dmem (reg m0 .rdx) L.bytecode.toList :=
  h.2.2.2.2.2.2.2.2.2.1
theorem pre_bcR : Readable m0 (reg m0 .rdx) (8 * (reg m0 .rcx).toNat) := h.2.2.2.2.2.2.2.2.2.2.1
theorem pre_bcS : 0 < (reg m0 .rcx).toNat →
    OffStack m0 (reg m0 .rdx) (8 * (reg m0 .rcx).toNat) NN := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_bus : OutOk m0 (reg m0 .rdi) a (reg m0 .r8) busBytes NN :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_busR : RodataApart (reg m0 .r8) busBytes := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_busL : Apart (reg m0 .r8) busBytes (reg m0 .rsi) layoutBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_busB : 0 < (reg m0 .rcx).toNat →
    Apart (reg m0 .r8) busBytes (reg m0 .rdx) (8 * (reg m0 .rcx).toNat) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_cl : OutOk m0 (reg m0 .rdi) a (reg m0 .r9) claimsBytes NN :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_clR : RodataApart (reg m0 .r9) claimsBytes := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_clL : Apart (reg m0 .r9) claimsBytes (reg m0 .rsi) layoutBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_clB : 0 < (reg m0 .rcx).toNat →
    Apart (reg m0 .r9) claimsBytes (reg m0 .rdx) (8 * (reg m0 .rcx).toNat) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_busCl : Apart (reg m0 .r8) busBytes (reg m0 .r9) claimsBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_tR : RodataApart (reg m0 .rdi) tstateBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem pre_bcT : 0 < (reg m0 .rcx).toNat →
    Apart (reg m0 .rdx) (8 * (reg m0 .rcx).toNat) (reg m0 .rdi) tstateBytes :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem pre_got :
    GotAt m0 NN ([(reg m0 .rdi, tstateBytes), (a.words, 8 * a.len),
      (reg m0 .rsi, layoutBytes), (reg m0 .r8, busBytes), (reg m0 .r9, claimsBytes),
      (rcAddr, 192)] ++
      (if (reg m0 .rcx).toNat = 0 then [] else [(reg m0 .rdx, 8 * (reg m0 .rcx).toNat)]) ++
      ([.tuples, .tables, .padding, .pushBlocks, .pullBlocks, .countBlocks, .one] :
        List NativeRustcVm.Data.Item).map (fun i => (rodataAddr i, i.bytes.length)))
      ["memcpy", "memset"] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The outputs and stack cannot overwrite loader slots. -/
theorem got_same {d : MachineData} {o : Nat} (fr : St m0 o d) :
    ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  refine got_keep (pre_got h) (pre_stack h)
    (writes := [(reg m0 .rdi, tstateBytes), (reg m0 .r8, busBytes), (reg m0 .r9, claimsBytes)])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> simp)
    (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact (pre_ts h).footprint.1.2
      · exact (pre_bus h).2.1
      · exact (pre_cl h).2.1)
    (NativeRustcVm.SameOutside.mono fr.same ?_)
  intro q hq
  rcases hq with hq | hq | hq | hq
  · exact .inr hq
  · exact .inl ⟨(reg m0 .rdi, tstateBytes), by simp, hq⟩
  · exact .inl ⟨(reg m0 .r8, busBytes), by simp, hq⟩
  · exact .inl ⟨(reg m0 .r9, claimsBytes), by simp, hq⟩

/-- A raw copy call's frame and read-only loader slot. -/
theorem wf_copy {d : MachineData} (hk : Kept m0.dmem d.dmem)
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 d 5520 [(gotAddr "memcpy", 8)] vars ret).WF :=
  Bus.wf1 (pre_stack h) N_ge hk
    ⟨(pre_got h).mapped (by simp), ((pre_got h).1 "memcpy" (by simp)).2.1⟩
    ((pre_got h).1 "memcpy" (by simp)).2.2.1

theorem match_copy {d : MachineData} (fr : St m0 104 d)
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    Match (frameEnv m0 d 5520 [(gotAddr "memcpy", 8)] vars ret) copyS d := by
  have hm := match_ofMachine (m := d)
    (regions := [(fb m0, 5528), (gotAddr "memcpy", 8)]) (vars := vars) (ret := ret)
    (sregions := [5528, 8]) (known := [(.rsp, .ptr 0 104)])
    (labels := []) (bounds := []) (aliases := [(.gotSlot "memcpy", 1, 0)])
    ⟨rfl, rfl, trivial⟩ ⟨fr.frame.rsp_eval, trivial⟩ trivial trivial
    ⟨(BitVec.add_zero _).symm, trivial⟩
  apply hm.withKnownBytes (r := 1) (off := 0) (n := 8) (v := .label "memcpy")
  intro i hi
  simp only [Env.ofMachine_mem0, Env.base_ofMachine_eq, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.map_some, Option.getD_some, Nat.zero_add, Sym.eval]
  rw [got_same h fr "memcpy" (by simp) i hi]
  exact (pre_got h).byte (by simp) hi

/-- The entry's context. -/
theorem ctx : Ctx m0 (reg m0 .rdi) a NN 5520 :=
  ⟨pre_stack h, pre_rc h, pre_tok h, (pre_ts h).footprint, N_ge⟩

theorem outs_not_rc : ∀ q, outs m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
  intro q hq
  have c := ctx h
  rcases hq with hq | hq | hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (pre_bus h) hq
  · exact c.out_not_rc (pre_cl h) hq

theorem outs_not_frame : ∀ q, outs m0 q → ¬ NativeRustcVm.InRange (fb m0) (5520 + 8) q := by
  intro q hq
  have c := ctx h
  rcases hq with hq | hq | hq
  · exact not_inRange_of_apart (apart_frame c.tok.1 c.spN N_ge) c.fp.1.2 c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame (pre_bus h).2.2.2.2.1 c.spN N_ge) (pre_bus h).2.1
      c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame (pre_cl h).2.2.2.2.1 c.spN N_ge) (pre_cl h).2.1
      c.noWrap_frame hq

theorem outs_not_stack : ∀ q, outs m0 q →
    ¬ NativeRustcVm.InRange (stackBelow m0 NN) NN q := by
  intro q hq
  have c := ctx h
  rcases hq with hq | hq | hq
  · exact fun h' ↦ (c.stack_not_t h').1 hq
  · exact fun h' ↦ c.out_not_stack (pre_bus h) hq h'
  · exact fun h' ↦ c.out_not_stack (pre_cl h) hq h'

/-- The `TState` kept where the memory changed in the stack, the bus or the claims. -/
theorem ts_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hk : Kept d d')
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨
      NativeRustcVm.InRange (reg m0 .r8) busBytes q ∨ NativeRustcVm.InRange (reg m0 .r9) claimsBytes q)
    {s : TState} (ht : TStateAt d (reg m0 .rdi) a s) : TStateAt d' (reg m0 .rdi) a s := by
  have c := ctx h
  refine ht.frame hk (fun q hq ↦ ?_) hs
  rcases hR q hq with hq | hq | hq
  · exact c.stack_not_t hq
  · exact c.out_not_t (pre_bus h) hq
  · exact c.out_not_t (pre_cl h) hq

/-- The frame's environment, no other region. -/
theorem wf0 {d : MachineData} (hk : Kept m0.dmem d.dmem) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : (frameEnv m0 d 5520 [] vars ret).WF :=
  Bus.wf0 (pre_stack h) N_ge hk

/-- The frame's environment with the bus as region 1. -/
theorem wfBus {d : MachineData} (hk : Kept m0.dmem d.dmem) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : (frameEnv m0 d 5520 [(reg m0 .r8, busBytes)] vars ret).WF :=
  Bus.wf1 (pre_stack h) N_ge hk ⟨(pre_bus h).1, (pre_bus h).2.1⟩ (pre_bus h).2.2.2.2.1

end

/-! ## Blocks and calls -/

/-- **A block keeps `St`**: its writes in the frame below the slots' top or the outputs. -/
theorem St.blk {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState} {o o' : Nat}
    {d d' : MachineData} (fr : St m0 o d) (hS : StackOk m0 NN)
    (hwf : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) S d')
    (hmid : MidOk 5520 o' slots S = true)
    (hW : ∀ q, Written (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) S q →
      NativeRustcVm.InRange (fb m0) 5520 q ∨ outs m0 q) : St m0 o' d' :=
  (fr.block hS N_ge hwf hm hmid slots_le hW).1

omit [Labels] in
/-- A block's writes in region `0`, within the frame. -/
theorem wr0 [Labels] {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState} {d : MachineData}
    (hS : StackOk m0 NN) {lo hi : Nat} (h0 : W0 lo hi S) (hhi : hi ≤ 5520) {q : BitVec 64}
    (hq : Written (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) S q) :
    NativeRustcVm.InRange (fb m0) 5520 q ∨ outs m0 q :=
  .inl (written_fb hS N_ge (fun w hw ↦ ⟨(h0 w hw).1, by have := h0 w hw; omega⟩) hq)

omit [Labels] in
/-- A block's writes in region `0`, within the frame, and in region `1`, an output. -/
theorem wr1 [Labels] {x : BitVec 64} {n : Nat} {ret : BitVec 64} {S : SState} {d : MachineData}
    (hS : StackOk m0 NN) {lo hi lo1 n' : Nat} (h0 : W01 lo hi lo1 n' S) (hhi : hi ≤ 5520) (hn : n' ≤ n)
    (hx : x.toNat + n ≤ 2 ^ 64) (hout : ∀ q, NativeRustcVm.InRange x n q → outs m0 q) {q : BitVec 64}
    (hq : Written (frameEnv m0 d 5520 [(x, n)] (fun _ ↦ 0) ret) S q) :
    NativeRustcVm.InRange (fb m0) 5520 q ∨ outs m0 q := by
  rcases written_fb1 hS N_ge (fun w hw ↦ (h0 w hw).elim (fun h ↦ .inl ⟨h.1, by omega⟩)
    fun h ↦ .inr ⟨h.1, by omega⟩) hx hq with h | h
  · exact .inl h
  · exact .inr (hout q h)

omit [Labels] in
/-- **The frame's bytes a block misses** are kept. -/
theorem keepB [Labels] {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    {d d' : MachineData} (hwf : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true)
    {j n : Nat} (hjn : j + n ≤ 5528)
    (hmiss : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ j ∨ j + n ≤ w.off) :
    Same d.dmem d'.dmem (loc m0 j) n := fun i hi ↦ by
  rw [off_add]
  exact hm.get?_mem0 hwf (not_written0 hwf hm hin (j := j + i) (by omega) fun w hw hr ↦ by
    rcases hmiss w hw hr with h | h
    · exact .inl (by omega)
    · exact .inr (by omega))

omit [Labels] in
theorem miss0 {S : SState} {lo hi j n : Nat} (h0 : W0 lo hi S) (hd : j + n ≤ lo ∨ hi ≤ j) :
    ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ j ∨ j + n ≤ w.off := fun w hw _ ↦ by
  have := h0 w hw; omega

omit [Labels] in
theorem miss01 {S : SState} {lo hi lo1 n' j n : Nat} (h0 : W01 lo hi lo1 n' S) (hd : j + n ≤ lo ∨ hi ≤ j) :
    ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ j ∨ j + n ≤ w.off := fun w hw hr ↦ by
  rcases h0 w hw with h | h
  · omega
  · omega

omit [Labels] in
/-- The frame's byte `j` as a number. -/
theorem loc_toNat (hS : StackOk m0 NN) {j : Nat} (hj : j < 5528) :
    (loc m0 j).toNat = (rspOf m0).toNat - 5520 + j :=
  fb_off_toNat hS N_ge hj

omit [Labels] in
/-- **The frame's bytes a call misses** are kept: the call at the frame's offset `c`, its stack
below it, its other changes `X`. -/
theorem keepC (hS : StackOk m0 NN) {c Nc : Nat} {st m2 : MachineData}
    (hsp : rspOf st = loc m0 c) (hc : c ≤ 5520) (hle : 5520 - c + Nc ≤ NN) {X : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside st.dmem m2.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow st Nc) Nc q ∨ X q))
    {j n : Nat} (hj : c ≤ j) (hjn : j + n ≤ 5528) (hX : ∀ i < n, ¬ X (loc m0 (j + i))) :
    Same st.dmem m2.dmem (loc m0 j) n := fun i hi ↦ by
  rw [off_add]
  refine hs _ ?_
  rintro (h' | h')
  · have e1 := hS.1
    have e2 := hS.2.1
    have hsp' : (rspOf st).toNat = (rspOf m0).toNat - 5520 + c := by
      rw [hsp, loc_toNat hS (by omega)]
    have hcb : (stackBelow st Nc).toNat = (rspOf m0).toNat - 5520 + c - Nc := by
      rw [stackBelow_toNat (by omega), hsp']
    rw [inRange_toNat (by rw [hcb]; omega), hcb, loc_toNat hS (by omega)] at h'
    omega
  · exact hX i hi h'

end

/-! ## The exits -/

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- What `verify_bus_balance` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData) (st : MachineState) :
    Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ VerifyBusBalancePost a s0 L m0 st.data

/-- The failure's address. -/
theorem lF_eq (hp : Placed code k) : Labels.label lF = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b56Offset) :=
  hp.label (label_of_infix b56_in_code rfl)

/-- The epilogue's address. -/
theorem l28_eq (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.VerifyBusBalance.label_28 = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b57Offset) :=
  hp.label (label_of_infix b57_in_code rfl)

/-- A state of the body in the frame's environment. -/
theorem match_fS {d : MachineData} {o : Nat} (fr : St m0 o d) {rest : List (BitVec 64 × Nat)}
    {ret : BitVec 64} : Match (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) (fS o) d :=
  match_ofMachine (sregions := [5528]) (by
      refine ⟨rfl, ?_⟩
      cases rest <;> trivial)
    ⟨fr.frame.rsp_eval, trivial⟩ trivial trivial trivial

/-- **The epilogue** (`NativeRustcVmX64.Vm.VerifyBusBalance.label_28`, `b57`): AL the result, the outputs its values. -/
theorem exit_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0) {d : MachineData}
    (fr : St m0 104 d) (hal : OkAl d ((verifyBusBalance L).run s0).isSome)
    (hok : ∀ res s', (verifyBusBalance L).run s0 = some (res, s') →
      TStateAt d.dmem (reg m0 .rdi) a s' ∧ BusWAt d.dmem (reg m0 .r8) res ∧
        ClaimsWAt d.dmem (reg m0 .r9) res.claims) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b57Offset)⟩ := by
  have hwf := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  obtain ⟨hepi, hmem, hk⟩ := ok_b57
  refine fr.exit (pre_stack h) N_ge (infix_of b57_in_code (by simp [b57]) hp) exit_b57 hwf rfl
    (match_fS fr) hepi (fun q ⟨w, hw, _⟩ ↦ by rw [hmem] at hw; cases hw)
    fun st hm' hpc' hrsp' hsame _ hsv ↦ .done _ ⟨hpc', hrsp', ?_, ?_, ?_, hsv⟩
  · have e : reg st.data .rax = reg d .rax := hk.reg hm' (by simp)
    unfold OkAl boolRet
    rw [e]
    exact hal
  · intro res s' he
    rw [hm'.dmem_eq hwf hmem]
    exact hok res s' he
  · exact NativeRustcVm.SameOutside.mono hsame fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inr (.inr (.inr hq))
      · exact .inl hq
      · exact .inr (.inl hq)
      · exact .inr (.inr (.inl hq))

/-- **A failure** (`NativeRustcVmX64.Vm.VerifyBusBalance.label_27`, `b56`): AL = `0`. -/
theorem fail_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0) {d : MachineData}
    (fr : St m0 104 d) (hr : (verifyBusBalance L).run s0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b56Offset)⟩ := by
  have hwf := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_then (infix_of b56_in_code (by simp [b56]) hp) exit_b56 hwf nofun (match_fS fr)
    fun st hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hrax, -⟩ := ok_b56
  have fr1 := (fr.block0 (pre_stack h) N_ge hwf hm1 hmid slots_le (by simp [hmem])).1
  simp only [PcOk] at hpc1
  refine at_pc (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyBusBalance.b56_next)) (exit_spec hp h fr1 ?_
    fun _ _ he ↦ by rw [hr] at he; cases he)
  rw [hr]
  unfold OkAl boolRet
  rw [show reg st.data .rax = _ from hm1.regs .rax _ hrax]
  rfl

/-- **A test** (`TestOk`) at the code's index `j`, branching to the failure where `c` holds. -/
theorem test_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0) {bX : List Directive}
    {j n : Nat} (hin : bX.IsInfixAt Host.prog (k + j)) (hn : bX.length = n) {c : SBool}
    (hx : exec bX (fS 104) = some (after bX (fS 104), .cond c lF))
    (hok : TestOk (after bX (fS 104))) {d : MachineData} (fr : St m0 104 d)
    (hfail : c.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0) 0) = true →
      (verifyBusBalance L).run s0 = none)
    (cont : ∀ d' : MachineData, St m0 104 d' → d'.dmem = d.dmem →
      (∀ r ∈ nsp, reg d' r = reg d r) →
      c.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0) 0) = false →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d', Host.addrOf (k + j + n)⟩) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + j)⟩ := by
  have hwf := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_then hin hx hwf nofun (match_fS fr) fun st hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hk⟩ := hok
  have fr1 := (fr.block0 (pre_stack h) N_ge hwf hm1 hmid slots_le (by simp [hmem])).1
  have hd : st.data.dmem = d.dmem := hm1.dmem_eq hwf hmem
  simp only [PcOk] at hpc1
  cases hc : c.eval (frameEnv m0 d 5520 [] (fun _ ↦ 0) 0) with
  | true =>
    rw [hc] at hpc1
    simp only [↓reduceIte] at hpc1
    exact at_pc (hpc1.trans (lF_eq hp)) (fail_spec hp h fr1 (hfail hc))
  | false =>
    rw [hc] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [hn] at hpc1
    exact at_pc hpc1 (cont st.data fr1 hd (fun r hr ↦ hk.reg hm1 hr) hc)

end

end NativeRustcVmX64.Bus.VerifyBusBalance
