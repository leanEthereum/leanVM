module

public import NativeRustcVmArm.Code.Vm.BusLayout.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.SharePre
public import NativeRustcVmArm.Bus.BusLayout.Common

/-!
# `verify_bus_balance`'s head: what it shares

- `get_of_copy`, `blw_copy`: bytes, a side's layout copied.
- `blocks_bytes_length`: a list of blocks' bytes.
- `lay_at`: the layout (X1) in every state of the frame.
- `ts_block`, `ts_call`: the `TState` through a block, a call writing the frame.
- `writeOk_frame`, `reg_add`: a block's writes in the frame; a register a pointer plus a literal.
- `bl_call`: `bus_layout` from the frame, its output at `4176`.
- `mc_call`: `memcpy` within the frame.
- `AtGrind`: the state at `b10` (`k + 76`), the three layouts built.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- A byte copied: where `d'` at `b` holds `bytesOf d a n`. -/
theorem get_of_copy {d d' : Mem 64} {a b : BitVec 64} {n : Nat}
    (hb : NativeRustcVm.BytesAt d' b (bytesOf d a n)) :
    ∀ i < n, ∀ x, d.get? (a + BitVec.ofNat 64 i) = some x →
      d'.get? (b + BitVec.ofNat 64 i) = some x := fun i hi x hx ↦ by
  rw [hb i (by simp [NativeRustcArm.bytesOf]; exact hi)]
  simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range, hx, Option.getD_some]

/-- **A side's layout copied**: its depth word stored at `b`, its other `880` bytes copied. -/
theorem blw_copy {d d' : Mem 64} {a b : BitVec 64} {BL : BusLayoutW} (h : BusLayoutWAt d a BL)
    (hw : NativeRustcVm.WordAt d' b BL.depth.toUInt64)
    (hc : NativeRustcVm.BytesAt d' (b + BitVec.ofNat 64 8)
      (bytesOf d (a + BitVec.ofNat 64 8) 880)) :
    BusLayoutWAt d' b BL := by
  refine BusLayout.busLayoutWAt_transfer (fun i hi x hx ↦ ?_) h
  rcases Nat.lt_or_ge i 8 with h8 | h8
  · have e1 := h.depth i (by rw [NativeRustcVm.length_wordBytes]; exact h8)
    obtain rfl := Option.some.inj (e1.symm.trans hx)
    exact hw i (by rw [NativeRustcVm.length_wordBytes]; exact h8)
  · have e : 8 + (i - 8) = i := by omega
    have := get_of_copy hc (i - 8) (by omega) x
      (by rw [NativeRustcVm.addr_add_add, e]; exact hx)
    rwa [NativeRustcVm.addr_add_add, e] at this

/-- A list of blocks' bytes: `16` each. -/
theorem blocks_bytes_length (l : List NativeRustcVm.Data.Block) :
    (l.flatMap NativeRustcVm.Data.Block.bytes).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes, List.length_append,
      NativeRustcVm.length_wordBytes]
    omega

/-- A block's writes in the frame. -/
theorem writeOk_frame [Labels] {env : Env} {outs : BitVec 64 → Prop} {S : SState}
    (h : (S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 5488)) = true) :
    ∀ w ∈ S.mem, WriteOk env 5488 [] outs w := fun w hw ↦ by
  have := List.all_eq_true.mp h w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact .inl ⟨this.1, this.2, by simp⟩

/-- A register a block set to another plus a literal, the other the frame's byte `o`. -/
theorem reg_add [Labels] {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {x y : XReg} {c o : Nat} (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hx : S.reg x = some (.bin .add .W64 (.reg y) (.lit c)))
    (hy : (m.regs.getXReg y).toBitVec = loc m0 o) :
    (m'.regs.getXReg x).toBitVec = loc m0 (o + c) := by
  rw [hm.regs x _ hx]
  simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, hy]
  rw [NativeRustcVm.addr_add_add]

end

/-! ## The layout, the `TState` -/

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **The layout** (X1) in a state of the frame. -/
theorem lay_at (h : VerifyBusBalancePre a s0 L m0) {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m) :
    LayoutWAt m.dmem m0.regs.X1.toBitVec L := by
  have hlo := pre_layOk h
  have hnw := hlo.1.2
  refine NativeRustcVm.Tables.LayoutWAt.of_same (pre_lay h)
    (Same.of_sameOutside hfr.same fun j hj hq ↦ ?_)
  rcases hq with hq | hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add hlo.2 hnw (Bus.stack_noWrap (pre_stack h)) hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_layT h) hnw (pre_ts h).footprint.1.2 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_busL h).symm hnw (pre_bus h).2.1 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (pre_clL h).symm hnw (pre_cl h).2.1 hj hq

/-- **The `TState` through a block** writing the frame only. -/
theorem ts_block (h : VerifyBusBalancePre a s0 L m0) {m m' : MachineData}
    {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).WF)
    (hS : (S.mem.all fun w ↦ w.r == 0 && decide (0 ≤ w.off) && decide (w.off + w.n ≤ 5488)) =
      true)
    {s : TState} (hts : TStateAt m.dmem m0.regs.X0.toBitVec a s) :
    TStateAt m'.dmem m0.regs.X0.toBitVec a s :=
  hts.frame (hm.kept hwf) (fun q hq ↦ loc_not_tsw h (le_refl _)
    (written_loc hS hq (by have := (pre_stack h).2.1; have := N_ge; omega)))
    (hm.sameOutside hwf)

/-- **The `TState` through a call** writing below the frame and `n` bytes of it at `o`. -/
theorem ts_call (h : VerifyBusBalancePre a s0 L m0) {m d : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m) {N' : Nat}
    (hle : 5488 + N' ≤ verifyBusBalanceStack) {o n : Nat} (hon : o + n ≤ 5488)
    (hk : Kept m.dmem d.dmem)
    (hs : SameOutside m.dmem d.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨
      InRange (loc m0 o) n q))
    {s : TState} (hts : TStateAt m.dmem m0.regs.X0.toBitVec a s) :
    TStateAt d.dmem m0.regs.X0.toBitVec a s :=
  hts.frame hk (fun _ hq ↦ hq.elim
    (fun hq ↦ have c := callee_apart h hfr hle hq; ⟨fun h' ↦ c.2.1 (.inl h'), c.1⟩)
    (fun hq ↦ loc_not_tsw h hon hq)) hs

end

/-! ## The calls -/

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **`bus_layout(out, fw, n, blocks, len, layout)`** from the frame, the output at `4176`: the
side's layout, of the framework sizes `fw`. -/
theorem bl_call (h : VerifyBusBalancePre a s0 L m0)
    (hbl : ∀ L bl, Spec (Labels.label NativeRustcVmArm.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.BusLayout.entryLabel ∧ retOf st.data = next)
    {side : Nat} {it : NativeRustcVm.Data.Item}
    (hit : it.bytes = (sideBlocks side).flatMap NativeRustcVm.Data.Block.bytes)
    (hl1 : 1 ≤ (sideBlocks side).length) (hl2 : (sideBlocks side).length ≤ maxBlocks)
    (hown : ∀ x ∈ sideBlocks side, x.owner < nTables)
    {rows : Array Nat} (hrows : busBlocks L.tableLogHeights rows = (L.push, L.pull, L.count))
    {fw : Array Nat} (hfw : natsOf st.data st.data.regs.X1 st.data.regs.X2.toNat = fw)
    (hfw3 : st.data.regs.X2.toNat ≤ 3) (hfw30 : ∀ s ∈ fw, s ≤ 30)
    (hfok : InOk st.data st.data.regs.X1.toBitVec (8 * st.data.regs.X2.toNat) busLayoutStack)
    (hfap : Apart (loc m0 4176) optBusLayoutBytes st.data.regs.X1.toBitVec
      (8 * st.data.regs.X2.toNat))
    (x0 : st.data.regs.X0.toBitVec = loc m0 4176)
    (x3 : st.data.regs.X3.toBitVec = NativeRustcVmArm.rodataAddr it)
    (x4 : st.data.regs.X4.toNat = (sideBlocks side).length) (x5 : st.data.regs.X5 = m0.regs.X1)
    (cont : ∀ m2, Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m2 →
      OptBusLayoutWAt m2.dmem (loc m0 4176) (some (busLayout fw (sideOf L side))) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange (stackBelow st.data busLayoutStack) busLayoutStack q ∨
          InRange (loc m0 4176) optBusLayoutBytes q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have c := ctx h
  have hat := Fr.at_ c hfr (outs_not_rc h)
  have hlo := pre_layOk h
  obtain ⟨hro, hrok, -⟩ := ro_ok h hfr le_bl it
  have hlen : it.bytes.length = 16 * (sideBlocks side).length := by
    rw [hit, blocks_bytes_length]
  refine Fr.callLocal (o := 4176) (n := optBusLayoutBytes)
    (X := fun q ↦ InRange (loc m0 4176) optBusLayoutBytes q)
    hfr hS.2.1 le_bl keep_callee (slots_lo (by decide)) (by decide) (outs_not_frame h)
    (fun q hq ↦ .inr hq) (hbl L (sideBlocks side)) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
      rcases hq' with hq' | hq'
      · rw [x0] at hq'; exact .inr hq'
      · exact .inl hq', hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · dsimp only [BusLayoutPre]
    rw [x0, x3, x4, x5]
    refine ⟨hfr.stackOk hS rfl le_bl, hfw3, by rw [hfw]; exact hfw30, hfok, hl1, hl2, rfl, hown,
      by rw [← hit]; exact hro, by rw [← hlen]; exact hrok, lay_at h hfr,
      ⟨⟨fun i hi ↦ hfr.kept _ (hlo.1.1 i hi), hlo.1.2⟩, c.apart hat le_bl hlo.2⟩,
      loc_inOk h hfr le_bl (by decide), hfap, ?_, c.apart_of_stack (by decide) hlo.2⟩
    rw [← hlen]
    exact c.apart_of_stack (by decide) ((pre_ro h).apart it)
  · dsimp only [BusLayoutPost] at hq2
    obtain ⟨ho, -, hsv⟩ := hq2
    have ho' := ho rows
    rw [x0, hfw, sideOf_eq hrows side] at ho'
    exact cont m2 hfr2 ho' hsv.2.2 hcs2 hs2

/-- **`memcpy(loc dst, loc src, n)`** within the frame, below the slots. -/
theorem mc_call (h : VerifyBusBalancePre a s0 L m0)
    (hmc : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel ∧ retOf st.data = next)
    {dst src n : Nat} (hd : dst + n ≤ 5392) (hs : src + n ≤ 5488)
    (hap : dst + n ≤ src ∨ src + n ≤ dst)
    (x0 : st.data.regs.X0.toBitVec = loc m0 dst) (x1 : st.data.regs.X1.toBitVec = loc m0 src)
    (x2 : st.data.regs.X2.toNat = n)
    (cont : ∀ m2, Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m2 →
      NativeRustcVm.BytesAt m2.dmem (loc m0 dst) (bytesOf st.data.dmem (loc m0 src) n) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange (stackBelow st.data 0) 0 q ∨
        InRange (loc m0 dst) n q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  refine Fr.callLocal (o := dst) (n := n) (N' := 0) (X := fun q ↦ InRange (loc m0 dst) n q)
    hfr hS.2.1 le_mem keep_callee (slots_lo hd) (by omega) (outs_not_frame h)
    (fun q hq ↦ .inr hq) hmc hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [x0, x2] at hq'; exact .inr hq', hq.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · have hd' := loc_inOk h hfr le_mem (o := dst) (n := n) (by omega)
    have hs' := loc_inOk h hfr le_mem (o := src) (n := n) hs
    unfold MemcpyPre
    rw [x0, x1, x2]
    refine ⟨hd'.1.1, hs'.1.1, hd'.1.2, hs'.1.2, ?_⟩
    unfold Apart
    rw [loc_toNat hS (by omega), loc_toNat hS (by omega)]
    omega
  · obtain ⟨-, hb, -, hsv⟩ := hq2
    rw [x0, x1, x2] at hb
    exact cont m2 hfr2 hb hsv.2.2 hcs2 hs2

end

/-! ## After the layouts -/

public section
variable [Labels]

/-- **The state at `b10`** (`k + 76`): the three layouts at `160`, `1048`, `1936`, the push
side's depth below `64` in X26. -/
structure AtGrind (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData) (m : MachineData) :
    Prop where
  fr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m
  push : BusLayoutWAt m.dmem (loc m0 160) (pushL L)
  pull : BusLayoutWAt m.dmem (loc m0 1048) (pullL L)
  count : BusLayoutWAt m.dmem (loc m0 1936) (countL L)
  dep : (pushL L).depth < 64
  x19 : m.regs.getXReg .X19 = m0.regs.X4
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x23 : m.regs.getXReg .X23 = m0.regs.X3
  x24 : m.regs.getXReg .X24 = m0.regs.X2
  x25 : m.regs.getXReg .X25 = m0.regs.X0
  x26 : (m.regs.getXReg .X26).toNat = (pushL L).depth
  x27 : (m.regs.getXReg .X27).toNat = L.logMemory
  x28 : m.regs.getXReg .X28 = m0.regs.X5
  x29 : (m.regs.getXReg .X29).toNat = L.logBytecode
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s0

end

end NativeRustcVmArm.Bus.VerifyBusBalance
