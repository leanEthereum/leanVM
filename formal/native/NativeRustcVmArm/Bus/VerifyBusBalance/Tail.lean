module

public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.Common

/-!
# `verify_bus_balance`'s tail

From `b46` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b46Offset`), after the count side: `b46` checks its total's tag; `b47` empties the bus's
point and calls `Buf<EW, 63>::extend` with the GKR point; `b48` checks it; `b49` writes the three
totals and jumps to the epilogue with X0 = `1` (`tail_spec`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- The forms over bytes that stayed the same. -/
theorem FormsAt.of_same {d d' : Mem 64} {a : BitVec 64} {F : Array (Array FormW)}
    (h : FormsAt d a F) (hs : Same d d' a busPointOff) : FormsAt d' a F := by
  have hf : formBufBytes = 5928 := rfl
  have hb : busPointOff = 106704 := rfl
  refine ⟨h.size, h.row_size, fun t ht s hs' ↦ ?_⟩
  have h1 := h.row_size t ht
  have h2 := h.size
  exact NativeRustcVm.Tables.FormBufAt.of_same (h.forms t ht s hs')
    (hs.sub (by rw [hb, hf]; unfold nTables at h2; omega))

/-- Region `i` plus `o`. -/
theorem eval_ptr_off [Labels] {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {i n : Nat} {b : BitVec 64} (hb : regions[i]? = some (b, n))
    (o : Int) :
    (Sym.ptr i o).eval (Env.ofMachine m regions vars) = b + BitVec.ofInt 64 o := by
  rw [Sym.eval, Env.base_ofMachine m regions vars hb]

/-- A state in the frame with a second region `b`, register `r` at its byte `o`. -/
theorem match_frameO [Labels] {m0 m : MachineData} (hS : StackOk m0 verifyBusBalanceStack)
    (hsp : m.regs.SP.toBitVec = base m0 5488) {r : XReg} {n : Nat} {b : BitVec 64} {o : Int}
    (hx : (m.regs.getXReg r).toBitVec = b + BitVec.ofInt 64 o) :
    Match (Env.ofMachine m [(base m0 5488, 5488), (b, n)])
      (init [(5488, true), (n, false)] (.ptr 0 0) [(r, .ptr 1 o)]) m :=
  match_ofMachine (sregions := [(5488, true), (n, false)])
    (regions := [(base m0 5488, 5488), (b, n)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hS N_ge rfl, rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hsp]; simp)
    ⟨by show (m.regs.getXReg r).toBitVec = _; rw [hx, eval_ptr_off (by rfl)], trivial⟩ trivial
    trivial trivial

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The tail** (`b46`, `k + NativeRustcVmArm.Vm.VerifyBusBalance.b46Offset`): the count side's total at `5344`, the GKR point at `3136`,
the forms at the bus. -/
theorem tail_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {m : MachineData} {res : BusResultW} {s' : TState} {t0 t1 t2 : EW}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m)
    (hr : (verifyBusBalance L).run s0 = some (res, s')) (htot : res.totals = #[t0, t1, t2])
    (x19 : m.regs.getXReg .X19 = m0.regs.X4)
    (x25 : (m.regs.getXReg .X25).toBitVec = loc m0 3136)
    (x26 : (m.regs.getXReg .X26).toNat = res.point.size) (hsz : res.point.size ≤ 63)
    (x28 : m.regs.getXReg .X28 = t0.c0) (x24 : m.regs.getXReg .X24 = t0.c1)
    (x21 : m.regs.getXReg .X21 = t1.c0) (x22 : m.regs.getXReg .X22 = t1.c1)
    (hpt : NativeRustcVm.EWsAt m.dmem (loc m0 3136) res.point.toList)
    (hopt : OptEWAt m.dmem (loc m0 5344) (some t2))
    (hF : FormsAt m.dmem m0.regs.X4.toBitVec res.forms)
    (hts : TStateAt m.dmem m0.regs.X0.toBitVec a s')
    (hcl : ClaimsWAt m.dmem m0.regs.X5.toBitVec res.claims) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b46Offset)⟩ := by
  have hS := pre_stack h
  have hN := hS.2.1
  have hbus := pre_bus h
  have hbnw : m0.regs.X4.toBitVec.toNat + 107768 ≤ 2 ^ 64 := hbus.2.1
  have hbap : Apart m0.regs.X4.toBitVec 107768 (stackBelow m0 verifyBusBalanceStack)
      verifyBusBalanceStack := hbus.2.2.2.2.1
  have hstk : (stackBelow m0 verifyBusBalanceStack).toNat = m0.regs.SP.toNat - 18288 := by
    rw [N_eq]; exact Sumcheck.toNat_stackBelow (by rw [← N_eq]; exact hN)
  have hsp0 := m0.regs.SP.toNat_lt
  rw [N_eq] at hbap hN hstk
  unfold Apart at hbap
  have hbo : ∀ o, o < 107768 →
      (m0.regs.X4.toBitVec + BitVec.ofNat 64 o).toNat = m0.regs.X4.toBitVec.toNat + o :=
    fun o ho ↦ NativeRustcVm.toNat_add_ofNat (by omega)
  have hlo : ∀ o, o ≤ 5488 → (loc m0 o).toNat = m0.regs.SP.toNat - 5488 + o :=
    fun o ho ↦ loc_toNat hS ho
  -- `b46`: the count side's tag.
  refine Fr.runBlock hS N_ge rfl hfr (b46_in_code.trans hp.1 (by simp [b46])) run_b46 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hl : (Env.ofMachine m [(base m0 5488, 5488)]).load 0 5344 4 = BitVec.ofNat 64 1 :=
    Transcript.load4_of_tag (w := 1) (.inr rfl) hopt.1
  have hc : SBool.eval (Env.ofMachine m [(base m0 5488, 5488)])
      (.not (.bit .W32 (.load 0 5344 4) 0)) = false := by
    show (!(low .W32 ((Env.ofMachine m [(base m0 5488, 5488)]).load 0 5344 4)).getLsbD 0) = false
    rw [hl]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b47`: the bus's point emptied, `extend` called.
  have e19 : st1.data.regs.getXReg .X19 = m0.regs.X4 := (reg_of hm1 rfl).trans x19
  have hwf2 : (Env.ofMachine st1.data
      [(base m0 5488, 5488), (m0.regs.X4.toBitVec, 107768)]).WF :=
    Bus.wf_frame2 hS N_ge hfr1.kept ⟨hbus.1, hbus.2.1⟩ hbus.2.2.2.2.1
  have hm2 := match_frameW (n := 107768) hS N_ge rfl hfr1.sp (r := .X19) (by rw [e19])
  refine exec_at (b47_in_code.trans hp.1 (by simp [b47])) run_b47 hwf2 hpc1 hm2
    fun st2 hm2' hpc2 ↦ ?_
  have hbIn : ∀ o n, o + n ≤ 107768 → ∀ q,
      InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n q →
        InRange m0.regs.X4.toBitVec busBytes q := fun o n hon q hq ↦ by
    rcases Nat.lt_or_ge o 107768 with ho | ho
    · refine NativeRustcVm.InRange.mono hq ?_ hbus.2.1 ?_ ?_
      · unfold NativeRustcVm.NoWrap; rw [hbo o ho]; omega
      · rw [hbo o ho]; omega
      · rw [hbo o ho, busBytes_eq]; omega
    · have : n = 0 := by omega
      subst this
      unfold InRange at hq
      omega
  have hbusIn : ∀ o n, o + n ≤ 107768 → ∀ q,
      InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n q → outs m0 q :=
    fun o n hon q hq ↦ .inr (.inl (hbIn o n hon q hq))
  have hs2 : SameOutside st1.data.dmem st2.data.dmem
      (InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 106704) 1064) :=
    NativeRustcVm.SameOutside.mono (hm2'.sameOutside hwf2) fun q hq ↦ by
      have := written_in (r := 1) (lo := 106704) (hi := 106712) rfl (by decide) hq
      rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)]
      omega
  have hfr2 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st2.data :=
    Fr.ofBlockW hfr1 hm2 hm2' hwf2 rfl rfl (fun r hr ↦ by simp at hr) rfl N_ge hS.2.1 slots_le
      fun w hw ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw
        refine .inr ⟨by decide, fun b sz hb ↦ ?_⟩
        simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact ⟨by decide, fun i hi ↦ hbusIn 0 107768 (by omega) _
          (by rw [add_zero']; exact NativeRustcVm.inRange_add hi (by omega))⟩
  have hoi : BitVec.ofInt 64 (106704 : Int) = BitVec.ofNat 64 106704 := rfl
  have f0 : st2.data.regs.X0.toBitVec = m0.regs.X4.toBitVec + BitVec.ofNat 64 106704 := by
    rw [show st2.data.regs.X0 = st2.data.regs.getXReg .X0 from rfl, hm2'.regs .X0 _ rfl,
      eval_ptr_off rfl, hoi]
  have f19 : (st2.data.regs.getXReg .X19).toBitVec =
      m0.regs.X4.toBitVec + BitVec.ofInt 64 106704 := by
    rw [hm2'.regs .X19 _ rfl, eval_ptr_off rfl]
  have f1 : (st2.data.regs.X1).toBitVec = loc m0 3136 := by
    rw [show st2.data.regs.X1 = st2.data.regs.getXReg .X1 from rfl,
      reg_of hm2' (r := .X1) (r' := .X25) rfl, reg_of hm1 rfl, x25]
  have f2 : (st2.data.regs.X2).toNat = res.point.size := by
    rw [show st2.data.regs.X2 = st2.data.regs.getXReg .X2 from rfl,
      reg_of hm2' (r := .X2) (r' := .X26) rfl, reg_of hm1 rfl, x26]
  obtain ⟨ht2a, ht2b⟩ := NativeRustcVm.ewAt_iff.mp hopt.2
  have f23 : st2.data.regs.getXReg .X23 = t2.c0 := by
    refine UInt64.toBitVec_inj.mp ((hm2'.regs .X23 _ rfl).trans
      (Transcript.load_ofMachine (b := base m0 5488) (n := 5488) rfl ?_))
    rw [hd1]
    simpa only [off, NativeRustcVm.addr_add_add] using ht2a
  have f20 : st2.data.regs.getXReg .X20 = t2.c1 := by
    refine UInt64.toBitVec_inj.mp ((hm2'.regs .X20 _ rfl).trans
      (Transcript.load_ofMachine (b := base m0 5488) (n := 5488) rfl ?_))
    rw [hd1]
    simpa only [off, NativeRustcVm.addr_add_add] using ht2b
  have f28 : st2.data.regs.getXReg .X28 = t0.c0 :=
    (reg_of hm2' rfl).trans ((reg_of hm1 rfl).trans x28)
  have f24 : st2.data.regs.getXReg .X24 = t0.c1 :=
    (reg_of hm2' rfl).trans ((reg_of hm1 rfl).trans x24)
  have f21 : st2.data.regs.getXReg .X21 = t1.c0 :=
    (reg_of hm2' rfl).trans ((reg_of hm1 rfl).trans x21)
  have f22 : st2.data.regs.getXReg .X22 = t1.c1 :=
    (reg_of hm2' rfl).trans ((reg_of hm1 rfl).trans x22)
  have w0 : NativeRustcVm.WordAt st2.data.dmem (off m0.regs.X4.toBitVec 106704) 0 :=
    Transcript.wordAt_write hm2' (r := 1) (o := 106704) rfl (by decide) (v := .lit 0) (by decide)
  have hw0 : NativeRustcVm.wordOf st2.data.dmem st2.data.regs.X0.toBitVec = 0 := by
    rw [f0]; exact NativeRustcVm.wordOf_of_wordAt w0
  have hsz16 : 3136 + 16 * res.point.size ≤ 5488 := by omega
  have hpt2 : NativeRustcVm.EWsAt st2.data.dmem (loc m0 3136) res.point.toList := by
    refine NativeRustcVm.BytesAt.of_sameOutside (by rw [hd1]; exact hpt) hs2 fun i hi hq ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList] at hi
    rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega),
      NativeRustcVm.addr_add_add, hlo _ (by omega)] at hq
    omega
  have hle63 : (NativeRustcVm.wordOf st2.data.dmem st2.data.regs.X0.toBitVec).toNat +
      st2.data.regs.X2.toNat ≤ 63 := by rw [hw0, f2]; simpa using hsz
  simp only [PcOk] at hpc2
  refine Fr.callSpec hfr2 hS.2.1 le_ext keep_callee slots_le (outs_not_frame h) hext hpc2 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m3 hfr3 hq3 hcs3 ↦ ?_
  · refine ⟨by rw [hw0]; decide, ⟨fun i hi ↦ hfr2.kept _ ?_, ?_⟩,
      ⟨fun i hi ↦ hfr2.kept _ ?_, ?_⟩, ?_⟩
    · rw [f0, NativeRustcVm.addr_add_add]; exact hbus.1 _ (by rw [busBytes_eq]; omega)
    · unfold NoWrap; rw [f0, hbo _ (by omega)]; omega
    · rw [f2] at hi; rw [f1]
      rw [NativeRustcVm.addr_add_add]
      exact (frame_mapped hS N_ge).1 _ (by omega)
    · unfold NoWrap; rw [f1, f2, hlo _ (by omega)]; omega
    · unfold Apart; rw [f0, f1, f2, hbo _ (by omega), hlo _ (by omega)]; omega
  · rcases hq' with hq' | hq'
    · right
      rw [f0] at hq'
      exact hbusIn 106704 1016 (by omega) q hq'
    · left; exact hq'
  · obtain ⟨h3a, h3c, h3s⟩ := hq3
    simp only [hle63, ↓reduceIte] at h3a
    obtain ⟨h3x0, h3buf⟩ := h3a
    have hbe : NativeRustcVm.bufEWOf st2.data.dmem st2.data.regs.X0.toBitVec = [] := by
      unfold NativeRustcVm.bufEWOf; rw [hw0]; rfl
    have hsl : (slice st2.data st2.data.regs.X1 st2.data.regs.X2).toList = res.point.toList := by
      have := NativeRustcVm.ewsOf_of_ewsAt hpt2
      rw [Array.length_toList] at this
      unfold slice
      rw [f1, f2, this]
    rw [hbe, hsl, List.nil_append, f0] at h3buf
    have h3' : SameOutside st2.data.dmem m3.dmem
        (InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 106704) 1064) :=
      NativeRustcVm.SameOutside.mono h3c fun q hq ↦ by
        rcases hq with hq | hq
        · rw [f0] at hq
          rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)]
          rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)] at hq
          omega
        · unfold InRange bufExtendStack at hq; omega
    -- `b48`: `extend`'s result.
    refine Fr.runBlock hS N_ge rfl hfr3 (b48_in_code.trans hp.1 (by simp [b48])) run_b48 rfl rfl
      (by decide) (by decide) fun st4 hfr4 hd4 hm4 hpc4 ↦ ?_
    have hc4 : SBool.eval (Env.ofMachine m3 [(base m0 5488, 5488)])
        (.not (.bit .W32 (.reg .X0) 0)) = false := by
      show (!(low .W32 (m3.regs.getXReg .X0).toBitVec).getLsbD 0) = false
      rw [show m3.regs.getXReg .X0 = m3.regs.X0 from rfl, h3x0]
      rfl
    simp only [PcOk, hc4, Bool.false_eq_true, ↓reduceIte] at hpc4
    -- `b49`: the totals.
    have g19 : (st4.data.regs.getXReg .X19).toBitVec =
        m0.regs.X4.toBitVec + BitVec.ofInt 64 106704 := by
      rw [reg_of hm4 rfl, hcs3 .X19 rfl, f19]
    have g28 : st4.data.regs.getXReg .X28 = t0.c0 :=
      (reg_of hm4 rfl).trans ((hcs3 .X28 rfl).trans f28)
    have g24 : st4.data.regs.getXReg .X24 = t0.c1 :=
      (reg_of hm4 rfl).trans ((hcs3 .X24 rfl).trans f24)
    have g21 : st4.data.regs.getXReg .X21 = t1.c0 :=
      (reg_of hm4 rfl).trans ((hcs3 .X21 rfl).trans f21)
    have g22 : st4.data.regs.getXReg .X22 = t1.c1 :=
      (reg_of hm4 rfl).trans ((hcs3 .X22 rfl).trans f22)
    have g23 : st4.data.regs.getXReg .X23 = t2.c0 :=
      (reg_of hm4 rfl).trans ((hcs3 .X23 rfl).trans f23)
    have g20 : st4.data.regs.getXReg .X20 = t2.c1 :=
      (reg_of hm4 rfl).trans ((hcs3 .X20 rfl).trans f20)
    have hwf5 : (Env.ofMachine st4.data
        [(base m0 5488, 5488), (m0.regs.X4.toBitVec, 107768)]).WF :=
      Bus.wf_frame2 hS N_ge hfr4.kept ⟨hbus.1, hbus.2.1⟩ hbus.2.2.2.2.1
    have hm5 := match_frameO (n := 107768) hS hfr4.sp (r := .X19) g19
    refine exec_at (b49_in_code.trans hp.1 (by simp [b49])) run_b49 hwf5 hpc4 hm5
      fun st5 hm5' hpc5 ↦ ?_
    have hs5 : SameOutside st4.data.dmem st5.data.dmem
        (InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 107720) 48) :=
      NativeRustcVm.SameOutside.mono (hm5'.sameOutside hwf5) fun q hq ↦ by
        have := written_in (r := 1) (lo := 107720) (hi := 107768) rfl (by decide) hq
        rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)]
        omega
    have hfr5 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st5.data :=
      Fr.ofBlockW hfr4 hm5 hm5' hwf5 rfl rfl (fun r hr ↦ by simp at hr) rfl N_ge hS.2.1 slots_le
        fun w hw ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
          · refine .inr ⟨by decide, fun b sz hb ↦ ?_⟩
            simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl⟩ := hb
            exact ⟨by decide, fun i hi ↦ hbusIn 0 107768 (by omega) _
              (by rw [add_zero']; exact NativeRustcVm.inRange_add hi (by omega))⟩
    have v0 := Transcript.wordAt_write hm5' (r := 1) (o := 107720) rfl (by decide)
      (v := .reg .X28) (by decide)
    have v1 := Transcript.wordAt_write hm5' (r := 1) (o := 107728) rfl (by decide)
      (v := .reg .X24) (by decide)
    have v2 := Transcript.wordAt_write hm5' (r := 1) (o := 107736) rfl (by decide)
      (v := .reg .X21) (by decide)
    have v3 := Transcript.wordAt_write hm5' (r := 1) (o := 107744) rfl (by decide)
      (v := .reg .X22) (by decide)
    have v4 := Transcript.wordAt_write hm5' (r := 1) (o := 107752) rfl (by decide)
      (v := .reg .X23) (by decide)
    have v5 := Transcript.wordAt_write hm5' (r := 1) (o := 107760) rfl (by decide)
      (v := .reg .X20) (by decide)
    simp only [Sym.eval, Env.ofMachine, g28, g24, g21, g22, g23, g20] at v0 v1 v2 v3 v4 v5
    have htot5 : NativeRustcVm.EWsAt st5.data.dmem (off m0.regs.X4.toBitVec busTotalsOff)
        res.totals.toList := by
      rw [htot]
      refine Bus.ewsAt_of_words [t0, t1, t2] fun i hi ↦ ?_
      simp only [List.length_cons, List.length_nil] at hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
        simp only [off, busTotalsOff_eq, NativeRustcVm.addr_add_add, List.getElem_cons_zero,
          List.getElem_cons_succ] at v0 v1 v2 v3 v4 v5 ⊢
      · exact ⟨v0, v1⟩
      · exact ⟨v2, v3⟩
      · exact ⟨v4, v5⟩
    have hall : SameOutside m.dmem st5.data.dmem
        (InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 106704) 1064) := fun q hq ↦ by
      have h5 : ¬InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 107720) 48 q := fun h' ↦ hq (by
        rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)]
        rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega)] at h'
        omega)
      rw [hs5 q h5, hd4, h3' q hq, hs2 q hq, hd1]
    have hkeeps : Keeps m.dmem st5.data.dmem := fun p hp ↦
      hm5'.kept hwf5 p (by
        show (st4.data.dmem.get? p).isSome = true
        rw [hd4]
        exact h3s.2.2 p (hm2'.kept hwf2 p (by
          show (st1.data.dmem.get? p).isSome = true
          rw [hd1]; exact hp)))
    have hfp := hts.footprint
    have hnotb : ∀ q, InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 106704) 1064 q →
        InRange m0.regs.X4.toBitVec busBytes q := hbIn 106704 1064 (by omega)
    simp only [PcOk] at hpc5
    refine at_pc (hpc5.trans (hp.label (label_of_infix b51_in_code rfl)))
      (exit_spec hp h hfr5 ?_ fun res' s'' he ↦ ?_)
    · rw [hr]
      exact UInt64.toBitVec_inj.mp (reg_lit hm5' (r := .X0) (n := 1) rfl)
    · rw [hr] at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
      refine ⟨hts.frame hkeeps (fun q hq ↦ ⟨NativeRustcVm.Apart.not_inRange hbus.2.2.1 hbus.2.1
          hfp.1.2 (hnotb q hq), NativeRustcVm.Apart.not_inRange hbus.2.2.2.1 hbus.2.1 hfp.2.1.2
          (hnotb q hq)⟩) hall, BusWAt.of_formsAt ?_ ?_ (by rw [htot]; rfl) htot5, ?_⟩
      · refine FormsAt.of_same hF (Same.of_sameOutside hall fun j hj hq ↦ ?_)
        rw [busPointOff_eq] at hj
        rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega),
          hbo _ (by omega)] at hq
        omega
      · refine NativeRustcVm.Layout.BufEWAt.of_same (n := 1016) h3buf ?_ (by decide)
        refine Same.of_sameOutside (R := InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 107720) 48)
          (fun q hq ↦ by rw [hs5 q hq, hd4]) fun j hj hq ↦ ?_
        simp only [off, busPointOff_eq, NativeRustcVm.addr_add_add] at hq
        rw [Sym.inRange_iff (by rw [hbo _ (by omega)]; omega), hbo _ (by omega),
          hbo _ (by omega)] at hq
        omega
      · refine NativeRustcVm.Tables.ClaimsWAt.of_same hcl
          (Same.of_sameOutside hall fun j hj hq ↦ ?_)
        exact NativeRustcVm.Apart.not_inRange_add (pre_busCl h).symm (pre_cl h).2.1 hbus.2.1 hj
          (hnotb _ hq)

end

end NativeRustcVmArm.Bus.VerifyBusBalance
