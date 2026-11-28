module

public import NativeRustcVmX64.Tables.TableSumcheck.Rev
public import NativeRustcVmX64.Tables.TableTerms.Blocks
public import NativeRustcVmX64.Code.Vm.TableWeights.Names

/-!
# `table_sumcheck`: the tables' weights (x86-64)

From the reversed challenges: `b10` (`NativeRustcVmX64.Vm.TableSumcheck.label_9`) saves the claim's `c0` at `48`, keeps
its `c1` in R14 and calls `table_weights` on the heights, the bus's GKR point and the reversed
challenges, its six weights at `592` of the frame (`weights`). What follows reads the state `Wt`.
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableSumcheck
open NativeRustcVmX64.Tables.TableTerms (at_pc addr_eq rin_sub)

@[expose] public section

/-- **After `table_weights`**: the body, the claim (`c0` at `48`, `c1` in R14), the words saved
at `56` to `88`, the reversed challenges at `112`, the weights at `592`, the registers. -/
structure Wt [Labels] (a : DecArea) (s1 : TState) (heights : Array Nat) (bus : BusResultW)
    (m0 : MachineData) (xs : Array EW) (c : EW) (d : MachineData) : Prop where
  bd : Bd m0 736 N slots (outs m0) 40 d
  w48 : NativeRustcVm.WordAt d.dmem (off (fb m0) 48) c.c0
  w56 : NativeRustcVm.WordAt d.dmem (off (fb m0) 56) (.ofBitVec (cpA m0))
  w64 : NativeRustcVm.WordAt d.dmem (off (fb m0) 64) (.ofBitVec (fpA m0))
  w80 : NativeRustcVm.WordAt d.dmem (off (fb m0) 80) (.ofBitVec (tA m0))
  ts : TStateAt d.dmem (tA m0) a s1
  pt : NativeRustcVm.EWsAt d.dmem (off (fb m0) 112) xs.toList.reverse
  w : NativeRustcVm.EWsAt d.dmem (off (fb m0) 592) (tableWeights heights bus.point xs.reverse).toList
  r13 : reg d .r13 = BitVec.ofNat 64 (nR heights)
  rbx : reg d .rbx = hA m0
  rbp : reg d .rbp = bA m0
  r12 : reg d .r12 = off (fb m0) 592
  r14 : reg d .r14 = c.c1.toBitVec
  r15 : reg d .r15 = off (fb m0) 112

end

public section

theorem off_fb (m0 : MachineData) {j : Nat} (hj : j ≤ 736) (o : Nat) :
    off (fb m0) (j + o) = off (stackBelow m0 (736 - j)) o := by
  rw [← off_off, off_frame_eq hj]

variable [Labels] {a : DecArea} {s s1 : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

/-- **Bytes of the frame kept by a call** at offset `o` changing a part of the frame and its
stack. -/
theorem keepB_call (h : TableSumcheckPre a s heights bus m0) {d d' : MachineData} {o : Nat}
    (hb : Bd m0 736 N slots (outs m0) o d) (ho : o ≤ 40) {Nc : Nat} (hn : 736 - o + Nc ≤ N)
    {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {j : Nat} {bs : List UInt8} (hj : o + 8 ≤ j) (hjb : j + bs.length ≤ 744)
    (hRo : ∀ i < bs.length, ¬ Ro (off (fb m0) (j + i)))
    (hx : NativeRustcVm.BytesAt d.dmem (off (fb m0) j) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fb m0) j) bs := by
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  refine NativeRustcVm.BytesAt.of_sameOutside hx hso fun i hi hq ↦ ?_
  rw [off_add] at hq
  rcases hq with hq | hq
  · exact hRo i hi hq
  · exact (hb.callee_in hS (by omega) hn hq).2
      ((inRange_off_iff (by omega) (by omega)).mpr ⟨by omega, by omega⟩)

omit [Labels] in
theorem slice_eq {d : MachineData} {x : BitVec 64} {L : List EW}
    (hx : NativeRustcVm.EWsAt d.dmem x L) {n : Nat} (hn : L.length = n) (hn' : n < 2 ^ 64) :
    slice d x (BitVec.ofNat 64 n) = L.toArray := by
  unfold slice
  rw [toNat_ofNat_lt hn', ← hn, NativeRustcVm.ewsOf_of_ewsAt hx]

end

public section

variable [Host] {k : Nat} {a : DecArea} {s s1 : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} {xs : Array EW} {c : EW}

/-- **The weights** (`b10`). -/
theorem weights (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0)
    (hw : Spec (Labels.label NativeRustcVmX64.Vm.TableWeights.entryLabel) TableWeightsPre TableWeightsPost)
    (hsz : xs.size = nR heights) {d : MachineData} (K : Kp a s1 heights m0 c d)
    (hpt : NativeRustcVm.EWsAt d.dmem (off (fb m0) 112) xs.toList.reverse)
    (cont : ∀ d', Wt a s1 heights bus m0 xs c d' →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b11Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b10Offset)⟩ := by
  have hS := Pre.stack h
  have hH := Pre.hts h
  have hn30 : nR heights ≤ 30 := foldl_max_le heights hH.1 hH.2.1
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hNle := N_ge
  have hbus := bus_bd h K.bd
  have hpb := hbus.point
  have hpl : bus.point.toList.length ≤ 63 := hpb.1
  rw [Array.length_toList] at hpl
  have hbr : ReadIn m0 (bA m0) 106712 N (wsL m0) := by
    have := rin_sub (Pre.bs h) (o := 0) (k := 106712) (by rw [busBytes_eq]; omega)
    rwa [NativeRustcVm.addr_add_zero] at this
  -- `b10`.
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b10Offset + b10.length)).toBitVec
  have hwf : (E m0 d [(bA m0, 106712)] ra).WF :=
    wf_one h K.bd.fr.kept hbr.1.1 hbr.1.2 (frame_ap h hbr.2.1)
  have hm : Match (E m0 d [(bA m0, 106712)] ra) busS d := by
    refine match_body K.bd ⟨rfl, rfl, trivial⟩ ⟨?_, trivial⟩
    show (Sym.load 0 72 8).eval (E m0 d [(bA m0, 106712)] ra) = _
    rw [ld0 K.w72, ofInt_zero64, BitVec.add_zero]
    rfl
  refine exec_then (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf (fun _ _ ↦ rfl) hm
    fun st hm1 hpc1 ↦ ?_
  obtain ⟨mid1, W1, wr1, w48, r14_1, rcx1, rdx1, rsi1, rdi1, rbp1, r8_1, r9_1, r12_1, r15_1, k1⟩ :=
    ok_b10
  obtain ⟨hb1, hso1⟩ := blockB h K.bd hwf hm1 mid1 W1
  have hin1 := writesIn_of_mid mid1
  have rg : ∀ {r : Reg64} {v : Sym}, (after b10 busS).reg r = some v →
      reg st.data r = v.eval (E m0 d [(bA m0, 106712)] ra) := fun hv ↦ hm1.regs _ _ hv
  have kw : ∀ {o : Nat} {w : UInt64}, 56 ≤ o → o + 8 ≤ 744 →
      NativeRustcVm.WordAt d.dmem (off (fb m0) o) w →
      NativeRustcVm.WordAt st.data.dmem (off (fb m0) o) w := fun h1 h2 hx ↦
    keepW hwf hm1 hin1 (by omega) (fun w hw _ ↦ by have := wr1 w hw; omega) hx
  have hcl := NativeRustcVm.ewAt_iff.mp K.cl
  rw [off_add] at hcl
  have t1 : TStateAt st.data.dmem (tA m0) a s1 :=
    K.ts.frame (hm1.kept hwf) (fun q hq ↦ (ctx h).stack_not_t (fr_stack h hq)) hso1
  have pt1 : NativeRustcVm.EWsAt st.data.dmem (off (fb m0) 112) xs.toList.reverse :=
    keep_frame hwf hm1 hin1 (o := 112) (bs := xs.toList.reverse.flatMap NativeRustcVm.ewBytes)
      (by rw [NativeRustcVm.length_ewsBytes, List.length_reverse, Array.length_toList]; omega)
      (fun w hw _ ↦ by have := wr1 w hw; omega) hpt
  have w48' : NativeRustcVm.WordAt st.data.dmem (off (fb m0) 48) c.c0 :=
    wroteW hm1 (by omega) w48 (ld0 hcl.1)
  -- The registers.
  have hlw : (E m0 d [(bA m0, 106712)] ra).load 1 106704 8 =
      BitVec.ofNat 64 bus.point.size := by
    refine (load_of_wordAt (w := bus.point.toList.length.toUInt64) ?_).trans ?_
    · exact hpb.2.1
    · apply BitVec.eq_of_toNat_eq
      rw [UInt64.toNat_toBitVec, Array.length_toList, toNat_toUInt64 (by omega),
        toNat_ofNat_lt (by omega)]
  have hult : (SBool.cmp .ult .W64 (.load 1 106704 8) (.lit 64)).eval
      (E m0 d [(bA m0, 106712)] ra) = true := by
    show CmpOp.apply .ult .W64 ((E m0 d [(bA m0, 106712)] ra).load 1 106704 8)
      (BitVec.ofNat 64 64) = true
    rw [hlw]
    simp only [CmpOp.apply, low_W64, BitVec.ult, decide_eq_true_eq]
    rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
    omega
  have e_rcx : reg st.data .rcx = BitVec.ofNat 64 bus.point.size := by
    rw [rg rcx1]
    show (if (SBool.cmp .ult .W64 (.load 1 106704 8) (.lit 64)).eval
      (E m0 d [(bA m0, 106712)] ra) then _ else _) = _
    rw [hult]
    exact hlw
  have e_rdx : reg st.data .rdx = bA m0 + BitVec.ofNat 64 106712 := by
    rw [rg rdx1]
    show (if (SBool.cmp .ult .W64 (.load 1 106704 8) (.lit 64)).eval
      (E m0 d [(bA m0, 106712)] ra) then _ else _) = _
    rw [hult]
    show BinOp.apply .add .W64 ((E m0 d [(bA m0, 106712)] ra).load 0 72 8) _ = _
    rw [show (E m0 d [(bA m0, 106712)] ra).load 0 72 8 = bA m0 from ld0 K.w72, add_apply]
    rfl
  have e_rsi : reg st.data .rsi = hA m0 := (rg rsi1).trans K.rbx
  have e_rdi : reg st.data .rdi = off (fb m0) 592 := (rg rdi1).trans (eval_ptr0 592)
  have e_r8 : reg st.data .r8 = off (fb m0) 112 := (rg r8_1).trans (eval_ptr0 112)
  have e_r9 : reg st.data .r9 = BitVec.ofNat 64 (nR heights) := (rg r9_1).trans K.r13
  -- `table_weights`' precondition.
  have hat : At m0 704 st.data := Bd.atO h (by omega) hb1
  have c704 := ctxF h (F := 704) (by omega)
  have hle : 704 + tableWeightsStack ≤ N := by omega
  have o592 := c704.outOk_frame hat hle (o := 560) (n := 96) (by omega) (by omega)
  have o112 := c704.outOk_frame hat hle (o := 80) (n := 16 * nR heights) (by omega) (by omega)
  rw [← off_fb m0 (j := 32) (by omega)] at o592 o112
  have hbp := rin_sub (Pre.bs h) (o := 106712) (k := 16 * bus.point.size)
    (by rw [busBytes_eq]; omega)
  have hpre : TableWeightsPre st.data := by
    refine ⟨hb1.stackOk_at hS (by omega) (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_rdi]; exact ⟨o592.1, o592.2.1⟩
    · rw [e_rdi]; exact o592.2.2.2.2.1
    · rw [e_rsi]
      exact ⟨⟨Mapped.keeps (Pre.hs h).1.1 hb1.fr.kept, (Pre.hs h).1.2⟩,
        hb1.apart_at hS (by omega) (by omega) (Pre.hs h).2.1, nofun⟩
    · unfold SliceOk
      rw [e_rdx, e_rcx, toNat_ofNat_lt (by omega)]
      exact ⟨⟨Mapped.keeps hbp.1.1 hb1.fr.kept, hbp.1.2⟩,
        hb1.apart_at hS (by omega) (by omega) hbp.2.1⟩
    · unfold SliceOk
      rw [e_r8, e_r9, toNat_ofNat_lt (by omega)]
      exact ⟨⟨o112.1, o112.2.1⟩, o112.2.2.2.2.1⟩
  simp only [PcOk] at hpc1
  refine call_then (env := E m0 d [(bA m0, 106712)] ra) hpc1 hw hpre fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨q1, q2, q3⟩ := hq
  unfold Changes at q2
  rw [e_rdi] at q1 q2
  have hb2 := call_frame h hb1 (by omega) (by omega) q3 hrsp2
    (Ro := NativeRustcVm.InRange (off (fb m0) 592) 96) q2 fun q hq ↦ .inr ⟨592, 96, by omega, hq⟩
  have kb : ∀ {j : Nat} {bs : List UInt8}, 40 ≤ j → j + bs.length ≤ 592 →
      NativeRustcVm.BytesAt st.data.dmem (off (fb m0) j) bs →
      NativeRustcVm.BytesAt st2.data.dmem (off (fb m0) j) bs := fun h1 h2 hx ↦
    keepB_call h hb1 (by omega) (by omega) q2 (by omega) (by omega) (fun i hi hq ↦ by
      change NativeRustcVm.InRange (off (fb m0) 592) 96 _ at hq
      rw [inRange_off_iff (by omega) (by omega)] at hq; omega) hx
  have kbw : ∀ {j : Nat} {w : UInt64}, 40 ≤ j → j + 8 ≤ 592 →
      NativeRustcVm.WordAt st.data.dmem (off (fb m0) j) w →
      NativeRustcVm.WordAt st2.data.dmem (off (fb m0) j) w := fun h1 h2 hx ↦
    kb h1 (by rw [NativeRustcVm.length_wordBytes]; omega) hx
  have kr : ∀ r, calleeSaved r = true → reg st2.data r = reg st.data r := fun r hr ↦ q3.1 r hr
  -- The weights.
  have hh : heightsOf st.data.dmem (reg st.data .rsi) = heights := by
    rw [e_rsi]; exact heightsOf_eq (heights_bd h hb1)
  have sp1 : slice st.data (reg st.data .rdx) (reg st.data .rcx) = bus.point := by
    rw [e_rdx, e_rcx]
    have := (bus_bd h hb1).point.2.2
    rw [show off (bA m0) busPointOff + 8#64 = bA m0 + BitVec.ofNat 64 106712 by
      rw [off, busPointOff_eq, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
        NativeRustcVm.addr_add_add]] at this
    rw [slice_eq (d := st.data) this Array.length_toList (by omega)]
  have sp2 : slice st.data (reg st.data .r8) (reg st.data .r9) = xs.reverse := by
    rw [e_r8, e_r9, slice_eq pt1 (by rw [List.length_reverse, Array.length_toList, hsz])
      (by omega)]
    exact Array.toList_inj.mp (by simp)
  rw [hh, sp1, sp2] at q1
  refine at_pc (hpc2.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b10_next)))
    (cont st2.data ⟨hb2, kbw (by omega) (by omega) w48', kbw (by omega) (by omega) (kw (by omega)
      (by omega) K.w56), kbw (by omega) (by omega) (kw (by omega) (by omega) K.w64),
      kbw (by omega) (by omega) (kw (by omega) (by omega) K.w80), ?_, ?_, q1, ?_, ?_, ?_, ?_, ?_,
      ?_⟩)
  · refine t1.frame q3.2 (fun q hq ↦ (ctx h).stack_not_t ?_) q2
    rcases hq with hq | hq
    · exact loc_stack h (by omega) hq
    · exact (hb1.callee_in hS (by omega) (by omega) hq).1
  · exact kb (by omega) (by rw [NativeRustcVm.length_ewsBytes, List.length_reverse,
      Array.length_toList]; omega) pt1
  · rw [kr .r13 rfl, keeps_reg hm1 k1 (by simp)]; exact K.r13
  · rw [kr .rbx rfl, keeps_reg hm1 k1 (by simp)]; exact K.rbx
  · rw [kr .rbp rfl, rg rbp1]; exact ld0 K.w72
  · rw [kr .r12 rfl, rg r12_1]; exact eval_ptr0 592
  · rw [kr .r14 rfl, rg r14_1]; exact ld0 hcl.2
  · rw [kr .r15 rfl, rg r15_1]; exact eval_ptr0 112

end

end NativeRustcVmX64.Tables.TableSumcheck
