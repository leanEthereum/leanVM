module

public import NativeRustcVmX64.Sumcheck.RoundPoly.NoneRead
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `sumcheck_round_poly`'s entry (x86-64)

`b0` pushes the registers (the prologue) and tests `eq`'s tag. In equality mode `b1` saves the
claim and the factor's limb `0` in the frame, its limb `1` in R15, and calls `read_scalars` for
`msg[1..count]` (`some_entry`, then `some_tail`); in plain mode `b9` calls `read_scalar` into the
frame at `40` (`none_entry`, then `none_b10`).
-/

namespace NativeRustcVmX64.Sumcheck.RoundPoly

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateSumcheckRoundPoly
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The entry's environment: the frame, `n` bytes of `eq`. -/
abbrev env0 (m0 : MachineData) (n : Nat) (ret : BitVec 64) : Env :=
  frameEnv m0 m0 112 [(reg m0 .r8, n)] (fun _ ↦ 0) ret

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 112 := by decide

theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

section
variable [Labels] {a : DecArea} {s : TState} {e : Option EW} {m0 : MachineData}

theorem wf_env0 (h : RoundPolyPre a s e m0) {n : Nat} (hn : n ≤ 24)
    (hmap : NativeRustcVm.Mapped m0.dmem (reg m0 .r8) n) (ret : BitVec 64) :
    (env0 m0 n ret).WF := by
  have c := ctx_of h
  have hA := apart_frame (F := 112) h.2.2.2.2.2.2.2.2.1 c.spN (by rw [roundPolyStack_eq]; omega)
  refine frame_wf ⟨frame_mapped c.stack (by rw [roundPolyStack_eq]; omega), c.noWrap_frame⟩
    (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hx
    subst hx
    exact ⟨hmap, NativeRustcVm.NoWrap.mono h.2.2.2.2.2.2.2.1 hn⟩
  · show NativeRustcVm.Apart (stackBelow m0 112) (112 + 8) (reg m0 .r8) n
    unfold NativeRustcVm.Apart at hA ⊢
    omega

theorem match_env0 (n : Nat) (ret : BitVec 64) :
    Match (env0 m0 n ret) (init [120, n] [(.rsp, .ptr 0 112), (.r8, .ptr 1 0)]) m0 :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
    trivial

/-- **The prologue's frame** after `b0` and `b1`/`b9` (`S`, writes only below the frame's offset
`112`): RBX the message. -/
theorem rf_entry (h : RoundPolyPre a s e m0) {n : Nat} {ret : BitVec 64}
    (hwf : (env0 m0 n ret).WF) {S : SState} {d : MachineData} (hm : Match (env0 m0 n ret) S d)
    (hpro : ProOk 112 0 slots S = true) (hall : ∀ w ∈ S.mem, w.r = 0)
    (hrbx : S.reg .rbx = some (.reg .r9)) :
    RF m0 0 d ∧ NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (fa m0) 112) := by
  have hs : NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (fa m0) 112) :=
    sameOutside_low hwf hm (r := 0) rfl (hi := 112) (by omega) fun w hw ↦
      ⟨hall w hw, belowRet_spec (belowRet_of_pro hpro) w hw (hall w hw)⟩
  exact ⟨⟨Frame.of_prologue Frame.entry hwf hm hpro slots_le slots_cs,
    SameOutside.mono hs fun q hq ↦ chg_frame h hq, hm.regs .rbx _ hrbx⟩, hs⟩

end

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **Equality mode**: `b0`, `b1` saves the claim and the factor and calls `read_scalars` for
`msg[1..count]`, then `some_tail`. -/
theorem some_entry (hp : Placed code k)
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {ev : EW} (h : RoundPolyPre a s (some ev) m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        RoundPolyPost a s (some ev) m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b0Offset)⟩ := by
  have c := ctx_of h
  have hc2 : 2 ≤ cnt m0 := h.2.2.2.2.1
  have hc5 : cnt m0 ≤ 5 := h.2.2.2.2.2.1
  obtain ⟨htag, hev⟩ : OptEWAt m0.dmem (reg m0 .r8) (some ev) := h.2.2.2.2.2.2.1
  have hev' := ewAt_iff.mp hev
  rw [off_off] at hev'
  have hmap : NativeRustcVm.Mapped m0.dmem (reg m0 .r8) 24 :=
    NativeRustcVm.mapped_append_iff (n := 8) (m := 16) |>.2 ⟨htag.mapped, hev.mapped⟩
  let R := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b1Offset + b1.length)).toBitVec
  have hwf := wf_env0 h le_rfl hmap R
  have hm : Match (env0 m0 24 R) entryS m0 := match_env0 24 R
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf nofun hm
    fun st0 hm0 hpc0 ↦ ?_
  have htag1 : (env0 m0 24 R).load 1 0 1 = BitVec.ofNat 64 1 :=
    load1_of_tag (Or.inr rfl) (by
      show NativeRustcVm.WordAt m0.dmem (off (reg m0 .r8) 0) 1
      rw [off_zero]; exact htag)
  have hc0 : c0.eval (env0 m0 24 R) = false := by
    show CmpOp.apply .eq .W8 ((env0 m0 24 R).load 1 0 1) (BitVec.ofNat 64 0) = false
    rw [htag1]; decide
  simp only [PcOk] at hpc0
  rw [hc0] at hpc0
  simp (config := { decide := true }) only [↓reduceIte] at hpc0
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf (fun _ _ ↦ rfl)
    (hpc0.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b0_next)) hm0 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hrdi, hrsi, hrdx, hrbx, hr12, hr13, hr14, hr15, hW8, hW16, hW32, hall⟩ := ok_some
  obtain ⟨hf1, hs1⟩ := rf_entry h hwf hm1 hpro hall hrbx
  have hat1 := hf1.at h
  have hrdi1 : reg st1.data .rdi = tAt m0 := hm1.regs .rdi _ hrdi
  have hrsi1 : reg st1.data .rsi = off (msgAt m0) 16 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rfl
  have hr14_1 : reg st1.data .r14 = off (msgAt m0) 16 := by
    rw [show reg st1.data .r14 = _ from hm1.regs .r14 _ hr14]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rfl
  have hrdx1 : (reg st1.data .rdx).toNat = cnt m0 - 1 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx]
    exact toNat_sub_one' (x := reg m0 .rsi) (show 1 ≤ cnt m0 by omega)
  have ts1 : TStateAt st1.data.dmem (tAt m0) a s :=
    tstate_keep h hs1 (hm1.kept hwf) (fun q hq ↦ Or.inr (frame_in h hq)) h.2.2.1
  have w8_1 : NativeRustcVm.WordAt st1.data.dmem (off (fa m0) 8) (claimOf m0).c0 :=
    wordAt_written hm1 (r := 0) rfl (by omega) hW8 rfl
  have w16_1 : NativeRustcVm.WordAt st1.data.dmem (off (fa m0) 16) (claimOf m0).c1 :=
    wordAt_written hm1 (r := 0) rfl (by omega) hW16 rfl
  have w32_1 : NativeRustcVm.WordAt st1.data.dmem (off (fa m0) 32) ev.c0 :=
    wordAt_written hm1 (r := 0) rfl (by omega) hW32 (load_ofMachine (o := 8) rfl hev'.1)
  refine call_then hpc1 (hrss a s) ?pre fun st2 hpc2 hrsp2 hpost2 ↦ ?_
  case pre =>
    unfold ReadScalarsPre
    rw [hrdi1, hrsi1, hrdx1]
    refine ⟨c.stackOk hat1 (by decide), c.rcAt hat1 (by decide), ts1,
      c.tstateOk hat1 (by decide), msgOut h hat1 (by decide) (by omega) (by omega), ?_⟩
    apply hf1.gotAt h (by decide)
    intro l hl x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact got_area h hl (by simp)
    · exact got_area h hl (by simp)
    · exact got_msg h hl (by omega) (by omega)
    · exact got_area h hl (by simp)
  simp only [ReadScalarsPost, hrdi1, hrsi1, hrdx1] at hpost2
  obtain ⟨hok2, hxs2, hnext2, hs2, hsv2⟩ := hpost2
  have hR2 : ∀ q, (NativeRustcVm.InRange (off (msgAt m0) 16) (16 * (cnt m0 - 1)) q ∨
      NativeRustcVm.InRange (tAt m0) tstateBytes q) → Chg m0 q ∧ NotHigh m0 q := by
    rintro q (hq | hq)
    · have hq' := msg_part h (by omega) (by omega) hq
      exact ⟨Or.inl hq', notHigh_of_not_frame h (not_frame_msg h hq')⟩
    · exact ⟨Or.inr (Or.inl hq), notHigh_of_not_frame h (not_frame_t h hq)⟩
  have hs2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      (NativeRustcVm.InRange (off (msgAt m0) 16) (16 * (cnt m0 - 1)) q ∨
        NativeRustcVm.InRange (tAt m0) tstateBytes q) ∨
      NativeRustcVm.InRange (stackBelow st1.data readScalarsStack) readScalarsStack q) :=
    fun q hq ↦ hs2 q fun h' ↦ hq (or_assoc.mpr h')
  have hf2 : RF m0 8 st2.data :=
    hf1.call h (Nc := readScalarsStack) (by decide) hsv2 hrsp2 hR2 hs2'
  have kc2 := fun {o : Nat} {w : UInt64} (ho : 8 ≤ o) (hon : o + 8 ≤ 112) ↦
    keepW_call (w := w) h hat1 (Nc := readScalarsStack) (by decide)
      (fun q hq ↦ hq.elim (fun hq ↦ not_frame_msg h (msg_part h (by omega) (by omega) hq))
        (fun hq ↦ not_frame_t h hq)) hs2' ho hon
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2
  subst hpc2
  rw [NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b1_length]
  refine some_tail hp hsum hbl hgr hmul h
    ⟨hf2, (hsv2.1 .r12 rfl).trans (hm1.regs .r12 _ hr12), ?_,
      (hsv2.1 .r14 rfl).trans hr14_1,
      (hsv2.1 .r15 rfl).trans ((hm1.regs .r15 _ hr15).trans (load_ofMachine (o := 16) rfl hev'.2)),
      kc2 (by omega) (by omega) w8_1, kc2 (by omega) (by omega) w16_1,
      kc2 (by omega) (by omega) w32_1⟩ hok2 fun tail s1 h' ↦ ⟨hxs2 tail s1 h', hnext2 tail s1 h'⟩
  rw [show reg d2 .r13 = _ from (hsv2.1 .r13 rfl).trans (hm1.regs .r13 _ hr13)]
  exact toNat_sub_one' (x := reg m0 .rsi) (show 1 ≤ cnt m0 by omega)

/-- **Plain mode**: `b0`, `b9` calls `read_scalar` into the frame's `Option<EW>` at `40`, then
`none_b10`. -/
theorem none_entry (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (h : RoundPolyPre a s none m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        RoundPolyPost a s none m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b0Offset)⟩ := by
  have c := ctx_of h
  have htag : NativeRustcVm.WordAt m0.dmem (reg m0 .r8) 0 := h.2.2.2.2.2.2.1
  let R := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b9Offset + b9.length)).toBitVec
  have hwf := wf_env0 h (n := 8) (by omega) htag.mapped R
  have hm : Match (env0 m0 8 R) entryN m0 := match_env0 8 R
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0n hwf nofun hm
    fun st0 hm0 hpc0 ↦ ?_
  have htag0 : (env0 m0 8 R).load 1 0 1 = BitVec.ofNat 64 0 :=
    load1_of_tag (Or.inl rfl) (by
      show NativeRustcVm.WordAt m0.dmem (off (reg m0 .r8) 0) 0
      rw [off_zero]; exact htag)
  have hc0 : c0.eval (env0 m0 8 R) = true := by
    show CmpOp.apply .eq .W8 ((env0 m0 8 R).load 1 0 1) (BitVec.ofNat 64 0) = true
    rw [htag0]; decide
  simp only [PcOk] at hpc0
  rw [hc0] at hpc0
  simp (config := { decide := true }) only [↓reduceIte] at hpc0
  rw [hp.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_4_at] at hpc0
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf (fun _ _ ↦ rfl) hpc0 hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hrdi, hrsi, hrbx, hr12, hr13, hr14, hr15, hall⟩ := ok_none
  obtain ⟨hf1, hs1⟩ := rf_entry h hwf hm1 hpro (fun w hw ↦ by
    rcases hall w hw with ⟨h', -⟩ | ⟨h', -⟩ <;> exact h') hrbx
  have hat1 := hf1.at h
  have hrdi1 : reg st1.data .rdi = off (fa m0) 40 := (hm1.regs .rdi _ hrdi).trans (eval_ptr0 40)
  have hrsi1 : reg st1.data .rsi = tAt m0 := hm1.regs .rsi _ hrsi
  have ts1 : TStateAt st1.data.dmem (tAt m0) a s :=
    tstate_keep h hs1 (hm1.kept hwf) (fun q hq ↦ Or.inr (frame_in h hq)) h.2.2.1
  refine call_then hpc1 (hrs a s) ?pre fun st2 hpc2 hrsp2 hpost2 ↦ ?_
  case pre =>
    unfold ReadScalarPre
    rw [hrdi1, hrsi1]
    refine ⟨c.stackOk hat1 (by decide), c.rcAt hat1 (by decide), ts1,
      c.tstateOk hat1 (by decide), c.outOk_frame hat1 (by decide) (o := 40) (n := 24) (by omega)
        (by omega), ?_⟩
    apply hf1.gotAt h (by decide)
    intro l hl x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact got_area h hl (by simp)
    · exact got_area h hl (by simp)
    · exact got_frame h hl (by omega)
    · exact got_area h hl (by simp)
  simp only [ReadScalarPost, hrdi1, hrsi1] at hpost2
  obtain ⟨hopt2, hnext2, hs2, hsv2⟩ := hpost2
  have hfnw := c.noWrap_frame
  have hR2 : ∀ q, (NativeRustcVm.InRange (off (fa m0) 40) 24 q ∨
      NativeRustcVm.InRange (tAt m0) tstateBytes q) → Chg m0 q ∧ NotHigh m0 q := by
    rintro q (hq | hq)
    · exact ⟨chg_frame h (inRange_of_off (hfnw.mono (by omega)) (by omega) hq),
        notHigh_out h hq⟩
    · exact ⟨Or.inr (Or.inl hq), notHigh_of_not_frame h (not_frame_t h hq)⟩
  have hs2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      (NativeRustcVm.InRange (off (fa m0) 40) 24 q ∨
        NativeRustcVm.InRange (tAt m0) tstateBytes q) ∨
      NativeRustcVm.InRange (stackBelow st1.data readScalarStack) readScalarStack q) :=
    fun q hq ↦ hs2 q fun h' ↦ hq (or_assoc.mpr h')
  have hf2 : RF m0 8 st2.data :=
    hf1.call h (Nc := readScalarStack) (by decide) hsv2 hrsp2 hR2 hs2'
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2
  subst hpc2
  rw [NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b9_length]
  exact none_b10 hp hrss hsum hbl hgr h
    ⟨hf2, (hsv2.1 .r12 rfl).trans (hm1.regs .r12 _ hr12),
      by rw [show reg d2 .r13 = _ from (hsv2.1 .r13 rfl).trans (hm1.regs .r13 _ hr13)]; rfl,
      (hsv2.1 .r14 rfl).trans (hm1.regs .r14 _ hr14),
      (hsv2.1 .r15 rfl).trans (hm1.regs .r15 _ hr15), hopt2, hnext2⟩

end

end NativeRustcVmX64.Sumcheck.RoundPoly
