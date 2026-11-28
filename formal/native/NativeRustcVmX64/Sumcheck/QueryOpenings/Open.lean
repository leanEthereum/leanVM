module

public import NativeRustcVmX64.Sumcheck.QueryOpenings.Ok
public import NativeVm.Equiv.Transcript
public import NativeRustcVmX64.Code.Vm.OpenPhase.Names

/-!
# `TState::query_openings` from `b3`: `open_phase`, its result tested (x86-64)

`b3` (`k + NativeRustcVmX64.Vm.TStateQueryOpenings.b3Offset`, the phase's address in RAX) stores the phase's address as `open_phase`'s stack
argument (the frame's `8`) and calls it with its output at the frame's `16`, root `i`
(`t + 368 + 48 i`, its height and width), the positions (`open_pre`: its precondition); `b4`
(`k + NativeRustcVmX64.Vm.TStateQueryOpenings.b4Offset`) tests the `Option<Rows>`'s first word: `0` goes to `b6` (`finish_fail`), the rows to
`b5` (`finish_ok`). `open_spec` runs it all.
-/

namespace NativeRustcVmX64.Sumcheck.QueryOpenings

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateQueryOpenings
open NativeRustcVm.Transcript NativeVm NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeRustcVm.Sumcheck

public section

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-- The model at root `i` and phase `s.phase`, both there: `openPhase`'s result, the phase
advanced. -/
theorem run_some {s : TState} {i : Nat} {Q : Array UInt64} (hi : i < s.roots.size)
    (hlt : s.phase < s.openings.size) :
    (queryOpenings i Q).run s = (openPhase s.roots[i].digest s.roots[i].height s.roots[i].width Q
      s.openings[s.phase]).map fun rows ↦ (rows, { s with phase := s.phase + 1 }) := by
  rw [NativeVm.Equiv.queryOpenings_run, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hlt]

/-- `rootSym`'s value: `t + 48 i`. -/
theorem rootSym_eval [Labels] {env : Env} {t : BitVec 64} {i : Nat}
    (hb : env.regs .rbx = t) (hp : (env.regs .rbp).toNat = i) :
    rootSym.eval env = off t (48 * i) := by
  simp only [rootSym, Sym.eval, BinOp.apply, low_W64, ext_W64, hb]
  rw [show shiftCount .W64 (BitVec.ofNat 64 4) = 4 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hp,
    BitVec.toNat_ofNat, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  omega

variable [Host] {k : Nat}

/-- **`open_phase`'s precondition** at `b3`'s call. -/
theorem open_pre {a : DecArea} {s : TState} {Q : Array UInt64} {m0 : MachineData}
    (hpre : QueryOpeningsPre a s Q m0) (hi : (reg m0 .rdx).toNat < s.roots.size)
    (hlt : s.phase < s.openings.size) {d : MachineData} (hf : Frame m0 96 slots 0 d)
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Stk m0))
    (hsa : stackArg d 0 = a.word (phaseBase a.l s.phase))
    (hdi : reg d .rdi = off (stackBelow m0 96) 16)
    (hsi : reg d .rsi = off (reg m0 .rsi) (368 + 48 * (reg m0 .rdx).toNat))
    (hr8 : reg d .r8 = reg m0 .rcx) (hr9 : reg d .r9 = reg m0 .r8) :
    OpenPhasePre s.openings[s.phase] s.roots[(reg m0 .rdx).toNat].digest Q d := by
  have c := ctx hpre
  have hts := tstate_stk hpre hf.kept hs
  have hsp : rspOf d = stackBelow m0 96 := by rw [hf.sp, off_zero]
  have hAt : At m0 96 d := At.of_frame hf (rc_keep hs fun q hq ↦ c.not_rc_stack hq)
  simp only [OpenPhasePre]
  rw [hdi, hsi, hr8, hr9, hsa]
  obtain ⟨hst, hrc, -, htok, hQn, hQw, hpnw, hpS, hpA, hout, hop, hg⟩ := hpre
  set t := reg m0 .rsi
  set i := (reg m0 .rdx).toNat
  set fb := stackBelow m0 96
  set ph := a.word (phaseBase a.l s.phase)
  set rb := off t (368 + 48 * i)
  set pos := reg m0 .rcx
  set n := (reg m0 .r8).toNat
  have hN : queryOpeningsStack = 1280 := rfl
  have hO : openPhaseStack = 1184 := rfl
  have hTB : tstateBytes = 760 := rfl
  have hPW := phaseWords_eq
  have hn : queryOpeningsStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfb : fb.toNat = (rspOf m0).toNat - 96 := stackBelow_toNat (by omega)
  have hS0 : (stackBelow m0 queryOpeningsStack).toNat = (rspOf m0).toNat - 1280 :=
    stackBelow_toNat hn
  have hS : (stackBelow d openPhaseStack).toNat = (rspOf m0).toNat - 1280 := by
    rw [stackBelow_callee hsp (by omega), stackBelow_toNat (by omega)]
    omega
  obtain ⟨⟨-, hTn⟩, ⟨hAm, hAn⟩, hTA⟩ := hts.footprint
  have hTn' : t.toNat + tstateBytes ≤ 2 ^ 64 := hTn
  have hAn' : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hAn
  have htS : t.toNat + tstateBytes ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + (queryOpeningsStack + 8) ≤ t.toNat := htok.1
  have haS : a.words.toNat + 8 * a.len ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + (queryOpeningsStack + 8) ≤ a.words.toNat :=
    htok.2.1
  have hpnw' : pos.toNat + 8 * n ≤ 2 ^ 64 := hpnw
  have hpS' : pos.toNat + 8 * n ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + (queryOpeningsStack + 8) ≤ pos.toNat := hpS
  have hpA' : pos.toNat + 8 * n ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ pos.toNat := hpA
  have hrcN : rcAddr.toNat + 192 ≤ 2 ^ 64 := hrc.2.1
  have hrcS : rcAddr.toNat + 192 ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + (queryOpeningsStack + 8) ≤ rcAddr.toNat :=
    hrc.2.2
  have hi8 : i < 8 := Nat.lt_of_lt_of_le hi hts.roots_le
  have hrb : rb.toNat = t.toNat + (368 + 48 * i) := toNat_off (by omega)
  have hphl : phaseBase a.l s.phase + phaseWords ≤ a.len :=
    Nat.le_trans (phaseBase_add_le (Nat.lt_of_lt_of_le hlt hts.decoded.phases_le)) hts.decoded.len
  have hph : ph.toNat = a.words.toNat + 8 * phaseBase a.l s.phase := toNat_off (by omega)
  have hout' : (off fb 16).toNat = (rspOf m0).toNat - 96 + 16 := by
    rw [toNat_off (by omega), hfb]
  have hroot := hts.roots i hi
  have hfm : NativeRustcVm.Mapped d.dmem fb (96 + 8) :=
    Mapped.keeps (frame_mapped hst (by decide)) hf.kept
  have hgot : GotAt d openPhaseStack
      [(ph, 8 * phaseWords), (rb, 32), (pos, 8 * n), (off fb 16, 32), (rcAddr, 192)]
      ["memcpy", "memset"] := by
    refine c.gotAt hAt (by decide) hg hs (fun _ hq ↦ Or.inl hq) ?_
    intro l hl x hx
    have ht := (hg.1 l hl).2.2.2 (t, tstateBytes) (by simp [t])
    have ha := (hg.1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
    have hstk := (hg.1 l hl).2.2.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · change (gotAddr l).toNat + 8 ≤ ph.toNat ∨
        ph.toNat + 8 * phaseWords ≤ (gotAddr l).toNat
      change (gotAddr l).toNat + 8 ≤ a.words.toNat ∨
        a.words.toNat + 8 * a.len ≤ (gotAddr l).toNat at ha
      rw [hph]
      omega
    · change (gotAddr l).toNat + 8 ≤ rb.toNat ∨
        rb.toNat + 32 ≤ (gotAddr l).toNat
      change (gotAddr l).toNat + 8 ≤ t.toNat ∨
        t.toNat + tstateBytes ≤ (gotAddr l).toNat at ht
      rw [hrb]
      omega
    · exact (hg.1 l hl).2.2.2 _ (by simp [pos, n])
    · exact c.apart_of_stack hstk (by omega)
    · exact (hg.1 l hl).2.2.2 _ (by simp)
  refine ⟨c.stackOk hAt (by decide), c.rcAt hAt (by decide), ⟨?_, ?_⟩,
    hts.decoded.phases s.phase hlt, hroot.2.2.1, hQn,
    wordsAt_stk (ws := Q.toList) hst hs (by rw [Array.length_toList, hQn]; exact hpnw)
      (by rw [Array.length_toList, hQn]; exact hpS) hQw,
    mapped_off hAm (by show 8 * phaseBase a.l s.phase + 8 * phaseWords ≤ 8 * a.len; omega),
    ?_, ?_, ?_, mapped_off hfm (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hgot⟩
  · rw [hsp]
    exact mapped_off (o := 8) hfm (by omega)
  all_goals first
    | (show _ ≤ _; rw [hsp]; omega)
    | (show _ ≤ _; omega)
    | (show _ ∨ _; omega)

/-- **From `b3`**: `open_phase` called, its result tested, the function finished. -/
theorem open_spec (hp : Placed code k)
    (hop : ∀ P R Q, Spec (Labels.label NativeRustcVmX64.Vm.OpenPhase.entryLabel) (OpenPhasePre P R Q) (OpenPhasePost P R Q))
    {a : DecArea} {s : TState} {Q : Array UInt64} {m0 : MachineData}
    (hpre : QueryOpeningsPre a s Q m0) (hi : (reg m0 .rdx).toNat < s.roots.size)
    (hlt : s.phase < s.openings.size) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b3Offset))
    (hf : Frame m0 96 slots 8 st.data)
    (hs : NativeRustcVm.SameOutside m0.dmem st.data.dmem (Stk m0))
    (hax : reg st.data .rax = a.word (phaseBase a.l s.phase))
    (hbx : reg st.data .rbx = reg m0 .rsi) (hbp : reg st.data .rbp = reg m0 .rdx)
    (h12 : reg st.data .r12 = reg m0 .r8) (h13 : reg st.data .r13 = reg m0 .rcx)
    (h14 : reg st.data .r14 = reg m0 .rdi) (h15 : reg st.data .r15 = s.phase.toUInt64.toBitVec) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ QueryOpeningsPost a s Q m0 st'.data) st := by
  have c := ctx hpre
  have hts := tstate_stk hpre hf.kept hs
  have hst := hpre.1
  set t := reg m0 .rsi
  set i := (reg m0 .rdx).toNat
  set fb := stackBelow m0 96
  set rb := off t (48 * i)
  set ph := a.word (phaseBase a.l s.phase)
  set r := s.roots[i]
  set P := s.openings[s.phase]
  have hn : queryOpeningsStack ≤ (rspOf m0).toNat := hst.1
  have hfnw : NativeRustcVm.NoWrap fb (96 + 8) := frame_noWrap hst (by decide)
  obtain ⟨⟨hTm, hTn⟩, -, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hTF : NativeRustcVm.Apart t 760 fb (96 + 8) := apart_frame c.tok.1 hn (by decide)
  have hi8 : i < 8 := Nat.lt_of_lt_of_le hi hts.roots_le
  have hrb : rb.toNat = t.toNat + 48 * i := toNat_off (by omega)
  have hroot : RootAt st.data.dmem (off t (368 + 48 * i)) r := hts.roots i hi
  -- `b3`: the arguments, `call open_phase`.
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 96) (rest := [(rb, 416)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b3Offset + b3.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      refine ⟨mapped_off hTm (by show 48 * i + 416 ≤ 760; omega), ?_⟩
      show rb.toNat + 416 ≤ 2 ^ 64; omega)
    (List.pairwise_pair.mpr (by
      have h1 : t.toNat + 760 ≤ fb.toNat ∨ fb.toNat + (96 + 8) ≤ t.toNat := hTF
      show fb.toNat + (96 + 8) ≤ rb.toNat ∨ rb.toNat + 416 ≤ fb.toNat; omega))
  have hal : rootSym.eval (frameEnv m0 st.data 96 [(rb, 416)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b3Offset + b3.length)).toBitVec) =
      (frameEnv m0 st.data 96 [(rb, 416)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b3Offset + b3.length)).toBitVec).base 1 + BitVec.ofInt 64 0 := by
    rw [ofInt_zero64, BitVec.add_zero]
    exact rootSym_eval hbx (by show (reg st.data .rbp).toNat = i; rw [hbp])
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf (fun _ _ ↦ rfl) hpc
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial ⟨hal, trivial⟩)
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hmid1, hws1, hw8, hdi1, hsi1, hdx1, hcx1, hr8₁, hr9₁, hkb1⟩ := ok_b3
  have hf1 : Frame m0 96 slots 0 st1.data := Frame.of_block hf hwf hm1 hmid1 slots_le
  have hsp1 : rspOf st1.data = fb := by rw [hf1.sp, off_zero]
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Stk m0) := by
    intro q hq
    rw [← hs q hq]
    exact sameOutside_low hwf hm1 (r := 0) rfl (hi := 16) (by omega) hws1 q
      fun h ↦ hq (frame_stk hst (inRange_mono h (by omega)))
  have hk1 : ∀ r, r ≠ .rsp → [Reg64.rcx, .rdx, .rsi, .rdi, .r8, .r9].contains r = false →
      reg st1.data r = reg st.data r := fun r h1 h2 ↦ KeepBut.regs hkb1 hm1 h1 h2
  have hsa : stackArg st1.data 0 = ph := by
    have := wordAt_write hm1 (r := 0) (o := 8) rfl (by omega) hw8
    rw [show Sym.eval (frameEnv m0 st.data 96 [(rb, 416)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b3Offset + b3.length)).toBitVec) (.reg .rax) = ph from hax] at this
    unfold stackArg
    rw [hsp1, show fb + BitVec.ofNat 64 (8 + 8 * 0) = off fb 8 from rfl,
      NativeRustcVm.wordOf_of_wordAt this]
  have hdi : reg st1.data .rdi = off fb 16 := (hm1.regs .rdi _ hdi1).trans (eval_ptr0 16)
  have hsi : reg st1.data .rsi = off t (368 + 48 * i) := by
    refine (hm1.regs .rsi _ hsi1).trans ?_
    show BinOp.apply .add .W64 (BitVec.ofNat 64 368) (rootSym.eval _) = _
    rw [hal, ofInt_zero64, BitVec.add_zero]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 368) rb = _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [BitVec.add_comm]
    show off (off t (48 * i)) 368 = _
    rw [off_off]
    congr 1
    omega
  have hdx : (reg st1.data .rdx).toNat = r.height := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx1]
    show ((frameEnv m0 st.data 96 [(rb, 416)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b3Offset + b3.length)).toBitVec).load 1 400 8).toNat = _
    rw [load_ofMachine (o := 400) rfl (b := rb) (w := r.height.toUInt64)
      (by rw [show off rb 400 = off (off t (368 + 48 * i)) 32 by
            rw [off_off, off_off]; congr 1; omega]
          exact hroot.2.2.2.1)]
    exact toNat_toUInt64 hroot.1
  have hcx : (reg st1.data .rcx).toNat = r.width := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hcx1]
    show ((frameEnv m0 st.data 96 [(rb, 416)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b3Offset + b3.length)).toBitVec).load 1 408 8).toNat = _
    rw [load_ofMachine (o := 408) rfl (b := rb) (w := r.width.toUInt64)
      (by rw [show off rb 408 = off (off t (368 + 48 * i)) 40 by
            rw [off_off, off_off]; congr 1; omega]
          exact hroot.2.2.2.2)]
    exact toNat_toUInt64 hroot.2.1
  have hr8 : reg st1.data .r8 = reg m0 .rcx := (hm1.regs .r8 _ hr8₁).trans h13
  have hr9 : reg st1.data .r9 = reg m0 .r8 := (hm1.regs .r9 _ hr9₁).trans h12
  refine call_then hpc1 (hop P r.digest Q)
    (open_pre hpre hi hlt hf1 hs1 hsa hdi hsi hr8 hr9) fun st2 hpc2 hrsp2 ⟨hout2, hs2, hsv2⟩ => ?_
  rw [hdi, hsa, hdx, hcx] at hout2
  rw [hdi] at hs2
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st1.data openPhaseStack) openPhaseStack q →
      Stk m0 q ∧ ¬ NativeRustcVm.InRange fb (96 + 8) q :=
    fun q hq ↦ inRange_callee hsp1 hst.2.1 hn (by decide) hq
  have hR : ∀ j, 48 ≤ j → j < 96 + 8 → ¬ (NativeRustcVm.InRange (off fb 16) 32 (off fb j) ∨
      NativeRustcVm.InRange (stackBelow st1.data openPhaseStack) openPhaseStack (off fb j)) := by
    rintro j hj1 hj2 (h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h; omega
    · exact (hcal _ h).2 (inRange_off_self hj2 (by omega))
  have hf2 : Frame m0 96 slots 8 st2.data :=
    Frame.call_slots hf1 hsv2 hrsp2 hs2
      (fun p hp i hi ↦ hR _ (by have := slots_ge p hp; omega)
        (by have := slots_le p hp; omega))
      (fun j hj ↦ hR _ (by omega) (by omega))
  have hs2' : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (Stk m0) := by
    intro q hq
    rw [← hs1 q hq]
    exact hs2 q (by
      rintro (h | h)
      · exact hq (frame_stk hst (inRange_of_off (hfnw.mono (by omega)) (by omega) h))
      · exact hq (hcal q h).1)
  -- `b4`: the result's first word against `0`.
  have hwf4 := frame_wf (m0 := m0) (d := st2.data) (F := 96) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf2.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf4 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateQueryOpenings.b3_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hka3⟩ := ok_b4
  have hf3 : Frame m0 96 slots 8 st3.data := Frame.of_block hf2 hwf4 hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf4 hmem3
  have hs3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (Stk m0) := by
    rw [hd3]; exact hs2'
  have hk3 : ∀ r, calleeSaved r = true → r ≠ .rsp → reg st3.data r = reg st.data r := by
    intro r hr hr'
    refine (KeepAll.regs hka3 hm3 hr').trans ((hsv2.1 r hr).trans (hk1 r hr' ?_))
    cases r <;> first | rfl | exact absurd hr (by decide)
  simp only [PcOk] at hpc3
  have hl0 : ∀ {w : UInt64}, NativeRustcVm.WordAt st2.data.dmem (off fb 16) w →
      c4.eval (frameEnv m0 st2.data 96 [] (fun _ ↦ 0) 0) = (w.toBitVec == 0#64) := by
    intro w hw
    simp only [c4, SBool.eval, Sym.eval, CmpOp.apply, low_W64]
    rw [load_ofMachine (o := 16) rfl hw]
  cases hop3 : openPhase r.digest r.height r.width Q P with
  | none =>
    rw [hop3] at hout2
    rw [hl0 hout2] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    have hnone : (queryOpenings i Q).run s = none := by
      rw [run_some hi hlt, hop3]; rfl
    exact finish_fail hp hpre hnone (hpc3.trans (hp.label NativeRustcVmX64.Vm.TStateQueryOpenings.label_4_at)) hf3
      ((hk3 .r14 rfl (by decide)).trans h14)
      (NativeRustcVm.SameOutside.mono hs3 fun _ hq ↦ Or.inr (Or.inr hq))
  | some rows =>
    rw [hop3] at hout2
    have hcp := hout2
    obtain ⟨hp0, -, w, -, hhdr, -⟩ := hcp
    rw [hl0 (wordsAt_cons.mp hhdr).1] at hpc3
    have hp0' : (UInt64.ofBitVec (off ph 24)).toBitVec ≠ 0#64 := hp0
    simp only [beq_iff_eq, hp0', ↓reduceIte] at hpc3
    have hrun : (queryOpenings i Q).run s = some (rows, { s with phase := s.phase + 1 }) := by
      rw [run_some hi hlt, hop3]; rfl
    exact finish_ok hp hpre hrun hlt (openPhase_some hop3)
      (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateQueryOpenings.b4_next)) hf3
      ((hk3 .r14 rfl (by decide)).trans h14) ((hk3 .rbx rfl (by decide)).trans hbx)
      ((hk3 .r15 rfl (by decide)).trans h15) (tstate_stk hpre hf3.kept hs3)
      (by rw [hd3]; exact hout2)
      (NativeRustcVm.SameOutside.mono hs3 fun _ hq ↦ Or.inr (Or.inr hq))

end

end NativeRustcVmX64.Sumcheck.QueryOpenings
