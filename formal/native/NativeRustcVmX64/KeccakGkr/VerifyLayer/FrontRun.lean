module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Front
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `verify_layer` on x86-64: from the entry to the projection's loop

`front`: the prologue (`b0`), `read_scalars` of the product, the exit on `None` (`b1`), the
spills (`b2`), then `NativeRustcVmX64.Vm.VerifyLayer.label_4` with `PHead` (no term summed).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At testAl_eq)
open NativeRustcVm.Sumcheck (readScalars_size)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Parameters LeanVM.Protocol.Verifier

public section

/-- A word a block writes at the frame's `o`, its symbolic value found by `rfl` (`h0`). -/
theorem fwW [Labels] {env : Env} {S : SState} {d : MachineData} (hm : Match env S d) {o : Nat}
    {b : BitVec 64} {sz : Nat} (hb : env.regions[0]? = some (b, sz)) {v : Sym}
    (_h0 : findWrite 0 o S.mem = some (v, 0)) (hle : o + 8 ≤ sz)
    (hw : NativeRustcVmX64.Sumcheck.WordW 0 o v S) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    NativeRustcVm.WordAt d.dmem (off b o) w :=
  NativeRustcVmX64.Sumcheck.wordAt_written hm hb hle hw hv

theorem ult64 (x y : BitVec 64) : CmpOp.apply .ult .W64 x y = decide (x.toNat < y.toNat) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult]

theorem sub64 (x y : BitVec 64) : BinOp.apply .sub .W64 x y = x - y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem add64 (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem and30 : ∀ n < 17, BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 n))
    (BitVec.ofNat 64 30) = BitVec.ofNat 64 (n % 32 / 2 * 2) := by decide +kernel

theorem ite_len (x : BitVec 64) (h : x.toNat < 17) :
    (if (!CmpOp.apply .ult .W64 x (BitVec.ofNat 64 17)) = true then BitVec.ofNat 64 0 else x) =
      x := by
  rw [ult64]
  simp [h]

theorem ite_ptr (x y : BitVec 64) (h : x.toNat < 17) :
    (if CmpOp.apply .ult .W64 x (BitVec.ofNat 64 17) = true then y else BitVec.ofNat 64 8) = y := by
  rw [ult64]
  simp [h]

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- The front's outputs are outputs. -/
theorem wFront_outs [Labels] (hpre : VerifyLayerPre a s c m0) : ∀ q, wFront m0 q → outs m0 q := by
  have g := geo_of hpre
  intro q hq
  rcases hq with hq | hq
  · exact .inl hq
  · right; right
    have := g.hs; have hl := g.lN
    rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)] at hq
    rw [Sym.inRange_iff (by omega), hl]
    omega

/-- A range of the frame within a larger one. -/
theorem fr_sub (g : Geo m0) {o n lo len : Nat} (h1 : lo ≤ o) (h2 : o + n ≤ lo + len)
    (h3 : lo + len ≤ 2016) {q : BitVec 64} (h : InRange (off (stackBelow m0 2016) o) n q) :
    InRange (off (stackBelow m0 2016) lo) len q := by
  have := g.top; have := g.hN
  rw [Sym.inRange_iff (by rw [off, g.fa (by omega)]; omega), off, g.fa (by omega)] at h
  rw [Sym.inRange_iff (by rw [off, g.fa (by omega)]; omega), off, g.fa (by omega)]
  omega

/-- A range of the frame is in the frame. -/
theorem fr_in (g : Geo m0) {o n : Nat} (h2 : o + n ≤ 2024) {q : BitVec 64}
    (h : InRange (off (stackBelow m0 2016) o) n q) : InRange (stackBelow m0 2016) 2024 q := by
  have := g.top; have := g.hN; have := g.fbN
  by_cases hn : n = 0
  · subst hn; unfold InRange at h; omega
  rw [Sym.inRange_iff (by rw [off, g.fa (by omega)]; omega), off, g.fa (by omega)] at h
  rw [Sym.inRange_iff (by omega)]
  omega

theorem runL_none_rs (hr : (readScalars productBits).run s = none) : runL s c m0 = none := by
  unfold runL
  rw [run_rest, hr]
  rfl

/-- The claim's region is apart from the frame. -/
theorem claim_apart (g : Geo m0) :
    NativeRustcVm.Apart (stackBelow m0 2016) (2016 + 8) (cA m0) 768 := by
  have := g.fbN; have := g.hN; have := g.hcs; have := g.top
  unfold NativeRustcVm.Apart
  omega

/-- A body's environment with the claim beside the frame. -/
theorem wfC [Labels] (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop} {o : Nat}
    {d : MachineData} (hb : Body m0 W o d) {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (envB m0 d [(cA m0, 768)] vars ret).WF :=
  wf1 (pre_stack hpre) hb
    (NativeRustcVm.Transcript.Mapped.keeps (areas_ok (pre_areas hpre) (r := ⟨cA m0, 768⟩)
      (.inl (by simp))).1 hb.fr.kept)
    (areas_ok (pre_areas hpre) (r := ⟨cA m0, 768⟩) (.inl (by simp))).2 (claim_apart (geo_of hpre))

/-- A word of the claim, loaded. -/
theorem cload [Labels] {d : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat}
    {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (cA m0 + BitVec.ofNat 64 o) w) :
    (envB m0 d [(cA m0, 768)] vars ret).load 1 o 8 = w.toBitVec :=
  load_of_wordAt h

theorem packV_eq (x : BitVec 64) :
    (if (!CmpOp.apply .ult .W64 x (BitVec.ofNat 64 4)) = true then BinOp.apply .sub .W64 x
      (BitVec.ofNat 64 4) else BitVec.ofNat 64 0) = (x.toNat - 4).toUInt64.toBitVec := by
  rw [ult64, sub64]
  apply BitVec.eq_of_toNat_eq
  by_cases h : x.toNat < 4
  · simp [h]; omega
  · simp [h]
    omega

variable [Host] {k : Nat}

/-- **From the entry to the projection's loop.** -/
theorem front (hp : Placed code k)
    (hrs : Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hpre : VerifyLayerPre a s c m0)
    (hcont : ∀ p s1 d, (readScalars productBits).run s = some (p, s1) →
      PHead m0 a c p s1 0 d →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b7Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b0Offset)⟩ := by
  have g := geo_of hpre
  have hS := pre_stack hpre
  have hWo := wFront_outs hpre
  -- the prologue and the product's read
  have hwf : (envB m0 m0 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b0Offset + b0.length)).toBitVec).WF :=
    frame_wf (frame_ok hS fun _ h ↦ h) (fun _ h ↦ by cases h) (List.pairwise_singleton _ _)
  have hm : Match (envB m0 m0 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b0Offset + b0.length)).toBitVec)
      (fr 2016) m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp (F := 2016), trivial⟩ trivial trivial trivial
  refine exec_then (blk hp b0_in_code (by simp [b0])) e0 hwf (fun _ _ ↦ rfl) hm
    fun st hm1 hpc1 ↦ ?_
  have hb1 : Body m0 (wFront m0) 16 st.data :=
    ⟨Frame.of_prologue Frame.entry hwf hm1 (by decide +kernel) slots_le slots_cs,
      fun q hq ↦ by
        rw [hm1.get?_mem0 hwf fun hw ↦ hq (chg_written0 hpre (by decide +kernel)
          (by decide +kernel) hw)]
        rfl⟩
  have hrdi : reg st.data .rdi = tA m0 := hm1.regs .rdi _ rfl
  have hrsi : reg st.data .rsi = off (stackBelow m0 2000) 456 := by
    rw [off_fr]
    exact (hm1.regs .rsi _ rfl).trans (eval_ptr0 472)
  have hrdx : reg st.data .rdx = 47#64 := hm1.regs .rdx _ rfl
  have hrbx : reg st.data .rbx = 0#64 := hm1.regs .rbx _ rfl
  have hat : At m0 2000 st.data := hb1.at_ hpre hWo (by decide)
  have cx : Ctx m0 (tA m0) a 3232 2000 := ctx hpre (by decide)
  have hts : TStateAt st.data.dmem (tA m0) a s :=
    ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) (pre_ts hpre)
  refine call_then hpc1 hrs ?_ fun st2 hpc2 hrsp2 hq ↦ ?_
  · show StackOk st.data readScalarsStack ∧ RcAt st.data readScalarsStack ∧
      TStateAt st.data.dmem (reg st.data .rdi) a s ∧
      TStateOk st.data (reg st.data .rdi) a readScalarsStack ∧
      OutOk st.data (reg st.data .rdi) a (reg st.data .rsi) (16 * (reg st.data .rdx).toNat)
        readScalarsStack ∧
      GotAt st.data readScalarsStack
        [(reg st.data .rdi, tstateBytes), (a.words, 8 * a.len),
          (reg st.data .rsi, 16 * (reg st.data .rdx).toNat), (rcAddr, 192)] ["memcpy"]
    rw [hrdi, hrsi, hrdx]
    refine ⟨cx.stackOk hat (by decide), cx.rcAt hat (by decide), hts, cx.tstateOk hat (by decide),
      cx.outOk_frame hat (by decide) (o := 456) (n := 752) (by decide) (by decide), ?_⟩
    apply hb1.got hpre hWo (by decide) (by decide)
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, le_rfl, le_rfl⟩
    · exact ⟨_, by simp [NativeRustcVm.Transcript.DecArea.region], le_rfl, le_rfl⟩
    · refine ⟨(stackBelow m0 verifyLayerStack, verifyLayerStack + 8), by simp, ?_, ?_⟩
      all_goals
        have h47 : (47#64).toNat = 47 := rfl
        have hN := g.hN
        have ht := g.top
        rw [stack_eq, g.sbN, NativeRustcVm.Transcript.toNat_off
          (by rw [stackBelow_toNat (by omega)]; omega),
          stackBelow_toNat (by omega)]
        omega
    · exact ⟨_, by simp, le_rfl, le_rfl⟩
  obtain ⟨hok, hxs, hnext, hso, hsv⟩ := hq
  simp only [hrdi, hrsi, hrdx] at hok hxs hnext hso
  rw [show (47#64).toNat = productBits from rfl] at hok hxs hnext hso
  have hb2 : Body m0 (wFront m0) 24 st2.data :=
    Body.call g hWo hb1 (by decide) hsv hrsp2 (Sk := readScalarsStack) (by decide)
      (Wc := fun q ↦ InRange (off (stackBelow m0 2000) 456) (16 * productBits) q ∨
        InRange (tA m0) tstateBytes q)
      (NativeRustcVm.SameOutside.mono hso fun q hq ↦ by
        rcases hq with h | h | h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
        · exact .inl h)
      fun q hq ↦ by
        rcases hq with h | h
        · rw [off_fr] at h
          exact .inr (fr_sub g (by decide) (by decide) (by decide) h)
        · exact .inl (.inl h)
  have hrbx2 : reg st2.data .rbx = 0#64 := (hsv.1 .rbx rfl).trans hrbx
  -- `b1`: `None` exits
  have hwf2 := wf0 hS hb2 (vars := fun _ ↦ 0) (ret := 0)
  have hm2 : Match (envB m0 st2.data [] (fun _ ↦ 0) 0) (fr 24) st2.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hb2 hok hxs hnext hso hsv hrbx2 hm2 hwf2
  subst hpc2
  refine Body.blk (o' := 24) g hb2 hwf2 (blk hp b1_in_code (by simp [b1])) e1 nofun hm2
    (by decide +kernel) (hex0 (by decide +kernel)) fun st3 hm3 hpc3 hb3 hs3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (envB m0 d2 [] (fun _ ↦ 0) 0) = !((readScalars productBits).run s).isSome by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [testAl_eq]
    unfold OkAl at hok
    rw [show (d2.regs.get64 .rax).toNat % 256 = _ from hok]
    cases ((readScalars productBits).run s).isSome <;> rfl] at hpc3
  have hrbx3 : reg st3.data .rbx = 0#64 := (hm3.regs .rbx _ rfl).trans hrbx2
  cases hr : (readScalars productBits).run s with
  | none =>
    rw [hr] at hpc3
    simp only [Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3 hb3 hrbx3
    subst hpc3
    rw [lbl hp b87_in_code rfl]
    exact exit50 hp hpre hWo hb3 (by rw [hrbx3, runL_none_rs hr]; rfl)
      (fun c' s' h ↦ by rw [runL_none_rs hr] at h; cases h)
  | some ps =>
    obtain ⟨p, s1⟩ := ps
    rw [hr] at hpc3 hxs hnext
    simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    have hp3 := hxs p s1 rfl
    have hts3 : TStateAt st3.data.dmem (tA m0) a s1 :=
      ts_blk0 hpre hwf2 hm3 (by decide +kernel) (by decide +kernel) (hnext p s1 rfl)
    have hd3 : st3.data.dmem = d2.dmem := hm3.dmem_eq hwf2 rfl
    have hp3' : NativeRustcVm.EWsAt st3.data.dmem (off (stackBelow m0 2016) 472) p.toList := by
      rw [hd3, ← off_fr]
      exact hp3
    -- the callee-saved registers at `b2`
    have hcs : ∀ r, calleeSaved r = true → reg st3.data r = reg st.data r := fun r hr ↦
      (hm3.regs r (.reg r) (by cases r <;> first | rfl | exact absurd hr (by decide))).trans
        (hsv.1 r hr)
    have hrbp : reg st3.data .rbp = (packV m0).toBitVec := by
      rw [hcs .rbp rfl, show reg st.data .rbp = _ from hm1.regs .rbp _ rfl]
      simp only [Sym.eval, SBool.eval, Env.ofMachine_regs]
      exact packV_eq _
    have hr12 : reg st3.data .r12 = tA m0 := by rw [hcs .r12 rfl]; exact hm1.regs .r12 _ rfl
    have hr13 : reg st3.data .r13 = reg m0 .rdx := by rw [hcs .r13 rfl]; exact hm1.regs .r13 _ rfl
    have hr14 : reg st3.data .r14 = cA m0 := by rw [hcs .r14 rfl]; exact hm1.regs .r14 _ rfl
    have hr15 : reg st3.data .r15 = sA m0 := by rw [hcs .r15 rfl]; exact hm1.regs .r15 _ rfl
    clear hm1 hm hwf hm3
    -- `b2`
    have hb3' : Body m0 (wFront m0) 24 st3.data := hb3
    have hwf3 := wfC hpre hb3' (vars := fun _ ↦ 0) (ret := 0)
    have hm3' : Match (envB m0 st3.data [(cA m0, 768)] (fun _ ↦ 0) 0)
        (fr 24 [768] [] [] [(.reg .r14, 1, 0)]) st3.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb3'.rsp, trivial⟩ trivial trivial
        ⟨by show reg st3.data .r14 = cA m0 + BitVec.ofInt 64 0
            rw [hr14]; simp, trivial⟩
    obtain ⟨hlen, hlw, -⟩ := (hb3'.claim hpre fun _ h ↦ h).2.1
    have hlen' : c.mu.size < 17 := by
      have : c.mu.toList.length ≤ 16 := hlen
      simp at this; omega
    have hl16 : (envB m0 st3.data [(cA m0, 768)] (fun _ ↦ 0) 0).load 1 16 8 =
        BitVec.ofNat 64 c.mu.size := by
      rw [cload (o := 16) hlw]
      simp only [Array.length_toList, Nat.toUInt64]
      rfl
    have hl16n : (BitVec.ofNat 64 c.mu.size).toNat < 17 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlen'
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3 hb3 hb3' hts3 hp3' hd3 hcs hrbp hr12 hr13 hr14 hr15 hm3' hwf3 hl16
    subst hpc3
    rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b1Offset + b1.length = k + NativeRustcVmX64.Vm.VerifyLayer.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b1_next]]
    refine Body.blk (o' := 24) g hb3' hwf3 (blk hp b2_in_code (by simp [b2])) e2 nofun hm3'
      (by decide +kernel) (hex0 (by decide +kernel)) fun st4 hm4 hpc4 hb4 hs4 ↦ ?_
    simp only [PcOk] at hpc4
    rw [lbl hp b7_in_code rfl] at hpc4
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc4 hm4 hb4 hs4
    subst hpc4
    refine hcont p s1 d4 hr ⟨⟨hb4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact ts_blk0 hpre hwf3 hm4 (by decide +kernel) (by decide +kernel) hts3
    · exact (frSame_blk (o := 472) (n := 752) hwf3 hm4 (by decide +kernel) (by decide)
        (by decide +kernel)).ews hp3'
        (by rw [Array.length_toList, (readScalars_size hr : p.size = productBits)]; decide)
    · have e3 : ∀ r, (envB m0 d3 [(cA m0, 768)] (fun _ ↦ 0) 0).regs r = reg d3 r := fun _ ↦ rfl
      intro q hq
      simp only [spills, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
        refine fwW hm4 rfl rfl (by decide) (by decide +kernel) ?_ <;>
        simp only [Sym.eval, SBool.eval, hl16, ite_len _ hl16n, ite_ptr _ _ hl16n, add64, e3, hrbp,
          hr12, hr13, hr14, hr15]
      · rfl
      · rw [ult64, ite_eq_left_of_eq_true _ _ (by simpa using hl16n), BitVec.add_assoc]; rfl
    · exact (hm4.regs .rax _ rfl)
    · exact (hm4.regs .r14 _ rfl)
    · rw [show reg d4 .rbx = _ from hm4.regs .rbx _ rfl]
      simp only [Sym.eval, SBool.eval, hl16, ite_len _ hl16n]
      exact and30 _ hlen'
    · exact (hm4.regs .r15 _ rfl)
    · rw [show reg d4 .r12 = _ from hm4.regs .r12 _ rfl, show reg d4 .r13 = _ from hm4.regs .r13 _ rfl]
      rfl
    · decide
    · exact readScalars_size hr
    · rw [show reg d4 .rsi = _ from hm4.regs .rsi _ rfl]
      simp only [Sym.eval, SBool.eval, hl16, ite_len _ hl16n]

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
