module

public import NativeRustcVmX64.Top.Verify.Check
public import NativeRustcVmX64.Code.Vm.DecodedPhaseCount.Names

/-!
# `verify`'s verdict (x86-64)

`stageC`: from `SB`, `b2` returns `0` when the walk failed (`exit0`); else `b3`, `b4` compare the
cursor with the stream's count (the area's first word, read through the `Decoded`'s pointer; the
area is never empty, so `b7` is not reached) and return `0` when they differ; else `b5` calls
`Decoded::phase_count` and `b6` sets AL to whether the phase equals it, `b9` returns. AL is
`Model.verify`'s verdict.
-/

namespace NativeRustcVmX64.Top.Verify

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Verify NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Top NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)

public section

variable [Host] {k : Nat}

/-- **After the walk**: AL the verdict. -/
theorem stageC (hp : Placed code k)
    (hpcnt : ∀ a stream openings, Spec (Labels.label NativeRustcVmX64.Vm.DecodedPhaseCount.entryLabel)
      (PhaseCountPre a stream openings) (PhaseCountPost openings))
    {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)} {m0 : MachineData}
    (hpre : VerifyPre a stream openings m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b2Offset)) (hSB : SB a stream openings m0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧
      OkAl st'.data (NativeVm.Model.verify (bcOf m0).toArray (pubOf m0) stream openings) ∧
      NativeRustcVm.SameOutside m0.dmem st'.data.dmem
        (fun q ↦ NativeRustcVm.InRange (stackBelow m0 18704) 18704 q ∨
          NativeRustcVm.InRange (reg m0 .r8) workAreaBytes q) ∧
      Saved m0 st'.data) st := by
  have g := geo_of hpre
  obtain ⟨hst, -, -, hdecF, -, -, -, ⟨hdecM, -⟩, ⟨haM, -⟩, -, -, -, -⟩ := hpre
  obtain ⟨hf, hsame, hrbx, hok, hnext⟩ := hSB
  have hR := g.R
  have h8 := g.e8
  have hfnw := frame_noWrap (F := 816) hst (by decide)
  have hBn := g.F
  have hdecN := g.decN
  have haN := g.areaN
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (fb m0) (816 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by decide)) hk
  have hstk' : ∀ q, NativeRustcVm.InRange (stackBelow m0 18704) 18704 q →
      sb m0 ≤ q.toNat ∧ q.toNat < sb m0 + 18704 := by
    intro q h
    rw [inR (by unfold NativeRustcVm.NoWrap; rw [sb_eq]; omega), sb_eq] at h
    exact h
  have hdec : DecFieldsAt st.data.dmem (reg m0 .rcx) a :=
    DecFieldsAt.keep hdecF hdecN hsame fun q hq h ↦ by
      rw [inR hdecN] at h
      rcases hq with hq | hq
      · have := hstk' q hq
        have := g.dec
        omega
      · rw [inR (by unfold NativeRustcVm.NoWrap; exact g.workN)] at hq
        have := g.decWork
        omega
  obtain ⟨hd0, hd1, -⟩ := hdec
  rw [verify_eq]
  -- `b2`: the walk's verdict tested.
  have hwf2 := frame_wf (m0 := m0) (d := st.data) (F := 816) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨hFm _ hf.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf2 nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hmem2, hrbx2⟩ := after_eq run_b2 ▸ ok_b2
  have hf2 : Frame m0 816 slots 8 st2.data := Frame.of_block hf hwf2 hm2 hmid2 slots_le
  have hd2 : st2.data.dmem = st.data.dmem := hm2.dmem_eq hwf2 hmem2
  have eRbx2 : reg st2.data .rbx = reg m0 .rcx := (hm2.regs .rbx _ hrbx2).trans hrbx
  have hc2 : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (frameEnv m0 st.data 816 [] (fun _ ↦ 0) 0) = !(run m0 stream openings).isSome := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    exact testAl_okAl hok
  simp only [PcOk, hc2] at hpc2
  revert hok hnext hc2 hpc2
  rcases hr : run m0 stream openings with _ | ⟨⟨⟩, s⟩ <;> intro hok hnext hc2 hpc2
  · -- the walk failed: `0`
    simp only [Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc2
    refine Eventually.mono (exit0 hp hst (hpc2.trans (lbl_5 hp)) hf2)
      fun s ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, ?_, h5⟩
    rw [h4, hd2]
    exact hsame
  · simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    have ht : TStateAt st.data.dmem (tOf m0) a s := hnext () s rfl
    -- `b3`: the cursor, the area's length.
    have hwf3 := frame_wf (m0 := m0) (d := st2.data) (F := 816) (rest := [(reg m0 .rcx, 24)])
      (vars := fun _ ↦ 0) (ret := 0) ⟨hFm _ hf2.kept, hfnw⟩
      (fun x hx ↦ by
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨Mapped.keeps hdecM hf2.kept, hdecN⟩)
      (List.pairwise_pair.mpr (by
        unfold NativeRustcVm.Apart; dsimp only; rw [hBn]; have := g.dec; omega))
    have hm3 : Match (frameEnv m0 st2.data 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) 0) initS
        st2.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, known_ptr rfl eRbx2, trivial⟩ trivial
        trivial trivial
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3 nofun
      (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.Verify.b2Offset + b2.length = k + NativeRustcVmX64.Vm.Verify.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Verify.b2_next]])) hm3
      fun st3 hm3' hpc3 ↦ ?_
    obtain ⟨hmid3, hmem3, hrax3, hrbx3⟩ := after_eq run_b3 ▸ ok_b3
    have hf3 : Frame m0 816 slots 8 st3.data := Frame.of_block hf2 hwf3 hm3' hmid3 slots_le
    have hd3 : st3.data.dmem = st.data.dmem := (hm3'.dmem_eq hwf3 hmem3).trans hd2
    have eRbx3 : reg st3.data .rbx = reg m0 .rcx := (hm3'.regs .rbx _ hrbx3).trans (eval_ptr rfl)
    have hcur : reg st3.data .rax = s.cursor.toUInt64.toBitVec := by
      rw [show reg st3.data .rax = _ from hm3'.regs .rax _ hrax3]
      refine load_ofMachine (r := 0) (b := fb m0) (n := 824) rfl ?_
      have := ht.cursor
      rw [hd2.symm, off_off] at this
      exact this
    have hlen : a.len < 2 ^ 64 := by have := g.len; omega
    have hc3 : (SBool.cmp .eq .W64 (.load 1 8 8) (.lit 0)).eval
        (frameEnv m0 st2.data 816 [(reg m0 .rcx, 24)] (fun _ ↦ 0) 0) = false := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
      rw [load_ofMachine (r := 1) (b := reg m0 .rcx) (n := 24) rfl (by rw [hd2]; exact hd1)]
      rw [Bool.eq_false_iff]
      intro h
      rw [beq_iff_eq, ← BitVec.toNat_inj] at h
      simp only [UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlen,
        BitVec.toNat_ofNat] at h
      have := g.len
      omega
    simp only [PcOk, hc3, Bool.false_eq_true, ↓reduceIte] at hpc3
    -- `b4`: the stream's count.
    have haW : a.words.toNat + 8 ≤ a.words.toNat + 8 * a.len := by have := g.len; omega
    have hwf4 := frame_wf (m0 := m0) (d := st3.data) (F := 816)
      (rest := [(reg m0 .rcx, 24), (a.words, 8)]) (vars := fun _ ↦ 0) (ret := 0)
      ⟨hFm _ hf3.kept, hfnw⟩
      (fun x hx ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨Mapped.keeps hdecM hf3.kept, hdecN⟩
        · exact ⟨Mapped.keeps (fun i hi ↦ haM i (by
              show i < 8 * a.len
              have : i < 8 := hi
              omega)) hf3.kept, by
            show a.words.toNat + 8 ≤ 2 ^ 64
            omega⟩)
      (pairwise3 (by unfold NativeRustcVm.Apart; dsimp only; rw [hBn]; have := g.dec; omega)
        (by
          show (fb m0).toNat + (816 + 8) ≤ a.words.toNat ∨ a.words.toNat + 8 ≤ (fb m0).toNat
          rw [hBn]; have := g.area; omega)
        (by
          show (reg m0 .rcx).toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 ≤ (reg m0 .rcx).toNat
          have := g.decArea; omega))
    have hm4 : Match (frameEnv m0 st3.data 816 [(reg m0 .rcx, 24), (a.words, 8)] (fun _ ↦ 0) 0)
        areaS st3.data := by
      refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf3.rsp_eval, known_ptr rfl eRbx3, trivial⟩
        trivial trivial ⟨?_, trivial⟩
      show (frameEnv m0 st3.data 816 [(reg m0 .rcx, 24), (a.words, 8)] (fun _ ↦ 0) 0).load 1 0 8 =
        a.words + BitVec.ofInt 64 0
      rw [load_ofMachine (r := 1) (b := reg m0 .rcx) (n := 24) rfl
        (w := UInt64.ofBitVec a.words) (by rw [hd3, off_zero]; exact hd0)]
      rw [ofInt_zero64, BitVec.add_zero]
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf4 nofun
      (hpc3.trans (by rw [show k + NativeRustcVmX64.Vm.Verify.b3Offset + b3.length = k + NativeRustcVmX64.Vm.Verify.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Verify.b3_next]])) hm4
      fun st4 hm4' hpc4 ↦ ?_
    obtain ⟨hmid4, hmem4, hrbx4⟩ := after_eq run_b4 ▸ ok_b4
    have hf4 : Frame m0 816 slots 8 st4.data := Frame.of_block hf3 hwf4 hm4' hmid4 slots_le
    have hd4 : st4.data.dmem = st.data.dmem := (hm4'.dmem_eq hwf4 hmem4).trans hd3
    have eRbx4 : reg st4.data .rbx = reg m0 .rcx := (hm4'.regs .rbx _ hrbx4).trans (eval_ptr rfl)
    have hDs := ht.decoded
    have hsl : s.stream.size < 2 ^ 64 := by
      have h1 := hDs.stream_le
      have h2 := hDs.l_lt
      unfold NativeVm.maxStream at h1
      omega
    have hcl : s.cursor < 2 ^ 64 := by have := ht.cursor_le; omega
    have hc4 : (SBool.cmp .eq .W64 (.reg .rax) (.load 2 0 8)).not.eval
        (frameEnv m0 st3.data 816 [(reg m0 .rcx, 24), (a.words, 8)] (fun _ ↦ 0) 0) =
        !(s.cursor == s.stream.size) := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
      rw [load_ofMachine (r := 2) (b := a.words) (n := 8) rfl
        (by rw [hd3, off_zero]; have := hDs.stream_count; rwa [DecArea.word, off_zero] at this)]
      rw [show st3.data.regs.get64 .rax = _ from hcur, toBV_beq hcl hsl]
    simp only [PcOk, hc4] at hpc4
    cases hcs : s.cursor == s.stream.size
    · -- the cursor short of the stream's end: `0`
      simp only [hcs, Bool.not_false, ↓reduceIte] at hpc4
      refine Eventually.mono (exit0 hp hst (hpc4.trans (lbl_5 hp)) hf4)
        fun s' ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, by show OkAl _ (s.cursor == s.stream.size && _); rw [hcs, Bool.false_and]; exact h3, ?_, h5⟩
      rw [h4, hd4]
      exact hsame
    simp only [hcs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    -- `b5`: the phase, `call phase_count`.
    have hwf5 := frame_wf (m0 := m0) (d := st4.data) (F := 816) (rest := []) (vars := fun _ ↦ 0)
      (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b5Offset + b5.length)).toBitVec) ⟨hFm _ hf4.kept, hfnw⟩ (by simp)
      (List.pairwise_singleton _ _)
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf5 (fun _ _ ↦ rfl)
      (hpc4.trans (by rw [show k + NativeRustcVmX64.Vm.Verify.b4Offset + b4.length = k + NativeRustcVmX64.Vm.Verify.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Verify.b4_next]]))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf4.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st5 hm5 hpc5 ↦ ?_
    obtain ⟨hmid5, hw5, hrdi5, hr145⟩ := after_eq run_b5 ▸ ok_b5
    have hf5 : Frame m0 816 slots 0 st5.data := Frame.of_block hf4 hwf5 hm5 hmid5 slots_le
    have hsp5 : rspOf st5.data = fb m0 := by rw [hf5.sp, off_zero]
    have hs5 : NativeRustcVm.SameOutside st4.data.dmem st5.data.dmem
        (NativeRustcVm.InRange (fb m0) 8) :=
      sameOutside_low hwf5 hm5 (r := 0) rfl (by decide) hw5
    have hs5' : ∀ q, NativeRustcVm.InRange (fb m0) 8 q →
        sb m0 + 17888 ≤ q.toNat ∧ q.toNat < sb m0 + 17896 := fun q h ↦ by
      rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn] at h
      omega
    have eRdi5 : reg st5.data .rdi = reg m0 .rcx := (hm5.regs .rdi _ hrdi5).trans eRbx4
    have hph : reg st5.data .r14 = s.phase.toUInt64.toBitVec := by
      rw [show reg st5.data .r14 = _ from hm5.regs .r14 _ hr145]
      refine load_ofMachine (r := 0) (b := fb m0) (n := 824) rfl ?_
      have := ht.phase
      rw [hd4.symm, off_off] at this
      exact this
    have hnotA : ∀ q, NativeRustcVm.InRange (fb m0) 8 q →
        ¬ NativeRustcVm.InRange a.words (8 * a.len) q := fun q h h' ↦ by
      have := hs5' q h
      rw [inR haN] at h'
      have := g.area
      omega
    have hnotD : ∀ q, NativeRustcVm.InRange (fb m0) 8 q →
        ¬ NativeRustcVm.InRange (reg m0 .rcx) 24 q := fun q h h' ↦ by
      have := hs5' q h
      rw [inR hdecN] at h'
      have := g.dec
      omega
    have hpre5 : PhaseCountPre a s.stream s.openings st5.data := by
      unfold PhaseCountPre
      simp only [eRdi5]
      refine ⟨stackOk_callee hst hf5.kept hsp5 (by show 816 + 0 ≤ verifyStack; decide), ?_, Mapped.keeps hdecM hf5.kept,
        hdecN, g.decArea, ⟨Mapped.keeps haM hf5.kept, haN⟩, ?_⟩
      · refine DecFieldsAt.keep ⟨hd0, hd1, ?_⟩ hdecN (hd4 ▸ hs5) hnotD
        exact (DecFieldsAt.keep hdecF hdecN hsame fun q hq h ↦ by
          rw [inR hdecN] at h
          rcases hq with hq | hq
          · have := hstk' q hq
            have := g.dec
            omega
          · rw [inR (by unfold NativeRustcVm.NoWrap; exact g.workN)] at hq
            have := g.decWork
            omega).2.2
      · exact DecodedAt.keep hDs haN (hd4 ▸ hs5) hnotA
    refine call_then hpc5 (hpcnt a s.stream s.openings) hpre5 fun st6 hpc6 hrsp6 hpost6 ↦ ?_
    obtain ⟨hcnt6, hs6, hsv6⟩ := hpost6
    have hf6 : Frame m0 816 slots 8 st6.data :=
      Frame.call hf5 hsv6 hrsp6 hs6 (fun _ h ↦ h.elim) hfnw slots_le
    have hd6 : st6.data.dmem = st5.data.dmem :=
      Std.ExtHashMap.ext_getElem? fun q ↦ by
        rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
        exact hs6 q id
    -- `b6`: AL whether the phase is the count; `b9`.
    have hwf6 := frame_wf (m0 := m0) (d := st6.data) (F := 816) (rest := []) (vars := fun _ ↦ 0)
      (ret := 0) ⟨hFm _ hf6.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _)
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf6 nofun
      (hpc6.trans (by rw [show k + NativeRustcVmX64.Vm.Verify.b5Offset + b5.length = k + NativeRustcVmX64.Vm.Verify.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Verify.b5_next]]))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf6.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st7 hm7 hpc7 ↦ ?_
    obtain ⟨hmid7, hmem7, hrax7⟩ := after_eq run_b6 ▸ ok_b6
    have hf7 : Frame m0 816 slots 8 st7.data := Frame.of_block hf6 hwf6 hm7 hmid7 slots_le
    have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf6 hmem7
    have hpl : s.openings.size < 2 ^ 64 := by
      have := hDs.phases_le
      unfold LeanVM.Protocol.Compile.wireMaxPhases at this
      omega
    have hpp : s.phase < 2 ^ 64 := by have := ht.phase_le; omega
    have hok7 : OkAl st7.data (s.phase == s.openings.size) := by
      unfold OkAl boolRet
      rw [show reg st7.data .rax = _ from hm7.regs .rax _ hrax7]
      simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
      rw [show st6.data.regs.get64 .r14 = _ from (hsv6.1 .r14 rfl).trans hph,
        show st6.data.regs.get64 .rax = _ from hcnt6, toBV_beq hpp hpl]
      exact sete_okAl _ _
    simp only [PcOk] at hpc7
    refine Eventually.mono (exit9 hp hst (hpc7.trans (lbl_6 hp)) hf7 hok7)
      fun s' ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, by show OkAl _ (s.cursor == s.stream.size && _); rw [hcs, Bool.true_and]; exact h3, fun q hq ↦ ?_, h5⟩
    rw [h4, hd7, hd6, hs5 q fun h ↦ hq (Or.inl ?_), hd4]
    · exact hsame q hq
    · have := hs5' q h
      rw [inR (by unfold NativeRustcVm.NoWrap; rw [sb_eq]; omega), sb_eq]
      omega

end

end NativeRustcVmX64.Top.Verify
