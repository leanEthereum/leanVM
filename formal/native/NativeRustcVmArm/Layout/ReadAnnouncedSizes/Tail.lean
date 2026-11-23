module

public import NativeRustcVmArm.Code.Vm.BuildLayout.Names
public import NativeRustcVmArm.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmArm.Layout.ReadAnnouncedSizes.Model

/-!
# `read_announced_sizes` after the high limbs' checks

`from10`: `b10` copies the six row counts to frame bytes `128`-`176`, keeps the rate in X21 and
returns `0` (`b15`) unless `1 ≤ rate ≤ 4`; `b11` calls `build_layout` on the rows. `from12`: `b12`
returns `0` on its `None`, `b13` sets X0 to the stack's log-size check, `b14` returns it with the
rate in X1.
-/

namespace NativeRustcVmArm.Layout.ReadAnnouncedSizes

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReadAnnouncedSizes NativeVm.Model
open NativeRustcVm.Layout NativeRustcVm.Transcript LeanVM.Parameters
open NativeRustcVm (wordOf wordsOf WordAt WordsAt EWsAt wordOf_of_wordAt)
open NativeVm.Math.Layout (tailP lmA rowsA rateA rateA_eq ite_true_of ite_false_of)

public section

variable [Host] {k : Nat}

theorem lbl_13' (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.ReadAnnouncedSizes.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b15Offset) := lbl_13 hp

omit [Host] in
theorem rateA_get {xs : Array EW} (hsz : xs.size = 8) :
    rateA xs = (xs[7]'(by omega)).c0.toNat := by
  rw [rateA_eq hsz, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
    Option.getD_some]

/-- **After `build_layout`** (`b12`-`b14`). -/
theorem from12 (hp : Placed code k) {bc : Array UInt64} {a : DecArea} {s s1 : TState}
    {m0 : MachineData} (hpre : ReadAnnouncedSizesPre bc a s m0) {xs : Array EW}
    (hrs : (readScalars 8).run s = some (xs, s1)) (hsz : xs.size = 8)
    (hall : (xs.all fun x ↦ x.c1 == 0) = true) (hrate : 1 ≤ rateA xs ∧ rateA xs ≤ 4)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b12Offset)) (hb : Fr m0 st.data)
    (h19 : st.data.regs.X19 = m0.regs.X2) (h21 : st.data.regs.X21 = (xs[7]'(by omega)).c0)
    (h0 : st.data.regs.X0 = okWord (buildLayout bc (lmA xs) (rowsA xs)).isSome)
    (hL : ∀ L, buildLayout bc (lmA xs) (rowsA xs) = some L → LayoutWAt st.data.dmem (ll m0) L)
    (hts : TStateAt st.data.dmem (tt m0) a s1) :
    Eventually (step1 Host.exe) (Post bc a s m0) st := by
  obtain ⟨hst, -, -, -, -, -, -, hlr, -⟩ := id hpre
  have hF : 208 ≤ N := by have := le_rs; omega
  have hrun := run_tail bc hrs
  rw [tailP_of bc hall, ite_true_of hrate] at hrun
  obtain ⟨hwf, hm⟩ := fr_match hst hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, k12, m12⟩ := keeps_b1_b9
  obtain ⟨r12, r13, x13⟩ := b12_b13_regs
  obtain ⟨k13, m13⟩ := b13_keeps
  obtain ⟨x14, x14'⟩ := b14_regs
  obtain ⟨h14, h14m, -⟩ := restores_b14_b16
  rw [after_eq run_b12] at k12 m12 r12
  rw [after_eq run_b13] at r13 x13 k13 m13
  rw [after_eq run_b14] at x14 x14' h14 h14m
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hfr1, hd1⟩ := fr_step hst hb hm hm1 hwf k12 m12
  have he1 := Arrays.regs_eq_of hm hm1 _ r12
  have g19 : st1.data.regs.X19 = m0.regs.X2 := (he1 .X19 (by simp)).trans h19
  have g21 : st1.data.regs.X21 = (xs[7]'(by omega)).c0 := (he1 .X21 (by simp)).trans h21
  have h0v : (st.data.regs.getXReg .X0).toBitVec =
      (okWord (buildLayout bc (lmA xs) (rowsA xs)).isSome).toBitVec := by
    show st.data.regs.X0.toBitVec = _; rw [h0]
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [Env.ofMachine_regs, h0v] at hpc1
  cases hr : buildLayout bc (lmA xs) (rowsA xs) with
  | none =>
    simp (config := { decide := true }) only [hr, Option.isSome_none, okWord,
      Bool.false_eq_true, ↓reduceIte] at hpc1
    refine fail15 hp hst (hpc1.trans (lbl_13 hp)) hfr1 ?_
    rw [hrun, hr]; rfl
  | some L =>
  simp (config := { decide := true }) only [hr, Option.isSome_some, okWord, ↓reduceIte] at hpc1
  have hLw : LayoutWAt st1.data.dmem (ll m0) L := by rw [hd1]; exact hL L hr
  -- `b13`: the stack's log-size, at the layout's byte `16`.
  obtain ⟨hmap, hnw⟩ := readable_prefix (j := 24) hlr hfr1.kept (by decide)
  have hwf13 : (Env.ofMachine st1.data [(ll m0, 24)]).WF := Arrays.wf_one hmap hnw
  have hm13 : Match (Env.ofMachine st1.data [(ll m0, 24)]) layS st1.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by show st1.data.regs.X19.toBitVec = ll m0 + BitVec.ofInt 64 0
          rw [g19, ofInt_zero, BitVec.add_zero], trivial⟩
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 hwf13 hpc1 hm13
    fun st2 hm2 hpc2 ↦ ?_
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf13 m13
  have hfr2 : Fr m0 st2.data := Frame.of_block hfr1 hst hF hm13 hm2 hwf13 k13
    (fun p _ ↦ by rw [hd2]) (fun _ _ _ _ ↦ by rw [hd2])
  have he2 := Arrays.regs_eq_of hm13 hm2 _ r13
  have g21' : st2.data.regs.X21 = (xs[7]'(by omega)).c0 := (he2 .X21 (by simp)).trans g21
  have hld : (Env.ofMachine st1.data [(ll m0, 24)]).load 0 16 8 = L.stackLog.toUInt64.toBitVec :=
    load_word hLw.stack_log
  have hx0 := hm2.regs .X0 _ x13
  sym_simp at hx0
  rw [hld] at hx0
  have hcond := stack_cond hLw.stack_log_lt
  -- `b14`: X0, the rate in X1, the epilogue.
  refine exit_block (infix_of b14_in_code (by simp [b14]) hp) run_b14 h14 h14m hst hpc2 hfr2
    fun s' hpc' hsaved hd hm' ↦ ?_
  have hX0 : (s'.data.regs.getXReg .X0).toBitVec = (st2.data.regs.getXReg .X0).toBitVec :=
    hm'.regs .X0 _ x14
  have hX1 : s'.data.regs.X1 = (xs[7]'(by omega)).c0 :=
    (UInt64.toBitVec_inj.mp (hm'.regs .X1 _ x14')).trans g21'
  have hsame : SameOutside m0.dmem s'.data.dmem (fun q ↦ InRange (ll m0) layoutBytes q ∨
      InRange (tt m0) tstateBytes q ∨ InRange (stackBelow m0 N) N q) := by
    rw [hd]; exact Fr.sameOut hfr2
  have hdm : s'.data.dmem = st.data.dmem := by rw [hd, hd2, hd1]
  refine ⟨hpc', ?_, ?_, hsame, hsaved⟩
  · by_cases hc : 16 ≤ L.stackLog ∧ L.stackLog ≤ 30
    · have hrs' : (readAnnouncedSizes bc).run s = some ((L, rateA xs), s1) := by
        rw [hrun, hr, Option.bind_some, ite_true_of hc]; rfl
      rw [hrs']
      apply UInt64.toBitVec_inj.mp
      rw [show s'.data.regs.X0 = s'.data.regs.getXReg .X0 from rfl, hX0, hx0,
        hcond.mpr hc]
      rfl
    · have hrs' : (readAnnouncedSizes bc).run s = none := by
        rw [hrun, hr, Option.bind_some, ite_false_of hc]; rfl
      rw [hrs']
      apply UInt64.toBitVec_inj.mp
      rw [show s'.data.regs.X0 = s'.data.regs.getXReg .X0 from rfl, hX0, hx0,
        (Bool.not_eq_true _).mp fun h ↦ hc (hcond.mp h)]
      rfl
  · intro L' rate s' h
    rw [hrun, hr, Option.bind_some] at h
    by_cases hc : 16 ≤ L.stackLog ∧ L.stackLog ≤ 30
    · rw [ite_true_of hc] at h
      cases h
      refine ⟨by rw [hX1, rateA_get hsz], ?_, ?_⟩
      · rw [hd, hd2]; exact hLw
      · rw [hdm]; exact hts
    · rw [ite_false_of hc] at h
      cases h

/-- **After the checks** (`b10`, `b11`, the call of `build_layout`). -/
theorem from10 (hp : Placed code k)
    (hbl : ∀ bc, Spec (Labels.label NativeRustcVmArm.Vm.BuildLayout.entryLabel) (BuildLayoutPre bc) (BuildLayoutPost bc))
    {bc : Array UInt64} {a : DecArea} {s s1 : TState} {m0 : MachineData}
    (hpre : ReadAnnouncedSizesPre bc a s m0) {xs : Array EW}
    (hrs : (readScalars 8).run s = some (xs, s1)) {D : Mem 64} (hts : TStateAt D (tt m0) a s1)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b10Offset)) (hM : Mid m0 xs D st.data)
    (hc1 : ∀ i (hi : i < xs.size), xs[i].c1 = 0) :
    Eventually (step1 Host.exe) (Post bc a s m0) st := by
  obtain ⟨hst, -, hrod, hts0, htok, -, hX1, hlr, hlo, hlrod, -, hlt, hla⟩ := id hpre
  have hF : 208 ≤ N := by have := le_rs; omega
  have hsz := hM.size
  have hall := all_c1 hc1
  have hrun := run_tail bc hrs
  rw [tailP_of bc hall] at hrun
  obtain ⟨⟨-, hTn⟩, ⟨-, hAn⟩, -⟩ := hts0.footprint
  -- `b10`: the rows copied, the rate's check.
  obtain ⟨hwf, hm⟩ := fr_match hst hM.fr
  obtain ⟨k10, hw10, hv10⟩ := b10_facts
  obtain ⟨r1, r21, rk⟩ := b10_regs
  rw [after_eq run_b10] at k10 hw10 hv10 r1 r21 rk
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfw := frame_write (lo := 176) (slots := slots) hst hF hm1 hwf
    (fun w hw ↦ ⟨(hw10 w hw).1, (hw10 w hw).2.2⟩) (by decide) (by decide)
  have hfr1 : Fr m0 st1.data := Frame.of_block hM.fr hst hF hm hm1 hwf k10 hfw.1 hfw.2
  have he1 := Arrays.regs_eq_of hm hm1 _ rk
  have h19 : st1.data.regs.X19 = m0.regs.X2 := (he1 .X19 (by simp)).trans hM.regs.x19
  have h20 : st1.data.regs.X20 = m0.regs.X1 := (he1 .X20 (by simp)).trans hM.regs.x20
  have w0 : WordAt st.data.dmem (fbase m0 208 + BitVec.ofNat 64 0) (xs[0]'(by omega)).c0 :=
    (hM.word (i := 0) (by decide)).1
  have w7 : WordAt st.data.dmem (fbase m0 208 + BitVec.ofNat 64 112) (xs[7]'(by omega)).c0 :=
    (hM.word (i := 7) (by decide)).1
  have h1 : st1.data.regs.X1 = (xs[0]'(by omega)).c0 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X1 _ r1).trans (load_frame w0))
  have h21 : st1.data.regs.X21 = (xs[7]'(by omega)).c0 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X21 _ r21).trans (load_frame w7))
  have hrow : ∀ t (ht : t < 6), WordAt st1.data.dmem
      (fbase m0 208 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * t)) (xs[1 + t]'(by omega)).c0 := by
    intro t ht
    have hw := Match.wordAt_write hm1 (r := 0) (o := 128 + 8 * t) rfl (by omega) (hv10 t ht)
    have hv : (Sym.load 0 (16 * (t + 1)) 8).eval (Env.ofMachine st.data [(fbase m0 208, 208)]) =
        (xs[1 + t]'(by omega)).c0.toBitVec := by
      rw [show 16 * (t + 1) = 16 * (1 + t) by omega]
      exact load_frame (hM.word (i := 1 + t) (by omega)).1
    rw [hv] at hw
    rw [NativeRustcVm.addr_add]
    exact hw
  have hts0' : TStateAt st.data.dmem (tt m0) a s1 := by rw [hM.dm]; exact hts
  have hts1 : TStateAt st1.data.dmem (tt m0) a s1 :=
    hts0'.frame (R := InRange (fbase m0 208) 208) (hm1.kept hwf) (frame_tstate hpre)
      fun p hp ↦ hfw.1 p hp
  have hrA := rateA_get hsz
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [load_frame w7] at hpc1
  obtain ⟨hy, hn⟩ := Arrays.pc_cond hpc1
  by_cases hr : 1 ≤ rateA xs ∧ rateA xs ≤ 4
  swap
  · refine fail15 hp hst ((hy ((rate_cond _).mpr (by rw [hrA] at hr; exact hr))).trans
      (lbl_13 hp)) hfr1 ?_
    rw [hrun, ite_false_of hr]; rfl
  have hpc50 : st1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b11Offset) :=
    hn fun h ↦ (rate_cond _).mp h (by rw [hrA] at hr; exact hr)
  -- `b11`: `build_layout(bytecode_len, log_memory, rows, layout)`.
  obtain ⟨hwf1, hm1'⟩ := fr_match hst hfr1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, k11, m11, -⟩ := keeps_b1_b9
  obtain ⟨q0, q2, q3, qk⟩ := b11_regs
  rw [after_eq run_b11] at k11 m11 q0 q2 q3 qk
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf1 hpc50 hm1'
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hfr2, hd2⟩ := fr_step hst hfr1 hm1' hm2 hwf1 k11 m11
  have he2 := Arrays.regs_eq_of hm1' hm2 _ qk
  have g1 : st2.data.regs.X1 = (xs[0]'(by omega)).c0 := (he2 .X1 (by simp)).trans h1
  have g19 : st2.data.regs.X19 = m0.regs.X2 := (he2 .X19 (by simp)).trans h19
  have g21 : st2.data.regs.X21 = (xs[7]'(by omega)).c0 := (he2 .X21 (by simp)).trans h21
  have g0 : st2.data.regs.X0 = m0.regs.X1 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X0 _ q0)).trans h20
  have g2 : st2.data.regs.X2.toBitVec = fbase m0 208 + BitVec.ofNat 64 128 := by
    rw [show st2.data.regs.X2 = st2.data.regs.getXReg .X2 from rfl, hm2.regs .X2 _ q2]
    rfl
  have g3 : st2.data.regs.X3.toBitVec = ll m0 := by
    rw [show st2.data.regs.X3 = st2.data.regs.getXReg .X3 from rfl, hm2.regs .X3 _ q3]
    show st1.data.regs.X19.toBitVec = _
    rw [h19]
  have hcs : StackOk st2.data buildLayoutStack := stackOk_callee hst hfr2 (by decide) le_bl
  have hpbl : BuildLayoutPre bc st2.data := by
    show StackOk _ _ ∧ RodataAt _ _ ∧ st2.data.regs.X0.toNat = bc.size ∧
      Readable _ st2.data.regs.X2.toBitVec _ ∧ OffStack _ st2.data.regs.X2.toBitVec _ _ ∧
      Readable _ st2.data.regs.X3.toBitVec _ ∧ OffStack _ st2.data.regs.X3.toBitVec _ _ ∧
      RodataApart st2.data.regs.X3.toBitVec _ ∧
      Apart st2.data.regs.X2.toBitVec _ st2.data.regs.X3.toBitVec _
    rw [g2, g3, g0]
    exact ⟨hcs, rodataAt_callee hst hrod hfr2.same (rodata_out hpre) hfr2.sp le_bl, hX1,
      frame_readable hst hF hfr2 (o := 128) (k := 8 * nTables) (by decide),
      frame_apart_callee hst hfr2.sp le_bl (o := 128) (k := 8 * nTables) (by decide),
      ⟨Mapped.keeps hlr.1 hfr2.kept, hlr.2⟩, apart_callee hst hfr2.sp le_bl hlo, hlrod,
      apart_frame_sub hst hF hlo (o := 128) (k := 8 * nTables) (by decide)⟩
  refine call_then hpc2 (hbl bc) hpbl fun st3 hpc3 ⟨hok3, hL3, hch3, hsv3⟩ ↦ ?_
  have hnats : natsOf st2.data st2.data.regs.X2 nTables = rowsA xs :=
    natsOf_rows hsz fun t ht ↦ by rw [g2, hd2]; exact hrow t ht
  have hlm : st2.data.regs.X1.toNat = lmA xs := by
    rw [g1]
    show _ = (xs.getD 0 0).c0.toNat
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hnats, hlm] at hok3 hL3
  rw [g3] at hL3 hch3
  -- The body, the `TState` kept by `build_layout`.
  have hfn := (Arrays.frame_ok hst hF).2.1
  have hfl : Apart (fbase m0 208) 208 (ll m0) layoutBytes := apart_frame hst hF hlo
  have hfr3 : Fr m0 st3.data := by
    refine Frame.call hfr2 hch3 hsv3 (fun p hp ↦ hp.elim (fun h ↦ Or.inl (Or.inl h))
      fun h ↦ Or.inr (callee_stack hst hfr2.sp le_bl h)) fun q hq i hi ↦ ?_
    have hq8 : q.1 + i < 208 := by
      have := (show ∀ q ∈ slots, q.1 + 8 ≤ 208 by decide) q hq; omega
    rintro (h | h) <;> rw [NativeRustcVm.addr_add] at h
    · exact Arrays.not_inRange_of_apart hfl hfn hlr.2 hq8 h
    · exact callee_below hst hfr2.sp le_bl hq8 h
  have hts3 : TStateAt st3.data.dmem (tt m0) a s1 := by
    refine TStateAt.frame (by rw [hd2]; exact hts1) hsv3.2.2 (fun q hq ↦ ?_) hch3
    rcases hq with hq | hq
    · exact ⟨not_inRange_of_apart hlt hlr.2 hTn hq, not_inRange_of_apart hla hlr.2 hAn hq⟩
    · have hsn := stack_noWrap hcs
      exact ⟨not_inRange_of_apart
          (NativeRustcVmArm.Transcript.Apart.symm' (apart_callee hst hfr2.sp le_bl htok.1))
          hsn hTn hq,
        not_inRange_of_apart
          (NativeRustcVmArm.Transcript.Apart.symm' (apart_callee hst hfr2.sp le_bl htok.2.1))
          hsn hAn hq⟩
  exact from12 hp hpre hrs hsz hall hr hpc3 hfr3 ((hsv3.1 .X19 rfl).trans g19)
    ((hsv3.1 .X21 rfl).trans g21) hok3 hL3 hts3

end

end NativeRustcVmArm.Layout.ReadAnnouncedSizes
