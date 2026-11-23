module

public import NativeRustcVmX64.Whir.FoldRounds.Exit
public import NativeRustcVmX64.Code.Vm.FoldRound.Names
public import NativeRustcVmX64.Code.Vm.FoldRounds.Names

/-!
# A round of `fold_rounds` (x86-64)

`round`: from `fold_round`'s call after `i` rounds, its tag tested (`T`): `None` rejects
(`fail20`); `Some` stores its `α`, `β` in the buffer (`S`, `StoreOk`), then the rounds done are
compared with `n`: equal, the return (`done`); else `Inv (i + 1)` at the store's end. `step`: a
round after the first, from its call block (`C`, `CallOk`).
-/

namespace NativeRustcVmX64.Whir.FoldRounds

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRounds
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 wrote kept wrote_spec kept_spec wr0_spec)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

/-- **One round**: from `fold_round`'s call, its tag tested (`T`), its `α`, `β` stored (`S`). -/
theorem round (hp : Placed code k)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmX64.Vm.FoldRound.entryLabel) (FoldRoundPre a s w) (FoldRoundPost a s w))
    (h : FoldRoundsPre a s w m0) (i : Nat)
    {T S : List Directive} {kt : Nat} {ST SS S0 : SState} {cT : SBool}
    (hT : T.IsInfixAt code kt) (hTne : T ≠ [])
    (hrunT : exec T midS = some (ST, .cond cT NativeRustcVmX64.Vm.FoldRounds.label_2)) (hokT : TagOk (after T midS))
    (hc0 : ∀ d : MachineData, WordAt d.dmem (off (fb m0) 40) 0 →
      cT.eval (frameEnv m0 d 160 []) = true)
    (hc1 : ∀ d : MachineData, WordAt d.dmem (off (fb m0) 40) 1 →
      cT.eval (frameEnv m0 d 160 []) = false)
    (hS : S.IsInfixAt code (kt + T.length)) (hSne : S ≠ [])
    (hS0 : S0 = store0S ∨ (S0 = storeS ∧ 0 < i))
    (hrunS : exec S S0 =
      some (SS, .cond (.cmp .eq .W64 (.reg .r13) (.lit (i + 1))) NativeRustcVmX64.Vm.FoldRounds.label_3))
    (hokS : StoreOk i (after S S0)) (hi : i < (reg m0 .rsi).toNat) {st : MachineState}
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.FoldRound.entryLabel ∧ retOf st.data = Host.addrOf (k + kt))
    (hI : Inv a s w m0 i 0 st.data) (hdi : reg st.data .rdi = off (fb m0) 40)
    (hsi : reg st.data .rsi = tA m0) (hdx : reg st.data .rdx = pA m0)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + (kt + T.length) + S.length) →
      (reg m0 .rsi).toNat ≠ i + 1 → Inv a s w m0 (i + 1) 8 st'.data →
      Eventually (step1 Host.exe) (Goal a s w m0) st') :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  rw [after_eq hrunT] at hokT
  rw [after_eq hrunS] at hokS
  have c := ctx h
  have hn6 := pre_n6 h
  have hfnw : (stackBelow m0 160).toNat + (160 + 8) ≤ 2 ^ 64 := c.fnw
  have hrn : (rA m0).toNat + 200 ≤ 2 ^ 64 := (pre_r h).2.1
  obtain ⟨w1, rs, s1, hrun, hrs, hal1, hws1, hbr1, hts1⟩ := hI.run
  have hsp : rspOf st.data = stackBelow m0 160 := by rw [hI.fr.sp, off_zero]
  /- `fold_round`. -/
  refine call0 c hI.fr hI.same slots_le call_le (hfr a s1 w1) (Lf := InRange (off (fb m0) 40) 40)
    (fun m' hq ↦ ⟨hq.2.2, SameOutside.mono hq.2.1 fun q hq ↦ ?_⟩)
    (fun q hq ↦ Transcript.inRange_of_off (N := 160) (by unfold NativeRustcVm.NoWrap; omega)
      (by omega) hq)
    (fun p hp' j hj ↦ off_not_in (N := 160 + 8) hfnw (by have := slots_le p hp'; omega) (by omega)
      (by have := slots_112 p hp'; omega))
    hpc (callPre h hI.fr hI.same hi hal1 hts1 hws1 hdi hsi hdx) fun st2 hpc2 hw2 hq _ ↦ ?_
  · rw [three_iff, hdi, hdx, hsi] at hq
    rcases hq with (hq | hq | hq) | hq
    · exact .inr (.inl hq)
    · exact .inr (.inr (.inr (.inl hq)))
    · exact .inr (.inr (.inr (.inr hq)))
    · exact .inl hq
  obtain ⟨hres, hch, hsv⟩ := hq
  have hbr2 : BufRoundsAt st2.data.dmem (rA m0) rs.toList :=
    bufRoundsAt_agree hbr1 fun j hj _ ↦
      hch _ (r_not_call h hsp hdi hsi hdx (inRange_off_self hj (by omega)))
  /- `T`: the tag. -/
  have hwf2 := c.wf0 (d := st2.data) (vars := fun _ ↦ 0) (ret := 0) hw2.fr.kept
  refine exec_at (inf hp hT hTne) hrunT hwf2 (by intro l h; cases h) hpc2 (mid hw2.fr)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hk3⟩ := hokT
  have hw3 : WFr m0 160 foldRoundsStack slots (outs m0) st3.data :=
    WFr.block c hw2 hwf2 hm3 hmid3 slots_le fun q ⟨_, hw, _⟩ ↦ by rw [hmem3] at hw; cases hw
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hr3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st.data r := fun r hr ↦
    (hm3.regs r _ (kept_spec hk3 (cs_of hr))).trans (hsv.1 r hr)
  simp only [PcOk] at hpc3
  cases hfr2 : (foldRound w1).run s1 with
  | none =>
    have h0 : WordAt st2.data.dmem (off (fb m0) 40) 0 := by
      rw [hfr2] at hres
      rw [← hdi]
      exact hres
    rw [hc0 st2.data h0] at hpc3
    simp only [↓reduceIte] at hpc3
    exact fail20 hp h (hpc3.trans (hp.label NativeRustcVmX64.Vm.FoldRounds.label_2_at)) hw3.fr hw3.same
      (foldRounds_none_of hrun hfr2 _ hi)
  | some q2 =>
  obtain ⟨⟨w2, ρ⟩, s2⟩ := q2
  rw [hfr2] at hres
  obtain ⟨ht1, hab, hws2, hts2⟩ := hres
  rw [hdi] at ht1 hab
  rw [hdx] at hws2
  rw [hsi] at hts2
  rw [hc1 st2.data ht1] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
  /- `S`: `α`, `β` stored. -/
  have hi6 : i < 6 := by omega
  have hap : NativeRustcVm.Apart (stackBelow m0 160) (160 + 8) (rA m0) 200 :=
    Transcript.Apart.symm' (Transcript.apart_frame (pre_r h).2.2.2.2.1 c.hN F_le)
  have hwf3 : (frameEnv m0 st3.data 160 [(rA m0, 200)]).WF := by
    refine Transcript.frame_wf ⟨Mapped.keeps (Transcript.frame_mapped c.stack F_le) hw3.fr.kept,
      c.fnw⟩ (fun x hx ↦ ?_) (List.pairwise_pair.mpr hap)
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps (pre_r h).1 hw3.fr.kept, (pre_r h).2.1⟩
  have h12 : reg st3.data .r12 = rA m0 := (hr3 .r12 rfl).trans hI.r12
  have hbp : 0 < i → reg st3.data .rbp = off (fb m0) 48 := fun hi0 ↦
    (hr3 .rbp rfl).trans (hI.rbp hi0)
  refine exec_at (inf hp hS hSne) hrunS hwf3 (by intro l h; cases h)
    (hpc3.trans (by rw [Nat.add_assoc])) (store_match hS0 hw3.fr h12 hbp) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hcn, hv0, hv1, hv2, hv3, hsw, h12', hbp', hk4⟩ := hokS
  have hw4 : WFr m0 160 foldRoundsStack slots (outs m0) st4.data :=
    WFr.block c hw3 hwf3 hm4 hmid4 slots_le fun q hW ↦ storeR_sm h (store_written hi6 hwf3 hsw hW)
  have hs4 : SameOutside st3.data.dmem st4.data.dmem (storeR m0 i) := fun q hq ↦
    hm4.get?_mem0 hwf3 fun hW ↦ hq (store_written hi6 hwf3 hsw hW)
  have hs4' : SameOutside st2.data.dmem st4.data.dmem (storeR m0 i) := by rw [← hd3]; exact hs4
  -- The output's `α`, `β`, loaded.
  have hab' : EWsAt st3.data.dmem (off (fb m0) 48) [ρ.alpha, ρ.beta] := by
    rw [hd3, show off (fb m0) 48 = off (off (fb m0) 40) 8 from (off_off _ 40 8).symm]
    exact hab
  rw [ewsAt_cons, ewsAt_cons, ewAt_iff, ewAt_iff] at hab'
  obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩, -⟩ := hab'
  rw [off_off] at ha1 hb0
  rw [off_off, off_off] at hb1
  have el : ∀ {o : Nat} {v : UInt64}, WordAt st3.data.dmem (off (fb m0) o) v →
      (Sym.load 0 o 8).eval (frameEnv m0 st3.data 160 [(rA m0, 200)]) = v.toBitVec :=
    fun hw ↦ Transcript.load_ofMachine rfl hw
  have wr4 : ∀ {o : Nat} {v : Sym} {u : UInt64}, o + 8 ≤ 200 → wrote SS 1 o v = true →
      v.eval (frameEnv m0 st3.data 160 [(rA m0, 200)]) = u.toBitVec →
      WordAt st4.data.dmem (off (rA m0) o) u := fun hle hw hv ↦ by
    have := Transcript.wordAt_write hm4 (r := 1) rfl hle (wrote_spec hw)
    rwa [hv, UInt64.ofBitVec_toBitVec] at this
  have hw0 := wr4 (by omega) hv0 (el ha0)
  have hw1 := wr4 (by omega) hv1 (el (o := 56) ha1)
  have hw2' := wr4 (by omega) hv2 (el (o := 64) hb0)
  have hw3' := wr4 (by omega) hv3 (el (o := 72) hb1)
  have hcnt := wr4 (o := 0) (u := (i + 1).toUInt64) (by omega) hcn rfl
  rw [off_zero] at hcnt
  have hab4 : EWsAt st4.data.dmem (off (rA m0) (8 + 32 * i)) [ρ.alpha, ρ.beta] := by
    refine ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨hw0, ?_⟩, ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩,
      ewsAt_nil _ _⟩⟩
    · rw [off_off, show 8 + 32 * i + 8 = 16 + 32 * i by omega]; exact hw1
    · rw [off_off, show 8 + 32 * i + 16 = 24 + 32 * i by omega]; exact hw2'
    · rw [off_off, off_off, show 8 + 32 * i + 16 + 8 = 32 + 32 * i by omega]; exact hw3'
  -- The buffer, the state, the `TState`.
  have hA4 : Agree st2.data.dmem st4.data.dmem (rA m0) 200 (Wi i) :=
    agree_of_sameOutside (R := InRange (fb m0) 160) hrn
      (fun q hq hr ↦ r_not_frame h (Transcript.inRange_mono hq (by omega)) hr) hs4'
  have hlen : rs.toList.length = i := by rw [Array.length_toList, hrs]
  have hbr4 : BufRoundsAt st4.data.dmem (rA m0) (rs.toList ++ [ρ]) :=
    bufRoundsAt_push hbr2 (by rw [hlen]; unfold roundCap; omega) (by rw [hlen]; exact hA4)
      (by rw [hlen]; exact hcnt) (by rw [hlen]; exact hab4)
  have hws4 : WhirStateAt st4.data.dmem (pA m0) w2 :=
    WhirStateAt.agree hws2 fun j hj _ ↦ hs4' _ (p_not_store h hj)
  have hts4 : TStateAt st4.data.dmem (tA m0) a s2 :=
    TStateAt.frame (show TStateAt st3.data.dmem (tA m0) a s2 by rw [hd3]; exact hts2) (hm4.kept hwf3) (fun q hq ↦ t_not_store h hq) hs4
  -- `Inv (i + 1)`.
  have e13 : reg st4.data .r13 = reg st.data .r13 :=
    (hm4.regs .r13 _ (kept_spec hk4 (by simp))).trans (hr3 .r13 rfl)
  have e14 : reg st4.data .r14 = reg st.data .r14 :=
    (hm4.regs .r14 _ (kept_spec hk4 (by simp))).trans (hr3 .r14 rfl)
  have e15 : reg st4.data .r15 = reg st.data .r15 :=
    (hm4.regs .r15 _ (kept_spec hk4 (by simp))).trans (hr3 .r15 rfl)
  have ebx : reg st4.data .rbx = reg st.data .rbx :=
    (hm4.regs .rbx _ (kept_spec hk4 (by simp))).trans (hr3 .rbx rfl)
  have hInv : Inv a s w m0 (i + 1) 8 st4.data :=
    ⟨hw4.fr, hw4.same, (hm4.regs .r12 _ h12').trans (Transcript.eval_ptr rfl), e13.trans hI.r13,
      e14.trans hI.r14, e15.trans hI.r15, by rw [ebx]; exact hI.rbx,
      fun _ ↦ (hm4.regs .rbp _ hbp').trans (Transcript.eval_ptr0 48),
      ⟨w2, rs.push ρ, s2, foldRounds_some hrun hfr2, by rw [Array.size_push, hrs],
        by rw [foldRound_alphas hfr2, hal1]; omega, hws4,
        by rw [Array.toList_push]; exact hbr4, hts4⟩⟩
  -- `n` against the rounds done.
  simp only [PcOk] at hpc4
  have hx13 : reg st3.data .r13 = reg m0 .rsi := (hr3 .r13 rfl).trans hI.r13
  rw [cnt_eq (by omega), hx13] at hpc4
  by_cases he : (reg m0 .rsi).toNat = i + 1
  · rw [decide_eq_true he] at hpc4
    simp only [↓reduceIte] at hpc4
    exact done hp h (hpc4.trans (hp.label NativeRustcVmX64.Vm.FoldRounds.label_3_at)) (by rw [he]; exact hInv)
  · rw [decide_eq_false he] at hpc4
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
    exact cont st4 hpc4 he hInv

/-- **A round after the first**: its call block (`C`), then `round`. -/
theorem step (hp : Placed code k)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmX64.Vm.FoldRound.entryLabel) (FoldRoundPre a s w) (FoldRoundPost a s w))
    (h : FoldRoundsPre a s w m0) (i : Nat)
    {C T S : List Directive} {kc : Nat} {SC ST SS S0 : SState} {cT : SBool}
    (hC : C.IsInfixAt code kc) (hCne : C ≠ [])
    (hrunC : exec C midS = some (SC, .call NativeRustcVmX64.Vm.FoldRound.entryLabel))
    (hokC : CallOk (after C midS))
    (hT : T.IsInfixAt code (kc + C.length)) (hTne : T ≠ [])
    (hrunT : exec T midS = some (ST, .cond cT NativeRustcVmX64.Vm.FoldRounds.label_2)) (hokT : TagOk (after T midS))
    (hc0 : ∀ d : MachineData, WordAt d.dmem (off (fb m0) 40) 0 →
      cT.eval (frameEnv m0 d 160 []) = true)
    (hc1 : ∀ d : MachineData, WordAt d.dmem (off (fb m0) 40) 1 →
      cT.eval (frameEnv m0 d 160 []) = false)
    (hS : S.IsInfixAt code (kc + C.length + T.length)) (hSne : S ≠ [])
    (hS0 : S0 = store0S ∨ (S0 = storeS ∧ 0 < i))
    (hrunS : exec S S0 =
      some (SS, .cond (.cmp .eq .W64 (.reg .r13) (.lit (i + 1))) NativeRustcVmX64.Vm.FoldRounds.label_3))
    (hokS : StoreOk i (after S S0)) (hi : i < (reg m0 .rsi).toNat) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + kc)) (hI : Inv a s w m0 i 8 st.data)
    (cont : ∀ st' : MachineState,
      st'.pc = Host.addrOf (k + (kc + C.length + T.length) + S.length) →
      (reg m0 .rsi).toNat ≠ i + 1 → Inv a s w m0 (i + 1) 8 st'.data →
      Eventually (step1 Host.exe) (Goal a s w m0) st') :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  rw [after_eq hrunC] at hokC
  have c := ctx h
  have hwf := c.wf0 (d := st.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + kc + C.length)).toBitVec) hI.fr.kept
  refine exec_at (inf hp hC hCne) hrunC hwf (fun _ _ ↦ rfl) hpc (mid hI.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw0, hdi, hsi, hdx, hk⟩ := hokC
  have hf1 := Frame.of_block hI.fr hwf hm1 hmid slots_le
  have hs1 : SameOutside st.data.dmem st1.data.dmem (InRange (fb m0) 8) :=
    Transcript.sameOutside_low hwf hm1 (r := 0) rfl (by omega) (wr0_spec hw0)
  have hr1 : ∀ r ∈ cs, reg st1.data r = reg st.data r := fun r hr ↦ hm1.regs r _ (kept_spec hk hr)
  have hfs : ∀ q, InRange (fb m0) 8 q → InRange (fb m0) 168 q :=
    fun q hq ↦ Transcript.inRange_mono hq (by omega)
  obtain ⟨w1, rs, s1, hrun, hrs, hal1, hws1, hbr1, hts1⟩ := hI.run
  have hrn : (rA m0).toNat + 200 ≤ 2 ^ 64 := (pre_r h).2.1
  have hI1 : Inv a s w m0 i 0 st1.data :=
    ⟨hf1, fun q hq ↦ (hs1 q fun h' ↦ hq (.inr (c.frame_stack (Transcript.inRange_mono h'
        (by omega))))).trans (hI.same q hq),
      (hr1 .r12 (by simp [cs])).trans hI.r12, (hr1 .r13 (by simp [cs])).trans hI.r13,
      (hr1 .r14 (by simp [cs])).trans hI.r14, (hr1 .r15 (by simp [cs])).trans hI.r15,
      by rw [hr1 .rbx (by simp [cs])]; exact hI.rbx,
      fun hi0 ↦ (hr1 .rbp (by simp [cs])).trans (hI.rbp hi0),
      ⟨w1, rs, s1, hrun, hrs, hal1,
        WhirStateAt.agree hws1 fun j hj _ ↦ hs1 _ fun hq ↦ (p_not h hj).1 (hfs _ hq),
        bufRoundsAt_agree hbr1 fun j hj _ ↦ hs1 _ fun hq ↦
          r_not_frame h (hfs _ hq) (inRange_off_self hj (by omega)),
        c.ts_frame (hm1.kept hwf) (L := 8) (by omega) hs1 hts1⟩⟩
  simp only [PcOk] at hpc1
  exact round hp hfr h i hT hTne hrunT hokT hc0 hc1 hS hSne hS0 hrunS hokS hi
    ⟨hpc1.1, hpc1.2.trans (by rw [Nat.add_assoc])⟩ hI1
    ((hm1.regs .rdi _ hdi).trans (Transcript.eval_ptr0 40))
    ((hm1.regs .rsi _ hsi).trans hI.r15) ((hm1.regs .rdx _ hdx).trans hI.r14) cont

end

end NativeRustcVmX64.Whir.FoldRounds
