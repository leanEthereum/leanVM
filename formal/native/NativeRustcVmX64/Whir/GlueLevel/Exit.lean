module

public import NativeRustcVmX64.Whir.GlueLevel.Third

/-!
# `glue_level`'s exit (x86-64)

`b13` pops the registers and returns. The state is `glueLevel`'s: the new claim, the `α`s, the
glued claims so far and the two new ones, their count (`exit_step`).
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Vm.GlueLevel
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

public section

variable {s : WhirStateW} {m0 : MachineData}

theorem ew_add (x y : EW) : x + y = ⟨x.c0 ^^^ y.c0, x.c1 ^^^ y.c1⟩ := rfl

theorem ofBitVec_toNat (x : BitVec 64) : x.toNat.toUInt64 = UInt64.ofBitVec x :=
  UInt64.ofNat_toNat (x := UInt64.ofBitVec x)

/-- An element from its two words. -/
theorem ewAt_of {d : DataMem} {a : BitVec 64} {x : EW} (h0 : WordAt d (off a 0) x.c0)
    (h1 : WordAt d (off a 8) x.c1) : EWAt d a x := by
  rw [off_zero] at h0
  exact NativeRustcVm.ewAt_iff.mpr ⟨h0, h1⟩

theorem glue_claim {mu : Nat} {pt : Array EW} :
    (glueLevel s (lamOf m0) mu pt (oodOf m0) (glueArgs m0).1 (glueArgs m0).2.1
      (glueArgs m0).2.2).claim = s.claim + mul1 m0 + cc2 m0 := by
  simp only [glueLevel, glueArgs, mul1, cc2, l2, batOf]

theorem glue_glued {mu : Nat} {pt : Array EW} :
    (glueLevel s (lamOf m0) mu pt (oodOf m0) (glueArgs m0).1 (glueArgs m0).2.1
      (glueArgs m0).2.2).glued = s.glued ++ #[⟨lamOf m0, s.alphas.size, .eq pt⟩,
        ⟨l2 m0, s.alphas.size, .induced mu (glueArgs m0).1 (glueArgs m0).2.1⟩] := by
  simp only [glueLevel, l2]

/-- A change in the stack and the state's regions is in the stack and the state. -/
theorem outs_state (hpre : GlueLevelPre s m0) {wr : Nat → Bool} {q : BitVec 64}
    (h : outsOf (rsOf s m0) wr q) : InRange (pOf m0) stateBytes q := by
  obtain ⟨i, e, -, he, hin⟩ := h
  obtain ⟨⟨o, sz⟩, ho, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? he)
  obtain ⟨hpos, hle⟩ := offs_le _ (pre_cap hpre) _ ho
  have hpnw := pre_pnw hpre
  have hnw := noWrap_off hpnw hpos hle
  simp only at hin hnw
  rw [Sym.inRange_iff hnw] at hin
  unfold NoWrap at hpnw
  rw [Sym.inRange_iff hpnw]
  rw [toNat_off (by omega)] at hin
  omega

variable [Host] {k : Nat}

/-- **From `b13` to the return.** -/
theorem exit_step (hp : Placed code k) (hpre : GlueLevelPre s m0) {st : MachineState}
    (h : AtB13 s m0 k st) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ GlueLevelPost s m0 st.data)
      st := by
  obtain ⟨⟨hpc, hB⟩, hpt, hqs, hws, hal⟩ := h
  obtain ⟨m13, pc13⟩ := st
  simp only at hpc hB hpt hqs hws hal
  subst hpc
  have hl := lay hpre
  have hpnw := pre_pnw hpre
  have hn := pre_size hpre
  have hst := pre_st hpre
  refine exitStepA hl hB (b13_in_code.trans hp.1 (by simp [b13])) run_b13
    ([1, 3, 4, 6].contains ·) (sub_of _ (by simp)) (by rw [rs_sizes]; rfl) rfl
    (fun r hr ↦ ?_) fun st hm hret hrsp hsame hsv hloc ↦ .done _ ⟨hret, hrsp, ?_, ?_, ?_, hsv⟩
  · cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr <;> exact ⟨_, rfl, rfl⟩
  · -- AL
    show (reg st.data .rax).toNat % 256 = 1
    rw [show reg st.data .rax = _ from hm.regs .rax _ rfl]
    exact hal
  · -- the state
    have hb1 : Same m0.dmem st.data.dmem (off (pOf m0) 16) 488 := keep_reg hpre hsame rs_1 rfl
    have hold : Same m0.dmem st.data.dmem (off (pOf m0) 512) (6064 * s.glued.size) :=
      keep_old hpre hsame
    have hal' : s.alphas.size ≤ stackCap := by
      have := hst.alphas.1
      rwa [Array.length_toList] at this
    have hmu : (reg m0 .rcx).toNat ≤ stackCap := hpre.2.2.2.2.1
    have e20 : UInt64.ofBitVec (vA s m0 20) = (s.claim + mul1 m0 + cc2 m0).c0 := by
      apply UInt64.toBitVec_inj.mp
      show c0 (cc2 m0) ^^^ (c0 (mul1 m0) ^^^ c0 s.claim) = _
      simp only [ew_add, UInt64.toBitVec_xor, c0]
      ac_rfl
    have e21 : UInt64.ofBitVec (vA s m0 21) = (s.claim + mul1 m0 + cc2 m0).c1 := by
      apply UInt64.toBitVec_inj.mp
      show c1 (cc2 m0) ^^^ (c1 (mul1 m0) ^^^ c1 s.claim) = _
      simp only [ew_add, UInt64.toBitVec_xor, c1]
      ac_rfl
    have e27 : UInt64.ofBitVec (vA s m0 27) = (s.glued.size + 2).toUInt64 := by
      apply UInt64.toBitVec_inj.mp
      show BitVec.ofNat 64 s.glued.size + BitVec.ofNat 64 1 + BitVec.ofNat 64 1 =
        BitVec.ofNat 64 (s.glued.size + 2)
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    have w20 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 1) (o := 0)
      (b := off (pOf m0) 0) (sz := 16) rfl (by decide) (v := .var 20) (by decide)
    have w21 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 1) (o := 8)
      (b := off (pOf m0) 0) (sz := 16) rfl (by decide) (v := .var 21) (by decide)
    have w27 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 3) (o := 0)
      (b := off (pOf m0) 504) (sz := 8) rfl (by decide) (v := .var 27) (by decide)
    have g10 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 4) (o := 0)
      (b := off (pOf m0) (o1 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 8) (by decide)
    have g18 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 4) (o := 8)
      (b := off (pOf m0) (o1 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 9) (by decide)
    have g116 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 4) (o := 16)
      (b := off (pOf m0) (o1 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 22) (by decide)
    have g124 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 4) (o := 24)
      (b := off (pOf m0) (o1 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 23) (by decide)
    have g20 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 6) (o := 0)
      (b := off (pOf m0) (o2 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 18) (by decide)
    have g28 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 6) (o := 8)
      (b := off (pOf m0) (o2 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 17) (by decide)
    have g216 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 6) (o := 16)
      (b := off (pOf m0) (o2 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 22) (by decide)
    have g224 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 6) (o := 24)
      (b := off (pOf m0) (o2 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 26) (by decide)
    have g232 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 6) (o := 32)
      (b := off (pOf m0) (o2 s.glued.size)) (sz := 40) rfl (by decide) (v := .var 12) (by decide)
    have hpt := bufEWAt_keep0 (keep_reg hpre hloc rs_4 rfl) (by decide) hpt
    have hqs := bufWordsAt_keep0 (keep_reg hpre hloc rs_6 rfl) (by decide) hqs
    have hws := bufEWAt_keep0 (keep_reg hpre hloc rs_7 rfl) (by decide) hws
    let g1 : GluedClaimW := ⟨lamOf m0, s.alphas.size, .eq (slice m0 (reg m0 .r8) (reg m0 .r9))⟩
    let g2 : GluedClaimW := ⟨l2 m0, s.alphas.size,
      .induced (reg m0 .rcx).toNat (glueArgs m0).1 (glueArgs m0).2.1⟩
    have hg1 : GluedAt st.data.dmem (off (pOf m0) (gluedOff + 8 + gluedBytes * s.glued.size)) g1 := by
      rw [show gluedOff + 8 + gluedBytes * s.glued.size = o1 s.glued.size from rfl]
      refine ⟨ewAt_of g10 g18, show s.alphas.size < 2 ^ 64 by unfold stackCap at hal'; omega,
        g116, g124, ?_⟩
      show BufEWAt st.data.dmem (off (off (pOf m0) (o1 s.glued.size)) 40) stackCap
        (slice m0 (reg m0 .r8) (reg m0 .r9)).toList
      rw [off_off]
      exact hpt
    have hg2 : GluedAt st.data.dmem
        (off (pOf m0) (gluedOff + 8 + gluedBytes * (s.glued.size + 1))) g2 := by
      rw [show gluedOff + 8 + gluedBytes * (s.glued.size + 1) = o2 s.glued.size from rfl]
      have e18 : UInt64.ofBitVec ((Sym.var 18).eval (envG s m0 m13 (vA s m0) 0)) = (l2 m0).c0 :=
        congrArg UInt64.ofBitVec (show vA s m0 18 = c0 (l2 m0) from rfl)
      have e17 : UInt64.ofBitVec ((Sym.var 17).eval (envG s m0 m13 (vA s m0) 0)) = (l2 m0).c1 :=
        congrArg UInt64.ofBitVec (show vA s m0 17 = c1 (l2 m0) from rfl)
      have e26 : UInt64.ofBitVec ((Sym.var 26).eval (envG s m0 m13 (vA s m0) 0)) = 1 := rfl
      have e12 : UInt64.ofBitVec ((Sym.var 12).eval (envG s m0 m13 (vA s m0) 0)) =
          (reg m0 .rcx).toNat.toUInt64 :=
        (congrArg UInt64.ofBitVec (show vA s m0 12 = reg m0 .rcx from rfl)).trans
          (ofBitVec_toNat _).symm
      rw [e18] at g20
      rw [e17] at g28
      rw [e26] at g224
      rw [e12] at g232
      have hq1 : (glueArgs m0).1.toList = qsOf m0 := by
        simp only [glueArgs, wordSlice, qsOf, List.toList_toArray]
      have hw1 : (glueArgs m0).2.1.toList = wsOf m0 := by simp only [glueArgs, wsOf]
      refine ⟨ewAt_of g20 g28, show s.alphas.size < 2 ^ 64 by unfold stackCap at hal'; omega,
        g216, g224, hmu, g232, ?_, ?_⟩
      · rw [hq1, off_off]
        exact hqs
      · rw [hw1, off_off]
        exact hws
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- the claim
      rw [glue_claim]
      refine ewAt_of ?_ ?_
      · rw [← e20]; rw [off_off] at w20; exact w20
      · rw [← e21]; rw [off_off] at w21; exact w21
    · exact bufEWAt_keep0 hb1 (by decide) hst.alphas
    · simp only [glue_glued, Array.size_append, List.size_toArray, List.length_cons,
        List.length_nil]
      have := pre_cap hpre
      omega
    · simp only [glue_glued, Array.size_append, List.size_toArray, List.length_cons,
        List.length_nil, Nat.zero_add]
      rw [show s.glued.size + (1 + 1) = s.glued.size + 2 from rfl, ← e27]
      rw [← off_zero (off (pOf m0) gluedOff)]
      exact w27
    · intro i hi
      simp only [glue_glued, Array.size_append, List.size_toArray, List.length_cons,
        List.length_nil] at hi ⊢
      rcases Nat.lt_or_ge i s.glued.size with hlt | hge
      · rw [Array.getElem_append_left hlt]
        have := hst.glued i hlt
        rw [show gluedOff + 8 + gluedBytes * i = 512 + 6064 * i from rfl, ← off_off] at this ⊢
        exact gluedAt_keep hold (by unfold gluedBytes; omega) this
      · rw [Array.getElem_append_right hge]
        rcases (show i = s.glued.size ∨ i = s.glued.size + 1 by omega) with rfl | rfl
        · simp only [Nat.sub_self, List.getElem_toArray, List.getElem_cons_zero]
          exact hg1
        · simp only [Nat.add_sub_cancel_left, List.getElem_toArray, List.getElem_cons_succ,
            List.getElem_cons_zero]
          exact hg2
  · -- the frame
    intro q hq
    exact hsame q fun h' ↦ hq (h'.elim .inr fun h ↦ .inl ⟨_, List.mem_singleton_self _,
      outs_state hpre h⟩)

end

end NativeRustcVmX64.Whir.GlueLevel
