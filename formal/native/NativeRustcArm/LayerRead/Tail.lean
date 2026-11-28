module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.LayerRead.Mid
meta import NativeRustcArm.Code.Xmss.LayerRead

/-!
# `LayerSignature::read`: assembling the output

The final two copies write the path and chain values. Between them block 22
reads the randomizer from the preserved input and writes it at `out + 1184`.
Block 23 restores the saved registers and releases the frame.
-/

namespace NativeRustcArm.Xmss.LayerRead

open NativeRustcArm.Sym NativeRustcArm

set_option Elab.async false

/-- After the `memcpy` of the path. -/
structure TailAt (m₀ m : MachineData) : Prop where
  x19 : (m.regs.getXReg .X19).toBitVec = out m₀
  x21 : (m.regs.getXReg .X21).toBitVec = sig m₀
  keep : ∀ r ∈ [XReg.X25, .X26, .X27], m.regs.getXReg r = m₀.regs.getXReg r
  sp : m.regs.SP.toBitVec = frame m₀
  same : SameOutside m₀.dmem m.dmem (fun p => Scratch m₀ p ∨ InRange (out m₀) 1200 p)
  kept : Kept m₀.dmem m.dmem
  save : ∀ j < 10, j ≠ 3 → BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 (1856 + 8 * j))
    (regBytes (m₀.regs.getXReg (saveRegs.getD j .X0)).toBitVec)
  rand : BytesAt m.dmem (sig m₀) (rand m₀)
  cursorData : BytesAt m.dmem (cur m₀) (regBytes (sig m₀ + 1200))
  cursorLength : BytesAt m.dmem (cur m₀ + 8) (regBytes (BitVec.ofNat 64 (remaining m₀ - 1200)))
  chain : BytesAt m.dmem (frame m₀) (chainBytes m₀)
  path : BytesAt m.dmem (out m₀) (pathBytes m₀)

theorem length_pathBytes {m₀ : MachineData} (P : Pre m₀) : (pathBytes m₀).length = 256 := by
  unfold pathBytes
  rw [List.length_flatten, List.map_map]
  have : ∀ n ≤ 16, ((List.range n).map (List.length ∘ pathSlot m₀)).sum = 16 * n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp [P.pathSlot_length (j := n) (by omega)]
      omega
  exact this 16 le_rfl

section
variable {m₀ : MachineData}

theorem out_apart_frame (P : Pre m₀) {o s x : Nat} (hs : o + s ≤ 1200) (hx : x < 1936) (h0 : 0 < s) :
    ¬InRange (out m₀ + BitVec.ofNat 64 o) s (frame m₀ + BitVec.ofNat 64 x) :=
  not_inRange_of_apart (NoWrap.sub P.outNW hs)
    ((P.outF.sub_left P.outNW hs h0).sub_right P.frameNW (by unfold layerReadStack; omega) (by omega))

theorem out_apart_cur (P : Pre m₀) {o s x : Nat} (hs : o + s ≤ 1200) (hx : x < 16) (h0 : 0 < s) :
    ¬InRange (out m₀ + BitVec.ofNat 64 o) s (cur m₀ + BitVec.ofNat 64 x) :=
  not_inRange_of_apart (NoWrap.sub P.outNW hs)
    ((P.outCur.sub_left P.outNW hs h0).sub_right P.curNW (by omega) (by omega))

end

/-- The `memcpy` of the path. -/
theorem tailAt_of [Labels] {m₀ m m' : MachineData} (P : Pre m₀) (h : PathCall m₀ m)
    (hpost : MemcpyPost m m') : TailAt m₀ m' := by
  have C := h.common
  obtain ⟨-, hcopy, hsame, hs⟩ := hpost
  have hx0 : m.regs.X0.toBitVec = out m₀ := h.x0
  have hx1 : m.regs.X1.toBitVec = frame m₀ + BitVec.ofNat 64 928 := h.x1
  have hx2 : m.regs.X2.toNat = 256 := by
    show m.regs.X2.toBitVec.toNat = 256
    erw [h.x2]
    rfl
  simp only [hx0, hx1, hx2] at hcopy hsame
  have hof : ∀ x < 1936, ¬InRange (out m₀) 256 (frame m₀ + BitVec.ofNat 64 x) := fun x hx => by
    simpa using out_apart_frame (o := 0) P (by omega) hx (by omega)
  have hoc : ∀ x < 16, ¬InRange (out m₀) 256 (cur m₀ + BitVec.ofNat 64 x) := fun x hx => by
    simpa using out_apart_cur (o := 0) P (by omega) hx (by omega)
  have hrand : BytesAt m.dmem (sig m₀) (rand m₀) := by
    refine bytesAt_slice (by omega) fun t ht => ?_
    rw [C.same _ (P.sig_not_scratch (by omega))]
    simp only [Nat.zero_add]
    change m₀.dmem.get? (sig m₀ + BitVec.ofNat 64 t) =
      some ((m₀.dmem.get? (sig m₀ + BitVec.ofNat 64 t)).getD 0)
    have hm := P.sigMapped t (by omega)
    cases he : m₀.dmem.get? (sig m₀ + BitVec.ofNat 64 t) <;> simp_all
  refine ⟨by rw [hs.1 .X19 rfl]; exact C.x19,
    by rw [hs.1 .X21 rfl]; exact C.x21, fun r hr => ?_, by rw [hs.2.1]; exact C.sp,
    (C.same.trans hsame).mono fun p hp => hp.elim Or.inl fun hp' => Or.inr ?_,
    C.kept.trans hs.2.2, fun j hj hj3 => (C.save j hj hj3).sameOutside hsame fun t ht => ?_,
    hrand.sameOutside hsame (fun t ht => ?_),
    h.cursorData.sameOutside hsame (fun t ht => hoc t (by rw [length_regBytes] at ht; omega)),
    h.cursorLength.sameOutside hsame (fun t ht => by
      change ¬InRange (out m₀) 256 (cur m₀ + BitVec.ofNat 64 8 + BitVec.ofNat 64 t)
      rw [addr_add_addr]
      exact hoc _ (by rw [length_regBytes] at ht; omega)),
    h.chain.sameOutside hsame (fun t ht => hof t (by rw [length_chainBytes P] at ht; omega)), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hs.1 _ rfl).trans (C.keep _ (by simp))
  · unfold InRange at hp' ⊢
    omega
  · rw [addr_add_addr]
    exact hof _ (by rw [length_regBytes] at ht; omega)
  · simpa using not_inRange_of_apart (NoWrap.sub P.outNW (i := 0) (k := 256) (by omega))
      ((P.outSig.sub_left P.outNW (i := 0) (k := 256) (by omega) (by omega)).sub_right P.sigNW
        (by rw [P.rand_length] at ht; omega) (by omega))
  · have := h.path.bytesOf
    rw [length_pathBytes P] at this
    rw [this] at hcopy
    exact hcopy

/-- Block 22's regions: the frame, output, and input randomizer. -/
def stT0 : SState := init [(1936, true), (1200, false), (16, false)] (.ptr 0 0)
  [(.X19, .ptr 1 0), (.X21, .ptr 2 0)]

sym_block b22_execT := exec b22 stT0

/-- The symbolic state after block 22. -/
def stT1 : SState := ((exec b22 stT0).getD (stT0, .fall)).1

theorem stT1_facts : stT1.reg .X0 = some (.ptr 1 256) ∧ stT1.reg .X1 = some (.ptr 0 0) ∧
    stT1.reg .X2 = some (.lit 928) ∧ keeps stT0 stT1 = true ∧ writesIn stT1 [1] = true ∧
    firstOverlap 0 0 928 stT1.mem = none ∧
    (∀ j < 10, firstOverlap 0 (1856 + 8 * j) 8 stT1.mem = none) ∧
    firstOverlap 1 0 256 stT1.mem = none := by decide +kernel

theorem stT1_rand : ∀ t < 16,
    findWrite 1 (1184 + t) stT1.mem = some (.load 2 (8 * (t / 8)) 8, t % 8) := by decide +kernel

/-- The symbolic state at block 23: region 0 the frame. -/
def stE0 : SState := init [(1936, true)] (.ptr 0 0)

sym_block b23_execE := exec b23 stE0

/-- The symbolic state after block 23. -/
def stE1 : SState := ((exec b23 stE0).getD (stE0, .fall)).1

theorem stE1_facts : stE1.mem = [] ∧ stE1.sp = .ptr 0 1936 ∧
    (∀ j < 10, j ≠ 3 → stE1.reg (saveRegs.getD j .X0) = some (.load 0 (1856 + 8 * j) 8)) ∧
    ∀ r ∈ [XReg.X25, .X26, .X27], stE1.reg r = some (.reg r) := by decide +kernel

theorem saveRegs_cases (r : XReg) (hr : calleeSaved r = true) :
    (∃ j < 10, j ≠ 3 ∧ saveRegs.getD j .X0 = r) ∨ r ∈ [XReg.X25, .X26, .X27] := by
  cases r <;> simp_all [calleeSaved] <;> decide

theorem frame_add_stack (m₀ : MachineData) :
    frame m₀ + BitVec.ofNat 64 1936 = m₀.regs.SP.toBitVec := by
  unfold frame stackBelow layerReadStack
  exact BitVec.sub_add_cancel _ _

theorem memBytes_takeLayer (m₀ : MachineData) :
    (NativeRustc.Xmss.takeLayer (LayerReadPre.bytes m₀) 0).1.memBytes =
      pathBytes m₀ ++ chainBytes m₀ ++ rand m₀ := by
  simp only [NativeRustc.Xmss.takeLayer, NativeRustc.Xmss.LayerSignature.memBytes, pathBytes,
    chainBytes, rand]
  rfl

/-- **The output**: from the call of the path's `memcpy` to the return. -/
public theorem tail [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Labels.label NativeRustcArm.Common.Memcpy.entryLabel)
    (hret : retOf st.data = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b22Offset)) (h : PathCall m₀ st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧ LayerReadPost m₀ st'.data) st := by
  have hpre : MemcpyPre st.data := by
    have hx0 : st.data.regs.X0.toBitVec = out m₀ := h.common.x19 ▸ h.x0
    have hx1 : st.data.regs.X1.toBitVec = frame m₀ + BitVec.ofNat 64 928 := h.x1
    have hx2 : st.data.regs.X2.toNat = 256 := by
      show st.data.regs.X2.toBitVec.toNat = 256
      erw [h.x2]
      rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hx0, hx1, hx2]
    · simpa using (P.outMapped.sub (i := 0) (k := 256) (by omega)).kept h.common.kept
    · exact (P.frameMapped.sub (by unfold layerReadStack; omega)).kept h.common.kept
    · simpa using NoWrap.sub (i := 0) (k := 256) P.outNW (by omega)
    · exact P.frameNW.sub (by unfold layerReadStack; omega)
    · simpa using (P.outF.sub_left (i := 0) (k := 256) P.outNW (by omega) (by omega)).sub_right P.frameNW
        (by unfold layerReadStack; omega) (by omega)
  refine Eventually.bind (Spec.apply hmemcpy hpc hpre) fun st₁ ⟨hpc₁, hpost₁⟩ => ?_
  rw [hret] at hpc₁
  have T := tailAt_of P h hpost₁
  have hs₁ : Saved st.data st₁.data := hpost₁.2.2.2
  have hF := P.frameNW
  have hO := P.outNW
  unfold layerReadStack at hF
  -- Block 22.
  have hwf₂ : (Env.ofMachine st₁.data [(frame m₀, 1936), (out m₀, 1200), (sig m₀, 16)]).WF :=
    Env.wf_of ⟨⟨P.frameMapped.kept T.kept, P.frameNW⟩, ⟨P.outMapped.kept T.kept, P.outNW⟩,
      ⟨(show Mapped m₀.dmem (sig m₀) 16 from fun i hi => P.sigMapped i (by omega)).kept T.kept,
        by change (sig m₀).toNat + 16 ≤ 2 ^ 64; have := P.sigNW; omega⟩, trivial⟩
      (pairwise3 P.outF.symm
        (by simpa [layerReadStack] using P.sigF.symm.sub_right P.sigNW (i' := 0) (k' := 16) (by omega) (by omega))
        (by simpa using P.outSig.sub_right P.sigNW (i' := 0) (k' := 16) (by omega) (by omega)))
  have hm₁ : Match (Env.ofMachine st₁.data [(frame m₀, 1936), (out m₀, 1200), (sig m₀, 16)]) stT0 st₁.data := by
    unfold stT0
    apply match_ofMachine
    · exact And.intro rfl (And.intro (fun _ => P.frame16) (And.intro rfl (And.intro (by simp)
        (And.intro rfl (And.intro (by simp) trivial)))))
    · rw [T.sp]
      simp [Sym.eval]
    · exact ⟨T.x19.trans (by simp [Sym.eval]), T.x21.trans (by simp [Sym.eval]), trivial⟩
    · exact trivial
    · exact trivial
    · exact trivial
  obtain ⟨hX0, hX1, hX2, hkeeps, hwrites, hch, hsv, hpa⟩ := stT1_facts
  refine call_step (b22_in_code.trans hp.1 (List.cons_ne_nil _ _)) b22_execT hwf₂ hpc₁ hm₁
    fun st₂ hpc₂ hm₂ => ?_
  change Match _ stT1 st₂.data at hm₂
  have hs₂ : Saved st₁.data st₂.data := Match.saved hm₁ hm₂ hwf₂ rfl hkeeps
  have hr0 : (Env.ofMachine st₁.data [(frame m₀, 1936), (out m₀, 1200), (sig m₀, 16)]).regions[0]? =
    some (frame m₀, 1936) := rfl
  have hr1 : (Env.ofMachine st₁.data [(frame m₀, 1936), (out m₀, 1200), (sig m₀, 16)]).regions[1]? =
    some (out m₀, 1200) := rfl
  have hx0 : st₂.data.regs.X0.toBitVec = out m₀ + BitVec.ofNat 64 256 :=
    (hm₂.regs .X0 _ hX0).trans (by simp [Sym.eval])
  have hx1 : st₂.data.regs.X1.toBitVec = frame m₀ :=
    (hm₂.regs .X1 _ hX1).trans (by simp [Sym.eval])
  have hx2 : st₂.data.regs.X2.toNat = 928 := by
    show st₂.data.regs.X2.toBitVec.toNat = 928
    erw [hm₂.regs .X2 _ hX2]
    rfl
  have hk₂ : Kept st₁.data.dmem st₂.data.dmem := hs₂.2.2
  have hsame₂ : SameOutside st₁.data.dmem st₂.data.dmem (InRange (out m₀) 1200) :=
    (hm₂.sameOutside_in hwf₂ hwrites).mono fun p ⟨r, hr, b, sz, hb, hin⟩ => by
      simp only [List.mem_singleton] at hr
      subst r
      cases hb
      exact hin
  have hpre₂ : MemcpyPre st₂.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hx0, hx1, hx2]
    · exact (P.outMapped.sub (by omega)).kept (T.kept.trans hk₂)
    · exact (show Mapped m₀.dmem (frame m₀) 928 from
        fun i hi => P.frameMapped i (by unfold layerReadStack; omega)).kept (T.kept.trans hk₂)
    · exact NoWrap.sub P.outNW (by omega)
    · have hf : (frame m₀).toNat + 1936 ≤ 2 ^ 64 := P.frameNW
      unfold NoWrap
      omega
    · simpa using (P.outF.sub_left P.outNW (by omega) (by omega)).sub_right P.frameNW
        (i' := 0) (k' := 928) (by unfold layerReadStack; omega) (by omega)
  refine call_then hpc₂ hmemcpy hpre₂ fun st₃ hpc₃ hpost₃ => ?_
  obtain ⟨-, hcopy, hsame₃, hs₃⟩ := hpost₃
  simp only [hx0, hx1, hx2] at hcopy hsame₃
  -- Block 23.
  have hk₃ : Kept m₀.dmem st₃.data.dmem := T.kept.trans (hk₂.trans hs₃.2.2)
  have hwf₄ : (Env.ofMachine st₃.data [(frame m₀, 1936)]).WF :=
    Env.wf_of ⟨⟨P.frameMapped.kept hk₃, P.frameNW⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hsp₃ : st₃.data.regs.SP.toBitVec = frame m₀ := by rw [hs₃.2.1, hs₂.2.1]; exact T.sp
  have hm₃ : Match (Env.ofMachine st₃.data [(frame m₀, 1936)]) stE0 st₃.data := by
    unfold stE0
    apply match_ofMachine
    · exact And.intro rfl (And.intro (fun _ => P.frame16) trivial)
    · rw [hsp₃]
      simp [Sym.eval]
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
  refine exec_at (b23_in_code.trans hp.1 (List.cons_ne_nil _ _)) b23_execE hwf₄
    (hpc₃.trans rfl) hm₃ fun st₄ hm₄ hpc₄ => ?_
  change Match _ stE1 st₄.data at hm₄
  obtain ⟨hmem₄, hsp₄, hld₄, hkp₄⟩ := stE1_facts
  have hd₄ : st₄.data.dmem = st₃.data.dmem := hm₄.dmem_eq hwf₄ hmem₄
  -- The saved registers' slots.
  have hsave₃ : ∀ j < 10, j ≠ 3 → BytesAt st₃.data.dmem (frame m₀ + BitVec.ofNat 64 (1856 + 8 * j))
      (regBytes (m₀.regs.getXReg (saveRegs.getD j .X0)).toBitVec) := fun j hj hj3 =>
    (hm₂.bytesAt_keep hr0 (by rw [length_regBytes]; omega) (by rw [length_regBytes]; exact hsv j hj)
      (T.save j hj hj3)).sameOutside hsame₃ fun t ht => by
        rw [addr_add_addr]
        exact out_apart_frame P (by omega) (by rw [length_regBytes] at ht; omega) (by omega)
  have hreg : ∀ j < 10, j ≠ 3 → st₄.data.regs.getXReg (saveRegs.getD j .X0) =
      m₀.regs.getXReg (saveRegs.getD j .X0) := fun j hj hj3 => by
    apply UInt64.toBitVec_inj.mp
    rw [hm₄.regs _ _ (hld₄ j hj hj3)]
    simp only [Sym.eval]
    rw [Env.load_of_bytesAt (length_regBytes _) (by simpa using hsave₃ j hj hj3), ofBytes_regBytes]
    rfl
  have hsaved : Saved m₀ st₄.data := by
    refine ⟨fun r hr => ?_, ?_, hk₃.trans (hd₄ ▸ Kept.refl _)⟩
    · rcases saveRegs_cases r hr with ⟨j, hj, hj3, rfl⟩ | hr'
      · exact hreg j hj hj3
      · have h4 : st₄.data.regs.getXReg r = st₃.data.regs.getXReg r :=
          UInt64.toBitVec_inj.mp (hm₄.regs r _ (hkp₄ r hr'))
        rw [h4, hs₃.1 r hr, hs₂.1 r hr]
        exact T.keep r hr'
    · apply UInt64.toBitVec_inj.mp
      rw [hm₄.sp, hsp₄]
      simp only [Sym.eval, Env.base_ofMachine_eq]
      exact frame_add_stack m₀
  have hx30 : st₄.data.regs.X30 = m₀.regs.X30 := hreg 1 (by omega) (by omega)
  refine .done _ ⟨?_, ?_, ?_, ?_, ?_, hsaved⟩
  · have : st₄.pc = retOf st₄.data := hpc₄
    rw [this]
    unfold retOf
    rw [hx30]
  · -- The layer.
    rw [memBytes_takeLayer, hd₄]
    refine BytesAt.append (BytesAt.append ?_ ?_) ?_
    · have h1 := (hm₂.bytesAt_keep (o := 0) hr1 (by rw [length_pathBytes P]; omega)
        (by rw [length_pathBytes P]; exact hpa) (by simpa using T.path)).sameOutside hsame₃
        fun t ht => by
          rw [length_pathBytes P] at ht
          rw [addr_add_addr, inRange_offsets P.outNW (by omega) (by omega)]
          omega
      exact bytesAt_add_zero h1
    · rw [length_pathBytes P]
      have hc₂ : BytesAt st₂.data.dmem (frame m₀) (chainBytes m₀) :=
        bytesAt_add_zero (hm₂.bytesAt_keep (o := 0) (bs := chainBytes m₀) hr0
          (by rw [length_chainBytes P]; decide)
          (by rw [length_chainBytes P]; exact hch) (by simpa using T.chain))
      have hb₂ := bytesOf_of hc₂ (length_chainBytes P)
      rwa [hb₂] at hcopy
    · rw [List.length_append, length_pathBytes P, length_chainBytes P]
      intro t ht
      rw [P.rand_length] at ht
      have hnot : ¬InRange (out m₀ + BitVec.ofNat 64 256) 928 (out m₀ + BitVec.ofNat 64 (1184 + t)) := by
        rw [inRange_offsets P.outNW (by omega) (by omega)]
        omega
      have hg := hm₂.get?_load hr1 (by omega) (stT1_rand t ht) (by omega) (le_refl 8)
      change st₃.data.dmem.get? (out m₀ + BitVec.ofNat 64 (256 + 928) + BitVec.ofNat 64 t) = _
      rw [addr_add_addr, show 256 + 928 + t = 1184 + t by omega, hsame₃ _ hnot, hg,
        show 8 * (t / 8) + t % 8 = t by omega]
      simp only [Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some, Env.ofMachine_mem0]
      rw [T.rand t (by rw [P.rand_length]; exact ht)]
      rfl
  · -- The descriptor's pointer.
    rw [hd₄]
    have h₂ := T.cursorData.sameOutside hsame₂ fun t ht => by
      simpa using out_apart_cur P (o := 0) (s := 1200) (by omega)
        (by rw [length_regBytes] at ht; omega) (by omega)
    have h₃ := h₂.sameOutside hsame₃ fun t ht => out_apart_cur P (by omega)
      (by rw [length_regBytes] at ht; omega) (by omega)
    rw [regBytes_eq_wordBytes] at h₃
    exact h₃
  · -- The descriptor's remaining length.
    rw [hd₄]
    have h₂ := T.cursorLength.sameOutside hsame₂ fun t ht => by
      change ¬InRange (out m₀) 1200 (cur m₀ + BitVec.ofNat 64 8 + BitVec.ofNat 64 t)
      rw [addr_add_addr]
      simpa using out_apart_cur P (o := 0) (s := 1200) (by omega)
        (by rw [length_regBytes] at ht; omega) (by omega)
    have h₃ := h₂.sameOutside hsame₃ fun t ht => by
      change ¬InRange (out m₀ + BitVec.ofNat 64 256) 928
        (cur m₀ + BitVec.ofNat 64 8 + BitVec.ofNat 64 t)
      rw [addr_add_addr]
      exact out_apart_cur P (by omega) (by rw [length_regBytes] at ht; omega) (by omega)
    rw [regBytes_eq_wordBytes] at h₃
    exact h₃
  · -- What changed.
    rw [hd₄]
    refine ((T.same.trans (hm₂.sameOutside_in hwf₂ hwrites)).trans hsame₃).mono fun p hp => ?_
    rcases hp with (hp | hp) | hp
    · rcases hp with (hp | hp) | hp
      · exact Or.inr (Or.inr hp)
      · exact Or.inr (Or.inl hp)
      · exact Or.inl hp
    · obtain ⟨r, hr, b, sz, hb, hin⟩ := hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      cases hb
      exact Or.inl hin
    · exact Or.inl (inRange_sub P.outNW (by omega) hp)

end NativeRustcArm.Xmss.LayerRead
