module

public import NativeRustcX64.Code.Common.Memcpy.Names

public import NativeRustcX64.LayerRead.Mid
public import NativeRustcX64.LayerRead.TailExec

/-! # The output copies, randomizer, and return -/

namespace NativeRustcX64.Xmss.LayerRead

open NativeRustcX64.Sym

set_option Elab.async false

structure TailAt [Labels] (m₀ m : MachineData) : Prop where
  r14 : reg m .r14 = out m₀
  rsp : reg m .rsp = base m₀ + 8#64
  same : SameOutside m₀.dmem m.dmem (fun p => Scratch m₀ p ∨ InRange (out m₀) 1200 p)
  kept : Kept m₀.dmem m.dmem
  save : ∀ j < 6, BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (1888 + 8 * j))
    (regBytes (reg m₀ (saveRegs.getD j .rax)))
  input : BytesAt m.dmem (base m₀ + 16#64) (regBytes (sig m₀))
  cursor : BytesAt m.dmem (cur m₀) (regBytes (sig m₀ + 1200#64))
  length : BytesAt m.dmem (cur m₀ + 8#64) (regBytes (BitVec.ofNat 64 (remaining m₀ - 1200)))
  chain : BytesAt m.dmem (base m₀ + 960#64) (chainBytes m₀)
  path : BytesAt m.dmem (out m₀) (pathBytes m₀)
  rbx : reg m .rbx = (Labels.label "memcpy").toBitVec

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

theorem out_apart_stack (P : Pre m₀) {o s x : Nat} (hs : o + s ≤ 1200) (hx : x < 1944)
    (h0 : 0 < s) : ¬InRange (out m₀ + BitVec.ofNat 64 o) s (base m₀ + BitVec.ofNat 64 x) :=
  not_inRange_of_apart (NoWrap.sub P.outNW hs)
    ((P.outF.sub_left P.outNW hs h0).sub_right P.baseNW (by omega) (by omega))

theorem out_apart_cur (P : Pre m₀) {o s x : Nat} (hs : o + s ≤ 1200) (hx : x < 16) (h0 : 0 < s) :
    ¬InRange (out m₀ + BitVec.ofNat 64 o) s (cur m₀ + BitVec.ofNat 64 x) :=
  not_inRange_of_apart (NoWrap.sub P.outNW hs)
    ((P.outCur.sub_left P.outNW hs h0).sub_right P.curNW (by omega) (by omega))

theorem not_scratch_ret (P : Pre m₀) {i : Nat} (hi : i < 8) :
    ¬(Scratch m₀ (base m₀ + BitVec.ofNat 64 (1936 + i)) ∨
      InRange (out m₀) 1200 (base m₀ + BitVec.ofNat 64 (1936 + i))) := by
  rintro ((h | h) | h)
  · have h' : ¬InRange (base m₀ + BitVec.ofNat 64 0) 1936
        (base m₀ + BitVec.ofNat 64 (1936 + i)) := by
      rw [inRange_offsets P.baseNW (by omega) (by omega)]
      omega
    simp only [BitVec.add_zero] at h'
    exact h' h
  · exact not_inRange_of_apart P.curNW (P.curF.sub_right P.baseNW (by omega) (by omega)) h
  · exact not_inRange_of_apart P.outNW (P.outF.sub_right P.baseNW (by omega) (by omega)) h

end

theorem tailAt_of [Labels] {m₀ m m' : MachineData} (P : Pre m₀) (h : PathCall m₀ m)
    (hrsp : rspOf m' = rspOf m + 8#64) (hpost : MemcpyPost m m') : TailAt m₀ m' := by
  have C := h.common
  obtain ⟨-, hcopy, hsame, hs⟩ := hpost
  have hdx : (reg m .rdx).toNat = 256 := by rw [h.rdx]; rfl
  simp only [h.rdi, h.rsi, hdx] at hcopy hsame
  have hof : ∀ x < 1944, ¬InRange (out m₀) 256 (base m₀ + BitVec.ofNat 64 x) := fun x hx => by
    simpa using out_apart_stack (o := 0) P (by omega) hx (by omega)
  have hoc : ∀ x < 16, ¬InRange (out m₀) 256 (cur m₀ + BitVec.ofNat 64 x) := fun x hx => by
    simpa using out_apart_cur (o := 0) P (by omega) hx (by omega)
  refine ⟨(hs.1 .r14 rfl).trans h.r14, ?_,
    (C.same.trans hsame).mono fun p hp => hp.elim Or.inl fun hp' => Or.inr ?_,
    C.kept.trans hs.2, fun j hj => (C.save j hj).sameOutside hsame fun t ht => ?_,
    h.input.sameOutside hsame fun t ht => ?_,
    h.cursor.sameOutside hsame fun t ht => hoc t (by rw [length_regBytes] at ht; omega),
    h.length.sameOutside hsame fun t ht => ?_,
    h.chain.sameOutside hsame fun t ht => ?_, ?_, (hs.1 .rbx rfl).trans h.rbx⟩
  · show rspOf m' = _
    rw [hrsp]
    change reg m .rsp + _ = _
    rw [C.rsp, addr_add_addr]
  · unfold InRange at hp' ⊢
    omega
  · rw [addr_add_addr]
    exact hof _ (by rw [length_regBytes] at ht; omega)
  · rw [addr_add_addr]
    exact hof _ (by rw [length_regBytes] at ht; omega)
  · rw [addr_add_addr]
    exact hoc _ (by rw [length_regBytes] at ht; omega)
  · rw [addr_add_addr]
    exact hof _ (by rw [length_chainBytes P] at ht; omega)
  · have := h.path.bytesOf
    rw [length_pathBytes P] at this
    rwa [this] at hcopy

theorem saveRegs_cases (r : Reg64) (hr : calleeSaved r = true) :
    ∃ j, j < 6 ∧ saveRegs.getD j .rax = r := by
  cases r <;> simp [calleeSaved] at hr <;> first
    | exact ⟨0, by decide, rfl⟩ | exact ⟨1, by decide, rfl⟩ | exact ⟨2, by decide, rfl⟩
    | exact ⟨3, by decide, rfl⟩ | exact ⟨4, by decide, rfl⟩ | exact ⟨5, by decide, rfl⟩

theorem memBytes_takeLayer (m₀ : MachineData) :
    (NativeRustc.Xmss.takeLayer (LayerReadPre.bytes m₀) 0).1.memBytes =
      pathBytes m₀ ++ chainBytes m₀ ++ rand m₀ := by
  simp only [NativeRustc.Xmss.takeLayer, NativeRustc.Xmss.LayerSignature.memBytes, pathBytes,
    chainBytes, rand, Nat.zero_add]
  rfl

public theorem tail [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Labels.label NativeRustcX64.Common.Memcpy.entryLabel)
    (hret : retOf st.data = Host.addrOf (k + b23Offset)) (h : PathCall m₀ st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧
      rspOf st'.data = rspOf m₀ + 8#64 ∧ LayerReadPost m₀ st'.data) st := by
  have C := h.common
  have hB := P.baseNW
  have hO := P.outNW
  unfold NoWrap at hB hO
  have hrsp0 : rspOf st.data = base m₀ := by
    change reg st.data .rsp = _
    rw [C.rsp]
    simp
  have hpre : MemcpyPre st.data := by
    have hdx : (reg st.data .rdx).toNat = 256 := by rw [h.rdx]; rfl
    refine ⟨⟨by omega, by rw [hrsp0]; omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [h.rdi, h.rsi, hdx, hrsp0]
    · rw [BitVec.sub_zero]
      simpa using (P.stackMapped.sub (i := 0) (k := 8) (by omega)).kept C.kept
    · simpa using (P.outMapped.sub (i := 0) (k := 256) (by omega)).kept C.kept
    · exact (P.stackMapped.sub (by omega)).kept C.kept
    · unfold NoWrap; omega
    · exact P.baseNW.sub (by omega)
    · simpa using (P.outF.sub_left (i := 0) (k := 256) P.outNW (by omega) (by omega)).sub_right
        (i' := 32) (k' := 256) P.baseNW (by omega) (by omega)
    · simpa using (P.outF.sub_left (i := 0) (k := 256) P.outNW (by omega) (by omega)).sub_right
        (i' := 0) (k' := 8) P.baseNW (by omega) (by omega)
  refine NativeRustcX64.Eventually.bind (Spec.apply hmemcpy hpc hpre)
    fun st₁ ⟨hpc₁, hrsp₁, hpost₁⟩ => ?_
  rw [hret] at hpc₁
  have T := tailAt_of P h hrsp₁ hpost₁
  let env₂ := Env.ofMachine st₁.data [(base m₀, 1944), (out m₀, 1200), (sig m₀, 1200)]
    (fun _ => 0) (Host.addrOf (k + b24Offset)).toBitVec
  have hwf₂ : env₂.WF := Env.wf_of
    ⟨⟨P.stackMapped.kept T.kept, P.baseNW⟩, ⟨P.outMapped.kept T.kept, P.outNW⟩,
      ⟨P.sigMapped.kept T.kept, P.sigNW⟩, trivial⟩ (pairwise3 P.outF.symm P.sigF.symm P.outSig)
  have hm₁ : Match env₂ stT0 st₁.data := by
    apply match_ofMachine
    · exact ⟨rfl, rfl, rfl, trivial⟩
    · exact ⟨T.rsp.trans (by simp [Sym.eval]), T.r14.trans (by simp [Sym.eval]), T.rbx, trivial⟩
    · exact trivial
    · exact trivial
    · refine ⟨?_, trivial⟩
      simp only [Sym.eval]
      rw [Env.load_of_bytesAt (length_regBytes _) (by simpa [env₂] using T.input),
        ofBytes_regBytes]
      simp [Env.base]
  obtain ⟨hdi, hsi, hdx, hsp, hwrites, hch, hsv, hpa⟩ := stT1_facts
  refine call_step (b23_in_code.trans hp.1 (List.cons_ne_nil _ _)) b23_execT hwf₂ rfl hpc₁ hm₁
    fun st₂ hpc₂ hm₂ => ?_
  change Match _ stT1 st₂.data at hm₂
  have hr0 : env₂.regions[0]? = some (base m₀, 1944) := rfl
  have hr1 : env₂.regions[1]? = some (out m₀, 1200) := rfl
  have hrdi : reg st₂.data .rdi = out m₀ + 256#64 :=
    (hm₂.regs .rdi _ hdi).trans (by simp [Sym.eval, env₂])
  have hrsi : reg st₂.data .rsi = base m₀ + 960#64 :=
    (hm₂.regs .rsi _ hsi).trans (by simp [Sym.eval, env₂])
  have hrdx : (reg st₂.data .rdx).toNat = 928 := by
    change (st₂.data.regs.get64 .rdx).toNat = 928
    rw [hm₂.regs .rdx _ hdx]
    rfl
  have hrsp₂ : rspOf st₂.data = base m₀ := (hm₂.regs .rsp _ hsp).trans (by simp [Sym.eval, env₂])
  have hk₂ : Kept m₀.dmem st₂.data.dmem := T.kept.trans (hm₂.kept hwf₂)
  have hpre₂ : MemcpyPre st₂.data := by
    refine ⟨⟨by omega, by rw [hrsp₂]; omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hrdi, hrsi, hrdx, hrsp₂]
    · rw [BitVec.sub_zero]
      simpa using (P.stackMapped.sub (i := 0) (k := 8) (by omega)).kept hk₂
    · exact (P.outMapped.sub (by omega)).kept hk₂
    · exact (P.stackMapped.sub (by omega)).kept hk₂
    · exact NoWrap.sub P.outNW (by omega)
    · exact P.baseNW.sub (by omega)
    · exact (P.outF.sub_left P.outNW (by omega) (by omega)).sub_right P.baseNW (by omega) (by omega)
    · simpa using (P.outF.sub_left (i := 256) (k := 928) P.outNW (by omega) (by omega)).sub_right
        (i' := 0) (k' := 8) P.baseNW (by omega) (by omega)
  refine call_then hpc₂ hmemcpy hpre₂ fun st₃ hpc₃ hrsp₃ hpost₃ => ?_
  obtain ⟨-, hcopy, hsame₃, hs₃⟩ := hpost₃
  simp only [hrdi, hrsi, hrdx] at hcopy hsame₃
  have hk₃ : Kept m₀.dmem st₃.data.dmem := hk₂.trans hs₃.2
  let env₄ := Env.ofMachine st₃.data [(base m₀, 1944)]
  have hwf₄ : env₄.WF :=
    Env.wf_of ⟨⟨P.stackMapped.kept hk₃, P.baseNW⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hsp₃ : reg st₃.data .rsp = base m₀ + 8#64 := by
    change rspOf st₃.data = _
    rw [hrsp₃, hrsp₂]
  have hm₃ : Match env₄ stE0 st₃.data := match_ofMachine ⟨rfl, trivial⟩
    ⟨hsp₃.trans (by simp [Sym.eval]), trivial⟩ trivial trivial trivial
  refine exec_at (b24_in_code.trans hp.1 (List.cons_ne_nil _ _)) b24_execE hwf₄
    (fun _ h => nomatch h) hpc₃ hm₃ fun st₄ hm₄ hpc₄ => ?_
  change Match _ stE1 st₄.data at hm₄
  obtain ⟨hmem₄, hsp₄, hld₄⟩ := stE1_facts
  have hd₄ : st₄.data.dmem = st₃.data.dmem := hm₄.dmem_eq hwf₄ hmem₄
  have hsameAll : SameOutside m₀.dmem st₃.data.dmem
      (fun p => Scratch m₀ p ∨ InRange (out m₀) 1200 p) := by
    refine ((T.same.trans (hm₂.sameOutside_below hwf₂ hwrites)).trans hsame₃).mono fun p hp => ?_
    rcases hp with (hp | ⟨rb, hrb, b, sz, hb, hin⟩) | hp
    · exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
      rcases hrb with rfl | rfl
      · cases hb
        exact Or.inl (P.stack_scratch (o := 0) (s := 8) (by omega) (by simpa using hin))
      · cases hb
        exact Or.inr hin
    · exact Or.inr (inRange_sub P.outNW (by omega) hp)
  have hsave₃ : ∀ j < 6, BytesAt st₃.data.dmem (base m₀ + BitVec.ofNat 64 (1888 + 8 * j))
      (regBytes (reg m₀ (saveRegs.getD j .rax))) := fun j hj =>
    (hm₂.bytesAt_keep hr0 (by rw [length_regBytes]; omega)
      (by rw [length_regBytes]; exact hsv j hj) (T.save j hj)).sameOutside hsame₃ fun t ht => by
        rw [addr_add_addr]
        exact out_apart_stack P (by omega) (by rw [length_regBytes] at ht; omega) (by omega)
  have hsaved : Saved m₀ st₄.data := by
    refine ⟨fun r hr => ?_, hk₃.trans fun p hp => by rw [hd₄]; exact hp⟩
    obtain ⟨j, hj, rfl⟩ := saveRegs_cases r hr
    rw [hm₄.regs _ _ (hld₄ j hj)]
    simp only [Sym.eval]
    rw [Env.load_of_bytesAt (length_regBytes _) (by simpa [env₄] using hsave₃ j hj),
      ofBytes_regBytes]
    rfl
  have hcurKeep : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 16 →
      BytesAt st₁.data.dmem (cur m₀ + BitVec.ofNat 64 o) bs →
      BytesAt st₄.data.dmem (cur m₀ + BitVec.ofNat 64 o) bs := by
    intro o bs hlen hb
    rw [hd₄]
    have h₂ := hm₂.bytesAt_outside (fun t ht => by
      rw [addr_add_addr]
      exact Env.outside_of_apart
        ⟨P.curF.symm.sub_right P.curNW (by omega) (by omega),
          P.outCur.sub_right P.curNW (by omega) (by omega),
          P.curSig.symm.sub_right P.curNW (by omega) (by omega), trivial⟩) hb
    exact h₂.sameOutside hsame₃ fun t ht => by
      rw [addr_add_addr]
      exact out_apart_cur P (by omega) (by omega) (by omega)
  refine .done _ ⟨?_, ?_, ?_, ?_, ?_, ?_, hsaved⟩
  · have hread := hm₃.read hwf₄ (r := 0) (o := 1936) (n := 8) rfl (by decide) (by decide)
    have hb : env₄.base 0 + 1936#64 = rspOf m₀ := by rw [P.rsp_eq]; rfl
    rw [hb, loadInt_congr (d := m₀.dmem) fun i hi => ?_] at hread
    · simp only [PcOk] at hpc₄
      rw [hpc₄]
      exact (retOf_of_loadInt hread).symm
    · rw [P.rsp_eq, addr_add_addr]
      exact hsameAll _ (not_scratch_ret P hi)
  · change st₄.data.regs.get64 .rsp = _
    rw [hm₄.regs .rsp _ hsp₄, P.rsp_eq, addr_add_addr]
    simp [Sym.eval, env₄]
  · change BytesAt st₄.data.dmem (out m₀) (NativeRustc.Xmss.takeLayer (LayerReadPre.bytes m₀) 0).1.memBytes
    rw [memBytes_takeLayer, hd₄]
    refine BytesAt.append (BytesAt.append ?_ ?_) ?_
    · have h1 := (hm₂.bytesAt_keep (o := 0) hr1 (by rw [length_pathBytes P]; omega)
        (by rw [length_pathBytes P]; exact hpa)
        (by change BytesAt st₁.data.dmem _ _; simpa using T.path)).sameOutside hsame₃
        fun t ht => by
          rw [length_pathBytes P] at ht
          rw [addr_add_addr, inRange_offsets P.outNW (by omega) (by omega)]
          omega
      exact bytesAt_add_zero h1
    · rw [length_pathBytes P]
      have := (hm₂.bytesAt_keep hr0 (by rw [length_chainBytes P]; omega)
        (by rw [length_chainBytes P]; exact hch) T.chain).bytesOf
      rw [length_chainBytes P] at this
      rwa [this] at hcopy
    · rw [List.length_append, length_pathBytes P, length_chainBytes P]
      intro t ht
      rw [P.rand_length] at ht
      have hnot : ¬InRange (out m₀ + 256#64) 928 (out m₀ + BitVec.ofNat 64 (1184 + t)) := by
        rw [inRange_offsets P.outNW (by omega) (by omega)]
        omega
      have hg := hm₂.get?_load hr1 (by omega) (stT1_rand t ht) (by omega) (le_refl 8)
      change st₃.data.dmem.get? (out m₀ + BitVec.ofNat 64 (256 + 928) + BitVec.ofNat 64 t) = _
      rw [addr_add_addr, show 256 + 928 + t = 1184 + t by omega, hsame₃ _ hnot, hg,
        show 8 * (t / 8) + t % 8 = t by omega]
      simp only [Env.base_ofMachine_eq, env₂, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some, Env.ofMachine_mem0]
      rw [T.same _ (by
        rintro (hs | ho)
        · exact P.sig_not_scratch (by omega) hs
        · exact P.outSig.symm.not_inRange P.sigNW P.outNW (by omega) ho)]
      simp [rand, LayerReadPre.bytes, NativeRustc.slice, bytesOf, sig]
  · have hc := hcurKeep (o := 0) (bs := regBytes (sig m₀ + 1200#64))
      (by rw [length_regBytes]; omega) (by simpa only [BitVec.add_zero] using T.cursor)
    simpa only [BitVec.add_zero, regBytes_eq_wordBytes, cur, sig] using hc
  · have hl := hcurKeep (o := 8) (bs := regBytes (BitVec.ofNat 64 (remaining m₀ - 1200)))
      (by rw [length_regBytes]) T.length
    rw [regBytes_eq_wordBytes] at hl
    exact hl
  · rw [hd₄]
    refine hsameAll.mono fun p hp => ?_
    rcases hp with (hp | hp) | hp
    · exact Or.inr (Or.inr hp)
    · exact Or.inr (Or.inl hp)
    · exact Or.inl hp

end NativeRustcX64.Xmss.LayerRead
