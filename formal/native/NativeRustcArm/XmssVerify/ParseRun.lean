module

public import NativeRustcArm.Code.Xmss.LayerRead.Names

public import NativeRustcArm.XmssVerify.Frame

/-!
# `xmss_verify`: from the copied signature to the parsed layers

`parse`: blocks 3 and 4 and the two calls of `LayerSignature::read`
(`NativeRustcArm.XmssVerify.Parse`), from `LoopAt 75` to `Parsed` at block 5.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash

set_option Elab.async false

section
variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

omit [Labels] in
/-- The signature's bytes after the copy. -/
theorem sig_of (h : LoopAt w m₀ m 75) : BytesAt m.dmem (ad m₀ (fb + 44)) (sigB w) := by
  unfold sigB NativeRustc.Xmss.sigBytes
  rw [u32Bytes_toUInt32, wordsBytes_map]
  refine BytesAt.append h.li ?_
  rw [List.length_take, NativeRustc.length_wordBytes, ad_add]
  exact bytesAt_flatten 300 (fun _ _ => NativeRustc.length_wordBytes _) fun k hk => by
    rw [ad_add, show fb + 44 + min 4 8 + 8 * k = fb + 48 + 8 * k by simp]
    exact h.sig k (by omega)

omit [Labels] in
/-- The message's bytes after the copy. -/
theorem msg_of (h : LoopAt w m₀ m 75) : BytesAt m.dmem (ad m₀ (fb + 8)) (msgB w) := by
  unfold msgB NativeRustc.Xmss.messageBytes
  rw [wordsBytes_map]
  exact bytesAt_flatten 4 (fun _ _ => NativeRustc.length_wordBytes _) fun k hk => by
    rw [ad_add]
    exact h.msg k hk

/-- A reader call may change its output, slice descriptor, and frame. -/
def ReadR (m₀ m : MachineData) (o oc : Nat) (p : BitVec 64) : Prop :=
  InRange (ad m₀ (fb + o)) 1200 p ∨ InRange (ad m₀ (fb + oc)) 16 p ∨
    InRange (stackBelow m layerReadStack) layerReadStack p

theorem readR_lo (P : Pre w m₀) (C : Common m₀ m) {o oc : Nat} (ho : o + 1200 ≤ 5872)
    (hoc : oc + 16 ≤ 5872) : ∀ p, ReadR m₀ m o oc p → InRange (lo m₀) 9200 p := by
  intro p hp
  rcases hp with hp | hp | hp
  · exact P.inRange_lo (by fbo) hp
  · exact P.inRange_lo (by fbo) hp
  · exact inRange_stack P C (by decide) hp

theorem not_readR (P : Pre w m₀) (C : Common m₀ m) {o oc x : Nat} (ho : o + 1200 ≤ 5872)
    (hoc : oc + 16 ≤ 5872) (hx : x < 5872) (h1 : x < o ∨ o + 1200 ≤ x) (h2 : x < oc ∨ oc + 16 ≤ x) :
    ¬ReadR m₀ m o oc (ad m₀ (fb + x)) := by
  intro hp
  rcases hp with hp | hp | hp
  · exact P.not_inRange_ad (by fbo) (by fbo) (by omega) hp
  · exact P.not_inRange_ad (by fbo) (by fbo) (by omega) hp
  · exact not_inRange_stack P C (by decide) (by omega) (by fbo) hp

theorem keep_readR (P : Pre w m₀) (C : Common m₀ m) {o oc : Nat} (ho : o + 1200 ≤ 5872)
    (hoc : oc + 16 ≤ 5872) {d d' : DataMem} (hsame : SameOutside d d' (ReadR m₀ m o oc)) {x : Nat}
    {bs : List UInt8} (h : BytesAt d (ad m₀ (fb + x)) bs) (hx : x + bs.length ≤ 5872)
    (h1 : x + bs.length ≤ o ∨ o + 1200 ≤ x) (h2 : x + bs.length ≤ oc ∨ oc + 16 ≤ x) :
    BytesAt d' (ad m₀ (fb + x)) bs :=
  keep_ad hsame h fun t ht => by
    rw [Nat.add_assoc]
    exact not_readR P C ho hoc (by omega) (by omega) (by omega)

theorem Common.readR (P : Pre w m₀) (C : Common m₀ m) {m' : MachineData} (hs : Saved m m')
    {o oc : Nat} (ho : o + 1200 ≤ 5776) (hoc : oc + 16 ≤ 5776)
    (hsame : SameOutside m.dmem m'.dmem (ReadR m₀ m o oc)) : Common m₀ m' :=
  C.call hs hsame (readR_lo P C (by omega) (by omega)) fun x hx hx' => by
    have := not_readR P C (x := x - fb) (o := o) (oc := oc) (by omega) (by omega) (by fbo)
      (by fbo) (by fbo)
    rwa [show fb + (x - fb) = x by omega] at this

omit [Labels] in
theorem reader_data {oc ob : Nat} (h1 : m.regs.X1.toBitVec = ad m₀ oc)
    (hd : BytesAt m.dmem (ad m₀ oc) (wordBytes (UInt64.ofBitVec (ad m₀ ob)))) :
    LayerReadPre.data m = ad m₀ ob := by
  simp only [LayerReadPre.data, h1, bytesOf_of hd (NativeRustc.length_wordBytes _), leNat_wordBytes]
  simp

omit [Labels] in
theorem reader_remaining {oc n : Nat} (h1 : m.regs.X1.toBitVec = ad m₀ oc)
    (hl : BytesAt m.dmem (ad m₀ (oc + 8)) (wordBytes n.toUInt64)) (hn : n < 2 ^ 64) :
    LayerReadPre.remaining m = n := by
  unfold LayerReadPre.remaining
  rw [h1]
  change (BitVec.ofNat 64 (NativeRustc.leNat (bytesOf m.dmem (ad m₀ oc + BitVec.ofNat 64 8) 8))).toNat = n
  rw [ad_add, bytesOf_of hl (NativeRustc.length_wordBytes _), leNat_wordBytes]
  simp
  exact hn

/-- The slice reader's precondition for buffers in the verifier's frame. -/
theorem layerReadPre (P : Pre w m₀) (C : Common m₀ m) {o oc ob n : Nat}
    (h0 : m.regs.X0.toBitVec = ad m₀ o) (h1 : m.regs.X1.toBitVec = ad m₀ oc)
    (hd : BytesAt m.dmem (ad m₀ oc) (wordBytes (UInt64.ofBitVec (ad m₀ ob))))
    (hl : BytesAt m.dmem (ad m₀ (oc + 8)) (wordBytes n.toUInt64))
    (ho : fb ≤ o) (hoc : fb ≤ oc) (hob : fb ≤ ob)
    (h : o + 1200 ≤ 9200) (hc : oc + 16 ≤ 9200) (hb : ob + 1200 ≤ 9200)
    (hd1 : o + 1200 ≤ oc ∨ oc + 16 ≤ o) (hd2 : o + 1200 ≤ ob ∨ ob + 1200 ≤ o)
    (hd3 : oc + 16 ≤ ob ∨ ob + 1200 ≤ oc) (hn : 1200 ≤ n) (hn' : n < 2 ^ 64) :
    LayerReadPre m := by
  have hs : layerReadStack ≤ fb := by decide
  refine ⟨C.stackOk P hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [LayerReadPre.Buf, h0, h1, reader_data h1 hd, reader_remaining h1 hl hn']
  · exact hn
  · exact ⟨C.mapped P h, P.ad_nw h, apart_stack P C hs (by decide) ho h (by omega)⟩
  · exact ⟨C.mapped P hc, P.ad_nw hc, apart_stack P C hs (by decide) hoc hc (by omega)⟩
  · exact ⟨C.mapped P hb, P.ad_nw hb, apart_stack P C hs (by decide) hob hb (by omega)⟩
  · exact P.apart_ad hd1 h hc (by omega) (by omega)
  · exact P.apart_ad hd2 h hb (by omega) (by omega)
  · exact P.apart_ad hd3 hc hb (by omega) (by omega)

omit [Labels] in
theorem bytesOf_slice_of {d : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d a bs) {c n : Nat} (hc : c + n ≤ bs.length) :
    bytesOf d (a + BitVec.ofNat 64 c) n = NativeRustc.slice bs c n := by
  apply List.ext_getElem
  · simp [bytesOf, NativeRustc.slice]
    omega
  · intro i hi hj
    have hi' : i < n := by simpa [length_bytesOf] using hi
    simp only [bytesOf, NativeRustc.slice, List.getElem_map, List.getElem_range,
      List.getElem_take, List.getElem_drop, addr_add_addr]
    rw [h (c + i) (by omega)]
    rfl

omit [Labels] in
theorem takeLayer_slice (bs : List UInt8) (c : Nat) :
    (NativeRustc.Xmss.takeLayer (NativeRustc.slice bs c 1200) 0).1 =
      (NativeRustc.Xmss.takeLayer bs c).1 := by
  have hs : ∀ x, x + 16 ≤ 1200 →
      NativeRustc.slice (NativeRustc.slice bs c 1200) x 16 = NativeRustc.slice bs (c + x) 16 := by
    intro x hx
    simp [NativeRustc.slice, List.drop_take, List.drop_drop, List.take_take,
      Nat.min_eq_left (show 16 ≤ 1200 - x by omega)]
  simp only [NativeRustc.Xmss.takeLayer]
  congr 1
  · simpa using hs 0 (by omega)
  · apply List.map_congr_left
    intro j hj
    have := List.mem_range.mp hj
    simpa [Nat.add_assoc] using hs (16 + 16 * j) (by omega)
  · apply List.map_congr_left
    intro j hj
    have := List.mem_range.mp hj
    simpa [Nat.add_assoc] using hs (944 + 16 * j) (by omega)

end

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **Parsing**: from the end of the copy to block 5. -/
public theorem parse {k : Nat} (hp : Placed code k)
    (hfb : Spec (label NativeRustcArm.Xmss.LayerRead.entryLabel) LayerReadPre LayerReadPost) (P : Pre w m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b3Offset)) (h : LoopAt w m₀ st.data 75)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b5Offset) → Parsed w m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hsig := sig_of h
  have hmsg := msg_of h
  -- Block 3.
  have hwf := frame_wf P C
  have hm0 := match_stF0 P C (known := []) trivial
  obtain ⟨h0, h1, h19, h20, h24, h23, h29, hsp, hw, hsave, hov1, hov2⟩ := st3_facts
  refine call_step (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) b3_exec hwf hpc hm0
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ st3 st₁.data at hm₁
  have C₁ := Common.block P C hwf hm0 hm₁ hsp rfl h29 hw hsave
  have hx : ∀ {r : XReg} {o : Nat}, st3.reg r = some (.ptr 0 o) →
      (st₁.data.regs.getXReg r).toBitVec = ad m₀ (fb + o) := fun hr =>
    (hm₁.regs _ _ hr).trans (eval_ptr0 _)
  have hk : ∀ {r : XReg}, st3.reg r = some (.reg r) → st₁.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun hr => UInt64.toBitVec_inj.mp (hm₁.regs _ _ hr)
  have hdata₁ : BytesAt st₁.data.dmem (ad m₀ (fb + 5408))
      (wordBytes (UInt64.ofBitVec (ad m₀ (fb + 48)))) := by
    have := frameWrite hm₁ (o := 5408) (by omega) st3_cursorData
    simpa only [Sym.eval, Env.ofMachine_regs, h.x19, regBytes_eq_wordBytes] using this
  have hlen₁ : BytesAt st₁.data.dmem (ad m₀ (fb + 5416)) (wordBytes (2400 : Nat).toUInt64) := by
    have := frameWrite hm₁ (o := 5416) (by omega) st3_cursorLength
    rwa [regBytes_eq_wordBytes] at this
  have hpk₁ : BytesAt st₁.data.dmem (ad m₀ (fb + 2448)) (pkB w) := by
    unfold pkB NativeRustc.Xmss.pkBytes
    rw [wordsBytes_map]
    refine bytesAt_flatten 4 (fun _ _ => NativeRustc.length_wordBytes _) fun j hj => ?_
    have := frameWrite hm₁ (o := 2448 + 8 * j) (by omega) (st3_pk j hj)
    rw [ad_add, show fb + 2448 + 8 * j = fb + (2448 + 8 * j) by omega,
      show wordBytes (w j) = regBytes (w j).toBitVec from (regBytes_eq_wordBytes _).symm]
    convert this using 2
    simp only [Sym.eval, Env.ofMachine_regs]
    interval_cases j
    · exact congrArg UInt64.toBitVec h.x8.symm
    · exact congrArg UInt64.toBitVec h.x9.symm
    · exact congrArg UInt64.toBitVec h.x10.symm
    · exact congrArg UInt64.toBitVec h.x11.symm
  have hmsg₁ := frameKeep hm₁ (by rw [length_msgB]; omega) (by rw [length_msgB]; exact hov1) hmsg
  have hsig₁ := frameKeep hm₁ (by rw [length_sigB]; omega) (by rw [length_sigB]; exact hov2) hsig
  -- Read the bottom layer from the initial slice.
  have e0 : st₁.data.regs.X0.toBitVec = ad m₀ (fb + 2492) := hx h0
  have e1 : st₁.data.regs.X1.toBitVec = ad m₀ (fb + 5408) := hx h1
  have hd1 := reader_data e1 hdata₁
  have hl1 := reader_remaining e1 hlen₁ (by decide)
  have hpre₁ : LayerReadPre st₁.data :=
    layerReadPre P C₁ e0 e1 hdata₁ hlen₁ (by fbo) (by fbo) (by fbo)
      (by fbo) (by fbo) (by fbo) (by omega) (by omega) (by omega) (by decide) (by decide)
  refine call_then hpc₁ hfb hpre₁ fun st₂ hpc₂ hpost₂ => ?_
  obtain ⟨hout₂, hdata₂, hlen₂, hsame₂, hs₂⟩ := hpost₂
  simp only [LayerReadPre.bytes, e0, hd1] at hout₂
  have hb1 := bytesOf_slice_of hsig₁ (c := 4) (n := 1200) (by rw [length_sigB]; decide)
  simp only [ad_add] at hb1
  rw [hb1, takeLayer_slice] at hout₂
  simp only [e1, hd1, hl1] at hdata₂ hlen₂
  have ha : ad m₀ (fb + 48) + (1200 : BitVec 64) = ad m₀ (fb + 1248) := by
    change ad m₀ (fb + 48) + BitVec.ofNat 64 1200 = _
    rw [ad_add]
  rw [ha] at hdata₂
  change BytesAt st₂.data.dmem (ad m₀ (fb + 5408) + BitVec.ofNat 64 8)
    (wordBytes (1200 : Nat).toUInt64) at hlen₂
  rw [ad_add] at hlen₂
  rw [e0, e1] at hsame₂
  change SameOutside _ _ (ReadR m₀ st₁.data 2492 5408) at hsame₂
  have C₂ := C₁.readR P hs₂ (by decide) (by decide) hsame₂
  have hpk₂ := keep_readR P C₁ (by decide) (by decide) hsame₂ hpk₁ (by rw [length_pkB]; decide)
    (by rw [length_pkB]; decide) (by rw [length_pkB]; decide)
  have hmsg₂ := keep_readR P C₁ (by decide) (by decide) hsame₂ hmsg₁ (by rw [length_msgB]; decide)
    (by rw [length_msgB]; decide) (by rw [length_msgB]; decide)
  have hsig₂ := keep_readR P C₁ (by decide) (by decide) hsame₂ hsig₁ (by rw [length_sigB]; decide)
    (by rw [length_sigB]; decide) (by rw [length_sigB]; decide)
  -- Block 4.
  have hwf₃ := frame_wf P C₂
  have hm₃ := match_stF0 P C₂ (known := [(.X19, .ptr 0 2492)])
    ⟨(congrArg UInt64.toBitVec (hs₂.1 .X19 rfl)).trans ((hx h19).trans (eval_ptr0 _).symm), trivial⟩
  obtain ⟨g0, g1, gmem, gsp, g19, gk, gw, gsave⟩ := st4_facts
  refine call_step (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) b4_exec hwf₃ (hpc₂.trans rfl)
    hm₃ fun st₃ hpc₃ hm₃' => ?_
  change Match _ st4 st₃.data at hm₃'
  have C₃ := Common.block P C₂ hwf₃ hm₃ hm₃' gsp rfl (gk .X29 (by simp)) gw gsave
  have hd₃ : st₃.data.dmem = st₂.data.dmem := hm₃'.dmem_eq hwf₃ gmem
  have f0 : st₃.data.regs.X0.toBitVec = ad m₀ (fb + 3692) := (hm₃'.regs _ _ g0).trans (eval_ptr0 _)
  have f1 : st₃.data.regs.X1.toBitVec = ad m₀ (fb + 5408) := (hm₃'.regs _ _ g1).trans (eval_ptr0 _)
  have hdata₃ : BytesAt st₃.data.dmem (ad m₀ (fb + 5408))
      (wordBytes (UInt64.ofBitVec (ad m₀ (fb + 1248)))) := by
    rw [hd₃]
    exact hdata₂
  have hlen₃ : BytesAt st₃.data.dmem (ad m₀ (fb + 5416)) (wordBytes (1200 : Nat).toUInt64) := by
    rw [hd₃]
    exact hlen₂
  have hd3 := reader_data f1 hdata₃
  have hpre₃ : LayerReadPre st₃.data :=
    layerReadPre P C₃ f0 f1 hdata₃ hlen₃ (by fbo) (by fbo) (by fbo)
      (by fbo) (by fbo) (by fbo) (by omega) (by omega) (by omega) (by decide) (by decide)
  refine call_then hpc₃ hfb hpre₃ fun st₄ hpc₄ hpost₄ => cont st₄ (hpc₄.trans rfl) ?_
  obtain ⟨hout₄, -, -, hsame₄, hs₄⟩ := hpost₄
  simp only [LayerReadPre.bytes, f0, hd3, hd₃] at hout₄
  have hb3 := bytesOf_slice_of hsig₂ (c := 1204) (n := 1200) (by rw [length_sigB])
  simp only [ad_add] at hb3
  rw [hb3, takeLayer_slice] at hout₄
  rw [f0, f1] at hsame₄
  change SameOutside _ _ (ReadR m₀ st₃.data 3692 5408) at hsame₄
  have C₄ := C₃.readR P hs₄ (by decide) (by decide) hsame₄
  have hkeep : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 3692 →
      BytesAt st₂.data.dmem (ad m₀ (fb + o)) bs → BytesAt st₄.data.dmem (ad m₀ (fb + o)) bs :=
    fun h2 hb => keep_readR P C₃ (by decide) (by decide) hsame₄ (hd₃ ▸ hb) (by omega)
      (Or.inl h2) (Or.inl (by omega))
  have hreg : ∀ r ∈ [XReg.X23, .X24], st₄.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have h3 : st₃.data.regs.getXReg .X23 = st₂.data.regs.getXReg .X23 :=
        UInt64.toBitVec_inj.mp (hm₃'.regs _ _ (gk .X23 (by simp)))
      rw [hs₄.1 _ rfl, h3, hs₂.1 _ rfl]
      exact hk h23
    · have h3 : st₃.data.regs.getXReg .X24 = st₂.data.regs.getXReg .X24 :=
        UInt64.toBitVec_inj.mp (hm₃'.regs _ _ (gk .X24 (by simp)))
      rw [hs₄.1 _ rfl, h3, hs₂.1 _ rfl]
      exact hk h24
  refine ⟨C₄, ?_, ?_, ?_, ?_, hkeep (by rw [length_msgB]; decide) hmsg₂,
    hkeep (by rw [length_pkB]; decide) hpk₂,
    hkeep (by rw [bottomL, length_memBytes (by rw [length_sigB]; decide)]) hout₂, ?_, ?_, ?_⟩
  · rw [hs₄.1 _ rfl]
    exact (hm₃'.regs _ _ g19).trans (eval_ptr0 _)
  · rw [hs₄.1 _ rfl]
    have h3 : st₃.data.regs.getXReg .X20 = st₂.data.regs.getXReg .X20 :=
      UInt64.toBitVec_inj.mp (hm₃'.regs _ _ (gk .X20 (by simp)))
    rw [h3, hs₂.1 _ rfl]
    exact hx h20
  · rw [hreg .X24 (by simp)]; exact h.x24
  · rw [toNat_X, hreg .X23 (by simp)]; exact h.x23
  · rw [show fb + 3692 = fb + 3692 from rfl]
    exact hout₄
  · rw [hs₄.1 _ rfl]
    have h3 : st₃.data.regs.getXReg .X21 = st₂.data.regs.getXReg .X21 :=
      UInt64.toBitVec_inj.mp (hm₃'.regs _ _ (gk .X21 (by simp)))
    rw [h3, hs₂.1 _ rfl, hk st3_x21]
    exact h.x21
  · rw [hs₄.1 _ rfl]
    exact (hm₃'.regs _ _ st4_x22).trans (eval_ptr0 _)

end NativeRustcArm.Xmss.XmssVerify
