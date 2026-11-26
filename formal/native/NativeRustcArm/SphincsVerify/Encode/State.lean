module

public import NativeRustcArm.SphincsVerify.Encode.Layout

/-!
# The encoding's invariant

From `b92`'s end to `b102`'s start the encoding keeps (`Run.EncBase l s c`): the frame, the
inputs, the layer's spills, X19, X21, X22, X24, X25, X27, the message `s` at `20032`, and the
counter `c` in W20. A call that changes only bytes of hasher A (`8640 .. 8984`) or hasher B
(`19008 .. 19352`) keeps it (`Run.EncBase.of_call`), and so does a block that writes none of its
bytes and keeps the registers (`Run.EncBase.of_block`, its checks `encKeeps` decided on the
block's literal result).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs LeanVM.Protocol.KeccakHash

@[expose] public section

/-- No write of `S` in the bytes `o' .. o' + n'` inside `o .. o + n` it writes none of. -/
theorem noWriteIn_mono {S : Sym.SState} {o n o' n' : Nat} (h : Run.noWriteIn S o n = true)
    (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) : Run.noWriteIn S o' n' = true := by
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h ⊢
  intro w hw
  rcases h w hw with (h | h) | h
  · exact .inl (.inl h)
  · exact .inl (.inr (by omega))
  · exact .inr (by omega)

/-- The registers a block keeps and the invariant's bytes it does not write. -/
def encKeeps (S : Sym.SState) : Bool :=
  S.sp == .ptr 0 0 && S.reg .X29 == some (.ptr 0 21520) && Run.frameWrites S &&
    S.reg .X19 == some (.reg .X19) && S.reg .X20 == some (.reg .X20) &&
    S.reg .X21 == some (.reg .X21) && S.reg .X22 == some (.reg .X22) &&
    S.reg .X24 == some (.reg .X24) && S.reg .X25 == some (.reg .X25) &&
    S.reg .X27 == some (.reg .X27) &&
    Run.noWriteIn S 8 48 && Run.noWriteIn S 392 56 && Run.noWriteIn S 448 7776 &&
    Run.noWriteIn S 20032 16

namespace Run

variable (r : Run) [Labels]

/-- **The encoding's invariant** for layer `l`, message `s`, counter `c`. -/
def EncBase (l : Nat) (s : List UInt8) (c : UInt32) (m : MachineData) : Prop :=
  l < 3 ∧ s.length = 16 ∧ r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧
    RegIs m .X22 (r.off 15936) ∧ RegIs m .X21 (r.off 19208) ∧ RegIs m .X24 (r.off 19009) ∧
    RegIs m .X25 (r.off 8840) ∧ RegIs m .X19 136 ∧ RegIs m .X27 (r.off 19008) ∧
    BytesAt m.dmem (r.off 20032) s ∧
    UInt32.ofNat (m.regs.getXReg .X20).toBitVec.toNat = c

omit [Labels] in
theorem length_sigMem' : (sigMem r.sig).length = 7740 := r.length_sigMem

omit [Labels] in
theorem length_be64 (x : UInt64) : (be64 x).length = 8 := rfl
omit [Labels] in
theorem length_be32 (x : UInt32) : (be32 x).length = 4 := rfl
omit [Labels] in
theorem length_wordBytes' (x : UInt64) : (wordBytes x).length = 8 := length_wordBytes x

omit [Labels] in
/-- Bytes kept: each fact of the invariant's bytes, from bytes kept at each place. -/
theorem encBase_of_bytes {l : Nat} {s : List UInt8} {c : UInt32} {m m' : MachineData}
    (h : r.EncBase l s c m) (hF : r.Frame m')
    (hk : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 21616 →
      ((8 ≤ o ∧ o + bs.length ≤ 56) ∨ (392 ≤ o ∧ o + bs.length ≤ 448) ∨
        (448 ≤ o ∧ o + bs.length ≤ 8224) ∨ (20032 ≤ o ∧ o + bs.length ≤ 20048)) →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs)
    (hreg : ∀ x : XReg, x = .X19 ∨ x = .X20 ∨ x = .X21 ∨ x = .X22 ∨ x = .X24 ∨ x = .X25 ∨ x = .X27 →
      m'.regs.getXReg x = m.regs.getXReg x) : r.EncBase l s c m' := by
  obtain ⟨hl, hs, -, ⟨hpk, hsig, h392⟩, ⟨s8, s16, s24, s32, s40, s48, s400, s408, s424, s432, s440⟩,
    h22, h21, h24, h25, h19, h27, hsm, h20⟩ := h
  have w : ∀ o, (8 ≤ o ∧ o + 8 ≤ 56) ∨ (392 ≤ o ∧ o + 8 ≤ 448) → ∀ v : UInt64,
      r.WordAt m o v → r.WordAt m' o v := fun o ho v hv ↦
    hk (by rw [length_wordBytes']; omega) (by rw [length_wordBytes']; omega) hv
  refine ⟨hl, hs, hF, ⟨hk (by rw [r.hpk]; omega) (by rw [r.hpk]; omega) hpk,
    hk (by rw [length_sigMem']; omega) (by rw [length_sigMem']; omega) hsig,
    w 392 (by omega) _ h392⟩,
    ⟨w 8 (by omega) _ s8, w 16 (by omega) _ s16, w 24 (by omega) _ s24, w 32 (by omega) _ s32,
    w 40 (by omega) _ s40, w 48 (by omega) _ s48, w 400 (by omega) _ s400, w 408 (by omega) _ s408,
    hk (by rw [length_be32]; omega) (by rw [length_be32]; omega) s424,
    hk (by rw [length_be32]; omega) (by rw [length_be32]; omega) s432,
    hk (by rw [length_be64]; omega) (by rw [length_be64]; omega) s440⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    hk (by rw [hs]; omega) (by rw [hs]; omega) hsm, ?_⟩
  · rw [RegIs, hreg .X22 (by simp)]; exact h22
  · rw [RegIs, hreg .X21 (by simp)]; exact h21
  · rw [RegIs, hreg .X24 (by simp)]; exact h24
  · rw [RegIs, hreg .X25 (by simp)]; exact h25
  · rw [RegIs, hreg .X19 (by simp)]; exact h19
  · rw [RegIs, hreg .X27 (by simp)]; exact h27
  · rw [hreg .X20 (by simp)]; exact h20

/-- **A call keeps the invariant** when it changes only bytes of hasher A or hasher B. -/
theorem EncBase.of_call (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32}
    {m m' : MachineData} (h : r.EncBase l s c m) (hS : Saved m m') {a n N : Nat}
    (ha : (8640 ≤ a ∧ a + n ≤ 8984) ∨ (19008 ≤ a ∧ a + n ≤ 19352)) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : r.EncBase l s c m' :=
  r.encBase_of_bytes h (r.frame_of_call hpre h.2.2.1 hS (by omega) hN hout)
    (fun ho hr hb ↦ r.bytesAt_of_call hpre h.2.2.1 (by omega) hN hout ho (by omega) hb)
    fun x hx ↦ hS.1 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

/-- **A block keeps the invariant** when it keeps the registers and writes none of its bytes. -/
theorem EncBase.of_block (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32}
    {m m' : MachineData} (h : r.EncBase l s c m) {vars : Nat → BitVec 64} {S : Sym.SState}
    (hm : Sym.Match (r.env m vars) S m') (hwf : (r.env m vars).WF) (hS : encKeeps S = true) :
    r.EncBase l s c m' := by
  simp only [encKeeps, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp, h29⟩, hfw⟩, h19⟩, h20⟩, h21⟩, h22⟩, h24⟩, h25⟩, h27⟩, k8⟩, k392⟩, k448⟩,
    k20032⟩ := hS
  refine r.encBase_of_bytes h (Run.Frame.of_match r hpre h.2.2.1 hm hwf hsp h29 hfw)
    (fun ho hr hb ↦ r.bytesAt_kept hpre hm hwf ho hb ?_) fun x hx ↦ ?_
  · rcases hr with hr | hr | hr | hr
    · exact noWriteIn_mono k8 hr.1 (by omega)
    · exact noWriteIn_mono k392 hr.1 (by omega)
    · exact noWriteIn_mono k448 hr.1 (by omega)
    · exact noWriteIn_mono k20032 hr.1 (by omega)
  · apply UInt64.toBitVec_inj.mp
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm.regs .X19 _ h19
    · exact hm.regs .X20 _ h20
    · exact hm.regs .X21 _ h21
    · exact hm.regs .X22 _ h22
    · exact hm.regs .X24 _ h24
    · exact hm.regs .X25 _ h25
    · exact hm.regs .X27 _ h27

end Run

end

end NativeRustcArm.SphincsVerifyProof
