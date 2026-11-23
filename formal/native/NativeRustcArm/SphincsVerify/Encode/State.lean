module

public import NativeRustcArm.SphincsVerify.Encode.Layout

/-!
# The encoding's invariant

From `b101`'s end to `b111`'s start the encoding keeps (`Run.EncBase l s c`): the frame, the
inputs, the layer's spills, X20, X21, X23, X25, X26, the message `s` at `27792`, and the counter `c`
in W19. A call that changes only bytes of hasher A (`16400 .. 16744`) or hasher B
(`26768 .. 27112`) keeps it (`Run.EncBase.of_call`), and so does a block that writes none of its
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
  S.sp == .ptr 0 0 && S.reg .X29 == some (.ptr 0 29280) && Run.frameWrites S &&
    S.reg .X19 == some (.reg .X19) && S.reg .X20 == some (.reg .X20) &&
    S.reg .X21 == some (.reg .X21) && S.reg .X23 == some (.reg .X23) &&
    S.reg .X25 == some (.reg .X25) && S.reg .X26 == some (.reg .X26) &&
    Run.noWriteIn S 0 48 && Run.noWriteIn S 376 56 && Run.noWriteIn S 8208 7776 &&
    Run.noWriteIn S 27792 16

namespace Run

variable (r : Run) [Labels]

/-- **The encoding's invariant** for layer `l`, message `s`, counter `c`. -/
def EncBase (l : Nat) (s : List UInt8) (c : UInt32) (m : MachineData) : Prop :=
  l < 3 ∧ s.length = 16 ∧ r.Frame m ∧ r.Inputs m ∧ r.LayerSpills l m ∧
    RegIs m .X20 (r.off 21648) ∧ RegIs m .X21 (r.off 26968) ∧ RegIs m .X23 (r.off 26769) ∧
    RegIs m .X25 (r.off 16600) ∧ RegIs m .X26 136 ∧ BytesAt m.dmem (r.off 27792) s ∧
    UInt32.ofNat (m.regs.getXReg .X19).toBitVec.toNat = c

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
    (hk : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 29376 →
      (o + bs.length ≤ 48 ∨ (376 ≤ o ∧ o + bs.length ≤ 432) ∨ (8208 ≤ o ∧ o + bs.length ≤ 15984) ∨
        (27792 ≤ o ∧ o + bs.length ≤ 27808)) →
      BytesAt m.dmem (r.off o) bs → BytesAt m'.dmem (r.off o) bs)
    (hreg : ∀ x : XReg, x = .X19 ∨ x = .X20 ∨ x = .X21 ∨ x = .X23 ∨ x = .X25 ∨ x = .X26 →
      m'.regs.getXReg x = m.regs.getXReg x) : r.EncBase l s c m' := by
  obtain ⟨hl, hs, -, ⟨hpk, hsig, h376⟩, ⟨s0, s8, s16, s24, s32, s40, s384, s392, s408, s416, s424⟩,
    h20, h21, h23, h25, h26, hsm, h19⟩ := h
  have w : ∀ o, o + 8 ≤ 48 ∨ (376 ≤ o ∧ o + 8 ≤ 432) → ∀ v : UInt64,
      r.WordAt m o v → r.WordAt m' o v := fun o ho v hv ↦
    hk (by rw [length_wordBytes']; omega) (by rw [length_wordBytes']; omega) hv
  refine ⟨hl, hs, hF, ⟨hk (by rw [length_pkBytes]; omega) (by rw [length_pkBytes]; omega) hpk,
    hk (by rw [length_sigMem']; omega) (by rw [length_sigMem']; omega) hsig,
    w 376 (by omega) _ h376⟩,
    ⟨w 0 (by omega) _ s0, w 8 (by omega) _ s8, w 16 (by omega) _ s16, w 24 (by omega) _ s24,
    w 32 (by omega) _ s32, w 40 (by omega) _ s40, w 384 (by omega) _ s384, w 392 (by omega) _ s392,
    hk (by rw [length_be32]; omega) (by rw [length_be32]; omega) s408,
    hk (by rw [length_be32]; omega) (by rw [length_be32]; omega) s416,
    hk (by rw [length_be64]; omega) (by rw [length_be64]; omega) s424⟩, ?_, ?_, ?_, ?_, ?_,
    hk (by rw [hs]; omega) (by rw [hs]; omega) hsm, ?_⟩
  · rw [RegIs, hreg .X20 (by simp)]; exact h20
  · rw [RegIs, hreg .X21 (by simp)]; exact h21
  · rw [RegIs, hreg .X23 (by simp)]; exact h23
  · rw [RegIs, hreg .X25 (by simp)]; exact h25
  · rw [RegIs, hreg .X26 (by simp)]; exact h26
  · rw [hreg .X19 (by simp)]; exact h19

/-- **A call keeps the invariant** when it changes only bytes of hasher A or hasher B. -/
theorem EncBase.of_call (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32}
    {m m' : MachineData} (h : r.EncBase l s c m) (hS : Saved m m') {a n N : Nat}
    (ha : (16400 ≤ a ∧ a + n ≤ 16744) ∨ (26768 ≤ a ∧ a + n ≤ 27112)) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) : r.EncBase l s c m' :=
  r.encBase_of_bytes h (r.frame_of_call hpre h.2.2.1 hS (by omega) hN hout)
    (fun ho hr hb ↦ r.bytesAt_of_call hpre h.2.2.1 (by omega) hN hout ho (by omega) hb)
    fun x hx ↦ hS.1 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

/-- **A block keeps the invariant** when it keeps the registers and writes none of its bytes. -/
theorem EncBase.of_block (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32}
    {m m' : MachineData} (h : r.EncBase l s c m) {vars : Nat → BitVec 64} {S : Sym.SState}
    (hm : Sym.Match (r.env m vars) S m') (hwf : (r.env m vars).WF) (hS : encKeeps S = true) :
    r.EncBase l s c m' := by
  simp only [encKeeps, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp, h29⟩, hfw⟩, h19⟩, h20⟩, h21⟩, h23⟩, h25⟩, h26⟩, k0⟩, k376⟩, k8208⟩,
    k27792⟩ := hS
  refine r.encBase_of_bytes h (Run.Frame.of_match r hpre h.2.2.1 hm hwf hsp h29 hfw)
    (fun ho hr hb ↦ r.bytesAt_kept hpre hm hwf ho hb ?_) fun x hx ↦ ?_
  · rcases hr with hr | hr | hr | hr
    · exact noWriteIn_mono k0 (by omega) (by omega)
    · exact noWriteIn_mono k376 hr.1 (by omega)
    · exact noWriteIn_mono k8208 hr.1 (by omega)
    · exact noWriteIn_mono k27792 hr.1 (by omega)
  · apply UInt64.toBitVec_inj.mp
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm.regs .X19 _ h19
    · exact hm.regs .X20 _ h20
    · exact hm.regs .X21 _ h21
    · exact hm.regs .X23 _ h23
    · exact hm.regs .X25 _ h25
    · exact hm.regs .X26 _ h26

end Run

end

end NativeRustcArm.SphincsVerifyProof
