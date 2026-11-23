module

public import NativeRustcArm.XmssVerify.Inv
public import NativeRustcArm.Spec.LayerRead

/-!
# `xmss_verify`: its callees' preconditions and what their postconditions keep

From `Common` and arguments that are ranges of the frame (`ad m₀ o`, `o ≥ fb`): the callees'
preconditions (`memsetPre`, `memcpyPre`, `updatePre`, `finalizePre`, `wotsLeafPre`,
`layerReadPre`); and `Common.call`: a call that keeps the callee-saved registers and SP and changes
only bytes of the stack other than the save area keeps `Common`. `Common.keep`: bytes of the stack
outside what a call changes are kept.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

public section

variable [Labels] {w : Nat → UInt64} {m₀ m m' : MachineData}

theorem Common.mapped (P : Pre w m₀) (C : Common m₀ m) {o s : Nat} (h : o + s ≤ 9200) :
    Mapped m.dmem (ad m₀ o) s :=
  (P.mapped.sub h).kept C.kept

theorem Common.stackOk (P : Pre w m₀) (C : Common m₀ m) {n : Nat} (hn : n ≤ fb) :
    StackOk m n := by
  have h16 := P.sp16
  have hle := P.spLe
  have hlo := P.loNat
  have hsp := C.sp
  have hat : (ad m₀ fb).toNat = (lo m₀).toNat + fb := P.ad_toNat (by rw [fb_eq]; omega)
  refine ⟨?_, ?_, ?_⟩
  · show m.regs.SP.toBitVec.toNat % 16 = 0
    rw [hsp, hat, hlo, fb_eq]
    have : m₀.regs.SP.toBitVec.toNat = m₀.regs.SP.toNat := rfl
    omega
  · show n ≤ m.regs.SP.toBitVec.toNat
    rw [hsp, hat]
    rw [fb_eq] at hn ⊢
    omega
  · have := C.stackBelow hn
    unfold NativeRustcArm.stackBelow at this
    rw [this]
    exact C.mapped P (by rw [fb_eq] at hn ⊢; omega)

omit [Labels] in
theorem rcBytes_length : rcBytes.length = 192 := by
  simp [rcBytes, List.length_flatMap, NativeRustc.length_wordBytes]
  rfl

theorem Common.rcAt (P : Pre w m₀) (C : Common m₀ m) {n : Nat} (hn : n ≤ fb) (hn0 : 0 < n) :
    RcAt m n := by
  refine ⟨fun i hi => ?_, P.rcNW, ?_⟩
  · rw [C.same _ (P.rc_not_lo (by rw [rcBytes_length] at hi; exact hi))]
    exact P.rc i hi
  · rw [C.stackBelow hn]
    exact P.rc_apart (by rw [fb_eq] at hn ⊢; omega) hn0

/-- A range of the frame is apart from a callee's stack. -/
theorem apart_stack (P : Pre w m₀) (C : Common m₀ m) {o s n : Nat} (hn : n ≤ fb) (hn0 : 0 < n)
    (ho : fb ≤ o) (hs : o + s ≤ 9200) (hs0 : 0 < s) :
    Apart (ad m₀ o) s (stackBelow m n) n := by
  rw [C.stackBelow hn]
  exact P.apart_ad (by omega) hs (by rw [fb_eq] at hn ⊢; omega) hs0 hn0

/-- A callee's stack is in the stack. -/
theorem inRange_stack (P : Pre w m₀) (C : Common m₀ m) {n : Nat} (hn : n ≤ fb) {p : BitVec 64}
    (h : InRange (stackBelow m n) n p) : InRange (lo m₀) 9200 p := by
  rw [C.stackBelow hn] at h
  exact P.inRange_lo (by rw [fb_eq] at hn ⊢; omega) h

/-- A byte of the frame is outside a callee's stack. -/
theorem not_inRange_stack (P : Pre w m₀) (C : Common m₀ m) {n x : Nat} (hn : n ≤ fb)
    (hx : fb ≤ x) (hx' : x < 9200) : ¬InRange (stackBelow m n) n (ad m₀ x) := by
  rw [C.stackBelow hn]
  exact P.not_inRange_ad (by rw [fb_eq] at hn ⊢; omega) hx' (by omega)

/-! ## Preconditions -/

theorem memsetPre (P : Pre w m₀) (C : Common m₀ m) {o n : Nat} (h0 : m.regs.X0.toBitVec = ad m₀ o)
    (h2 : m.regs.X2.toNat = n) (h : o + n ≤ 9200) : MemsetPre m := by
  unfold MemsetPre
  rw [h0, h2]
  exact ⟨C.mapped P h, P.ad_nw h⟩

theorem memcpyPre (P : Pre w m₀) (C : Common m₀ m) {o o' n : Nat}
    (h0 : m.regs.X0.toBitVec = ad m₀ o) (h1 : m.regs.X1.toBitVec = ad m₀ o')
    (h2 : m.regs.X2.toNat = n) (h : o + n ≤ 9200) (h' : o' + n ≤ 9200)
    (hd : o + n ≤ o' ∨ o' + n ≤ o) (hn : 0 < n) : MemcpyPre m := by
  unfold MemcpyPre
  rw [h0, h1, h2]
  exact ⟨C.mapped P h, C.mapped P h', P.ad_nw h, P.ad_nw h', P.apart_ad hd h h' hn hn⟩

theorem updatePre (P : Pre w m₀) (C : Common m₀ m) {o o' n : Nat}
    (h0 : m.regs.X0.toBitVec = ad m₀ o) (h1 : m.regs.X1.toBitVec = ad m₀ o')
    (h2 : m.regs.X2.toNat = n) (ho : fb ≤ o) (ho' : fb ≤ o') (h : o + 344 ≤ 9200)
    (h' : o' + n ≤ 9200) (hd : o + 344 ≤ o' ∨ o' + n ≤ o) (hn : 0 < n)
    (hh : ∃ a, NativeRustc.Keccak.HasherHolds (bytesOf m.dmem (ad m₀ o) 344) a) : UpdatePre m := by
  unfold UpdatePre
  rw [h0, h1, h2]
  have hu : updateStack ≤ fb := by decide
  exact ⟨C.stackOk P hu, C.rcAt P hu (by decide), hh, C.mapped P h, P.ad_nw h, C.mapped P h',
    P.ad_nw h', P.apart_ad hd h h' (by omega) hn,
    apart_stack P C hu (by decide) ho h (by omega), apart_stack P C hu (by decide) ho' h' hn,
    (P.rc_apart h (by omega)).symm⟩

theorem finalizePre (P : Pre w m₀) (C : Common m₀ m) {o o' : Nat}
    (h0 : m.regs.X0.toBitVec = ad m₀ o) (h1 : m.regs.X1.toBitVec = ad m₀ o')
    (ho : fb ≤ o) (ho' : fb ≤ o') (h : o + 32 ≤ 9200) (h' : o' + 344 ≤ 9200)
    (hd : o + 32 ≤ o' ∨ o' + 344 ≤ o)
    (hh : ∃ a, NativeRustc.Keccak.HasherHolds (bytesOf m.dmem (ad m₀ o') 344) a) : FinalizePre m := by
  unfold FinalizePre
  rw [h0, h1]
  have hu : finalizeStack ≤ fb := by decide
  exact ⟨C.stackOk P hu, C.rcAt P hu (by decide), hh, C.mapped P h', P.ad_nw h', C.mapped P h,
    P.ad_nw h, P.apart_ad hd h h' (by omega) (by omega),
    apart_stack P C hu (by decide) ho' h' (by omega), apart_stack P C hu (by decide) ho h (by omega),
    (P.rc_apart h (by omega)).symm⟩

/-- An input of `wots_leaf` in the frame. -/
theorem wotsInput (P : Pre w m₀) (C : Common m₀ m) {a : BitVec 64} {o n : Nat}
    (ha : a = ad m₀ o) (ho : fb ≤ o) (h : o + n ≤ 9200) (hn : 0 < n) :
    WotsLeafPre.Input m a n := by
  subst ha
  exact ⟨C.mapped P h, P.ad_nw h, apart_stack P C le_rfl (by decide) ho h hn⟩

theorem wotsLeafPre (P : Pre w m₀) (C : Common m₀ m) {o o1 o4 n5 o6 o7 : Nat}
    (h0 : m.regs.X0.toBitVec = ad m₀ o) (h1 : m.regs.X1.toBitVec = ad m₀ o1)
    (h4 : m.regs.X4.toBitVec = ad m₀ o4) (h5 : m.regs.X5.toNat = n5)
    (h6 : m.regs.X6.toBitVec = ad m₀ o6) (h7 : m.regs.X7.toBitVec = ad m₀ o7)
    (ho : fb ≤ o) (ho1 : fb ≤ o1) (ho4 : fb ≤ o4) (ho6 : fb ≤ o6) (ho7 : fb ≤ o7)
    (h : o + 75 ≤ 9200) (h1' : o1 + 16 ≤ 9200) (h4' : o4 + n5 ≤ 9200) (h6' : o6 + 16 ≤ 9200)
    (h7' : o7 + 16 * 58 ≤ 9200) (hn5 : 0 < n5) : WotsLeafPre m := by
  have hu : wotsLeafStack ≤ fb := le_rfl
  refine ⟨C.stackOk P hu, C.rcAt P hu (by decide), wotsInput P C h0 ho h (by omega),
    wotsInput P C h1 ho1 h1' (by omega), ?_, wotsInput P C h6 ho6 h6' (by omega),
    wotsInput P C h7 ho7 h7' (by omega)⟩
  rw [h5]
  exact wotsInput P C h4 ho4 h4' hn5

/-! ## What a call keeps -/

omit [Labels] in
/-- **A call keeps `Common`** when it keeps the callee-saved registers and SP and changes only
bytes of the stack outside the save area. -/
theorem Common.call (C : Common m₀ m) (hs : Saved m m') {R : BitVec 64 → Prop}
    (hsame : SameOutside m.dmem m'.dmem R) (hR : ∀ p, R p → InRange (lo m₀) 9200 p)
    (hsave : ∀ x, fb + 5776 ≤ x → x < 9200 → ¬R (ad m₀ x)) : Common m₀ m' where
  sp := by rw [hs.2.1]; exact C.sp
  x29 := by rw [hs.1 .X29 rfl]; exact C.x29
  save j hj := (C.save j hj).sameOutside hsame fun t ht => by
    rw [ad_add]
    rw [length_regBytes] at ht
    exact hsave _ (by omega) (by rw [fb_eq]; omega)
  same := (C.same.trans hsame).mono fun p hp => hp.elim id (hR p)
  kept := C.kept.trans hs.2.2

omit [Labels] in
/-- Bytes of the stack a call does not change are kept. -/
theorem keep_ad {d d' : DataMem} {R : BitVec 64 → Prop} (hsame : SameOutside d d' R) {o : Nat}
    {bs : List UInt8} (h : BytesAt d (ad m₀ o) bs)
    (hR : ∀ t < bs.length, ¬R (ad m₀ (o + t))) : BytesAt d' (ad m₀ o) bs :=
  h.sameOutside hsame fun t ht => by rw [ad_add]; exact hR t ht

end

end NativeRustcArm.Xmss.XmssVerify
