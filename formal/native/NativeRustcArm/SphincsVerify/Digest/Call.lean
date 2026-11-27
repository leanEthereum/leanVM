module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Common.Update.Names

public import NativeRustcArm.SphincsVerify.Digest.Keep
public import NativeRustcArm.SphincsVerify.Digest.Exec

/-!
# A block of the frame ending in a call

A block run in the frame from `frameS k` (the registers `k` known, `KnownOK`) whose writes miss
what the digest keeps (`keepOK`), then its callee's contract: `Run.frameCall`, and per callee
(`Run.memsetCall`, `Run.memcpyCall`, `Run.updateCall`, `Run.updateCallMsg`, `Run.finalizeCall`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustcArm.Sym

@[expose] public section

/-- The known registers of `frameS k` hold their values. -/
def KnownOK [Labels] (r : Run) (m : MachineData) (k : List (XReg × Sym)) : Prop :=
  AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m)) k

/-- The frame's bytes a block from `m` to `m₁` (literal state `S`) did not write are kept. -/
def KB (r : Run) (S : SState) (m m₁ : MachineData) : Prop :=
  ∀ o (bs : List UInt8), o + bs.length ≤ 21616 → Run.noWriteIn S o bs.length = true →
    BytesAt m.dmem (r.off o) bs → BytesAt m₁.dmem (r.off o) bs

/-- The frame's bytes apart from `a .. a + n` are kept from `m₁` to `m₂`. -/
def KC (r : Run) (m₁ m₂ : MachineData) (a n : Nat) : Prop :=
  ∀ o (bs : List UInt8), o + bs.length ≤ 21616 → (o + bs.length ≤ a ∨ a + n ≤ o) →
    BytesAt m₁.dmem (r.off o) bs → BytesAt m₂.dmem (r.off o) bs

/-- A hasher that has absorbed `x` at the frame's byte `a`. -/
def HasherAt (r : Run) (m : MachineData) (a : Nat) (x : List UInt8) : Prop :=
  ∃ h, BytesAt m.dmem (r.off a) h ∧ Keccak.HasherHolds h x

end

public section

theorem HasherAt.keepB {r : Run} {S : SState} {m m₁ : MachineData} (hk : KB r S m m₁) {a : Nat}
    {x : List UInt8} (h : HasherAt r m a x) (ha : a + 344 ≤ 21616)
    (hn : Run.noWriteIn S a 344 = true) : HasherAt r m₁ a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, hk a b (by omega) (by rw [hl]; exact hn) hb, hh⟩

theorem HasherAt.keepC {r : Run} {m₁ m₂ : MachineData} {a' n : Nat} (hk : KC r m₁ m₂ a' n)
    {a : Nat} {x : List UInt8} (h : HasherAt r m₁ a x) (ha : a + 344 ≤ 21616)
    (hd : a + 344 ≤ a' ∨ a' + n ≤ a) : HasherAt r m₂ a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, hk a b (by omega) (by omega) hb, hh⟩

/-- Mapped bytes are what `bytesOf` reads. -/
theorem bytesAt_bytesOf {d : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n) :
    BytesAt d a (bytesOf d a n) := by
  intro i hi
  simp only [bytesOf, List.length_map, List.length_range] at hi
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h i hi)
  rw [hv]
  rfl

theorem HasherAt.holds_some {r : Run} {m : MachineData} {a : Nat} {x : List UInt8}
    (h : HasherAt r m a x) : ∃ y, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) y := by
  obtain ⟨b, hb, hh⟩ := h
  rw [← Keccak.length_of_holds hh, bytesOf_of_bytesAt hb]
  exact ⟨x, hh⟩

theorem HasherAt.holds {r : Run} {m : MachineData} {a : Nat} {x : List UInt8}
    (h : HasherAt r m a x) : Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x := by
  obtain ⟨b, hb, hh⟩ := h
  rw [← Keccak.length_of_holds hh, bytesOf_of_bytesAt hb]
  exact hh

section
variable {r : Run} [Labels]

theorem knownOK_nil (m : MachineData) : KnownOK r m [] := trivial

theorem knownOK_ptr {m : MachineData} {y : XReg} {o : Nat} {k : List (XReg × Sym)}
    (h : Run.RegIs m y (r.off o)) (hk : KnownOK r m k) : KnownOK r m ((y, .ptr 0 o) :: k) :=
  known_cons h hk

theorem knownOK_lit {m : MachineData} {y : XReg} {c : Nat} {k : List (XReg × Sym)}
    (h : Run.RegIs m y (BitVec.ofNat 64 c)) (hk : KnownOK r m k) :
    KnownOK r m ((y, .lit c) :: k) :=
  known_lit h hk

/-- The frame's symbolic state for a state of the frame. -/
theorem Run.frame_match (r : Run) (hpre : r.Pre) {m : MachineData} (hK : Keep r m)
    {k : List (XReg × Sym)} (hk : KnownOK r m k) : Match (r.env m) (frameS k) m :=
  r.match_frame hpre hK.1 (known := (.X29, .ptr 0 21520) :: k)
    (known_cons (o := 21520) hK.1.2.1 hk) trivial trivial trivial

end

variable [ElfHost]

/-- **A block of the frame, then its callee.** -/
theorem Run.frameCall (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {ds : List Directive} {j j' : Nat} (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    (hj : j + ds.length = j') {k : List (XReg × Sym)} {S' : SState} {l : Label}
    (hx : exec ds (frameS k) = some (S', .call l)) (hok : keepOK S' = true)
    {m : MachineData} (hK : Keep r m) (hk : KnownOK r m k)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : ElfSpec (Labels.label l) P Q) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m) S' m₁ → Keep r m₁ → KB r S' m m₁ → P m₁ ∧
      ∀ m₂, Q m₁ m₂ → Eventually (elfStep1 ElfHost.exe) R ⟨m₂, r.pc j'⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  exact Run.callStep r hp hb hj hwf hx (Run.frame_match r hpre hK hk) hspec fun m₁ hm₁ ↦
    h m₁ hm₁ (hK.of_block hpre hm₁ hwf hok) fun _ _ ho hn hb ↦ r.bytesAt_kept hpre hm₁ hwf ho hb hn

/-- **A block of the frame falling through.** -/
theorem Run.frameFall (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {ds : List Directive} {j j' : Nat} (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    (hj : j + ds.length = j') (hne : ds ≠ []) {k : List (XReg × Sym)} {S' : SState}
    (hx : exec ds (frameS k) = some (S', .fall)) (hok : keepOK S' = true)
    {m : MachineData} (hK : Keep r m) (hk : KnownOK r m k) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m) S' m₁ → Keep r m₁ → KB r S' m m₁ →
      Eventually (elfStep1 ElfHost.exe) R ⟨m₁, r.pc j'⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  exact Run.fallStep r hp hb hj hne hwf hx (Run.frame_match r hpre hK hk) fun m₁ hm₁ ↦
    h m₁ hm₁ (hK.of_block hpre hm₁ hwf hok) fun _ _ ho hn hb ↦ r.bytesAt_kept hpre hm₁ hwf ho hb hn

/-- What follows a call returning in `m₂`: what the digest keeps, the callee-saved registers, the
frame's bytes apart from `a .. a + n`. -/
abbrev After (r : Run) (m₁ : MachineData) (a n : Nat) (j' : Nat) (Res : MachineData → Prop)
    (R : MachineState → Prop) : Prop :=
  ∀ m₂, Keep r m₂ → Saved m₁ m₂ → KC r m₁ m₂ a n → Res m₂ →
    Eventually (elfStep1 ElfHost.exe) R ⟨m₂, r.pc j'⟩

omit [ElfHost] in
theorem kc_of_call {r : Run} [Labels] (hpre : r.Pre) {m₁ m₂ : MachineData} (hF : r.Frame m₁) {a n N : Nat}
    (ha : a + n ≤ 21616) (hN : N ≤ finalizeStack)
    (hout : SameOutside m₁.dmem m₂.dmem (r.CallOut m₁ a n N)) : KC r m₁ m₂ a n :=
  fun _ _ ho hd h ↦ r.bytesAt_of_call hpre hF ha hN hout ho hd h

/-- **`memset(a, 0, n)`** after a block. -/
theorem Run.memsetCall (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (XReg × Sym)} {S' : SState} (hx : exec ds (frameS k) = some (S', .call NativeRustcArm.Common.Memset.entryLabel))
    (hok : keepOK S' = true) {m : MachineData} (hK : Keep r m) (hk : KnownOK r m k) {a n : Nat}
    (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.lit 0))
    (h2 : S'.reg .X2 = some (.lit n)) (ha : Scratch a n) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m) S' m₁ → Keep r m₁ → KB r S' m m₁ →
      After r m₁ a n j' (fun m₂ ↦ BytesAt m₂.dmem (r.off a) (List.replicate n 0)) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ha
  refine Run.frameCall r hp hpre hb hj hx hok hK hk hc.2.1 fun m₁ hm₁ hK₁ hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r2 := x2_lit hm₁ h2 (by omega)
  have r1 : m₁.regs.X1.toUInt8 = 0 := by
    have := regIs_lit hm₁ h1
    unfold Run.RegIs at this
    rw [← getXReg_X1, UInt64.toUInt8, UInt64.toNat, this]
    rfl
  refine ⟨r.memset_pre hpre hK₁.1 r0 r2 (by omega), fun m₂ hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memset_out r0 r2 hQ
  rw [r1] at hB
  exact h m₁ hm₁ hK₁ hkb m₂ (hK₁.of_call hpre hS ⟨ha.1, ha.2⟩ (by decide) hout) hS
    (kc_of_call hpre hK₁.1 (by omega) (by decide) hout) hB

/-- **`memcpy(a, b, n)`** after a block, the bytes `bs` at `b`. -/
theorem Run.memcpyCall (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (XReg × Sym)} {S' : SState} (hx : exec ds (frameS k) = some (S', .call NativeRustcArm.Common.Memcpy.entryLabel))
    (hok : keepOK S' = true) {m : MachineData} (hK : Keep r m) (hk : KnownOK r m k) {a b n : Nat}
    (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.ptr 0 b))
    (h2 : S'.reg .X2 = some (.lit n)) (ha : Scratch a n) (hbn : b + n ≤ 21616)
    (hd : a + n ≤ b ∨ b + n ≤ a) {bs : List UInt8} (hl : bs.length = n) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m) S' m₁ → Keep r m₁ → KB r S' m m₁ →
      BytesAt m₁.dmem (r.off b) bs ∧
        After r m₁ a n j' (fun m₂ ↦ BytesAt m₂.dmem (r.off a) bs) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ha
  refine Run.frameCall r hp hpre hb hj hx hok hK hk hc.1 fun m₁ hm₁ hK₁ hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r1 := regIs_ptr hm₁ h1
  have r2 := x2_lit hm₁ h2 (by omega)
  obtain ⟨hbs, hc'⟩ := h m₁ hm₁ hK₁ hkb
  refine ⟨r.memcpy_pre hpre hK₁.1 r0 r1 r2 (by omega) hbn hd, fun m₂ hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memcpy_out r0 r1 r2 hQ
  rw [← hl, bytesOf_of_bytesAt hbs] at hB
  exact hc' m₂ (hK₁.of_call hpre hS ⟨ha.1, ha.2⟩ (by decide) hout) hS
    (kc_of_call hpre hK₁.1 (by omega) (by decide) hout) hB

/-- **`Hasher::update(a, b, n)`** after a block, the hasher at `a` having absorbed `x`, the bytes
`bs` at `b`. -/
theorem Run.updateCall (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (XReg × Sym)} {S' : SState} (hx : exec ds (frameS k) = some (S', .call NativeRustcArm.Common.Update.entryLabel))
    (hok : keepOK S' = true) {m : MachineData} (hK : Keep r m) (hk : KnownOK r m k) {a b n : Nat}
    (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.ptr 0 b))
    (h2 : S'.reg .X2 = some (.lit n)) (ha : Scratch a 344) (hbn : b + n ≤ 21616)
    (hd : a + 344 ≤ b ∨ b + n ≤ a) {x bs : List UInt8} (hl : bs.length = n)
    {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m) S' m₁ → Keep r m₁ → KB r S' m m₁ →
      HasherAt r m₁ a x ∧ BytesAt m₁.dmem (r.off b) bs ∧
        After r m₁ a 344 j' (fun m₂ ↦ HasherAt r m₂ a (x ++ bs)) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ha
  refine Run.frameCall r hp hpre hb hj hx hok hK hk hc.2.2.1 fun m₁ hm₁ hK₁ hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r1 := regIs_ptr hm₁ h1
  have r2 := x2_lit hm₁ h2 (by omega)
  obtain ⟨hH, hbs, hc'⟩ := h m₁ hm₁ hK₁ hkb
  refine ⟨r.update_pre hpre hK₁.1 r0 r1 r2 (by omega) hbn hd hH.holds_some, fun m₂ hQ ↦ ?_⟩
  obtain ⟨hA, hout, hS⟩ := r.update_out r0 r1 r2 hQ
  have hF₂ := r.frame_of_call hpre hK₁.1 hS (by omega) (by decide) hout
  have hA' := hA x hH.holds
  rw [← hl, bytesOf_of_bytesAt hbs] at hA'
  exact hc' m₂ (hK₁.of_call hpre hS ⟨ha.1, ha.2⟩ (by decide) hout) hS
    (kc_of_call hpre hK₁.1 (by omega) (by decide) hout)
    ⟨_, bytesAt_bytesOf (r.frame_mapped hpre hF₂ (by omega)).1, hA'⟩

/-- **`Hasher::update(a, msgPtr, 32)`** after a block where `X1` comes from register `y` holding
`r.msgPtr`. -/
theorem Run.updateCallMsg (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (XReg × Sym)} {S' : SState} (hx : exec ds (frameS k) = some (S', .call NativeRustcArm.Common.Update.entryLabel))
    (hok : keepOK S' = true) {m : MachineData} (hK : Keep r m) (hk : KnownOK r m k) {a : Nat}
    {y : XReg} (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.reg y))
    (hy : Run.RegIs m y r.msgPtr) (h2 : S'.reg .X2 = some (.lit 32)) (ha : Scratch a 344)
    {x : List UInt8} {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m) S' m₁ → Keep r m₁ → KB r S' m m₁ →
      HasherAt r m₁ a x ∧ After r m₁ a 344 j' (fun m₂ ↦ HasherAt r m₂ a (x ++ r.msg)) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ha
  refine Run.frameCall r hp hpre hb hj hx hok hK hk hc.2.2.1 fun m₁ hm₁ hK₁ hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r1 : Run.RegIs m₁ .X1 r.msgPtr := (hm₁.regs .X1 _ h1).trans hy
  have r2 := x2_lit hm₁ h2 (by decide)
  obtain ⟨hH, hc'⟩ := h m₁ hm₁ hK₁ hkb
  refine ⟨r.update_pre_msg hpre hK₁.1 r0 r1 r2 (by omega) hH.holds_some, fun m₂ hQ ↦ ?_⟩
  obtain ⟨hA, hout, hS⟩ := r.update_out_msg r0 r1 r2 hQ
  have hF₂ := r.frame_of_call hpre hK₁.1 hS (by omega) (by decide) hout
  have hA' := hA x hH.holds
  have hmsg : BytesAt m₁.dmem r.msgPtr r.msgBytes := r.msg_bytesAt hpre hK₁.1
  rw [← r.hmsg, bytesOf_of_bytesAt hmsg] at hA'
  exact hc' m₂ (hK₁.of_call hpre hS ⟨ha.1, ha.2⟩ (by decide) hout) hS
    (kc_of_call hpre hK₁.1 (by omega) (by decide) hout)
    ⟨_, bytesAt_bytesOf (r.frame_mapped hpre hF₂ (by omega)).1, hA'⟩

/-- **`Hasher::finalize(o, a)`** after a block, the hasher at `a` having absorbed `x`. -/
theorem Run.finalizeCall (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (XReg × Sym)} {S' : SState}
    (hx : exec ds (frameS k) = some (S', .call NativeRustcArm.Common.Finalize.entryLabel))
    (hok : keepOK S' = true) {m : MachineData} (hK : Keep r m) (hk : KnownOK r m k) {o a : Nat}
    (h0 : S'.reg .X0 = some (.ptr 0 o)) (h1 : S'.reg .X1 = some (.ptr 0 a))
    (ho : Scratch o 32) (ha : a + 344 ≤ 21616) (hd : o + 32 ≤ a ∨ a + 344 ≤ o) {x : List UInt8}
    {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m) S' m₁ → Keep r m₁ → KB r S' m m₁ →
      HasherAt r m₁ a x ∧
        After r m₁ o 32 j' (fun m₂ ↦ BytesAt m₂.dmem (r.off o) (Keccak.hashBytes x)) R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ho
  refine Run.frameCall r hp hpre hb hj hx hok hK hk hc.2.2.2.1 fun m₁ hm₁ hK₁ hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r1 := regIs_ptr hm₁ h1
  obtain ⟨hH, hc'⟩ := h m₁ hm₁ hK₁ hkb
  refine ⟨r.finalize_pre hpre hK₁.1 r0 r1 (by omega) ha hd hH.holds_some, fun m₂ hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.finalize_out r0 r1 hQ
  rw [Keccak.finalize_eq hH.holds] at hB
  exact hc' m₂ (hK₁.of_call hpre hS ⟨ho.1, ho.2⟩ (by decide) hout) hS
    (kc_of_call hpre hK₁.1 (by omega) (by decide) hout) hB

/-- From one block's start in a state `P` to another's in `Q`, then on. -/
theorem Run.stage (r : Run) {j : Nat} {P : MachineData → Prop} {s : MachineState}
    {R : MachineState → Prop}
    (h : Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc j ∧ P st.data) s)
    (k : ∀ m, P m → Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc j⟩) :
    Eventually (elfStep1 ElfHost.exe) R s :=
  Eventually.bind_elf h fun ⟨m, pc⟩ ⟨hpc, hP⟩ ↦ by
    simp only at hpc
    subst hpc
    exact k m hP

end

end NativeRustcArm.SphincsVerifyProof.Digest
