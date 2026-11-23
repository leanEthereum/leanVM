module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.SphincsVerify.Digest.Keep

/-!
# A block of the frame ending in a call (x86-64)

A block run in the frame from `frameS k` (the registers `k` known, `KnownOK`) whose writes miss
what the digest keeps (`keepOK`), then its callee's contract: per callee (`Run.memsetCall`,
`Run.memcpyCall`, `Run.updateCall`, `Run.finalizeCall`) with its arguments the frame's bytes the
block's literal state gives. The proof continues from the block's end with the frame's bytes the
block did not write (`KB`), then from the return with what the digest keeps, the callee-saved
registers and the bytes the callee did not change (`After`, `KC`). A hasher in the frame:
`HasherAt`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustc NativeRustcX64.Sym

@[expose] public section

/-- A hasher that has absorbed `x` at the frame's byte `a`. -/
def HasherAt (r : Run) (m : MachineData) (a : Nat) (x : List UInt8) : Prop :=
  ∃ h, BytesAt m.dmem (r.off a) h ∧ Keccak.HasherHolds h x

end

public section

theorem HasherAt.keepB {r : Run} {S : SState} {m m₁ : MachineData} (hk : KB r S m m₁) {a : Nat}
    {x : List UInt8} (h : HasherAt r m a x) (ha : a + 344 ≤ 29400)
    (hn : Run.noWriteIn S a 344 = true) : HasherAt r m₁ a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, hk a b (by omega) (by rw [hl]; exact hn) hb, hh⟩

theorem HasherAt.keepC {r : Run} {m₁ m₂ : MachineData} {a' n : Nat} (hk : KC r m₁ m₂ a' n)
    {a : Nat} {x : List UInt8} (h : HasherAt r m₁ a x) (ha : a + 344 ≤ 29400)
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

variable [Host]

/-- What follows a call returning in `m₂`: what the digest keeps, the callee-saved registers,
the frame's bytes apart from `a .. a + n`. -/
abbrev After (r : Run) (m₁ : MachineData) (a n : Nat) (j' : Nat) (Res : MachineData → Prop)
    (R : MachineState → Prop) : Prop :=
  ∀ m₂, Keep r m₂ → Saved m₁ m₂ → KC r m₁ m₂ a n → Res m₂ →
    Eventually (step1 Host.exe) R ⟨m₂, r.pc j'⟩

omit [Host] in
theorem kc_of_call {r : Run} [Labels] (hpre : r.Pre) {m₁ m₂ : MachineData} (hc : r.AtCall m₁)
    {a n N : Nat} (ha : a + n ≤ 29400) (hN : N ≤ finalizeStack)
    (hout : SameOutside m₁.dmem m₂.dmem (r.CallOut m₁ a n N)) : KC r m₁ m₂ a n :=
  fun _ _ ho hd h ↦ r.bytesAt_of_call hpre hc ha hN hout ho hd h

/-- **`memset(a, 0, n)`** after a block. -/
theorem Run.memsetCall (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (Reg64 × Sym)} {S' : SState} (hx : exec ds (frameS k) = some (S', .call NativeRustcX64.Common.Memset.entryLabel))
    (hok : keepOK S' = true) (hrsp : S'.reg .rsp = some (.ptr 0 (-8))) {m : MachineData}
    (hK : Keep r m) (hk : KnownOK r m (r.pc j').toBitVec k) {a n : Nat}
    (h0 : S'.reg .rdi = some (.ptr 0 a)) (h1 : S'.reg .rsi = some (.lit 0))
    (h2 : S'.reg .rdx = some (.lit n)) (ha : Scratch a n) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc j').toBitVec) S' m₁ → KB r S' m m₁ →
      After r m₁ a n j' (fun m₂ ↦ BytesAt m₂.dmem (r.off a) (List.replicate n 0)) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ha
  refine Run.frameCall r hp hpre hb hj hx hok hrsp hK hk hc.2.1
    fun m₁ hm₁ hc₁ hI₁ h176 hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r2 := rdx_lit hm₁ h2 (by omega)
  have r1 : reg m₁ .rsi = 0 := regIs_lit hm₁ h1
  refine ⟨r.memset_pre hpre hc₁ r0 r2 (by omega), fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memset_out r0 r2 hQ
  rw [r1] at hB
  exact h m₁ hm₁ hkb m₂ (Keep.of_call hpre hc₁ hI₁ h176 hS hsp (by unfold Scratch; omega)
    (by decide) hout) hS (kc_of_call hpre hc₁ (by omega) (by decide) hout) hB

/-- **`memcpy(a, b, n)`** after a block, the bytes `bs` at `b`. -/
theorem Run.memcpyCall (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (Reg64 × Sym)} {S' : SState} (hx : exec ds (frameS k) = some (S', .call NativeRustcX64.Common.Memcpy.entryLabel))
    (hok : keepOK S' = true) (hrsp : S'.reg .rsp = some (.ptr 0 (-8))) {m : MachineData}
    (hK : Keep r m) (hk : KnownOK r m (r.pc j').toBitVec k) {a b n : Nat}
    (h0 : S'.reg .rdi = some (.ptr 0 a)) (h1 : S'.reg .rsi = some (.ptr 0 b))
    (h2 : S'.reg .rdx = some (.lit n)) (ha : Scratch a n) (hbn : b + n ≤ 29400)
    (hd : a + n ≤ b ∨ b + n ≤ a) {bs : List UInt8} (hl : bs.length = n) {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc j').toBitVec) S' m₁ → KB r S' m m₁ →
      BytesAt m₁.dmem (r.off b) bs ∧
        After r m₁ a n j' (fun m₂ ↦ BytesAt m₂.dmem (r.off a) bs) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ha
  refine Run.frameCall r hp hpre hb hj hx hok hrsp hK hk hc.1 fun m₁ hm₁ hc₁ hI₁ h176 hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r1 := regIs_ptr hm₁ h1
  have r2 := rdx_lit hm₁ h2 (by omega)
  obtain ⟨hbs, hc'⟩ := h m₁ hm₁ hkb
  refine ⟨r.memcpy_pre hpre hc₁ r0 r1 r2 (by omega) hbn hd, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memcpy_out r0 r1 r2 hQ
  rw [← hl, bytesOf_of_bytesAt hbs] at hB
  exact hc' m₂ (Keep.of_call hpre hc₁ hI₁ h176 hS hsp (by unfold Scratch; omega) (by decide) hout)
    hS (kc_of_call hpre hc₁ (by omega) (by decide) hout) hB

/-- **`Hasher::update(a, b, n)`** after a block, the hasher at `a` having absorbed `x`, the bytes
`bs` at `b`. -/
theorem Run.updateCall (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (Reg64 × Sym)} {S' : SState} (hx : exec ds (frameS k) = some (S', .call NativeRustcX64.Common.Update.entryLabel))
    (hok : keepOK S' = true) (hrsp : S'.reg .rsp = some (.ptr 0 (-8))) {m : MachineData}
    (hK : Keep r m) (hk : KnownOK r m (r.pc j').toBitVec k) {a b n : Nat}
    (h0 : S'.reg .rdi = some (.ptr 0 a)) (h1 : S'.reg .rsi = some (.ptr 0 b))
    (h2 : S'.reg .rdx = some (.lit n)) (ha : Scratch a 344) (hbn : b + n ≤ 29400)
    (hd : a + 344 ≤ b ∨ b + n ≤ a) {x bs : List UInt8} (hl : bs.length = n)
    {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc j').toBitVec) S' m₁ → KB r S' m m₁ →
      HasherAt r m₁ a x ∧ BytesAt m₁.dmem (r.off b) bs ∧
        After r m₁ a 344 j' (fun m₂ ↦ HasherAt r m₂ a (x ++ bs)) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ha
  refine Run.frameCall r hp hpre hb hj hx hok hrsp hK hk hc.2.2.1
    fun m₁ hm₁ hc₁ hI₁ h176 hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r1 := regIs_ptr hm₁ h1
  have r2 := rdx_lit hm₁ h2 (by omega)
  obtain ⟨hH, hbs, hc'⟩ := h m₁ hm₁ hkb
  refine ⟨r.update_pre hpre hc₁ r0 r1 r2 (by omega) hbn hd hH.holds_some, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hA, hout, hS⟩ := r.update_out r0 r1 r2 hQ
  have hK₂ := Keep.of_call hpre hc₁ hI₁ h176 hS hsp (by unfold Scratch; omega) (by decide) hout
  have hA' := hA x hH.holds
  rw [← hl, bytesOf_of_bytesAt hbs] at hA'
  exact hc' m₂ hK₂ hS (kc_of_call hpre hc₁ (by omega) (by decide) hout)
    ⟨_, bytesAt_bytesOf (r.frame_mapped hpre hK₂.1.2.2.2 (by omega)).1, hA'⟩

/-- **`Hasher::finalize(o, a)`** after a block, the hasher at `a` having absorbed `x`. -/
theorem Run.finalizeCall (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    (hc : Callees) {ds : List Directive} {j j' : Nat}
    (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hj : j + ds.length = j')
    {k : List (Reg64 × Sym)} {S' : SState}
    (hx : exec ds (frameS k) = some (S', .call NativeRustcX64.Common.Finalize.entryLabel))
    (hok : keepOK S' = true) (hrsp : S'.reg .rsp = some (.ptr 0 (-8))) {m : MachineData}
    (hK : Keep r m) (hk : KnownOK r m (r.pc j').toBitVec k) {o a : Nat}
    (h0 : S'.reg .rdi = some (.ptr 0 o)) (h1 : S'.reg .rsi = some (.ptr 0 a))
    (ho : Scratch o 32) (ha : a + 344 ≤ 29400) (hd : o + 32 ≤ a ∨ a + 344 ≤ o) {x : List UInt8}
    {R : MachineState → Prop}
    (h : ∀ m₁, Match (r.env m (fun _ ↦ 0) (r.pc j').toBitVec) S' m₁ → KB r S' m m₁ →
      HasherAt r m₁ a x ∧
        After r m₁ o 32 j' (fun m₂ ↦ BytesAt m₂.dmem (r.off o) (Keccak.hashBytes x)) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  unfold Scratch at ho
  refine Run.frameCall r hp hpre hb hj hx hok hrsp hK hk hc.2.2.2.1
    fun m₁ hm₁ hc₁ hI₁ h176 hkb ↦ ?_
  have r0 := regIs_ptr hm₁ h0
  have r1 := regIs_ptr hm₁ h1
  obtain ⟨hH, hc'⟩ := h m₁ hm₁ hkb
  refine ⟨r.finalize_pre hpre hc₁ r0 r1 (by omega) ha hd hH.holds_some, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.finalize_out r0 r1 hQ
  rw [Keccak.finalize_eq hH.holds] at hB
  exact hc' m₂ (Keep.of_call hpre hc₁ hI₁ h176 hS hsp (by unfold Scratch; omega) (by decide) hout)
    hS (kc_of_call hpre hc₁ (by omega) (by decide) hout) hB

end

end NativeRustcX64.SphincsVerifyProof.Digest
