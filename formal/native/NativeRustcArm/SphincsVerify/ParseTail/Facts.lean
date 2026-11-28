module

public import NativeRustcArm.SphincsVerify.ParseTail.Glue

/-!
# Facts carried through the parse's tail

`Facts r m L K`: the frame's invariant, the frame's bytes `L` (offset, length, bytes) and the
registers `K` (register, value). A change of the frame's range `a .. a + n` keeps the bytes it
misses (`BytesL.keep`, decided by `disj`), a block those no write of its literal summary reaches
(`BytesL.keep_block`, decided by `noW`); a callee keeps the callee-saved registers
(`RegsL.keep_call`), a block those its summary leaves as they were (`RegsL.keep_block`).
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustcArm.Sym

@[expose] public section

/-- The frame's bytes `L`: at offset `p.1`, the `p.2.1` bytes `p.2.2`. -/
def BytesL (r : Run) (d : DataMem) (L : List (Nat × Nat × List UInt8)) : Prop :=
  AllOf (fun p ↦ p.2.2.length = p.2.1 ∧ BytesAt d (r.off p.1) p.2.2) L

/-- The registers `K`. -/
def RegsL (m : MachineData) (K : List (XReg × BitVec 64)) : Prop :=
  AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2) K

/-- **The facts**: the frame, its bytes `L`, the registers `K`. -/
def Facts (r : Run) (m : MachineData) (L : List (Nat × Nat × List UInt8))
    (K : List (XReg × BitVec 64)) : Prop :=
  r.Frame m ∧ BytesL r m.dmem L ∧ RegsL m K

/-- The bytes `L` are in the frame and miss `a .. a + n`. -/
def disj (L : List (Nat × Nat × List UInt8)) (a n : Nat) : Bool :=
  L.all fun p ↦ decide (p.1 + p.2.1 ≤ 29376) && (decide (p.1 + p.2.1 ≤ a) || decide (a + n ≤ p.1))

/-- The bytes `L` are in the frame and no write of `S` reaches them. -/
def noW (S : SState) (L : List (Nat × Nat × List UInt8)) : Bool :=
  L.all fun p ↦ decide (p.1 + p.2.1 ≤ 29376) && Run.noWriteIn S p.1 p.2.1

/-- The registers `K` are callee-saved. -/
def savedK (K : List (XReg × BitVec 64)) : Bool := K.all fun p ↦ calleeSaved p.1

/-- The registers `K` are as they were in `S₀` (known there). -/
def keptK (S₀ S : SState) (K : List (XReg × BitVec 64)) : Bool :=
  K.all fun p ↦ (S₀.reg p.1).isSome && S.reg p.1 == S₀.reg p.1

/-! The side conditions on the facts' offsets and lengths (`shape`) and registers (`regsOf`) only:
once the lists are unfolded these mention neither the run nor the facts' bytes, so the kernel
decides them on a block's literal summary. -/

/-- The facts' offsets and lengths. -/
def shape (L : List (Nat × Nat × List UInt8)) : List (Nat × Nat) := L.map fun p ↦ (p.1, p.2.1)

/-- The facts' registers. -/
def regsOf (K : List (XReg × BitVec 64)) : List XReg := K.map Prod.fst

/-- `disj` on the shape. -/
def disjS (P : List (Nat × Nat)) (a n : Nat) : Bool :=
  P.all fun p ↦ decide (p.1 + p.2 ≤ 29376) && (decide (p.1 + p.2 ≤ a) || decide (a + n ≤ p.1))

/-- `noW` on the shape. -/
def noWS (S : SState) (P : List (Nat × Nat)) : Bool :=
  P.all fun p ↦ decide (p.1 + p.2 ≤ 29376) && Run.noWriteIn S p.1 p.2

/-- `savedK` on the registers. -/
def savedKS (X : List XReg) : Bool := X.all calleeSaved

/-- `keptK` on the registers. -/
def keptKS (S₀ S : SState) (X : List XReg) : Bool :=
  X.all fun x ↦ (S₀.reg x).isSome && S.reg x == S₀.reg x

end

public section

theorem allOf_iff {α : Type} {P : α → Prop} : ∀ {L : List α}, AllOf P L ↔ ∀ a ∈ L, P a
  | [] => by simp [AllOf]
  | a :: L => by simp [AllOf, allOf_iff]

theorem allOf_append {α : Type} {P : α → Prop} {L L' : List α} :
    AllOf P (L ++ L') ↔ AllOf P L ∧ AllOf P L' := by
  simp only [allOf_iff, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha ↦ h a (.inl ha), fun a ha ↦ h a (.inr ha)⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact h1 a ha
    · exact h2 a ha

theorem disj_mono {L : List (Nat × Nat × List UInt8)} {a n a' n' : Nat} (h : disj L a n = true)
    (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : disj L a' n' = true := by
  simp only [disj, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  intro p hp
  have := h p hp
  omega

theorem disj_eq (L : List (Nat × Nat × List UInt8)) (a n : Nat) :
    disj L a n = disjS (shape L) a n := by
  simp only [disj, disjS, shape, List.all_map, Function.comp_def]

theorem noW_eq (S : SState) (L : List (Nat × Nat × List UInt8)) : noW S L = noWS S (shape L) := by
  simp only [noW, noWS, shape, List.all_map, Function.comp_def]

theorem savedK_eq (K : List (XReg × BitVec 64)) : savedK K = savedKS (regsOf K) := by
  simp only [savedK, savedKS, regsOf, List.all_map, Function.comp_def]

theorem keptK_eq (S₀ S : SState) (K : List (XReg × BitVec 64)) :
    keptK S₀ S K = keptKS S₀ S (regsOf K) := by
  simp only [keptK, keptKS, regsOf, List.all_map, Function.comp_def]

variable (r : Run) [Labels]

/-- **Bytes a change elsewhere keeps.** -/
theorem BytesL.keep (hpre : r.Pre) {d d' : DataMem} {a n : Nat}
    (hs : SameOutside d d' (InRange (r.off a) n)) (ha : a + n ≤ 29376)
    {L : List (Nat × Nat × List UInt8)} (hd : disj L a n = true) (h : BytesL r d L) :
    BytesL r d' L := by
  unfold BytesL at *
  rw [allOf_iff] at h ⊢
  simp only [disj, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hd
  intro p hp
  obtain ⟨hl, hb⟩ := h p hp
  have := hd p hp
  exact ⟨hl, Parse.keep r hpre hb hs hl this.2 this.1 ha⟩

/-- **Bytes a block keeps**: those no write of its summary reaches. -/
theorem BytesL.keep_block (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF)
    {L : List (Nat × Nat × List UInt8)} (hd : noW S L = true) (h : BytesL r m.dmem L) :
    BytesL r m'.dmem L := by
  unfold BytesL at *
  rw [allOf_iff] at h ⊢
  simp only [noW, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd
  intro p hp
  obtain ⟨hl, hb⟩ := h p hp
  obtain ⟨h1, h2⟩ := hd p hp
  exact ⟨hl, r.bytesAt_kept hpre hm hwf (by omega) hb (hl ▸ h2)⟩

omit [Labels] in
/-- **Registers a callee keeps.** -/
theorem RegsL.keep_call {m m' : MachineData} (hS : Saved m m') {K : List (XReg × BitVec 64)}
    (hK : savedK K = true) (h : RegsL m K) : RegsL m' K := by
  unfold RegsL at *
  rw [allOf_iff] at h ⊢
  simp only [savedK, List.all_eq_true] at hK
  intro p hp
  rw [hS.1 p.1 (hK p hp)]
  exact h p hp

/-- **Registers a block keeps.** -/
theorem RegsL.keep_block {env : Env} {S₀ S : SState} {m m' : MachineData}
    (hm₀ : Match env S₀ m) (hm : Match env S m') {K : List (XReg × BitVec 64)}
    (hK : keptK S₀ S K = true) (h : RegsL m K) : RegsL m' K := by
  unfold RegsL at *
  rw [allOf_iff] at h ⊢
  simp only [keptK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hK
  intro p hp
  obtain ⟨⟨v, hv⟩, hS⟩ := hK p hp
  rw [Match.reg_eq hm₀ hm hv (hS.trans hv)]
  exact h p hp

omit [Labels] in
/-- Bytes then bytes. -/
theorem bytesAt_append {d : DataMem} {a : BitVec 64} {xs ys : List UInt8} (hx : BytesAt d a xs)
    (hy : BytesAt d (a + BitVec.ofNat 64 xs.length) ys) : BytesAt d a (xs ++ ys) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases h : i < xs.length
  · rw [List.getElem_append_left h]
    exact hx i h
  · rw [List.getElem_append_right (by omega)]
    have := hy (i - xs.length) (by omega)
    rwa [addr_add, show xs.length + (i - xs.length) = i by omega] at this

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
