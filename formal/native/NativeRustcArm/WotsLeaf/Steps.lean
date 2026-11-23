module

public import NativeRustcArm.WotsLeaf.Bytes
public import NativeRustcArm.WotsLeaf.FrameS

/-!
# What the frame keeps, and the steps from block to block

`Keep r L m`: the frame's invariant and the frame's slots `L` (offset, length, bytes) in place.
A call changing frame bytes apart from the slots (`slotsOff`, decided on literal offsets) keeps it
(`Keep.of_call`), as does a block run in the frame whose writes miss them (`slotsKept`,
`blockOK`, decided on the block's literal state; `Keep.of_block`). The frame's bytes a block does
not write (`KB`) and a call does not change (`KC`) stay.

Steps: a block of the function from its directive (`blk`), the pc its exit gives (`pc_true`,
`pc_false`, `pc_at`); each callee's contract from the frame (`memsetFrame`, `memcpyFrame`,
`updateFrame`, `finalizeFrame`, `keccakFrame`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustcArm.Sym

@[expose] public section

/-- A slot of the frame: its offset, its length and its bytes. -/
abbrev Slot := Nat × Nat × List UInt8

/-- The frame's slots `L` hold their bytes, below the saved registers. -/
def SlotsAt (r : Run) (m : MachineData) (L : List Slot) : Prop :=
  AllOf (fun s : Slot ↦ s.2.2.length = s.2.1 ∧ s.1 + s.2.1 ≤ 2656 ∧
    BytesAt m.dmem (r.off s.1) s.2.2) L

/-- **What the frame keeps**: its invariant and the slots `L`. -/
def Keep (r : Run) (L : List Slot) (m : MachineData) : Prop := r.Frame m ∧ SlotsAt r m L

/-- The slots `L` are apart from the frame's bytes `a .. a + n`. -/
def slotsOff (L : List Slot) (a n : Nat) : Bool :=
  L.all fun s ↦ decide (s.1 + s.2.1 ≤ a) || decide (a + n ≤ s.1)

/-- No write of `S` touches the slots `L`. -/
def slotsKept (S : SState) (L : List Slot) : Bool := L.all fun s ↦ Run.noWriteIn S s.1 s.2.1

/-- A block's literal state keeps the frame's invariant: its writes in the frame below the saved
registers, SP and X29 as they were. -/
def blockOK (S : SState) : Bool :=
  Run.frameWrites S && S.sp == .ptr 0 0 && S.reg .X29 == some (.ptr 0 2656)

/-- The known registers of `frameS k` hold their values. -/
def KnownOK [Labels] (r : Run) (m : MachineData) (k : List (XReg × Sym)) : Prop :=
  AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m)) k

/-- The frame's bytes a block from `m` to `m₁` (literal state `S`) did not write are kept. -/
def KB (r : Run) (S : SState) (m m₁ : MachineData) : Prop :=
  ∀ o (bs : List UInt8), o + bs.length ≤ 2752 → Run.noWriteIn S o bs.length = true →
    BytesAt m.dmem (r.off o) bs → BytesAt m₁.dmem (r.off o) bs

/-- The frame's bytes apart from `a .. a + n` are kept from `m₁` to `m₂`. -/
def KC (r : Run) (m₁ m₂ : MachineData) (a n : Nat) : Prop :=
  ∀ o (bs : List UInt8), o + bs.length ≤ 2752 → (o + bs.length ≤ a ∨ a + n ≤ o) →
    BytesAt m₁.dmem (r.off o) bs → BytesAt m₂.dmem (r.off o) bs

/-- A hasher that has absorbed `x` at the frame's byte `a`. -/
def HasherAt (r : Run) (m : MachineData) (a : Nat) (x : List UInt8) : Prop :=
  ∃ h, BytesAt m.dmem (r.off a) h ∧ Keccak.HasherHolds h x

end

public section

theorem allOf_imp {α : Type} {P Q : α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, P a → Q a) → AllOf P l → AllOf Q l
  | [], _, _ => trivial
  | a :: _, h, hL => ⟨h a List.mem_cons_self hL.1,
      allOf_imp (fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) hL.2⟩

theorem allOf_append {α : Type} {P : α → Prop} :
    ∀ {a : List α} {b : List α}, AllOf P a → AllOf P b → AllOf P (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ha, hb => ⟨ha.1, allOf_append ha.2 hb⟩

theorem allOf_left {α : Type} {P : α → Prop} :
    ∀ {a : List α} {b : List α}, AllOf P (a ++ b) → AllOf P a
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, allOf_left h.2⟩

theorem allOf_right {α : Type} {P : α → Prop} :
    ∀ {a : List α} {b : List α}, AllOf P (a ++ b) → AllOf P b
  | [], _, h => h
  | _ :: _, _, h => allOf_right h.2

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

theorem HasherAt.holds {r : Run} {m : MachineData} {a : Nat} {x : List UInt8}
    (h : HasherAt r m a x) : Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) x := by
  obtain ⟨b, hb, hh⟩ := h
  rw [← Keccak.length_of_holds hh, bytesOf_of_bytesAt hb]
  exact hh

theorem HasherAt.holds_some {r : Run} {m : MachineData} {a : Nat} {x : List UInt8}
    (h : HasherAt r m a x) : ∃ y, Keccak.HasherHolds (bytesOf m.dmem (r.off a) 344) y :=
  ⟨x, h.holds⟩

theorem HasherAt.keepB {r : Run} {S : SState} {m m₁ : MachineData} (hk : KB r S m m₁) {a : Nat}
    {x : List UInt8} (h : HasherAt r m a x) (ha : a + 344 ≤ 2752)
    (hn : Run.noWriteIn S a 344 = true) : HasherAt r m₁ a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, hk a b (by omega) (by rw [hl]; exact hn) hb, hh⟩

theorem HasherAt.keepC {r : Run} {m₁ m₂ : MachineData} {a' n : Nat} (hk : KC r m₁ m₂ a' n)
    {a : Nat} {x : List UInt8} (h : HasherAt r m₁ a x) (ha : a + 344 ≤ 2752)
    (hd : a + 344 ≤ a' ∨ a' + n ≤ a) : HasherAt r m₂ a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, hk a b (by omega) (by omega) hb, hh⟩

theorem slotsOff_spec {L : List Slot} {a n : Nat} (h : slotsOff L a n = true) :
    ∀ s ∈ L, s.1 + s.2.1 ≤ a ∨ a + n ≤ s.1 := by
  intro s hs
  have := List.all_eq_true.mp h s hs
  simpa using this

theorem slotsKept_spec {S : SState} {L : List Slot} (h : slotsKept S L = true) :
    ∀ s ∈ L, Run.noWriteIn S s.1 s.2.1 = true :=
  fun s hs ↦ List.all_eq_true.mp h s hs

/-- Slots of `L ++ L'`. -/
theorem SlotsAt.append {r : Run} {m : MachineData} {L L' : List Slot} (h : SlotsAt r m L)
    (h' : SlotsAt r m L') : SlotsAt r m (L ++ L') := allOf_append h h'

/-- A callee-saved register stays through a call. -/
theorem RegIs.of_saved {m m' : MachineData} (hS : Saved m m') {y : XReg} {v : BitVec 64}
    (hy : calleeSaved y = true) (h : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [hS.1 _ hy]
  exact h

section
variable {r : Run} [Labels]

theorem eval_ptr0 (m : MachineData) (vars : Nat → BitVec 64) (o : Nat) :
    (Sym.ptr 0 o).eval (r.env m vars) = r.off o := by
  simp only [Sym.eval, Run.off, BitVec.ofInt_natCast]
  rfl

/-- **A register the block sets to the frame's byte `o`.** -/
theorem regIs_ptr {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {y : XReg} {o : Nat} (h : S.reg y = some (.ptr 0 o)) :
    Run.RegIs m' y (r.off o) := by
  unfold Run.RegIs
  rw [hm.regs y _ h, eval_ptr0]

/-- **A register the block sets to a literal.** -/
theorem regIs_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : XReg}
    {c : Nat} (h : S.reg y = some (.lit c)) : Run.RegIs m' y (BitVec.ofNat 64 c) := by
  unfold Run.RegIs
  rw [hm.regs y _ h]
  rfl

/-- **A register a block keeps** (its symbolic value its own atom). -/
theorem regIs_reg {m m' : MachineData} {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (Env.ofMachine m regions vars) S m') {y : XReg} {v : BitVec 64}
    (h : S.reg y = some (.reg y)) (hv : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [hm.regs y _ h]
  exact hv

/-- A register a block sets to a literal: its number. -/
theorem toNat_of_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : XReg}
    {c : Nat} (h : S.reg y = some (.lit c)) (hc : c < 2 ^ 64) : (m'.regs.getXReg y).toNat = c := by
  have := hm.regs y _ h
  rw [← UInt64.toNat_toBitVec, this]
  exact Nat.mod_eq_of_lt hc

/-- X2 set to a literal. -/
theorem x2_eq {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {c : Nat}
    (h : S.reg .X2 = some (.lit c)) (hc : c < 2 ^ 64) : m'.regs.X2.toNat = c :=
  toNat_of_lit hm h hc

/-- X1 set to `0`. -/
theorem x1_zero {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m')
    (h : S.reg .X1 = some (.lit 0)) : m'.regs.X1.toUInt8 = 0 := by
  have := toNat_of_lit hm h (by decide)
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8]
  exact (congrArg (· % 256) this).trans rfl

/-- A known register that is the frame's byte `o`. -/
theorem known_ptr {m : MachineData} {y : XReg} {o : Nat} (h : Run.RegIs m y (r.off o)) :
    (m.regs.getXReg y).toBitVec = (Sym.ptr 0 o).eval (r.env m) := by
  rw [eval_ptr0]
  exact h

/-- A known register that is a literal. -/
theorem known_lit {m : MachineData} {y : XReg} {c : Nat} (h : Run.RegIs m y (BitVec.ofNat 64 c)) :
    (m.regs.getXReg y).toBitVec = (Sym.lit c).eval (r.env m) := h

/-- **A fresh symbolic state for a state of the frame**: the registers `k`. -/
theorem match_frameS (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {k : List (XReg × Sym)}
    (hk : KnownOK r m k) : Match (r.env m) (frameS k) m :=
  r.match_frame hpre hF (known := (.X29, .ptr 0 2656) :: k) ⟨known_ptr hF.2.1, hk⟩ trivial trivial
    trivial

/-- **Slots a call does not change** stay. -/
theorem SlotsAt.of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {L : List Slot}
    (h : SlotsAt r m L) {a n N : Nat} (ha : a + n ≤ 2752) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) (hL : slotsOff L a n = true) :
    SlotsAt r m' L :=
  allOf_imp (fun s hs ⟨hl, ho, hb⟩ ↦ ⟨hl, ho, r.bytesAt_of_call hpre hF ha hN hout (by omega)
    (by have := slotsOff_spec hL s hs; omega) hb⟩) h

/-- **A call changing frame bytes apart from the slots keeps what the frame keeps.** -/
theorem Keep.of_call (hpre : r.Pre) {L : List Slot} {m m' : MachineData} (hK : Keep r L m)
    (hS : Saved m m') {a n N : Nat} (ha : a + n ≤ 2656) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) (hL : slotsOff L a n = true) :
    Keep r L m' :=
  ⟨r.frame_of_call hpre hK.1 hS ha hN hout, hK.2.of_call hpre hK.1 (by omega) hN hout hL⟩

/-- **Slots a block does not write** stay. -/
theorem SlotsAt.of_block (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF) {L : List Slot}
    (h : SlotsAt r m L) (hL : slotsKept S L = true) : SlotsAt r m' L :=
  allOf_imp (fun s hs ⟨hl, ho, hb⟩ ↦ ⟨hl, ho, r.bytesAt_kept hpre hm hwf (by omega) hb
    (by rw [hl]; exact slotsKept_spec hL s hs)⟩) h

/-- **A block keeping the frame's invariant and missing the slots keeps what the frame
keeps.** -/
theorem Keep.of_block (hpre : r.Pre) {L : List Slot} {m m' : MachineData} (hK : Keep r L m)
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.env m vars) S m')
    (hwf : (r.env m vars).WF) (hok : blockOK S = true) (hL : slotsKept S L = true) :
    Keep r L m' := by
  simp only [blockOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hw, hsp⟩, hx29⟩ := hok
  exact ⟨Run.Frame.of_match r hpre hK.1 hm hwf hsp hx29 hw, hK.2.of_block hpre hm hwf hL⟩

/-- The frame's bytes a block does not write. -/
theorem kb_of_block (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF) : KB r S m m' :=
  fun _ _ ho hn hb ↦ r.bytesAt_kept hpre hm hwf ho hb hn

theorem kc_of_call (hpre : r.Pre) {m₁ m₂ : MachineData} (hF : r.Frame m₁) {a n N : Nat}
    (ha : a + n ≤ 2752) (hN : N ≤ finalizeStack)
    (hout : SameOutside m₁.dmem m₂.dmem (r.CallOut m₁ a n N)) : KC r m₁ m₂ a n :=
  fun _ _ ho hd h ↦ r.bytesAt_of_call hpre hF ha hN hout ho hd h

/-! ## The callees from the frame -/

/-- **`memset(a, 0, n)`** from the frame: its precondition, and after it the `n` zeros, what the
frame keeps, the callee-saved registers, the frame's other bytes. -/
theorem memsetFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : Keep r L m₁)
    {a n : Nat} (h0 : Run.RegIs m₁ .X0 (r.off a)) (h1 : m₁.regs.X1.toUInt8 = 0)
    (h2 : m₁.regs.X2.toNat = n) (ha : a + n ≤ 2656) (hL : slotsOff L a n = true) :
    MemsetPre m₁ ∧ ∀ m₂, MemsetPost m₁ m₂ → Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a n ∧
      BytesAt m₂.dmem (r.off a) (List.replicate n 0) := by
  refine ⟨r.memset_pre hpre hK.1 h0 h2 (by omega), fun m₂ hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memset_out h0 h2 hQ
  rw [h1] at hB
  exact ⟨hK.of_call hpre hS ha (by decide) hout hL, hS,
    kc_of_call hpre hK.1 (by omega) (by decide) hout, hB⟩

/-- **`memcpy(a, b, n)`** from the frame, the bytes `bs` at `b`. -/
theorem memcpyFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : Keep r L m₁)
    {a b n : Nat} (h0 : Run.RegIs m₁ .X0 (r.off a)) (h1 : Run.RegIs m₁ .X1 (r.off b))
    (h2 : m₁.regs.X2.toNat = n) (ha : a + n ≤ 2656) (hb : b + n ≤ 2752)
    (hd : a + n ≤ b ∨ b + n ≤ a) (hL : slotsOff L a n = true) {bs : List UInt8}
    (hl : bs.length = n) (hbs : BytesAt m₁.dmem (r.off b) bs) :
    MemcpyPre m₁ ∧ ∀ m₂, MemcpyPost m₁ m₂ → Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a n ∧
      BytesAt m₂.dmem (r.off a) bs := by
  refine ⟨r.memcpy_pre hpre hK.1 h0 h1 h2 (by omega) hb hd, fun m₂ hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 hQ
  rw [← hl, bytesOf_of_bytesAt hbs] at hB
  exact ⟨hK.of_call hpre hS ha (by decide) hout hL, hS,
    kc_of_call hpre hK.1 (by omega) (by decide) hout, hB⟩

/-- **`Hasher::update(a, b, n)`** from the frame, the hasher at `a` having absorbed `x`, the
bytes `bs` at `b`. -/
theorem updateFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : Keep r L m₁)
    {a b n : Nat} (h0 : Run.RegIs m₁ .X0 (r.off a)) (h1 : Run.RegIs m₁ .X1 (r.off b))
    (h2 : m₁.regs.X2.toNat = n) (ha : a + 344 ≤ 2656) (hb : b + n ≤ 2752)
    (hd : a + 344 ≤ b ∨ b + n ≤ a) (hL : slotsOff L a 344 = true) {x bs : List UInt8}
    (hH : HasherAt r m₁ a x) (hl : bs.length = n) (hbs : BytesAt m₁.dmem (r.off b) bs) :
    UpdatePre m₁ ∧ ∀ m₂, UpdatePost m₁ m₂ → Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a 344 ∧
      HasherAt r m₂ a (x ++ bs) := by
  refine ⟨r.update_pre hpre hK.1 h0 h1 h2 (by omega) hb hd hH.holds_some, fun m₂ hQ ↦ ?_⟩
  obtain ⟨hA, hout, hS⟩ := r.update_out h0 h1 h2 hQ
  have hF₂ := r.frame_of_call hpre hK.1 hS (by omega) (by decide) hout
  have hA' := hA x hH.holds
  rw [← hl, bytesOf_of_bytesAt hbs] at hA'
  exact ⟨hK.of_call hpre hS ha (by decide) hout hL, hS,
    kc_of_call hpre hK.1 (by omega) (by decide) hout,
    ⟨_, bytesAt_bytesOf (r.frame_mapped hpre hF₂ (by omega)).1, hA'⟩⟩

/-- **`Hasher::finalize(o, a)`** from the frame, the hasher at `a` having absorbed `x`. -/
theorem finalizeFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : Keep r L m₁)
    {o a : Nat} (h0 : Run.RegIs m₁ .X0 (r.off o)) (h1 : Run.RegIs m₁ .X1 (r.off a))
    (ho : o + 32 ≤ 2656) (ha : a + 344 ≤ 2752) (hd : o + 32 ≤ a ∨ a + 344 ≤ o)
    (hL : slotsOff L o 32 = true) {x : List UInt8} (hH : HasherAt r m₁ a x) :
    FinalizePre m₁ ∧ ∀ m₂, FinalizePost m₁ m₂ → Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ o 32 ∧
      BytesAt m₂.dmem (r.off o) (Keccak.hashBytes x) := by
  refine ⟨r.finalize_pre hpre hK.1 h0 h1 (by omega) ha hd hH.holds_some, fun m₂ hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.finalize_out h0 h1 hQ
  rw [Keccak.finalize_eq hH.holds] at hB
  exact ⟨hK.of_call hpre hS ho (by decide) hout hL, hS,
    kc_of_call hpre hK.1 (by omega) (by decide) hout, hB⟩

/-- **`keccak_f(a)`** from the frame, the 200 bytes `st` at `a`. -/
theorem keccakFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : Keep r L m₁)
    {a : Nat} (h0 : Run.RegIs m₁ .X0 (r.off a)) (ha : a + 200 ≤ 2656)
    (hL : slotsOff L a 200 = true) {st : List UInt8} (hl : st.length = 200)
    (hst : BytesAt m₁.dmem (r.off a) st) :
    KeccakFPre m₁ ∧ ∀ m₂, KeccakFPost m₁ m₂ → Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a 200 ∧
      BytesAt m₂.dmem (r.off a) (Keccak.keccakF st) := by
  refine ⟨r.keccakF_pre hpre hK.1 h0 (by omega), fun m₂ hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.keccakF_out h0 hQ
  rw [← hl, bytesOf_of_bytesAt hst] at hB
  exact ⟨hK.of_call hpre hS ha (by decide) hout hL, hS,
    kc_of_call hpre hK.1 (by omega) (by decide) hout, hB⟩

end

/-! ## Steps -/

section
variable [NativeRustcArm.Host]

/-- **A block of the function** run from directive `j`, then `cont` from where it ends. -/
theorem blk (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) {ds : List Directive}
    {j : Nat} (hb : ds.IsInfixAt Xmss.WotsLeaf.code j) (hne : ds ≠ []) {env : Env}
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WF) {m : MachineData}
    (hm : Match env S m) {R : MachineState → Prop}
    (cont : ∀ st, Match env S' st.data → PcOk env x (r.pc (j + ds.length)) st →
      Eventually (step1 NativeRustcArm.Host.exe) R st) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ :=
  exec_then (hb.trans hp.1 hne) hx hwf hm fun st h1 h2 ↦
    cont st h1 (by rw [Run.pc, ← Nat.add_assoc]; exact h2)

/-- A state at a known pc. -/
theorem pc_at {R : MachineState → Prop} {st : MachineState} {a : Int64} (h : st.pc = a)
    (k : Eventually (step1 NativeRustcArm.Host.exe) R ⟨st.data, a⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R st := by
  obtain ⟨d, pc⟩ := st
  subst h
  exact k

/-- **A label of the function** is the address of the block it starts. -/
theorem Run.label_of_block (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) {b : List Directive}
    {j : Nat} (hb : b.IsInfixAt Xmss.WotsLeaf.code j) {l : Label} {b' : List Directive}
    (h : b = .label l :: b') : Labels.label l = r.pc j := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

/-- **A call**: the callee's contract from the machine at its entry, then `cont` at the return
address. -/
theorem callAt {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (hpc : PcOk env (.call l) next st) {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (hspec : Spec (Labels.label l) P Q)
    {R : MachineState → Prop}
    (h : P st.data ∧ ∀ m₂, Q st.data m₂ → Eventually (step1 NativeRustcArm.Host.exe) R ⟨m₂, next⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R st :=
  call_then hpc hspec h.1 fun st' hpc' hq ↦ pc_at hpc' (h.2 st'.data hq)


/-- **A block of the frame**: run from `frameS k`, its writes keeping the frame's invariant and
missing the slots; `cont` from where it ends, with what the frame keeps. -/
theorem frameStep (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hb : ds.IsInfixAt Xmss.WotsLeaf.code j) (hne : ds ≠ [])
    {k : List (XReg × Sym)} {S' : SState} {x : Exit} (hx : exec ds (frameS k) = some (S', x))
    (hok : blockOK S' = true) {L : List Slot} (hL : slotsKept S' L = true) {m : MachineData}
    (hK : Keep r L m) (hk : KnownOK r m k) {R : MachineState → Prop}
    (cont : ∀ st, Match (r.env m) S' st.data → Keep r L st.data → KB r S' m st.data →
      PcOk (r.env m) x (r.pc (j + ds.length)) st → Eventually (step1 NativeRustcArm.Host.exe) R st) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  exact blk r hp hb hne hx hwf (match_frameS hpre hK.1 hk) fun st hm hpc ↦
    cont st hm (hK.of_block hpre hm hwf hok hL) (kb_of_block hpre hm hwf) hpc

/-- **A block of the frame ending in a call**, then the callee's contract. -/
theorem frameCall (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hb : ds.IsInfixAt Xmss.WotsLeaf.code j) (hne : ds ≠ [])
    {k : List (XReg × Sym)} {S' : SState} {l : Label} (hx : exec ds (frameS k) = some (S', .call l))
    (hok : blockOK S' = true) {L : List Slot} (hL : slotsKept S' L = true) {m : MachineData}
    (hK : Keep r L m) (hk : KnownOK r m k) {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (hspec : Spec (Labels.label l) P Q)
    {R : MachineState → Prop}
    (cont : ∀ m₁, Match (r.env m) S' m₁ → Keep r L m₁ → KB r S' m m₁ → P m₁ ∧
      ∀ m₂, Q m₁ m₂ → Eventually (step1 NativeRustcArm.Host.exe) R ⟨m₂, r.pc (j + ds.length)⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ :=
  frameStep r hp hpre hb hne hx hok hL hK hk fun st hm hK₁ hkb hpc ↦
    callAt hpc hspec (cont st.data hm hK₁ hkb)

end

variable [Labels]

theorem pc_true {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit true) l) next st) : st.pc = Labels.label l := h

theorem pc_false {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit false) l) next st) : st.pc = next := h

/-- The pc after a conditional branch whose condition evaluates to `b`. -/
theorem pc_cond {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) {b : Bool} (hc : c.eval env = b) :
    st.pc = if b then Labels.label l else next := by
  rw [← hc]
  exact h

end

end NativeRustcArm.WotsLeafProof
