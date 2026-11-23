module

public import NativeRustcX64.WotsLeaf.Bytes
public import NativeRustcX64.WotsLeaf.FrameS

/-!
# What the frame keeps, and the steps from block to block

`Keep r L m`: the frame's invariant and the frame's slots `L` (offset, length, bytes) in place;
`CallKeep r L m` the same at a callee's entry (RSP 8 below the base). A callee changing frame
bytes apart from the slots keeps it (`Keep.of_call`), as does a block run in the frame whose
writes miss them (`slotsKept`, `blockOK`, decided on the block's literal state;
`Keep.of_block`). The frame's bytes a block does not write (`KB`) and a call does not change
(`KC`) stay.

Steps: a block of the function from its directive (`blk`, `frameStep`, `frameCall`), the pc its
exit gives (`pc_cond`); each callee's contract from the frame (`memsetFrame`, `memcpyFrame`,
`updateFrame`, `updateInput`, `finalizeFrame`, `keccakFrame`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustcX64.Sym

@[expose] public section

/-- A slot of the frame: its offset, its length and its bytes. -/
abbrev Slot := Nat × Nat × List UInt8

/-- The frame's slots `L` hold their bytes, below the saved registers. -/
def SlotsAt (r : Run) (m : MachineData) (L : List Slot) : Prop :=
  AllOf (fun s : Slot ↦ s.2.2.length = s.2.1 ∧ s.1 + s.2.1 ≤ 2712 ∧
    BytesAt m.dmem (r.off s.1) s.2.2) L

/-- **What the frame keeps**: its invariant and the slots `L`. -/
def Keep (r : Run) (L : List Slot) (m : MachineData) : Prop := r.Frame m ∧ SlotsAt r m L

/-- What the frame keeps at a callee's entry. -/
def CallKeep (r : Run) (L : List Slot) (m : MachineData) : Prop := r.CallFrame m ∧ SlotsAt r m L

/-- The slots `L` are apart from the frame's bytes `a .. a + n` (decided first by `a + n ≤ s.1`,
so that a slot whose length is not a literal, above the change, decides by evaluation). -/
def slotsOff (L : List Slot) (a n : Nat) : Bool :=
  L.all fun s ↦ decide (a + n ≤ s.1) || decide (s.1 + s.2.1 ≤ a)

/-- No write of `S` touches the slots `L`. -/
def slotsKept (S : SState) (L : List Slot) : Bool := L.all fun s ↦ Run.noWriteIn S s.1 s.2.1

/-- A block's literal state keeps the frame's invariant: its writes in the frame below the saved
registers or in the call's return slot, RSP `d` from the base. -/
def blockOK (S : SState) (d : Int) : Bool := Run.frameWrites S && S.reg .rsp == some (.ptr 0 d)

/-- The environment of the frame's blocks: no variables, `ret` the return address a call
pushes. -/
abbrev Run.envR [Labels] (r : Run) (m : MachineData) (extra : List (BitVec 64 × Nat)) (ret : BitVec 64) :
    Env := r.env m ((gotAddr "memcpy", 8) :: (gotAddr "memset", 8) :: extra) (fun _ ↦ 0) ret

/-- The known registers of `frameS k` hold their values. -/
def KnownOK [Labels] (r : Run) (m : MachineData) (extra : List (BitVec 64 × Nat)) (ret : BitVec 64)
    (k : List (Reg64 × Sym)) : Prop :=
  AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.envR m extra ret)) k

/-- The extra regions are mapped, do not wrap, are apart from the frame's two regions and from
each other. -/
def ExtraOK [Labels] (r : Run) (m : MachineData) (extra : List (BitVec 64 × Nat)) : Prop :=
  AllOf (fun e : BitVec 64 × Nat ↦ Mapped m.dmem e.1 e.2 ∧ NoWrap e.1 e.2) extra ∧
    AllOf (fun e : BitVec 64 × Nat ↦ Apart r.base regionSize e.1 e.2 ∧
      Apart (r.base - 8#64) 8 e.1 e.2) extra ∧
    extra.Pairwise (fun e e' ↦ Apart e.1 e.2 e'.1 e'.2) ∧
    ∀ l ∈ ["memcpy", "memset"], ∀ e ∈ extra, Apart (gotAddr l) 8 e.1 e.2

/-- The frame's bytes a block from `m` to `m₁` (literal state `S`) did not write are kept. -/
def KB (r : Run) (S : SState) (m m₁ : MachineData) : Prop :=
  ∀ o (bs : List UInt8), o + bs.length ≤ 2768 → Run.noWriteIn S o bs.length = true →
    BytesAt m.dmem (r.off o) bs → BytesAt m₁.dmem (r.off o) bs

/-- The frame's bytes apart from `a .. a + n` are kept from `m₁` to `m₂`. -/
def KC (r : Run) (m₁ m₂ : MachineData) (a n : Nat) : Prop :=
  ∀ o (bs : List UInt8), o + bs.length ≤ 2768 → (o + bs.length ≤ a ∨ a + n ≤ o) →
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
    {x : List UInt8} (h : HasherAt r m a x) (ha : a + 344 ≤ 2768)
    (hn : Run.noWriteIn S a 344 = true) : HasherAt r m₁ a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, hk a b (by omega) (by rw [hl]; exact hn) hb, hh⟩

theorem HasherAt.keepC {r : Run} {m₁ m₂ : MachineData} {a' n : Nat} (hk : KC r m₁ m₂ a' n)
    {a : Nat} {x : List UInt8} (h : HasherAt r m₁ a x) (ha : a + 344 ≤ 2768)
    (hd : a + 344 ≤ a' ∨ a' + n ≤ a) : HasherAt r m₂ a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, hk a b (by omega) (by omega) hb, hh⟩

theorem slotsOff_spec {L : List Slot} {a n : Nat} (h : slotsOff L a n = true) :
    ∀ s ∈ L, s.1 + s.2.1 ≤ a ∨ a + n ≤ s.1 := by
  intro s hs
  have := List.all_eq_true.mp h s hs
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this.symm

theorem slotsKept_spec {S : SState} {L : List Slot} (h : slotsKept S L = true) :
    ∀ s ∈ L, Run.noWriteIn S s.1 s.2.1 = true :=
  fun s hs ↦ List.all_eq_true.mp h s hs

theorem extraOK_nil [Labels] {r : Run} {m : MachineData} : ExtraOK r m [] :=
  ⟨trivial, trivial, List.Pairwise.nil, by simp⟩

/-- Slots of `L ++ L'`. -/
theorem SlotsAt.append {r : Run} {m : MachineData} {L L' : List Slot} (h : SlotsAt r m L)
    (h' : SlotsAt r m L') : SlotsAt r m (L ++ L') := allOf_append h h'

/-- A callee-saved register stays through a call. -/
theorem RegIs.of_saved {m m' : MachineData} (hS : Saved m m') {y : Reg64} {v : BitVec 64}
    (hy : calleeSaved y = true) (h : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs reg at *
  rw [hS.1 _ hy]
  exact h

/-- RSP back from a call: the base. -/
theorem Run.callSp_add (r : Run) : r.base - 8#64 + 8#64 = r.base := by
  rw [BitVec.sub_add_cancel]

section
variable {r : Run} [Labels]

theorem eval_ptr0 (m : MachineData) (extra : List (BitVec 64 × Nat)) (ret : BitVec 64) (o : Nat) :
    (Sym.ptr 0 o).eval (r.envR m extra ret) = r.off o := by
  simp only [Sym.eval, Run.off, BitVec.ofInt_natCast]
  rfl

theorem eval_ptr_neg8 (m : MachineData) (extra : List (BitVec 64 × Nat)) (ret : BitVec 64) :
    (Sym.ptr 0 (-8)).eval (r.envR m extra ret) = r.base - 8#64 := by
  show r.base + BitVec.ofInt 64 (-8) = r.base - 8#64
  rw [show BitVec.ofInt 64 (-8) = -8#64 by decide +kernel, BitVec.sub_eq_add_neg]

/-- **A register the block sets to the frame's byte `o`.** -/
theorem regIs_ptr {m m' : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hm : Match (r.envR m extra ret) S m') {y : Reg64} {o : Nat}
    (h : S.reg y = some (.ptr 0 o)) : Run.RegIs m' y (r.off o) := by
  unfold Run.RegIs reg
  rw [hm.regs y _ h, eval_ptr0]

/-- **A register the block sets to a literal.** -/
theorem regIs_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : Reg64}
    {c : Nat} (h : S.reg y = some (.lit c)) : Run.RegIs m' y (BitVec.ofNat 64 c) := by
  unfold Run.RegIs reg
  rw [hm.regs y _ h]
  rfl

/-- **A register a block keeps** (its symbolic value its own atom). -/
theorem regIs_reg {m m' : MachineData} {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (Env.ofMachine m regions vars ret) S m') {y : Reg64}
    {v : BitVec 64} (h : S.reg y = some (.reg y)) (hv : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs reg at *
  rw [hm.regs y _ h]
  exact hv

/-- A register a block sets to another's atom. -/
theorem regIs_of_reg {m m' : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine m regions vars ret) S m') {y x : Reg64}
    (h : S.reg y = some (.reg x)) {v : BitVec 64} (hv : Run.RegIs m x v) : Run.RegIs m' y v := by
  unfold Run.RegIs reg at *
  rw [hm.regs y _ h]
  exact hv

/-- A register a block sets to a literal: its number. -/
theorem toNat_of_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : Reg64}
    {c : Nat} (h : S.reg y = some (.lit c)) (hc : c < 2 ^ 64) : (reg m' y).toNat = c := by
  unfold reg
  rw [hm.regs y _ h]
  exact Nat.mod_eq_of_lt hc

/-- A register a block sets to `0`, as a byte. -/
theorem byte_zero {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : Reg64}
    (h : S.reg y = some (.lit 0)) : UInt8.ofNat (reg m' y).toNat = 0 := by
  rw [toNat_of_lit hm h (by decide)]
  rfl

/-- A known register that is the frame's byte `o`. -/
theorem known_ptr {m : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} {y : Reg64}
    {o : Nat} (h : Run.RegIs m y (r.off o)) :
    m.regs.get64 y = (Sym.ptr 0 o).eval (r.envR m extra ret) := by
  rw [eval_ptr0]
  exact h

/-- A known register that is a literal. -/
theorem known_lit {m : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} {y : Reg64}
    {c : Nat} (h : Run.RegIs m y (BitVec.ofNat 64 c)) :
    m.regs.get64 y = (Sym.lit c).eval (r.envR m extra ret) := h

/-- **A fresh symbolic state for a state of the frame**: the registers `k`, the extra regions,
bounds and aliases. -/
theorem match_frameS {m : MachineData}
    (hgot : ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        some (byteOf (Labels.label l).toBitVec i))
    (hsp : reg m .rsp = r.base) {extra : List (BitVec 64 × Nat)}
    {sextra : List Nat} (hex : RegionsOk sextra extra) {ret : BitVec 64} {k : List (Reg64 × Sym)}
    (hk : KnownOK r m extra ret k) {bounds : List (Sym × Nat)}
    (hbounds : AllOf (fun p ↦ (p.1.eval (r.envR m extra ret)).toNat < p.2) bounds)
    {aliases : List (Sym × Nat × Int)}
    (haliases : AllOf (fun p ↦ p.1.eval (r.envR m extra ret) =
      (r.envR m extra ret).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Match (r.envR m extra ret) (frameS k sextra bounds aliases) m := by
  apply Match.withKnownBytes
  · apply Match.withKnownBytes
    · apply match_ofMachine
      · exact ⟨rfl, rfl, rfl, rfl, hex⟩
      · exact ⟨by simpa [Sym.eval, Run.envR, Run.env, Env.base] using hsp, hk⟩
      · exact trivial
      · exact hbounds
      · refine ⟨?_, ?_, ?_, haliases⟩
        · change r.base + BitVec.ofInt 64 (-8) = r.base - 8#64 + BitVec.ofInt 64 0
          simp [BitVec.sub_eq_add_neg]
        · simp [Sym.eval, Env.base, gotAddr]
        · simp [Sym.eval, Env.base, gotAddr]
    · intro i hi
      simpa [Sym.eval, Run.envR, Run.env, Env.base] using
        hgot "memcpy" (by simp) i hi
  · intro i hi
    simpa [Sym.eval, Run.envR, Run.env, Env.base] using
      hgot "memset" (by simp) i hi

/-- The frame's environment with extra regions is well formed. -/
theorem envR_wf (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    {extra : List (BitVec 64 × Nat)} (hx : ExtraOK r m extra) (ret : BitVec 64) :
    (r.envR m extra ret).WF := by
  have hc := (r.got hpre).1 "memcpy" (by simp)
  have hs := (r.got hpre).1 "memset" (by simp)
  refine r.env_wf hpre hk (extra := (gotAddr "memcpy", 8) :: (gotAddr "memset", 8) :: extra)
    ⟨⟨fun i hi => hk _ ((r.got hpre).mapped (by simp : "memcpy" ∈ _) i hi), hc.2.1⟩,
      ⟨fun i hi => hk _ ((r.got hpre).mapped (by simp : "memset" ∈ _) i hi), hs.2.1⟩, hx.1⟩
    ⟨r.got_apart_regions hpre (by simp), r.got_apart_regions hpre (by simp), hx.2.1⟩
    ?_ _ ret
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hx.2.2.1)
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · simpa using (r.got hpre).2
    · exact hx.2.2.2 "memcpy" (by simp) e he
  · intro e he
    exact hx.2.2.2 "memset" (by simp) e he

/-- **Slots a call does not change** stay. -/
theorem SlotsAt.of_call (hpre : r.Pre) {m m' : MachineData} (hsp : rspOf m = r.base - 8#64)
    {L : List Slot} (h : SlotsAt r m L) {a n N : Nat} (ha : a + n ≤ 2768) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) (hL : slotsOff L a n = true) :
    SlotsAt r m' L :=
  allOf_imp (fun s hs ⟨hl, ho, hb⟩ ↦ ⟨hl, ho, r.bytesAt_of_call hpre hsp ha hN hout (by omega)
    (by have := slotsOff_spec hL s hs; omega) hb⟩) h

/-- **A call changing frame bytes apart from the slots keeps what the frame keeps.** -/
theorem Keep.of_call (hpre : r.Pre) {L : List Slot} {m m' : MachineData} (hK : CallKeep r L m)
    (hS : Saved m m') (hsp : rspOf m' = rspOf m + 8#64) {a n N : Nat} (ha : a + n ≤ 2712)
    (hN : N ≤ finalizeStack) (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N))
    (hL : slotsOff L a n = true) : Keep r L m' := by
  have hsp' : rspOf m' = r.base := by rw [hsp, hK.1.rsp, r.callSp_add]
  exact ⟨r.frame_of_call hpre hK.1 hS hsp' ha hN hout,
    hK.2.of_call hpre hK.1.rsp (by omega) hN hout hL⟩

/-- **Slots a block does not write** stay. -/
theorem SlotsAt.of_block (hpre : r.Pre) {m m' : MachineData} {extra : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {S : SState} (hm : Match (r.envR m extra ret) S m')
    (hwf : (r.envR m extra ret).WF) {L : List Slot} (h : SlotsAt r m L)
    (hL : slotsKept S L = true) : SlotsAt r m' L :=
  allOf_imp (fun s hs ⟨hl, ho, hb⟩ ↦ ⟨hl, ho, r.bytesAt_kept hpre hm hwf (by omega) hb
    (by rw [hl]; exact slotsKept_spec hL s hs)⟩) h

/-- The frame's invariant after a block run with extra regions, its writes in the frame. -/
theorem frameAt_of_match (hpre : r.Pre) {sp : BitVec 64} {m m' : MachineData}
    (hF : r.FrameAt sp m) {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hm : Match (r.envR m extra ret) S m') (hwf : (r.envR m extra ret).WF) {sp' : BitVec 64}
    (hsp : reg m' .rsp = sp') (hw : Run.frameWrites S = true) : r.FrameAt sp' m' := by
  have hb := r.base_toNat hpre
  have hc := r.callSp_toNat hpre
  refine hF.of_block hsp (hm.sameOutside hwf) ?_ (hm.kept hwf)
  rintro p ⟨w, hwm, b, sz, hr, h1, h2⟩
  simp only [Run.frameWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hoff⟩
  · rw [hw0] at hr
    cases hr
    exact r.inRange_off hpre (a := 0) (n := 2712) (by decide) (by
      have := r.off_toNat hpre (a := 2712) (by decide)
      rw [Run.off_zero, Sym.inRange_iff (by omega)]
      omega)
  · rw [hw1] at hr
    cases hr
    have hs := r.off_toNat hpre (a := 2712) (by decide)
    refine ⟨?_, ?_⟩
    · rw [r.stackArea_iff hpre]
      omega
    · rw [Sym.inRange_iff (by rw [hs]; omega), hs]
      omega

/-- **A block keeping the frame's invariant and missing the slots keeps what the frame keeps**,
RSP the base after it. -/
theorem Keep.of_block (hpre : r.Pre) {L : List Slot} {m m' : MachineData} (hK : Keep r L m)
    {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hm : Match (r.envR m extra ret) S m') (hwf : (r.envR m extra ret).WF)
    (hok : blockOK S 0 = true) (hL : slotsKept S L = true) : Keep r L m' := by
  simp only [blockOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hw, hsp⟩ := hok
  refine ⟨(r.frame_iff m').2 (frameAt_of_match hpre ((r.frame_iff m).1 hK.1) hm hwf ?_ hw),
    hK.2.of_block hpre hm hwf hL⟩
  unfold reg
  rw [hm.regs .rsp _ hsp, show (0 : Int) = ((0 : Nat) : Int) from rfl, eval_ptr0, Run.off_zero]

/-- **A block ending in a call keeps what the frame keeps** at the callee's entry. -/
theorem CallKeep.of_block (hpre : r.Pre) {L : List Slot} {m m' : MachineData} (hK : Keep r L m)
    {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hm : Match (r.envR m extra ret) S m') (hwf : (r.envR m extra ret).WF)
    (hok : blockOK S (-8) = true) (hL : slotsKept S L = true) : CallKeep r L m' := by
  simp only [blockOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hw, hsp⟩ := hok
  refine ⟨frameAt_of_match hpre ((r.frame_iff m).1 hK.1) hm hwf ?_ hw,
    hK.2.of_block hpre hm hwf hL⟩
  unfold reg
  rw [hm.regs .rsp _ hsp, eval_ptr_neg8]

/-- The frame's bytes a block does not write. -/
theorem kb_of_block (hpre : r.Pre) {m m' : MachineData} {extra : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {S : SState} (hm : Match (r.envR m extra ret) S m')
    (hwf : (r.envR m extra ret).WF) : KB r S m m' :=
  fun _ _ ho hn hb ↦ r.bytesAt_kept hpre hm hwf ho hb hn

theorem kc_of_call (hpre : r.Pre) {m₁ m₂ : MachineData} (hsp : rspOf m₁ = r.base - 8#64)
    {a n N : Nat} (ha : a + n ≤ 2768) (hN : N ≤ finalizeStack)
    (hout : SameOutside m₁.dmem m₂.dmem (r.CallOut m₁ a n N)) : KC r m₁ m₂ a n :=
  fun _ _ ho hd h ↦ r.bytesAt_of_call hpre hsp ha hN hout ho hd h

/-! ## The callees from the frame -/

/-- **`memset(a, 0, n)`** from the frame: its precondition, and after it the `n` zeros, what the
frame keeps, the callee-saved registers, the frame's other bytes. -/
theorem memsetFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : CallKeep r L m₁)
    {a n : Nat} (h0 : Run.RegIs m₁ .rdi (r.off a)) (h1 : UInt8.ofNat (reg m₁ .rsi).toNat = 0)
    (h2 : (reg m₁ .rdx).toNat = n) (ha : a + n ≤ 2712) (hL : slotsOff L a n = true) :
    MemsetPre m₁ ∧ ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → MemsetPost m₁ m₂ →
      Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a n ∧
      BytesAt m₂.dmem (r.off a) (List.replicate n 0) := by
  refine ⟨r.memset_pre hpre hK.1 h0 h2 (by omega), fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memset_out h0 h2 hQ
  rw [h1] at hB
  exact ⟨Keep.of_call hpre hK hS hsp ha (by decide) hout hL, hS,
    kc_of_call hpre hK.1.rsp (by omega) (by decide) hout, hB⟩

/-- **`memcpy(a, b, n)`** from the frame, the bytes `bs` at `b`. -/
theorem memcpyFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : CallKeep r L m₁)
    {a b n : Nat} (h0 : Run.RegIs m₁ .rdi (r.off a)) (h1 : Run.RegIs m₁ .rsi (r.off b))
    (h2 : (reg m₁ .rdx).toNat = n) (ha : a + n ≤ 2712) (hb : b + n ≤ 2768)
    (hd : a + n ≤ b ∨ b + n ≤ a) (hL : slotsOff L a n = true) {bs : List UInt8}
    (hl : bs.length = n) (hbs : BytesAt m₁.dmem (r.off b) bs) :
    MemcpyPre m₁ ∧ ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → MemcpyPost m₁ m₂ →
      Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a n ∧ BytesAt m₂.dmem (r.off a) bs := by
  refine ⟨r.memcpy_pre hpre hK.1 h0 h1 h2 (by omega) hb hd, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 hQ
  rw [← hl, bytesOf_of_bytesAt hbs] at hB
  exact ⟨Keep.of_call hpre hK hS hsp ha (by decide) hout hL, hS,
    kc_of_call hpre hK.1.rsp (by omega) (by decide) hout, hB⟩

/-- **`Hasher::update(a, b, n)`** from the frame, the hasher at `a` having absorbed `x`, the
bytes `bs` at `b`. -/
theorem updateFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : CallKeep r L m₁)
    {a b n : Nat} (h0 : Run.RegIs m₁ .rdi (r.off a)) (h1 : Run.RegIs m₁ .rsi (r.off b))
    (h2 : (reg m₁ .rdx).toNat = n) (ha : a + 344 ≤ 2712) (hb : b + n ≤ 2768)
    (hd : a + 344 ≤ b ∨ b + n ≤ a) (hL : slotsOff L a 344 = true) {x bs : List UInt8}
    (hH : HasherAt r m₁ a x) (hl : bs.length = n) (hbs : BytesAt m₁.dmem (r.off b) bs) :
    UpdatePre m₁ ∧ ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → UpdatePost m₁ m₂ →
      Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a 344 ∧ HasherAt r m₂ a (x ++ bs) := by
  refine ⟨r.update_pre hpre hK.1 h0 h1 h2 (by omega) hb hd hH.holds_some, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hA, hout, hS⟩ := r.update_out h0 h1 h2 hQ
  have hK₂ := Keep.of_call hpre hK hS hsp ha (by decide) hout hL
  have hA' := hA x hH.holds
  rw [← hl, bytesOf_of_bytesAt hbs] at hA'
  exact ⟨hK₂, hS, kc_of_call hpre hK.1.rsp (by omega) (by decide) hout,
    ⟨_, bytesAt_bytesOf (r.frame_mapped hpre ((r.frame_iff m₂).1 hK₂.1) (a := a) (n := 344) (by omega)).1, hA'⟩⟩

/-- **`Hasher::update(a, d, n)`** from the frame, the data an input. -/
theorem updateInput (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : CallKeep r L m₁)
    {a n : Nat} {d : BitVec 64} (h0 : Run.RegIs m₁ .rdi (r.off a)) (h1 : Run.RegIs m₁ .rsi d)
    (h2 : (reg m₁ .rdx).toNat = n) (hin : WotsLeafPre.Input r.m0 d n) (ha : a + 344 ≤ 2712)
    (hL : slotsOff L a 344 = true) (hdgot : Apart (gotAddr "memcpy") 8 d n)
    {x : List UInt8} (hH : HasherAt r m₁ a x) :
    UpdatePre m₁ ∧ ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → UpdatePost m₁ m₂ →
      Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a 344 ∧
      HasherAt r m₂ a (x ++ bytesOf r.m0.dmem d n) := by
  have hA8 := r.input_apart hin
  have hdf : Apart (r.off a) 344 d n := by
    have := r.off_toNat hpre (a := a) (by omega)
    have := r.below_toNat hpre
    have := hin.2.2
    unfold Apart at *
    simp only [Run.wotsLeafStack_eq'] at *
    omega
  refine ⟨r.update_pre_input hpre hK.1 h0 h1 h2 (by omega)
    (fun i hi ↦ hK.1.kept _ (hin.1 i hi)) hin.2.1 hA8 hdf hdgot hH.holds_some, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hA, hout, hS⟩ := r.update_out h0 h1 h2 hQ
  have hK₂ := Keep.of_call hpre hK hS hsp ha (by decide) hout hL
  have hA' := hA x hH.holds
  have hbs := r.bytesAt_entry hpre hK.1 (bytesAt_bytesOf hin.1)
    (by rw [length_bytesOf]; exact hA8) (by rw [length_bytesOf]; exact hin.2.1)
  rw [← length_bytesOf r.m0.dmem d n, bytesOf_of_bytesAt hbs] at hA'
  exact ⟨hK₂, hS, kc_of_call hpre hK.1.rsp (by omega) (by decide) hout,
    ⟨_, bytesAt_bytesOf (r.frame_mapped hpre ((r.frame_iff m₂).1 hK₂.1) (a := a) (n := 344) (by omega)).1, hA'⟩⟩

/-- **`Hasher::finalize(o, a)`** from the frame, the hasher at `a` having absorbed `x`. -/
theorem finalizeFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : CallKeep r L m₁)
    {o a : Nat} (h0 : Run.RegIs m₁ .rdi (r.off o)) (h1 : Run.RegIs m₁ .rsi (r.off a))
    (ho : o + 32 ≤ 2712) (ha : a + 344 ≤ 2768) (hd : o + 32 ≤ a ∨ a + 344 ≤ o)
    (hL : slotsOff L o 32 = true) {x : List UInt8} (hH : HasherAt r m₁ a x) :
    FinalizePre m₁ ∧ ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → FinalizePost m₁ m₂ →
      Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ o 32 ∧
      BytesAt m₂.dmem (r.off o) (Keccak.hashBytes x) := by
  refine ⟨r.finalize_pre hpre hK.1 h0 h1 (by omega) ha hd hH.holds_some, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.finalize_out h0 h1 hQ
  rw [Keccak.finalize_eq hH.holds] at hB
  exact ⟨Keep.of_call hpre hK hS hsp ho (by decide) hout hL, hS,
    kc_of_call hpre hK.1.rsp (by omega) (by decide) hout, hB⟩

/-- **`keccak_f(a)`** from the frame, the 200 bytes `st` at `a`. -/
theorem keccakFrame (hpre : r.Pre) {L : List Slot} {m₁ : MachineData} (hK : CallKeep r L m₁)
    {a : Nat} (h0 : Run.RegIs m₁ .rdi (r.off a)) (ha : a + 200 ≤ 2712)
    (hL : slotsOff L a 200 = true) {st : List UInt8} (hl : st.length = 200)
    (hst : BytesAt m₁.dmem (r.off a) st) :
    KeccakFPre m₁ ∧ ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → KeccakFPost m₁ m₂ →
      Keep r L m₂ ∧ Saved m₁ m₂ ∧ KC r m₁ m₂ a 200 ∧
      BytesAt m₂.dmem (r.off a) (Keccak.keccakF st) := by
  refine ⟨r.keccakF_pre hpre hK.1 h0 (by omega), fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.keccakF_out h0 hQ
  rw [← hl, bytesOf_of_bytesAt hst] at hB
  exact ⟨Keep.of_call hpre hK hS hsp ha (by decide) hout hL, hS,
    kc_of_call hpre hK.1.rsp (by omega) (by decide) hout, hB⟩

end

/-! ## Steps -/

section
variable [Host]

/-- **A block of the function** run from directive `j`, then `cont` from where it ends. -/
theorem blk (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) {ds : List Directive}
    {j : Nat} (hb : ds.IsInfixAt Xmss.WotsLeaf.code j) (hne : ds ≠ []) {env : Env}
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WF)
    (hret : env.ret = (r.pc (j + ds.length)).toBitVec) {m : MachineData}
    (hm : Match env S m) {R : MachineState → Prop}
    (cont : ∀ st, Match env S' st.data → PcOk env x (r.pc (j + ds.length)) st →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ :=
  exec_then (hb.trans hp.1 hne) hx hwf
    (fun _ _ ↦ by rw [hret, Run.pc, Nat.add_assoc]) hm fun st h1 h2 ↦
    cont st h1 (by rw [Run.pc, ← Nat.add_assoc]; exact h2)

/-- A state at a known pc. -/
theorem pc_at {R : MachineState → Prop} {st : MachineState} {a : Int64} (h : st.pc = a)
    (k : Eventually (step1 Host.exe) R ⟨st.data, a⟩) :
    Eventually (step1 Host.exe) R st := by
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
    (h : P st.data ∧ ∀ m₂, rspOf m₂ = rspOf st.data + 8#64 → Q st.data m₂ →
      Eventually (step1 Host.exe) R ⟨m₂, next⟩) :
    Eventually (step1 Host.exe) R st :=
  call_then hpc hspec h.1 fun st' hpc' hsp hq ↦ pc_at hpc' (h.2 st'.data hsp hq)

/-- **A block of the frame**: run from `frameS k` with the extra regions, its writes keeping the
frame's invariant and missing the slots; `cont` from where it ends, with what the frame keeps. -/
theorem frameStep (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hb : ds.IsInfixAt Xmss.WotsLeaf.code j) (hne : ds ≠ [])
    {k : List (Reg64 × Sym)} {sextra : List Nat} {bounds : List (Sym × Nat)}
    {aliases : List (Sym × Nat × Int)} {S' : SState} {x : Exit}
    (hx : exec ds (frameS k sextra bounds aliases) = some (S', x))
    (hok : blockOK S' 0 = true) {L : List Slot} (hL : slotsKept S' L = true) {m : MachineData}
    (hK : Keep r L m) {extra : List (BitVec 64 × Nat)} (hex : RegionsOk sextra extra)
    (hxo : ExtraOK r m extra)
    (hk : KnownOK r m extra (r.pc (j + ds.length)).toBitVec k)
    (hbounds : AllOf (fun p ↦ (p.1.eval (r.envR m extra (r.pc (j + ds.length)).toBitVec)).toNat <
      p.2) bounds)
    (haliases : AllOf (fun p ↦ p.1.eval (r.envR m extra (r.pc (j + ds.length)).toBitVec) =
      (r.envR m extra (r.pc (j + ds.length)).toBitVec).base p.2.1 + BitVec.ofInt 64 p.2.2)
      aliases)
    {R : MachineState → Prop}
    (cont : ∀ st, Match (r.envR m extra (r.pc (j + ds.length)).toBitVec) S' st.data →
      Keep r L st.data → KB r S' m st.data →
      PcOk (r.envR m extra (r.pc (j + ds.length)).toBitVec) x (r.pc (j + ds.length)) st →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  have hwf := envR_wf hpre ((r.frame_iff m).1 hK.1).kept hxo (r.pc (j + ds.length)).toBitVec
  exact blk r hp hb hne hx hwf rfl
    (match_frameS (fun _ hl _ hi => r.got_byte hpre hK.1.2.2.1 hl hi) hK.1.1 hex hk hbounds haliases) fun st hm hpc ↦
    cont st hm (hK.of_block hpre hm hwf hok hL) (kb_of_block hpre hm hwf) hpc

/-- **A block of the frame ending in a call**, then the callee's contract. -/
theorem frameCall (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hb : ds.IsInfixAt Xmss.WotsLeaf.code j) (hne : ds ≠ [])
    {k : List (Reg64 × Sym)} {sextra : List Nat} {bounds : List (Sym × Nat)}
    {aliases : List (Sym × Nat × Int)} {S' : SState} {l : Label}
    (hx : exec ds (frameS k sextra bounds aliases) = some (S', .call l))
    (hok : blockOK S' (-8) = true) {L : List Slot} (hL : slotsKept S' L = true)
    {m : MachineData} (hK : Keep r L m) {extra : List (BitVec 64 × Nat)}
    (hex : RegionsOk sextra extra) (hxo : ExtraOK r m extra)
    (hk : KnownOK r m extra (r.pc (j + ds.length)).toBitVec k)
    (hbounds : AllOf (fun p ↦ (p.1.eval (r.envR m extra (r.pc (j + ds.length)).toBitVec)).toNat <
      p.2) bounds)
    (haliases : AllOf (fun p ↦ p.1.eval (r.envR m extra (r.pc (j + ds.length)).toBitVec) =
      (r.envR m extra (r.pc (j + ds.length)).toBitVec).base p.2.1 + BitVec.ofInt 64 p.2.2)
      aliases)
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {R : MachineState → Prop}
    (cont : ∀ m₁, Match (r.envR m extra (r.pc (j + ds.length)).toBitVec) S' m₁ →
      CallKeep r L m₁ → KB r S' m m₁ → P m₁ ∧
      ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → Q m₁ m₂ →
        Eventually (step1 Host.exe) R ⟨m₂, r.pc (j + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  have hwf := envR_wf hpre ((r.frame_iff m).1 hK.1).kept hxo (r.pc (j + ds.length)).toBitVec
  exact blk r hp hb hne hx hwf rfl
    (match_frameS (fun _ hl _ hi => r.got_byte hpre hK.1.2.2.1 hl hi) hK.1.1 hex hk hbounds haliases) fun st hm hpc ↦
    callAt hpc hspec (cont st.data hm (CallKeep.of_block hpre hK hm hwf hok hL)
      (kb_of_block hpre hm hwf))

end

variable [Labels]

/-- The pc after a conditional branch whose condition evaluates to `b`. -/
theorem pc_cond {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) {b : Bool} (hc : c.eval env = b) :
    st.pc = if b then Labels.label l else next := by
  rw [← hc]
  exact h

end

end NativeRustcX64.WotsLeafProof
