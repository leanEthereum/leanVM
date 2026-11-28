module

public import NativeRustcVmX64.Keccak.Common
public import NativeRustcVm.Keccak.Words

/-!
# `keccak256_words` (x86-64): its frame, and what holds between its blocks

Both instances (`hash_words`'s closure, `fiat_shamir_iv`'s) push six registers and lower RSP by
232. The frame (`frame`, region 0 of every block, 296 bytes from 288 below the entry's RSP): a
callee's return address (offset 0), the function's slots (16 to 39), the 25 lanes (40 to 239),
the pushed registers (RBX at 240, R12, R13, R14, R15, RBP at 280) and the return address (288).
In the body RSP is `frame + 8`, at a call `frame`.

`Ctx m0 L R o m`, from the entry's state `m0`: RSP `frame + o`; the registers `R` and the slots
`L` (below the lanes) hold their values; the pushed registers are the entry's; memory is the
entry's outside the stack the function uses; every mapped byte stays mapped. `Lanes m0 d f`: the
lanes hold `f`. `pre A w B j`: the lanes `A` with the words `w (B + i)` XORed into the first `j`.

`ctx_step` carries `Ctx` over a block whose writes are a callee's return address and lanes
(`bodyW`), `lanes_of` the lanes, `call_kf` over a call of `keccak_f` on the lanes.
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep same_region)

@[expose] public section

/-- The frame's base: 288 bytes below the entry's RSP. -/
def frame (m0 : MachineData) : BitVec 64 := rspOf m0 - BitVec.ofNat 64 288

/-- The registers hold their values. -/
def RegsAt (m : MachineData) (R : List (Reg64 × BitVec 64)) : Prop :=
  AllOf (fun p : Reg64 × BitVec 64 => m.regs.get64 p.1 = p.2) R

/-- The frame's slots hold their words. -/
def SlotsAt (m0 : MachineData) (d : DataMem) (L : List (Nat × BitVec 64)) : Prop :=
  AllOf (fun p : Nat × BitVec 64 => WordAt d (frame m0 + BitVec.ofNat 64 p.1) p.2) L

/-- The slots of the pushed registers. -/
def savedSlots (m0 : MachineData) : List (Nat × BitVec 64) :=
  [(240, m0.regs.get64 .rbx), (248, m0.regs.get64 .r12), (256, m0.regs.get64 .r13),
    (264, m0.regs.get64 .r14), (272, m0.regs.get64 .r15), (280, m0.regs.get64 .rbp)]

/-- The slots are past a callee's return address and below the lanes. -/
def LowSlots (L : List (Nat × BitVec 64)) : Prop :=
  AllOf (fun p : Nat × BitVec 64 => 8 ≤ p.1 ∧ p.1 + 8 ≤ 40) L

/-- The 25 lanes at the frame's byte 40 hold `f`. -/
def Lanes (m0 : MachineData) (d : DataMem) (f : Nat → UInt64) : Prop :=
  ∀ i < 25, WordAt d (frame m0 + BitVec.ofNat 64 (40 + 8 * i)) (f i).toBitVec

/-- The lanes `A` with the words `w (base + i)` XORed into the first `j`. -/
def pre (A : KeccakState) (w : Nat → UInt64) (base j : Nat) (i : Nat) : UInt64 :=
  if i < j then Keccak.lane A i ^^^ w (base + i) else Keccak.lane A i

/-- A write of a block of the body: in the frame, a callee's return address or in the lanes. -/
def bodyW (w : Write) : Bool :=
  w.r == 0 && (decide (w.off + w.n ≤ 8) || (decide (40 ≤ w.off) && decide (w.off + w.n ≤ 240)))

/-- The registers keep their values. -/
def keepsRegs (S : SState) (rs : List Reg64) : Bool := rs.all fun r => S.reg r == some (.reg r)

/-- **What holds throughout the body**, RSP at the frame's offset `o`. -/
structure Ctx (m0 : MachineData) (L : List (Nat × BitVec 64)) (R : List (Reg64 × BitVec 64))
    (o : Nat) (m : MachineData) : Prop where
  rsp : rspOf m = frame m0 + BitVec.ofNat 64 o
  regs : RegsAt m R
  slots : SlotsAt m0 m.dmem L
  saved : SlotsAt m0 m.dmem (savedSlots m0)
  same : SameOutside m0.dmem m.dmem (InRange (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
    NativeRustcVmX64.keccak256WordsStack)
  kept : Kept m0.dmem m.dmem

end

public section

theorem stk_eq : NativeRustcVmX64.keccak256WordsStack = 768 := rfl

theorem bv_sub_toNat {a : BitVec 64} {n : Nat} (h : n ≤ a.toNat) :
    (a - BitVec.ofNat 64 n).toNat = a.toNat - n := by
  have := a.isLt
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn]; exact h), hn]

/-- The numbers of the stack. -/
theorem stack_facts {m0 : MachineData} (h : StackOk m0 NativeRustcVmX64.keccak256WordsStack) :
    (frame m0).toNat + 288 = (rspOf m0).toNat ∧
      (stackBelow m0 768).toNat + 768 = (rspOf m0).toNat ∧
      768 ≤ (rspOf m0).toNat ∧ (rspOf m0).toNat + 8 ≤ 2 ^ 64 := by
  rw [stk_eq] at h
  have h1 := h.1
  have h2 := h.2.1
  refine ⟨?_, ?_, h1, h2⟩
  · rw [frame, bv_sub_toNat (by omega)]; omega
  · rw [stackBelow, bv_sub_toNat (by omega)]; omega

theorem frame_noWrap {m0 : MachineData} (h : StackOk m0 NativeRustcVmX64.keccak256WordsStack) :
    NoWrap (frame m0) 296 := by
  have := stack_facts h
  unfold NoWrap
  omega

theorem frame_add (m0 : MachineData) : frame m0 + BitVec.ofNat 64 288 = rspOf m0 :=
  BitVec.sub_add_cancel _ _

theorem frame_add_toNat {m0 : MachineData} (h : StackOk m0 NativeRustcVmX64.keccak256WordsStack)
    {o : Nat} (ho : o < 296) : (frame m0 + BitVec.ofNat 64 o).toNat = (frame m0).toNat + o := by
  have := stack_facts h
  exact Hasher.toNat_add_ofNat' (by omega)

/-- The frame is mapped. -/
theorem frame_mapped {m0 : MachineData} (h : StackOk m0 NativeRustcVmX64.keccak256WordsStack)
    {d : DataMem} (hk : Kept m0.dmem d) : Mapped d (frame m0) 296 := by
  intro i hi
  have hs := stack_facts h
  rw [stk_eq] at h
  have e : frame m0 + BitVec.ofNat 64 i =
      stackBelow m0 768 + BitVec.ofNat 64 (480 + i) := by
    apply BitVec.eq_of_toNat_eq
    rw [frame_add_toNat h (by omega), Hasher.toNat_add_ofNat' (by omega)]
    omega
  rw [e]
  exact hk _ (h.2.2 _ (by omega))

/-- The frame below the pushed registers' end is in the stack the function uses. -/
theorem inStack_of_frame {m0 : MachineData} (h : StackOk m0 NativeRustcVmX64.keccak256WordsStack)
    {n : Nat} (hn : n ≤ 288) {p : BitVec 64} (hp : InRange (frame m0) n p) :
    InRange (stackBelow m0 NativeRustcVmX64.keccak256WordsStack)
      NativeRustcVmX64.keccak256WordsStack p := by
  have hs := stack_facts h
  rw [inRange_iff (by omega)] at hp
  rw [stk_eq, inRange_iff (by omega)]
  omega

theorem firstOverlap_none_of {r o n : Nat} {ws : List Write}
    (h : ∀ w ∈ ws, w.r = r → w.off + w.n ≤ o ∨ o + n ≤ w.off) : firstOverlap r o n ws = none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [firstOverlap]
    split
    · rename_i hc
      have := h w List.mem_cons_self hc.1
      omega
    · exact ih fun w' hw' => h w' (List.mem_cons_of_mem _ hw')

theorem bodyW_iff {w : Write} :
    bodyW w = true ↔ w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 40 ≤ w.off ∧ w.off + w.n ≤ 240) := by
  simp [bodyW]

theorem allOf_imp {α : Type} {P Q : α → Prop} {l : List α} (h : ∀ a ∈ l, P a → Q a)
    (hl : AllOf P l) : AllOf Q l := NativeRustcX64.KeccakF.allOf_imp h hl

theorem allOf_imp2 {α : Type} {P Q T : α → Prop} {l : List α} (h : ∀ a ∈ l, P a → Q a → T a)
    (hp : AllOf P l) (hq : AllOf Q l) : AllOf T l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    exact ⟨h a List.mem_cons_self hp.1 hq.1,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb)) hp.2 hq.2⟩

theorem lowSlots_cons {o : Nat} {v : BitVec 64} {L : List (Nat × BitVec 64)}
    (h : 8 ≤ o ∧ o + 8 ≤ 40) (hL : LowSlots L) : LowSlots ((o, v) :: L) := ⟨h, hL⟩

theorem Ctx.withRegs {m0 : MachineData} {L R R' o m} (hc : Ctx m0 L R o m) (h : RegsAt m R') :
    Ctx m0 L R' o m := { hc with regs := h }

variable [Labels] {env : Env} {S : SState}

/-- **The registers a block keeps.** -/
theorem regsAt_keep {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hm : Match (Env.ofMachine m rs vars ret) S m') {R : List (Reg64 × BitVec 64)}
    (hR : RegsAt m R) {names : List Reg64} (hn : R.map Prod.fst = names)
    (hk : keepsRegs S names = true) : RegsAt m' R := by
  subst hn
  unfold keepsRegs at hk
  induction R with
  | nil => trivial
  | cons p R ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hk
    exact ⟨(hm.regs p.1 _ hk.1).trans hR.1, ih hR.2 hk.2⟩

omit [Labels] in
/-- A register whose value a block computes. -/
theorem regsAt_cons {m : MachineData} {r : Reg64} {v : BitVec 64} {R : List (Reg64 × BitVec 64)}
    (h : m.regs.get64 r = v) (hR : RegsAt m R) : RegsAt m ((r, v) :: R) := ⟨h, hR⟩

/-- RSP after a block, at the frame's offset `o`. -/
theorem rsp_of {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hm : Match (Env.ofMachine m rs vars ret) S m')
    (hb : rs[0]? = some (frame m0, 296)) {o : Nat} (h : S.reg .rsp = some (.ptr 0 o)) :
    rspOf m' = frame m0 + BitVec.ofNat 64 o := by
  rw [rspOf, hm.regs .rsp _ h]
  simp only [Sym.eval, Env.base_ofMachine_eq, hb, Option.map_some, Option.getD_some,
    BitVec.ofInt_natCast]

omit [Labels] in
/-- **The registers a call keeps**: callee-saved ones. -/
theorem regsAt_saved {m m' : MachineData} {R : List (Reg64 × BitVec 64)} (hR : RegsAt m R)
    (hs : ∀ r, calleeSaved r = true → m'.regs.get64 r = m.regs.get64 r)
    {names : List Reg64} (hn : R.map Prod.fst = names) (hcs : names.all calleeSaved = true) :
    RegsAt m' R := by
  subst hn
  induction R with
  | nil => trivial
  | cons p R ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hcs
    exact ⟨(hs p.1 hcs.1).trans hR.1, ih hR.2 hcs.2⟩

/-- **Slots kept** by a block with no write over them. -/
theorem slotsAt_keep {m0 m : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 296)) {L : List (Nat × BitVec 64)}
    (hL : AllOf (fun p : Nat × BitVec 64 => p.1 + 8 ≤ 296 ∧ firstOverlap 0 p.1 8 S.mem = none) L)
    (h : SlotsAt m0 env.mem0 L) : SlotsAt m0 m.dmem L :=
  allOf_imp2 (fun _ _ h1 h2 => wordAt_keep hm hb h1.1 h1.2 h2) hL h

/-- **`Ctx` after a block** whose writes are in the frame, a callee's return address or lanes. -/
theorem ctx_step {m0 m m' : MachineData} (hstk : StackOk m0 NativeRustcVmX64.keccak256WordsStack)
    {L : List (Nat × BitVec 64)} (hL : LowSlots L) {R R' : List (Reg64 × BitVec 64)} {o o' : Nat}
    (hc : Ctx m0 L R o m) {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hm : Match (Env.ofMachine m rs vars ret) S m') (hwf : (Env.ofMachine m rs vars ret).WF)
    (hb : rs[0]? = some (frame m0, 296)) (hrsp : S.reg .rsp = some (.ptr 0 o'))
    (hall : S.mem.all bodyW = true) (hR : RegsAt m' R') : Ctx m0 L R' o' m' := by
  have hb' : (Env.ofMachine m rs vars ret).regions[0]? = some (frame m0, 296) := hb
  have hw : ∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 40 ≤ w.off ∧ w.off + w.n ≤ 240) :=
    fun w hw => bodyW_iff.mp (List.all_eq_true.mp hall w hw)
  have hfo : ∀ q : Nat, (8 ≤ q ∧ q + 8 ≤ 40) ∨ 240 ≤ q → firstOverlap 0 q 8 S.mem = none :=
    fun q hq => firstOverlap_none_of fun w hw' _ => by have := hw w hw'; omega
  refine ⟨rsp_of hm hb hrsp, hR, ?_, ?_, ?_, fun p h => hm.kept hwf p (hc.kept p h)⟩
  · refine slotsAt_keep hm hb' (allOf_imp (fun p _ hp => ⟨by omega, hfo p.1 (.inl hp)⟩) hL)
      hc.slots
  · have hs := hc.saved
    simp only [SlotsAt, savedSlots, AllOf] at hs ⊢
    obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hs
    exact ⟨wordAt_keep hm hb' (by decide) (hfo _ (.inr (by decide))) s0,
      wordAt_keep hm hb' (by decide) (hfo _ (.inr (by decide))) s1,
      wordAt_keep hm hb' (by decide) (hfo _ (.inr (by decide))) s2,
      wordAt_keep hm hb' (by decide) (hfo _ (.inr (by decide))) s3,
      wordAt_keep hm hb' (by decide) (hfo _ (.inr (by decide))) s4,
      wordAt_keep hm hb' (by decide) (hfo _ (.inr (by decide))) s5, trivial⟩
  · intro p hp
    refine (same_region hm hwf hb' (lim := 240) (fun w hw' => ⟨(hw w hw').1, by
      have := hw w hw'; omega⟩) (by decide) p fun h => hp (inStack_of_frame hstk (by decide) h)).trans
      (hc.same p hp)

/-- **The lanes after a block**: each kept or written. -/
theorem lanes_of {m0 m : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 296)) {f g : Nat → UInt64}
    (h : ∀ i < 25, (firstOverlap 0 (40 + 8 * i) 8 S.mem = none ∧ g i = f i) ∨
      ∃ v, firstOverlap 0 (40 + 8 * i) 8 S.mem = some ⟨0, 40 + 8 * i, 8, v⟩ ∧
        v.eval env = (g i).toBitVec)
    (hl : Lanes m0 env.mem0 f) : Lanes m0 m.dmem g := by
  intro i hi
  rcases h i hi with ⟨hn, he⟩ | ⟨v, hv, he⟩
  · rw [he]
    exact wordAt_keep hm hb (by omega) hn (hl i hi)
  · exact wordAt_of_eq (wordAt_write hm hb (by omega) hv) he

/-- A write of a block that writes lane `j`, or below the lanes. -/
@[expose] def laneW (j : Nat) (w : Write) : Bool :=
  w.r != 0 || decide (w.off + w.n ≤ 40) || (w.off == 40 + 8 * j && w.n == 8)

/-- The lanes after a block that writes none. -/
theorem lanes_keep {m0 m : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 296))
    (h : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ 40) {f : Nat → UInt64}
    (hl : Lanes m0 env.mem0 f) : Lanes m0 m.dmem f :=
  lanes_of hm hb (fun i _ => .inl ⟨firstOverlap_none_of fun w hw hr => by
    have := h w hw hr; omega, rfl⟩) hl

/-- **The lanes after a block that writes lane `j`**, the newest write over it. -/
theorem lanes_step {m0 m : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 296)) {j : Nat} {v : Sym}
    (hj : firstOverlap 0 (40 + 8 * j) 8 S.mem = some ⟨0, 40 + 8 * j, 8, v⟩)
    (hk : ∀ w ∈ S.mem, w.r = 0 → (w.off + w.n ≤ 40 ∨ w.off = 40 + 8 * j ∧ w.n = 8))
    {f : Nat → UInt64} (hl : Lanes m0 env.mem0 f) {x : UInt64} (hv : v.eval env = x.toBitVec) :
    Lanes m0 m.dmem (fun i => if i = j then x else f i) := by
  refine lanes_of hm hb (fun i hi => ?_) hl
  by_cases h : i = j
  · subst h
    exact .inr ⟨v, hj, by simp only [↓reduceIte]; exact hv⟩
  · refine .inl ⟨firstOverlap_none_of fun w hw hr => ?_, by simp [h]⟩
    rcases hk w hw hr with h1 | ⟨h1, h2⟩
    · omega
    · omega

/-- `lanes_step`, the writes checked by `laneW`. -/
theorem lanes_stepB {m0 m : MachineData} (hm : Match env S m)
    (hb : env.regions[0]? = some (frame m0, 296)) {j : Nat} {v : Sym}
    (hj : firstOverlap 0 (40 + 8 * j) 8 S.mem = some ⟨0, 40 + 8 * j, 8, v⟩)
    (hk : S.mem.all (laneW j) = true)
    {f : Nat → UInt64} (hl : Lanes m0 env.mem0 f) {x : UInt64} (hv : v.eval env = x.toBitVec) :
    Lanes m0 m.dmem (fun i => if i = j then x else f i) :=
  lanes_step hm hb hj (fun w hw hr => by
    have := List.all_eq_true.mp hk w hw
    simp only [laneW, hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true, beq_iff_eq] at this
    exact this) hl hv

omit [Labels] in
theorem pre_zero (A : KeccakState) (w : Nat → UInt64) (base : Nat) :
    pre A w base 0 = Keccak.lane A := by
  funext i
  simp [pre]

omit [Labels] in
theorem pre_succ (A : KeccakState) (w : Nat → UInt64) (base j : Nat) :
    (fun i => if i = j then Keccak.lane A j ^^^ w (base + j) else pre A w base j i) =
      pre A w base (j + 1) := by
  funext i
  unfold pre
  by_cases h : i = j
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    by_cases h' : i < j
    · simp [h', show i < j + 1 by omega]
    · simp [h', show ¬ i < j + 1 by omega]

omit [Labels] in
theorem pre_17 (A : KeccakState) (w : Nat → UInt64) (base : Nat) {i : Nat} (hi : i < 25) :
    pre A w base 17 i = Keccak.lane (Native.Keccak.Proof.xorRate A fun k => w (base + k)) i := by
  rw [Native.Keccak.Proof.lane_xorRate _ _ hi, pre]

omit [Labels] in
theorem lanes_congr {m0 : MachineData} {d : DataMem} {f g : Nat → UInt64} (h : Lanes m0 d f)
    (hfg : ∀ i < 25, f i = g i) : Lanes m0 d g := fun i hi => hfg i hi ▸ h i hi

omit [Labels] in
/-- The frame as region 0 of a block's environment. -/
theorem frame_wf {m0 m : MachineData} (hstk : StackOk m0 NativeRustcVmX64.keccak256WordsStack)
    (hk : Kept m0.dmem m.dmem) {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (Env.ofMachine m [(frame m0, 296)] vars ret).WF :=
  Env.wf_of ⟨⟨frame_mapped hstk hk, frame_noWrap hstk⟩, trivial⟩ (List.pairwise_singleton _ _)

/-- RSP at the frame's offset `o`, as a symbolic value. -/
theorem rsp_eval {m0 m : MachineData} {o : Nat} (h : rspOf m = frame m0 + BitVec.ofNat 64 o)
    {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hb : rs[0]? = some (frame m0, 296)) :
    m.regs.get64 .rsp = (Sym.ptr 0 o).eval (Env.ofMachine m rs vars ret) := by
  rw [← rspOf, h]
  simp only [Sym.eval, Env.base_ofMachine_eq, hb, Option.map_some, Option.getD_some,
    BitVec.ofInt_natCast]

end

end NativeRustcVmX64.WordsHash
