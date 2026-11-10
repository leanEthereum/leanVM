import Rv64Verifier.Proofs.Main.NewInv

/-!
# `Bytecode::new`'s blocks: the state inside one, the slots cleared

`BK`: inside block `i` of length `L`, entered with `NEXT` at `Hb`: what the block keeps until it
writes the `Vec`s (`BK.frame`, for writes in `WB`). `GMem`: `group`'s state in memory, the slots
(`SlotsRel`: a tag `u16` and a group `u16` each), `group_of` and `distinct` (the `Vec` at
`msp + 104`). `GH`: the head of `group`'s loop (`0x800005b4`).

`0x80000520` writes a zero tag to each of the `2^15` slots, four bytes apart (`clear_loop`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

theorem valid2_of {a : Word} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat ≤ 0x78000000)
    (h3 : a.toNat % 2 = 0) : Sym.validAccess 2 a = true := by
  simp only [Sym.validAccess, isValidHalfwordAccess, isValidMemAddr_eq, isAligned2, MEM_START,
    MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem validMem_of {a : Word} (h : 0x20 ≤ a.toNat ∧ a.toNat ≤ 0x78000000 ∨
    0xa0000000 ≤ a.toNat ∧ a.toNat ≤ 0xc0000000) : isValidMemAddr a = true := by
  simp only [isValidMemAddr_eq, MEM_START, MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START,
    RAM_MEM_END, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem off0 (w : Word) : w + signExtend12 0 = w := by simp [signExtend12]

/-- Halfwords whose bytes miss a frame are kept. -/
theorem BFrame.half {s t : MachineState} {W : Word → Prop} (h : BFrame s t W) {a : Word}
    (ha : a.toNat % 2 = 0) (h0 : ¬ W a) (h1 : ¬ W (a + 1)) : t.getHalfword a = s.getHalfword a :=
  getHalfword_eq_of_bytes ha (h a h0) (h _ h1)

/-- `0x80000520`: the tags of the slots from `k` on cleared. -/
theorem clear_loop {SL : Word} (hS : SL.toNat % 2 = 0 ∧ 0x20000000 ≤ SL.toNat ∧
    SL.toNat + 0x20000 ≤ 0x78000000) :
    ∀ m k (t : MachineState), k + m = 0x8000 → 0 < m → t.pc = 0x80000520 →
      t.getReg .x10 = SL + BitVec.ofNat 64 (4 * k) → t.getReg .x25 = SL + 0x20000 →
      (∀ j < k, t.getHalfword (SL + BitVec.ofNat 64 (4 * j)) = 0) →
      ∃ v, Reaches Image.code t v ∧ v.pc = 0x8000052c ∧ (∀ r, r ≠ .x10 → v.getReg r = t.getReg r) ∧
        BFrame t v (Within · SL 0x20000) ∧
        ∀ j < 0x8000, v.getHalfword (SL + BitVec.ofNat 64 (4 * j)) = 0 := by
  obtain ⟨hS2, hS1, hS3⟩ := hS
  intro m
  induction m with
  | zero => intro _ _ _ h; omega
  | succ m ih =>
    intro k t hk _ hpc h10 h25 hz
    have hf : Image.code.fetch t.pc = some (.base (.SH .x10 .x0 0)) := by
      rw [hpc]; exact fetch_of (by decide +kernel)
    obtain ⟨u, hu, hpcu, hru, hhu, hfu⟩ := step_sh hf (by
      rw [off0, h10]; exact valid2_of (by addr_omega [hS1, hS3, hk]) (by addr_omega [hS1, hS3, hk])
        (by addr_omega [hS1, hS2, hS3, hk]))
    rw [off0, h10] at hhu hfu
    obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches NB.g80000524_spec (by rw [hpcu, hpc]; rfl) trivial
    have kv := NB.g80000524_keeps hv
    have x10v : v.getReg .x10 = SL + BitVec.ofNat 64 (4 * (k + 1)) := by
      rw [NB.g80000524_x10 hv, hru, h10]
      apply BitVec.eq_of_toNat_eq
      addr_omega [hk, hS3]
    have hzv : ∀ j < k + 1, v.getHalfword (SL + BitVec.ofNat 64 (4 * j)) = 0 := by
      intro j hj
      simp only [MachineState.getHalfword, alignToDword, NB.g80000524_mem_same hv]
      show u.getHalfword _ = 0
      rcases (show j < k ∨ j = k by omega) with hj | rfl
      · rw [BFrame.half hfu.byte (by addr_omega [hS2, hS3, hj, hk]) (fun h ↦ by
            rcases h with h | h <;> have := congrArg BitVec.toNat h <;> addr_omega [this, hj, hk, hS3])
          (fun h ↦ by
            rcases h with h | h <;> have := congrArg BitVec.toNat h <;> addr_omega [this, hj, hk, hS3])]
        exact hz j hj
      · rw [hhu]; rfl
    have hfv : BFrame t v (Within · SL 0x20000) := fun a ha ↦ by
      rw [byteAt_eq, byteAt_eq, NB.g80000524_mem_same hv, ← byteAt_eq, ← byteAt_eq]
      exact hfu.byte a fun h ↦ ha (by rcases h with h | h <;> rw [h] <;> addr_omega [hk, hS1, hS3])
    have hregs : ∀ r, r ≠ .x10 → v.getReg r = t.getReg r := by
      intro r hr
      rw [← hru r]
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | exact absurd rfl hr | exact kv _ (by decide) | rfl
    by_cases hm : m = 0
    · subst hm
      refine ⟨v, (show Reaches Image.code t u from ⟨1, hu⟩).trans rv,
        NB.g80000524_pc_not_taken hv ?_, hregs, hfv, fun j hj ↦ hzv j (by omega)⟩
      rw [hru, hru, h10, h25]
      apply BitVec.eq_of_toNat_eq
      addr_omega [hk, hS3]
    · have hpcv : v.pc = 0x80000520 := NB.g80000524_pc_taken hv (by
        rw [hru, hru, h10, h25]
        intro he
        have := congrArg BitVec.toNat he
        addr_omega [this, hk, hS3, hm])
      obtain ⟨w, rw', hw1, hw2, hw3, hw4⟩ := ih (k + 1) v (by omega) (by omega) hpcv x10v
        (by rw [hregs _ (by decide)]; exact h25) hzv
      refine ⟨w, (show Reaches Image.code t u from ⟨1, hu⟩).trans (rv.trans rw'), hw1,
        fun r hr ↦ (hw2 r hr).trans (hregs r hr), hfv.trans hw3 fun _ h ↦ h, hw4⟩

/-! ## Inside a block -/

/-- The words of block `i`. -/
def blk (words : List Word) (i : Nat) : List Word := ((tbl words).drop (i * 2 ^ 14)).take (2 ^ 14)

/-- The slots from `SL` hold `sl`: an empty slot's tag is zero, an occupied one's not, and its
group follows it. -/
def SlotsRel (t : MachineState) (SL : Word) (sl : List (Option (BitVec 16))) : Prop :=
  ∀ j < 2 ^ 15, (sl.getD j none = none → t.getHalfword (SL + BitVec.ofNat 64 (4 * j)) = 0) ∧
    ∀ g, sl.getD j none = some g → t.getHalfword (SL + BitVec.ofNat 64 (4 * j)) ≠ 0 ∧
      t.getHalfword (SL + BitVec.ofNat 64 (4 * j) + 2) = g

/-- What a block writes before its `Vec`s: four scratch slots, `distinct`'s header and the `Vec` at
`msp + 272`, callees' stacks, `NEXT`, the heap below `H0` and from `Hb` on. -/
@[rv_addr] def WB (H0 Hb : Nat) (a : Word) : Prop :=
  Within a (msp + 24) 16 ∨ Within a (msp + 72) 16 ∨ Within a (msp + 104) 32 ∨
    Within a (msp + 272) 24 ∨ Within a (msp - 4096) 4096 ∨ Within a nextAddr 8 ∨
    (heapStart ≤ a.toNat ∧ a.toNat < H0) ∨ (Hb ≤ a.toNat ∧ a.toNat < heapEnd)

/-- The scratch slots a block reads back: the slots' end, the bump allocator's bound, `group_of`,
the index, the next index and the block's end. -/
structure BMem (u₀ : MachineState) (i L : Nat) (t : MachineState) : Prop where
  m8 : t.getMem (msp + 8) = u₀.getReg .x8 + 0x20000
  m16 : t.getMem (msp + 16) = 0x77fff801
  m40 : t.getMem (msp + 40) = u₀.getReg .x9
  m48 : t.getMem (msp + 48) = BitVec.ofNat 64 i
  m56 : t.getMem (msp + 56) = BitVec.ofNat 64 i + 1
  m64 : t.getMem (msp + 64) = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + L))

/-- Inside block `i` of length `L`, entered with `NEXT` at `Hb` and `newRust`'s state `st`. -/
structure BK (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (t : MachineState) : Prop where
  a : NewA s words u₀
  lt : 2 ^ 14 * i < (words.getD 0 0).toNat
  hL : L = min ((words.getD 0 0).toNat - 2 ^ 14 * i) (2 ^ 14)
  fold : foldNew (tbl words) i = some st
  slotsLen : st.slots.length = 2 ^ 15
  hb0 : heapNext u₀ ≤ Hb
  ng : NG u₀ t
  hb : Hb ≤ heapNext t
  bm : BMem u₀ i L t

theorem BK.frame {s : MachineState} {words : List Word} {u₀ t t' : MachineState} {i L Hb : Nat}
    {st : Model.NewState} {W : Word → Prop} (h : BK s words u₀ i L Hb st t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → WB (heapNext u₀) Hb a) (hsp : t'.getReg .x2 = msp) (hheap : HeapOk t')
    (hmono : heapNext t ≤ heapNext t') : BK s words u₀ i L Hb st t' := by
  have hhi := h.ng.heap.hi
  have hm0 := h.ng.mono
  have hlo0 := h.a.inv.heap.lo
  have hb0 := h.hb0
  simp only [heapEnd, heapNext, heapStart] at hhi hm0 hlo0 hb0
  have hW' : ∀ a, W a → Wg a := by
    intro a ha
    rcases hW a ha with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by addr_omega [h1])
    · exact Or.inl (by addr_omega [h1])
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [h1])))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, ?_⟩)))))
      simp only [heapNext, heapEnd] at h2 ⊢; omega
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, h2⟩)))))
      simp only [heapStart] at h1 ⊢; omega
  have K : ∀ c : Nat, c % 8 = 0 → (8 ≤ c ∧ c + 8 ≤ 24 ∨ 40 ≤ c ∧ c + 8 ≤ 72) →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun j hj hw ↦ ?_
    rcases hW _ hw with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · simp only [heapNext] at h2; rcases hc with hc | hc <;> addr_omega [h2, hj, hc, hm0, hhi]
    · simp only [heapEnd] at h2; rcases hc with hc | hc <;> addr_omega [h2, hj, hc]
  have bm := h.bm
  exact ⟨h.a, h.lt, h.hL, h.fold, h.slotsLen, h.hb0, h.ng.step hf hW' hsp hheap hmono,
    le_trans h.hb hmono,
    ⟨(K 8 (by decide) (by decide)).trans bm.m8, (K 16 (by decide) (by decide)).trans bm.m16,
      (K 40 (by decide) (by decide)).trans bm.m40, (K 48 (by decide) (by decide)).trans bm.m48,
      (K 56 (by decide) (by decide)).trans bm.m56, (K 64 (by decide) (by decide)).trans bm.m64⟩⟩

/-- `group`'s state: the slots, `group_of` and the distinct words. -/
abbrev GrpSt := List (Option (BitVec 16)) × List (BitVec 16) × List (BitVec 64)

/-- `group`'s fold over block `i`'s first `q` positions. -/
def gfold (words : List Word) (i : Nat) (st : Model.NewState) (q : Nat) : Option GrpSt :=
  (List.range q).foldl (Model.groupStepRust (blk words i))
    (some (st.slots.map fun _ ↦ none, st.groupOf, []))

/-- `group`'s state `g` in memory: the slots at `NewA`'s `s0`, `group_of` at its `s1`, `distinct`
the `Vec` at `msp + 104`, its buffer allocated from `Hb` on. -/
structure GMem (u₀ : MachineState) (Hb : Nat) (g : GrpSt) (t : MachineState) : Prop where
  slots : SlotsRel t (u₀.getReg .x8) g.1
  groupOf : halvesAt t (u₀.getReg .x9) 0x4000 = g.2.1
  len : t.getMem (msp + 120) = BitVec.ofNat 64 g.2.2.length
  cap : g.2.2.length ≤ (t.getMem (msp + 104)).toNat
  al : (t.getMem (msp + 112)).toNat % 8 = 0
  buf : (t.getMem (msp + 104)).toNat * 8 = 0 ∨ Hb ≤ (t.getMem (msp + 112)).toNat ∧
    (t.getMem (msp + 112)).toNat + (t.getMem (msp + 104)).toNat * 8 ≤ heapNext t
  dist : t.readWords (t.getMem (msp + 112)) g.2.2.length = g.2.2

/-- In `group`'s loop at position `q` of block `i`, its state `g` in memory. -/
structure GS (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (q : Nat) (g : GrpSt) (t : MachineState) : Prop where
  k : BK s words u₀ i L Hb st t
  vecs : VecsAt t st
  bufs : VecBufs t (heapNext u₀) Hb
  mem : GMem u₀ Hb g t
  hq : q ≤ L
  x8 : t.getReg .x8 = u₀.getReg .x8
  x9 : t.getReg .x9 = BitVec.ofNat 64 q
  x10 : t.getReg .x10 = t.getMem (msp + 112)
  x15 : t.getReg .x15 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + L))
  x16 : t.getReg .x16 = u₀.getReg .x9
  x18 : t.getReg .x18 = BitVec.ofNat 64 g.2.2.length
  x20 : t.getReg .x20 = BitVec.ofNat 64 (8 * L)
  x21 : t.getReg .x21 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i))
  x22 : t.getReg .x22 = 32768
  x23 : t.getReg .x23 = u₀.getReg .x9
  x24 : t.getReg .x24 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + q))
  x25 : t.getReg .x25 = u₀.getReg .x8 + 0x20000
  x26 : t.getReg .x26 = BitVec.ofNat 64 ((words.getD 0 0).toNat - 2 ^ 14 * i - L)
  x27 : t.getReg .x27 = 1

/-- At `0x800005b4`, the head of `group`'s loop, at position `q`. -/
structure GH (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (q : Nat) (g : GrpSt) (t : MachineState) : Prop where
  gs : GS s words u₀ i L Hb st q g t
  pc : t.pc = 0x800005b4
  fold : gfold words i st q = some g
  lt : q < L

end Rv64Verifier.Proofs.Main
