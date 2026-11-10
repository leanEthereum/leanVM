import Rv64Verifier.Proofs.Main.NewHead
import Rv64Verifier.Proofs.Main.NewBlocks
import Rv64Verifier.Proofs.Bytecode.Bits

/-!
# `Bytecode::new`'s loop: what it keeps

`NG u₀ t`: from `NewA`'s `u₀` to `t`, memory changed only in `Wg` (`main`'s scratch slots but the
table's length and the input slice, the `Vec`s' headers, callees' stacks, `NEXT` and the heap);
then `MInv`, the table's length, the input slice and the IV are as at `u₀`. `VecIn`: a `Vec` whose
buffer is allocated from a bound on; `VecsAt`: the four `Vec`s holding a `NewState`'s. `NewL`: the
state at the head of the blocks' loop (`0x80000518`), `newRust`'s fold after `i` blocks.

`step_sh` stores a halfword at any even address, which the executor does only at an 8-aligned base.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-! ## Halfword stores -/

theorem getLsbD_65535 (i : Nat) : (65535#64).getLsbD i = decide (i < 16) := by
  rw [BitVec.getLsbD_ofNat, show (65535 : Nat) = 2 ^ 16 - 1 by rfl, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 16 <;> simp [h]; omega

theorem extractHalfword_replaceHalfword (w : Word) {p : Nat} (h : BitVec 16) (hp : p < 4) :
    extractHalfword (replaceHalfword w p h) p = h := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h64 : p * 16 + k < 64 := by omega
  simp only [extractHalfword, replaceHalfword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hk, h64, decide_true, Bool.true_and, getLsbD_65535]
  simp [hk, h64, show k < 64 by omega]

theorem extractByte_replaceHalfword (w : Word) {p q : Nat} (h : BitVec 16) (hq : q < 8)
    (hne : q / 2 ≠ p) : extractByte (replaceHalfword w p h) q = extractByte w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h64 : q * 8 + k < 64 := by omega
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hk, h64, decide_true, Bool.true_and, getLsbD_65535]
  by_cases h1 : q * 8 + k < p * 16
  · simp [h1]
  · have h2 : ¬ (q * 8 + k - p * 16 < 16) := by omega
    simp [h1, h2, BitVec.getLsbD_of_ge h _ (Nat.le_of_not_lt h2)]

/-- `SH rs2, off(rs1)` at an even address: the halfword there becomes `rs2`'s low half, and no
other byte changes. -/
theorem step_sh {code : Code} {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hf : code.fetch s.pc = some (.base (.SH rs1 rs2 off)))
    (hv : Sym.validAccess 2 (s.getReg rs1 + signExtend12 off) = true) :
    ∃ t, Steps code 1 s t ∧ t.pc = s.pc + 4 ∧ (∀ r, t.getReg r = s.getReg r) ∧
      t.getHalfword (s.getReg rs1 + signExtend12 off) = (s.getReg rs2).truncate 16 ∧
      ByteFrame s t (fun a ↦ a = s.getReg rs1 + signExtend12 off ∨
        a = s.getReg rs1 + signExtend12 off + 1) := by
  set p := s.getReg rs1 + signExtend12 off with hp'
  obtain ⟨u, hu, hpc, hr, hm⟩ := step_micro (m := .store .h rs1 rs2 (signExtend12 off)) hf rfl
    (by simp only [Sym.Micro.exec, Sym.StoreKind.width, ← hp', hv, ↓reduceIte]; rfl)
  have hm' : ∀ a, u.getMem a = (s.setHalfword p ((s.getReg rs2).truncate 16)).getMem a := by
    intro a; rw [hm]; rfl
  have h2 : p.toNat % 2 = 0 := by
    simp only [Sym.validAccess, isValidHalfwordAccess, isAligned2, Bool.and_eq_true,
      beq_iff_eq] at hv
    exact hv.2
  have hb : byteOffset p = p.toNat % 8 := toNat_and7 p
  have hset : ∀ a, (s.setHalfword p ((s.getReg rs2).truncate 16)).getMem a =
      if a = p &&& ~~~7#64 then replaceHalfword (s.getMem (p &&& ~~~7#64)) (p.toNat % 8 / 2)
        ((s.getReg rs2).truncate 16) else s.getMem a := by
    intro a
    simp only [MachineState.setHalfword, alignToDword, hb]
    split
    · rename_i h; rw [h, MachineState.getMem_setMem_eq]
    · rename_i h; exact MachineState.getMem_setMem_ne h
  refine ⟨u, hu, by rw [hpc]; rfl, fun r ↦ by rw [hr]; rfl, ?_, ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩⟩
  · simp only [MachineState.getHalfword, alignToDword, byteOffset, toNat_and7, hm', hset,
      ↓reduceIte]
    exact extractHalfword_replaceHalfword _ _ (by omega)
  · simp only [not_or] at ha
    rw [byteAt_eq, byteAt_eq, hm', hset]
    split
    · rename_i hd
      rw [hd]
      have h1 := congrArg BitVec.toNat hd
      rw [toNat_alignDown, toNat_alignDown] at h1
      refine extractByte_replaceHalfword _ _ (by omega) fun he ↦ ?_
      have hpw := p.isLt
      have haw := a.isLt
      rcases (show a.toNat % 8 = p.toNat % 8 ∨ a.toNat % 8 = p.toNat % 8 + 1 by omega) with e | e
      · exact ha.1 (BitVec.eq_of_toNat_eq (by omega))
      · refine ha.2 (BitVec.eq_of_toNat_eq ?_)
        rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]
        omega
    · rfl
  · have hne : a ≠ p &&& ~~~7#64 := fun h ↦ ha (by rw [h, toNat_alignDown]; omega)
    rw [hm', hset]
    simp only [hne, ↓reduceIte]

/-- A halfword is its two bytes. -/
theorem getHalfword_eq_append {s : MachineState} {a : Word} (ha : a.toNat % 2 = 0) :
    s.getHalfword a = byteAt s (a + 1) ++ byteAt s a := by
  have hb (j : Nat) (hj : j < 16) :
      (s.getHalfword a).getLsbD j = (byteAt s (a + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
    have hal : (a + BitVec.ofNat 64 (j / 8)) &&& ~~~7#64 = a &&& ~~~7#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_alignDown, toNat_alignDown, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := a.isLt
      by_cases hw : a.toNat + j / 8 < 2 ^ 64
      · rw [Nat.mod_eq_of_lt (by omega : j / 8 < 2 ^ 64), Nat.mod_eq_of_lt hw]; omega
      · omega
    have hoff : ((a + BitVec.ofNat 64 (j / 8)).toNat % 8) = a.toNat % 8 + j / 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := a.isLt
      rw [Nat.mod_eq_of_lt (by omega : j / 8 < 2 ^ 64)]
      omega
    rw [byteAt_eq, hal, hoff]
    simp only [MachineState.getHalfword, extractHalfword, extractByte, alignToDword, byteOffset,
      toNat_and7, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    simp only [hj, decide_true, Bool.true_and, show j % 8 < 8 from Nat.mod_lt _ (by decide)]
    congr 1
    omega
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [hb j hj, BitVec.getLsbD_append]
  by_cases h8 : j < 8
  · simp only [h8, show j / 8 = 0 by omega, BitVec.add_zero, Nat.mod_eq_of_lt h8, ite_true]
  · simp only [h8, show j / 8 = 1 by omega, ite_false]
    rw [show j % 8 = j - 8 by omega]
    rfl

/-! ## Frames of blocks -/

/-- A block whose writes are doublewords at `msp + c`, `c ∈ cs`, changes no byte outside them. -/
theorem holds_slots {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t)
    (hsp : s.getReg .x2 = msp) (cs : List Nat)
    (hw : (x.writes.all fun k ↦ (match k.base with
      | some e => Sym.E.beq e (.reg .x2)
      | none => false) && cs.contains k.off.toNat) = true)
    (h8 : (cs.all fun c ↦ c % 8 == 0 && c < 4096) = true) :
    BFrame s t (fun a ↦ ∃ c ∈ cs, Within a (msp + BitVec.ofNat 64 c) 8) := by
  have hk : ∀ k ∈ x.writes, ∃ c ∈ cs, Sym.Addr.eval s k = msp + BitVec.ofNat 64 c := by
    intro k hk
    have e := List.all_eq_true.mp hw k hk
    rcases k with ⟨_ | b, off⟩
    · simp at e
    · simp only [Bool.and_eq_true, List.contains_iff_mem] at e
      refine ⟨off.toNat, e.2, ?_⟩
      have hb : b = .reg .x2 := Sym.E.beq_eq e.1
      subst hb
      simp only [Sym.Addr.eval, Sym.E.eval, hsp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine BFrame.of_dwords (fun a ha ↦ h.frame a fun k hk' heq ↦ ?_) ?_
  · obtain ⟨c, hc, e⟩ := hk k hk'
    exact ha ⟨c, hc, by rw [heq, e]; simp only [Within]; omega⟩
  · rintro a ⟨c, hc, hin⟩
    have := List.all_eq_true.mp h8 c hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨c, hc, within_of_alignDown (by simp only [msp]; addr_omega [this.1, this.2]) (by decide)
      hin⟩


/-! ## What the loop writes -/

/-- `main`'s scratch slots but the table's length and the input slice, the `Vec`s' headers (the
IV between them kept), callees' stacks, `NEXT` and the heap. -/
@[rv_addr] def Wg (a : Word) : Prop :=
  Within a (msp + 8) 80 ∨ Within a (msp + 104) 32 ∨ Within a (msp + 240) 80 ∨
    Within a (msp + 352) 120 ∨ Within a (msp - 4096) 4096 ∨ Within a nextAddr 8 ∨
    (heapStart ≤ a.toNat ∧ a.toNat < heapEnd)

theorem not_kept_wg {words : List Word} (hf : words.length ≤ inputWords) {a : Word} (h : Wg a) :
    ¬ Kept words a := by
  intro hk
  simp only [Kept, inputBase_eq] at hk
  simp only [inputWords] at hf
  rcases h with h | h | h | h | h | h | h <;> rcases hk with hk | hk | hk <;>
    addr_omega [h, hk, hf]

/-- From `u₀` on: `sp` is `msp`, the heap in shape and grown, memory changed only in `Wg`. -/
structure NG (u₀ t : MachineState) : Prop where
  sp : t.getReg .x2 = msp
  heap : HeapOk t
  mono : heapNext u₀ ≤ heapNext t
  frame : BFrame u₀ t Wg

theorem NG.refl {u₀ : MachineState} (hsp : u₀.getReg .x2 = msp) (hh : HeapOk u₀) : NG u₀ u₀ :=
  ⟨hsp, hh, le_refl _, BFrame.refl _ _⟩

theorem NG.step {u₀ t t' : MachineState} {W : Word → Prop} (h : NG u₀ t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → Wg a) (hsp : t'.getReg .x2 = msp) (hheap : HeapOk t')
    (hmono : heapNext t ≤ heapNext t') : NG u₀ t' :=
  ⟨hsp, hheap, le_trans h.mono hmono, h.frame.trans hf hW⟩

/-- A step that writes no memory. -/
theorem NG.same {u₀ t t' : MachineState} (h : NG u₀ t) (hm : ∀ a, t'.getMem a = t.getMem a)
    (hsp : t'.getReg .x2 = msp) : NG u₀ t' := by
  have hn : heapNext t' = heapNext t := by simp only [heapNext, hm]
  exact h.step (BFrame.of_same hm (fun _ ↦ False)) (fun _ h ↦ h.elim) hsp
    ⟨by rw [hn]; exact h.heap.lo, by rw [hn]; exact h.heap.hi⟩ (le_of_eq hn.symm)

/-- A step that writes `main`'s scratch slots at `cs`, all in `Wg`. -/
theorem NG.slots {u₀ t t' : MachineState} {cs : List Nat} (h : NG u₀ t)
    (hf : BFrame t t' fun a ↦ ∃ c ∈ cs, Within a (msp + BitVec.ofNat 64 c) 8)
    (hc : (cs.all fun c ↦ (8 ≤ c && c + 8 ≤ 88) || (104 ≤ c && c + 8 ≤ 136) ||
      (240 ≤ c && c + 8 ≤ 320) || (352 ≤ c && c + 8 ≤ 472)) = true)
    (hsp : t'.getReg .x2 = msp) : NG u₀ t' := by
  have hW : ∀ a, (∃ c ∈ cs, Within a (msp + BitVec.ofNat 64 c) 8) → Wg a := by
    rintro a ⟨c, hc', hin⟩
    have := List.all_eq_true.mp hc c hc'
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with ((h1 | h1) | h1) | h1
    · exact Or.inl (by addr_omega [hin, h1.1, h1.2])
    · exact Or.inr (Or.inl (by addr_omega [hin, h1.1, h1.2]))
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [hin, h1.1, h1.2])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hin, h1.1, h1.2]))))
  have hn : heapNext t' = heapNext t := by
    simp only [heapNext]
    refine congrArg BitVec.toNat (hf.getMem (a := nextAddr) (by decide) fun i hi hw ↦ ?_)
    obtain ⟨c, hc', hin⟩ := hw
    have := List.all_eq_true.mp hc c hc'
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    have h1 : c + 8 ≤ 472 := by omega
    addr_omega [hin, hi, h1]
  exact h.step hf hW hsp ⟨by rw [hn]; exact h.heap.lo, by rw [hn]; exact h.heap.hi⟩
    (le_of_eq hn.symm)

section
variable {s u₀ t : MachineState} {words : List Word}

theorem NG.minv (h0 : NewA s words u₀) (h : NG u₀ t) : MInv s words t :=
  h0.inv.bframe h.frame h.sp h.heap fun _ ha ↦ not_kept_wg h0.inv.fits ha

theorem NG.keepMsp (h : NG u₀ t) {c : Nat} (h8 : c % 8 = 0)
    (hc : c + 8 ≤ 8 ∨ (88 ≤ c ∧ c + 8 ≤ 104) ∨ (320 ≤ c ∧ c + 8 ≤ 352)) :
    t.getMem (msp + BitVec.ofNat 64 c) = u₀.getMem (msp + BitVec.ofNat 64 c) :=
  h.frame.getMem (by addr_omega [h8, hc]) fun i hi hw ↦ by
    rcases hw with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2⟩
    all_goals first
      | (rcases hc with hc | hc | hc <;> addr_omega [h1, hi, hc])
      | (simp only [heapEnd, heapStart] at h1 h2; rcases hc with hc | hc | hc <;>
          addr_omega [h1, h2, hi, hc])

theorem NG.iv' (h : NG u₀ t) : bytesAt t (msp + 320) 32 = bytesAt u₀ (msp + 320) 32 :=
  h.frame.bytesAt fun i hi hw ↦ by
    rcases hw with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2⟩
    all_goals first
      | addr_omega [h1, hi]
      | (simp only [heapEnd, heapStart] at h1 h2; addr_omega [h1, h2, hi])

end

/-! ## The `Vec`s -/

/-- The `Vec` at `a`, of `size`-byte elements aligned to `al`: its length within its capacity, its
buffer in `[H, H')`, or none. -/
structure VecIn (t : MachineState) (a : Word) (size al H H' : Nat) : Prop where
  len : (vecLen t a).toNat ≤ (vecCap t a).toNat
  al : (vecPtr t a).toNat % al = 0
  buf : (vecCap t a).toNat * size = 0 ∨
    H ≤ (vecPtr t a).toNat ∧ (vecPtr t a).toNat + (vecCap t a).toNat * size ≤ H'

/-- The `Vec`s' buffers, `blocks` (`msp + 400`), `words` (`424`), `positions` (`448`) and `bytes`
(`240`), in `[H, H')` and pairwise apart. -/
structure VecBufs (t : MachineState) (H H' : Nat) : Prop where
  b : VecIn t (msp + 400) 24 8 H H'
  w : VecIn t (msp + 424) 16 8 H H'
  p : VecIn t (msp + 448) 2 2 H H'
  y : VecIn t (msp + 240) 2 2 H H'
  bw : Apart (vecPtr t (msp + 400)) ((vecCap t (msp + 400)).toNat * 24)
    (vecPtr t (msp + 424)) ((vecCap t (msp + 424)).toNat * 16)
  bp : Apart (vecPtr t (msp + 400)) ((vecCap t (msp + 400)).toNat * 24)
    (vecPtr t (msp + 448)) ((vecCap t (msp + 448)).toNat * 2)
  bY : Apart (vecPtr t (msp + 400)) ((vecCap t (msp + 400)).toNat * 24)
    (vecPtr t (msp + 240)) ((vecCap t (msp + 240)).toNat * 2)
  wp : Apart (vecPtr t (msp + 424)) ((vecCap t (msp + 424)).toNat * 16)
    (vecPtr t (msp + 448)) ((vecCap t (msp + 448)).toNat * 2)
  wy : Apart (vecPtr t (msp + 424)) ((vecCap t (msp + 424)).toNat * 16)
    (vecPtr t (msp + 240)) ((vecCap t (msp + 240)).toNat * 2)
  py : Apart (vecPtr t (msp + 448)) ((vecCap t (msp + 448)).toNat * 2)
    (vecPtr t (msp + 240)) ((vecCap t (msp + 240)).toNat * 2)

/-- The four `Vec`s hold `st`'s. -/
structure VecsAt (t : MachineState) (st : Model.NewState) : Prop where
  blocks : blocksAt t (vecPtr t (msp + 400)) (vecLen t (msp + 400)).toNat = st.blocks
  words : wordsAt t (vecPtr t (msp + 424)) (vecLen t (msp + 424)).toNat = st.words
  positions : halvesAt t (vecPtr t (msp + 448)) (vecLen t (msp + 448)).toNat = st.positions
  bytes : halvesAt t (vecPtr t (msp + 240)) (vecLen t (msp + 240)).toNat = st.bytes

/-- A frame that misses the `Vec`s' headers and `[H, H')` keeps them. -/
theorem VecsAt.frame {t t' : MachineState} {st : Model.NewState} {H H' : Nat} {W : Word → Prop}
    (hv : VecsAt t st) (hb : VecBufs t H H') (hf : BFrame t t' W)
    (hW : ∀ a, W a → ¬ Within a (msp + 240) 24 ∧ ¬ Within a (msp + 400) 72 ∧
      ¬ (H ≤ a.toNat ∧ a.toNat < H')) (hH : H' ≤ heapEnd) :
    VecsAt t' st ∧ VecBufs t' H H' := by
  have hk : ∀ c : Nat, c % 8 = 0 → (240 ≤ c ∧ c + 8 ≤ 264 ∨ 400 ≤ c ∧ c + 8 ≤ 472) →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun i hi hw ↦ ?_
    obtain ⟨h1, h2, -⟩ := hW _ hw
    rcases hc with hc | hc
    · exact h1 (by addr_omega [hc, hi])
    · exact h2 (by addr_omega [hc, hi])
  have hB : ∀ a : Word, H ≤ a.toNat → a.toNat < H' → byteAt t' a = byteAt t a :=
    fun a h1 h2 ↦ hf a fun hw ↦ (hW a hw).2.2 ⟨h1, h2⟩
  simp only [heapEnd] at hH
  have p0 : vecPtr t' (msp + 400) = vecPtr t (msp + 400) := hk 408 (by decide) (by decide)
  have l0 : vecLen t' (msp + 400) = vecLen t (msp + 400) := hk 416 (by decide) (by decide)
  have c0 : vecCap t' (msp + 400) = vecCap t (msp + 400) := hk 400 (by decide) (by decide)
  have p1 : vecPtr t' (msp + 424) = vecPtr t (msp + 424) := hk 432 (by decide) (by decide)
  have l1 : vecLen t' (msp + 424) = vecLen t (msp + 424) := hk 440 (by decide) (by decide)
  have c1 : vecCap t' (msp + 424) = vecCap t (msp + 424) := hk 424 (by decide) (by decide)
  have p2 : vecPtr t' (msp + 448) = vecPtr t (msp + 448) := hk 456 (by decide) (by decide)
  have l2 : vecLen t' (msp + 448) = vecLen t (msp + 448) := hk 464 (by decide) (by decide)
  have c2 : vecCap t' (msp + 448) = vecCap t (msp + 448) := hk 448 (by decide) (by decide)
  have p3 : vecPtr t' (msp + 240) = vecPtr t (msp + 240) := hk 248 (by decide) (by decide)
  have l3 : vecLen t' (msp + 240) = vecLen t (msp + 240) := hk 256 (by decide) (by decide)
  have c3 : vecCap t' (msp + 240) = vecCap t (msp + 240) := hk 240 (by decide) (by decide)
  have dw : ∀ (p : Word) (n sz : Nat), (n * sz = 0 ∨ H ≤ p.toNat ∧ p.toNat + n * sz ≤ H') →
      ∀ m, m ≤ n → ∀ a : Word, a.toNat % 8 = 0 → p.toNat ≤ a.toNat → a.toNat + 8 ≤ p.toNat + sz * m →
        t'.getMem a = t.getMem a := by
    intro p n sz hpn m hm a h8 h1 h2
    have : m * sz ≤ n * sz := Nat.mul_le_mul_right _ hm
    rcases hpn with h0 | ⟨h3, h4⟩
    · rw [Nat.mul_comm] at h2; omega
    · rw [Nat.mul_comm] at h2
      exact getMem_eq_of_bytes h8 h8 fun i hi ↦ hB _ (by addr_omega [h1, h2, h3, h4, hi, this, hH])
        (by addr_omega [h2, h4, hi, this, hH])
  have bt : ∀ (p : Word) (n sz : Nat), (n * sz = 0 ∨ H ≤ p.toNat ∧ p.toNat + n * sz ≤ H') →
      ∀ m, m ≤ n → ∀ a : Word, p.toNat ≤ a.toNat → a.toNat < p.toNat + sz * m →
        byteAt t' a = byteAt t a := by
    intro p n sz hpn m hm a h1 h2
    have : m * sz ≤ n * sz := Nat.mul_le_mul_right _ hm
    rcases hpn with h0 | ⟨h3, h4⟩
    · rw [Nat.mul_comm] at h2; omega
    · exact hB _ (by omega) (by rw [Nat.mul_comm] at h2; omega)
  have lt : ∀ (p : Word) (n sz m : Nat), (n * sz = 0 ∨ H ≤ p.toNat ∧ p.toNat + n * sz ≤ H') →
      m ≤ n → 0 < sz → m = 0 ∨ p.toNat + sz * m < 2 ^ 64 := by
    intro p n sz m hpn hm hsz
    rcases hpn with h0 | ⟨_, h4⟩
    · left; rcases Nat.mul_eq_zero.mp h0 with h | h <;> omega
    · right
      have : m * sz ≤ n * sz := Nat.mul_le_mul_right _ hm
      rw [Nat.mul_comm]; omega
  have hv0 := hv.blocks
  have hv1 := hv.words
  have hv2 := hv.positions
  have hv3 := hv.bytes
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, l0, ← hv0]
    rcases lt _ _ _ _ hb.b.buf hb.b.len (by decide) with h' | h'
    · rw [h']; rfl
    · exact blocksAt_keep hb.b.al (dw _ _ _ hb.b.buf _ hb.b.len) h'
  · rw [p1, l1, ← hv1]
    rcases lt _ _ _ _ hb.w.buf hb.w.len (by decide) with h' | h'
    · rw [h']; rfl
    · exact wordsAt_keep hb.w.al (dw _ _ _ hb.w.buf _ hb.w.len) h'
  · rw [p2, l2, ← hv2]
    rcases lt _ _ _ _ hb.p.buf hb.p.len (by decide) with h' | h'
    · rw [h']; rfl
    · exact halvesAt_keep hb.p.al (bt _ _ _ hb.p.buf _ hb.p.len) h'
  · rw [p3, l3, ← hv3]
    rcases lt _ _ _ _ hb.y.buf hb.y.len (by decide) with h' | h'
    · rw [h']; rfl
    · exact halvesAt_keep hb.y.al (bt _ _ _ hb.y.buf _ hb.y.len) h'
  · have hb0 := hb.b
    have hb1 := hb.w
    have hb2 := hb.p
    have hb3 := hb.y
    obtain ⟨_, _, _, _, bw, bp, bY, wp, wy, py⟩ := hb
    exact ⟨⟨by rw [l0, c0]; exact hb0.len, by rw [p0]; exact hb0.al, by rw [p0, c0]; exact hb0.buf⟩,
      ⟨by rw [l1, c1]; exact hb1.len, by rw [p1]; exact hb1.al, by rw [p1, c1]; exact hb1.buf⟩,
      ⟨by rw [l2, c2]; exact hb2.len, by rw [p2]; exact hb2.al, by rw [p2, c2]; exact hb2.buf⟩,
      ⟨by rw [l3, c3]; exact hb3.len, by rw [p3]; exact hb3.al, by rw [p3, c3]; exact hb3.buf⟩,
      by rw [p0, c0, p1, c1]; exact bw, by rw [p0, c0, p2, c2]; exact bp,
      by rw [p0, c0, p3, c3]; exact bY, by rw [p1, c1, p2, c2]; exact wp,
      by rw [p1, c1, p3, c3]; exact wy, by rw [p2, c2, p3, c3]; exact py⟩

/-! ## `newRust`'s fold -/

/-- `newRust`'s buffers before the first block. -/
def newInit : Model.NewState :=
  ⟨[], [], [], [], List.replicate (2 ^ 15) none, List.replicate (2 ^ 14) 0⟩

/-- `newRust`'s fold after `i` blocks. -/
def foldNew (T : List Word) (i : Nat) : Option Model.NewState :=
  (List.range i).foldl (fun st index ↦ st.bind fun st ↦ Model.blockNewRust T st index) (some newInit)

theorem foldNew_succ (T : List Word) (i : Nat) :
    foldNew T (i + 1) = (foldNew T i).bind fun st ↦ Model.blockNewRust T st i := by
  simp only [foldNew, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem newRust_eq (T : List Word) : Model.newRust T =
    (foldNew T ((T.length + 2 ^ 14 - 1) / 2 ^ 14)).map fun st ↦
      ⟨T.length, Model.fiatShamirIvRust T, st.blocks, st.words, st.positions, st.bytes⟩ := rfl

/-! ## The head of the blocks' loop -/

/-- At `0x80000518`, `i` blocks done, a word left: `newRust`'s fold holds `st`, the four `Vec`s
hold its, `group_of` (at `NewA`'s `s1`) its `groupOf`; `s0` the slots, `a5` the block's first
word, `a3` its index, `s10` the words left. -/
structure NewL (s : MachineState) (words : List Word) (u₀ : MachineState) (i : Nat)
    (st : Model.NewState) (t : MachineState) : Prop where
  a : NewA s words u₀
  ng : NG u₀ t
  pc : t.pc = 0x80000518
  lt : 2 ^ 14 * i < (words.getD 0 0).toNat
  fold : foldNew (tbl words) i = some st
  x8 : t.getReg .x8 = u₀.getReg .x8
  x13 : t.getReg .x13 = BitVec.ofNat 64 i
  x15 : t.getReg .x15 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i))
  x16 : t.getReg .x16 = u₀.getReg .x9
  x22 : t.getReg .x22 = 32768
  x25 : t.getReg .x25 = u₀.getReg .x8 + 0x20000
  x26 : (t.getReg .x26).toNat = (words.getD 0 0).toNat - 2 ^ 14 * i
  x27 : t.getReg .x27 = 1
  m8 : t.getMem (msp + 8) = u₀.getReg .x8 + 0x20000
  m16 : t.getMem (msp + 16) = 0x77fff801
  m40 : t.getMem (msp + 40) = u₀.getReg .x9
  vecs : VecsAt t st
  bufs : VecBufs t (heapNext u₀) (heapNext t)
  groupOf : halvesAt t (u₀.getReg .x9) 0x4000 = st.groupOf
  slots : st.slots.length = 2 ^ 15

theorem halvesAt_zero {t : MachineState} {p : Word} {n : Nat} (hp : p.toNat % 2 = 0)
    (hn : p.toNat + 2 * n < 2 ^ 64) (hz : bytesAt t p (2 * n) = List.replicate (2 * n) 0) :
    halvesAt t p n = List.replicate n 0 := by
  have hb : ∀ i < 2 * n, byteAt t (p + BitVec.ofNat 64 i) = 0 := by
    intro i hi
    have := congrArg (fun l ↦ l[i]?) hz
    simpa [bytesAt, hi] using this
  apply List.ext_getElem (by simp [halvesAt])
  intro i h1 _
  simp only [halvesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp only [halvesAt, List.length_map, List.length_range] at h1
  rw [getHalfword_eq_append (by addr_omega [hp, hn, h1]), hb (2 * i) (by omega),
    show p + BitVec.ofNat 64 (2 * i) + 1 = p + BitVec.ofNat 64 (2 * i + 1) by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl, hb (2 * i + 1) (by omega)]
  rfl

/-- A frame of `main`'s scratch slots keeps the doubleword at `msp + d` it misses. -/
theorem slots_keepMsp {t t' : MachineState} {cs : List Nat}
    (hf : BFrame t t' fun a ↦ ∃ c ∈ cs, Within a (msp + BitVec.ofNat 64 c) 8) {d : Nat}
    (hd : d % 8 = 0 ∧ d < 4096 ∧ (cs.all fun c ↦ (c + 8 ≤ d || d + 8 ≤ c) && c < 4096) = true) :
    t'.getMem (msp + BitVec.ofNat 64 d) = t.getMem (msp + BitVec.ofNat 64 d) :=
  hf.getMem (by addr_omega [hd.1, hd.2.1]) fun i hi ⟨c, hc, hin⟩ ↦ by
    have := List.all_eq_true.mp hd.2.2 c hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with ⟨h1 | h1, h2⟩ <;> addr_omega [hin, hi, h1, h2, hd.2.1]

/-- A frame of `main`'s scratch slots keeps memory below `msp`'s frame. -/
theorem slots_keepB {t t' : MachineState} {cs : List Nat}
    (hf : BFrame t t' fun a ↦ ∃ c ∈ cs, Within a (msp + BitVec.ofNat 64 c) 8)
    (hcs : (cs.all fun c ↦ c < 4096) = true) {a : Word} (ha : a.toNat < msp.toNat) :
    byteAt t' a = byteAt t a :=
  hf a fun ⟨c, hc, hin⟩ ↦ by
    have := List.all_eq_true.mp hcs c hc
    simp only [decide_eq_true_eq] at this
    addr_omega [hin, ha, this]

section
variable {s u : MachineState} {words : List Word}

/-- `0x80000498`: into the blocks' loop. -/
theorem new_init (h : NewA s words u) :
    ∃ v, Reaches Image.code u v ∧ NewL s words u 0 newInit v := by
  have hsp := h.inv.sp
  obtain ⟨t, r, h₁⟩ := Sym.BlockSpec.reaches b80000498_spec h.pc (by rv_eval [hsp, msp]; decide)
  have k := b80000498_keeps h₁
  have hsp₁ : t.getReg .x2 = msp := by rw [k .x2 (by decide), hsp]
  have hf := holds_slots h₁ hsp [8, 40, 16] (by decide) (by decide)
  have ng : NG u t := (NG.refl hsp h.inv.heap).slots hf (by decide) hsp₁
  have K : ∀ d : Nat, d % 8 = 0 ∧ d < 4096 ∧
      ([8, 40, 16].all fun c ↦ (c + 8 ≤ d || d + 8 ≤ c) && c < 4096) = true →
      t.getMem (msp + BitVec.ofNat 64 d) = u.getMem (msp + BitVec.ofNat 64 d) :=
    fun d hd ↦ slots_keepMsp hf hd
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun i hi ⟨c, hc, hin⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> addr_omega [hin, hi]]
  obtain ⟨v400, v408, v416, v424, v432, v440, v448, v456, v464, v240, v248, v256⟩ := h.vecs
  have e : ∀ {c : Nat} {w : Word}, u.getMem (msp + BitVec.ofNat 64 c) = w → c % 8 = 0 ∧ c < 4096 ∧
      ([8, 40, 16].all fun c' ↦ (c' + 8 ≤ c || c + 8 ≤ c') && c' < 4096) = true →
      t.getMem (msp + BitVec.ofNat 64 c) = w := fun hw hc ↦ (K _ hc).trans hw
  have w400 := e (c := 400) v400 (by decide)
  have w408 := e (c := 408) v408 (by decide)
  have w416 := e (c := 416) v416 (by decide)
  have w424 := e (c := 424) v424 (by decide)
  have w432 := e (c := 432) v432 (by decide)
  have w440 := e (c := 440) v440 (by decide)
  have w448 := e (c := 448) v448 (by decide)
  have w456 := e (c := 456) v456 (by decide)
  have w464 := e (c := 464) v464 (by decide)
  have w240 := e (c := 240) v240 (by decide)
  have w248 := e (c := 248) v248 (by decide)
  have w256 := e (c := 256) v256 (by decide)
  have hGO := h.groupOf
  have hhi := h.inv.heap.hi
  simp only [heapNext, heapEnd] at hGO hhi
  have m8 : t.getMem (msp + 8) = u.getReg .x8 + 0x20000 := by
    have e := b80000498_m_x2_8 h₁
    rw [hsp] at e
    exact e
  have m16 : t.getMem (msp + 16) = 0x77fff801 := by
    have e := b80000498_m_x2_16 h₁
    rw [hsp] at e
    exact e
  have m40 : t.getMem (msp + 40) = u.getReg .x9 := by
    have e := b80000498_m_x2_40 h₁
    rw [hsp] at e
    exact e
  have hpos : 2 ^ 14 * 0 < (words.getD 0 0).toNat := Nat.pos_of_ne_zero
    fun h0 ↦ h.pos (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  refine ⟨t, r, ⟨h, ng, b80000498_pc h₁, hpos, rfl, k .x8 (by decide),
    b80000498_x13 h₁, b80000498_x15 h₁, b80000498_x16 h₁, by rw [k .x22 (by decide), h.x22],
    b80000498_x25 h₁, by rw [b80000498_x26 h₁, hsp, h.n]; omega,
    b80000498_x27 h₁, m8, m16, m40, ?_, ?_, ?_, by simp only [newInit, List.length_replicate]⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [vecLen, vecPtr]
    · rw [show (msp + 400 + 16 : Word) = msp + BitVec.ofNat 64 416 from rfl, w416]; rfl
    · rw [show (msp + 424 + 16 : Word) = msp + BitVec.ofNat 64 440 from rfl, w440]; rfl
    · rw [show (msp + 448 + 16 : Word) = msp + BitVec.ofNat 64 464 from rfl, w464]; rfl
    · rw [show (msp + 240 + 16 : Word) = msp + BitVec.ofNat 64 256 from rfl, w256]; rfl
  · have z : ∀ {a : Word} {sz al : Nat} (h0 : t.getMem a = 0) (h1 : (t.getMem (a + 8)).toNat % al = 0)
        (h2 : t.getMem (a + 16) = 0), VecIn t a sz al (heapNext u) (heapNext t) := fun h0 h1 h2 ↦
      ⟨by simp only [vecLen, vecCap, h0, h2]; rfl, h1,
        Or.inl (by simp only [vecCap, h0]; exact Nat.zero_mul _)⟩
    have c0 : ∀ {a : Word} {m : Nat} {b : Word} {k : Nat}, t.getMem a = 0 →
        Apart (vecPtr t a) ((vecCap t a).toNat * m) b k := fun h0 ↦
      Or.inl (by simp only [vecCap, h0]; exact Nat.zero_mul _)
    have a408 : (t.getMem (msp + 400 + 8)).toNat % 8 = 0 := by
      rw [show (msp + 400 + 8 : Word) = msp + BitVec.ofNat 64 408 from rfl, w408]; rfl
    have a432 : (t.getMem (msp + 424 + 8)).toNat % 8 = 0 := by
      rw [show (msp + 424 + 8 : Word) = msp + BitVec.ofNat 64 432 from rfl, w432]; rfl
    have a456 : (t.getMem (msp + 448 + 8)).toNat % 2 = 0 := by
      rw [show (msp + 448 + 8 : Word) = msp + BitVec.ofNat 64 456 from rfl, w456]; rfl
    have a248 : (t.getMem (msp + 240 + 8)).toNat % 2 = 0 := by
      rw [show (msp + 240 + 8 : Word) = msp + BitVec.ofNat 64 248 from rfl, w248]; rfl
    exact ⟨z w400 a408 w416, z w424 a432 w440, z w448 a456 w464, z w240 a248 w256,
      c0 w400, c0 w400, c0 w400, c0 w424, c0 w424, c0 w448⟩
  · rw [halvesAt_zero h.groupOf.1 (by omega)]
    · rfl
    · rw [show 2 * 0x4000 = 0x8000 from rfl, ← h.groupOfZero]
      exact hf.bytesAt fun i hi ⟨c, hc, hin⟩ ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> addr_omega [hin, hi, hGO, hhi]

end

end Rv64Verifier.Proofs.Main
