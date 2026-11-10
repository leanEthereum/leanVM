import Rv64Verifier.Proofs.Bytecode.EvalTailLoop

/-!
# `Bytecode::evaluate`: a block's end

From `0x80011618`, the block's buckets credited to `bit_sums` (`Tail`): `0x80011618` traps unless
`block.index < high_weights.len()`; `0x80011628`..`0x80011650` compute `monomial_sum(&bit_sums)`
as three `u128`s (`c0`, `c1`, `c2` in `a2`/`a5`, `a1`/`a4`, `a0`/`a3`, low/high words), a `bit_sums`
entry per iteration; `0x80010f88` reduces them and calls `mul(high_weights[block.index], ·)`;
`0x80011054` adds the product to the total and goes on to the next block (`0x80011090`) or, after
the last, to `Ok(total)` (`0x800116f8`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

/-- At `0x80011618`, block `i` credited: `bit_sums` (at `sp + 280`) holds `S`, the buckets `B`,
`s3` the positions' end `pe`; the frame holds the block's pointer, the next block's, its
`words_end` and `bytes_end`, and the total before the block. -/
structure Tail (e : Env) (t : MachineState) (i : Nat) (S B : List E) (pe : Nat) : Prop
    extends Regs e t where
  lt : i < e.bc.blocks.length
  x19 : (t.getReg .x19).toNat = pe
  ptr : t.getMem (e.s.getReg .x2 - 1848) = e.blocksPtr + BitVec.ofNat 64 (24 * i)
  next : t.getMem (e.s.getReg .x2 - 1896) = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1))
  we : t.getMem (e.s.getReg .x2 - 1888) =
    e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8)
  be : t.getMem (e.s.getReg .x2 - 1856) =
    e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16)
  total : (t.getMem (e.s.getReg .x2 - 1880), t.getMem (e.s.getReg .x2 - 1872),
    t.getMem (e.s.getReg .x2 - 1864)) = limbs (e.st i).total
  sums : eListAt t (e.s.getReg .x2 - 1688) 64 = S
  buckets : eListAt t e.bk 2048 = B

/-- The total after block `i`, from its bit sums. -/
def Env.total' (e : Env) (i : Nat) (S : List E) : E :=
  (e.st i).total + e.highW.getD (e.bc.blocks[i]?.map BlockRust.index |>.getD 0) 0 *
    monomialSumRust S

/-! ## The block's index -/

/-- `0x80011618` and `0x80011628`: the index in range, and `monomial_sum`'s loop before entry
`0`. -/
theorem start (he : EnvOk e) {t : MachineState} {i : Nat} {S B : List E} {pe : Nat}
    (ht : Tail e t i S B pe) (hpc : t.pc = 0x80011618) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x80011684 ∧
      (e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i))).toNat < 2 ^ (e.n - e.m) ∧
      MInv e t u (e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i))) S 0)) := by
  have hsp := he.sp
  have hst := he.pre.stack.valid
  have hbc := he.pre.bcClear.blocks
  have hbm := he.blocksMem ht.lt
  have hba := he.pre.bc.blocksAlign
  have hlen := bc_blocks_length e
  have hi := ht.lt
  have e2 : t.getReg .x2 = e.s.getReg .x2 - 1968 := ht.sp
  have a120 : t.getReg .x2 + 120 = e.s.getReg .x2 - 1848 := by rw [e2]; addr_omega [hsp]
  have a64 : t.getReg .x2 + 64 = e.s.getReg .x2 - 1904 := by rw [e2]; addr_omega [hsp]
  have hp : t.getMem (t.getReg .x2 + 120) = e.blocksPtr + BitVec.ofNat 64 (24 * i) := by
    rw [a120]; exact ht.ptr
  have hix : t.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i)) =
      e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i)) :=
    ht.mem.bc he hbc hbm (by addr_omega [hbm, hi, hlen]) (by addr_omega [hbm, hi, hlen])
  have hlen64 : (t.getMem (t.getReg .x2 + 64)).toNat = 2 ^ (e.n - e.m) := by
    rw [a64, ht.mem.slot he]; exact he.c64
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011618_spec hpc (by
    rv_eval [e2, ht.ptr]
    and_intros <;> first
      | valid_access hst [hsp]
      | valid_in hbm [hbm, hba, hi, hlen])
  have k₁ := b80011618_keeps h₁
  by_cases hc : (t.getMem (t.getReg .x2 + 64)).toNat ≤
      (t.getMem (t.getMem (t.getReg .x2 + 120))).toNat
  · exact ⟨t₁, hr₁, Or.inl (dead_of_fetch (by rw [b80011618_pc_taken h₁ hc]; exact trap))⟩
  have hlt := Nat.lt_of_not_le hc
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80011628_spec (b80011618_pc_not_taken h₁ hlt)
    trivial
  have k₂ := b80011628_keeps h₂
  rw [hp, hix, hlen64] at hlt
  refine ⟨t₂, hr₁.trans hr₂, Or.inr ⟨b80011628_pc h₂, hlt, ?_⟩⟩
  exact {
    le := by decide
    mem := fun a ↦ by rw [b80011628_mem_same h₂, b80011618_mem_same h₁]
    keep := fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    x16 := by rw [k₂ .x16 (by decide), b80011618_x16 h₁, hp, hix]
    x5 := by rw [b80011628_x5 h₂, k₁ .x2 (by decide), e2]; addr_omega [hsp]
    x17 := b80011628_x17 h₂
    x12 := by rw [b80011628_x12 h₂, macc_zero]; rfl
    x15 := by rw [b80011628_x15 h₂, macc_zero]; rfl
    x11 := by rw [b80011628_x11 h₂, macc_zero]; rfl
    x14 := by rw [b80011628_x14 h₂, macc_zero]; rfl
    x10 := by rw [b80011628_x10 h₂, macc_zero]; rfl
    x13 := by rw [b80011628_x13 h₂, macc_zero]; rfl }

/-! ## The product and the total -/

/-- `reduce_wide` as `0x80010f88` computes it. -/
theorem reduceWords_code (hi lo : Word) :
    (hi >>> 63 ^^^ hi >>> 61 ^^^ (hi >>> 60 ^^^ hi)) * (2 : Word) ^^^ lo ^^^
        ((hi >>> 63 ^^^ hi >>> 61 ^^^ (hi >>> 60 ^^^ hi)) * (8 : Word) ^^^
          (hi >>> 63 ^^^ hi >>> 61 ^^^ (hi >>> 60 ^^^ hi)) * (16 : Word)) ^^^
      (hi >>> 63 ^^^ hi >>> 61 ^^^ (hi >>> 60 ^^^ hi)) = reduceWords hi lo := by
  have hv : hi >>> 63 ^^^ hi >>> 61 ^^^ (hi >>> 60 ^^^ hi) =
      hi ^^^ (hi >>> 63 ^^^ hi >>> 61 ^^^ hi >>> 60) := by ac_rfl
  rw [hv]
  simp only [reduceWords]
  generalize hi ^^^ (hi >>> 63 ^^^ hi >>> 61 ^^^ hi >>> 60) = v
  rv_eval []
  ac_rfl

/-- Three doublewords in the heap. -/
theorem validRange3 {a : Word} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat + 24 ≤ 0x78000000)
    (h3 : a.toNat % 8 = 0) : ValidMemRange a 3 := fun i hi ↦
  (Sym.validAccess_eight _).mpr (by addr_omega [h1, h2, h3, hi])

set_option maxHeartbeats 4000000 in
/-- From `0x80010f88`: the sums reduced, multiplied by the block's high weight and added to the
total, then the next block or `Ok`. -/
theorem finish (hMul : MulSpec) (he : EnvOk e) {t v : MachineState} {i : Nat} {S B : List E}
    {pe : Nat} {ix : Word} (ht : Tail e t i S B pe)
    (hix' : e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i)) = ix)
    (hix : ix.toNat < 2 ^ (e.n - e.m)) (hv : MInv e t v ix S 64) (hpc : v.pc = 0x80010f88) :
    ∃ u, Reaches Image.code v u ∧ (Dead Image.code u ∨
      (u.pc = 0x80011090 ∧ Regs e u ∧ i + 1 < e.bc.blocks.length ∧
        u.getReg .x13 = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1)) ∧
        u.getReg .x12 = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8) ∧
        u.getReg .x11 = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16) ∧
        (u.getReg .x19).toNat = pe ∧
        (u.getReg .x5, u.getReg .x17, u.getReg .x16) = limbs (e.total' i S) ∧
        eListAt u e.bk 2048 = B) ∨
      (u.pc = 0x800116f8 ∧ Regs e u ∧ i + 1 = e.bc.blocks.length ∧
        (u.getReg .x5, u.getReg .x17, u.getReg .x16) = limbs (e.total' i S))) := by
  have hsp := he.sp
  have hst := he.pre.stack.valid
  have hstr := he.pre.stack.rodata
  have hbk := he.bkIn
  have hhi := he.highIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hbk hhi hh hlo
  have hbm := he.blocksMem ht.lt
  have hlen := bc_blocks_length e
  have hi := ht.lt
  have hidx : (e.bc.blocks[i]?.map BlockRust.index |>.getD 0) = ix.toNat := by
    simp only [List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some, bc_blocks e hi, hix']
  have e2 : v.getReg .x2 = e.s.getReg .x2 - 1968 := (hv.keep .x2 (by decide)).trans ht.sp
  have hmv : LoopMem e v := ht.mem.same hv.mem
  -- the reductions, and `mul`'s arguments
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010f88_spec hpc (by
    rv_eval [e2]; and_intros <;> valid_access hst [hsp])
  have k₁ := b80010f88_keeps h₁
  have x2₁ : v₁.getReg .x2 = e.s.getReg .x2 - 1968 := (k₁ .x2 (by decide)).trans e2
  have hf₁ := b80010f88_frame h₁ (by rw [e2]; addr_omega [hsp])
  have m0 := h₁.memAt 0 (by decide)
  have m1 := h₁.memAt 1 (by decide)
  have m2 := h₁.memAt 2 (by decide)
  rv_eval [] at m0 m1 m2
  rw [reduceWords_code, hv.x13, hv.x10, show ∀ p : BitVec 128,
    reduceWords (p.extractLsb' 64 64) (p.extractLsb' 0 64) = reduce128 p from fun _ ↦ rfl] at m0
  rw [reduceWords_code, hv.x14, hv.x11, show ∀ p : BitVec 128,
    reduceWords (p.extractLsb' 64 64) (p.extractLsb' 0 64) = reduce128 p from fun _ ↦ rfl] at m1
  rw [reduceWords_code, hv.x15, hv.x12, show ∀ p : BitVec 128,
    reduceWords (p.extractLsb' 64 64) (p.extractLsb' 0 64) = reduce128 p from fun _ ↦ rfl] at m2
  rw [e2] at m0 m1 m2
  rv_eval [] at m0 m1 m2
  have hm₁ : LoopMem e v₁ := hmv.step h₁ (by rv_eval [e2]; and_intros <;> addr_omega [hsp])
  have x10₁ : v₁.getReg .x10 = e.s.getReg .x2 - 152 := by
    rw [b80010f88_x10 h₁, e2]; addr_omega [hsp]
  have x12₁ : v₁.getReg .x12 = e.s.getReg .x2 - 128 := by
    rw [b80010f88_x12 h₁, e2]; addr_omega [hsp]
  have h56 : v.getMem (v.getReg .x2 + 56) = e.high := by
    rw [show v.getReg .x2 + 56 = e.s.getReg .x2 - 1912 by rw [e2]; addr_omega [hsp], hmv.slot he]
    exact he.c56
  have x11₁ : v₁.getReg .x11 = e.high + BitVec.ofNat 64 (24 * ix.toNat) := by
    rw [b80010f88_x11 h₁, h56, hv.x16, mul24]
  have hsum : eAt v₁ (v₁.getReg .x12) = monomialSumRust S := by
    rw [x12₁, monomialSumRust_macc]
    apply eAt_eq_of_limbs
    rw [limbs_eOfLimbs]
    rv_eval [m0, m1, m2]
  have hhigh : eAt v₁ (v₁.getReg .x11) = e.highW.getD ix.toNat 0 := by
    rw [x11₁]; exact hm₁.high he hix
  have hpre : MulPre v₁ := {
    out := by rw [x10₁]; valid_sub hst [hsp]
    lhs := by
      rw [x11₁]; exact validRange3 (by addr_omega [hhi, hix, hlo]) (by addr_omega [hhi, hix, hh])
        (by addr_omega [hhi, hix, hh])
    rhs := by rw [x12₁]; valid_sub hst [hsp]
    stack := ⟨by valid_sub hst [hsp, x2₁], by rw [x2₁]; addr_omega [hsp]⟩
    outLhs := by rw [x10₁, x11₁]; addr_omega [hsp, hhi, hix, hh]
    outRhs := by rw [x10₁, x12₁]; addr_omega [hsp]
    outStack := by rw [x10₁]; addr_omega [hsp, x2₁]
    lhsStack := by rw [x11₁]; addr_omega [hsp, x2₁, hhi, hix, hh]
    rhsStack := by rw [x12₁]; addr_omega [hsp, x2₁]
    rodata := RodataOk.of_dwords he.rodataL fun a ha ↦
      hm₁ a (by addr_omega [ha, hsp, hstr, hbk, hh])
    stackRodata := by addr_omega [hsp, x2₁, hstr] }
  obtain ⟨v₂, hr₂, ⟨pc₂, pres₂, post₂⟩ | hd⟩ := hMul.call hr₁ (b80010f88_pc h₁) hpre
  swap
  · exact ⟨v₂, hr₂, Or.inl hd⟩
  have hra : returnAddress v₁ = 0x80011054 := by rw [returnAddress_eq, b80010f88_x1 h₁]; rfl
  rw [hra] at pc₂
  have x2₂ : v₂.getReg .x2 = e.s.getReg .x2 - 1968 := (pres₂.reg .x2).trans x2₁
  have hprod := post₂.value
  rw [hhigh, hsum, x10₁] at hprod
  have back : ∀ a, (a.toNat < (e.s.getReg .x2).toNat - 2992 ∨
      (e.s.getReg .x2).toNat - 1968 ≤ a.toNat) →
      a.toNat < (e.s.getReg .x2).toNat - 152 → v₂.getMem a = t.getMem a := fun a h1 h2 ↦ by
    rw [post₂.frame a (by rw [x10₁]; addr_omega [h1, h2, hsp])
      (by addr_omega [h1, h2, hsp, x2₁]), hf₁ a (by addr_omega [h1, h2, hsp, e2]), hv.mem]
  -- the total, and the next block
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011054_spec pc₂ (by
    rv_eval [x2₂]; and_intros <;> valid_access hst [hsp])
  have k₃ := b80011054_keeps h₃
  have g (n c : Word) (hn : v₂.getReg .x2 + n = e.s.getReg .x2 - c)
      (h1 : 153 ≤ c.toNat) (h2 : c.toNat ≤ 1968) :
      v₂.getMem (v₂.getReg .x2 + n) = t.getMem (e.s.getReg .x2 - c) := by
    rw [hn]; exact back _ (by addr_omega [hsp, h1, h2]) (by addr_omega [hsp, h1, h2])
  have g72 := g 72 1896 (by rw [x2₂]; addr_omega [hsp]) (by decide) (by decide)
  have g32 := g 32 1936 (by rw [x2₂]; addr_omega [hsp]) (by decide) (by decide)
  have g80 := g 80 1888 (by rw [x2₂]; addr_omega [hsp]) (by decide) (by decide)
  have g112 := g 112 1856 (by rw [x2₂]; addr_omega [hsp]) (by decide) (by decide)
  have g88 := g 88 1880 (by rw [x2₂]; addr_omega [hsp]) (by decide) (by decide)
  have g96 := g 96 1872 (by rw [x2₂]; addr_omega [hsp]) (by decide) (by decide)
  have g104 := g 104 1864 (by rw [x2₂]; addr_omega [hsp]) (by decide) (by decide)
  rw [ht.next] at g72
  rw [ht.we] at g80
  rw [ht.be] at g112
  rw [ht.mem.slot he, he.c32, mul24, ← hlen] at g32
  have hp0 : v₂.getMem (v₂.getReg .x2 + 1816) = (limbs (eAt v₂ (e.s.getReg .x2 - 152))).1 := by
    rw [limbs_eAt, x2₂]; rv_eval []
  have hp1 : v₂.getMem (v₂.getReg .x2 + 1824) = (limbs (eAt v₂ (e.s.getReg .x2 - 152))).2.1 := by
    rw [limbs_eAt, x2₂]; rv_eval []
  have hp2 : v₂.getMem (v₂.getReg .x2 + 1832) = (limbs (eAt v₂ (e.s.getReg .x2 - 152))).2.2 := by
    rw [limbs_eAt, x2₂]; rv_eval []
  have htot : (w.getReg .x5, w.getReg .x17, w.getReg .x16) = limbs (e.total' i S) := by
    rw [b80011054_x5 h₃, b80011054_x17 h₃, b80011054_x16 h₃, hp0, hp1, hp2, g88, g96, g104,
      hprod, Env.total', hidx, limbs_add, ← ht.total]
    simp only [Prod.mk.injEq]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  have K : ∀ r ∈ [Reg.x2, .x9, .x18, .x19, .x20, .x21, .x23], w.getReg r = t.getReg r :=
    fun r hr ↦ by
      rw [k₃ r (mem_of_mem hr _), pres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _),
        hv.keep r hr]
  have hR : Regs e w := {
    sp := (K .x2 (by decide)).trans ht.sp
    mem := hm₁.frame fun a ha ↦ by
      rw [b80011054_mem_same h₃]
      exact post₂.frame a (by rw [x10₁]; exact fun hw ↦ ha (by addr_omega [hw, hsp]))
        (fun hw ↦ ha (by addr_omega [hw, hsp, x2₁]))
    x9 := (K .x9 (by decide)).trans ht.x9
    x18 := by rw [K .x18 (by decide)]; exact ht.x18
    x20 := (K .x20 (by decide)).trans ht.x20
    x21 := (K .x21 (by decide)).trans ht.x21
    x23 := (K .x23 (by decide)).trans ht.x23 }
  have hr := hr₂.trans hr₃
  by_cases hc : v₂.getMem (v₂.getReg .x2 + 72) = v₂.getMem (v₂.getReg .x2 + 32)
  · refine ⟨w, hr, Or.inr (Or.inr ⟨b80011054_pc_taken h₃ hc, hR, ?_, htot⟩)⟩
    rw [g72, g32] at hc
    addr_omega [hc, hbm, hi, hlen]
  · refine ⟨w, hr, Or.inr (Or.inl ⟨b80011054_pc_not_taken h₃ hc, hR, ?_, ?_, ?_, ?_, ?_, htot,
      ?_⟩)⟩
    · rw [g72, g32] at hc
      addr_omega [hc, hbm, hi, hlen]
    · rw [b80011054_x13 h₃, g72]
    · rw [b80011054_x12 h₃, g80]
    · rw [b80011054_x11 h₃, g112]
    · rw [K .x19 (by decide)]; exact ht.x19
    · refine (buckets_congr he fun a ha ↦ ?_).trans ht.buckets
      rw [b80011054_mem_same h₃]
      exact back a (by addr_omega [ha, hbk, hh, hsp]) (by addr_omega [ha, hbk, hh, hsp])


/-- **A block's end**: on to the next block, the state after this one in registers and the
buckets in memory, or, after the last, to `Ok`. -/
theorem tail (hMul : MulSpec) (he : EnvOk e) {t : MachineState} {i : Nat} {S B : List E}
    {pe : Nat} (ht : Tail e t i S B pe) (hpc : t.pc = 0x80011618) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨
      (u.pc = 0x80011090 ∧ Regs e u ∧ i + 1 < e.bc.blocks.length ∧
        u.getReg .x13 = e.blocksPtr + BitVec.ofNat 64 (24 * (i + 1)) ∧
        u.getReg .x12 = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 8) ∧
        u.getReg .x11 = e.s.getMem (e.blocksPtr + BitVec.ofNat 64 (24 * i) + 16) ∧
        (u.getReg .x19).toNat = pe ∧
        (u.getReg .x5, u.getReg .x17, u.getReg .x16) = limbs (e.total' i S) ∧
        eListAt u e.bk 2048 = B) ∨
      (u.pc = 0x800116f8 ∧ Regs e u ∧ i + 1 = e.bc.blocks.length ∧
        (u.getReg .x5, u.getReg .x17, u.getReg .x16) = limbs (e.total' i S))) := by
  obtain ⟨u, hr, hd | ⟨hu, hix, hm⟩⟩ := start he ht hpc
  · exact ⟨u, hr, Or.inl hd⟩
  obtain ⟨v, hr', hv, hvm⟩ := mloop he ht.x23 ht.sums (by decide) hm hu
  obtain ⟨w, hr'', hw⟩ := finish hMul he ht rfl hix hvm hv
  exact ⟨w, hr.trans (hr'.trans hr''), hw⟩

end Rv64Verifier.Proofs.Bytecode.Eval
