import Rv64Verifier.Proofs.Bus.TsSumcheck

/-!
# `table_sumcheck`: `point`, the challenges reversed

```rust
let point: Vec<E> = challenges.into_iter().rev().collect();
```

`0x80008100` keeps the claim's limbs and `bus_forms.len()` in the frame (`Kept`), allocates
`point`'s buffer (`try_allocate_in`, then `reserve`) and copies the challenges into it from the
last, in the loop at `0x800081e8` (`revLoop`); it reaches `0x80008210` (`AtWeights`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the frame keeps from `0x80008180` to the end: the claim's limbs, `bus_forms.len()`, the
result's address, `form_powers.len()` and `point`'s buffer, at `sp + 8` to `sp + 56`. -/
structure Kept (s u : MachineState) (cl : E) (P : Word) : Prop where
  claim : Model.limbs cl = (u.getMem (s.getReg .x2 - 464), u.getMem (s.getReg .x2 - 480),
    u.getMem (s.getReg .x2 - 488))
  forms : u.getMem (s.getReg .x2 - 472) = s.getReg .x16
  out : u.getMem (s.getReg .x2 - 456) = s.getReg .x10
  formLen : u.getMem (s.getReg .x2 - 448) = s.getReg .x30
  point : u.getMem (s.getReg .x2 - 440) = P

theorem Kept.step {s u v : MachineState} {cl : E} {P : Word} {w : Word → Prop} (h : Kept s u cl P)
    (hf : DFrame u v w) (hw : ∀ a, w a → ¬ Within a (s.getReg .x2 - 488) 56)
    (hb : 0xa0000f38 + 2128 ≤ (s.getReg .x2).toNat) : Kept s v cl P where
  claim := by
    rw [h.claim, hf _ fun i hi hw' ↦ hw _ hw' (by addr_omega [hb, hi]),
      hf _ fun i hi hw' ↦ hw _ hw' (by addr_omega [hb, hi]),
      hf _ fun i hi hw' ↦ hw _ hw' (by addr_omega [hb, hi])]
  forms := (hf _ fun i hi hw' ↦ hw _ hw' (by addr_omega [hb, hi])).trans h.forms
  out := (hf _ fun i hi hw' ↦ hw _ hw' (by addr_omega [hb, hi])).trans h.out
  formLen := (hf _ fun i hi hw' ↦ hw _ hw' (by addr_omega [hb, hi])).trans h.formLen
  point := (hf _ fun i hi hw' ↦ hw _ hw' (by addr_omega [hb, hi])).trans h.point

/-- At `0x80008210`: `point` (the challenges reversed) in a buffer at `P` allocated since the
entry, its length in `s1`. -/
structure AtWeights (s u : MachineState) (ch : List E) (cl : E) (P : Word) : Prop where
  inv : Inv s u
  kept : Kept s u cl P
  args : Args s u
  x9 : (u.getReg .x9).toNat = ch.length
  x19 : u.getReg .x19 = s.getReg .x14 * 8
  x23 : u.getReg .x23 = s.getReg .x12
  x26 : u.getReg .x26 = s.getReg .x14
  buf : NewBuf s u P (24 * ch.length) 8
  point : eListAt u P ch.length = ch.reverse
  run : ∀ T, TranscriptAt s (tsSelf s) T → ∃ T',
    (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
      some ((ch, cl), T') ∧ TranscriptAt u (tsSelf s) T'

theorem trap {t : MachineState} (h : t.pc = 0x80008978) : Dead Image.code t :=
  dead_of_fetch (by rw [h]; exact Option.isNone_iff_eq_none.mp (by decide +kernel))

/-- `24 b / 8 · 3⁻¹` is `b`. -/
theorem len_eq (b : Word) (h : b.toNat < 2 ^ 59) :
    (b * 16 + b * 8) >>> 3 * (0xaaaaaaaaaaaaaaab : Word) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  simp only [Sym.wordToNatLit]
  rw [Nat.mod_eq_of_lt (a := b.toNat * 16) (by omega), Nat.mod_eq_of_lt (a := b.toNat * 8) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat * 16 + b.toNat * 8) (by omega)]
  omega

/-- The loop's end, `src - 24`, through `(24 b - 24) / 24` by `mulhu`. -/
theorem rev_end (a b : Word) (h1 : 1 ≤ b.toNat) (h2 : a.toNat + 24 * b.toNat < 2 ^ 64) :
    b * 16 + b * 8 + a -
        ((rv64_mulhu (b * 16 + b * 8 - 24) (12297829382473034411 : Word) &&&
          (18446744073709551600 : Word)) +
          rv64_mulhu (b * 16 + b * 8 - 24) (12297829382473034411 : Word) >>> 4 * 8) - 48 =
      a - 24 := by
  have e := MultilinearWords.end_ptr a b h1 h2
  have hx : BitVec.ofNat 64 (24 * b.toNat) = b * 16 + b * 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul]
    simp only [Sym.wordToNatLit]
    omega
  rw [hx] at e
  linear_combination -e

/-- The loop at `0x800081e8`, `k` elements copied: `point[k] = challenges[L - 1 - k]` from the
source at `P` to the destination at `Q` above it; it reaches `0x80008210` with all `L` copied,
writing only the destination. -/
theorem revLoop {u₀ : MachineState} {P Q : Word} {L : Nat} (hP : 24 ≤ P.toNat)
    (hPQ : P.toNat + 24 * L ≤ Q.toNat) (hQ : Q.toNat + 24 * L ≤ 0x78000000)
    (hvP : ValidMemRange P (3 * L)) (hvQ : ValidMemRange Q (3 * L)) :
    ∀ m k (u : MachineState), L - k = m → k < L → u.pc = 0x800081e8 →
      u.getReg .x9 = BitVec.ofNat 64 k → u.getReg .x10 = P + BitVec.ofNat 64 (24 * (L - 1 - k)) →
      u.getReg .x11 = Q + BitVec.ofNat 64 (24 * k) → u.getReg .x12 = P - 24 →
      DFrame u₀ u (Within · Q (24 * k)) →
      (∀ j < k, eAt u (Q + BitVec.ofNat 64 (24 * j)) =
        eAt u₀ (P + BitVec.ofNat 64 (24 * (L - 1 - j)))) →
      ∃ t, Reaches Image.code u t ∧ t.pc = 0x80008210 ∧ t.getReg .x9 = BitVec.ofNat 64 L ∧
        DFrame u₀ t (Within · Q (24 * L)) ∧
        (∀ j < L, eAt t (Q + BitVec.ofNat 64 (24 * j)) =
          eAt u₀ (P + BitVec.ofNat 64 (24 * (L - 1 - j)))) ∧
        ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 →
          t.getReg r = u.getReg r := by
  intro m
  induction m with
  | zero => intro k u hm hk; omega
  | succ m ih =>
    intro k u hm hk hpc h9 h10 h11 h12 hf he
    have hsrc : ValidMemRange (P + BitVec.ofNat 64 (24 * (L - 1 - k))) 3 :=
      ValidMemRange.sub hvP (by addr_omega [hP, hPQ, hQ, hk]) (by addr_omega [hP, hPQ, hQ, hk])
        (by addr_omega [hP, hPQ, hQ, hk])
    have hdst : ValidMemRange (Q + BitVec.ofNat 64 (24 * k)) 3 :=
      ValidMemRange.sub hvQ (by addr_omega [hP, hPQ, hQ, hk]) (by addr_omega [hP, hPQ, hQ, hk])
        (by addr_omega [hP, hPQ, hQ, hk])
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800081e8_spec hpc (by
      rv_eval [h10, h11]
      and_intros <;> first | valid_access hsrc [hP, hPQ, hQ, hk] | valid_access hdst [hP, hPQ, hQ, hk])
    have k₁ := b800081e8_keeps h₁
    have hf₁ := DFrame.of_memFrame (b800081e8_frame h₁ (by rw [h11]; addr_omega [hP, hPQ, hQ, hk]))
    rw [h11] at hf₁
    have hf' : DFrame u₀ u₁ (Within · Q (24 * (k + 1))) :=
      (hf.mono fun a ha ↦ by addr_omega [ha, hP, hPQ, hQ, hk]).trans hf₁
        fun a ha ↦ by addr_omega [ha, hP, hPQ, hQ, hk]
    have he' (j : Nat) (hj : j < k + 1) : eAt u₁ (Q + BitVec.ofNat 64 (24 * j)) =
        eAt u₀ (P + BitVec.ofNat 64 (24 * (L - 1 - j))) := by
      rcases Nat.lt_or_ge j k with hj' | hj'
      · rw [hf₁.eAt fun i hi hw ↦ by addr_omega [hw, hi, hP, hPQ, hQ, hk, hj']]
        exact he j hj'
      · have hjk : j = k := by omega
        subst hjk
        rw [eAt_congr (s := u) (b := P + BitVec.ofNat 64 (24 * (L - 1 - j)))
          (by rw [← h11, b800081e8_m_x11_0 h₁, h10])
          (by rw [← h11, b800081e8_m_x11_8 h₁, h10])
          (by rw [← h11, b800081e8_m_x11_16 h₁, h10])]
        exact hf.eAt fun i hi hw ↦ by addr_omega [hw, hi, hP, hPQ, hQ, hk]
    have hx9 : u₁.getReg .x9 = BitVec.ofNat 64 (k + 1) := by
      rw [b800081e8_x9 h₁, h9]; addr_omega [hk, hQ]
    have hkeep (r : Reg) (h9' : r ≠ .x9) (h10' : r ≠ .x10) (h11' : r ≠ .x11) (h13' : r ≠ .x13)
        (h14' : r ≠ .x14) (h15' : r ≠ .x15) : u₁.getReg r = u.getReg r := by
      rcases r <;> first
        | (exfalso; exact h9' rfl) | (exfalso; exact h10' rfl) | (exfalso; exact h11' rfl)
        | (exfalso; exact h13' rfl) | (exfalso; exact h14' rfl) | (exfalso; exact h15' rfl)
        | exact k₁ _ (by decide) | rfl
    by_cases hlast : k + 1 = L
    · refine ⟨u₁, hr₁, b800081e8_pc_not_taken h₁ (by rw [h10, h12]; addr_omega [hP, hk, hlast]),
        by rw [hx9, hlast], hlast ▸ hf', fun j hj ↦ he' j (by omega), hkeep⟩
    · obtain ⟨t, hr, hpc', h9', hf'', he'', hk'⟩ := ih (k + 1) u₁ (by omega) (by omega)
        (b800081e8_pc_taken h₁ (by rw [h10, h12]; addr_omega [hP, hPQ, hQ, hk, hlast]))
        hx9 (by rw [b800081e8_x10 h₁, h10]; addr_omega [hP, hPQ, hQ, hk, hlast])
        (by rw [b800081e8_x11 h₁, h11]; addr_omega [hP, hPQ, hQ, hk])
        (by rw [k₁ .x12 (by decide), h12]) hf' he'
      refine ⟨t, hr₁.trans hr, hpc', h9', hf'', he'', fun r a b c d e f ↦
        (hk' r a b c d e f).trans (hkeep r a b c d e f)⟩

/-- `Vec::with_capacity(len)`, then `reserve(len)`, from `0x80008100` to `0x80008180`: the new
buffer at `S - 144`, apart from the challenges'. -/
theorem stageC1 (hTA : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8)
    {s w : MachineState} {ch : List E} {cl : E} (hpre : TableSumcheckPre s)
    (h : AfterSumcheck s w ch cl) (hpc : w.pc = 0x80008100) :
    ∃ u, Reaches Image.code w u ∧ ((u.pc = 0x80008180 ∧ Inv s u ∧ DFrame w u (Loc s w u) ∧
      Args s u ∧ u.getReg .x2 = s.getReg .x2 - 496 ∧
      u.getMem (s.getReg .x2 - 464) = w.getMem (s.getReg .x2 - 128) ∧
      u.getMem (s.getReg .x2 - 472) = s.getReg .x16 ∧
      u.getReg .x24 = w.getMem (s.getReg .x2 - 112) ∧
      u.getReg .x25 = w.getMem (s.getReg .x2 - 120) ∧
      u.getReg .x8 = w.getReg .x21 * 16 + w.getReg .x21 * 8 ∧
      (∀ r ∈ ([.x18, .x19, .x20, .x21, .x22, .x23, .x26] : List Reg), u.getReg r = w.getReg r) ∧
      vecLen u (s.getReg .x2 - 152) = 0 ∧ (vecPtr u (s.getReg .x2 - 152)).toNat % 8 = 0 ∧
      ((w.getReg .x21).toNat = 0 ∨ heapNext w ≤ (vecPtr u (s.getReg .x2 - 152)).toNat ∧
        (vecPtr u (s.getReg .x2 - 152)).toNat + 24 * (w.getReg .x21).toNat ≤ heapNext u)) ∨
      Dead Image.code u) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := h.inv
  have hsp := I.sp
  have ha := hpre.stack.above
  have hx := hpre.stack.next
  simp only [stack_eq] at ha hx
  have hLc : (w.getReg .x21).toNat ≤ (vecCap w (s.getReg .x2 - 152)).toNat := by
    rw [h.x21]; exact h.vec.vec.len
  have hbufs := h.vec.buf
  have hhn := I.heap.hi
  simp only [NewBuf, heapEnd] at hbufs hhn
  have hL59 : (w.getReg .x21).toNat < 2 ^ 59 := by omega
  -- `0x80008100`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008100_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hval [hb1])
  have k₁ := b80008100_keeps h₁
  have hf₁ := DFrame.of_memFrame (b80008100_frame h₁ (by rw [hsp]; addr_omega [hb1]))
  rw [hsp] at hf₁
  have hn₁ : heapNext u₁ = heapNext w := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf₁ nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hx, hb1])
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
  have h9₁ : u₁.getReg .x9 = w.getReg .x21 := by rw [b80008100_x9 h₁]; exact len_eq _ hL59
  have h10₁ : u₁.getReg .x10 = s.getReg .x2 - 152 := by rw [b80008100_x10 h₁, hsp]; rv_eval []
  have m32 : u₁.getMem (s.getReg .x2 - 464) = w.getMem (s.getReg .x2 - 128) := by
    have := b80008100_m_x2_32 h₁; rw [hsp] at this; rv_eval [] at this; exact this
  have m24 : u₁.getMem (s.getReg .x2 - 472) = s.getReg .x16 := by
    have := b80008100_m_x2_24 h₁; rw [hsp, h.regs.x8] at this; rv_eval [] at this; exact this
  -- `try_allocate_in(len, 8, 24)`
  have hpre₂ : TryAllocPre .x13 .x14 u₁ := {
    heap := ⟨hn₁ ▸ I.heap.lo, hn₁ ▸ I.heap.hi⟩
    out := by rw [h10₁]; valid_sub hval [hb1]
    align := by rw [b80008100_x13 h₁]; decide
    size := by rw [b80008100_x14 h₁]; decide
    stack := hpre.stack.sub 496 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [h10₁]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    outStack := by
      rw [h10₁]; simp only [stackLo, tryAllocStack, hsp₁]; addr_omega [hb1] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post₂, -⟩ | hd⟩ := hTA.call hr₁ (b80008100_pc h₁) hpre₂
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  have hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 496 := (hp₂.reg .x2).trans hsp₁
  have hf₂ := DFrame.of_byteFrame post₂.frame
  simp only [h10₁, stackLo, tryAllocStack, hsp₁] at hf₂
  -- `0x80008154`: `Ok`
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008154_spec
    (by rw [hpc₂, returnAddress_eq, b80008100_x1 h₁]; decide) (by
      rv_eval [hsp₂]; valid_access hval [hb1])
  have hm₃ := b80008154_mem_same h₃
  have k₃ := b80008154_keeps h₃
  have e344 : u₂.getMem (u₂.getReg .x2 + 344) = u₂.getMem (u₁.getReg .x10) := by
    rw [hsp₂, h10₁]; congr 1; addr_omega [hb1]
  by_cases hok : u₂.getMem (u₁.getReg .x10) = 0
  swap
  · exact ⟨u₃, hr₂.trans hr₃, Or.inr (trap (b80008154_pc_taken h₃ (by rw [e344]; exact hok)))⟩
  have hpc₃ := b80008154_pc_not_taken h₃ (by rw [e344]; exact hok)
  obtain ⟨hcap₂, hbuf₂⟩ := post₂.ok hok
  rw [h10₁] at hcap₂ hbuf₂
  rw [show u₁.getReg .x11 = w.getReg .x21 by rw [b80008100_x11 h₁]; exact len_eq _ hL59]
    at hcap₂ hbuf₂
  rw [b80008100_x14 h₁, b80008100_x13 h₁] at hbuf₂
  have hsp₃ : u₃.getReg .x2 = s.getReg .x2 - 496 := (k₃ .x2 (by decide)).trans hsp₂
  -- `0x8000815c`: `Vec { cap: len, ptr, len: 0 }`, `reserve(len)`
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000815c_spec hpc₃ (by
    rv_eval [hsp₃]; and_intros <;> valid_access hval [hb1])
  have k₄ := b8000815c_keeps h₄
  have hf₄ := DFrame.of_memFrame (b8000815c_frame h₄ (by rw [hsp₃]; addr_omega [hb1]))
  rw [hsp₃] at hf₄
  have hsp₄ : u₄.getReg .x2 = s.getReg .x2 - 496 := (k₄ .x2 (by decide)).trans hsp₃
  have h10₄ : u₄.getReg .x10 = s.getReg .x2 - 152 := by rw [b8000815c_x10 h₄, hsp₃]; rv_eval []
  have h11₄ : u₄.getReg .x11 = w.getReg .x21 := by
    rw [b8000815c_x11 h₄, k₃ .x9 (by decide), hp₂.reg .x9, h9₁]
  have c₄ : vecCap u₄ (s.getReg .x2 - 152) = w.getReg .x21 := by
    have := b8000815c_m_x2_344 h₄; rw [hsp₃, hm₃] at this; rv_eval [] at this
    rw [vecCap, this, ← hcap₂]; congr 1; addr_omega [hb1]
  have p₄ : vecPtr u₄ (s.getReg .x2 - 152) = u₂.getMem (s.getReg .x2 - 152 + 16) := by
    have := b8000815c_m_x2_352 h₄; rw [hsp₃, hm₃] at this; rv_eval [] at this
    rw [vecPtr, show s.getReg .x2 - 152 + 8 = s.getReg .x2 - 144 by addr_omega [hb1], this]
    congr 1; addr_omega [hb1]
  have l₄ : vecLen u₄ (s.getReg .x2 - 152) = 0 := by
    have := b8000815c_m_x2_360 h₄; rw [hsp₃] at this; rv_eval [] at this
    rw [vecLen, show s.getReg .x2 - 152 + 16 = s.getReg .x2 - 136 by addr_omega [hb1], this]
  have hn₄ : heapNext u₄ = heapNext u₂ := by
    simp only [heapNext, ← hm₃]
    exact congrArg BitVec.toNat (hf₄ nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hx, hb1])
  have hm₂ := post₂.mono
  have hl₁ := hpre₂.heap.lo
  have hpre₅ : ReservePre 24 8 u₄ := {
    heap := ⟨hn₄ ▸ post₂.heap.lo, hn₄ ▸ post₂.heap.hi⟩
    self := by rw [h10₄]; valid_sub hval [hb1]
    vec := by
      rw [h10₄]
      refine ⟨?_, by rw [l₄]; exact Nat.zero_le _⟩
      simp only [RawVecOk, Buf, c₄, p₄, hn₄, heapStart]
      simp only [NewBuf, heapStart] at hbuf₂ hl₁
      simp only [Sym.wordToNatLit] at hbuf₂ ⊢
      omega
    stack := hpre.stack.sub 496 hsp₄ (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [h10₄]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    selfStack := by
      rw [h10₄]; simp only [stackLo, reserveStack, hsp₄]; addr_omega [hb1] }
  obtain ⟨u₅, hr₅, ⟨hpc₅, hp₅, post₅, hfresh⟩ | hd⟩ := hR.call hr₄ (b8000815c_pc h₄) hpre₅
  swap
  · exact ⟨u₅, hr₂.trans (hr₃.trans hr₅), Or.inr hd⟩
  have hf₅ := DFrame.of_byteFrame post₅.frame
  simp only [h10₄, stackLo, reserveStack, hsp₄] at hf₅
  have n5 := post₅.mono
  have hhi₅ := post₅.heap.hi
  have n4 : heapNext u₄ = heapNext u₂ := hn₄
  -- the writes from `u₁` on: the result slot, the callees' stack, `NEXT`, the heap allocated
  have g2 : DFrame u₁ u₂ fun a ↦ Within a (s.getReg .x2 - 152) 24 ∨
      Within a (s.getReg .x2 - 2128) 1632 ∨ Within a nextAddr 8 ∨ Fresh u₁ u₅ a :=
    hf₂.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩))
  have dA := ((g2.trans (DFrame.of_same hm₃ fun _ ↦ False) fun _ h ↦ h.elim).trans hf₄
    fun a ha ↦ Or.inl (by addr_omega [ha, hb1])).trans hf₅ fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩))
  have hfw : DFrame w u₅ (Loc s w u₅) := (hf₁.mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1])).trans
    dA fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨by omega, h2⟩)
  have miss (a : Word) (hA : a.toNat + 8 ≤ (s.getReg .x2).toNat - 152)
      (hB : (s.getReg .x2).toNat - 496 ≤ a.toNat) : u₅.getMem a = u₁.getMem a :=
    dA a fun i hi hw ↦ by
      rcases hw with hw | hw | hw | ⟨h1, h2⟩
      · addr_omega [hw, hi, hA, hB, hb1]
      · addr_omega [hw, hi, hA, hB, hb1]
      · addr_omega [hw, hi, hA, hB, hb1, hx]
      · addr_omega [h1, h2, hi, hA, hB, hb1, ha, hhi₅]
  have hsp₅ : u₅.getReg .x2 = s.getReg .x2 - 496 := (hp₅.reg .x2).trans hsp₄
  have chain (r : Reg) (h1 : r ∈ calleeSaved) (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9,
      .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27, .x28, .x29, .x30, .x31] : List Reg)) (h3 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8,
      .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) : u₅.getReg r = u₁.getReg r := by
    rw [hp₅ r h1, k₄ r h2, k₃ r h3,
      hp₂ r h1]
  refine ⟨u₅, hr₂.trans (hr₃.trans hr₅), Or.inl ⟨?_, ?_, hfw, ?_, hsp₅, ?_, ?_, ?_, ?_, ?_,
    fun r hr ↦ ?_, ?_, ?_, ?_⟩⟩
  · rw [hpc₅, returnAddress_eq, b8000815c_x1 h₄]; decide
  · exact I.loc hpre hfw post₅.heap (by omega) (hsp₅.trans hsp.symm)
  · refine (h.args.step hf₁ (fun a ha ↦ ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1]⟩)
      hb1).step dA (fun a ha ↦ ?_) hb1
    have hha := ha
    rcases hha with h0 | h0 | h0 | h0 <;>
      exact ⟨by addr_omega [h0, hb1, hx, ha, hhi₅], by addr_omega [h0, hb1, hx, ha, hhi₅]⟩
  · rw [miss _ (by addr_omega [hb1]) (by addr_omega [hb1]), m32]
  · rw [miss _ (by addr_omega [hb1]) (by addr_omega [hb1]), m24]
  · rw [chain .x24 (by decide) (by decide) (by decide), b80008100_x24 h₁, hsp]; rv_eval []
  · rw [chain .x25 (by decide) (by decide) (by decide), b80008100_x25 h₁, hsp]; rv_eval []
  · rw [chain .x8 (by decide) (by decide) (by decide), b80008100_x8 h₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [chain _ (by decide) (by decide) (by decide), k₁ _ (by decide)]
  · rw [show vecLen u₅ (s.getReg .x2 - 152) = vecLen u₄ (u₄.getReg .x10) by rw [← post₅.len, h10₄],
      h10₄, l₄]
  · have := post₅.vec.raw.1; rw [h10₄] at this; exact this
  · have hc := post₅.cap
    rw [h10₄, l₄, h11₄] at hc
    have h0 : (0 : Word).toNat = 0 := rfl
    rcases hfresh with ⟨e1, -⟩ | hnb
    · rw [h10₄] at e1
      rw [e1, p₄]
      simp only [NewBuf, Sym.wordToNatLit] at hbuf₂
      omega
    · rw [h10₄] at hnb
      simp only [NewBuf] at hnb
      omega

theorem heap_range {a : Word} {n : Nat} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat + 8 * n ≤ 0x78000000)
    (h3 : a.toNat % 8 = 0) : ValidMemRange a n :=
  region_range ⟨Or.inl ⟨h1, h2⟩, h3⟩

theorem stageC (hTA : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8)
    {s w : MachineState} {ch : List E} {cl : E} (hpre : TableSumcheckPre s)
    (h : AfterSumcheck s w ch cl) (hpc : w.pc = 0x80008100) :
    ∃ u, Reaches Image.code w u ∧
      ((∃ P, u.pc = 0x80008210 ∧ AtWeights s u ch cl P) ∨ Dead Image.code u) := by
  obtain ⟨u₅, hr₅, ⟨hpc₅, I₅, hfw, A₅, hsp₅, m464, m472, h24, h25, h8, hregs, hlen₅, hQ8, hQ⟩ | hd⟩ :=
    stageC1 hTA hR hpre h hpc
  swap
  · exact ⟨u₅, hr₅, Or.inr hd⟩
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hx := hpre.stack.next
  simp only [stack_eq] at hx
  set Q := vecPtr u₅ (s.getReg .x2 - 152) with hQdef
  set L := (w.getReg .x21).toNat with hLdef
  have hchL : ch.length = L := by
    rw [← h.vec.elems, vecEs, eListAt_length, ← h.x21]
  -- `0x80008180`: the frame's slots
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80008180_spec hpc₅ (by
    rv_eval [hsp₅]; and_intros <;> valid_access hval [hb1])
  have k₆ := b80008180_keeps h₆
  have hf₆ := DFrame.of_memFrame (b80008180_frame h₆ (by rw [hsp₅]; addr_omega [hb1]))
  rw [hsp₅] at hf₆
  have hn₆ : heapNext u₆ = heapNext u₅ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf₆ nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hx, hb1])
  have hsp₆ : u₆.getReg .x2 = s.getReg .x2 - 496 := (k₆ .x2 (by decide)).trans hsp₅
  have reg₅ (r : Reg) (hr : r ∈ ([.x18, .x19, .x20, .x21, .x22, .x23, .x26] : List Reg)) :
      u₆.getReg r = w.getReg r := by
    rw [← hregs r hr]; exact k₆ r (mem_of_mem hr _)
  have K₆ : Kept s u₆ cl Q := {
    claim := by
      rw [← h.claim, limbs_eAt]
      have e1 := b80008180_m_x2_16 h₆
      have e2 := b80008180_m_x2_8 h₆
      rw [hsp₅, h25] at e1
      rw [hsp₅, h24] at e2
      rv_eval [] at e1 e2
      rw [e1, e2, h₆.frame _ (by rv_eval [hsp₅]; and_intros <;> addr_omega [hb1]), m464]
      congr 2 <;> congr 1 <;> addr_omega [hb1]
    forms := by rw [h₆.frame _ (by rv_eval [hsp₅]; and_intros <;> addr_omega [hb1]), m472]
    out := by
      have e := b80008180_m_x2_40 h₆
      rw [hsp₅, hregs .x18 (by decide), h.regs.x18] at e; rv_eval [] at e; exact e
    formLen := by
      have e := b80008180_m_x2_48 h₆
      rw [hsp₅, hregs .x22 (by decide), h.regs.x22] at e; rv_eval [] at e; exact e
    point := by
      have e := b80008180_m_x2_56 h₆
      rw [hsp₅] at e; rv_eval [] at e
      rw [e, hQdef, vecPtr]; congr 1; addr_omega [hb1] }
  have A₆ : Args s u₆ := A₅.step hf₆ (fun a ha ↦ ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1]⟩)
    hb1
  have hfw₆ : DFrame w u₆ (Loc s w u₆) := (hfw.mono fun a ha ↦ by
      rcases ha with ha | ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨h1, by omega⟩)).trans hf₆ fun a ha ↦ Or.inl (by addr_omega [ha, hb1])
  have hx9₆ : u₆.getReg .x9 = 0 := by
    rw [b80008180_x9 h₆, hsp₅, ← hlen₅, vecLen]; congr 1; addr_omega [hb1]
  have hm₆ := I₅.mono
  have I₆ : Inv s u₆ := I₅.loc hpre (hf₆.mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1]))
    ⟨hn₆ ▸ I₅.heap.lo, hn₆ ▸ I₅.heap.hi⟩ hn₆.ge (hsp₆.trans hsp₅.symm)
  have hhi₆ := I₅.heap.hi
  -- the challenges' buffer, below `heapNext w`
  have hsrc := h.vec.buf
  have hcap := h.vec.vec.len
  have hP := h.x20
  rw [← h.x21] at hcap
  simp only [NewBuf] at hsrc
  have hlo := hpre.heap.lo
  by_cases hL0 : w.getReg .x21 = 0
  · -- no challenges: `point` is empty
    have hL : L = 0 := by rw [hLdef, hL0]; rfl
    have hch : ch = [] := List.eq_nil_of_length_eq_zero (hchL.trans hL)
    refine ⟨u₆, hr₅.trans hr₆, Or.inl ⟨Q, b80008180_pc_taken h₆ (by rw [hregs .x21 (by decide)]; exact hL0),
      I₆, K₆, A₆, by rw [hx9₆, hch]; rfl, ?_, ?_, ?_, ⟨hQ8, Or.inl (by rw [hch]; rfl)⟩,
      by rw [hch]; rfl, fun T hT ↦ ?_⟩⟩
    · rw [reg₅ .x19 (by decide)]; exact h.regs.x19
    · rw [reg₅ .x23 (by decide)]; exact h.regs.x23
    · rw [reg₅ .x26 (by decide)]; exact h.regs.x26
    · obtain ⟨T', e, hT'⟩ := h.run T hT
      exact ⟨T', e, h.inv.transcript hpre I₆.heap hfw₆ hT'⟩
  -- the copy loop
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [← hLdef, h0]; rfl)) hL0
    · exact h0
  obtain ⟨hQa, hQb⟩ : heapNext w ≤ Q.toNat ∧ Q.toNat + 24 * L ≤ heapNext u₅ := by
    rcases hQ with h0 | h0
    · omega
    · exact h0
  have hPa : heapNext s ≤ (w.getReg .x20).toNat ∧
      (w.getReg .x20).toNat + 24 * L ≤ heapNext w := by
    rw [hP]; simp only [heapStart] at hlo; omega
  obtain ⟨u₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800081a0_spec
    (b80008180_pc_not_taken h₆ (by rw [hregs .x21 (by decide)]; exact hL0)) trivial
  have hm₇ := b800081a0_mem_same h₇
  have k₇ := b800081a0_keeps h₇
  have hx8₆ : u₆.getReg .x8 = w.getReg .x21 * 16 + w.getReg .x21 * 8 := by
    rw [k₆ .x8 (by decide), h8]
  have hx20₆ : u₆.getReg .x20 = w.getReg .x20 := reg₅ .x20 (by decide)
  have hx12₇ : u₇.getReg .x12 = w.getReg .x20 - 24 :=
    h₇.reg_eq .x12 rfl (by
      rv_eval [hx8₆, hx20₆]
      exact rev_end _ _ hL1 (by simp only [heapEnd] at hhi₆; omega))
  have hb20 : (w.getReg .x20).toNat + 24 * L < 2 ^ 64 := by simp only [heapEnd] at hhi₆; omega
  have hx10₇ : u₇.getReg .x10 = w.getReg .x20 + BitVec.ofNat 64 (24 * (L - 1 - 0)) := by
    rw [b800081a0_x10 h₇, hx8₆, hx20₆]; addr_omega [hb20, hL1]
  have hx11₇ : u₇.getReg .x11 = Q + BitVec.ofNat 64 (24 * 0) := by
    rw [b800081a0_x11 h₇, hx9₆, b80008180_x14 h₆, hsp₅, hQdef, vecPtr]
    rw [show s.getReg .x2 - 496 + 352 = s.getReg .x2 - 152 + 8 by addr_omega [hb1]]
    addr_omega []
  have hx9₇ : u₇.getReg .x9 = BitVec.ofNat 64 0 := by rw [k₇ .x9 (by decide), hx9₆]; rfl
  simp only [heapEnd] at hhi₆
  have hmw := h.inv.mono
  simp only [heapStart] at hlo
  obtain ⟨t, hrt, hpct, hx9t, hft, hel, hkt⟩ := revLoop (u₀ := u₇) (by omega)
    (by omega) (by omega)
    (heap_range (by omega) (by omega) (by rw [hP]; exact hsrc.1))
    (heap_range (by omega) (by omega) hQ8) L 0 u₇ (by omega) (by omega) (b800081a0_pc h₇)
    hx9₇ hx10₇ hx11₇ hx12₇ (DFrame.refl _ _) (fun j hj ↦ absurd hj (Nat.not_lt_zero _))
  have hnt : heapNext t = heapNext u₅ := by
    rw [← hn₆]; simp only [heapNext]
    rw [hft nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hQb, hhi₆], hm₇]
  have hht : HeapOk t := ⟨by rw [hnt]; exact I₅.heap.lo, by rw [hnt]; exact I₅.heap.hi⟩
  have hspt : t.getReg .x2 = s.getReg .x2 - 496 := by
    rw [hkt .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₇ .x2 (by decide), hsp₆]
  have hs₂ := hpre.stack.above
  simp only [stack_eq, heapEnd] at hs₂
  have qmiss (a : Word) (ha : Within a Q (24 * L)) : ¬ Within a (s.getReg .x2 - 488) 56 ∧
      ¬ Within a (s.getReg .x2 - 432) 40 ∧ ¬ Within a (s.getReg .x2 - 360) 16 ∧
      ¬ Within a (s.getReg .x2 - 104) 104 ∧ Fresh w t a := by
    refine ⟨by addr_omega [ha, hQb, hhi₆, hs₂, hb1], by addr_omega [ha, hQb, hhi₆, hs₂, hb1],
      by addr_omega [ha, hQb, hhi₆, hs₂, hb1], by addr_omega [ha, hQb, hhi₆, hs₂, hb1], ?_⟩
    simp only [Fresh, Within] at ha ⊢
    rw [hnt]; omega
  have hf7 : DFrame u₆ t (Within · Q (24 * L)) := (DFrame.of_same hm₇ _).trans hft fun _ h ↦ h
  have hfwt : DFrame w t (Loc s w t) := (hfw₆.mono fun a ha ↦ by
      rcases ha with ha | ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨h1, by rw [hnt, ← hn₆]; exact h2⟩)).trans hf7
    fun a ha ↦ Or.inr (Or.inr (qmiss a ha).2.2.2.2)
  have It : Inv s t := I₆.step hpre hf7 (fun a ha ↦ ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨by have := (qmiss a ha).2.2.2.2; simp only [Fresh] at this; omega,
      by have := (qmiss a ha).2.2.2.2; exact this.2⟩)))), (qmiss a ha).2.2.2.1⟩)
    hht (by rw [hnt, hn₆]) (hspt.trans hsp₆.symm)
  have keep (r : Reg) (hr : r ∈ ([.x19, .x23, .x26] : List Reg)) : t.getReg r = w.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [hkt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        k₇ _ (by decide), reg₅ _ (by decide)]
  refine ⟨t, hr₅.trans (hr₆.trans (hr₇.trans hrt)), Or.inl ⟨Q, hpct, It,
    K₆.step hf7 (fun a ha ↦ (qmiss a ha).1) hb1,
    A₆.step hf7 (fun a ha ↦ ⟨(qmiss a ha).2.1, (qmiss a ha).2.2.1⟩) hb1, ?_,
    by rw [keep .x19 (by decide)]; exact h.regs.x19, by rw [keep .x23 (by decide)]; exact h.regs.x23,
    by rw [keep .x26 (by decide)]; exact h.regs.x26, ⟨hQ8, Or.inr ⟨by omega, by rw [hnt, hchL]; omega⟩⟩,
    ?_, fun T hT ↦ ?_⟩⟩
  · rw [hx9t, hchL, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  · rw [hchL]
    apply List.ext_getElem (by rw [eListAt_length, List.length_reverse, hchL])
    intro j h1 h2
    rw [eListAt_getElem, hel j (by rw [eListAt_length] at h1; exact h1), List.getElem_reverse]
    have hj : j < L := by rw [eListAt_length] at h1; exact h1
    have hsrc' : DFrame w u₇ (Loc s w u₆) :=
      hfw₆.trans (DFrame.of_same hm₇ fun _ ↦ False) fun _ h ↦ h.elim
    have hvs := h.vec.elems
    have hwhi := h.inv.heap.hi
    simp only [heapEnd] at hwhi
    rw [vecEs, ← hP, ← h.x21] at hvs
    rw [hsrc'.eAt fun i hi hw ↦ by
        rcases hw with hw | hw | ⟨h1, h2⟩
        · addr_omega [hw, hi, hj, hPa, hwhi, hs₂, hb1]
        · addr_omega [hw, hi, hj, hPa, hwhi]
        · addr_omega [h1, hi, hj, hPa]]
    simp only [← hvs, eListAt_getElem, eListAt_length]
    rfl
  · obtain ⟨T', e, hT'⟩ := h.run T hT
    exact ⟨T', e, h.inv.transcript hpre hht hfwt hT'⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
