import Rv64Verifier.Proofs.Pcs.VsoKernelCall

/-!
# `verify_stacked_opening`'s level loop: a deeper level's rows, the pieces

At a level `ℓ ≠ 0` (`0x8000b158`) each row of `n` words becomes `ext_row(row)`, a `Vec<E>` of its
full chunks of three words: `try_allocate_in(S - 384, n / 3, 0, 8, 24)` (`callTryAlloc24`),
`reserve` with room, the copy loop at `0x8000b2b8` (`copyRow`), then `dot` with the kernel at
`0x80007f3c` (`callDot`). `n / 3` is compiled as a `mulhu` by `[S - 880]` (`div3`), and the chunks
read as `E`s are the row's words read three at a time (`extRow_kListAt`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso.RowsD
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The values -/

theorem rowsD_kListAt_succ (t : MachineState) (p : Word) (n : ℕ) :
    kListAt t p (n + 1) = BF64.ofBitVec (t.getMem p) :: kListAt t (p + 8) n := by
  simp only [kListAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    add_ofNat_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  congr 2
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : Word).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h8]
  omega

theorem rowsD_eListAt_succ (t : MachineState) (p : Word) (n : ℕ) :
    eListAt t p (n + 1) = eAt t p :: eListAt t (p + 24) n := by
  simp only [eListAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    add_ofNat_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  congr 1
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h24 : (24 : Word).toNat = 24 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h24]
  omega

/-- `ext_row` of `n` words read from `p`: the `n / 3` `E`s from `p`. -/
theorem extRow_kListAt (t : MachineState) (p : Word) (n : ℕ) :
    Model.Pcs.extRowRust (kListAt t p n) = eListAt t p (n / 3) := by
  induction n using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | m + 3, ih =>
      rw [rowsD_kListAt_succ, rowsD_kListAt_succ, rowsD_kListAt_succ,
        show (m + 3) / 3 = m / 3 + 1 by omega, rowsD_eListAt_succ, Model.Pcs.extRowRust,
        ih m (by omega)]
      congr 1
      · simp only [eAt]
        congr 2
        · rw [BitVec.add_assoc]; rfl
      · congr 1
        rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

/-- `x / 3` as compiled: the high word of `x * 0xaaaaaaaaaaaaaaab`, shifted right once. -/
theorem div3 (x : Word) :
    rv64_mulhu x ((0xffffffffaaaaaaab : Word) + (0xffffffffaaaaaaab : Word) <<< 32) >>> 1 =
      BitVec.ofNat 64 (x.toNat / 3) := by
  rw [show (0xffffffffaaaaaaab : Word) + (0xffffffffaaaaaaab : Word) <<< 32 =
    0xaaaaaaaaaaaaaaab by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_mulhu, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  have hM : (0xaaaaaaaaaaaaaaab : Word).toNat = 12297829382473034411 := rfl
  rw [hM, show (2 : ℕ) ^ 64 = 18446744073709551616 from rfl,
    show (2 : ℕ) ^ 1 = 2 from rfl, Nat.div_div_eq_div_mul]
  generalize x.toNat = a at hx ⊢
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ a = 3 * q + r :=
    ⟨a / 3, a % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod _ _).symm⟩
  have e : (3 * q + r) * 12297829382473034411 =
      18446744073709551616 * 2 * q + (q + r * 12297829382473034411) := by ring
  rw [e, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt (by omega)]
  omega

/-! ## The callees -/

/-- `try_allocate_in(S - 384, a1, _, 8, 24)`: a buffer of `a1` `E`s. -/
theorem callTryAlloc24 (hT : TryAllocZeroedSpec) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x800049ac) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 384) (hx13 : t.getReg .x13 = 8)
    (hx14 : t.getReg .x14 = 24) (hheap : HeapOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      (v.getMem (s.getReg .x2 - 384) = 0 → v.getMem (s.getReg .x2 - 376) = t.getReg .x11 ∧
        NewBuf t v (v.getMem (s.getReg .x2 - 368)) ((t.getReg .x11).toNat * 24) 8) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 1088) 48 ∨
        Within a nextAddr 8 ∨ Fresh t v a)) := by
  have hst := hpre.stack
  have hb := bounds hpre
  have hsl : stackLo t tryAllocStack = s.getReg .x2 - 1088 := by
    simp only [stackLo, tryAllocStack, hsp]; rv_eval []
  have hnx := hst.next
  have hab := hst.above
  simp only [vso_stack] at hnx hab
  have hpreT : TryAllocPre .x13 .x14 t := {
    heap := hheap
    out := by rw [hx10]; valid_sub hst.valid [hb]
    align := by rw [hx13]; decide
    size := by rw [hx14]; decide
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx, hb]⟩
    outStack := by rw [hx10, hsl]; addr_omega [hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, -⟩ | hdead⟩ := hT.call (Reaches.refl t) hpc hpreT
  · have hok := hpost.ok
    have hfr := DFrame.of_byteFrame hpost.frame
    rw [hx10, hx14, hx13] at hok
    rw [hx10, hsl] at hfr
    refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, fun h0 ↦ ?_, hfr⟩⟩
    obtain ⟨h1, h2⟩ := hok h0
    rw [show s.getReg .x2 - 384 + 8 = s.getReg .x2 - 376 by rv_eval []] at h1
    rw [show s.getReg .x2 - 384 + 16 = s.getReg .x2 - 368 by rv_eval [],
      show (24 : Word).toNat = 24 from rfl, show (8 : Word).toNat = 8 from rfl] at h2
    exact ⟨h1, h2⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- `n` `E`s from `a` in the heap, for `dot`. -/
def HeapEs (a : Word) (n : ℕ) : Prop :=
  n = 0 ∨ Region a (24 * n) ∧ a.toNat + 24 * n ≤ heapEnd

/-- `dot` into `S - 384` of two slices in the heap. -/
theorem callDot (hDt : MultilinearContracts.DotSpec) {s t : MachineState} {nx : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hpc : t.pc = 0x80007f3c)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 384)
    (hl : HeapEs (t.getReg .x11) (t.getReg .x12).toNat)
    (hr : HeapEs (t.getReg .x13) (t.getReg .x14).toNat) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      t.getReg .x12 = t.getReg .x14 ∧
      eAt v (s.getReg .x2 - 384) = Model.dotRust (eListAt t (t.getReg .x11) (t.getReg .x12).toNat)
        (eListAt t (t.getReg .x13) (t.getReg .x12).toNat) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 2160) 1120)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsm := stack_mapped hpre
  obtain ⟨hnx, hrs⟩ := sfacts hpre
  have hsp := hinv.sp
  have hslD : stackLo t MultilinearContracts.dotStack = s.getReg .x2 - 2160 := by
    simp only [stackLo, MultilinearContracts.dotStack, mulStack, hsp, Nat.reduceAdd]; rv_eval []
  have vr (a : Word) (n : ℕ) (h : HeapEs a n) : ValidMemRange a (3 * n) := by
    rcases h with h0 | ⟨h1, h2⟩
    · intro i hi; omega
    · exact Region.vrange h1 (Nat.le_refl _) (by omega) h1.2
  have ap (a : Word) (n : ℕ) (h : HeapEs a n) (b : Word) (m : ℕ)
      (hb' : 0xa0000000 ≤ b.toNat) : Apart b m a (24 * n) := by
    rcases h with h0 | ⟨h1, h2⟩
    · simp only [Apart, h0, Nat.mul_zero, true_or, or_true]
    · simp only [Apart, heapEnd] at h2 ⊢; omega
  have hpreD : MultilinearContracts.DotPre t := {
    ret := by rw [hx10]; valid_sub hst.valid [hb]
    left := vr _ _ hl
    right := vr _ _ hr
    stack := (hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    retLeft := ap _ _ hl _ _ (by rw [hx10]; addr_omega [hsm])
    retRight := ap _ _ hr _ _ (by rw [hx10]; addr_omega [hsm])
    retStack := by rw [hx10, hslD]; addr_omega [hb]
    leftStack := by
      have := ap _ _ hl (stackLo t MultilinearContracts.dotStack) MultilinearContracts.dotStack
        (by rw [hslD]; addr_omega [hsm])
      simp only [Apart] at this ⊢; omega
    rightStack := by
      have := ap _ _ hr (stackLo t MultilinearContracts.dotStack) MultilinearContracts.dotStack
        (by rw [hslD]; addr_omega [hsm])
      simp only [Apart] at this ⊢; omega
    rodata := hinv.rodata' hpre
    retRodata := by rw [hx10]; addr_omega [hsm, hrs]
    stackRodata := by rw [hslD]; addr_omega [hsm, hrs] }
  obtain ⟨v, hrv, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hDt.call (Reaches.refl t) hpc hpreD
  · have hval := hpost.value
    have hfr := DFrame.of_two hpost.frame
    rw [hx10] at hval
    rw [hx10, hslD] at hfr
    exact ⟨v, hrv, Or.inr ⟨hpc', hpres, hpost.len, hval, hfr⟩⟩
  · exact ⟨v, hrv, Or.inl hdead⟩

/-! ## The copy loop -/

/-- The first `e` `E`s at `dst` are `t0`'s at `src`. -/
def CopiedEs (t t0 : MachineState) (src dst : Word) (e : ℕ) : Prop :=
  ∀ i < e, eAt t (dst + BitVec.ofNat 64 (24 * i)) = eAt t0 (src + BitVec.ofNat 64 (24 * i))

/-- **The copy loop** at `0x8000b2b8`, from element `e` to its exit at `0x8000b2dc`. -/
theorem copyRow {src dst : Word} {m : ℕ} (hs : Region src (24 * m)) (hd : Region dst (24 * m))
    (hsd : Apart src (24 * m) dst (24 * m)) (t0 : MachineState) :
    ∀ c e (t : MachineState), e + c = m → 0 < c → t.pc = 0x8000b2b8 →
      t.getReg .x8 = src + BitVec.ofNat 64 (24 * e + 16) →
      t.getReg .x10 = dst + BitVec.ofNat 64 (24 * e + 16) →
      t.getReg .x13 = src + BitVec.ofNat 64 (24 * m + 16) →
      DFrame t0 t (Within · dst (24 * m)) → CopiedEs t t0 src dst e →
      ∃ t', Reaches Image.code t t' ∧ t'.pc = 0x8000b2dc ∧ CopiedEs t' t0 src dst m ∧
        DFrame t0 t' (Within · dst (24 * m)) ∧
        ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x11, .x12, .x13, .x17, .x18, .x19,
          .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg),
          t'.getReg r = t.getReg r := by
  have hsb := Region.bounds hs
  have hdb := Region.bounds hd
  intro c
  induction c with
  | zero => intro e t _ h0; omega
  | succ c ih =>
    intro e t hec _ hpc h8 h10 h13 hfr hcp
    have he : e < m := by omega
    obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b2b8_spec hpc (by
      rv_eval [h8, h10]
      and_intros
      · exact Region.valid hd (by addr_omega [hdb, he]) (by addr_omega [hdb, he])
          (by addr_omega [hdb, he])
      · exact Region.valid hd (by addr_omega [hdb, he]) (by addr_omega [hdb, he])
          (by addr_omega [hdb, he])
      · exact Region.valid hd (by addr_omega [hdb, he]) (by addr_omega [hdb, he])
          (by addr_omega [hdb, he])
      · exact Region.valid hs (by addr_omega [hsb, he]) (by addr_omega [hsb, he])
          (by addr_omega [hsb, he])
      · exact Region.valid hs (by addr_omega [hsb, he]) (by addr_omega [hsb, he])
          (by addr_omega [hsb, he])
      · exact Region.valid hs (by addr_omega [hsb, he]) (by addr_omega [hsb, he])
          (by addr_omega [hsb, he]))
    have k₁ := b8000b2b8_keeps h₁
    have f₁ := DFrame.of_memFrame (b8000b2b8_frame h₁ (by rw [h10]; addr_omega [hdb, he]))
    rw [h10, show dst + BitVec.ofNat 64 (24 * e + 16) - 16 = dst + BitVec.ofNat 64 (24 * e) by
      addr_omega [hdb, he]] at f₁
    have fr₁ : DFrame t0 t₁ (Within · dst (24 * m)) :=
      hfr.trans f₁ fun a ha ↦ by addr_omega [ha, hdb, he]
    have kS (o : ℕ) (ho : o + 8 ≤ 24 * m) :
        t.getMem (src + BitVec.ofNat 64 o) = t0.getMem (src + BitVec.ofNat 64 o) :=
      hfr _ fun i hi hw ↦ by addr_omega [hw, hi, hsd, hsb, hdb, ho]
    have m0 := b8000b2b8_m_x10_0 h₁
    have m8 := b8000b2b8_m_x10_n8 h₁
    have m16 := b8000b2b8_m_x10_n16 h₁
    rw [h10, h8] at m0 m8 m16
    rw [show src + BitVec.ofNat 64 (24 * e + 16) - 16 = src + BitVec.ofNat 64 (24 * e) by
        addr_omega [hsb, he],
      show dst + BitVec.ofNat 64 (24 * e + 16) - 16 = dst + BitVec.ofNat 64 (24 * e) by
        addr_omega [hdb, he]] at m16
    rw [show src + BitVec.ofNat 64 (24 * e + 16) - 8 = src + BitVec.ofNat 64 (24 * e + 8) by
        addr_omega [hsb, he],
      show dst + BitVec.ofNat 64 (24 * e + 16) - 8 = dst + BitVec.ofNat 64 (24 * e + 8) by
        addr_omega [hdb, he]] at m8
    have cp₁ : CopiedEs t₁ t0 src dst (e + 1) := fun i hi ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [← hcp i hi]
        exact f₁.eAt' (fun x hx hw ↦ by addr_omega [hw, hx, hdb, he, hi]) (by addr_omega [hdb, hi, he])
      · simp only [eAt]
        rw [show dst + BitVec.ofNat 64 (24 * i) + 8 = dst + BitVec.ofNat 64 (24 * i + 8) by
            addr_omega [hdb, he],
          show dst + BitVec.ofNat 64 (24 * i) + 16 = dst + BitVec.ofNat 64 (24 * i + 16) by
            addr_omega [hdb, he],
          show src + BitVec.ofNat 64 (24 * i) + 8 = src + BitVec.ofNat 64 (24 * i + 8) by
            addr_omega [hsb, he],
          show src + BitVec.ofNat 64 (24 * i) + 16 = src + BitVec.ofNat 64 (24 * i + 16) by
            addr_omega [hsb, he],
          m0, m8, m16, kS _ (by omega), kS _ (by omega), kS _ (by omega)]
    have x8₁ : t₁.getReg .x8 = src + BitVec.ofNat 64 (24 * (e + 1) + 16) := by
      rw [b8000b2b8_x8 h₁, h8]; addr_omega [hsb, he]
    have x10₁ : t₁.getReg .x10 = dst + BitVec.ofNat 64 (24 * (e + 1) + 16) := by
      rw [b8000b2b8_x10 h₁, h10]; addr_omega [hdb, he]
    have x13₁ : t₁.getReg .x13 = src + BitVec.ofNat 64 (24 * m + 16) := by
      rw [k₁ .x13 (by decide), h13]
    by_cases hlast : e + 1 = m
    · have hpc₁ := b8000b2b8_pc_not_taken h₁ (by rw [h8, h13]; addr_omega [hsb, hlast])
      exact ⟨t₁, hr₁, hpc₁, hlast ▸ cp₁, fr₁, fun r hr ↦ k₁ r hr⟩
    · have hpc₁ := b8000b2b8_pc_taken h₁ (by
        rw [h8, h13]; intro heq
        have := congrArg BitVec.toNat heq
        addr_omega [this, hsb, he, hlast])
      obtain ⟨t', hr', hpc', cp', fr', kr'⟩ := ih (e + 1) t₁ (by omega) (by omega) hpc₁ x8₁ x10₁
        x13₁ fr₁ cp₁
      exact ⟨t', hr₁.trans hr', hpc', cp', fr', fun r hr ↦ (kr' r hr).trans (k₁ r hr)⟩

theorem CopiedEs.eList {t t0 : MachineState} {src dst : Word} {m : ℕ}
    (h : CopiedEs t t0 src dst m) : eListAt t dst m = eListAt t0 src m := by
  unfold eListAt
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

end Rv64Verifier.Proofs.Pcs.Vso.RowsD
