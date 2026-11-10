import Rv64Verifier.Proofs.Pcs.VsoRows0A
import Rv64Verifier.Proofs.Field.Contracts

/-!
# `verify_stacked_opening`'s level loop: level 0's rows, `base_dot`

Row `j`'s value is `base_dot(row, lane_weights)`: the loop at `0x8000b3ec` walks the row's words
from the last (`s0`) and the kernel's elements from the first (`a1`), `min(len, lane_weights.len())`
of each, multiplies with `<E as Mul<K>>::mul` into `S - 384` and xors the product into
`s8, s7, s6` (`inner`). `accE` is the mirror's partial sum.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The mirror's partial sums -/

/-- `base_dot`'s products, `lane_weights[i] * row[len - 1 - i]`. -/
def bdTerms (lw : List E) (row : List K) : List E :=
  (row.reverse.zip lw).map fun p ↦ p.2 * ofK p.1

/-- The first `i` products summed. -/
def accE (lw : List E) (row : List K) (i : ℕ) : E :=
  ((bdTerms lw row).take i).foldl (· + ·) 0

theorem bdTerms_length (lw : List E) (row : List K) :
    (bdTerms lw row).length = min row.length lw.length := by
  simp [bdTerms]

theorem accE_succ (lw : List E) (row : List K) {i : ℕ} (hi : i < min row.length lw.length) :
    accE lw row (i + 1) = accE lw row i +
      lw[i]'(by omega) * ofK (row[row.length - 1 - i]'(by omega)) := by
  have hl : i < (bdTerms lw row).length := by rw [bdTerms_length]; exact hi
  rw [accE, accE, List.take_add_one, List.getElem?_eq_getElem hl]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 1
  simp [bdTerms, List.getElem_reverse]

theorem accE_zero (lw : List E) (row : List K) : accE lw row 0 = 0 := by
  simp [accE]

theorem accE_full (lw : List E) (row : List K) :
    accE lw row (min row.length lw.length) = Model.Pcs.baseDot lw row := by
  rw [accE, ← bdTerms_length, List.take_length]
  rfl

theorem limbs_zero0 : Model.limbs (0 : E) = (0, 0, 0) := by
  decide +kernel

/-! ## What the rows' loop writes -/

/-- What the rows' loop writes: `mul`'s stack, its result at `S - 384`, and the `n` values
from `Q`. -/
@[rv_addr] def R0W (s : MachineState) (Q : Word) (n : ℕ) (y : Word) : Prop :=
  Within y (s.getReg .x2 - 1200) 160 ∨ Within y (s.getReg .x2 - 384) 24 ∨ Within y Q (24 * n)

/-- The loop's constants, from its start `r` on: the kernel's elements `lw` at `KP`, the buffer
`Q` of `n` values in the heap. -/
structure R0K (s r : MachineState) (Q : Word) (n : ℕ) (KP : Word) (lw : List E) : Prop where
  kp : lw.length = 0 ∨ Region KP (24 * lw.length)
  kmiss : ∀ y, Within y KP (24 * lw.length) → ¬ R0W s Q n y
  kfit : lw.length = 0 ∨ KP.toNat + 24 * lw.length ≤ heapEnd
  elems : eListAt r KP lw.length = lw
  ro : RodataOk r
  q1 : heapStart ≤ Q.toNat
  q2 : Q.toNat + 24 * n ≤ heapEnd
  q8 : Q.toNat % 8 = 0
  m904 : r.getMem (s.getReg .x2 - 904) = KP
  m784 : r.getMem (s.getReg .x2 - 784) = BitVec.ofNat 64 lw.length

/-- At every point of the loop: memory changed since `r` only in `R0W`. -/
structure R0B (s r : MachineState) (Q : Word) (n : ℕ) (u : MachineState) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  fr : DFrame r u (R0W s Q n)
  x9 : u.getReg .x9 = r.getReg .x9
  x26 : u.getReg .x26 = r.getReg .x26

theorem r0w_rodata {s : MachineState} (hpre : VsoPre s) {Q : Word} {n : ℕ}
    (hq : Q.toNat + 24 * n ≤ heapEnd) {y : Word} (h : R0W s Q n y) :
    ¬ Within y rodataBase Rv64Verifier.rodataSize := by
  have hb := bounds hpre
  obtain ⟨-, hro⟩ := sfacts hpre
  intro hy
  simp only [R0W] at h
  rcases h with h | h | h <;> addr_omega [h, hy, hb, hro, hq]

theorem R0B.rodata {s r u : MachineState} {Q : Word} {n : ℕ} {KP : Word} {lw : List E}
    (hpre : VsoPre s)
    (K : R0K s r Q n KP lw) (B : R0B s r Q n u) : RodataOk u :=
  K.ro.dframe B.fr fun _ hy h ↦ r0w_rodata hpre K.q2 h hy

/-- The kernel's elements, kept. -/
theorem R0B.lw {s r u : MachineState} {Q : Word} {n : ℕ} {KP : Word} {lw : List E}
    (K : R0K s r Q n KP lw) (B : R0B s r Q n u) {i : ℕ} (hi : i < lw.length) :
    eAt u (KP + BitVec.ofNat 64 (24 * i)) = lw[i] := by
  have hk := K.kfit.resolve_left (by omega)
  rw [B.fr.eAt fun c hc h ↦ K.kmiss _ (by addr_omega [hc, hi, hk]) h,
    ← List.getElem_of_eq K.elems (by rw [eListAt_length]; exact hi), eListAt_getElem]

/-- In the inner loop of row `j` (words `row` from `rp`), `i` products summed, at `0x8000b3ec`. -/
structure R0I (s r : MachineState) (Q : Word) (n : ℕ) (KP : Word) (lw : List E) (rp : Word)
    (row : List K) (vs : List E) (j i : ℕ) (u : MachineState) : Prop where
  base : R0B s r Q n u
  x8 : i < min row.length lw.length →
    u.getReg .x8 = rp + BitVec.ofNat 64 (8 * (row.length - 1 - i))
  x11 : u.getReg .x11 = KP + BitVec.ofNat 64 (24 * i)
  x25 : u.getReg .x25 = KP + BitVec.ofNat 64 (24 * min row.length lw.length)
  acc : (u.getReg .x24, u.getReg .x23, u.getReg .x22) = Model.limbs (accE lw row i)
  x18 : u.getReg .x18 = BitVec.ofNat 64 n
  x19 : u.getReg .x19 = Q
  x21 : u.getReg .x21 = BitVec.ofNat 64 j
  x27 : u.getReg .x27 = BitVec.ofNat 64 j
  vals : eListAt u Q j = vs

/-- Row `rp` holds `row`, kept since `r`. -/
structure R0Row (s r : MachineState) (Q : Word) (n : ℕ) (rp : Word) (row : List K) : Prop where
  words : kListAt r rp row.length = row
  region : row.length = 0 ∨ Region rp (8 * row.length)
  miss : ∀ y, Within y rp (8 * row.length) → ¬ R0W s Q n y

/-- Word `k` of the row, kept. -/
theorem R0Row.word {s r u : MachineState} {Q : Word} {n : ℕ} {rp : Word} {row : List K}
    (R : R0Row s r Q n rp row) (B : R0B s r Q n u) {k : ℕ} (hk : k < row.length) :
    BF64.ofBitVec (u.getMem (rp + BitVec.ofNat 64 (8 * k))) = row[k] := by
  have hR : Region rp (8 * row.length) := by
    rcases R.region with h | h
    · omega
    · exact h
  have hb := Region.bounds hR
  rw [B.fr _ fun c hc h ↦ R.miss _ (by addr_omega [hc, hk, hb]) h,
    ← List.getElem_of_eq R.words (by simp [kListAt]; exact hk)]
  simp [kListAt]

/-- **One product** of `base_dot`: from `0x8000b3ec` back to it, or to `0x8000b424` after the
last. -/
theorem inner0_step (hMK : MulKSpec) {s r u : MachineState} {Q : Word} {n : ℕ} {KP : Word}
    {lw : List E} {rp : Word} {row : List K} {vs : List E} {j i : ℕ} (hpre : VsoPre s)
    (K : R0K s r Q n KP lw) (R : R0Row s r Q n rp row) (hj : j < n)
    (hi : i < min row.length lw.length) (hpc : u.pc = 0x8000b3ec)
    (I : R0I s r Q n KP lw rp row vs j i u) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x8000b3ec ∧ i + 1 < min row.length lw.length ∧
      R0I s r Q n KP lw rp row vs j (i + 1) v) ∨
      (v.pc = 0x8000b424 ∧ i + 1 = min row.length lw.length ∧
        R0I s r Q n KP lw rp row vs j (i + 1) v) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, hro⟩ := sfacts hpre
  have B := I.base
  have hR : Region rp (8 * row.length) := by
    rcases R.region with h | h
    · omega
    · exact h
  have hRb := Region.bounds hR
  have hK : Region KP (24 * lw.length) := by
    rcases K.kp with h | h
    · omega
    · exact h
  have hKb := Region.bounds hK
  have hkf := K.kfit.resolve_left (by omega)
  have hab := hst.above
  simp only [vso_stack] at hab
  have hil : i < row.length := by omega
  have hik : i < lw.length := by omega
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b3ec_spec hpc (by
    rv_eval [I.x8 hi]
    exact Region.valid hR (by addr_omega [hRb, hil]) (by addr_omega [hRb, hil])
      (by addr_omega [hRb, hil]))
  have k₁ := b8000b3ec_keeps h₁
  have m₁ := b8000b3ec_mem_same h₁
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans B.sp
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 384 := by
    rw [b8000b3ec_x10 h₁, B.sp]; rv_eval []
  have x11₁ : u₁.getReg .x11 = KP + BitVec.ofNat 64 (24 * i) :=
    (k₁ .x11 (by decide)).trans I.x11
  have x12₁ : u₁.getReg .x12 = u.getMem (rp + BitVec.ofNat 64 (8 * (row.length - 1 - i))) := by
    rw [b8000b3ec_x12 h₁, I.x8 hi]
  have slo : stackLo u₁ mulKStack = s.getReg .x2 - 1200 := by
    simp only [stackLo, sp₁, mulKStack, baseMulStack]
    exact BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hro₁ : RodataOk u₁ := fun p hp ↦ by rw [m₁]; exact B.rodata hpre K p hp
  have hmk : MulKPre u₁ := {
    out := by rw [x10₁]; valid_sub hst.valid [hb]
    lhs := by
      rw [x11₁]
      exact Region.vrange hK (by addr_omega [hKb, hik]) (by addr_omega [hKb, hik])
        (by addr_omega [hKb, hik])
    stack := (hst.sub 1040 sp₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    pool := poolOk_of_rodata hro₁ (by rw [slo]; addr_omega [hb, hro])
    outStack := by rw [x10₁, slo]; addr_omega [hb]
    lhsStack := by rw [x11₁, slo]; addr_omega [hb, hKb, hik, hkf, hab] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ :=
    hMK.call hr₁ (b8000b3ec_pc h₁) hmk
  swap
  · exact ⟨u₂, hr₂, Or.inr (Or.inr hd)⟩
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1040 := (hpres₂.reg .x2).trans sp₁
  have pv : eAt u₂ (s.getReg .x2 - 384) =
      lw[i] * ofK (row[row.length - 1 - i]'(by omega)) := by
    have hv := hpost₂.value
    rw [x10₁, x11₁, x12₁] at hv
    rw [hv]
    have e1 : eAt u₁ (KP + BitVec.ofNat 64 (24 * i)) = eAt u (KP + BitVec.ofNat 64 (24 * i)) := by
      unfold eAt; simp only [m₁]
    rw [e1, B.lw K hik]
    congr 2
    exact R.word B (by omega)
  have F₂ : DFrame u₁ u₂ fun y ↦ Within y (s.getReg .x2 - 384) 24 ∨
      Within y (s.getReg .x2 - 1200) 160 := by
    have := DFrame.of_two hpost₂.frame
    rw [x10₁, slo] at this
    exact this
  obtain ⟨v, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000b400_spec
    (by rw [hpc₂, returnAddress_eq, b8000b3ec_x1 h₁]; decide) (by
      rv_eval [sp₂]; and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000b400_keeps h₃
  have m₃ := b8000b400_mem_same h₃
  have hl : (u₂.getMem (s.getReg .x2 - 384), u₂.getMem (s.getReg .x2 - 384 + 8),
      u₂.getMem (s.getReg .x2 - 384 + 16)) =
        Model.limbs (lw[i] * ofK (row[row.length - 1 - i]'(by omega))) := by
    rw [← pv, limbs_eAt]
  have reg (q : Reg) (h3 : q ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x13, .x14, .x15, .x16,
      .x17, .x18, .x19, .x20, .x21, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (hc : q ∈ calleeSaved)
      (h1 : q ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x13, .x14, .x15, .x16, .x17,
        .x18, .x19, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      v.getReg q = u.getReg q := by
    rw [k₃ q h3, hpres₂ q hc, k₁ q h1]
  have F : DFrame u v (R0W s Q n) := by
    intro y hy
    rw [m₃, F₂ y fun c hc h ↦ hy c hc (by
      simp only [R0W]
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h), m₁]
  have x20₂ : u₂.getReg .x20 = KP + BitVec.ofNat 64 (24 * (i + 1)) := by
    rw [hpres₂.reg .x20, b8000b3ec_x20 h₁, I.x11]
    addr_omega [hKb, hik]
  have x25₂ : u₂.getReg .x25 = KP + BitVec.ofNat 64 (24 * min row.length lw.length) := by
    rw [hpres₂.reg .x25, k₁ .x25 (by decide), I.x25]
  have I' : R0I s r Q n KP lw rp row vs j (i + 1) v := {
    base := {
      sp := (k₃ .x2 (by decide)).trans sp₂
      fr := B.fr.trans F fun _ h ↦ h
      x9 := (reg .x9 (by decide) (by decide) (by decide)).trans B.x9
      x26 := (reg .x26 (by decide) (by decide) (by decide)).trans B.x26 }
    x8 := fun hi' ↦ by
      rw [b8000b400_x8 h₃, hpres₂.reg .x8, k₁ .x8 (by decide), I.x8 hi]
      addr_omega [hRb, hil, hi, hi']
    x11 := by rw [b8000b400_x11 h₃, x20₂]
    x25 := by rw [k₃ .x25 (by decide), x25₂]
    acc := by
      rw [b8000b400_x24 h₃, b8000b400_x23 h₃, b8000b400_x22 h₃, hpres₂.reg .x24,
        hpres₂.reg .x23, hpres₂.reg .x22, k₁ .x24 (by decide), k₁ .x23 (by decide),
        k₁ .x22 (by decide), accE_succ lw row hi, limbs_add, ← I.acc, ← hl, sp₂]
      simp only [show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval [],
        show s.getReg .x2 - 1040 + 664 = s.getReg .x2 - 384 + 8 by rv_eval [],
        show s.getReg .x2 - 1040 + 672 = s.getReg .x2 - 384 + 16 by rv_eval [],
        BitVec.xor_comm]
    x18 := (reg .x18 (by decide) (by decide) (by decide)).trans I.x18
    x19 := (reg .x19 (by decide) (by decide) (by decide)).trans I.x19
    x21 := (reg .x21 (by decide) (by decide) (by decide)).trans I.x21
    x27 := (reg .x27 (by decide) (by decide) (by decide)).trans I.x27
    vals := by
      rw [← I.vals]
      have G : DFrame u v fun y ↦ Within y (s.getReg .x2 - 384) 24 ∨
          Within y (s.getReg .x2 - 1200) 160 := fun y hy ↦ by rw [m₃, F₂ y hy, m₁]
      have hq := K.q2
      exact G.eListAt fun c hc h ↦ by
        rcases h with h | h <;> addr_omega [h, hc, hb, hab, hq, hj] }
  by_cases hlast : i + 1 = min row.length lw.length
  · refine ⟨v, hr₂.trans hr₃,
      Or.inr (Or.inl ⟨b8000b400_pc_not_taken h₃ ?_, hlast, I'⟩)⟩
    rw [x20₂, x25₂, hlast]
  · refine ⟨v, hr₂.trans hr₃, Or.inl ⟨b8000b400_pc_taken h₃ ?_, by omega, I'⟩⟩
    rw [x20₂, x25₂]
    intro he
    have := congrArg BitVec.toNat he
    have hm : min row.length lw.length ≤ lw.length := Nat.min_le_right _ _
    addr_omega [this, hKb, hik, hm, hlast]

/-- **`base_dot`'s loop**, from its first product to `0x8000b424`. -/
theorem inner0 (hMK : MulKSpec) {s r u : MachineState} {Q : Word} {n : ℕ} {KP : Word}
    {lw : List E} {rp : Word} {row : List K} {vs : List E} {j : ℕ} (hpre : VsoPre s)
    (K : R0K s r Q n KP lw) (R : R0Row s r Q n rp row) (hj : j < n)
    (hm : 0 < min row.length lw.length) (hpc : u.pc = 0x8000b3ec)
    (I : R0I s r Q n KP lw rp row vs j 0 u) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x8000b424 ∧
      R0I s r Q n KP lw rp row vs j (min row.length lw.length) v) ∨ Dead Image.code v) := by
  refine Reaches.loop (fun v ↦ ∃ i, i < min row.length lw.length ∧ v.pc = 0x8000b3ec ∧
      R0I s r Q n KP lw rp row vs j i v) (fun v ↦ min row.length lw.length - ((v.getReg .x11 -
      KP).toNat / 24)) _ (fun v ⟨i, hi, hpc, I⟩ ↦ ?_) u ⟨0, hm, hpc, I⟩
  obtain ⟨w, hr, ⟨hpc', hi', I'⟩ | ⟨hpc', hl, I'⟩ | hd⟩ :=
    inner0_step hMK hpre K R hj hi hpc I
  · refine Or.inr ⟨w, hr, ⟨i + 1, hi', hpc', I'⟩, ?_⟩
    have hK : Region KP (24 * lw.length) := by
      rcases K.kp with h | h
      · omega
      · exact h
    have hKb := Region.bounds hK
    have e (k : ℕ) (hk : k ≤ lw.length) :
        (KP + BitVec.ofNat 64 (24 * k) - KP).toNat / 24 = k := by
      rw [add_sub_cancel_left, BitVec.toNat_ofNat]
      omega
    rw [I.x11, I'.x11, e i (by omega), e (i + 1) (by omega)]
    omega
  · exact Or.inl ⟨w, hr, Or.inl ⟨hpc', hl ▸ I'⟩⟩
  · exact Or.inl ⟨w, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Pcs.Vso
