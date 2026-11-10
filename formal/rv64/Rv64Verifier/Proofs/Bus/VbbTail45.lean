import Rv64Verifier.Proofs.Bus.VbbTail44

/-!
# `verify_bus_balance`'s side loop: a block's head

From the block loop's head (`Blk`) through `0x800078f0` (the selector to `S - 272`, the owner's
check), `0x80007930` (the side's check in the owner's row, the sum so far to `S - 1128`) and
`Form::term` to `0x80007984` with `constant(beta)` at `S - 296` (`Hd`, `blkHead`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Block `k` of side `i`. -/
def blkAddr (s : MachineState) (i k : Nat) : Word := vecPtr s (blkVec s i) + BitVec.ofNat 64 (48 * k)

/-- Its owner. -/
def blkOwner (s : MachineState) (i k : Nat) : Nat := (s.getMem (blkAddr s i k + 40)).toNat

theorem mul48 (k : Nat) :
    BitVec.ofNat 64 k * 32 + BitVec.ofNat 64 k * 16 = BitVec.ofNat 64 (48 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (32 : Word).toNat = 32 from rfl, show (16 : Word).toNat = 16 from rfl]
  omega

theorem mul24 (k : Nat) :
    BitVec.ofNat 64 k * 16 + BitVec.ofNat 64 k * 8 = BitVec.ofNat 64 (24 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

theorem mul24w (w : Word) :
    w * 16 + w * 8 = BitVec.ofNat 64 (24 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

/-- A frame slot outside the scratch. -/
theorem blkW_miss {s : MachineState} (hpre : BusBalancePre s) {j : Nat} (hj : 8 ≤ j)
    (hj2 : j ≤ 1344) (h1 : j ≤ 1104 ∨ 1144 ≤ j) (h2 : j ≤ 104 ∨ 304 ≤ j) :
    ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ BlkW s y := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro y hy hw
  rcases hw with hw | hw <;> addr_omega [hy, hw, hb1, hj, hj2, h1, h2]

/-- At `0x80007984`, block `k`'s head done from the loop's head `t₀`. -/
structure Hd (s z h e t₀ t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n k : Nat) : Prop where
  cur : Cur s z h t
  fr : DFrame t₀ t (ItW s t₀ t)
  mono : heapNext t₀ ≤ heapNext t
  regs : ∀ r ∈ ([.x2, .x21, .x22, .x24, .x25] : List Reg), t.getReg r = t₀.getReg r
  x27 : t.getReg .x27 = blkAddr s i k
  own : blkOwner s i k < n
  x8 : t.getReg .x8 = vecPtr t₀ (rowAt P (blkOwner s i k))
  x20 : t.getReg .x20 = e.getMem (s.getReg .x2 - 1144)
  sel : eAt t (s.getReg .x2 - 272) = (tbSel sd point).getD k 0
  acc : eAt t (s.getReg .x2 - 1128) = eOf3 (t₀.getReg .x17) (t₀.getReg .x16) (t₀.getReg .x15)
  ok : Layout.FormOk t (s.getReg .x2 - 296)
  fbuf : ∀ x, Layout.formBuf t (s.getReg .x2 - 296) x → heapNext t₀ ≤ x.toNat ∧ x.toNat < heapNext t
  form : Layout.formOf t (s.getReg .x2 - 296) = LayoutMirror.constantRust sd.2.2.2.2

set_option maxRecDepth 8192 in
theorem blkHead (hTm : Layout.TermSpec) {s z h e t₀ : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (En : Entry s z h e i sd point P n) (B : Blk s z h e t₀ i sd point P n forms tot k)
    (hk : k < min sd.2.1.tables.length sd.1.length) (hpc : t₀.pc = 0x800078f0) :
    ∃ t, Reaches Image.code t₀ t ∧ (Dead Image.code t ∨
      (t.pc = 0x80007984 ∧ Hd s z h e t₀ t i sd point P n k)) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hab hnx
  have C₀ := B.cur
  have I₀ := C₀.inv
  have sp₀ : t₀.getReg .x2 = s.getReg .x2 - 1344 := I₀.sp
  have ht₀E := I₀.heap.hi
  have hht₀ := C₀.step.mono
  have hlo := Ih.heap.lo
  have slot (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 1104 ∨ 1144 ≤ j)
      (h2 : j ≤ 104 ∨ 304 ≤ j) :
      t₀.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    B.slots j hj hj2 (blkW_miss hpre hj hj2 h1 h2)
  -- the block
  have hro := En.bro.blocks
  have hlen : (vecLen s (blkVec s i)).toNat = sd.1.length := by
    rw [← En.blocks, blocksAt, List.length_map, List.length_range]
  rw [hlen] at hro
  have hkB : k < sd.1.length := lt_of_lt_of_le hk (min_le_right _ _)
  have hkT : k < sd.2.1.tables.length := lt_of_lt_of_le hk (min_le_left _ _)
  have hvB : ValidMemRange (vecPtr s (blkVec s i)) (6 * sd.1.length) :=
    Bus.RO.range (n := 6 * sd.1.length) (by rw [show 8 * (6 * sd.1.length) = 48 * sd.1.length by omega]; exact hro)
  have hBb := hro.bound
  have hBr := hro.region
  have hB8 : (vecPtr s (blkVec s i)).toNat % 8 = 0 := by
    rcases hBr with h0 | h0
    · omega
    · exact h0.2
  have s1192 : t₀.getMem (s.getReg .x2 - 1192) = vecPtr s (blkVec s i) :=
    (slot 1192 (by omega) (by omega) (by omega) (by omega)).trans En.blk
  -- the tables' selectors
  have x20₀ : t₀.getReg .x20 = e.getReg .x20 := B.regs .x20 (by decide)
  have hTb := En.tbBuf
  obtain ⟨T8, Tb⟩ := hTb
  have hTl := Tb.resolve_left (by omega)
  have hmE := B.mono
  simp only [heapNext, heapEnd, heapStart] at hTl ht₀E hht₀ hlo hmE
  have hvT : ValidMemRange (e.getReg .x20) (3 * sd.2.1.tables.length) :=
    heapRange T8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have x24₀ := B.x24
  have h48 := mul48 k
  have h24 := mul24 k
  -- `0x800078f0`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800078f0_spec hpc (by
    rv_eval [sp₀, x24₀, x20₀, h48, h24]
    rw [s1192]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hvB [hBb, hkB]
      | valid_access hvT [hTl, hkT, ht₀E])
  have k₁ := b800078f0_keeps h₁
  have fr₁ : DFrame t₀ t₁ (Within · (s.getReg .x2 - 272) 24) := by
    have := DFrame.of_memFrame (b800078f0_frame h₁ (by rw [sp₀]; addr_omega [hb1]))
    rw [sp₀] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have x25₀ : t₀.getReg .x25 = BitVec.ofNat 64 n := (B.regs .x25 (by decide)).trans En.x25
  have hn64 : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt En.n64
  have eo : t₀.getMem ((t₀.getMem (t₀.getReg .x2 + 152) + (t₀.getReg .x24 * 32 +
      t₀.getReg .x24 * 16)) + 40) = s.getMem (blkAddr s i k + 40) := by
    rw [sp₀, x24₀, h48]; rv_eval []; rw [s1192]
    exact I₀.word hro (by addr_omega [hBb, hkB])
      (by addr_omega [hBb, hkB])
  by_cases hown : blkOwner s i k < n
  swap
  · exact ⟨t₁, hr₁, Or.inl (dead_of_fetch (by
      rw [b800078f0_pc_taken h₁ (by rw [eo, x25₀, hn64]; exact Nat.not_lt.mp hown)]
      exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have pc₁ := b800078f0_pc_not_taken h₁ (by rw [eo, x25₀, hn64]; exact hown)
  have x10₁ : t₁.getReg .x10 = s.getMem (blkAddr s i k + 40) := by
    rw [b800078f0_x10 h₁, ← eo]
  have hn₁ : heapNext t₁ = heapNext t₀ := by
    simp only [heapNext]; rw [fr₁ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx]]
  have st₁ : StepS s t₀ t₁ (Within · (s.getReg .x2 - 272) 24) :=
    StepS.ofDFrame I₀.heap fr₁ (fun _ h ↦ h) (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx])
      (k₁ .x2 (by decide))
  have C₁ : Cur s z h t₁ := C₀.next hpre hsz st₁ fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
  -- the owner's row
  set o := blkOwner s i k with ho
  have hP := B.mat.hdr
  obtain ⟨P8, Pb⟩ := hP
  have hPl := Pb.resolve_left (by omega)
  simp only [heapNext, heapStart] at hPl
  have hvP : ValidMemRange P (3 * n) :=
    heapRange P8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hrow := (B.mat.rows o hown).2
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1344 := C₁.inv.sp
  have s1224 : t₁.getMem (s.getReg .x2 - 1224) = P := by
    rw [fr₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1]]
    exact (slot 1224 (by omega) (by omega) (by omega) (by omega)).trans En.p1224
  have hoW : (s.getMem (blkAddr s i k + 40)).toNat = o := rfl
  have h24o := mul24w (s.getMem (blkAddr s i k + 40))
  rw [hoW] at h24o
  -- `0x80007930`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007930_spec pc₁ (by
    rv_eval [sp₁, x10₁, h24o]
    rw [s1224]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hvP [hPl, hown, ht₀E]
      | addr_omega [hb1, hPl, hown, ht₀E])
  have k₂ := b80007930_keeps h₂
  have fr₂ : DFrame t₁ t₂ (Within · (s.getReg .x2 - 1128) 24) := by
    have := DFrame.of_memFrame (b80007930_frame h₂ (by rw [sp₁]; addr_omega [hb1]))
    rw [sp₁] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have rowW (j : Nat) (hj : j < 3) : t₁.getMem (rowAt P o + BitVec.ofNat 64 (8 * j)) =
      t₀.getMem (rowAt P o + BitVec.ofNat 64 (8 * j)) :=
    fr₁ _ fun x hx hw ↦ by simp only [rowAt] at hw; addr_omega [hw, hx, hb1, hPl, hown, ht₀E, hj]
  have elen : t₁.getMem ((t₁.getMem (t₁.getReg .x2 + 120) + (t₁.getReg .x10 * 16 +
      t₁.getReg .x10 * 8)) + 16) = 3 := by
    rw [sp₁, x10₁, h24o]; rv_eval []; rw [s1224]
    have := rowW 2 (by omega)
    simp only [show 8 * 2 = 16 from rfl] at this
    exact this.trans hrow
  have x22₀ : t₀.getReg .x22 = BitVec.ofNat 64 i := (B.regs .x22 (by decide)).trans En.x22
  have pc₂ := b80007930_pc_not_taken h₂ (by
    rw [elen, k₁ .x22 (by decide), x22₀]
    have := En.i3
    rw [show (3 : Word).toNat = 3 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact this)
  have x10₂ : t₂.getReg .x10 = rowAt P o := by
    rw [b80007930_x10 h₂, sp₁, x10₁, h24o]; rv_eval []; rw [s1224]; rfl
  have hn₂ : heapNext t₂ = heapNext t₁ := by
    simp only [heapNext]; rw [fr₂ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx]]
  have st₂ : StepS s t₁ t₂ (Within · (s.getReg .x2 - 1128) 24) :=
    StepS.ofDFrame C₁.inv.heap fr₂ (fun _ h ↦ h) (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx])
      (k₂ .x2 (by decide))
  have C₂ : Cur s z h t₂ := C₁.next hpre hsz st₂ fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1344 := C₂.inv.sp
  -- `0x8000795c`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000795c_spec pc₂ (by
    rv_eval [sp₂, x10₂]
    and_intros <;> first
      | valid_access hval [hb1]
      | (simp only [rowAt]; valid_access hvP [hPl, hown, ht₀E]))
  have k₃ := b8000795c_keeps h₃
  have fr₃ : DFrame t₂ t₃ (Within · (s.getReg .x2 - 248) 144) := by
    have := DFrame.of_memFrame (b8000795c_frame h₃ (by rw [sp₂]; addr_omega [hb1]))
    rw [sp₂] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have hn₃ : heapNext t₃ = heapNext t₂ := by
    simp only [heapNext]; rw [fr₃ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx]]
  have st₃ : StepS s t₂ t₃ (Within · (s.getReg .x2 - 248) 144) :=
    StepS.ofDFrame C₂.inv.heap fr₃ (fun _ h ↦ h) (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx])
      (k₃ .x2 (by decide))
  have C₃ : Cur s z h t₃ := C₂.next hpre hsz st₃ fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
  have tag₃ : t₃.getMem (s.getReg .x2 - 248) = 0 := by
    have := b8000795c_m_x2_1096 h₃; rw [sp₂] at this; rv_eval [] at this; exact this
  -- `Form::term`
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, C₄, fr₄, hm₄, ok₄, fb₄, hv₄⟩ | hd⟩ := termC hTm hpre hsz C₃
    (b8000795c_pc h₃) (by rw [b8000795c_x10 h₃, sp₂]; rv_eval [])
    (by rw [b8000795c_x11 h₃, sp₂]; rv_eval []) (by rw [b8000795c_x12 h₃, sp₂]; rv_eval []) tag₃
  swap
  · exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl hd⟩
  have hn₀₃ : heapNext t₃ = heapNext t₀ := by rw [hn₃, hn₂, hn₁]
  have hm₀₄ : heapNext t₀ ≤ heapNext t₄ := by rw [← hn₀₃]; exact hm₄
  have frA : DFrame t₀ t₄ (ItW s t₀ t₄) := by
    refine (((fr₁.mono fun a ha ↦ ?_).trans (fr₂.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
      (fr₃.mono fun a ha ↦ ?_) fun _ h ↦ h).trans (fr₄.mono fun a ha ↦ ?_) fun _ h ↦ h
    · exact Or.inl (Or.inr (by addr_omega [ha, hb1]))
    · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inl (Or.inr (by addr_omega [ha, hb1]))
    · rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl (Or.inr (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by rw [← hn₀₃]; exact a1, a2⟩))
  -- from `t₁` on, `S - 272` and `S - 1128` are kept
  have hh₄ := C₄.inv.heap.hi
  have frB : DFrame t₂ t₄ fun a ↦ Within a (s.getReg .x2 - 248) 144 ∨
      Within a (s.getReg .x2 - 296) 24 ∨ Within a (s.getReg .x2 - 4544) 3200 ∨
        Within a nextAddr 8 ∨ (heapNext t₃ ≤ a.toNat ∧ a.toNat < heapNext t₄) :=
    (fr₃.mono fun a ha ↦ Or.inl ha).trans (fr₄.mono fun a ha ↦ Or.inr ha) fun _ h ↦ h
  have keepB (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : 320 ≤ j ∨ j = 272) :
      ∀ q < 24, ¬ (Within (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 q)
        (s.getReg .x2 - 248) 144 ∨ Within (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 q)
        (s.getReg .x2 - 296) 24 ∨ Within (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 q)
        (s.getReg .x2 - 4544) 3200 ∨ Within (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 q)
        nextAddr 8 ∨ (heapNext t₃ ≤ (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 q).toNat ∧
        (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 q).toNat < heapNext t₄)) := by
    intro q hq hw
    simp only [heapNext, heapEnd] at hh₄
    rcases hw with hw | hw | hw | hw | ⟨-, hw⟩
    · addr_omega [hw, hq, hb1, hb2, hj, hj2, h1]
    · addr_omega [hw, hq, hb1, hb2, hj, hj2, h1]
    · addr_omega [hw, hq, hb1, hb2, hj, hj2]
    · addr_omega [hw, hq, hb1, hb2, hj, hj2, hnx]
    · simp only [heapNext] at hw; addr_omega [hw, hq, hb1, hb2, hj, hj2, hh₄]
  -- the selector
  have hTk : (e.getReg .x20).toNat + 24 * k + 24 ≤ heapNext e := by
    simp only [heapNext]; omega
  have rdT (j : Nat) (hj : j + 8 ≤ 24) :
      t₀.getMem (e.getReg .x20 + BitVec.ofNat 64 (24 * k) + BitVec.ofNat 64 j) =
        e.getMem (e.getReg .x20 + BitVec.ofNat 64 (24 * k) + BitVec.ofNat 64 j) :=
    B.hk _ (by simp only [heapNext]; addr_omega [hTl, hkT, hTk, hj])
      (by simp only [heapNext] at hTk; addr_omega [hTl, hkT, hTk, hj])
  have sel₁ : eAt t₁ (s.getReg .x2 - 272) = eAt e (e.getReg .x20 + BitVec.ofNat 64 (24 * k)) := by
    have e0 := b800078f0_m_x2_1072 h₁
    have e8 := b800078f0_m_x2_1080 h₁
    have e16 := b800078f0_m_x2_1088 h₁
    rw [sp₀, x20₀, x24₀, h24] at e0 e8 e16
    rv_eval [] at e0 e8 e16
    refine eAt_congr (e0.trans ?_)
      ((congrArg t₁.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans (e8.trans ?_))
      ((congrArg t₁.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans (e16.trans ?_))
    · simpa using rdT 0 (by omega)
    · exact rdT 8 (by omega)
    · exact rdT 16 (by omega)
  have sel : eAt t₄ (s.getReg .x2 - 272) = (tbSel sd point).getD k 0 := by
    have a1 : eAt t₄ (s.getReg .x2 - 272) = eAt t₂ (s.getReg .x2 - 272) :=
      frB.eAt (keepB 272 (by omega) (by omega) (by omega))
    rw [a1, fr₂.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb1], sel₁, ← En.tb, eListAt_getD _ _ hkT]
  have acc : eAt t₄ (s.getReg .x2 - 1128) =
      eOf3 (t₀.getReg .x17) (t₀.getReg .x16) (t₀.getReg .x15) := by
    have a1 : eAt t₄ (s.getReg .x2 - 1128) = eAt t₂ (s.getReg .x2 - 1128) :=
      frB.eAt (keepB 1128 (by omega) (by omega) (by omega))
    rw [a1, eAt_eq_eOf3]
    have e0 := b80007930_m_x2_216 h₂
    have e8 := b80007930_m_x2_224 h₂
    have e16 := b80007930_m_x2_232 h₂
    rw [sp₁] at e0 e8 e16
    rv_eval [] at e0 e8 e16
    rw [show t₂.getMem (s.getReg .x2 - 1128) = t₁.getReg .x17 from e0,
      show t₂.getMem (s.getReg .x2 - 1128 + 8) = t₁.getReg .x16 from
        (congrArg t₂.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans e8,
      show t₂.getMem (s.getReg .x2 - 1128 + 16) = t₁.getReg .x15 from
        (congrArg t₂.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans e16,
      k₁ .x17 (by decide), k₁ .x16 (by decide), k₁ .x15 (by decide)]
  have beta₃ : eAt t₃ (s.getReg .x2 - 128) = sd.2.2.2.2 := by
    rw [eAt_eq_eOf3]
    have e0 := b8000795c_m_x2_1216 h₃
    have e8 := b8000795c_m_x2_1224 h₃
    have e16 := b8000795c_m_x2_1232 h₃
    rw [sp₂] at e0 e8 e16
    rv_eval [] at e0 e8 e16
    rw [show t₃.getMem (s.getReg .x2 - 128) = t₂.getReg .x26 from e0,
      show t₃.getMem (s.getReg .x2 - 128 + 8) = t₂.getReg .x9 from
        (congrArg t₃.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans e8,
      show t₃.getMem (s.getReg .x2 - 128 + 16) = t₂.getReg .x18 from
        (congrArg t₃.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans e16,
      k₂ .x26 (by decide), k₂ .x9 (by decide), k₂ .x18 (by decide), k₁ .x26 (by decide),
      k₁ .x9 (by decide), k₁ .x18 (by decide), B.regs .x26 (by decide), B.regs .x9 (by decide),
      B.regs .x18 (by decide), En.x26, En.x9, En.x18]
    exact En.beta
  refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr ⟨by
    rw [hpc₄, returnAddress_eq, b8000795c_x1 h₃]; decide, ⟨C₄, frA, hm₀₄, fun r hr ↦ ?_, ?_, hown,
    ?_, ?_, sel, acc, ok₄, fun x hx ↦ ?_, by rw [hv₄, beta₃]⟩⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [hp₄.reg _ (by decide), k₃ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]
  · rw [hp₄.reg .x27, k₃ .x27 (by decide), k₂ .x27 (by decide), b800078f0_x27 h₁, sp₀, x24₀, h48]
    rv_eval []
    rw [s1192]; rfl
  · rw [hp₄.reg .x8, b8000795c_x8 h₃, x10₂, fr₂ _ fun j hj hw ↦ by
      simp only [rowAt] at hw; addr_omega [hw, hj, hb1, hPl, hown, ht₀E]]
    have := rowW 1 (by omega)
    simp only [Nat.mul_one] at this
    exact this
  · rw [hp₄.reg .x20, k₃ .x20 (by decide), b80007930_x20 h₂, sp₁]
    rv_eval []
    rw [fr₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1]]
    exact slot 1144 (by omega) (by omega) (by omega) (by omega)
  · have := fb₄ x hx
    rw [hn₀₃] at this
    exact this

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
