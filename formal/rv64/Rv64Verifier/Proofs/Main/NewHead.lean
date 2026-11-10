import Rv64Verifier.Proofs.Main.ParseEnd

/-!
# `Bytecode::new`, before its loop

From `AfterIv`: `0x80000404` empties the four `Vec`s (`blocks` at `msp + 400`, `words` at `424`,
`positions` at `448`, `bytes` at `240`), `Bump::alloc` and `memset` give `slots` (`0x20000` zero
bytes, in `s0`) and `group_of` (`0x8000`, in `s1`), and `0x80000490` stores the table's length at
`msp`: an empty table ends there (`AfterNew`), any other goes on to the blocks' loop at
`0x80000498` (`NewA`) (`new_head`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- `MInv` across a frame of bytes that misses what `main` keeps. -/
theorem MInv.bframe {s u t : MachineState} {words : List Word} {W : Word → Prop}
    (h : MInv s words u) (hf : BFrame u t W) (hsp : t.getReg .x2 = msp) (hheap : HeapOk t)
    (hk : ∀ a, W a → ¬ Kept words a) : MInv s words t where
  fits := h.fits
  sp := hsp
  slots := by
    intro p hp
    rw [← h.slots p hp]
    obtain ⟨h1, h2, h8⟩ := slot_bounds hp
    exact hf.getMem (by addr_omega [h1, h2, h8]) fun i hi hw ↦
      hk _ hw (Or.inl (by addr_omega [h1, h2, hi]))
  input := by
    intro i hi
    rw [← h.input i hi]
    have hfit := h.fits
    simp only [inputWords] at hfit
    have hib : inputBase.toNat = 0x10000000 := rfl
    exact hf.getMem (by addr_omega [hib, hi, hfit]) fun j hj hw ↦
      hk _ hw (Or.inr (Or.inl (by addr_omega [hi, hj, hfit, hib])))
  heap := hheap
  rodata := by
    intro p hp
    have hw' := within_of_mem_rodataWords hp
    have h8 : p.1.toNat % 8 = 0 := by
      simpa using List.all_eq_true.mp rodataWords_aligned' p hp
    rw [hf.getMem h8 fun i hi hw ↦ hk _ hw (Or.inr (Or.inr (by addr_omega [hw', h8, hi])))]
    exact h.rodata p hp

/-- After `Bump::alloc`: only `NEXT` changed. -/
theorem BFrame.of_alloc {s t : MachineState} (h : ∀ a, a ≠ nextAddr → t.getMem a = s.getMem a) :
    BFrame s t (Within · nextAddr 8) :=
  BFrame.of_dwords (fun a ha ↦ h a fun e ↦ ha (by rw [e]; addr_omega []))
    fun _ ha ↦ within_of_alignDown (by decide) (by decide) ha

/-- At `0x80000498`, before the blocks' loop: the four `Vec`s empty, `s0` the `slots` buffer and
`s1` `group_of`, both zero, the table's length `s3` nonzero and at `msp`. -/
structure NewA (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = 0x80000498
  len : (words.getD 0 0).toNat + 1 ≤ words.length
  pos : words.getD 0 0 ≠ 0
  n : u.getMem msp = words.getD 0 0
  x19 : u.getReg .x19 = words.getD 0 0
  x22 : u.getReg .x22 = 32768
  ptr : u.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * ((words.getD 0 0).toNat + 1))
  rest : (u.getMem (msp + 96)).toNat = words.length - ((words.getD 0 0).toNat + 1)
  iv : bytesAt u (msp + 320) 32 = Model.fiatShamirIvRust (tbl words)
  slots : (u.getReg .x8).toNat % 2 = 0 ∧ heapStart ≤ (u.getReg .x8).toNat ∧
    (u.getReg .x8).toNat + 0x20000 ≤ (u.getReg .x9).toNat
  groupOf : (u.getReg .x9).toNat % 2 = 0 ∧ (u.getReg .x9).toNat + 0x8000 ≤ heapNext u
  slotsZero : bytesAt u (u.getReg .x8) 0x20000 = List.replicate 0x20000 0
  groupOfZero : bytesAt u (u.getReg .x9) 0x8000 = List.replicate 0x8000 0
  vecs : u.getMem (msp + 400) = 0 ∧ u.getMem (msp + 408) = 8 ∧ u.getMem (msp + 416) = 0 ∧
    u.getMem (msp + 424) = 0 ∧ u.getMem (msp + 432) = 8 ∧ u.getMem (msp + 440) = 0 ∧
    u.getMem (msp + 448) = 0 ∧ u.getMem (msp + 456) = 2 ∧ u.getMem (msp + 464) = 0 ∧
    u.getMem (msp + 240) = 0 ∧ u.getMem (msp + 248) = 2 ∧ u.getMem (msp + 256) = 0

/-- What `new_head` writes: `main`'s slot for the length, the four `Vec`s' headers, `NEXT` and the
heap from `B` on. -/
def Wn (B : Nat) (a : Word) : Prop :=
  Within a msp 8 ∨ Within a (msp + 240) 232 ∨ Within a nextAddr 8 ∨
    (B ≤ a.toNat ∧ a.toNat < heapEnd)

theorem not_kept_wn {words : List Word} (hf : words.length ≤ inputWords) {B : Nat}
    (hB : heapStart ≤ B) {a : Word} (h : Wn B a) : ¬ Kept words a := by
  intro hk
  simp only [Kept, inputBase_eq] at hk
  simp only [inputWords] at hf
  simp only [heapStart] at hB
  rcases h with h | h | h | h <;> rcases hk with hk | hk | hk <;>
    addr_omega [h, hk, hf, hB]

/-- The empty `Bytecode` of an empty table. -/
theorem newRust_nil {table : List Word} (h : table.length = 0) :
    Model.newRust table = some ⟨0, Model.fiatShamirIvRust table, [], [], [], []⟩ := by
  rw [List.eq_nil_of_length_eq_zero h]
  rfl

section
variable {s u : MachineState} {words : List Word}

/-- **`Bytecode::new`, before its loop.** -/
theorem new_head (h : AfterIv s words u) :
    ∃ v, Reaches Image.code u v ∧ ((AfterNew s words v ∨ NewA s words v) ∨ Dead Image.code v) := by
  have hsp := h.inv.sp
  have hfit := h.inv.fits
  simp only [inputWords] at hfit
  have hhi := h.inv.heap.hi
  have hlo := h.inv.heap.lo
  simp only [heapStart, heapNext, heapEnd] at hhi hlo
  -- `0x80000404`: the `Vec`s, `Bump::alloc`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000404_spec h.pc (by rv_eval [hsp, msp]; decide)
  have k₁ := b80000404_keeps h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have hfr₁ := b80000404_frame h₁ (by rw [hsp]; decide)
  rw [hsp] at hfr₁
  have hb₁ : BFrame u t₁ (Within · (msp + 240) 232) := BFrame.of_memFrame hfr₁ (by decide) (by decide)
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext]; rw [hfr₁ _ (by addr_omega [])]
  have keep₁ : ∀ a : Word, (msp + 320).toNat ≤ a.toNat → a.toNat < (msp + 352).toNat →
      t₁.getMem a = u.getMem a := fun a ha1 ha2 ↦
    h₁.frame a (by rv_eval [hsp]; and_intros <;> addr_omega [ha1, ha2])
  obtain ⟨v₁, rv₁, hout⟩ := alloc_spec t₁ (b80000404_pc h₁)
    ⟨⟨by rw [hn₁]; exact h.inv.heap.lo, by rw [hn₁]; exact h.inv.heap.hi⟩,
      by rw [b80000404_x10 h₁]; decide⟩
  rcases hout with ⟨hpc₂, hpres₂, hp₂⟩ | hd
  swap
  · exact ⟨v₁, r₁.trans rv₁, Or.inr hd⟩
  have hsp₂ : v₁.getReg .x2 = msp := (hpres₂.reg .x2).trans hsp₁
  have hpc₂' : v₁.pc = 0x8000044c := by rw [hpc₂, returnAddress, b80000404_x1 h₁]; decide
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000044c_spec hpc₂' trivial
  by_cases z₃ : v₁.getReg .x10 = 0
  · obtain ⟨w, hw, hd⟩ := abort (u := t₃) (by rw [b8000044c_pc_taken h₃ z₃]; decide)
    exact ⟨w, r₁.trans (rv₁.trans (r₃.trans hw)), Or.inr hd⟩
  set SL := v₁.getReg .x10 with hSL
  have hSL2 : SL.toNat % 2 = 0 := by
    have := hp₂.aligned; rw [b80000404_x10 h₁] at this; exact this
  have hSLlo : heapNext u ≤ SL.toNat := by rw [← hn₁]; exact hp₂.above
  have hn₂ : heapNext v₁ = SL.toNat + 0x20000 := by
    rw [hp₂.next, b80000404_x11 h₁]; rfl
  have hhi₂ := hp₂.heap.hi
  simp only [heapNext, heapEnd] at hhi₂ hn₂ hSLlo
  -- `0x80000450`: `memset` of `slots`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000450_spec (b8000044c_pc_not_taken h₃ z₃) trivial
  have m₃ := b8000044c_mem_same h₃
  have k₃ := b8000044c_keeps h₃
  have k₄ := b80000450_keeps h₄
  have m₄ := b80000450_mem_same h₄
  have x10₄ : t₄.getReg .x10 = SL := by rw [k₄ .x10 (by decide), k₃ .x10 (by decide)]
  have x12₄ : (t₄.getReg .x12).toNat = 0x20000 := by rw [b80000450_x12 h₄]; rfl
  obtain ⟨v₂, rv₂, hout⟩ := Runtime.memset t₄ (b80000450_pc h₄)
    (by show Mapped (t₄.getReg .x10) (t₄.getReg .x12).toNat
        rw [x10₄, x12₄]; simp only [Mapped]; omega)
  rcases hout with ⟨hpc₅, hpres₅, hp₅⟩ | hd
  swap
  · exact ⟨v₂, r₁.trans (rv₁.trans (r₃.trans (r₄.trans rv₂))), Or.inr hd⟩
  have hsp₅ : v₂.getReg .x2 = msp := by
    rw [hpres₅.reg .x2 (by decide), k₄ .x2 (by decide), k₃ .x2 (by decide), hsp₂]
  have hb₅ : BFrame t₄ v₂ (Within · SL 0x20000) := BFrame.mono hp₅.frame.byte fun a ha ↦ by
    rw [x10₄, x12₄] at ha; exact ha
  have hz₅ : bytesAt v₂ SL 0x20000 = List.replicate 0x20000 0 := by
    have e := hp₅.bytes
    rw [x10₄, x12₄, b80000450_x11 h₄] at e
    exact e
  have hn₅ : heapNext v₂ = heapNext v₁ := by
    have e : v₂.getMem nextAddr = t₄.getMem nextAddr := hb₅.getMem (by decide) fun i hi hw ↦ by
      addr_omega [hw, hi, hn₂, hhi₂]
    simp only [heapNext, e, m₄, m₃]
  -- `0x80000464`: `Bump::alloc` of `group_of`
  have hpc₅' : v₂.pc = 0x80000464 := by rw [hpc₅, returnAddress, b80000450_x1 h₄]; decide
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b80000464_spec hpc₅' trivial
  have k₆ := b80000464_keeps h₆
  have m₆ := b80000464_mem_same h₆
  have hn₆ : heapNext t₆ = heapNext v₁ := by rw [← hn₅]; simp only [heapNext, m₆]
  obtain ⟨v₃, rv₃, hout⟩ := alloc_spec t₆ (b80000464_pc h₆)
    ⟨⟨by rw [hn₆]; exact hp₂.heap.lo, by rw [hn₆]; exact hp₂.heap.hi⟩,
      by rw [b80000464_x10 h₆]; decide⟩
  rcases hout with ⟨hpc₇, hpres₇, hp₇⟩ | hd
  swap
  · exact ⟨v₃, r₁.trans (rv₁.trans (r₃.trans (r₄.trans (rv₂.trans (r₆.trans rv₃))))), Or.inr hd⟩
  have hsp₇ : v₃.getReg .x2 = msp := by
    rw [hpres₇.reg .x2 (by decide), k₆ .x2 (by decide), hsp₅]
  have hpc₇' : v₃.pc = 0x80000474 := by rw [hpc₇, returnAddress, b80000464_x1 h₆]; decide
  obtain ⟨t₈, r₈, h₈⟩ := Sym.BlockSpec.reaches b80000474_spec hpc₇' trivial
  by_cases z₈ : v₃.getReg .x10 = 0
  · obtain ⟨w, hw, hd⟩ := abort (u := t₈) (by rw [b80000474_pc_taken h₈ z₈]; decide)
    exact ⟨w, r₁.trans (rv₁.trans (r₃.trans (r₄.trans (rv₂.trans (r₆.trans (rv₃.trans
      (r₈.trans hw))))))), Or.inr hd⟩
  set GO := v₃.getReg .x10 with hGO
  have hGO2 : GO.toNat % 2 = 0 := by
    have := hp₇.aligned; rw [b80000464_x10 h₆] at this; exact this
  have hGOlo : heapNext t₆ ≤ GO.toNat := hp₇.above
  have hn₇ : heapNext v₃ = GO.toNat + 0x8000 := by
    rw [hp₇.next, b80000464_x11 h₆]; rfl
  have hhi₇ := hp₇.heap.hi
  rw [hn₆] at hGOlo
  simp only [heapNext, heapEnd] at hhi₇ hn₇ hGOlo
  -- `0x80000478`: `memset` of `group_of`
  obtain ⟨t₉, r₉, h₉⟩ := Sym.BlockSpec.reaches b80000478_spec (b80000474_pc_not_taken h₈ z₈) trivial
  have m₈ := b80000474_mem_same h₈
  have k₈ := b80000474_keeps h₈
  have k₉ := b80000478_keeps h₉
  have m₉ := b80000478_mem_same h₉
  have x10₉ : t₉.getReg .x10 = GO := by rw [k₉ .x10 (by decide), k₈ .x10 (by decide)]
  have x12₉ : (t₉.getReg .x12).toNat = 0x8000 := by rw [b80000478_x12 h₉]; rfl
  obtain ⟨v₄, rv₄, hout⟩ := Runtime.memset t₉ (b80000478_pc h₉)
    (by show Mapped (t₉.getReg .x10) (t₉.getReg .x12).toNat
        rw [x10₉, x12₉]; simp only [Mapped]; omega)
  rcases hout with ⟨hpc₁₀, hpres₁₀, hp₁₀⟩ | hd
  swap
  · exact ⟨v₄, r₁.trans (rv₁.trans (r₃.trans (r₄.trans (rv₂.trans (r₆.trans (rv₃.trans
      (r₈.trans (r₉.trans rv₄)))))))), Or.inr hd⟩
  have hb₁₀ : BFrame t₉ v₄ (Within · GO 0x8000) := BFrame.mono hp₁₀.frame.byte fun a ha ↦ by
    rw [x10₉, x12₉] at ha; exact ha
  have hz₁₀ : bytesAt v₄ GO 0x8000 = List.replicate 0x8000 0 := by
    have e := hp₁₀.bytes
    rw [x10₉, x12₉, b80000478_x11 h₉] at e
    exact e
  have hsp₁₀ : v₄.getReg .x2 = msp := by
    rw [hpres₁₀.reg .x2 (by decide), k₉ .x2 (by decide), k₈ .x2 (by decide), hsp₇]
  have hn₁₀ : heapNext v₄ = heapNext v₃ := by
    have e : v₄.getMem nextAddr = t₉.getMem nextAddr := hb₁₀.getMem (by decide) fun i hi hw ↦ by
      addr_omega [hw, hi, hn₇, hhi₇]
    simp only [heapNext, e, m₉, m₈]
  -- `0x80000490`: the length at `msp`
  have hpc₁₀' : v₄.pc = 0x80000490 := by rw [hpc₁₀, returnAddress, b80000478_x1 h₉]; decide
  obtain ⟨t₁₁, r₁₁, h₁₁⟩ := Sym.BlockSpec.reaches b80000490_spec hpc₁₀' (by rv_eval [hsp₁₀, msp]; decide)
  have k₁₁ := b80000490_keeps h₁₁
  have hsp₁₁ : t₁₁.getReg .x2 = msp := by rw [k₁₁ .x2 (by decide), hsp₁₀]
  have hfr₁₁ := b80000490_frame h₁₁ (by rw [hsp₁₀]; decide)
  rw [hsp₁₀] at hfr₁₁
  have hb₁₁ : BFrame v₄ t₁₁ (Within · msp 8) := BFrame.of_memFrame hfr₁₁ (by decide) (by decide)
  have hn₁₁ : heapNext t₁₁ = heapNext v₄ := by simp only [heapNext]; rw [hfr₁₁ _ (by addr_omega [])]
  -- the frames
  have g : BFrame t₁ t₁₁ fun a ↦ Within a nextAddr 8 ∨ (heapNext u ≤ a.toNat ∧ a.toNat < heapEnd) ∨
      Within a msp 8 := by
    have g0 : BFrame t₁ v₁ fun a ↦ Within a nextAddr 8 ∨
        (heapNext u ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a msp 8 :=
      BFrame.mono (BFrame.of_alloc hp₂.mem) fun a ha ↦ Or.inl ha
    have g1 : BFrame t₁ t₄ fun a ↦ Within a nextAddr 8 ∨
        (heapNext u ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a msp 8 :=
      g0.trans (BFrame.of_same (fun a ↦ by rw [m₄, m₃]) _) fun _ h ↦ h
    have g2 : BFrame t₁ v₂ fun a ↦ Within a nextAddr 8 ∨
        (heapNext u ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a msp 8 :=
      g1.trans hb₅ fun a ha ↦ Or.inr (Or.inl
        ⟨by simp only [Within] at ha; simp only [heapNext] at hSLlo ⊢; omega,
          by simp only [Within] at ha; simp only [heapEnd]; omega⟩)
    have g3 : BFrame t₁ v₃ fun a ↦ Within a nextAddr 8 ∨
        (heapNext u ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a msp 8 :=
      (g2.trans (BFrame.of_same m₆ _) fun _ h ↦ h).trans (BFrame.of_alloc hp₇.mem)
        fun a ha ↦ Or.inl ha
    have g4 : BFrame t₁ v₄ fun a ↦ Within a nextAddr 8 ∨
        (heapNext u ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a msp 8 :=
      (g3.trans (BFrame.of_same (fun a ↦ by rw [m₉, m₈]) _) fun _ h ↦ h).trans hb₁₀
        fun a ha ↦ Or.inr (Or.inl ⟨by simp only [Within] at ha; simp only [heapNext] at hSLlo ⊢; omega,
          by simp only [Within] at ha; simp only [heapEnd]; omega⟩)
    exact g4.trans hb₁₁ fun a ha ↦ Or.inr (Or.inr ha)
  have hB : BFrame u t₁₁ (Wn (heapNext u)) :=
    ((BFrame.refl u _).trans hb₁ fun a ha ↦ Or.inr (Or.inl ha)).trans g fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ha))
      · exact Or.inl ha
  have hnt : heapNext t₁₁ = GO.toNat + 0x8000 := by
    rw [hn₁₁, hn₁₀]; simp only [heapNext]; exact hn₇
  have heap₁₁ : HeapOk t₁₁ := ⟨by rw [hnt]; simp only [heapStart]; omega,
    by rw [hnt]; simp only [heapEnd]; omega⟩
  have hinv : MInv s words t₁₁ := h.inv.bframe hB hsp₁₁ heap₁₁ fun a ha ↦
    not_kept_wn h.inv.fits h.inv.heap.lo ha
  have keepU : ∀ a : Word, a.toNat % 8 = 0 → (∀ i < 8, ¬ Wn (heapNext u) (a + BitVec.ofNat 64 i)) →
      t₁₁.getMem a = u.getMem a := fun a h8 ha ↦ hB.getMem h8 ha
  have keepT : ∀ c : Nat, c % 8 = 0 → 240 ≤ c → c + 8 ≤ 472 →
      t₁₁.getMem (msp + BitVec.ofNat 64 c) = t₁.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 h1 h2
    refine g.getMem (by addr_omega [h8, h1, h2]) fun i hi hw ↦ ?_
    rcases hw with hw | ⟨hw1, hw2⟩ | hw
    · addr_omega [hw, hi, h1, h2]
    · simp only [heapEnd] at hw2; addr_omega [hw2, hi, h1, h2]
    · addr_omega [hw, hi, h1, h2]
  have x19 : t₁₁.getReg .x19 = words.getD 0 0 := by
    rw [k₁₁ .x19 (by decide), hpres₁₀.reg .x19 (by decide), k₉ .x19 (by decide),
      k₈ .x19 (by decide), hpres₇.reg .x19 (by decide), k₆ .x19 (by decide),
      hpres₅.reg .x19 (by decide), k₄ .x19 (by decide), k₃ .x19 (by decide),
      hpres₂.reg .x19 (by decide), k₁ .x19 (by decide), h.n]
  have hm0 : t₁₁.getMem msp = words.getD 0 0 := by
    have e := b80000490_m_x2_0 h₁₁
    rw [hsp₁₀, hpres₁₀.reg .x19 (by decide), k₉ .x19 (by decide), k₈ .x19 (by decide),
      hpres₇.reg .x19 (by decide), k₆ .x19 (by decide), hpres₅.reg .x19 (by decide),
      k₄ .x19 (by decide), k₃ .x19 (by decide), hpres₂.reg .x19 (by decide), k₁ .x19 (by decide),
      h.n] at e
    exact e
  have hptr : t₁₁.getMem (msp + 88) = u.getMem (msp + 88) := keepU _ (by decide) fun i hi hw ↦ by
    rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
    · addr_omega [hw, hi]
    · addr_omega [hw, hi]
    · addr_omega [hw, hi]
    · simp only [heapEnd] at hw2; addr_omega [hw2, hi]
  have hrest : t₁₁.getMem (msp + 96) = u.getMem (msp + 96) := keepU _ (by decide) fun i hi hw ↦ by
    rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
    · addr_omega [hw, hi]
    · addr_omega [hw, hi]
    · addr_omega [hw, hi]
    · simp only [heapEnd] at hw2; addr_omega [hw2, hi]
  have hiv : bytesAt t₁₁ (msp + 320) 32 = Model.fiatShamirIvRust (tbl words) := by
    rw [← h.iv, g.bytesAt fun i hi hw ↦ by
      rcases hw with hw | ⟨hw1, hw2⟩ | hw
      · addr_omega [hw, hi]
      · simp only [heapEnd] at hw2; addr_omega [hw2, hi]
      · addr_omega [hw, hi]]
    refine bytesAt_dframe fun i hi ↦ ?_
    have ha := toNat_alignDown (msp + 320 + BitVec.ofNat 64 i)
    exact keep₁ _ (by addr_omega [ha, hi]) (by addr_omega [ha, hi])
  have v400 : t₁₁.getMem (msp + 400) = 0 :=
    (keepT 400 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_400 h₁; rw [hsp] at e; exact e)
  have v408 : t₁₁.getMem (msp + 408) = 8 :=
    (keepT 408 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_408 h₁; rw [hsp] at e; exact e)
  have v416 : t₁₁.getMem (msp + 416) = 0 :=
    (keepT 416 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_416 h₁; rw [hsp] at e; exact e)
  have v424 : t₁₁.getMem (msp + 424) = 0 :=
    (keepT 424 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_424 h₁; rw [hsp] at e; exact e)
  have v432 : t₁₁.getMem (msp + 432) = 8 :=
    (keepT 432 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_432 h₁; rw [hsp] at e; exact e)
  have v440 : t₁₁.getMem (msp + 440) = 0 :=
    (keepT 440 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_440 h₁; rw [hsp] at e; exact e)
  have v448 : t₁₁.getMem (msp + 448) = 0 :=
    (keepT 448 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_448 h₁; rw [hsp] at e; exact e)
  have v456 : t₁₁.getMem (msp + 456) = 2 :=
    (keepT 456 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_456 h₁; rw [hsp] at e; exact e)
  have v464 : t₁₁.getMem (msp + 464) = 0 :=
    (keepT 464 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_464 h₁; rw [hsp] at e; exact e)
  have v240 : t₁₁.getMem (msp + 240) = 0 :=
    (keepT 240 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_240 h₁; rw [hsp] at e; exact e)
  have v248 : t₁₁.getMem (msp + 248) = 2 :=
    (keepT 248 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_248 h₁; rw [hsp] at e; exact e)
  have v256 : t₁₁.getMem (msp + 256) = 0 :=
    (keepT 256 (by decide) (by decide) (by decide)).trans (by
      have e := b80000404_m_x2_256 h₁; rw [hsp] at e; exact e)
  have r : Reaches Image.code u t₁₁ := r₁.trans (rv₁.trans (r₃.trans (r₄.trans (rv₂.trans
    (r₆.trans (rv₃.trans (r₈.trans (r₉.trans (rv₄.trans r₁₁)))))))))
  have hx19 : v₄.getReg .x19 = words.getD 0 0 := by rw [← k₁₁ .x19 (by decide)]; exact x19
  have x8₁₁ : t₁₁.getReg .x8 = SL := by
    rw [k₁₁ .x8 (by decide), hpres₁₀.reg .x8 (by decide), k₉ .x8 (by decide), k₈ .x8 (by decide),
      hpres₇.reg .x8 (by decide), k₆ .x8 (by decide), hpres₅.reg .x8 (by decide), b80000450_x8 h₄,
      k₃ .x10 (by decide)]
  have x9₁₁ : t₁₁.getReg .x9 = GO := by
    rw [k₁₁ .x9 (by decide), hpres₁₀.reg .x9 (by decide), b80000478_x9 h₉, k₈ .x10 (by decide)]
  have gs : BFrame v₂ t₁₁ fun a ↦ Within a nextAddr 8 ∨ Within a GO 0x8000 ∨ Within a msp 8 := by
    have e0 : BFrame v₂ v₃ fun a ↦ Within a nextAddr 8 ∨ Within a GO 0x8000 ∨ Within a msp 8 :=
      ((BFrame.of_same m₆ _).trans (BFrame.of_alloc hp₇.mem) fun a ha ↦ Or.inl ha)
    exact ((e0.trans (BFrame.of_same (fun a ↦ by rw [m₉, m₈]) _) fun _ h ↦ h).trans hb₁₀
      fun a ha ↦ Or.inr (Or.inl ha)).trans hb₁₁ fun a ha ↦ Or.inr (Or.inr ha)
  by_cases z : v₄.getReg .x19 = 0
  · -- an empty table
    have hN : (words.getD 0 0).toNat = 0 := by rw [← hx19, z]; rfl
    refine ⟨t₁₁, r, Or.inl (Or.inl ⟨hinv, b80000490_pc_taken h₁₁ z, h.len, hm0, by rw [hptr, h.ptr],
      by rw [hrest, h.rest], hiv, ⟨_, newRust_nil (by rw [tbl_length h.len, hN]), ?_⟩⟩)⟩
    have hS := hinv.heap.lo
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [vecPtr, vecLen, Buf]
    · rw [show (msp + 400 + 16 : Word) = msp + 416 from rfl, v416]; rfl
    · rw [show (msp + 424 + 8 : Word) = msp + 432 from rfl, show (msp + 424 + 16 : Word) = msp + 440
        from rfl, v440]; rfl
    · rw [show (msp + 448 + 16 : Word) = msp + 464 from rfl, v464]; rfl
    · rw [show (msp + 240 + 16 : Word) = msp + 256 from rfl, v256]; rfl
    · rw [show (msp + 400 + 8 : Word) = msp + 408 from rfl, v408,
        show (msp + 400 + 16 : Word) = msp + 416 from rfl, v416]; exact ⟨rfl, Or.inl rfl⟩
    · rw [show (msp + 424 + 8 : Word) = msp + 432 from rfl, v432,
        show (msp + 424 + 16 : Word) = msp + 440 from rfl, v440]; exact ⟨rfl, Or.inl rfl⟩
    · rw [show (msp + 448 + 8 : Word) = msp + 456 from rfl, v456,
        show (msp + 448 + 16 : Word) = msp + 464 from rfl, v464]; exact ⟨rfl, Or.inl rfl⟩
    · rw [show (msp + 240 + 8 : Word) = msp + 248 from rfl, v248,
        show (msp + 240 + 16 : Word) = msp + 256 from rfl, v256]; exact ⟨rfl, Or.inl rfl⟩
    · rw [show (msp + 400 + 8 : Word) = msp + 408 from rfl, v408]; exact le_trans (by decide) hS
    · rw [show (msp + 424 + 8 : Word) = msp + 432 from rfl, v432]; exact le_trans (by decide) hS
    · rw [show (msp + 448 + 8 : Word) = msp + 456 from rfl, v456]; exact le_trans (by decide) hS
    · rw [show (msp + 240 + 8 : Word) = msp + 248 from rfl, v248]; exact le_trans (by decide) hS
  · refine ⟨t₁₁, r, Or.inl (Or.inr ⟨hinv, b80000490_pc_not_taken h₁₁ z, h.len,
      by rw [← hx19]; exact z, hm0, x19, ?_, by rw [hptr, h.ptr], by rw [hrest, h.rest], hiv, ?_, ?_,
      ?_, ?_, ⟨v400, v408, v416, v424, v432, v440, v448, v456, v464, v240, v248, v256⟩⟩)⟩
    · rw [k₁₁ .x22 (by decide), hpres₁₀.reg .x22 (by decide), b80000478_x22 h₉]
    · rw [x8₁₁, x9₁₁]; exact ⟨hSL2, by simp only [heapStart]; omega, by omega⟩
    · rw [x9₁₁, hnt]; exact ⟨hGO2, le_refl _⟩
    · rw [x8₁₁, gs.bytesAt fun i hi hw ↦ by
        rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hn₂, hGOlo, hhi₂, hhi₇]]
      exact hz₅
    · rw [x9₁₁, hb₁₁.bytesAt fun i hi hw ↦ by addr_omega [hw, hi, hn₇, hhi₇]]
      exact hz₁₀

end

end Rv64Verifier.Proofs.Main
