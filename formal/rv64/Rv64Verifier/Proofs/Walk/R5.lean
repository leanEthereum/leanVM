import Rv64Verifier.Proofs.Walk.Head

/-!
# `walk`: `table_log_heights` (R5)

From `0x80001338` (`Head`): `alloc(8, 48)` (null traps), the `Vec` {6, `Q`, 0} at `sp + 1728`,
`Vec<K>::reserve(6)` (room enough: `ReserveFastSpec`), then six unrolled
`log2_ceil(rows[i]).max(floor)`. RV64IM has no `clz`: each smears `rows[i].saturating_sub(1)`
(`ssub`), counts the ones of its complement (`popW`, skipped for zero, which gives `64` too) and
stores `64 - popW` (`height_eq`: `log2CeilRust`); the KECCAK one is `max(_, 9)`. Then the spills,
an empty `Flushes` at `sp + 1168` and the call of `Flushes::state_step` (`AtR5`, at its entry).

Every write lies in the heights' buffer or in frame slots apart from the transcript and
`log_bytecode`'s slot (`R5W`), so `Head` carries over (`Head.r5`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Local writes -/

/-- What a step may write: the frame below the saved registers but the transcript, and the heap
allocated since the entry. -/
def LocalW (s u : MachineState) (a : Word) : Prop :=
  ((s.getReg .x2 - 2656).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 104).toNat ∧
    ¬ Within a (tp s) 368) ∨ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext u)

theorem localStep {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) (fr : DFrame u v (LocalW s u))
    (sp : v.getReg .x2 = u.getReg .x2) :
    Inv s v ∧ heapNext v = heapNext u ∧
      ∀ T, TranscriptAt u (tp s) T → TranscriptAt v (tp s) T := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := h.heap.hi
  have hm := h.mono
  simp only [heapEnd] at hh
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    refine congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ ?_)
    simp only [LocalW, Within, tp, heapNext] at hw hh
    rcases hw with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
    · addr_omega [hi, h1, h2, hb1]
    · addr_omega [hi, h2, hh]
  have hv : HeapOk v := ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩
  refine ⟨h.step hpre fr (fun a ha ↦ ?_) hv hn.ge sp, hn, fun T hT ↦ ?_⟩
  · rcases ha with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inr (Or.inl (by rw [stackLo_eq, stack_eq]; simp only [Within]; addr_omega [h1, h2, hb1])),
        by simp only [Within]; addr_omega [h1, h2, hb1]⟩
    · refine ⟨Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩)), ?_⟩
      simp only [Within, heapNext] at h2 hh ⊢
      addr_omega [h2, hh, hb1]
  · obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
    have pRO := hpre.proofRO
    have sRO := hpre.streamRO
    have hP := hpre.proof
    simp only [ReadOnly, Outside, stack_eq, heapEnd] at pRO sRO
    obtain ⟨⟨p1, -⟩, p2, -⟩ := pRO
    obtain ⟨⟨s1, -⟩, s2, -⟩ := sRO
    refine fr.transcriptAt hT (tok hpre h hptr) ?_ ?_ ?_ ?_
    · intro y hy hw
      rcases hw with ⟨-, -, h3⟩ | ⟨-, h2⟩
      · exact h3 (by simp only [Within] at hy ⊢; omega)
      · simp only [Within, tp, heapNext] at hy h2 hh; addr_omega [hy, h2, hh, hb1]
    · rw [e0]; intro y hy hw
      rcases hw with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
      · simp only [Within] at hy; addr_omega [hy, h1, h2, p2, hb1]
      · simp only [Within] at hy; omega
    · rw [e1, e2]; intro y hy hw
      rcases hw with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
      · simp only [Within] at hy; addr_omega [hy, h1, h2, s2, hb1]
      · simp only [Within] at hy; omega
    · intro y hy hw
      rcases hw with ⟨-, -, h3⟩ | ⟨-, h2⟩
      · exact h3 (by simp only [Within, tp] at hy ⊢; addr_omega [hy, hb1])
      · simp only [Within, tp, heapNext] at hy h2 hh; addr_omega [hy, h2, hh, hb1]

/-! ## `Head` along `table_log_heights` -/

/-- The registers `Head` reads. -/
def headRegs : List Reg := [.x2, .x8, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]

theorem Head.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} (hpre : WalkPre s) (h : Head OI s u A k)
    (hm : ∀ a, v.getMem a = u.getMem a) (hr : ∀ r ∈ headRegs, v.getReg r = u.getReg r) :
    Head OI s v A k := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  have x18 := hr .x18 (by decide)
  exact {
    inv := h.inv.same hm (hr .x2 (by decide))
    regs := h.regs.keep fun r hr' ↦ hr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    proofPtr := by rw [hm]; exact h.proofPtr
    checked := by
      have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (hm _)]; exact h.checked
    x26 := by rw [hr .x26 (by decide)]; exact h.x26
    x8 := by rw [hr .x8 (by decide)]; exact h.x8
    x25 := by rw [hr .x25 (by decide)]; exact h.x25
    buf := by rw [x18, hn]; exact h.buf
    rows := by simp only [x18, hm]; exact h.rows
    lb := by rw [hm]; exact h.lb
    ok := h.ok
    rate := h.rate
    tracks := h.tracks.keep fun T hT ↦ TranscriptAt.same hpre h.inv h.proofPtr hm hT }

/-- What `table_log_heights` writes: the heights' buffer at `Q` and frame slots (`sp + 72 ..
sp + 160`, `sp + 168 .. sp + 200`, `sp + 1168 .. sp + 1752`). -/
def R5W (s : MachineState) (Q a : Word) : Prop :=
  Within a Q 48 ∨ Within a (s.getReg .x2 - 2584) 88 ∨ Within a (s.getReg .x2 - 2488) 32 ∨
    Within a (s.getReg .x2 - 1488) 584

theorem Head.r5 {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (h : Head OI s u A k)
    (hQ : heapNext s ≤ Q.toNat ∧ (u.getReg .x18).toNat + 48 ≤ Q.toNat ∧ Q.toNat + 48 ≤ heapNext u)
    (fr : DFrame u v (R5W s Q)) (hr : ∀ r ∈ headRegs, v.getReg r = u.getReg r) :
    Head OI s v A k := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have lw : ∀ a, R5W s Q a → LocalW s u a := fun a ha ↦ by
    simp only [R5W, Within] at ha
    rcases ha with ha | ha | ha | ha
    · exact Or.inr ⟨by omega, by omega⟩
    all_goals exact Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1],
      by simp only [Within, tp]; addr_omega [ha, hb1]⟩
  obtain ⟨Iv, hn, hT⟩ := localStep hpre h.inv h.proofPtr (fr.mono lw) (hr .x2 (by decide))
  have x18 := hr .x18 (by decide)
  have hu := h.buf
  have stk (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 2584).toNat ∨
        (s.getReg .x2 - 2496).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 2488).toNat ∨
        (s.getReg .x2 - 2456).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2 - 1488).toNat)
      (h3 : x.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem x = u.getMem x :=
    fr x fun i hi hw ↦ by
      simp only [R5W, Within] at hw
      rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, h1, h2, h3, hb1, hQ, hh]
  have hrow (j : Word) (hj : j.toNat ≤ 40) : v.getMem (u.getReg .x18 + j) = u.getMem (u.getReg .x18 + j) :=
    fr _ fun i hi hw ↦ by
      simp only [R5W, Within] at hw
      rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, hj, hb1, hQ, hh, hu]
  exact {
    inv := Iv
    regs := h.regs.keep fun r hr' ↦ hr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    proofPtr := by
      rw [stk _ (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1])]
      exact h.proofPtr
    checked := by
      have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (stk _ (by rw [tp]; addr_omega [hb1]) (by rw [tp]; addr_omega [hb1])
        (by rw [tp]; addr_omega [hb1]))]
      exact h.checked
    x26 := by rw [hr .x26 (by decide)]; exact h.x26
    x8 := by rw [hr .x8 (by decide)]; exact h.x8
    x25 := by rw [hr .x25 (by decide)]; exact h.x25
    buf := by rw [x18, hn]; exact h.buf
    rows := by
      have e0 : v.getMem (u.getReg .x18) = u.getMem (u.getReg .x18) := by
        simpa using hrow 0 (by decide)
      rw [x18, e0, hrow 8 (by decide), hrow 16 (by decide), hrow 24 (by decide),
        hrow 32 (by decide), hrow 40 (by decide)]
      exact h.rows
    lb := by
      rw [stk _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])]
      exact h.lb
    ok := h.ok
    rate := h.rate
    tracks := h.tracks.keep hT }

/-- An allocation keeps `Head`. -/
theorem Head.heap {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} (hpre : WalkPre s) (h : Head OI s u A k) (hv : HeapOk v)
    (fr : DFrame u v (HeapW u v)) (mono : heapNext u ≤ heapNext v)
    (hr : ∀ r ∈ headRegs, v.getReg r = u.getReg r) : Head OI s v A k := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have x18 := hr .x18 (by decide)
  have hu := h.buf
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have stk (x : Word) (hy : (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem x = u.getMem x := HeapW.frame hpre hv fr hy
  have hrow (j : Word) (hj : j.toNat ≤ 40) : v.getMem (u.getReg .x18 + j) = u.getMem (u.getReg .x18 + j) :=
    fr _ fun i hi hw ↦ by
      simp only [HeapW, Fresh, Within, heapNext] at hw hu
      rcases hw with hw | ⟨hw, -⟩ <;> addr_omega [hw, hi, hj, hu, hh]
  exact {
    inv := h.inv.loc hpre (fr.mono fun _ h ↦ h.loc) hv mono (hr .x2 (by decide))
    regs := h.regs.keep fun r hr' ↦ hr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    proofPtr := by rw [stk _ (by rw [tp]; constructor <;> addr_omega [hb1])]; exact h.proofPtr
    checked := by
      have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (stk _ (by rw [tp]; constructor <;> addr_omega [hb1]))]
      exact h.checked
    x26 := by rw [hr .x26 (by decide)]; exact h.x26
    x8 := by rw [hr .x8 (by decide)]; exact h.x8
    x25 := by rw [hr .x25 (by decide)]; exact h.x25
    buf := by rw [x18]; exact ⟨hu.1, hu.2.1, by omega⟩
    rows := by
      have e0 : v.getMem (u.getReg .x18) = u.getMem (u.getReg .x18) := by
        simpa using hrow 0 (by decide)
      rw [x18, e0, hrow 8 (by decide), hrow 16 (by decide), hrow 24 (by decide),
        hrow 32 (by decide), hrow 40 (by decide)]
      exact h.rows
    lb := by rw [stk _ (by constructor <;> addr_omega [hb1])]; exact h.lb
    ok := h.ok
    rate := h.rate
    tracks := h.tracks.keep fun T hT ↦ TranscriptAt.heap hpre h.inv h.proofPtr hv fr hT }

/-! ## `log2_ceil` as compiled -/

/-- `rows.saturating_sub(1)` as compiled: `rows - (0 <ᵤ rows)`. -/
def ssub (r : Word) : Word := r - (if BitVec.ult 0 r then 1 else 0)

/-- `count_ones(!smear(y))`, the popcount blocks' result. -/
def popW (y : Word) : Word := popSwar (smear y ^^^ 0xffffffffffffffff)

theorem ssub_eq (r : Word) : ssub r = satSubOne r := by
  unfold ssub satSubOne
  by_cases h : r = 0#64
  · subst h; decide
  · have h0 : r.toNat ≠ 0 := fun h0 ↦ h (BitVec.eq_of_toNat_eq h0)
    have : BitVec.ult 0 r = true := by
      have e : (0 : Word).toNat = 0 := rfl
      simp only [BitVec.ult, decide_eq_true_eq, e]; omega
    simp only [this, h, ↓reduceIte]
    rfl

theorem popW_zero : popW 0 = 64 := by decide +kernel

theorem height_eq (r : Word) :
    (64 : Word) - popW (ssub r) = BitVec.ofNat 64 (log2CeilRust r) := by
  unfold popW log2CeilRust
  rw [ssub_eq]
  have hx : smear (satSubOne r) ^^^ 0xffffffffffffffff = ~~~ smear (satSubOne r) := by
    rw [show (0xffffffffffffffff : Word) = BitVec.allOnes 64 from rfl]
    exact BitVec.xor_allOnes
  rw [hx, pop_smear]
  have hc : (satSubOne r).clz.toNat ≤ 64 := by
    have := BitVec.clz_le (x := satSubOne r); simpa [BitVec.le_def] using this
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have e64 : (64 : Word).toNat = 64 := rfl
  rw [e64, Nat.mod_eq_of_lt (by omega : (satSubOne r).clz.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 64 - (satSubOne r).clz.toNat < 2 ^ 64)]
  omega

/-- The popcount, run or skipped: zero gives `64`. -/
theorem popW_skip {y : Word} (h : y = 0) : (64 : Word) = popW y := by rw [h, popW_zero]

theorem b80001394_x11' {s t : MachineState} (h : b80001394.Holds s t) :
    t.getReg .x11 = popW (s.getReg .x10) := h.reg_eq .x11 rfl rfl
theorem b8000145c_x12' {s t : MachineState} (h : b8000145c.Holds s t) :
    t.getReg .x12 = popW (s.getReg .x11) := h.reg_eq .x12 rfl rfl
theorem b80001520_x13' {s t : MachineState} (h : b80001520.Holds s t) :
    t.getReg .x13 = popW (s.getReg .x12) := h.reg_eq .x13 rfl rfl
theorem b800015dc_x11' {s t : MachineState} (h : b800015dc.Holds s t) :
    t.getReg .x11 = popW (s.getReg .x12) := h.reg_eq .x11 rfl rfl
theorem b800016a0_x13' {s t : MachineState} (h : b800016a0.Holds s t) :
    t.getReg .x13 = popW (s.getReg .x11) := h.reg_eq .x13 rfl rfl
theorem b8000175c_x12' {s t : MachineState} (h : b8000175c.Holds s t) :
    t.getReg .x12 = popW (s.getReg .x11) := h.reg_eq .x12 rfl rfl

theorem b80001370_x10' {s t : MachineState} (h : b80001370.Holds s t) :
    t.getReg .x10 = ssub (s.getMem (s.getReg .x18)) := h.reg_eq .x10 rfl rfl
theorem b80001370_pc' {s t : MachineState} (h : b80001370.Holds s t) :
    t.pc = if (ssub (s.getMem (s.getReg .x18)) == 0) = true then 0x80001438 else 0x80001394 :=
  h.pc_eq rfl

/-! ## The allocation and `reserve(6)` -/

theorem headRegs_sub : ∀ r ∈ headRegs, r ∈ calleeSaved := by decide

/-- At `0x80001370`: `table_log_heights`' `Vec` {cap 6, `Q`, len 0} at `sp + 1728`, its buffer
allocated past `table_rows`, `reserve(6)` done. -/
structure HtA (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (Q : Word) : Prop extends Head OI s u A k where
  q : heapNext s ≤ Q.toNat ∧ Q.toNat % 8 = 0 ∧ (u.getReg .x18).toNat + 48 ≤ Q.toNat ∧
    Q.toNat + 48 ≤ heapNext u
  vec : u.getMem (s.getReg .x2 - 928) = 6 ∧ u.getMem (s.getReg .x2 - 920) = Q ∧
    u.getMem (s.getReg .x2 - 912) = 0

set_option maxRecDepth 8192 in
/-- `alloc(8, 48)` (null traps), the `Vec` at `sp + 1728`, `reserve(6)` (room enough). -/
theorem heightsAlloc (hAS : AllocSpec) (hRF : ReserveFastSpec 0x8000d628)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x80001338) (h : Head OI s u A k) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001370 ∧ ∃ Q, HtA OI s t A k Q) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hlo := h.inv.heap.lo
  have hmono := h.inv.mono
  have hbuf := h.buf
  simp only [heapStart] at hlo
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001338_spec hpc (by rv_eval [])
  have m₁ := b80001338_mem_same h₁
  have k₁ := b80001338_keeps h₁
  have H₁ : Head OI s u₁ A k := h.same hpre m₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have pre₁ : AllocPre u₁ := ⟨⟨by rw [hn₁]; exact h.inv.heap.lo, by rw [hn₁]; exact h.inv.heap.hi⟩,
    by rw [b80001338_x10 h₁]; decide⟩
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post₂⟩ | hd⟩ := hAS.call (Reaches.refl u₁) (b80001338_pc h₁) pre₁
  swap
  · exact ⟨u₂, hr₁.trans hr₂, Or.inr hd⟩
  have hal := post₂.aligned
  have hab := post₂.above
  have hnx := post₂.next
  rw [b80001338_x10 h₁] at hal
  rw [b80001338_x11 h₁] at hnx
  have e8 : (8 : Word).toNat = 8 := rfl
  have e48 : (48 : Word).toNat = 48 := rfl
  rw [e8] at hal
  rw [e48] at hnx
  rw [hn₁] at hab
  set Q := u₂.getReg .x10 with hQ
  have fr₂ : DFrame u₁ u₂ (HeapW u₁ u₂) := fun a ha ↦ by
    have h0 := ha 0 (by decide)
    rw [add_ofNat_zero] at h0
    exact post₂.mem a fun he ↦ h0 (Or.inl (by rw [he]; simp only [Within]; omega))
  have H₂ : Head OI s u₂ A k := H₁.heap hpre post₂.heap fr₂ (by omega)
    fun r hr ↦ hp₂.reg r (headRegs_sub r hr)
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80001348_spec
    (by rw [hpc₂, returnAddress_eq, b80001338_x1 h₁]; decide) (by rv_eval [])
  have hQ0 : u₂.getReg .x10 ≠ 0 := fun he ↦ by
    have := congrArg BitVec.toNat he; rw [← hQ] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega
  have pc₃ := b80001348_pc_taken h₃ hQ0
  have m₃ := b80001348_mem_same h₃
  have H₃ : Head OI s u₃ A k := H₂.same hpre m₃ fun r hr ↦ b80001348_keeps h₃ r (mem_of_mem hr _)
  have x10₃ : u₃.getReg .x10 = Q := b80001348_keeps h₃ .x10 (by decide)
  have x18₃ : u₃.getReg .x18 = u.getReg .x18 := by
    rw [b80001348_keeps h₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)]
  have hn₃ : heapNext u₃ = Q.toNat + 48 := by simp only [heapNext, m₃]; exact hnx
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := H₃.inv.sp
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80001350_spec pc₃ (by
    rv_eval [sp₃]
    and_intros <;> valid_access hval [hb1])
  have e1728 : u₃.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1736 : u₃.getReg .x2 + 1736 = s.getReg .x2 - 920 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1744 : u₃.getReg .x2 + 1744 = s.getReg .x2 - 912 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr₄ : MemFrame u₃ u₄ (s.getReg .x2 - 928) 24 := by
    rw [← e1728]; exact b80001350_frame h₄ (by rw [sp₃]; addr_omega [hb1])
  have k₄ := b80001350_keeps h₄
  have H₄ : Head OI s u₄ A k := H₃.r5 (Q := Q) hpre
    ⟨by omega, by rw [x18₃]; omega, by omega⟩
    ((DFrame.of_memFrame fr₄).mono fun a ha ↦ Or.inr (Or.inr (Or.inr (by
      simp only [Within] at ha ⊢; addr_omega [ha, hb1]))))
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  have v0 : u₄.getMem (s.getReg .x2 - 928) = 6 := by rw [← e1728]; exact b80001350_m_x2_1728 h₄
  have v1 : u₄.getMem (s.getReg .x2 - 920) = Q := by
    rw [← e1736, b80001350_m_x2_1736 h₄, x10₃]
  have v2 : u₄.getMem (s.getReg .x2 - 912) = 0 := by rw [← e1744]; exact b80001350_m_x2_1744 h₄
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - 928 := by rw [b80001350_x10 h₄, e1728]
  have pre₄ : ValidMemRange (u₄.getReg .x10) 3 ∧ (vecLen u₄ (u₄.getReg .x10)).toNat +
      (u₄.getReg .x11).toNat ≤ (vecCap u₄ (u₄.getReg .x10)).toNat := by
    have e16 : s.getReg .x2 - 928 + 16 = s.getReg .x2 - 912 := by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    refine ⟨by rw [x10₄]; valid_sub hval [hb1], ?_⟩
    simp only [vecLen, vecCap, x10₄, e16, v0, v2, b80001350_x11 h₄]
    decide
  obtain ⟨u₅, hr₅, ⟨hpc₅, hp₅, post₅⟩ | hd⟩ := hRF.call (Reaches.refl u₄) (b80001350_pc h₄) pre₄
  swap
  · exact ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr hd⟩
  have m₅ := post₅.2
  have H₅ : Head OI s u₅ A k := H₄.same hpre m₅ fun r hr ↦ hp₅.reg r (headRegs_sub r hr)
  have hn₄ : heapNext u₄ = Q.toNat + 48 := by
    simp only [heapNext]
    rw [fr₄ nextAddr (by simp only [Within]; addr_omega [hb1])]
    exact hn₃
  have hn₅ : heapNext u₅ = Q.toNat + 48 := by simp only [heapNext, m₅]; exact hn₄
  refine ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl ⟨by
    rw [hpc₅, returnAddress_eq, b80001350_x1 h₄]; decide, Q, {
      toHead := H₅
      q := ⟨by omega, hal, by rw [hp₅.reg .x18, k₄ .x18 (by decide), x18₃]; omega, by omega⟩
      vec := ⟨by rw [m₅]; exact v0, by rw [m₅]; exact v1, by rw [m₅]; exact v2⟩ }⟩⟩

/-! ## The six heights -/

/-- `rows[i]`'s height as the code computes it: `64 - count_ones(!smear(rows[i].saturating_sub(1)))`. -/
def hgt (A : List E) (i : Nat) : Word := 64 - popW (ssub ((rowsOf A).getD i 0))

/-- Past `0x80001370`: the buffer's address also at `sp + 192`, the length `0` in `s1`, the first
`j` heights stored. -/
structure Ht (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (Q : Word) (j : Nat) : Prop extends HtA OI s u A k Q where
  slot : u.getMem (s.getReg .x2 - 2464) = Q
  x9 : u.getReg .x9 = 0
  done : ∀ i < j, u.getMem (Q + BitVec.ofNat 64 (8 * i)) = hgt A i

theorem Head.row {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} (h : Head OI s u A k) {i : Nat} (hi : i < 6) :
    u.getMem (u.getReg .x18 + BitVec.ofNat 64 (8 * i)) = (rowsOf A).getD i 0 := by
  rw [← h.rows]
  interval_cases i <;> simp

/-- A step that writes nothing. -/
theorem Ht.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {Q : Word} {j : Nat} (hpre : WalkPre s) (h : Ht OI s u A k Q j)
    (hm : ∀ a, v.getMem a = u.getMem a) (hr : ∀ r ∈ headRegs, v.getReg r = u.getReg r)
    (x9 : v.getReg .x9 = u.getReg .x9) : Ht OI s v A k Q j := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  have q := h.q
  exact {
    toHead := h.toHead.same hpre hm hr
    q := by rw [hr .x18 (by decide), hn]; exact q
    vec := by simp only [hm]; exact h.vec
    slot := by rw [hm]; exact h.slot
    x9 := by rw [x9]; exact h.x9
    done := fun i hi ↦ by rw [hm]; exact h.done i hi }

/-- The `j`th height stored. -/
theorem Ht.store {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {Q : Word} {j : Nat} (hpre : WalkPre s) (h : Ht OI s u A k Q j)
    (hj : j < 6) (fr : MemFrame u v (Q + BitVec.ofNat 64 (8 * j)) 8)
    (hv : v.getMem (Q + BitVec.ofNat 64 (8 * j)) = hgt A j)
    (hr : ∀ r ∈ headRegs, v.getReg r = u.getReg r) (x9 : v.getReg .x9 = u.getReg .x9) :
    Ht OI s v A k Q (j + 1) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have keep (x : Word) (hx : x.toNat + 8 ≤ (Q + BitVec.ofNat 64 (8 * j)).toNat ∨
      (Q + BitVec.ofNat 64 (8 * j)).toNat + 8 ≤ x.toNat) : v.getMem x = u.getMem x :=
    fr x fun hw ↦ by simp only [Within] at hw; omega
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    rw [keep _ (by addr_omega [hj, q4, hh])]
  have stk (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat) : v.getMem x = u.getMem x :=
    keep x (by addr_omega [h1, hj, q4, hh, hb1])
  exact {
    toHead := h.toHead.r5 hpre ⟨q1, q3, q4⟩ ((DFrame.of_memFrame fr).mono fun a ha ↦ Or.inl (by
      simp only [Within] at ha ⊢; addr_omega [ha, hj, q4, hh])) hr
    q := by rw [hr .x18 (by decide), hn]; exact h.q
    vec := by
      rw [stk _ (by addr_omega [hb1]), stk _ (by addr_omega [hb1]), stk _ (by addr_omega [hb1])]
      exact h.vec
    slot := by rw [stk _ (by addr_omega [hb1])]; exact h.slot
    x9 := by rw [x9]; exact h.x9
    done := fun i hi ↦ by
      by_cases hij : i = j
      · subst hij; exact hv
      · rw [keep _ (by addr_omega [hi, hij, hj, q4, hh])]
        exact h.done i (by omega) }

/-! ### The blocks' values -/

theorem b80001438_x11' {s t : MachineState} (h : b80001438.Holds s t) :
    t.getReg .x11 = ssub (s.getMem (s.getReg .x18 + 8)) := h.reg_eq .x11 rfl rfl
theorem b80001438_pc' {s t : MachineState} (h : b80001438.Holds s t) :
    t.pc = if (ssub (s.getMem (s.getReg .x18 + 8)) == 0) = true then 0x80001500 else 0x8000145c :=
  h.pc_eq rfl
theorem b80001438_frame' {s t : MachineState} (h : b80001438.Holds s t) :
    MemFrame s t (s.getMem (s.getReg .x2 + 192) + s.getReg .x9 * 8) 8 :=
  h.memFrame (by rv_eval []; simp only [Within]; omega)

theorem b80001500_x12' {s t : MachineState} (h : b80001500.Holds s t) :
    t.getReg .x12 = ssub (s.getMem (s.getReg .x18 + 16)) := h.reg_eq .x12 rfl rfl
theorem b80001500_pc' {s t : MachineState} (h : b80001500.Holds s t) :
    t.pc = if (ssub (s.getMem (s.getReg .x18 + 16)) == 0) = true then 0x800015c4 else 0x80001520 :=
  h.pc_eq rfl

theorem b800015c4_x12' {s t : MachineState} (h : b800015c4.Holds s t) :
    t.getReg .x12 = ssub (s.getMem (s.getReg .x18 + 24)) := h.reg_eq .x12 rfl rfl
theorem b800015c4_pc' {s t : MachineState} (h : b800015c4.Holds s t) :
    t.pc = if (ssub (s.getMem (s.getReg .x18 + 24)) == 0) = true then 0x80001680 else 0x800015dc :=
  h.pc_eq rfl

theorem b80001680_x11' {s t : MachineState} (h : b80001680.Holds s t) :
    t.getReg .x11 = ssub (s.getMem (s.getReg .x18 + 32)) := h.reg_eq .x11 rfl rfl
theorem b80001680_pc' {s t : MachineState} (h : b80001680.Holds s t) :
    t.pc = if (ssub (s.getMem (s.getReg .x18 + 32)) == 0) = true then 0x80001744 else 0x800016a0 :=
  h.pc_eq rfl

theorem b80001744_x11' {s t : MachineState} (h : b80001744.Holds s t) :
    t.getReg .x11 = ssub (s.getMem (s.getReg .x18 + 40)) := h.reg_eq .x11 rfl rfl
theorem b80001744_pc' {s t : MachineState} (h : b80001744.Holds s t) :
    t.pc = if (ssub (s.getMem (s.getReg .x18 + 40)) == 0) = true then 0x80001800 else 0x8000175c :=
  h.pc_eq rfl

theorem rowsBuf {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} (h : Head OI s u A k) : Mapped (u.getReg .x18) 48 := by
  have hb := h.buf
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  exact Or.inl ⟨by omega, by omega⟩

set_option maxRecDepth 8192 in
/-- `rows[0]`: `ssub` in `a0`, the popcount (or `64`) in `a1`. -/
theorem row0 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80001370)
    (h : HtA OI s u A k Q) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001438 ∧ Ht OI s t A k Q 0 ∧
      t.getReg .x11 = popW (ssub ((rowsOf A).getD 0 0)) ∧ t.getReg .x12 = 64 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.inv.sp
  have hm := rowsBuf h.toHead
  have hb := h.buf
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001370_spec hpc (by
    rv_eval [sp]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | exact Mapped.valid8 hm (by omega) (by omega) hb.1)
  have e192 : u.getReg .x2 + 192 = s.getReg .x2 - 2464 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1744 : u.getReg .x2 + 1744 = s.getReg .x2 - 912 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1736 : u.getReg .x2 + 1736 = s.getReg .x2 - 920 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr₁ : MemFrame u u₁ (s.getReg .x2 - 2464) 8 := by
    rw [← e192]; exact b80001370_frame h₁ (by rw [sp]; addr_omega [hb1])
  have k₁ := b80001370_keeps h₁
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have H₁ : Head OI s u₁ A k := h.toHead.r5 hpre ⟨q1, q3, q4⟩
    ((DFrame.of_memFrame fr₁).mono fun a ha ↦ Or.inr (Or.inr (Or.inl (by
      simp only [Within] at ha ⊢; addr_omega [ha, hb1]))))
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]; rw [fr₁ _ (by simp only [Within]; addr_omega [hb1])]
  have stk (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 2464).toNat ∨ (s.getReg .x2 - 2456).toNat ≤ x.toNat) :
      u₁.getMem x = u.getMem x := fr₁ x fun hw ↦ by simp only [Within] at hw; addr_omega [hw, h2, hb1]
  have Ht₁ : Ht OI s u₁ A k Q 0 := {
    toHead := H₁
    q := by rw [k₁ .x18 (by decide), hn₁]; exact h.q
    vec := by
      rw [stk _ (by addr_omega [hb1]) (by addr_omega [hb1]), stk _ (by addr_omega [hb1])
        (by addr_omega [hb1]), stk _ (by addr_omega [hb1]) (by addr_omega [hb1])]
      exact h.vec
    slot := by rw [← e192, b80001370_m_x2_192 h₁, e1736]; exact h.vec.2.1
    x9 := by rw [b80001370_x9 h₁, e1744]; exact h.vec.2.2
    done := fun i hi ↦ absurd hi (Nat.not_lt_zero _) }
  have r0 : u.getMem (u.getReg .x18) = (rowsOf A).getD 0 0 := by
    simpa using h.toHead.row (i := 0) (by decide)
  have pc₁ := b80001370_pc' h₁
  rw [r0] at pc₁
  have x10₁ : u₁.getReg .x10 = ssub ((rowsOf A).getD 0 0) := by rw [b80001370_x10' h₁, r0]
  by_cases hz : ssub ((rowsOf A).getD 0 0) = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte] at pc₁
    exact ⟨u₁, hr₁, pc₁, Ht₁, by rw [b80001370_x11 h₁, hz, popW_zero], b80001370_x12 h₁⟩
  · simp only [beq_iff_eq, hz, ↓reduceIte] at pc₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001394_spec pc₁ (by rv_eval [])
    have k₂ := b80001394_keeps h₂
    exact ⟨u₂, hr₁.trans hr₂, b80001394_pc h₂,
      Ht₁.same hpre (b80001394_mem_same h₂) (fun r hr ↦ k₂ r (mem_of_mem hr _)) (k₂ .x9 (by decide)),
      by rw [b80001394_x11' h₂, x10₁], by rw [k₂ .x12 (by decide), b80001370_x12 h₁]⟩

set_option maxRecDepth 8192 in
/-- `rows[0]`'s height stored at `Q`; `rows[1]`'s popcount in `a2`. -/
theorem row1 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80001438)
    (h : Ht OI s u A k Q 0) (x11 : u.getReg .x11 = popW (ssub ((rowsOf A).getD 0 0)))
    (x12 : u.getReg .x12 = 64) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001500 ∧ Ht OI s t A k Q 1 ∧ t.getReg .x10 = Q ∧
      t.getReg .x12 = popW (ssub ((rowsOf A).getD 1 0)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.inv.sp
  have hm := rowsBuf h.toHead
  have hb := h.buf
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have hmQ : Mapped Q 48 := Or.inl ⟨by omega, by omega⟩
  have slot := h.slot
  have x9 := h.x9
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001438_spec hpc (by
    rv_eval [sp, slot, x9]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | exact Mapped.valid8 hm (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      | exact Mapped.valid8 hmQ (by addr_omega [q2, q4, hh]) (by addr_omega [q2, q4, hh])
          (by addr_omega [q2, q4, hh])
      | addr_omega [hb, q3, q4, hh])
  have ea : u.getMem (u.getReg .x2 + 192) + u.getReg .x9 * 8 = Q + BitVec.ofNat 64 (8 * 0) := by
    have e192 : u.getReg .x2 + 192 = s.getReg .x2 - 2464 := by
      rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rw [e192, slot, x9]; simp
  have fr₁ : MemFrame u u₁ (Q + BitVec.ofNat 64 (8 * 0)) 8 := by rw [← ea]; exact b80001438_frame' h₁
  have k₁ := b80001438_keeps h₁
  have Ht₁ : Ht OI s u₁ A k Q 1 := h.store hpre (by decide) fr₁
    (by rw [← ea, b80001438_m0 h₁, x11, x12]; rfl)
    (fun r hr ↦ k₁ r (mem_of_mem hr _)) (k₁ .x9 (by decide))
  have x10₁ : u₁.getReg .x10 = Q := by rw [b80001438_x10 h₁, ea]; simp
  have r1 : u.getMem (u.getReg .x18 + 8) = (rowsOf A).getD 1 0 := by
    simpa using h.toHead.row (i := 1) (by decide)
  have pc₁ := b80001438_pc' h₁
  rw [r1] at pc₁
  have x11₁ : u₁.getReg .x11 = ssub ((rowsOf A).getD 1 0) := by rw [b80001438_x11' h₁, r1]
  by_cases hz : ssub ((rowsOf A).getD 1 0) = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte] at pc₁
    exact ⟨u₁, hr₁, pc₁, Ht₁, x10₁, by rw [k₁ .x12 (by decide), x12, hz, popW_zero]⟩
  · simp only [beq_iff_eq, hz, ↓reduceIte] at pc₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000145c_spec pc₁ (by rv_eval [])
    have k₂ := b8000145c_keeps h₂
    exact ⟨u₂, hr₁.trans hr₂, b8000145c_pc h₂,
      Ht₁.same hpre (b8000145c_mem_same h₂) (fun r hr ↦ k₂ r (mem_of_mem hr _)) (k₂ .x9 (by decide)),
      by rw [k₂ .x10 (by decide), x10₁], by rw [b8000145c_x12' h₂, x11₁]⟩

set_option maxRecDepth 8192 in
/-- `rows[1]`'s height stored at `Q + 8`; `rows[2]`'s popcount in `a3`. -/
theorem row2 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80001500)
    (h : Ht OI s u A k Q 1) (x10 : u.getReg .x10 = Q)
    (x12 : u.getReg .x12 = popW (ssub ((rowsOf A).getD 1 0))) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x800015c4 ∧ Ht OI s t A k Q 2 ∧ t.getReg .x10 = Q ∧
      t.getReg .x11 = 64 ∧ t.getReg .x13 = popW (ssub ((rowsOf A).getD 2 0)) := by
  have hm := rowsBuf h.toHead
  have hb := h.buf
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have hmQ : Mapped Q 48 := Or.inl ⟨by omega, by omega⟩
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001500_spec hpc (by
    rv_eval [x10]
    and_intros
    all_goals first
      | exact Mapped.valid8 hm (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      | exact Mapped.valid8 hmQ (by addr_omega [q2, q4, hh]) (by addr_omega [q2, q4, hh])
          (by addr_omega [q2, q4, hh])
      | addr_omega [hb, q3, q4, hh])
  have ea : u.getReg .x10 + 8 = Q + BitVec.ofNat 64 (8 * 1) := by rw [x10]; rfl
  have fr₁ : MemFrame u u₁ (Q + BitVec.ofNat 64 (8 * 1)) 8 := by
    rw [← ea]; exact b80001500_frame h₁ (by rw [x10]; omega)
  have k₁ := b80001500_keeps h₁
  have Ht₁ : Ht OI s u₁ A k Q 2 := h.store hpre (by decide) fr₁
    (by rw [← ea, b80001500_m_x10_8 h₁, x12]; rfl)
    (fun r hr ↦ k₁ r (mem_of_mem hr _)) (k₁ .x9 (by decide))
  have x10₁ : u₁.getReg .x10 = Q := by rw [k₁ .x10 (by decide), x10]
  have r2 : u.getMem (u.getReg .x18 + 16) = (rowsOf A).getD 2 0 := by
    simpa using h.toHead.row (i := 2) (by decide)
  have pc₁ := b80001500_pc' h₁
  rw [r2] at pc₁
  have x12₁ : u₁.getReg .x12 = ssub ((rowsOf A).getD 2 0) := by rw [b80001500_x12' h₁, r2]
  by_cases hz : ssub ((rowsOf A).getD 2 0) = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte] at pc₁
    exact ⟨u₁, hr₁, pc₁, Ht₁, x10₁, b80001500_x11 h₁, by rw [b80001500_x13 h₁, hz, popW_zero]⟩
  · simp only [beq_iff_eq, hz, ↓reduceIte] at pc₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001520_spec pc₁ (by rv_eval [])
    have k₂ := b80001520_keeps h₂
    exact ⟨u₂, hr₁.trans hr₂, b80001520_pc h₂,
      Ht₁.same hpre (b80001520_mem_same h₂) (fun r hr ↦ k₂ r (mem_of_mem hr _)) (k₂ .x9 (by decide)),
      by rw [k₂ .x10 (by decide), x10₁], by rw [k₂ .x11 (by decide), b80001500_x11 h₁],
      by rw [b80001520_x13' h₂, x12₁]⟩

set_option maxRecDepth 8192 in
/-- `rows[2]`'s height stored at `Q + 16`; `rows[3]`'s popcount in `a1`. -/
theorem row3 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x800015c4)
    (h : Ht OI s u A k Q 2) (x10 : u.getReg .x10 = Q) (x11 : u.getReg .x11 = 64)
    (x13 : u.getReg .x13 = popW (ssub ((rowsOf A).getD 2 0))) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001680 ∧ Ht OI s t A k Q 3 ∧ t.getReg .x10 = Q ∧
      t.getReg .x11 = popW (ssub ((rowsOf A).getD 3 0)) := by
  have hm := rowsBuf h.toHead
  have hb := h.buf
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have hmQ : Mapped Q 48 := Or.inl ⟨by omega, by omega⟩
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800015c4_spec hpc (by
    rv_eval [x10]
    and_intros
    all_goals first
      | exact Mapped.valid8 hm (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      | exact Mapped.valid8 hmQ (by addr_omega [q2, q4, hh]) (by addr_omega [q2, q4, hh])
          (by addr_omega [q2, q4, hh])
      | addr_omega [hb, q3, q4, hh])
  have ea : u.getReg .x10 + 16 = Q + BitVec.ofNat 64 (8 * 2) := by rw [x10]; rfl
  have fr₁ : MemFrame u u₁ (Q + BitVec.ofNat 64 (8 * 2)) 8 := by
    rw [← ea]; exact b800015c4_frame h₁ (by rw [x10]; omega)
  have k₁ := b800015c4_keeps h₁
  have Ht₁ : Ht OI s u₁ A k Q 3 := h.store hpre (by decide) fr₁
    (by rw [← ea, b800015c4_m_x10_16 h₁, x11, x13]; rfl)
    (fun r hr ↦ k₁ r (mem_of_mem hr _)) (k₁ .x9 (by decide))
  have x10₁ : u₁.getReg .x10 = Q := by rw [k₁ .x10 (by decide), x10]
  have r3 : u.getMem (u.getReg .x18 + 24) = (rowsOf A).getD 3 0 := by
    simpa using h.toHead.row (i := 3) (by decide)
  have pc₁ := b800015c4_pc' h₁
  rw [r3] at pc₁
  have x12₁ : u₁.getReg .x12 = ssub ((rowsOf A).getD 3 0) := by rw [b800015c4_x12' h₁, r3]
  by_cases hz : ssub ((rowsOf A).getD 3 0) = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte] at pc₁
    exact ⟨u₁, hr₁, pc₁, Ht₁, x10₁, by rw [k₁ .x11 (by decide), x11, hz, popW_zero]⟩
  · simp only [beq_iff_eq, hz, ↓reduceIte] at pc₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800015dc_spec pc₁ (by rv_eval [])
    have k₂ := b800015dc_keeps h₂
    exact ⟨u₂, hr₁.trans hr₂, b800015dc_pc h₂,
      Ht₁.same hpre (b800015dc_mem_same h₂) (fun r hr ↦ k₂ r (mem_of_mem hr _)) (k₂ .x9 (by decide)),
      by rw [k₂ .x10 (by decide), x10₁], by rw [b800015dc_x11' h₂, x12₁]⟩

set_option maxRecDepth 8192 in
/-- `rows[3]`'s height stored at `Q + 24`; `rows[4]`'s popcount in `a3`. -/
theorem row4 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80001680)
    (h : Ht OI s u A k Q 3) (x10 : u.getReg .x10 = Q)
    (x11 : u.getReg .x11 = popW (ssub ((rowsOf A).getD 3 0))) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001744 ∧ Ht OI s t A k Q 4 ∧ t.getReg .x10 = Q ∧
      t.getReg .x12 = 64 ∧ t.getReg .x13 = popW (ssub ((rowsOf A).getD 4 0)) := by
  have hm := rowsBuf h.toHead
  have hb := h.buf
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have hmQ : Mapped Q 48 := Or.inl ⟨by omega, by omega⟩
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001680_spec hpc (by
    rv_eval [x10]
    and_intros
    all_goals first
      | exact Mapped.valid8 hm (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      | exact Mapped.valid8 hmQ (by addr_omega [q2, q4, hh]) (by addr_omega [q2, q4, hh])
          (by addr_omega [q2, q4, hh])
      | addr_omega [hb, q3, q4, hh])
  have ea : u.getReg .x10 + 24 = Q + BitVec.ofNat 64 (8 * 3) := by rw [x10]; rfl
  have fr₁ : MemFrame u u₁ (Q + BitVec.ofNat 64 (8 * 3)) 8 := by
    rw [← ea]; exact b80001680_frame h₁ (by rw [x10]; omega)
  have k₁ := b80001680_keeps h₁
  have Ht₁ : Ht OI s u₁ A k Q 4 := h.store hpre (by decide) fr₁
    (by rw [← ea, b80001680_m_x10_24 h₁, x11]; rfl)
    (fun r hr ↦ k₁ r (mem_of_mem hr _)) (k₁ .x9 (by decide))
  have x10₁ : u₁.getReg .x10 = Q := by rw [k₁ .x10 (by decide), x10]
  have r4 : u.getMem (u.getReg .x18 + 32) = (rowsOf A).getD 4 0 := by
    simpa using h.toHead.row (i := 4) (by decide)
  have pc₁ := b80001680_pc' h₁
  rw [r4] at pc₁
  have x11₁ : u₁.getReg .x11 = ssub ((rowsOf A).getD 4 0) := by rw [b80001680_x11' h₁, r4]
  by_cases hz : ssub ((rowsOf A).getD 4 0) = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte] at pc₁
    exact ⟨u₁, hr₁, pc₁, Ht₁, x10₁, b80001680_x12 h₁, by rw [b80001680_x13 h₁, hz, popW_zero]⟩
  · simp only [beq_iff_eq, hz, ↓reduceIte] at pc₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800016a0_spec pc₁ (by rv_eval [])
    have k₂ := b800016a0_keeps h₂
    exact ⟨u₂, hr₁.trans hr₂, b800016a0_pc h₂,
      Ht₁.same hpre (b800016a0_mem_same h₂) (fun r hr ↦ k₂ r (mem_of_mem hr _)) (k₂ .x9 (by decide)),
      by rw [k₂ .x10 (by decide), x10₁], by rw [k₂ .x12 (by decide), b80001680_x12 h₁],
      by rw [b800016a0_x13' h₂, x11₁]⟩

set_option maxRecDepth 8192 in
/-- `rows[4]`'s height stored at `Q + 32`; `rows[5]`'s popcount in `a2`. -/
theorem row5 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80001744)
    (h : Ht OI s u A k Q 4) (x10 : u.getReg .x10 = Q) (x12 : u.getReg .x12 = 64)
    (x13 : u.getReg .x13 = popW (ssub ((rowsOf A).getD 4 0))) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001800 ∧ Ht OI s t A k Q 5 ∧ t.getReg .x10 = Q ∧
      t.getReg .x12 = popW (ssub ((rowsOf A).getD 5 0)) := by
  have hm := rowsBuf h.toHead
  have hb := h.buf
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have hmQ : Mapped Q 48 := Or.inl ⟨by omega, by omega⟩
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001744_spec hpc (by
    rv_eval [x10]
    and_intros
    all_goals first
      | exact Mapped.valid8 hm (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      | exact Mapped.valid8 hmQ (by addr_omega [q2, q4, hh]) (by addr_omega [q2, q4, hh])
          (by addr_omega [q2, q4, hh])
      | addr_omega [hb, q3, q4, hh])
  have ea : u.getReg .x10 + 32 = Q + BitVec.ofNat 64 (8 * 4) := by rw [x10]; rfl
  have fr₁ : MemFrame u u₁ (Q + BitVec.ofNat 64 (8 * 4)) 8 := by
    rw [← ea]; exact b80001744_frame h₁ (by rw [x10]; omega)
  have k₁ := b80001744_keeps h₁
  have Ht₁ : Ht OI s u₁ A k Q 5 := h.store hpre (by decide) fr₁
    (by rw [← ea, b80001744_m_x10_32 h₁, x12, x13]; rfl)
    (fun r hr ↦ k₁ r (mem_of_mem hr _)) (k₁ .x9 (by decide))
  have x10₁ : u₁.getReg .x10 = Q := by rw [k₁ .x10 (by decide), x10]
  have r5 : u.getMem (u.getReg .x18 + 40) = (rowsOf A).getD 5 0 := by
    simpa using h.toHead.row (i := 5) (by decide)
  have pc₁ := b80001744_pc' h₁
  rw [r5] at pc₁
  have x11₁ : u₁.getReg .x11 = ssub ((rowsOf A).getD 5 0) := by rw [b80001744_x11' h₁, r5]
  by_cases hz : ssub ((rowsOf A).getD 5 0) = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte] at pc₁
    exact ⟨u₁, hr₁, pc₁, Ht₁, x10₁, by rw [k₁ .x12 (by decide), x12, hz, popW_zero]⟩
  · simp only [beq_iff_eq, hz, ↓reduceIte] at pc₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000175c_spec pc₁ (by rv_eval [])
    have k₂ := b8000175c_keeps h₂
    exact ⟨u₂, hr₁.trans hr₂, b8000175c_pc h₂,
      Ht₁.same hpre (b8000175c_mem_same h₂) (fun r hr ↦ k₂ r (mem_of_mem hr _)) (k₂ .x9 (by decide)),
      by rw [k₂ .x10 (by decide), x10₁], by rw [b8000175c_x12' h₂, x11₁]⟩

/-! ## The KECCAK floor and the spills -/

theorem spAdd {s u : MachineState} (hpre : WalkPre s) (sp : u.getReg .x2 = s.getReg .x2 - 2656)
    {N M : Word} (h : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, h]

/-- A store to the frame at `sp + 72 .. sp + 160`. -/
theorem Ht.stk {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {Q : Word} {j : Nat} (hpre : WalkPre s) (h : Ht OI s u A k Q j)
    (hj : j ≤ 6) {lo : Word} (hlo : (s.getReg .x2 - 2584).toNat ≤ lo.toNat ∧
      lo.toNat + 8 ≤ (s.getReg .x2 - 2496).toNat) (fr : MemFrame u v lo 8)
    (hr : ∀ r ∈ headRegs, v.getReg r = u.getReg r) (x9 : v.getReg .x9 = u.getReg .x9) :
    Ht OI s v A k Q j := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have keep (x : Word) (hx : x.toNat + 8 ≤ lo.toNat ∨ lo.toNat + 8 ≤ x.toNat) :
      v.getMem x = u.getMem x := fr x fun hw ↦ by simp only [Within] at hw; omega
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [keep _ (by addr_omega [hlo, hb1])]
  exact {
    toHead := h.toHead.r5 hpre ⟨q1, q3, q4⟩ ((DFrame.of_memFrame fr).mono fun a ha ↦
      Or.inr (Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hlo, hb1]))) hr
    q := by rw [hr .x18 (by decide), hn]; exact h.q
    vec := by
      rw [keep _ (by addr_omega [hlo, hb1]), keep _ (by addr_omega [hlo, hb1]),
        keep _ (by addr_omega [hlo, hb1])]
      exact h.vec
    slot := by rw [keep _ (by addr_omega [hlo, hb1])]; exact h.slot
    x9 := by rw [x9]; exact h.x9
    done := fun i hi ↦ by
      rw [keep _ (by addr_omega [hlo, hb1, q4, hh, hi, hj])]; exact h.done i hi }

theorem heights_getD {rows : List Word} (hl : rows.length = 6) {i : Nat} (hi : i < 6) :
    (LayoutMirror.tableLogHeightsRust rows).getD i 0 =
      max (log2CeilRust (rows.getD i 0)) (if i = 5 then 9 else 0) := by
  match rows, hl with
  | [a, b, c, d, e, f], _ => interval_cases i <;> rfl

theorem hgt_eq (A : List E) (i : Nat) : hgt A i = BitVec.ofNat 64 (log2CeilRust ((rowsOf A).getD i 0)) :=
  height_eq _

theorem max9 {L : Nat} (hL : L ≤ 64) :
    (if (9 : Word).toNat < (BitVec.ofNat 64 L).toNat then BitVec.ofNat 64 L else 9) =
      BitVec.ofNat 64 (max L 9) := by
  have e9 : (9 : Word).toNat = 9 := rfl
  rw [e9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases h : 9 < L
  · simp only [h, ↓reduceIte, Nat.max_eq_left (by omega : 9 ≤ L)]
  · simp only [h, ↓reduceIte, Nat.max_eq_right (by omega : L ≤ 9)]; rfl

/-- At `0x80004a90`, `Flushes::state_step`'s entry (`a0 = sp + 1168`, an empty `Flushes`
{push: {0, 8, 0}, pull: {0, 8, 0}}; return to `0x8000186c`): `table_log_heights` is the `Vec` of
capacity 6 (at `sp + 120` and `sp + 1728`), buffer `Q` (at `sp + 192` and `sp + 1736`) and
length 0 in `s1` (the length `extend` will start from), its buffer holding
`tableLogHeightsRust (rowsOf A)`; `s0`, `s2..s9` spilled (`s3..s6`, `s7`, `s8` as the entry's
values `Regs` names). -/
structure AtR5 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (Q : Word) : Prop extends Head OI s u A k where
  q : heapNext s ≤ Q.toNat ∧ Q.toNat % 8 = 0 ∧ (u.getReg .x18).toNat + 48 ≤ Q.toNat ∧
    Q.toNat + 48 ≤ heapNext u
  heights : ∀ i < 6, u.getMem (Q + BitVec.ofNat 64 (8 * i)) =
    BitVec.ofNat 64 ((LayoutMirror.tableLogHeightsRust (rowsOf A)).getD i 0)
  x1 : u.getReg .x1 = 0x8000186c
  x9 : u.getReg .x9 = 0
  x10 : u.getReg .x10 = s.getReg .x2 - 1488
  x11 : u.getReg .x11 = 8
  vec : u.getMem (s.getReg .x2 - 928) = 6 ∧ u.getMem (s.getReg .x2 - 920) = Q ∧
    u.getMem (s.getReg .x2 - 912) = 0
  cap : u.getMem (s.getReg .x2 - 2536) = 6
  ptr : u.getMem (s.getReg .x2 - 2464) = Q
  spills : u.getMem (s.getReg .x2 - 2584) = rateOf A ∧
    u.getMem (s.getReg .x2 - 2576) = s.getMem (s.getReg .x12 + 16) ∧
    u.getMem (s.getReg .x2 - 2568) = s.getMem (s.getReg .x12) ∧
    u.getMem (s.getReg .x2 - 2560) = s.getMem (s.getReg .x12 + 24) ∧
    u.getMem (s.getReg .x2 - 2552) = s.getMem (s.getReg .x12 + 8) ∧
    u.getMem (s.getReg .x2 - 2528) = s.getReg .x11 ∧ u.getMem (s.getReg .x2 - 2512) = lmOf A ∧
    u.getMem (s.getReg .x2 - 2488) = s.getReg .x10 ∧ u.getMem (s.getReg .x2 - 2480) = u.getReg .x18
  flushes : u.getMem (s.getReg .x2 - 1488) = 0 ∧ u.getMem (s.getReg .x2 - 1480) = 8 ∧
    u.getMem (s.getReg .x2 - 1472) = 0 ∧ u.getMem (s.getReg .x2 - 1464) = 0 ∧
    u.getMem (s.getReg .x2 - 1456) = 8 ∧ u.getMem (s.getReg .x2 - 1448) = 0

set_option maxRecDepth 8192 in
/-- `max(log2_ceil(rows[5]), 9)` in `a1`, `log_memory` spilled to `sp + 144`. -/
theorem keccakFloor {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80001800)
    (h : Ht OI s u A k Q 5) (x10 : u.getReg .x10 = Q)
    (x12 : u.getReg .x12 = popW (ssub ((rowsOf A).getD 5 0))) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001818 ∧ Ht OI s t A k Q 5 ∧ t.getReg .x10 = Q ∧
      t.getReg .x11 = BitVec.ofNat 64 (max (log2CeilRust ((rowsOf A).getD 5 0)) 9) ∧
      t.getMem (s.getReg .x2 - 2512) = lmOf A := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001800_spec hpc (by
    rv_eval [sp]; valid_access hval [hb1])
  have e144 : u.getReg .x2 + 144 = s.getReg .x2 - 2512 := spAdd hpre sp (by decide)
  have fr₁ : MemFrame u u₁ (s.getReg .x2 - 2512) 8 := by
    rw [← e144]; exact b80001800_frame h₁ (by rw [sp]; addr_omega [hb1])
  have k₁ := b80001800_keeps h₁
  have H₁ : Ht OI s u₁ A k Q 5 := h.stk hpre (by decide) (by addr_omega [hb1]) fr₁
    (fun r hr ↦ k₁ r (mem_of_mem hr _)) (k₁ .x9 (by decide))
  have m144 : u₁.getMem (s.getReg .x2 - 2512) = lmOf A := by
    rw [← e144, b80001800_m_x2_144 h₁]; exact h.x25
  have x10₁ : u₁.getReg .x10 = Q := by rw [k₁ .x10 (by decide), x10]
  have hL : (64 : Word) - u.getReg .x12 = BitVec.ofNat 64 (log2CeilRust ((rowsOf A).getD 5 0)) := by
    rw [x12]; exact height_eq _
  have hL64 : log2CeilRust ((rowsOf A).getD 5 0) ≤ 64 := by unfold log2CeilRust; omega
  have hm := max9 hL64
  by_cases hc : (9 : Word).toNat < ((64 : Word) - u.getReg .x12).toNat
  · refine ⟨u₁, hr₁, b80001800_pc_taken h₁ hc, H₁, x10₁, ?_, m144⟩
    rw [b80001800_x11 h₁, ← hm, ← hL]; simp only [hc, ↓reduceIte]
  · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001814_spec
      (b80001800_pc_not_taken h₁ (Nat.le_of_not_lt hc)) (by rv_eval [])
    have k₂ := b80001814_keeps h₂
    have m₂ := b80001814_mem_same h₂
    refine ⟨u₂, hr₁.trans hr₂, b80001814_pc h₂,
      H₁.same hpre m₂ (fun r hr ↦ k₂ r (mem_of_mem hr _)) (k₂ .x9 (by decide)),
      by rw [k₂ .x10 (by decide), x10₁], ?_, by rw [m₂]; exact m144⟩
    rw [b80001814_x11 h₂, ← hm, ← hL]; simp only [hc, ↓reduceIte]

theorem Expect.dframe {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t) {w : Word → Prop}
    (hw : ∀ k ∈ x.writes, w (k.eval s)) : DFrame s t w := fun a ha ↦ h.frame a fun k hk he ↦ by
  have h0 := ha 0 (by decide)
  rw [add_ofNat_zero] at h0
  exact h0 (he ▸ hw k hk)

set_option maxRecDepth 8192 in
/-- The KECCAK height stored at `Q + 40`, the spills, the empty `Flushes` at `sp + 1168`, then the
call of `state_step`. -/
theorem heightsSpill {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {Q : Word} (hpre : WalkPre s) (hpc : u.pc = 0x80001818)
    (h : Ht OI s u A k Q 5) (x10 : u.getReg .x10 = Q)
    (x11 : u.getReg .x11 = BitVec.ofNat 64 (max (log2CeilRust ((rowsOf A).getD 5 0)) 9))
    (m144 : u.getMem (s.getReg .x2 - 2512) = lmOf A) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80004a90 ∧ AtR5 OI s t A k Q := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.inv.sp
  obtain ⟨q1, q2, q3, q4⟩ := h.q
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  have hmQ : Mapped Q 48 := Or.inl ⟨by omega, by omega⟩
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80001818_spec hpc (by
    rv_eval [sp, x10]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | exact Mapped.valid8 hmQ (by addr_omega [q2, q4, hh]) (by addr_omega [q2, q4, hh])
          (by addr_omega [q2, q4, hh])
      | addr_omega [hb1, q4, hh])
  have fr : DFrame u t (R5W s Q) := Expect.dframe ht (by
    rv_eval [sp, x10]
    simp only [R5W, Within]
    and_intros <;> addr_omega [hb1, q4, hh])
  have keep (x : Word) (hx : ∀ k ∈ b80001818.writes, x ≠ k.eval u) : t.getMem x = u.getMem x :=
    ht.frame x hx
  have kt := b80001818_keeps ht
  have H : Head OI s t A k := h.toHead.r5 hpre ⟨q1, q3, q4⟩ fr fun r hr ↦ kt r (mem_of_mem hr _)
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]
    rw [keep _ (by rv_eval [sp, x10]; and_intros <;> addr_omega [hb1, q4, hh])]
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have hrows : (rowsOf A).length = 6 := by rw [← h.rows]; rfl
  refine ⟨t, hr, b80001818_pc ht, {
    toHead := H
    q := by rw [kt .x18 (by decide), hn]; exact ⟨q1, q2, q3, q4⟩
    heights := fun i hi ↦ by
      rw [heights_getD hrows hi]
      by_cases h5 : i = 5
      · subst h5
        rw [show Q + BitVec.ofNat 64 (8 * 5) = u.getReg .x10 + 40 by rw [x10]; rfl,
          b80001818_m_x10_40 ht, x11]
        rfl
      · rw [keep _ (by rv_eval [sp, x10]; and_intros <;> addr_omega [hb1, q4, hh, hi, h5]),
          h.done i (by omega), hgt_eq]
        simp only [h5, ↓reduceIte, Nat.max_zero]
    x1 := b80001818_x1 ht
    x9 := by rw [kt .x9 (by decide)]; exact h.x9
    x10 := by rw [b80001818_x10 ht, e 1168 1488 (by decide)]
    x11 := b80001818_x11 ht
    vec := by
      rw [keep (s.getReg .x2 - 928) (by rv_eval [sp, x10]; and_intros <;> addr_omega [hb1, q4, hh]),
        keep (s.getReg .x2 - 920) (by rv_eval [sp, x10]; and_intros <;> addr_omega [hb1, q4, hh]),
        keep (s.getReg .x2 - 912) (by rv_eval [sp, x10]; and_intros <;> addr_omega [hb1, q4, hh])]
      exact h.vec
    cap := by rw [← e 120 2536 (by decide), b80001818_m_x2_120 ht, e 1728 928 (by decide)]; exact h.vec.1
    ptr := by
      rw [keep _ (by rv_eval [sp, x10]; and_intros <;> addr_omega [hb1, q4, hh])]; exact h.slot
    spills := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← e 72 2584 (by decide), b80001818_m_x2_72 ht]; exact h.x8
      · rw [← e 80 2576 (by decide), b80001818_m_x2_80 ht]; exact h.regs.x22
      · rw [← e 88 2568 (by decide), b80001818_m_x2_88 ht]; exact h.regs.x21
      · rw [← e 96 2560 (by decide), b80001818_m_x2_96 ht]; exact h.regs.x20
      · rw [← e 104 2552 (by decide), b80001818_m_x2_104 ht]; exact h.regs.x19
      · rw [← e 128 2528 (by decide), b80001818_m_x2_128 ht]; exact h.regs.x24
      · rw [keep _ (by rv_eval [sp, x10]; and_intros <;> addr_omega [hb1, q4, hh])]; exact m144
      · rw [← e 168 2488 (by decide), b80001818_m_x2_168 ht]; exact h.regs.x23
      · rw [← e 176 2480 (by decide), b80001818_m_x2_176 ht, kt .x18 (by decide)]
    flushes := ⟨by rw [← e 1168 1488 (by decide)]; exact b80001818_m_x2_1168 ht,
      by rw [← e 1176 1480 (by decide)]; exact b80001818_m_x2_1176 ht,
      by rw [← e 1184 1472 (by decide)]; exact b80001818_m_x2_1184 ht,
      by rw [← e 1192 1464 (by decide)]; exact b80001818_m_x2_1192 ht,
      by rw [← e 1200 1456 (by decide)]; exact b80001818_m_x2_1200 ht,
      by rw [← e 1208 1448 (by decide)]; exact b80001818_m_x2_1208 ht⟩ }⟩

/-- **`table_log_heights`**: from `0x80001338` (`Head`) to `state_step`'s call (`AtR5`), or a
trap. -/
theorem r5 (hAS : AllocSpec) (hRF : ReserveFastSpec 0x8000d628)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x80001338) (h : Head OI s u A k) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004a90 ∧ ∃ Q, AtR5 OI s t A k Q) ∨
      Dead Image.code t) := by
  obtain ⟨u₁, hr₁, ⟨pc₁, Q, h₁⟩ | hd⟩ := heightsAlloc hAS hRF hpre hpc h
  swap
  · exact ⟨u₁, hr₁, Or.inr hd⟩
  obtain ⟨u₂, hr₂, pc₂, h₂, a₂, b₂⟩ := row0 hpre pc₁ h₁
  obtain ⟨u₃, hr₃, pc₃, h₃, a₃, b₃⟩ := row1 hpre pc₂ h₂ a₂ b₂
  obtain ⟨u₄, hr₄, pc₄, h₄, a₄, b₄, c₄⟩ := row2 hpre pc₃ h₃ a₃ b₃
  obtain ⟨u₅, hr₅, pc₅, h₅, a₅, b₅⟩ := row3 hpre pc₄ h₄ a₄ b₄ c₄
  obtain ⟨u₆, hr₆, pc₆, h₆, a₆, b₆, c₆⟩ := row4 hpre pc₅ h₅ a₅ b₅
  obtain ⟨u₇, hr₇, pc₇, h₇, a₇, b₇⟩ := row5 hpre pc₆ h₆ a₆ b₆ c₆
  obtain ⟨u₈, hr₈, pc₈, h₈, a₈, b₈, c₈⟩ := keccakFloor hpre pc₇ h₇ a₇ b₇
  obtain ⟨t, hr, pc, ht⟩ := heightsSpill hpre pc₈ h₈ a₈ b₈ c₈
  exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₇.trans
    (hr₈.trans hr))))))), Or.inl ⟨pc, Q, ht⟩⟩

end Rv64Verifier.Proofs.Walk
