import Rv64Verifier.Proofs.Walk.Announced

/-!
# `walk`: the announced sizes' high limbs

From `0x8000116c` the loop at `0x80001184` walks the `Vec` of the eight announced scalars and
checks that `c1 | c2` is zero for each (`TM.require` of `afterScalars`). A nonzero limb is `Err`
(`0x800011a0`, the stores at `0x800012bc`); otherwise the code is at `0x800011b8` (`High`).

`err12bc` and `err12d0` are the two `Err` stores shared by `build_layout`'s head, and
`trapAt` the shared trap at `0x80004140`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Exits -/

theorem trap : Image.code.fetch 0x80004140 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem trapAt {u : MachineState} (hpc : u.pc = 0x80004140) : Dead Image.code u :=
  dead_of_fetch (by rw [hpc]; exact trap)

/-- The `Err` stores at `0x800012bc`, then the epilogue. -/
theorem err12bc {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    (hpre : WalkPre s) (h : Inv s u) (x23 : u.getReg .x23 = s.getReg .x10)
    (hpc : u.pc = 0x800012bc) : ∃ t, Reaches Image.code u t ∧ Done OI s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hR := hpre.out
  have hO := hpre.outStack
  rw [stackLo_eq, stack_eq] at hO
  obtain ⟨t, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800012bc_spec hpc (by
    rv_eval [x23]
    and_intros <;> exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR])
      (by addr_omega [hR]))
  have fr₀ := b800012bc_frame h₃ (by rw [x23]; addr_omega [hR])
  rw [x23] at fr₀
  have fr := DFrame.of_memFrame fr₀
  have hx := hpre.outFree.2
  have he : heapNext t = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi])
  have It : Inv s t := h.step hpre fr
    (fun a ha ↦ ⟨Or.inl (by addr_omega [ha, hR]), by addr_omega [ha, hO, hb1]⟩)
    ⟨he ▸ h.heap.lo, he ▸ h.heap.hi⟩ he.ge (b800012bc_keeps h₃ .x2 (by decide))
  obtain ⟨t', hr₄, hd⟩ := errExit (OI := OI) hpre It (b800012bc_pc h₃) (by
    rw [← x23, b800012bc_m_x23_0 h₃]; rfl)
  exact ⟨t', hr₃.trans hr₄, hd⟩

/-- The `Err` stores at `0x800012d0`, then the epilogue. -/
theorem err12d0 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    (hpre : WalkPre s) (h : Inv s u) (x23 : u.getReg .x23 = s.getReg .x10)
    (hpc : u.pc = 0x800012d0) : ∃ t, Reaches Image.code u t ∧ Done OI s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hR := hpre.out
  have hO := hpre.outStack
  rw [stackLo_eq, stack_eq] at hO
  obtain ⟨t, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800012d0_spec hpc (by
    rv_eval [x23]
    and_intros <;> exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR])
      (by addr_omega [hR]))
  have fr₀ := b800012d0_frame h₃ (by rw [x23]; addr_omega [hR])
  rw [x23] at fr₀
  have fr := DFrame.of_memFrame fr₀
  have hx := hpre.outFree.2
  have he : heapNext t = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi])
  have It : Inv s t := h.step hpre fr
    (fun a ha ↦ ⟨Or.inl (by addr_omega [ha, hR]), by addr_omega [ha, hO, hb1]⟩)
    ⟨he ▸ h.heap.lo, he ▸ h.heap.hi⟩ he.ge (b800012d0_keeps h₃ .x2 (by decide))
  obtain ⟨t', hr₄, hd⟩ := errExit (OI := OI) hpre It (b800012d0_pc h₃) (by
    rw [← x23, b800012d0_m_x23_0 h₃]; rfl)
  exact ⟨t', hr₃.trans hr₄, hd⟩

/-- `0x800012cc`: the code `2`, then the stores at `0x800012d0`. -/
theorem err12cc {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    (hpre : WalkPre s) (h : Inv s u) (x23 : u.getReg .x23 = s.getReg .x10)
    (hpc : u.pc = 0x800012cc) : ∃ t, Reaches Image.code u t ∧ Done OI s t := by
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b800012cc_spec hpc (by rv_eval [])
  obtain ⟨t', hr', hd⟩ := err12d0 (OI := OI) hpre (h.same (b800012cc_mem_same h₁)
    (b800012cc_keeps h₁ .x2 (by decide))) (by rw [b800012cc_keeps h₁ .x23 (by decide), x23])
    (b800012cc_pc h₁)
  exact ⟨t', hr.trans hr', hd⟩

/-- `0x800012b8`: the code `25`, then the stores at `0x800012bc`. -/
theorem err12b8 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    (hpre : WalkPre s) (h : Inv s u) (x23 : u.getReg .x23 = s.getReg .x10)
    (hpc : u.pc = 0x800012b8) : ∃ t, Reaches Image.code u t ∧ Done OI s t := by
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b800012b8_spec hpc (by rv_eval [])
  obtain ⟨t', hr', hd⟩ := err12bc (OI := OI) hpre (h.same (b800012b8_mem_same h₁)
    (b800012b8_keeps h₁ .x2 (by decide))) (by rw [b800012b8_keeps h₁ .x23 (by decide), x23])
    (b800012b8_pc h₁)
  exact ⟨t', hr.trans hr', hd⟩

/-! ## The loop -/

/-- The registers the stages keep: `ra`, `sp` and the callee-saved ones. -/
def keepRegs : List Reg :=
  [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The `n`-element buffer of `E` at `P`: aligned, in the heap. -/
def VBuf (P : Word) (n : Nat) : Prop :=
  P.toNat % 8 = 0 ∧ (n = 0 ∨ 0x20000000 ≤ P.toNat ∧ P.toNat + 24 * n ≤ 0x78000000)

/-- At `0x80001184`, `i` elements checked; `w` is the state at the loop's entry. -/
structure HighLoop (v w : MachineState) (P L : Word) (i : Nat) (u : MachineState) : Prop where
  pc : u.pc = 0x80001184
  mem : ∀ a, u.getMem a = v.getMem a
  regs : ∀ r ∈ keepRegs, u.getReg r = w.getReg r
  le : i ≤ L.toNat
  x10 : (u.getReg .x10).toNat + 24 * i = 24 * L.toNat
  x11 : u.getReg .x11 = P + BitVec.ofNat 64 (24 * i)
  zero : ∀ j < i, v.getMem (P + BitVec.ofNat 64 (24 * j) + 8) = 0 ∧
    v.getMem (P + BitVec.ofNat 64 (24 * j) + 16) = 0

/-- Where the loop leaves: every element checked at `0x800011b8`, or a nonzero limb at
`0x800012bc`. -/
def HighOut (v w : MachineState) (P L : Word) (t : MachineState) : Prop :=
  (∀ a, t.getMem a = v.getMem a) ∧ (∀ r ∈ keepRegs, t.getReg r = w.getReg r) ∧
    ((t.pc = 0x800011b8 ∧ ∀ j < L.toNat, v.getMem (P + BitVec.ofNat 64 (24 * j) + 8) = 0 ∧
      v.getMem (P + BitVec.ofNat 64 (24 * j) + 16) = 0) ∨ t.pc = 0x800012bc)

theorem elem_toNat {P : Word} {n i : Nat} (hL : P.toNat + 24 * n ≤ 0x78000000) (hi : i < n) :
    (P + BitVec.ofNat 64 (24 * i)).toNat = P.toNat + 24 * i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : 24 * i % 2 ^ 64 = 24 * i := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  exact Nat.mod_eq_of_lt (by omega)

theorem add8_toNat {x : Word} (h : x.toNat + 16 < 0x78000000) :
    (x + 8).toNat = x.toNat + 8 ∧ (x + 16).toNat = x.toNat + 16 := by
  have e8 : (8 : Word).toNat = 8 := rfl
  have e16 : (16 : Word).toNat = 16 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_add, e8, e16]
  exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩

theorem elem_succ (P : Word) (i : Nat) :
    P + BitVec.ofNat 64 (24 * i) + 24 = P + BitVec.ofNat 64 (24 * (i + 1)) := by
  rw [BitVec.add_assoc, show 24 * (i + 1) = 24 * i + 24 by ring, BitVec.ofNat_add]
  rfl

theorem highBody {v w u : MachineState} {P L : Word} {i : Nat} (hb : VBuf P L.toNat)
    (h : HighLoop v w P L i u) :
    (∃ t, Reaches Image.code u t ∧ HighOut v w P L t) ∨
      (∃ t, Reaches Image.code u t ∧ HighLoop v w P L (i + 1) t ∧
        (t.getReg .x10).toNat < (u.getReg .x10).toNat) := by
  obtain ⟨hP8, hPL⟩ := hb
  have hle := h.le
  have hx10 := h.x10
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001184_spec h.pc (by rv_eval [])
  have m₁ := b80001184_mem_same h₁
  have k₁ := b80001184_keeps h₁
  by_cases hi : i = L.toNat
  · refine Or.inl ⟨t₁, hr₁, fun a ↦ (m₁ a).trans (h.mem a),
      fun r hr ↦ (k₁ r (mem_of_mem hr _)).trans (h.regs r hr), Or.inl ⟨?_, ?_⟩⟩
    · refine b80001184_pc_taken h₁ ?_
      apply BitVec.eq_of_toNat_eq
      have h0 : (0 : Word).toNat = 0 := rfl
      rw [h0]; omega
    · intro j hj; exact h.zero j (by omega)
  have hi' : i < L.toNat := by omega
  have hL : 0x20000000 ≤ P.toNat ∧ P.toNat + 24 * L.toNat ≤ 0x78000000 := by omega
  have x11 : t₁.getReg .x11 = P + BitVec.ofNat 64 (24 * i) := by
    rw [k₁ .x11 (by decide), h.x11]
  have hA := elem_toNat hL.2 hi'
  obtain ⟨hA8, hA16⟩ := add8_toNat (x := P + BitVec.ofNat 64 (24 * i)) (by omega)
  have hm : Mapped P (24 * L.toNat) := Or.inl ⟨by omega, by omega⟩
  have hne : u.getReg .x10 ≠ 0 := by
    intro he
    have he' := congrArg BitVec.toNat he
    have h0 : (0 : Word).toNat = 0 := rfl
    omega
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001188_spec (b80001184_pc_not_taken h₁ hne) (by
    rv_eval [x11]
    exact ⟨Mapped.valid8 hm (by omega) (by omega) (by omega),
      Mapped.valid8 hm (by omega) (by omega) (by omega)⟩)
  have m₂ := b80001188_mem_same h₂
  have k₂ := b80001188_keeps h₂
  have mt : ∀ a, t₂.getMem a = v.getMem a := fun a ↦ (m₂ a).trans ((m₁ a).trans (h.mem a))
  have rt : ∀ r ∈ keepRegs, t₂.getReg r = w.getReg r := fun r hr ↦
    (k₂ r (mem_of_mem hr _)).trans ((k₁ r (mem_of_mem hr _)).trans (h.regs r hr))
  have e8 : t₁.getMem (t₁.getReg .x11 + 8) = v.getMem (P + BitVec.ofNat 64 (24 * i) + 8) := by
    rw [x11, m₁, h.mem]
  have e16 : t₁.getMem (t₁.getReg .x11 + 16) = v.getMem (P + BitVec.ofNat 64 (24 * i) + 16) := by
    rw [x11, m₁, h.mem]
  have x10₂ : (t₂.getReg .x10).toNat + 24 = (u.getReg .x10).toNat := by
    rw [b80001188_x10 h₂, k₁ .x10 (by decide), AddrOmega.sub_le _ _ (by rw [show (24 : Word).toNat = 24 from rfl]; omega)]
    rw [show (24 : Word).toNat = 24 from rfl]; omega
  by_cases hc : t₁.getMem (t₁.getReg .x11 + (8 : Word)) ||| t₁.getMem (t₁.getReg .x11 + 16) = 0
  · have hz := BitVec.or_eq_zero_iff.mp hc
    rw [e8, e16] at hz
    refine Or.inr ⟨t₂, hr₁.trans hr₂, ⟨b80001188_pc_taken h₂ hc, mt, rt, by omega, by omega, ?_,
      fun j hj ↦ ?_⟩, by omega⟩
    · rw [b80001188_x11 h₂, x11, elem_succ]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h.zero j hj
      · exact hz
  · obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800011a0_spec (b80001188_pc_not_taken h₂ hc)
      (by rv_eval [])
    exact Or.inl ⟨t₃, hr₁.trans (hr₂.trans hr₃), fun a ↦ (b800011a0_mem_same h₃ a).trans (mt a),
      fun r hr ↦ (b800011a0_keeps h₃ r (mem_of_mem hr _)).trans (rt r hr),
      Or.inr (b800011a0_pc h₃)⟩

theorem highLoop {v w : MachineState} {P L : Word} (hb : VBuf P L.toNat) :
    ∀ u, (∃ i, HighLoop v w P L i u) → ∃ t, Reaches Image.code u t ∧ HighOut v w P L t :=
  Reaches.loop _ (fun u ↦ (u.getReg .x10).toNat) _ fun _ ⟨_, h⟩ ↦
    (highBody hb h).imp id fun ⟨t, hr, ht, hlt⟩ ↦ ⟨t, hr, ⟨_, ht⟩, hlt⟩

/-! ## The stage -/

/-- `walk` once the announced scalars' high limbs are checked. -/
def afterHigh (s : MachineState) (a : List E) : TM SummaryRust :=
  (announcedTail (Proofs.Bytecode.readBytecode s (s.getReg .x11)) a >>=
      bodyRest (Proofs.Bytecode.readBytecode s (s.getReg .x11)) (bytesAt s (s.getReg .x12) 32)) >>=
    finishRust

theorem afterScalars_eq (s : MachineState) (a : List E) :
    afterScalars s a = TM.require (a.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0) >>=
      fun _ ↦ afterHigh s a := by
  simp only [afterScalars, afterHigh, bind_assoc]

theorem limb1_eAt (u : MachineState) (a : Word) :
    (eAt u a).limb 1 = BF64.ofBitVec (u.getMem (a + 8)) := rfl

theorem limb2_eAt (u : MachineState) (a : Word) :
    (eAt u a).limb 2 = BF64.ofBitVec (u.getMem (a + 16)) := rfl

theorem all_high {v : MachineState} {P : Word} {n : Nat}
    (hz : ∀ j < n, v.getMem (P + BitVec.ofNat 64 (24 * j) + 8) = 0 ∧
      v.getMem (P + BitVec.ofNat 64 (24 * j) + 16) = 0) :
    ((eListAt v P n).all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0) = true := by
  rw [List.all_eq_true]
  intro x hx
  simp only [eListAt, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  obtain ⟨z1, z2⟩ := hz j hj
  rw [decide_eq_true_eq, limb1_eAt, limb2_eAt, z1, z2]
  exact ⟨rfl, rfl⟩

/-- At `0x800011b8`: the announced scalars `A` hold in the `n`-element buffer at `P`, their high
limbs zero, and the code runs `afterHigh`. -/
structure High (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (P : Word) (n : Nat) : Prop where
  inv : Inv s u
  regs : Regs s u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  x8 : u.getReg .x8 = P
  x9 : u.getReg .x9 = BitVec.ofNat 64 n
  x26 : u.getReg .x26 = s.getReg .x2 - 512
  buf : VBuf P n
  below : n = 0 ∨ P.toNat + 24 * n ≤ heapNext u
  elems : eListAt u P n = A
  tracks : Tracks OI s u (afterHigh s A)

theorem high {OI : MachineState → Word → List (List Opening) → Prop} {s v : MachineState}
    (hpre : WalkPre s) (hpc : v.pc = 0x8000116c) (h : Announced OI s v) :
    ∃ t, Reaches Image.code v t ∧
      ((t.pc = 0x800011b8 ∧ High OI s t (vecEs v (s.getReg .x2 - 928)) (v.getReg .x8)
        (v.getReg .x9).toNat) ∨ Done OI s t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hv := h.vec.vec
  have hraw := hv.raw
  have hlen := hv.len
  have hhi := h.inv.heap.hi
  simp only [RawVecOk, Buf, heapNext, heapEnd, heapStart] at hraw hhi
  rw [← h.x8] at hraw
  rw [← h.x9] at hlen
  have hbuf : VBuf (v.getReg .x8) (v.getReg .x9).toNat := by
    simp only [VBuf]; omega
  have hbelow : (v.getReg .x9).toNat = 0 ∨
      (v.getReg .x8).toNat + 24 * (v.getReg .x9).toNat ≤ heapNext v := by
    simp only [heapNext]; omega
  obtain ⟨w, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000116c_spec hpc (by rv_eval [])
  have x16x8 (x : Word) : x * 16 + x * 8 = x * 24 := by
    rw [← BitVec.mul_add]; rfl
  have k₀ := b8000116c_keeps h₀
  have m₀ := b8000116c_mem_same h₀
  have start : HighLoop v w (v.getReg .x8) (v.getReg .x9) 0 w := {
    pc := b8000116c_pc h₀
    mem := m₀
    regs := fun _ _ ↦ rfl
    le := Nat.zero_le _
    x10 := by
      rw [b8000116c_x10 h₀, x16x8]
      obtain ⟨-, hL⟩ := hbuf
      rw [Nat.mul_zero, Nat.add_zero, BitVec.toNat_mul, show (24 : Word).toNat = 24 from rfl,
        Nat.mod_eq_of_lt (by omega)]
      ring
    x11 := by rw [b8000116c_x11 h₀]; simp
    zero := fun _ h ↦ absurd h (Nat.not_lt_zero _) }
  obtain ⟨t, hr, mt, rt, out⟩ := highLoop hbuf w ⟨0, start⟩
  have It : Inv s t := h.inv.same mt (by rw [rt .x2 (by decide), k₀ .x2 (by decide)])
  have regs : Regs s t := h.regs.keep fun r hr ↦ by
    rw [rt r (mem_of_mem hr _), k₀ r (mem_of_mem hr _)]
  rcases out with ⟨hpc', hz⟩ | hpc'
  · refine ⟨t, hr₀.trans hr, Or.inl ⟨hpc', {
      inv := It
      regs := regs
      proofPtr := by rw [mt]; exact h.proofPtr
      checked := ?_
      x8 := by rw [rt .x8 (by decide), k₀ .x8 (by decide)]
      x9 := by rw [rt .x9 (by decide), k₀ .x9 (by decide)]; simp
      x26 := by
        rw [rt .x26 (by decide), b8000116c_x26 h₀, h.inv.sp]
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      buf := hbuf
      below := by simp only [heapNext, mt]; exact hbelow
      elems := ?_
      tracks := ?_ }⟩⟩
    · have ha : (tp s + 360).toNat % 8 = 0 := by
        obtain ⟨-, -, hb3, -⟩ := bounds hpre
        rw [tp]; addr_omega [hb1, hb3]
      rw [byteAt_congr ha (mt _)]
      exact h.checked
    · simp only [vecEs, vecPtr, vecLen, eListAt, eAt, mt]
      rw [← vecPtr, ← vecLen, ← h.x8, ← h.x9]
    · have hA : vecEs v (s.getReg .x2 - 928) = eListAt v (v.getReg .x8) (v.getReg .x9).toNat := by
        rw [vecEs, h.x8, h.x9]
      have tr : Tracks OI s t (afterScalars s (vecEs v (s.getReg .x2 - 928))) :=
        h.tracks.keep fun T hT ↦ TranscriptAt.same hpre h.inv h.proofPtr mt hT
      rw [afterScalars_eq] at tr
      exact tr.require (by rw [hA]; exact all_high hz)
  · obtain ⟨t', hr', hd⟩ := err12bc (OI := OI) hpre It (by rw [regs.x23]) hpc'
    exact ⟨t', hr₀.trans (hr.trans hr'), Or.inr hd⟩

end Rv64Verifier.Proofs.Walk
