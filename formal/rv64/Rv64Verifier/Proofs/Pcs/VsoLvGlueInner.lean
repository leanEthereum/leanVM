import Rv64Verifier.Proofs.Pcs.VsoLvGlueCalls

/-!
# `verify_stacked_opening`'s glue: the intro added to the running quadratic

The loop at `0x8000b75c`..`0x8000b778` adds `scalar * intro[j]` (the scalar at `S - 408`, the
intro's buffer `Ip`) to the quadratic's coefficient `j` (its buffer `Q`), for
`j < min(m, len)`: `ZInv` before coefficient `j`, `ZOut` at the exit `0x8000b7b8`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A step writing the frame below `S - 104` and the heap allocated since the entry keeps the
invariant and `NEXT`. -/
theorem invR_step {s c c' : MachineState} {X : Word → Prop} (hpre : VsoPre s)
    (h : InvR s c (c.getMem nextAddr)) (hheap : HeapOk c) (hX : DFrame c c' X)
    (hXs : ∀ a, X a → Within a (s.getReg .x2 - 2464) 2360 ∨
      (heapNext s ≤ a.toNat ∧ a.toNat < heapNext c))
    (hsp : c'.getReg .x2 = c.getReg .x2) :
    c'.getMem nextAddr = c.getMem nextAddr ∧ InvR s c' (c'.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhi := hheap.hi
  have nx : c'.getMem nextAddr = c.getMem nextAddr := hX _ fun i hi hx ↦ by
    rcases hXs _ hx with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · simp only [heapNext] at hw hhi; addr_omega [hw.2, hi, hhi]
  refine ⟨nx, ?_⟩
  rw [nx]
  refine Inv.step' hpre h hX (fun a ha ↦ ?_) (fun a ha ↦ ?_) nx (Nat.le_refl _)
    (by have := h.fits; exact this) hsp
  · rcases hXs a ha with hw | hw
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [hw, hb])))
    · exact Or.inr (Or.inr (Or.inr ⟨hw.1, by simp only [heapNext] at hw; exact hw.2⟩))
  · rcases hXs a ha with hw | hw
    · addr_omega [hw, hb]
    · simp only [heapEnd] at hhi; addr_omega [hw.2, hb, hhi]

/-- What the zip loop writes from `c0` on. -/
def ZW (s : MachineState) (Q : Word) (m : ℕ) (a : Word) : Prop :=
  Within a Q (24 * m) ∨ Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 2064) 1024

/-- The quadratic's coefficients after the first `j` were given `scalar * intro`. -/
def ZQuad (s c0 c : MachineState) (Q Ip : Word) (m j : ℕ) : Prop :=
  ∀ k < m, eAt c (Q + BitVec.ofNat 64 (24 * k)) =
    if k < j then eAt c0 (Q + BitVec.ofNat 64 (24 * k)) +
      eAt c0 (s.getReg .x2 - 408) * eAt c0 (Ip + BitVec.ofNat 64 (24 * k))
    else eAt c0 (Q + BitVec.ofNat 64 (24 * k))

/-- The registers the zip loop keeps. -/
def ZK : List Reg := [.x9, .x18, .x20, .x23, .x24, .x25, .x26, .x27]

/-- At `0x8000b75c`, before coefficient `j`. -/
structure ZInv (s c0 c : MachineState) (Q Ip : Word) (m len j : ℕ) : Prop where
  pc : c.pc = 0x8000b75c
  sp : c.getReg .x2 = s.getReg .x2 - 1040
  keep : ∀ r ∈ ZK, c.getReg r = c0.getReg r
  x8 : c.getReg .x8 = BitVec.ofNat 64 (24 * (len - j))
  x19 : c.getReg .x19 = Q + BitVec.ofNat 64 (24 * j)
  x12 : c.getReg .x12 = Ip + BitVec.ofNat 64 (24 * j)
  x27 : c0.getReg .x27 = Q + BitVec.ofNat 64 (24 * m)
  jm : j < m
  jl : j ≤ len
  inv : InvR s c (c.getMem nextAddr)
  heap : HeapOk c
  nx : c.getMem nextAddr = c0.getMem nextAddr
  fr : DFrame c0 c (ZW s Q m)
  quad : ZQuad s c0 c Q Ip m j

/-- At `0x8000b7b8`, the zip loop done. -/
structure ZOut (s c0 c : MachineState) (Q Ip : Word) (m len : ℕ) : Prop where
  pc : c.pc = 0x8000b7b8
  sp : c.getReg .x2 = s.getReg .x2 - 1040
  keep : ∀ r ∈ ZK, c.getReg r = c0.getReg r
  inv : InvR s c (c.getMem nextAddr)
  heap : HeapOk c
  nx : c.getMem nextAddr = c0.getMem nextAddr
  fr : DFrame c0 c (ZW s Q m)
  quad : ZQuad s c0 c Q Ip m (min m len)

/-- Where the quadratic and the intro lie. -/
structure ZBufs (s c0 : MachineState) (Q Ip : Word) (m len : ℕ) : Prop where
  q : heapNext s ≤ Q.toNat ∧ Q.toNat + 24 * m ≤ heapNext c0 ∧ Q.toNat % 8 = 0
  i : Ip.toNat % 8 = 0 ∧ (len = 0 ∨ 0x20 ≤ Ip.toNat ∧ Ip.toNat + 24 * len ≤ heapEnd)
  ap : Apart Q (24 * m) Ip (24 * len)
  len : 24 * len < 2 ^ 64

/-- **The zip loop**, from coefficient `j` to its exit. -/
theorem zloop (hM : MulSpec) {s c0 : MachineState} {Q Ip : Word} {m len : ℕ} (hpre : VsoPre s)
    (hz : ZBufs s c0 Q Ip m len) :
    ∀ k j (c : MachineState), min m len - j = k → ZInv s c0 c Q Ip m len j →
      ∃ c', Reaches Image.code c c' ∧ (Dead Image.code c' ∨ ZOut s c0 c' Q Ip m len) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsl := hpre.heap.lo
  obtain ⟨hq1, hq2, hq3⟩ := hz.q
  intro k
  induction k with
  | zero =>
    intro j c hk hc
    have hjm := hc.jm
    have hjl := hc.jl
    have hj : j = len := by omega
    obtain ⟨c', r, h⟩ := Sym.BlockSpec.reaches b8000b75c_spec hc.pc trivial
    have hm := b8000b75c_mem_same h
    have kk := b8000b75c_keeps h
    refine ⟨c', r, Or.inr {
      pc := b8000b75c_pc_taken h (by rw [hc.x8, hj, Nat.sub_self]; rfl)
      sp := (kk .x2 (by decide)).trans hc.sp
      keep := fun r hr ↦ (kk r (by simp only [ZK] at hr; revert hr; decide +revert)).trans
        (hc.keep r hr)
      inv := by rw [hm]; exact Inv.same' hc.inv hm (kk .x2 (by decide))
      heap := ⟨by simp only [heapNext, hm]; exact hc.heap.lo, by simp only [heapNext, hm]; exact hc.heap.hi⟩
      nx := by rw [hm]; exact hc.nx
      fr := (hc.fr.trans (DFrame.of_same hm _)) fun _ h ↦ h
      quad := fun k' hk' ↦ by
        rw [show min m len = j by omega]
        simp only [eAt, hm]; exact hc.quad k' hk' }⟩
  | succ k ih =>
    intro j c hk hc
    have hjl : j < len := by have := hc.jm; omega
    have hjm := hc.jm
    have hlen := hz.len
    obtain ⟨hI8, hI⟩ := hz.i
    have hI' : 0x20 ≤ Ip.toNat ∧ Ip.toNat + 24 * len ≤ heapEnd := by
      rcases hI with h0 | h0
      · omega
      · exact h0
    have hhc := hc.heap.hi
    have hQe : Q.toNat + 24 * m ≤ heapNext c := by
      have : heapNext c = heapNext c0 := by simp only [heapNext, hc.nx]
      omega
    have hQb : Q.toNat + 24 * m ≤ 2013265920 := by simp only [heapEnd] at hhc; omega
    have hQ0 : 0x20000000 ≤ Q.toNat := by simp only [heapStart] at hsl; omega
    -- `0x8000b75c`, `0x8000b760`, `0x8000b764`
    obtain ⟨c1, r1, h1⟩ := Sym.BlockSpec.reaches b8000b75c_spec hc.pc trivial
    have hpc1 := b8000b75c_pc_not_taken h1 (by
      rw [hc.x8]; intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega)
    have k1 := b8000b75c_keeps h1
    have m1 := b8000b75c_mem_same h1
    obtain ⟨c2, r2, h2⟩ := Sym.BlockSpec.reaches b8000b760_spec hpc1 trivial
    have hpc2 := b8000b760_pc_not_taken h2 (by
      rw [k1 .x19 (by decide), hc.x19]; intro he
      have := congrArg BitVec.toNat he
      simp only [heapStart] at hsl
      addr_omega [this, hq1, hQb, hjm, hsl])
    have k2 := b8000b760_keeps h2
    have m2 := b8000b760_mem_same h2
    obtain ⟨c3, r3, h3⟩ := Sym.BlockSpec.reaches b8000b764_spec hpc2 trivial
    have k3 := b8000b764_keeps h3
    have m3 := b8000b764_mem_same h3
    have m13 (a : Word) : c3.getMem a = c.getMem a := by rw [m3, m2, m1]
    have sp3 : c3.getReg .x2 = s.getReg .x2 - 1040 := by
      rw [k3 .x2 (by decide), k2 .x2 (by decide), k1 .x2 (by decide), hc.sp]
    have hinv3 : InvR s c3 (c3.getMem nextAddr) := by
      rw [m13]; exact Inv.same' hc.inv m13 (by rw [sp3, hc.sp])
    have hRQ : Region Q (24 * m) := heap_region (by simp only [heapStart] at hsl; omega)
      (by omega) hq3
    simp only [heapEnd] at hI' hhc
    obtain ⟨v, r4, hv⟩ := callMulH hM hpre hinv3 (b8000b764_pc h3) (o := s.getReg .x2 - 384)
      (a := s.getReg .x2 - 408) (b := Ip + BitVec.ofNat 64 (24 * j))
      (by rw [b8000b764_x10 h3, k2 .x2 (by decide), k1 .x2 (by decide), hc.sp]; rv_eval [])
      (by rw [b8000b764_x11 h3, k2 .x2 (by decide), k1 .x2 (by decide), hc.sp]; rv_eval [])
      (by rw [k3 .x12 (by decide), k2 .x12 (by decide), k1 .x12 (by decide), hc.x12])
      (by addr_omega [hb]) (by addr_omega [hb])
      (by simp only [heapEnd]; addr_omega [hI', hI8, hjl]) (by addr_omega [hb])
    rcases hv with hd | ⟨hpc4, hpres4, hfr4, hval4⟩
    · exact ⟨v, r1.trans (r2.trans (r3.trans r4)), Or.inl hd⟩
    have hpc4' : v.pc = 0x8000b778 := by
      rw [hpc4, returnAddress_eq, b8000b764_x1 h3]; decide
    have sp4 : v.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres4 .x2 (by decide), sp3]
    have x19v : v.getReg .x19 = Q + BitVec.ofNat 64 (24 * j) := by
      rw [hpres4 .x19 (by decide), k3 .x19 (by decide), k2 .x19 (by decide),
        k1 .x19 (by decide), hc.x19]
    obtain ⟨w, r5, h5⟩ := Sym.BlockSpec.reaches b8000b778_spec hpc4' (by
      rv_eval [sp4, x19v]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hRQ (by addr_omega [hQb, hjm]) (by addr_omega [hQb, hjm])
            (by addr_omega [hQb, hq3, hjm]))
    have k5 := b8000b778_keeps h5
    have f5 : DFrame v w (Within · (Q + BitVec.ofNat 64 (24 * j)) 24) := by
      have := DFrame.of_memFrame (b8000b778_frame h5 (by rw [x19v]; addr_omega [hQb, hjm]))
      rwa [x19v] at this
    -- the registers
    have kreg (r : Reg) (hr : r ∈ ZK) : w.getReg r = c0.getReg r := by
      have hr' : r ∈ calleeSaved := by simp only [ZK] at hr; revert hr; decide +revert
      rw [k5 r (by simp only [ZK] at hr; revert hr; decide +revert), hpres4 r hr',
        k3 r (by simp only [ZK] at hr; revert hr; decide +revert),
        k2 r (by simp only [ZK] at hr; revert hr; decide +revert),
        k1 r (by simp only [ZK] at hr; revert hr; decide +revert), hc.keep r hr]
    have sp5 : w.getReg .x2 = s.getReg .x2 - 1040 := by rw [k5 .x2 (by decide), sp4]
    -- memory and the invariant
    have hX4 : ∀ a, (Within a (s.getReg .x2 - 384) 24 ∨ Within a (s.getReg .x2 - 2064) 1024) →
        Within a (s.getReg .x2 - 2464) 2360 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext c3) :=
      fun a ha ↦ Or.inl (by rcases ha with ha | ha <;> addr_omega [ha, hb])
    have hheap3 : HeapOk c3 := ⟨by simp only [heapNext, m13]; exact hc.heap.lo,
      by simp only [heapNext, m13]; exact hc.heap.hi⟩
    obtain ⟨nx4, inv4⟩ := invR_step hpre hinv3 hheap3 hfr4 hX4 (by rw [sp4, sp3])
    have hn3 : heapNext c3 = heapNext c := by simp only [heapNext, m13]
    have hheap4 : HeapOk v := ⟨by simp only [heapNext, nx4]; exact hheap3.lo,
      by simp only [heapNext, nx4]; exact hheap3.hi⟩
    have hsv : heapNext s ≤ heapNext c := hc.inv.mono
    obtain ⟨nx5, inv5⟩ := invR_step hpre inv4 hheap4 f5 (fun a ha ↦ Or.inr ⟨by addr_omega [ha, hq1, hQb, hjm],
      by rw [show heapNext v = heapNext c by simp only [heapNext, nx4, m13]]
         addr_omega [ha, hQe, hjm, hQb]⟩) (by rw [sp5, sp4])
    have hnxw : w.getMem nextAddr = c0.getMem nextAddr := by rw [nx5, nx4, m13, hc.nx]
    have hheap5 : HeapOk w := ⟨by simp only [heapNext, nx5]; exact hheap4.lo,
      by simp only [heapNext, nx5]; exact hheap4.hi⟩
    have fr5 : DFrame c0 w (ZW s Q m) :=
      ((hc.fr.trans (DFrame.of_same m13 _) fun _ h ↦ h).trans hfr4 fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr ha)).trans f5 fun a ha ↦ Or.inl (by addr_omega [ha, hQb, hjm])
    -- the quadratic
    have quad5 : ZQuad s c0 w Q Ip m (j + 1) := by
      intro k' hk'
      by_cases hkj : k' = j
      · subst hkj
        simp only [show k' < k' + 1 by omega, ite_true]
        have hold : eAt v (Q + BitVec.ofNat 64 (24 * k')) = eAt c0 (Q + BitVec.ofNat 64 (24 * k')) := by
          rw [hfr4.eAt fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hQb, hjm]]
          simp only [eAt, m13]
          have := hc.quad k' hjm
          simp only [Nat.lt_irrefl, ite_false] at this
          exact this
        have hsc : eAt c3 (s.getReg .x2 - 408) = eAt c0 (s.getReg .x2 - 408) := by
          simp only [eAt, m13]
          exact hc.fr.eAt fun i hi hw ↦ by
            rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb, hQb]
        have hin : eAt c3 (Ip + BitVec.ofNat 64 (24 * k')) = eAt c0 (Ip + BitVec.ofNat 64 (24 * k')) := by
          simp only [eAt, m13]
          exact hc.fr.eAt fun i hi hw ↦ by
            have hap := hz.ap
            rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb, hap, hI', hjl, hQb, hQ0]
        rw [← hold, ← hsc, ← hin, ← hval4]
        apply eAt_eq_of_limbs
        rw [limbs_add, limbs_eAt, limbs_eAt]
        have e0 := b8000b778_m_x19_0 h5
        have e8 := b8000b778_m_x19_8 h5
        have e16 := b8000b778_m_x19_16 h5
        rw [x19v, sp4] at e0 e8 e16
        rw [e0, e8, e16, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval [],
          show s.getReg .x2 - 1040 + (664 : Word) = s.getReg .x2 - 384 + 8 by rv_eval [],
          show s.getReg .x2 - 1040 + (672 : Word) = s.getReg .x2 - 384 + 16 by rv_eval []]
        simp only [BitVec.xor_comm]
      · have e : eAt w (Q + BitVec.ofNat 64 (24 * k')) = eAt c (Q + BitVec.ofNat 64 (24 * k')) := by
          rw [f5.eAt fun i hi hw ↦ by addr_omega [hw, hi, hQb, hjm, hk', hkj]]
          rw [hfr4.eAt fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hQb, hk']]
          simp only [eAt, m13]
        rw [e, hc.quad k' hk']
        by_cases hlt : k' < j
        · simp only [hlt, show k' < j + 1 by omega, ite_true]
        · simp only [hlt, show ¬ k' < j + 1 by omega, ite_false]
    have r15 := r1.trans (r2.trans (r3.trans (r4.trans r5)))
    by_cases hend : j + 1 = m
    · refine ⟨w, r15, Or.inr {
        pc := b8000b778_pc_not_taken h5 (by
          rw [x19v, hpres4 .x27 (by decide), k3 .x27 (by decide), k2 .x27 (by decide),
            k1 .x27 (by decide), hc.keep .x27 (by decide), hc.x27, ← hend]
          addr_omega [hQb, hend])
        sp := sp5
        keep := kreg
        inv := inv5
        heap := hheap5
        nx := hnxw
        fr := fr5
        quad := by rw [show min m len = j + 1 by omega]; exact quad5 }⟩
    · have hpc5 := b8000b778_pc_taken h5 (by
        rw [x19v, hpres4 .x27 (by decide), k3 .x27 (by decide), k2 .x27 (by decide),
          k1 .x27 (by decide), hc.keep .x27 (by decide), hc.x27]
        intro he
        have := congrArg BitVec.toNat he
        addr_omega [this, hQb, hjm, hend])
      obtain ⟨c', r', h'⟩ := ih (j + 1) w (by omega) {
        pc := hpc5
        sp := sp5
        keep := kreg
        x8 := by
          rw [b8000b778_x8 h5, hpres4 .x8 (by decide), k3 .x8 (by decide), k2 .x8 (by decide),
            k1 .x8 (by decide), hc.x8]
          addr_omega [hlen, hjl]
        x19 := by rw [b8000b778_x19 h5, x19v]; addr_omega [hQb, hjm]
        x12 := by
          rw [b8000b778_x12 h5, hpres4 .x21 (by decide), b8000b764_x21 h3, k2 .x12 (by decide),
            k1 .x12 (by decide), hc.x12]
          addr_omega [hI', hjl]
        x27 := hc.x27
        jm := by omega
        jl := by omega
        inv := inv5
        heap := hheap5
        nx := hnxw
        fr := fr5
        quad := quad5 }
      exact ⟨c', r15.trans r', h'⟩

theorem eListAt_getD (u : MachineState) (p : Word) {n k : ℕ} (hk : k < n) :
    (eListAt u p n).getD k 0 = eAt u (p + BitVec.ofNat 64 (24 * k)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [eListAt_length]; exact hk),
    Option.getD_some, eListAt_getElem]

/-- The zip loop's result is `zipAddScaled`. -/
theorem ZQuad.eList {s c0 c : MachineState} {Q Ip : Word} {m len : ℕ}
    (h : ZQuad s c0 c Q Ip m (min m len)) :
    eListAt c Q m = Model.Pcs.zipAddScaled (eListAt c0 Q m) (eListAt c0 Ip len)
      (eAt c0 (s.getReg .x2 - 408)) := by
  rw [zipAddScaled_eq, eListAt_length, eListAt_length]
  apply List.ext_getElem (by simp [zipPart, eListAt_length])
  intro k h1 h2
  rw [eListAt_length] at h1
  rw [eListAt_getElem, h k h1]
  simp only [zipPart, List.getElem_map, List.getElem_range, eListAt_length]
  by_cases hk : k < min m len
  · simp only [hk, ite_true, eListAt_getD _ _ h1, eListAt_getD _ _ (show k < len by omega)]
  · simp only [hk, ite_false, eListAt_getD _ _ h1]

end Rv64Verifier.Proofs.Pcs.Vso
