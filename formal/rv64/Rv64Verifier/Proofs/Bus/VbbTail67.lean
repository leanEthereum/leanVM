import Rv64Verifier.Proofs.Bus.VbbTail66

/-!
# `verify_bus_balance`'s side loop: the total pushed

`0x80007480` stores the side's total after the totals and counts the side (`pushTot`): from `t`
past `0x80007bbc` with `Mm` and room (`Push`), the matrix, its forms and the totals hold at the next
head (or past the last side).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the totals' growth and push write, as the matrix sees it: the totals' header, the saved
registers, the stack below the frame, `NEXT` and the old totals' buffer. -/
def PushO (s t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 632) 24 ∨ Within a (s.getReg .x2 - 1136) 32 ∨
    Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨
    Within a (vecPtr t (s.getReg .x2 - 632)) (24 * (vecCap t (s.getReg .x2 - 632)).toNat)

theorem PushO.miss {s z h e t : MachineState} {P : Word} {n : Nat} {fs : List (List Form)}
    {tot : List E} (hpre : BusBalancePre s) (M : Mm s z h e t P n fs tot) {x : Word}
    (hx : PushO s t x) : ¬ Within x P (24 * n) ∧ ∀ a < n, ∀ j ≤ 3, ¬ piece t P a j x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have htE := M.cur.inv.heap.hi
  have hP := M.mat.hdr.2
  simp only [heapNext, heapEnd] at htE
  have out (hlo : x.toNat < heapStart ∨ heapEnd ≤ x.toNat) :
      ¬ Within x P (24 * n) ∧ ∀ a < n, ∀ j ≤ 3, ¬ piece t P a j x := by
    refine ⟨fun hw ↦ ?_, fun a ha j hj hp ↦ ?_⟩
    · rcases hP with h0 | ⟨b1, b2⟩
      · simp only [Within] at hw; omega
      · simp only [Within, heapStart, heapEnd, heapNext] at hw hlo b1 b2; omega
    · have := M.mat.below ha hj hp
      simp only [heapStart, heapEnd, heapNext] at this hlo; omega
  rcases hx with hx | hx | hx | hx | hx
  · exact out (Or.inr (by simp only [heapEnd]; addr_omega [hx, hb1]))
  · exact out (Or.inr (by simp only [heapEnd]; addr_omega [hx, hb1]))
  · exact out (Or.inr (by simp only [heapEnd]; addr_omega [hx, hb1]))
  · exact out (Or.inr (by simp only [heapEnd, nextAddr] at hx ⊢; addr_omega [hx]))
  · exact M.tbuf x hx

set_option maxRecDepth 8192 in
theorem pushTot {s z h e t q : MachineState} {P : Word} {n : Nat} {fs : List (List Form)}
    {tot : List E} {total : E} {i : Nat} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z)
    (M : Mm s z h e t P n fs tot) (Q : Push s z h t q tot) (hpc : q.pc = 0x80007480)
    (hx21 : t.getReg .x21 = vecLen t (s.getReg .x2 - 632))
    (hx22 : t.getReg .x22 = BitVec.ofNat 64 i) (hi : i < 3)
    (htot : eOf3 ((((t.getReg .x17 ^^^ t.getReg .x19) ^^^ t.getReg .x28) ^^^ t.getReg .x24) ^^^ 1)
      (((t.getReg .x23 ^^^ t.getReg .x16) ^^^ t.getReg .x8) ^^^ t.getReg .x26)
      (((t.getReg .x18 ^^^ t.getReg .x15) ^^^ t.getReg .x30) ^^^ t.getReg .x27) = total) :
    ∃ h', Reaches Image.code q h' ∧ Cur s z h h' ∧ Mat z h' P n ∧
      (∀ a < n, ∀ j < 3, (vecPtr h' (cellAt h' (rowAt P a) j)).toNat +
        48 * (vecLen h' (cellAt h' (rowAt P a) j)).toNat ≤ heapNext h') ∧
      formRowsAt h' P n = fs ∧ NewVecE z h' (s.getReg .x2 - 632) (tot ++ [total]) ∧
      (∀ x, Within x (vecPtr h' (s.getReg .x2 - 632))
          (24 * (vecCap h' (s.getReg .x2 - 632)).toNat) →
        ¬ Within x P (24 * n) ∧ ∀ a < n, ∀ j ≤ 3, ¬ piece h' P a j x) ∧
      h'.getReg .x25 = t.getReg .x25 ∧ h'.getReg .x27 = q.getMem (s.getReg .x2 - 1256) ∧
      ((i + 1 < 3 ∧ h'.pc = 0x800074e0 ∧ h'.getReg .x22 = BitVec.ofNat 64 (i + 1)) ∨
        (i + 1 = 3 ∧ h'.pc = 0x80007c2c)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have Cq := Q.cur
  have spq : q.getReg .x2 = s.getReg .x2 - 1344 := Cq.inv.sp
  have hqE := Cq.inv.heap.hi
  have hx21q : q.getReg .x21 = vecLen t (s.getReg .x2 - 632) :=
    (Q.regs .x21 (by decide)).trans hx21
  have m624 : q.getMem (s.getReg .x2 - 624) = vecPtr q (s.getReg .x2 - 632) := by
    simp only [vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have room := Q.room
  have TQ := Q.totals
  have raw := TQ.vec.raw
  simp only [RawVecOk, Buf] at raw
  obtain ⟨P8, Pb⟩ := raw
  have Pb' := Pb.resolve_left (by omega)
  have zb := TQ.buf
  simp only [NewBuf] at zb
  have zb' := zb.2.resolve_left (by omega)
  simp only [heapStart, heapNext, heapEnd] at Pb' hqE zb'
  have hvP : ValidMemRange (vecPtr q (s.getReg .x2 - 632))
      (3 * (vecCap q (s.getReg .x2 - 632)).toNat) :=
    heapRange P8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  obtain ⟨h', hr, hh⟩ := Sym.BlockSpec.reaches b80007480_spec hpc (by
    rv_eval [spq, m624, hx21q, mul24w]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hvP [Pb', room, hqE]
      | addr_omega [Pb', room, hqE, hb1])
  have k := b80007480_keeps hh
  have a720 : q.getReg .x2 + 720 = s.getReg .x2 - 624 := by
    rw [spq]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a728 : q.getReg .x2 + 728 = s.getReg .x2 - 616 := by
    rw [spq]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a88 : q.getReg .x2 + 88 = s.getReg .x2 - 1256 := by
    rw [spq]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e0 := b80007480_m3 hh
  have e8 := b80007480_m2 hh
  have e16 := b80007480_m1 hh
  have e728 := b80007480_m_x2_728 hh
  rw [a720, m624, hx21q, mul24w] at e0 e8 e16
  rw [a728, hx21q] at e728
  have fq : DFrame q h' fun a ↦ Within a (s.getReg .x2 - 616) 8 ∨ Within a (vecPtr q (s.getReg .x2 - 632) + BitVec.ofNat 64 (24 * (vecLen t (s.getReg .x2 - 632)).toNat)) 24 :=
    fun a ha ↦ hh.frame a (by
      rv_eval [spq, m624, hx21q, mul24w]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]
        first
          | exact Or.inl (by addr_omega [hb1])
          | exact Or.inr (by addr_omega [Pb', room, hqE])))
  have nxA : ∀ j < 8, ¬ (Within (nextAddr + BitVec.ofNat 64 j) (s.getReg .x2 - 616) 8 ∨
      Within (nextAddr + BitVec.ofNat 64 j) (vecPtr q (s.getReg .x2 - 632) + BitVec.ofNat 64 (24 * (vecLen t (s.getReg .x2 - 632)).toNat)) 24) := fun j hj hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hj, hb1, hnx]
    · simp only [nextAddr] at hw; addr_omega [hw, hj, Pb', room, hqE]
  have hn' : heapNext h' = heapNext q := by
    simp only [heapNext]; rw [fq nextAddr nxA]
  have st : StepS s q h' fun a ↦ Within a (s.getReg .x2 - 616) 8 ∨ Within a (vecPtr q (s.getReg .x2 - 632) + BitVec.ofNat 64 (24 * (vecLen t (s.getReg .x2 - 632)).toNat)) 24 :=
    StepS.ofDFrame Cq.inv.heap fq (fun _ h ↦ h) nxA (k .x2 (by decide))
  have Ch : Cur s z h h' := Cq.next hpre hsz st fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl (by
        simp only [SlotW]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))))
    · exact Or.inr ⟨by simp only [heapNext]; addr_omega [ha, zb', Pb', room],
        by rw [hn']; simp only [heapNext]; addr_omega [ha, Pb', room, hqE]⟩
  -- the matrix
  have hmq := Q.mono
  have fth : DFrame t h' fun a ↦ PushO s t a ∨ Fresh t h' a := by
    refine (Q.fr.mono fun a ha ↦ ?_).trans fq fun a ha ↦ ?_
    · rcases ha with ha | ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inl (Or.inr (Or.inl ha))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · exact Or.inr ⟨a1, by rw [hn']; exact a2⟩
    · rcases ha with ha | ha
      · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
      · rcases Q.buf with ⟨p1, c1⟩ | nb
        · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
          rw [← p1, ← c1]
          addr_omega [ha, Pb', room]
        · simp only [NewBuf] at nb
          have nb' := nb.2.resolve_left (by omega)
          refine Or.inr ⟨?_, ?_⟩
          · simp only [heapNext] at nb' ⊢; addr_omega [ha, nb', room]
          · rw [hn']; simp only [heapNext]; addr_omega [ha, Pb', room, hqE]
  have It := M.cur.inv
  obtain ⟨Mh, hrow, hcell, hform⟩ := M.mat.keepO It.heap (le_trans hmq (le_of_eq hn'.symm)) fth
    fun x hx ↦ PushO.miss hpre M hx
  have pe (a : Nat) (ha : a < n) (j : Nat) (hj : j ≤ 3) (x : Word) :
      piece h' P a j x ↔ piece t P a j x :=
    piece_congr (hrow a ha) (fun h3 k hk ↦ hcell a ha j h3 k hk) x
  -- the totals' header
  have hdr (j : Nat) (hj : j = 0 ∨ j = 8) :
      h'.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 j) =
        q.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 j) :=
    fq _ fun r hr hw ↦ by
      rcases hw with hw | hw
      · rcases hj with rfl | rfl <;> addr_omega [hw, hr, hb1]
      · rcases hj with rfl | rfl <;> addr_omega [hw, hr, hb1, Pb', room, hqE]
  have ph : vecPtr h' (s.getReg .x2 - 632) = (vecPtr q (s.getReg .x2 - 632)) := hdr 8 (Or.inr rfl)
  have ch : vecCap h' (s.getReg .x2 - 632) = vecCap q (s.getReg .x2 - 632) := by
    have := hdr 0 (Or.inl rfl); simp only [add_ofNat_zero] at this; exact this
  have lh : vecLen h' (s.getReg .x2 - 632) = (vecLen t (s.getReg .x2 - 632)) + 1 := by
    have e : s.getReg .x2 - 632 + 16 = s.getReg .x2 - 616 := by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    show h'.getMem (s.getReg .x2 - 632 + 16) = _
    rw [e]; exact e728
  have hL1 : ((vecLen t (s.getReg .x2 - 632)) + 1).toNat = (vecLen t (s.getReg .x2 - 632)).toNat + 1 := by
    have : (vecLen t (s.getReg .x2 - 632)).toNat + 1 < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl, Nat.mod_eq_of_lt this]
  refine ⟨h', hr, Ch, Mh, fun a ha j hj ↦ ?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, fun x hx ↦ ?_,
    (k .x25 (by decide)).trans (Q.regs .x25 (by decide)), by rw [b80007480_x27 hh, a88], ?_⟩
  · have hptr : vecPtr h' (rowAt P a) = vecPtr t (rowAt P a) := by
      have h := hrow a ha 1 (by omega); simp only [Nat.mul_one] at h; exact h
    have hc : cellAt h' (rowAt P a) j = cellAt t (rowAt P a) j := by simp only [cellAt, hptr]
    have ep : vecPtr h' (cellAt t (rowAt P a) j) = vecPtr t (cellAt t (rowAt P a) j) := by
      simpa [vecPtr] using hcell a ha j hj 1 (by omega)
    have el : vecLen h' (cellAt t (rowAt P a) j) = vecLen t (cellAt t (rowAt P a) j) := by
      simpa [vecLen] using hcell a ha j hj 2 (by omega)
    rw [hc, ep, el, hn']
    exact le_trans (M.below a ha j hj) hmq
  · rw [formRowsAt_keep (fun a ha ↦ (M.mat.rows a ha).2) hrow hform]; exact M.value
  · simp only [RawVecOk, Buf]
    rw [ph, ch, hn']
    exact ⟨P8, Pb⟩
  · rw [lh, ch, hL1]; omega
  · simp only [NewBuf]
    rw [ph, ch, hn']
    exact zb
  · simp only [vecEs]
    rw [ph, lh, hL1, eListAt_succ]
    have hold : eListAt h' (vecPtr q (s.getReg .x2 - 632)) (vecLen t (s.getReg .x2 - 632)).toNat = eListAt q (vecPtr q (s.getReg .x2 - 632)) (vecLen t (s.getReg .x2 - 632)).toNat :=
      fq.eListAt fun r hr hw ↦ by
        rcases hw with hw | hw
        · addr_omega [hw, hr, hb1, Pb', room, hqE]
        · addr_omega [hw, hr, Pb', room, hqE]
    have hq := TQ.elems
    simp only [vecEs] at hq
    rw [Q.len] at hq
    rw [hold, hq, ← htot, eAt_eq_eOf3, e0, e8, e16]
    rw [Q.regs .x17 (by decide), Q.regs .x19 (by decide), Q.regs .x28 (by decide),
      Q.regs .x24 (by decide), Q.regs .x23 (by decide), Q.regs .x16 (by decide),
      Q.regs .x8 (by decide), Q.regs .x26 (by decide), Q.regs .x18 (by decide),
      Q.regs .x15 (by decide), Q.regs .x30 (by decide), Q.regs .x27 (by decide)]
  · rw [ph, ch] at hx
    rcases Q.buf with ⟨p1, c1⟩ | nb
    · rw [p1, c1] at hx
      obtain ⟨t1, t2⟩ := M.tbuf x hx
      exact ⟨t1, fun a ha j hj hp ↦ t2 a ha j hj ((pe a ha j hj x).mp hp)⟩
    · simp only [NewBuf] at nb
      have nb' := nb.2.resolve_left (by omega)
      have hxt : heapNext t ≤ x.toNat := by
        simp only [Within] at hx; simp only [heapNext] at nb' ⊢; omega
      have hP := M.mat.hdr.2
      refine ⟨fun hw ↦ ?_, fun a ha j hj hp ↦ ?_⟩
      · rcases hP with h0 | ⟨-, b2⟩
        · simp only [Within] at hw; omega
        · simp only [Within] at hw; omega
      · have := M.mat.below ha hj ((pe a ha j hj x).mp hp); omega
  · have x22q : q.getReg .x22 = BitVec.ofNat 64 i := (Q.regs .x22 (by decide)).trans hx22
    rw [b80007480_x22 hh, x22q]
    rcases Nat.lt_or_ge (i + 1) 3 with hlt | hge
    · refine Or.inl ⟨hlt, b80007480_pc_not_taken hh ?_, ?_⟩
      · rw [x22q]; interval_cases i <;> first | decide | omega
      · interval_cases i <;> decide
    · refine Or.inr ⟨by omega, b80007480_pc_taken hh ?_⟩
      obtain rfl : i = 2 := by omega
      rw [x22q]; decide

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
