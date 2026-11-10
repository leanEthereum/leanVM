import Rv64Verifier.Proofs.Pcs.VsoOpenFinal

/-!
# `verify_stacked_opening`'s level loop: the back edge

`0x8000b51c` copies the next root, spilled in the frame (`NR`), bytewise over the root (`[S - 840]`,
the root's address) and jumps back to the level's head at `0x8000a190` with the head's registers
reloaded (`backEdge`). `b51c_w0`..`b51c_w3` are the root's doublewords it writes.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem b51c_w3 {z v : MachineState} (h : b8000b51c.Holds z v) :
    v.getMem (z.getMem (z.getReg .x2 + 200) + 24) = z.getMem (z.getReg .x2 + 104) := by
  have m : v.getMem (z.getMem (z.getReg .x2 + 200) + 24) = _ :=
    h.mem_eq 0 (by decide) (by rv_eval []) rfl
  simp only [reduceMem, List.getElem_cons_zero, Sym.E.eval, Sym.BinOp.eval] at m
  refine m.trans ?_
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sym.StoreKind.merge, replaceByte, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.zeroExtend_eq_setWidth]
  interval_cases i <;> simp

theorem split56 {x a : Word} (h : x &&& 0x00ffffffffffffff = a &&& 0x00ffffffffffffff) :
    x = (a &&& 0x00ffffffffffffff) ||| (x &&& ~~~0x00ffffffffffffff) := by
  rw [← h]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
  cases x.getLsbD i <;> cases (0x00ffffffffffffff : Word).getLsbD i <;> simp [hi]

theorem b51c_w0 {z v : MachineState} {a b : Word} (h : b8000b51c.Holds z v)
    (h448 : z.getMem (z.getReg .x2 + 448) &&& 0x00ffffffffffffff = a &&& 0x00ffffffffffffff)
    (h96 : z.getMem (z.getReg .x2 + 96) = a >>> 56 ||| b <<< 8) :
    v.getMem (z.getMem (z.getReg .x2 + 200)) = a := by
  have m : v.getMem (z.getMem (z.getReg .x2 + 200)) = _ :=
    h.mem_eq 1 (by decide) (by rv_eval []) rfl
  simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
    Sym.BinOp.eval, Sym.UnOp.eval] at m
  rw [show z.getReg .x2 + 96#64 = z.getReg .x2 + 96 from rfl, h96,
    show z.getReg .x2 + 448#64 = z.getReg .x2 + 448 from rfl, split56 h448] at m
  refine m.trans ?_
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sym.StoreKind.merge, Sym.LoadKind.fromWord, replaceByte, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.zeroExtend_eq_setWidth, getLsbD_extractByte]
  interval_cases i <;> simp

theorem b51c_w1 {z v : MachineState} {a b c : Word} (h : b8000b51c.Holds z v)
    (h96 : z.getMem (z.getReg .x2 + 96) = a >>> 56 ||| b <<< 8)
    (h88 : z.getMem (z.getReg .x2 + 88) = b >>> 56 ||| c <<< 8) :
    v.getMem (z.getMem (z.getReg .x2 + 200) + 8) = b := by
  have m : v.getMem (z.getMem (z.getReg .x2 + 200) + 8) = _ :=
    h.mem_eq 3 (by decide) (by rv_eval []) rfl
  simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
    Sym.BinOp.eval] at m
  rw [show z.getReg .x2 + 96#64 = z.getReg .x2 + 96 from rfl, h96,
    show z.getReg .x2 + 88#64 = z.getReg .x2 + 88 from rfl, h88] at m
  refine m.trans ?_
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sym.StoreKind.merge, replaceByte, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.zeroExtend_eq_setWidth]
  interval_cases i <;> simp

theorem b51c_w2 {z v : MachineState} {b c : Word} (h : b8000b51c.Holds z v)
    (h88 : z.getMem (z.getReg .x2 + 88) = b >>> 56 ||| c <<< 8)
    (h120 : z.getMem (z.getReg .x2 + 120) = c >>> 56) :
    v.getMem (z.getMem (z.getReg .x2 + 200) + 16) = c := by
  have m : v.getMem (z.getMem (z.getReg .x2 + 200) + 16) = _ :=
    h.mem_eq 2 (by decide) (by rv_eval []) rfl
  simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
    Sym.BinOp.eval] at m
  rw [show z.getReg .x2 + 88#64 = z.getReg .x2 + 88 from rfl, h88,
    show z.getReg .x2 + 120#64 = z.getReg .x2 + 120 from rfl, h120] at m
  refine m.trans ?_
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sym.StoreKind.merge, replaceByte, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.zeroExtend_eq_setWidth]
  interval_cases i <;> simp

/-- **The back edge**, from `0x8000b51c` to the level's head: the next root `d` over the root. -/
theorem backEdge {s z : MachineState} {d : Digest} (hpre : VsoPre s) (hpc : z.pc = 0x8000b51c)
    (hsp : z.getReg .x2 = s.getReg .x2 - 1040)
    (hR : z.getMem (s.getReg .x2 - 840) = s.getReg .x11) (hNR : NR z (s.getReg .x2) d) :
    ∃ u, Reaches Image.code z u ∧ u.pc = 0x8000a190 ∧ digestAt u (s.getReg .x11) = d ∧
      DFrame z u (fun a ↦ Within a (s.getReg .x11) 32 ∨ Within a (s.getReg .x2 - 784) 8 ∨
        Within a (s.getReg .x2 - 824) 8) ∧
      (∀ q ∈ [Reg.x1, .x2, .x9, .x25, .x26], u.getReg q = z.getReg q) ∧
      u.getReg .x5 = z.getMem (s.getReg .x2 - 1008) ∧ u.getReg .x8 = 0xffffffffffffffff ∧
      u.getReg .x10 = z.getMem (s.getReg .x2 - 864) ∧ u.getReg .x17 = 8 ∧
      u.getReg .x22 = z.getMem (s.getReg .x2 - 896) ∧
      u.getReg .x23 = z.getMem (s.getReg .x2 - 808) ∧
      u.getReg .x27 = z.getMem (s.getReg .x2 - 816) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hRr : Region (s.getReg .x11) 32 := by
    rcases hpre.root.region with h0 | h0
    · cases h0
    · exact h0
  have hRb := Region.bounds hRr
  have hsm := stack_mapped hpre
  have hRm := hRr.1
  simp only [Mapped] at hRm
  have e200 : z.getMem (z.getReg .x2 + 200) = s.getReg .x11 := by
    rw [hsp, show s.getReg .x2 - 1040 + 200 = s.getReg .x2 - 840 by rv_eval [], hR]
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b8000b51c_spec hpc (by
    rv_eval [hsp, hR]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | addr_omega [hb, hRb, hrst]
      | exact validAccess_one (Or.inr (by addr_omega [hsm]))
      | (apply validAccess_one; rcases hRm with hm | hm
         · exact Or.inl (by addr_omega [hm])
         · exact Or.inr (by addr_omega [hm])))
  have k := b8000b51c_keeps h
  have X : DFrame z u fun a ↦ Within a (s.getReg .x11) 32 ∨ Within a (s.getReg .x2 - 784) 8 ∨
      Within a (s.getReg .x2 - 824) 8 :=
    (holds_dframe h).mono fun a ⟨k, hk, hw'⟩ ↦ by
      simp only [b8000b51c, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rv_eval [hsp, hR] at hw' <;> first
        | exact Or.inl (by addr_omega [hw', hRb])
        | exact Or.inr (Or.inl (by addr_omega [hw', hb]))
        | exact Or.inr (Or.inr (by addr_omega [hw', hb]))
  obtain ⟨n0, n1, n2, n3, n4⟩ := hNR
  have a448 : s.getReg .x2 - 592 = z.getReg .x2 + 448 := by rw [hsp]; rv_eval []
  have a96 : s.getReg .x2 - 944 = z.getReg .x2 + 96 := by rw [hsp]; rv_eval []
  have a88 : s.getReg .x2 - 952 = z.getReg .x2 + 88 := by rw [hsp]; rv_eval []
  have a120 : s.getReg .x2 - 920 = z.getReg .x2 + 120 := by rw [hsp]; rv_eval []
  have a104 : s.getReg .x2 - 936 = z.getReg .x2 + 104 := by rw [hsp]; rv_eval []
  rw [a448] at n0
  rw [a96] at n1
  rw [a88] at n2
  rw [a120] at n3
  rw [a104] at n4
  have w0 := b51c_w0 h n0 n1
  have w1 := b51c_w1 h n1 n2
  have w2 := b51c_w2 h n2 n3
  have w3 := b51c_w3 h
  rw [e200] at w0 w1 w2 w3
  rw [n4] at w3
  refine ⟨u, hr, b8000b51c_pc h, ?_, X, fun q hq ↦ k q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp),
    by rw [b8000b51c_x5 h, hsp]; rv_eval [], b8000b51c_x8 h,
    by rw [b8000b51c_x10 h, hsp]; rv_eval [], b8000b51c_x17 h,
    by rw [b8000b51c_x22 h, hsp]; rv_eval [], by rw [b8000b51c_x23 h, hsp]; rv_eval [],
    by rw [b8000b51c_x27 h, hsp]; rv_eval []⟩
  refine Vector.ext fun i hi ↦ ?_
  interval_cases i
  · exact UInt64.toBitVec_inj.mp ((dg0 u _).trans w0)
  · exact UInt64.toBitVec_inj.mp ((dg1 u _).trans w1)
  · exact UInt64.toBitVec_inj.mp ((dg2 u _).trans w2)
  · exact UInt64.toBitVec_inj.mp ((dg3 u _).trans w3)

end Rv64Verifier.Proofs.Pcs.Vso
