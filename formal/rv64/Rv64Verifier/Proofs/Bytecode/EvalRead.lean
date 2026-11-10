import Rv64Verifier.Proofs.Bytecode.EvalEnv

/-!
# `Bytecode::evaluate`: reading inside the loop

Through `LoopMem`: a doubleword (`LoopMem.bc`) or a halfword (`LoopMem.bcHalf`) of a part of the
`Bytecode`, as at the entry; an element of the eq tables (`LoopMem.low`, `LoopMem.high`), as
`eq_kernel` computed it; a slot of the frame the loop does not write (`LoopMem.slot`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts

variable {e : Env} {t : MachineState}

/-- A doubleword of a `Clear` part. -/
theorem LoopMem.bc (he : EnvOk e) (hm : LoopMem e t) {lo : Word} {n : Nat}
    (hc : Clear e.s lo n evalStack (e.s.getReg .x10)) (hmap : Mapped lo n) {a : Word}
    (h1 : lo.toNat ≤ a.toNat) (h2 : a.toNat + 8 ≤ lo.toNat + n) : t.getMem a = e.s.getMem a := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hh := he.heapL.hi
  have hn := he.pre.stack.next
  simp only [heapNext, heapEnd] at hbk hh
  rw [hm a (by addr_omega [hc, hmap, h1, h2, hsp, hbk, hh])]
  exact he.frame a fun i hi hw ↦ by
    simp only [Fresh, heapNext] at hw
    addr_omega [hw, hc, hmap, h1, h2, hi, hsp, hh, hn]

/-- A halfword of a `Clear` part whose doublewords are `Clear`. -/
theorem LoopMem.bcHalf (he : EnvOk e) (hm : LoopMem e t) {lo : Word} {n : Nat}
    (hc : Clear e.s lo n evalStack (e.s.getReg .x10))
    (hd : ClearDw e.s lo n evalStack (e.s.getReg .x10)) (hmap : Mapped lo n) {a : Word}
    (h1 : lo.toNat ≤ a.toNat) (h2 : a.toNat + 2 ≤ lo.toNat + n) :
    t.getHalfword a = e.s.getHalfword a := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hh := he.heapL.hi
  have hn := he.pre.stack.next
  simp only [heapNext, heapEnd] at hbk hh
  have hdw : t.getMem (alignToDword a) = e.tL.getMem (alignToDword a) := by
    apply hm
    intro hs
    have hal := toNat_alignDown a
    simp only [alignToDword] at hs
    simp only [Scratch, Within, stackLo, fp, evalStack, eqKernelStack, mulStack] at hs
    addr_omega [hs, hal, hc, hmap, h1, h2, hsp, hbk, hh]
  have hal := toNat_alignDown a
  have hcd := hd (alignToDword a) (by simp only [alignToDword]; omega)
    (by simp only [alignToDword]; omega) (by simp only [alignToDword]; omega) (by omega)
  have hdw' : e.tL.getMem (alignToDword a) = e.s.getMem (alignToDword a) :=
    he.frame _ fun i hi hw ↦ by
      simp only [alignToDword] at hcd hw
      simp only [Fresh, heapNext] at hw
      addr_omega [hw, hcd, hal, hi, hsp, hh, hn]
  simp only [MachineState.getHalfword, hdw, hdw']

/-- An element of the low eq table. -/
theorem LoopMem.low (he : EnvOk e) (hm : LoopMem e t) {p : Nat} (hp : p < 2 ^ e.m) :
    Model.limbs (e.lowW.getD p 0) = (t.getMem (e.low + BitVec.ofNat 64 (24 * p)),
      t.getMem (e.low + BitVec.ofNat 64 (24 * p) + 8),
      t.getMem (e.low + BitVec.ofNat 64 (24 * p) + 16)) := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hl := he.lowIn
  have hh := he.heapL.hi
  have hlb := he.lowBk
  simp only [heapNext, heapEnd] at hbk hh hl
  have hv := he.lowVals
  have hlen : p < (eListAt e.tL e.low (2 ^ e.m)).length := by rw [eListAt_length]; exact hp
  rw [← hv, List.getD_eq_getElem _ _ hlen, eListAt_getElem, limbs_eAt,
    hm _ (by addr_omega [hp, hsp, hbk, hh, hl, hlb]), hm _ (by addr_omega [hp, hsp, hbk, hh, hl, hlb]),
    hm _ (by addr_omega [hp, hsp, hbk, hh, hl, hlb])]

/-- An element of the high eq table. -/
theorem LoopMem.high (he : EnvOk e) (hm : LoopMem e t) {p : Nat} (hp : p < 2 ^ (e.n - e.m)) :
    eAt t (e.high + BitVec.ofNat 64 (24 * p)) = e.highW.getD p 0 := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hl := he.highIn
  have hh := he.heapL.hi
  have hlb := he.highBk
  simp only [heapNext, heapEnd] at hbk hh hl
  have hv := he.highVals
  have hlen : p < (eListAt e.tL e.high (2 ^ (e.n - e.m))).length := by rw [eListAt_length]; exact hp
  rw [← hv, List.getD_eq_getElem _ _ hlen, eListAt_getElem]
  unfold eAt
  rw [hm _ (by addr_omega [hp, hsp, hbk, hh, hl, hlb]), hm _ (by addr_omega [hp, hsp, hbk, hh, hl, hlb]),
    hm _ (by addr_omega [hp, hsp, hbk, hh, hl, hlb])]

/-- A slot of the frame outside the scratch, `c` bytes below the entry's `sp`. -/
theorem LoopMem.slot (he : EnvOk e) (hm : LoopMem e t) {c : Word}
    (hk : (8 ≤ c.toNat ∧ c.toNat ≤ 104) ∨ (1800 ≤ c.toNat ∧ c.toNat ≤ 1840) ∨
      (1904 ≤ c.toNat ∧ c.toNat ≤ 1960) := by decide) :
    t.getMem (e.s.getReg .x2 - c) = e.tL.getMem (e.s.getReg .x2 - c) := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hbk hh
  exact hm _ (by addr_omega [hk, hsp, hbk, hh])

end Rv64Verifier.Proofs.Bytecode.Eval
