import Rv64Verifier.Proofs.Walk.R19C

/-!
# `walk` R19, the public input's claims: one claim, the clone and the allocation

`IW`: the frame bytes an iteration of the claims loop writes before the claim's store. `allocW`:
the allocator as a step. `r19pA`: from the head `0x80003b80` through `0x80003b80` (the limb's
words, the column), `clone` of the point into `S - 1488`, `0x80003bbc` (the challenge at
`S - 416`) and `alloc(8, 48)` to `0x80003bdc` (`AtA`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What an iteration writes in the frame before its claim's store. -/
@[rv_addr] def IW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2504) 16 ∨ Within a (s.getReg .x2 - 2464) 16 ∨
  Within a (s.getReg .x2 - 1488) 24 ∨ Within a (s.getReg .x2 - 1344) 32 ∨
  Within a (s.getReg .x2 - 512) 24 ∨ Within a (s.getReg .x2 - 416) 24 ∨
  Within a (s.getReg .x2 - 224) 24

theorem IW_ok {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {a : Word}
    (ha : IW s a) : InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368 ∧
      ¬ Within a (s.getReg .x2 - 1632) 16 ∧ ¬ Within a (s.getReg .x2 - 2616) 16 := by
  rcases ha with ha | ha | ha | ha | ha | ha | ha
  · exact range_okT hpre h (c := 2504) (k := 2504) (n := 16) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha
  · exact range_okT hpre h (c := 2464) (k := 2464) (n := 16) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha
  · exact range_okT hpre h (c := 1488) (k := 1488) (n := 24) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha
  · exact range_okT hpre h (c := 1344) (k := 1344) (n := 32) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha
  · exact range_okT hpre h (c := 512) (k := 512) (n := 24) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha
  · exact range_okT hpre h (c := 416) (k := 416) (n := 24) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha
  · exact range_okT hpre h (c := 224) (k := 224) (n := 24) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) ha

/-- A frame slot `S - k` an iteration does not write keeps its value. -/
theorem IW_slot {s u v : MachineState} (hpre : WalkPre s) (st : StepW s u v (IW s) False)
    {k : Nat} (hk : 112 ≤ k ∧ k ≤ 2648)
    (hk1 : k ≤ 200 ∨ (232 ≤ k ∧ k ≤ 392) ∨ (424 ≤ k ∧ k ≤ 488) ∨ (520 ≤ k ∧ k ≤ 1312) ∨
      (1352 ≤ k ∧ k ≤ 1464) ∨ (1496 ≤ k ∧ k ≤ 2448) ∨ (2472 ≤ k ∧ k ≤ 2488) ∨ 2512 ≤ k) :
    v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine st.getF hpre (by addr_omega [hb1, hk]) (fun i hi hw ↦ ?_) (fun hf ↦ hf.elim)
  simp only [IW, Within] at hw
  have k1 := hk.1
  have k2 := hk.2
  rcases hw with hw | hw | hw | hw | hw | hw | hw <;>
    rcases hk1 with q | ⟨q, q'⟩ | ⟨q, q'⟩ | ⟨q, q'⟩ | ⟨q, q'⟩ | ⟨q, q'⟩ | ⟨q, q'⟩ | q <;>
    first | addr_omega [hw, hi, hb1, q, k1, k2] | addr_omega [hw, hi, hb1, q, q', k1, k2]

/-- `alloc`, as a step writing `NEXT` alone. -/
theorem allocW (hA : AllocSpec) {s u u' : MachineState} (I : Inv s u)
    (hr : Reaches Image.code u' u) (hpc : u.pc = 0x80000284) (h10 : u.getReg .x10 = 8) :
    ∃ v, Reaches Image.code u' v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepW s u v (fun _ ↦ False) False ∧ (v.getReg .x10).toNat % 8 = 0 ∧
      heapNext u ≤ (v.getReg .x10).toNat ∧
      heapNext v = (v.getReg .x10).toNat + (u.getReg .x11).toNat) ∨ Dead Image.code v) := by
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hA.call hr hpc ⟨I.heap, by rw [h10]; decide⟩
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have al := post.aligned
  rw [h10] at al
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, ⟨fun a ha ↦ post.mem a fun he ↦ ha 0 (by decide) ?_,
    post.heap, by have := post.next; have := post.above; omega, hp .x2 (by decide)⟩, al, post.above,
    post.next⟩⟩
  subst he
  refine Or.inr (Or.inr (Or.inl ?_))
  simp only [Within, add_ofNat_zero]
  have : nextAddr.toNat = 2684358448 := rfl
  omega

/-- At `0x80003bdc`, past the clone and the allocation. -/
structure AtA (s u x : MachineState) (i : Nat) (c : E) (n : Nat) (L Q : Word) : Prop where
  st : StepW s u x (IW s) False
  pc : x.pc = 0x80003bdc
  qa : Q.toNat % 8 = 0
  q1 : (vecPtr x (s.getReg .x2 - 1488)).toNat + 24 * n ≤ Q.toNat
  q2 : Q.toNat + 48 ≤ heapNext x
  x10 : x.getReg .x10 = Q
  cpa : (vecPtr x (s.getReg .x2 - 1488)).toNat % 8 = 0
  cp1 : heapNext u ≤ (vecPtr x (s.getReg .x2 - 1488)).toNat
  cl : vecLen x (s.getReg .x2 - 1488) = BitVec.ofNat 64 n
  ce : vecEs x (s.getReg .x2 - 1488) = c :: List.replicate (n - 1) 0
  s192 : x.getMem (s.getReg .x2 - 2464) = BitVec.ofNat 64 i
  x18 : x.getReg .x18 = pubHi s i
  x19 : x.getReg .x19 = pubLo s i
  x23 : x.getReg .x23 = BitVec.ofNat 64 i
  x20 : x.getReg .x20 = (Model.limbs c).1
  x21 : x.getReg .x21 = (Model.limbs c).2.1
  x27 : x.getReg .x27 = (Model.limbs c).2.2
  x24 : x.getReg .x24 = s.getReg .x2 - 512
  x25 : x.getReg .x25 = L + BitVec.ofNat 64 i
  r0 : x.getMem (s.getReg .x2 - 416) = (Model.limbs c).1
  r1 : x.getMem (s.getReg .x2 - 408) = (Model.limbs c).2.1
  r2 : x.getMem (s.getReg .x2 - 400) = (Model.limbs c).2.2

end Rv64Verifier.Proofs.Walk
