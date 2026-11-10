import Rv64Verifier.Proofs.Walk.New
import Rv64Verifier.Proofs.Transcript.Openings
import Rv64Verifier.Proofs.Pcs.Contracts

/-!
# The proof's Merkle openings, from `walk`'s entry to `verify_stacked_opening`

`Transcript/Openings.lean` reads the openings through a pointer to the `Proof`, the transcript's;
at `walk`'s entry there is no transcript yet, so this file keys them on the `Proof`'s address
(`OpenFootA`, `OpenMappedA`, `OpeningsAtA`). `OpenPre`: what `walk` asks of them beyond `WalkPre`,
their buffers mapped and the doublewords they read missing what `walk` writes. `openKeep`: `walk`'s
frame keeps them; `openMem_vso`: they are in place as `verify_stacked_opening` asks (`OpenMem`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript

/-- `OpenFoot`, of the `Proof` at `a`. -/
def OpenFootA (s : MachineState) (a y : Word) : Prop :=
  Within y (vecPtr s (a + 24)) (24 * (vecLen s (a + 24)).toNat) ∨
    ∃ k < (vecLen s (a + 24)).toNat, PhaseFoot s (vecPtr s (a + 24) + BitVec.ofNat 64 (24 * k)) y

/-- `OpenMapped`, of the `Proof` at `a`. -/
structure OpenMappedA (s : MachineState) (a : Word) : Prop where
  buf : (vecLen s (a + 24)).toNat = 0 ∨
    Region (vecPtr s (a + 24)) (24 * (vecLen s (a + 24)).toNat)
  phases : ∀ k < (vecLen s (a + 24)).toNat,
    PhaseMapped s (vecPtr s (a + 24) + BitVec.ofNat 64 (24 * k))

/-- `OpeningsAt`, of the `Proof` at `a`. -/
structure OpeningsAtA (s : MachineState) (a : Word) (ops : List (List Opening)) : Prop where
  len : (vecLen s (a + 24)).toNat = ops.length
  phases : ∀ k (h : k < ops.length), PhaseAt s (vecPtr s (a + 24) + BitVec.ofNat 64 (24 * k)) ops[k]

/-- What the openings of the `Proof` at `a` read is only read by `walk`: it misses the result, the
stack, `NEXT`, the free heap and the low eight bytes. -/
def OpenRO (s : MachineState) (a : Word) : Prop :=
  ∀ y, OpenFootA s a y → ¬ (Within y (s.getReg .x10) 80 ∨ Within y (stackLo s walkStack) walkStack ∨
    Within y nextAddr 8 ∨ (heapNext s ≤ y.toNat ∧ y.toNat < heapEnd) ∨ y.toNat < 8)

/-- What `walk` asks of the proof's openings at its entry. -/
structure OpenPre (s : MachineState) : Prop where
  mapped : OpenMappedA s (s.getReg .x13)
  ro : OpenRO s (s.getReg .x13)

/-- `walk`'s contract, the openings in place. -/
abbrev WalkSpecO (OpeningsIn : MachineState → Word → List (List Opening) → Prop) : Prop :=
  FunSpec Image.code 0x80000ef8 (fun s ↦ WalkPre s ∧ OpenPre s) (WalkPost OpeningsIn)

section
variable {s t : MachineState}

theorem OpenMappedA.toP {p : Word} (h : OpenMappedA s (proofAt s p)) : OpenMapped s p :=
  ⟨h.buf, h.phases⟩

theorem OpeningsAtA.toP {p : Word} {T : TState} (h : OpeningsAtA s (proofAt s p) T.proof.openings) :
    OpeningsAt s p T :=
  ⟨h.len, h.phases⟩

theorem OpenMappedA.fb {a : Word} (h : OpenMappedA s a) :
    (vecPtr s (a + 24)).toNat + 24 * (vecLen s (a + 24)).toNat ≤ 2 ^ 64 := by
  rcases h.buf with h0 | ⟨hm, -⟩
  · have := (vecPtr s (a + 24)).isLt
    omega
  · simp only [Mapped] at hm
    omega

/-- A frame missing the `Proof`'s 48 bytes and what its openings read keeps them. -/
theorem DFrame.openA {w : Word → Prop} (h : DFrame s t w) {a : Word} (hq : Misses w a 48)
    (hqn : a.toNat + 48 ≤ 2 ^ 64) (hf : ∀ y, OpenFootA s a y → ¬ w y) (hm : OpenMappedA s a) :
    (∀ ops, OpeningsAtA s a ops → OpeningsAtA t a ops) ∧ (∀ y, OpenFootA t a y ↔ OpenFootA s a y) ∧
      OpenMappedA t a := by
  have e0 : vecPtr t (a + 24) = vecPtr s (a + 24) :=
    h _ (hq.bytes (by addr_omega [hqn]) (by addr_omega [hqn]) hqn)
  have e1 : vecLen t (a + 24) = vecLen s (a + 24) :=
    h _ (hq.bytes (by addr_omega [hqn]) (by addr_omega [hqn]) hqn)
  have fb := hm.fb
  have phase (k : Nat) (hk : k < (vecLen s (a + 24)).toNat) :=
    h.phase (a := vecPtr s (a + 24) + BitVec.ofNat 64 (24 * k))
      (fun y hy ↦ hf y (Or.inl (by addr_omega [hy, fb, hk]))) (by addr_omega [fb, hk])
      (fun y hy ↦ hf y (Or.inr ⟨k, hk, hy⟩)) (hm.phases k hk).fits
  refine ⟨fun ops hT ↦ ⟨by rw [e1]; exact hT.len, fun k hk ↦ ?_⟩, fun y ↦ ?_, ⟨?_, fun k hk ↦ ?_⟩⟩
  · have hk' : k < (vecLen s (a + 24)).toNat := by rw [hT.len]; exact hk
    rw [e0]
    exact (phase k hk').1 _ (hT.phases k hk)
  · simp only [OpenFootA, e0, e1]
    refine or_congr Iff.rfl (exists_congr fun k ↦ ?_)
    exact ⟨fun ⟨hk, hy⟩ ↦ ⟨hk, ((phase k hk).2.1 y).mp hy⟩,
      fun ⟨hk, hy⟩ ↦ ⟨hk, ((phase k hk).2.1 y).mpr hy⟩⟩
  · rw [e0, e1]; exact hm.buf
  · rw [e1] at hk
    rw [e0]
    exact h.phaseMapped (fun y hy ↦ hf y (Or.inl (by addr_omega [hy, fb, hk])))
      (by addr_omega [fb, hk]) (fun y hy ↦ hf y (Or.inr ⟨k, hk, hy⟩)) ((hm.phases k hk).fits)
      (hm.phases k hk)

/-- `walk`'s frame keeps the openings. -/
theorem openKeep (hpre : WalkPre s) (hO : OpenPre s) (I : Inv s t) :
    (∀ ops, OpeningsAtA s (s.getReg .x13) ops → OpeningsAtA t (s.getReg .x13) ops) ∧
      (∀ y, OpenFootA t (s.getReg .x13) y ↔ OpenFootA s (s.getReg .x13) y) ∧
      OpenMappedA t (s.getReg .x13) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hR := hpre.proof
  have hRb := hR.1
  simp only [Mapped] at hRb
  obtain ⟨⟨o1, o2⟩, o3, o4, -⟩ := hpre.proofRO
  have hh := I.heap.hi
  have hm := I.mono
  rw [stackLo_eq] at o3
  refine DFrame.openA (lframe_d I.frame) (fun y hy hw ↦ ?_) (by omega) (fun y hy hw ↦ hO.ro y hy ?_)
    hO.mapped
  · simp only [Within] at hy
    rcases hw with ((hw | hw | hw | hw) | hw)
    · addr_omega [hy, hw, o4, hRb]
    · rw [stackLo_eq] at hw; addr_omega [hy, hw, o3, hRb, hb1]
    · addr_omega [hy, hw, o2, hRb]
    · simp only [Fresh, heapNext, heapEnd] at hw hh hm o1
      addr_omega [hy, hw, o1, hRb, hh, hm]
    · addr_omega [hy, hw, hRb]
  · simp only [WalkW, Fresh] at hw
    rcases hw with ((hw | hw | hw | hw) | hw)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hw.1, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hw)))

/-- The openings in place at `verify_stacked_opening`'s call: `a0` the transcript, whose proof
pointer is `walk`'s `a3`, `a1` the root at `S - 1800`. -/
theorem openMem_vso (hpre : WalkPre s) (hO : OpenPre s) (I : Inv s t)
    (hptr : t.getMem (tp s) = s.getReg .x13) (hx10 : t.getReg .x10 = tp s)
    (hx11 : t.getReg .x11 = s.getReg .x2 - 1800) :
    OpenMem t (t.getReg .x10) fun y ↦ (heapNext t ≤ y.toNat ∧ y.toNat < heapEnd) ∨
      Within y nextAddr 8 ∨ Within y (stackLo t PcsContracts.vsoStack) PcsContracts.vsoStack ∨
        Within y (t.getReg .x10 + 8) 352 ∨ Within y (t.getReg .x11) 32 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨-, hfoot, hmap⟩ := openKeep hpre hO I
  have hp : proofAt t (tp s) = s.getReg .x13 := hptr
  have hk : PcsContracts.vsoStack ≤ 8736 := by decide
  have hm := I.mono
  rw [hx10, hx11, stackLo_callee I]
  refine ⟨by rw [← hp] at hmap; exact hmap.toP, fun y hy hw ↦ ?_⟩
  have hy' : OpenFootA s (s.getReg .x13) y := (hfoot y).mp (by rw [← hp]; exact hy)
  refine hO.ro y hy' ?_
  rw [stackLo_eq]
  rcases hw with hw | hw | hw | hw | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hw.2⟩)))
  · exact Or.inr (Or.inr (Or.inl hw))
  · simp only [Within] at hw ⊢; exact Or.inr (Or.inl (by addr_omega [hw, hb1, hk]))
  · simp only [Within, tp] at hw ⊢; exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
  · simp only [Within] at hw ⊢; exact Or.inr (Or.inl (by addr_omega [hw, hb1]))

end

end Rv64Verifier.Proofs.Walk
