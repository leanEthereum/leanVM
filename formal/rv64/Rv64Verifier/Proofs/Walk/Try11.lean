import Rv64Verifier.Proofs.Walk.Body11

/-!
# `walk`: `try_allocate_in` into `sp + 1728` (R11)

`tryCall`: the call keeps `Keep11` and `kappas`; on `Ok` (tag `0`) the new buffer `T` lies above
`kappas`' buffer, below `NEXT`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

theorem tryCall (hTA : TryAllocZeroedSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s c : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat} {ks : List Nat}
    (hpre : WalkPre s) (hk : ks ≠ []) (K : Keep11 OI s c A k R Q B lo lo2) (kv : KapVec s c lo2 ks)
    (hpc : c.pc = 0x800049ac) (x10 : c.getReg .x10 = s.getReg .x2 - 928) {w : Nat} (hw : w ≤ 92)
    (x11 : c.getReg .x11 = BitVec.ofNat 64 w) (x13 : c.getReg .x13 = 8)
    (x14 : c.getReg .x14 = 8) (hw0 : 0 < w) :
    ∃ t, Reaches Image.code c t ∧ (Dead Image.code t ∨ (t.pc = returnAddress c ∧ Preserves c t ∧
      Keep11 OI s t A k R Q B lo lo2 ∧ KapVec s t lo2 ks ∧
      vecPtr t (s.getReg .x2 - 1344) = vecPtr c (s.getReg .x2 - 1344) ∧
      vecCap t (s.getReg .x2 - 1344) = vecCap c (s.getReg .x2 - 1344) ∧
      (t.getMem (s.getReg .x2 - 928) = 0 → t.getMem (s.getReg .x2 - 920) = BitVec.ofNat 64 w ∧
        (t.getMem (s.getReg .x2 - 912)).toNat % 8 = 0 ∧
        (vecPtr c (s.getReg .x2 - 1344)).toNat + 8 * (vecCap c (s.getReg .x2 - 1344)).toNat ≤
          (t.getMem (s.getReg .x2 - 912)).toNat ∧
        (t.getMem (s.getReg .x2 - 912)).toNat + 8 * w ≤ heapNext t ∧
        (c.getReg .x12 ≠ 0 → bytesAt t (t.getMem (s.getReg .x2 - 912)) (w * 8) =
          List.replicate (w * 8) 0)))) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := K.at11.base
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab hx
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have pre : TryAllocPre .x13 .x14 c := {
    heap := H.inv.heap
    out := by
      rw [x10]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩)
    align := by rw [x13]; decide
    size := by rw [x14]; decide
    stack := stk10 hpre H.inv (by decide) (by decide)
    outFree := by
      rw [x10]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by simp only [Apart]; addr_omega [hx, hb1]⟩
    outStack := by rw [x10, stackLo_callee H.inv]; simp only [Apart]; addr_omega [hb1] }
  obtain ⟨t, hr, ⟨hpct, hp, post, hz⟩ | hd⟩ := hTA c hpc pre
  swap
  · exact ⟨t, hr, Or.inl hd⟩
  have fr := post.frame.dframe
  rw [x10] at fr hz
  have ok := post.ok
  rw [x10, x11, x13, x14] at ok
  rw [x11, x14] at hz
  have hhc := H.inv.heap.hi
  have hht := post.heap.hi
  have hmono := post.mono
  have hl2 := K.lo2le
  simp only [heapEnd] at hhc hht
  have hW : ∀ a, (Within a (s.getReg .x2 - 928) 24 ∨ Within a (stackLo c tryAllocStack) tryAllocStack ∨
      Within a nextAddr 8 ∨ Fresh c t a) → W11 s lo2 t a := fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · simp only [Within] at ha
      refine Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1], ?_⟩
      simp only [hdrs, Within]; addr_omega [ha, hb1]
    · rw [stackLo_callee H.inv] at ha
      exact Or.inr (Or.inl (by simp only [Within, tryAllocStack] at ha ⊢; addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))
  have K' := K.keep hpre fr hW post.heap hmono (hp .x2 (by decide))
  obtain ⟨b1, b2, b3, b4⟩ := kv.bounds hk
  have hhdr : ∀ x, Within x (s.getReg .x2 - 1344) 24 → ¬ (Within x (s.getReg .x2 - 928) 24 ∨
      Within x (stackLo c tryAllocStack) tryAllocStack ∨ Within x nextAddr 8 ∨ Fresh c t x) :=
    fun x hx hw ↦ by
      rcases hw with h2 | h2 | h2 | h2
      · simp only [Within] at hx h2; addr_omega [hx, h2, hb1]
      · rw [stackLo_callee H.inv] at h2
        simp only [Within, tryAllocStack] at hx h2; addr_omega [hx, h2, hb1]
      · simp only [Within, nextAddr] at hx h2; addr_omega [hx, h2, hb1]
      · simp only [Fresh] at h2; simp only [Within] at hx; addr_omega [hx, h2, hb1, hhc, hht]
  have kv' := kv.keep hk fr hhdr
    (fun x hx hw ↦ by
      simp only [kapBuf, Within] at hx
      simp only [heapStart] at b2
      rcases hw with h2 | h2 | h2 | h2
      · simp only [Within] at h2; addr_omega [hx, h2, hb1, b2, b3, hhc]
      · rw [stackLo_callee H.inv] at h2
        simp only [Within, tryAllocStack] at h2
        addr_omega [hx, h2, hb1, b2, b3, hhc]
      · simp only [Within, nextAddr] at h2; addr_omega [hx, h2, b2, b3, hhc]
      · simp only [Fresh] at h2; omega)
    (by addr_omega [hb1]) H.inv.heap.hi hmono
  have g (o : Nat) (ho : o + 8 ≤ 24) : t.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) =
      c.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) :=
    fr.getMem_of (fun x hx ↦ hhdr x (by addr_omega [hx, ho, hb1])) (by addr_omega [ho, hb1])
  have hC : vecCap t (s.getReg .x2 - 1344) = vecCap c (s.getReg .x2 - 1344) := by
    simpa [vecCap] using g 0 (by decide)
  have hP : vecPtr t (s.getReg .x2 - 1344) = vecPtr c (s.getReg .x2 - 1344) := g 8 (by decide)
  have e8 : s.getReg .x2 - 928 + 8 = s.getReg .x2 - 920 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e16 : s.getReg .x2 - 928 + 16 = s.getReg .x2 - 912 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e8, e16] at ok
  rw [e16] at hz
  have hwN : (BitVec.ofNat 64 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
  have h8 : (8 : Word).toNat = 8 := rfl
  rw [hwN, h8] at ok hz
  refine ⟨t, hr, Or.inr ⟨hpct, hp, K', kv', hP, hC, fun h0 ↦ ?_⟩⟩
  obtain ⟨o1, o2⟩ := ok h0
  simp only [NewBuf] at o2
  refine ⟨o1, o2.1, ?_, ?_, fun h12 ↦ hz h12 h0⟩
  · rcases o2.2 with h0' | h0' <;> omega
  · rcases o2.2 with h0' | h0' <;> omega

end Rv64Verifier.Proofs.Walk
