import Rv64Verifier.Proofs.Walk.R9A

/-!
# `walk`: `tables()`, one table's copy (R9)

`memcpy(Bb + 80 n, slot, 72)` of the `n`-th table (`cpyC`) and the block storing the `n`-th opcode
(`opC`) keep `M8` and grow the copies made (`Cp`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

set_option maxRecDepth 8192 in
/-- `memcpy(Bb + 80 n, o, 72)`, `o` the slot of the `n`-th table. -/
theorem cpyC (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o : Word} {n : Nat}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (c : Cp u B W Bb n n) (hn : n < 6)
    (he : (o, tl n) ∈ L) (hpc : u.pc = 0x800126e4)
    (x10 : u.getReg .x10 = Bb + BitVec.ofNat 64 (80 * n)) (x11 : u.getReg .x11 = o)
    (x12 : u.getReg .x12 = 72) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W L ∧ Cp t B W Bb (n + 1) n ∧ heapNext t = heapNext u) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  obtain ⟨⟨o1, o2, o3⟩, T, hd⟩ := h.tabs _ he
  obtain ⟨b1, b2, b3, b4⟩ := h.bb
  have I := h.m.inv
  have hu := I.heap.hi
  obtain ⟨-, q2, q3, -⟩ := h.m.bufQ
  have hs := hpre.heap.lo
  simp only [heapEnd, heapStart] at hu hs
  have hBb : 0x20000000 ≤ Bb.toNat := by omega
  have hbn := bb_off0 (Bb := Bb) (i := n) (by omega) (by omega)
  have h72 : (u.getReg .x12).toNat = 72 := by rw [x12]; rfl
  have hmc : MemcpyPre u := {
    dst := by rw [x10, h72]; simp only [Mapped]; left; omega
    src := by rw [x11, h72]; addr_omega [hb1, hb2, o1, o2]
    apart := by rw [x10, x11, h72]; simp only [Apart]; right; right; left; addr_omega [hb1, o1, hbn, hu, b3, b4, hn]
    stack := calleeStack hpre I (by decide) (by decide)
    dstStack := by
      rw [x10, h72, stackLo_callee I]; simp only [Apart, memcpyStack]; right; right; left
      addr_omega [hb1, hbn, hu, b3, b4, hn]
    srcStack := by rw [x11, h72, stackLo_callee I]; addr_omega [hb1, o1] }
  obtain ⟨t, r, ⟨pc, hp, post⟩ | d⟩ := hMC u hpc hmc
  swap
  · exact ⟨t, r, Or.inr d⟩
  have by₁ := post.bytes
  rw [x10, x11, h72] at by₁
  have fr := post.frame.dframe
  rw [x10, h72] at fr
  have notW : ∀ x : Word, x.toNat < heapNext u → ¬ Within x (Bb + BitVec.ofNat 64 (80 * n)) 72 →
      ¬ (Within x (Bb + BitVec.ofNat 64 (80 * n)) 72 ∨ Within x (stackLo u memcpyStack) memcpyStack) :=
    fun x hx hx' hw ↦ by
      rcases hw with hw | hw
      · exact hx' hw
      · rw [stackLo_callee I] at hw; simp only [Within, memcpyStack] at hw
        addr_omega [hw, hx, hb1, hu]
  have hN : heapNext t = heapNext u := by
    simp only [heapNext]
    rw [fr _ (fun x hx hw ↦ by
      simp only [Within, nextAddr] at hx
      rcases hw with hw | hw
      · simp only [Within] at hw; addr_omega [hx, hw, hbn, hu, b3, b4, hn]
      · rw [stackLo_callee I] at hw; simp only [Within, memcpyStack] at hw; addr_omega [hx, hw, hb1])
      (by decide)]
  have hv : HeapOk t := ⟨hN ▸ I.heap.lo, hN ▸ I.heap.hi⟩
  have M := h.stepBb hpre fr (m := memcpyStack) (fun a ha ↦ ha.imp (fun ha ↦ by
    simp only [Within] at ha ⊢; omega) id) (by decide) hv hN.ge (hp.reg .x2)
  have T' := T.moveB fr (fun j hj ↦ getMem_eq_of_bytesAt by₁ (by rw [hbn]; omega) o3 (by omega) (by omega))
    (fun x hx ↦ notW x (by have := (hd x hx).2.1; omega) fun hw ↦ (hd x hx).2.2 (by
      simp only [Within] at hw ⊢; omega))
    (fun x hx hd' ↦ (hd x hd').2.2 (by simp only [Within] at hx ⊢; omega)) (by omega) I.heap hN.ge
  have c' := c.frame fr (by omega) (by omega) (fun a ha ↦ by
      rcases ha with ha | ha
      · simp only [Within] at ha; left; omega
      · right; rw [stackLo_callee I] at ha; simp only [Within, memcpyStack] at ha
        simp only [heapEnd]; addr_omega [ha, hb1])
    (by simp only [heapEnd]; omega) (by simp only [heapEnd]; omega) I.heap hN.ge
  refine ⟨t, r, Or.inl ⟨pc, hp, M, ⟨fun i hi ↦ ?_, c'.op⟩, hN⟩⟩
  by_cases hin : i < n
  · exact c'.tab i hin
  · obtain rfl : i = n := by omega
    exact ⟨T'.1, fun x hx ↦ hd x (by rw [← T'.2]; exact hx)⟩

/-- A block storing the `n`-th opcode at `Bb + 80 n + 72`. -/
theorem opC {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {n : Nat}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (c : Cp u B W Bb (n + 1) n) (hn : n < 5)
    (fr : Rv64Verifier.Layout.DFrame u v (Within · (Bb + BitVec.ofNat 64 (80 * n + 72)) 8))
    (hval : v.getMem (Bb + BitVec.ofNat 64 (80 * n + 72)) = BitVec.ofNat 64 n)
    (sp : v.getReg .x2 = u.getReg .x2) :
    M8 OI s v A k R Q B Bb W L ∧ Cp v B W Bb (n + 1) (n + 1) ∧ heapNext v = heapNext u := by
  obtain ⟨-, b2, b3, b4⟩ := h.bb
  have I := h.m.inv
  have hu := I.heap.hi
  obtain ⟨-, q2, q3, -⟩ := h.m.bufQ
  have hs := hpre.heap.lo
  simp only [heapEnd, heapStart] at hu hs
  have hbn := bb_off (Bb := Bb) (i := n) (by omega) 72 (by omega)
  have hN : heapNext v = heapNext u := by
    simp only [heapNext]
    rw [fr _ (fun x hx hw ↦ by
      simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, hbn, hu, b3, b4, hn]) (by decide)]
  have hv : HeapOk v := ⟨hN ▸ I.heap.lo, hN ▸ I.heap.hi⟩
  have M := h.stepBb hpre fr (m := 0) (fun a ha ↦ Or.inl (by simp only [Within] at ha ⊢; omega))
    (by decide) hv hN.ge sp
  have c' := c.frame fr (by omega) (by omega) (fun a ha ↦ by simp only [Within] at ha; left; omega)
    (by simp only [heapEnd]; omega) (by simp only [heapEnd]; omega) I.heap hN.ge
  refine ⟨M, ⟨c'.tab, fun i hi ↦ ?_⟩, hN⟩
  by_cases hin : i < n
  · exact c'.op i hin
  · obtain rfl : i = n := by omega
    exact hval

end Rv64Verifier.Proofs.Walk
