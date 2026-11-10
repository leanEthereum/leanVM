import Rv64Verifier.Proofs.Pcs.VsoGlueBase
import Rv64Verifier.Proofs.Field.Contracts

/-!
# `verify_stacked_opening`'s final level: the subspace roots, their frame

`RPF s v w t`: the loop's frame at `t` from `v`, and everything `t` wrote since the piece's start `w`
among the loop's writes from `w`'s `NEXT` on (so a buffer allocated by the piece may be written).
`RLW`: what the roots' loop writes once set up; `RSL`: the slots the piece keeps for its successors.
`kListAt` helpers and the model's `subspace_roots` step.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The piece's frame -/

/-- The loop's frame at `t` from `v`, and the piece's writes from `w` on. -/
structure RPF (s v w t : MachineState) : Prop where
  gs : GS s v t
  fr : DFrame w t (GLW s (heapNext w) (t.getMem nextAddr))
  vw : heapNext v ≤ heapNext w
  wt : heapNext w ≤ heapNext t

theorem RPF.init {s v w : MachineState} (h : GS s v w) : RPF s v w w :=
  ⟨h, DFrame.refl _ _, h.mono, Nat.le_refl _⟩

section
variable {s v w t : MachineState}

/-- One more step whose writes are the loop's from `w`'s `NEXT` on. -/
theorem RPF.step (hpre : VsoPre s) (h : RPF s v w t) {t' : MachineState} {X : Word → Prop}
    (hX : DFrame t t' X) (hXs : ∀ a, X a → GLW s (heapNext w) (t'.getMem nextAddr) a)
    (hheap : HeapOk t') (hmono : heapNext t ≤ heapNext t') (hsp : t'.getReg .x2 = t.getReg .x2) :
    RPF s v w t' := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsu := h.gs.sv
  have hvw := h.vw
  have hhi := hheap.hi
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  refine ⟨⟨Inv.step' hpre h.gs.inv hX (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hmono hhi hsp,
    (h.gs.fr.mono fun a ha ↦ ha.mono (Nat.le_refl _) hmono).trans hX
      (fun a ha ↦ (hXs a ha).mono hvw (Nat.le_refl _)), hheap, Nat.le_trans h.gs.mono hmono,
    hsp.trans h.gs.sp, h.gs.sv⟩,
    (h.fr.mono fun a ha ↦ ha.mono (Nat.le_refl _) hmono).trans hX hXs, hvw,
    Nat.le_trans h.wt hmono⟩
  · rcases hXs a ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))
  · simp only [heapEnd] at hhi
    rcases hXs a ha with ha | ha | ha | ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · addr_omega [ha.2, hb, hhi, hab]

/-- A step writing only the loop's stack slots: `NEXT` kept. -/
theorem RPF.stepS (hpre : VsoPre s) (h : RPF s v w t) {t' : MachineState} {X : Word → Prop}
    (hX : DFrame t t' X) (hXs : ∀ a, X a → GLS s a) (hsp : t'.getReg .x2 = t.getReg .x2) :
    RPF s v w t' ∧ t'.getMem nextAddr = t.getMem nextAddr := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have nx : t'.getMem nextAddr = t.getMem nextAddr := hX _ fun i hi hw ↦ by
    rcases hXs _ hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hnx]
  have hn : heapNext t' = heapNext t := by simp only [heapNext, nx]
  exact ⟨h.step hpre hX (fun a ha ↦ (hXs a ha).gw (heapNext w) (t'.getMem nextAddr))
    ⟨by rw [hn]; exact h.gs.heap.lo, by rw [hn]; exact h.gs.heap.hi⟩ (by rw [hn]) hsp, nx⟩

/-- A step writing no memory. -/
theorem RPF.same (hpre : VsoPre s) (h : RPF s v w t) {t' : MachineState}
    (hm : ∀ a, t'.getMem a = t.getMem a) (hsp : t'.getReg .x2 = t.getReg .x2) : RPF s v w t' :=
  (h.stepS hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) hsp).1

theorem RPF.inv (h : RPF s v w t) : InvR s t (t.getMem nextAddr) := h.gs.inv
theorem RPF.sp (h : RPF s v w t) : t.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := h.gs.sp
theorem RPF.heap (h : RPF s v w t) : HeapOk t := h.gs.heap
theorem RPF.sw (h : RPF s v w t) : heapNext s ≤ heapNext w := Nat.le_trans h.gs.sv h.vw

/-- A heap word allocated from `w`'s `NEXT` on, in the piece's writes. -/
theorem glw_heap {lo : ℕ} {hi a : Word} (h1 : lo ≤ a.toNat) (h2 : a.toNat < hi.toNat) :
    GLW s lo hi a :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))

end

/-! ## What the roots' loop writes -/

/-- The roots' loop's writes: the counter at `S - 792`, the roots' `Vec` at `S - 128`, the callees'
stacks, `NEXT`, the heap since the entry. -/
def RLW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 792) 8 ∨ Within a (s.getReg .x2 - 128) 24 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < heapEnd)

/-- The slots the piece hands on, from the piece's start `w` (claim at `a`, layer at `L`). -/
structure RSL (s w t : MachineState) (a : Word) (n : ℕ) (L : Word) : Prop where
  m856 : t.getMem (s.getReg .x2 - 856) = w.getMem (a + 8)
  m824 : t.getMem (s.getReg .x2 - 824) = w.getMem (a + 32)
  m816 : t.getMem (s.getReg .x2 - 816) = w.getReg .x18
  m808 : t.getMem (s.getReg .x2 - 808) = w.getReg .x9
  m800 : t.getMem (s.getReg .x2 - 800) = w.getMem (a + 40)
  m888 : t.getMem (s.getReg .x2 - 888) = w.getMem (a + 16)
  m784 : t.getMem (s.getReg .x2 - 784) = L
  m840 : t.getMem (s.getReg .x2 - 840) = L + 8
  m832 : t.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 n
  keep : ∀ y, GK s y → t.getMem y = w.getMem y

theorem RSL.keep' {s w t t' : MachineState} {a : Word} {n : ℕ} {L : Word} (hpre : VsoPre s)
    (h : RSL s w t a n L) {X : Word → Prop} (hX : DFrame t t' X) (hXs : ∀ y, X y → RLW s y) :
    RSL s w t' a n L := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have k (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 792).toNat ∨
      (s.getReg .x2 - 784).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 128).toNat ∨
      (s.getReg .x2 - 104).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t'.getMem y = t.getMem y :=
    hX y fun i hi hw ↦ by
      rcases hXs _ hw with hw | hw | hw | hw | hw <;> rcases hy with hy | hy | hy
      all_goals first
        | addr_omega [hw, hi, hy, hb]
        | addr_omega [hw, hi, hy, hb, hnx, hab]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy ↦ ?_⟩
  · rw [k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m856
  · rw [k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m824
  · rw [k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m816
  · rw [k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m808
  · rw [k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m800
  · rw [k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m888
  · rw [k _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))]; exact h.m784
  · rw [k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m840
  · rw [k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m832
  · rw [← h.keep y hy]
    simp only [GK] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact k _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)
      | exact k _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))

/-! ## `K` lists -/

theorem kListAt_length (t : MachineState) (p : Word) (n : ℕ) : (kListAt t p n).length = n := by
  simp [kListAt]

theorem kListAt_succ (t : MachineState) (p : Word) (n : ℕ) :
    kListAt t p (n + 1) = kListAt t p n ++ [BF64.ofBitVec (t.getMem (p + BitVec.ofNat 64 (8 * n)))] := by
  simp [kListAt, List.range_succ]

theorem kListAt_congr {t t' : MachineState} {p p' : Word} {n : ℕ}
    (h : ∀ i < n, t.getMem (p + BitVec.ofNat 64 (8 * i)) = t'.getMem (p' + BitVec.ofNat 64 (8 * i))) :
    kListAt t p n = kListAt t' p' n := by
  unfold kListAt
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem kListAt_getElem (t : MachineState) (p : Word) (n i : ℕ) (hi : i < (kListAt t p n).length) :
    (kListAt t p n)[i] = BF64.ofBitVec (t.getMem (p + BitVec.ofNat 64 (8 * i))) := by
  simp [kListAt]

/-- A `K` list whose words a frame misses. -/
theorem DFrame.kList {t t' : MachineState} {X : Word → Prop} (hX : DFrame t t' X) {p : Word} {n : ℕ}
    (hp : p.toNat + 8 * n ≤ 2 ^ 64) (hm : ∀ y, Within y p (8 * n) → ¬ X y) :
    kListAt t' p n = kListAt t p n :=
  kListAt_congr fun i hi ↦ hX _ fun j hj hw ↦ hm _ (by addr_omega [hp, hi, hj]) hw

/-! ## The model -/

/-- `subspace_roots`' first layer. -/
def layer0 (n : ℕ) : List K := (List.range' 1 n).map fun i ↦ BF64.ofBitVec (1#64 <<< (i % 64))

/-- The layer's update by `root`. -/
def sqAdd (root : K) (x : K) : K := x * x + root * x

theorem roots_eq (n : ℕ) :
    Model.Pcs.subspaceRootsRust n = (Model.Pcs.subspaceRootsLoop n ([1], layer0 n)).map (·.1) := rfl

/-- One step of the loop, its updated layer `M` nonempty. -/
theorem rootsStep {roots layer : List K} (hl : layer ≠ []) :
    Model.Pcs.subspaceRootsStep (roots, layer) =
      some (roots ++ [(layer.map (sqAdd (roots.getLastD 0)))[0]'(by simp; exact List.length_pos_iff.mpr hl)],
        (layer.map (sqAdd (roots.getLastD 0))).tail) := by
  unfold Model.Pcs.subspaceRootsStep
  cases layer with
  | nil => exact absurd rfl hl
  | cons x xs => simp [sqAdd]

theorem rootsLoop_succ (m : ℕ) (st st' : List K × List K) (h : Model.Pcs.subspaceRootsStep st = some st') :
    Model.Pcs.subspaceRootsLoop (m + 1) st = Model.Pcs.subspaceRootsLoop m st' := by
  simp [Model.Pcs.subspaceRootsLoop, h]

/-- The machine's update of one word: `square` then `base_mul` by the root, `xor`. -/
theorem sqAdd_word (r x : Word) :
    BF64.ofBitVec ((kOf r * kOf x).toBitVec ^^^ (kOf x * kOf x).toBitVec) = sqAdd (kOf r) (kOf x) := by
  rw [sqAdd, add_comm, ← Model.toBitVec_add]
  rfl

end Rv64Verifier.Proofs.Pcs.Vso
