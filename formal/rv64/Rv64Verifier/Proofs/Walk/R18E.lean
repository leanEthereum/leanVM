import Rv64Verifier.Proofs.Walk.R18D
import Rv64Verifier.Proofs.Multilinear.Contracts

/-!
# `walk` R18, the table claims: the point's clone

`point.clone()` at `0x80003894`, into `S - 1344`. A table of log-height `0` has an empty point,
whose dangling pointer `Mapped` and `Outside` do not hold of: `CloneSpecE` is `CloneSpec` asking
for the slice only when it is not empty (`clone` then reads nothing of it).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `ClonePre`, the slice asked for only when it is not empty. -/
structure ClonePreE (s : MachineState) : Prop where
  heap : HeapOk s
  out : ValidMemRange (s.getReg .x10) 3
  src : (s.getReg .x12).toNat ≠ 0 → Mapped (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  srcAlign : (s.getReg .x11).toNat % 8 = 0
  stack : RtStack s MultilinearContracts.cloneStack
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s MultilinearContracts.cloneStack)
    MultilinearContracts.cloneStack
  srcFree : (s.getReg .x12).toNat ≠ 0 → Outside s (s.getReg .x11) (24 * (s.getReg .x12).toNat)
  srcOut : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat) (s.getReg .x10) 24
  srcStack : Apart (s.getReg .x11) (24 * (s.getReg .x12).toNat)
    (stackLo s MultilinearContracts.cloneStack) MultilinearContracts.cloneStack

abbrev CloneSpecE : Prop :=
  FunSpec Image.code 0x8000897c ClonePreE MultilinearContracts.ClonePost

theorem heapValid {a : Word} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat ≤ 0x78000000)
    (h3 : a.toNat % 8 = 0) : Sym.validAccess 8 a = true :=
  (Sym.validAccess_eight a).mpr ⟨Or.inl ⟨h1, h2⟩, h3⟩

/-- A `Vec<E>` allocated from `w` on to `t`. -/
theorem newVecE_facts {w t : MachineState} {a : Word} {xs : List E} (h : NewVecE w t a xs) :
    (vecPtr t a).toNat % 8 = 0 ∧ (vecLen t a).toNat = xs.length ∧
      ((vecLen t a).toNat = 0 ∨ heapNext w ≤ (vecPtr t a).toNat ∧
        (vecPtr t a).toNat + 24 * (vecLen t a).toNat ≤ heapNext t) := by
  have hl := h.vec.len
  have hb := h.buf
  simp only [NewBuf] at hb
  refine ⟨h.vec.raw.1, by rw [← h.elems, vecEs, eListAt_length], ?_⟩
  rcases hb.2 with h0 | h0
  · left; rw [Nat.mul_eq_zero] at h0; omega
  · right; constructor <;> omega

/-- The rows' `Vec`. -/
theorem rowsAt_facts {w t : MachineState} {a : Word} {evs : List (List E × List E)}
    (h : RowsAt w t a evs) : (vecPtr t a).toNat % 8 = 0 ∧ (vecLen t a).toNat = evs.length ∧
      (evs.length = 0 ∨ heapNext w ≤ (vecPtr t a).toNat ∧
        (vecPtr t a).toNat + 48 * evs.length ≤ heapNext t) := by
  have hl := h.vec.len
  have hb := h.fresh
  have e := h.len
  simp only [NewBuf] at hb
  refine ⟨h.vec.raw.1, e, ?_⟩
  rcases hb.2 with h0 | h0
  · left; rw [Nat.mul_eq_zero] at h0; omega
  · right; constructor <;> omega

section Clone
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {k j : Nat} {P C L : Word}

/-- Table `k`'s point and values, as `walk` reads them. -/
theorem InnerR18.row
    (H : InnerR18 OI s u₀ w t u layout rows lir bus evs k j P C L) (o : Nat) (ho : o ≤ 24) :
    heapNext w ≤ (vecPtr t (s.getReg .x2 - 928)).toNat ∧
    (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + o)).toNat =
      (vecPtr t (s.getReg .x2 - 928)).toNat + 48 * k + o ∧
    (vecPtr t (s.getReg .x2 - 928)).toNat + 48 * k + 48 ≤ heapNext t ∧
    (vecPtr t (s.getReg .x2 - 928)).toNat % 8 = 0 := by
  have hk := H.hk
  obtain ⟨Pa, -, Pf⟩ := rowsAt_facts H.rowsAt
  have hh := H.rest.inv.heap.hi
  have htm := H.tmono
  simp only [heapEnd] at hh
  rcases Pf with h0 | ⟨p1, p2⟩
  · omega
  refine ⟨p1, by addr_omega [p2, hh, htm, ho, hk], by omega, Pa⟩

/-- `clone` of table `k`'s point into `S - 1344`: returns at `0x800038a8` with the loop's facts,
the callee-saved registers, and the new `Vec`, or the run dies. -/
theorem innerClone (hCl : CloneSpecE) (hpre : WalkPre s)
    (H : InnerR18 OI s u₀ w t u layout rows lir bus evs k j P C L) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x800038a8 ∧
      (∀ r ∈ calleeSaved, v.getReg r = u.getReg r) ∧
      CoreR18 OI s u₀ w t v layout rows lir bus evs P C (L.toNat + j)
        (bus.claims ++ tableClaimsRust (evs.take k) ++ (tableClaimsOf evs k).take j) ∧
      vecEs v (s.getReg .x2 - 1344) = (evs.getD k ([], [])).1 ∧
      ((vecLen v (s.getReg .x2 - 1344)).toNat = 0 ∨
        heapNext u ≤ (vecPtr v (s.getReg .x2 - 1344)).toNat ∧
        (vecPtr v (s.getReg .x2 - 1344)).toNat + 24 * (vecLen v (s.getReg .x2 - 1344)).toNat ≤
          heapNext v) ∧
      (vecPtr v (s.getReg .x2 - 1344)).toNat % 8 = 0 ∧
      v.getMem (s.getReg .x2 - 1616) = L) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := H.rest.inv
  have sp := I.sp
  have hk := H.hk
  have hh := I.heap.hi
  have hl0 := I.heap.lo
  have htm := H.tmono
  have hwm := H.wmono
  have m₀ := I.mono
  have hs0 := hpre.heap.lo
  have hsm := H.smono
  simp only [heapEnd, heapStart] at hh hl0 hs0
  obtain ⟨r1, -, r3, r4⟩ := H.row 0 (by omega)
  have r2 : (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)).toNat =
      (vecPtr t (s.getReg .x2 - 928)).toNat + 48 * k := by addr_omega [r3, hh, htm]
  have pk := (H.rowsAt.pairs k hk.2).1
  obtain ⟨qa, ql, qb⟩ := newVecE_facts pk
  -- the point's pointer and length, read at `u`
  have e8 : u.getMem (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k) + 8) =
      vecPtr t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)) := by
    rw [H.evKept _ (by addr_omega [r1, r2, r3, hh, htm]) (by addr_omega [r1, r2, r3, hh, htm])]; rfl
  have e16 : u.getMem (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k) + 16) =
      vecLen t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)) := by
    rw [H.evKept _ (by addr_omega [r1, r2, r3, hh, htm]) (by addr_omega [r1, r2, r3, hh, htm])]; rfl
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003894_spec H.pc (by
    rv_eval [H.x23]
    and_intros <;> refine heapValid ?_ ?_ ?_ <;> addr_omega [r1, r2, r3, r4, hh, htm, hs0, hsm, hwm])
  have m₁ := b80003894_mem_same h₁
  have k₁ := b80003894_keeps h₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have I₁ : Inv s u₁ := I.same m₁ (k₁ .x2 (by decide))
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1344 := by
    rw [b80003894_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₁ : u₁.getReg .x11 = vecPtr t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)) := by
    rw [b80003894_x11 h₁, H.x23]; exact e8
  have x12₁ : u₁.getReg .x12 = vecLen t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)) := by
    rw [b80003894_x12 h₁, H.x23]; exact e16
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have hcs : MultilinearContracts.cloneStack ≤ 8736 := by decide
  have pre : ClonePreE u₁ := {
    heap := I₁.heap
    out := by rw [x10₁]; valid_sub hval [hb1, hb3]
    src := fun hn ↦ by
      rw [x12₁] at hn; rw [x11₁, x12₁]
      rcases qb with h0 | ⟨q1, q2⟩
      · exact absurd h0 hn
      · exact Or.inl ⟨by omega, by omega⟩
    srcAlign := by rw [x11₁]; exact qa
    stack := hpre.stack.sub 2656 I₁.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by
      rw [x10₁]
      exact (fr_ok hpre I₁ (c := 1344) (k := 1344) (n := 24) (m := 0) rfl (by omega) (by omega)
        (by omega)).1
    outStack := by
      rw [x10₁]
      exact (fr_ok hpre I₁ (c := 1344) (k := 1344) (n := 24) rfl (by omega) (by omega) hcs).2.1
    srcFree := fun hn ↦ by
      rw [x12₁] at hn; rw [x11₁, x12₁]
      rcases qb with h0 | ⟨q1, q2⟩
      · exact absurd h0 hn
      · exact (heap_ok I₁.heap (by rw [hn₁]; omega)).1
    srcOut := by
      rw [x11₁, x10₁, x12₁]
      simp only [Apart]
      rcases qb with h0 | ⟨q1, q2⟩
      · left; omega
      · right; right; left; addr_omega [q2, hb1, hab, hh, htm]
    srcStack := by
      rw [x11₁, x12₁, stackLo_callee I₁]
      simp only [Apart]
      rcases qb with h0 | ⟨q1, q2⟩
      · left; omega
      · right; right; left; addr_omega [q2, hb1, hab, hh, htm, hcs] }
  obtain ⟨v, hr, ⟨hpc, hp, post⟩ | hd⟩ := hCl.call (Reaches.refl u₁) (b80003894_pc h₁) pre
  swap
  · exact ⟨v, hr₁.trans hr, Or.inr hd⟩
  have fr := post.frame
  rw [x10₁] at fr
  have st₁ : StepW s u u₁ (fun _ ↦ False) False := StepW.same I.heap m₁ (k₁ .x2 (by decide)) _ _
  have st₂ : StepW s u₁ v (Within · (s.getReg .x2 - 1344) 24) False :=
    StepW.ofCall hpre I₁ hcs (DFrame.of_byteFrame fr) post.heap post.mono (hp .x2 (by decide))
  have C₁ := H.toCoreR18.stepW hpre st₁ (fun a h ↦ h.elim) (fun a h ↦ h.elim)
  have C₂ := C₁.stepW hpre st₂ (fun a ha ↦ by
      obtain ⟨o1, o2⟩ := range_ok hpre H.rest (c := 1344) (k := 1344) (n := 24) rfl (by omega)
        (by omega) ha
      refine ⟨o1, o2, ?_⟩
      rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1])
    (fun a ha ↦ by simp only [Within] at ha ⊢; refine ⟨?_, ?_, ?_, ?_⟩ <;> addr_omega [ha, hb1])
  have el := post.elems
  have ln := post.len
  have fs := post.fresh
  rw [x10₁, x11₁, x12₁] at el
  rw [x10₁, x12₁] at ln fs
  simp only [NewBuf] at fs
  have hvm := post.mono
  refine ⟨v, hr₁.trans hr, Or.inl ⟨by rw [hpc, returnAddress, b80003894_x1 h₁]; decide,
    fun r hr ↦ ?_, C₂, ?_, ?_, fs.1, ?_⟩⟩
  · rw [hp r hr]
    refine k₁ r ?_
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  · rw [el, List.getD_eq_getElem _ _ hk.2, ← pk.elems, vecEs]
    refine Bus.eListAt_congr fun i hi ↦ ?_
    rcases qb with h0 | ⟨q1, q2⟩
    · omega
    have g (c : Nat) (hc : c ≤ 16) (y : Word)
        (hy : y = vecPtr t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)) +
          BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) : u₁.getMem y = t.getMem y := by
      subst hy
      rw [m₁, H.evKept _ (by addr_omega [q1, q2, hi, hc, hh, htm])
        (by addr_omega [q1, q2, hi, hc, hh, htm])]
    exact eAt_congr (g 0 (by omega) _ (by rw [add_ofNat_zero])) (g 8 (by omega) _ rfl)
      (g 16 (by omega) _ rfl)
  · rw [ln]
    rcases fs.2 with h0 | ⟨f1, f2⟩
    · left; omega
    · right; rw [hn₁] at f1; exact ⟨f1, by omega⟩
  · rw [show (1616 : Word) = BitVec.ofNat 64 1616 from rfl, st₂.getF hpre (by addr_omega [hb1])
      (fun i hi hw ↦ by simp only [Within] at hw; addr_omega [hw, hi, hb1]) (fun hf ↦ hf.elim), m₁]
    exact H.lenSlot

end Clone

end Rv64Verifier.Proofs.Walk
