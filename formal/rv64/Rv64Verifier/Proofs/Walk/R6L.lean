import Rv64Verifier.Proofs.Walk.R6
import Rv64Verifier.Proofs.Layout.ContractsKeccak
import Rv64Verifier.Proofs.Layout.MemoryColsBase

/-!
# `walk`: `flushes_keccak`'s cell loop, the state it keeps

The loop over the sides and cells (`0x80001b90 .. 0x80001f00`) keeps, besides `walk`'s state
(`M6`) and the `Flushes` at `sp + 1168` (`FlAt`), the two lane tables at `sp + 1312` and
`sp + 1728`, the side's lanes, flag and missing lane, and the second side's tuple while the first
runs (`KM`). Its body writes only the scratch slots (`Scr`), what callees own (the stack below the
frame, `NEXT`, fresh heap) and the `Flushes` (`KM.step`). A `Form` the body builds sits in a slot,
its buffer within a range of the heap (`SF`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

/-! ## Frame slots -/

/-- `n` bytes from `o`, aligned, between the transcript's end (`sp + 576`) and the saved
registers. -/
@[rv_addr] def InSlot (s : MachineState) (o : Word) (n : Nat) : Prop :=
  (s.getReg .x2 - 2080).toNat ≤ o.toNat ∧ o.toNat + n ≤ (s.getReg .x2 - 104).toNat ∧
    o.toNat % 8 = 0

/-- A slot is valid, outside the free heap and apart from a callee's stack. -/
theorem slotW {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {o : Word} {n m : Nat}
    (ho : InSlot s o (8 * n)) (hm : m ≤ 8736) :
    ValidMemRange o n ∧ Outside u o (8 * n) ∧ Apart o (8 * n) (stackLo u m) m := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx
  simp only [heapEnd] at hab
  obtain ⟨o1, o2, o3⟩ := ho
  refine ⟨by valid_sub hval [hb1, hb3, o1, o2, o3], ⟨Or.inr (by addr_omega [hab, hb1, o1]),
    by addr_omega [hx, hb1, o1, o2]⟩, by rw [stackLo_callee h]; addr_omega [hb1, hm, o1, o2]⟩

/-! ## A `Form` in a slot -/

/-- The `Form` at `o` holds `f`, its buffer within `[lo, hi)`. -/
structure SF (u : MachineState) (o : Word) (f : LayoutMirror.FormRust) (lo hi : Nat) : Prop where
  ok : FormOk u o
  val : formOf u o = f
  buf : ∀ x, formBuf u o x → lo ≤ x.toNat ∧ x.toNat < hi

theorem SF.frame {u v : MachineState} {o : Word} {f : LayoutMirror.FormRust} {lo hi : Nat}
    {w : Word → Prop} (h : SF u o f lo hi) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hh : ∀ x, Within x o 24 → ¬ w x) (hb : ∀ x, lo ≤ x.toNat → x.toNat < hi → ¬ w x)
    (hw : o.toNat + 24 ≤ 2 ^ 64) (hheap : HeapOk u) (hmono : heapNext u ≤ heapNext v) :
    SF v o f lo hi := by
  have G := Rv64Verifier.Layout.formOf_frame fr h.ok hh (fun x hx ↦ hb x (h.buf x hx).1 (h.buf x hx).2)
    hw hheap hmono
  have Hb := Rv64Verifier.Layout.formBuf_frame fr hh hw
  exact ⟨G.2, by rw [G.1]; exact h.val, fun x hx ↦ h.buf x (by rw [← Hb]; exact hx)⟩

theorem SF.move {u v : MachineState} {o o' : Word} {f : LayoutMirror.FormRust} {lo hi : Nat}
    {w : Word → Prop} (h : SF u o' f lo hi) (fr : Rv64Verifier.Layout.DFrame u v w)
    (m0 : v.getMem o = u.getMem o') (m8 : v.getMem (o + 8) = u.getMem (o' + 8))
    (m16 : v.getMem (o + 16) = u.getMem (o' + 16))
    (hb : ∀ x, lo ≤ x.toNat → x.toNat < hi → ¬ w x) (hheap : HeapOk u)
    (hmono : heapNext u ≤ heapNext v) : SF v o f lo hi := by
  have G := Rv64Verifier.Layout.formOf_move fr h.ok m0 m8 m16
    (fun x hx ↦ hb x (h.buf x hx).1 (h.buf x hx).2) hheap hmono
  exact ⟨G.2.1, by rw [G.1]; exact h.val, fun x hx ↦ h.buf x (by rw [← G.2.2]; exact hx)⟩

theorem SF.ofNew {u t : MachineState} {o : Word} {n : Nat} {f : LayoutMirror.FormRust}
    (h : Rv64Verifier.Layout.NewForm u t o n) (hv : formOf t o = f) :
    SF t o f (heapNext u) (heapNext t) := by
  refine ⟨h.ok, hv, fun x hx ↦ ?_⟩
  have nb := h.fresh
  simp only [NewBuf, formBuf, Within] at nb hx
  rcases nb.2 with h0 | h0 <;> omega

/-! ## The loop's state -/

/-- The slots the loop body overwrites: the forms at `sp + 952`, `sp + 1024`, `sp + 1096`, the
closure's environment at `sp + 1240`, the forms at `sp + 2240 .. 2336`, the values at
`sp + 2432`. -/
@[rv_addr] def Scr (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1704) 168 ∨ Within a (s.getReg .x2 - 1416) 24 ∨
    Within a (s.getReg .x2 - 416) 96 ∨ Within a (s.getReg .x2 - 224) 72

/-- Side `σ`'s lanes, flag and missing lane: `(KECCAK_IN, ODD_IN, Some(FREE))`, then
`(KECCAK_OUT, ODD_OUT, None)`. -/
def sideLanes (σ : Nat) : Nat := if σ = 0 then 15 else 40
def sideMissing (σ : Nat) : Option Nat := if σ = 0 then some 14 else none

theorem OptAt.congr {u v : MachineState} {a : Word} {o : Option Nat} (h : OptAt u a o)
    (h0 : v.getMem a = u.getMem a) (h8 : v.getMem (a + 8) = u.getMem (a + 8)) : OptAt v a o := by
  cases o with
  | none => simp only [OptAt] at h ⊢; rw [h0]; exact h
  | some x => simp only [OptAt] at h ⊢; rw [h0, h8]; exact h

/-- The loop's state in memory, on side `σ`, the `Flushes` at `sp + 1168` holding `F`. -/
structure KM (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (σ : Nat) (F : LayoutMirror.FlushesRust) :
    Prop where
  m : M6 OI s u A k R Q B
  fl : FlAt s u F B
  lens : u.getMem (s.getReg .x2 - 2520) = 6 ∧ u.getMem (s.getReg .x2 - 2504) = 0
  even : ∀ i < 13,
    OptAt u (s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * i))
      (LayoutMirror.keccakCellLanesAt false i).1 ∧
    OptAt u (s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * i) + 16)
      (LayoutMirror.keccakCellLanesAt false i).2
  odd : ∀ i < 13,
    OptAt u (s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * i))
      (LayoutMirror.keccakCellLanesAt true i).1 ∧
    OptAt u (s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * i) + 16)
      (LayoutMirror.keccakCellLanesAt true i).2
  side : u.getMem (s.getReg .x2 - 2456) = BitVec.ofNat 64 σ
  lanes : u.getMem (s.getReg .x2 - 1368) = BitVec.ofNat 64 (sideLanes σ)
  lanesPtr : u.getMem (s.getReg .x2 - 272) = s.getReg .x2 - 1368
  flag : u.getMem (s.getReg .x2 - 296) = BitVec.ofNat 64 (10 + σ)
  missing : OptAt u (s.getReg .x2 - 248) (sideMissing σ)
  next : σ = 0 → u.getMem (s.getReg .x2 - 2472) = 0xa00001b8 ∧
    u.getMem (s.getReg .x2 - 456) = 1 ∧ u.getMem (s.getReg .x2 - 448) = 40 ∧
    u.getMem (s.getReg .x2 - 440) = 11 ∧ u.getMem (s.getReg .x2 - 432) = 0

/-- A step that writes only the scratch slots, the `Flushes`' header and outside the frame keeps
`KM`'s words; `walk`'s state and the `Flushes` are the caller's to give. -/
theorem KM.of {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F F' : LayoutMirror.FlushesRust}
    {w : Word → Prop} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (fr : Rv64Verifier.Layout.DFrame u v w)
    (hs : ∀ a, w a → Scr s a ∨ Within a (s.getReg .x2 - 1488) 48 ∨
      ¬ Within a (s.getReg .x2 - 2656) 2552)
    (m : M6 OI s v A k R Q B) (fl : FlAt s v F' B) : KM OI s v A k R Q B σ F' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have keep (x : Word) (hx : (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat ∧
      (x.toNat + 8 ≤ (s.getReg .x2 - 1704).toNat ∨ (s.getReg .x2 - 1392).toNat ≤ x.toNat) ∧
      (x.toNat + 8 ≤ (s.getReg .x2 - 416).toNat ∨ (s.getReg .x2 - 320).toNat ≤ x.toNat) ∧
      (x.toNat + 8 ≤ (s.getReg .x2 - 224).toNat ∨ (s.getReg .x2 - 152).toNat ≤ x.toNat)) :
      v.getMem x = u.getMem x :=
    fr x (fun y hy hwy ↦ by
      rcases hs y hwy with hc | hc | hc
      · simp only [Scr, Within] at hy hc; rcases hc with hc | hc | hc | hc <;> addr_omega [hy, hc, hx, hb1]
      · simp only [Within] at hy hc; addr_omega [hy, hc, hx, hb1]
      · simp only [Within] at hy hc; addr_omega [hy, hc, hx, hb1]) (by addr_omega [hx, hb1])
  exact {
    m := m
    fl := fl
    lens := by rw [keep _ (by addr_omega [hb1]), keep _ (by addr_omega [hb1])]; exact h.lens
    even := fun i hi ↦ ⟨OptAt.congr (h.even i hi).1 (keep _ (by addr_omega [hb1, hi]))
        (keep _ (by addr_omega [hb1, hi])),
      OptAt.congr (h.even i hi).2 (keep _ (by addr_omega [hb1, hi])) (keep _ (by addr_omega [hb1, hi]))⟩
    odd := fun i hi ↦ ⟨OptAt.congr (h.odd i hi).1 (keep _ (by addr_omega [hb1, hi]))
        (keep _ (by addr_omega [hb1, hi])),
      OptAt.congr (h.odd i hi).2 (keep _ (by addr_omega [hb1, hi])) (keep _ (by addr_omega [hb1, hi]))⟩
    side := by rw [keep _ (by addr_omega [hb1])]; exact h.side
    lanes := by rw [keep _ (by addr_omega [hb1])]; exact h.lanes
    lanesPtr := by rw [keep _ (by addr_omega [hb1])]; exact h.lanesPtr
    flag := by rw [keep _ (by addr_omega [hb1])]; exact h.flag
    missing := OptAt.congr h.missing (keep _ (by addr_omega [hb1])) (keep _ (by addr_omega [hb1]))
    next := fun hσ ↦ by
      rw [keep _ (by addr_omega [hb1]), keep _ (by addr_omega [hb1]), keep _ (by addr_omega [hb1]),
        keep _ (by addr_omega [hb1]), keep _ (by addr_omega [hb1])]
      exact h.next hσ }

/-- A step that writes only the scratch slots, outside the frame (what `W6` allows there), and
nothing the `Flushes` reaches keeps `KM`. -/
theorem KM.step {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    {w : Word → Prop} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (fr : Rv64Verifier.Layout.DFrame u v w) (hw : ∀ a, w a → W6 s B v a)
    (hs : ∀ a, w a → Scr s a ∨ ¬ Within a (s.getReg .x2 - 2656) 2552)
    (hd : ∀ a, w a → ¬ flushesDeep u (s.getReg .x2 - 1488) a) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) :
    KM OI s v A k R Q B σ F ∧
      flushesDeep v (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have FL := h.fl.frame hpre fr (fun x hx hwx ↦ by
      rcases hs x hwx with hc | hc
      · simp only [Scr, Within] at hx hc; rcases hc with hc | hc | hc | hc <;> addr_omega [hx, hc, hb1]
      · simp only [Within] at hx hc; addr_omega [hx, hc, hb1])
    (fun x hx hwx ↦ hd x hwx hx) h.m.inv.heap mono
  exact ⟨h.of hpre fr (fun a ha ↦ (hs a ha).imp_right Or.inr) (h.m.step hpre (fr.mono hw) hv mono sp)
    FL.1, FL.2⟩

/-- A function growing the `Flushes` at `sp + 1168` to `F'`. -/
theorem KM.grow {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F F' : LayoutMirror.FlushesRust}
    {n : Nat} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (g : Rv64Verifier.Layout.GrowFlushes u t (s.getReg .x2 - 1488) n (fun _ ↦ False))
    (hn : n ≤ 8736) (sp : t.getReg .x2 = u.getReg .x2)
    (hF : Rv64Verifier.Layout.flushesOf t (s.getReg .x2 - 1488) = F') :
    KM OI s t A k R Q B σ F' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := g.heap.hi
  have hu := h.m.inv.heap.hi
  simp only [heapEnd] at hh hu
  refine h.of hpre g.frame (fun a ha ↦ ?_)
    (h.m.step hpre (g.frame.mono fun x hx ↦ grow_w6 hpre h.m.inv hn h.m.bufQ.2.2.2
      (fun y hy ↦ h.fl.deep y (hy.imp Or.inl Or.inl)) h.fl.ok g.mono hx) g.heap g.mono sp)
    ⟨g.ok, hF, fun x hx ↦ ?_⟩
  · rcases ha with ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl ha)
    · right; right; have := (h.fl.ok.buf_below ha).2; simp only [Within, heapNext] at this ⊢
      addr_omega [this, hu, hb1]
    · right; right; rw [stackLo_callee h.m.inv] at ha; simp only [Within] at ha ⊢; addr_omega [ha, hb1, hn]
    · right; right; simp only [Within] at ha ⊢; addr_omega [ha, hb1]
    · right; right; simp only [Fresh, heapNext] at ha hh; simp only [Within]; addr_omega [ha, hb1, hh]
  · rcases g.deep x hx with hd | hd | hd
    · exact h.fl.deep x hd
    · exact hd.elim
    · exact le_trans h.m.bufQ.2.2.2 hd.1

/-! ## Callees -/

/-- A callee's frame: its result's 24 bytes at `o`, its stack, `NEXT`, what it allocates. -/
@[rv_addr] def CW (u t : MachineState) (o : Word) (n : Nat) (a : Word) : Prop :=
  Within a o 24 ∨ Within a (stackLo u n) n ∨ Within a nextAddr 8 ∨ Fresh u t a

/-- `o`'s 24 bytes are scratch. -/
@[rv_addr] def InScr (s : MachineState) (o : Word) : Prop := ∀ x, Within x o 24 → Scr s x

theorem KM.call {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    {o : Word} {n : Nat} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (fr : Rv64Verifier.Layout.DFrame u t (CW u t o n)) (ho : InScr s o) (hn : n ≤ 8736)
    (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) (sp : t.getReg .x2 = u.getReg .x2) :
    KM OI s t A k R Q B σ F ∧
      flushesDeep t (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hB := h.m.bufQ.2.2.2
  have hh := hv.hi
  simp only [heapEnd] at hh
  refine h.step hpre fr (fun a ha ↦ ?_) (fun a ha ↦ ?_) (fun a ha hd ↦ ?_) hv mono sp
  · rcases ha with ha | ha | ha | ha
    · have hs := ho a ha
      exact Or.inl (by simp only [Scr, Within] at hs ⊢; rcases hs with c | c | c | c <;> addr_omega [c, hb1])
    · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre h.m.inv hn ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))))
  · rcases ha with ha | ha | ha | ha
    · exact Or.inl (ho a ha)
    · right; rw [stackLo_callee h.m.inv] at ha; simp only [Within] at ha ⊢; addr_omega [ha, hb1, hn]
    · right; simp only [Within] at ha ⊢; addr_omega [ha, hb1]
    · right; simp only [Fresh, heapNext] at ha hh; simp only [Within]; addr_omega [ha, hb1, hh]
  · have hdb := (h.fl.ok.deep_below hd).2
    have hu := h.m.inv.heap.hi
    simp only [heapEnd, heapNext] at hu hdb
    rcases ha with ha | ha | ha | ha
    · have hs := ho a ha
      simp only [Scr, Within] at hs; rcases hs with c | c | c | c <;> addr_omega [c, hb1, hdb, hu]
    · rw [stackLo_callee h.m.inv] at ha; simp only [Within] at ha; addr_omega [ha, hb1, hn, hdb, hu]
    · simp only [Within] at ha; addr_omega [ha, hdb, hu]
    · simp only [Fresh, heapNext] at ha; omega

theorem SF.call {s u t : MachineState} {o o' : Word} {n : Nat} {f : LayoutMirror.FormRust}
    {lo hi : Nat} (hpre : WalkPre s) (h : Inv s u) (hf : SF u o' f lo hi)
    (fr : Rv64Verifier.Layout.DFrame u t (CW u t o n)) (hn : n ≤ 8736)
    (ho : InSlot s o 24) (ho' : InSlot s o' 24)
    (hoo : o.toNat + 24 ≤ o'.toNat ∨ o'.toNat + 24 ≤ o.toNat) (hhi : hi ≤ heapNext u)
    (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) : SF t o' f lo hi := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, -⟩ := ho
  obtain ⟨p1, p2, -⟩ := ho'
  have hu := h.heap.hi
  have ht := hv.hi
  simp only [heapEnd, heapNext] at hu hhi ht
  refine hf.frame fr (fun x hx hw ↦ ?_) (fun x hx1 hx2 hw ↦ ?_) (by addr_omega [p2, hb1]) h.heap mono
  · simp only [Within] at hx
    rcases hw with hw | hw | hw | hw
    · simp only [Within] at hw; omega
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hx, hw, hb1, hn, p1, p2]
    · simp only [Within] at hw; addr_omega [hx, hw, hb1, p1, p2]
    · simp only [Fresh, heapNext] at hw; addr_omega [hx, hw, hb1, p1, p2, hu, ht]
  · rcases hw with hw | hw | hw | hw
    · simp only [Within] at hw; addr_omega [hw, hb1, o1, o2, hx2, hhi, hu]
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hw, hb1, hn, hx2, hhi, hu]
    · simp only [Within] at hw; addr_omega [hw, hx2, hhi, hu]
    · simp only [Fresh, heapNext] at hw; omega

/-! ## `flushes_keccak`'s limb closure -/

theorem cellLanes_le (b : Bool) {c : Nat} (hc : c < 13) :
    (∀ v, (LayoutMirror.keccakCellLanesAt b c).1 = some v → v ≤ 25) ∧
      (∀ v, (LayoutMirror.keccakCellLanesAt b c).2 = some v → v ≤ 25) := by
  unfold LayoutMirror.keccakCellLanesAt
  split_ifs <;> simp <;> omega

theorem optTag {u : MachineState} {a : Word} {o : Option Nat} (h : OptAt u a o) :
    u.getMem a = 0 ∨ u.getMem a = 1 := by
  cases o with
  | none => exact Or.inl h
  | some _ => exact Or.inr h.1

theorem laneOf_opt {u : MachineState} {a : Word} {o : Option Nat} {L : Nat} (h : OptAt u a o)
    (hL : L ≤ 40) (ho : ∀ v, o = some v → v ≤ 25) :
    Rv64Verifier.Layout.laneOf (BitVec.ofNat 64 L) (u.getMem a) (u.getMem (a + 8)) =
      o.map (L + ·) := by
  cases o with
  | none =>
    simp only [OptAt] at h
    simp only [Rv64Verifier.Layout.laneOf, h, ↓reduceIte, Option.map_none]
  | some v =>
    simp only [OptAt] at h
    have hv := ho v rfl
    simp only [Rv64Verifier.Layout.laneOf, h.1, h.2, Option.map_some]
    split
    · exact absurd (by assumption) (by decide)
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      congr 1
      omega

theorem optOf_opt {u : MachineState} {a : Word} {o : Option Nat} (h : OptAt u a o)
    (ho : ∀ v, o = some v → v ≤ 25) :
    Rv64Verifier.Layout.optOf (u.getMem a) (u.getMem (a + 8)) = o := by
  cases o with
  | none =>
    simp only [OptAt] at h
    simp only [Rv64Verifier.Layout.optOf, h, ↓reduceIte]
  | some v =>
    simp only [OptAt] at h
    have hv := ho v rfl
    simp only [Rv64Verifier.Layout.optOf, h.1, h.2]
    split
    · exact absurd (by assumption) (by decide)
    · simp only [BitVec.toNat_ofNat]
      congr 1
      omega

theorem sideMissing_le (σ : Nat) : ∀ v, sideMissing σ = some v → v ≤ 25 := by
  intro v hv
  by_cases h0 : σ = 0
  · simp only [sideMissing, h0, ↓reduceIte, Option.some.injEq] at hv; omega
  · simp only [sideMissing, h0, ↓reduceIte, reduceCtorEq] at hv

/-- The limb closure, `|e, o| layout_limb(lane(e), lane(o), flag, missing)`, into the slot `o`:
`e`, `d` the lanes' `Option`s at `a`, `b`. -/
theorem limbCall (hL : Rv64Verifier.Layout.LimbSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    {o a b : Word} {e d : Option Nat} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (hσ : σ < 2) (hpc : u.pc = 0x80004de4) (x10 : u.getReg .x10 = o) (ho : InScr s o)
    (ho' : InSlot s o 24) (x11 : u.getReg .x11 = s.getReg .x2 - 1416)
    (env : u.getMem (s.getReg .x2 - 1416) = s.getReg .x2 - 272 ∧
      u.getMem (s.getReg .x2 - 1408) = s.getReg .x2 - 296 ∧
      u.getMem (s.getReg .x2 - 1400) = s.getReg .x2 - 248)
    (he : OptAt u a e) (hd : OptAt u b d) (hev : ∀ v, e = some v → v ≤ 25)
    (hdv : ∀ v, d = some v → v ≤ 25)
    (x12 : u.getReg .x12 = u.getMem a) (x13 : u.getReg .x13 = u.getMem (a + 8))
    (x14 : u.getReg .x14 = u.getMem b) (x15 : u.getReg .x15 = u.getMem (b + 8)) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      KM OI s t A k R Q B σ F ∧
      flushesDeep t (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) ∧
      Rv64Verifier.Layout.NewForm u t o Rv64Verifier.Layout.limbStack ∧
      formOf t o = LayoutMirror.layoutLimbRust (e.map (sideLanes σ + ·)) (d.map (sideLanes σ + ·))
        (10 + σ) (sideMissing σ)) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.limbStack ≤ 8736 := by decide
  have I := h.m.inv
  obtain ⟨e0, e8, e16⟩ := env
  have a8 : s.getReg .x2 - 1416 + 8 = s.getReg .x2 - 1408 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a16 : s.getReg .x2 - 1416 + 16 = s.getReg .x2 - 1400 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have sO := slotW (n := 3) hpre I (o := o) (by simpa [InSlot] using ho') hn
  have sE := slotW (n := 3) hpre I (o := s.getReg .x2 - 1416) (by simp only [InSlot]; addr_omega [hb1, hb3]) hn
  have sL1 := slotW (n := 1) hpre I (o := s.getReg .x2 - 272) (by simp only [InSlot]; addr_omega [hb1, hb3]) hn
  have sL2 := slotW (n := 1) hpre I (o := s.getReg .x2 - 1368) (by simp only [InSlot]; addr_omega [hb1, hb3]) hn
  have sF := slotW (n := 1) hpre I (o := s.getReg .x2 - 296) (by simp only [InSlot]; addr_omega [hb1, hb3]) hn
  have sM := slotW (n := 2) hpre I (o := s.getReg .x2 - 248) (by simp only [InSlot]; addr_omega [hb1, hb3]) hn
  have pre : Rv64Verifier.Layout.LimbPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    out := by rw [x10]; exact sO.1
    outFree := by rw [x10]; exact sO.2.1
    outStack := by rw [x10]; exact sO.2.2
    env := by rw [x11]; exact sE.1
    envStack := by rw [x11]; exact sE.2.2
    lanes1 := by rw [x11, e0]; exact sL1.1
    lanes1Stack := by rw [x11, e0]; exact sL1.2.2
    lanes2 := by rw [x11, e0, h.lanesPtr]; exact sL2.1
    lanes2Stack := by rw [x11, e0, h.lanesPtr]; exact sL2.2.2
    flag := by simp only [Rv64Verifier.Layout.limbFlagPtr]; rw [x11, a8, e8]; exact sF.1
    flagStack := by simp only [Rv64Verifier.Layout.limbFlagPtr]; rw [x11, a8, e8]; exact sF.2.2
    missing := by simp only [Rv64Verifier.Layout.limbMissing]; rw [x11, a16, e16]; exact sM.1
    missingStack := by simp only [Rv64Verifier.Layout.limbMissing]; rw [x11, a16, e16]; exact sM.2.2
    evenTag := by rw [x12]; exact optTag he
    oddTag := by rw [x14]; exact optTag hd
    rodata := I.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hdd⟩ := hL u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hdd⟩
  rw [x10] at nf fv
  have K := KM.call hpre h nf.frame ho hn nf.heap nf.mono (hp .x2 (by decide))
  refine ⟨t, hr, Or.inl ⟨hpct, hp, K.1, K.2, nf, ?_⟩⟩
  have hlanes : Rv64Verifier.Layout.limbLanes u = BitVec.ofNat 64 (sideLanes σ) := by
    simp only [Rv64Verifier.Layout.limbLanes]; rw [x11, e0, h.lanesPtr, h.lanes]
  have hL40 : sideLanes σ ≤ 40 := by unfold sideLanes; split_ifs <;> omega
  rw [fv, hlanes, x12, x13, x14, x15, laneOf_opt he hL40 hev, laneOf_opt hd hL40 hdv]
  simp only [Rv64Verifier.Layout.limbFlagPtr, Rv64Verifier.Layout.limbMissing]
  rw [x11, a8, a16, e8, e16, h.flag, optOf_opt h.missing (sideMissing_le σ)]
  congr 1
  simp only [BitVec.toNat_ofNat]; omega

/-- A block that writes scratch only keeps `KM` and `NEXT`. -/
theorem KM.scr {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    {w : Word → Prop} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (fr : Rv64Verifier.Layout.DFrame u v w) (hw : ∀ a, w a → Scr s a)
    (sp : v.getReg .x2 = u.getReg .x2) :
    KM OI s v A k R Q B σ F ∧
      flushesDeep v (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) ∧
      heapNext v = heapNext u := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    rw [fr nextAddr (fun x hx hwx ↦ by
      have hs := hw x hwx
      simp only [Scr, Within] at hs hx; rcases hs with c | c | c | c <;> addr_omega [c, hx, hb1])
      (by decide)]
  have hh := h.m.inv.heap
  have K := h.step hpre fr (fun a ha ↦ by
      have hs := hw a ha
      exact Or.inl (by simp only [Scr, Within] at hs ⊢; rcases hs with c | c | c | c <;> addr_omega [c, hb1]))
    (fun a ha ↦ Or.inl (hw a ha))
    (fun a ha hd ↦ by
      have hdb := (h.fl.ok.deep_below hd).2
      have hu := hh.hi
      have hs := hw a ha
      simp only [heapEnd, heapNext] at hu hdb
      simp only [Scr, Within] at hs; rcases hs with c | c | c | c <;> addr_omega [c, hb1, hdb, hu])
    ⟨hn ▸ hh.lo, hn ▸ hh.hi⟩ hn.ge sp
  exact ⟨K.1, K.2, hn⟩

/-- `Form::term(monomial, coefficient)` into the slot `o`: the monomial at `m` is `One`, the
coefficient a constant in `.rodata`. -/
theorem termCall (hT : Rv64Verifier.Layout.TermSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    {o m c : Word} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (hpc : u.pc = 0x800050a8) (x10 : u.getReg .x10 = o) (ho : InScr s o) (ho' : InSlot s o 24)
    (x11 : u.getReg .x11 = m) (hm : InSlot s m 24) (hm0 : u.getMem m = 0)
    (x12 : u.getReg .x12 = c) (hc : c.toNat % 8 = 0 ∧ 0xa0000000 ≤ c.toNat ∧
      c.toNat + 24 ≤ 0xa0000f30) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      KM OI s t A k R Q B σ F ∧
      flushesDeep t (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) ∧
      Rv64Verifier.Layout.NewForm u t o Rv64Verifier.Layout.termStack ∧
      formOf t o = LayoutMirror.constantRust (eAt u c)) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.termStack ≤ 8736 := by decide
  have I := h.m.inv
  have sO := slotW (n := 3) hpre I (o := o) (by simpa [InSlot] using ho') hn
  have sM := slotW (n := 3) hpre I (o := m) (by simpa [InSlot] using hm) hn
  obtain ⟨c1, c2, c3⟩ := hc
  obtain ⟨m1, m2, -⟩ := hm
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have pre : Rv64Verifier.Layout.TermPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    out := by rw [x10]; exact sO.1
    mono := by rw [x11]; exact sM.1
    coeff := by rw [x12]; exact Rv64Verifier.Layout.validMemRange_of c1 (Or.inr ⟨c2, by omega⟩)
    monoOk := by rw [x11]; simp only [Rv64Verifier.Layout.MonoOk, hm0]; decide
    outFree := by rw [x10]; exact sO.2.1
    monoNext := by rw [x11]; addr_omega [hb1, m1, m2]
    coeffNext := by rw [x12]; addr_omega [c2, c3]
    outStack := by rw [x10]; exact sO.2.2
    monoStack := by rw [x11]; exact sM.2.2
    coeffStack := by rw [x12, stackLo_callee I]; addr_omega [hb1, c2, c3] }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hdd⟩ := hT u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hdd⟩
  rw [x10] at nf fv
  have K := KM.call hpre h nf.frame ho hn nf.heap nf.mono (hp .x2 (by decide))
  refine ⟨t, hr, Or.inl ⟨hpct, hp, K.1, K.2, nf, ?_⟩⟩
  rw [fv, x11, x12, Rv64Verifier.Layout.monoOf, hm0]
  rfl

/-- The registers at the cell loop's head, on side `σ`, cell `c`. -/
structure KR (s u : MachineState) (σ c : Nat) : Prop where
  x8 : u.getReg .x8 = s.getReg .x2 - 200
  x9 : u.getReg .x9 = s.getReg .x2 - 912 + BitVec.ofNat 64 (32 * c)
  x18 : u.getReg .x18 = 13
  x19 : u.getReg .x19 = s.getReg .x2 - 1328 + BitVec.ofNat 64 (32 * c)
  x20 : u.getReg .x20 = s.getReg .x2 - 176
  x21 : u.getReg .x21 = BitVec.ofNat 64 (65 + 13 * σ)
  x22 : u.getReg .x22 = 0xa00001b8 + BitVec.ofNat 64 (8 * c)
  x23 : u.getReg .x23 = BitVec.ofNat 64 c
  x25 : u.getReg .x25 = s.getReg .x2 - 272
  x26 : u.getReg .x26 = s.getReg .x2 - 512
  x27 : u.getReg .x27 = BitVec.ofNat 64 σ

theorem KR.pres {s u t : MachineState} {σ c : Nat} (h : KR s u σ c) (hp : Preserves u t) :
    KR s t σ c :=
  ⟨by rw [hp .x8 (by decide)]; exact h.x8, by rw [hp .x9 (by decide)]; exact h.x9,
    by rw [hp .x18 (by decide)]; exact h.x18, by rw [hp .x19 (by decide)]; exact h.x19,
    by rw [hp .x20 (by decide)]; exact h.x20, by rw [hp .x21 (by decide)]; exact h.x21,
    by rw [hp .x22 (by decide)]; exact h.x22, by rw [hp .x23 (by decide)]; exact h.x23,
    by rw [hp .x25 (by decide)]; exact h.x25, by rw [hp .x26 (by decide)]; exact h.x26,
    by rw [hp .x27 (by decide)]; exact h.x27⟩

theorem KR.keeps {s u t : MachineState} {σ c : Nat} (h : KR s u σ c)
    (hk : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27] : List Reg),
      t.getReg r = u.getReg r) : KR s t σ c :=
  ⟨by rw [hk .x8 (by decide)]; exact h.x8, by rw [hk .x9 (by decide)]; exact h.x9,
    by rw [hk .x18 (by decide)]; exact h.x18, by rw [hk .x19 (by decide)]; exact h.x19,
    by rw [hk .x20 (by decide)]; exact h.x20, by rw [hk .x21 (by decide)]; exact h.x21,
    by rw [hk .x22 (by decide)]; exact h.x22, by rw [hk .x23 (by decide)]; exact h.x23,
    by rw [hk .x25 (by decide)]; exact h.x25, by rw [hk .x26 (by decide)]; exact h.x26,
    by rw [hk .x27 (by decide)]; exact h.x27⟩

end Rv64Verifier.Proofs.Walk
