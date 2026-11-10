import Rv64Verifier.Proofs.Walk.Loop10

/-!
# `walk` from `0x80003038` to the `Layout`: what stays put, and `kappas`

`Keep11 .. lo lo2` is `AtR11` with everything the three `Vec<BusBlock>`s reach below `lo2`. A step
that writes only the frame from `sp + 576` but the three `Vec`s' headers, the stack below the frame,
`NEXT` and the heap from `lo2` (`W11`) keeps it (`Keep11.keep`).

`kappas` is built in the `Vec<K>` at `sp + 1312` (`S - 1344`): `KapVec` says its buffer is allocated
from `lo2` on and holds `ks`; `kapPre A k i` is `kappasRust` over the first `i` tables.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

/-- The headers of `count`, `push` and `pull`. -/
@[rv_addr] def hdrs (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 512) 24 ∨ Within a (s.getReg .x2 - 416) 24 ∨
    Within a (s.getReg .x2 - 224) 24

/-- What the code writes from `0x80003038` on: the frame from `sp + 576` but the three headers, the
stack below the frame, `NEXT`, the heap from `lo2` on. -/
@[rv_addr] def W11 (s : MachineState) (lo2 : Nat) (v : MachineState) (a : Word) : Prop :=
  ((s.getReg .x2 - 2080).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 104).toNat ∧ ¬ hdrs s a) ∨
    Within a (s.getReg .x2 - 11392) 8736 ∨ Within a nextAddr 8 ∨
    (lo2 ≤ a.toNat ∧ a.toNat < heapNext v)

/-- `AtR11`, what the three `Vec`s reach below `lo2`. -/
structure Keep11 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 : Nat) : Prop where
  at11 : AtR11 OI s u A k R Q B lo
  lo2le : lo2 ≤ heapNext u
  lole : lo ≤ lo2
  below : ∀ x, (blocksFoot u (s.getReg .x2 - 416) x ∨ blocksFoot u (s.getReg .x2 - 224) x ∨
    blocksFoot u (s.getReg .x2 - 512) x) → x.toNat < lo2

section Keep
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
  {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat}

theorem AtR11.keep11 (h : AtR11 OI s u A k R Q B lo) : Keep11 OI s u A k R Q B lo (heapNext u) where
  at11 := h
  lo2le := le_refl _
  lole := h.base.loLe
  below := fun x hx ↦ by
    rcases hx with hx | hx | hx
    · exact (h.vecs.push.foot_below hx).2
    · exact (h.vecs.pull.foot_below hx).2
    · exact (h.vecs.count.foot_below hx).2

/-- The heap below `lo2` is not in `W11`. -/
theorem W11.heap (hpre : WalkPre s) (hl : lo2 ≤ heapEnd) {x : Word} (hx1 : heapStart ≤ x.toNat)
    (hx2 : x.toNat < lo2) : ¬ W11 s lo2 v x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [W11, Within, heapStart, nextAddr] at hx1 ⊢
  simp only [heapEnd] at hl
  rintro (⟨h1, -, -⟩ | h1 | h1 | ⟨h1, -⟩)
  · addr_omega [h1, hx1, hx2, hb1, hl]
  · addr_omega [h1, hx1, hx2, hb1, hl]
  · addr_omega [h1, hx2, hl]
  · omega

/-- The three headers are not in `W11`. -/
theorem W11.hdr (hpre : WalkPre s) (hv : heapNext v ≤ heapEnd) {x : Word} (hx : hdrs s x) :
    ¬ W11 s lo2 v x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [W11, Within] at hx ⊢
  simp only [heapEnd] at hv
  rintro (⟨-, -, h1⟩ | h1 | h1 | ⟨-, h1⟩)
  · exact h1 hx
  all_goals rcases hx with hx | hx | hx <;> addr_omega [h1, hx, hb1, hv]

theorem Keep11.keep (hpre : WalkPre s) (h : Keep11 OI s u A k R Q B lo lo2) {w : Word → Prop}
    (fr : Layout.DFrame u v w) (hw : ∀ a, w a → W11 s lo2 v a) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) :
    Keep11 OI s v A k R Q B lo lo2 := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have H := h.at11.base
  have V := h.at11.vecs
  have hl2 := h.lole
  have hl2u := h.lo2le
  have hhu := H.inv.heap.hi
  have hB := H.bufB
  have hl := H.loLe
  simp only [heapEnd] at hhu
  have hX : ∀ a, w a → X10 s lo B v a := fun a ha ↦ by
    rcases hw a ha with ⟨h1, h2, -⟩ | h1 | h1 | ⟨h1, h2⟩
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩))))
  have nh : ∀ x, heapStart ≤ x.toNat → x.toNat < lo2 → ¬ w x := fun x h1 h2 hwx ↦
    W11.heap hpre (by simp only [heapEnd]; omega) h1 h2 (hw x hwx)
  have nhd : ∀ x, hdrs s x → ¬ w x := fun x hx hwx ↦
    W11.hdr hpre hv.hi hx (hw x hwx)
  have K (a : Word) (hok : BlocksOk u a) (hha : ∀ x, Within x a 24 → hdrs s x)
      (ha : a.toNat + 24 ≤ 2 ^ 64) (hb : ∀ x, blocksFoot u a x → x.toNat < lo2) :=
    vecKeep fr hok ha (fun x hx ↦ nhd x (hha x hx))
      (fun x hx ↦ nh x (hok.foot_below hx).1 (hb x hx)) H.inv.heap mono
  have kp := K _ V.push (fun x hx ↦ Or.inr (Or.inl hx)) (by addr_omega [hb1])
    fun x hx ↦ h.below x (Or.inl hx)
  have kl := K _ V.pull (fun x hx ↦ Or.inr (Or.inr hx)) (by addr_omega [hb1])
    fun x hx ↦ h.below x (Or.inr (Or.inl hx))
  have kc := K _ V.count (fun x hx ↦ Or.inl hx) (by addr_omega [hb1])
    fun x hx ↦ h.below x (Or.inr (Or.inr hx))
  have op : v.getMem (B + 472) = u.getMem (B + 472) := by
    have hs0 := hpre.heap.lo
    simp only [heapStart] at hs0
    exact fr _ (fun y hy ↦ nh y (by simp only [Within, heapStart] at hy ⊢; addr_omega [hy, hB, hs0, hl, hhu])
      (by simp only [Within] at hy; addr_omega [hy, hB, hl, hhu, hl2])) (by addr_omega [hB, hl, hhu])
  refine ⟨⟨H.keep hpre fr hX hv mono sp, op.trans h.at11.op5, ⟨kp.1, kl.1, kc.1,
    by rw [kp.2.1]; exact V.pushV, by rw [kl.2.1]; exact V.pullV, by rw [kc.2.1]; exact V.countV,
    ?_, ?_, ?_, ?_⟩⟩, le_trans hl2u mono, hl2, ?_⟩ <;> simp only [kp.2.2, kl.2.2, kc.2.2]
  · exact V.fresh
  · exact V.d1
  · exact V.d2
  · exact V.d3
  · exact h.below

end Keep

end Rv64Verifier.Proofs.Walk
