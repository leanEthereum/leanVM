import Rv64Verifier.Proofs.Walk.R11

/-!
# `walk` from `0x800031dc` (R12, R13): what stays put

`Base12 .. lo3` is `Keep11` with `kappas` (`KapVec`), its buffer below `lo3`. A step that writes
only the 32 bytes at `sp + 1728`, the stack below the frame, `NEXT` and the heap from `lo3` on
(`W12`) keeps it (`Base12.keep`). `WVec u hd lo ws` is a `Vec<u64>` at `hd` holding `ws`, its
buffer from `lo` on.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

/-- What R12 and R13 write: `sp + 1728 .. 1760`, the stack below the frame, `NEXT`, the heap from
`lo3` on. -/
@[rv_addr] def W12 (s : MachineState) (lo3 : Nat) (v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 928) 32 ∨ Within a (s.getReg .x2 - 11392) 8736 ∨ Within a nextAddr 8 ∨
    (lo3 ≤ a.toNat ∧ a.toNat < heapNext v)

/-- `Keep11`, `kappas` below `lo3`. -/
structure Base12 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 lo3 : Nat) : Prop where
  k11 : Keep11 OI s u A k R Q B lo lo2
  kv : KapVec s u lo2 (kapPre A k 6)
  kbelow : (vecPtr u (s.getReg .x2 - 1344)).toNat + 8 * (vecCap u (s.getReg .x2 - 1344)).toNat ≤ lo3
  le23 : lo2 ≤ lo3
  lo3le : lo3 ≤ heapNext u

/-- A `Vec<u64>` at `hd` holding `ws`, its buffer from `lo` on. -/
structure WVec (u : MachineState) (hd : Word) (lo : Nat) (ws : List Nat) : Prop where
  ok : VecOk u hd 8 8
  fresh : lo ≤ (vecPtr u hd).toNat
  len : (vecLen u hd).toNat = ws.length
  vals : ∀ j < ws.length, u.getMem (vecPtr u hd + BitVec.ofNat 64 (8 * j)) =
    BitVec.ofNat 64 (ws.getD j 0)

section
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
  {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat}

theorem WVec.bounds {hd : Word} {lo : Nat} {ws : List Nat} (h : WVec u hd lo ws) (hk : ws ≠ []) :
    (vecPtr u hd).toNat % 8 = 0 ∧ heapStart ≤ (vecPtr u hd).toNat ∧
      (vecPtr u hd).toNat + 8 * (vecCap u hd).toNat ≤ heapNext u ∧ ws.length ≤ (vecCap u hd).toNat := by
  have hr := h.ok.raw
  have hl := h.ok.len
  have hn := h.len
  have : ws.length ≠ 0 := fun h0 ↦ hk (List.eq_nil_of_length_eq_zero h0)
  simp only [RawVecOk, Buf] at hr
  rcases hr.2 with h0 | h0
  · omega
  · exact ⟨hr.1, h0.1, by omega, by omega⟩

/-- A frame missing the header and the buffer keeps a `WVec`. -/
theorem WVec.keep {hd : Word} {lo : Nat} {ws : List Nat} (h : WVec u hd lo ws) (hk : ws ≠ [])
    {w : Word → Prop} (fr : Layout.DFrame u v w) (hh : ∀ x, Within x hd 24 → ¬ w x)
    (hb : ∀ x, Within x (vecPtr u hd) (8 * (vecCap u hd).toNat) → ¬ w x)
    (hs : hd.toNat + 24 ≤ 2 ^ 64) (hhi : heapNext u ≤ heapEnd) (mono : heapNext u ≤ heapNext v) :
    WVec v hd lo ws := by
  obtain ⟨b1, b2, b3, b4⟩ := h.bounds hk
  simp only [heapEnd] at hhi
  have g (o : Nat) (ho : o + 8 ≤ 24) : v.getMem (hd + BitVec.ofNat 64 o) = u.getMem (hd + BitVec.ofNat 64 o) :=
    fr.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, ho, hs])) (by addr_omega [ho, hs])
  have hc : vecCap v hd = vecCap u hd := by simpa [vecCap] using g 0 (by decide)
  have hp : vecPtr v hd = vecPtr u hd := g 8 (by decide)
  have hl : vecLen v hd = vecLen u hd := g 16 (by decide)
  have hraw := h.ok.raw
  refine ⟨⟨?_, ?_⟩, by rw [hp]; exact h.fresh, by rw [hl]; exact h.len, fun j hj ↦ ?_⟩
  · simp only [RawVecOk, Buf, hc, hp] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, by omega⟩⟩
  · rw [hc, hl]; exact h.ok.len
  · rw [hp, ← h.vals j hj]
    simp only [heapStart] at b2
    exact fr.getMem_of (fun x hx ↦ hb x (by simp only [Within] at hx ⊢; addr_omega [hx, hj, b2, b3, b4, hhi]))
      (by addr_omega [hj, b2, b3, b4, hhi])

theorem Base12.keep (hpre : WalkPre s) (h : Base12 OI s u A k R Q B lo lo2 lo3) {w : Word → Prop}
    (fr : Layout.DFrame u v w) (hw : ∀ a, w a → W12 s lo3 v a) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) :
    Base12 OI s v A k R Q B lo lo2 lo3 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hk := kapPre_ne A k (le_refl 6)
  have h23 := h.le23
  have hhv := hv.hi
  have hhu := h.k11.at11.base.inv.heap.hi
  simp only [heapEnd] at hhv hhu
  obtain ⟨b1, b2, b3, b4⟩ := h.kv.bounds hk
  have kb := h.kbelow
  simp only [heapStart] at b2
  have nh : ∀ x, Within x (s.getReg .x2 - 1344) 24 → ¬ w x := fun x hx hwx ↦ by
    simp only [Within] at hx
    rcases hw x hwx with h1 | h1 | h1 | h1
    · simp only [Within] at h1; addr_omega [hx, h1, hb1]
    · simp only [Within] at h1; addr_omega [hx, h1, hb1]
    · simp only [Within, nextAddr] at h1; addr_omega [hx, h1, hb1]
    · addr_omega [hx, h1, hb1, hhv]
  have nb : ∀ x, kapBuf s u x → ¬ w x := fun x hx hwx ↦ by
    simp only [kapBuf, Within] at hx
    rcases hw x hwx with h1 | h1 | h1 | h1
    · simp only [Within] at h1; addr_omega [hx, h1, hb1, b2, b3, hhu]
    · simp only [Within] at h1; addr_omega [hx, h1, hb1, b2, b3, hhu]
    · simp only [Within, nextAddr] at h1; addr_omega [hx, h1, b2, b3, hhu]
    · omega
  have g (o : Nat) (ho : o + 8 ≤ 24) : v.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) =
      u.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) :=
    fr.getMem_of (fun x hx ↦ nh x (by addr_omega [hx, ho, hb1])) (by addr_omega [ho, hb1])
  have hc : vecCap v (s.getReg .x2 - 1344) = vecCap u (s.getReg .x2 - 1344) := by
    simpa [vecCap] using g 0 (by decide)
  have hp : vecPtr v (s.getReg .x2 - 1344) = vecPtr u (s.getReg .x2 - 1344) := g 8 (by decide)
  refine ⟨h.k11.keep hpre fr (fun a ha ↦ ?_) hv mono sp,
    h.kv.keep hk fr nh nb (by addr_omega [hb1]) h.k11.at11.base.inv.heap.hi mono,
    by rw [hc, hp]; exact kb, h23, le_trans h.lo3le mono⟩
  rcases hw a ha with h1 | h1 | h1 | h1
  · simp only [Within] at h1
    refine Or.inl ⟨by addr_omega [h1, hb1], by addr_omega [h1, hb1], ?_⟩
    simp only [hdrs, Within]; addr_omega [h1, hb1]
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, h1.2⟩))

theorem Base12.same (hpre : WalkPre s) (h : Base12 OI s u A k R Q B lo lo2 lo3)
    (hm : ∀ a, v.getMem a = u.getMem a) (sp : v.getReg .x2 = u.getReg .x2) :
    Base12 OI s v A k R Q B lo lo2 lo3 := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact h.keep hpre (w := fun _ ↦ False) (Layout.DFrame.of_same hm _) (fun _ h ↦ h.elim)
    ⟨hn ▸ h.k11.at11.base.inv.heap.lo, hn ▸ h.k11.at11.base.inv.heap.hi⟩ hn.ge sp

theorem Lat11.base12 (h : Lat11 OI s u A k R Q B lo lo2 6) :
    Base12 OI s u A k R Q B lo lo2 (heapNext u) := by
  obtain ⟨-, -, b3, -⟩ := h.kv.bounds (kapPre_ne A k (le_refl 6))
  exact ⟨h.keep, h.kv, b3, h.keep.lo2le, le_refl _⟩

end

end Rv64Verifier.Proofs.Walk
