import Rv64Verifier.Proofs.Pcs.VsoMerkleMid

/-!
# `verify_stacked_opening`'s Merkle checks: what they write, and what they keep

From `0x8000aa14` the Merkle checks write the opening offset, the spills at `S - 1008` and the header's
slot `S - 832` (`MY`), then what the path loop writes (`PW`): together `MW`. `Clear` bytes, safe for
the path loop and apart from the sponge and offsets, miss all of it, so the paths' headers, leaves
and siblings, the queries and the root keep their values (`Clear.keep`, `openingAt_keep`), and a
path the scans checked is a `PathOk` at the path loop's start (`pathOk_of`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `n` bytes from `a` the Merkle checks never write. -/
def Clear (s : MachineState) (lo : ℕ) (a : Word) (n : ℕ) : Prop :=
  Safe s lo a n ∧ Apart a n (s.getReg .x10 + 8) 352

/-- What the Merkle checks write before the path loop. -/
def MY (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10 + 352) 8 ∨ Within a (s.getReg .x2 - 1008) 40 ∨
    Within a (s.getReg .x2 - 832) 8

/-- What the Merkle checks write, the heap from `lo` to `hi`. -/
def MW (s : MachineState) (lo hi : ℕ) (a : Word) : Prop := MY s a ∨ PW s lo hi a

theorem Clear.misses {s : MachineState} {lo hi : ℕ} {a : Word} {n : ℕ} (hpre : VsoPre s)
    (h : Clear s lo a n) (hhi : hi ≤ heapEnd) : ∀ y, Within y a n → ¬ MW s lo hi y := by
  have hb := bounds hpre
  have hT := Region.bounds hpre.self.ok.self
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  intro y hy hw
  rcases hw with (hw | hw | hw) | hw
  · addr_omega [hy, hw, h4, hT]
  · addr_omega [hy, hw, h2, hb]
  · addr_omega [hy, hw, h2, hb]
  · exact Safe.misses hpre ⟨h1, h2, h3⟩ hhi y hy hw

theorem Clear.sub {s : MachineState} {lo : ℕ} {a b : Word} {n m : ℕ} (h : Clear s lo a n)
    (h1 : a.toNat ≤ b.toNat) (h2 : b.toNat + m ≤ a.toNat + n) : Clear s lo b m := by
  obtain ⟨⟨c1, c2, c3⟩, c4⟩ := h
  simp only [Apart] at c2 c3 c4
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> (try simp only [Apart]) <;> omega

theorem Clear.mono {s : MachineState} {lo lo' : ℕ} {a : Word} {n : ℕ} (h : Clear s lo a n)
    (hl : lo ≤ lo') : Clear s lo' a n :=
  ⟨Safe.mono h.1 hl, h.2⟩

/-- A doubleword of `Clear` bytes is kept. -/
theorem Clear.keep {s u v : MachineState} {lo hi : ℕ} {a x : Word} {n : ℕ} (hpre : VsoPre s)
    (hf : DFrame u v (MW s lo hi)) (h : Clear s lo a n) (hhi : hi ≤ heapEnd)
    (hn : a.toNat + n ≤ 2 ^ 64) (h1 : a.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ a.toNat + n) :
    v.getMem x = u.getMem x :=
  hf x fun i hi' hw ↦ h.misses hpre hhi _ (by addr_omega [h1, h2, hi', hn]) hw

theorem MY.toMW {s u v : MachineState} (hf : DFrame u v (MY s)) (lo hi : ℕ) :
    DFrame u v (MW s lo hi) :=
  hf.mono fun _ h ↦ Or.inl h

/-- `MY` misses `NEXT`. -/
theorem MY.next {s u v : MachineState} (hpre : VsoPre s) (hf : DFrame u v (MY s)) :
    heapNext v = heapNext u := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hT := Region.bounds hpre.self.ok.self
  have hTf := hpre.self.free.2
  simp only [heapNext]
  rw [hf nextAddr fun i hi hw ↦ by
    rcases hw with hw | hw | hw
    · addr_omega [hw, hi, hT, hTf]
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hb, hnx]]

/-- `MY` misses `.rodata`. -/
theorem MY.rodata {s u v : MachineState} (hpre : VsoPre s) (hro : RodataOk u)
    (hf : DFrame u v (MY s)) : RodataOk v := by
  have hb := bounds hpre
  obtain ⟨-, hrs⟩ := sfacts hpre
  have hT := Region.bounds hpre.self.ok.self
  have hTr := hpre.self.rodata
  exact hro.dframe hf fun a ha hw ↦ by
    rcases hw with hw | hw | hw
    · addr_omega [hw, ha, hT, hTr]
    · addr_omega [hw, ha, hb, hrs]
    · addr_omega [hw, ha, hb, hrs]

/-- From `InvR`, what the Merkle checks write keeps it. -/
theorem MW.inv {s u v : MachineState} (hpre : VsoPre s) (hinv : InvR s u (u.getMem nextAddr))
    (fr : DFrame u v (MW s (heapNext u) (heapNext v))) (heap : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (hsp : v.getReg .x2 = u.getReg .x2) :
    InvR s v (v.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hT := Region.bounds hpre.self.ok.self
  have hmono := hinv.mono
  have hhi := heap.hi
  simp only [heapNext] at mono hhi
  refine Inv.step' hpre hinv fr (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl mono hhi hsp
  · rcases ha with (ha | ha | ha) | (ha | ha | ha | ha) | ha | ha | ⟨ha1, ha2⟩
    · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hT]))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · simp only [heapNext] at ha1 ha2
      exact Or.inr (Or.inr (Or.inr ⟨by omega, ha2⟩))
  · rcases ha with (ha | ha | ha) | (ha | ha | ha | ha) | ha | ha | ⟨ha1, ha2⟩
    · addr_omega [ha, hT, hb, hpre.self.stack]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · simp only [heapNext] at ha2
      addr_omega [ha2, hb, hhi]

/-- The path at `p`, apart from a frame. -/
theorem openingAt_keep {u v : MachineState} {X : Word → Prop} (hX : DFrame u v X) {p : Word}
    (hp : p.toNat + 56 ≤ 2 ^ 64) (hh : ∀ y, Within y p 56 → ¬ X y)
    (hl : (vecLen u p).toNat = 0 ∨ ((vecPtr u p).toNat + 8 * (vecLen u p).toNat ≤ 2 ^ 64 ∧
      ∀ y, Within y (vecPtr u p) (8 * (vecLen u p).toNat) → ¬ X y))
    (hs : (vecLen u (p + 24)).toNat = 0 ∨
      ((vecPtr u (p + 24)).toNat + 32 * (vecLen u (p + 24)).toNat ≤ 2 ^ 64 ∧
        ∀ y, Within y (vecPtr u (p + 24)) (32 * (vecLen u (p + 24)).toNat) → ¬ X y)) :
    openingAt v p = openingAt u p := by
  have w (o : ℕ) (ho : o + 8 ≤ 56) :
      v.getMem (p + BitVec.ofNat 64 o) = u.getMem (p + BitVec.ofNat 64 o) :=
    hX _ fun i hi hw ↦ hh _ (by addr_omega [hp, hi, ho]) hw
  have e48 : v.getMem (p + 48) = u.getMem (p + 48) := w 48 (by decide)
  have e8 : vecPtr v p = vecPtr u p := w 8 (by decide)
  have e16 : vecLen v p = vecLen u p := w 16 (by decide)
  have e32 : vecPtr v (p + 24) = vecPtr u (p + 24) := by
    simp only [vecPtr]; rw [BitVec.add_assoc]; exact w 32 (by decide)
  have e40 : vecLen v (p + 24) = vecLen u (p + 24) := by
    simp only [vecLen]; rw [BitVec.add_assoc]; exact w 40 (by decide)
  have eL : vecWords v p = vecWords u p := by
    simp only [vecWords, e8, e16]
    rcases hl with h0 | ⟨hb, hm⟩
    · rw [h0]; rfl
    · exact DFrame.readWords' hX (fun a ha hw ↦ hm a hw ha) hb
  unfold openingAt
  rw [e48, eL, e40, e32]
  congr 1
  rcases hs with h0 | ⟨hb, hm⟩
  · rw [h0]; rfl
  · apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    exact digest_keep hX (by addr_omega [hb, hi]) fun y hy hw ↦ hm y (by addr_omega [hy, hi, hb]) hw

theorem pathRoot_keep {u v : MachineState} {p R : Word} (h : PathRoot v p R)
    (ho : openingAt v p = openingAt u p) (hd : digestAt v R = digestAt u R) : PathRoot u p R := by
  unfold PathRoot at h ⊢
  rw [← ho, ← hd]
  exact h

/-- A shifted odd word is not zero. -/
theorem shl_ne_zero {x : Word} (hx : x.getLsbD 0 = true) {k : ℕ} (hk : k < 64) : x <<< k ≠ 0 := by
  intro h
  have := congrArg (fun y : Word ↦ y.getLsbD k) h
  simp [hk] at this
  simp [this] at hx

theorem width_ne_zero (ℓ fc : ℕ) : (if ℓ = 0 then 1 else 3 : Word) <<< (fc % 64) ≠ 0 :=
  shl_ne_zero (by split <;> decide) (Nat.mod_lt _ (by decide))

/-- A path the scans found with a leaf, at the path loop's start `w`, after the writes `MY` from
`u`. -/
theorem pathOk_of {s u w : MachineState} {p : Word} (hpre : VsoPre s) (hu : HeapOk u)
    (hf : DFrame u w (MY s)) (hh : Region p 56) (hc : Clear s (heapNext u) p 56) (hl : (vecLen u p).toNat ≠ 0)
    (hlr : (vecLen u p).toNat = 0 ∨ Region (vecPtr u p) (8 * (vecLen u p).toNat) ∧
      Clear s (heapNext u) (vecPtr u p) (8 * (vecLen u p).toNat))
    (hs : (vecLen u (p + 24)).toNat = 0 ∨ Region (vecPtr u (p + 24)) (32 * (vecLen u (p + 24)).toNat) ∧
      Clear s (heapNext u) (vecPtr u (p + 24)) (32 * (vecLen u (p + 24)).toNat)) :
    PathOk s w p := by
  have hP := Region.bounds hh
  have hn := MY.next hpre hf
  have w' (o : ℕ) (ho : o + 8 ≤ 56) :
      w.getMem (p + BitVec.ofNat 64 o) = u.getMem (p + BitVec.ofNat 64 o) :=
    hc.keep hpre (MY.toMW hf (heapNext u) (heapNext u)) hu.hi (by omega)
      (by addr_omega [hP, ho]) (by addr_omega [hP, ho])
  have e8 : vecPtr w p = vecPtr u p := w' 8 (by decide)
  have e16 : vecLen w p = vecLen u p := w' 16 (by decide)
  have e32 : vecPtr w (p + 24) = vecPtr u (p + 24) := by
    simp only [vecPtr]; rw [BitVec.add_assoc]; exact w' 32 (by decide)
  have e40 : vecLen w (p + 24) = vecLen u (p + 24) := by
    simp only [vecLen]; rw [BitVec.add_assoc]; exact w' 40 (by decide)
  rcases hlr with h0 | ⟨hlr, hlc⟩
  · exact absurd h0 hl
  refine ⟨hh, by rw [hn]; exact hc.1, by rw [e16]; exact hl, by rw [e8, e16]; exact hlr,
    by rw [e8, e16, hn]; exact hlc.1, ?_⟩
  rw [e32, e40, hn]
  rcases hs with h0 | ⟨h1, h2⟩
  · exact Or.inl h0
  · exact Or.inr ⟨h1, h2.1⟩

end Rv64Verifier.Proofs.Pcs.Vso
