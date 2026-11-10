import Rv64Verifier.Proofs.Pcs.ExtendBase

/-!
# `Vec<StackClaim>::extend_desugared`: the loop's invariant

`StepW s u`: what one pass from `u` writes (the `Vec`, the iterator's position, the frame below the
saved registers and the callees' stacks, `NEXT`, the heap from `u`'s `NEXT` on, the spare
capacity). `Safe s u`: a region no pass from `u` on writes. `Inv s u j`: the first `j` claims done.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs

/-- The spare capacity of the `Vec` at `a`. -/
@[rv_addr] def spareLo (u : MachineState) (a : Word) : Word :=
  vecPtr u a + BitVec.ofNat 64 (88 * (vecLen u a).toNat)
@[rv_addr] def spareLen (u : MachineState) (a : Word) : Nat :=
  88 * ((vecCap u a).toNat - (vecLen u a).toNat)

/-- What a pass from `u` writes. -/
def StepW (s u : MachineState) (nx x : Word) : Prop :=
  Within x (s.getReg .x10) 24 ∨ Within x (s.getReg .x11) 8 ∨
    Within x (stackLo s extendStack) (extendStack - 104) ∨ Within x nextAddr 8 ∨
    (heapNext u ≤ x.toNat ∧ x.toNat < nx.toNat) ∨
    Within x (spareLo u (s.getReg .x10)) (spareLen u (s.getReg .x10))

/-- A region no pass from `u` on writes. -/
def Safe (s u : MachineState) (a : Word) (n : Nat) : Prop :=
  n = 0 ∨ (Region a n ∧ ExtendOff s a n ∧ Apart a n (stackLo s extendStack) extendStack ∧
    Apart a n nextAddr 8 ∧ (a.toNat + n ≤ heapNext u ∨ heapEnd ≤ a.toNat) ∧
    Apart a n (spareLo u (s.getReg .x10)) (spareLen u (s.getReg .x10)))

theorem Safe.miss {s u : MachineState} {a : Word} {n : Nat} (h : Safe s u a n) {nx : Word}
    (hnx : nx.toNat ≤ heapEnd) : ∀ x, Within x a n → ¬ StepW s u nx x := by
  intro x hx hW
  rcases h with h0 | ⟨hR, ⟨ho1, ho2⟩, hst, hnx, hh, hsp⟩
  · simp only [Within] at hx; omega
  have hb := Region.bounds hR
  rcases hW with hW | hW | hW | hW | hW | hW
  · addr_omega [hx, hW, ho1, hb]
  · addr_omega [hx, hW, ho2, hb]
  · addr_omega [hx, hW, hst, hb]
  · addr_omega [hx, hW, hnx, hb]
  · simp only [Within] at hx; omega
  · addr_omega [hx, hW, hsp, hb]

theorem Safe.bound {s u : MachineState} {a : Word} {n : Nat} (h : Safe s u a n) :
    n = 0 ∨ a.toNat + n ≤ 0xc0000000 := by
  rcases h with h0 | ⟨hR, -⟩
  · exact Or.inl h0
  · exact Or.inr (Region.bounds hR).2.1

/-- A safe region, still safe once `NEXT` has grown and the spare capacity moved off it. -/
theorem Safe.mono {s u v : MachineState} {a : Word} {n : Nat} (h : Safe s u a n)
    (hn : heapNext u ≤ heapNext v)
    (hsp : Apart a n (spareLo v (s.getReg .x10)) (spareLen v (s.getReg .x10))) : Safe s v a n := by
  rcases h with h0 | ⟨hR, ho, hst, hnx, hh, -⟩
  · exact Or.inl h0
  · exact Or.inr ⟨hR, ho, hst, hnx, by omega, hsp⟩

/-- A pass keeps a claim whose regions are safe. -/
theorem claim_step {s u v : MachineState} {e : Word} {nx : Word} (hnx : nx.toNat ≤ heapEnd)
    (hf : DFrame u v (StepW s u nx))
    (h : ClaimRegions (Safe s u) u e) :
    stackClaimAt v e = stackClaimAt u e ∧ ClaimRegions (Safe s u) v e := by
  have he := h.1
  have hb : e.toNat + 88 ≤ 0xc0000000 := by
    rcases he.bound with h0 | h0
    · omega
    · exact h0
  refine claim_move (fun k hk ↦ hf _ fun i hi ↦ he.miss hnx _ (by addr_omega [hb, hk, hi])) h
    (fun a m hm ↦ hf.eList (fun x hx ↦ hm.miss hnx x hx) ?_) (fun _ _ h ↦ h) he
  rcases hm.bound with h0 | h0
  · left; omega
  · right; omega

/-! ## The invariant -/

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19),
  (48, .x20), (56, .x21), (64, .x22), (72, .x23), (80, .x24), (88, .x25), (96, .x26), (104, .x27)]

/-- What the function writes but its stack, `NEXT` and the heap. -/
def W (s : MachineState) (x : Word) : Prop :=
  Within x (s.getReg .x10) 24 ∨ Within x (s.getReg .x11) 8

/-- What the claims make: `onStackAt` on the layout's placements and stack size. -/
def onStackS (s : MachineState) : Model.LayoutMirror.ColumnClaimRust → Option StackClaimRust :=
  onStackAt (placementsAt s (placementsPtr s) (placementsLen s)) (stackLogAt s)

/-- The first `j` claims done, the registers the loop keeps. -/
structure Inv (s u : MachineState) (j : Nat) : Prop where
  p : PInv s u 240 extendStack slots [] (W s) (u.getMem nextAddr)
  x8 : u.getReg .x8 = s.getReg .x11
  x9 : u.getReg .x9 = s.getReg .x10
  x19 : u.getReg .x19 = itEnd s
  x20 : u.getReg .x20 = itLayout s
  x21 : u.getReg .x21 = s.getReg .x2 - 208
  x22 : u.getReg .x22 = 88
  x23 : u.getReg .x23 = 0xffffffffffffffff
  x24 : u.getReg .x24 = eqTag
  vec : VecOk u (s.getReg .x10) 88 8
  buf : vecLen u (s.getReg .x10) = vecCap u (s.getReg .x10) ∨
    NewBuf s u (vecPtr u (s.getReg .x10)) ((vecCap u (s.getReg .x10)).toNat * 88) 8
  safe : ∀ i < (vecLen u (s.getReg .x10)).toNat,
    ClaimRegions (Safe s u) u (vecPtr u (s.getReg .x10) + BitVec.ofNat 64 (88 * i))
  value : stackClaimsAt u (s.getReg .x10) = stackClaimsAt s (s.getReg .x10) ++
    (columnClaimsAt s (itCur s) j).filterMap (onStackS s)
  le : j ≤ itCount s

/-- A word of a region the function reads keeps its entry value. -/
theorem Inv.read {s u : MachineState} {j : Nat} (h : Inv s u j) {a : Word} {n : Nat}
    (hs : Src s extendStack a n) (ho : ExtendOff s a n) {p : Word} (h1 : a.toNat ≤ p.toNat)
    (h2 : p.toNat + 8 ≤ a.toNat + n) : u.getMem p = s.getMem p := by
  have hb : a.toNat + n ≤ 0xc0000000 := by
    rcases hs.bound with h0 | h0
    · omega
    · exact h0
  have hm := hs.miss (w := W s) (fun x hx hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hx, hw, ho.1, hb]
    · addr_omega [hx, hw, ho.2, hb]) h.p.fits
  exact h.p.mem.word (fun x hx ↦ hm x (by addr_omega [hx, h1, h2, hb])) (by omega)

theorem Inv.eList {s u : MachineState} {j : Nat} (h : Inv s u j) {a : Word} {m : Nat}
    (hs : Src s extendStack a (24 * m)) (ho : ExtendOff s a (24 * m)) :
    eListAt u a m = eListAt s a m := by
  have hm := hs.miss (w := W s) (fun x hx hw ↦ by
    have hb := hs.bound
    rcases hw with hw | hw
    · rcases hb with hb | hb
      · simp only [Within] at hx; omega
      · addr_omega [hx, hw, ho.1, hb]
    · rcases hb with hb | hb
      · simp only [Within] at hx; omega
      · addr_omega [hx, hw, ho.2, hb]) h.p.fits
  refine h.p.mem.eList hm ?_
  rcases hs.bound with h0 | h0
  · left; omega
  · right; omega

/-- The machine's `c * 24`. -/
theorem mul24 (c : Word) : c * 16 + c * 8 = BitVec.ofNat 64 (24 * c.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have h16 : (16 : Word).toNat = 16 := rfl
  have h8 : (8 : Word).toNat = 8 := rfl
  rw [h16, h8]
  omega

theorem placementsAt_getD (s : MachineState) (p : Word) {n c : Nat} (hc : c < n) :
    (placementsAt s p n).getD c none = placementAt s (p + BitVec.ofNat 64 (24 * c)) := by
  simp only [placementsAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hc, Option.map_some, Option.getD_some]

/-- A claim whose placement's tag has bit 0 clear is not on the stack. -/
theorem onStack_none (s : MachineState) {c : Model.LayoutMirror.ColumnClaimRust}
    (hc : c.column < placementsLen s)
    (h0 : s.getMem (placementsPtr s + BitVec.ofNat 64 (24 * c.column)) &&& 1 = 0) :
    onStackS s c = none := by
  simp only [onStackS, onStackAt, placementsAt_getD s _ hc, placementAt, h0, ite_true]

/-- One whose bit 0 is set is, at its placement's point. -/
theorem onStack_some (s : MachineState) {c : Model.LayoutMirror.ColumnClaimRust}
    (hc : c.column < placementsLen s)
    (h0 : s.getMem (placementsPtr s + BitVec.ofNat 64 (24 * c.column)) &&& 1 ≠ 0) :
    onStackS s c = some ⟨.eq ((⟨(s.getMem (placementsPtr s + BitVec.ofNat 64 (24 * c.column) + 8)).toNat,
      s.getMem (placementsPtr s + BitVec.ofNat 64 (24 * c.column) + 16)⟩ : Model.PlacementRust).stackPoint
        c.point (stackLogAt s)), c.value⟩ := by
  simp only [onStackS, onStackAt, placementsAt_getD s _ hc, placementAt, h0, ite_false]

end Rv64Verifier.Proofs.Pcs.Extend
