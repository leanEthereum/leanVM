import Rv64Verifier.Proofs.Transcript.Repr

/-!
# The sponge read back

`spongeAt` against the statement's sponge: the rate lanes of the waiting scalars are the
doublewords they occupy (`pendingLanes_pendingAt`), so a buffer holding those doublewords, zeros up
to lane `16`, and the state's capacity is `duplexInput` (`stateAt_eq_duplexInput`).
-/

namespace Rv64Verifier.Transcript
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model

theorem ofNat_add_ofNat (a : Word) {k i m : Nat} (h : k + i = m) :
    a + BitVec.ofNat 64 k + BitVec.ofNat 64 i = a + BitVec.ofNat 64 m := by
  rw [add_ofNat_add, h]

theorem lane_limb0 (s : MachineState) (p : Word) :
    ((eAt s p).limb 0).lane = UInt64.ofBitVec (s.getMem p) := rfl

theorem lane_limb1 (s : MachineState) (p : Word) :
    ((eAt s p).limb 1).lane = UInt64.ofBitVec (s.getMem (p + 8)) := rfl

theorem lane_limb2 (s : MachineState) (p : Word) :
    ((eAt s p).limb 2).lane = UInt64.ofBitVec (s.getMem (p + 16)) := rfl

theorem toUInt64_toNat (w : Word) : w.toNat.toUInt64 = UInt64.ofBitVec w := by
  apply UInt64.toBitVec_inj.mp
  simp

/-- The rate lanes of the waiting scalars are the doublewords they occupy. -/
theorem pendingLanes_pendingAt (s : MachineState) (a : Word) (n : Nat) :
    pendingLanes (pendingAt s a n) =
      (List.range (4 * n)).map fun j ↦ UInt64.ofBitVec (s.getMem (a + BitVec.ofNat 64 (8 * j))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : pendingAt s a (n + 1) = pendingAt s a n ++
        [(eAt s (a + BitVec.ofNat 64 (32 * n)),
          (s.getMem (a + BitVec.ofNat 64 (32 * n + 24))).toNat)] := by
      simp only [pendingAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    have hr : List.range (4 * (n + 1)) =
        List.range (4 * n) ++ [4 * n, 4 * n + 1, 4 * n + 2, 4 * n + 3] := by
      rw [show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by omega, List.range_succ, List.range_succ,
        List.range_succ, List.range_succ]
      simp
    rw [hp, pendingLanes, List.flatMap_append, ← pendingLanes, ih, hr, List.map_append]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
      lane_limb0, lane_limb1, lane_limb2, toUInt64_toNat]
    have e (k : Nat) (hk : k < 4) : a + BitVec.ofNat 64 (32 * n) + BitVec.ofNat 64 (8 * k) =
        a + BitVec.ofNat 64 (8 * (4 * n + k)) := ofNat_add_ofNat a (by omega)
    have e1 := e 1 (by decide)
    have e2 := e 2 (by decide)
    have e3 : a + BitVec.ofNat 64 (32 * n + 24) = a + BitVec.ofNat 64 (8 * (4 * n + 3)) := by
      congr 2; omega
    have e0 : a + BitVec.ofNat 64 (32 * n) = a + BitVec.ofNat 64 (8 * (4 * n)) := by
      congr 2; omega
    simp only [Nat.mul_one, Nat.reduceMul] at e1 e2
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, show (16 : Word) = BitVec.ofNat 64 16 from rfl,
      e1, e2, e3, e0]

theorem getD_map_range {α : Type} (f : Nat → α) (n j : Nat) (d : α) :
    ((List.range n).map f).getD j d = if j < n then f j else d := by
  by_cases h : j < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem lane_stateAt (s : MachineState) (a : Word) {j : Nat} (hj : j < 25) :
    Keccak.lane (stateAt s a) j = UInt64.ofBitVec (s.getMem (a + BitVec.ofNat 64 (8 * j))) := by
  simp [Keccak.lane, stateAt, hj]

/-- A buffer of the waiting scalars' doublewords, zeros up to lane `16`, and the capacity is the
permutation's input. -/
theorem stateAt_eq_duplexInput {s u : MachineState} {a b : Word} (hn : nPending s a ≤ 4)
    (h : ∀ j < 25, u.getMem (b + BitVec.ofNat 64 (8 * j)) =
      if j < 4 * nPending s a then s.getMem (a + BitVec.ofNat 64 (8 * j))
      else if j < 16 then 0 else s.getMem (a + 128 + BitVec.ofNat 64 (8 * j))) :
    stateAt u b = duplexInput (spongeAt s a) := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, duplexInput, spongeAt, Vector.getElem_ofFn, pendingLanes_pendingAt,
    getD_map_range]
  rw [h j hj]
  by_cases h1 : j < 4 * nPending s a
  · simp only [h1, ↓reduceIte, show j < 16 by omega]
  · by_cases h2 : j < 16
    · simp only [h1, h2, ↓reduceIte]
      rfl
    · simp only [h1, h2, ↓reduceIte]
      simp [Keccak.lane, hj]

/-- A sponge with no scalar waiting. -/
theorem spongeAt_of_empty {t : MachineState} {a : Word} (h : t.getMem (a + 328) = 0) :
    spongeAt t a = ⟨stateAt t (a + 128), []⟩ := by
  simp only [spongeAt, nPending, h]
  rfl

theorem stateAt_congr {t t' : MachineState} {x y : Word}
    (h : ∀ j < 25, t.getMem (x + BitVec.ofNat 64 (8 * j)) = t'.getMem (y + BitVec.ofNat 64 (8 * j))) :
    stateAt t x = stateAt t' y := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn]
  rw [h j hj]

theorem pendingAt_length (s : MachineState) (a : Word) (n : Nat) : (pendingAt s a n).length = n := by
  simp [pendingAt]

/-- The first `n` waiting scalars are read from their doublewords. -/
theorem pendingAt_congr {s t : MachineState} {a : Word} {n : Nat} (ha : a.toNat + 32 * n ≤ 2 ^ 64)
    (h : ∀ x : Word, a.toNat ≤ x.toNat → x.toNat + 8 ≤ a.toNat + 32 * n → t.getMem x = s.getMem x) :
    pendingAt t a n = pendingAt s a n := by
  simp only [pendingAt]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have e (k : Nat) (hk : k < 4) : t.getMem (a + BitVec.ofNat 64 (32 * i + 8 * k)) =
      s.getMem (a + BitVec.ofNat 64 (32 * i + 8 * k)) :=
    h _ (by addr_omega [ha, hi, hk]) (by addr_omega [ha, hi, hk])
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2 e3
  unfold Rv64Verifier.eAt
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, show (16 : Word) = BitVec.ofNat 64 16 from rfl,
    add_ofNat_add, add_ofNat_add, e0, e1, e2, e3]

/-- The sponge is read from its doublewords. -/
theorem spongeAt_congr {s t : MachineState} {a : Word} (ha : a.toNat + 336 ≤ 2 ^ 64)
    (h : ∀ x : Word, a.toNat ≤ x.toNat → x.toNat + 8 ≤ a.toNat + 336 → t.getMem x = s.getMem x) :
    spongeAt t a = spongeAt s a := by
  have hn : nPending t a = nPending s a := by
    simp only [nPending]; rw [h _ (by addr_omega [ha]) (by addr_omega [ha])]
  have h4 : nPending s a ≤ 4 := by unfold nPending; omega
  have hs : stateAt t (a + 128) = stateAt s (a + 128) :=
    stateAt_congr fun j hj ↦ h _ (by addr_omega [ha, hj]) (by addr_omega [ha, hj])
  have hp : pendingAt t a (nPending s a) = pendingAt s a (nPending s a) :=
    pendingAt_congr (by omega) fun x h1 h2 ↦ h x h1 (by omega)
  unfold spongeAt
  rw [hn, hs, hp]

/-- Pushing a scalar onto the queue. -/
theorem spongeAt_push {u t : MachineState} {a : Word} {x : E} {tag : ℕ}
    (ha : a.toNat + 336 ≤ 2 ^ 64) (hn : (u.getMem (a + 328)).toNat < 4)
    (hcnt : (t.getMem (a + 328)).toNat = (u.getMem (a + 328)).toNat + 1)
    (hx : eAt t (a + BitVec.ofNat 64 (32 * (u.getMem (a + 328)).toNat)) = x)
    (htag : (t.getMem (a + BitVec.ofNat 64 (32 * (u.getMem (a + 328)).toNat + 24))).toNat = tag)
    (hf : ∀ y : Word, a.toNat ≤ y.toNat →
      (y.toNat + 8 ≤ a.toNat + 32 * (u.getMem (a + 328)).toNat ∨
        (a.toNat + 128 ≤ y.toNat ∧ y.toNat + 8 ≤ a.toNat + 328)) → t.getMem y = u.getMem y) :
    spongeAt t a = { spongeAt u a with pending := (spongeAt u a).pending ++ [(x, tag)] } := by
  generalize hN : (u.getMem (a + 328)).toNat = n at hn hcnt hx htag hf
  have hu : nPending u a = n := by unfold nPending; omega
  have ht : nPending t a = n + 1 := by unfold nPending; omega
  have hs : stateAt t (a + 128) = stateAt u (a + 128) := stateAt_congr fun j hj ↦
    hf _ (by addr_omega [ha, hj]) (Or.inr ⟨by addr_omega [ha, hj], by addr_omega [ha, hj]⟩)
  have hp : pendingAt t a (n + 1) = pendingAt u a n ++ [(x, tag)] := by
    rw [pendingAt, List.range_succ, List.map_append, ← pendingAt,
      pendingAt_congr (by omega) fun y h1 h2 ↦ hf y h1 (Or.inl h2)]
    simp only [List.map_cons, List.map_nil, hx, htag]
  unfold spongeAt
  rw [hu, ht, hs, hp]

/-- Absorbing pushes onto the queue, after a permutation if it is full. -/
theorem spAbsorb_eq (sp : Sponge) (x : E) (tag : ℕ) :
    spAbsorb sp x tag =
      { (if sp.pending.length = 4 then spDuplex sp else sp) with
        pending := (if sp.pending.length = 4 then spDuplex sp else sp).pending ++ [(x, tag)] } := by
  unfold spAbsorb absorb spDuplex rateScalars
  split <;> rfl

theorem nPending_of_nil {t : MachineState} {a : Word} (h : (spongeAt t a).pending = []) :
    nPending t a = 0 := by
  have := congrArg List.length h
  simpa [spongeAt, pendingAt_length] using this

end Rv64Verifier.Transcript
