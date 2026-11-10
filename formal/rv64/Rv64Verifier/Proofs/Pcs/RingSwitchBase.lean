import Rv64Verifier.Proofs.Pcs.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.Transcript.Sponge
import Rv64Verifier.Blocks.F36

/-!
# `ring_switch`: the mirror's loops and the frame

```rust
pub fn ring_switch(point: Vec<E>, s: &[E], transcript: &mut Transcript) -> (E, RingWeight) {
    let challenges = transcript.samples(RING_MAP_SHIFTS.len());
    let coefficient = |k: usize| {
        let stages = challenges.iter().zip(RING_MAP_SHIFTS).filter(|&(_, shift)| k & shift != 0);
        stages.fold(ONE, |acc, (f, shift)| acc * f.pow(1 << (k % shift)))
    };
    let coefficients: Vec<E> = (0..K_BITS).map(coefficient).collect();
    let images: Vec<E> = s.iter().map(|&value| ring_map(value, &challenges)).collect();
    let target = poly_eval(&images, GEN);
    (target, RingWeight { point, coefficients })
}
```

compiled at `0x80009754` (`Blocks/F36.lean`), with `S` the entry's `sp` and `F = S - 464` the
frame: the prologue saves `ra`, `s0`..`s11` and `s` (`F + 16`) and calls `samples(F + 56, transcript,
6)`; `Bump::alloc(8, 1536)` gives the coefficients' buffer `C` (`Vec` at `F + 128`, then
`reserve(64)`, which returns at once). The coefficient loop (`0x8000986c`, `k` in `s10`) writes the
shifts at `F + 272`, `acc = 1` at `F + 152`, and runs the stages (`0x800098d4`, the shift pointer
in `s0`, the challenge in `s9`, the count down in `s5`): where `k & shift ≠ 0`, `pow(F + 216,
F + 336, 1 << (k % shift))` and `mul(F + 152, F + 176, F + 216)`; `0x8000982c` pushes `acc`. Then
`0x8000994c` moves the coefficients' `Vec` to `F + 152` and calls `try_allocate_in(F + 240,
s.len(), 0, 8, 24)` for the images' buffer `I` (`Vec` at `F + 216`, `reserve`, at once again); the
images loop (`0x80009a24`, `i` in `s10`) loads `s[i]` into `s9`, `s0`, `s2` and runs the six stages
(`0x80009a90`): `pow(F + 336, F + 176, 1 << shift)`, `mul(F + 176, challenge, F + 336)`, the value
`+=` it; `0x800099f4` pushes the value. `0x80009b00` calls `poly_eval(out, I, n, GEN)` and
`0x80009b20` moves `point` and the coefficients into the result, restores and returns.

This file: the mirror's loops as the machine runs them (`cacc`, `img`), and `Ph`, the frame
from a base state `B` on: `sp` fixed, memory changed only in `w`, the 1120 bytes below `sp`, `NEXT`
and the heap allocated since `B`.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs

/-! ## The mirror's loops -/

/-- A coefficient's stage: `acc * f^(2^(k % shift))` where `k & shift ≠ 0`. -/
def cstage (k : ℕ) (acc : E) (p : E × ℕ) : E :=
  if k &&& p.2 ≠ 0 then acc * p.1 ^ (2 ^ (k % p.2)) else acc

theorem foldl_filter (k : ℕ) : ∀ (l : List (E × ℕ)) (acc : E),
    (l.filter fun (_, shift) ↦ k &&& shift ≠ 0).foldl
      (fun acc (f, shift) ↦ acc * f ^ (2 ^ (k % shift))) acc = l.foldl (cstage k) acc
  | [], _ => rfl
  | (f, sh) :: l, acc => by
    by_cases h : k &&& sh = 0
    · simp only [List.filter_cons, h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.foldl_cons, cstage]
      exact foldl_filter k l acc
    · simp only [List.filter_cons, h, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
        List.foldl_cons, cstage]
      exact foldl_filter k l _

/-- Coefficient `k` after `j` stages. -/
def cacc (ch : List E) (k j : ℕ) : E := ((ch.zip ringMapShiftsRust).take j).foldl (cstage k) 1

theorem coeffs_length (ch : List E) : (ringCoefficientsRust ch).length = 64 := by
  simp [ringCoefficientsRust, kBitsRust]

theorem coeffs_getD (ch : List E) (k : ℕ) (hk : k < 64) :
    (ringCoefficientsRust ch).getD k 0 = cacc ch k 6 := by
  rw [List.getD_eq_getElem _ _ (by rw [coeffs_length]; exact hk)]
  simp only [ringCoefficientsRust, List.getElem_map, List.getElem_range, cacc]
  rw [foldl_filter, List.take_of_length_le (by simp [ringMapShiftsRust])]

theorem zip_length (ch : List E) (hch : ch.length = 6) : (ch.zip ringMapShiftsRust).length = 6 := by
  simp [hch, ringMapShiftsRust]

theorem zip_getElem (ch : List E) (hch : ch.length = 6) (j : ℕ) (hj : j < 6) :
    (ch.zip ringMapShiftsRust)[j]'(by rw [zip_length ch hch]; exact hj) =
      (ch.getD j 0, ringMapShiftsRust.getD j 0) := by
  rw [List.getElem_zip, List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by simp [ringMapShiftsRust]; omega)]

theorem cacc_succ (ch : List E) (hch : ch.length = 6) (k j : ℕ) (hj : j < 6) :
    cacc ch k (j + 1) = cstage k (cacc ch k j) (ch.getD j 0, ringMapShiftsRust.getD j 0) := by
  rw [cacc, List.take_succ_eq_append_getElem (by rw [zip_length ch hch]; exact hj),
    List.foldl_append, zip_getElem ch hch j hj]
  rfl

theorem cacc_zero (ch : List E) (k : ℕ) : cacc ch k 0 = 1 := rfl

/-- A value's stage in `ring_map`. -/
def istage (v : E) (p : E × ℕ) : E := v + p.1 * v ^ (2 ^ p.2)

/-- `ring_map` after `j` stages. -/
def img (ch : List E) (v : E) (j : ℕ) : E := ((ch.zip ringMapShiftsRust).take j).foldl istage v

theorem ringMap_eq (ch : List E) (v : E) : ringMapRust v ch = img ch v 6 := by
  rw [img, List.take_of_length_le (by simp [ringMapShiftsRust])]
  rfl

theorem img_succ (ch : List E) (hch : ch.length = 6) (v : E) (j : ℕ) (hj : j < 6) :
    img ch v (j + 1) = istage (img ch v j) (ch.getD j 0, ringMapShiftsRust.getD j 0) := by
  rw [img, List.take_succ_eq_append_getElem (by rw [zip_length ch hch]; exact hj),
    List.foldl_append, zip_getElem ch hch j hj]
  rfl

theorem img_zero (ch : List E) (v : E) : img ch v 0 = v := rfl

/-- The shift of stage `j`, as stored at `F + 272 + 8 j`. -/
def shiftW (j : ℕ) : Word := BitVec.ofNat 64 (ringMapShiftsRust.getD j 0)

theorem shift_cases (j : ℕ) (hj : j < 6) :
    (ringMapShiftsRust.getD j 0 = 32 ∧ shiftW j = 32) ∨ (ringMapShiftsRust.getD j 0 = 16 ∧ shiftW j = 16) ∨
    (ringMapShiftsRust.getD j 0 = 8 ∧ shiftW j = 8) ∨ (ringMapShiftsRust.getD j 0 = 4 ∧ shiftW j = 4) ∨
    (ringMapShiftsRust.getD j 0 = 2 ∧ shiftW j = 2) ∨ (ringMapShiftsRust.getD j 0 = 1 ∧ shiftW j = 1) := by
  interval_cases j <;> simp [shiftW, ringMapShiftsRust]

theorem shift_toNat (j : ℕ) (hj : j < 6) : (shiftW j).toNat = ringMapShiftsRust.getD j 0 := by
  rcases shift_cases j hj with h | h | h | h | h | h <;> rw [h.1, h.2] <;> rfl

theorem shift_pos (j : ℕ) (hj : j < 6) :
    0 < ringMapShiftsRust.getD j 0 ∧ ringMapShiftsRust.getD j 0 ≤ 32 := by
  rcases shift_cases j hj with h | h | h | h | h | h <;> rw [h.1] <;> decide

/-- `1 << n` for `n < 64`. -/
theorem one_shl (n : Nat) (hn : n < 64) : ((1 : Word) <<< (n % 64)).toNat = 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hn, show (1 : Word).toNat = 1 from rfl,
    Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hn)

/-! ## The frame from a base state on -/

/-- From `B` on: `sp` as `B`'s, memory changed only in `Wr B 1120 w nx`, `NEXT = nx`. -/
structure Ph (B u : MachineState) (w : Word → Prop) (nx : Word) : Prop where
  sp : u.getReg .x2 = B.getReg .x2
  mem : DFrame B u (Wr B 1120 w nx)
  next : u.getMem nextAddr = nx
  mono : heapNext B ≤ nx.toNat
  fits : nx.toNat ≤ heapEnd

theorem Ph.refl {B : MachineState} (hB : HeapOk B) (w : Word → Prop) : Ph B B w (B.getMem nextAddr) :=
  ⟨rfl, DFrame.refl _ _, rfl, Nat.le_refl _, hB.hi⟩

theorem Ph.step {B u v : MachineState} {w X : Word → Prop} {nx nx' : Word} (h : Ph B u w nx)
    (hX : DFrame u v X) (hXsub : ∀ a, X a → Wr B 1120 w nx' a)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) : Ph B v w nx' :=
  ⟨hsp.trans h.sp, (h.mem.mono fun _ ha ↦ ha.mono hle).trans hX hXsub, hnx,
    Nat.le_trans h.mono hle, hend⟩

theorem Ph.same {B u v : MachineState} {w : Word → Prop} {nx : Word} (h : Ph B u w nx)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2) : Ph B v w nx :=
  ⟨hsp.trans h.sp, h.mem.trans (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim),
    (hm _).trans h.next, h.mono, h.fits⟩

theorem Ph.heap {B u : MachineState} {w : Word → Prop} {nx : Word} (h : Ph B u w nx)
    (hB : HeapOk B) : HeapOk u := by
  have hn : heapNext u = nx.toNat := by simp only [heapNext, h.next]
  exact ⟨by rw [hn]; exact Nat.le_trans hB.lo h.mono, by rw [hn]; exact h.fits⟩

/-- A byte outside `w`, the stack below `sp`, `NEXT` and the free heap is not written. -/
theorem Ph.miss {B u : MachineState} {w : Word → Prop} {nx : Word} (h : Ph B u w nx) {x : Word}
    (hw : ¬ w x) (hst : ¬ Within x (stackLo B 1120) 1120) (hn : ¬ Within x nextAddr 8)
    (hf : x.toNat < heapNext B ∨ heapEnd ≤ x.toNat) : ¬ Wr B 1120 w nx x := by
  have := h.fits
  rintro (h1 | h1 | h1 | h1)
  · exact hw h1
  · exact hst h1
  · exact hn h1
  · omega

theorem Ph.rodata {B u : MachineState} {w : Word → Prop} {nx : Word} (h : Ph B u w nx)
    (hro : RodataOk B) (hw : ∀ a, w a → ¬ Within a rodataBase Rv64Verifier.rodataSize)
    (hst : Apart (stackLo B 1120) 1120 rodataBase Rv64Verifier.rodataSize) : RodataOk u := by
  have hfit := h.fits
  refine hro.dframe h.mem fun a ha hW ↦ ?_
  rcases hW with hW | hW | hW | hW
  · exact hw a hW ha
  · addr_omega [ha, hW, hst]
  · addr_omega [ha, hW]
  · addr_omega [ha, hW.2, hfit]

/-- The transcript at `p` across a frame that misses it and the proof's bytes. -/
theorem transcriptAt_frame {s t : MachineState} {W : Word → Prop} (hf : DFrame s t W) {p : Word}
    {T : Model.TState} (h : TranscriptAt s p T) (hok : TranscriptOk s p)
    (hp : ∀ x, Within x p transcriptSize → ¬ W x) (hq : ∀ x, Within x (proofAt s p) 48 → ¬ W x)
    (hb : ∀ x, Within x (streamPtr s p) (24 * streamLen s p) → ¬ W x) : TranscriptAt t p T := by
  have hP := Region.bounds hok.self
  have hQ := Region.bounds hok.proof
  have hp' : ∀ i < 8, ¬ W (p + BitVec.ofNat 64 i) := fun i hi ↦ hp _ (by addr_omega [hP, hi])
  have hq' : ∀ i < 48, ¬ W (proofAt s p + BitVec.ofNat 64 i) := fun i hi ↦
    hq _ (by addr_omega [hQ, hi])
  have hb' : ∀ i < 24 * streamLen s p, ¬ W (streamPtr s p + BitVec.ofNat 64 i) := by
    intro i hi
    rcases hok.stream with h0 | hR
    · omega
    · have := Region.bounds hR; exact hb _ (by addr_omega [this, hi])
  have hw (x : Word) (h1 : p.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ p.toNat + transcriptSize) :
      t.getMem x = s.getMem x :=
    hf x fun i hi ↦ hp _ (by simp only [transcriptSize] at h2 ⊢; addr_omega [hP, hi, h1, h2])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf.eListAt_stream hp' hq' hb']; exact h.stream
  · rw [spongeAt_congr (by addr_omega [hP]) fun x h1 h2 ↦ hw x (by addr_omega [hP, h1])
      (by simp only [transcriptSize]; addr_omega [hP, h2])]
    exact h.sponge
  · rw [hw _ (by addr_omega [hP]) (by simp only [transcriptSize]; addr_omega [hP])]
    exact h.streamOffset
  · rw [hw _ (by addr_omega [hP]) (by simp only [transcriptSize]; addr_omega [hP])]
    exact h.openingOffset

/-- A transcript the machine's stands for: the statement's state read off memory. -/
theorem exists_T (s : MachineState) (p : Word) : ∃ T, TranscriptAt s p T :=
  ⟨⟨⟨eListAt s (streamPtr s p) (streamLen s p), []⟩, spongeAt s (p + 8),
    (s.getMem (p + 344)).toNat, (s.getMem (p + 352)).toNat, []⟩, rfl, rfl, rfl, rfl⟩

/-! ## Bounds -/

/-- `sp` above `.rodata` and `NEXT` by the whole stack. -/
theorem bounds {s : MachineState} (h : RingSwitchPre s) :
    0xa0000f38 + 1584 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hn := h.stack.next
  have hr := h.stack.rodata
  have ha := h.stack.aligned
  simp only [ringSwitchStack, MultilinearContracts.polyEvalStack, mulStack] at hm hn hr
  refine ⟨?_, ?_, ha⟩ <;> addr_omega [hm, hn, hr]

end Rv64Verifier.Proofs.Pcs.RingSwitch
