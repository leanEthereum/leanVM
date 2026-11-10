import Rv64Verifier.Proofs.Bus.VbbTail26

/-!
# `verify_bus_balance` past the GKR loop: the side loop's invariant

The side loop (`0x800074e0`, three iterations) folds `sideF` over the sides (`accAt`). At its head
for side `i` (`Sides`) memory is the loop entry's (`h₀`) but for `LoopW`, the frame's slots the loop
writes and the heap allocated from `z` on; the forms' rows at `P` are a matrix (`Mat`) holding the
fold's forms, every form's pointer below `NEXT` (`below`), and `S - 632` holds the fold's totals.
`SideStage` is one iteration, `FinalStage` the stores past the last one and the return, `SidesEntry`
the way in (`restToSides` with the empty buffers' pointers, `Ptrs`); `restStage` composes them.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-! ## The fold -/

/-- The sides, as `tailValue` lists them. -/
def sidesOf (s : MachineState) (k : Start) (state : GkrState) (mem : List E) (mf bf bv : E) :
    List (List BusBlock × BusLayoutRust × List E × List E × E) :=
  let layout := busLayoutAt s (s.getReg .x11)
  let point := state.point
  let weights := eqKernelRust k.alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memoryIndex := indexMleRust memoryLow
  let bytecodeIndex := indexMleRust bytecodeLow
  let fingerprints := fun (pc memoryCount bytecodeCount : E) ↦
    [dotRust (weights.take 3) [sepStateRust, pc, gpowRust 0#64],
      dotRust (weights.take 6) [sepMemRust, memoryIndex, memoryCount, mem.getD 0 0,
        mem.getD 1 0, mem.getD 2 0],
      dotRust (weights.take 3) [sepBytecodeRust, bytecodeIndex, bytecodeCount] + bv]
  let finalPc := gpowRust ((1#64 <<< (layout.logBytecode % 64)) - 1#64)
  [(layout.push, busLayoutRust [0, layout.logMemory, layout.logBytecode] layout.push,
      fingerprints (gpowRust 0#64) 1 1, weights, k.beta),
    (layout.pull, busLayoutRust [0, layout.logMemory, layout.logBytecode] layout.pull,
      fingerprints finalPc mf bf, weights, k.beta),
    (layout.count, busLayoutRust [] layout.count, [], [1], 0)]

/-- One side of the fold: its forms, its total appended. -/
def sideF (point treeValues : List E) (acc : List (List Form) × List E)
    (sd : (List BusBlock × BusLayoutRust × List E × List E × E) × ℕ) :
    List (List Form) × List E :=
  let side := sideStepRust point treeValues acc.1 sd.2 sd.1.1 sd.1.2.1 sd.1.2.2.1 sd.1.2.2.2.1
    sd.1.2.2.2.2
  (side.1, acc.2 ++ [side.2])

/-- The fold after `i` sides. -/
def accAt (s : MachineState) (k : Start) (state : GkrState) (mem : List E) (mf bf bv : E) (i : ℕ) :
    List (List Form) × List E :=
  ((sidesOf s k state mem mf bf bv).zipIdx.take i).foldl (sideF state.point state.values)
    (List.replicate tables.length (List.replicate 3 {}), [])

theorem restValue_forms (s : MachineState) (k : Start) (state : GkrState) (mem : List E)
    (mf bf bv : E) :
    (restValue s k state mem mf bf bv).forms = (accAt s k state mem mf bf bv 3).1 := rfl

theorem restValue_totals (s : MachineState) (k : Start) (state : GkrState) (mem : List E)
    (mf bf bv : E) :
    (restValue s k state mem mf bf bv).totals = (accAt s k state mem mf bf bv 3).2 := rfl

theorem accAt_succ (s : MachineState) (k : Start) (state : GkrState) (mem : List E) (mf bf bv : E)
    {i : ℕ} (hi : i < 3) :
    accAt s k state mem mf bf bv (i + 1) = sideF state.point state.values
      (accAt s k state mem mf bf bv i) ((sidesOf s k state mem mf bf bv).getD i ([], ⟨0, [], []⟩, [], [], 0), i) := by
  interval_cases i <;> rfl

/-! ## The matrix under a step that keeps the heap -/

/-- A step that keeps every doubleword of the heap allocated from `b` on keeps the matrix, its rows'
headers and its forms' headers. -/
theorem Mat.keep {b t t' : MachineState} {P : Word} {n : Nat} (M : Mat b t P n) (hheap : HeapOk t)
    (hm : heapNext t ≤ heapNext t') (hPb : n = 0 ∨ heapNext b ≤ P.toNat)
    (hw : ∀ x : Word, heapNext b ≤ x.toNat → x.toNat + 8 ≤ heapNext t →
      t'.getMem x = t.getMem x) :
    Mat b t' P n ∧ (∀ i < n, ∀ k < 3, t'.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) =
      t.getMem (rowAt P i + BitVec.ofNat 64 (8 * k))) ∧
      (∀ i < n, ∀ j < 3, ∀ k < 3,
        t'.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) =
          t.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k))) ∧
      ∀ i < n, ∀ j < 3,
        Layout.formOf t' (cellAt t (rowAt P i) j) = Layout.formOf t (cellAt t (rowAt P i) j) := by
  have hnt := hheap.hi
  have hbt := M.mono
  simp only [heapNext, heapEnd] at hnt hbt hm
  have hP (hn : 0 < n) : heapNext b ≤ P.toNat ∧ P.toNat + 24 * n ≤ heapNext t := by
    rcases M.hdr.2 with h0 | h0
    · omega
    · exact ⟨hPb.resolve_left (by omega), h0.2⟩
  simp only [heapNext] at hP
  have rb (i : Nat) (hi : i < n) : 3 ≤ (vecCap t (rowAt P i)).toNat ∧
      heapStart ≤ (vecPtr t (rowAt P i)).toNat ∧
      (vecPtr t (rowAt P i)).toNat + 24 * (vecCap t (rowAt P i)).toNat ≤ heapNext t := by
    obtain ⟨hv, hl⟩ := M.rows i hi
    have hc := hv.len
    rw [hl] at hc
    have e3 : (3 : Word).toNat = 3 := rfl
    have hraw := hv.raw
    simp only [RawVecOk, Buf] at hraw
    refine ⟨by omega, ?_⟩
    rcases hraw.2 with h0 | h0
    · omega
    · exact ⟨h0.1, by omega⟩
  have hrow (i : Nat) (hi : i < n) (k : Nat) (hk : k < 3) :
      t'.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) =
        t.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) := by
    obtain ⟨p1, p2⟩ := hP (by omega)
    exact hw _ (by simp only [rowAt, heapNext] at p1 ⊢; addr_omega [p1, p2, hi, hk, hnt])
      (by simp only [rowAt, heapNext] at p2 ⊢; addr_omega [p1, p2, hi, hk, hnt])
  have hptr (i : Nat) (hi : i < n) : vecPtr t' (rowAt P i) = vecPtr t (rowAt P i) := by
    have h := hrow i hi 1 (by omega)
    simp only [Nat.mul_one] at h
    exact h
  have hcap (i : Nat) (hi : i < n) : vecCap t' (rowAt P i) = vecCap t (rowAt P i) := by
    have h := hrow i hi 0 (by omega)
    simp only [Nat.mul_zero, add_ofNat_zero] at h
    exact h
  have hlen (i : Nat) (hi : i < n) : vecLen t' (rowAt P i) = vecLen t (rowAt P i) := by
    have h := hrow i hi 2 (by omega)
    simp only [show 8 * 2 = 16 from rfl] at h
    exact h
  have hcellAt (i : Nat) (hi : i < n) (j : Nat) :
      cellAt t' (rowAt P i) j = cellAt t (rowAt P i) j := by
    simp only [cellAt, hptr i hi]
  have inRow (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (x : Word)
      (h : Within x (cellAt t (rowAt P i) j) 24) : piece t P i 3 x := by
    rw [piece_row]
    obtain ⟨c3, l, u⟩ := rb i hi
    simp only [Layout.formVecBuf, cellAt, Within] at h ⊢
    addr_omega [h, c3, l, u, hj, hnt]
  have hcellw (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) (k : Nat) (hk : k < 3) :
      t'.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) =
        t.getMem (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) := by
    obtain ⟨c3, l, u⟩ := rb i hi
    simp only [heapStart, heapNext] at l u
    have hcw : (cellAt t (rowAt P i) j).toNat + 24 ≤ (vecPtr t (rowAt P i)).toNat +
        24 * (vecCap t (rowAt P i)).toNat := by simp only [cellAt]; addr_omega [c3, l, u, hj, hnt]
    have hx := M.fresh i hi 3 (le_refl _) _
      (inRow i hi j hj (cellAt t (rowAt P i) j + BitVec.ofNat 64 (8 * k)) (by
      simp only [Within, cellAt] at hcw ⊢; addr_omega [hcw, c3, l, u, hj, hk, hnt]))
    exact hw _ hx (by simp only [cellAt, heapNext] at hcw ⊢; addr_omega [hcw, c3, l, u, hj, hk, hnt])
  have hfr : DFrame t t' fun a ↦ ¬ (heapNext b ≤ a.toNat ∧ a.toNat < heapNext t) := by
    intro a ha
    have h0 := ha 0 (by decide)
    have h7 := ha 7 (by decide)
    simp only [not_not] at h0 h7
    rw [add_ofNat_zero] at h0
    exact hw a h0.1 (by simp only [heapNext] at h0 h7 ⊢; addr_omega [h0, h7, hnt])
  have pe (i : Nat) (hi : i < n) (j : Nat) (hj : j ≤ 3) (x : Word) :
      piece t' P i j x ↔ piece t P i j x := by
    rcases Nat.lt_or_ge j 3 with h3 | h3
    · rw [piece_form h3, piece_form h3, hcellAt i hi j]
      have e0 := hcellw i hi j h3 0 (by omega)
      have e8 := hcellw i hi j h3 1 (by omega)
      simp only [Nat.mul_zero, Nat.mul_one, add_ofNat_zero] at e0 e8
      simp only [Layout.formBuf, vecPtr, vecCap]
      rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, e0, e8]
    · obtain rfl : j = 3 := by omega
      rw [piece_row, piece_row]
      simp only [Layout.formVecBuf, hptr i hi, hcap i hi]
  have hm' : heapNext t ≤ heapNext t' := by simp only [heapNext]; omega
  have fo (i : Nat) (hi : i < n) (j : Nat) (hj : j < 3) :
      Layout.formOf t' (cellAt t (rowAt P i) j) = Layout.formOf t (cellAt t (rowAt P i) j) ∧
        Layout.FormOk t' (cellAt t (rowAt P i) j) := by
    have hok := M.forms i hi j hj
    have hcw : (cellAt t (rowAt P i) j).toNat + 24 ≤ 2 ^ 64 := by
      obtain ⟨c3, l, u⟩ := rb i hi
      simp only [heapNext] at u
      simp only [cellAt]; addr_omega [c3, l, u, hj, hnt]
    refine Layout.formOf_frame (toLayoutFrame hfr) hok (fun x hx hx' ↦ hx' ?_)
      (fun x hx hx' ↦ hx' ⟨M.fresh i hi j hj.le x ((piece_form hj).mpr hx),
        (M.below hi hj.le ((piece_form hj).mpr hx)).2⟩) hcw hheap hm'
    have hr := inRow i hi j hj x hx
    exact ⟨M.fresh i hi 3 (le_refl _) x hr, (M.below hi (le_refl _) hr).2⟩
  refine ⟨⟨by simp only [heapNext]; omega, ⟨M.hdr.1, M.hdr.2.imp id fun h ↦ ⟨h.1, by omega⟩⟩,
    fun i hi ↦ ⟨(M.rows i hi).1.keep (hcap i hi) (hptr i hi) (hlen i hi) hm',
      (hlen i hi).trans (M.rows i hi).2⟩,
    fun i hi j hj ↦ by rw [hcellAt i hi j]; exact (fo i hi j hj).2,
    fun i hi j hj x hx ↦ M.fresh i hi j hj x ((pe i hi j hj x).mp hx),
    fun i hi j hj i' hi' j' hj' hne x hx hx' ↦
      M.apart i hi j hj i' hi' j' hj' hne x ((pe i hi j hj x).mp hx) ((pe i' hi' j' hj' x).mp hx'),
    fun i hi j hj x hx ↦ M.outer i hi j hj x ((pe i hi j hj x).mp hx)⟩, hrow, hcellw,
    fun i hi j hj ↦ (fo i hi j hj).1⟩

/-! ## The invariant -/

/-- What the side loop writes from its entry on: the frame's slots `sp + [40, 64)`, `+ 72`, `+ 80`,
`+ 96`, `+ [128, 200)`, `+ [208, 240)`, `+ [712, 736)` (`totals`), `+ [1024, 1240)`, and the heap
allocated from `z` on. -/
def LoopW (s z : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1304) 24 ∨ Within a (s.getReg .x2 - 1272) 16 ∨
    Within a (s.getReg .x2 - 1248) 8 ∨ Within a (s.getReg .x2 - 1216) 72 ∨
    Within a (s.getReg .x2 - 1136) 32 ∨ Within a (s.getReg .x2 - 632) 24 ∨
    Within a (s.getReg .x2 - 320) 216 ∨ (heapNext z ≤ a.toNat ∧ a.toNat < heapEnd)

/-- Empty buffers' pointers lie below `NEXT` too (beyond `NewBuf`, which says nothing of them):
the point's at `z`, each claim's point's at `z`, each form's of the forms' rows at `v`. -/
structure Ptrs (s z v : MachineState) (P : Word) (n : Nat) : Prop where
  point : (z.getMem (s.getReg .x2 - 1256)).toNat + 24 * (z.getMem (s.getReg .x2 - 1144)).toNat ≤
    heapNext z
  claims : ∀ i < 5,
    (vecPtr z (z.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (56 * i))).toNat +
      24 * (vecLen z (z.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (56 * i))).toNat ≤ heapNext z
  forms : ∀ i < n, ∀ j < 3, (vecPtr v (cellAt v (rowAt P i) j)).toNat ≤ heapNext v

/-- What holds at the side loop's entry `h₀`: the stages before it, and `Ptrs`. -/
structure SCtx (bev : MachineState → Word → List E → Option E) (s z w v h₀ : MachineState)
    (k : Start) (state : GkrState) (mem : List E) (mf bf bv : E) : Prop where
  fps : Fps bev s z k state mem mf bf bv
  rows0 : Rows0 s z w
  rows1 : Rows1 s z w v
  kept : Kept2 s v k
  setup : Setup s v h₀
  ptrs : Ptrs s z v (w.getReg .x23) (w.getReg .x25).toNat
  vlen : state.values.length = 3

/-- At the side loop's head (or past its last iteration), the fold `acc` done. -/
structure Sides (s z h₀ h : MachineState) (P : Word) (n : Nat)
    (acc : List (List Form) × List E) : Prop where
  inv : Inv s h
  step : StepS s h₀ h (LoopW s z)
  mat : Mat z h P n
  below : ∀ i < n, ∀ j < 3, (vecPtr h (cellAt h (rowAt P i) j)).toNat +
    48 * (vecLen h (cellAt h (rowAt P i) j)).toNat ≤ heapNext h
  forms : formRowsAt h P n = acc.1
  totals : NewVecE z h (s.getReg .x2 - 632) acc.2
  x25 : h.getReg .x25 = h₀.getReg .x25
  x27 : h.getReg .x27 = h₀.getReg .x27
  tbuf : ∀ x, Within x (vecPtr h (s.getReg .x2 - 632)) (24 * (vecCap h (s.getReg .x2 - 632)).toNat) →
    ¬ Within x P (24 * n) ∧ ∀ a < n, ∀ j ≤ 3, ¬ piece h P a j x

/-- One iteration of the side loop: to the next side's head, past the last one to `0x80007c2c`, or
a dead end. -/
def SideStage (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s z w v h₀ h k state mem mf bf bv (i : Nat), BusBalancePre s →
    SCtx bev s z w v h₀ k state mem mf bf bv → i < 3 → h.pc = 0x800074e0 →
    h.getReg .x22 = BitVec.ofNat 64 i →
    Sides s z h₀ h (w.getReg .x23) (w.getReg .x25).toNat (accAt s k state mem mf bf bv i) →
    ∃ h', Reaches Image.code h h' ∧ (Dead Image.code h' ∨
      Sides s z h₀ h' (w.getReg .x23) (w.getReg .x25).toNat (accAt s k state mem mf bf bv (i + 1)) ∧
        ((i + 1 < 3 ∧ h'.pc = 0x800074e0 ∧ h'.getReg .x22 = BitVec.ofNat 64 (i + 1)) ∨
          (i + 1 = 3 ∧ h'.pc = 0x80007c2c)))

/-- Past the last side: the result's stores and the return. -/
def FinalStage (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s z w v h₀ h k state mem mf bf bv, BusBalancePre s →
    SCtx bev s z w v h₀ k state mem mf bf bv → h.pc = 0x80007c2c →
    Sides s z h₀ h (w.getReg .x23) (w.getReg .x25).toNat (accAt s k state mem mf bf bv 3) →
    ∃ t, Reaches Image.code h t ∧ Done bev s t

/-- From `0x80006ca0` to the side loop's entry, with `Ptrs`. -/
def SidesEntry (BcOk : MachineState → Nat → Word → Prop)
    (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s q k state mem mf bf, BusBalancePre s →
    BcOk s busBalanceStack (bytecodeOf s (s.getReg .x11)) → Scalars bev s q k state mem mf bf →
    q.pc = 0x80006ca0 → ∃ h, Reaches Image.code q h ∧ (Done bev s h ∨ Dead Image.code h ∨
      ∃ z w v bv, SCtx bev s z w v h k state mem mf bf bv ∧ h.pc = 0x800074e0)

/-! ## The loop's entry -/

/-- A step that writes nothing of the heap below `B` keeps its doublewords. -/
theorem StepS.heapWord {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepS s v w A) {B : Nat} (hB : B ≤ heapNext v) (hv : HeapOk v)
    (hA : ∀ a, A a → ¬ (heapStart ≤ a.toNat ∧ a.toNat < B)) {x : Word}
    (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ B) : w.getMem x = v.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := hv.hi
  simp only [heapNext, heapEnd, heapStart] at hh hB h1
  refine st.frame x fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw
  · exact hA _ hw ⟨by simp only [heapStart]; addr_omega [h1, h2, hi, hB, hh],
      by addr_omega [h1, h2, hi, hB, hh]⟩
  · addr_omega [hw, hb1, h1, h2, hi, hB, hh]
  · addr_omega [hw, h1, h2, hi, hB, hh]
  · simp only [Fresh, heapNext] at hw; addr_omega [hw, h1, h2, hi, hB, hh]

/-- A frame write misses the heap. -/
theorem frameW_heap {s : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (hA : FrameW s A) : ∀ a, A a → ¬ (heapStart ≤ a.toNat ∧ a.toNat < heapEnd) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha hh
  have := hA a ha
  simp only [heapStart, heapEnd] at hh
  addr_omega [this, hh, hb1]

/-- Kept heap doublewords, as a frame. -/
theorem dframe_heap {t t' : MachineState} (hnt : heapNext t ≤ heapEnd)
    (hw : ∀ x : Word, heapStart ≤ x.toNat → x.toNat + 8 ≤ heapNext t → t'.getMem x = t.getMem x) :
    DFrame t t' fun a ↦ ¬ (heapStart ≤ a.toNat ∧ a.toNat < heapNext t) := by
  intro a ha
  have h0 := ha 0 (by decide)
  have h7 := ha 7 (by decide)
  simp only [not_not] at h0 h7
  rw [add_ofNat_zero] at h0
  simp only [heapStart, heapNext, heapEnd] at h0 h7 hnt
  exact hw a h0.1 (by simp only [heapNext]; addr_omega [h0, h7, hnt])

/-- A frame slot `S - j` that `A` misses keeps its doubleword. -/
theorem StepS.slot' {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepS s v w A) {j : Nat} (hj : 8 ≤ j) (hj2 : j ≤ 1344)
    (hx : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ A y) :
    w.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact st.toR.word hpre hx (Or.inl (by addr_omega [hb1, hj, hj2]))

theorem Sides.start {bev : MachineState → Word → List E → Option E} {s z w v h₀ : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) :
    Sides s z h₀ h₀ (w.getReg .x23) (w.getReg .x25).toNat (accAt s k state mem mf bf bv 0) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have I₀ := C.setup.inv
  have hz := C.fps.inv
  have Iv := C.rows1.inv
  have M1 := C.rows1.mat hz.heap.lo
  have stS := C.setup.step
  have hvS (x : Word) (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ heapNext v) :
      h₀.getMem x = v.getMem x :=
    stS.heapWord hpre (le_refl _) Iv.heap (fun a ha hh ↦ frameW_heap hpre (SetupW.frameW hpre) a ha
      ⟨hh.1, by have := Iv.heap.hi; omega⟩) h1 h2
  have hPb : (w.getReg .x25).toNat = 0 ∨ heapNext z ≤ (w.getReg .x23).toNat := by
    have ho := C.rows1.obuf
    simp only [NewBuf] at ho
    rcases ho.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr h0.1
  obtain ⟨M, hrow, hcell, -⟩ := M1.keep Iv.heap stS.mono hPb fun x h1 h2 ↦
    hvS x (by have := hz.heap.lo; omega) h2
  have hn : (w.getReg .x25).toNat = tables.length := by
    rw [C.rows0.x25]; exact hpre.tablesLen
  have fr := dframe_heap Iv.heap.hi hvS
  have rowOk (i : Nat) (hi : i < (w.getReg .x25).toNat) :
      RowOk z h₀ (rowAt (w.getReg .x23) i) := by
    have r := C.rows1.rows i hi
    refine r.move fr stS.mono ?_ ?_ ?_ fun x hx hx' ↦ hx' ?_
    · simpa using hrow i hi 0 (by omega)
    · simpa using hrow i hi 1 (by omega)
    · simpa using hrow i hi 2 (by omega)
    · obtain ⟨q0, q1, q2⟩ := r.bufIn
      have := hz.heap.lo
      simp only [Within] at hx
      exact ⟨by omega, by omega⟩
  have hptr (i : Nat) (hi : i < (w.getReg .x25).toNat) :
      vecPtr h₀ (rowAt (w.getReg .x23) i) = vecPtr v (rowAt (w.getReg .x23) i) := by
    simpa [vecPtr] using hrow i hi 1 (by omega)
  have stZ := C.rows1.step.trans stS
  have t0 : vecCap h₀ (s.getReg .x2 - 632) = 0 :=
    (stZ.slot' hpre (j := 632) (by omega) (by omega) fun y hy hy' ↦ by
      rcases hy' with hy' | hy'
      · rcases hy' with hy' | hy' | hy' <;> addr_omega [hy, hy', hb1]
      · rcases hy' with hy' | hy' <;> addr_omega [hy, hy', hb1]).trans C.fps.t0
  refine ⟨I₀, StepS.same (fun _ ↦ rfl) I₀.heap rfl, M, fun i hi j hj ↦ ?_, ?_, ?_, rfl, rfl,
    fun x hx ↦ ?_⟩
  · have hc : cellAt h₀ (rowAt (w.getReg .x23) i) j = cellAt v (rowAt (w.getReg .x23) i) j := by
      simp only [cellAt, hptr i hi]
    have e8 : vecPtr h₀ (cellAt v (rowAt (w.getReg .x23) i) j) =
        vecPtr v (cellAt v (rowAt (w.getReg .x23) i) j) := by
      simpa [vecPtr] using hcell i hi j hj 1 (by omega)
    have e16 : vecLen h₀ (cellAt v (rowAt (w.getReg .x23) i) j) =
        vecLen v (cellAt v (rowAt (w.getReg .x23) i) j) := by
      simpa [vecLen] using hcell i hi j hj 2 (by omega)
    have hl := ((C.rows1.rows i hi).cells j hj).2.1
    have hp := C.ptrs.forms i hi j hj
    have hm := stS.mono
    rw [hc, e8, e16, hl]
    have e0 : (0 : Word).toNat = 0 := rfl
    omega
  · have e : ∀ i ∈ List.range (w.getReg .x25).toNat,
        formVecAt h₀ (w.getReg .x23 + BitVec.ofNat 64 (24 * i)) = List.replicate 3 {} :=
      fun i hi ↦ (rowOk i (List.mem_range.mp hi)).value
    simp only [formRowsAt, accAt, List.take_zero, List.foldl_nil]
    rw [List.map_congr_left e, List.map_const', List.length_range, hn]
  · have stZ := C.rows1.step.trans stS
    have wd (j : Nat) (hj : 632 ≥ j) (hj2 : j ≥ 616) (hj8 : j % 8 = 0) :
        h₀.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = z.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
      stZ.slot' hpre (by omega) (by omega) fun y hy hy' ↦ by
        rcases hy' with hy' | hy'
        · rcases hy' with hy' | hy' | hy' <;> addr_omega [hy, hy', hb1, hj, hj2]
        · rcases hy' with hy' | hy' <;> addr_omega [hy, hy', hb1, hj, hj2]
    have t0 : vecCap h₀ (s.getReg .x2 - 632) = 0 := (wd 632 (by omega) (by omega) rfl).trans C.fps.t0
    have t1 : vecPtr h₀ (s.getReg .x2 - 632) = 8 := by
      have e : s.getReg .x2 - 632 + 8 = s.getReg .x2 - BitVec.ofNat 64 624 := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      simp only [vecPtr]; rw [e]; exact (wd 624 (by omega) (by omega) rfl).trans C.fps.t1
    have t2 : vecLen h₀ (s.getReg .x2 - 632) = 0 := by
      have e : s.getReg .x2 - 632 + 16 = s.getReg .x2 - BitVec.ofNat 64 616 := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      simp only [vecLen]; rw [e]; exact (wd 616 (by omega) (by omega) rfl).trans C.fps.t2
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [RawVecOk, Buf, t0, t1]; exact ⟨rfl, Or.inl rfl⟩
    · rw [t0, t2]
    · simp only [NewBuf, t0, t1]; exact ⟨rfl, Or.inl rfl⟩
    · simp only [vecEs, t2, accAt, List.take_zero, List.foldl_nil]; rfl
  · rw [t0] at hx
    simp only [Within] at hx
    have : (0 : Word).toNat = 0 := rfl
    omega

/-! ## The rest -/

/-- `RestStage` from the way in, one side, and the way out. -/
theorem restStage {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hE : SidesEntry BcOk bev)
    (hS : SideStage bev) (hF : FinalStage bev) : RestStage BcOk bev := by
  intro s q k state mem mf bf hpre hbc Sc hpc
  obtain ⟨h₀, hr₀, hd | hd | ⟨z, w, v, bv, C, hpc₀⟩⟩ := hE s q k state mem mf bf hpre hbc Sc hpc
  · exact ⟨h₀, hr₀, Or.inl hd⟩
  · exact ⟨h₀, hr₀, Or.inr hd⟩
  obtain ⟨h₁, hr₁, hd | ⟨S₁, ⟨-, hpc₁, x₁⟩ | ⟨h3, -⟩⟩⟩ :=
    hS s z w v h₀ h₀ k state mem mf bf bv 0 hpre C (by decide) hpc₀ C.setup.x22 (Sides.start hpre C)
  · exact ⟨h₁, hr₀.trans hr₁, Or.inr hd⟩
  swap
  · omega
  obtain ⟨h₂, hr₂, hd | ⟨S₂, ⟨-, hpc₂, x₂⟩ | ⟨h3, -⟩⟩⟩ :=
    hS s z w v h₀ h₁ k state mem mf bf bv 1 hpre C (by decide) hpc₁ x₁ S₁
  · exact ⟨h₂, hr₀.trans (hr₁.trans hr₂), Or.inr hd⟩
  swap
  · omega
  obtain ⟨h₃, hr₃, hd | ⟨S₃, ⟨h3, -⟩ | ⟨-, hpc₃⟩⟩⟩ :=
    hS s z w v h₀ h₂ k state mem mf bf bv 2 hpre C (by decide) hpc₂ x₂ S₂
  · exact ⟨h₃, hr₀.trans (hr₁.trans (hr₂.trans hr₃)), Or.inr hd⟩
  · omega
  obtain ⟨t, hrt, hdone⟩ := hF s z w v h₀ h₃ k state mem mf bf bv hpre C hpc₃ S₃
  exact ⟨t, hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans hrt))), Or.inl hdone⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
