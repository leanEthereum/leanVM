import Rv64Verifier.Proofs.Bus.VbbTail23

/-!
# `verify_bus_balance` past the GKR loop: `vec![vec![Form::default(); 3]; tables]`

From the clone loop's test (`Rows0`, at `w`): the loop (`0x80007334`, `0x80007348`) clones the
default row into the first `tables - 1` slots of the forms' buffer at `P`; `0x80007370` moves it
into the last. `CloneI` holds at the loop's head and at the move with `i` rows written, each a
`RowOk`, their buffers pairwise apart, and memory changed since `w` only in `CloneW`. `Rows1`, at
`0x8000737c`, is the forms' rows, all `n` of them (`rowsStage`, `restToRows1`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the loop writes from `w`: `S - 608`, the forms' buffer, the stack below the frame, `NEXT`
and the heap it allocates. -/
def CloneW (s w u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 608) 24 ∨ Within a (w.getReg .x23) (24 * (w.getReg .x25).toNat) ∨
    Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh w u a

/-- Row `j`'s header in the forms' buffer at `P`. -/
def rowAt (P : Word) (j : Nat) : Word := P + BitVec.ofNat 64 (24 * j)

/-- `i` rows written, at the loop's head (`i + 1 < n`) or at the move (`i + 1 = n`). -/
structure CloneI (s w u : MachineState) (i : Nat) : Prop where
  inv : Inv s u
  mono : heapNext w ≤ heapNext u
  fr : DFrame w u (CloneW s w u)
  regs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x25, .x26, .x27] : List Reg),
    u.getReg r = w.getReg r
  x23 : u.getReg .x23 = rowAt (w.getReg .x23) i
  pc : (u.pc = 0x80007334 ∧ i + 1 < (w.getReg .x25).toNat ∧
      u.getReg .x24 = rowAt (w.getReg .x23) ((w.getReg .x25).toNat - 1)) ∨
    ((u.pc = 0x80007368 ∨ u.pc = 0x80007370) ∧ i + 1 = (w.getReg .x25).toNat)
  rows : ∀ j < i, RowOk w u (rowAt (w.getReg .x23) j)
  apart : ∀ j < i, ∀ j' < i, j ≠ j' → ∀ x,
    Layout.formVecBuf u (rowAt (w.getReg .x23) j) x →
    ¬ Layout.formVecBuf u (rowAt (w.getReg .x23) j') x

/-- Where `Rows0` puts the default row's and the forms' buffers, for a nonempty layout. -/
theorem Rows0.bounds {s z w : MachineState} (hz : Inv s z) (R : Rows0 s z w)
    (hn : 1 ≤ (w.getReg .x25).toNat) :
    heapStart ≤ heapNext z ∧ heapNext w ≤ heapEnd ∧
      (w.getReg .x18).toNat % 8 = 0 ∧ heapNext z ≤ (w.getReg .x18).toNat ∧
      (w.getReg .x18).toNat + (w.getReg .x9).toNat * 24 ≤ (w.getReg .x23).toNat ∧
      (w.getReg .x23).toNat % 8 = 0 ∧
      (w.getReg .x23).toNat + 24 * (w.getReg .x25).toNat ≤ heapNext w ∧
      3 ≤ (w.getReg .x9).toNat := by
  have hl := hz.heap.lo
  have hh := R.inv.heap.hi
  have hi := R.ibuf
  have ho := R.obuf
  have hc := R.icap
  have ha := R.apart
  simp only [NewBuf] at hi ho
  refine ⟨hl, hh, hi.1, ?_, ?_, ho.1, ?_, hc⟩
  · rcases hi.2 with h0 | h0 <;> omega
  · rcases ha with h0 | h0 <;> omega
  · rcases ho.2 with h0 | h0 <;> omega

/-- What an iteration writes from `u`: `clone`'s frame and the row's header. -/
def IterW (s v₁ t : MachineState) (row : Word) (a : Word) : Prop :=
  (Within a (s.getReg .x2 - 608) 24 ∨
    Within a (s.getReg .x2 - BitVec.ofNat 64 (1344 + 176)) Layout.cloneStack ∨
    Within a nextAddr 8 ∨ Fresh v₁ t a) ∨ Within a row 24

/-- One iteration of the loop: row `i` cloned from the default row. -/
theorem cloneIter (hCl : Layout.Clone.CloneCapsSpec) {s z w u : MachineState} {i : Nat}
    (hpre : BusBalancePre s) (hz : Inv s z) (R : Rows0 s z w) (C : CloneI s w u i)
    (hpc : u.pc = 0x80007334) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ CloneI s w v (i + 1)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have hi1 : i + 1 < (w.getReg .x25).toNat := by
    rcases C.pc with ⟨-, h, -⟩ | ⟨h, -⟩
    · exact h
    · rw [hpc] at h; rcases h with h | h <;> exact absurd h (by decide)
  have hx24 : u.getReg .x24 = rowAt (w.getReg .x23) ((w.getReg .x25).toNat - 1) := by
    rcases C.pc with ⟨-, -, h⟩ | ⟨h, -⟩
    · exact h
    · rw [hpc] at h; rcases h with h | h <;> exact absurd h (by decide)
  obtain ⟨hzl, hwh, hB8, hBz, hBP, hP8, hPw, hC3⟩ := R.bounds hz (by omega)
  have hzs := hz.mono
  have hmz := R.step.mono
  have hmu := C.mono
  have huh := C.inv.heap.hi
  have hx19 := R.x19
  simp only [heapNext, heapStart, heapEnd] at hzl hwh hBz hPw hzs hmz hmu huh hab
  -- the default forms at `u`
  have hdef : ∀ j < 3, DefaultAt u (w.getReg .x18 + BitVec.ofNat 64 (24 * j)) := by
    intro j hj
    obtain ⟨d0, d1, d2⟩ := R.idef j hj
    have kw (x : Word) (h1 : (w.getReg .x18).toNat ≤ x.toNat)
        (h2 : x.toNat + 8 ≤ (w.getReg .x18).toNat + 72) : u.getMem x = w.getMem x :=
      C.fr x fun k hk hw ↦ by
        simp only [CloneW, Fresh, heapNext] at hw
        rcases hw with hw | hw | hw | hw | hw <;>
          addr_omega [hw, hk, h1, h2, hb1, hBP, hC3, hPw, hwh, hBz, hzl, hab]
    refine ⟨(kw _ ?_ ?_).trans d0, (kw _ ?_ ?_).trans d1, (kw _ ?_ ?_).trans d2⟩ <;>
      addr_omega [hj, hBP, hC3, hwh, hBz, hzl]
  -- the call
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007334_spec hpc trivial
  have k₁ := b80007334_keeps h₁
  have m₁ := b80007334_mem_same h₁
  have I₁ := C.inv.same m₁ (k₁ .x2 (by decide))
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  have x10₁ : v₁.getReg .x10 = s.getReg .x2 - 608 := by
    rw [b80007334_x10 h₁, C.inv.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₁ : v₁.getReg .x11 = w.getReg .x18 := by
    rw [b80007334_x11 h₁, C.regs .x18 (by decide)]
  have x12₁ : v₁.getReg .x12 = 3 := by
    rw [b80007334_x12 h₁, C.regs .x19 (by decide), hx19]
  have hn₁ : heapNext v₁ = heapNext u := by simp only [heapNext, m₁]
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := Layout.cloneStack) hpre I₁ (n := 24) (k := 608)
    (by omega) (by omega) (by omega) (by decide)
  have hsl : stackLo v₁ Layout.cloneStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 176) := by
    simp only [stackLo, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have pre : Layout.ClonePre v₁ := {
    heap := I₁.heap
    stack := hpre.stack.sub 1344 sp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    out := by rw [x10₁]; exact regionRange o1 (Nat.le_refl _) (by addr_omega [hb1]) o1.2
    src := by
      rw [x11₁, x12₁, show (3 : Word).toNat = 3 from rfl]
      exact heapRange hB8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
    srcOk := by
      rw [x11₁, x12₁]
      intro j hj
      obtain ⟨d0, d1, d2⟩ := hdef j hj
      have e0 : vecCap v₁ (w.getReg .x18 + BitVec.ofNat 64 (24 * j)) = 0 := (m₁ _).trans d0
      have e8 : vecPtr v₁ (w.getReg .x18 + BitVec.ofNat 64 (24 * j)) = 8 := (m₁ _).trans d1
      have e16 : vecLen v₁ (w.getReg .x18 + BitVec.ofNat 64 (24 * j)) = 0 := (m₁ _).trans d2
      refine ⟨⟨?_, ?_⟩, fun k hk ↦ ?_⟩
      · simp only [RawVecOk, Buf, e0, e8]; exact ⟨by decide, Or.inl (by decide)⟩
      · rw [e0, e16]
      · rw [e16] at hk; exact absurd hk (Nat.not_lt_zero _)
    outFree := x10₁ ▸ o2
    srcFree := by
      rw [x11₁, x12₁, show (3 : Word).toNat = 3 from rfl]
      simp only [Outside, heapNext, heapEnd, m₁]
      refine ⟨Or.inl (by omega), ?_⟩
      addr_omega [hBP, hC3, hwh, hPw]
    outStack := x10₁ ▸ o3
    srcStack := by
      rw [x11₁, x12₁, hsl, show (3 : Word).toNat = 3 from rfl]
      addr_omega [hBP, hC3, hwh, hab, hb1, hPw] }
  obtain ⟨t, hrt, ⟨hpct, hpt, ⟨N, hvl⟩, hcp, hdp⟩ | hd⟩ :=
    hCl.call (Reaches.refl v₁) (b80007334_pc h₁) pre
  swap
  · exact ⟨t, hr₁.trans hrt, Or.inl hd⟩
  have hpc₂ : t.pc = 0x80007348 := by rw [hpct, returnAddress_eq, b80007334_x1 h₁]; decide
  rw [x10₁] at N hvl hcp hdp
  rw [x11₁, x12₁] at hvl hcp hdp
  have frt : DFrame v₁ t fun a ↦ Within a (s.getReg .x2 - 608) 24 ∨
      Within a (stackLo v₁ Layout.cloneStack) Layout.cloneStack ∨ Within a nextAddr 8 ∨
        Fresh v₁ t a :=
    layoutFrame hrt N.frame
  rw [hsl] at frt
  have spt : t.getReg .x2 = s.getReg .x2 - 1344 := (hpt .x2 (by decide)).trans sp₁
  have It : Inv s t := I₁.loc hpre (frt.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)) N.heap N.mono (hpt .x2 (by decide))
  have hmt := N.mono
  have htn := N.heap.hi
  simp only [heapNext, heapEnd, m₁] at hmt htn
  -- the clone at `S - 608`
  have hok := N.ok
  have hlen3 : vecLen t (s.getReg .x2 - 608) = 3 := by
    have := congrArg List.length hvl
    rw [Layout.formVecOf, Layout.formsAt_length, Layout.formsAt_length] at this
    exact BitVec.eq_of_toNat_eq this
  have hnew : (vecCap t (s.getReg .x2 - 608)).toNat = 0 ∨
      heapNext u ≤ (vecPtr t (s.getReg .x2 - 608)).toNat := by
    rcases Nat.eq_zero_or_pos ((vecCap t (s.getReg .x2 - 608)).toNat) with h0 | h0
    · exact Or.inl h0
    · right
      have hf := N.fresh (vecPtr t (s.getReg .x2 - 608))
        (Or.inl (by simp only [Layout.formVecBuf, Within]; omega))
      simp only [Fresh, heapNext, m₁] at hf
      simp only [heapNext]; omega
  have nr : RowOk w t (s.getReg .x2 - 608) := by
    refine ⟨hok.vec, hlen3, ?_, fun j hj ↦ ?_⟩
    · have hraw := hok.vec.raw
      simp only [RawVecOk, Buf] at hraw
      simp only [NewBuf]
      refine ⟨hraw.1, ?_⟩
      rcases hraw.2 with h1 | h1
      · exact Or.inl h1
      rcases hnew with h0 | h0
      · exact Or.inl (by rw [h0])
      · right; simp only [heapNext] at h0 h1 ⊢; exact ⟨by omega, h1.2⟩
    · have hj' : j < (vecLen t (s.getReg .x2 - 608)).toNat := by rw [hlen3]; exact hj
      have hfo := hok.forms j hj'
      have hc0 : vecCap t (vecPtr t (s.getReg .x2 - 608) + BitVec.ofNat 64 (24 * j)) = 0 := by
        rw [hcp j hj]
        exact (m₁ _).trans (hdef j hj).2.2
      refine ⟨hc0, ?_, hdp j hj ((m₁ _).trans (hdef j hj).2.2)⟩
      show vecLen t (vecPtr t (s.getReg .x2 - 608) + BitVec.ofNat 64 (24 * j)) = 0
      have hl := hfo.vec.len
      rw [hc0] at hl
      have e0 : (0 : Word).toNat = 0 := rfl
      exact BitVec.eq_of_toNat_eq (by omega)
  -- the move into row `i`
  have tx23 : t.getReg .x23 = rowAt (w.getReg .x23) i := by
    rw [hpt .x23 (by decide), k₁ .x23 (by decide), C.x23]
  have tx24 : t.getReg .x24 = rowAt (w.getReg .x23) ((w.getReg .x25).toNat - 1) := by
    rw [hpt .x24 (by decide), k₁ .x24 (by decide), hx24]
  have hPv : ValidMemRange (w.getReg .x23) (3 * (w.getReg .x25).toNat) :=
    heapRange hP8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007348_spec hpc₂ (by
    rv_eval [spt, tx23, rowAt]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hPv [hP8, hPw, hi1, hwh]
      | addr_omega [hb1, hPw, hi1, hwh, hab])
  have k₂ := b80007348_keeps h₂
  have fr₂ := b80007348_frame h₂ (by rw [tx23]; simp only [rowAt]; addr_omega [hPw, hi1, hwh])
  rw [tx23] at fr₂
  have w0 := b80007348_m_x23_0 h₂
  have w8 := b80007348_m_x23_8 h₂
  have w16 := b80007348_m_x23_16 h₂
  rw [tx23, spt, show s.getReg .x2 - 1344 + 736 = s.getReg .x2 - 608 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at w0
  rw [tx23, spt, show s.getReg .x2 - 1344 + 744 = s.getReg .x2 - 608 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at w8
  rw [tx23, spt, show s.getReg .x2 - 1344 + 752 = s.getReg .x2 - 608 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at w16
  have df₂ := DFrame.of_memFrame fr₂
  have hnx₂ : v₂.getMem nextAddr = t.getMem nextAddr :=
    df₂ _ fun k hk hw ↦ by simp only [rowAt] at hw; addr_omega [hw, hk, hPw, hi1, hwh]
  have hn₂ : heapNext v₂ = heapNext t := by simp only [heapNext, hnx₂]
  have fru : DFrame u v₂ (IterW s v₁ t (rowAt (w.getReg .x23) i)) :=
    ((DFrame.of_same m₁ _).trans (frt.mono fun a ha ↦ Or.inl ha) fun a ha ↦ ha).trans df₂
      fun a ha ↦ Or.inr ha
  have missIW (x : Word) (h1 : heapStart ≤ x.toNat) (h2 : x.toNat < heapNext u)
      (h3 : ¬ Within x (rowAt (w.getReg .x23) i) 24) :
      ¬ IterW s v₁ t (rowAt (w.getReg .x23) i) x := by
    simp only [heapNext, heapStart] at h1 h2
    rintro ((hx | hx | hx | hx) | hx)
    · addr_omega [hx, h2, huh, hab, hb1]
    · addr_omega [hx, h2, huh, hab, hb1]
    · addr_omega [hx, h2, huh]
    · simp only [Fresh, heapNext, m₁] at hx; omega
    · exact h3 hx
  have hdw (x : Word) (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ heapNext u)
      (h3 : x.toNat + 8 ≤ (rowAt (w.getReg .x23) i).toNat ∨
        (rowAt (w.getReg .x23) i).toNat + 24 ≤ x.toNat) : v₂.getMem x = u.getMem x :=
    fru x fun k hk hw ↦ missIW _
      (by simp only [heapStart, heapNext] at h1 h2 ⊢; addr_omega [h1, h2, hk, huh])
      (by simp only [heapNext] at h2 ⊢; addr_omega [h2, hk, huh])
      (by simp only [rowAt, heapNext] at h3 h2 ⊢; addr_omega [h3, h2, hk, hPw, hi1, hwh, huh]) hw
  have hPs : heapStart ≤ (w.getReg .x23).toNat := by simp only [heapStart]; omega
  -- the rows
  have newRow : RowOk w v₂ (rowAt (w.getReg .x23) i) :=
    nr.move df₂ hn₂.ge w0 w8 w16 fun x hx hw ↦ by
      obtain ⟨-, q1, -⟩ := nr.bufIn
      simp only [heapNext] at q1
      simp only [rowAt] at hw
      addr_omega [hx, hw, q1, hPw, hi1, hwh]
  have oldRow (j : Nat) (hj : j < i) : RowOk w v₂ (rowAt (w.getReg .x23) j) ∧
      Layout.formVecBuf v₂ (rowAt (w.getReg .x23) j) =
        Layout.formVecBuf u (rowAt (w.getReg .x23) j) := by
    have hr := C.rows j hj
    obtain ⟨q0, q1, q2⟩ := hr.bufIn
    simp only [heapNext] at q1 q2
    have e (k : Nat) (hk : k ≤ 16) : v₂.getMem (rowAt (w.getReg .x23) j + BitVec.ofNat 64 k) =
        u.getMem (rowAt (w.getReg .x23) j + BitVec.ofNat 64 k) :=
      hdw _ (by simp only [rowAt]; addr_omega [hPs, hk, hPw, hi1, hj, hwh])
        (by simp only [rowAt, heapNext]; addr_omega [hk, hPw, hi1, hj, hwh, hmu])
        (by simp only [rowAt]; addr_omega [hk, hPw, hi1, hj, hwh])
    have e0 := e 0 (by omega)
    rw [add_ofNat_zero] at e0
    have e8 : v₂.getMem (rowAt (w.getReg .x23) j + 8) = u.getMem (rowAt (w.getReg .x23) j + 8) :=
      e 8 (by omega)
    have e16 : v₂.getMem (rowAt (w.getReg .x23) j + 16) =
        u.getMem (rowAt (w.getReg .x23) j + 16) := e 16 (by omega)
    refine ⟨hr.move fru (by rw [hn₂]; simp only [heapNext]; omega) e0 e8 e16
      fun x hx hw ↦ ?_, ?_⟩
    · refine missIW x (by simp only [heapStart, Within] at hx ⊢; omega)
        (by simp only [heapNext, Within] at hx ⊢; omega) (fun h' ↦ ?_) hw
      simp only [rowAt] at h'
      addr_omega [hx, h', hPw, hi1, hwh, q1, hmz]
    · funext x; simp only [Layout.formVecBuf, vecPtr, vecCap, e0, e8]
  have newBuf : ∀ x, Layout.formVecBuf v₂ (rowAt (w.getReg .x23) i) x →
      heapNext u ≤ x.toNat := by
    intro x hx
    simp only [Layout.formVecBuf, vecPtr, vecCap, w0, w8, Within] at hx
    simp only [vecPtr, vecCap] at hnew
    rcases hnew with h0 | h0 <;> omega
  have oldBuf : ∀ j < i, ∀ x, Layout.formVecBuf v₂ (rowAt (w.getReg .x23) j) x →
      x.toNat < heapNext u := by
    intro j hj x hx
    rw [(oldRow j hj).2] at hx
    obtain ⟨-, -, q2⟩ := (C.rows j hj).bufIn
    simp only [Layout.formVecBuf, Within] at hx
    omega
  have hmv : heapNext u ≤ heapNext v₂ := by rw [hn₂]; simp only [heapNext]; omega
  refine ⟨v₂, hr₁.trans (hrt.trans hr₂), Or.inr {
    inv := It.step hpre df₂ (fun a ha ↦ by
        simp only [rowAt] at ha
        refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))), ?_⟩
        · simp only [heapNext]; addr_omega [ha, hPw, hi1, hwh, hzs, hmz, hBz, hBP]
        · rw [hn₂]; simp only [heapNext]; addr_omega [ha, hPw, hi1, hwh, hmu, hmt]
        · addr_omega [ha, hPw, hi1, hwh, hb1, hab])
      ⟨hn₂ ▸ N.heap.lo, hn₂ ▸ N.heap.hi⟩ hn₂.ge (k₂ .x2 (by decide))
    mono := by simp only [heapNext] at hmv ⊢; omega
    fr := (C.fr.mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ha | ⟨f1, f2⟩
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f1, by omega⟩)))).trans fru fun a ha ↦ by
      rcases ha with ((ha | ha | ha | ⟨f1, f2⟩) | ha)
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, by rw [hn₂]; exact f2⟩)))
        simp only [heapNext, m₁] at f1 ⊢; omega
      · exact Or.inr (Or.inl (by simp only [rowAt] at ha; addr_omega [ha, hPw, hi1, hwh]))
    regs := fun r hr ↦ by
      rw [k₂ r (mem_of_mem hr _), hpt r (by unfold calleeSaved; exact mem_of_mem hr _),
        k₁ r (mem_of_mem hr _), C.regs r hr]
    x23 := by
      rw [b80007348_x23 h₂, tx23]; simp only [rowAt]
      apply BitVec.eq_of_toNat_eq; addr_omega [hPw, hi1, hwh]
    pc := by
      by_cases h2 : i + 2 < (w.getReg .x25).toNat
      · refine Or.inl ⟨b80007348_pc_taken h₂ ?_, by omega,
          by rw [k₂ .x24 (by decide), tx24]⟩
        rw [tx23, tx24]; simp only [rowAt]; intro h
        have := congrArg BitVec.toNat h
        addr_omega [this, hPw, hi1, hwh, h2]
      · refine Or.inr ⟨Or.inl (b80007348_pc_not_taken h₂ ?_), by omega⟩
        rw [tx23, tx24]; simp only [rowAt]
        apply BitVec.eq_of_toNat_eq; addr_omega [hPw, hi1, hwh, h2]
    rows := fun j hj ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact (oldRow j hj).1
      · exact newRow
    apart := fun j hj j' hj' hne x hx hx' ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · rw [(oldRow j hj).2] at hx; rw [(oldRow j' hj').2] at hx'
        exact C.apart j hj j' hj' hne x hx hx'
      · have := newBuf x hx'; have := oldBuf j hj x hx; omega
      · have := newBuf x hx; have := oldBuf j' hj' x hx'; omega
      · exact hne rfl }⟩

/-- The loop's start: no row written. With no tables, straight past the loop. -/
theorem cloneStart {s z w : MachineState} (hz : Inv s z)
    (R : Rows0 s z w) :
    ∃ u, Reaches Image.code w u ∧ ((u.pc = 0x8000737c ∧ (w.getReg .x25).toNat = 0 ∧
      (∀ a, u.getMem a = w.getMem a) ∧ u.getReg .x2 = w.getReg .x2 ∧
      ∀ r ∈ ([.x8, .x20, .x21, .x22, .x25, .x26, .x27] : List Reg), u.getReg r = w.getReg r) ∨
      CloneI s w u 0) := by
  have r0 : rowAt (w.getReg .x23) 0 = w.getReg .x23 := by simp [rowAt]
  have base (u : MachineState) (hm : ∀ a, u.getMem a = w.getMem a)
      (hr : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27] :
        List Reg),
        u.getReg r = w.getReg r)
      (hpc : (u.pc = 0x80007334 ∧ 0 + 1 < (w.getReg .x25).toNat ∧
        u.getReg .x24 = rowAt (w.getReg .x23) ((w.getReg .x25).toNat - 1)) ∨
        ((u.pc = 0x80007368 ∨ u.pc = 0x80007370) ∧ 0 + 1 = (w.getReg .x25).toNat)) :
      CloneI s w u 0 := by
    have hn : heapNext u = heapNext w := by simp only [heapNext, hm]
    exact {
      inv := R.inv.same hm (hr .x2 (by decide))
      mono := hn.ge
      fr := DFrame.of_same hm _
      regs := fun r h ↦ hr r (mem_of_mem h _)
      x23 := by rw [hr .x23 (by decide), r0]
      pc := hpc
      rows := fun j hj ↦ absurd hj (Nat.not_lt_zero _)
      apart := fun j hj ↦ absurd hj (Nat.not_lt_zero _) }
  rcases R.pc with ⟨hpc, h2⟩ | ⟨hpc, h2⟩
  · obtain ⟨hzl, hwh, -, -, -, -, hPw, -⟩ := R.bounds hz (by omega)
    simp only [heapNext, heapStart, heapEnd] at hzl hwh hPw
    obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b80007320_spec hpc trivial
    have k := b80007320_keeps h
    refine ⟨u, hr, Or.inr (base u (b80007320_mem_same h) (fun r hr' ↦ k r (mem_of_mem hr' _))
      (Or.inl ⟨b80007320_pc h, by omega, ?_⟩))⟩
    rw [b80007320_x24 h]; simp only [rowAt]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl,
      show (24 : Word).toNat = 24 from rfl]
    have := (w.getReg .x23).isLt
    omega
  · obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b8000736c_spec hpc trivial
    have k := b8000736c_keeps h
    have hm := b8000736c_mem_same h
    by_cases h0 : (w.getReg .x25).toNat = 0
    · refine ⟨u, hr, Or.inl ⟨b8000736c_pc_taken h (BitVec.eq_of_toNat_eq h0), h0, hm,
        k .x2 (by decide), fun r hr' ↦ k r (mem_of_mem hr' _)⟩⟩
    · refine ⟨u, hr, Or.inr (base u hm (fun r hr' ↦ k r (mem_of_mem hr' _))
        (Or.inr ⟨Or.inr (b8000736c_pc_not_taken h fun he ↦ h0 (by rw [he]; rfl)),
          by omega⟩))⟩

/-- The loop runs to the move, or to a dead end. -/
theorem cloneLoop (hCl : Layout.Clone.CloneCapsSpec) {s z w : MachineState}
    (hpre : BusBalancePre s) (hz : Inv s z) (R : Rows0 s z w) (k : Nat) :
    ∀ i u, (w.getReg .x25).toNat = i + k + 1 → CloneI s w u i →
      ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨
        ∃ j, CloneI s w v j ∧ j + 1 = (w.getReg .x25).toNat ∧
          (v.pc = 0x80007368 ∨ v.pc = 0x80007370)) := by
  induction k with
  | zero =>
    intro i u hk C
    rcases C.pc with ⟨-, hlt, -⟩ | ⟨hpc, he⟩
    · omega
    · exact ⟨u, Reaches.refl u, Or.inr ⟨i, C, he, hpc⟩⟩
  | succ k ih =>
    intro i u hk C
    rcases C.pc with ⟨hpc, -, -⟩ | ⟨hpc, he⟩
    · obtain ⟨v, hr, hd | C'⟩ := cloneIter hCl hpre hz R C hpc
      · exact ⟨v, hr, Or.inl hd⟩
      · obtain ⟨t, hrt, ht⟩ := ih (i + 1) v (by omega) C'
        exact ⟨t, hr.trans hrt, ht⟩
    · exact ⟨u, Reaches.refl u, Or.inr ⟨i, C, he, hpc⟩⟩

/-- Past the loop, at `0x8000737c`: the forms' buffer at `P` (`w`'s `s7`, also at `S - 1224`) holds
`n` (`w`'s `s9`, also at `S - 1328`) rows of three empty forms, their buffers allocated from `z` on,
pairwise apart and apart from the forms' buffer. -/
structure Rows1 (s z w v : MachineState) : Prop where
  inv : Inv s v
  step : StepS s z v (RowsW s)
  regs : ∀ r ∈ ([.x8, .x20, .x21, .x22, .x25, .x26, .x27] : List Reg), v.getReg r = w.getReg r
  ptr : v.getMem (s.getReg .x2 - 1224) = w.getReg .x23
  cap : v.getMem (s.getReg .x2 - 1328) = w.getReg .x25
  obuf : NewBuf z v (w.getReg .x23) ((w.getReg .x25).toNat * 24) 8
  rows : ∀ j < (w.getReg .x25).toNat, RowOk z v (rowAt (w.getReg .x23) j)
  apart : ∀ j < (w.getReg .x25).toNat, ∀ j' < (w.getReg .x25).toNat, j ≠ j' → ∀ x,
    Layout.formVecBuf v (rowAt (w.getReg .x23) j) x →
      ¬ Layout.formVecBuf v (rowAt (w.getReg .x23) j') x
  outer : ∀ j < (w.getReg .x25).toNat, ∀ x, Layout.formVecBuf v (rowAt (w.getReg .x23) j) x →
    ¬ Within x (w.getReg .x23) (24 * (w.getReg .x25).toNat)
  pc : v.pc = 0x8000737c

/-- The move: the default row into the last slot. -/
theorem cloneStore {s z w u u' : MachineState} {i : Nat} (hpre : BusBalancePre s) (hz : Inv s z)
    (R : Rows0 s z w) (C : CloneI s w u i) (hi : i + 1 = (w.getReg .x25).toNat)
    (hm : ∀ a, u'.getMem a = u.getMem a)
    (hr : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27] :
        List Reg),
      u'.getReg r = u.getReg r)
    (hpc : u'.pc = 0x80007370) :
    ∃ v, Reaches Image.code u' v ∧ Rows1 s z w v := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  obtain ⟨hzl, hwh, hB8, hBz, hBP, hP8, hPw, hC3⟩ := R.bounds hz (by omega)
  have hzs := hz.mono
  have hmz := R.step.mono
  have hmu := C.mono
  have huh := C.inv.heap.hi
  simp only [heapNext, heapStart, heapEnd] at hzl hwh hBz hPw hzs hmz hmu huh hab
  have kw (x : Word) (h1 : (w.getReg .x18).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (w.getReg .x18).toNat + (w.getReg .x9).toNat * 24) :
      u.getMem x = w.getMem x :=
    C.fr x fun k hk hw ↦ by
      simp only [CloneW, Fresh, heapNext] at hw
      rcases hw with hw | hw | hw | hw | hw <;>
        addr_omega [hw, hk, h1, h2, hb1, hBP, hC3, hPw, hwh, hBz, hzl, hab]
  have hPv : ValidMemRange (w.getReg .x23) (3 * (w.getReg .x25).toNat) :=
    heapRange hP8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have x23 : u'.getReg .x23 = rowAt (w.getReg .x23) i := (hr .x23 (by decide)).trans C.x23
  obtain ⟨v, hrv, h⟩ := Sym.BlockSpec.reaches b80007370_spec hpc (by
    rv_eval [x23, rowAt]
    and_intros <;> valid_access hPv [hP8, hPw, hi, hwh])
  have k₁ := b80007370_keeps h
  have fr := b80007370_frame h (by rw [x23]; simp only [rowAt]; addr_omega [hPw, hi, hwh])
  rw [x23] at fr
  have w0 := b80007370_m_x23_0 h
  have w8 := b80007370_m_x23_8 h
  have w16 := b80007370_m_x23_16 h
  rw [x23, hr .x9 (by decide), C.regs .x9 (by decide)] at w0
  rw [x23, hr .x18 (by decide), C.regs .x18 (by decide)] at w8
  rw [x23, hr .x19 (by decide), C.regs .x19 (by decide), R.x19] at w16
  have dfu : DFrame u v (Within · (rowAt (w.getReg .x23) i) 24) :=
    (DFrame.of_same hm _).trans (DFrame.of_memFrame fr) fun _ ha ↦ ha
  have hnx : v.getMem nextAddr = u.getMem nextAddr :=
    dfu _ fun k hk hw ↦ by simp only [rowAt] at hw; addr_omega [hw, hk, hPw, hi, hwh]
  have hnv : heapNext v = heapNext u := by simp only [heapNext, hnx]
  have hmv : heapNext w ≤ heapNext v := by rw [hnv]; simp only [heapNext]; omega
  have hdu (x : Word) (h1 : x.toNat + 8 ≤ (rowAt (w.getReg .x23) i).toNat ∨
      (rowAt (w.getReg .x23) i).toNat + 24 ≤ x.toNat) (h2 : x.toNat + 8 ≤ 2 ^ 64) :
      v.getMem x = u.getMem x :=
    dfu x fun k hk hw ↦ by simp only [rowAt] at hw h1; addr_omega [hw, hk, h1, h2, hPw, hi, hwh]
  -- the old rows
  have oldRow (j : Nat) (hj : j < i) : RowOk w v (rowAt (w.getReg .x23) j) ∧
      Layout.formVecBuf v (rowAt (w.getReg .x23) j) =
        Layout.formVecBuf u (rowAt (w.getReg .x23) j) := by
    have hrj := C.rows j hj
    obtain ⟨q0, q1, q2⟩ := hrj.bufIn
    simp only [heapNext] at q1 q2
    have e (k : Nat) (hk : k ≤ 16) : v.getMem (rowAt (w.getReg .x23) j + BitVec.ofNat 64 k) =
        u.getMem (rowAt (w.getReg .x23) j + BitVec.ofNat 64 k) :=
      hdu _ (by simp only [rowAt]; addr_omega [hk, hPw, hi, hj, hwh])
        (by simp only [rowAt]; addr_omega [hk, hPw, hi, hj, hwh])
    have e0 := e 0 (by omega)
    rw [add_ofNat_zero] at e0
    have e8 : v.getMem (rowAt (w.getReg .x23) j + 8) = u.getMem (rowAt (w.getReg .x23) j + 8) :=
      e 8 (by omega)
    have e16 : v.getMem (rowAt (w.getReg .x23) j + 16) = u.getMem (rowAt (w.getReg .x23) j + 16) :=
      e 16 (by omega)
    refine ⟨hrj.move dfu (by rw [hnv]) e0 e8 e16 fun x hx hw ↦ ?_, ?_⟩
    · simp only [rowAt] at hw
      addr_omega [hx, hw, hPw, hi, hwh, q1]
    · funext x; simp only [Layout.formVecBuf, vecPtr, vecCap, e0, e8]
  -- the moved row
  have newRow : RowOk z v (rowAt (w.getReg .x23) i) := by
    have hp : vecPtr v (rowAt (w.getReg .x23) i) = w.getReg .x18 := w8
    have hc : vecCap v (rowAt (w.getReg .x23) i) = w.getReg .x9 := w0
    have hl : vecLen v (rowAt (w.getReg .x23) i) = 3 := w16
    refine ⟨⟨?_, ?_⟩, hl, ?_, fun j hj ↦ ?_⟩
    · simp only [RawVecOk, Buf, hp, hc]
      refine ⟨hB8, Or.inr ⟨by simp only [heapStart]; omega, ?_⟩⟩
      simp only [heapNext] at hmv ⊢; omega
    · rw [hc, hl]; exact hC3
    · simp only [NewBuf, hp, hc]
      refine ⟨hB8, Or.inr ⟨by simp only [heapNext]; omega, ?_⟩⟩
      simp only [heapNext] at hmv ⊢; omega
    · obtain ⟨d0, d1, d2⟩ := R.idef j hj
      have e (k : Nat) (hk : k ≤ 16) :
          v.getMem (w.getReg .x18 + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 k) =
            w.getMem (w.getReg .x18 + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 k) := by
        rw [hdu _ (by simp only [rowAt]; addr_omega [hk, hj, hBP, hC3, hPw, hwh, hi])
          (by addr_omega [hk, hj, hBP, hC3, hPw, hwh])]
        exact kw _ (by addr_omega [hk, hj, hBP, hC3, hPw, hwh])
          (by addr_omega [hk, hj, hBP, hC3, hPw, hwh])
      have e0 := e 0 (by omega)
      rw [add_ofNat_zero] at e0
      simp only [cellAt]
      rw [hp]
      simp only [vecCap, vecLen, vecPtr]
      refine ⟨e0.trans d0, (e 16 (by omega)).trans d2, ?_⟩
      rw [show (w.getReg .x18 + BitVec.ofNat 64 (24 * j) + 8) =
        w.getReg .x18 + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 8 from rfl, e 8 (by omega)]
      exact d1
  have newBuf : ∀ x, Layout.formVecBuf v (rowAt (w.getReg .x23) i) x →
      x.toNat + 1 ≤ (w.getReg .x18).toNat + (w.getReg .x9).toNat * 24 := by
    intro x hx
    simp only [Layout.formVecBuf, vecPtr, vecCap, w0, w8, Within] at hx
    omega
  have oldBuf : ∀ j < i, ∀ x, Layout.formVecBuf v (rowAt (w.getReg .x23) j) x →
      heapNext w ≤ x.toNat := by
    intro j hj x hx
    rw [(oldRow j hj).2] at hx
    obtain ⟨-, q1, -⟩ := (C.rows j hj).bufIn
    simp only [Layout.formVecBuf, Within] at hx
    omega
  have iv : Inv s v := (C.inv.same hm (hr .x2 (by decide))).step hpre (DFrame.of_memFrame fr)
    (fun a ha ↦ by
      simp only [rowAt] at ha
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))), ?_⟩
      · simp only [heapNext]; addr_omega [ha, hPw, hi, hwh, hzs, hmz, hBz, hBP]
      · rw [hnv]; simp only [heapNext]; addr_omega [ha, hPw, hi, hwh, hmu]
      · addr_omega [ha, hPw, hi, hwh, hb1, hab])
    ⟨hnv ▸ C.inv.heap.lo, hnv ▸ C.inv.heap.hi⟩ (by rw [hnv]; simp only [heapNext, hm]; rfl)
    (k₁ .x2 (by decide))
  have hw1224 : v.getMem (s.getReg .x2 - 1224) = w.getMem (s.getReg .x2 - 1224) := by
    rw [hdu _ (by simp only [rowAt]; addr_omega [hb1, hPw, hi, hwh, hab]) (by addr_omega [hb1])]
    exact C.fr _ fun k hk hw ↦ by
      simp only [CloneW, Fresh, heapNext] at hw
      rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hk, hb1, hPw, hwh, hab, huh]
  have hw1328 : v.getMem (s.getReg .x2 - 1328) = w.getMem (s.getReg .x2 - 1328) := by
    rw [hdu _ (by simp only [rowAt]; addr_omega [hb1, hPw, hi, hwh, hab]) (by addr_omega [hb1])]
    exact C.fr _ fun k hk hw ↦ by
      simp only [CloneW, Fresh, heapNext] at hw
      rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hk, hb1, hPw, hwh, hab, huh]
  have frw : DFrame w v (CloneW s w v) :=
    (C.fr.mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ha | ⟨f1, f2⟩
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f1, by rw [hnv]; exact f2⟩)))).trans dfu
      fun a ha ↦ Or.inr (Or.inl (by simp only [rowAt] at ha; addr_omega [ha, hPw, hi, hwh]))
  have stp : StepS s z v (RowsW s) := by
    refine ⟨(R.step.frame.mono fun a ha ↦ ?_).trans frw fun a ha ↦ ?_, iv.heap,
      by simp only [heapNext] at hmv ⊢; omega,
      by rw [k₁ .x2 (by decide), hr .x2 (by decide), C.inv.sp, hz.sp]⟩
    · rcases ha with ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨f1, by simp only [heapNext] at f2 hmv ⊢; omega⟩))
    · rcases ha with ha | ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl (Or.inl ha)
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)) <;> simp only [heapNext] at hmv ⊢ <;>
          addr_omega [ha, hPw, hzl, hBz, hBP, hmz, hwh, hmv]
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext] at f1 ⊢; omega, f2⟩))
  refine ⟨v, hrv, {
    inv := iv
    step := stp
    regs := fun r h' ↦ by
      rw [k₁ r (mem_of_mem h' _), hr r (mem_of_mem h' _), C.regs r (mem_of_mem h' _)]
    ptr := hw1224.trans R.x23.symm
    cap := hw1328.trans R.ocap
    obuf := by
      have ho := R.obuf
      simp only [NewBuf] at ho ⊢
      exact ⟨ho.1, ho.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
    rows := fun j hj ↦ by
      rcases Nat.lt_or_ge j i with hj' | hj'
      · exact (oldRow j hj').1.widen (by simp only [heapNext]; omega)
      · obtain rfl : j = i := by omega
        exact newRow
    apart := fun j hj j' hj' hne x hx hx' ↦ by
      rcases Nat.lt_or_ge j i with h1 | h1 <;> rcases Nat.lt_or_ge j' i with h2 | h2
      · rw [(oldRow j h1).2] at hx; rw [(oldRow j' h2).2] at hx'
        exact C.apart j h1 j' h2 hne x hx hx'
      · obtain rfl : j' = i := by omega
        have := newBuf x hx'; have := oldBuf j h1 x hx; simp only [heapNext] at this; omega
      · obtain rfl : j = i := by omega
        have := newBuf x hx; have := oldBuf j' h2 x hx'; simp only [heapNext] at this; omega
      · exact hne (by omega)
    outer := fun j hj x hx hP ↦ by
      simp only [Within] at hP
      rcases Nat.lt_or_ge j i with h1 | h1
      · have := oldBuf j h1 x hx; simp only [heapNext] at this; omega
      · obtain rfl : j = i := by omega
        have := newBuf x hx; omega
    pc := b80007370_pc h }⟩

/-- No tables: no row. -/
theorem rowsNone {s z w u : MachineState} (R : Rows0 s z w) (hpc : u.pc = 0x8000737c)
    (h0 : (w.getReg .x25).toNat = 0) (hm : ∀ a, u.getMem a = w.getMem a)
    (hsp : u.getReg .x2 = w.getReg .x2)
    (hr : ∀ r ∈ ([.x8, .x20, .x21, .x22, .x25, .x26, .x27] : List Reg),
      u.getReg r = w.getReg r) :
    Rows1 s z w u := by
  have hn : heapNext u = heapNext w := by simp only [heapNext, hm]
  refine {
    inv := R.inv.same hm hsp
    step := (R.step.trans (StepS.same (A := fun _ ↦ False) hm R.inv.heap hsp)).weaken
      fun a ha ↦ by rcases ha with ha | ha; exacts [ha, ha.elim]
    regs := hr
    ptr := (hm _).trans R.x23.symm
    cap := (hm _).trans R.ocap
    obuf := by
      have ho := R.obuf
      simp only [NewBuf] at ho ⊢
      rw [hn]; exact ho
    rows := fun j hj ↦ absurd hj (by omega)
    apart := fun j hj ↦ absurd hj (by omega)
    outer := fun j hj ↦ absurd hj (by omega)
    pc := hpc }

/-- From the clone loop's test to `0x8000737c`: the forms' rows. -/
theorem rowsStage (hCl : Layout.Clone.CloneCapsSpec) {s z w : MachineState}
    (hpre : BusBalancePre s) (hz : Inv s z) (R : Rows0 s z w) :
    ∃ v, Reaches Image.code w v ∧ (Dead Image.code v ∨ Rows1 s z w v) := by
  obtain ⟨u, hru, ⟨hpc, h0, hm, hsp, hr⟩ | C⟩ := cloneStart hz R
  · exact ⟨u, hru, Or.inr (rowsNone R hpc h0 hm hsp hr)⟩
  have hn : (w.getReg .x25).toNat = 0 + ((w.getReg .x25).toNat - 1) + 1 := by
    rcases C.pc with ⟨-, h, -⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨v, hrv, hd | ⟨j, C', hj, hpc⟩⟩ := cloneLoop hCl hpre hz R _ 0 u hn C
  · exact ⟨v, hru.trans hrv, Or.inl hd⟩
  rcases hpc with hpc | hpc
  · obtain ⟨v', hr', h'⟩ := Sym.BlockSpec.reaches b80007368_spec hpc trivial
    have k := b80007368_keeps h'
    obtain ⟨t, hrt, Rt⟩ := cloneStore hpre hz R C' hj (b80007368_mem_same h')
      (fun r hr ↦ k r (mem_of_mem hr _)) (b80007368_pc h')
    exact ⟨t, hru.trans (hrv.trans (hr'.trans hrt)), Or.inr Rt⟩
  · obtain ⟨t, hrt, Rt⟩ := cloneStore hpre hz R C' hj (fun _ ↦ rfl) (fun _ _ ↦ rfl) hpc
    exact ⟨t, hru.trans (hrv.trans hrt), Or.inr Rt⟩

/-- From `0x80006ca0` to `0x8000737c`: the rest's stages and the forms' rows. -/
theorem restToRows1 (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) (hA : AllocSpec)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hI : IndexMleSpec) (hC : SliceConcatSpec)
    {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E}
    (hB : Vbb.BytecodeEvalSpec BcOk bev) (hBT : BcTransfer BcOk bev) (hP : PowSpec)
    (hF : FingerprintsSpec) (hR : ReserveFreshSpec 0x80004aec 24 8)
    (hCl : Layout.Clone.CloneCapsSpec) {s q : MachineState} {k : Start} {state : GkrState}
    {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (hbc : BcOk s busBalanceStack (bytecodeOf s (s.getReg .x11)))
    (Sc : Scalars bev s q k state mem mf bf) (hpc : q.pc = 0x80006ca0) :
    ∃ v, Reaches Image.code q v ∧ (Done bev s v ∨ Dead Image.code v ∨
      ∃ z w bv, Fps bev s z k state mem mf bf bv ∧ Rows0 s z w ∧ Rows1 s z w v) := by
  obtain ⟨w, hrw, hdone | hd | ⟨z, bv, F, R⟩⟩ :=
    restToRows hT hM hA hG hI hC hB hBT hP hF hR hpre hbc Sc hpc
  · exact ⟨w, hrw, Or.inl hdone⟩
  · exact ⟨w, hrw, Or.inr (Or.inl hd)⟩
  obtain ⟨v, hrv, hd | R1⟩ := rowsStage hCl hpre F.inv R
  · exact ⟨v, hrw.trans hrv, Or.inr (Or.inl hd)⟩
  · exact ⟨v, hrw.trans hrv, Or.inr (Or.inr ⟨z, w, bv, F, R, R1⟩)⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
