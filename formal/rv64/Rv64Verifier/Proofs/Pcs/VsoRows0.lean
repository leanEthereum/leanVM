import Rv64Verifier.Proofs.Pcs.VsoRows0C
import Rv64Verifier.Proofs.Pcs.VsoRowed

/-!
# `verify_stacked_opening`'s level loop: level 0's rows (`RowsZero`)

From `0x8000b2e0`: the rows' buffer (`alloc0`, to `0x8000b328`), the branch on the row count,
the kernel's pointer and length spilled to `S - 904` and `S - 784` (`0x8000b334`), the loop over
rows (`rows0`), to `0x8000b42c` (`Rowed`) with `base_dot` of every row against `eq_kernel`'s
weights, `rowValuesRust 0`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What is kept up to the loop: the old heap, apart from the stack and `NEXT`. -/
theorem keep0 {s k r : MachineState} {X : Word → Prop} (hrh : HeapOk r)
    (hX : ∀ y, X y → Within y (s.getReg .x2 - 2464) 2464 ∨ Within y nextAddr 8 ∨
      (heapNext k ≤ y.toNat ∧ y.toNat < heapNext r))
    (F : DFrame k r X) {p : Word} {m : ℕ}
    (h1 : p.toNat + m ≤ heapNext k ∨ heapEnd ≤ p.toNat)
    (h2 : Apart p m (s.getReg .x2 - 2464) 2464) (h3 : Apart p m nextAddr 8)
    (h4 : p.toNat + m ≤ 2 ^ 64) {y : Word}
    (hy : p.toNat ≤ y.toNat ∧ y.toNat + 8 ≤ p.toNat + m) : r.getMem y = k.getMem y := by
  have hh := hrh.hi
  refine F y fun c hc hw ↦ ?_
  rcases hX _ hw with h | h | ⟨h5, h6⟩
  · addr_omega [h, h2, hy, hc, h4]
  · addr_omega [h, h3, hy, hc, h4]
  · rcases h1 with h1 | h1
    · addr_omega [h4, h5, h6, h1, hy, hc]
    · addr_omega [h4, h5, h6, h1, hy, hc, hh]

/-- `(k.readWords p n).map BF64.ofBitVec` is `kListAt`. -/
theorem kListAt_of_readWords (k : MachineState) (p : Word) (n : ℕ) :
    (k.readWords p n).map BF64.ofBitVec = kListAt k p n := by
  rw [kListAt, readWords_eq_map, List.map_map]
  rfl

theorem kListAt_congr0 {k r : MachineState} {p : Word} {n : ℕ}
    (h : ∀ i < n,
      r.getMem (p + BitVec.ofNat 64 (8 * i)) = k.getMem (p + BitVec.ofNat 64 (8 * i))) :
    kListAt r p n = kListAt k p n := by
  unfold kListAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [h i hi]

/-- A `Clear` range misses what the rows' loop writes. -/
theorem clear_r0w {s k : MachineState} {Q : Word} {n : ℕ} (hpre : VsoPre s)
    (hq1 : heapNext k ≤ Q.toNat) (hq2 : Q.toNat + 24 * n ≤ heapEnd) {p : Word} {m : ℕ}
    (hc : Clear s (heapNext k) p m) : ∀ y, Within y p m → ¬ R0W s Q n y := by
  have hb := bounds hpre
  obtain ⟨⟨h1, h2, -⟩, -⟩ := hc
  intro y hy hw
  simp only [R0W] at hw
  rcases hw with hw | hw | hw
  · addr_omega [hw, hy, h2, hb]
  · addr_omega [hw, hy, h2, hb]
  · rcases h1 with h1 | h1
    · addr_omega [hw, hy, h1, hq1]
    · addr_omega [hw, hy, h1, hq2]

/-- What the level writes before its rows' loop is in `RowW`. -/
theorem a0w_roww {s k k' r t : MachineState} (hpre : VsoPre s) (hk : heapNext k' = heapNext k)
    (ht : heapNext r ≤ heapNext t) {y : Word} (h : A0W s k' r y) : RowW s k t y := by
  have hb := bounds hpre
  simp only [A0W, RowW, Fresh] at h ⊢
  rcases h with h | h | h | h | ⟨h1, h2⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))


/-- The slots the level reads after its rows' loop miss what it writes before. -/
theorem pre_miss {s k' r₀ : MachineState} (hpre : VsoPre s) (h₀ : HeapOk r₀) {y : Word}
    (hy : (s.getReg .x2 - 880).toNat ≤ y.toNat ∧ y.toNat < (s.getReg .x2 - 800).toNat ∨
      (s.getReg .x2 - 528).toNat ≤ y.toNat ∧ y.toNat < (s.getReg .x2 - 512).toNat) :
    ¬ (A0W s k' r₀ y ∨ Within y (s.getReg .x2 - 784) 8 ∨
      Within y (s.getReg .x2 - 904) 8) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  simp only [vso_stack] at hab
  have hh := h₀.hi
  simp only [A0W, Fresh]
  rintro ((h | h | h | h | ⟨-, h⟩) | h | h)
  all_goals first
    | addr_omega [h, hy, hb]
    | addr_omega [h, hy, hb, hnx]
    | addr_omega [h, hy, hb, hab, hh]

/-- What the rows' loop writes is in `RowW`. -/
theorem r0w_roww {s k t : MachineState} {Q : Word} {n : ℕ} (hpre : VsoPre s)
    (hq1 : heapNext k ≤ Q.toNat) (hq2 : Q.toNat + 24 * n ≤ heapNext t) {y : Word}
    (h : R0W s Q n y) : RowW s k t y := by
  have hb := bounds hpre
  simp only [R0W, RowW, Fresh] at h ⊢
  rcases h with h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hq1],
      by addr_omega [h, hq2]⟩)))))

/-- **Level `0`'s rows**: from `0x8000b2e0` to `0x8000b42c`, `base_dot` of every row against
`eq_kernel`'s weights, or a dead end. -/
theorem rowsZero (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x80008a10) (hMK : MulKSpec) :
    RowsZero := by
  intro s t' k k' lf ws hpre hk hL h808 hpc hmem hregs
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hst.above
  simp only [vso_stack] at hab
  have sp' : k'.getReg .x2 = s.getReg .x2 - 1040 := (hregs .x2 (by decide)).trans hk.sp
  have hn' : heapNext k' = heapNext k := by simp only [heapNext, hmem]
  have inv' : InvR s k' (k'.getMem nextAddr) := by
    rw [hmem]; exact Inv.same' hk.inv hmem (sp'.trans hk.sp.symm)
  obtain ⟨r₀, hr₀, hd | A⟩ := alloc0 hT hR hpre hpc sp' inv'
  · exact ⟨r₀, hr₀, Or.inl (Or.inl hd)⟩
  have hN : (k'.getReg .x20).toNat = ws.length := by rw [hregs .x20 (by decide)]; exact hL.n
  have hx20 : k'.getReg .x20 = BitVec.ofNat 64 ws.length := by
    apply BitVec.eq_of_toNat_eq
    have := (k'.getReg .x20).isLt
    rw [hN] at this ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
  have hbuf := A.buf
  rw [hN] at hbuf
  have h₀ := A.heap
  have F₀ : DFrame k r₀ (A0W s k' r₀) :=
    (DFrame.of_same hmem (A0W s k' r₀)).trans A.fr fun _ h ↦ h
  have kreg (q : Reg) (hq : q ∈ calleeSaved) : r₀.getReg q = k.getReg q :=
    (A.regs q hq).trans (hregs q hq)
  -- `0x8000b328`
  obtain ⟨r₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b328_spec A.pc (by
    rv_eval [A.sp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000b328_keeps h₁
  have m₁ := b8000b328_mem_same h₁
  have x25₁ : r₁.getReg .x25 = r₀.getMem (s.getReg .x2 - 456) := by
    rw [b8000b328_x25 h₁, A.sp, show s.getReg .x2 - 1040 + 584 = s.getReg .x2 - 456 by rv_eval []]
  have x27₁ : r₁.getReg .x27 = 0 := by
    rw [b8000b328_x27 h₁, A.sp, show s.getReg .x2 - 1040 + 592 = s.getReg .x2 - 448 by rv_eval [],
      A.len]
  have x20₀ : r₀.getReg .x20 = BitVec.ofNat 64 ws.length := (A.regs .x20 (by decide)).trans hx20
  have hn₁ : heapNext r₁ = heapNext r₀ := by simp only [heapNext, m₁]
  by_cases hn0 : ws.length = 0
  · -- no rows
    have hws : ws = [] := List.eq_nil_of_length_eq_zero hn0
    have hpc₁ := b8000b328_pc_taken h₁ (by rw [x20₀, hn0]; rfl)
    refine ⟨r₁, hr₀.trans hr₁, Or.inr {
      pc := hpc₁
      sp := (k₁ .x2 (by decide)).trans A.sp
      regs := fun q hq ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;>
          exact (k₁ _ (by decide)).trans (kreg _ (by decide))
      inv := Inv.same' (by
          rw [show r₁.getMem nextAddr = r₀.getMem nextAddr from m₁ _]; exact A.inv)
        m₁ ((k₁ .x2 (by decide)).trans rfl)
      heap := ⟨by rw [hn₁]; exact h₀.lo, by rw [hn₁]; exact h₀.hi⟩
      mono := by rw [hn₁, ← hn']; exact A.mono
      value := by
        rw [x27₁, hws]
        rfl
      buf := by
        rw [x25₁, x27₁]
        simp only [NewBuf] at hbuf ⊢
        exact ⟨hbuf.1, Or.inl rfl⟩
      fr := (F₀.trans (DFrame.of_same m₁ _) fun _ h ↦ h).mono fun y h ↦
        a0w_roww hpre hn' (le_of_eq hn₁.symm) h }⟩
  have hnpos : 0 < ws.length := Nat.pos_of_ne_zero hn0
  have hwl := (k'.getReg .x20).isLt
  rw [hN] at hwl
  have hpc₁ := b8000b328_pc_not_taken h₁ (by
    rw [x20₀]
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwl] at this
    exact hn0 this)
  obtain ⟨hQ8, hQ⟩ := hbuf
  obtain ⟨hq1, hq2⟩ := hQ.resolve_left (by omega)
  rw [hn'] at hq1
  have hQd : r₀.getMem (s.getReg .x2 - 456) = r₁.getMem (s.getReg .x2 - 456) := (m₁ _).symm
  -- `0x8000b334`
  have sp₁ : r₁.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans A.sp
  obtain ⟨r₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000b334_spec hpc₁ (by
    rv_eval [sp₁]; and_intros <;> valid_access hst.valid [hb])
  have k₂ := b8000b334_keeps h₂
  have X₂ : DFrame r₁ r₂ fun y ↦ Within y (s.getReg .x2 - 784) 8 ∨
      Within y (s.getReg .x2 - 904) 8 :=
    (holds_dframe h₂).mono fun a ⟨q, hq, hw⟩ ↦ by
      simp only [b8000b334, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rv_eval [sp₁] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr (by addr_omega [hw, hb])
  have m256 := b8000b334_m_x2_256 h₂
  have m136 := b8000b334_m_x2_136 h₂
  rw [sp₁, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval [],
    show s.getReg .x2 - 1040 + 520 = s.getReg .x2 - 520 by rv_eval [], m₁] at m256
  rw [sp₁, show s.getReg .x2 - 1040 + 136 = s.getReg .x2 - 904 by rv_eval [],
    show s.getReg .x2 - 1040 + 512 = s.getReg .x2 - 528 by rv_eval [], m₁] at m136
  have sp₂ : r₂.getReg .x2 = s.getReg .x2 - 1040 := (k₂ .x2 (by decide)).trans sp₁
  have F₂ : DFrame k r₂ fun y ↦ A0W s k' r₀ y ∨ Within y (s.getReg .x2 - 784) 8 ∨
      Within y (s.getReg .x2 - 904) 8 :=
    ((F₀.trans (DFrame.of_same m₁ _) fun _ h ↦ h).mono fun _ h ↦ Or.inl h).trans X₂
      fun _ h ↦ Or.inr h
  have nx₂ : r₂.getMem nextAddr = r₀.getMem nextAddr := by
    rw [X₂ _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hnx], m₁]
  have hn₂ : heapNext r₂ = heapNext r₀ := by simp only [heapNext, nx₂]
  have h₂h : HeapOk r₂ := ⟨by rw [hn₂]; exact h₀.lo, by rw [hn₂]; exact h₀.hi⟩
  have hX (y : Word) (h : A0W s k' r₀ y ∨ Within y (s.getReg .x2 - 784) 8 ∨
      Within y (s.getReg .x2 - 904) 8) : Within y (s.getReg .x2 - 2464) 2464 ∨
      Within y nextAddr 8 ∨ (heapNext k ≤ y.toNat ∧ y.toNat < heapNext r₂) := by
    simp only [A0W, Fresh] at h
    rcases h with (h | h | h | h | ⟨h1, h2⟩) | h | h
    · exact Or.inl (by addr_omega [h, hb])
    · exact Or.inl (by addr_omega [h, hb])
    · exact Or.inl (by addr_omega [h, hb])
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inl (by addr_omega [h, hb])
    · exact Or.inl (by addr_omega [h, hb])
  have kslot (y : Word) (hy : (s.getReg .x2 - 880).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 800).toNat ∨
      (s.getReg .x2 - 528).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat) :
      r₂.getMem y = k.getMem y :=
    F₂ y fun c hc ↦ pre_miss hpre h₀ (by addr_omega [hc, hy, hb])
  -- the kernel
  have KV := hk.ker
  have hraw := KV.vec.raw
  have hkl := KV.vec.len
  simp only [RawVecOk, Buf] at hraw
  have hkh := hk.heap
  have hlwl : (Model.eqKernelRust lf).length = (vecLen k (s.getReg .x2 - 536)).toNat := by
    rw [← KV.elems, vecEs, eListAt_length]
  have kb : (Model.eqKernelRust lf).length = 0 ∨
      (heapStart ≤ (vecPtr k (s.getReg .x2 - 536)).toNat ∧
        (vecPtr k (s.getReg .x2 - 536)).toNat + 24 * (Model.eqKernelRust lf).length ≤
          heapNext k) := by
    rcases Nat.eq_zero_or_pos (Model.eqKernelRust lf).length with h0 | hpos
    · exact Or.inl h0
    · right
      rw [hlwl] at hpos ⊢
      rcases hraw.2 with h0 | ⟨h1, h2⟩
      · omega
      · exact ⟨h1, by omega⟩
  have k0slot (y : Word) (hy : (s.getReg .x2 - 528).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat) : r₀.getMem y = k.getMem y :=
    F₀ y fun c hc hw ↦ pre_miss hpre h₀ (by addr_omega [hc, hy, hb]) (Or.inl hw)
  have inv₁ : InvR s r₁ (r₀.getMem nextAddr) := Inv.same' A.inv m₁ (k₁ .x2 (by decide))
  have inv₂ : InvR s r₂ (r₂.getMem nextAddr) :=
    Inv.step' hpre inv₁ X₂
      (fun y hy ↦ Or.inr (Or.inl (in_stack hpre (by
        rcases hy with hy | hy <;> addr_omega [hy, hb]))))
      (fun y hy ↦ by rcases hy with hy | hy <;> addr_omega [hy, hb]) rfl
      (le_of_eq (by rw [nx₂])) (by rw [nx₂]; exact h₀.hi) (k₂ .x2 (by decide))
  have hq2' : (r₀.getMem (s.getReg .x2 - 456)).toNat + 24 * ws.length ≤ heapEnd :=
    le_trans hq2 h₀.hi
  have hkhi := hkh.hi
  have K : R0K s r₂ (r₀.getMem (s.getReg .x2 - 456)) ws.length (vecPtr k (s.getReg .x2 - 536))
      (Model.eqKernelRust lf) := {
    kp := kb.imp id fun ⟨h1, h2⟩ ↦
      heap_region (by simp only [heapStart] at h1; omega) (by omega) hraw.1
    kmiss := fun y hy hw ↦ by
      rcases kb with h0 | ⟨h1, h2⟩
      · rw [h0] at hy; addr_omega [hy]
      · simp only [R0W] at hw
        rcases hw with hw | hw | hw
        · addr_omega [hw, hy, h2, hkhi, hb, hab]
        · addr_omega [hw, hy, h2, hkhi, hb, hab]
        · addr_omega [hw, hy, h2, hq1]
    kfit := kb.imp id fun ⟨_, h2⟩ ↦ by omega
    elems := by
      conv_rhs => rw [← KV.elems]
      rw [vecEs, ← hlwl]
      refine F₂.eListAt fun c hc hw ↦ ?_
      rcases kb with h0 | ⟨h1, h2⟩
      · omega
      · rcases hX _ hw with h | h | ⟨h3, -⟩
        · addr_omega [h, hc, h2, hkhi, hb, hab]
        · addr_omega [h, hc, h2, hkhi]
        · addr_omega [h3, hc, h2]
    ro := inv₂.rodata' hpre
    q1 := le_trans hkh.lo hq1
    q2 := hq2'
    q8 := hQ8
    m904 := by
      rw [m136, k0slot _ (by addr_omega [hb])]
      simp only [vecPtr]
      congr 1
      rv_eval []
    m784 := by
      rw [m256, k0slot _ (by addr_omega [hb]), hlwl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      simp only [vecLen]
      congr 1
      rv_eval [] }
  -- the rows
  obtain ⟨hPR, hPC⟩ := hL.slices.resolve_left hn0
  have hPb := Region.bounds hPR
  obtain ⟨⟨hPs1, hPs2, hPs3⟩, -⟩ := id hPC
  have pkeep (y : Word) (hy : (k.getMem (s.getReg .x2 - 832)).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (k.getMem (s.getReg .x2 - 832)).toNat + 16 * ws.length) :
      r₂.getMem y = k.getMem y :=
    keep0 h₂h hX F₂ hPs1 hPs2 hPs3 (by omega) hy
  have Pp : R0P s r₂ (r₀.getMem (s.getReg .x2 - 456)) ws.length (k.getMem (s.getReg .x2 - 832))
      ws := {
    len := rfl
    p := Or.inr hPR
    pmiss := clear_r0w hpre hq1 hq2' hPC
    m832 := kslot _ (by addr_omega [hb])
    row := fun j hj ↦ by
      have hbj := hL.buf j hj
      have hwj := hL.words j hj
      rw [kListAt_of_readWords] at hwj
      have hlen : ws[j].length = (sliceL s k j).toNat := by rw [← hwj]; simp [kListAt]
      rw [show r₂.getMem (k.getMem (s.getReg .x2 - 832) + BitVec.ofNat 64 (16 * j)) = sliceP s k j
        from pkeep _ (by addr_omega [hPb, hj])]
      exact {
        words := by
          conv_rhs => rw [← hwj]
          rw [hlen]
          apply kListAt_congr0
          intro i hi
          rcases hbj with h0 | ⟨hR, ⟨⟨c1, c2, c3⟩, -⟩⟩
          · omega
          · have := Region.bounds hR
            exact keep0 h₂h hX F₂ c1 c2 c3 (by omega) (by addr_omega [this, hi])
        region := by rw [hlen]; exact hbj.imp id (·.1)
        miss := by
          rw [hlen]
          rcases hbj with h0 | ⟨-, hC⟩
          · intro y hy; rw [h0] at hy; addr_omega [hy]
          · exact clear_r0w hpre hq1 hq2' hC }
    rlen := fun j hj ↦ by
      have hwj := hL.words j hj
      rw [kListAt_of_readWords] at hwj
      rw [pkeep _ (by addr_omega [hPb, hj]), ← hwj]
      simp [kListAt, sliceL] }
  -- the loop
  have O₀ : R0O s r₂ (r₀.getMem (s.getReg .x2 - 456)) ws.length (Model.eqKernelRust lf) ws 0
      r₂ := {
    base := ⟨sp₂, DFrame.refl _ _, rfl, rfl⟩
    x20 := by rw [k₂ .x20 (by decide), k₁ .x20 (by decide), x20₀]
    x21 := by rw [b8000b334_x21 h₂]; rfl
    x25 := by rw [k₂ .x25 (by decide), x25₁]
    x27 := by rw [k₂ .x27 (by decide), x27₁]; rfl
    x23 := fun h ↦ absurd h (Nat.lt_irrefl 0)
    vals := rfl }
  obtain ⟨u, hr₃, ⟨hpc₃, O⟩ | hd⟩ := rows0 hMK hpre K Pp hnpos (b8000b334_pc h₂) O₀
  swap
  · exact ⟨u, hr₀.trans (hr₁.trans (hr₂.trans hr₃)), Or.inl (Or.inl hd)⟩
  have B := O.base
  have nxu : u.getMem nextAddr = r₂.getMem nextAddr := B.fr _ fun c hc hw ↦ by
    simp only [R0W] at hw
    rcases hw with hw | hw | hw
    · addr_omega [hw, hc, hb, hnx]
    · addr_omega [hw, hc, hb, hnx]
    · addr_omega [hw, hc, hq2', hnx]
  have hnu : heapNext u = heapNext r₀ := by simp only [heapNext, nxu, nx₂]
  have hwl64 : ws.length < 2 ^ 64 := hwl
  have reg₂ (q : Reg) (hq : q ∈ ([.x9, .x26] : List Reg)) : u.getReg q = k.getReg q := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [B.x9, k₂ .x9 (by decide), k₁ .x9 (by decide), kreg .x9 (by decide)]
    · rw [B.x26, k₂ .x26 (by decide), k₁ .x26 (by decide), kreg .x26 (by decide)]
  refine ⟨u, hr₀.trans (hr₁.trans (hr₂.trans hr₃)), Or.inr {
    pc := hpc₃
    sp := B.sp
    regs := fun q hq ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact reg₂ .x9 (by decide)
      · rw [O.x23 hnpos, kslot _ (by addr_omega [hb]), h808]
      · exact reg₂ .x26 (by decide)
    inv := Inv.step' hpre inv₂ B.fr (fun y hy ↦ ?_) (fun y hy ↦ ?_) rfl
      (le_of_eq (by rw [nxu]))
      (by rw [nxu, nx₂]; exact h₀.hi) (B.sp.trans sp₂.symm)
    heap := ⟨by rw [hnu]; exact h₀.lo, by rw [hnu]; exact h₀.hi⟩
    mono := by rw [hnu, ← hn']; exact A.mono
    value := by
      rw [O.x25, O.x27, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwl64, O.vals, List.take_length]
      simp [Model.Pcs.rowValuesRust]
    buf := by
      rw [O.x25, O.x27, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwl64]
      simp only [NewBuf]
      exact ⟨hQ8, Or.inr ⟨hq1, by rw [hnu]; exact hq2⟩⟩
    fr := (F₂.mono fun y h ↦ ?_).trans B.fr fun y h ↦
      r0w_roww hpre hq1 (by rw [hnu]; exact hq2) h }⟩
  · simp only [R0W] at hy
    rcases hy with hy | hy | hy
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [hy, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [hy, hb])))
    · have := inv'.mono
      have h4 : heapNext k' ≤ (k'.getMem nextAddr).toNat := le_refl _
      refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
      · simp only [heapNext] at hq1 hn' this ⊢; addr_omega [hy, hq1, hn', this]
      · have e : (u.getMem nextAddr).toNat = heapNext r₀ := hnu
        rw [e]; addr_omega [hy, hq2]
  · simp only [R0W] at hy
    rcases hy with hy | hy | hy
    · addr_omega [hy, hb]
    · addr_omega [hy, hb]
    · addr_omega [hy, hq2', hb, hab]
  · rcases h with h | h | h
    · exact a0w_roww hpre hn' (le_of_eq hnu.symm) h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h

end Rv64Verifier.Proofs.Pcs.Vso
