import Rv64Verifier.Proofs.Walk.R18A

/-!
# `walk` R18, the table claims: the loop's head

`claims.extend(..)` for each of the six tables' evaluations, zipped with `GLOBAL_COLUMN_BASES` (on
the stack at `S - 896`). `LoopR18`: at the outer loop's head `0x80003854`, `k` tables done, the
claims `Vec` at `S - 1632` (capacity `C`, buffer `P`, length `L`) holding the bus's claims and the
first `k` tables' (`claims`), every claim's point allocated by `walk` apart from the buffer
(`points`), and the evaluations as `table_sumcheck` left them at `t` (`evKept`). `r18Entry`: from
`AtR18` to the head with `k = 0`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The claims' list in the buffer at `P`, `L` of them. -/
def claimsIn (u : MachineState) (P : Word) (L : Nat) : List ColumnClaim :=
  (List.range L).map fun i ↦ claimAt u (P + BitVec.ofNat 64 (56 * i))

/-- At `0x80003854`, `k` tables' claims appended. -/
structure LoopR18 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (k : Nat)
    (P C L : Word) : Prop where
  pc : u.pc = 0x80003854
  rest : Rest s u₀ u
  wmono : heapNext u₀ ≤ heapNext w
  tmono : heapNext t ≤ heapNext u
  evKept : ∀ x : Word, heapNext w ≤ x.toNat → x.toNat + 8 ≤ heapNext t → u.getMem x = t.getMem x
  rowsAt : RowsAt w t (s.getReg .x2 - 928) evs
  hk : k ≤ 6 ∧ k ≤ evs.length
  x8 : u.getReg .x8 = 6
  x9 : u.getReg .x9 = 0xffffffffffffffff
  x18 : u.getReg .x18 = BitVec.ofNat 64 k
  x19 : u.getReg .x19 = s.getReg .x2 - 896
  x21 : u.getReg .x21 = s.getReg .x2 - 1312
  x22 : u.getReg .x22 = vecPtr t (s.getReg .x2 - 928) + 48 * vecLen t (s.getReg .x2 - 928)
  x23 : u.getReg .x23 = vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)
  x25 : u.getReg .x25 = L
  bases : ∀ i < 6, u.getMem (s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * i)) =
    BitVec.ofNat 64 (LayoutMirror.globalColumnBasesRust.getD i 0)
  capSlot : u.getMem (s.getReg .x2 - 1632) = C
  ptrSlot : u.getMem (s.getReg .x2 - 1624) = P
  lenSlot : u.getMem (s.getReg .x2 - 1616) = L
  ptr184 : u.getMem (s.getReg .x2 - 2472) = P
  len : L.toNat ≤ C.toNat
  /-- The buffer: `u₀`'s, or one allocated after `table_sumcheck`. -/
  buf : P.toNat % 8 = 0 ∧ P.toNat + 56 * C.toNat ≤ heapNext u ∧
    ((P = vecPtr u₀ (s.getReg .x2 - 928) ∧ C = vecCap u₀ (s.getReg .x2 - 928)) ∨
      heapNext t ≤ P.toNat)
  claims : claimsIn u P L.toNat = bus.claims ++ tableClaimsRust (evs.take k)
  points : ∀ i < L.toNat, Old s u (vecPtr u (P + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen u (P + BitVec.ofNat 64 (56 * i))).toNat) ∧
    Apart (vecPtr u (P + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen u (P + BitVec.ofNat 64 (56 * i))).toNat) P (56 * C.toNat)
  tracks : TracksR OI s u
    (PcsContracts.digestAt u₀ (s.getReg .x2 - 1800), stackShape layout.stackLog lir.toNat)
    (afterTables (bytesAt s (s.getReg .x12) 32) layout rows lir bus evs)

theorem Old.mono {s u v : MachineState} {p : Word} {n : Nat} (h : Old s u p n)
    (hm : heapNext u ≤ heapNext v) : Old s v p n :=
  ⟨h.1, h.2.1.trans hm, h.2.2⟩

/-- A claim whose header and point lie in memory that agrees. -/
theorem claimAt_congr {u v : MachineState} {N : Nat}
    (hm : ∀ y : Word, y.toNat + 8 ≤ N → u.getMem y = v.getMem y) (hN : N ≤ 2 ^ 63) {x : Word}
    (hx : x.toNat + 56 ≤ N) (hp : (vecPtr v x).toNat + 24 * (vecLen v x).toNat ≤ N) :
    claimAt u x = claimAt v x := by
  have g (c : Nat) (hc : c ≤ 48) (y : Word) (hy : y = x + BitVec.ofNat 64 c) :
      u.getMem y = v.getMem y := by
    subst hy; exact hm _ (by addr_omega [hx, hc, hN])
  have e0 : u.getMem x = v.getMem x := g 0 (by omega) x (by rw [add_ofNat_zero])
  have ep : vecPtr u x = vecPtr v x := g 8 (by omega) _ rfl
  have el : vecLen u x = vecLen v x := g 16 (by omega) _ rfl
  simp only [claimAt, vecEs, ep, el, g 24 (by omega) (x + 24) rfl]
  congr 1
  · exact Bus.eListAt_congr fun i hi ↦ eAt_congr (hm _ (by addr_omega [hp, hi, hN]))
      (hm _ (by addr_omega [hp, hi, hN])) (hm _ (by addr_omega [hp, hi, hN]))
  · exact eAt_congr (g 32 (by omega) _ rfl) (g 40 (by omega) _ (by bv_omega))
      (g 48 (by omega) _ (by bv_omega))

/-- `0x800037c0`'s frame writes. -/
@[rv_addr] def W37c0 (s : MachineState) (a : Word) : Prop :=
  a = s.getReg .x2 - 2616 ∨ a = s.getReg .x2 - 840 ∨ a = s.getReg .x2 - 848 ∨
  a = s.getReg .x2 - 888 ∨ a = s.getReg .x2 - 896 ∨ a = s.getReg .x2 - 904 ∨
  a = s.getReg .x2 - 920 ∨ a = s.getReg .x2 - 856 ∨ a = s.getReg .x2 - 864 ∨
  a = s.getReg .x2 - 872 ∨ a = s.getReg .x2 - 880 ∨ a = s.getReg .x2 - 2608 ∨
  a = s.getReg .x2 - 1616 ∨ a = s.getReg .x2 - 1624 ∨ a = s.getReg .x2 - 1632

theorem W37c0_ok {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {a : Word}
    (ha : W37c0 s a) : InF s a ∧ ¬ KeepR s u₀ a := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slot_ok (k := 2616) hpre h (by omega) (by omega)
  · exact slot_ok (k := 840) hpre h (by omega) (by omega)
  · exact slot_ok (k := 848) hpre h (by omega) (by omega)
  · exact slot_ok (k := 888) hpre h (by omega) (by omega)
  · exact slot_ok (k := 896) hpre h (by omega) (by omega)
  · exact slot_ok (k := 904) hpre h (by omega) (by omega)
  · exact slot_ok (k := 920) hpre h (by omega) (by omega)
  · exact slot_ok (k := 856) hpre h (by omega) (by omega)
  · exact slot_ok (k := 864) hpre h (by omega) (by omega)
  · exact slot_ok (k := 872) hpre h (by omega) (by omega)
  · exact slot_ok (k := 880) hpre h (by omega) (by omega)
  · exact slot_ok (k := 2608) hpre h (by omega) (by omega)
  · exact slot_ok (k := 1616) hpre h (by omega) (by omega)
  · exact slot_ok (k := 1624) hpre h (by omega) (by omega)
  · exact slot_ok (k := 1632) hpre h (by omega) (by omega)

theorem bases_val : LayoutMirror.globalColumnBasesRust = [6, 21, 36, 44, 59, 73] := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- From `AtR18` to the loop's head, no table done. -/
theorem r18Entry {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ w t : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} {evs : List (List E × List E)} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (H : AtR18 OI s u₀ w t layout rows lir bus evs) :
    ∃ u, Reaches Image.code t u ∧ LoopR18 OI s u₀ w t u layout rows lir bus evs 0
      (vecPtr u₀ (s.getReg .x2 - 928)) (vecCap u₀ (s.getReg .x2 - 928))
      (vecLen u₀ (s.getReg .x2 - 928)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have R := H.rest
  have sp := R.inv.sp
  have ea (c d : Word) (hc : c.toNat + d.toNat = 2656) : t.getReg .x2 + c = s.getReg .x2 - d := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800037ac_spec H.pc (by
    rv_eval [sp]; and_intros <;> valid_access hval [hb1])
  have m₁ := b800037ac_mem_same h₁
  have k₁ := b800037ac_keeps h₁
  have pc₁ := b800037ac_pc_not_taken h₁ (by rw [ea 1728 928 rfl]; exact H.ok)
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide), sp]
  have R₁ := R.same m₁ (k₁ .x2 (by decide))
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800037c0_spec pc₁ (by
    rv_eval [sp₁]; and_intros <;> valid_access hval [hb1])
  have k₂ := b800037c0_keeps h₂
  have sp₂ : u₂.getReg .x2 = u₁.getReg .x2 := k₂ .x2 (by decide)
  have st : StepW s u₁ u₂ (W37c0 s) False := StepW.ofFrame hpre R₁.inv.heap (h₂.dframe (by
      rv_eval [sp₁]; simp only [W37c0, true_or, or_true, and_self]))
    (fun a ha ↦ (W37c0_ok hpre R₁ ha).1) sp₂
  have R₂ := R₁.stepW hpre (fun a ha ↦ W37c0_ok hpre R₁ ha) st
  have fW : ∀ a, W37c0 s a → InF s a := fun a ha ↦ (W37c0_ok hpre R₁ ha).1
  have hn₁ : heapNext u₁ = heapNext t := by simp only [heapNext, m₁]
  have m₀ := R.mono
  have oldT : ∀ x : Word, x.toNat + 8 ≤ heapNext t → u₂.getMem x = t.getMem x := fun x hx ↦ by
    rw [st.getH hpre fW (by omega), m₁]
  have old₂ : ∀ x : Word, x.toNat + 8 ≤ heapNext u₀ → u₂.getMem x = u₀.getMem x := fun x hx ↦ by
    rw [oldT x (by omega), H.old x hx]
  have eb (c d : Word) (hc : c.toNat + d.toNat = 2656) : u₁.getReg .x2 + c = s.getReg .x2 - d := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have gF (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648) (hw : ∀ i < 8,
      ¬ W37c0 s (s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i)) :
      u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
    rw [st.getF hpre (by addr_omega [hb1, hk]) hw fun hf ↦ hf.elim, m₁]
  have hh := R.inv.heap.hi
  have hN : heapNext u₀ ≤ 2 ^ 63 := by simp only [heapNext, heapEnd] at hh m₀ ⊢; omega
  have B := h.busAt.claims
  have CO := h.claimsOld
  simp only [Old] at CO
  have e920 : t.getMem (s.getReg .x2 - 920) = vecPtr t (s.getReg .x2 - 928) := by
    rw [vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e912 : t.getMem (s.getReg .x2 - 912) = vecLen t (s.getReg .x2 - 928) := by
    rw [vecLen]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e920₀ : u₀.getMem (s.getReg .x2 - 920) = vecPtr u₀ (s.getReg .x2 - 928) := by
    rw [vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e912₀ : u₀.getMem (s.getReg .x2 - 912) = vecLen u₀ (s.getReg .x2 - 928) := by
    rw [vecLen]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hlen := B.1.len
  -- the claims' headers and points, as at `u₀`
  have hdr (i : Nat) (hi : i < (vecLen u₀ (s.getReg .x2 - 928)).toNat) (c : Nat) (hc : c ≤ 16) :
      (vecPtr u₀ (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c).toNat + 8 ≤
        heapNext u₀ := by
    addr_omega [CO.2.1, hi, hc, hlen, hN]
  have pv (i : Nat) (hi : i < (vecLen u₀ (s.getReg .x2 - 928)).toNat) :
      vecPtr u₂ (vecPtr u₀ (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i)) =
        vecPtr u₀ (vecPtr u₀ (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i)) ∧
      vecLen u₂ (vecPtr u₀ (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i)) =
        vecLen u₀ (vecPtr u₀ (s.getReg .x2 - 928) + BitVec.ofNat 64 (56 * i)) :=
    ⟨old₂ _ (hdr i hi 8 (by omega)), old₂ _ (hdr i hi 16 (by omega))⟩
  refine ⟨u₂, hr₁.trans hr₂, {
    pc := b800037c0_pc h₂
    rest := R₂
    wmono := H.mono
    tmono := by have := st.mono; omega
    evKept := fun x _ hx ↦ oldT x hx
    rowsAt := H.rowsAt
    hk := ⟨by omega, by omega⟩
    x8 := by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), H.x8]
    x9 := by rw [k₂ .x9 (by decide), b800037ac_x9 h₁]
    x18 := b800037c0_x18 h₂
    x19 := by rw [b800037c0_x19 h₂, eb 1760 896 rfl]
    x21 := by rw [b800037c0_x21 h₂, eb 1344 1312 rfl]
    x22 := by
      rw [b800037c0_x22 h₂, b800037ac_x23 h₁, b800037ac_x11 h₁, ea 1736 920 rfl, ea 1744 912 rfl,
        e920, e912]
      bv_omega
    x23 := by
      rw [k₂ .x23 (by decide), b800037ac_x23 h₁, ea 1736 920 rfl, e920]
      simp
    x25 := by rw [k₂ .x25 (by decide), k₁ .x25 (by decide), H.regs .x25 (by decide), h.x25, e912₀]
    bases := fun i hi ↦ by
      rw [bases_val]
      interval_cases i
      · rw [show s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * 0) = u₁.getReg .x2 + 1760 by rw [sp₁]; bv_omega,
          b800037c0_m_x2_1760 h₂, k₁ .x8 (by decide), H.x8]; rfl
      · rw [show s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * 1) = u₁.getReg .x2 + 1768 by rw [sp₁]; bv_omega,
          b800037c0_m_x2_1768 h₂]; rfl
      · rw [show s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * 2) = u₁.getReg .x2 + 1776 by rw [sp₁]; bv_omega,
          b800037c0_m_x2_1776 h₂]; rfl
      · rw [show s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * 3) = u₁.getReg .x2 + 1784 by rw [sp₁]; bv_omega,
          b800037c0_m_x2_1784 h₂]; rfl
      · rw [show s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * 4) = u₁.getReg .x2 + 1792 by rw [sp₁]; bv_omega,
          b800037c0_m_x2_1792 h₂]; rfl
      · rw [show s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * 5) = u₁.getReg .x2 + 1800 by rw [sp₁]; bv_omega,
          b800037c0_m_x2_1800 h₂]; rfl
    capSlot := by
      rw [← eb 1024 1632 rfl, b800037c0_m_x2_1024 h₂, k₁ .x19 (by decide), H.regs .x19 (by decide),
        h.x19]; rfl
    ptrSlot := by
      rw [← eb 1032 1624 rfl, b800037c0_m_x2_1032 h₂, eb 184 2472 rfl, m₁, H.m184, e920₀]
    lenSlot := by
      rw [← eb 1040 1616 rfl, b800037c0_m_x2_1040 h₂, k₁ .x25 (by decide), H.regs .x25 (by decide),
        h.x25, e912₀]
    ptr184 := by
      rw [show (2472 : Word) = BitVec.ofNat 64 2472 from rfl, gF 2472 (by omega) (fun i hi hw ↦ by
        simp only [W37c0] at hw
        rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw <;>
          · have := congrArg BitVec.toNat hw; addr_omega [this, hb1, hi])]
      exact H.m184.trans e920₀
    len := hlen
    buf := ⟨CO.1, by have := st.mono; omega, Or.inl ⟨rfl, rfl⟩⟩
    claims := by
      rw [List.take_zero, show tableClaimsRust [] = [] from rfl, List.append_nil, ← B.2.2.1]
      simp only [claimsIn]
      refine List.map_congr_left fun i hi ↦ ?_
      simp only [List.mem_range] at hi
      have hp := h.claimPoints i hi
      simp only [Old] at hp
      exact claimAt_congr old₂ hN (by addr_omega [CO.2.1, hi, hlen, hN]) hp.2.1
    points := fun i hi ↦ by
      obtain ⟨e1, e2⟩ := pv i hi
      rw [e1, e2]
      exact ⟨(h.claimPoints i hi).mono (by have := st.mono; omega), h.claimsApart i hi⟩
    tracks := H.tracks.keep fun T hT ↦ st.transcript hpre R₁.inv (by
        have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
        rw [etp, R₁.get (keep_slot hpre (by omega)), ← etp]; exact h.proofPtr)
      (fun a ha ↦ ⟨fW a ha, by
        simp only [W37c0] at ha
        rw [tp]
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> addr_omega [hb1]⟩)
      ((StepW.same R.inv.heap m₁ (k₁ .x2 (by decide)) (fun _ ↦ False) False).transcript hpre R.inv
        (by
          have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
          rw [etp, R.get (keep_slot hpre (by omega)), ← etp]; exact h.proofPtr)
        (fun _ hf ↦ hf.elim) hT) }⟩

end Rv64Verifier.Proofs.Walk
