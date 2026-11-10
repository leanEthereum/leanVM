import Rv64Verifier.Proofs.Walk.R18E
import Rv64Verifier.Proofs.Walk.R18Blk

/-!
# `walk` R18, the table claims: one value's claim

`innerStore`: from `clone`'s return at `0x800038a8`, the claim `(point, base + j, value)` built at
`S - 1344` (`0x800038a8`) and copied to the buffer's next slot (`0x800038c4`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4S Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem tableClaimsOf_length (evs : List (List E × List E)) (k : Nat) :
    (tableClaimsOf evs k).length = (evs.getD k ([], [])).2.length := by
  simp [tableClaimsOf]

theorem tableClaimsOf_take_succ (evs : List (List E × List E)) (k j : Nat)
    (hj : j < (evs.getD k ([], [])).2.length) :
    (tableClaimsOf evs k).take (j + 1) = (tableClaimsOf evs k).take j ++
      [⟨LayoutMirror.globalColumnBasesRust.getD k 0 + j, (evs.getD k ([], [])).1,
        (evs.getD k ([], [])).2.getD j 0⟩] := by
  rw [List.take_add_one]
  congr 1
  have hj' : j < (evs[k]?.getD ([], [])).2.length := by simpa using hj
  simp [tableClaimsOf, List.getElem?_eq_getElem hj']

theorem bases_le (k : Nat) (hk : k < 6) : LayoutMirror.globalColumnBasesRust.getD k 0 ≤ 73 := by
  rw [bases_val]; interval_cases k <;> decide

section Store
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {k j : Nat} {P C L : Word}

set_option maxHeartbeats 1600000 in
/-- The claim for table `k`'s value `j` stored, from `clone`'s return. -/
theorem innerStore (hpre : WalkPre s)
    (H : InnerR18 OI s u₀ w t u layout rows lir bus evs k j P C L) {v : MachineState}
    (hpc : v.pc = 0x800038a8) (hreg : ∀ r ∈ calleeSaved, v.getReg r = u.getReg r)
    (Cv : CoreR18 OI s u₀ w t v layout rows lir bus evs P C (L.toNat + j)
      (bus.claims ++ tableClaimsRust (evs.take k) ++ (tableClaimsOf evs k).take j))
    (hel : vecEs v (s.getReg .x2 - 1344) = (evs.getD k ([], [])).1)
    (hfr : (vecLen v (s.getReg .x2 - 1344)).toNat = 0 ∨
      heapNext u ≤ (vecPtr v (s.getReg .x2 - 1344)).toNat ∧
      (vecPtr v (s.getReg .x2 - 1344)).toNat + 24 * (vecLen v (s.getReg .x2 - 1344)).toNat ≤
        heapNext v)
    (hal : (vecPtr v (s.getReg .x2 - 1344)).toNat % 8 = 0)
    (hls : v.getMem (s.getReg .x2 - 1616) = L) :
    ∃ v₂, Reaches Image.code v v₂ ∧
      CoreR18 OI s u₀ w t v₂ layout rows lir bus evs P C (L.toNat + (j + 1))
        (bus.claims ++ tableClaimsRust (evs.take k) ++ (tableClaimsOf evs k).take (j + 1)) ∧
      v₂.getMem (s.getReg .x2 - 1616) = L ∧
      (∀ r ∈ ([.x8, .x9, .x18, .x19, .x21, .x22, .x23, .x25] : List Reg),
        v₂.getReg r = u.getReg r) ∧
      v₂.getReg .x20 = u.getReg .x20 - 1 ∧ v₂.getReg .x24 = u.getReg .x24 + 24 ∧
      v₂.getReg .x26 = u.getReg .x26 + 1 ∧ v₂.getReg .x27 = u.getReg .x27 + 56 ∧
      (u.getReg .x20 - 1 ≠ 0 → v₂.pc = 0x80003894) ∧
      (u.getReg .x20 - 1 = 0 → v₂.pc = 0x8000390c) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have spv : v.getReg .x2 = s.getReg .x2 - 2656 := Cv.rest.inv.sp
  have hk := H.hk
  have hj := H.hj
  have hroom := H.room
  have hh := Cv.rest.inv.heap.hi
  have htv := Cv.tmono
  have hwm := Cv.wmono
  have hsm := Cv.smono
  have hs0 := hpre.heap.lo
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd, heapStart] at hh hab hs0
  obtain ⟨bal, bhi, blo, -⟩ := Cv.buf
  have bhu := H.buf.2.1
  have hsu := H.rest.inv.mono
  have hjC : L.toNat + j + 1 ≤ C.toNat := by omega
  have hPs : heapNext s ≤ P.toNat := by omega
  -- the values
  have pv := (H.rowsAt.pairs k hk.2).2
  obtain ⟨Va, Vl, Vb⟩ := newVecE_facts pv
  have hgd : evs.getD k ([], []) = evs[k] := List.getD_eq_getElem _ _ hk.2
  have hjn : j < evs[k].2.length := by rw [← hgd]; exact hj
  rcases Vb with V0 | ⟨V1, V2⟩
  · omega
  -- registers at `v`
  have x21v : v.getReg .x21 = s.getReg .x2 - 1312 := by rw [hreg .x21 (by decide), H.x21]
  have x24v : v.getReg .x24 = vecPtr t (vecPtr t (s.getReg .x2 - 928) +
      BitVec.ofNat 64 (48 * k + 24)) + BitVec.ofNat 64 (24 * j) := by
    rw [hreg .x24 (by decide), H.x24]
  have x27v : v.getReg .x27 = P + BitVec.ofNat 64 (56 * (L.toNat + j)) := by
    rw [hreg .x27 (by decide), H.x27]
  -- `0x800038a8`: the value and the column on the stack
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches c800038a8_spec hpc (by
    rv_eval [spv, x21v, x24v]
    and_intros <;> first
      | valid_access hval [hb1, hb3]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [V1, V2, Va, Vl, hjn, htv, hh, hwm, hsm, hs0])
      | addr_omega [V1, V2, Vl, hjn, htv, hh, hb1, hab])
  have k₁ := c800038a8_keeps h₁
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide), spv]
  have W₁ok : ∀ a, Within a (s.getReg .x2 - 1320) 32 → InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦
    range_ok hpre Cv.rest (c := 1320) (k := 1320) (n := 32) rfl (by omega) (by omega) ha
  have st₁ : StepW s v v₁ (Within · (s.getReg .x2 - 1320) 32) False :=
    StepW.ofFrame hpre Cv.rest.inv.heap (h₁.dframe (by
      rv_eval [spv, x21v]; and_intros <;> addr_omega [hb1])) (fun a ha ↦ (W₁ok a ha).1)
      (k₁ .x2 (by decide))
  have C₁ := Cv.stepW hpre st₁ (fun a ha ↦ ⟨(W₁ok a ha).1, (W₁ok a ha).2, by
      rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩)
    (fun a ha ↦ by simp only [Within] at ha ⊢; refine ⟨?_, ?_, ?_, ?_⟩ <;> addr_omega [ha, hb1])
  have g₁ : ∀ x : Word, x.toNat + 8 ≤ heapNext v → v₁.getMem x = v.getMem x :=
    fun x hx ↦ st₁.getH hpre (fun a ha ↦ (W₁ok a ha).1) hx
  have gF₁ (c : Nat) (hc : 1616 = c ∨ 1336 = c ∨ 1328 = c) :
      v₁.getMem (s.getReg .x2 - BitVec.ofNat 64 c) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 c) :=
    st₁.getF hpre (by rcases hc with rfl | rfl | rfl <;> addr_omega [hb1])
      (fun i hi hw ↦ by simp only [Within] at hw; rcases hc with rfl | rfl | rfl <;>
        addr_omega [hw, hi, hb1]) (fun hf ↦ hf.elim)
  -- `0x800038c4`: the claim copied to `P + 56 (L + j)`
  have x27₁ : v₁.getReg .x27 = P + BitVec.ofNat 64 (56 * (L.toNat + j)) := by
    rw [k₁ .x27 (by decide), x27v]
  have hX : (P + BitVec.ofNat 64 (56 * (L.toNat + j))).toNat = P.toNat + 56 * (L.toNat + j) := by
    addr_omega [bhi, hjC, hh]
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches c800038c4_spec (c800038a8_pc h₁) (by
    rv_eval [sp₁, x27₁]
    and_intros <;> first
      | valid_access hval [hb1, hb3]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [hX, bal, bhi, hjC, hh, hPs, hs0])
      | addr_omega [hX, bhi, hjC, hh, hb1, hab])
  have k₂ := c800038c4_keeps h₂
  have fr₂ : DFrame v₁ v₂ (Within · (P + BitVec.ofNat 64 (56 * (L.toNat + j))) 56) := by
    have := DFrame.of_memFrame (c800038c4_frame h₂ (by rw [x27₁]; addr_omega [hX, bhi, hjC, hh]))
    rwa [x27₁] at this
  have g₂ : ∀ y : Word, (y.toNat + 8 ≤ P.toNat + 56 * (L.toNat + j) ∨
      P.toNat + 56 * (L.toNat + j) + 56 ≤ y.toNat) → y.toNat + 8 ≤ 2 ^ 64 →
      v₂.getMem y = v₁.getMem y := fun y hy hw ↦
    fr₂ y fun i hi h' ↦ by simp only [Within] at h'; rw [hX] at h'; addr_omega [hy, hw, hi, h']
  have hn₂ : heapNext v₂ = heapNext v₁ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (g₂ nextAddr (Or.inr (by
      have : nextAddr.toNat = 2684358448 := rfl
      omega)) (by decide))
  have hn₁ := st₁.mono
  -- the claim
  have hbase := bases_le k hk.1
  have col : v₂.getMem (P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 24) =
      BitVec.ofNat 64 (LayoutMirror.globalColumnBasesRust.getD k 0 + j) := by
    rw [← x27₁, c800038c4_m_x27_24 h₂, k₁ .x26 (by decide), hreg .x26 (by decide), H.x26]
  have pt8 : v₂.getMem (P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 8) =
      vecPtr v (s.getReg .x2 - 1344) := by
    rw [← x27₁, c800038c4_m_x27_8 h₂, sp₁,
      show s.getReg .x2 - 2656 + 1320 = s.getReg .x2 - BitVec.ofNat 64 1336 by bv_omega,
      gF₁ 1336 (by omega)]
    show _ = v.getMem _
    congr 1; bv_omega
  have pt16 : v₂.getMem (P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 16) =
      vecLen v (s.getReg .x2 - 1344) := by
    rw [← x27₁, c800038c4_m_x27_16 h₂, sp₁,
      show s.getReg .x2 - 2656 + 1328 = s.getReg .x2 - BitVec.ofNat 64 1328 by bv_omega,
      gF₁ 1328 (by omega)]
    show _ = v.getMem _
    congr 1; bv_omega
  have val : eAt v₂ (P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 32) =
      (evs.getD k ([], [])).2.getD j 0 := by
    have a0 := c800038c4_m_x27_32 h₂
    have a1 := c800038c4_m_x27_40 h₂
    have a2 := c800038c4_m_x27_48 h₂
    rw [x27₁, sp₁] at a0 a1 a2
    have b0 := c800038a8_m_x21_0 h₁
    have b1 := c800038a8_m_x21_8 h₁
    have b2 := c800038a8_m_x21_16 h₁
    rw [x21v, x24v] at b0 b1 b2
    have e1 : eAt v₂ (P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 32) =
        eAt v (vecPtr t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + 24)) +
          BitVec.ofNat 64 (24 * j)) := by
      refine eAt_congr ?_ ?_ ?_
      · rw [a0, show s.getReg .x2 - 2656 + 1344 = s.getReg .x2 - 1312 by bv_omega, b0]
      · rw [show P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 32 + 8 =
          P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 40 by bv_omega, a1,
          show s.getReg .x2 - 2656 + 1352 = s.getReg .x2 - 1312 + 8 by bv_omega, b1]
      · rw [show P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 32 + 16 =
          P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 48 by bv_omega, a2,
          show s.getReg .x2 - 2656 + 1360 = s.getReg .x2 - 1312 + 16 by bv_omega, b2]
    have gv (c : Nat) (hc : c ≤ 16) (y : Word) (hy : y = vecPtr t (vecPtr t (s.getReg .x2 - 928) +
        BitVec.ofNat 64 (48 * k + 24)) + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 c) :
        v.getMem y = t.getMem y := by
      subst hy
      exact Cv.evKept _ (by addr_omega [V1, V2, Vl, hjn, hc, htv, hh])
        (by addr_omega [V1, V2, Vl, hjn, hc, htv, hh])
    rw [e1, eAt_congr (gv 0 (by omega) _ (by rw [add_ofNat_zero])) (gv 8 (by omega) _ rfl)
      (gv 16 (by omega) _ rfl), hgd, ← pv.elems, vecEs,
      List.getD_eq_getElem _ _ (by rw [eListAt_length]; omega), eListAt_getElem]
  have hc : claimAt v₂ (P + BitVec.ofNat 64 (56 * (L.toNat + j))) =
      ⟨LayoutMirror.globalColumnBasesRust.getD k 0 + j, (evs.getD k ([], [])).1,
        (evs.getD k ([], [])).2.getD j 0⟩ := by
    simp only [claimAt]
    rw [col, val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by addr_omega [V2, Vl, hjn, htv, hh, hbase])]
    congr 1
    show eListAt v₂ (v₂.getMem (P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 8))
      (v₂.getMem (P + BitVec.ofNat 64 (56 * (L.toNat + j)) + 16)).toNat = _
    rw [pt8, pt16, ← hel, vecEs]
    rcases hfr with h0 | ⟨f1, f2⟩
    · rw [h0]; rfl
    refine Bus.eListAt_congr fun i hi ↦ ?_
    have gp (c : Nat) (hc : c ≤ 16) (y : Word) (hy : y = vecPtr v (s.getReg .x2 - 1344) +
        BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) : v₂.getMem y = v.getMem y := by
      subst hy
      rw [g₂ _ (Or.inr (by addr_omega [f1, f2, hi, hc, bhu, hjC, hh, htv])) (by
        addr_omega [f1, f2, hi, hc, hh, htv]), g₁ _ (by addr_omega [f1, f2, hi, hc, hh, htv])]
    exact eAt_congr (gp 0 (by omega) _ (by rw [add_ofNat_zero])) (gp 8 (by omega) _ rfl)
      (gp 16 (by omega) _ rfl)
  have hpt : ((vecLen v₂ (P + BitVec.ofNat 64 (56 * (L.toNat + j)))).toNat = 0 ∨
        Old s v₂ (vecPtr v₂ (P + BitVec.ofNat 64 (56 * (L.toNat + j))))
          (24 * (vecLen v₂ (P + BitVec.ofNat 64 (56 * (L.toNat + j)))).toNat)) ∧
      Apart (vecPtr v₂ (P + BitVec.ofNat 64 (56 * (L.toNat + j))))
        (24 * (vecLen v₂ (P + BitVec.ofNat 64 (56 * (L.toNat + j)))).toNat) P (56 * C.toNat) := by
    simp only [vecPtr, vecLen] at pt8 pt16 ⊢
    rw [pt8, pt16]
    simp only [Old, Apart]
    rcases hfr with h0 | ⟨f1, f2⟩
    · simp only [vecLen] at h0; rw [h0]; simp
    · refine ⟨Or.inr ⟨hal, by simp only [vecPtr, vecLen] at f2; omega, Or.inr (by
        simp only [vecPtr] at f1; omega)⟩, Or.inr (Or.inr (Or.inr (by
        simp only [vecPtr] at f1; omega)))⟩
  have C₂ := C₁.store hpre (by omega) fr₂ (k₂ .x2 (by decide)) hc hpt
  refine ⟨v₂, hr₁.trans hr₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tableClaimsOf_take_succ evs k j hj, ← List.append_assoc]; exact C₂
  · rw [g₂ _ (Or.inr (by addr_omega [hb1, hab, bhi, hjC, hh])) (by addr_omega [hb1]),
      show (1616 : Word) = BitVec.ofNat 64 1616 from rfl, gF₁ 1616 (by omega)]
    exact hls
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₂ _ (by decide), k₁ _ (by decide), hreg _ (by decide)]
  · rw [c800038c4_x20 h₂, k₁ .x20 (by decide), hreg .x20 (by decide)]
  · rw [c800038c4_x24 h₂, k₁ .x24 (by decide), hreg .x24 (by decide)]
  · rw [c800038c4_x26 h₂, k₁ .x26 (by decide), hreg .x26 (by decide)]
  · rw [c800038c4_x27 h₂, x27₁, ← x27v, hreg .x27 (by decide)]
  · intro hc'
    exact c800038c4_pc_taken h₂ (by rw [k₁ .x20 (by decide), hreg .x20 (by decide)]; exact hc')
  · intro hc'
    exact c800038c4_pc_not_taken h₂ (by rw [k₁ .x20 (by decide), hreg .x20 (by decide)]; exact hc')

end Store

end Rv64Verifier.Proofs.Walk
