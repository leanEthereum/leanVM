import Rv64Verifier.Proofs.Pcs.BasisEq
import Rv64Verifier.Proofs.Pcs.BasisPlaced

/-!
# `<StackBasis>::evaluate`: the push, the loop, `dot`'s tail call, the contract
-/

namespace Rv64Verifier.Proofs.Pcs.Basis
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.MultilinearContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F55
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The push -/

theorem push {s u : MachineState} {nx WP : Word} {k : Nat} (hpre : BasisPre s)
    (hg : Got s u nx WP k) :
    ∃ v, Reaches Image.code u v ∧
      ((k + 1 < ncl s ∧ Head s v nx WP (k + 1) 0x8000d1ac) ∨ (k + 1 = ncl s ∧ End s v nx WP)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hk := hg.lt
  have hsp := hg.inv.sp
  have hPa := hg.buf.align
  have hPr := hg.buf.range.resolve_left (by omega)
  have hfit := hg.inv.fits
  have hlo := hpre.heap.lo
  have hab := hst.above
  have hnx8 := hst.next
  simp only [ncl] at hk hPr
  have hHr := heap_region (a := WP) (n := 24 * ncl s) (by simp only [heapStart] at hlo; omega)
    (by simp only [ncl]; omega) hPa
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8000d180_spec hg.pc (by
    rv_eval [hsp, hg.x25]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hHr (by addr_omega [hPr, hk, hfit]) (by addr_omega [hPr, hk, hfit])
          (by addr_omega [hPa, hPr, hk, hfit]))
  have k₁ := b8000d180_keeps h
  have hm := b8000d180_frame h (by rw [hg.x25]; addr_omega [hPr, hk, hfit])
  rw [hg.x25] at hm
  have inv := Inv.step' hpre hg.inv (DFrame.of_memFrame hm)
    (fun a ha ↦ Or.inr (Or.inr (Or.inr (by addr_omega [ha, hPr, hk, hfit]))))
    (fun a ha ↦ by addr_omega [ha, hPr, hk, hfit, hab, hb])
    ((hm _ (by addr_omega [hPr, hk, hfit])).trans hg.inv.next) (Nat.le_refl _) hfit
    (k₁ .x2 (by decide)) (k₁ .x27 (by decide))
  have hnew : eAt t (WP + BitVec.ofNat 64 (24 * k)) = eAt u (s.getReg .x2 - 168) := by
    have m0 := b8000d180_m_x25_0 h
    have m1 := b8000d180_m_x25_8 h
    have m2 := b8000d180_m_x25_16 h
    rw [hg.x25, hsp] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    unfold eAt
    rv_eval [m0, m1, m2]
  have hws (l : Nat) (hl : l < k + 1) :
      weightOf s l = some (eAt t (WP + BitVec.ofNat 64 (24 * l))) := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · rw [hm.eAt (by addr_omega [hl, hk, hPr, hfit]) (by addr_omega [hl, hk, hPr, hfit])]
      exact hg.ws l hl
    · rw [hnew]; exact hg.w
  have hx21 := hg.x21
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x22, .x24, .x26]) :
      t.getReg r = u.getReg r := k₁ r (Runtime.mem_of_mem hr _)
  by_cases hlast : k + 1 = ncl s
  · refine ⟨t, hr, Or.inr ⟨hlast, {
      inv := inv
      pc := b8000d180_pc_taken h (by rw [hx21]; simp only [ncl] at hlast; addr_omega [hlast, hk])
      x8 := (hreg .x8 (by decide)).trans hg.x8
      x9 := (hreg .x9 (by decide)).trans hg.x9
      x22 := (hreg .x22 (by decide)).trans hg.x22
      x23 := by rw [b8000d180_x23 h, hg.x23, ← hlast]; addr_omega [hk]
      buf := hg.buf
      ws := fun l hl ↦ hws l (by omega) }⟩⟩
  · have hk1 : k + 1 < ncl s := by simp only [ncl] at hlast ⊢; omega
    have hC := Region.bounds (claims_region hpre hk)
    refine ⟨t, hr, Or.inl ⟨hk1, {
      x8 := (hreg .x8 (by decide)).trans hg.x8
      x9 := (hreg .x9 (by decide)).trans hg.x9
      x18 := (hreg .x18 (by decide)).trans hg.x18
      x19 := (hreg .x19 (by decide)).trans hg.x19
      x20 := by
        rw [b8000d180_x20 h, hg.x20]; simp only [claimAddr, ncl] at hC hk1 ⊢; addr_omega [hC, hk1]
      x21 := by rw [b8000d180_x21 h, hx21]; simp only [ncl] at hk1 ⊢; addr_omega [hk1]
      x22 := (hreg .x22 (by decide)).trans hg.x22
      x23 := by rw [b8000d180_x23 h, hg.x23]; simp only [ncl] at hk1; addr_omega [hk1]
      x24 := (hreg .x24 (by decide)).trans hg.x24
      x25 := by rw [b8000d180_x25 h, hg.x25]; addr_omega [hk1, hPr, hfit]
      x26 := (hreg .x26 (by decide)).trans hg.x26
      inv := inv
      pc := b8000d180_pc_not_taken h (by
        rw [hx21]; simp only [ncl] at hk1; addr_omega [hk1, hk])
      lt := hk1
      buf := hg.buf
      ws := hws }⟩⟩

/-! ## The loop -/

def measure (u : MachineState) : Nat := (u.getReg .x21).toNat

theorem loop (hEq : FunSpec Image.code 0x8000da88 Proofs.EqEval.Pre Proofs.EqEval.Post)
    (hR : RingEvalSpec) (hA : EqAboveSpec) (hMul : MulSpec) {s u : MachineState} {nx WP : Word}
    (hpre : BasisPre s) (h0 : Head s u nx WP 0 0x8000d1ac) :
    ∃ v, Reaches Image.code u v ∧ ((∃ nx', End s v nx' WP) ∨ Dead Image.code v) := by
  refine Reaches.loop (fun v ↦ ∃ nx k, Head s v nx WP k 0x8000d1ac) measure
    (fun v ↦ (∃ nx', End s v nx' WP) ∨ Dead Image.code v) ?_ u ⟨nx, 0, h0⟩
  rintro v ⟨nx₁, k, hv⟩
  obtain ⟨w, hvw, hw⟩ := dispatch hpre hv
  obtain ⟨x, hwx, hx⟩ : ∃ x, Reaches Image.code w x ∧ (Dead Image.code x ∨ ∃ nx', Got s x nx' WP k) := by
    rcases hw with ⟨htag, hw⟩ | ⟨htag, hw⟩ | ⟨he, hr, hw⟩
    · obtain ⟨x, hwx, hx⟩ := evalEq hEq hpre hw htag
      rcases hx with hx | hx
      · exact ⟨x, hwx, Or.inl hx⟩
      · exact ⟨x, hwx, Or.inr ⟨_, hx⟩⟩
    · exact evalRing hR hpre hw htag
    · exact evalPlaced hR hA hMul hpre hw he hr
  rcases hx with hx | ⟨nx', hx⟩
  · exact Or.inl ⟨x, hvw.trans hwx, Or.inr hx⟩
  obtain ⟨y, hxy, hy⟩ := push hpre hx
  rcases hy with ⟨hk1, hy⟩ | ⟨-, hy⟩
  · refine Or.inr ⟨y, hvw.trans (hwx.trans hxy), ⟨nx', k + 1, hy⟩, ?_⟩
    simp only [measure]
    rw [hy.x21, hv.x21]
    simp only [ncl] at hk1 ⊢
    addr_omega [hk1]
  · exact Or.inl ⟨y, hvw.trans (hwx.trans hxy), Or.inl ⟨nx', hy⟩⟩

/-! ## `dot`'s tail call -/

theorem mapM_range {α β : Type} (f : α → Option β) (g : ℕ → α) (h : ℕ → β) :
    ∀ n, (∀ i < n, f (g i) = some (h i)) →
      ((List.range n).map g).mapM f = some ((List.range n).map h)
  | 0, _ => rfl
  | n + 1, hf => by
    rw [List.range_succ, List.map_append, List.map_append, List.mapM_append,
      mapM_range f g h n fun i hi ↦ hf i (by omega)]
    simp [hf n (by omega)]

theorem finish (hDot : DotSpec) {s u : MachineState} {nx WP : Word} (hpre : BasisPre s)
    (he : End s u nx WP) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ BasisPost s t) ∨ Dead Image.code t) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := he.inv.sp
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hBr := hpre.self.region.resolve_left (by decide)
  have hBb := Region.bounds hBr
  have sl := he.inv.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at sl
  obtain ⟨s1, s8, s9, s18, s19, s20, s21, s22, s23, s24, s25, s26⟩ := sl
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000d238_spec he.pc (by
    rv_eval [hsp, he.x8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hBr (by addr_omega [hBb]) (by addr_omega [hBb]) (by addr_omega [hBb]))
  have hm := b8000d238_mem_same h
  have k := b8000d238_keeps h
  have x1 := b8000d238_x1 h
  have x2 := b8000d238_x2 h
  have x8 := b8000d238_x8 h
  have x9 := b8000d238_x9 h
  have x18 := b8000d238_x18 h
  have x19 := b8000d238_x19 h
  have x20 := b8000d238_x20 h
  have x21 := b8000d238_x21 h
  have x22 := b8000d238_x22 h
  have x23 := b8000d238_x23 h
  have x24 := b8000d238_x24 h
  have x25 := b8000d238_x25 h
  have x26 := b8000d238_x26 h
  rv_eval [hsp, s1, s8, s9, s18, s19, s20, s21, s22, s23, s24, s25, s26] at x1 x2 x8 x9 x18
  rv_eval [hsp, s19, s20, s21, s22, s23, s24, s25, s26] at x19 x20 x21 x22 x23 x24 x25 x26
  have x27 : v.getReg .x27 = s.getReg .x27 := (k .x27 (by decide)).trans (he.inv.kept _ (by decide))
  have w8 : u.getMem (s.getReg .x11 + 8) = s.getMem (s.getReg .x11 + 8) :=
    Inv.word he.inv hpre.self (by addr_omega [hBb]) (by addr_omega [hBb])
  have w16 : u.getMem (s.getReg .x11 + 16) = s.getMem (s.getReg .x11 + 16) :=
    Inv.word he.inv hpre.self (by addr_omega [hBb]) (by addr_omega [hBb])
  have hx10 : v.getReg .x10 = s.getReg .x10 := by rw [b8000d238_x10 h, he.x9]
  have hx11 : v.getReg .x11 = vecPtr s (s.getReg .x11) := by
    rw [b8000d238_x11 h, he.x8, w8]; rfl
  have hx12 : v.getReg .x12 = vecLen s (s.getReg .x11) := by
    rw [b8000d238_x12 h, he.x8, w16]; rfl
  have hx13 : v.getReg .x13 = WP := by rw [b8000d238_x13 h, he.x22]
  have hx14 : v.getReg .x14 = BitVec.ofNat 64 (ncl s) := by rw [b8000d238_x14 h, he.x23]
  have hO := Region.bounds hpre.out.region
  have hOs := hpre.out.stack
  have hOf := hpre.out.free
  simp only [Outside] at hOf
  have hsS : Apart (vecPtr s (s.getReg .x11)) (24 * (vecLen s (s.getReg .x11)).toNat)
      (stackLo s basisStack) basisStack := by
    rcases hpre.scales with h0 | h0
    · exact Or.inl (by omega)
    · exact h0.stack
  have hsc := hpre.outScales
  have hPa := he.buf.align
  have hfit := he.inv.fits
  have hlo := hpre.heap.lo
  have hncl : ncl s < 2 ^ 32 := by
    have := hpre.claims.region
    simp only [basisClaimsLen, basisClaimsPtr] at this
    rcases this with h0 | h0
    · simp only [ncl]; omega
    · have := Region.bounds h0; simp only [ncl]; omega
  have hW : ncl s = 0 ∨ (heapNext s ≤ WP.toNat ∧ WP.toNat + 24 * ncl s ≤ nx.toNat) := he.buf.range
  have hsl : stackLo v dotStack = s.getReg .x2 - 1120 := by
    simp only [stackLo, x2, dotStack, mulStack, Nat.reduceAdd]; rv_eval []
  have hpreD : DotPre v := {
    ret := by
      rw [hx10]; exact Region.vrange hpre.out.region (Nat.le_refl _) (by omega) hO.2.2
    left := by
      rw [hx11, hx12]
      rcases hpre.scales with h0 | h0
      · intro i hi; omega
      rcases h0.region with h0 | h0
      · intro i hi; omega
      · exact Region.vrange h0 (Nat.le_refl _) (by omega) (Region.bounds h0).2.2
    right := by
      rw [hx13, hx14]
      rcases hW with h0 | h0
      · intro i hi; rw [BitVec.toNat_ofNat] at hi; omega
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact Region.vrange (heap_region (a := WP) (n := 24 * ncl s)
          (by simp only [heapStart] at hlo; omega) (by omega) hPa) (Nat.le_refl _) (by omega) hPa
    stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [x2]; exact hst.aligned⟩
    retLeft := by rw [hx10, hx11, hx12]; exact hsc
    retRight := by
      rw [hx10, hx13, hx14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rcases hW with h0 | h0
      · simp [Apart, h0]
      · rcases hOf.1 with h1 | h1
        · addr_omega [h0, h1, hO]
        · addr_omega [h0, h1, hfit]
    retStack := by rw [hx10, hsl]; addr_omega [hOs, hb]
    leftStack := by rw [hx11, hx12, hsl]; addr_omega [hsS, hb]
    rightStack := by
      rw [hx13, hx14, hsl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rcases hW with h0 | h0
      · simp [Apart, h0]
      · addr_omega [h0, hfit, hab, hb]
    rodata := by
      have := Inv.rodata' hpre he.inv
      intro p hp; rw [hm]; exact this p hp
    retRodata := by rw [hx10]; exact hpre.out.rodata
    stackRodata := by rw [hsl]; addr_omega [hro, hb] }
  obtain ⟨t, hrt, ⟨hpct, hprest, hpost⟩ | hdead⟩ := hDot v (b8000d238_pc h) hpreD
  swap
  · exact ⟨t, hr.trans hrt, Or.inr hdead⟩
  have hfr := hpost.frame
  rw [hx10, hsl] at hfr
  have hnt : t.getMem nextAddr = nx := by
    rw [hfr _ (by addr_omega [hOf.2, hO]) (by addr_omega [hnx8, hb]), hm, he.inv.next]
  have hn : heapNext t = nx.toNat := by simp only [heapNext, hnt]
  have hn' : heapNext u = nx.toNat := by simp only [heapNext, he.inv.next]
  have hlen := hpost.len
  rw [hx12, hx14] at hlen
  have hval := hpost.value
  rw [hx10, hx11, hx12, hx13, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hval
  refine ⟨t, hr.trans hrt, Or.inl ⟨?_, ?_, {
    heap := ⟨by rw [hn]; exact Nat.le_trans hpre.heap.lo he.inv.mono, by rw [hn]; exact he.inv.fits⟩
    mono := by rw [hn]; exact he.inv.mono
    value := ?_
    frame := ?_ }⟩⟩
  · rw [hpct, returnAddress, x1, returnAddress]
  · intro r hr'
    rw [hprest r hr']
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x2
    · exact x8
    · exact x9
    · exact x18
    · exact x19
    · exact x20
    · exact x21
    · exact x22
    · exact x23
    · exact x24
    · exact x25
    · exact x26
    · exact x27
  · simp only [stackBasisEvaluate]
    have hws := mapM_range (fun claim : StackClaimRust ↦ claim.weight.evaluate (eListAt s (s.getReg .x12)
      (s.getReg .x13).toNat)) (fun i ↦ stackClaimAt s (basisClaimsPtr s (s.getReg .x11) +
        BitVec.ofNat 64 (88 * i))) (fun i ↦ eAt u (WP + BitVec.ofNat 64 (24 * i)))
      (ncl s) he.ws
    simp only [claimsAt, basisClaimsLen]
    rw [show (s.getMem (s.getReg .x11 + 32)).toNat = ncl s from rfl, hws]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [hval]
    have eS : eListAt v (vecPtr s (s.getReg .x11)) (ncl s) = vecEs s (s.getReg .x11) := by
      have : (vecLen s (s.getReg .x11)).toNat = ncl s := by rw [hlen, BitVec.toNat_ofNat]; omega
      simp only [Runtime.vecEs, ← this]
      rcases hpre.scales with h0 | h0
      · rw [h0]; rfl
      rw [← Inv.eList he.inv h0]
      simp only [eListAt, eAt, hm]
    have eW : eListAt v WP (ncl s) = (List.range (ncl s)).map fun i ↦
        eAt u (WP + BitVec.ofNat 64 (24 * i)) := by
      simp only [eListAt, eAt, hm]
    rw [eS, eW]
  · refine (he.inv.frame.mono fun a ha ↦ ?_).trans
      ((DFrame.of_same hm _).trans (DFrame.of_two hfr) fun a ha ↦ ha) fun a ha ↦ ?_
    · rcases ha with ha | ha | ha | ha
      · exact ha.elim
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn, hn'] at ha ⊢; exact ha)))
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by simp only [basisStack, ringEvalStack, mulStack, stackLo]; addr_omega [ha, hb]))

/-! ## `StackBasis::evaluate` -/

/-- **`StackBasis::evaluate` meets its contract**, given its callees'. -/
theorem basis_spec (hT : TryAllocZeroedSpec)
    (hEq : FunSpec Image.code 0x8000da88 Proofs.EqEval.Pre Proofs.EqEval.Post)
    (hR : RingEvalSpec) (hA : EqAboveSpec) (hMul : MulSpec) (hDot : DotSpec) : BasisSpec := by
  intro s hpc hpre
  obtain ⟨u, hsu, hu⟩ := setup hT hpc hpre
  rcases hu with hd | ⟨nx, WP, he | hh⟩
  · exact ⟨u, hsu, Or.inr hd⟩
  · obtain ⟨t, hut, ht⟩ := finish hDot hpre he
    exact ⟨t, hsu.trans hut, ht⟩
  · obtain ⟨v, huv, hv⟩ := loop hEq hR hA hMul hpre hh
    rcases hv with ⟨nx', he⟩ | hd
    · obtain ⟨t, hvt, ht⟩ := finish hDot hpre he
      exact ⟨t, hsu.trans (huv.trans hvt), ht⟩
    · exact ⟨v, hsu.trans huv, Or.inr hd⟩

end Rv64Verifier.Proofs.Pcs.Basis

/-- info: 'Rv64Verifier.Proofs.Pcs.Basis.basis_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Basis.basis_spec
