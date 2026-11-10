import Rv64Verifier.Proofs.Walk.R18I
import Rv64Verifier.Proofs.Walk.Limbs

/-!
# `walk` R18, the table claims: no room, `grow_amortized`

`tabGrow`: at `0x80003910` the buffer has no room for table `k`'s values; `grow_amortized` moves
the claims to a new buffer (`P'`, `C'`) with room (`0x8000392c` traps on its error), and
`0x80003930` stores the new pointer at `S - 2472`. The claims read the same from the new buffer
(`claimAt_move`): the old one's bytes were copied.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A claim whose header words and point read the same elsewhere. -/
theorem claimAt_move {u v : MachineState} {x x' : Word}
    (h : ∀ c : Nat, c ≤ 48 → c % 8 = 0 →
      v.getMem (x' + BitVec.ofNat 64 c) = u.getMem (x + BitVec.ofNat 64 c))
    (hp : (vecLen u x).toNat = 0 ∨ ∀ i < (vecLen u x).toNat, ∀ c ≤ 16,
      v.getMem (vecPtr u x + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) =
        u.getMem (vecPtr u x + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c)) :
    claimAt v x' = claimAt u x := by
  have g (c : Nat) (hc : c ≤ 48) (h8 : c % 8 = 0) (y y' : Word) (hy : y = x + BitVec.ofNat 64 c)
      (hy' : y' = x' + BitVec.ofNat 64 c) : v.getMem y' = u.getMem y := by
    subst hy hy'; exact h c hc h8
  have e8 : vecPtr v x' = vecPtr u x := g 8 (by omega) (by omega) _ _ rfl rfl
  have e16 : vecLen v x' = vecLen u x := g 16 (by omega) (by omega) _ _ rfl rfl
  simp only [claimAt, vecEs, e8, e16, g 24 (by omega) (by omega) (x + 24) (x' + 24) rfl rfl]
  congr 1
  · rcases hp with h0 | hp
    · simp [h0, eListAt]
    · refine Bus.eListAt_congr fun i hi ↦ ?_
      have q (c : Nat) (hc : c ≤ 16) (y : Word)
          (hy : y = vecPtr u x + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) :
          v.getMem y = u.getMem y := by subst hy; exact hp i hi c hc
      exact eAt_congr (q 0 (by omega) _ (by rw [add_ofNat_zero])) (q 8 (by omega) _ rfl)
        (q 16 (by omega) _ rfl)
  · exact eAt_congr (g 32 (by omega) (by omega) _ _ rfl rfl)
      (g 40 (by omega) (by omega) _ _ (by bv_omega) (by bv_omega))
      (g 48 (by omega) (by omega) _ _ (by bv_omega) (by bv_omega))

section Grow
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {k : Nat} {P C L : Word}

set_option maxHeartbeats 1600000 in
/-- `grow_amortized`: room for table `k`'s values in a new buffer, or the run dies. -/
theorem tabGrow (hG : GrowSpec) (hpre : WalkPre s)
    (T : TabR18 OI s u₀ w t u layout rows lir bus evs k P C L) (hpc : u.pc = 0x80003910)
    (hc : C.toNat - L.toNat < (evs.getD k ([], [])).2.length) :
    ∃ v, Reaches Image.code u v ∧ ((∃ P' C', TabR18 OI s u₀ w t v layout rows lir bus evs k P' C' L ∧
      v.pc = 0x8000387c ∧ L.toNat + (evs.getD k ([], [])).2.length ≤ C'.toNat) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := T.rest.inv
  have sp := I.sp
  have hLC := T.len
  have hC := T.n_lt
  have hh := I.heap.hi
  have hs0 := hpre.heap.lo
  have htm := T.tmono
  have hwm := T.wmono
  have hum := T.umono
  have hsm := T.smono
  simp only [heapEnd, heapStart] at hh hs0
  obtain ⟨bal, bhi, blo, -⟩ := T.buf
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003910_spec hpc (by rv_eval [])
  have m₁ := b80003910_mem_same h₁
  have k₁ := b80003910_keeps h₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have I₁ : Inv s u₁ := I.same m₁ (k₁ .x2 (by decide))
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1632 := by
    rw [b80003910_x10 h₁, sp]; bv_omega
  have eP : vecPtr u₁ (s.getReg .x2 - 1632) = P := by
    simp only [vecPtr]; rw [show s.getReg .x2 - 1632 + 8 = s.getReg .x2 - 1624 by bv_omega, m₁]
    exact T.ptrSlot
  have eC : vecCap u₁ (s.getReg .x2 - 1632) = C := by
    simp only [vecCap]; rw [m₁]; exact T.capSlot
  have hgs : growStack ≤ 8736 := by decide
  have pre : GrowPre u₁ := {
    heap := I₁.heap
    self := by rw [x10₁]; valid_sub hval [hb1, hb3]
    align := by rw [b80003910_x13 h₁]; decide
    size := by rw [b80003910_x14 h₁]; decide
    raw := by
      rw [x10₁, b80003910_x14 h₁, b80003910_x13 h₁]
      simp only [RawVecOk, Buf]
      rw [eP, eC, show (56 : Word).toNat = 56 from rfl, show (8 : Word).toNat = 8 from rfl]
      refine ⟨bal, ?_⟩
      rcases blo with h0 | h0
      · left; simp [h0]
      · right; rw [hn₁]; exact ⟨by simp only [heapStart]; omega, by omega⟩
    stack := hpre.stack.sub 2656 I₁.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    selfFree := by
      rw [x10₁]
      exact (fr_ok hpre I₁ (c := 1632) (k := 1632) (n := 16) (m := 0) rfl (by omega) (by omega)
        (by omega)).1
    selfStack := by
      rw [x10₁]
      exact (fr_ok hpre I₁ (c := 1632) (k := 1632) (n := 16) rfl (by omega) (by omega) hgs).2.1 }
  obtain ⟨v, hr, ⟨hpcv, hp, post⟩ | hd⟩ := hG.call (Reaches.refl u₁) (b80003910_pc h₁) pre
  swap
  · exact ⟨v, hr₁.trans hr, Or.inr hd⟩
  have pc₂ : v.pc = 0x8000392c := by rw [hpcv, returnAddress, b80003910_x1 h₁]; decide
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000392c_spec pc₂ (by rv_eval [])
  have x9v : v.getReg .x9 = 0xffffffffffffffff := by
    rw [hp .x9 (by decide), k₁ .x9 (by decide), T.x9]
  by_cases hx : v.getReg .x10 = v.getReg .x9
  swap
  · exact ⟨v₂, hr₁.trans (hr.trans hr₂), Or.inr (trapAt (b8000392c_pc_taken h₂ hx))⟩
  rw [x9v] at hx
  have pc₃ := b8000392c_pc_not_taken h₂ (by rw [x9v]; exact hx)
  have m₂ := b8000392c_mem_same h₂
  have k₂ := b8000392c_keeps h₂
  obtain ⟨okL, okR, okB⟩ := post.ok hx
  have fs := post.fresh hx
  rw [x10₁, b80003910_x11 h₁, b80003910_x12 h₁, T.x25, T.x20] at okL
  rw [x10₁, b80003910_x14 h₁, b80003910_x13 h₁, show (56 : Word).toNat = 56 from rfl,
    show (8 : Word).toNat = 8 from rfl] at okR fs
  rw [x10₁, b80003910_x14 h₁, eC, eP, show (56 : Word).toNat = 56 from rfl] at okB
  simp only [NewBuf] at fs
  have hn64 : (evs.getD k ([], [])).2.length < 2 ^ 64 := by
    obtain ⟨-, Vl, -⟩ := newVecE_facts (T.rowsAt.pairs k T.hk.2).2
    have h := (vecLen t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + 24))).isLt
    rw [Vl, ← List.getD_eq_getElem _ ([], []) T.hk.2] at h; exact h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at okL
  -- `0x80003930`: the new pointer at `S - 2472`
  have spv : v.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [hp .x2 (by decide), k₁ .x2 (by decide), sp]
  have sp₂ : v₂.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₂ .x2 (by decide), spv]
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003930_spec pc₃ (by
    rv_eval [sp₂]; and_intros <;> valid_access hval [hb1, hb3])
  have k₃ := b80003930_keeps h₃
  have fr₃ : DFrame v₂ v₃ (Within · (s.getReg .x2 - 2472) 8) := by
    have := DFrame.of_memFrame (b80003930_frame h₃ (by rw [sp₂]; addr_omega [hb1, hb2]))
    rwa [show v₂.getReg .x2 + 184 = s.getReg .x2 - 2472 by rw [sp₂]; bv_omega] at this
  -- the steps
  have W1ok : ∀ a, Within a (s.getReg .x2 - 1632) 16 → InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦
    range_ok hpre T.rest (c := 1632) (k := 1632) (n := 16) rfl (by omega) (by omega) ha
  have W3ok : ∀ a, Within a (s.getReg .x2 - 2472) 8 → InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦
    range_ok hpre T.rest (c := 2472) (k := 2472) (n := 8) rfl (by omega) (by omega) ha
  have fr := post.frame
  rw [x10₁] at fr
  have st₀ : StepW s u u₁ (fun _ ↦ False) False := StepW.same I.heap m₁ (k₁ .x2 (by decide)) _ _
  have st₁ : StepW s u₁ v (Within · (s.getReg .x2 - 1632) 16) False :=
    StepW.ofCall hpre I₁ hgs (DFrame.of_byteFrame fr) post.heap post.mono (hp .x2 (by decide))
  have st₂ : StepW s v v₂ (fun _ ↦ False) False := StepW.same post.heap m₂ (k₂ .x2 (by decide)) _ _
  have st₃ : StepW s v₂ v₃ (Within · (s.getReg .x2 - 2472) 8) False :=
    StepW.ofFrame hpre st₂.heap fr₃ (fun a ha ↦ (W3ok a ha).1) (k₃ .x2 (by decide))
  have st : StepW s u v₃ (fun a ↦ Within a (s.getReg .x2 - 1632) 16 ∨
      Within a (s.getReg .x2 - 2472) 8) False :=
    (((st₀.trans st₁).trans st₂).trans st₃).weaken
      (fun a ha ↦ by
        rcases ha with ((ha | ha) | ha) | ha
        · exact ha.elim
        · exact Or.inl ha
        · exact ha.elim
        · exact Or.inr ha)
      (fun h ↦ by rcases h with ((h | h) | h) | h <;> exact h)
  have st' : StepW s v v₃ (Within · (s.getReg .x2 - 2472) 8) False :=
    (st₂.trans st₃).weaken (fun a ha ↦ by rcases ha with ha | ha; exact ha.elim; exact ha)
      (fun h ↦ by rcases h with h | h <;> exact h)
  have Wok : ∀ a, (Within a (s.getReg .x2 - 1632) 16 ∨ Within a (s.getReg .x2 - 2472) 8) →
      InF s a ∧ ¬ KeepR s u₀ a := fun a ha ↦ ha.elim (W1ok a) (W3ok a)
  have gu : ∀ x : Word, x.toNat + 8 ≤ heapNext u → v₃.getMem x = u.getMem x := fun x hx ↦
    st.getH hpre (fun a ha ↦ (Wok a ha).1) hx
  have gv : ∀ x : Word, x.toNat + 8 ≤ heapNext v → v₃.getMem x = v.getMem x := fun x hx ↦
    st'.getH hpre (fun a ha ↦ (W3ok a ha).1) hx
  have gF (c : Nat) (hc : 112 ≤ c ∧ c ≤ 2648)
      (hw : c ≤ 1616 ∨ (1640 ≤ c ∧ c ≤ 2464) ∨ 2480 ≤ c) :
      v₃.getMem (s.getReg .x2 - BitVec.ofNat 64 c) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 c) :=
    st.getF hpre (by addr_omega [hb1, hc]) (fun i hi hw' ↦ by
      simp only [Within] at hw'
      rcases hw' with hw' | hw' <;> rcases hw with hw | hw | hw <;> addr_omega [hw', hw, hi, hb1, hc])
      (fun hf ↦ hf.elim)
  have gF₃ (c : Nat) (hc : 112 ≤ c ∧ c ≤ 2648) (hw : c ≤ 2464 ∨ 2480 ≤ c) :
      v₃.getMem (s.getReg .x2 - BitVec.ofNat 64 c) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 c) :=
    st'.getF hpre (by addr_omega [hb1, hc]) (fun i hi hw' ↦ by
      simp only [Within] at hw'; rcases hw with hw | hw <;> addr_omega [hw', hw, hi, hb1, hc])
      (fun hf ↦ hf.elim)
  -- the new buffer
  obtain ⟨P', hP'⟩ : ∃ P', vecPtr v (s.getReg .x2 - 1632) = P' := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C', vecCap v (s.getReg .x2 - 1632) = C' := ⟨_, rfl⟩
  rw [hC'] at okL
  rw [hP'] at okB
  rw [hP', hC'] at fs
  rcases fs with ⟨fa, f0 | ⟨f1, f2⟩⟩
  · omega
  rw [hn₁] at f1
  have hm := st.mono
  have hmv := st'.mono
  have hdr (i : Nat) (hi : i < L.toNat) (c : Nat) (hc48 : c ≤ 48) (h8 : c % 8 = 0) :
      v₃.getMem (P' + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c) =
        u.getMem (P + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c) := by
    rw [show P' + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c = P' + BitVec.ofNat 64 (56 * i + c)
        by bv_omega,
      show P + BitVec.ofNat 64 (56 * i) + BitVec.ofNat 64 c = P + BitVec.ofNat 64 (56 * i + c)
        by bv_omega,
      gv _ (by addr_omega [f2, hi, hc48, okL, hh, hmv]),
      getMem_eq_of_bytesAt okB fa bal (by omega) (by omega), m₁]
  have hn0 : 0 < (evs.getD k ([], [])).2.length := by omega
  have R (r : Reg) (h1 : r ∈ calleeSaved)
      (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x18, .x19, .x20, .x21,
        .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h3 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27, .x28, .x29, .x30, .x31] :
        List Reg)) : v₃.getReg r = u.getReg r := by
    rw [k₃ r h3, k₂ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h1 ⊢
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp), hp r h1, k₁ r h2]
  have e1616 : v₂.getMem (s.getReg .x2 - 1616) = L := by
    rw [m₂, show (1616 : Word) = BitVec.ofNat 64 1616 from rfl,
      st₁.getF hpre (by addr_omega [hb1]) (fun i hi hw ↦ by
        simp only [Within] at hw; addr_omega [hw, hi, hb1]) (fun hf ↦ hf.elim), m₁]
    exact T.lenSlot
  have eP'v : v.getMem (s.getReg .x2 - 1624) = P' := by
    rw [← hP']; simp only [vecPtr]; congr 1; bv_omega
  refine ⟨v₃, hr₁.trans (hr.trans (hr₂.trans hr₃)), Or.inl ⟨P', C', {
    rest := T.rest.stepW hpre Wok st
    smono := hsm
    wmono := hwm
    umono := hum
    tmono := by omega
    evKept := fun x h1 h2 ↦ (gu x (by omega)).trans (T.evKept x h1 h2)
    rowsAt := T.rowsAt
    bases := fun i hi ↦ by
      have e : s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * i) =
          s.getReg .x2 - BitVec.ofNat 64 (896 - 8 * i) := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hi]
      rw [e, gF _ (by omega) (by omega), ← e]
      exact T.bases i hi
    capSlot := by
      rw [show (1632 : Word) = BitVec.ofNat 64 1632 from rfl, gF₃ 1632 (by omega) (by omega), ← hC']
      rfl
    ptrSlot := by
      rw [show (1624 : Word) = BitVec.ofNat 64 1624 from rfl, gF₃ 1624 (by omega) (by omega)]
      exact eP'v
    ptr184 := by
      rw [show s.getReg .x2 - 2472 = v₂.getReg .x2 + 184 by rw [sp₂]; bv_omega,
        b80003930_m_x2_184 h₃, sp₂, show s.getReg .x2 - 2656 + 1032 = s.getReg .x2 - 1624 by bv_omega,
        m₂]
      exact eP'v
    proofPtr := by
      have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
      rw [etp, gF 2448 (by omega) (by omega), ← etp]; exact T.proofPtr
    len := by omega
    buf := ⟨fa, by omega, Or.inr (by omega), Or.inr (by omega)⟩
    claims := by
      rw [← T.claims]
      simp only [claimsIn]
      refine List.map_congr_left fun i hi ↦ ?_
      simp only [List.mem_range] at hi
      refine claimAt_move (fun c hc h8 ↦ hdr i hi c hc h8) ?_
      rcases (T.points i hi).1 with h0 | hp'
      · exact Or.inl h0
      · simp only [Old] at hp'
        exact Or.inr fun j hj c hc ↦ gu _ (by addr_omega [hp'.2.1, hj, hc, hh])
    points := fun i hi ↦ by
      have e8 : vecPtr v₃ (P' + BitVec.ofNat 64 (56 * i)) = vecPtr u (P + BitVec.ofNat 64 (56 * i)) :=
        hdr i hi 8 (by omega) (by omega)
      have e16 : vecLen v₃ (P' + BitVec.ofNat 64 (56 * i)) = vecLen u (P + BitVec.ofNat 64 (56 * i)) :=
        hdr i hi 16 (by omega) (by omega)
      rw [e8, e16]
      refine ⟨(T.points i hi).1.imp_right fun h ↦ h.mono (by omega), ?_⟩
      simp only [Apart]
      rcases (T.points i hi).1 with h0 | hp'
      · left; omega
      · simp only [Old] at hp'; right; right; left; omega
    tracks := T.tracks.keep fun T' hT ↦ st.transcript hpre I T.proofPtr (fun a ha ↦ ⟨(Wok a ha).1,
      by rw [tp]; rcases ha with ha | ha <;> simp only [Within] at ha ⊢ <;> addr_omega [ha, hb1]⟩) hT
    hk := T.hk
    x8 := by rw [R .x8 (by decide) (by decide) (by decide), T.x8]
    x9 := by rw [R .x9 (by decide) (by decide) (by decide), T.x9]
    x18 := by rw [R .x18 (by decide) (by decide) (by decide), T.x18]
    x19 := by rw [R .x19 (by decide) (by decide) (by decide), T.x19]
    x21 := by rw [R .x21 (by decide) (by decide) (by decide), T.x21]
    x22 := by rw [R .x22 (by decide) (by decide) (by decide), T.x22]
    x23 := by rw [R .x23 (by decide) (by decide) (by decide), T.x23]
    x20 := by rw [R .x20 (by decide) (by decide) (by decide), T.x20]
    x24 := by rw [R .x24 (by decide) (by decide) (by decide), T.x24]
    x25 := by
      rw [b80003930_x25 h₃, sp₂, show s.getReg .x2 - 2656 + 1040 = s.getReg .x2 - 1616 by bv_omega]
      exact e1616
    x26 := by rw [R .x26 (by decide) (by decide) (by decide), T.x26]
    lenSlot := by
      rw [show (1616 : Word) = BitVec.ofNat 64 1616 from rfl, gF₃ 1616 (by omega) (by omega), ← m₂]
      exact e1616 }, b80003930_pc h₃, okL⟩⟩

end Grow

end Rv64Verifier.Proofs.Walk
