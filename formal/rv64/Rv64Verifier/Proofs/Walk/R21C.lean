import Rv64Verifier.Proofs.Walk.R21B

/-!
# `walk` R21: `vec![ringswitch]`

`r21alloc`: from `RingR21`, `0x8000400c` keeps the target and the weight, `alloc(8, 88)` gives the
`StackClaim`'s buffer (`0x80004140` traps on a null), and `0x80004070` writes the claim there, the
`Vec` (capacity and length one) at `S - 512` and the claims' iterator at `S - 928`, then calls
`extend_desugared` (`ExtR21`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.PcsContracts Rv64Verifier.Pcs Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `extend_desugared`'s entry: the `Vec` at `S - 512` holds the ring claim, the iterator at
`S - 928` runs over the `L` claims at `P`. -/
structure ExtR21 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t e : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (cl : List ColumnClaim) (ks ke : ℕ) (tg : E) (rw : Pcs.RingWeightRust) : Prop
    extends CoreT OI s u₀ w t e layout lir evs P C L.toNat cl
      (afterRing layout rows lir bus cl ks ke (tg, rw)) where
  pc : e.pc = 0x80009b94
  x1 : e.getReg .x1 = 0x80004104
  x10 : e.getReg .x10 = s.getReg .x2 - 512
  x11 : e.getReg .x11 = s.getReg .x2 - 928
  x22 : e.getReg .x22 = lir
  x23 : e.getReg .x23 = s.getReg .x10
  x24 : e.getReg .x24 = s.getReg .x2 - 512
  cap1 : vecCap e (s.getReg .x2 - 512) = 1
  len1 : vecLen e (s.getReg .x2 - 512) = 1
  cbuf : HeapBuf e (vecPtr e (s.getReg .x2 - 512)) 88
  claim : stackClaimAt e (vecPtr e (s.getReg .x2 - 512)) = ⟨.placedRing layout.qkeccak rw, tg⟩
  weight : WeightIn e (vecPtr e (s.getReg .x2 - 512))
  itCur : e.getMem (s.getReg .x2 - 928) = P
  itEnd : e.getMem (s.getReg .x2 - 920) = P + BitVec.ofNat 64 (56 * L.toNat)
  itLay : e.getMem (s.getReg .x2 - 912) = s.getReg .x2 - 2080

section Alloc
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t v : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {cl : List ColumnClaim}
  {ks ke : ℕ}

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- To `extend_desugared`'s entry, or a dead end. -/
theorem r21alloc (hA : AllocSpec) (hpre : WalkPre s) (h : AtR17 OI s u₀ layout rows lir bus)
    (R : RingR21 OI s u₀ w t v layout rows lir bus evs P C L cl ks ke) :
    ∃ e, Reaches Image.code v e ∧
      (ExtR21 OI s u₀ w t e layout rows lir bus evs P C L cl ks ke
        (eAt v (s.getReg .x2 - 928)) (ringWeightAt v (s.getReg .x2 - 904)) ∨
        Dead Image.code e) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have H := R.toCoreT
  have I := H.rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hs0 := hpre.heap.lo
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd, heapStart] at hh hs0 hab
  have ea (c d : Word) (hc : c.toNat + d.toNat = 2656) : v.getReg .x2 + c = s.getReg .x2 - d := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  -- `0x8000400c`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000400c_spec R.pc (by
    rv_eval [sp, R.x24]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | (intro he; have := congrArg BitVec.toNat he; addr_omega [this, hb1]))
  have fr₁ : DFrame v u₁ fun a ↦ Within a (s.getReg .x2 - 1344) 48 ∨
      Within a (s.getReg .x2 - 224) 24 := h₁.dframe (by
    rv_eval [sp, R.x24]
    and_intros <;> simp only [Within] <;> first
      | (left; constructor <;> addr_omega [hb1])
      | (right; constructor <;> addr_omega [hb1]))
  have k₁ := b8000400c_keeps h₁
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide), sp]
  have hW₁ : ∀ a, (Within a (s.getReg .x2 - 1344) 48 ∨ Within a (s.getReg .x2 - 224) 24) →
      InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368 := fun a ha ↦ by
    rcases ha with ha | ha
    · obtain ⟨o1, o2⟩ := range_ok hpre H.rest (c := 1344) (k := 1344) (n := 48) rfl (by omega)
        (by omega) ha
      exact ⟨o1, o2, by rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩
    · obtain ⟨o1, o2⟩ := range_ok hpre H.rest (c := 224) (k := 224) (n := 24) rfl (by omega)
        (by omega) ha
      exact ⟨o1, o2, by rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩
  have st₁ : StepW s v u₁ (fun a ↦ Within a (s.getReg .x2 - 1344) 48 ∨
      Within a (s.getReg .x2 - 224) 24) False :=
    StepW.ofFrame hpre I.heap fr₁ (fun a ha ↦ (hW₁ a ha).1) (k₁ .x2 (by decide))
  have hs₁ : ∀ a, (Within a (s.getReg .x2 - 1344) 48 ∨ Within a (s.getReg .x2 - 224) 24) →
      ¬ Within a (s.getReg .x2 - 1632) 16 ∧ ¬ Within a (s.getReg .x2 - 2616) 16 := fun a ha ↦ by
    rcases ha with ha | ha <;> simp only [Within] at ha ⊢ <;> refine ⟨?_, ?_⟩ <;> addr_omega [ha, hb1]
  have C₁ := H.stepW hpre st₁ hW₁ hs₁
  have hn₁ : heapNext u₁ = heapNext v := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₁ nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1])
  -- `alloc(8, 88)`
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post₂⟩ | hd⟩ := hA.call (Reaches.refl u₁) (b8000400c_pc h₁)
    ⟨C₁.rest.inv.heap, by rw [b8000400c_x10 h₁]; decide⟩
  swap
  · exact ⟨u₂, hr₁.trans hr₂, Or.inr hd⟩
  have al := post₂.aligned
  have ab := post₂.above
  have nx := post₂.next
  rw [b8000400c_x10 h₁] at al
  rw [b8000400c_x11 h₁] at nx
  have hh₂ := post₂.heap.hi
  simp only [heapEnd] at hh₂
  set a0 := u₂.getReg .x10 with ha0
  have fA : DFrame u₁ u₂ (Within · nextAddr 8) := fun a ha ↦ post₂.mem a fun he ↦
    ha 0 (by decide) (by rw [he]; simp only [Within]; addr_omega [])
  have stA : StepW s u₁ u₂ (fun _ ↦ False) False :=
    ⟨fA.mono fun a ha ↦ Or.inr (Or.inr (Or.inl ha)), post₂.heap, by omega,
      hp₂ .x2 (by decide)⟩
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000406c_spec
    (by rw [hpc₂, returnAddress_eq, b8000400c_x1 h₁]; decide) (by rv_eval [])
  by_cases hz : a0 = 0
  · exact ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr (trapAt (b8000406c_pc_taken h₃ hz))⟩
  have pc₃ := b8000406c_pc_not_taken h₃ hz
  have m₃ := b8000406c_mem_same h₃
  have k₃ := b8000406c_keeps h₃
  have hl₁ := C₁.rest.inv.heap.lo
  simp only [heapStart] at hl₁
  have al' : a0.toNat % 8 = 0 := by simpa using al
  have nx' : heapNext u₂ = a0.toNat + 88 := by rw [nx]; rfl
  have aLo : 0x20000000 ≤ a0.toNat := by omega
  have aHi : a0.toNat + 88 ≤ 0x78000000 := by omega
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [k₃ .x2 (by decide), hp₂ .x2 (by decide), sp₁]
  have x24₃ : u₃.getReg .x24 = s.getReg .x2 - 512 := by
    rw [k₃ .x24 (by decide), hp₂ .x24 (by decide), k₁ .x24 (by decide), R.x24]
  have x10₃ : u₃.getReg .x10 = a0 := k₃ .x10 (by decide)
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80004070_spec pc₃ (by
    rv_eval [sp₃, x24₃, x10₃]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [aLo, aHi, al'])
      | (intro he; have := congrArg BitVec.toNat he; addr_omega [this, hb1, aLo, aHi, hab]))
  have fr₄ : DFrame u₃ u₄ fun a ↦ (Within a (s.getReg .x2 - 928) 24 ∨
      Within a (s.getReg .x2 - 512) 24) ∨ Within a a0 88 := h₄.dframe (by
    rv_eval [sp₃, x24₃, x10₃]
    and_intros <;> simp only [Within] <;> first
      | (right; constructor <;> addr_omega [aLo, aHi])
      | (left; left; constructor <;> addr_omega [hb1])
      | (left; right; constructor <;> addr_omega [hb1]))
  have hWF : ∀ a, (Within a (s.getReg .x2 - 928) 24 ∨ Within a (s.getReg .x2 - 512) 24) →
      InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368 := fun a ha ↦ by
    rcases ha with ha | ha
    · obtain ⟨o1, o2⟩ := range_ok hpre C₁.rest (c := 928) (k := 928) (n := 24) rfl (by omega)
        (by omega) ha
      exact ⟨o1, o2, by rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩
    · obtain ⟨o1, o2⟩ := range_ok hpre C₁.rest (c := 512) (k := 512) (n := 24) rfl (by omega)
        (by omega) ha
      exact ⟨o1, o2, by rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1]⟩
  have st₂ : StepW s u₁ u₄ (fun a ↦ False ∨ (Within a (s.getReg .x2 - 928) 24 ∨
      Within a (s.getReg .x2 - 512) 24)) False :=
    StepW.thenE hpre C₁.rest.inv.heap stA (fun a ha ↦ (hWF a ha).1)
      ((DFrame.of_same m₃ _).trans fr₄ fun _ h ↦ h) (by omega) (by omega)
      ((b80004070_keeps h₄ .x2 (by decide)).trans (k₃ .x2 (by decide)))
  have C₂ := C₁.stepW hpre st₂ (fun a ha ↦ ha.elim (fun h ↦ h.elim) (hWF a))
    (fun a ha ↦ by
      rcases ha with h | ha
      · exact h.elim
      rcases ha with ha | ha <;> simp only [Within] at ha ⊢ <;> refine ⟨?_, ?_⟩ <;>
        addr_omega [ha, hb1])
  have hm31 : ∀ a, a ≠ nextAddr → u₃.getMem a = u₁.getMem a := fun a ha ↦ (m₃ a).trans (post₂.mem a ha)
  have nn (k : Word) (hk : k.toNat < 2656) : v.getReg .x2 + k ≠ nextAddr := fun he ↦ by
    have := congrArg BitVec.toNat he; rw [sp] at this; addr_omega [this, hb1, hk]
  have wd (j k k2 : Word) (hj : u₄.getMem (u₃.getReg .x10 + j) = u₃.getMem (u₃.getReg .x2 + k))
      (hk : k.toNat < 2656) (hv : u₁.getMem (v.getReg .x2 + k) = v.getMem (v.getReg .x2 + k2)) :
      u₄.getMem (a0 + j) = v.getMem (v.getReg .x2 + k2) := by
    rw [← x10₃, hj, sp₃, ← sp, hm31 _ (nn k hk), hv]
  have w0 : u₄.getMem a0 = v.getMem (s.getReg .x2 - 904) := by
    rw [← x10₃, b80004070_m_x10_0 h₄, sp₃, ← sp, hm31 _ (nn 1312 (by decide)),
      b8000400c_m_x2_1312 h₁, ea 1752 904 rfl]
  have w8 := wd 8 1320 1760 (b80004070_m_x10_8 h₄) (by decide) (b8000400c_m_x2_1320 h₁)
  have w16 := wd 16 1328 1768 (b80004070_m_x10_16 h₄) (by decide) (b8000400c_m_x2_1328 h₁)
  have w32 := wd 32 1344 1784 (b80004070_m_x10_32 h₄) (by decide) (b8000400c_m_x2_1344 h₁)
  have w40 := wd 40 1352 1792 (b80004070_m_x10_40 h₄) (by decide) (b8000400c_m_x2_1352 h₁)
  rw [ea 1760 896 rfl] at w8
  rw [ea 1768 888 rfl] at w16
  rw [ea 1784 872 rfl] at w32
  rw [ea 1792 864 rfl] at w40
  have x24v : v.getReg .x24 = v.getReg .x2 + 2144 := by rw [R.x24, sp]; bv_omega
  have wt (j k : Word) (k2 : Word) (hj : u₄.getMem (u₃.getReg .x10 + j) = u₃.getMem (u₃.getReg .x24 + k))
      (hk : (2144 + k.toNat) < 2656) (hv : u₁.getMem (v.getReg .x24 + k) = v.getMem (v.getReg .x2 + k2)) :
      u₄.getMem (a0 + j) = v.getMem (v.getReg .x2 + k2) := by
    rw [← x10₃, hj, x24₃, show s.getReg .x2 - 512 = v.getReg .x24 by rw [R.x24],
      hm31 _ (by rw [x24v, BitVec.add_assoc]; exact nn _ (by addr_omega [hk])), hv]
  have w64 := wt 64 288 1728 (b80004070_m_x10_64 h₄) (by decide) (b8000400c_m_x24_288 h₁)
  have w72 := wt 72 296 1736 (b80004070_m_x10_72 h₄) (by decide) (b8000400c_m_x24_296 h₁)
  have w80 := wt 80 304 1744 (b80004070_m_x10_80 h₄) (by decide) (b8000400c_m_x24_304 h₁)
  rw [ea 1728 928 rfl] at w64
  rw [ea 1736 920 rfl] at w72
  rw [ea 1744 912 rfl] at w80
  have w48 : u₄.getMem (a0 + 48) = v.getMem (s.getReg .x2 - 1912) := by
    rw [← x10₃, b80004070_m_x10_48 h₄, k₃ .x19 (by decide), hp₂ .x19 (by decide),
      b8000400c_x19 h₁, ea 744 1912 rfl]
  have w56 : u₄.getMem (a0 + 56) = v.getMem (s.getReg .x2 - 1904) := by
    rw [← x10₃, b80004070_m_x10_56 h₄, k₃ .x20 (by decide), hp₂ .x20 (by decide),
      b8000400c_x20 h₁, ea 752 1904 rfl]
  have k₄ := b80004070_keeps h₄
  have RR (r : Reg) (h4 : r ∈ ([.x2, .x18, .x22, .x23, .x24, .x25] : List Reg)) :
      u₄.getReg r = v.getReg r ∨ r = .x25 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
    rcases h4 with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inr rfl
      | exact Or.inl (by rw [k₄ _ (by decide), k₃ _ (by decide), hp₂ _ (by decide), k₁ _ (by decide)])
  have reg (r : Reg) (h4 : r ∈ ([.x2, .x18, .x22, .x23, .x24] : List Reg)) :
      u₄.getReg r = v.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
    rcases h4 with rfl | rfl | rfl | rfl | rfl <;>
      exact (RR _ (by simp)).resolve_right (by decide)
  have x18₃ : u₃.getReg .x18 = P := by
    rw [k₃ .x18 (by decide), hp₂ .x18 (by decide), k₁ .x18 (by decide), R.x18]
  have x25₃ : u₃.getReg .x25 = L := by
    rw [k₃ .x25 (by decide), hp₂ .x25 (by decide), k₁ .x25 (by decide), R.x25]
  have stT := st₁.trans st₂
  have hWT : ∀ a, ((Within a (s.getReg .x2 - 1344) 48 ∨ Within a (s.getReg .x2 - 224) 24) ∨
      False ∨ (Within a (s.getReg .x2 - 928) 24 ∨ Within a (s.getReg .x2 - 512) 24)) → InF s a :=
    fun a ha ↦ by
      rcases ha with ha | h | ha
      · exact (hW₁ a ha).1
      · exact h.elim
      · exact (hWF a ha).1
  have hnv := stT.mono
  have hn4 : heapNext u₄ = heapNext u₂ := by
    simp only [heapNext]
    rw [fr₄ nextAddr (fun i hi hw ↦ by rcases hw with (hw | hw) | hw <;> addr_omega [hw, hi, hb1, aHi]),
      m₃]
  have po := R.pointOld
  have co := R.coeffsOld
  have hp0 : vecPtr u₄ a0 = vecPtr v (s.getReg .x2 - 904) := by
    simp only [vecPtr]; rw [w8, show s.getReg .x2 - 904 + 8 = s.getReg .x2 - 896 by bv_omega]
  have hl0 : vecLen u₄ a0 = vecLen v (s.getReg .x2 - 904) := by
    simp only [vecLen]; rw [w16, show s.getReg .x2 - 904 + 16 = s.getReg .x2 - 888 by bv_omega]
  have hp24 : vecPtr u₄ (a0 + 24) = vecPtr v (s.getReg .x2 - 880) := by
    simp only [vecPtr]
    rw [show a0 + 24 + 8 = a0 + 32 by bv_omega, w32,
      show s.getReg .x2 - 880 + 8 = s.getReg .x2 - 872 by bv_omega]
  have hl24 : vecLen u₄ (a0 + 24) = vecLen v (s.getReg .x2 - 880) := by
    simp only [vecLen]
    rw [show a0 + 24 + 16 = a0 + 40 by bv_omega, w40,
      show s.getReg .x2 - 880 + 16 = s.getReg .x2 - 864 by bv_omega]
  have hcap : (u₄.getMem a0).toNat < 2 ^ 62 := by rw [w0]; exact R.cap
  have hne1 : u₄.getMem a0 ≠ eqTag := fun he ↦ by rw [he] at hcap; exact absurd hcap (by decide)
  have hne2 : u₄.getMem a0 ≠ ringTag := fun he ↦ by rw [he] at hcap; exact absurd hcap (by decide)
  have hrw : ringWeightAt u₄ a0 = ringWeightAt v (s.getReg .x2 - 904) := by
    simp only [ringWeightAt, vecEs]
    rw [hp0, hl0, hp24, hl24, show s.getReg .x2 - 904 + 24 = s.getReg .x2 - 880 by bv_omega]
    simp only [Old] at po co
    congr 1
    · exact stT.eListH hpre hWT (by omega)
    · exact stT.eListH hpre hWT (by omega)
  have he64 : eAt u₄ (a0 + 64) = eAt v (s.getReg .x2 - 928) := by
    simp only [eAt]
    rw [show a0 + 64 + 8 = a0 + 72 by bv_omega, show a0 + 64 + 16 = a0 + 80 by bv_omega, w64, w72,
      w80, show s.getReg .x2 - 928 + 8 = s.getReg .x2 - 920 by bv_omega,
      show s.getReg .x2 - 928 + 16 = s.getReg .x2 - 912 by bv_omega]
  have q1 : (v.getMem (s.getReg .x2 - 1912)).toNat = layout.qkeccak.variableCount := by
    rw [show (1912 : Word) = BitVec.ofNat 64 1912 from rfl,
      H.rest.get (keep_slot hpre (by omega))]
    exact h.layoutIn.qkeccakVars
  have q2 : v.getMem (s.getReg .x2 - 1904) = layout.qkeccak.index := by
    rw [show (1904 : Word) = BitVec.ofNat 64 1904 from rfl,
      H.rest.get (keep_slot hpre (by omega))]
    exact h.layoutIn.qkeccakIndex
  have e512 : vecPtr u₄ (s.getReg .x2 - 512) = a0 := by
    simp only [vecPtr]; rw [← x24₃, b80004070_m_x24_8 h₄, x10₃]
  have hL := H.len
  have hC := H.n_lt
  refine ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl {
    toCoreT := C₂
    pc := b80004070_pc h₄
    x1 := b80004070_x1 h₄
    x10 := by rw [b80004070_x10 h₄, sp₃]; bv_omega
    x11 := by rw [b80004070_x11 h₄, sp₃]; bv_omega
    x22 := by rw [reg .x22 (by simp), R.x22]
    x23 := by rw [reg .x23 (by simp), R.x23]
    x24 := by rw [reg .x24 (by simp), R.x24]
    cap1 := by simp only [vecCap]; rw [← x24₃, b80004070_m_x24_0 h₄]
    len1 := by simp only [vecLen]; rw [← x24₃, b80004070_m_x24_16 h₄]
    cbuf := by
      rw [e512]; simp only [HeapBuf, heapStart]; rw [hn4, nx']; omega
    claim := by
      rw [e512]
      simp only [stackClaimAt, stackWeightAt]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne1), ite_eq_right_of_eq_false _ _ (eq_false hne2), w48, w56, hrw, he64, q1, q2]
    weight := by
      rw [e512]
      simp only [WeightIn, RingIn]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne1), ite_eq_right_of_eq_false _ _ (eq_false hne2), hp0, hl0, hp24, hl24]
      exact ⟨(po.heapBuf hpre.heap).mono hnv, (co.heapBuf hpre.heap).mono hnv⟩
    itCur := by
      rw [show s.getReg .x2 - 928 = u₃.getReg .x2 + 1728 by rw [sp₃]; bv_omega,
        b80004070_m_x2_1728 h₄, x18₃]
    itEnd := by
      rw [show s.getReg .x2 - 920 = u₃.getReg .x2 + 1736 by rw [sp₃]; bv_omega,
        b80004070_m_x2_1736 h₄, x18₃, x25₃]
      congr 1
      have : L.toNat < 2 ^ 32 := by omega
      bv_omega
    itLay := by
      rw [show s.getReg .x2 - 912 = u₃.getReg .x2 + 1744 by rw [sp₃]; bv_omega,
        b80004070_m_x2_1744 h₄, sp₃]; bv_omega }⟩

end Alloc

end Rv64Verifier.Proofs.Walk
