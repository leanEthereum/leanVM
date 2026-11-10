import Rv64Verifier.Proofs.Walk.At14
import Rv64Verifier.Proofs.Walk.AtR17
import Rv64Verifier.Proofs.Walk.Err14

/-!
# `walk`: the `Layout` (R14)

`layoutOf A k` is what `build_layout` returns (`buildLayout_eq`, from `HeadOk`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The layout `build_layout` returns. -/
def layoutOf (A : List E) (k : Nat) : LayoutRust :=
  ⟨(lmOf A).toNat, k - 4, tablesRust, (busBlocksRust tablesRust (hts A) (rowsOf A)).1,
    (busBlocksRust tablesRust (hts A) (rowsOf A)).2.1,
    (busBlocksRust tablesRust (hts A) (rowsOf A)).2.2, (plc A k).1, (plc A k).2.1, (plc A k).2.2,
    hts A, (hts A).getD 5 0⟩

theorem buildLayout_eq {s : MachineState} {A : List E} {k : Nat} (h : HeadOk s A k) :
    buildLayoutRust (BitVec.ofNat 64 (Proofs.Bytecode.readBytecode s (s.getReg .x11)).len)
      (lmOf A) (rowsOf A) = some (layoutOf A k) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [buildLayoutRust, h1, h2, h3, h4, and_self, ↓reduceIte]
  simp only [layoutOf, plc, kapPre_six, slotBits_eq]
  rfl

/-- `walk` once the layout is built and `stack_log` checked. -/
theorem tracks14 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} (h : Tracks OI s u (afterRate s A)) (hb : HeadOk s A k)
    (hs : Pcs.minStackedLog ≤ (layoutOf A k).stackLog ∧ (layoutOf A k).stackLog ≤ Pcs.maxStackedLog) :
    Tracks OI s u (bodyRest (Proofs.Bytecode.readBytecode s (s.getReg .x11)) (bytesAt s (s.getReg .x12) 32)
      (layoutOf A k, rowsOf A, rateOf A) >>= finishRust) := by
  unfold afterRate at h
  rw [buildLayout_eq hb] at h
  simp only [TM.ofOption, bind_assoc, pure_bind] at h
  exact Tracks.require h hs

theorem Keep11.mono {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo2' : Nat} (h : Keep11 OI s u A k R Q B lo lo2)
    (h1 : lo2 ≤ lo2') (h2 : lo2' ≤ heapNext u) : Keep11 OI s u A k R Q B lo lo2' :=
  ⟨h.at11, h2, le_trans h.lole h1, fun x hx ↦ lt_of_lt_of_le (h.below x hx) h1⟩

/-- At `0x800034c0`: the `Layout` at `sp + 576`, `stack_log` checked; `walk` runs `bodyRest`. -/
structure AtR15 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 : Nat) : Prop where
  keep : Keep11 OI s u A k R Q B lo lo2
  /-- The placements' buffer, below `lo2`. -/
  plBelow : (vecPtr u (s.getReg .x2 - 1984)).toNat + 24 * 165 ≤ lo2
  layoutIn : LayoutIn s u (layoutOf A k)
  /-- The `Layout`'s `push`, `pull` and `count` headers are `walk`'s. -/
  push : ∀ j < 3, u.getMem (s.getReg .x2 - 2056 + BitVec.ofNat 64 (8 * j)) =
    u.getMem (s.getReg .x2 - 416 + BitVec.ofNat 64 (8 * j))
  pull : ∀ j < 3, u.getMem (s.getReg .x2 - 2032 + BitVec.ofNat 64 (8 * j)) =
    u.getMem (s.getReg .x2 - 224 + BitVec.ofNat 64 (8 * j))
  count : ∀ j < 3, u.getMem (s.getReg .x2 - 2008 + BitVec.ofNat 64 (8 * j)) =
    u.getMem (s.getReg .x2 - 512 + BitVec.ofNat 64 (8 * j))
  /-- `&Bytecode` at `+144`, `log_bytecode` at `+160`. -/
  bc : u.getMem (s.getReg .x2 - 1936) = s.getReg .x11
  lb : u.getMem (s.getReg .x2 - 1920) = BitVec.ofNat 64 (k - 4)
  stack : Pcs.minStackedLog ≤ (layoutOf A k).stackLog ∧ (layoutOf A k).stackLog ≤ Pcs.maxStackedLog
  tracks : Tracks OI s u (bodyRest (Proofs.Bytecode.readBytecode s (s.getReg .x11))
    (bytesAt s (s.getReg .x12) 32) (layoutOf A k, rowsOf A, rateOf A) >>= finishRust)
  x27 : u.getReg .x27 = 6

set_option maxRecDepth 8192 in
/-- The staging copies and `memcpy` into the `Layout` (`0x800033f0`), to `0x80003454`. -/
theorem lay14a (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} {PL : Word} (hpre : WalkPre s)
    (hpc : u.pc = 0x800033f0) (h : AtR14 OI s u A k R Q B lo lo2 lo3 PL) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ (t.pc = 0x80003454 ∧
      Keep11 OI s t A k R Q B lo lo2 ∧ heapNext t = heapNext u ∧
      (∀ a, a.toNat < 0x78000000 → t.getMem a = u.getMem a) ∧
      (∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x21, .x22, .x23, .x24, .x26] : List Reg),
        t.getReg r = u.getReg r) ∧
      (∀ a, (s.getReg .x2 - 2656).toNat ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2 - 2056).toNat →
        t.getMem a = u.getMem a) ∧
      (∀ a, (s.getReg .x2 - 1984).toNat ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2 - 1872).toNat →
        t.getMem a = u.getMem a) ∧
      (∀ a, (s.getReg .x2 - 1800).toNat ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2).toNat →
        t.getMem a = u.getMem a) ∧
      (∀ j < 3, t.getMem (s.getReg .x2 - 2056 + BitVec.ofNat 64 (8 * j)) =
        u.getMem (s.getReg .x2 - 416 + BitVec.ofNat 64 (8 * j))) ∧
      (∀ j < 3, t.getMem (s.getReg .x2 - 2032 + BitVec.ofNat 64 (8 * j)) =
        u.getMem (s.getReg .x2 - 224 + BitVec.ofNat 64 (8 * j))) ∧
      (∀ j < 3, t.getMem (s.getReg .x2 - 2008 + BitVec.ofNat 64 (8 * j)) =
        u.getMem (s.getReg .x2 - 512 + BitVec.ofNat 64 (8 * j))))) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have K := h.base.k11
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := K.at11.base.inv.sp
  obtain ⟨c₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800033f0_spec hpc (by
    rv_eval [sp]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have fr₁ := (b800033f0_frame h₁ (by rw [sp]; addr_omega [hb1])).dframe
  have e784 : u.getReg .x2 + 784 = s.getReg .x2 - 1872 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e784] at fr₁
  have k₁ := b800033f0_keeps h₁
  have hn₁ : heapNext c₁ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₁.getMem_of (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw; addr_omega [hy, hw, hb1]) (by decide))
  have hv₁ : HeapOk c₁ := ⟨hn₁ ▸ K.at11.base.inv.heap.lo, hn₁ ▸ K.at11.base.inv.heap.hi⟩
  have K₁ := K.keep hpre fr₁ (fun a ha ↦ by
      simp only [Within] at ha
      refine Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1], ?_⟩
      simp only [hdrs, Within]; addr_omega [ha, hb1]) hv₁ hn₁.ge (k₁ .x2 (by decide))
  have I₁ := K₁.at11.base.inv
  have x10₁ : c₁.getReg .x10 = s.getReg .x2 - 2056 := by
    rw [b800033f0_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₁ : c₁.getReg .x11 = s.getReg .x2 - 1872 := by rw [b800033f0_x11 h₁, e784]
  have x12₁ : (c₁.getReg .x12).toNat = 72 := by rw [b800033f0_x12 h₁]; rfl
  have hmc : MemcpyPre c₁ := {
    dst := by rw [x10₁, x12₁]; addr_omega [hb1, hb2]
    src := by rw [x11₁, x12₁]; addr_omega [hb1, hb2]
    apart := by rw [x10₁, x11₁, x12₁]; addr_omega [hb1]
    stack := calleeStack hpre I₁ (by decide) (by decide)
    dstStack := by rw [x10₁, x12₁, stackLo_callee I₁]; addr_omega [hb1]
    srcStack := by rw [x11₁, x12₁, stackLo_callee I₁]; addr_omega [hb1] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hMC.call (Reaches.refl c₁) (b800033f0_pc h₁) hmc
  swap
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have by₂ := post.bytes
  have fr₂ := post.frame.dframe
  rw [x10₁, x11₁, x12₁] at by₂
  rw [x10₁, x12₁, stackLo_callee I₁] at fr₂
  have hn₂ : heapNext t₂ = heapNext c₁ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₂.getMem_of (fun y hy hw ↦ by
      simp only [Within, nextAddr, memcpyStack] at hy hw
      rcases hw with hw | hw <;> addr_omega [hy, hw, hb1]) (by decide))
  have hv₂ : HeapOk t₂ := ⟨hn₂ ▸ hv₁.lo, hn₂ ▸ hv₁.hi⟩
  have K₂ := K₁.keep hpre fr₂ (fun a ha ↦ by
      rcases ha with ha | ha
      · simp only [Within] at ha
        refine Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1], ?_⟩
        simp only [hdrs, Within]; addr_omega [ha, hb1]
      · simp only [Within, memcpyStack] at ha
        exact Or.inr (Or.inl (by simp only [Within]; addr_omega [ha, hb1]))) hv₂ hn₂.ge
    (hp₂ .x2 (by decide))
  have pc₂ : t₂.pc = 0x80003454 := by rw [hpc₂, returnAddress_eq, b800033f0_x1 h₁]; decide
  have m₁₂ (a : Word) (ha1 : ∀ x, Within x a 8 → ¬ (Within x (s.getReg .x2 - 2672) 16 ∨
      Within x (s.getReg .x2 - 2056) 72 ∨ Within x (s.getReg .x2 - 1872) 72))
      (ha2 : a.toNat + 8 ≤ 2 ^ 64) : t₂.getMem a = u.getMem a := by
    rw [fr₂.getMem_of (fun x hx hw ↦ ha1 x hx (by
        simp only [Within, memcpyStack] at hw ⊢
        rcases hw with hw | hw
        · exact Or.inr (Or.inl hw)
        · exact Or.inl (by addr_omega [hw, hb1]))) ha2,
      fr₁.getMem_of (fun x hx hw ↦ ha1 x hx (Or.inr (Or.inr hw))) ha2]
  have stg (j : Nat) (hj : j < 9) : t₂.getMem (s.getReg .x2 - 2056 + BitVec.ofNat 64 (8 * j)) =
      c₁.getMem (s.getReg .x2 - 1872 + BitVec.ofNat 64 (8 * j)) :=
    getMem_eq_of_bytesAt by₂ (by addr_omega [hb1, hb3]) (by addr_omega [hb1, hb3]) (by omega) (by omega)
  have mm (a : Word) (h1 : a.toNat + 8 ≤ (s.getReg .x2 - 2672).toNat ∨
      ((s.getReg .x2 - 2656).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2 - 2056).toNat) ∨
      ((s.getReg .x2 - 1984).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2 - 1872).toNat) ∨
      ((s.getReg .x2 - 1800).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat)) :
      t₂.getMem a = u.getMem a :=
    m₁₂ a (fun x hx hw ↦ by
      simp only [Within] at hx hw
      rcases hw with hw | hw | hw <;> rcases h1 with h1 | h1 | h1 | h1 <;> addr_omega [hx, hw, h1, hb1])
      (by rcases h1 with h1 | h1 | h1 | h1 <;> addr_omega [h1, hb1, hb2])
  refine ⟨t₂, hr₁.trans hr₂, Or.inr ⟨pc₂, K₂, hn₂.trans hn₁, fun a ha ↦ mm a (Or.inl (by addr_omega [ha, hb1])),
    fun r hr ↦ ?_, fun a h1 h2 ↦ mm a (Or.inr (Or.inl ⟨h1, h2⟩)),
    fun a h1 h2 ↦ mm a (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))),
    fun a h1 h2 ↦ mm a (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))),
    fun j hj ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩⟩
  · rw [hp₂ r (mem_of_mem hr _), k₁ r (by revert r hr; decide)]
  · rw [stg j (by omega)]
    interval_cases j
    · have := b800033f0_m_x2_784 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · have := b800033f0_m_x2_792 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · have := b800033f0_m_x2_800 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  · have e := stg (j + 3) (by omega)
    rw [show s.getReg .x2 - 2056 + BitVec.ofNat 64 (8 * (j + 3)) =
      s.getReg .x2 - 2032 + BitVec.ofNat 64 (8 * j) by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]] at e
    rw [e]
    interval_cases j
    · have := b800033f0_m_x2_808 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · have := b800033f0_m_x2_816 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · have := b800033f0_m_x2_824 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  · have e := stg (j + 6) (by omega)
    rw [show s.getReg .x2 - 2056 + BitVec.ofNat 64 (8 * (j + 6)) =
      s.getReg .x2 - 2008 + BitVec.ofNat 64 (8 * j) by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]] at e
    rw [e]
    interval_cases j
    · have := b800033f0_m_x2_832 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · have := b800033f0_m_x2_840 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · have := b800033f0_m_x2_848 h₁; rw [sp] at this
      convert this using 2 <;> (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])

theorem hts_length (A : List E) (h : (rowsOf A).length = 6) : (hts A).length = 6 := by
  simp only [hts, tableLogHeightsRust, List.length_map, List.length_zip, h]; rfl

theorem natsAt_hts {s t : MachineState} {A : List E} {k : Nat} {Q : Word} (hb : HeadOk s A k)
    (hl : (rowsOf A).length = 6)
    (hv : ∀ i < 6, t.getMem (Q + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 ((hts A).getD i 0)) :
    Bus.natsAt t Q 6 = hts A := by
  have hL := hts_length A hl
  simp only [Bus.natsAt, readWords_eq_map, List.map_map]
  apply List.ext_getElem (by simp [hL])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Function.comp, hv i h1, BitVec.toNat_ofNat]
  have : (hts A).getD i 0 ≤ 32 := heightsLe hb i
  rw [Nat.mod_eq_of_lt (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem placementsAt_congr {t u : MachineState} {P : Word} {n : Nat}
    (h : ∀ i < n, ∀ o < 3, t.getMem (P + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 (8 * o)) =
      u.getMem (P + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 (8 * o))) :
    PcsContracts.placementsAt t P n = PcsContracts.placementsAt u P n := by
  unfold PcsContracts.placementsAt PcsContracts.placementAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have h0 := h i hi 0 (by decide)
  have h8 := h i hi 1 (by decide)
  have h16 := h i hi 2 (by decide)
  simp only [show 8 * 0 = 0 from rfl, BitVec.add_zero] at h0
  rw [h0, show (8 : Word) = BitVec.ofNat 64 (8 * 1) from rfl, h8,
    show (16 : Word) = BitVec.ofNat 64 (8 * 2) from rfl, h16]

set_option maxRecDepth 8192 in
/-- The `Layout`'s other fields (`0x80003454`) and `stack_log`'s check. -/
theorem lay14b (hDL : DropLayoutSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u c : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} {PL : Word}
    (hpre : WalkPre s) (h : AtR14 OI s u A k R Q B lo lo2 lo3 PL) (hpc : c.pc = 0x80003454)
    (Kc : Keep11 OI s c A k R Q B lo lo2) (hnc : heapNext c = heapNext u) (mh : ∀ a, a.toNat < 0x78000000 → c.getMem a = u.getMem a)
    (rg : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x21, .x22, .x23, .x24, .x26] : List Reg),
      c.getReg r = u.getReg r)
    (hi : ∀ a, (s.getReg .x2 - 1800).toNat ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2).toNat →
      c.getMem a = u.getMem a)
    (hP : ∀ j < 3, c.getMem (s.getReg .x2 - 2056 + BitVec.ofNat 64 (8 * j)) =
      u.getMem (s.getReg .x2 - 416 + BitVec.ofNat 64 (8 * j)))
    (hL : ∀ j < 3, c.getMem (s.getReg .x2 - 2032 + BitVec.ofNat 64 (8 * j)) =
      u.getMem (s.getReg .x2 - 224 + BitVec.ofNat 64 (8 * j)))
    (hC : ∀ j < 3, c.getMem (s.getReg .x2 - 2008 + BitVec.ofNat 64 (8 * j)) =
      u.getMem (s.getReg .x2 - 512 + BitVec.ofNat 64 (8 * j))) :
    ∃ t, Reaches Image.code c t ∧ (Done OI s t ∨ Dead Image.code t ∨
      (t.pc = 0x800034c0 ∧ AtR15 OI s t A k R Q B lo (heapNext u))) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := Kc.at11.base
  have sp : c.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  obtain ⟨-, -, -, -, -, s2528, s2512, -, -⟩ := H.spills
  obtain ⟨-, s2520, -, -, s2464, s2456⟩ := H.slots
  obtain ⟨c₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003454_spec hpc (by
    rv_eval [sp]; simp only [Sym.validAccess_eight]; and_intros <;> addr_omega [hb1, hb2, hb3])
  have fr₁ : Layout.DFrame c c₁ fun a ↦ Within a (s.getReg .x2 - 2080) 24 ∨
      Within a (s.getReg .x2 - 1984) 112 :=
    exL h₁ (by rv_eval [sp]; simp only [Within]; and_intros <;> addr_omega [hb1])
  have k₁ := b80003454_keeps h₁
  have hn₁ : heapNext c₁ = heapNext c := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₁.getMem_of (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw; rcases hw with hw | hw <;> addr_omega [hy, hw, hb1])
      (by decide))
  have hv₁ : HeapOk c₁ := ⟨hn₁ ▸ H.inv.heap.lo, hn₁ ▸ H.inv.heap.hi⟩
  have K₁ := Kc.keep hpre fr₁ (fun a ha ↦ by
      rcases ha with ha | ha <;> simp only [Within] at ha <;>
        refine Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1], ?_⟩ <;>
        simp only [hdrs, Within] <;> addr_omega [ha, hb1]) hv₁ hn₁.ge (k₁ .x2 (by decide))
  have H₁ := K₁.at11.base
  have mid (a : Word) (h1 : (s.getReg .x2 - 2056).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2 - 1984).toNat) : c₁.getMem a = c.getMem a :=
    fr₁.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, h1, h2])
      (by addr_omega [h2, hb1])
  have hiS (a : Word) (h1 : (s.getReg .x2 - 1800).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat) : c₁.getMem a = u.getMem a := by
    rw [fr₁.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, h1, h2])
      (by addr_omega [h2, hb1]), hi a h1 h2]
  have hh (a : Word) (h1 : a.toNat < 0x78000000) : c₁.getMem a = u.getMem a := by
    rw [fr₁.getMem_of (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, h1])
      (by omega), mh a h1]
  have l576 := b80003454_m_x2_576 h₁
  have l584 := b80003454_m_x2_584 h₁
  have l592 := b80003454_m_x2_592 h₁
  have l672 := b80003454_m_x2_672 h₁
  have l680 := b80003454_m_x2_680 h₁
  have l688 := b80003454_m_x2_688 h₁
  have l720 := b80003454_m_x2_720 h₁
  have l728 := b80003454_m_x2_728 h₁
  have l736 := b80003454_m_x2_736 h₁
  have l744 := b80003454_m_x2_744 h₁
  have l752 := b80003454_m_x2_752 h₁
  have l760 := b80003454_m_x2_760 h₁
  have l768 := b80003454_m_x2_768 h₁
  have l776 := b80003454_m_x2_776 h₁
  rw [sp] at l576 l584 l592 l672 l680 l688 l720 l728 l736 l744 l752 l760 l768 l776
  rv_eval [] at l576 l584 l592 l672 l680 l688 l720 l728 l736 l744 l752 l760 l768 l776
  rw [s2456] at l584
  rw [s2528] at l720
  rw [s2512] at l728
  rw [rg .x22 (by decide), h.x22] at l672
  rw [rg .x21 (by decide), h.x21] at l680
  rw [rg .x24 (by decide), h.x24] at l688
  rw [rg .x23 (by decide), h.x23] at l736
  rw [rg .x26 (by decide), h.x26] at l744
  rw [rg .x19 (by decide), h.x19] at l752
  rw [rg .x9 (by decide)] at l760
  rw [rg .x18 (by decide), h.x18] at l768
  have hbB := H₁.bufB
  have hlo := hpre.heap.lo
  have hhi := H₁.inv.heap.hi
  have hl := H₁.loLe
  simp only [heapStart, heapEnd] at hlo hhi
  have e1 : s.getReg .x2 - 2080 + 8 = s.getReg .x2 - 2072 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e2 : s.getReg .x2 - 2080 + 16 = s.getReg .x2 - 2064 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e3 : s.getReg .x2 - 1984 + 8 = s.getReg .x2 - 1976 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e4 : s.getReg .x2 - 1984 + 16 = s.getReg .x2 - 1968 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have eP : vecPtr c₁ (s.getReg .x2 - 2080) = B := by
    simp only [vecPtr]; rw [e1]; exact l584
  have eL : vecLen c₁ (s.getReg .x2 - 2080) = 6 := by
    simp only [vecLen]; rw [e2]; exact l592
  have x8 := rg .x8 (by decide)
  by_cases h29 : 29 ≤ (u.getReg .x8).toNat
  · have pc₁ := b80003454_pc_taken h₁ (by rw [x8]; exact h29)
    obtain ⟨t, hr, ht⟩ := err14 (OI := OI) hDL hpre H₁.inv pc₁ H₁.spills.2.2.2.2.2.2.2.2
      hbB.2.1 (by omega) (by omega) eP eL
    exact ⟨t, hr₁.trans hr, ht.elim Or.inl (fun hd ↦ Or.inr (Or.inl hd))⟩
  have pc₁ := b80003454_pc_not_taken h₁ (by rw [x8]; show _ < 29; omega)
  have hst : Pcs.minStackedLog ≤ (layoutOf A k).stackLog ∧
      (layoutOf A k).stackLog ≤ Pcs.maxStackedLog := by
    have e := h.x8
    show 15 ≤ (plc A k).2.2 ∧ (plc A k).2.2 ≤ 28
    omega
  have ePL : vecPtr c₁ (s.getReg .x2 - 1984) = PL := by
    simp only [vecPtr]; rw [e3]; exact l680
  have eLL : vecLen c₁ (s.getReg .x2 - 1984) = 165 := by
    simp only [vecLen]; rw [e4]; exact l688
  obtain ⟨-, -, -, -, t2464, t2456⟩ := H₁.slots
  have hbQ := H₁.bufQ
  have hpl := h.plhi
  have hpl0 := h.pllo
  have h23 := h.base.le23
  have hle := Kc.lole
  have hn₁u : heapNext c₁ = heapNext u := hn₁.trans hnc
  have h5 : (hts A).getD 5 0 ≤ 32 := heightsLe H₁.ok 5
  refine ⟨c₁, hr₁, Or.inr (Or.inr ⟨pc₁, {
    keep := K₁.mono h.base.k11.lo2le hn₁u.ge
    plBelow := by rw [ePL]; exact hpl
    layoutIn := {
      tables := by rw [t2456]; exact ⟨hbB.2.1, by omega, Or.inr hbB.1⟩
      tablesVec := ⟨by rw [eP, t2456], eL⟩
      opcodes := fun i hi ↦ by
        rw [t2456]
        by_cases h5' : i < 5
        · exact H₁.opcodes i h5'
        · have : i = 5 := by omega
          subst this; exact K₁.at11.op5
      heights := by rw [t2464]; exact ⟨hbQ.2.1, by omega, Or.inr hbQ.1⟩
      heightsVal := by rw [t2464]; exact natsAt_hts H₁.ok H₁.rowsLen H₁.heights
      placements := by
        rw [ePL, eLL]; exact ⟨h.plal, by rw [hn₁u]; exact hpl, Or.inr (by omega)⟩
      placementsVal := by
        rw [ePL, eLL, placementsAt_congr (fun i hi o ho ↦ hh _ (by addr_omega [hpl, hhi, hn₁u, hi, ho]))]
        exact h.plvals
      logMemory := by rw [l728]; rfl
      qkeccakVars := by
        rw [l744, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
      qkeccakIndex := l752
      stackLog := by rw [l760]; exact h.x9
      keccakLogSteps := by rw [l768, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl
      keccakDepth := l776 }
    push := fun j hj ↦ by
      rw [mid _ (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj]), hP j hj,
        hiS _ (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj])]
    pull := fun j hj ↦ by
      rw [mid _ (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj]), hL j hj,
        hiS _ (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj])]
    count := fun j hj ↦ by
      rw [mid _ (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj]), hC j hj,
        hiS _ (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj])]
    bc := l720
    lb := l736
    stack := hst
    tracks := tracks14 H₁.tracks H₁.ok hst
    x27 := by
      rw [b80003454_x27 h₁, sp]; rv_eval []; exact s2520 }⟩)⟩

/-- R14: from `0x800033f0` to `next_scalars(2)`'s call at `0x800034c0` (or `Err` 26). -/
theorem r14 (hMC : MemcpySpec 0x800126e4) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 lo3 : Nat} {PL : Word} (hpre : WalkPre s)
    (hpc : u.pc = 0x800033f0) (h : AtR14 OI s u A k R Q B lo lo2 lo3 PL) :
    ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t ∨
      (t.pc = 0x800034c0 ∧ AtR15 OI s t A k R Q B lo (heapNext u))) := by
  obtain ⟨c, hr, hd | ⟨hpc₁, Kc, hnc, mh, rg, -, -, hi, hP, hL, hC⟩⟩ := lay14a hMC hpre hpc h
  · exact ⟨c, hr, Or.inr (Or.inl hd)⟩
  obtain ⟨t, hr', ht⟩ := lay14b hDL hpre h hpc₁ Kc hnc mh rg hi hP hL hC
  exact ⟨t, hr.trans hr', ht⟩

end Rv64Verifier.Proofs.Walk
