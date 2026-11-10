import Rv64Verifier.Proofs.Walk.R15B

/-!
# `walk` R16: `verify_bus_balance`'s precondition

What the call reads lies in `walk`'s frame or in the heap `walk` allocated before `AtR15`, which
nothing has written since (`roFrame`, `roHeap`, `vecRO`). Every buffer it reads is nonempty
(`tablesNe`, `busNe`: the statement's tables), so its pointer is in the heap. The `Bytecode` is read
as `BcOk` says, `BcWalk` carrying it from `walk`'s entry.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.LayoutMirror Rv64Verifier.Transcript Rv64Verifier.Bus

/-! ## The tables' shapes -/

/-- Every table has blocks on each side, a padding row, and forms with terms. -/
theorem tablesNe : (tablesRust.all fun t ↦ !t.flushes.push.isEmpty && !t.flushes.pull.isEmpty &&
    !t.countColumns.isEmpty && !t.padding.isEmpty &&
    (t.flushes.push ++ t.flushes.pull).all fun c ↦ !c.isEmpty && c.all fun f ↦ !f.terms.isEmpty) =
    true := by
  decide +kernel

theorem tableNe {t : TableRust} (ht : t ∈ tablesRust) :
    t.flushes.push ≠ [] ∧ t.flushes.pull ≠ [] ∧ t.countColumns ≠ [] ∧ t.padding ≠ [] ∧
      ∀ c ∈ t.flushes.push ++ t.flushes.pull, c ≠ [] ∧ ∀ f ∈ c, f.terms ≠ [] := by
  have := List.all_eq_true.mp tablesNe t ht
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
    at this
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
  exact ⟨h1, h2, h3, h4, fun c hc ↦ ⟨(h5 c hc).1, fun f hf ↦ (h5 c hc).2 f hf⟩⟩

/-- A list of blocks whose coordinates and forms are nonempty. -/
def BlocksNe (L : List BusBlockRust) : Prop :=
  L ≠ [] ∧ ∀ b ∈ L, b.coordinates ≠ [] ∧ ∀ f ∈ b.coordinates, f.terms ≠ []

theorem busNe {H : List ℕ} {R : List (BitVec 64)} (hH : H.length = 6) (hR : R.length = 6) :
    BlocksNe (busBlocksRust tablesRust H R).1 ∧ BlocksNe (busBlocksRust tablesRust H R).2.1 ∧
      BlocksNe (busBlocksRust tablesRust H R).2.2 := by
  have hT : tablesRust.length = 6 := by decide
  obtain ⟨t0, ts, eT⟩ : ∃ t0 ts, tablesRust = t0 :: ts := by
    rcases h : tablesRust with _ | ⟨t0, ts⟩
    · rw [h] at hT; simp at hT
    · exact ⟨t0, ts, rfl⟩
  obtain ⟨h0, H', rfl⟩ : ∃ h0 H', H = h0 :: H' := by
    rcases H with _ | ⟨h0, H'⟩
    · simp at hH
    · exact ⟨h0, H', rfl⟩
  obtain ⟨r0, R', rfl⟩ : ∃ r0 R', R = r0 :: R' := by
    rcases R with _ | ⟨r0, R'⟩
    · simp at hR
    · exact ⟨r0, R', rfl⟩
  have m0 : t0 ∈ tablesRust := by rw [eT]; exact List.mem_cons_self
  obtain ⟨n1, n2, n3, -, -⟩ := tableNe m0
  have mem : ∀ x ∈ (tablesRust.zip (h0 :: H')).zip (r0 :: R'), x.1.1 ∈ tablesRust :=
    fun x hx ↦ (List.of_mem_zip (List.of_mem_zip hx).1).1
  unfold busBlocksRust
  rw [foldl_append3]
  simp only [List.nil_append]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    rw [eT] at h
    simp only [List.zip_cons_cons, List.flatMap_cons, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
    exact n1 h.1
  · simp only [List.mem_flatMap, List.mem_map]
    rintro b ⟨x, hx, c, hc, rfl⟩
    exact (tableNe (mem x hx)).2.2.2.2 c (List.mem_append_left _ hc)
  · intro h
    rw [eT] at h
    simp only [List.zip_cons_cons, List.flatMap_cons, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
    exact n2 h.1
  · simp only [List.mem_flatMap, List.mem_map]
    rintro b ⟨x, hx, c, hc, rfl⟩
    exact (tableNe (mem x hx)).2.2.2.2 c (List.mem_append_right _ hc)
  · intro h
    rw [eT] at h
    simp only [List.zip_cons_cons, List.flatMap_cons, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
    exact n3 h.1
  · simp only [List.mem_flatMap, List.mem_map]
    rintro b ⟨x, hx, l, -, rfl⟩
    simp [colRust, FormRust.term]

/-! ## What the call only reads -/

/-- `verify_bus_balance`'s writes in `walk`'s frame: its result. -/
abbrev busWs (s : MachineState) : List (Word × Nat) := [(s.getReg .x2 - 928, 120)]

theorem busStack_le : busBalanceStack ≤ 8736 := by decide

/-- An allocated heap range. -/
theorem roHeap {s c : MachineState} (hpre : WalkPre s) (I : Inv s c) {p : Word} {m : Nat}
    (hal : p.toNat % 8 = 0) (h1 : heapStart ≤ p.toNat) (h2 : p.toNat + m ≤ heapNext c) :
    RO c busBalanceStack (busWs s) (tp s) p m := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have hh := I.heap.hi
  have hs := busStack_le
  simp only [heapStart, heapEnd, heapNext] at h1 h2 hab hh
  refine ⟨Or.inr ⟨by simp only [Mapped]; omega, hal⟩, ⟨Or.inl h2, by addr_omega [h2, hh]⟩, ?_, ?_, ?_⟩
  · rw [stackLo_callee I]; addr_omega [h2, hh, hab, hb1, hs]
  · intro x hx
    simp only [busWs, List.mem_singleton] at hx
    subst hx
    addr_omega [h2, hh, hab, hb1]
  · rw [tp]; addr_omega [h2, hh, hab, hb1]

/-- A frame range `[S - k, S - k + n)`, apart from the result and the sponge. -/
theorem roFrame {s c : MachineState} (hpre : WalkPre s) (I : Inv s c) {k n : Nat}
    (hk : 104 + n ≤ k ∧ k ≤ 2656) (h8 : k % 8 = 0) (ho : k ≤ 808 ∨ 928 + n ≤ k)
    (ht : k ≤ 2096 ∨ 2440 + n ≤ k) :
    RO c busBalanceStack (busWs s) (tp s) (s.getReg .x2 - BitVec.ofNat 64 k) n := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hfm := frameMapped hpre
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx
  have hs := busStack_le
  simp only [heapEnd, Mapped] at hab hfm
  refine ⟨Or.inr ⟨by simp only [Mapped]; addr_omega [hfm, hb1, hk], by addr_omega [hb1, hb3, hk, h8]⟩,
    ⟨Or.inr (by simp only [heapEnd]; addr_omega [hab, hb1, hk]), by addr_omega [hx, hb1, hk]⟩, ?_, ?_, ?_⟩
  · rw [stackLo_callee I]; addr_omega [hb1, hk, hs]
  · intro x hx
    simp only [busWs, List.mem_singleton] at hx
    subst hx
    addr_omega [hb1, hk, ho]
  · rw [tp]; addr_omega [hb1, hk, ht]

/-- A `Vec`'s nonempty buffer, allocated before `u₀`. -/
theorem vecRO {s u₀ c : MachineState} (hpre : WalkPre s) (I : Inv s c)
    (hmono : heapNext u₀ ≤ heapNext c) {a : Word} {size : Nat} (hv : VecOk u₀ a size 8)
    (hne : (vecLen u₀ a).toNat ≠ 0) (hsz : 0 < size) :
    RO c busBalanceStack (busWs s) (tp s) (vecPtr u₀ a) (size * (vecLen u₀ a).toNat) := by
  obtain ⟨h8, hb⟩ := Layout.vecBuf_bounds hv hsz
  have hle := hv.len
  rcases hb with hb | ⟨hb1, hb2⟩
  · omega
  have : size * (vecLen u₀ a).toNat ≤ (vecCap u₀ a).toNat * size := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hle
  exact roHeap hpre I h8 hb1 (by omega)

/-- A `Vec` header below `NEXT` at `u₀`, read the same in `c`. -/
theorem hdrEq {u₀ c : MachineState} (hu : HeapOk u₀)
    (hm : ∀ x : Word, x.toNat + 8 ≤ heapNext u₀ → c.getMem x = u₀.getMem x) {a : Word}
    (ha : a.toNat + 24 ≤ heapNext u₀) : vecPtr c a = vecPtr u₀ a ∧ vecLen c a = vecLen u₀ a := by
  have hh := hu.hi
  simp only [heapEnd] at hh
  exact ⟨hm _ (by addr_omega [ha, hh]), hm _ (by addr_omega [ha, hh])⟩

/-- The blocks' `Vec`s are nonempty in memory as in the mirror. -/
theorem blocksNe_mem {u : MachineState} {V : Word} (h : BlocksNe (blocksOf u V)) :
    (vecLen u V).toNat ≠ 0 ∧ ∀ i < (vecLen u V).toNat,
      (vecLen u (vecPtr u V + BitVec.ofNat 64 (48 * i))).toNat ≠ 0 ∧
      ∀ j < (vecLen u (vecPtr u V + BitVec.ofNat 64 (48 * i))).toNat,
        (vecLen u (vecPtr u (vecPtr u V + BitVec.ofNat 64 (48 * i)) +
          BitVec.ofNat 64 (24 * j))).toNat ≠ 0 := by
  obtain ⟨hne, hall⟩ := h
  refine ⟨fun h0 ↦ hne (by simp [blocksOf, blocksAt, h0]), fun i hi ↦ ?_⟩
  have hb : blockOf u (vecPtr u V + BitVec.ofNat 64 (48 * i)) ∈ blocksOf u V := by
    simp only [blocksOf, blocksAt, List.mem_map, List.mem_range]
    exact ⟨i, hi, rfl⟩
  obtain ⟨hc, hf⟩ := hall _ hb
  refine ⟨fun h0 ↦ hc (by simp [blockOf, Layout.formVecOf, Layout.formsAt, h0]), fun j hj h0 ↦ ?_⟩
  refine hf (Layout.formOf u (vecPtr u (vecPtr u V + BitVec.ofNat 64 (48 * i)) +
    BitVec.ofNat 64 (24 * j))) ?_ (by simp [Layout.formOf, Layout.termsOf, h0])
  simp only [blockOf, Layout.formVecOf, Layout.formsAt, List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

set_option maxRecDepth 8192 in
/-- A side's `Vec<BusBlock>` in the `Layout` at `S - k`, its header a copy of `walk`'s at `V`. -/
theorem blocksRO {s u₀ c : MachineState} (hpre : WalkPre s) (I : Inv s c) (hu : HeapOk u₀)
    (hmono : heapNext u₀ ≤ heapNext c)
    (hm : ∀ x : Word, x.toNat + 8 ≤ heapNext u₀ → c.getMem x = u₀.getMem x)
    {k : Nat} {V : Word} (hk : k = 2056 ∨ k = 2032 ∨ k = 2008)
    (hhd : ∀ j < 3, c.getMem (s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 (8 * j)) =
      u₀.getMem (V + BitVec.ofNat 64 (8 * j)))
    (hok : BlocksOk u₀ V) (hne : BlocksNe (blocksOf u₀ V)) :
    BlocksRO c busBalanceStack (busWs s) (tp s) (s.getReg .x2 - BitVec.ofNat 64 k) := by
  have hh := hu.hi
  simp only [heapEnd] at hh
  obtain ⟨n0, nb⟩ := blocksNe_mem hne
  have eP : vecPtr c (s.getReg .x2 - BitVec.ofNat 64 k) = vecPtr u₀ V := hhd 1 (by omega)
  have eL : vecLen c (s.getReg .x2 - BitVec.ofNat 64 k) = vecLen u₀ V := hhd 2 (by omega)
  have hS := hok
  simp only [BlocksOk] at hS
  have hB := hS.buf
  have hle := hS.le
  simp only [Buf] at hB
  have hB2 := hB.2.resolve_left (by omega)
  refine ⟨roFrame hpre I (by omega) (by omega) (by omega) (by omega), ?_, fun i hi ↦ ?_⟩
  · rw [eP, eL]
    have := vecRO hpre I hmono hS.vecOk n0 (by decide : 0 < 48)
    exact this
  rw [eL] at hi
  rw [eP]
  have hfv := hS.elems i hi
  have hbk : (vecPtr u₀ V + BitVec.ofNat 64 (48 * i)).toNat + 48 ≤ heapNext u₀ := by
    addr_omega [hB2, hle, hi, hh]
  obtain ⟨bP, bL⟩ := hdrEq hu hm (a := vecPtr u₀ V + BitVec.ofNat 64 (48 * i)) (by omega)
  obtain ⟨cn, cf⟩ := nb i hi
  refine ⟨roHeap hpre I (by addr_omega [hB.1, hB2, hh, hi, hle]) (by addr_omega [hB2, hh, hi, hle])
      (by addr_omega [hB2, hh, hi, hle, hmono]), fun i' hi' ↦ ?_, fun i' hi' j hj ↦ ?_,
    fun i' hi' j hj q hq ↦ ?_⟩
  · obtain rfl : i' = 0 := by omega
    rw [show 24 * 0 = 0 from rfl, BitVec.add_zero, bP, bL]
    exact vecRO hpre I hmono hfv.vec cn (by decide)
  · obtain rfl : i' = 0 := by omega
    rw [show 24 * 0 = 0 from rfl, BitVec.add_zero] at hj ⊢
    rw [bL] at hj
    rw [bP]
    obtain ⟨c8, cb⟩ := Layout.vecBuf_bounds hfv.vec (by decide : 0 < 24)
    have cl := hfv.vec.len
    rcases cb with cb | ⟨cb1, cb2⟩
    · omega
    obtain ⟨fP, fL⟩ := hdrEq hu hm
      (a := vecPtr u₀ (vecPtr u₀ V + BitVec.ofNat 64 (48 * i)) + BitVec.ofNat 64 (24 * j))
      (by addr_omega [cb2, hj, cl, hh])
    rw [fP, fL]
    exact vecRO hpre I hmono (hfv.forms j hj).vec (cf j hj) (by decide)
  · obtain rfl : i' = 0 := by omega
    rw [show 24 * 0 = 0 from rfl, BitVec.add_zero] at hj hq ⊢
    rw [bL] at hj
    rw [bP] at hq ⊢
    obtain ⟨c8, cb⟩ := Layout.vecBuf_bounds hfv.vec (by decide : 0 < 24)
    have cl := hfv.vec.len
    rcases cb with cb | ⟨cb1, cb2⟩
    · omega
    have hf := hfv.forms j hj
    obtain ⟨fP, fL⟩ := hdrEq hu hm
      (a := vecPtr u₀ (vecPtr u₀ V + BitVec.ofNat 64 (48 * i)) + BitVec.ofNat 64 (24 * j))
      (by addr_omega [cb2, hj, cl, hh])
    rw [fL] at hq
    rw [fP]
    obtain ⟨t8, tb⟩ := Layout.vecBuf_bounds hf.vec (by decide : 0 < 48)
    have tl := hf.vec.len
    rcases tb with tb | ⟨tb1, tb2⟩
    · omega
    rw [hm _ (by addr_omega [tb2, hq, tl, hh])]
    exact hf.tags q hq

/-! ## The precondition -/

/-- `BcOk` holds of `walk`'s `Bytecode` in any state past the prologue, and `bev` reads it as
`evaluateRust`: the bytecode is only read. -/
def BcWalk (BcOk : MachineState → Nat → Word → Prop)
    (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s c, WalkPre s → Inv s c → BcOk c busBalanceStack (s.getReg .x11) ∧
    bev c (s.getReg .x11) = evaluateRust (Proofs.Bytecode.readBytecode s (s.getReg .x11))

/-- What the steps from `u₀` write misses the heap below `NEXT` at `u₀`. -/
theorem StepW.heapMiss {s u₀ c : MachineState} (hpre : WalkPre s) {T : Prop}
    (st : StepW s u₀ c (W15 s) T) {x : Word} (hx : x.toNat < heapNext u₀) :
    ¬ (W15 s x ∨ Within x (s.getReg .x2 - 11392) 8736 ∨ Within x nextAddr 8 ∨ Fresh u₀ c x ∨
      (T ∧ Within x (tp s + 8) 352)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have hh := st.heap.hi
  have hm := st.mono
  simp only [W15, Fresh, Within, heapNext, heapEnd, nextAddr, tp] at hx hab hh hm ⊢
  rintro ((h | h) | h | h | ⟨h, -⟩ | ⟨-, h⟩) <;> addr_omega [h, hx, hab, hh, hm, hb1]

/-- The doublewords below `NEXT` at `u₀` are kept. -/
theorem StepW.heapKeep {s u₀ c : MachineState} (hpre : WalkPre s) {T : Prop}
    (st : StepW s u₀ c (W15 s) T) {x : Word} (hx : x.toNat + 8 ≤ heapNext u₀) :
    c.getMem x = u₀.getMem x :=
  st.getH hpre (fun _ ha ↦ W15.inF hpre ha) hx

/-- A `Vec<E>` allocated before `u₀`, its header read the same in `c`, holds the same. -/
theorem vecEsKeep {s u₀ c : MachineState} (hpre : WalkPre s) {T : Prop}
    (st : StepW s u₀ c (W15 s) T) {a : Word} (hv : VecOk u₀ a 24 8)
    (hp : vecPtr c a = vecPtr u₀ a) (hl : vecLen c a = vecLen u₀ a) : vecEs c a = vecEs u₀ a := by
  obtain ⟨h8, hb⟩ := Layout.vecBuf_bounds hv (by decide)
  have hle := hv.len
  simp only [vecEs, hp, hl]
  rcases hb with hb | ⟨-, hb2⟩
  · have : (vecLen u₀ a).toNat = 0 := by omega
    rw [this]; rfl
  · exact st.eListH hpre (fun _ ha ↦ W15.inF hpre ha) (by omega)

theorem tables_length : tables.length = 6 := by decide

/-- A side's header in the `Layout`, read at the call, is `walk`'s at `u₀`. -/
theorem hdrCopy {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ c : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s)
    (h : AtBus OI s u₀ c A k R Q B lo lo2) {k' : Nat} {W : Word}
    (hk : k' = 2056 ∨ k' = 2032 ∨ k' = 2008)
    (hc : ∀ j < 3, u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k' + BitVec.ofNat 64 (8 * j)) =
      u₀.getMem (W + BitVec.ofNat 64 (8 * j))) :
    ∀ j < 3, c.getMem (s.getReg .x2 - BitVec.ofNat 64 k' + BitVec.ofNat 64 (8 * j)) =
      u₀.getMem (W + BitVec.ofNat 64 (8 * j)) := fun j hj ↦ by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [← hc j hj, show s.getReg .x2 - BitVec.ofNat 64 k' + BitVec.ofNat 64 (8 * j) =
    s.getReg .x2 - BitVec.ofNat 64 (k' - 8 * j) by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hk, hj]]
  exact h.st.slot15 hpre (by omega) (by omega)

/-! ## The `Bytecode`'s doublewords -/

theorem bcIn_parts {s : MachineState} {p : Word} (hb : BytecodeIn s p) :
    ∀ q ∈ bcParts s p, ReadOnly s q.1 q.2 := by
  intro q hq
  simp only [bcParts, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hb.self
  · exact hb.blocks
  · exact hb.words
  · exact hb.positions
  · exact hb.bytes

/-- Bytes apart from an aligned range: so is each aligned doubleword holding one of them. -/
theorem apart_dword {a q b : Word} {n m : Nat} (h : Apart q n b m) (hb : b.toNat % 8 = 0)
    (hm : m % 8 = 0) (ha : Meets a q n) : Apart a 8 b m := by
  simp only [Apart, Meets] at h ha ⊢
  omega

/-- A doubleword holding a byte of a part only read misses `walk`'s stack, its result and
`NEXT`. -/
theorem bcDword {s : MachineState} (hpre : WalkPre s) {q a : Word} {n : Nat}
    (hq : ReadOnly s q n) (ha : Meets a q n) :
    Apart a 8 (s.getReg .x2 - 11392) 11392 ∧ Apart a 8 (s.getReg .x10) 80 ∧
      Apart a 8 nextAddr 8 := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hs := hq.2.1
  rw [stackLo_eq, stack_eq] at hs
  exact ⟨apart_dword hs (by addr_omega [hb1, hb3]) (by decide) ha,
    apart_dword hq.2.2.1 hpre.out.2 (by decide) ha, apart_dword hq.1.2 (by decide) (by decide) ha⟩

/-- A doubleword holding a byte of a part only read, below `NEXT` at the entry or above the heap,
is kept. -/
theorem bcKeep {s c : MachineState} (hpre : WalkPre s) (I : Inv s c) {q a : Word} {n : Nat}
    (hq : ReadOnly s q n) (hend : q.toNat + n ≤ 0xc0000000) (ha : Meets a q n)
    (hc : a.toNat + 8 ≤ heapNext s ∨ heapEnd ≤ a.toNat) : c.getMem a = s.getMem a := by
  obtain ⟨hs, ho, hn⟩ := bcDword hpre hq ha
  have hm := I.heap.hi
  simp only [Meets] at ha
  simp only [heapNext, heapEnd] at hc hm
  refine I.frame a (fun x hx hw ↦ ?_) (by omega)
  simp only [WalkW, Fresh, stackLo_eq] at hw
  rcases hw with hw | hw | hw | ⟨f1, f2⟩
  · addr_omega [hx, hw, ho, ha, hend]
  · addr_omega [hx, hw, hs, ha, hend]
  · addr_omega [hx, hw, hn, ha, hend]
  · simp only [heapNext] at f1 f2; addr_omega [hx, f1, f2, hc, hm, ha, hend]

/-- The `Bytecode`'s header, kept. -/
theorem bcHdr {s c : MachineState} (hpre : WalkPre s) (I : Inv s c) {k : Nat} (hk8 : k % 8 = 0)
    (hk : k + 8 ≤ 136) :
    c.getMem (s.getReg .x11 + BitVec.ofNat 64 k) = s.getMem (s.getReg .x11 + BitVec.ofNat 64 k) := by
  have hm := hpre.bytecode.mem
  have hro := hpre.bytecode.self
  have he : (s.getReg .x11).toNat + 136 ≤ 0xc0000000 := by
    have := hm.self; simp only [Mapped] at this; omega
  have hal := hm.align
  refine bcKeep hpre I hro he ⟨by addr_omega [hal, he, hk8, hk], by addr_omega [he, hk],
    by addr_omega [he, hk], by omega⟩ ?_
  rcases hro.1.1 with h0 | h0
  · exact Or.inl (by addr_omega [h0, he, hk])
  · exact Or.inr (by addr_omega [h0, he, hk])

/-- The `Bytecode`'s parts, read in a state past the entry. -/
theorem bcParts_walk {s c : MachineState} (hpre : WalkPre s) (I : Inv s c) :
    bcParts c (s.getReg .x11) = bcParts s (s.getReg .x11) := by
  have w2 (b j : Nat) (hb : b + j + 8 ≤ 136) (hj : (b + j) % 8 = 0) :
      c.getMem (s.getReg .x11 + BitVec.ofNat 64 b + BitVec.ofNat 64 j) =
        s.getMem (s.getReg .x11 + BitVec.ofNat 64 b + BitVec.ofNat 64 j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact bcHdr hpre I hj hb
  have p0 : vecPtr c (s.getReg .x11) = vecPtr s (s.getReg .x11) := bcHdr hpre I (k := 8) rfl (by omega)
  have l0 : vecLen c (s.getReg .x11) = vecLen s (s.getReg .x11) :=
    bcHdr hpre I (k := 16) rfl (by omega)
  have p1 : vecPtr c (s.getReg .x11 + 24) = vecPtr s (s.getReg .x11 + 24) := w2 24 8 (by omega) rfl
  have l1 : vecLen c (s.getReg .x11 + 24) = vecLen s (s.getReg .x11 + 24) := w2 24 16 (by omega) rfl
  have p2 : vecPtr c (s.getReg .x11 + 48) = vecPtr s (s.getReg .x11 + 48) := w2 48 8 (by omega) rfl
  have l2 : vecLen c (s.getReg .x11 + 48) = vecLen s (s.getReg .x11 + 48) := w2 48 16 (by omega) rfl
  have p3 : vecPtr c (s.getReg .x11 + 72) = vecPtr s (s.getReg .x11 + 72) := w2 72 8 (by omega) rfl
  have l3 : vecLen c (s.getReg .x11 + 72) = vecLen s (s.getReg .x11 + 72) := w2 72 16 (by omega) rfl
  simp only [bcParts, p0, l0, p1, l1, p2, l2, p3, l3]

/-- The `Bytecode`'s doublewords miss `verify_bus_balance`'s result and the transcript's sponge,
both in `walk`'s frame. -/
theorem bcApart {s c : MachineState} (hpre : WalkPre s) (I : Inv s c) {x : Word} {m : Nat}
    (hx1 : (s.getReg .x2).toNat - 11392 ≤ x.toNat) (hx2 : x.toNat + m ≤ (s.getReg .x2).toNat) :
    ∀ q ∈ bcParts c (s.getReg .x11), ∀ a, Meets a q.1 q.2 → Apart a 8 x m := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [bcParts_walk hpre I]
  intro q hq a ha
  obtain ⟨hs, -, -⟩ := bcDword hpre (bcIn_parts hpre.bytecode q hq) ha
  addr_omega [hs, hx1, hx2, hb1]

set_option maxRecDepth 8192 in
/-- `verify_bus_balance`'s precondition at its call. -/
theorem busPre {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hBW : BcWalk BcOk bev)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ c : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s)
    (h : AtBus OI s u₀ c A k R Q B lo lo2) : BusBalancePreB BcOk c := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have I := h.inv
  have H := h.at15.keep.at11.base
  have V := h.at15.keep.at11.vecs
  have hu := H.inv.heap
  have hmono := h.st.mono
  have hm : ∀ x : Word, x.toNat + 8 ≤ heapNext u₀ → c.getMem x = u₀.getMem x :=
    fun _ hx ↦ h.st.heapKeep hpre hx
  have sl (k' : Nat) (hk : 104 + 8 ≤ k' ∧ k' ≤ 2656)
      (hn : (k' ≤ 808 ∨ 928 + 8 ≤ k') ∧ (k' ≤ 1768 ∨ 1800 + 8 ≤ k') ∧ (k' ≤ 2088 ∨ 2440 + 8 ≤ k')) :
      c.getMem (s.getReg .x2 - BitVec.ofNat 64 k') = u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k') :=
    h.st.slot15 hpre hk hn
  have ptr : c.getMem (tp s) = s.getReg .x13 := by
    rw [show tp s = s.getReg .x2 - BitVec.ofNat 64 2448 from rfl, sl 2448 (by omega) (by omega)]
    exact H.proofPtr
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  have hro := hpre.stack.rodata
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx hro
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hrs : rodataStart.toNat = 2684354560 := rfl
  have pRO := hpre.proofRO.2.1
  have sRO := hpre.streamRO.2.1
  rw [stackLo_eq, stack_eq] at pRO sRO
  obtain ⟨e0, e1, e2⟩ := proofVals hpre I ptr
  have hsl := stackLo_callee I busBalanceStack
  have hs := busStack_le
  simp only [heapEnd] at hab
  have hlen : (tableLogHeightsRust (rowsOf A)).length = 6 := hts_length A H.rowsLen
  obtain ⟨nP, nL, nC⟩ := busNe hlen H.rowsLen
  have e24 : s.getReg .x2 - 2080 + 24 = s.getReg .x2 - BitVec.ofNat 64 2056 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e48 : s.getReg .x2 - 2080 + 48 = s.getReg .x2 - BitVec.ofNat 64 2032 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e72 : s.getReg .x2 - 2080 + 72 = s.getReg .x2 - BitVec.ofNat 64 2008 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨tP, tL⟩ := tablesVec15 hpre h.at15 h.st
  have hbB := H.bufB
  have hlo := hpre.heap.lo
  have hl := H.loLe
  have hhs := h.at15.keep.lo2le
  simp only [heapStart] at hlo
  have hB8 : (B.toNat + 480) ≤ heapNext u₀ := by omega
  -- the tables' paddings, kept from `u₀`
  have pad (i : Nat) (hi : i < 6) : ∃ t, tablesRust[i]? = some t ∧
      TableAt u₀ (B + BitVec.ofNat 64 (80 * i)) t ∧
      vecPtr c (B + BitVec.ofNat 64 (80 * i)) = vecPtr u₀ (B + BitVec.ofNat 64 (80 * i)) ∧
      vecLen c (B + BitVec.ofNat 64 (80 * i)) = vecLen u₀ (B + BitVec.ofNat 64 (80 * i)) := by
    obtain ⟨t, ht⟩ : ∃ t, tablesRust[i]? = some t :=
      ⟨tablesRust[i]'(by have : tablesRust.length = 6 := by decide
                         omega), List.getElem?_eq_getElem _⟩
    have hh := hu.hi
    simp only [heapEnd] at hh
    exact ⟨t, ht, H.tables i t ht, hdrEq hu hm (by addr_omega [hbB, hB8, hi, hh])⟩
  refine {
    heap := I.heap
    stack := hpre.stack.sub 2656 I.sp (by rw [stack_eq]; omega) (by decide) (by decide)
      (by decide) (by decide)
    rodata := I.rodata hpre
    out := by rw [h.x10]; addr_omega [hb1, hb2, hb3]
    outFree := by
      rw [h.x10]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by addr_omega [hx, hb1]⟩
    outStack := by rw [h.x10, hsl]; addr_omega [hb1, hs]
    outRodata := by rw [h.x10]; addr_omega [hro, hrb, hrs, hb1]
    self := by rw [h.x12]; exact tok hpre I ptr
    checked := by
      rw [h.x12, byteAt_congr (by rw [tp]; addr_omega [hb1, hb3])
        (show c.getMem (tp s + 360) = u₀.getMem (tp s + 360) by
          rw [show tp s + 360 = s.getReg .x2 - BitVec.ofNat 64 2088 by
            rw [tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
          exact sl 2088 (by omega) (by omega)), H.checked]
      decide
    selfStack := by rw [h.x12, hsl, tp]; addr_omega [hb1, hs]
    selfOut := by rw [h.x10, h.x12, tp]; addr_omega [hb1]
    selfFree := by rw [h.x12, tp]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by addr_omega [hx, hb1]⟩
    selfRodata := by rw [h.x12, tp]; addr_omega [hro, hrb, hrs, hb1]
    proofStack := by
      rw [h.x12]; simp only [ProofApart, e0, e1, e2, hsl]
      exact ⟨by addr_omega [pRO, hb1, hs], by addr_omega [sRO, hb1, hs]⟩
    proofOut := by
      rw [h.x12, h.x10]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [pRO, hb1], by addr_omega [sRO, hb1]⟩
    proofFree := by rw [h.x12, e0]; exact outside_mono' hpre.proofRO.1 I.mono
    streamFree := by rw [h.x12, e1, e2]; exact outside_mono' hpre.streamRO.1 I.mono
    layout := by
      rw [h.x10, h.x11, h.x12]
      exact roFrame hpre I (k := 2080) (n := 168) (by omega) (by omega) (by omega) (by omega)
    push := by
      rw [h.x11, h.x12, h.x10, e24]
      exact blocksRO hpre I hu hmono hm (Or.inl rfl)
        (hdrCopy hpre h (W := s.getReg .x2 - 416) (Or.inl rfl) h.at15.push) V.push (V.pushV ▸ nP)
    pull := by
      rw [h.x11, h.x12, h.x10, e48]
      exact blocksRO hpre I hu hmono hm (Or.inr (Or.inl rfl))
        (hdrCopy hpre h (W := s.getReg .x2 - 224) (Or.inr (Or.inl rfl)) h.at15.pull) V.pull (V.pullV ▸ nL)
    count := by
      rw [h.x11, h.x12, h.x10, e72]
      exact blocksRO hpre I hu hmono hm (Or.inr (Or.inr rfl))
        (hdrCopy hpre h (W := s.getReg .x2 - 512) (Or.inr (Or.inr rfl)) h.at15.count) V.count (V.countV ▸ nC)
    tablesLen := by rw [h.x11, tL, tables_length]; rfl
    tablesRO := by
      rw [h.x11, h.x12, h.x10, tP, tables_length]
      exact roHeap hpre I hbB.2.1 (by simp only [heapStart]; omega) (by omega)
    padding := fun i hi ↦ by
      rw [tables_length] at hi
      obtain ⟨t, ht, hT, eP, eL⟩ := pad i hi
      rw [h.x11, tP, vecEsKeep hpre h.st hT.padVec eP eL, hT.pad]
      have e := congrArg (·[i]?) tablesRust_padding
      simp only [List.getElem?_map, ht, Option.map_some] at e
      rw [List.getElem?_eq_getElem (by rw [tables_length]; exact hi), Option.map_some,
        Option.some_inj] at e
      rw [e, List.getD_eq_getElem _ _ (by rw [tables_length]; exact hi)]
    paddingRO := fun i hi ↦ by
      rw [tables_length] at hi
      obtain ⟨t, ht, hT, eP, eL⟩ := pad i hi
      rw [h.x11, h.x12, h.x10, tP, eP, eL]
      refine vecRO hpre I hmono hT.padVec ?_ (by decide)
      have hp := hT.pad
      have hne := (tableNe (List.mem_of_getElem? ht)).2.2.2.1
      intro h0
      apply hne
      rw [← hp, vecEs, h0]
      rfl
    bytecode := by
      have e144 : c.getReg .x11 + 144 = s.getReg .x2 - BitVec.ofNat 64 1936 := by
        rw [h.x11]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have hbc : u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 1936) = s.getReg .x11 := h.at15.bc
      rw [bytecodeOf, e144, sl 1936 (by omega) (by omega), hbc]
      exact (hBW s c hpre I).1
    bytecodeApart := by
      have e144 : c.getReg .x11 + 144 = s.getReg .x2 - BitVec.ofNat 64 1936 := by
        rw [h.x11]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have hbc : u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 1936) = s.getReg .x11 := h.at15.bc
      rw [bytecodeOf, e144, sl 1936 (by omega) (by omega), hbc]
      intro q hq a ha
      exact ⟨bcApart hpre I (by rw [h.x10]; addr_omega [hb1]) (by rw [h.x10]; addr_omega [hb1]) q hq a ha,
        bcApart hpre I (by rw [h.x12, tp]; addr_omega [hb1]) (by rw [h.x12, tp]; addr_omega [hb1])
          q hq a ha⟩ }

theorem vbb_congr (f : List E → Option E) {L₁ L₂ : LeanVM.Protocol.Verifier.Layout}
    (h1 : L₁.logMemory = L₂.logMemory) (h2 : L₁.logBytecode = L₂.logBytecode)
    (h3 : L₁.push = L₂.push) (h4 : L₁.pull = L₂.pull) (h5 : L₁.count = L₂.count) :
    verifyBusBalanceM f L₁ = verifyBusBalanceM f L₂ := by
  simp only [verifyBusBalanceM, h1, h2, h3, h4, h5]

/-- A side's blocks, read through a copy of its header, kept from `u₀`. -/
theorem sideEq {s u₀ c : MachineState} (hpre : WalkPre s) {T : Prop}
    (st : StepW s u₀ c (W15 s) T) (hu : HeapOk u₀) {L V : Word} (hP : vecPtr c L = vecPtr u₀ V)
    (hL : vecLen c L = vecLen u₀ V) (hok : BlocksOk u₀ V)
    (hbelow : ∀ x, blocksFoot u₀ V x → x.toNat < heapNext u₀) :
    Bus.blocksAt c L = (blocksOf u₀ V).map BusBlockRust.toSpec := by
  have hle := hok.le
  rw [← blocksOf_toSpec, blocksOf, hP, hL,
    (blocksAt_frame (dframe_l st.frame) hok (fun x hx ↦ st.heapMiss hpre (hbelow x (Or.inl (by
        simp only [Within] at hx ⊢; constructor <;> omega))))
      (fun x hx ↦ st.heapMiss hpre (hbelow x (Or.inr hx))) hu st.mono).1]
  rfl

set_option maxRecDepth 8192 in
/-- What the call computes is the mirror's bus. -/
theorem busArgs {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hBW : BcWalk BcOk bev)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ c : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s)
    (h : AtBus OI s u₀ c A k R Q B lo lo2) :
    verifyBusBalanceM (bev c (bytecodeOf c (c.getReg .x11))) (busLayoutAt c (c.getReg .x11)) =
      verifyBusBalanceM (evaluateRust (Proofs.Bytecode.readBytecode s (s.getReg .x11)))
        ((layoutOf A k).toSpec []) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have H := h.at15.keep.at11.base
  have V := h.at15.keep.at11.vecs
  have K := h.at15.keep
  have sl (k' : Nat) (hk : 104 + 8 ≤ k' ∧ k' ≤ 2656)
      (hn : (k' ≤ 808 ∨ 928 + 8 ≤ k') ∧ (k' ≤ 1768 ∨ 1800 + 8 ≤ k') ∧ (k' ≤ 2088 ∨ 2440 + 8 ≤ k')) :
      c.getMem (s.getReg .x2 - BitVec.ofNat 64 k') = u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k') :=
    h.st.slot15 hpre hk hn
  have eo (o k' : Nat) (ho : o + k' = 2080) :
      c.getReg .x11 + BitVec.ofNat 64 o = s.getReg .x2 - BitVec.ofNat 64 k' := by
    rw [h.x11]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, ho]
  have hbc : bytecodeOf c (c.getReg .x11) = s.getReg .x11 := by
    have hb : u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 1936) = s.getReg .x11 := h.at15.bc
    rw [bytecodeOf, show (144 : Word) = BitVec.ofNat 64 144 from rfl, eo 144 1936 rfl,
      sl 1936 (by omega) (by omega), hb]
  rw [hbc, (hBW s c hpre h.inv).2]
  have hlo2 := K.lo2le
  have side (k' : Nat) (W : Word) (hk : k' = 2056 ∨ k' = 2032 ∨ k' = 2008)
      (hc : ∀ j < 3, u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k' + BitVec.ofNat 64 (8 * j)) =
        u₀.getMem (W + BitVec.ofNat 64 (8 * j))) (hok : BlocksOk u₀ W)
      (hbl : ∀ x, blocksFoot u₀ W x → x.toNat < lo2) :
      Bus.blocksAt c (s.getReg .x2 - BitVec.ofNat 64 k') = (blocksOf u₀ W).map BusBlockRust.toSpec := by
    have hd := hdrCopy hpre h hk hc
    exact sideEq hpre h.st H.inv.heap (hd 1 (by omega)) (hd 2 (by omega)) hok
      fun x hx ↦ lt_of_lt_of_le (hbl x hx) hlo2
  refine vbb_congr _ ?_ ?_ ?_ ?_ ?_
  · show (c.getMem (c.getReg .x11 + 152)).toNat = _
    rw [show (152 : Word) = BitVec.ofNat 64 152 from rfl, eo 152 1928 rfl,
      sl 1928 (by omega) (by omega)]
    exact h.at15.layoutIn.logMemory
  · show (c.getMem (c.getReg .x11 + 160)).toNat = k - 4
    have hl : u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 1920) = BitVec.ofNat 64 (k - 4) := h.at15.lb
    have hk := H.ok.2.2.2.2
    have hbb : LayoutMirror.busBitsRust ≤ 64 := by decide
    rw [show (160 : Word) = BitVec.ofNat 64 160 from rfl, eo 160 1920 rfl,
      sl 1920 (by omega) (by omega), hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · show Bus.blocksAt c (c.getReg .x11 + 24) = _
    rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, eo 24 2056 rfl,
      side 2056 (s.getReg .x2 - 416) (Or.inl rfl) h.at15.push V.push
        (fun x hx ↦ K.below x (Or.inl hx)), V.pushV]
    rfl
  · show Bus.blocksAt c (c.getReg .x11 + 48) = _
    rw [show (48 : Word) = BitVec.ofNat 64 48 from rfl, eo 48 2032 rfl,
      side 2032 (s.getReg .x2 - 224) (Or.inr (Or.inl rfl)) h.at15.pull V.pull
        (fun x hx ↦ K.below x (Or.inr (Or.inl hx))), V.pullV]
    rfl
  · show Bus.blocksAt c (c.getReg .x11 + 72) = _
    rw [show (72 : Word) = BitVec.ofNat 64 72 from rfl, eo 72 2008 rfl,
      side 2008 (s.getReg .x2 - 512) (Or.inr (Or.inr rfl)) h.at15.count V.count
        (fun x hx ↦ K.below x (Or.inr (Or.inr hx))), V.countV]
    rfl

end Rv64Verifier.Proofs.Walk
