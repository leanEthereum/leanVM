import Rv64Verifier.Proofs.Pcs.VsoRows0B

/-!
# `verify_stacked_opening`'s level loop: level 0's rows, the loop over rows

From `0x8000b38c` (`R0O`, row `j`): the row's length from the slices at `S - 832`, `min` with
the kernel's (`0x8000b3a4`), zero for an empty zip (`0x8000b34c`), else `base_dot`'s loop
(`inner0`); at `0x8000b358` (`R0S`) the value goes to `Q + 24 j` (`store0`), `s7` comes back from
`S - 808`, and the loop goes on or leaves to `0x8000b42c` (`rows0`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem r0_mul24 (e : ℕ) :
    BitVec.ofNat 64 e * 16 + BitVec.ofNat 64 e * 8 = BitVec.ofNat 64 (24 * e) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

theorem r0_mul16 (e : ℕ) : BitVec.ofNat 64 e * 16 = BitVec.ofNat 64 (16 * e) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (16 : Word).toNat = 16 from rfl]
  omega

theorem r0_succ (e : ℕ) : BitVec.ofNat 64 e + 1 = BitVec.ofNat 64 (e + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
  omega

theorem r0_eListAt_succ (u : MachineState) (p : Word) (j : ℕ) :
    eListAt u p (j + 1) = eListAt u p j ++ [eAt u (p + BitVec.ofNat 64 (24 * j))] := by
  simp only [eListAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The frame's slots the loop does not write are kept. -/
theorem R0B.keep {s r u : MachineState} {Q : Word} {n : ℕ} {KP : Word} {lw : List E}
    (hpre : VsoPre s) (K : R0K s r Q n KP lw) (B : R0B s r Q n u) {y : Word}
    (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 384).toNat ∨
      (s.getReg .x2 - 360).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
    u.getMem y = r.getMem y := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  simp only [vso_stack] at hab
  have hq := K.q2
  exact B.fr y fun c hc h ↦ by
    simp only [R0W] at h
    rcases h with h | h | h <;> addr_omega [h, hc, hy, hb, hab, hq]

/-- The slices `P` of the rows `rows`, kept since `r`. -/
structure R0P (s r : MachineState) (Q : Word) (n : ℕ) (P : Word) (rows : List (List K)) :
    Prop where
  len : rows.length = n
  p : n = 0 ∨ Region P (16 * n)
  pmiss : ∀ y, Within y P (16 * n) → ¬ R0W s Q n y
  m832 : r.getMem (s.getReg .x2 - 832) = P
  row : ∀ j (h : j < rows.length), R0Row s r Q n (r.getMem (P + BitVec.ofNat 64 (16 * j))) rows[j]
  rlen : ∀ j (h : j < rows.length),
    (r.getMem (P + BitVec.ofNat 64 (16 * j + 8))).toNat = rows[j].length

/-- At `0x8000b38c`, `j` rows' values stored. -/
structure R0O (s r : MachineState) (Q : Word) (n : ℕ) (lw : List E) (rows : List (List K))
    (j : ℕ) (u : MachineState) : Prop where
  base : R0B s r Q n u
  x20 : u.getReg .x20 = BitVec.ofNat 64 n
  x21 : u.getReg .x21 = BitVec.ofNat 64 j
  x25 : u.getReg .x25 = Q
  x27 : u.getReg .x27 = BitVec.ofNat 64 j
  x23 : 0 < j → u.getReg .x23 = r.getMem (s.getReg .x2 - 808)
  vals : eListAt u Q j = (rows.take j).map (Model.Pcs.baseDot lw)

/-- At `0x8000b358`, row `j`'s value `e` in `s8, s7, s6`. -/
structure R0S (s r : MachineState) (Q : Word) (n : ℕ) (lw : List E) (rows : List (List K))
    (j : ℕ) (e : E) (w : MachineState) : Prop where
  base : R0B s r Q n w
  acc : (w.getReg .x24, w.getReg .x23, w.getReg .x22) = Model.limbs e
  x18 : w.getReg .x18 = BitVec.ofNat 64 n
  x19 : w.getReg .x19 = Q
  x21 : w.getReg .x21 = BitVec.ofNat 64 j
  x27 : w.getReg .x27 = BitVec.ofNat 64 j
  vals : eListAt w Q j = (rows.take j).map (Model.Pcs.baseDot lw)

/-- **Row `j`'s value stored**, from `0x8000b358` to the next row or the loop's exit. -/
theorem store0 {s r w : MachineState} {Q : Word} {n : ℕ} {KP : Word} {lw : List E}
    {rows : List (List K)} {j : ℕ} (hpre : VsoPre s) (K : R0K s r Q n KP lw)
    (hjr : j < rows.length) (hn : rows.length = n) (hpc : w.pc = 0x8000b358)
    (W : R0S s r Q n lw rows j (Model.Pcs.baseDot lw rows[j]) w) :
    ∃ v, Reaches Image.code w v ∧ R0O s r Q n lw rows (j + 1) v ∧
      ((j + 1 < n ∧ v.pc = 0x8000b38c) ∨ (j + 1 = n ∧ v.pc = 0x8000b42c)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  simp only [vso_stack] at hab
  have B := W.base
  have hq1 := K.q1
  have hq2 := K.q2
  have hq8 := K.q8
  have hj : j < n := hn ▸ hjr
  have hQ : Region Q (24 * n) := heap_region (by simp only [heapStart] at hq1; omega) hq2 hq8
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000b358_spec hpc (by
    rv_eval [B.sp, W.x19, W.x27, r0_mul24]
    and_intros
    all_goals first
      | (intro he; have := congrArg BitVec.toNat he; addr_omega [this, hb, hab, hq2, hj])
      | valid_access hst.valid [hb]
      | exact Region.valid hQ (by addr_omega [hq2, hj]) (by addr_omega [hq2, hj])
          (by addr_omega [hq2, hj, hq8]))
  have k₁ := b8000b358_keeps h
  have m0 := b8000b358_m0 h
  have m1 := b8000b358_m1 h
  have m2 := b8000b358_m2 h
  rw [W.x19, W.x27, r0_mul24] at m0 m1 m2
  have X : DFrame w v (Within · (Q + BitVec.ofNat 64 (24 * j)) 24) :=
    (holds_dframe h).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000b358, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> rv_eval [W.x19, W.x27, r0_mul24] at hw <;>
        addr_omega [hw, hq2, hj]
  have F : DFrame r v (R0W s Q n) :=
    B.fr.trans X fun _ h ↦ Or.inr (Or.inr (by addr_omega [h, hq2, hj]))
  have ev : eAt v (Q + BitVec.ofNat 64 (24 * j)) = Model.Pcs.baseDot lw rows[j] := by
    apply eAt_eq_of_limbs
    rw [← W.acc, m2, m1, m0]
  have hvals : eListAt v Q j = eListAt w Q j :=
    X.eListAt fun c hc hw ↦ by addr_omega [hw, hc, hq2, hj]
  have x2v : v.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans B.sp
  have x21v : v.getReg .x21 = BitVec.ofNat 64 (j + 1) := by
    rw [b8000b358_x21 h, W.x21, r0_succ]
  have x18v : v.getReg .x18 = BitVec.ofNat 64 n := (k₁ .x18 (by decide)).trans W.x18
  have O : R0O s r Q n lw rows (j + 1) v := {
    base := {
      sp := x2v
      fr := F
      x9 := (k₁ .x9 (by decide)).trans B.x9
      x26 := (k₁ .x26 (by decide)).trans B.x26 }
    x20 := by rw [b8000b358_x20 h, W.x18]
    x21 := x21v
    x25 := by rw [b8000b358_x25 h, W.x19]
    x27 := by rw [b8000b358_x27 h, W.x27, r0_succ]
    x23 := fun _ ↦ by
      rw [b8000b358_x23 h, B.sp, show s.getReg .x2 - 1040 + 232 = s.getReg .x2 - 808 by rv_eval []]
      exact B.keep hpre K (by addr_omega [hb])
    vals := by
      rw [r0_eListAt_succ, hvals, W.vals, ev, List.take_add_one, List.getElem?_eq_getElem hjr]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil] }
  by_cases hl : j + 1 = n
  · exact ⟨v, hr, O, Or.inr ⟨hl, b8000b358_pc_taken h (by rw [W.x21, W.x18, r0_succ, hl])⟩⟩
  · refine ⟨v, hr, O, Or.inl ⟨by omega, b8000b358_pc_not_taken h ?_⟩⟩
    rw [W.x21, W.x18, r0_succ]
    intro he
    have := congrArg BitVec.toNat he
    addr_omega [this, hq2, hj, hl]

/-- **Row `j`'s value**, from `0x8000b38c` to `0x8000b358`. -/
theorem row0 (hMK : MulKSpec) {s r u : MachineState} {Q : Word} {n : ℕ} {KP P : Word}
    {lw : List E} {rows : List (List K)} {j : ℕ} (hpre : VsoPre s) (K : R0K s r Q n KP lw)
    (Pp : R0P s r Q n P rows) (hjr : j < rows.length) (hpc : u.pc = 0x8000b38c)
    (O : R0O s r Q n lw rows j u) :
    ∃ w, Reaches Image.code u w ∧ ((w.pc = 0x8000b358 ∧
      R0S s r Q n lw rows j (Model.Pcs.baseDot lw rows[j]) w) ∨ Dead Image.code w) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have B := O.base
  have hj : j < n := Pp.len ▸ hjr
  have hP : Region P (16 * n) := Pp.p.resolve_left (by omega)
  have hPb := Region.bounds hP
  have R := Pp.row j hjr
  have hl := Pp.rlen j hjr
  have hlen : rows[j].length < 2 ^ 59 := by
    rcases R.region with h | h
    · omega
    · have := Region.bounds h; omega
  have hkl : lw.length < 2 ^ 59 := by
    rcases K.kfit with h | h
    · omega
    · simp only [heapEnd] at h; omega
  have pk (y : Word) (hy : P.toNat ≤ y.toNat ∧ y.toNat + 8 ≤ P.toNat + 16 * n) :
      u.getMem y = r.getMem y :=
    B.fr y fun c hc h ↦ Pp.pmiss _ (by addr_omega [hc, hy, hPb]) h
  have a208 : u.getMem (u.getReg .x2 + 208) = P := by
    rw [B.sp, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by rv_eval []]
    exact (B.keep hpre K (by addr_omega [hb])).trans Pp.m832
  have a256 : u.getMem (u.getReg .x2 + 256) = BitVec.ofNat 64 lw.length := by
    rw [B.sp, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval []]
    exact (B.keep hpre K (by addr_omega [hb])).trans K.m784
  have a136 : u.getMem (u.getReg .x2 + 136) = KP := by
    rw [B.sp, show s.getReg .x2 - 1040 + 136 = s.getReg .x2 - 904 by rv_eval []]
    exact (B.keep hpre K (by addr_omega [hb])).trans K.m904
  have aL : u.getMem (u.getMem (u.getReg .x2 + 208) + u.getReg .x21 * 16 + 8) =
      BitVec.ofNat 64 rows[j].length := by
    rw [a208, O.x21, r0_mul16, show P + BitVec.ofNat 64 (16 * j) + 8 =
      P + BitVec.ofNat 64 (16 * j + 8) by addr_omega [hPb, hj], pk _ (by addr_omega [hPb, hj])]
    apply BitVec.eq_of_toNat_eq
    rw [hl, BitVec.toNat_ofNat]
    omega
  have aP : u.getMem (u.getMem (u.getReg .x2 + 208) + u.getReg .x21 * 16) =
      r.getMem (P + BitVec.ofNat 64 (16 * j)) := by
    rw [a208, O.x21, r0_mul16, pk _ (by addr_omega [hPb, hj])]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b38c_spec hpc (by
    rv_eval [B.sp, O.x21]
    and_intros
    · valid_access hst.valid [hb]
    · have e := a208
      rw [B.sp, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by rv_eval []] at e
      rw [e, r0_mul16]
      exact Region.valid hP (by addr_omega [hPb, hj]) (by addr_omega [hPb, hj])
        (by addr_omega [hPb, hj])
    · valid_access hst.valid [hb])
  have k₁ := b8000b38c_keeps h₁
  have m₁ := b8000b38c_mem_same h₁
  have x10₁ : u₁.getReg .x10 = BitVec.ofNat 64 rows[j].length := by rw [b8000b38c_x10 h₁, aL]
  have x12₁ : u₁.getReg .x12 = P + BitVec.ofNat 64 (16 * j) := by
    rw [b8000b38c_x12 h₁, a208, O.x21, r0_mul16]
  -- `min(len, lane_weights.len())`
  obtain ⟨u₂, hr₂, pc₂, x11₂, k₂, m₂⟩ : ∃ u₂, Reaches Image.code u₁ u₂ ∧
      u₂.pc = 0x8000b3ac ∧
      u₂.getReg .x11 = BitVec.ofNat 64 (min rows[j].length lw.length) ∧
      (∀ q ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x12, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
        .x31] : List Reg), u₂.getReg q = u₁.getReg q) ∧
      ∀ a, u₂.getMem a = u₁.getMem a := by
    by_cases hlt : rows[j].length < lw.length
    · refine ⟨u₁, Reaches.refl _, b8000b38c_pc_taken h₁ (by
        rw [aL, a256, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega), ?_,
        fun _ _ ↦ rfl, fun _ ↦ rfl⟩
      rw [b8000b38c_x11 h₁, aL, Nat.min_eq_left (by omega)]
    · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000b3a8_spec
        (b8000b38c_pc_not_taken h₁ (by
        rw [aL, a256, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)) (by
        rv_eval [k₁ .x2 (by decide), B.sp]; valid_access hst.valid [hb])
      refine ⟨u₂, hr₂, b8000b3a8_pc h₂, ?_, b8000b3a8_keeps h₂, b8000b3a8_mem_same h₂⟩
      rw [b8000b3a8_x11 h₂, k₁ .x2 (by decide), m₁, a256, Nat.min_eq_right (by omega)]
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000b3ac_spec pc₂ trivial
  have k₃ := b8000b3ac_keeps h₃
  have m₃ := b8000b3ac_mem_same h₃
  have mem₃ (a : Word) : u₃.getMem a = u.getMem a := by rw [m₃, m₂, m₁]
  have reg₃ (q : Reg) (h3 : q ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12,
      .x13, .x14, .x15, .x16, .x17, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29,
      .x30, .x31] : List Reg))
      (h2 : q ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x12, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
        .x31] : List Reg))
      (h1 : q ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x19,
        .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      u₃.getReg q = u.getReg q := by
    rw [k₃ q h3, k₂ q h2, k₁ q h1]
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 1040 :=
    (reg₃ .x2 (by decide) (by decide) (by decide)).trans B.sp
  have x18₃ : u₃.getReg .x18 = BitVec.ofNat 64 n := by
    rw [b8000b3ac_x18 h₃, k₂ .x20 (by decide), k₁ .x20 (by decide), O.x20]
  have x19₃ : u₃.getReg .x19 = Q := by
    rw [b8000b3ac_x19 h₃, k₂ .x25 (by decide), k₁ .x25 (by decide), O.x25]
  have x21₃ := (reg₃ .x21 (by decide) (by decide) (by decide)).trans O.x21
  have x27₃ := (reg₃ .x27 (by decide) (by decide) (by decide)).trans O.x27
  have B₃ : R0B s r Q n u₃ := {
    sp := sp₃
    fr := B.fr.trans (DFrame.of_same mem₃ _) fun _ h ↦ h
    x9 := (reg₃ .x9 (by decide) (by decide) (by decide)).trans B.x9
    x26 := (reg₃ .x26 (by decide) (by decide) (by decide)).trans B.x26 }
  have vals₃ : eListAt u₃ Q j = (rows.take j).map (Model.Pcs.baseDot lw) := by
    rw [← O.vals]; simp only [eListAt, eAt, mem₃]
  by_cases hm0 : min rows[j].length lw.length = 0
  · -- an empty zip: `0`
    obtain ⟨w, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000b34c_spec
      (b8000b3ac_pc_taken h₃ (by rw [x11₂, hm0]; rfl)) trivial
    have k₄ := b8000b34c_keeps h₄
    have m₄ := b8000b34c_mem_same h₄
    refine ⟨w, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl ⟨b8000b34c_pc h₄, {
      base := {
        sp := (k₄ .x2 (by decide)).trans sp₃
        fr := B₃.fr.trans (DFrame.of_same m₄ _) fun _ h ↦ h
        x9 := (k₄ .x9 (by decide)).trans B₃.x9
        x26 := (k₄ .x26 (by decide)).trans B₃.x26 }
      acc := by
        rw [b8000b34c_x24 h₄, b8000b34c_x23 h₄, b8000b34c_x22 h₄, ← accE_full, hm0,
          accE_zero,
          limbs_zero0]
      x18 := (k₄ .x18 (by decide)).trans x18₃
      x19 := (k₄ .x19 (by decide)).trans x19₃
      x21 := (k₄ .x21 (by decide)).trans x21₃
      x27 := (k₄ .x27 (by decide)).trans x27₃
      vals := by rw [← vals₃]; simp only [eListAt, eAt, m₄] }⟩⟩
  -- `base_dot`'s loop
  have hRr : Region (r.getMem (P + BitVec.ofNat 64 (16 * j))) (8 * rows[j].length) :=
    R.region.resolve_left (by omega)
  have hRb := Region.bounds hRr
  have x12₃ : u₃.getReg .x12 = P + BitVec.ofNat 64 (16 * j) :=
    (k₃ .x12 (by decide)).trans ((k₂ .x12 (by decide)).trans x12₁)
  have eRp : u₃.getMem (u₃.getReg .x12) = r.getMem (P + BitVec.ofNat 64 (16 * j)) := by
    rw [x12₃, mem₃, ← aP, a208, O.x21, r0_mul16]
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000b3b8_spec
    (b8000b3ac_pc_not_taken h₃ (by
      rw [x11₂]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat] at this
      exact hm0 (by simp only [show (0 : Word).toNat = 0 from rfl] at this; omega))) (by
      rv_eval [sp₃, x12₃]
      and_intros
      · valid_access hst.valid [hb]
      · exact Region.valid hP (by addr_omega [hPb, hj]) (by addr_omega [hPb, hj])
          (by addr_omega [hPb, hj]))
  have k₄ := b8000b3b8_keeps h₄
  have m₄ := b8000b3b8_mem_same h₄
  have a136₃ : u₃.getMem (u₃.getReg .x2 + 136) = KP := by
    rw [sp₃, mem₃, ← B.sp, a136]
  have I₀ : R0I s r Q n KP lw (r.getMem (P + BitVec.ofNat 64 (16 * j))) rows[j]
      ((rows.take j).map (Model.Pcs.baseDot lw)) j 0 u₄ := {
    base := {
      sp := (k₄ .x2 (by decide)).trans sp₃
      fr := B₃.fr.trans (DFrame.of_same m₄ _) fun _ h ↦ h
      x9 := (k₄ .x9 (by decide)).trans B₃.x9
      x26 := (k₄ .x26 (by decide)).trans B₃.x26 }
    x8 := fun _ ↦ by
      rw [b8000b3b8_x8 h₄, eRp, k₃ .x10 (by decide), k₂ .x10 (by decide), x10₁]
      addr_omega [hRb, hlen, hm0]
    x11 := by rw [b8000b3b8_x11 h₄, a136₃, Nat.mul_zero, add_ofNat_zero]
    x25 := by rw [b8000b3b8_x25 h₄, a136₃, k₃ .x11 (by decide), x11₂, r0_mul24]
    acc := by
      rw [b8000b3b8_x24 h₄, b8000b3b8_x23 h₄, b8000b3b8_x22 h₄, accE_zero, limbs_zero0]
    x18 := (k₄ .x18 (by decide)).trans x18₃
    x19 := (k₄ .x19 (by decide)).trans x19₃
    x21 := (k₄ .x21 (by decide)).trans x21₃
    x27 := (k₄ .x27 (by decide)).trans x27₃
    vals := by rw [← vals₃]; simp only [eListAt, eAt, m₄] }
  obtain ⟨w₀, hr₅, ⟨pc₅, I⟩ | hd⟩ :=
    inner0 hMK hpre K R hj (by omega) (b8000b3b8_pc h₄) I₀
  swap
  · exact ⟨w₀, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr hd⟩
  obtain ⟨w, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000b424_spec pc₅ trivial
  have k₆ := b8000b424_keeps h₆
  have m₆ := b8000b424_mem_same h₆
  refine ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))),
    Or.inl ⟨b8000b424_pc h₆, {
      base := {
        sp := (k₆ .x2 (by decide)).trans I.base.sp
        fr := I.base.fr.trans (DFrame.of_same m₆ _) fun _ h ↦ h
        x9 := (k₆ .x9 (by decide)).trans I.base.x9
        x26 := (k₆ .x26 (by decide)).trans I.base.x26 }
      acc := by
        rw [k₆ .x24 (by decide), k₆ .x23 (by decide), k₆ .x22 (by decide), I.acc, accE_full]
      x18 := (k₆ .x18 (by decide)).trans I.x18
      x19 := (k₆ .x19 (by decide)).trans I.x19
      x21 := (k₆ .x21 (by decide)).trans I.x21
      x27 := (k₆ .x27 (by decide)).trans I.x27
      vals := by rw [← I.vals]; simp only [eListAt, eAt, m₆] }⟩⟩

/-- **The rows' loop**, from row `0` at `0x8000b38c` to `0x8000b42c`. -/
theorem rows0 (hMK : MulKSpec) {s r u : MachineState} {Q : Word} {n : ℕ} {KP P : Word}
    {lw : List E} {rows : List (List K)} (hpre : VsoPre s) (K : R0K s r Q n KP lw)
    (Pp : R0P s r Q n P rows) (hn : 0 < n) (hpc : u.pc = 0x8000b38c)
    (O : R0O s r Q n lw rows 0 u) :
    ∃ v, Reaches Image.code u v ∧
      ((v.pc = 0x8000b42c ∧ R0O s r Q n lw rows n v) ∨ Dead Image.code v) := by
  have hq := K.q2
  have hn60 : n < 2 ^ 60 := by simp only [heapEnd] at hq; omega
  refine Reaches.loop (fun v ↦ ∃ j, j < n ∧ v.pc = 0x8000b38c ∧ R0O s r Q n lw rows j v)
    (fun v ↦ n - (v.getReg .x21).toNat) _ (fun v ⟨j, hj, hpc, O⟩ ↦ ?_) u ⟨0, hn, hpc, O⟩
  have hjr : j < rows.length := Pp.len ▸ hj
  obtain ⟨w, hr, ⟨hpcw, W⟩ | hd⟩ := row0 hMK hpre K Pp hjr hpc O
  swap
  · exact Or.inl ⟨w, hr, Or.inr hd⟩
  obtain ⟨v', hr', O', ⟨hlt, hpc'⟩ | ⟨heq, hpc'⟩⟩ := store0 hpre K hjr Pp.len hpcw W
  · refine Or.inr ⟨v', hr.trans hr', ⟨j + 1, hlt, hpc', O'⟩, ?_⟩
    rw [O.x21, O'.x21, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · exact Or.inl ⟨v', hr.trans hr', Or.inl ⟨hpc', heq ▸ O'⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
