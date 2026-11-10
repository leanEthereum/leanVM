import Rv64Verifier.Proofs.Layout.ContractsKeccak
import Rv64Verifier.Blocks.F12
import Rv64Verifier.Proofs.Runtime.Memcpy

/-!
# `keccak_cell_lanes`, at `0x80004d10`

```rust
fn keccak_cell_lanes(odd: bool) -> [(Option<usize>, Option<usize>); KECCAK_CELLS] {
    core::array::from_fn(|cell| match (odd, cell) {
        (_, 9..) | (true, 1..) => (Some(2 * cell - 1), Some(2 * cell)),
        (true, _) => (None, Some(0)),
        (false, 8) => (Some(16), None),
        (false, _) => (Some(2 * cell), Some(2 * cell + 1)),
    })
}
```

compiled (`Blocks/F12.lean`), with `sp'` the entry's `sp - 448`: `0x80004d10` writes cell 0 at `sp'`
and enters the loop head `0x80004d98` for cell 1 (`a7`), `a2` = `sp' + 32 a7 + 24`, `a4` =
`2 a7 + 1`. `0x80004d4c` (odd, or a cell from 9) and `0x80004dbc` (even) put the cell's two values in
`t1`, `t0`, and `0x80004d54` stores `t1` at `sp' + 432`; `0x80004da8` (even, cell 8) points `t1`, `t3`
one word up instead. `0x80004d64` stores `t0` and `t2` through `t1` and `t3` (sometimes aliasing the
words it reads next, so its generated block is unusable: `storeE` and `copyE` split it), copies the
three words at `sp' + 416` into the cell and loops; `0x80004dc8` `memcpy`s the 416 bytes to `a0`.
-/

namespace Rv64Verifier.Layout.CellLanes
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Blocks.F12
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Runtime.Memcpy (keepE keepE_reg)
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def cfgN : Config := { noAlias := true }

theorem spec_ofN {x : Expect} {e : Word} (i n : Nat)
    (hrun : (symRun cfgN ((Image.code.words.drop i).take n) e n).any (·.meets cfgN x) = true)
    (hpc : e.toNat = Image.code.base.toNat + 4 * i) (h4 : e.toNat % 4 = 0)
    (hr : e.toNat + 4 * n < 2 ^ 64) :
    BlockSpec Image.code e x.steps (fun s ↦ Oblig.all s x.obl) x.Holds :=
  BlockSpec.of_expect hrun (CodeAt.slice Image.code i n e hpc h4 hr) (fun _ h ↦ h) fun _ _ _ h ↦ h

/-- `0x80004d64`, `0x80004d68`: `t2` through `t3`, then `t0` through `t1`. -/
def storeE : Expect where
  steps := 2
  pc := .c 0x80004d6c
  regs := keepE []
  mem := [(⟨some (.reg .x6), 0⟩, .reg .x5), (⟨some (.reg .x28), 0⟩, .reg .x7)]
  writes := [⟨some (.reg .x28), 0⟩, ⟨some (.reg .x6), 0⟩]
  obl := [.valid ⟨some (.reg .x28), 0⟩ 8, .valid ⟨some (.reg .x6), 0⟩ 8,
    .ne ⟨some (.reg .x28), 0⟩ ⟨some (.reg .x6), 0⟩]

/-- `0x80004d6c` to the loop's branch: the three words at `sp + 416` and `a3` into the cell. -/
def copyE : Expect where
  steps := 11
  pc := .ite .eq (.bin .add (.reg .x14) (.c 2)) (.reg .x15) (.c 0x80004dc8) (.c 0x80004d98)
  regs := [(.x5, .ld (.bin .add (.reg .x2) (.c 432))), (.x6, .ld (.bin .add (.reg .x2) (.c 424))),
    (.x7, .ld (.bin .add (.reg .x2) (.c 416))), (.x12, .bin .add (.reg .x12) (.c 32)),
    (.x14, .bin .add (.reg .x14) (.c 2)), (.x17, .bin .add (.reg .x17) (.c 1))] ++
    keepE [.x5, .x6, .x7, .x12, .x14, .x17]
  mem := [(⟨some (.reg .x12), 0⟩, .ld (.bin .add (.reg .x2) (.c 416))),
    (⟨some (.reg .x12), 0xfffffffffffffff8⟩, .ld (.bin .add (.reg .x2) (.c 424))),
    (⟨some (.reg .x12), 0xfffffffffffffff0⟩, .ld (.bin .add (.reg .x2) (.c 432))),
    (⟨some (.reg .x12), 0xffffffffffffffe8⟩, .reg .x13)]
  writes := [⟨some (.reg .x12), 0⟩, ⟨some (.reg .x12), 0xfffffffffffffff8⟩,
    ⟨some (.reg .x12), 0xfffffffffffffff0⟩, ⟨some (.reg .x12), 0xffffffffffffffe8⟩]
  obl := [.valid ⟨some (.reg .x12), 0⟩ 8, .valid ⟨some (.reg .x12), 0xfffffffffffffff8⟩ 8,
    .valid ⟨some (.reg .x12), 0xfffffffffffffff0⟩ 8, .valid ⟨some (.reg .x12), 0xffffffffffffffe8⟩ 8,
    .valid ⟨some (.reg .x2), 416⟩ 8, .valid ⟨some (.reg .x2), 424⟩ 8, .valid ⟨some (.reg .x2), 432⟩ 8]

theorem store_spec : BlockSpec Image.code 0x80004d64 2 (fun s ↦ Oblig.all s storeE.obl) storeE.Holds :=
  spec_ofN 4953 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem copy_spec : BlockSpec Image.code 0x80004d6c 11 (fun s ↦ Oblig.all s copyE.obl) copyE.Holds :=
  spec_ofN 4955 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The lanes of cell `c`, for `odd` as `a1` holds it. -/
abbrev lanes (s : MachineState) (c : Nat) : Option ℕ × Option ℕ :=
  keccakCellLanesAt (s.getReg .x11 = 1) c

/-- An `Option<usize>` whose tag and value are at `ta` and `va`. -/
def Opt2 (s : MachineState) (ta va : Word) : Option ℕ → Prop
  | none => s.getMem ta = 0
  | some v => s.getMem ta = 1 ∧ s.getMem va = BitVec.ofNat 64 v

/-- The registers the loop keeps. -/
def kept : List Reg := [.x1, .x8, .x9, .x10, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The loop's state before cell `c`: cells `0..c` written at `sp'`. -/
structure Base (s t : MachineState) (c : Nat) : Prop where
  lo : 1 ≤ c
  hi : c ≤ 13
  x2 : t.getReg .x2 = s.getReg .x2 - 448
  x11 : t.getReg .x11 = s.getReg .x11 ^^^ 0xffffffffffffffff
  x12 : t.getReg .x12 = s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c + 24)
  x13 : t.getReg .x13 = 1
  x14 : t.getReg .x14 = BitVec.ofNat 64 (2 * c + 1)
  x15 : t.getReg .x15 = 27
  x16 : t.getReg .x16 = 17
  x17 : t.getReg .x17 = BitVec.ofNat 64 c
  regs : ∀ r ∈ kept, t.getReg r = s.getReg r
  ra : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  mem : MemFrame s t (s.getReg .x2 - 448) 448
  cells : ∀ j < c, OptAt t (s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * j)) (lanes s j).1 ∧
    OptAt t (s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * j + 16)) (lanes s j).2

theorem facts {s : MachineState} (hpre : CellLanesPre s) :
    0x20 + 464 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (stackLo s cellLanesStack).toNat = (s.getReg .x2).toNat - 464 :=
  hpre.stack.bounds (by decide) (by decide)

theorem OptAt.congr {t v : MachineState} {a : Word} {o : Option ℕ} (h : OptAt t a o)
    (h0 : v.getMem a = t.getMem a) (h8 : v.getMem (a + 8) = t.getMem (a + 8)) : OptAt v a o := by
  cases o with
  | none => exact h0.trans h
  | some x => exact ⟨h0.trans h.1, h8.trans h.2⟩

/-- A step that writes only the temporaries `[sp' + 416, sp' + 440)`. -/
theorem Base.step {s t v : MachineState} {c : Nat} (hpre : CellLanesPre s) (h : Base s t c)
    (hm : ∀ a, ¬ Within a (s.getReg .x2 - 32) 24 → v.getMem a = t.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x11, .x12, .x13, .x14, .x15, .x16, .x17] ++ kept, v.getReg r = t.getReg r) :
    Base s v c := by
  obtain ⟨hsb, -⟩ := facts hpre
  have hc := h.hi
  exact {
    lo := h.lo
    hi := h.hi
    x2 := (hr _ (by decide)).trans h.x2
    x11 := (hr _ (by decide)).trans h.x11
    x12 := (hr _ (by decide)).trans h.x12
    x13 := (hr _ (by decide)).trans h.x13
    x14 := (hr _ (by decide)).trans h.x14
    x15 := (hr _ (by decide)).trans h.x15
    x16 := (hr _ (by decide)).trans h.x16
    x17 := (hr _ (by decide)).trans h.x17
    regs := fun r hk ↦ (hr r (List.mem_append_right _ hk)).trans (h.regs r hk)
    ra := (hm _ (by addr_omega [hsb])).trans h.ra
    mem := fun a ha ↦ (hm a (by addr_omega [ha, hsb])).trans (h.mem a ha)
    cells := fun j hj ↦ by
      obtain ⟨h1, h2⟩ := h.cells j hj
      exact ⟨OptAt.congr h1 (hm _ (by addr_omega [hsb, hj, hc])) (hm _ (by addr_omega [hsb, hj, hc])),
        OptAt.congr h2 (hm _ (by addr_omega [hsb, hj, hc])) (hm _ (by addr_omega [hsb, hj, hc]))⟩ }

/-- `0x80004d6c`: cell `c` from the temporaries, then the loop head or the `memcpy`. -/
theorem copy {s u : MachineState} {c : Nat} (hpre : CellLanesPre s) (h : Base s u c) (hc : c ≤ 12)
    (hpc : u.pc = 0x80004d6c) {v₁ : Nat} (hl : (lanes s c).1 = some v₁)
    (hv₁ : u.getMem (s.getReg .x2 - 16) = BitVec.ofNat 64 v₁)
    (hh : Opt2 u (s.getReg .x2 - 24) (s.getReg .x2 - 32) (lanes s c).2) :
    ∃ v, Reaches Image.code u v ∧ Base s v (c + 1) ∧
      v.pc = if c = 12 then 0x80004dc8 else 0x80004d98 := by
  obtain ⟨hsb, -⟩ := facts hpre
  have x2 := h.x2
  have x12 := h.x12
  obtain ⟨v, hr, hv⟩ := BlockSpec.reaches copy_spec hpc (by
    rv_eval [x2, x12]
    and_intros <;> valid_access hpre.stack.valid [hsb, hc])
  have k := hv.keeps (rs := [.x2, .x11, .x13, .x15, .x16] ++ kept) rfl
  have y12 := hv.reg_eq (v := u.getReg .x12 + 32) .x12 rfl (by rv_eval [])
  have y14 := hv.reg_eq (v := u.getReg .x14 + 2) .x14 rfl (by rv_eval [])
  have y17 := hv.reg_eq (v := u.getReg .x17 + 1) .x17 rfl (by rv_eval [])
  have m0 := hv.mem_eq 0 (by decide) (a := u.getReg .x12) (v := u.getMem (u.getReg .x2 + 416))
    (by rv_eval []) (by rv_eval [])
  have m1 := hv.mem_eq 1 (by decide) (a := u.getReg .x12 - 8) (v := u.getMem (u.getReg .x2 + 424))
    (by rv_eval []) (by rv_eval [])
  have m2 := hv.mem_eq 2 (by decide) (a := u.getReg .x12 - 16) (v := u.getMem (u.getReg .x2 + 432))
    (by rv_eval []) (by rv_eval [])
  have m3 := hv.mem_eq 3 (by decide) (a := u.getReg .x12 - 24) (v := u.getReg .x13)
    (by rv_eval []) (by rv_eval [])
  have hpcv := hv.pc_eq (v := if u.getReg .x14 + 2 == u.getReg .x15 then 0x80004dc8 else 0x80004d98)
    rfl
  have hfr (a : Word) (ha : ¬ Within a (s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c)) 32) :
      v.getMem a = u.getMem a := hv.2.2.2 a fun w hw ↦ by
    simp only [copyE, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> rv_eval [x12] <;> addr_omega [ha, hsb, hc]
  rw [x12, x2] at m0 m1 m2
  rw [x12] at m3
  rw [h.x13] at m3
  have e0 : s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c + 24) =
      s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c + 16) + 8 := by addr_omega [hsb, hc]
  have e1 : s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c + 24) - 8 =
      s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c + 16) := by addr_omega [hsb, hc]
  have e2 : s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c + 24) - 16 =
      s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c) + 8 := by addr_omega [hsb, hc]
  have e3 : s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c + 24) - 24 =
      s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * c) := by addr_omega [hsb, hc]
  have f416 : s.getReg .x2 - 448 + 416 = s.getReg .x2 - 32 := by addr_omega [hsb]
  have f424 : s.getReg .x2 - 448 + 424 = s.getReg .x2 - 24 := by addr_omega [hsb]
  have f432 : s.getReg .x2 - 448 + 432 = s.getReg .x2 - 16 := by addr_omega [hsb]
  rw [e0, f416] at m0
  rw [e1, f424] at m1
  rw [e2, f432] at m2
  rw [e3] at m3
  refine ⟨v, hr, {
    lo := by omega
    hi := by omega
    x2 := (k _ (by decide)).trans x2
    x11 := (k _ (by decide)).trans h.x11
    x12 := by rw [y12, x12]; addr_omega [hsb, hc]
    x13 := (k _ (by decide)).trans h.x13
    x14 := by rw [y14, h.x14]; addr_omega [hc]
    x15 := (k _ (by decide)).trans h.x15
    x16 := (k _ (by decide)).trans h.x16
    x17 := by rw [y17, h.x17]; addr_omega [hc]
    regs := fun r hk ↦ (k r (List.mem_append_right _ hk)).trans (h.regs r hk)
    ra := (hfr _ (by addr_omega [hsb, hc])).trans h.ra
    mem := fun a ha ↦ (hfr a (by addr_omega [ha, hsb, hc])).trans (h.mem a ha)
    cells := fun j hj ↦ ?_ }, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · obtain ⟨h1, h2⟩ := h.cells j hj
      exact ⟨OptAt.congr h1 (hfr _ (by addr_omega [hsb, hj, hc])) (hfr _ (by addr_omega [hsb, hj, hc])),
        OptAt.congr h2 (hfr _ (by addr_omega [hsb, hj, hc])) (hfr _ (by addr_omega [hsb, hj, hc]))⟩
    · refine ⟨?_, ?_⟩
      · rw [hl]; exact ⟨m3, m2.trans hv₁⟩
      · revert hh
        cases (lanes s j).2 with
        | none => intro hh; exact m1.trans hh
        | some x => intro hh; exact ⟨m1.trans hh.1, m0.trans hh.2⟩
  · rw [hpcv, h.x14, h.x15]
    by_cases h12 : c = 12
    · subst h12; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h12)]
      have : (BitVec.ofNat 64 (2 * c + 1) + 2 == (27 : Word)) = false := by
        rw [beq_eq_false_iff_ne]; addr_omega [h12, hc]
      rw [this]; rfl

/-- `storeE`: `t2` through `t3` and `t0` through `t1`, both temporaries. -/
theorem store {s w : MachineState} {c : Nat} (hpre : CellLanesPre s) (h : Base s w c)
    (hpc : w.pc = 0x80004d64)
    (hx : (w.getReg .x6 = s.getReg .x2 - 32 ∧ w.getReg .x28 = s.getReg .x2 - 24) ∨
      (w.getReg .x6 = s.getReg .x2 - 24 ∧ w.getReg .x28 = s.getReg .x2 - 16)) :
    ∃ u, Reaches Image.code w u ∧ Base s u c ∧ u.pc = 0x80004d6c ∧
      u.getMem (w.getReg .x6) = w.getReg .x5 ∧ u.getMem (w.getReg .x28) = w.getReg .x7 ∧
      ∀ a, a ≠ w.getReg .x6 → a ≠ w.getReg .x28 → u.getMem a = w.getMem a := by
  obtain ⟨hsb, -⟩ := facts hpre
  obtain ⟨u, hr, hu⟩ := BlockSpec.reaches store_spec hpc (by
    rv_eval []
    rcases hx with ⟨h6, h28⟩ | ⟨h6, h28⟩ <;> rw [h6, h28] <;> and_intros <;>
      first | valid_access hpre.stack.valid [hsb] | addr_omega [hsb])
  have k := hu.keeps (rs := [.x2, .x11, .x12, .x13, .x14, .x15, .x16, .x17] ++ kept) rfl
  have m0 := hu.mem_eq 0 (by decide) (a := w.getReg .x6) (v := w.getReg .x5) (by rv_eval [])
    (by rv_eval [])
  have m1 := hu.mem_eq 1 (by decide) (a := w.getReg .x28) (v := w.getReg .x7) (by rv_eval [])
    (by rv_eval [])
  have hfr (a : Word) (h6 : a ≠ w.getReg .x6) (h28 : a ≠ w.getReg .x28) : u.getMem a = w.getMem a :=
    hu.2.2.2 a fun k hk ↦ by
      simp only [storeE, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [] <;> assumption
  refine ⟨u, hr, h.step hpre (fun a ha ↦ hfr a ?_ ?_) k, hu.pc_eq rfl, m0, m1, hfr⟩ <;>
    rcases hx with ⟨h6, h28⟩ | ⟨h6, h28⟩ <;> simp only [h6, h28] <;> intro he <;> subst he <;>
      exact ha (by addr_omega [hsb])

/-- `0x80004d54` and `storeE`: the cell's two values, from `t1` and `t0`, in the temporaries. -/
theorem viaD54 {s w : MachineState} {c : Nat} (hpre : CellLanesPre s) (h : Base s w c)
    (hpc : w.pc = 0x80004d54) :
    ∃ u, Reaches Image.code w u ∧ Base s u c ∧ u.pc = 0x80004d6c ∧
      u.getMem (s.getReg .x2 - 16) = w.getReg .x6 ∧ u.getMem (s.getReg .x2 - 24) = 1 ∧
      u.getMem (s.getReg .x2 - 32) = w.getReg .x5 := by
  obtain ⟨hsb, -⟩ := facts hpre
  have x2 := h.x2
  obtain ⟨w₁, hr₁, h₁⟩ := BlockSpec.reaches b80004d54_spec hpc (by
    rv_eval [x2]; valid_access hpre.stack.valid [hsb])
  have k₁ := b80004d54_keeps h₁
  have hm₁ := b80004d54_frame h₁ (by rw [x2]; addr_omega [hsb])
  have m₁ := b80004d54_m_x2_432 h₁
  rw [x2, show s.getReg .x2 - 448 + 432 = s.getReg .x2 - 16 by addr_omega [hsb]] at hm₁ m₁
  have B₁ := h.step hpre (fun a ha ↦ hm₁ a (by addr_omega [ha, hsb])) fun r hr ↦
    k₁ r (by revert hr; revert r; decide)
  have y6 : w₁.getReg .x6 = s.getReg .x2 - 32 := by
    rw [b80004d54_x6 h₁, x2]; addr_omega [hsb]
  have y28 : w₁.getReg .x28 = s.getReg .x2 - 24 := by
    rw [b80004d54_x28 h₁, x2]; addr_omega [hsb]
  obtain ⟨u, hr, B, hpc', m6, m28, hfr⟩ := store hpre B₁ (b80004d54_pc h₁) (Or.inl ⟨y6, y28⟩)
  refine ⟨u, hr₁.trans hr, B, hpc', ?_, ?_, ?_⟩
  · rw [hfr _ (by rw [y6]; addr_omega [hsb]) (by rw [y28]; addr_omega [hsb]), m₁]
  · rw [← y28, m28, b80004d54_x7 h₁]
  · rw [← y6, m6, k₁ .x5 (by decide)]

theorem branch {o : Word} (ho : o = 0 ∨ o = 1) {c : Nat} (hc : c ≤ 12) :
    (((o ^^^ 0xffffffffffffffff) &&& (if BitVec.ult (BitVec.ofNat 64 c) 9 then 1 else 0)) == 0) =
      decide (o = 1 ∨ 9 ≤ c) := by
  rcases ho with rfl | rfl <;> interval_cases c <;> decide

/-- One iteration: cell `c` written, then the loop head or the `memcpy`. -/
theorem step {s t : MachineState} {c : Nat} (hpre : CellLanesPre s) (h : Base s t c) (hc : c ≤ 12)
    (hpc : t.pc = 0x80004d98) :
    ∃ v, Reaches Image.code t v ∧ Base s v (c + 1) ∧
      v.pc = if c = 12 then 0x80004dc8 else 0x80004d98 := by
  obtain ⟨hsb, -⟩ := facts hpre
  have hc1 := h.lo
  obtain ⟨t₁, hr₁, h₁⟩ := BlockSpec.reaches b80004d98_spec hpc trivial
  have k₁ := b80004d98_keeps h₁
  have B₁ := h.step hpre (fun a _ ↦ b80004d98_mem_same h₁ a) fun r hr ↦ k₁ r (by revert hr; revert r; decide)
  have hp₁ := h₁.pc_eq (v := if (t.getReg .x11 &&& (if BitVec.ult (t.getReg .x17) 9 then 1 else 0))
    == 0 then 0x80004d4c else 0x80004da4) rfl
  rw [h.x11, h.x17, branch hpre.odd hc] at hp₁
  have hl : lanes s c = if 9 ≤ c ∨ (decide (s.getReg .x11 = 1) = true ∧ 1 ≤ c) then
      (some (2 * c - 1), some (2 * c))
    else if decide (s.getReg .x11 = 1) = true then (none, some 0)
    else if c = 8 then (some 16, none) else (some (2 * c), some (2 * c + 1)) := rfl
  by_cases hA : s.getReg .x11 = 1 ∨ 9 ≤ c
  · -- `(Some(2c - 1), Some(2c))`
    rw [decide_eq_true hA] at hp₁
    obtain ⟨t₂, hr₂, h₂⟩ := BlockSpec.reaches b80004d4c_spec hp₁ trivial
    have k₂ := b80004d4c_keeps h₂
    have B₂ := B₁.step hpre (fun a _ ↦ b80004d4c_mem_same h₂ a) fun r hr ↦ k₂ r (by revert hr; revert r; decide)
    obtain ⟨u, hr, B, hpc', m16, m24, m32⟩ := viaD54 hpre B₂ (b80004d4c_pc h₂)
    have hl' : lanes s c = (some (2 * c - 1), some (2 * c)) := by
      rw [hl]; rcases hA with hA | hA
      · simp [hA, hc1]
      · simp [hA]
    have x17 : t₁.getReg .x17 = BitVec.ofNat 64 c := B₁.x17
    rw [b80004d4c_x6 h₂, x17] at m16
    rw [b80004d4c_x5 h₂, x17] at m32
    obtain ⟨v, hrv, Bv, hpcv⟩ := copy hpre B hc hpc' (by rw [hl']) (m16.trans (by addr_omega [hc, hc1]))
      (by rw [hl']; exact ⟨m24, m32.trans (by addr_omega [hc])⟩)
    exact ⟨v, hr₁.trans (hr₂.trans (hr.trans hrv)), Bv, hpcv⟩
  · rw [decide_eq_false hA] at hp₁
    have hodd : s.getReg .x11 = 0 := by rcases hpre.odd with h' | h' <;> simp_all
    have h9 : c < 9 := by omega
    obtain ⟨t₂, hr₂, h₂⟩ := BlockSpec.reaches b80004da4_spec hp₁ trivial
    have k₂ := b80004da4_keeps h₂
    have B₂ := B₁.step hpre (fun a _ ↦ b80004da4_mem_same h₂ a) fun r hr ↦ k₂ r (by revert hr; revert r; decide)
    have x14 : t₁.getReg .x14 = BitVec.ofNat 64 (2 * c + 1) := B₁.x14
    have x16 : t₁.getReg .x16 = 17 := B₁.x16
    by_cases h8 : c = 8
    · -- `(Some(16), None)`
      subst h8
      obtain ⟨t₃, hr₃, h₃⟩ := BlockSpec.reaches b80004da8_spec
        (b80004da4_pc_not_taken h₂ (by rw [x14, x16]; rfl)) trivial
      have k₃ := b80004da8_keeps h₃
      have B₃ := B₂.step hpre (fun a _ ↦ b80004da8_mem_same h₃ a) fun r hr ↦ k₃ r (by revert hr; revert r; decide)
      have x2 : t₂.getReg .x2 = s.getReg .x2 - 448 := B₂.x2
      have y6 : t₃.getReg .x6 = s.getReg .x2 - 24 := by
        rw [b80004da8_x6 h₃, x2]; addr_omega [hsb]
      have y28 : t₃.getReg .x28 = s.getReg .x2 - 16 := by
        rw [b80004da8_x28 h₃, x2]; addr_omega [hsb]
      obtain ⟨u, hr, B, hpc', m6, m28, -⟩ := store hpre B₃ (b80004da8_pc h₃) (Or.inr ⟨y6, y28⟩)
      have hl' : lanes s 8 = (some 16, none) := by rw [hl]; simp [hodd]
      rw [y6, b80004da8_x5 h₃] at m6
      rw [y28, b80004da8_x7 h₃] at m28
      obtain ⟨v, hrv, Bv, hpcv⟩ := copy hpre B hc hpc' (by rw [hl']) (m28.trans rfl)
        (by rw [hl']; exact m6)
      exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans (hr.trans hrv))), Bv, hpcv⟩
    · -- `(Some(2c), Some(2c + 1))`
      obtain ⟨t₃, hr₃, h₃⟩ := BlockSpec.reaches b80004dbc_spec
        (b80004da4_pc_taken h₂ (by rw [x14, x16]; addr_omega [h8, h9])) trivial
      have k₃ := b80004dbc_keeps h₃
      have B₃ := B₂.step hpre (fun a _ ↦ b80004dbc_mem_same h₃ a) fun r hr ↦ k₃ r (by revert hr; revert r; decide)
      obtain ⟨u, hr, B, hpc', m16, m24, m32⟩ := viaD54 hpre B₃ (b80004dbc_pc h₃)
      have hl' : lanes s c = (some (2 * c), some (2 * c + 1)) := by rw [hl]; simp [hodd, h8, h9]
      have x14' : t₂.getReg .x14 = BitVec.ofNat 64 (2 * c + 1) := B₂.x14
      rw [b80004dbc_x6 h₃, x14'] at m16
      rw [b80004dbc_x5 h₃, x14'] at m32
      obtain ⟨v, hrv, Bv, hpcv⟩ := copy hpre B hc hpc' (by rw [hl']) (m16.trans (by addr_omega [hc]))
        (by rw [hl']; exact ⟨m24, m32⟩)
      exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans (hr.trans hrv))), Bv, hpcv⟩

/-- The prologue: cell 0, and the loop head for cell 1. -/
theorem setup {s : MachineState} (hpre : CellLanesPre s) (hpc : s.pc = 0x80004d10) :
    ∃ t, Reaches Image.code s t ∧ Base s t 1 ∧ t.pc = 0x80004d98 := by
  obtain ⟨hsb, -⟩ := facts hpre
  obtain ⟨t, hr, h⟩ := BlockSpec.reaches b80004d10_spec hpc (by
    rv_eval []; and_intros <;> valid_access hpre.stack.valid [hsb])
  have k := b80004d10_keeps h
  have m24 := b80004d10_m_x2_n424 h
  have m16 := b80004d10_m_x2_n432 h
  have m8 := b80004d10_m_x2_n440 h
  have m0 := b80004d10_m_x2_n448 h
  refine ⟨t, hr, {
    lo := le_refl _
    hi := by decide
    x2 := b80004d10_x2 h
    x11 := b80004d10_x11 h
    x12 := by rw [b80004d10_x12 h]; addr_omega [hsb]
    x13 := b80004d10_x13 h
    x14 := b80004d10_x14 h
    x15 := b80004d10_x15 h
    x16 := b80004d10_x16 h
    x17 := b80004d10_x17 h
    regs := fun r hr ↦ k r (by revert hr; revert r; decide)
    ra := b80004d10_m_x2_n8 h
    mem := b80004d10_frame h (by addr_omega [hsb])
    cells := fun j hj ↦ ?_ }, b80004d10_pc h⟩
  obtain rfl : j = 0 := by omega
  have e0 : s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * 0) = s.getReg .x2 - 448 := by
    addr_omega [hsb]
  have e8 : s.getReg .x2 - 448 + 8 = s.getReg .x2 - 440 := by addr_omega [hsb]
  have e16 : s.getReg .x2 - 448 + BitVec.ofNat 64 (32 * 0 + 16) = s.getReg .x2 - 432 := by
    addr_omega [hsb]
  have e24 : s.getReg .x2 - 432 + 8 = s.getReg .x2 - 424 := by addr_omega [hsb]
  rw [e0, e16]
  rcases hpre.odd with ho | ho
  · have hl : lanes s 0 = (some 0, some 1) := by simp [lanes, keccakCellLanesAt, ho]
    rw [hl]
    exact ⟨⟨by rw [m0, ho]; rfl, by rw [e8, m8]; rfl⟩, ⟨m16, by rw [e24, m24, ho]; rfl⟩⟩
  · have hl : lanes s 0 = (none, some 0) := by simp [lanes, keccakCellLanesAt, ho]
    rw [hl]
    exact ⟨show t.getMem _ = 0 by rw [m0, ho]; rfl, ⟨m16, by rw [e24, m24, ho]; rfl⟩⟩

theorem OptAt.move {t v : MachineState} {a b : Word} {o : Option ℕ} (h : OptAt t b o)
    (h0 : v.getMem a = t.getMem b) (h8 : v.getMem (a + 8) = t.getMem (b + 8)) : OptAt v a o := by
  cases o with
  | none => exact h0.trans h
  | some x => exact ⟨h0.trans h.1, h8.trans h.2⟩

/-- The stack lies in the upper window: its second doubleword is valid and above the heap. -/
theorem stack_high {s : MachineState} (hpre : CellLanesPre s) :
    0xa0000000 ≤ (stackLo s cellLanesStack).toNat := by
  have hsb := facts hpre
  have hab := hpre.stack.above
  have hv := hpre.stack.valid 1 (by simp only [cellLanesStack, memcpyStack]; decide)
  have h := (Sym.validAccess_eight _).mp (validAccess_of_dword hv)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h
  simp only [heapEnd] at hab
  omega

/-- The `memcpy` of the 13 cells to `a0`, and the return. -/
theorem finish (hM : MemcpySpec 0x800126e4) {s t : MachineState} (hpre : CellLanesPre s)
    (h : Base s t 13) (hpc : t.pc = 0x80004dc8) :
    ∃ w, Reaches Image.code t w ∧
      ((w.pc = returnAddress s ∧ Preserves s w ∧ CellLanesPost s w) ∨ Dead Image.code w) := by
  have hsb := facts hpre
  have hlo := hsb.2.2.2
  have hos := hpre.outStack
  have hout := hpre.out
  have h8o := hpre.outAligned
  have hmp := stack_high hpre
  simp only [cellLanesStack, memcpyStack] at hos hmp hlo
  obtain ⟨u, hr₁, h₁⟩ := BlockSpec.reaches b80004dc8_spec hpc trivial
  have k₁ := b80004dc8_keeps h₁
  have x2₁ : u.getReg .x2 = s.getReg .x2 - 448 := (k₁ .x2 (by decide)).trans h.x2
  have x10₁ : u.getReg .x10 = s.getReg .x10 := (k₁ .x10 (by decide)).trans (h.regs .x10 (by decide))
  have x11₁ : u.getReg .x11 = s.getReg .x2 - 448 := (b80004dc8_x11 h₁).trans h.x2
  have x12₁ := b80004dc8_x12 h₁
  have hsl : stackLo u memcpyStack = s.getReg .x2 - 464 := by
    simp only [stackLo, x2₁, memcpyStack]; rv_eval []
  have hmc : MemcpyPre u := {
    dst := by rw [x10₁, x12₁]; exact hout
    src := by rw [x11₁, x12₁]; addr_omega [hsb, hmp, hlo]
    apart := by rw [x10₁, x11₁, x12₁]; addr_omega [hsb, hos, hlo]
    stack := (hpre.stack.inner (k := 448) x2₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [x10₁, x12₁, hsl]; addr_omega [hsb, hos, hlo]
    srcStack := by rw [x11₁, x12₁, hsl]; addr_omega [hsb] }
  obtain ⟨m, hr₂, ⟨hpc₂, hpres₂, hmp₂⟩ | hdead⟩ := hM.call hr₁ (b80004dc8_pc h₁) hmc
  swap
  · exact ⟨m, hr₂, Or.inr hdead⟩
  have hmf := hmp₂.frame.dframe
  have hb := hmp₂.bytes
  rw [x10₁, x11₁, x12₁] at hb
  rw [x10₁, x12₁, hsl] at hmf
  have x2₂ : m.getReg .x2 = s.getReg .x2 - 448 := (hpres₂ .x2 (by decide)).trans x2₁
  obtain ⟨w, hr₃, h₃⟩ := BlockSpec.reaches b80004dd8_spec
    (by rw [hpc₂, returnAddress_eq, b80004dc8_x1 h₁]; decide) (by
      rv_eval [x2₂]; valid_access hpre.stack.valid [hsb])
  have k₃ := b80004dd8_keeps h₃
  have hra : m.getMem (s.getReg .x2 - 448 + 440) = s.getReg .x1 := by
    rw [hmf.getMem_of (fun x hx hw ↦ by rcases hw with hw | hw <;> addr_omega [hx, hw, hsb, hos, hlo])
      (by addr_omega [hsb]), b80004dc8_mem_same h₁, show s.getReg .x2 - 448 + 440 = s.getReg .x2 - 8
        by addr_omega [hsb], h.ra]
  have pc₃ := b80004dd8_pc h₃
  rw [x2₂, hra] at pc₃
  have x2₃ : w.getReg .x2 = s.getReg .x2 := by rw [b80004dd8_x2 h₃, x2₂]; addr_omega [hsb]
  have regs (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : w.getReg r = s.getReg r := by
    rw [k₃ r (by revert hr; revert r; decide), hpres₂ r (by revert hr; revert r; decide),
      k₁ r (by revert hr; revert r; decide), h.regs r (by revert hr; revert r; decide)]
  have h8b : (s.getReg .x2 - 448).toNat % 8 = 0 := by addr_omega [hsb]
  have g (k : Nat) (hk : k % 8 = 0) (hkN : k + 8 ≤ 416) :
      w.getMem (s.getReg .x10 + BitVec.ofNat 64 k) =
        t.getMem (s.getReg .x2 - 448 + BitVec.ofNat 64 k) := by
    rw [b80004dd8_mem_same h₃, getMem_eq_of_bytesAt hb h8o h8b hk hkN, b80004dc8_mem_same h₁]
  have opt (k : Nat) (hk : k % 8 = 0) (hkN : k + 16 ≤ 416) {o : Option ℕ}
      (ho : OptAt t (s.getReg .x2 - 448 + BitVec.ofNat 64 k) o) :
      OptAt w (s.getReg .x10 + BitVec.ofNat 64 k) o := by
    refine OptAt.move ho (g k hk (by omega)) ?_
    rw [show s.getReg .x10 + BitVec.ofNat 64 k + 8 = s.getReg .x10 + BitVec.ofNat 64 (k + 8) by
        addr_omega [hout, hkN],
      show s.getReg .x2 - 448 + BitVec.ofNat 64 k + 8 = s.getReg .x2 - 448 + BitVec.ofNat 64 (k + 8) by
        addr_omega [hsb, hkN]]
    exact g (k + 8) (by omega) (by omega)
  refine ⟨w, hr₂.trans hr₃, Or.inl ⟨pc₃.trans (returnAddress_eq s).symm,
    preserves_of x2₃ (regs _ (by decide)) (regs _ (by decide)) (regs _ (by decide))
      (regs _ (by decide)) fun r hr ↦ regs r (by revert hr; revert r; decide), ?_, ?_⟩⟩
  · intro i hi
    obtain ⟨c1, c2⟩ := h.cells i (by simp only [keccakCellsRust] at hi; omega)
    simp only [keccakCellsRust] at hi
    exact ⟨opt _ (by omega) (by omega) c1, opt _ (by omega) (by omega) c2⟩
  · have F := ((h.mem.dframe.union (DFrame.of_same (b80004dc8_mem_same h₁) fun _ ↦ False)).union
      hmf).union (DFrame.of_same (b80004dd8_mem_same h₃) fun _ ↦ False)
    refine F.mono fun a ha ↦ ?_
    rcases ha with ((ha | ha) | ha | ha) | ha
    · exact Or.inr (by simp only [cellLanesStack, memcpyStack]; addr_omega [ha, hsb, hlo])
    · exact ha.elim
    · exact Or.inl (by simpa using ha)
    · exact Or.inr (by simp only [cellLanesStack, memcpyStack]; addr_omega [ha, hsb, hlo])
    · exact ha.elim

/-- **`keccak_cell_lanes` meets its contract**, given `memcpy`'s. -/
theorem cell_lanes_spec (hM : MemcpySpec 0x800126e4) : CellLanesSpec := by
  intro s hpc hpre
  obtain ⟨t, hst, B, hpct⟩ := setup hpre hpc
  obtain ⟨u, hu, hBu, hpu⟩ := Reaches.loop (code := Image.code)
    (fun t ↦ ∃ c, Base s t c ∧ c ≤ 12 ∧ t.pc = 0x80004d98)
    (fun t ↦ 13 - (t.getReg .x17).toNat) (fun t ↦ Base s t 13 ∧ t.pc = 0x80004dc8)
    (fun t ⟨c, hB, hc, hp⟩ ↦ by
      obtain ⟨v, hr, hBv, hpv⟩ := step hpre hB hc hp
      by_cases h12 : c = 12
      · subst h12; exact Or.inl ⟨v, hr, hBv, hpv⟩
      · refine Or.inr ⟨v, hr, ⟨c + 1, hBv, by omega,
          by rw [hpv, ite_eq_right_of_eq_false _ _ (eq_false h12)]⟩, ?_⟩
        rw [hBv.x17, hB.x17, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt (by omega : c + 1 < 2 ^ 64)]
        omega)
    t ⟨1, B, by decide, hpct⟩
  obtain ⟨w, hw, hres⟩ := finish hM hpre hBu hpu
  exact ⟨w, hst.trans (hu.trans hw), hres⟩

end Rv64Verifier.Layout.CellLanes
