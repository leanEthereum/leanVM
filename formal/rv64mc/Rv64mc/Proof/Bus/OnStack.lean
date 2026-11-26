/-
  Rv64mc.Proof.Bus.OnStack

  `ColumnClaim::on_stack` keeps its contract (`Spec.Bus.OnStack.spec`) from `stack_point`'s and the panic's. `rv_auto`
  stops after the prologue (instruction 8) and after the bounds check (14), where the heap words the code reads
  (the claim's, the layout's, the placement's) are put apart from the three saved slots as facts `rv_sym` reads
  through (`slots_ne`); the rest is by hand: `None` at `sret`, or `Eq`'s tag, the fresh point (kept through the
  three stores into `sret`, `hdr_apart`, `fresh_apart`) and the value (kept by `stack_point`, `callee_keep`).
-/

import Rv64mc.Spec.Bus.OnStack
import Rv64mc.Spec.Multilinear.StackPoint
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Proof.Layout.Out
import Rv64mc.Proof.Layout.Committed
import Rv64mc.Proof.Multilinear.Heap
import Rv64mc.Gen.Tmpl.Verifier.Bus.ColumnClaim.OnStack
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Bus.OnStack

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Bus Rv64mc.Spec.Bus.OnStack Rv64mc.Spec.Layout
open Rv64mc.Gen.Verifier.Bus.ColumnClaim.OnStack (Link tmpl)

/-- **A word below the heap's end or at or above `top` is not one of the three slots below `top`.** -/
theorem slots_ne {env : Env} {top b : Word} (hstk : env.stackLimit.toNat + 32 ≤ top.toNat)
    (hb : b.toNat < env.heapEnd.toNat ∨ top.toNat ≤ b.toNat) :
    b ≠ top + 0xfffffffffffffff8#64 ∧ b ≠ top + 0xfffffffffffffff0#64 ∧ b ≠ top + 0xffffffffffffffe8#64 := by
  have := env.layout
  have e8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := by
    rw [BitVec.toNat_add, show (0xfffffffffffffff8#64).toNat = 18446744073709551608 from rfl]; omega
  have e16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xfffffffffffffff0#64).toNat = 18446744073709551600 from rfl]; omega
  have e24 : (top + 0xffffffffffffffe8#64).toNat = top.toNat - 24 := by
    rw [BitVec.toNat_add, show (0xffffffffffffffe8#64).toNat = 18446744073709551592 from rfl]; omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> subst h <;> omega

/-- A word of an owned object is below the heap's end or at or above `top`. -/
theorem owned_at {env : Env} {m : MachineState} {top a : Word} {n k : Nat} (h : env.Owned m top a n)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hk : k < n) :
    (a + BitVec.ofNat 64 k).toNat < env.heapEnd.toNat ∨ top.toNat ≤ (a + BitVec.ofNat 64 k).toNat := by
  have := h.2
  rw [toNat_add_ofNat (by omega)]
  rcases h.1 with h1 | h1 <;> omega

/-- The stores of the prologue, `ra`, `s0` and `s1` below `top`. -/
abbrev saved (m : MachineState) (top a b c : Word) : MachineState :=
  ((m.setMem (top + 0xfffffffffffffff8#64) a).setMem (top + 0xfffffffffffffff0#64) b).setMem
    (top + 0xffffffffffffffe8#64) c

theorem top_sub {top : Word} {k : Nat} (c : Word) (hc : c.toNat = 2 ^ 64 - k) (hk : k ≤ top.toNat) :
    (top + c).toNat = top.toNat - k := by
  rw [BitVec.toNat_add, hc]; omega

/-- What the prologue's stores keep: the static data, `NEXT`, and a frame without `out`. -/
theorem saved_facts {env : Env} {m : MachineState} {top a b c : Word} (hstk : env.stackLimit.toNat + 32 ≤ top.toNat)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Static (saved m top a b c) ∧ env.next (saved m top a b c) = env.next m ∧
      env.Frame top Tactic.F m (saved m top a b c) := by
  have e8 := top_sub (top := top) 0xfffffffffffffff8#64 rfl (k := 8) (by omega)
  have e16 := top_sub (top := top) 0xfffffffffffffff0#64 rfl (k := 16) (by omega)
  have e24 := top_sub (top := top) 0xffffffffffffffe8#64 rfl (k := 24) (by omega)
  refine ⟨Env.static_setMem_stack (Env.static_setMem_stack (Env.static_setMem_stack hst (by omega)) (by omega))
    (by omega), ?_, ?_⟩
  · rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  · exact Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_refl hnx) (by omega) (by omega))
      (by omega) (by omega)) (by omega) (by omega)

/-- The callees' room below the frame: the panic's and `stack_point`'s, facts `rv_sym` closes the calls' with. -/
theorem room0 {env : Env} {top : Word} {sp : Nat} (h : env.stackLimit.toNat + (32 + sp) ≤ top.toNat) :
    env.stackLimit.toNat + 0 ≤ (top + 18446744073709551584#64).toNat ∧
      env.stackLimit.toNat + sp ≤ (top + 18446744073709551584#64).toNat := by
  have := top_sub (top := top) 18446744073709551584#64 rfl (k := 32) (by omega)
  omega

/-- `sret`'s words `8..32` (the point's header) lie in its `80`. -/
theorem sret8_sub {a b : Word} (ha : a.toNat + 80 < 2 ^ 64) (h : InRange (a + 8#64) 24 b) : InRange a 80 b := by
  obtain ⟨h1, h2⟩ := h
  rw [toNat_add_ofNat (by omega)] at h1 h2
  exact ⟨by omega, by omega⟩

/-- `sret`'s header words are none of the three slots below `top`. -/
theorem sret8_not_slot {env : Env} {m : MachineState} {top a : Word} (hown : env.Owned m top a 80)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hstk : env.stackLimit.toNat + 32 ≤ top.toNat) {k : Nat}
    (c : Word) (hc : c.toNat = 2 ^ 64 - k) (hk0 : 0 < k) (hk : k ≤ 24) : ¬ InRange (a + 8#64) 24 (top + c) := by
  have := env.layout; have := hown.2
  have e := top_sub (top := top) c hc (k := k) (by omega)
  intro ⟨h1, h2⟩
  rw [toNat_add_ofNat (by omega), e] at h1 h2
  rcases hown.1 with h | h <;> omega

/-- A slot at or above the callee's stack top, as `getMem_above` asks. -/
theorem slot_ge {top : Word} {k : Nat} (c : Word) (hc : c.toNat = 2 ^ 64 - k) (hk0 : 0 < k) (hk : k ≤ 32)
    (h32 : 32 ≤ top.toNat) : (top + 18446744073709551584#64).toNat ≤ (top + c).toNat := by
  rw [top_sub _ rfl (k := 32) (by omega), top_sub c hc (k := k) (by omega)]; omega

/-- The point's header in `sret` is apart from the code's three stores into it. -/
theorem hdr_apart {a : Word} (ha : a.toNat + 80 < 2 ^ 64) :
    ¬ InRange (a + 8#64) 24 (a + 64#64) ∧ ¬ InRange (a + 8#64) 24 (a + 72#64) ∧ ¬ InRange (a + 8#64) 24 a := by
  unfold InRange
  rw [toNat_add_ofNat (k := 8) (by omega), toNat_add_ofNat (k := 64) (by omega), toNat_add_ofNat (k := 72) (by omega)]
  omega

/-- A block allocated by the callee is apart from `sret`'s words, which the caller owns. -/
theorem fresh_apart {env : Env} {m : MachineState} {top a ptr : Word} {n : Nat} (hown : env.Owned m top a 80)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hlo : (env.next m).toNat ≤ ptr.toNat)
    (hhi : ptr.toNat + n ≤ env.heapEnd.toNat) {k : Nat} (hk : k < 80) : ¬ InRange ptr n (a + BitVec.ofNat 64 k) := by
  have := env.layout; have := hown.2
  unfold InRange; rw [toNat_add_ofNat (by omega)]
  rcases hown.1 with h | h <;> omega

/-- What the callee keeps of the caller's objects: below `NEXT`, or at or above `top`, outside its `out`. -/
theorem callee_keep {env : Env} {m S m1 : MachineState} {top b : Word} {out : Word → Prop}
    (hS2 : env.next S = env.next m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hF : env.Frame (top + 18446744073709551584#64) out S m1)
    (hlim32 : env.stackLimit.toNat ≤ (top + 18446744073709551584#64).toNat)
    (h32 : (top + 18446744073709551584#64).toNat = top.toNat - 32)
    (hb : b.toNat < (env.next m).toNat ∨ top.toNat ≤ b.toNat) (hout : ¬ out b) : m1.getMem b = S.getMem b := by
  rcases hb with hb | hb
  · exact hF.getMem_below_next (by rw [hS2]; exact hnx) (by rw [hS2]; exact hb) hout
  · exact hF.getMem_above hlim32 (by omega) hout

/-- The contract for one claim, `stack_point`'s at the claim's point. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {sp need : Nat} (hn : 32 + sp ≤ need) (l : Model.LayoutRust) (c : LeanVM.Protocol.Verifier.ColumnClaim)
    (hsp : Holds env p L.stackPoint.idx sp (Spec.Multilinear.StackPoint.Pre env c.point)
      (Spec.Multilinear.StackPoint.Post env c.point) (Spec.Whir.SretOut Layouts.Vec.byteSize))
    (hpanic : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx 0) :
    Holds env p i need (Pre env l c) (Post env l c) (Spec.Whir.SretOut Layouts.OptionStackClaim.byteSize) := by
  rv_auto hp stop [8] with [hL] using [hsp, hpanic]
  replace hpre_3 : env.stackLimit.toNat + (32 + sp) ≤ top.toNat := by omega
  have hstk : env.stackLimit.toNat + 32 ≤ top.toNat := by omega
  rw [hpre_2] at hpre_6 hpre_8 hpre_10
  obtain ⟨s0, s0', s0''⟩ := slots_ne hstk (by simpa using owned_at (k := 0) ⟨hpre_6, hpre_7⟩ hpre_5 (by decide))
  obtain ⟨s64, s64', s64''⟩ := slots_ne hstk (owned_at (k := 64) ⟨hpre_6, hpre_7⟩ hpre_5 (by decide))
  obtain ⟨s72, s72', s72''⟩ := slots_ne hstk (owned_at (k := 72) ⟨hpre_6, hpre_7⟩ hpre_5 (by decide))
  obtain ⟨a24, a24', a24''⟩ := slots_ne hstk (owned_at (k := 24) ⟨hpre_8, hpre_9⟩ hpre_5 (by decide))
  obtain ⟨a8, a8', a8''⟩ := slots_ne hstk (owned_at (k := 8) ⟨hpre_8, hpre_9⟩ hpre_5 (by decide))
  obtain ⟨a16, a16', a16''⟩ := slots_ne hstk (owned_at (k := 16) ⟨hpre_8, hpre_9⟩ hpre_5 (by decide))
  obtain ⟨b104, b104', b104''⟩ := slots_ne hstk (owned_at (k := 104) ⟨hpre_10, hpre_11⟩ hpre_5 (by decide))
  obtain ⟨b112, b112', b112''⟩ := slots_ne hstk (owned_at (k := 112) ⟨hpre_10, hpre_11⟩ hpre_5 (by decide))
  obtain ⟨b168, b168', b168''⟩ := slots_ne hstk (owned_at (k := 168) ⟨hpre_10, hpre_11⟩ hpre_5 (by decide))
  obtain ⟨pcap, hpv⟩ := hpre_15
  simp only [Layouts.ColumnClaim.column, Layouts.ColumnClaim.point, Layouts.ColumnClaim.value, vecPtr, vecLen,
    Layouts.Vec.ptr, Layouts.Vec.len, Layouts.Layout.placements, Layouts.Layout.stack_log, BitVec.add_zero,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd] at hpre_13 hpv hpre_16 hpre_17 hpre_18 hpre_19 hpre_20 hpre_21 hpre_22
  obtain ⟨hS1, hS2, hS3⟩ := saved_facts (a := ret) (b := regs .x8) (c := regs .x9) hstk hpre_4 hpre_5
  obtain ⟨_, _⟩ := room0 hpre_3
  rv_sym hp stop [14] with [hL] using [hsp, hpanic]
  all_goals try first | exact hS1 | (rw [hS2]; exact hpre_5)
  -- the column is in range: the element's three words are apart from the slots
  have hlenb : l.placements.length < 2 ^ 64 := by
    have := hpre_18; simp only [Layouts.OptionPlacement.byteSize] at this; omega
  have hk : c.column < l.placements.length := by
    rw [hpre_13, hpre_20, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hc; omega
  have helt := Proof.Layout.Committed.elem_addr (m.getMem (regs .x12 + 104#64)) (m.getMem (regs .x11 + 24#64))
  have hcolN : (m.getMem (regs .x11 + 24#64)).toNat = c.column := by
    rw [hpre_13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpre_14]
  rw [hcolN] at helt
  have hq : (m.getMem (regs .x12 + 104#64)).toNat + 24 * l.placements.length ≤ env.heapEnd.toNat := by
    have := hpre_21; unfold Env.Live at this; simp only [Layouts.OptionPlacement.byteSize] at this; omega
  have hE : ∀ k, k ≤ 16 → ((m.getMem (regs .x12 + 104#64) + (m.getMem (regs .x11 + 24#64) <<< 4 +
      m.getMem (regs .x11 + 24#64) <<< 3)) + BitVec.ofNat 64 k).toNat < env.heapEnd.toNat := fun k hk' => by
    have hb := env.heapEnd.isLt
    have h1 : (m.getMem (regs .x12 + 104#64) + BitVec.ofNat 64 (24 * c.column)).toNat =
        (m.getMem (regs .x12 + 104#64)).toNat + 24 * c.column := toNat_add_ofNat (by omega)
    rw [helt, toNat_add_ofNat (by rw [h1]; omega), h1]; omega
  obtain ⟨e0, e0', e0''⟩ := slots_ne hstk (Or.inl (by
    have := hE 0 (by omega); simp only [BitVec.add_zero] at this; exact this))
  obtain ⟨e8, e8', e8''⟩ := slots_ne hstk (Or.inl (hE 8 (by omega)))
  obtain ⟨e16, e16', e16''⟩ := slots_ne hstk (Or.inl (hE 16 (by omega)))
  have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  have hown : env.Owned m top (regs .x10) 80 := ⟨hpre_6, hpre_7⟩
  have hb80 : (regs .x10).toNat + 80 < 2 ^ 64 := hpre_7
  have o0 := Proof.Layout.owned_slot0 hown hpre_5 hlim (by decide)
  have o64 := Proof.Layout.owned_slot (k := 64) hown hpre_5 hlim (by decide)
  have o72 := Proof.Layout.owned_slot (k := 72) hown hpre_5 hlim (by decide)
  have h32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 := top_sub _ rfl (by omega)
  have hlim32 : env.stackLimit.toNat ≤ (top + 18446744073709551584#64).toNat := by omega
  obtain ⟨c32, c32', c32''⟩ := slots_ne hstk (owned_at (k := 32) ⟨hpre_8, hpre_9⟩ hpre_5 (by decide))
  obtain ⟨c40, c40', c40''⟩ := slots_ne hstk (owned_at (k := 40) ⟨hpre_8, hpre_9⟩ hpre_5 (by decide))
  have hel := hpre_19 c.column hk
  simp only [Layouts.OptionPlacement.byteSize] at hel
  rw [← helt] at hel
  have hgetD : l.placements.getD c.column none = l.placements[c.column] := List.getD_eq_getElem _ _ hk
  rv_sym hp with [hL] using [hsp, hpanic]
  -- the element `None`: `None` at `sret`
  · exact Proof.Layout.frame_setMem_out (Tactic.frame_weaken hS3) o0.1 o0.2.1
  · exact Env.static_setMem hS1 o0.2.2
  · have hnone : l.placements[c.column] = none := by
      cases h : l.placements[c.column] with
      | none => rfl
      | some pl =>
        rw [h] at hel
        simp only [OptPlacementAt, Layouts.OptionPlacement.tagOffset, Layouts.OptionPlacement.Some.tag,
          BitVec.add_zero] at hel
        rw [hel.1] at hc; exact absurd hc (by decide)
    have hon : Model.onStackRust l c = none := by simp only [Model.onStackRust, hgetD, hnone, Option.map_none]
    rw [hon]
    simp only [Layouts.OptionStackClaim.tagOffset, Layouts.OptionStackClaim.None.tag, BitVec.add_zero]
    exact MachineState.getMem_setMem_eq
  -- `stack_point`'s precondition
  · exact hS1
  · rw [hS2]; exact hpre_5
  · rw [hS2, toNat_add_ofNat (by omega), h32]; simp only [Layouts.Vec.byteSize]
    rcases hpre_6 with h | h <;> [exact Or.inl (by simp only [Layouts.OptionStackClaim.byteSize] at h; omega);
      exact Or.inr (by omega)]
  · rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega
  · have := hpv.len_eq; simp only [vecLen, Layouts.Vec.len] at this; exact this
  · exact hpv.elems.keep (Env.Frame.keeps_live hS3 hpre_5 (by simpa using hpre_16) fun _ _ h => h)
  · exact hpre_16.frame hS3
  -- after `stack_point`: the saved registers
  · rw [Env.Frame.getMem_above hret1_14 hlim32 (slot_ge (k := 8) 18446744073709551608#64 rfl (by omega) (by omega) (by omega))
      (sret8_not_slot hown hpre_5 hstk (k := 8) 18446744073709551608#64 rfl (by omega) (by omega))]
    simp
  · rw [Env.Frame.getMem_above hret1_14 hlim32 (slot_ge (k := 16) 18446744073709551600#64 rfl (by omega) (by omega) (by omega))
      (sret8_not_slot hown hpre_5 hstk (k := 16) 18446744073709551600#64 rfl (by omega) (by omega))]
    simp
  · rw [Env.Frame.getMem_above hret1_14 hlim32 (slot_ge (k := 24) 18446744073709551592#64 rfl (by omega) (by omega) (by omega))
      (sret8_not_slot hown hpre_5 hstk (k := 24) 18446744073709551592#64 rfl (by omega) (by omega))]
    simp
  · exact Proof.Layout.frame_setMem_out (Proof.Layout.frame_setMem_out (Proof.Layout.frame_setMem_out
      ((Tactic.frame_weaken hS3).trans hret1_14 (by omega)
        fun b h => Or.inr (Or.inr (Or.inr (sret8_sub hb80 h)))) o64.1 o64.2.1) o72.1 o72.2.1) o0.1 o0.2.1
  · exact Env.static_setMem (Env.static_setMem (Env.static_setMem hret1_15 o64.2.2) o72.2.2) o0.2.2
  · obtain ⟨pl, hpl⟩ : ∃ pl, l.placements[c.column] = some pl := by
      cases h : l.placements[c.column] with
      | none =>
        rw [h] at hel
        simp only [OptPlacementAt, Layouts.OptionPlacement.tagOffset, Layouts.OptionPlacement.None.tag,
          BitVec.add_zero] at hel
        rw [hel] at hc; exact absurd hc (by decide)
      | some pl => exact ⟨pl, rfl⟩
    rw [hpl] at hel
    simp only [OptPlacementAt, Layouts.OptionPlacement.tagOffset, Layouts.OptionPlacement.Some.tag,
      Layouts.OptionPlacement.Some.f0, Layouts.Placement.variables, Layouts.Placement.index, BitVec.add_zero,
      Nat.reduceAdd] at hel
    have hvc := hpre_24 pl (by rw [hgetD, hpl])
    have hon : Model.onStackRust l c = some (.eq (pl.stackPoint c.point l.stackLog), c.value) := by
      simp only [Model.onStackRust, hgetD, hpl, Option.map_some]
    rw [hon]
    obtain ⟨ptr, cap, hv, hfr⟩ := hret1_16
    simp only [Spec.Multilinear.StackPoint.placement, Tactic.rf_set_x1, Tactic.rf_get_x11, Tactic.rf_get_x12,
      hel.2.1, hel.2.2, hpre_22, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvc,
      Nat.mod_eq_of_lt hpre_23] at hv
    rw [show (⟨pl.variableCount, pl.index⟩ : Model.PlacementRust) = pl from rfl] at hv
    have hd := hdr_apart hb80
    have hnxM : ∀ (M : MachineState) (A B : Word),
        env.next (((M.setMem (regs .x10 + 64#64) A).setMem (regs .x10 + 72#64) B).setMem (regs .x10)
          9223372036854775808#64) = env.next M := fun M A B => by
      simp only [Env.next]
      rw [MachineState.getMem_setMem_ne (Ne.symm o0.2.1), MachineState.getMem_setMem_ne (Ne.symm o72.2.1),
        MachineState.getMem_setMem_ne (Ne.symm o64.2.1)]
    have hnx1 : (env.next m1).toNat ≤ env.heapEnd.toNat := hret1_14.2.1
    -- the claim's value, kept by `stack_point` and the stores
    have hx11 : ∀ k, k < 48 → ((regs .x11 + BitVec.ofNat 64 k).toNat < (env.next m).toNat ∨
        top.toNat ≤ (regs .x11 + BitVec.ofNat 64 k).toNat) := fun k hk => by
      have := hpre_9; simp only [Layouts.ColumnClaim.byteSize] at this hpre_8
      rw [toNat_add_ofNat (by omega)]; rcases hpre_8 with h | h <;> omega
    have hnot : ∀ k, k < 48 → ¬ InRange (regs .x10 + 8#64) 24 (regs .x11 + BitVec.ofNat 64 k) := fun k hk h =>
      hpre_12 _ (sret8_sub hb80 h) (by
        have := hpre_9; simp only [Layouts.ColumnClaim.byteSize] at this ⊢; unfold InRange
        rw [toNat_add_ofNat (by omega)]; omega)
    have v0 : m1.getMem (regs .x11 + 32#64) = (Model.limbs c.value).1 := by
      rw [callee_keep hS2 hpre_5 hret1_14 hlim32 h32 (hx11 32 (by omega)) (hnot 32 (by omega)),
        MachineState.getMem_setMem_ne c32'', MachineState.getMem_setMem_ne c32', MachineState.getMem_setMem_ne c32]
      have := hpre_17.1; simp only [Layouts.E.c0, BitVec.add_zero] at this; exact this
    have v1 : m1.getMem (regs .x11 + 40#64) = (Model.limbs c.value).2 := by
      rw [callee_keep hS2 hpre_5 hret1_14 hlim32 h32 (hx11 40 (by omega)) (hnot 40 (by omega)),
        MachineState.getMem_setMem_ne c40'', MachineState.getMem_setMem_ne c40', MachineState.getMem_setMem_ne c40]
      have := hpre_17.2; simp only [Layouts.E.c1, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd] at this
      exact this
    have k64 : regs .x10 + 64#64 ≠ regs .x10 := Tactic.add_ne (by decide)
    have k72 : regs .x10 + 72#64 ≠ regs .x10 := Tactic.add_ne (by decide)
    have k6472 : regs .x10 + 64#64 ≠ regs .x10 + 72#64 := Tactic.add_ne_add (by decide)
    refine ⟨?_, ⟨ptr, cap, ?_, ?_⟩, ?_⟩
    · simp only [Layouts.StackClaim.f0, Layouts.StackWeight.tagOffset, Layouts.StackWeight.Eq.tag, Nat.reduceAdd,
        BitVec.add_zero]
      exact MachineState.getMem_setMem_eq
    · simp only [Layouts.StackClaim.f0, Layouts.StackWeight.Eq.f0, Nat.reduceAdd]
      refine hv.keep (by rw [toNat_add_ofNat (by omega)]; simp only [Layouts.Vec.byteSize]; omega)
        (by simp only [Layouts.Vec.byteSize]
            exact ((Keeps.setMem hd.1).trans (Keeps.setMem hd.2.1)).trans (Keeps.setMem hd.2.2)) fun he => ?_
      rcases hfr with h0 | hf
      · have : (List.map Model.limbs (pl.stackPoint c.point l.stackLog)).length = 0 := by
          have := hv.len_le; omega
        exact he.keep (fun b hb => by simp only [this, Nat.mul_zero] at hb; exact absurd hb (by unfold InRange; omega))
      · have hl := hv.len_le
        have hlo : (env.next m).toNat ≤ ptr.toNat := by have := hf.1; rw [hS2] at this; exact this
        have hhi : ptr.toNat + Layouts.E.byteSize *
            (List.map Model.limbs (pl.stackPoint c.point l.stackLog)).length ≤ env.heapEnd.toNat := by
          have := hf.2; simp only [Layouts.E.byteSize] at this ⊢; omega
        have f64 := fresh_apart hown hlim hlo hhi (k := 64) (by omega)
        have f72 := fresh_apart hown hlim hlo hhi (k := 72) (by omega)
        have f0 := fresh_apart hown hlim hlo hhi (k := 0) (by omega)
        simp only [BitVec.add_zero] at f0
        exact he.keep (((Keeps.setMem f64).trans (Keeps.setMem f72)).trans (Keeps.setMem f0))
    · rcases hfr with h0 | hf
      · exact Or.inl h0
      · exact Or.inr ⟨by rw [← hS2]; exact hf.1, by rw [hnxM]; exact hf.2⟩
    · simp only [EAt, Layouts.StackClaim.f1, Layouts.E.c0, Layouts.E.c1, BitVec.add_zero, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, Nat.reduceAdd]
      refine ⟨?_, ?_⟩
      · rw [MachineState.getMem_setMem_ne k64, MachineState.getMem_setMem_ne k6472, MachineState.getMem_setMem_eq, v0]
      · rw [MachineState.getMem_setMem_ne k72, MachineState.getMem_setMem_eq, v1]

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {sp need : Nat} (hn : 32 + sp ≤ need) (hsp : Spec.Multilinear.StackPoint.spec env p L.stackPoint.idx sp)
    (hpanic : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx 0) : spec env p i need :=
  fun l c => ok_at env p i L hp hL hn l c (hsp c.point) hpanic

end Rv64mc.Proof.Bus.OnStack
