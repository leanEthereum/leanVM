import Rv64mc.Proof.Layout.MemoryIfT
import Rv64mc.Proof.Layout.GpowT
import Rv64mc.Proof.Runtime.PanicsT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Flushes.Bytecode

namespace Rv64mc.Proof.Layout.BytecodeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Layout
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Layout.FormReprT (FormT FormsT)
open Rv64mc.Proof.Layout.PairT (FlushesT OutT)
open Rv64mc.Proof.Layout.PairFormT (FlushesFormT)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Proof.Layout.FromElemVecFormT (VecFormT)
open Rv64mc.Proof.Layout.StateDerivedT (get_ne top_sub fkeep)
open Rv64mc.Gen.Verifier.Layout.Flushes.Bytecode (Link tmpl d_c8_d6dfd6bc_words)

variable {env : Env}

def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FlushesT env m (regs .x2) (regs .x10) ∧ (regs .x10).toNat % 8 = 0 ∧ FlushesFormT env m (regs .x10) ∧
    StackObj (regs .x2) (regs .x13) 24 ∧ VecFormT env m (regs .x13)

def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (StateDerivedT.PostT env) OutT AbortStop

@[irreducible] def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PreT env regs m

theorem preS_eq : PreS env = PreT env := by unfold PreS; rfl


open Rv64mc.Proof.Layout.ConcatFormT (Acc Slots Saved)
open Rv64mc.Proof.Layout.MemoryT (KPre KPost)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq)

/-! ## The vector at `sp + 0x48`: its header and the two `spec_extend`s -/

open Rv64mc.Proof.Layout.ConcatFormT (SliceFT Above buf_live add24 src_keep slice_end SEPre SEPost)

/-- **`spec_extend`'s precondition at a call** from `top - 160`, for the vector at `top - 88` over a buffer allocated
    since `m` and a slice that `SliceFT` puts below `NEXT` at `m`. -/
theorem se_pre {m M : MachineState} {top q l : Word} {n c : Nat} {R : Reg → Word}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 160 ≤ top.toNat)
    (hA : Acc env m M (top + 18446744073709551528#64) n c)
    (hkM : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M.getMem x = m.getMem x)
    (hnM : (env.next m).toNat ≤ (env.next M).toNat) (hMx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (hs : SliceFT env m top q l) (hroom : n + l.toNat ≤ c) (r2 : R .x2 = top + 18446744073709551456#64) (r10 : R .x10 = top + 18446744073709551528#64)
    (r11 : R .x11 = q) (r12 : (R .x12).toNat = q.toNat + 24 * l.toNat) : SEPre env R M := by
  obtain ⟨hV, hn, hc, hc0, hFs, hAb⟩ := hA
  have hlay := env.layout
  have := hW.top_le
  have hx := hW.next_ge
  have hbl := buf_live hV
  have t160 := top_sub (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have hcnt : SpecExtendFormT.cnt R = l.toNat := by unfold SpecExtendFormT.cnt; rw [r12, r11]; omega
  unfold SEPre SpecExtendFormT.PreT SpecExtendFormT.spareLo SpecExtendFormT.spareHi
  rw [hcnt, r10, r11, r12, r2, hn, hc]
  rw [hc] at hbl
  refine ⟨hV, ⟨by omega, by omega⟩, hFs, fun i hi => ?_, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rcases hAb i hi with h0 | ⟨a1, -⟩
    · exact .inl h0
    · exact .inr (.inr a1)
  · by_cases hl0 : l.toNat = 0
    · exact .inl hl0
    rcases hs with h0 | ⟨hw, hq, -⟩
    · exact absurd h0 hl0
    unfold InWin at hw
    refine .inr ⟨?_, ?_, ?_⟩
    · unfold OffStack; omega
    · rcases hq with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
    · rcases hc0 with h | h
      · omega
      rcases hq with h' | h'
      · exact .inl (by omega)
      · exact .inr (by rcases hbl with h0 | ⟨-, h2⟩ <;> have := hW.heapEnd_le <;> omega)
  · by_cases hl0 : l.toNat = 0
    · intro i hi; omega
    exact (src_keep hs hl0 hkM hnM).1
  · intro i hi
    have hl0 : l.toNat ≠ 0 := by omega
    obtain ⟨e1, e2⟩ := (src_keep hs hl0 hkM hnM).2 i hi
    rw [e1, e2]
    rcases hs with h0 | ⟨-, -, hF⟩
    · exact absurd h0 hl0
    rcases (hF i hi).foot with h0 | ⟨-, a2, -⟩
    · exact .inl h0
    · rcases hc0 with h | h
      · omega
      · exact .inr (.inl (by omega))

/-- **After a `spec_extend`** from `top - 160` on the vector at `top - 88` with `l` more `Form`s: the vector `l`
    longer, the frame from `m`, and the words from `top - 64` kept. -/
theorem acc_step {m M M' : MachineState} {top : Word} {n c l : Nat} {R r' : Reg → Word}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 160 ≤ top.toNat)
    (hA : Acc env m M (top + 18446744073709551528#64) n c) (r10 : R .x10 = top + 18446744073709551528#64)
    (hcnt : SpecExtendFormT.cnt R = l) (hroom : n + l ≤ c) (hF : env.Frame top Tactic.F m M)
    (hFs : env.Frame (top + 18446744073709551456#64) (SpecExtendFormT.OutT R M) M M')
    (hP : SEPost env R M r' M') :
    Acc env m M' (top + 18446744073709551528#64) (n + l) c ∧ env.Frame top Tactic.F m M' ∧
      ∀ x : Word, top.toNat - 64 ≤ x.toNat → x.toNat < top.toNat → M'.getMem x = M.getMem x := by
  have hlay := env.layout
  have := hW.top_le
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have hout := ConcatFormT.out_cases hA (by omega) t88 r10
  rw [hcnt] at hout
  obtain ⟨hV, hn, hc, hc0, -, hAb⟩ := hA
  unfold SEPost at hP
  obtain ⟨hV', hl', hc', hp', hF', -, hFT⟩ := hP
  rw [r10] at hV' hl' hc' hp' hF' hFT
  rw [hn, hcnt] at hl' hF' hFT
  have hx := hW.next_ge
  have t160 := top_sub (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have hbl := buf_live hV
  rw [hc] at hbl
  have nM := hF.1
  have xM := hF.2.1
  have nM' := hFs.1
  have xM' := hFs.2.1
  have kS : ∀ x : Word, (x.toNat < (env.next M).toNat ∧ ((vecPtr M (top + 18446744073709551528#64)).toNat ≤ x.toNat →
      x.toNat < (vecPtr M (top + 18446744073709551528#64)).toNat + 24 * n)) ∨ top.toNat - 64 ≤ x.toNat →
      M'.getMem x = M.getMem x :=
    fun x hx' => hFs.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · rw [t160] at hw; omega
      · omega
      · rw [hw] at hx'; omega
      · rcases hout x hw with h | ⟨h1, h2⟩
        · omega
        · rcases hbl with h' | ⟨h1', h2'⟩
          · omega
          · omega
  refine ⟨⟨hV', by rw [hl'], by rw [hc', hc], by rw [hp']; exact hc0, by rw [hp']; exact hF', ?_⟩,
    hF.trans hFs (by rw [t160]; omega) fun b hb => ?_, fun x h1 h2 => kS x (.inr h1)⟩
  · rw [hp']
    intro i hi
    have hc1 : c ≠ 0 := by omega
    rcases hbl with h0 | ⟨hb1, hb2⟩
    · exact absurd h0 hc1
    have ei : (vecPtr M (top + 18446744073709551528#64) + BitVec.ofNat 64 (24 * i)).toNat =
        (vecPtr M (top + 18446744073709551528#64)).toNat + 24 * i :=
      toNat_add_ofNat (by have := (env.next M).isLt; omega)
    by_cases hin : i < n
    · have e8 : (vecPtr M (top + 18446744073709551528#64) + BitVec.ofNat 64 (24 * i) + 8#64).toNat =
          (vecPtr M (top + 18446744073709551528#64)).toNat + 24 * i + 8 := by
        rw [toNat_add_ofNat (by have := (env.next M).isLt; omega), ei]
      have e16 : (vecPtr M (top + 18446744073709551528#64) + BitVec.ofNat 64 (24 * i) + 16#64).toNat =
          (vecPtr M (top + 18446744073709551528#64)).toNat + 24 * i + 16 := by
        rw [toNat_add_ofNat (by have := (env.next M).isLt; omega), ei]
      have kp : vecPtr M' (vecPtr M (top + 18446744073709551528#64) + BitVec.ofNat 64 (24 * i)) =
          vecPtr M (vecPtr M (top + 18446744073709551528#64) + BitVec.ofNat 64 (24 * i)) := by
        rw [vecPtr_eq M', vecPtr_eq M (vecPtr M _ + _)]; exact kS _ (.inl ⟨by omega, fun _ => by omega⟩)
      have kl : vecLen M' (vecPtr M (top + 18446744073709551528#64) + BitVec.ofNat 64 (24 * i)) =
          vecLen M (vecPtr M (top + 18446744073709551528#64) + BitVec.ofNat 64 (24 * i)) := by
        rw [vecLen_eq M', vecLen_eq M (vecPtr M _ + _)]; exact kS _ (.inl ⟨by omega, fun _ => by omega⟩)
      rw [kp, kl]
      exact (hAb i hin).imp id fun ⟨a1, a2⟩ => ⟨a1, by omega⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      rw [add24]
      rcases hFT j (by omega) with h0 | ⟨f1, f2⟩
      · exact .inl h0
      · exact .inr ⟨by omega, f2⟩
  · rcases hout b hb with h | ⟨h1, h2⟩
    · exact .inl ⟨by omega, by omega⟩
    · have h0 : c ≠ 0 := by omega
      rcases hbl with h' | ⟨h1', h2'⟩
      · exact absurd h' h0
      rcases hc0 with h'' | h''
      · exact absurd h'' h0
      exact .inr (.inl ⟨by omega, by omega⟩)

/-- **After a `spec_extend`**, with the slots kept. -/
theorem call_post {M3 M m1 : MachineState} {top ret q : Word} {n c l : Nat} {regs R r1 : Reg → Word}
    (hW : Windows env top M3) (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hsl : Slots M top ret regs)
    (hF : env.Frame top Tactic.F M3 M) (hA : Acc env M3 M (top + 18446744073709551528#64) n c)
    (hroom : n + l ≤ c) (hFs : env.Frame (top + 18446744073709551456#64) (SpecExtendFormT.OutT R M) M m1)
    (hP : SEPost env R M r1 m1) (r10 : R .x10 = top + 18446744073709551528#64) (r11 : R .x11 = q)
    (r12 : (R .x12).toNat = q.toNat + 24 * l) :
    Acc env M3 m1 (top + 18446744073709551528#64) (n + l) c ∧ env.Frame top Tactic.F M3 m1 ∧
      Slots m1 top ret regs := by
  have hcnt : SpecExtendFormT.cnt R = l := by unfold SpecExtendFormT.cnt; rw [r12, r11]; omega
  obtain ⟨hA1, hF1, hk⟩ := acc_step hW hlim hA r10 hcnt hroom hF hFs hP
  exact ⟨hA1, hF1, hsl.keep (by omega) hk⟩

/-! ## The tail: the prefix, `counted`, the return -/

/-- **`StateDerivedT.PostT` kept** by a memory agreeing with `M` below `NEXT` and on `self`'s 48 bytes. -/
theorem postT_keep {regs r' : Reg → Word} {m M M' : MachineState} (h : StateDerivedT.PostT env regs m r' M)
    (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ b : Word, b.toNat < (env.next M).toNat → M'.getMem b = M.getMem b)
    (hs : ∀ b : Word, (regs .x10).toNat ≤ b.toNat → b.toNat < (regs .x10).toNat + 48 → M'.getMem b = M.getMem b) :
    StateDerivedT.PostT env regs m r' M' := by
  obtain ⟨hFF, l1, l2, k1, k2⟩ := h
  have hlt := FormReprT.vecT_lt hFF.1
  have hlt2 := FormReprT.vecT_lt hFF.2.1
  have e24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by omega)
  obtain ⟨w0, w8, w16, w24, w32, w40⟩ := StateDerivedT.kept48 (by omega) hs
  have a8 : regs .x10 + 24#64 + 8#64 = regs .x10 + 32#64 := StateDerivedT.add_add rfl
  have a16 : regs .x10 + 24#64 + 16#64 = regs .x10 + 40#64 := StateDerivedT.add_add rfl
  refine ⟨(StateDerivedT.FlushesFormT.keep hFF hn hk hs).1, ?_, ?_, ?_, ?_⟩
  · rw [vecLen_eq, w16, ← vecLen_eq]; exact l1
  · rw [vecLen_eq, a16, w40, ← a16, ← vecLen_eq]; exact l2
  · rcases k1 with ⟨hp, hc⟩ | h1
    · exact .inl ⟨by rw [vecPtr_eq, w8, ← vecPtr_eq, hp], by rw [vecCap_eq, w0, ← vecCap_eq, hc]⟩
    · exact .inr (by rw [vecPtr_eq, w8, ← vecPtr_eq]; exact h1)
  · rcases k2 with ⟨hp, hc⟩ | h1
    · exact .inl ⟨by rw [vecPtr_eq, a8, w32, ← a8, ← vecPtr_eq, hp], by
        rw [vecCap_eq, w24, ← vecCap_eq, hc]⟩
    · exact .inr (by rw [vecPtr_eq, a8, w32, ← a8, ← vecPtr_eq]; exact h1)

/-- `Form::term`'s result slot `top + c` as `[top - k, top - k + 24)`. -/
theorem out_of {R : Reg → Word} {M : MachineState} {top c : Word} {k : Nat} (hc : c.toNat + k = 2 ^ 64)
    (hk : k ≤ top.toNat) (r : R .x10 = top + c) :
    ∀ x : Word, Spec.Layout.Term.Out R M x → top.toNat - k ≤ x.toNat ∧ x.toNat < top.toNat - k + 24 := fun x hx => by
  have := top_sub (top := top) hc hk
  unfold Spec.Layout.Term.Out InRange at hx; rw [r] at hx; simp only [Layouts.Form.byteSize] at hx; omega

/-- **A call from `top - 160` writing below `top - 88`** keeps what lies below `NEXT` at its entry and from
    `top - 88`. -/
theorem thru {N N' : MachineState} {top : Word} {out : Word → Prop}
    (hF : env.Frame (top + 18446744073709551456#64) out N N') (hlim : env.stackLimit.toNat + 160 ≤ top.toNat)
    (ho : ∀ y : Word, out y → top.toNat - 160 ≤ y.toNat ∧ y.toNat < top.toNat - 88) :
    ∀ x : Word, x.toNat < (env.next N).toNat ∨ top.toNat - 88 ≤ x.toNat → N'.getMem x = N.getMem x := by
  intro x hx
  have hlay := env.layout
  have := hF.1
  have := hF.2.1
  have t160 := top_sub (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  exact fkeep hF (by omega) (by omega) (fun e => by rw [e] at hx; omega) fun h => by have := ho x h; omega

/-- **`counted`'s precondition at its call**: the prefix `[constant(SEP_BYTECODE), col(0, 0)]` at `top - 160`,
    `col(count, 1)` at `top - 112`, the suffix the vector at `top - 88`; with the frame and the saved slots kept. -/
theorem cnt_pre {m M m1 m2 m3 m4 m5 M0 : MachineState} {top : Word} {regs R3 R4 R5 : Reg → Word} {n c : Nat}
    {f3 f4 f5 : LeanVM.Protocol.Verifier.Form}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (hA : Acc env M0 M (top + 18446744073709551528#64) n c)
    (d1 : env.Frame (top + 18446744073709551456#64) (fun _ => False) M m1)
    (d2 : env.Frame (top + 18446744073709551456#64) (fun _ => False) m1 m2)
    (d3 : env.Frame (top + 18446744073709551456#64) (Spec.Layout.Term.Out R3 m2) m2 m3)
    (e3 : FormIn (env.next m2) (env.next m3) m3 (top + 18446744073709551456#64) f3)
    (a3 : TermAlT.FormAl m3 (top + 18446744073709551456#64)) (r3 : R3 .x10 = top + 18446744073709551456#64)
    (d4 : env.Frame (top + 18446744073709551456#64) (Spec.Layout.Term.Out R4 m3) m3 m4)
    (e4 : FormIn (env.next m3) (env.next m4) m4 (top + 18446744073709551480#64) f4)
    (a4 : TermAlT.FormAl m4 (top + 18446744073709551480#64)) (r4 : R4 .x10 = top + 18446744073709551480#64)
    (d5 : env.Frame (top + 18446744073709551456#64) (Spec.Layout.Term.Out R5 m4) m4 m5)
    (e5 : FormIn (env.next m4) (env.next m5) m5 (top + 18446744073709551504#64) f5)
    (a5 : TermAlT.FormAl m5 (top + 18446744073709551504#64)) (r5 : R5 .x10 = top + 18446744073709551504#64)
 :
    (∀ R' : Reg → Word, R' .x2 = top + 18446744073709551456#64 → R' .x10 = regs .x10 →
      R' .x11 = top + 18446744073709551456#64 → R' .x12 = top + 18446744073709551504#64 →
      R' .x14 = M.getMem (top + 18446744073709551536#64) → R' .x15 = M.getMem (top + 18446744073709551544#64) →
      CountedT.PreT env R' m5) ∧ env.Frame top Tactic.F m m5 ∧
      ∀ x : Word, top.toNat - 64 ≤ x.toNat → x.toNat < top.toNat → m5.getMem x = M.getMem x := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, hBA⟩, hal, hFF, -, -⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  have htl := hW.top_le
  have t160 := top_sub (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have t136 := top_sub (top := top) (c := 18446744073709551480#64) (k := 136) rfl (by omega)
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have o3 := out_of (M := m2) (k := 160) rfl (by omega) r3
  have o4 := out_of (M := m3) (k := 136) rfl (by omega) r4
  have o5 := out_of (M := m4) (k := 112) rfl (by omega) r5
  have n1 := d1.1
  have n2 := d2.1
  have n3 := d3.1
  have n4 := d4.1
  have n5 := d5.1
  have x5 := d5.2.1
  have nM := hF.1
  have k1 := thru d1 hlim (fun _ h => h.elim)
  have k2 := thru d2 hlim (fun _ h => h.elim)
  have k3 := thru d3 hlim fun y hy => by have := o3 y hy; omega
  have k4 := thru d4 hlim fun y hy => by have := o4 y hy; omega
  have k5 := thru d5 hlim fun y hy => by have := o5 y hy; omega
  have kM : ∀ x : Word, (x.toNat < (env.next M).toNat ∨ top.toNat - 88 ≤ x.toNat) → m5.getMem x = M.getMem x :=
    fun x hx => by
      rw [k5 x (by omega), k4 x (by omega), k3 x (by omega), k2 x (by omega), k1 x hx]
  have F5 : env.Frame top Tactic.F m m5 := by
    have F1 := hF.trans d1 (by omega) fun _ h => h.elim
    have F2 := F1.trans d2 (by omega) fun _ h => h.elim
    have F3 := F2.trans d3 (by omega) fun x hx => .inl (by have := o3 x hx; omega)
    have F4 := F3.trans d4 (by omega) fun x hx => .inl (by have := o4 x hx; omega)
    exact F4.trans d5 (by omega) fun x hx => .inl (by have := o5 x hx; omega)
  have k0 := ConcatFormT.keepM (by omega) F5
  obtain ⟨hFF2, -⟩ := StateDerivedT.FlushesFormT.keep hFF F5.1 (fun b hb => k0 b (.inl hb))
    fun b h1 h2 => k0 b (.inr (by omega))
  have G3 : FormT env m3 (top + 18446744073709551456#64) :=
    TermAlT.formT_of e3 a3 (by omega) (Nat.le_refl _) d3.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  obtain ⟨G3', -, -⟩ := MemoryIfT.form_thru d4 G3 (by omega) (by omega) fun x hx => by have := o4 x hx; omega
  obtain ⟨G3'', -, -⟩ := MemoryIfT.form_thru d5 G3' (by omega) (by omega) fun x hx => by have := o5 x hx; omega
  have G4 : FormT env m4 (top + 18446744073709551480#64) :=
    TermAlT.formT_of e4 a4 (by omega) (Nat.le_refl _) d4.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  obtain ⟨G4', -, -⟩ := MemoryIfT.form_thru d5 G4 (by omega) (by omega) fun x hx => by have := o5 x hx; omega
  have G5 : FormT env m5 (top + 18446744073709551504#64) :=
    TermAlT.formT_of e5 a5 (by omega) (Nat.le_refl _) d5.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  obtain ⟨hV, hn, -, -, hFs, hAb⟩ := hA
  have hp8 : M.getMem (top + 18446744073709551536#64) = vecPtr M (top + 18446744073709551528#64) := by
    rw [vecPtr_eq, StateDerivedT.add_add (d := 18446744073709551536#64) rfl]
  have hl16 : M.getMem (top + 18446744073709551544#64) = vecLen M (top + 18446744073709551528#64) := by
    rw [vecLen_eq, StateDerivedT.add_add (d := 18446744073709551544#64) rfl]
  have hle := hV.2.2
  have hbl := ConcatFormT.buf_live hV
  have hb : ConcatFormT.SliceFT env m5 (top + 18446744073709551456#64) (M.getMem (top + 18446744073709551536#64))
      (M.getMem (top + 18446744073709551544#64)) := by
    rw [hp8, hl16]
    by_cases h0 : (vecLen M (top + 18446744073709551528#64)).toNat = 0
    · exact .inl h0
    rcases hbl with hc0 | ⟨hb1, hb2⟩
    · omega
    refine .inr ⟨.inl ⟨hb1, by have := hF.2.1; omega⟩, .inl (by omega), ?_⟩
    rw [hn]
    refine (ConcatFormT.forms_keep (lo := (vecPtr M (top + 18446744073709551528#64)).toNat) hFs hAb
      (.inr ⟨Nat.le_refl _, by omega⟩) (Nat.le_add_right _ _) (by omega) fun x l1 l2 => kM x (.inl l2)).1
  have two : (2#64).toNat = 2 := rfl
  refine ⟨fun R' s2 s10 s11 s12 s14 s15 => ?_, F5, fun x l1 l2 => kM x (.inr (by omega))⟩
  unfold CountedT.PreT PairT.FlushesT
  rw [s2, s10, s11, s12, s14, s15]
  refine ⟨⟨hFF2.1, hFF2.2.1, ⟨by omega, ha2⟩, hFF2.2.2.1⟩, hal, hFF2,
    .inr ⟨by rw [two]; exact .inr ⟨by omega, by omega⟩, .inr (Nat.le_refl _), fun i hi => ?_⟩,
    ⟨by omega, by omega⟩, G5, hb⟩
  rw [two] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simpa using G3''
  · rw [StateDerivedT.add_add (d := 18446744073709551480#64) rfl]; exact G4'

/-- **The return, from `counted`'s**: the saved slots, the frame and the postcondition. -/
theorem post {m M m6 : MachineState} {top : Word} {regs R' r6 : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m)
    (hstk : env.stackLimit.toNat + 160 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (hFs : env.Frame (top + 18446744073709551456#64) (OutT R' M) M m6)
    (hP : KPost env R' M r6 m6) (s10 : R' .x10 = regs .x10) :
    (∀ x : Word, top.toNat - 64 ≤ x.toNat → x.toNat < top.toNat → m6.getMem x = M.getMem x) ∧
      env.Frame top (OutT regs m) m m6 ∧ ∀ r', StateDerivedT.PostT env regs m r' m6 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have htl := hW.top_le
  have t160 := top_sub (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have kM := ConcatFormT.keepM (by omega) hF
  obtain ⟨hout, slotLow, hpost⟩ := StateDerivedT.self_kept hV1 hV2 hF.1 (fun x hx _ => kM x (.inr (by omega))) s10
  refine ⟨fun x l1 l2 => hFs.2.2 x fun hw => ?_, (Tactic.frame_weaken hF).trans hFs (by omega)
    fun b hb => .inr (.inr (.inr (hout b hb))), fun r' => ?_⟩
  · rcases hw with hw | hw | hw | hw
    · omega
    · have := hFs.2.1; omega
    · rw [hw] at l1; omega
    · rcases slotLow x (hout x hw) with h | h
      · have := hF.2.1; have := hF.1; omega
      · omega
  unfold KPost at hP
  exact hpost r6 r' m6 hP

/-- **The return after the last drop**: the frame and the postcondition kept. -/
theorem post7 {m m6 m7 : MachineState} {top : Word} {regs r' : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hstk : env.stackLimit.toNat + 160 ≤ top.toNat)
    (F6 : env.Frame top (OutT regs m) m m6) (P6 : StateDerivedT.PostT env regs m r' m6)
    (d7 : env.Frame (top + 18446744073709551456#64) (fun _ => False) m6 m7) :
    env.Frame top (OutT regs m) m m7 ∧ StateDerivedT.PostT env regs m r' m7 := by
  obtain ⟨⟨-, -, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hpre
  rw [h2] at ha1
  have t160 := top_sub (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have hlay := env.layout
  have k7 := thru d7 (by omega) fun _ h => h.elim
  exact ⟨F6.trans d7 (by omega) fun _ h => h.elim, postT_keep P6 d7.1 (fun b hb => k7 b (.inl hb))
    fun b h1 h2 => k7 b (.inr (by omega))⟩

/-! ## The head: `constant(g^opcode)`'s block and the operands -/

/-- **The state after `constant(g^opcode)`** at the 24-byte block `B` `alloc` returned: the slots, the frame, `B` a
    slice of one `Form`, the operands a slice of `Form`s, their length's bytes below `2 ^ 63`. -/
theorem blk {m S mA mG M3 : MachineState} {top ret B : Word} {regs RC : Reg → Word}
    {f : LeanVM.Protocol.Verifier.Form}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m)
    (hlim : env.stackLimit.toNat + 160 ≤ top.toNat) (hsl : Slots S top ret regs) (hF0 : env.Frame top Tactic.F m S)
    (a14 : env.Frame (top + 18446744073709551456#64) (fun _ => False) S mA)
    (a16 : (env.next m).toNat ≤ B.toNat) (a17 : B.toNat % 8 = 0)
    (a18 : B.toNat + (24#64).toNat = (env.next mA).toNat)
    (g14 : env.Frame (top + 18446744073709551456#64) (fun _ => False) mA mG)
    (c14 : env.Frame (top + 18446744073709551456#64) (Spec.Layout.Term.Out RC mG) mG M3) (rc : RC .x10 = B)
    (c16 : FormIn (env.next mG) (env.next M3) M3 B f) (c17 : TermAlT.FormAl M3 B) :
    Slots M3 top ret regs ∧ env.Frame top Tactic.F m M3 ∧ SliceFT env M3 top B 1#64 ∧
      SliceFT env M3 top (M3.getMem (regs .x13 + 8#64)) (M3.getMem (regs .x13 + 16#64)) ∧
      (M3.getMem (regs .x13 + 16#64)).toNat * 24 < 2 ^ 63 := by
  obtain ⟨-, -, -, ⟨hs1, -⟩, hV, hFs⟩ := hpre
  rw [h2] at hs1
  have hlay := env.layout
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  have htl := hW.top_le
  have e24 : (24#64).toNat = 24 := rfl
  rw [e24] at a18
  have t160 := top_sub (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have nA := a14.1
  have nG := g14.1
  have n3 := c14.1
  have x3 := c14.2.1
  have nS := hF0.1
  have hout : ∀ x : Word, Spec.Layout.Term.Out RC mG x → B.toNat ≤ x.toNat ∧ x.toNat < B.toNat + 24 :=
    fun x hx => by unfold Spec.Layout.Term.Out InRange at hx; rw [rc] at hx; exact hx
  have F3 : env.Frame top Tactic.F m M3 :=
    ((hF0.trans a14 (by omega) fun _ h => h.elim).trans g14 (by omega) fun _ h => h.elim).trans c14 (by omega)
      fun x hx => .inr (.inl ⟨by have := hout x hx; omega, by have := hout x hx; omega⟩)
  have kS : ∀ x : Word, top.toNat - 64 ≤ x.toNat → x.toNat < top.toNat → M3.getMem x = S.getMem x := fun x l1 l2 => by
    have h1 := fkeep (x := x) c14 (.inr (by omega)) (.inr (by omega)) (fun e => by rw [e] at l1; omega)
      fun h => by have := hout x h; omega
    have h2 := fkeep (x := x) g14 (.inr (by omega)) (.inr (by omega)) (fun e => by rw [e] at l1; omega) id
    have h3 := fkeep (x := x) a14 (.inr (by omega)) (.inr (by omega)) (fun e => by rw [e] at l1; omega) id
    rw [h1, h2, h3]
  have k0 := ConcatFormT.keepM (by omega) F3
  have hw13 := hV.1
  unfold InWin at hw13
  simp only [Layouts.Vec.byteSize] at hw13
  have r8 : M3.getMem (regs .x13 + 8#64) = vecPtr m (regs .x13) := by
    rw [vecPtr_eq]; exact k0 _ (.inr (by rw [toNat_add_ofNat (by omega)]; omega))
  have r16 : M3.getMem (regs .x13 + 16#64) = vecLen m (regs .x13) := by
    rw [vecLen_eq]; exact k0 _ (.inr (by rw [toNat_add_ofNat (by omega)]; omega))
  have hcap : (vecCap m (regs .x13)).toNat * 24 < 2 ^ 63 := by
    have := hV.2.1.2.2.2
    rwa [rvCapAt_eq, ← vecCap_eq] at this
  have hle := hV.2.2
  have hbl := buf_live hV
  have G : FormT env M3 B :=
    TermAlT.formT_of c16 c17 (by omega) (Nat.le_refl _) x3 hE (.inl ⟨by omega, by omega⟩) a17
  have one : (1#64).toNat = 1 := rfl
  refine ⟨hsl.keep (by omega) kS, F3, .inr ⟨by rw [one]; exact .inl ⟨by omega, by omega⟩, .inl (by omega),
    fun i hi => ?_⟩, ?_, by rw [r16]; omega⟩
  · rw [one] at hi
    obtain rfl : i = 0 := by omega
    simpa using G
  rw [r8, r16]
  refine CountedT.SliceFT.keep ?_ (by omega) F3 (Nat.le_refl _)
  by_cases h0 : (vecLen m (regs .x13)).toNat = 0
  · exact .inl h0
  rcases hbl with hc0 | ⟨hb1, hb2⟩
  · omega
  exact .inr ⟨.inl ⟨hb1, by omega⟩, .inl (by omega), hFs⟩

section Tail

variable {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC needK : Nat} (hnK : 160 + Constant.need ≤ need) (hnC : 160 + needC ≤ need)
    (hnN : 160 + needK ≤ need)
    (hdrop : Runtime.DropT.DropSpecT env p L.dropGlueVecForm.idx 0)
    (hconst : ConstantAlT.specT env p L.constant.idx) (hcol : ColAlT.colSpecT env p L.col.idx needC)
    (hcnt : HoldsT env p L.counted.idx needK (KPre env) (KPost env) OutT AbortStop)
    {needS : Nat} (hnS : 160 + needS ≤ need)
    (hse : HoldsT env p L.specExtend.idx needS (SEPre env) (SEPost env) SpecExtendFormT.OutT AbortStop)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (StateDerivedT.PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m)
include hp hL hnK hnC hnN hdrop hconst hcol hcnt hnS hse hk hstop hneed hW h16 h2 hpre

omit hnS hse in
set_option rv_sym.heap true in
theorem at68 :
    ∀ R M M0 n c, (R .x2 = top + 18446744073709551456#64 ∧ R .x8 = regs .x11 ∧ R .x9 = regs .x10 ∧
        Saved regs R) → Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      Acc env M0 M (top + 18446744073709551528#64) n c →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 136, ret, top⟩ :: rest, R, M⟩ := by
  intro R M M0 n c hR hsl hF hS hcd hA
  have hP' : True → PreT env regs m := fun _ => hpre
  have hsl' : True → Slots M top ret regs := fun _ => hsl
  have hF' : True → env.Frame top Tactic.F m M := fun _ => hF
  have hA' : True → Acc env M0 M (top + 18446744073709551528#64) n c := fun _ => hA
  have hnx : (env.next m).toNat ≤ (env.next M).toNat := hF.1
  have hnx' : (env.next M).toNat ≤ env.heapEnd.toNat := hF.2.1
  have hk' := hk
  clear hpre hsl hF hA hk
  rv_introT hR
  rv_symT hp with [hL, hnK, hnC, hnN] using [hdrop, hconst (Model.ofLimbsW (4#64, 0#64)), hcol, hcnt]
  all_goals
    have hlim : env.stackLimit.toNat + 160 ≤ top.toNat := by omega
    obtain ⟨C5, F5, k5⟩ := cnt_pre (hP' trivial) h2 hW h16 hlim (hF' trivial) (hA' trivial) hret1_14 hret2_14
      hret3_14 hret3_16 ⟨hret3_17, hret3_18⟩ rfl hret4_14 hret4_16 ⟨hret4_17, hret4_18⟩ rfl hret5_14 hret5_16
      ⟨hret5_17, hret5_18⟩ rfl
  · unfold KPre
    refine C5 _ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals rfl
  all_goals
    obtain ⟨k6, F6, P6⟩ := post (hP' trivial) h2 hW hlim F5 hret6_14 hret6_16 rfl
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ :=
      (hsl' trivial).keep (by omega) fun x l1 l2 => (k6 x l1 l2).trans (k5 x l1 l2)
  · exact t1
  · obtain ⟨F7, P7⟩ := post7 (hP' trivial) h2 hlim F6 (P6 _) hret7_14
    exact ⟨⟨rfl, t2, t3, t4, t5, t6, t7, t8, rfl, rfl, rfl, rfl, rfl⟩, F7, hret7_15, P7⟩

set_option rv_sym.heap true in
/-- **From the join after the buffer's `alloc`** (instruction 52): the header `(len + 1, buffer, 0)` at
    `sp + 0x48`, `spec_extend` from `constant`'s block `B`, then from the operands `[q, q + 24 l)`. -/
theorem at52 :
    ∀ R M M3 (B q l : Word), (R .x2 = top + 18446744073709551456#64 ∧ R .x8 = regs .x11 ∧ R .x9 = regs .x10 ∧
        R .x18 = B ∧ R .x19 = l ∧ R .x20 = q ∧ Saved regs R) → Slots M top ret regs →
      env.Frame top Tactic.F m M3 → env.Frame top Tactic.F M3 M → env.Static M → M.code = m.code →
      M3.code = m.code → SliceFT env M3 top B 1#64 → SliceFT env M3 top q l →
      (R .x21).toNat = l.toNat + 1 → (R .x21).toNat * 24 < 2 ^ 63 →
      env.Fresh M3 M (R .x10) ((R .x21).toNat * 24) → (R .x10).toNat % 8 = 0 →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 104, ret, top⟩ :: rest, R, M⟩ := by
  have h68 := at68 hp hL hnK hnC hnN hdrop hconst hcol hcnt hnS hse hk hstop hneed hW h16 h2 hpre
  intro R M M3 B q l hR hsl hF3 hFM hS hcd hcd3 hB hq hc hc63 hfr hal
  have hlim : env.stackLimit.toNat + 160 ≤ top.toNat := by simp only [Constant.need] at hnK; omega
  have hW3 : Windows env top M3 := hW.after hcd3 hF3.1
  have hlay := env.layout
  have hE := hW.heapEnd_le
  have hBw : B.toNat + 24 ≤ 0xc0000000 := by
    rcases hB with h | ⟨hw, -, -⟩
    · exact absurd h (by decide)
    · unfold InWin at hw; simp only [show (1#64).toNat = 1 from rfl] at hw; omega
  have hBr : (B + 24#64).toNat = B.toNat + 24 * (1#64).toNat := by
    rw [toNat_add_ofNat (by omega)]; rfl
  have hql := ConcatFormT.slice_lt hq hE
  obtain ⟨hA0, hF0, hS0, hk0⟩ := ConcatFormT.hdr_ok (by omega) h16 hW3 hFM hS hc63 (.inr ⟨hfr, hal⟩)
  have hsl0 := hsl.keep (by omega) hk0
  have hc0 : (ConcatFormT.hdr M top (R .x21) (R .x10)).code = m.code := by
    simp only [ConcatFormT.hdr, MachineState.code_setMem]; exact hcd
  have hk3 := ConcatFormT.keepM (by omega) hF0
  rw [hc] at hA0
  have hB' : True → SliceFT env M3 top B 1#64 := fun _ => hB
  have hq' : True → SliceFT env M3 top q l := fun _ => hq
  have hF3' : True → env.Frame top Tactic.F m M3 := fun _ => hF3
  have hnm : (env.next m).toNat ≤ (env.next M).toNat := Nat.le_trans hF3.1 hFM.1
  have hMx : (env.next M).toNat ≤ env.heapEnd.toNat := hFM.2.1
  clear hk0 hsl hfr hc hc63 hB hq hF3 hFM
  rv_introT hR
  rv_symT hp stop [136] with [hL] using [hse]
  · refine se_pre hW3 hlim hA0 hk3 hF0.1 hF0.2.1 (hB' trivial) (by rw [show (1#64).toNat = 1 from rfl]; omega)
      ?_ ?_ ?_ ?_
    all_goals first | rfl | exact hBr
  · obtain ⟨hA1, hF1, hsl1⟩ := call_post (l := 1) hW3 hlim hsl0 hF0 hA0 (by omega) hret1_14 hret1_16 rfl rfl hBr
    refine se_pre hW3 hlim hA1 (ConcatFormT.keepM (by omega) hF1) hF1.1 hF1.2.1 (hq' trivial) (by omega) ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · exact ConcatFormT.sh24 hql
  · obtain ⟨hA1, hF1, hsl1⟩ := call_post (l := 1) hW3 hlim hsl0 hF0 hA0 (by omega) hret1_14 hret1_16 rfl rfl hBr
    obtain ⟨hA2, hF2, hsl2⟩ := call_post (l := l.toNat) hW3 hlim hsl1 hF1 hA1 (by omega) hret2_14 hret2_16 rfl rfl
      (ConcatFormT.sh24 hql)
    exact h68 _ _ M3 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsl2
      ((hF3' trivial).trans hF2 (by omega) fun _ h => h.elim) hret2_15 (hret2_17.trans (hret1_17.trans hc0)) hA2

end Tail

set_option rv_sym.heap true in
/-- **`Flushes::bytecode` is total**, with 160 bytes of stack beyond its callees', given its bound's word in the
    static data. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c8_d6dfd6bc, d_c8_d6dfd6bc_words)])
    {need needA needG needH needC needS needK : Nat} (hnA : 160 + needA ≤ need) (hnG : 160 + needG ≤ need)
    (hnK : 160 + Constant.need ≤ need) (hnH : 160 + needH ≤ need) (hnC : 160 + needC ≤ need)
    (hnS : 160 + needS ≤ need) (hnN : 160 + needK ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hgpow : GpowT.specT env p L.gpow.idx needG)
    (hconst : ConstantAlT.specT env p L.constant.idx) (hhe : Aborts env p L.handleError.idx needH)
    (hse : SpecExtendFormT.SpecT env p L.specExtend.idx needS)
    (hdrop : Runtime.DropT.DropSpecT env p L.dropGlueVecForm.idx 0)
    (hcol : ColAlT.colSpecT env p L.col.idx needC)
    (hcnt : CountedT.SpecT env p L.counted.idx needK) (hpanic : Aborts env p L.panicNounwindFmt.idx 0) :
    SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hse' := ConcatFormT.se_spec hse
  have hcnt' : HoldsT env p L.counted.idx needK (KPre env) (KPost env) OutT AbortStop := by
    unfold KPre KPost; exact hcnt
  have hw1 := hd.words (List.mem_cons_self ..)
  suffices h : HoldsT env p i need (PreS env) (StateDerivedT.PostT env) OutT AbortStop by rwa [preS_eq] at h
  rv_autoT hp stop [54] with [hL, hw1] using [hal', hgpow, hpanic]
  have hP : PreT env regs m := by rw [← preS_eq]; exact hpre_6
  have hlim : env.stackLimit.toNat + 160 ≤ top.toNat := by simp only [Constant.need] at hnK; omega
  have hw13 := hP.2.2.2.2.1.1
  have ha13 : (regs .x13).toNat % 8 = 0 := hP.2.2.2.2.1.2.1.2.1
  unfold InWin at hw13
  simp only [Layouts.Vec.byteSize] at hw13
  have x8 : (regs .x13 + 8#64).toNat = (regs .x13).toNat + 8 := toNat_add_ofNat (by omega)
  have x16 : (regs .x13 + 16#64).toNat = (regs .x13).toNat + 16 := toNat_add_ofNat (by omega)
  have A14 := hret1_14
  have A16 := hret1_16
  have A17 := hret1_17
  have A18 := hret1_18
  have A19 := hret1_19
  have G14 := hret3_14
  have G18 := hret3_18
  rv_symT hp stop [104] with [hL, hw1] using [hconst (Model.gpowRust (regs .x12)), hal', hhe]
  all_goals try (rw [inWindow_iff]; first | (rw [x8]; omega) | (rw [x16]; omega))
  all_goals try (first | (rw [x8]; omega) | (rw [x16]; omega))
  all_goals try exact (Layout.CloneFormsT.data_ok hpre_8 hd (List.mem_cons_self ..) (by decide)).1
  all_goals try exact (Layout.CloneFormsT.data_ok hpre_8 hd (List.mem_cons_self ..) (by decide)).2
  all_goals
    obtain ⟨hsl0, hF0, hS0, hc0, hn0⟩ := ConcatFormT.saved_ok (top := top) (ret := ret) (regs := regs) (by omega) hpre_5 hpre_4
    simp only [ConcatFormT.saved] at hsl0 hF0 hS0 hc0 hn0
    have hblk := blk (B := r1 .x10) hP hpre_2 hpre_8 hlim hsl0 hF0 A14 A16 A17 A18 G14 hret1_14 ?rc hret1_16
      ⟨hret1_17, hret1_18⟩
    case rc => rfl
    obtain ⟨sl3, F3, hB, hq, hlen⟩ := hblk
    obtain ⟨h24, h63⟩ := ConcatFormT.sz24 hc_2
    have hS1 : (MachineState.getMem m1 (regs .x13 + 16#64) + 1#64).toNat =
        (MachineState.getMem m1 (regs .x13 + 16#64)).toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl]; omega
  · exfalso
    have := congrArg BitVec.toNat hc
    rw [h24, hS1, show (0#64).toNat = 0 from rfl] at this
    omega
  · rw [h24]; omega
  · rw [h24] at hret2_18
    refine at52 hp hL hnK hnC hnN hdrop hconst hcol hcnt' hnS hse' hk hstop hpre_3 hpre_8 hpre_7 hpre_2 hP _ _ m1
      _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (sl3.keep (by omega) fun x l1 l2 => fkeep hret2_14 (.inr (by omega)) (.inr (by omega))
        (fun e => by rw [e] at l1; omega) id)
      F3 ((Tactic.frame_refl hret1_14.2.1).trans hret2_14 (by omega) fun _ h => h.elim) hret2_15
      (hret2_19.trans (hret1_19.trans (G18.trans (A19.trans hc0))))
      (hret1_19.trans (G18.trans (A19.trans hc0))) hB hq ?_ ?_ ⟨hret2_16, ?_⟩ hret2_17
    · exact hS1
    · rw [hS1]; omega
    · rw [hS1]; omega

end Rv64mc.Proof.Layout.BytecodeT
