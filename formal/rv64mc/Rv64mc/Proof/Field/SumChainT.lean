/-
  Rv64mc.Proof.Field.SumChainT

  `<E>::sum::<Chain<vec::IntoIter<E>, vec::IntoIter<E>>>` is total (`SumChainSafeT`): passed the chain by reference,
  two optional iterators (`None` a null buffer) of `E`s, `16` bytes each, between a pointer and an end, it returns
  without writing memory. Each iterator present has its end at or above its pointer by a multiple of `16`, its
  pointer 8-byte aligned, and its elements in a window unless there are none (`IterOk`). The value returned, the sum,
  is not stated: no caller's safety reads it. The two loops are `Total.loop` with the bytes left as the measure.

  ## Main definitions

  * `IterOk`, `SumPreT`, `SumChainSafeT`

  ## Main results

  * `total`
-/

import Rv64mc.Spec.Runtime.MemT
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumChainIntoIterEIntoIterE

namespace Rv64mc.Proof.Field.SumChainT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Gen.Verifier.Field.E.SumChainIntoIterEIntoIterE (Link tmpl)

/-- The bytes `[a, a + n)` lie in a window, as numbers. -/
def Win (a : Word) (n : Nat) : Prop :=
  (0x10000000 ≤ a.toNat ∧ a.toNat + n ≤ 0x78000000) ∨ (0xa0000000 ≤ a.toNat ∧ a.toNat + n ≤ 0xc0000000)

/-- An optional `vec::IntoIter<E>` with buffer `tag`, pointer `q` and end `e`: `None` (a null buffer), or `q` at most
    `e` by a multiple of `16`, 8-byte aligned, and the elements between them in a window unless there are none. -/
def IterOk (tag q e : Word) : Prop :=
  tag = 0#64 ∨ (q.toNat ≤ e.toNat ∧ (e.toNat - q.toNat) % 16 = 0 ∧ q.toNat % 8 = 0 ∧
    (e.toNat = q.toNat ∨ Win q (e.toNat - q.toNat)))

/-- The total precondition: the chain's `64` bytes 8-byte aligned in a window, both iterators `IterOk` (the first
    at offsets `0`, `8`, `24`, the second at `32`, `40`, `56`). -/
def SumPreT (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ Win (regs .x10) 64 ∧
    IterOk (m.getMem (regs .x10)) (m.getMem (regs .x10 + 8#64)) (m.getMem (regs .x10 + 24#64)) ∧
    IterOk (m.getMem (regs .x10 + 32#64)) (m.getMem (regs .x10 + 40#64)) (m.getMem (regs .x10 + 56#64))

/-- **The total contract**: it returns, writing nothing. It does not state the sum. -/
def SumChainSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need SumPreT (fun _ _ _ _ => True)

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {Q : State rvIsa → Prop} {ret top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

/-- `AbiRegs` through writes of registers it does not read. -/
local macro "abi_ok " h:term : tactic =>
  `(tactic| ((repeat rw [AbiRegs.updReg_iff (by decide)]) <;> exact $h))

/-- The continuation the parts are proved against. -/
abbrev Cont (env : Env) (p : Lprog (Op Reg) Reg) (Q : State rvIsa → Prop) (ret top : Word) (rest : List Frame)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩

/-- The return. -/
theorem ret_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) {r : Reg → Word} (h1 : r .x1 = ret) (ha : AbiRegs top regs r) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 54, ret, top⟩ :: rest, r, m⟩ := by
  have hx2 := ha.1
  rv_symT hp with [h1, hx2]
  exact hk _ _ ⟨⟨ha, Env.Frame.refl hnx, hst, trivial⟩, rfl⟩

/-- The second iterator's loop, `k` bytes left from `x13` to `x12`. -/
theorem loopB_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    ∀ k r M, (M = m ∧ r .x1 = ret ∧ AbiRegs top regs r ∧ (r .x13).toNat + k = (r .x12).toNat ∧ k % 16 = 0 ∧
      0 < k ∧ (r .x13).toNat % 8 = 0 ∧ Win (r .x13) k) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 42, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) _ fun k r M ⟨hM, h1, ha, h13, hk16, hk0, ha13, hw⟩ ih => ?_
  subst hM
  unfold Win at hw
  have h' : (r .x13 + 16#64).toNat = (r .x13).toNat + 16 := toNat_add_ofNat (by omega)
  rv_symT hp stop [54]
  · refine ih (k - 16) _ _ (by omega) ⟨rfl, ?_, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · tnorm; exact h1
    · abi_ok ha
    · tnorm; omega
    · have : (r .x13 + 16#64).toNat ≠ (r .x12).toNat := fun h => hc (BitVec.eq_of_toNat_eq h)
      omega
    · tnorm; omega
    · unfold Win; tnorm; omega
  · exact ret_ok hp hk hst hnx (by tnorm; exact h1) (by abi_ok ha)

/-- The second iterator, present: its pointer and end, then its loop unless it is empty. -/
theorem second_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hal : (regs .x10).toNat % 8 = 0) (hw : Win (regs .x10) 64)
    (hb : IterOk (m.getMem (regs .x10 + 32#64)) (m.getMem (regs .x10 + 40#64)) (m.getMem (regs .x10 + 56#64)))
    {r : Reg → Word} (h1 : r .x1 = ret) (ha : AbiRegs top regs r) (h12 : r .x12 = regs .x10)
    (htag : m.getMem (regs .x10 + 32#64) ≠ 0#64) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 36, ret, top⟩ :: rest, r, m⟩ := by
  obtain ⟨hle, h16, hq8, hwq⟩ := hb.resolve_left htag
  unfold Win at hw
  rv_symT hp stop [42, 54] with [h12]
  · exact ret_ok hp hk hst hnx (by tnorm; exact h1) (by abi_ok ha)
  · simp only [h12] at hc ⊢
    have hne : (m.getMem (regs .x10 + 40#64)).toNat ≠ (m.getMem (regs .x10 + 56#64)).toNat :=
      fun h => hc (BitVec.eq_of_toNat_eq h)
    refine loopB_ok hp hk hst hnx ((m.getMem (regs .x10 + 56#64)).toNat - (m.getMem (regs .x10 + 40#64)).toNat)
      _ _ ⟨rfl, by tnorm; exact h1, by abi_ok ha, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 4
    · tnorm; exact hwq.resolve_left (Ne.symm hne)
    all_goals tomega

/-- The first iterator's loop, `k` bytes left from `x14` to `x15`, then the second iterator. -/
theorem loopA_ok (hp : p[i]? = some (tmpl L)) (hk : Cont env p Q ret top rest regs m) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hal : (regs .x10).toNat % 8 = 0) (hw : Win (regs .x10) 64)
    (hb : IterOk (m.getMem (regs .x10 + 32#64)) (m.getMem (regs .x10 + 40#64)) (m.getMem (regs .x10 + 56#64))) :
    ∀ k r M, (M = m ∧ r .x1 = ret ∧ AbiRegs top regs r ∧ r .x12 = regs .x10 ∧
      r .x13 = m.getMem (regs .x10 + 32#64) ∧ (r .x14).toNat + k = (r .x15).toNat ∧ k % 16 = 0 ∧
      0 < k ∧ (r .x14).toNat % 8 = 0 ∧ Win (r .x14) k) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 18, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) _ fun k r M ⟨hM, h1, ha, h12, h13, h14, hk16, hk0, ha14, hwk⟩ ih => ?_
  subst hM
  unfold Win at hwk
  have h' : (r .x14 + 16#64).toNat = (r .x14).toNat + 16 := toNat_add_ofNat (by omega)
  rv_symT hp stop [36, 54] with [h13]
  · refine ih (k - 16) _ _ (by omega) ⟨rfl, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · tnorm; exact h1
    · abi_ok ha
    · tnorm; exact h12
    · tnorm; exact h13
    · tnorm; omega
    · have : (r .x14 + 16#64).toNat ≠ (r .x15).toNat := fun h => hc (BitVec.eq_of_toNat_eq h)
      omega
    · tnorm; omega
    · unfold Win; tnorm; omega
  · exact ret_ok hp hk hst hnx (by tnorm; exact h1) (by abi_ok ha)
  · exact second_ok hp hk hst hnx hal hw hb (by tnorm; exact h1) (by abi_ok ha) (by tnorm; exact h12) (h13 ▸ hc)

set_option rv_sym.heap true in
/-- **`E::sum::<Chain<…>>` is total**, with no stack. -/
theorem total (hp : p[i]? = some (tmpl L)) : SumChainSafeT env p i 0 := by
  rv_autoT hp
  · exact ret_ok hp hk hpre_4 hpre_5 rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact second_ok hp hk hpre_4 hpre_5 hpre_6 hpre_7 hpre_9 rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl hc
  · exact second_ok hp hk hpre_4 hpre_5 hpre_6 hpre_7 hpre_9 rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl hc
  · exact ret_ok hp hk hpre_4 hpre_5 rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hle, h16, hq8, hwq⟩ := hpre_8.resolve_left hc_1
    have hne : (m.getMem (regs .x10 + 8#64)).toNat ≠ (m.getMem (regs .x10 + 24#64)).toNat :=
      fun h => hc (BitVec.eq_of_toNat_eq h)
    exact loopA_ok hp hk hpre_4 hpre_5 hpre_6 hpre_7 hpre_9
      ((m.getMem (regs .x10 + 24#64)).toNat - (m.getMem (regs .x10 + 8#64)).toNat) _ _
      ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
        by dsimp only [Tactic.rf]; omega, by omega, by omega, hq8, hwq.resolve_left (Ne.symm hne)⟩

end Rv64mc.Proof.Field.SumChainT

/-- info: 'Rv64mc.Proof.Field.SumChainT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.SumChainT.total
