/-
  Rv64mc.Proof.Multilinear.StackOffsetsT

  `verifier::multilinear::stack_offsets(sizes)` is total: called with the result's slot (`a0`, 32 bytes: the offsets'
  `Vec<u64>` header, then the `usize` log) and the sizes (`a1`, `a2`, words), it returns the offsets a vector of the
  sizes' length (`CloneT.ClonePostT`: `VecT`, its buffer fresh unless empty), writing only the result's 32 bytes, or
  the run ends with the guest's abort (`AbortStop`) where `try_allocate_in` or `handle_error` does. A safety-only
  contract: the class-C `StackOffsets.spec` (the offsets and the log `Model.stackOffsetsRust` gives) is not proved.

  The precondition asks the result's slot a caller's (`Owned`), in a window and 8-byte aligned, and the sizes a
  block allocated before (`BufT`). Every load and store is at a cursor that stays inside the sizes or the offsets'
  fresh block; the code's one bounds check (`offsets[i]`, `i` below the sizes' length) never fails, but its branch
  is closed by `panic_bounds_check`'s contract all the same.

  The body is cut at the maximum's loop head (instruction 56), at 66 (the largest size found), at the outer loop's
  head (78, one pass per size from the largest down to `0`, its measure that size), at the inner loop's head (104,
  over the sizes), at 74 (the outer loop's test), at 116 (after the loops) and at 210 (the result's stores).

  ## Main definitions

  * `PreT`, `SpecT`, `Slots`, `MemOk`, `Base`, `Common`, `Inv74`, `IInv`, `OInv`, `Inv66`, `MInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.TryAllocateInT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.VecHdrT
import Rv64mc.Spec.Whir.Basic
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.StackOffsets

namespace Rv64mc.Proof.Multilinear.StackOffsetsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.TryAllocateInT (TryAllocSpecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT)
open Rv64mc.Gen.Verifier.Multilinear.StackOffsets (Link tmpl)

/-- The total precondition: the result's 32 bytes a caller's, in a window and 8-byte aligned; the sizes (`a1`, `a2`)
    a block allocated before (`BufT`). -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) 32 ∧ InWin env (regs .x10) 32 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x12) (regs .x11) 8

/-- **The total contract of `stack_offsets`**: the offsets a vector's of the sizes' length, its buffer fresh unless
    empty; the result's 32 bytes written. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (ClonePostT env 8) (Spec.Whir.SretOut 32) AbortStop

/-- The prologue's four saved words in `M`, at `top - 8` down to `top - 32`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18

/-- What every part keeps of memory: the slots, the frame, the static data, the code. -/
def MemOk (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (M : MachineState) : Prop :=
  Slots M top ret regs ∧ env.Frame top (Spec.Whir.SretOut 32 regs m) m M ∧ env.Static M ∧ M.code = m.code

/-- What the return needs: the stack pointer, the registers never written, `MemOk`. -/
def Base (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (R : Reg → Word) (M : MachineState) :
    Prop :=
  R .x2 = top + 18446744073709551552#64 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧
    R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧
    R .x27 = regs .x27 ∧ MemOk env m top ret regs M

/-- What every part keeps: `Base`, the arguments in the saved registers, the capacity `n` in `x10`, the offsets'
    block `P` of `n` words fresh since the entry unless `n = 0`. -/
def Common (env : Env) (m : MachineState) (top ret P : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Base env m top ret regs R M ∧ R .x8 = regs .x12 ∧ R .x9 = regs .x10 ∧ R .x10 = regs .x12 ∧ R .x18 = regs .x11 ∧
    ((regs .x12).toNat = 0 ∨ (0x10000000 ≤ P.toNat ∧ (env.next m).toNat ≤ P.toNat ∧
      P.toNat + 8 * (regs .x12).toNat ≤ (env.next M).toNat ∧ P.toNat % 8 = 0))

/-- The slots kept by a memory that agrees from `top - 32` up to `top`. -/
theorem slots_keep {M X : MachineState} {top ret : Word} {regs : Reg → Word} (hlim : 64 ≤ top.toNat)
    (hk : ∀ a : Word, top.toNat - 32 ≤ a.toNat → a.toNat < top.toNat → X.getMem a = M.getMem a)
    (hsl : Slots M top ret regs) : Slots X top ret regs := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 32 → X.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := Runtime.CloneT.toNat_add_neg (t := top) hc (by omega)
      exact hk _ (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨s1, s2, s3, s4⟩ := hsl
  exact ⟨(es _ 8 rfl (by omega) (by omega)).trans s1, (es _ 16 rfl (by omega) (by omega)).trans s2,
    (es _ 24 rfl (by omega) (by omega)).trans s3, (es _ 32 rfl (by omega) (by omega)).trans s4⟩

/-- **One store into the frame's `out`**, a word apart from the slots and in a window: the slots, the frame,
    `env.Static`, the code and `NEXT` kept. -/
theorem out_store {env : Env} {m M : MachineState} {top ret b v : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (hb : out b) (hwin : InWin env b 8)
    (hsep : b.toNat + 8 ≤ top.toNat - 32 ∨ top.toNat ≤ b.toNat) (hF : env.Frame top out m M) (hS : env.Static M)
    (hc : M.code = m.code) (hsl : Slots M top ret regs) :
    Slots (M.setMem b v) top ret regs ∧ env.Frame top out m (M.setMem b v) ∧ env.Static (M.setMem b v) ∧
      (M.setMem b v).code = m.code ∧ env.next (M.setMem b v) = env.next M := by
  have hlay := env.layout
  have hn : b ≠ env.nextAddr := fun e => by rw [e] at hwin; unfold InWin at hwin; omega
  refine ⟨slots_keep (by omega) (fun a h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_out hF hb hn, Tactic.static_store hS (by unfold InWin at hwin; omega),
    by rw [MachineState.code_setMem, hc], Tactic.next_setMem hn⟩

/-- **The result's four stores** at `h`, a caller's 32 bytes in a window: `Base` kept, the header's three words
    read back. -/
theorem hdr4 {env : Env} {m M : MachineState} {top ret h v0 v1 v2 v3 : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (hh : regs .x10 = h) (hown : env.Owned m top h 32)
    (hwin : InWin env h 32) (hB : MemOk env m top ret regs M) :
    MemOk env m top ret regs ((((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).setMem (h + 24#64) v3) ∧
      env.next ((((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).setMem (h + 24#64) v3) = env.next M ∧
      ((((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).setMem (h + 24#64) v3).getMem h = v0 ∧
      ((((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).setMem (h + 24#64) v3).getMem (h + 8#64) = v1 ∧
      ((((M.setMem h v0).setMem (h + 8#64) v1).setMem (h + 16#64) v2).setMem (h + 24#64) v3).getMem (h + 16#64) =
        v2 := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hB
  have h32 := hown.2
  have hnm := hF.1
  have hnM := hF.2.1
  have e8 : (h + 8#64).toNat = h.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (h + 16#64).toNat = h.toNat + 16 := toNat_add_ofNat (by omega)
  have e24 : (h + 24#64).toNat = h.toNat + 24 := toNat_add_ofNat (by omega)
  have hsep : ∀ k, k ≤ 24 → h.toNat + k + 8 ≤ top.toNat - 32 ∨ top.toNat ≤ h.toNat + k := fun k hk => by
    rcases hown.1 with h1 | h1 <;> omega
  have hout : ∀ k : Nat, k ≤ 24 → ∀ b : Word, b.toNat = h.toNat + k → Spec.Whir.SretOut 32 regs m b :=
    fun k hk b hb => by show InRange (regs .x10) 32 b; unfold InRange; rw [hh]; omega
  have hw : ∀ k : Nat, k ≤ 24 → ∀ b : Word, b.toNat = h.toNat + k → InWin env b 8 :=
    fun k hk b hb => Runtime.MemsetT.InWin.sub hwin (by omega) (by omega)
  obtain ⟨s1, f1, t1, c1, n1⟩ := out_store (v := v0) hlim (hout 0 (by omega) h rfl) (hw 0 (by omega) h rfl)
    (hsep 0 (by omega)) hF hS hc hsl
  obtain ⟨s2, f2, t2, c2, n2⟩ := out_store (v := v1) hlim (hout 8 (by omega) _ e8) (hw 8 (by omega) _ e8)
    (by rw [e8]; exact hsep 8 (by omega)) f1 t1 c1 s1
  obtain ⟨s3, f3, t3, c3, n3⟩ := out_store (v := v2) hlim (hout 16 (by omega) _ e16) (hw 16 (by omega) _ e16)
    (by rw [e16]; exact hsep 16 (by omega)) f2 t2 c2 s2
  obtain ⟨s4, f4, t4, c4, n4⟩ := out_store (v := v3) hlim (hout 24 (by omega) _ e24) (hw 24 (by omega) _ e24)
    (by rw [e24]; exact hsep 24 (by omega)) f3 t3 c3 s3
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  refine ⟨⟨s4, f4, t4, c4⟩, by rw [n4, n3, n2, n1], ?_, ?_, ?_⟩
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]

set_option rv_sym.heap true in
/-- **The return**, from instruction 210: the result's four words, then the saved registers. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top P : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 8) (Spec.Whir.SretOut 32) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + 64 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hown : env.Owned m top (regs .x10) 32) (hwin : InWin env (regs .x10) 32) (hal : (regs .x10).toNat % 8 = 0)
    (hn8 : (regs .x12).toNat * 8 < 2 ^ 63) :
    ∀ R M, Common env m top ret P regs R M → R .x12 = P →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 210, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hP
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hM⟩, -, -, -, -, hbuf⟩ := id hI
  obtain ⟨hM', hn', r0, r8, r16⟩ := hdr4 (v0 := regs .x12) (v1 := R .x12) (v2 := regs .x12) (v3 := R .x11) (by omega)
    rfl hown hwin hM
  obtain ⟨⟨s1, s2, s3, s4⟩, hF, hS, hc⟩ := hM'
  have hPost : ∀ r, ClonePostT env 8 regs m r ((((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) (R .x12)).setMem
      (regs .x10 + 16#64) (regs .x12)).setMem (regs .x10 + 24#64) (R .x11)) := fun r =>
    Runtime.VecHdrT.post_ok (Runtime.MemsetT.InWin.sub hwin (Nat.le_refl _) (by omega)) hal r0 r8 r16
      (by rcases hbuf with h0 | ⟨h1, h2, h3, h4⟩
          · exact .inl h0
          · exact .inr ⟨by rw [hP]; exact h1, by rw [hP]; exact h2, by rw [hn', hP]; omega, by rw [hP]; exact h4⟩) hn8
  rv_introT hI
  rv_symT hp with [_hL]
  all_goals first | exact (hPost (fun _ => 0#64)).1.2.1.2.2.1 |
    exact (hPost (fun _ => 0#64)).1.2.1.2.2.2

set_option rv_sym.heap true in
/-- **After the loops**, from instruction 116: the `log2` of the cursor, the result's four words, the return. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top P : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 8) (Spec.Whir.SretOut 32) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + 64 ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hown : env.Owned m top (regs .x10) 32) (hwin : InWin env (regs .x10) 32) (hal : (regs .x10).toNat % 8 = 0)
    (hn8 : (regs .x12).toNat * 8 < 2 ^ 63) :
    ∀ R M, Common env m top ret P regs R M → R .x12 = P →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 116, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI hP
  have hlay := env.layout
  obtain ⟨hB, -, -, -, -, hbuf⟩ := id hI
  rv_introT hI
  rv_symT hp stop [210] with [hL]
  all_goals
    exact exit hp hL hk hstk hW h16 hown hwin hal hn8 _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hB.2.2.2.2.2.2.2.2.2.2⟩,
      rfl, rfl, rfl, rfl, hbuf⟩ hP

/-- Word `j` of a block `B` of `c` words below `NEXT`, `j` below `c`: in a window, aligned. -/
theorem elem_ok {env : Env} {M : MachineState} {B X : Word} {j c : Nat} (hB1 : 0x10000000 ≤ B.toNat)
    (hB2 : B.toNat + 8 * c ≤ (env.next M).toNat) (hB8 : B.toNat % 8 = 0)
    (hnx : (env.next M).toNat ≤ env.heapEnd.toNat) (hend : env.heapEnd.toNat ≤ 0x78000000)
    (hX : X.toNat = B.toNat + 8 * j) (hj : j < c) : inWindow X 8 = true ∧ X.toNat % 8 = 0 := by
  rw [inWindow_iff, hX]
  omega

/-- One store into a block allocated since the entry keeps `MemOk` and `NEXT`. -/
theorem store_ok {env : Env} {m M : MachineState} {top ret a v : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (hM : MemOk env m top ret regs M)
    (ha1 : (env.next m).toNat ≤ a.toNat) (ha2 : a.toNat + 8 ≤ (env.next M).toNat) :
    MemOk env m top ret regs (M.setMem a v) ∧ env.next (M.setMem a v) = env.next M := by
  have hlay := env.layout
  obtain ⟨hsl, hF, hS, hc⟩ := hM
  have hnM := hF.2.1
  have hne : a ≠ env.nextAddr := fun e => by rw [e] at ha2; omega
  exact ⟨⟨slots_keep (by omega) (fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega) hsl,
    Tactic.frame_fresh hF rfl ha1 (by omega), Tactic.static_store hS (.inl (by omega)),
    by rw [MachineState.code_setMem, hc]⟩, Tactic.next_setMem hne⟩

/-- The registers at instruction 74, the outer loop's test, after the pass over size `s`. -/
def Inv74 (env : Env) (m : MachineState) (top ret P : Word) (regs : Reg → Word) (s : Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret P regs R M ∧ R .x12 = P ∧ R .x13 = regs .x12 <<< 3 ∧ R .x15 = 1#64 ∧ R .x16 = s

/-- The inner loop's head (instruction 104) in the pass over size `s`, with `k + 1` sizes left: `x7` at size `j`,
    `x6` at offset `j`, `x5` the bytes left, `x11 = j`. -/
def IInv (env : Env) (m : MachineState) (top ret P : Word) (regs : Reg → Word) (s : Word) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  Inv74 env m top ret P regs s R M ∧ ∃ j, j + k + 1 = (regs .x12).toNat ∧ (R .x7).toNat = (regs .x11).toNat + 8 * j ∧
    (R .x6).toNat = P.toNat + 8 * j ∧ (R .x5).toNat = 8 * (k + 1) ∧ (R .x11).toNat = j

set_option rv_sym.heap true in
/-- **The inner loop**, from its head to the outer loop's test. -/
theorem inner {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needP : Nat} (hnP : 64 + needP ≤ need)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top P s : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hA : BufT env m (regs .x12) (regs .x11) 8)
    (hn0 : (regs .x12).toNat ≠ 0)
    (hk : ∀ R M, Inv74 env m top ret P regs s R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 74, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, IInv env m top ret P regs s k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 104, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (IInv env m top ret P regs s) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨⟨⟨-, -, -, -, -, -, -, -, -, -, hM⟩, -, -, -, -, hbuf⟩, -, -, -, -⟩, j, hj, hx7, hx6, hx5, hx11⟩ := id hI
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hW1 := hW.heapEnd_le
  have hge := hW.next_ge
  obtain ⟨hP1, hP2, hP3, hP8⟩ := hbuf.resolve_left hn0
  obtain ⟨a1, a2, a3⟩ : 0x10000000 ≤ (regs .x11).toNat ∧
      (regs .x11).toNat + 8 * (regs .x12).toNat ≤ (env.next m).toNat ∧ (regs .x11).toNat % 8 = 0 := by
    rcases hA with h | ⟨h1, h2, h3⟩
    · exact absurd h hn0
    · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
  have w7 := elem_ok (j := j) (c := (regs .x12).toNat) a1 a2 a3 hnx hW1 hx7 (by omega)
  have w6 := elem_ok (j := j) (c := (regs .x12).toNat) hP1 hP3 hP8 hnM hW1 hx6 (by omega)
  obtain ⟨hM1, hn1⟩ := store_ok (a := R .x6) (v := R .x14) (by omega) hM (by omega) (by omega)
  have h8 := Runtime.CloneT.toNat_add_neg (t := R .x5) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  rv_introT hI
  rv_symT hp stop [104, 74, 94] with [hL] using [hpb]
  all_goals rv_symT hp stop [104, 74] with [hL]
  all_goals
    have hb1 : (regs .x12).toNat = 0 ∨ (0x10000000 ≤ P.toNat ∧ (env.next m).toNat ≤ P.toNat ∧
        P.toNat + 8 * (regs .x12).toNat ≤ (env.next (M.setMem (R .x6) (R .x14))).toNat ∧ P.toNat % 8 = 0) :=
      .inr ⟨hP1, hP2, by rw [hn1]; exact hP3, hP8⟩
  · exact hk _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩, rfl, rfl, rfl, rfl⟩
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h8]; simp; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩,
      rfl, rfl, rfl, rfl⟩, j + 1, by omega, ?_, ?_, ?_, ?_⟩ <;> simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [h8]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
  · exact hk _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM1⟩, rfl, rfl, rfl, rfl, hb1⟩, rfl, rfl, rfl, rfl⟩
  · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h8]; simp; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM1⟩, rfl, rfl, rfl, rfl, hb1⟩,
      rfl, rfl, rfl, rfl⟩, j + 1, by omega, ?_, ?_, ?_, ?_⟩ <;> simp only [Tactic.rf]
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
    · rw [h8]; omega
    · rw [toNat_add_ofNat (by omega)]; omega

/-- The outer loop's head (instruction 78), the pass over size `x11 = k` next. -/
def OInv (env : Env) (m : MachineState) (top ret P : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret P regs R M ∧ R .x12 = P ∧ R .x13 = regs .x12 <<< 3 ∧ R .x15 = 1#64 ∧ (R .x11).toNat = k

set_option rv_sym.heap true in
/-- **The outer loop**, one pass per size from the largest down to `0`, from its head to the return. -/
theorem outer {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needP : Nat} (hnP : 64 + needP ≤ need)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top P : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (ClonePostT env 8) (Spec.Whir.SretOut 32) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hA : BufT env m (regs .x12) (regs .x11) 8)
    (hown : env.Owned m top (regs .x10) 32) (hwin : InWin env (regs .x10) 32) (hal : (regs .x10).toNat % 8 = 0)
    (hn8 : (regs .x12).toNat * 8 < 2 ^ 63) :
    ∀ k R M, OInv env m top ret P regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env m top ret P regs) fun k R M hI ih => ?_
  have hlay := env.layout
  have h74 : ∀ R' M', Inv74 env m top ret P regs (R .x11) R' M' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 74, ret, top⟩ :: rest, R', M'⟩ := by
    intro R' M' hJ
    obtain ⟨hC, -, -, -, -⟩ := id hJ
    have hM := hC.1.2.2.2.2.2.2.2.2.2.2
    have hbuf := hC.2.2.2.2.2
    have hx := hI.2.2.2.2
    rv_introT hJ
    rv_symT hp stop [78, 116] with [hL]
    · exact fin hp hL hk (by omega) hW h16 hown hwin hal hn8 _ _
        ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩ rfl
    · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by simp; omega))
      refine ih (k - 1) _ _ (by omega) ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩,
        rfl, rfl, rfl, ?_⟩
      simp only [Tactic.rf]
      rw [Runtime.CloneT.toNat_add_neg (c := 18446744073709551615#64) (k := 1) rfl (by omega)]
      omega
  obtain ⟨hC, -, -, -, -⟩ := id hI
  have hM := hC.1.2.2.2.2.2.2.2.2.2.2
  have hbuf := hC.2.2.2.2.2
  have hs : (regs .x12 <<< 3).toNat = 8 * (regs .x12).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  rv_introT hI
  rv_symT hp stop [74, 104] with [hL]
  · exact h74 _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩, rfl, rfl, rfl, rfl⟩
  · have hn0 : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    refine inner hp hL hnP hpb hstop hstk hnx hW h16 hA hn0 h74 ((regs .x12).toNat - 1) _ _
      ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩, rfl, rfl, rfl, rfl⟩, 0,
        by omega, ?_, ?_, ?_, ?_⟩ <;> simp only [Tactic.rf]
    · omega
    · omega
    · rw [hs]; omega
    · rfl

/-- At instruction 66, the largest size in `x11`: the offsets' pointer still in its slot. -/
def Inv66 (env : Env) (m : MachineState) (top ret P : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Common env m top ret P regs R M ∧ M.getMem (top + 18446744073709551576#64) = P ∧ R .x13 = regs .x12 <<< 3

set_option rv_sym.heap true in
/-- **From instruction 66**, the largest size found, to the outer loop's head. -/
theorem mid {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top P : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hstk : env.stackLimit.toNat + 64 ≤ top.toNat) (hW : Windows env top m)
    (h16 : top.toNat % 16 = 0)
    (hk : ∀ k R M, OInv env m top ret P regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Inv66 env m top ret P regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨hC, -, -⟩ := id hI
  have hM := hC.1.2.2.2.2.2.2.2.2.2.2
  have hbuf := hC.2.2.2.2.2
  have hlay := env.layout
  have e40 := Runtime.CloneT.toNat_add_neg (t := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have hw40 : inWindow (top + 18446744073709551576#64) 8 = true := by
    have := hW.top_le
    have := hW.nextAddr_ge
    rw [inWindow_iff, e40]; omega
  have ha40 : (top + 18446744073709551576#64).toNat % 8 = 0 := by rw [e40]; omega
  rv_introT hI
  rv_symT hp stop [78] with [_hL]
  exact hk _ _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩, hI_23, rfl, rfl,
    rfl⟩

/-- The maximum's loop head (instruction 56) with `k + 1` sizes left after `x12`, at size `j + 1`. -/
def MInv (env : Env) (m : MachineState) (top ret P : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  Inv66 env m top ret P regs R M ∧ R .x14 = regs .x11 + regs .x12 <<< 3 ∧
    ∃ j, j + k + 2 = (regs .x12).toNat ∧ (R .x12).toNat = (regs .x11).toNat + 8 + 8 * j

set_option rv_sym.heap true in
/-- **The maximum's loop**, from its head to instruction 66. -/
theorem maxLoop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top P : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hW : Windows env top m)
    (hA : BufT env m (regs .x12) (regs .x11) 8)
    (hk : ∀ R M, Inv66 env m top ret P regs R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 66, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, MInv env m top ret P regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 56, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (MInv env m top ret P regs) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨hC, hP, hx13⟩, hx14, j, hj, hx12⟩ := id hI
  have hM := hC.1.2.2.2.2.2.2.2.2.2.2
  have hbuf := hC.2.2.2.2.2
  have hW1 := hW.heapEnd_le
  obtain ⟨a1, a2, a3⟩ : 0x10000000 ≤ (regs .x11).toNat ∧
      (regs .x11).toNat + 8 * (regs .x12).toNat ≤ (env.next m).toNat ∧ (regs .x11).toNat % 8 = 0 := by
    rcases hA with h | ⟨h1, h2, h3⟩
    · omega
    · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
  have w12 := elem_ok (j := j + 1) (c := (regs .x12).toNat) a1 a2 a3 hnx hW1 (by rw [hx12]; omega) (by omega)
  have hs : (regs .x12 <<< 3).toNat = 8 * (regs .x12).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e14 : (regs .x11 + regs .x12 <<< 3).toNat = (regs .x11).toNat + 8 * (regs .x12).toNat := by
    rw [BitVec.toNat_add, hs]; omega
  have e12 : (R .x12 + 8#64).toNat = (R .x12).toNat + 8 := toNat_add_ofNat (by omega)
  rv_introT hI
  rv_symT hp stop [56, 66, 52] with [_hL]
  all_goals rv_symT hp stop [56, 66] with [_hL]
  all_goals clear hc_1
  iterate 2
    · exact hk _ _ ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩, hP, rfl⟩
    · have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [e12, e14]; omega))
      exact ih (k - 1) _ _ (by omega) ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hM⟩, rfl, rfl, rfl, rfl, hbuf⟩,
        hP, rfl⟩, rfl, j + 1, by omega, by simp only [Tactic.rf]; rw [e12]; omega⟩

/-- The prologue's four saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)

/-- The prologue's stores: in the frame, `env.Static`, `NEXT` and the code kept, the slots holding the saved
    words. -/
theorem saved_ok {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hlim : env.stackLimit.toNat + 64 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    env.Frame top out m (saved m top ret regs) ∧ env.Static (saved m top ret regs) ∧
      env.next (saved m top ret regs) = env.next m ∧ Slots (saved m top ret regs) top ret regs ∧
      (saved m top ret regs).code = m.code := by
  have es : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 64 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e1 := es 18446744073709551608#64 8 rfl (by omega)
  have e2 := es 18446744073709551600#64 16 rfl (by omega)
  have e3 := es 18446744073709551592#64 24 rfl (by omega)
  have e4 := es 18446744073709551584#64 32 rfl (by omega)
  refine ⟨?_, ?_, ?_, ?_, by simp only [saved, MachineState.code_setMem]⟩
  · simp only [saved]
    repeat (first | exact Env.Frame.refl hnx | refine Tactic.frame_slot ?_ (by omega) (by omega))
  · simp only [saved]
    repeat (first | exact hS | refine Env.static_setMem_stack ?_ (by omega))
  · simp only [saved]
    repeat rw [Env.next_setMem_stack (by omega)]
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4] at h'; omega)])

theorem cap_slot (top : Word) : taCapAt (top + 18446744073709551560#64) = top + 18446744073709551568#64 := by
  unfold taCapAt; rw [BitVec.add_assoc]; rfl

theorem ptr_slot (top : Word) : taPtrAt (top + 18446744073709551560#64) = top + 18446744073709551576#64 := by
  unfold taPtrAt; rw [BitVec.add_assoc]; rfl

set_option rv_sym.heap true in
/-- **`stack_offsets` is total**, with 64 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needT needP needH : Nat} (hnT : 64 + needT ≤ need) (hnP : 64 + needP ≤ need) (hnH : 64 + needH ≤ need)
    (hta : TryAllocSpecT env p L.tryAllocateInInVerifier.idx needT)
    (hpb : Aborts env p L.panicBoundsCheck.idx needP)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  rv_autoT hp stop [56, 66] with [hL] using [hta, hhe]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_6
    have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
    obtain ⟨hF0, hS0, hn0, hsl0, hc0⟩ := saved_ok (out := Spec.Whir.SretOut 32 regs m) (ret := ret) (regs := regs)
      hlim hpre_5 hpre_4
    simp only [saved] at hF0 hS0 hn0 hsl0 hc0
    have t64 : (top + 18446744073709551552#64).toNat = top.toNat - 64 :=
      Runtime.CloneT.toNat_add_neg (c := 18446744073709551552#64) (k := 64) rfl (by omega)
    have t56 : (top + 18446744073709551560#64).toNat = top.toNat - 56 :=
      Runtime.CloneT.toNat_add_neg (c := 18446744073709551560#64) (k := 56) rfl (by omega)
    have hF1 := hF0.trans hret1_14 (by rw [t64]; omega) fun b hb => Or.inl (by
      change InRange (top + 18446744073709551560#64) tryAllocBytes b at hb
      unfold InRange tryAllocBytes at hb; rw [t56] at hb; omega)
    have hsl1 : Slots m1 top ret regs := slots_keep (by omega)
      (fun a h1 h2 => keep1_1 a (BitVec.le_def.2 (by rw [t64]; omega)) fun hb => by
        change InRange (top + 18446744073709551560#64) tryAllocBytes a at hb
        unfold InRange tryAllocBytes at hb; rw [t56] at hb; omega) hsl0
    obtain ⟨hn8, hok⟩ := hret1_16 hc_1
    rw [show (8#64 : Word).toNat = 8 from rfl, cap_slot, ptr_slot] at hok
    rw [show (8#64 : Word).toNat = 8 from rfl] at hn8
    have hge := hpre_12.next_ge
    have hcap : m1.getMem (top + 18446744073709551568#64) = regs .x12 := by
      rcases hok with ⟨h0, h1⟩ | ⟨-, h1, -⟩
      · rw [h1]; exact (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega) : (0#64 : Word) = regs .x12)
      · exact h1
    have hbuf : (regs .x12).toNat = 0 ∨ (0x10000000 ≤ (m1.getMem (top + 18446744073709551576#64)).toNat ∧
        (env.next m).toNat ≤ (m1.getMem (top + 18446744073709551576#64)).toNat ∧
        (m1.getMem (top + 18446744073709551576#64)).toNat + 8 * (regs .x12).toNat ≤ (env.next m1).toNat ∧
        (m1.getMem (top + 18446744073709551576#64)).toNat % 8 = 0) := by
      rcases hok with ⟨h0, -⟩ | ⟨-, -, hfr, h8⟩
      · exact .inl (by omega)
      · unfold Env.Fresh at hfr; rw [hn0] at hfr; exact .inr ⟨by omega, hfr.1, by omega, h8⟩
    have hc1 := hret1_18.trans hc0
    have hO := outer (P := m1.getMem (top + 18446744073709551576#64)) hp hL hnP hpb hk hstop hpre_3 hpre_5
      hpre_12 hpre_11 hpre_10 ⟨hpre_6, hpre_7⟩ hpre_8 hpre_9 hn8
    have hmid := mid hp hL hlim hpre_12 hpre_11 hO
    have hmax := maxLoop hp hL hpre_5 hpre_12 hpre_10 hmid
    have hI66 : ∀ R, R .x2 = top + 18446744073709551552#64 → R .x19 = regs .x19 → R .x20 = regs .x20 →
        R .x21 = regs .x21 → R .x22 = regs .x22 → R .x23 = regs .x23 → R .x24 = regs .x24 → R .x25 = regs .x25 →
        R .x26 = regs .x26 → R .x27 = regs .x27 → R .x8 = regs .x12 → R .x9 = regs .x10 →
        R .x10 = regs .x12 → R .x18 = regs .x11 → R .x13 = regs .x12 <<< 3 →
        Inv66 env m top ret (m1.getMem (top + 18446744073709551576#64)) regs R m1 :=
      fun R h2 h19 h20 h21 h22 h23 h24 h25 h26 h27 h8 h9 h10 h18 h13 =>
        ⟨⟨⟨h2, h19, h20, h21, h22, h23, h24, h25, h26, h27, hsl1, hF1, hret1_15, hc1⟩, h8, h9, h10, h18, hbuf⟩, rfl, h13⟩
  · exact hmid _ _ (hI66 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcap rfl rfl)
  all_goals
    have hn0 : (regs .x12).toNat ≠ 0 := by
      first | exact fun h => hc_2 (BitVec.eq_of_toNat_eq h) | exact fun h => hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨a1, a2, a3⟩ : 0x10000000 ≤ (regs .x11).toNat ∧
        (regs .x11).toNat + 8 * (regs .x12).toNat ≤ (env.next m).toNat ∧ (regs .x11).toNat % 8 = 0 := by
      rcases hpre_10 with h | ⟨h1, h2, h3⟩
      · exact absurd h hn0
      · unfold Env.Live at h2; exact ⟨h1, by omega, h3⟩
  · exact (elem_ok (j := 0) a1 a2 a3 hpre_5 hpre_12.heapEnd_le (by omega) (Nat.pos_of_ne_zero hn0)).1
  · exact (elem_ok (j := 0) a1 a2 a3 hpre_5 hpre_12.heapEnd_le (by omega) (Nat.pos_of_ne_zero hn0)).2
  · exact hmid _ _ (hI66 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcap rfl rfl)
  · have hn1 : (regs .x12).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq h)
    refine hmax ((regs .x12).toNat - 2) _ _ ⟨hI66 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcap rfl rfl, rfl, 0,
      by omega, ?_⟩
    simp only [Tactic.rf]; rw [toNat_add_ofNat (by omega)]

end Rv64mc.Proof.Multilinear.StackOffsetsT

/-- info: 'Rv64mc.Proof.Multilinear.StackOffsetsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.StackOffsetsT.total
