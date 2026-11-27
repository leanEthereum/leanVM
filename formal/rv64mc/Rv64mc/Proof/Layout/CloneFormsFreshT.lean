/-
  Rv64mc.Proof.Layout.CloneFormsFreshT

  `<Vec<Form> as Clone>::clone`'s total contract with a stronger postcondition than `CloneFormsT.SpecT`'s: besides
  `CloneFormsT.PostT`, every cloned `Form`'s terms' block is allocated by the call (`FreshTermsT`), and each clone's
  capacity and length are its source's length (`CapsT`). A caller that writes into a block allocated before the call
  and then reads the clone (`from_elem::<Vec<Form>>`, which stores each clone's header into its result's block)
  needs the first: `FormsT` reads the `Form`s' terms' blocks, which `CloneFormsT.PostT` places only below `NEXT`. A
  caller that then writes into a clone's `Form`s (`verify_bus_balance` through `add_scaled`, whose `OutT` is the
  `Form`'s buffer by its capacity) needs the second. The proof is `CloneFormsT`'s: its parts that end in the return
  (`exit`, `join`, `back`, `after`, `inner`, `outer`, `total`) are restated here over the stronger postcondition,
  with `CloneFormsT`'s lemmas and its invariants each with `CapsT` of the clones so far (`OInvC`, `IInvC`, `TInvC`);
  `exit` derives `FreshTermsT` from the invariant `CloneFormsT.DoneT` it already holds (each terms' block between
  the result's block and `NEXT`), and `join` adds the new clone to `CapsT` (`CapsT.join`: the code stores the
  source's length as both).

  ## Main definitions

  * `FreshTermsT`, `CapsT`, `PostT`, `SpecT`, `OInvC`, `IInvC`, `TInvC`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.CloneFormsT

namespace Rv64mc.Proof.Layout.CloneFormsFreshT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.CloneT (ClonePostT CloneSpecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq post_ok)
open Rv64mc.Gen.Alloc.Vec.VecForm.AsClone.Clone (Link tmpl d_c8_d6dfd6bc_words d_c8_51ab739d_words)
open Rv64mc.Proof.Layout.CloneFormsT hiding PostT SpecT exit join back after inner outer total

/-- **The `n` `Form`s from `q` have their terms' blocks allocated between `m` and `m'`** (or no terms). -/
def FreshTermsT (env : Env) (m m' : MachineState) (q : Word) (n : Nat) : Prop :=
  ∀ i, i < n → (vecLen m' (q + BitVec.ofNat 64 (24 * i))).toNat = 0 ∨
    ((env.next m).toNat ≤ (vecPtr m' (q + BitVec.ofNat 64 (24 * i))).toNat ∧
      (vecPtr m' (q + BitVec.ofNat 64 (24 * i))).toNat + 40 * (vecLen m' (q + BitVec.ofNat 64 (24 * i))).toNat ≤
        (env.next m').toNat)

/-- **The `n` `Form`s from `q` in `m'` have the lengths of the `n` from `src` in `m`**, each its capacity and its
    length. -/
def CapsT (m m' : MachineState) (src q : Word) (n : Nat) : Prop :=
  ∀ i, i < n → vecCap m' (q + BitVec.ofNat 64 (24 * i)) = vecLen m (src + BitVec.ofNat 64 (24 * i)) ∧
    vecLen m' (q + BitVec.ofNat 64 (24 * i)) = vecLen m (src + BitVec.ofNat 64 (24 * i))

/-- The total postcondition: `CloneFormsT.PostT`, the clones' terms' blocks fresh, and each clone's capacity and
    length its source's length. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  CloneFormsT.PostT env regs m r' m' ∧ FreshTermsT env m m' (vecPtr m' (regs .x10)) (regs .x12).toNat ∧
    CapsT m m' (regs .x11) (vecPtr m' (regs .x10)) (regs .x12).toNat

/-- **The total contract of `<Vec<Form> as Clone>::clone`**, with the clones' terms' blocks fresh. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (CloneFormsT.PreT env) (PostT env) SretVecOut AbortStop

/-- The stronger contract gives `CloneFormsT`'s. -/
theorem SpecT.weaken {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : SpecT env p i need) :
    CloneFormsT.SpecT env p i need :=
  Isa.TContract.mono h (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ _ _ ⟨⟨ha, hf, hs, hp⟩, hc⟩ => ⟨⟨ha, hf, hs, hp.1⟩, hc⟩) fun _ _ _ _ _ _ _ hst => hst

/-! ## The clones' capacities -/

/-- **`CapsT` is kept** by a memory agreeing on the first `j` headers. -/
theorem CapsT.keep {m M M' : MachineState} {src D : Word} {j : Nat} (h : CapsT m M src D j)
    (hD : D.toNat + 24 * j < 2 ^ 64)
    (hk : ∀ b : Word, D.toNat ≤ b.toNat → b.toNat < D.toNat + 24 * j → M'.getMem b = M.getMem b) :
    CapsT m M' src D j := fun i hi => by
  have e : (D + BitVec.ofNat 64 (24 * i)).toNat = D.toNat + 24 * i := toNat_add_ofNat (by omega)
  have e16 : (D + BitVec.ofNat 64 (24 * i) + 16#64).toNat = D.toNat + 24 * i + 16 := by
    rw [toNat_add_ofNat (by omega), e]
  refine ⟨?_, ?_⟩
  · rw [vecCap_eq M', hk _ (by omega) (by omega), ← vecCap_eq M]; exact (h i hi).1
  · rw [vecLen_eq M', hk _ (by omega) (by omega), ← vecLen_eq M]; exact (h i hi).2

/-- **A store apart from the first `j` headers keeps `CapsT`.** -/
theorem CapsT.setMem {m M : MachineState} {src D a v : Word} {j : Nat} (h : CapsT m M src D j)
    (hD : D.toNat + 24 * j < 2 ^ 64) (ha : a.toNat < D.toNat ∨ D.toNat + 24 * j ≤ a.toNat) :
    CapsT m (M.setMem a v) src D j :=
  h.keep hD fun b h1 h2 => MachineState.getMem_setMem_ne fun e => by rw [e] at h1 h2; omega

/-- **The join's three stores** `(c, P, L)` at `D + 24 j`, `c` and `L` the source's length: `j + 1` clones. -/
theorem CapsT.join {m M : MachineState} {src D A c P L : Word} {j : Nat} (h : CapsT m M src D j)
    (hD : D.toNat + 24 * (j + 1) < 2 ^ 64) (hA : A = D + BitVec.ofNat 64 (24 * j)) (hc : c.toNat = L.toNat)
    (hL : L = vecLen m (src + BitVec.ofNat 64 (24 * j))) :
    CapsT m (((M.setMem A c).setMem (A + 8#64) P).setMem (A + 16#64) L) src D (j + 1) := by
  have eA : A.toNat = D.toNat + 24 * j := by rw [hA]; exact toNat_add_ofNat (by omega)
  have e8 : (A + 8#64).toNat = A.toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (A + 16#64).toNat = A.toNat + 16 := toNat_add_ofNat (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
  · refine (h.keep (by omega) fun b h1 h2 => ?_) i hi
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega))]
  · rw [hi, ← hA, ← hL, vecCap_eq, vecLen_eq, MachineState.getMem_setMem_eq,
      MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
    exact ⟨BitVec.eq_of_toNat_eq hc, rfl⟩

theorem addr_eq {a s : Word} {j : Nat} (ha : a.toNat = s.toNat + 24 * j) : a = s + BitVec.ofNat 64 (24 * j) :=
  BitVec.eq_of_toNat_eq (by rw [ha, toNat_add_ofNat (by have := a.isLt; omega)])

/-- `OInv`, the clones so far with their sources' lengths. -/
def OInvC (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  OInv env m top ret regs D k R M ∧ CapsT m M (regs .x11) D ((regs .x12).toNat - (k + 1))

/-- `IInv`, the clones so far with their sources' lengths. -/
def IInvC (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : Word) (H j k : Nat) (a T : Word)
    (q : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  IInv env m top ret regs D H j k a T q R M ∧ CapsT m M (regs .x11) D j

/-- `TInv`, the clones so far with their sources' lengths. -/
def TInvC (env : Env) (m : MachineState) (top ret : Word) (regs : Reg → Word) (D : Word) (H j k : Nat) (a T : Word)
    (t q : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  TInv env m top ret regs D H j k a T t q R M ∧ CapsT m M (regs .x11) D j

set_option rv_sym.heap true in
/-- **The return**, from instruction 226: the header `(n, D, n)` stored at `sret`, the saved registers. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) :
    ∀ D R M, XRegs top D regs R → MemOk env m top ret regs Tactic.F M →
      ((regs .x12).toNat = 0 ∨ (Blk env m D (regs .x12).toNat M ∧
        ∃ H, DoneT env M D (regs .x12).toNat (regs .x12).toNat H ∧ H ≤ (env.next M).toNat)) →
      CapsT m M (regs .x11) D (regs .x12).toNat →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 226, ret, top⟩ :: rest, R, M⟩ := by
  intro D R M hR hM hD hC
  have hlay := env.layout
  obtain ⟨hstk, hW, h16, hown, hwin, hal, hB, -⟩ := hA
  obtain ⟨hsl0, hF0, hS0, hc0⟩ := hM
  have hM' : MemOk env m top ret regs (SretVecOut regs m) M := ⟨hsl0, Tactic.frame_weaken hF0, hS0, hc0⟩
  obtain ⟨hM3, hn3, r0, r8, r16, rk⟩ := hdr3 (v0 := regs .x12) (v1 := D) (v2 := regs .x12) hstk hown hwin hM'
  have hge := hW.next_ge
  have hnm := hF0.1
  have hnM := hF0.2.1
  have hW1 := hW.heapEnd_le
  have hsmall : (regs .x12).toNat * 24 ≤ 0x78000000 := by
    rcases hB with h | ⟨-, h2, -⟩
    · rw [h]; omega
    · unfold Env.Live at h2; omega
  have hd2 : (regs .x12).toNat = 0 ∨ ((env.next m).toNat ≤ D.toNat ∧ ∃ H, H ≤ (env.next M).toNat ∧
      DoneT env (((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) D).setMem (regs .x10 + 16#64)
        (regs .x12)) D (regs .x12).toNat (regs .x12).toNat H) := by
    rcases hD with h | ⟨⟨b1, b2, b3⟩, H, hdone, hH⟩
    · exact .inl h
    refine .inr ⟨b1, H, hH, DoneT.keep hdone (by omega) (Nat.le_refl _) (by rw [hn3]) fun b hb => rk b ?_⟩
    have := hown.2
    rcases hown.1 with h1 | h1 <;> rcases hb with h2 | h2 <;> omega
  have hC3 : CapsT m (((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) D).setMem (regs .x10 + 16#64)
      (regs .x12)) (regs .x11) D (regs .x12).toNat := by
    rcases hD with h | ⟨⟨b1, b2, b3⟩, -⟩
    · intro i hi; omega
    refine hC.keep (by omega) fun b h1 h2 => rk b ?_
    have := hown.2
    rcases hown.1 with h | h <;> omega
  have hPost : ∀ r, PostT env regs m r
      (((M.setMem (regs .x10) (regs .x12)).setMem (regs .x10 + 8#64) D).setMem (regs .x10 + 16#64) (regs .x12)) := by
    intro r
    refine ⟨⟨post_ok hwin hal r0 r8 r16 ?_ (by omega), ?_⟩, ?_, by rw [vecPtr_eq, r8]; exact hC3⟩
    · rcases hD with h | ⟨⟨b1, b2, b3⟩, -⟩
      · exact .inl h
      · exact .inr ⟨by omega, b1, by rw [hn3]; omega, b3⟩
    · rw [vecPtr_eq, r8]
      intro j hj
      rcases hd2 with h | ⟨-, H, -, hdone⟩
      · omega
      exact (hdone j hj).1
    · rw [vecPtr_eq, r8]
      intro j hj
      rcases hd2 with h | ⟨b1, H, hH, hdone⟩
      · omega
      rw [hn3]
      rcases (hdone j hj).2 with h | ⟨h1, h2⟩
      · exact .inl h
      · exact .inr ⟨by omega, by omega⟩
  clear hd2 hC3
  obtain ⟨-, hF3, hS3, hc3⟩ := hM3
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13⟩ := hsl0
  have h24 := hown.2
  have := hW.nextAddr_ge
  have hw : ∀ k : Nat, k ≤ 16 → inWindow (regs .x10 + BitVec.ofNat 64 k) 8 = true := fun k hk => by
    have e : (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k := toNat_add_ofNat (by omega)
    rw [inWindow_iff, e]; unfold InWin at hwin; omega
  have w0 : inWindow (regs .x10) 8 = true := by simpa using hw 0 (by omega)
  have w8 := hw 8 (by omega)
  have w16 := hw 16 (by omega)
  rv_introT hR
  rv_symT hp with [_hL]
  all_goals try first | exact (hPost (fun _ => 0#64)).1.1.1.2.1.2.2.1 |
    exact (hPost (fun _ => 0#64)).1.1.1.2.1.2.2.2
  · have h := (hPost (fun _ => 0#64)).1.1.2.2
    rwa [vecPtr_eq, r8] at h
  · have h := (hPost (fun _ => 0#64)).1.2
    rwa [vecPtr_eq, r8] at h
  · have h := (hPost (fun _ => 0#64)).2.1
    unfold FreshTermsT at h
    rw [hn3] at h
    exact h
  · have h := (hPost (fun _ => 0#64)).2.2
    unfold CapsT at h
    simpa only [vecCap_eq, vecLen_eq] using h

set_option rv_sym.heap true in
/-- **The join**, from instruction 194: `Form` `j`'s header stored at `D + 24 j`, then the next `Form` (78) or the
    return. -/
theorem join {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {D : Word} {H j k : Nat}
    (h78 : 0 < k → ∀ R M, OInvC env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, JRegs top D regs R → (R .x19).toNat = (regs .x11).toNat + 24 * j → (R .x24).toNat = j →
      (R .x25).toNat = k + 1 → j + k + 1 = (regs .x12).toNat →
      (R .x23).toNat = (regs .x11).toNat + 24 * (regs .x12).toNat → (R .x26).toNat * 40 < 2 ^ 63 →
      ((R .x13).toNat = 0 ∧ (R .x26).toNat = 0 ∨ R .x13 = R .x26 ∧ H ≤ (R .x10).toNat ∧
        (R .x10).toNat + 40 * (R .x26).toNat ≤ (env.next M).toNat ∧ (R .x10).toNat % 8 = 0 ∧
        TermsT env M (R .x10) (R .x26).toNat) →
      Blk env m D (regs .x12).toNat M → D.toNat + 24 * (regs .x12).toNat ≤ H → H ≤ (env.next M).toNat →
      DoneT env M D (regs .x12).toNat j H → MemOk env m top ret regs Tactic.F M →
      R .x26 = vecLen m (regs .x11 + BitVec.ofNat 64 (24 * j)) → CapsT m M (regs .x11) D j →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 194, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR h19 h24 h25 hjk h23 hL40 hnew hB hDH hH hdone hM hLs hC
  have hlay := env.layout
  have hex := exit hp hL hk hA
  obtain ⟨hstk, hW, h16, hown, hwin, hal, hsrc, hforms⟩ := id hA
  obtain ⟨b1, b2, b3⟩ := id hB
  have hge := hW.next_ge
  have hnM := hM.2.1.2.1
  have hW1 := hW.heapEnd_le
  have hsrc' : (regs .x11).toNat + 24 * (regs .x12).toNat ≤ (env.next m).toNat := by
    rcases hsrc with h | ⟨-, h2, -⟩
    · omega
    · unfold Env.Live at h2; omega
  have eS : (R .x24 <<< 4 + R .x24 <<< 3).toNat = 24 * j := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq, h24]
    omega
  have eA : (D + (R .x24 <<< 4 + R .x24 <<< 3)).toNat = D.toNat + 24 * j := by
    rw [BitVec.toNat_add, eS]; omega
  have hAw : D + (R .x24 <<< 4 + R .x24 <<< 3) = D + BitVec.ofNat 64 (24 * j) :=
    BitVec.eq_of_toNat_eq (by rw [eA, toNat_add_ofNat (by omega)])
  have e8 : (D + (R .x24 <<< 4 + R .x24 <<< 3) + 8#64).toNat = D.toNat + 24 * j + 8 := by
    rw [toNat_add_ofNat (by omega), eA]
  have e16 : (D + (R .x24 <<< 4 + R .x24 <<< 3) + 16#64).toNat = D.toNat + 24 * j + 16 := by
    rw [toNat_add_ofNat (by omega), eA]
  obtain ⟨m3, n3, d3⟩ := join_mem (A := D + (R .x24 <<< 4 + R .x24 <<< 3)) (c := R .x13) (P := R .x10) (L := R .x26)
    hstk hge hM hB hAw (by omega) hDH hH hdone hL40 hnew
  have hC3 := hC.join (P := R .x10) (by omega) hAw
    (by rcases hnew with ⟨h1, h2⟩ | ⟨h1, -⟩; exacts [h1.trans h2.symm, by rw [h1]]) hLs
  have e19 : (R .x19 + 24#64).toNat = (regs .x11).toNat + 24 * (j + 1) := by
    rw [toNat_add_ofNat (by omega)]; omega
  have e24 : (R .x24 + 1#64).toNat = j + 1 := by rw [toNat_add_ofNat (by omega)]; omega
  have e25 : (R .x25 + 18446744073709551615#64).toNat = k := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hcM : M.code = m.code := hM.2.2.2
  rv_introT hR
  rv_symT hp stop [78, 226] with [hL]
  · have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [e25, h]; rfl)) hc
      · exact h
    clear hc
    have hjn : (regs .x12).toNat - (k - 1 + 1) = j + 1 := by omega
    exact h78 hk0 _ _ ⟨⟨⟨rfl, rfl, rfl, rfl⟩, h23, j + 1, by omega, e19, e24,
      by show (R .x25 + 18446744073709551615#64).toNat = k - 1 + 1; omega,
      ⟨b1, by rw [n3]; exact b2, b3⟩, d3, m3⟩, by rw [hjn]; exact hC3⟩
  · have hk0 : k = 0 := by have := congrArg BitVec.toNat hc; rw [e25] at this; exact this
    clear hc
    have hj1 : j + 1 = (regs .x12).toNat := by omega
    rw [hj1] at d3 hC3
    exact hex D _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ m3 (.inr ⟨⟨b1, by rw [n3]; exact b2, b3⟩, _, d3, Nat.le_refl _⟩) hC3

set_option rv_sym.heap true in
/-- **The inner loop's back edge** (instruction 174, `x23` the next term): the head again (130), or the join once
    the last term is done. -/
theorem back {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {D a T : Word} {H j k t q : Nat}
    (ha : a.toNat = (regs .x11).toNat + 24 * j) (hjk : j + k + 1 = (regs .x12).toNat)
    (hDH : D.toNat + 24 * (regs .x12).toNat ≤ H) (hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63)
    (h78 : 0 < k → ∀ R M, OInvC env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩)
    (h130 : ∀ R M, IInvC env m top ret regs D H j k a T q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, R .x23 = R .x27 → TInvC env m top ret regs D H j k a T t q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 174, ret, top⟩ :: rest, R, M⟩ := by
  intro R M h23 hI
  have hJ := join hp hL hk hA h78 (H := H) (j := j)
  obtain ⟨⟨hR, h19, h24, h25, h26, h21, h22, sT, s23, hHT, hT2, hT8, hB, hdone, hM, htq, h27, h20, hterms⟩, hC⟩ := hI
  obtain ⟨hstk, hW, h16, -⟩ := hA
  have hlay := env.layout
  have := hW.nextAddr_ge
  have hR' := And.intro hR h23
  rv_introT hR'
  rv_symT hp stop [130, 176] with [hL]
  · -- more terms: `x27 ≠ x22`
    have hq0 : q ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [h27, h22]; omega))
    clear hc
    exact h130 _ _ ⟨⟨⟨rfl, rfl, rfl, rfl⟩, h19, h24, h25, h26, h21, h22, sT, s23, hHT, hT2, hT8, hB, hdone, hM, t,
      htq, h27, h20, hterms⟩, hC⟩
  · have hq0 : q = 0 := by have := congrArg BitVec.toNat hc; rw [h27, h22] at this; omega
    clear hc
    have hfl : t = (vecLen m a).toNat := by omega
    rv_symT hp stop [194] with [hL]
    refine hJ _ _ ⟨rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ hjk ?_ ?_ (.inr ⟨?_, ?_, ?_, ?_, ?_⟩) hB hDH (by omega) hdone hM
      ?_ hC
    · simp only [Tactic.rf]; rw [h19]; exact ha
    · simpa only [Tactic.rf] using h24
    · simpa only [Tactic.rf] using h25
    · simpa only [Tactic.rf] using s23
    · simp only [Tactic.rf]; rw [h26]; exact hFL40
    · simp only [Tactic.rf]
    · simp only [Tactic.rf]; rw [sT]; exact hHT
    · simp only [Tactic.rf]; rw [sT, h26]; exact hT2
    · simp only [Tactic.rf]; rw [sT]; exact hT8
    · simp only [Tactic.rf]; rw [sT, h26, ← hfl]; exact hterms
    · simp only [Tactic.rf]; rw [h26, ← addr_eq ha]

set_option rv_sym.heap true in
/-- **After the monomial's clone** (instruction 144): the term stored at `T + 40 t`, then the next term (130) or
    the join. -/
theorem after {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩) (hA : Args env m top regs) {D a T : Word} {H j k t q : Nat}
    (ha : a.toNat = (regs .x11).toNat + 24 * j) (hjk : j + k + 1 = (regs .x12).toNat)
    (hDH : D.toNat + 24 * (regs .x12).toNat ≤ H) (hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63)
    (hP1 : 0x10000000 ≤ (vecPtr m a).toNat)
    (hP2 : (vecPtr m a).toNat + 40 * (vecLen m a).toNat ≤ (env.next m).toNat)
    (hP8 : (vecPtr m a).toNat % 8 = 0)
    (h78 : 0 < k → ∀ R M, OInvC env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩)
    (h130 : ∀ R M, IInvC env m top ret regs D H j k a T (q - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, (JRegs top D regs R ∧ R .x23 = R .x27 + 40#64) → R .x19 = a → (R .x24).toNat = j →
      (R .x25).toNat = k + 1 → R .x26 = vecLen m a → (R .x21).toNat = 40 * q →
      (R .x22).toNat = (vecPtr m a).toNat + 40 * (vecLen m a).toNat → (R .x27).toNat = (vecPtr m a).toNat + 40 * t →
      (R .x20).toNat = T.toNat + 40 * t → t + q = (vecLen m a).toNat → 0 < q →
      M.getMem (top + 18446744073709551448#64) = T →
      (M.getMem (top + 18446744073709551456#64)).toNat = (regs .x11).toNat + 24 * (regs .x12).toNat →
      H ≤ T.toNat → T.toNat + 40 * (vecLen m a).toNat ≤ (env.next M).toNat → T.toNat % 8 = 0 →
      Blk env m D (regs .x12).toNat M → DoneT env M D (regs .x12).toNat j H → MemOk env m top ret regs Tactic.F M →
      TermsT env M T t → VecT env M (top + 18446744073709551472#64) 8 → CapsT m M (regs .x11) D j →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 144, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR h19 h24 h25 h26 h21 h22 h27 h20 htq hq sT s23 hHT hT2 hT8 hB hdone hM hterms hV hC
  have hlay := env.layout
  have hJ := join hp hL hk hA h78 (H := H) (j := j)
  obtain ⟨hstk, hW, h16, -, -, -, -, -⟩ := id hA
  obtain ⟨b1, b2, b3⟩ := id hB
  have hge := hW.next_ge
  have hnM := hM.2.1.2.1
  have hnm := hM.2.1.1
  have hW1 := hW.heapEnd_le
  have hcM : M.code = m.code := hM.2.2.2
  have hTm : (env.next m).toNat ≤ T.toNat := by omega
  obtain ⟨m7, n7, sT7, s237, ht7, hd7⟩ := term_mem (A := R .x20) (u1 := M.getMem (R .x27 + 24#64))
    (u2 := M.getMem (R .x27 + 32#64)) (e0 := M.getMem (R .x27 + 24#64)) (e1 := M.getMem (R .x27 + 32#64)) hstk hge hM
    hV h20 (by omega : t < (vecLen m a).toNat) hTm hHT hT2 hT8 hterms hdone hDH (by omega)
  have w24 : (R .x27 + 24#64).toNat = (R .x27).toNat + 24 := toNat_add_ofNat (by omega)
  have w32 : (R .x27 + 32#64).toNat = (R .x27).toNat + 32 := toNat_add_ofNat (by omega)
  have v8 : (R .x20 + 8#64).toNat = (R .x20).toNat + 8 := toNat_add_ofNat (by omega)
  have v16 : (R .x20 + 16#64).toNat = (R .x20).toNat + 16 := toNat_add_ofNat (by omega)
  have v24 : (R .x20 + 24#64).toNat = (R .x20).toNat + 24 := toNat_add_ofNat (by omega)
  have v32 : (R .x20 + 32#64).toNat = (R .x20).toNat + 32 := toNat_add_ofNat (by omega)
  have e20 : (R .x20 + 40#64).toNat = T.toNat + 40 * (t + 1) := by rw [toNat_add_ofNat (by omega)]; omega
  have e27 : (R .x27 + 40#64).toNat = (vecPtr m a).toNat + 40 * (t + 1) := by rw [toNat_add_ofNat (by omega)]; omega
  have e21 : (R .x21 + 18446744073709551576#64).toNat = 40 * (q - 1) := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hback := back hp hL hk hA (t := t + 1) (q := q - 1) ha hjk hDH hFL40 h78 h130
  clear hA hV hdone hterms
  have hDj : D.toNat + 24 * j < 2 ^ 64 := by omega
  have e120 := es (top := top) (c := 18446744073709551496#64) (k := 120) rfl (by omega)
  have e112 := es (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  rv_introT hR
  rv_symT hp stop [174] with [hL]
  refine hback _ _ rfl ⟨⟨⟨rfl, rfl, rfl, rfl⟩, h19, h24, h25, h26, e21, h22, sT7.trans sT, by rw [s237]; exact s23,
    hHT, by rw [n7]; exact hT2, hT8, ⟨b1, by rw [n7]; exact b2, b3⟩, hd7, m7, by omega, e27, e20, ht7⟩, ?_⟩
  refine ((((((hC.setMem hDj ?_).setMem hDj ?_).setMem hDj ?_).setMem hDj ?_).setMem hDj ?_).setMem hDj ?_).setMem
    hDj ?_
  all_goals (try simp only [v8, v16, v24, v32, e120, e112])
  all_goals omega

set_option rv_sym.heap true in
/-- **The inner loop**, from its head to the join. -/
theorem inner {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC : Nat} (hnC : 176 + needC ≤ need) (hcl : CloneSpecT env 8 p L.clone.idx needC)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {D a T : Word} {H j k : Nat}
    (ha : a.toNat = (regs .x11).toNat + 24 * j) (hjk : j + k + 1 = (regs .x12).toNat) (hFa : FormT env m a)
    (hDH : D.toNat + 24 * (regs .x12).toNat ≤ H)
    (h78 : 0 < k → ∀ R M, OInvC env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩) :
    ∀ q R M, IInvC env m top ret regs D H j k a T q R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 130, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (IInvC env m top ret regs D H j k a T) fun q R M hI ih => ?_
  have hlay := env.layout
  have hJ := join hp hL hk hA h78 (H := H) (j := j)
  have hFL40 : (vecLen m a).toNat * 40 < 2 ^ 63 := by
    have := (vecT_buf hFa.1).2; have := Nat.mul_le_mul_right 40 this.1; omega
  obtain ⟨hstk, hW, h16, -, -, -, -, -⟩ := id hA
  obtain ⟨⟨hR, h19, h24, h25, h26, h21, h22, sT, s23, hHT, hT2, hT8, hB, hdone, hM, t, htq, h27, h20, hterms⟩, hC⟩ :=
    id hI
  clear hI
  have := hW.nextAddr_ge
  rcases Nat.eq_zero_or_pos q with hq | hq
  · -- no term left: to the join
    clear hA hFa
    have hx : R .x21 = 0#64 := BitVec.eq_of_toNat_eq (by rw [h21, hq]; rfl)
    have hfl : t = (vecLen m a).toNat := by omega
    have hR' := And.intro hR hx
    rv_introT hR'
    rv_symT hp stop [194] with [hL]
    refine hJ _ _ ⟨rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ hjk ?_ ?_ (.inr ⟨?_, ?_, ?_, ?_, ?_⟩) hB hDH (by omega) hdone hM
      ?_ hC
    · simp only [Tactic.rf]; rw [h19]; exact ha
    · simpa only [Tactic.rf] using h24
    · simpa only [Tactic.rf] using h25
    · simpa only [Tactic.rf] using s23
    · simp only [Tactic.rf]; rw [h26]; exact hFL40
    · simp only [Tactic.rf]
    · simp only [Tactic.rf]; rw [sT]; exact hHT
    · simp only [Tactic.rf]; rw [sT, h26]; exact hT2
    · simp only [Tactic.rf]; rw [sT]; exact hT8
    · simp only [Tactic.rf]; rw [sT, h26, ← hfl]; exact hterms
    · simp only [Tactic.rf]; rw [h26, ← addr_eq ha]
  · have hFL : 0 < (vecLen m a).toNat := by omega
    obtain ⟨hP1, hP2, hP8⟩ := hFa.foot.resolve_left (by omega)
    have hafter := after hp hL hk hA (T := T) (t := t) (q := q) ha hjk hDH hFL40 hP1 hP2 hP8 h78
      (fun R' M' h => ih (q - 1) R' M' (by omega) h)
    have hx27 : R .x27 = vecPtr m a + BitVec.ofNat 64 (40 * t) :=
      BitVec.eq_of_toNat_eq (by rw [h27, toNat_add_ofNat (by omega)])
    have hnm := hM.2.1.1
    have hnM := hM.2.1.2.1
    have hW1 := hW.heapEnd_le
    have hSt : env.Static M := hM.2.2.1
    have hcM : M.code = m.code := hM.2.2.2
    have w8 : (R .x27 + 8#64).toNat = (R .x27).toNat + 8 := toNat_add_ofNat (by omega)
    have w16 : (R .x27 + 16#64).toNat = (R .x27).toNat + 16 := toNat_add_ofNat (by omega)
    have ag : ∀ b : Word, b.toNat < (env.next m).toNat → M.getMem b = m.getMem b := fun b hb =>
      hM.2.1.getMem_below_next (by omega) hb id
    have hBt : BufT env M (M.getMem (R .x27 + 16#64)) (M.getMem (R .x27 + 8#64)) 8 := by
      have hv := (vecT_buf (hFa.2 t (by omega))).1
      rw [← hx27, vecLen_eq, vecPtr_eq] at hv
      rw [ag _ (by omega), ag _ (by omega)]
      exact hv.mono hnm
    obtain ⟨b1, b2, b3⟩ := hB
    clear hA hFa ag
    rv_introT hR
    rv_symT hp stop [144, 194] with [hL] using [hcl]
    · exact absurd (congrArg BitVec.toNat hc) (by rw [h21]; simp only [BitVec.toNat_ofNat]; omega)
    · -- after the clone
      have e144 := es (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
      have e168 := es (top := top) (c := 18446744073709551448#64) (k := 168) rfl (by omega)
      have e160 := es (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
      obtain ⟨hM1, hn1, hk1⟩ := call_keep hstk hM hret1_14 hret1_15 hret1_24 (fun b hb => by
        obtain ⟨h1, h2⟩ := hb
        change (top + 18446744073709551472#64).toNat ≤ b.toNat at h1
        change b.toNat < (top + 18446744073709551472#64).toNat + 24 at h2
        omega) keep1_2
      refine hafter _ _ ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ h19 h24 h25 h26 h21 h22 h27 h20 htq hq ?_ ?_ hHT (by omega) hT8
        ⟨b1, by omega, b3⟩ ?_ hM1 ?_ ?_ ?_
      · rw [hk1 _ (.inr (by omega)) (.inl (by omega))]; exact sT
      · rw [hk1 _ (.inr (by omega)) (.inl (by omega))]; exact s23
      · exact DoneT.keep hdone (by omega) (by omega) hn1 fun b hb => hk1 b (.inl (by omega)) (.inl (by omega))
      · exact TermsT.keep hterms (by omega) hn1 fun b h1 h2 => hk1 b (.inl (by omega)) (.inl (by omega))
      · exact ⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩
      · exact hC.keep (by omega) fun b h1 h2 => hk1 b (.inl (by omega)) (.inl (by omega))

/-! ## The outer loop: one `Form` cloned -/

set_option rv_sym.heap true in
/-- **The outer loop**, from its head to the return. -/
theorem outer {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needA needC needH : Nat} (hnA : 176 + needA ≤ need) (hnC : 176 + needC ≤ need)
    (hnH : 176 + needH ≤ need)
    (hal : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop))
    (hcl : CloneSpecT env 8 p L.clone.idx needC) (hhe : Aborts env p L.handleError.idx needH)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hA : Args env m top regs) {D : Word} :
    ∀ k R M, OInvC env m top ret regs D k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInvC env m top ret regs D) fun k R M hI ih => ?_
  have hlay := env.layout
  have h78 : 0 < k → ∀ R M, OInvC env m top ret regs D (k - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 78, ret, top⟩ :: rest, R, M⟩ := fun hk0 R' M' h => ih (k - 1) R' M'
    (by omega) h
  obtain ⟨⟨hR, h23, j, hjk, h19, h24, h25, hB, hdone, hM⟩, hC⟩ := hI
  rw [show (regs .x12).toNat - (k + 1) = j by omega] at hC
  obtain ⟨hstk, hW, h16, -, -, -, hsrc, hforms⟩ := id hA
  have hsrc' : (regs .x11).toNat + 24 * (regs .x12).toNat ≤ (env.next m).toNat := by
    rcases hsrc with h | ⟨-, h2, -⟩
    · omega
    · unfold Env.Live at h2; omega
  have ha : R .x19 = regs .x11 + BitVec.ofNat 64 (24 * j) :=
    BitVec.eq_of_toNat_eq (by rw [h19, toNat_add_ofNat (by omega)])
  have hFa : FormT env m (R .x19) := ha ▸ hforms j (by omega)
  have hFL40 : (vecLen m (R .x19)).toNat * 40 < 2 ^ 63 := by
    have := (vecT_buf hFa.1).2; have := Nat.mul_le_mul_right 40 this.1; omega
  have hlt := vecT_lt hFa.1
  have hnm := hM.2.1.1
  have hnM := hM.2.1.2.1
  have hW1 := hW.heapEnd_le
  have := hW.nextAddr_ge
  have hSt : env.Static M := hM.2.2.1
  have hcM : M.code = m.code := hM.2.2.2
  have ag8 : M.getMem (R .x19 + 8#64) = vecPtr m (R .x19) :=
    hM.2.1.getMem_below_next (by omega) (by rw [toNat_add_ofNat (by omega)]; omega) id
  have ag16 : M.getMem (R .x19 + 16#64) = vecLen m (R .x19) :=
    hM.2.1.getMem_below_next (by omega) (by rw [toNat_add_ofNat (by omega)]; omega) id
  have w8 : (R .x19 + 8#64).toNat = (R .x19).toNat + 8 := toNat_add_ofNat (by omega)
  have w16 : (R .x19 + 16#64).toNat = (R .x19).toNat + 16 := toNat_add_ofNat (by omega)
  clear hsrc hforms
  have hJ := join hp hL hk hA h78 (H := (env.next M).toNat) (j := j)
  have hin := fun T => inner hp hL hnC hcl hk hstop hneed hA (a := R .x19) (T := T) (H := (env.next M).toNat) h19 hjk
    hFa (by have := hB.2.1; omega) h78
  obtain ⟨b1, b2, b3⟩ := id hB
  have hFLn : (M.getMem (R .x19 + 16#64)).toNat * 40 < 2 ^ 63 := by rw [ag16]; exact hFL40
  have hLs : M.getMem (R .x19 + 16#64) = vecLen m (regs .x11 + BitVec.ofNat 64 (24 * j)) := by rw [ag16, ha]
  have hDj : D.toNat + 24 * j < 2 ^ 64 := by omega
  have s40 : (M.getMem (R .x19 + 16#64) <<< 5 + M.getMem (R .x19 + 16#64) <<< 3).toNat =
      40 * (M.getMem (R .x19 + 16#64)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega
  have sh : M.getMem (R .x19 + 16#64) <<< 3 >>> 3 = M.getMem (R .x19 + 16#64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have e176 := es (top := top) (c := 18446744073709551440#64) (k := 176) rfl (by omega)
  rv_introT hR
  rv_symT hp stop [130, 194, 218] with [hL] using [hal, hhe]
  · -- `x19 = x23`: not reached, `j < n`
    exact absurd (congrArg BitVec.toNat hc) (by rw [h19, h23]; omega)
  · -- no terms, no block
    have hF0 : (M.getMem (R .x19 + 16#64)).toNat = 0 := by
      have := congrArg BitVec.toNat hc; rw [s40] at this; simp only [BitVec.toNat_ofNat] at this; omega
    clear hc
    exact hJ _ _ ⟨rfl, rfl, rfl, rfl⟩ h19 h24 h25 hjk h23 hFLn (.inl ⟨rfl, hF0⟩) hB b2 (Nat.le_refl _) hdone hM
      hLs hC
  · -- after `alloc`, no terms
    have hF0 : (M.getMem (R .x19 + 16#64)).toNat = 0 := by rw [hc]; rfl
    clear hc
    obtain ⟨hM2, hn2, hk2⟩ := call_keep hstk hM hret2_14 hret2_15 hret2_19 (fun b hb => hb.elim)
      (fun a h _ => keep2_2 a h)
    exact hJ _ _ ⟨rfl, rfl, rfl, rfl⟩ h19 h24 h25 hjk h23 hFLn (.inl ⟨rfl, hF0⟩) ⟨b1, by omega, b3⟩ b2 hn2
      (DoneT.keep hdone (by omega) (by omega) hn2 fun b hb => hk2 b (.inl (by omega)) (.inl (by omega))) hM2
      hLs (hC.keep hDj fun b h1 h2 => hk2 b (.inl (by omega)) (.inl (by omega)))
  · -- `min(n, n - 1)` is `n`: not reached
    have hF1 : (M.getMem (R .x19 + 16#64)).toNat ≠ 0 := fun h => hc_5 (BitVec.eq_of_toNat_eq h)
    rw [sh, BitVec.lt_def, BitVec.toNat_add] at hc
    simp only [BitVec.toNat_ofNat] at hc
    omega
  · -- into the inner loop
    have hF1 : (M.getMem (R .x19 + 16#64)).toNat ≠ 0 := fun h => hc_5 (BitVec.eq_of_toNat_eq h)
    clear hc
    obtain ⟨-, hP2, -⟩ := hFa.foot.resolve_left (by rw [← ag16]; exact hF1)
    rw [← ag8, ← ag16] at hP2
    have e1 : (M.getMem (R .x19 + 16#64) + 18446744073709551615#64).toNat = (M.getMem (R .x19 + 16#64)).toNat - 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    have e22 : (M.getMem (R .x19 + 8#64) + ((M.getMem (R .x19 + 16#64) + 18446744073709551615#64) <<< 5 +
        (M.getMem (R .x19 + 16#64) + 18446744073709551615#64) <<< 3) + 40#64).toNat =
        (M.getMem (R .x19 + 8#64)).toNat + 40 * (M.getMem (R .x19 + 16#64)).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, Nat.shiftLeft_eq, e1]
      simp only [BitVec.toNat_ofNat]
      have : 2 ^ 5 * ((M.getMem (R .x19 + 16#64)).toNat - 1) + 2 ^ 3 * ((M.getMem (R .x19 + 16#64)).toNat - 1) + 40 =
        40 * (M.getMem (R .x19 + 16#64)).toNat := by omega
      omega
    obtain ⟨hM2, hn2, hk2⟩ := call_keep hstk hM hret2_14 hret2_15 hret2_19 (fun b hb => hb.elim)
      (fun a h _ => keep2_2 a h)
    have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
    have e168 := es (top := top) (c := 18446744073709551448#64) (k := 168) rfl (by omega)
    have e160 := es (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
    have e152 := es (top := top) (c := 18446744073709551464#64) (k := 152) rfl (by omega)
    obtain ⟨m3, n3, k3⟩ := frame_store (a := top + 18446744073709551456#64) (v := R .x23) hstk hM2 (by omega)
      (by omega)
    obtain ⟨m4, n4, k4⟩ := frame_store (a := top + 18446744073709551464#64) (v := R .x22) hstk m3 (by omega)
      (by omega)
    obtain ⟨m5, n5, k5⟩ := frame_store (a := top + 18446744073709551448#64) (v := r2 .x10) hstk m4 (by omega)
      (by omega)
    have hN : env.next (((m2.setMem (top + 18446744073709551456#64) (R .x23)).setMem (top + 18446744073709551464#64)
        (R .x22)).setMem (top + 18446744073709551448#64) (r2 .x10)) = env.next m2 := by rw [n5, n4, n3]
    refine hin (r2 .x10) (vecLen m (R .x19)).toNat _ _ ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, h24, h25, ag16,
      by rw [← ag16]; exact s40, by rw [← ag8, ← ag16]; exact e22, MachineState.getMem_setMem_eq, ?_, hret2_16,
      by rw [hN, ← ag16]; rw [s40] at hret2_18; omega, hret2_17, ⟨b1, by rw [hN]; omega, b3⟩, ?_, m5, 0, by omega,
      by simp only [Tactic.rf]; rw [← ag8]; omega, by simp only [Tactic.rf]; omega,
      fun t ht => absurd ht (Nat.not_lt_zero _)⟩, ?_⟩
    · rw [k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), MachineState.getMem_setMem_eq]; exact h23
    · refine DoneT.keep hdone (by omega) (by omega) (by rw [hN]; exact hn2) fun b hb => ?_
      rw [k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega))]
      exact hk2 b (.inl (by omega)) (.inl (by omega))
    · refine hC.keep hDj fun b h1 h2 => ?_
      rw [k5 _ (ne _ _ (by omega)), k4 _ (ne _ _ (by omega)), k3 _ (ne _ _ (by omega))]
      exact hk2 b (.inl (by omega)) (.inl (by omega))

set_option rv_sym.heap true in
/-- **`<Vec<Form> as Clone>::clone` is total**, with 176 bytes of stack beyond its callees', given its two bounds'
    words in the static data. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c8_d6dfd6bc, d_c8_d6dfd6bc_words), (L.d_c8_51ab739d, d_c8_51ab739d_words)])
    {need needA needC needH : Nat} (hnA : 176 + needA ≤ need) (hnC : 176 + needC ≤ need) (hnH : 176 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcl : CloneSpecT env 8 p L.clone.idx needC)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hw1 := hd.words (List.mem_cons_self ..)
  have hw2 := hd.words (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  rv_autoT hp stop [78, 226] with [hL, hw1, hw2] using [hal', hhe]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_6
    have hlim : env.stackLimit.toNat + 176 ≤ top.toNat := by omega
    have hM0 := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    simp only [saved] at hM0
    have hA : Args env m top regs := ⟨hlim, hpre_13, hpre_12, ⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, hpre_10, hpre_11⟩
    have hW1 := hpre_13.heapEnd_le
    have hsm : (regs .x12).toNat = 0 ∨ (regs .x11).toNat + 24 * (regs .x12).toNat ≤ 0x78000000 := by
      rcases hpre_10 with h | ⟨-, h2, -⟩
      · exact .inl h
      · unfold Env.Live at h2; exact .inr (by omega)
    have hsm' : 24 * (regs .x12).toNat ≤ 0x78000000 := by rcases hsm with h | h <;> omega
    have s24 : (regs .x12 <<< 4 + regs .x12 <<< 3).toNat = 24 * (regs .x12).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      omega
  · exact (data_ok hpre_13 hd (List.mem_cons_self ..) (by decide)).1
  · exact (data_ok hpre_13 hd (List.mem_cons_self ..) (by decide)).2
  · -- no `Form`s: the empty vector
    have hn0 : regs .x12 = 0#64 := BitVec.eq_of_toNat_eq (by
      have := congrArg BitVec.toNat hc; rw [s24] at this; simp only [BitVec.toNat_ofNat] at this ⊢; omega)
    clear hc
    exact exit hp hL hk hA (D := 8#64) _ _ ⟨rfl, rfl, rfl, by simp only [Tactic.rf]; exact hn0.symm, rfl⟩ hM0
      (.inl (by rw [hn0]; rfl)) fun _ h => absurd h (by rw [hn0]; simp)
  · rw [s24]; omega
  · -- `n = 0` after `alloc`: not reached, the empty vector all the same
    obtain ⟨hM1, -, -⟩ := call_keep hlim hM0 hret1_14 hret1_15 hret1_19 (fun b hb => hb.elim)
      (fun a h _ => keep1_2 a h)
    exact exit hp hL hk hA (D := r1 .x10) _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hM1 (.inl (by rw [hc]; rfl))
      fun _ h => absurd h (by rw [hc]; simp)
  · exact (data_ok hpre_13 hd (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by decide)).1
  · exact (data_ok hpre_13 hd (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by decide)).2
  · -- into the outer loop
    have hn0 : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
    clear hc
    replace hsm := hsm.resolve_left hn0
    obtain ⟨hM1, hn1, -⟩ := call_keep hlim hM0 hret1_14 hret1_15 hret1_19 (fun b hb => hb.elim)
      (fun a h _ => keep1_2 a h)
    have hnm := hM0.2.1.1
    rw [s24] at hret1_18
    exact outer hp hL hnA hnC hnH hal' hcl hhe hk hstop hpre_3 hA ((regs .x12).toNat - 1) _ _
      ⟨⟨⟨rfl, rfl, rfl, rfl⟩, by simp only [Tactic.rf]; rw [BitVec.toNat_add, s24]; omega, 0, by omega,
        by simp only [Tactic.rf]; omega, rfl, by simp only [Tactic.rf]; omega,
        ⟨by simp only [Tactic.rf]; omega, by simp only [Tactic.rf]; omega, hret1_17⟩,
        fun _ h => absurd h (Nat.not_lt_zero _), hM1⟩, fun _ h => absurd h (by omega)⟩


end Rv64mc.Proof.Layout.CloneFormsFreshT

/-- info: 'Rv64mc.Proof.Layout.CloneFormsFreshT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.CloneFormsFreshT.total
