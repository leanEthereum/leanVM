/-
  Rv64mc.Proof.Field.ESumFormT

  `E::sum` over `self.terms.iter().map(|(monomial, c)| monomial.iter().fold(*c, |acc, &i| acc * column[i]))`
  (`Form::evaluate`'s sum, index 33) is total (`SumSafeT`): passed the iterator by reference (the terms' pointer and
  end, the column's pointer and length), it returns, writing nothing of its caller's, or ends the run with `a0 = 2` on
  an index past the column (`panic_bounds_check`). The precondition (`SumPreT`): the iterator's four words 8-byte
  aligned, in a window and the caller's (`Owned`); the terms whole `40`-byte elements, unless none in a window,
  8-byte aligned and the caller's; each term's monomial, unless empty, in a window and 8-byte aligned (`TermsW`); the
  column a `TabW`. The sum is not stated: no caller's safety reads it.

  Two nested loops, each `Total.loop`: the terms left (`outer`, from its head, instruction 31) and the monomial's
  indices left (`inner`, instruction 40), with `E::mul` stepped through its total contract with its postcondition
  dropped (`KInvT.dropPost`). The inner loop goes on, after its last index, by the step to the next term (`after`,
  instruction 27), which closes over the outer loop's induction hypothesis. The ten saved registers' slots are
  `SavedT.MemOk`; the terms' words are read through it (`kept`: a word the caller owns is the entry's).

  ## Main definitions

  * `TermsW`, `SumPreT`, `SumSafeT`, `Mem`, `OInv`, `IInv`

  ## Main results

  * `kept`, `count_toNat`, `after`, `inner`, `outer`, `total`
-/

import Rv64mc.Proof.Field.ESumWinT
import Rv64mc.Proof.Field.KInvT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Core.AbortStop
import Rv64mc.Gen.Tmpl.Verifier.Field.E.SumMapIterTVecUsizeEEEvaluateClosure0

namespace Rv64mc.Proof.Field.ESumFormT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Proof.Field.ESumWinT (TabW)
open Rv64mc.Proof.Field.KInvT (dropPost)
open Rv64mc.Gen.Verifier.Field.E.SumMapIterTVecUsizeEEEvaluateClosure0 (Link tmpl)

/-- The `n` terms (`40` bytes: the monomial's capacity, pointer and length, the coefficient) from `q`: each one's
    monomial, unless empty, in a window and 8-byte aligned. -/
def TermsW (env : Env) (m : MachineState) (q : Word) (n : Nat) : Prop :=
  ∀ j, j < n → (m.getMem (q + BitVec.ofNat 64 (40 * j) + 16#64)).toNat = 0 ∨
    InWin env (m.getMem (q + BitVec.ofNat 64 (40 * j) + 8#64))
        (8 * (m.getMem (q + BitVec.ofNat 64 (40 * j) + 16#64)).toNat) ∧
      (m.getMem (q + BitVec.ofNat 64 (40 * j) + 8#64)).toNat % 8 = 0

/-- The total precondition: the iterator at `x10` (`32` bytes) 8-byte aligned, in a window and the caller's; the
    terms from `+ 0` to `+ 8` whole `40`-byte elements, unless none in a window, 8-byte aligned and the caller's, each
    a `TermsW`; the column (pointer `+ 16`, length `+ 24`) a `TabW`. -/
def SumPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧ InWin env (regs .x10) 32 ∧ env.Owned m (regs .x2) (regs .x10) 32 ∧
    (m.getMem (regs .x10)).toNat ≤ (m.getMem (regs .x10 + 8#64)).toNat ∧
    ((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) % 40 = 0 ∧
    (m.getMem (regs .x10 + 8#64) = m.getMem (regs .x10) ∨
      InWin env (m.getMem (regs .x10)) ((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) ∧
      (m.getMem (regs .x10)).toNat % 8 = 0 ∧
      env.Owned m (regs .x2) (m.getMem (regs .x10))
        ((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat)) ∧
    TermsW env m (m.getMem (regs .x10))
      (((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) / 40) ∧
    TabW env (m.getMem (regs .x10 + 16#64)) (m.getMem (regs .x10 + 24#64))

/-- **The total contract**: it returns, writing nothing of its caller's, or ends the run with `a0 = 2`. It does not
    state the sum. -/
def SumSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (SumPreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

/-- What the loops keep of memory: `SavedT.MemOk` with the ten saved registers' slots, from `top - 8` (the return
    address) down to `top - 80` (`s8`). -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (fun _ => False)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20, regs .x21, regs .x22, regs .x23, regs .x24] m M

/-- The saved slots lie in the `80` bytes below `top`. -/
theorem slots : SlotsIn 80
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64, 18446744073709551560#64, 18446744073709551552#64,
      18446744073709551544#64, 18446744073709551536#64] :=
  slots_le

/-- **`Mem` across `E::mul`**, from the stack pointer `top - 80`. -/
theorem call_back {env : Env} {ret top : Word} {regs : Reg → Word} {m M X : MachineState}
    (hf : env.Frame (top + 18446744073709551536#64) (fun _ => False) M X)
    (hk : ∀ a : Word, top + 18446744073709551536#64 ≤ a → X.getMem a = M.getMem a) (hc : X.code = M.code)
    (hs : env.Static X) (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hM : Mem env ret top regs m M) :
    Mem env ret top regs m X :=
  (hM.call_below slots le_rfl hlim (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hf hk hc hs).1

/-- **A word the caller owns is the entry's**, through `MemOk`'s frame. -/
theorem kept {env : Env} {top : Word} {cs vs : List Word} {m M : MachineState}
    (h : Runtime.SavedT.MemOk env top (fun _ => False) cs vs m M) (hlim : env.stackLimit.toNat ≤ top.toNat)
    {a : Word} (ho : a.toNat + 8 ≤ (env.next m).toNat ∨ top.toNat ≤ a.toNat) : M.getMem a = m.getMem a := by
  have hl := env.layout
  have hn := h.1.2.1
  have hn' := h.1.1
  refine h.1.2.2 a fun hw => ?_
  unfold Env.MayWrite at hw
  rcases hw with hw | hw | hw | hw
  · omega
  · omega
  · subst hw; omega
  · exact hw

/-- The terms' count, `(e - q) / 8` times the inverse of `5`, for a multiple of `40` bytes. -/
theorem count_toNat {q e : Word} (h : q.toNat ≤ e.toNat) (h40 : (e.toNat - q.toNat) % 40 = 0) :
    ((e - q) >>> 3 * 14757395258967641293#64).toNat = (e.toNat - q.toNat) / 40 := by
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have e1 : (2 ^ 64 - q.toNat + e.toNat) % 2 ^ 64 = e.toNat - q.toNat := by omega
  rw [e1]
  obtain ⟨t, ht⟩ : ∃ t, e.toNat - q.toNat = 40 * t := ⟨(e.toNat - q.toNat) / 40, by omega⟩
  have := e.isLt
  rw [ht, show 40 * t / 2 ^ 3 = 5 * t by omega, show 40 * t / 40 = t by omega,
    show 5 * t * (14757395258967641293 % 2 ^ 64) = t + 2 ^ 64 * (4 * t) by norm_num; ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- The outer loop's head (instruction 31), `d` terms of `n` left: the stack pointer, `s9` to `s11` as at the entry,
    the terms at `x19`, the column at `x22` with its length `x9`, the count `x21`, the index `x20`, `Mem`. -/
def OInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q c cl : Word) (n d : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551536#64 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    R .x19 = q ∧ R .x22 = c ∧ R .x9 = cl ∧ (R .x21).toNat = n ∧ (R .x20).toNat + d = n ∧ 1 ≤ d ∧
    Mem env ret top regs m M

/-- The inner loop's head (instruction 40), `k` of the monomial's indices left: `OInv`'s registers, the indices left
    `x23`, the next index's address `x24` in the monomial `[mp, mp + 8 len)`. -/
def IInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (q c cl : Word) (n d : Nat)
    (mp : Word) (len k : Nat) (R : Reg → Word) (M : MachineState) : Prop :=
  OInv env ret top regs m q c cl n d R M ∧ (R .x23).toNat = k ∧ 1 ≤ k ∧ k ≤ len ∧
    (R .x24).toNat = mp.toNat + 8 * (len - k)

set_option rv_sym.heap true in
/-- **The step to the next term** (instruction 27): the index advanced, then the return after the last term, or the
    outer loop's head with one term fewer (`hnext`). -/
theorem after (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 80 ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q c cl : Word} {n d : Nat} (hnext : ∀ R M, 2 ≤ d → OInv env ret top regs m q c cl n (d - 1) R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 62, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, OInv env ret top regs m q c cl n d R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 54, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hI
  obtain ⟨-, -, -, -, -, -, -, h21, h20, hd1, hM⟩ := id hI
  have hx20 : (R .x20 + 1#64).toNat = (R .x20).toNat + 1 := toNat_add_ofNat (by have := (R .x21).isLt; omega)
  rv_introT hI
  rv_symT hp stop [62] with [hlim]
  have hd2 : 2 ≤ d := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by omega))
  refine hnext _ _ hd2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h21, ?_, by omega, hM⟩
  simp only [Tactic.rf]; omega

set_option rv_sym.heap true in
/-- **The inner loop**, from its head: the index read and checked against the column's length (`panic_bounds_check`
    past it), the column's entry, `E::mul`, then back to the head (one index fewer) or the step to the next term. -/
theorem inner (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needU needP : Nat} (hnU : 80 + needU ≤ need) (hnP : 80 + needP ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needU) (hpanic : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q c cl mp : Word} {n d len : Nat} (htab : TabW env c cl) (hwm : InWin env mp (8 * len)) (ham : mp.toNat % 8 = 0)
    (hafter : ∀ R M, OInv env ret top regs m q c cl n d R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 54, ret, top⟩ :: rest, R, M⟩) :
    ∀ k R M, IInv env ret top regs m q c cl n d mp len k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 80, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (IInv env ret top regs m q c cl n d mp len) fun k R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨⟨-, -, -, -, -, h22, h9, h21, h20, hd1, hM⟩, h23, hk1, hkl, h24⟩ := id hI
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  have hwl := hwm.lt
  have hd := hwm.dword (x := R .x24) (o := 8 * (len - k)) hW ham h24 (by omega) (by omega)
  rv_introT hI
  rv_symT hp stop [54, 80] with [hL, hlim] using [dropPost hmul, hpanic]
  any_goals first
    | exact (htab.entry hW hc).1.1
    | exact (htab.entry hW hc).1.2
    | exact (htab.entry hW hc).2.1
    | exact (htab.entry hW hc).2.2
  all_goals
    have hM1 := call_back hret2_14 keep2_1 hret2_16 hret2_15 hlim hM
  -- back to the head, one index fewer
  · have hk2 : 2 ≤ k := Nat.le_of_not_lt fun h => hc (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega))
    refine ih (k - 1) _ _ (by omega) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h21, h20, hd1, hM1⟩, ?_, by omega,
      by omega, ?_⟩
    all_goals simp only [Tactic.rf]
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · rw [toNat_add_ofNat (by omega)]; omega
  -- the step to the next term
  · exact hafter _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h21, h20, hd1, hM1⟩

/-- The `j`-th term's offset, as the code computes it. -/
theorem off_eq (x : Word) : x <<< 5 + x <<< 3 = BitVec.ofNat 64 (40 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]; omega

set_option rv_sym.heap true in
/-- **The outer loop**, from its head: the term's monomial length and coefficient read, then the inner loop from its
    first index, or (an empty monomial) the step to the next term. -/
theorem outer (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needU needP : Nat} (hnU : 80 + needU ≤ need) (hnP : 80 + needP ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needU) (hpanic : Aborts env p L.panicBoundsCheck.idx needP)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) (fun _ _ _ => False) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m)
    {q c cl : Word} {n : Nat} (htab : TabW env c cl) (hwq : InWin env q (40 * n)) (haq : q.toNat % 8 = 0)
    (hoq : env.Owned m top q (40 * n)) (hts : TermsW env m q n) :
    ∀ d R M, OInv env ret top regs m q c cl n d R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 62, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (OInv env ret top regs m q c cl n) fun d R M hI ih => ?_
  have hlay := env.layout
  obtain ⟨-, -, -, -, -, -, -, h21, h20, hd1, hM⟩ := id hI
  have hlim : env.stackLimit.toNat + 80 ≤ top.toNat := by omega
  have hwl := hwq.lt
  have hoff := off_eq (R .x20)
  have hafter := after env p i L hp hk hlim hal hW (d := d) fun R' M' hd2 h' => ih (d - 1) R' M' (by omega) h'
  rv_introT hI
  rv_symT hp stop [54, 80] with [hL, hlim]
  all_goals
    have hj : (R .x20).toNat < n := by omega
    have et : (q + BitVec.ofNat 64 (40 * (R .x20).toNat)).toNat = q.toNat + 40 * (R .x20).toNat :=
      toNat_add_ofNat (by omega)
  any_goals (rw [hoff]; first
    | exact (hwq.dword_add hW haq et (by omega) (by omega)).1
    | exact (hwq.dword_add hW haq et (by omega) (by omega)).2)
  -- an empty monomial: the step to the next term
  · exact hafter _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h21, h20, hd1, hM⟩
  -- the inner loop from the monomial's first index
  · have ko : ∀ o : Nat, o + 8 ≤ 40 → M.getMem (q + BitVec.ofNat 64 (40 * (R .x20).toNat) + BitVec.ofNat 64 o) =
        m.getMem (q + BitVec.ofNat 64 (40 * (R .x20).toNat) + BitVec.ofNat 64 o) := fun o ho =>
      kept hM (by omega) (by rw [toNat_add_ofNat (by omega), et]; rcases hoq.1 with h | h <;> omega)
    have k8 := ko 8 (by omega)
    have k16 := ko 16 (by omega)
    rw [hoff] at hc
    rw [hoff, k8, k16]
    have hne : (m.getMem (q + BitVec.ofNat 64 (40 * (R .x20).toNat) + 16#64)).toNat ≠ 0 := fun h =>
      hc (by rw [k16]; exact BitVec.eq_of_toNat_eq h)
    obtain ⟨hwm, ham⟩ := (hts _ hj).resolve_left hne
    have := hwm.lt
    exact inner env p i L hp hL hnU hnP hmul hpanic hstop hstk hal hW htab hwm ham hafter _ _ _
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h21, h20, hd1, hM⟩, rfl, by simp only [Tactic.rf]; omega, le_rfl,
        by simp only [Tactic.rf]; omega⟩

set_option rv_sym.heap true in
/-- **`Form::evaluate`'s sum is total**: none for no terms, else the terms' count, then the outer loop from the
    first term. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needU needP : Nat} (hnU : 80 + needU ≤ need) (hnP : 80 + needP ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needU) (hpanic : Aborts env p L.panicBoundsCheck.idx needP) :
    SumSafeT env p i need := by
  rv_autoT hp stop [62] with [hL]
  have hn := count_toNat hpre_10 hpre_11
  have hne : (m.getMem (regs .x10)).toNat ≠ (m.getMem (regs .x10 + 8#64)).toNat :=
    fun h => hc (BitVec.eq_of_toNat_eq h)
  obtain ⟨hwq, haq, hoq⟩ := hpre_12.resolve_left (Ne.symm hc)
  have e40 : (m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat =
      40 * (((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) / 40) := by omega
  rw [e40] at hwq hoq
  rw [hpre_2] at hoq
  refine outer env p i L hp hL hnU hnP hmul hpanic hk hstop hpre_3 hpre_15 hpre_16 hpre_14 hwq haq hoq hpre_13
    (((m.getMem (regs .x10 + 8#64)).toNat - (m.getMem (regs .x10)).toNat) / 40) _ _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp only [Tactic.rf]; exact hn, by simp only [Tactic.rf]; simp,
      by omega, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT

end Rv64mc.Proof.Field.ESumFormT

/-- info: 'Rv64mc.Proof.Field.ESumFormT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumFormT.total
