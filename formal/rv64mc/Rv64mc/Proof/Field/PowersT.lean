/-
  Rv64mc.Proof.Field.PowersT

  `powers(base, n)` is total: it returns `Powers.Post`'s vector (`Spec.Field.Powers`, the powers `1, base, ...,
  base^(n - 1)`), which is also a vector's (`VecReprT.VecT`) of length `n`, its buffer fresh unless empty, or the run
  ends with the guest's abort (`AbortStop`) where `alloc` or `handle_error` does. Over any program holding its
  template, from the total contracts of `alloc`, `E::mul` and `handle_error`. There was no partial proof (class C).

  The code checks that `16 n` fits an `isize`, allocates the buffer (the dangling `8` for none), builds the header in
  its frame and, unless `n = 0`, runs a loop whose head is instruction 118: store the power, raise the length, multiply
  by `base` (`E::mul`), stop at `n`. The loop calls `grow_one` when the length reaches the capacity, which it never
  does: the capacity is `n` and the loop stops there first (`LInv`'s `j < n`). `Total.loop` with the elements left as
  the measure; `exit` copies the header to `sret`.

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`, `st`, `LInv`, `XInv`

  ## Main results

  * `total`
-/

import Rv64mc.Spec.Field.Powers
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.CloneT
import Rv64mc.Proof.Runtime.FromElemT
import Rv64mc.Gen.Tmpl.Verifier.Field.Powers
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Field.PowersT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Proof.Multilinear
  Rv64mc.Proof.Layout
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT)
open Rv64mc.Gen.Verifier.Field.Powers (Link tmpl)

/-- The total precondition: `Pre`, and the result's slot in a window and 8-byte aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  Spec.Field.Powers.Pre env regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧ (regs .x10).toNat % 8 = 0

/-- The total postcondition: `Post`, and the result a vector's of length `n` (`a3`), its buffer fresh unless
    empty. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  Spec.Field.Powers.Post env regs m r' m' ∧ VecT env m' (regs .x10) 16 ∧ vecLen m' (regs .x10) = regs .x13 ∧
    ((regs .x13).toNat = 0 ∨ env.Fresh m m' (vecPtr m' (regs .x10)) ((regs .x13).toNat * 16))

/-- **The total contract of `powers`**: `Powers.spec`'s, as a `HoldsT` from `PreT`, with `VecT` of the result, or the
    guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) (Spec.Whir.SretOut Layouts.Vec.byteSize) AbortStop

/-! ## The powers -/

/-- `Model.powersM`'s fold after `j` steps: the powers so far and the next. -/
def st (base : Model.Limbs) (j : Nat) : List Model.Limbs × Model.Limbs :=
  (List.range j).foldl (fun (s : List Model.Limbs × Model.Limbs) _ => (s.1 ++ [s.2], Model.eMul s.2 base))
    ([], Model.eOne)

theorem st_succ (base : Model.Limbs) (j : Nat) :
    st base (j + 1) = ((st base j).1 ++ [(st base j).2], Model.eMul (st base j).2 base) := by
  simp only [st, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem st_length (base : Model.Limbs) (j : Nat) : (st base j).1.length = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [st_succ, List.length_append, ih, List.length_singleton]

theorem st_getElem (base : Model.Limbs) {j k : Nat} (hk : k < j) :
    (st base j).1[k]'(by rw [st_length]; exact hk) = (st base k).2 := by
  induction j with
  | zero => omega
  | succ j ih =>
    simp only [st_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
    · rw [List.getElem_append_left (by rw [st_length]; exact h)]; exact ih h
    · rw [List.getElem_append_right (by rw [st_length]), List.getElem_singleton]

theorem st_next (base : Model.Limbs) (j : Nat) :
    (st base (j + 1)).2.1 = (Model.eMul ((st base j).2.1, (st base j).2.2) base).1 ∧
      (st base (j + 1)).2.2 = (Model.eMul ((st base j).2.1, (st base j).2.2) base).2 := by
  rw [st_succ]; exact ⟨rfl, rfl⟩

theorem off_step (j : Nat) : BitVec.ofNat 64 (16 * j) + 16#64 = BitVec.ofNat 64 (16 * (j + 1)) := by
  rw [show 16 * (j + 1) = 16 * j + 16 by omega, BitVec.ofNat_add]

theorem limbs_ofLimbsW (w : Model.Limbs) : Model.limbs (Model.ofLimbsW w) = w := by
  rw [Model.ofLimbsW, Model.limbs_ofLimbs, BF64.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]

/-! ## The frame -/

/-- The prologue's nine saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)

/-- The header in the frame: capacity `c`, pointer `q`, length `l`. -/
def hdr (N : MachineState) (top c q l : Word) : MachineState :=
  ((N.setMem (top + 18446744073709551520#64) c).setMem (top + 18446744073709551528#64) q).setMem
    (top + 18446744073709551536#64) l

/-- The twelve slots as numbers. -/
theorem slots {top : Word} {S : Nat} (h : S + 96 ≤ top.toNat) :
    (top + 18446744073709551608#64).toNat = top.toNat - 8 ∧ (top + 18446744073709551600#64).toNat = top.toNat - 16 ∧
    (top + 18446744073709551592#64).toNat = top.toNat - 24 ∧ (top + 18446744073709551584#64).toNat = top.toNat - 32 ∧
    (top + 18446744073709551576#64).toNat = top.toNat - 40 ∧ (top + 18446744073709551568#64).toNat = top.toNat - 48 ∧
    (top + 18446744073709551560#64).toNat = top.toNat - 56 ∧ (top + 18446744073709551552#64).toNat = top.toNat - 64 ∧
    (top + 18446744073709551544#64).toNat = top.toNat - 72 ∧ (top + 18446744073709551536#64).toNat = top.toNat - 80 ∧
    (top + 18446744073709551528#64).toNat = top.toNat - 88 ∧ (top + 18446744073709551520#64).toNat = top.toNat - 96 := by
  and_intros <;> exact slot_toNat (by decide) (by omega) (by decide)

/-- **The prologue's saves and the header**: in the frame, `env.Static` and `NEXT` kept. -/
theorem pro_frame {env : Env} {N m : MachineState} {top c q l : Word} (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m N) (hS : env.Static N) :
    env.Frame top Tactic.F m (hdr N top c q l) ∧ env.Static (hdr N top c q l) ∧ env.next (hdr N top c q l) = env.next N := by
  obtain ⟨-, -, -, -, -, -, -, -, -, e80, e88, e96⟩ := slots hlim
  refine ⟨Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF (by omega) (by omega)) (by omega) (by omega))
    (by omega) (by omega), Env.static_setMem_stack (Env.static_setMem_stack (Env.static_setMem_stack hS (by omega)) (by omega))
    (by omega), ?_⟩
  simp only [hdr]
  rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]

theorem saved_frame {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    env.Frame top Tactic.F m (saved m top ret regs) ∧ env.Static (saved m top ret regs) := by
  obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64, e72, -, -, -⟩ := slots hlim
  have f := Tactic.frame_refl (top := top) hnx
  refine ⟨?_, ?_⟩
  · simp only [saved]
    repeat (first | exact f | refine Tactic.frame_store ?_ (by omega) (by omega))
  · simp only [saved]
    repeat (first | exact hS | refine Env.static_setMem_stack ?_ (by omega))

/-- The header over memories that agree from the frame's start up. -/
theorem hdr_congr {N N' : MachineState} {top c q l : Word}
    (h : ∀ a, top + 18446744073709551520#64 ≤ a → N.getMem a = N'.getMem a) :
    ∀ a, top + 18446744073709551520#64 ≤ a → (hdr N top c q l).getMem a = (hdr N' top c q l).getMem a := by
  intro a ha
  simp only [hdr]
  by_cases e1 : a = top + 18446744073709551536#64
  · subst e1; simp only [MachineState.getMem_setMem_eq]
  by_cases e2 : a = top + 18446744073709551528#64
  · subst e2; simp only [MachineState.getMem_setMem_ne e1, MachineState.getMem_setMem_eq]
  by_cases e3 : a = top + 18446744073709551520#64
  · subst e3; simp only [MachineState.getMem_setMem_ne e1, MachineState.getMem_setMem_ne e2,
      MachineState.getMem_setMem_eq]
  simp only [MachineState.getMem_setMem_ne e1, MachineState.getMem_setMem_ne e2, MachineState.getMem_setMem_ne e3]
  exact h a ha

/-- The loop's head with `k + 1` powers left: `j` stored, `x10`, `x11` the next, the length `j` in the header. -/
def LInv (env : Env) (m M0 : MachineState) (top ret q : Word) (regs : Reg → Word) (k : Nat) (R : Reg → Word)
    (M : MachineState) : Prop :=
  ∃ j, j + k + 1 = (regs .x13).toNat ∧
    R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x13 ∧ R .x9 = regs .x12 ∧ R .x18 = regs .x11 ∧
    R .x19 = regs .x10 ∧ R .x20 = q ∧ R .x21 = regs .x13 ∧ R .x22 = BitVec.ofNat 64 (16 * j) ∧
    R .x23 = BitVec.ofNat 64 j ∧ R .x10 = (st (regs .x11, regs .x12) j).2.1 ∧
    R .x11 = (st (regs .x11, regs .x12) j).2.2 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    (∀ a, top + 18446744073709551520#64 ≤ a →
      M.getMem a = (hdr (saved m top ret regs) top (regs .x13) q (BitVec.ofNat 64 j)).getMem a) ∧
    (∀ k < j, M.getMem (q + BitVec.ofNat 64 (16 * k)) = (st (regs .x11, regs .x12) k).2.1 ∧
      M.getMem (q + BitVec.ofNat 64 (16 * k) + 8#64) = (st (regs .x11, regs .x12) k).2.2) ∧
    env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code ∧ (env.next M0).toNat ≤ (env.next M).toNat

/-- At the copy to `sret` (instruction 70): the header (capacity `c`, pointer `q`, length `n`) in the frame, the `n`
    powers at `q`. -/
def XInv (env : Env) (m : MachineState) (top ret c q : Word) (regs : Reg → Word) (R : Reg → Word)
    (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551520#64 ∧ R .x19 = regs .x10 ∧
    R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    (∀ a, top + 18446744073709551520#64 ≤ a →
      M.getMem a = (hdr (saved m top ret regs) top c q (regs .x13)).getMem a) ∧
    (∀ k < (regs .x13).toNat, M.getMem (q + BitVec.ofNat 64 (16 * k)) = (st (regs .x11, regs .x12) k).2.1 ∧
      M.getMem (q + BitVec.ofNat 64 (16 * k) + 8#64) = (st (regs .x11, regs .x12) k).2.2) ∧
    ((regs .x13).toNat = 0 ∧ c = 0#64 ∨
      c = regs .x13 ∧ env.Fresh m M q (16 * (regs .x13).toNat) ∧ q.toNat % 8 = 0) ∧
    env.Frame top Tactic.F m M ∧ env.Static M ∧ M.code = m.code

/-- **`Post`'s vector**, from the header copied to `s` (a caller's object) over `M`, which holds the `L` powers at
    `q`: none, or a block allocated since the entry. -/
theorem post_of {env : Env} {m M : MachineState} {top s c q L : Word} {b : Model.Limbs}
    (hown : env.Owned m top s Layouts.Vec.byteSize) (hlim : env.stackLimit.toNat ≤ top.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hMn : (env.next M).toNat ≤ env.heapEnd.toNat)
    (hel : ∀ k < L.toNat, M.getMem (q + BitVec.ofNat 64 (16 * k)) = (st b k).2.1 ∧
      M.getMem (q + BitVec.ofNat 64 (16 * k) + 8#64) = (st b k).2.2)
    (hov : 16 * L.toNat < 2 ^ 63)
    (hc : L.toNat = 0 ∧ c = 0#64 ∨ c = L ∧ env.Fresh m M q (16 * L.toNat)) :
    Spec.Multilinear.FreshVecE env m (((M.setMem s c).setMem (s + 8#64) q).setMem (s + 16#64) L) s
      ((Model.powersM b L.toNat).map Model.ofLimbsW) := by
  have s0 := owned_slot0 hown hnx hlim (by decide)
  have s8 := owned_slot (k := 8) hown hnx hlim (by decide)
  have s16 := owned_slot (k := 16) hown hnx hlim (by decide)
  have hlen : ((Model.powersM b L.toNat).map Model.ofLimbsW).map Model.limbs = (st b L.toNat).1 := by
    rw [List.map_map, show Model.limbs ∘ Model.ofLimbsW = id from funext limbs_ofLimbsW, List.map_id]; rfl
  have hnf : env.next (((M.setMem s c).setMem (s + 8#64) q).setMem (s + 16#64) L) = env.next M := by
    simp only [Env.next]
    rw [MachineState.getMem_setMem_ne (Ne.symm s16.2.1), MachineState.getMem_setMem_ne (Ne.symm s8.2.1),
      MachineState.getMem_setMem_ne (Ne.symm s0.2.1)]
  refine ⟨q, L.toNat, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [vecPtr, Layouts.Vec.ptr]
    rw [MachineState.getMem_setMem_ne (SelectorPoint.ne8_16 _), MachineState.getMem_setMem_eq]
  · simp only [vecCap, Layouts.Vec.cap, BitVec.add_zero]
    rw [MachineState.getMem_setMem_ne (SelectorPoint.ne16 _).symm,
      MachineState.getMem_setMem_ne (SelectorPoint.ne8 _).symm, MachineState.getMem_setMem_eq]
    rcases hc with h | h
    · rw [h.2, h.1]
    · rw [h.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [vecLen, Layouts.Vec.len]
    rw [MachineState.getMem_setMem_eq, hlen, st_length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hlen, st_length]
  · omega
  · rw [hlen]
    rcases hc with h | h
    · have : (st b L.toNat).1 = [] := List.eq_nil_of_length_eq_zero (by rw [st_length]; exact h.1)
      rw [this]; exact ⟨by simpa using BitVec.isLt _, fun k hk => by simp at hk⟩
    · have hq1 := h.2.1
      have hq2 := h.2.2
      refine ⟨by rw [st_length]; simp only [Layouts.E.byteSize]; have := env.heapEnd.isLt; omega, fun k hk => ?_⟩
      rw [st_length] at hk
      have hk1 : (q + BitVec.ofNat 64 (16 * k)).toNat = q.toNat + 16 * k := toNat_add_ofNat (by
        have := env.heapEnd.isLt; omega)
      have hk2 : (q + BitVec.ofNat 64 (16 * k) + 8#64).toNat = q.toNat + 16 * k + 8 := by
        rw [toNat_add_ofNat (k := 8) (by have := env.heapEnd.isLt; omega), hk1]
      have ne : ∀ x : Word, x.toNat < q.toNat + 16 * L.toNat → (env.next m).toNat ≤ x.toNat →
          ∀ y : Word, InRange s Layouts.Vec.byteSize y → y ≠ x := fun x h1 h2 y hy =>
        owned_ne_fresh hown hlim hy h2 (by omega)
      simp only [EAt, Layouts.E.byteSize, Layouts.E.c0, Layouts.E.c1, BitVec.add_zero]
      rw [st_getElem _ hk, MachineState.getMem_setMem_ne (ne _ (by omega) (by omega) _ s16.1).symm,
        MachineState.getMem_setMem_ne (ne _ (by omega) (by omega) _ s8.1).symm,
        MachineState.getMem_setMem_ne (ne _ (by omega) (by omega) _ s0.1).symm,
        MachineState.getMem_setMem_ne (ne _ (by omega) (by omega) _ s16.1).symm,
        MachineState.getMem_setMem_ne (ne _ (by omega) (by omega) _ s8.1).symm,
        MachineState.getMem_setMem_ne (ne _ (by omega) (by omega) _ s0.1).symm]
      exact hel k hk
  · rcases hc with h | h
    · exact Or.inl h.1
    · exact Or.inr ⟨h.2.1, by rw [hnf]; simp only [Layouts.E.byteSize]; exact h.2.2⟩

set_option rv_sym.heap true in
/-- **The copy to `sret`** and the return. -/
theorem exit {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    {need : Nat} (hn : 96 ≤ need) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m : MachineState} {c q : Word}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (Spec.Whir.SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (_hge : 0x10000000 ≤ (env.next m).toNat) (hov : 16 * (regs .x13).toNat < 2 ^ 63)
    (R : Reg → Word) (M : MachineState) (hX : XInv env m top ret c q regs R M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 140, ret, top⟩ :: rest, R, M⟩ := by
  obtain ⟨-, -, -, -, -, -, -, hel, hc, hF, hS, hcode⟩ := id hX
  have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
  have hpost := post_of (b := (regs .x11, regs .x12)) hown hlim hnx hF.2.1 hel hov
    (hc.imp id fun h => ⟨h.1, h.2.1⟩)
  rv_introT hX
  simp only [hdr, saved] at hX_7
  rcases hX_9 with ⟨hn0, rfl⟩ | ⟨rfl, hfr, hq8⟩
  all_goals rv_symT hp
  all_goals try exact hpost
  all_goals simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
  all_goals rv_closeT

/-- A store at another address keeps a word. -/
theorem gm_ne {M : MachineState} {a b v : Word} (h : b.toNat ≠ a.toNat) : (M.setMem a v).getMem b = M.getMem b :=
  MachineState.getMem_setMem_ne fun e => h (by rw [e])

/-- **One pass's memory**: the power stored at `q + 16 j`, the length `j + 1` in the header, then `E::mul`'s frame
    (`keep`, which keeps what lies below `NEXT` or in the frame). -/
theorem step_mem {env : Env} {M m1 S : MachineState} {top q c v0 v1 : Word} {j : Nat} {b : Model.Limbs}
    (hq : q.toNat + 16 * (j + 1) ≤ (env.next M).toNat) (hMn : (env.next M).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hH : ∀ a, top + 18446744073709551520#64 ≤ a → M.getMem a = (hdr S top c q (BitVec.ofNat 64 j)).getMem a)
    (hC : ∀ k < j, M.getMem (q + BitVec.ofNat 64 (16 * k)) = (st b k).2.1 ∧
      M.getMem (q + BitVec.ofNat 64 (16 * k) + 8#64) = (st b k).2.2)
    (hv0 : v0 = (st b j).2.1) (hv1 : v1 = (st b j).2.2)
    (keep : ∀ a : Word, a.toNat < (env.next (((M.setMem (q + BitVec.ofNat 64 (16 * j)) v0).setMem
        (q + BitVec.ofNat 64 (16 * j) + 8#64) v1).setMem (top + 18446744073709551536#64)
        (BitVec.ofNat 64 j + 1#64))).toNat ∨ (top + 18446744073709551520#64).toNat ≤ a.toNat →
      m1.getMem a = (((M.setMem (q + BitVec.ofNat 64 (16 * j)) v0).setMem
        (q + BitVec.ofNat 64 (16 * j) + 8#64) v1).setMem (top + 18446744073709551536#64)
        (BitVec.ofNat 64 j + 1#64)).getMem a) :
    (∀ a, top + 18446744073709551520#64 ≤ a →
      m1.getMem a = (hdr S top c q (BitVec.ofNat 64 (j + 1))).getMem a) ∧
    (∀ k < j + 1, m1.getMem (q + BitVec.ofNat 64 (16 * k)) = (st b k).2.1 ∧
      m1.getMem (q + BitVec.ofNat 64 (16 * k) + 8#64) = (st b k).2.2) := by
  have hlay := env.layout
  have ht96 : (top + 18446744073709551520#64).toNat = top.toNat - 96 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have ht80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have hb : q.toNat + 16 * (j + 1) < 2 ^ 64 := by have := env.heapEnd.isLt; omega
  have hnx : env.next (((M.setMem (q + BitVec.ofNat 64 (16 * j)) v0).setMem
      (q + BitVec.ofNat 64 (16 * j) + 8#64) v1).setMem (top + 18446744073709551536#64)
      (BitVec.ofNat 64 j + 1#64)) = env.next M := by
    rw [Env.next_setMem_stack (by omega)]
    have e0 : (q + BitVec.ofNat 64 (16 * j)).toNat = q.toNat + 16 * j := toNat_add_ofNat (by omega)
    rw [next_store_heap (by rw [toNat_add_ofNat (k := 8) (by omega), e0]; omega), next_store_heap (by omega)]
  rw [hnx] at keep
  have e0 : (q + BitVec.ofNat 64 (16 * j)).toNat = q.toNat + 16 * j := toNat_add_ofNat (by omega)
  have e8 : (q + BitVec.ofNat 64 (16 * j) + 8#64).toNat = q.toNat + 16 * j + 8 := by
    rw [toNat_add_ofNat (k := 8) (by omega), e0]
  refine ⟨fun a ha => ?_, fun k hk => ?_⟩
  · have ha' : top.toNat - 96 ≤ a.toNat := by rw [BitVec.le_def] at ha; omega
    rw [keep a (Or.inr (by omega))]
    by_cases e : a = top + 18446744073709551536#64
    · subst e; simp only [hdr, MachineState.getMem_setMem_eq, SelectorPoint.cnt_step]
    · have e' : a.toNat ≠ top.toNat - 80 := fun h => e (BitVec.eq_of_toNat_eq (by rw [h, ht80]))
      have h1 := hH a ha
      simp only [hdr] at h1 ⊢
      simp (disch := omega) only [gm_ne] at h1 ⊢
      exact h1
  · have b0 : (q + BitVec.ofNat 64 (16 * k)).toNat = q.toNat + 16 * k := toNat_add_ofNat (by omega)
    have b8 : (q + BitVec.ofNat 64 (16 * k) + 8#64).toNat = q.toNat + 16 * k + 8 := by
      rw [toNat_add_ofNat (k := 8) (by omega), b0]
    rw [keep (q + BitVec.ofNat 64 (16 * k)) (Or.inl (by omega)),
      keep (q + BitVec.ofNat 64 (16 * k) + 8#64) (Or.inl (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · simp (disch := omega) only [gm_ne]
      exact hC k hk
    · simp (disch := omega) only [gm_ne, MachineState.getMem_setMem_eq]
      exact ⟨hv0, hv1⟩

/-- **One pass's frame**: the two stores into the block, the length's, then `E::mul`'s frame. -/
theorem step_frame {env : Env} {m M m1 : MachineState} {top q v0 v1 l : Word} {j : Nat} {out : Word → Prop}
    (hF : env.Frame top Tactic.F m M) (hlo : (env.next m).toNat ≤ q.toNat)
    (hhi : q.toNat + 16 * (j + 1) ≤ (env.next M).toNat) (hMn : (env.next M).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hc : env.Frame (top + 18446744073709551520#64) out (((M.setMem (q + BitVec.ofNat 64 (16 * j)) v0).setMem
      (q + BitVec.ofNat 64 (16 * j) + 8#64) v1).setMem (top + 18446744073709551536#64) l) m1)
    (hout : ∀ a, out a → False) :
    env.Frame top Tactic.F m m1 ∧ (env.next M).toNat ≤ (env.next m1).toNat := by
  have hlay := env.layout
  have ht80 : (top + 18446744073709551536#64).toNat = top.toNat - 80 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have ht96 : (top + 18446744073709551520#64).toNat = top.toNat - 96 :=
    Multilinear.slot_toNat (by decide) (by omega) (by decide)
  have e0 : (q + BitVec.ofNat 64 (16 * j)).toNat = q.toNat + 16 * j :=
    toNat_add_ofNat (by have := env.heapEnd.isLt; omega)
  have e8 : (q + BitVec.ofNat 64 (16 * j) + 8#64).toNat = q.toNat + 16 * j + 8 := by
    rw [toNat_add_ofNat (k := 8) (by have := env.heapEnd.isLt; omega), e0]
  have f1 := frame_store_heap (a := q + BitVec.ofNat 64 (16 * j)) (v := v0) hF (by omega) (by omega)
  have f2 := frame_store_heap (a := q + BitVec.ofNat 64 (16 * j) + 8#64) (v := v1) f1 (by omega)
    (by rw [next_store_heap (by omega)]; omega)
  have f3 := Tactic.frame_store (a := top + 18446744073709551536#64) (v := l) f2 (by omega) (by omega)
  refine ⟨Multilinear.frame_call_own f3 hc (by omega) fun _ h => (hout _ h).elim, ?_⟩
  have := hc.1
  rwa [Env.next_setMem_stack (by omega), next_store_heap (by omega), next_store_heap (by omega)] at this

set_option rv_sym.heap true in
/-- **The loop**, from its head. -/
theorem loop {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 96 + needM ≤ need) (hmul : EMulT.specT env p L.mul.idx needM)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    {regs : Reg → Word} {m M0 : MachineState} {q : Word}
    (hk : ∀ r' m', HoldsT.post env (PostT env) (Spec.Whir.SretOut Layouts.Vec.byteSize) ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize) (hwin : InWin env (regs .x10) Layouts.Vec.byteSize)
    (hal : (regs .x10).toNat % 8 = 0) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hge : 0x10000000 ≤ (env.next m).toNat) (hend : env.heapEnd.toNat ≤ 0x78000000)
    (hfr : env.Fresh m M0 q (16 * (regs .x13).toNat)) (hq8 : q.toNat % 8 = 0)
    (hov : 16 * (regs .x13).toNat < 2 ^ 63) :
    ∀ k R M, LInv env m M0 top ret q regs k R M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 118, ret, top⟩ :: rest, R, M⟩ := by
  refine Total.loop (I := rvIsa) (LInv env m M0 top ret q regs) fun k R M hI ih => ?_
  have hlay := env.layout
  have hfr1 := hfr.1
  have hfr2 := hfr.2
  obtain ⟨j, hj, hI⟩ := hI
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hH, hC, hF, hS, hcode, hnM⟩ := id hI
  have hFn := hF.2.1
  have e0 : (q + BitVec.ofNat 64 (16 * j)).toNat = q.toNat + 16 * j := toNat_add_ofNat (by omega)
  have e8 : (q + BitVec.ofNat 64 (16 * j) + 8#64).toNat = q.toNat + 16 * j + 8 := by
    rw [toNat_add_ofNat (k := 8) (by omega), e0]
  rv_introT hI
  simp only [hdr, saved] at hI_16
  have hjn : j < (regs .x13).toNat := by omega
  have hjv : (BitVec.ofNat 64 j).toNat = j := by have := (regs .x13).isLt; simp; omega
  rv_symT hp stop [96, 120, 140] with [hL] using [hmul]
  rotate_left
  · exact absurd (congrArg BitVec.toNat hc) (by rw [hjv]; omega)
  clear hc
  rv_symT hp stop [118, 120, 140] with [hL] using [hmul]
  all_goals have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
  all_goals have sm := step_mem (b := (regs .x11, regs .x12)) (by omega) hFn hlim hH hC rfl rfl keep1_2
  all_goals obtain ⟨hF1, hn1⟩ := step_frame hF hfr1 (by omega) hFn hlim hret1_14 fun _ h => h
  · -- the last power: the copy to `sret`
    have hj1 : j + 1 = (regs .x13).toNat := by
      have := congrArg BitVec.toNat hc; rw [SelectorPoint.cnt_step] at this; simp at this; omega
    clear hc
    have hx13 : BitVec.ofNat 64 (j + 1) = regs .x13 := by rw [hj1]; simp
    refine exit hp (by omega) hk hstk hnx hown hwin hal hW h16 hge hov _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha => by rw [sm.1 a ha, hx13], fun k hk => sm.2 k (by omega),
      Or.inr ⟨rfl, ⟨hfr1, by omega⟩, hq8⟩, hF1, hret1_15, hret1_18.trans hcode⟩
    all_goals rv_closeT
  · -- back to the head
    have hk0 : k ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by rw [SelectorPoint.cnt_step]; simp; omega))
    clear hc
    refine ih (k - 1) _ _ (by omega) ⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      sm.1, sm.2, hF1, hret1_15, hret1_18.trans hcode, by omega⟩
    all_goals rv_closeT
    · exact off_step j
    · exact SelectorPoint.cnt_step j
    · exact (st_next (regs .x11, regs .x12) j).1.symm
    · exact (st_next (regs .x11, regs .x12) j).2.symm

set_option rv_sym.heap true in
/-- **`powers` is total**, with 96 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needM needH : Nat} (hnA : 96 + needA ≤ need) (hnM : 96 + needM ≤ need) (hnH : 96 + needH ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hmul : EMulT.specT env p L.mul.idx needM)
    (hhe : Runtime.Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [118, 140] with [hL] using [hal', hmul, hhe]
  all_goals have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
  all_goals have hov := SelectorPoint.ovf hc_1
  all_goals have hown : env.Owned m top (regs .x10) Layouts.Vec.byteSize := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
  all_goals obtain ⟨hF0, hS0⟩ := saved_frame (ret := ret) (regs := regs) hlim hpre_5 hpre_4
  · -- `n = 0`: the empty header copied
    obtain ⟨hF1, hS1, -⟩ := pro_frame (c := 0#64) (q := 8#64) (l := 0#64) hlim hF0 hS0
    refine exit hp (by omega) hk hpre_3 hpre_5 hown hpre_8 hpre_9 hpre_11 hpre_10 hpre_11.next_ge hov.2 _ _
      ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha => by rw [hc]; rfl, fun k hk => absurd hk (by rw [hc]; simp),
        Or.inl ⟨by rw [hc]; rfl, rfl⟩, hF1, hS1, rfl⟩
    all_goals rv_closeT
  · exfalso; have := hov.1; rw [hc_2] at this; exact hc (BitVec.eq_of_toNat_eq (by simp at this ⊢; omega))
  · omega
  · exfalso; exact hc_2 (by rw [hc]; rfl)
  · -- the loop from its first pass
    have e96 := (slots hlim).2.2.2.2.2.2.2.2.2.2.2
    obtain ⟨hF1, hS1, hn1⟩ := pro_frame (c := regs .x13) (q := r1 .x10) (l := 0#64) hlim
      (Multilinear.frame_call_own hF0 hret1_14 (by omega) fun _ h => h.elim) hret1_15
    refine loop hp hL (by omega) hmul hk hpre_3 hpre_5 hown hpre_8 hpre_9 hpre_11 hpre_10 hpre_11.next_ge
      hpre_11.heapEnd_le (M0 := hdr m1 top (regs .x13) (r1 .x10) 0#64) ⟨hret1_16, by rw [hn1, ← hret1_18, hov.1]⟩
      hret1_17 hov.2 ((regs .x13).toNat - 1) _ _ ⟨0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, hdr_congr keep1_1, fun k hk => absurd hk (Nat.not_lt_zero _), hF1, hS1, hret1_19, le_rfl⟩
    · have := Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq h); simp; omega
    all_goals rv_closeT
    all_goals exact rfl

end Rv64mc.Proof.Field.PowersT
