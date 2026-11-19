module

public import NativeVm.Wire.Code
public import NativeVm.Wire.Model
public import Native.Keccak.Spec
public import Native.Frame

/-!
# The decoder's memory

The decoder runs with `rdi` at the context and touches four areas: the context's first words and
its scratch (`Keccak.hash`'s), the wire's words (read only), the decoded area and the working area.
`Pre e` is what the caller provides; `Inv e s D W` says that `s` holds the decoded area's words `D`
and the working area's `W`, and every word outside the scratch and the two areas as at the start.
Loads and stores in the areas read and update `D` and `W` (`blk_load_work`, `blk_store_work`, ...).
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak

/-- Word `k` of an area at `a`. -/
def adr (a : UInt64) (k : Nat) : UInt64 := a + (8 * k).toUInt64

/-- The `n` words at `a` lie below `2^64`. -/
def Fit (a : UInt64) (n : Nat) : Prop := a.toNat + 8 * n ≤ 2 ^ 64

/-- The `n` words at `a` and the `m` at `b` do not overlap. -/
def Apart (a : UInt64) (n : Nat) (b : UInt64) (m : Nat) : Prop :=
  a.toNat + 8 * n ≤ b.toNat ∨ b.toNat + 8 * m ≤ a.toNat

/-- The `n` words at `a` are `f`. -/
def At (mem : UInt64 → Option UInt64) (a : UInt64) (n : Nat) (f : Nat → UInt64) : Prop :=
  ∀ k < n, mem (adr a k) = some (f k)

/-- The context's words the decoder reads or writes: up to the end of the scratch. -/
def ctxN : Nat := cScr + scratchWords

/-- The decoder's environment: the memory at the start, the context, the wire's words and their
byte count, the decoded and working areas. -/
structure Env where
  m0 : UInt64 → Option UInt64
  x : UInt64
  wa : UInt64
  da : UInt64
  wk : UInt64
  ws : List UInt64
  L : Nat

/-- The decoded area's words. -/
abbrev Env.dn (e : Env) : Nat := decodedWords e.L

/-- The wire's bytes. -/
def Env.B (e : Env) : List UInt8 := (wordsBytes e.ws).take e.L

/-- **What the caller provides**: the context (its words `0`, `1`, `8` to `11` as
`NativeVm.Input` says, its scratch), the wire's words holding `L < 2^32` bytes, the decoded and
working areas, at least as large as the decoder needs, all apart and below `2^64`. -/
structure Pre (e : Env) : Prop where
  fx : Fit e.x ctxN
  fw : Fit e.wa e.ws.length
  fd : Fit e.da e.dn
  fk : Fit e.wk workWords
  xw : Apart e.x ctxN e.wa e.ws.length
  xd : Apart e.x ctxN e.da e.dn
  xk : Apart e.x ctxN e.wk workWords
  wd : Apart e.wa e.ws.length e.da e.dn
  wk' : Apart e.wa e.ws.length e.wk workWords
  dk : Apart e.da e.dn e.wk workWords
  hold : HoldsBytes e.ws e.L
  L32 : e.L < 2 ^ 32
  c0 : e.m0 (adr e.x cWire) = some e.wa
  c1 : e.m0 (adr e.x cLen) = some e.L.toUInt64
  c8 : e.m0 (adr e.x cDec) = some e.da
  c9 : ∃ v, e.m0 (adr e.x cDecN) = some v ∧ e.dn ≤ v.toNat
  c10 : e.m0 (adr e.x cWork) = some e.wk
  c11 : ∃ v, e.m0 (adr e.x cWorkN) = some v ∧ workWords ≤ v.toNat
  scr : ∀ k < scratchWords, (e.m0 (adr e.x (cScr + k))).isSome
  wire : At e.m0 e.wa e.ws.length fun i ↦ e.ws.getD i 0
  dec : ∀ k < e.dn, (e.m0 (adr e.da k)).isSome
  work : ∀ k < workWords, (e.m0 (adr e.wk k)).isSome

/-- An address outside the scratch and the two areas. -/
def Out (e : Env) (a : UInt64) : Prop :=
  (∀ k < scratchWords, a ≠ adr e.x (cScr + k)) ∧ (∀ k < e.dn, a ≠ adr e.da k) ∧
    ∀ k < workWords, a ≠ adr e.wk k

/-- **The decoder's invariant**: `rdi` at the context, every word outside the scratch and the
areas as at the start, the scratch's words present, the areas holding `D` and `W`. -/
structure Inv (e : Env) (s : QState) (D W : Nat → UInt64) : Prop where
  rdi : s.reg .rdi = e.x
  out : ∀ a, Out e a → s.mem a = e.m0 a
  scr : ∀ k < scratchWords, (s.mem (adr e.x (cScr + k))).isSome
  dec : At s.mem e.da e.dn D
  work : At s.mem e.wk workWords W

/-- What every exit keeps: `rdi` at the context, every word outside the scratch and the areas. -/
def Kept (e : Env) (s : QState) : Prop := s.reg .rdi = e.x ∧ ∀ a, Out e a → s.mem a = e.m0 a

theorem Inv.kept {e : Env} {s : QState} {D W : Nat → UInt64} (h : Inv e s D W) : Kept e s :=
  ⟨h.rdi, h.out⟩

/-! ## Addresses -/


theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem adr_toNat {a : UInt64} {n k : Nat} (hf : Fit a n) (hk : k < n) :
    (adr a k).toNat = a.toNat + 8 * k := by
  unfold Fit at hf
  rw [adr, UInt64.toNat_add, toNat_toUInt64 (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem adr_inj {a : UInt64} {n k j : Nat} (hf : Fit a n) (hk : k < n) (hj : j < n)
    (h : adr a k = adr a j) : k = j := by
  have := congrArg UInt64.toNat h
  rw [adr_toNat hf hk, adr_toNat hf hj] at this
  omega

theorem adr_ne {a b : UInt64} {n m k j : Nat} (ha : Fit a n) (hb : Fit b m) (hab : Apart a n b m)
    (hk : k < n) (hj : j < m) : adr a k ≠ adr b j := fun h ↦ by
  have := congrArg UInt64.toNat h
  rw [adr_toNat ha hk, adr_toNat hb hj] at this
  unfold Apart at hab
  omega

theorem adr_add (a : UInt64) (j k : Nat) : adr a j + (8 * k).toUInt64 = adr a (j + k) := by
  simp only [adr, Nat.toUInt64_eq, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]

theorem adr_zero (a : UInt64) : adr a 0 = a := by simp [adr]

/-- A displacement `wd k` is `8 k`. -/
theorem wd_toUInt64 (k : Nat) : (wd k).toUInt64 = (8 * k).toUInt64 := by
  unfold wd
  rw [Int64.toUInt64_ofNat']

theorem eval_rw (s : QState) (r : Reg64) {a : UInt64} {j : Nat} (hr : s.reg r = adr a j)
    (k : Nat) : (rw r k).eval s = adr a (j + k) := by
  simp only [rw, at_, Addr.eval, hr, UInt64.add_zero, wd_toUInt64, adr_add]

theorem eval_ix (s : QState) (b i : Reg64) {a : UInt64} {j n : Nat} (hb : s.reg b = adr a j)
    (hi : s.reg i = n.toUInt64) (k : Nat) :
    (ix b i k).eval s = adr a (j + n + k) := by
  simp only [Addr.eval, hb, hi, Width.bytes, wd_toUInt64]
  rw [show (8 : Nat).toUInt64 = 8 from rfl, UInt64.mul_comm, show (8 : UInt64) * n.toUInt64 =
    (8 * n).toUInt64 by simp [Nat.toUInt64_eq, UInt64.ofNat_mul], adr_add, adr_add]

theorem eval_cw (s : QState) {e : Env} (hr : s.reg .rdi = e.x) (k : Nat) :
    (cw k).eval s = adr e.x k := by
  have := eval_rw s .rdi (a := e.x) (j := 0) (by rw [hr, adr_zero]) k
  simpa using this

/-! ## The areas apart -/

section Pre

variable {e : Env} (P : Pre e)
include P

theorem Pre.out_ctx {k : Nat} (hk : k < cScr) : Out e (adr e.x k) := by
  have hx : Fit e.x ctxN := P.fx
  refine ⟨fun j hj h ↦ ?_, fun j hj ↦ adr_ne hx P.fd P.xd (by unfold ctxN cScr at *; omega) hj,
    fun j hj ↦ adr_ne hx P.fk P.xk (by unfold ctxN cScr at *; omega) hj⟩
  have := adr_inj hx (by unfold ctxN cScr at *; omega) (by unfold ctxN; omega) h
  omega

theorem Pre.out_wire {i : Nat} (hi : i < e.ws.length) : Out e (adr e.wa i) :=
  ⟨fun j hj ↦ (adr_ne P.fx P.fw P.xw (by unfold ctxN; omega) hi).symm,
    fun j hj ↦ adr_ne P.fw P.fd P.wd hi hj, fun j hj ↦ adr_ne P.fw P.fk P.wk' hi hj⟩

theorem Pre.scr_ne_dec {k j : Nat} (hk : k < scratchWords) (hj : j < e.dn) :
    adr e.x (cScr + k) ≠ adr e.da j := adr_ne P.fx P.fd P.xd (by unfold ctxN; omega) hj

theorem Pre.scr_ne_work {k j : Nat} (hk : k < scratchWords) (hj : j < workWords) :
    adr e.x (cScr + k) ≠ adr e.wk j := adr_ne P.fx P.fk P.xk (by unfold ctxN; omega) hj

theorem Pre.dec_ne_work {k j : Nat} (hk : k < e.dn) (hj : j < workWords) :
    adr e.da k ≠ adr e.wk j := adr_ne P.fd P.fk P.dk hk hj

/-- The invariant at the start. -/
theorem Pre.inv0 {s : QState} (hm : s.mem = e.m0) (hr : s.reg .rdi = e.x) :
    Inv e s (fun k ↦ (e.m0 (adr e.da k)).getD 0) (fun k ↦ (e.m0 (adr e.wk k)).getD 0) := by
  refine ⟨hr, fun a _ ↦ by rw [hm], fun k hk ↦ by rw [hm]; exact P.scr k hk,
    fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · rw [hm]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (P.dec k hk)
    simp [hv]
  · rw [hm]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (P.work k hk)
    simp [hv]

/-! ## The invariant under updates -/

omit P in
theorem Inv.setReg {s : QState} {D W : Nat → UInt64} (hI : Inv e s D W) {d : Reg64}
    (hd : d ≠ .rdi) (v : UInt64) : Inv e (s.setReg d v) D W :=
  ⟨by simp [hI.rdi, Ne.symm hd], hI.out, hI.scr, hI.dec, hI.work⟩

theorem Inv.storeWork {s : QState} {D W : Nat → UInt64} (hI : Inv e s D W) {k : Nat}
    (hk : k < workWords) (v : UInt64) :
    Inv e (s.setMem (adr e.wk k) v) D (Function.update W k v) := by
  refine ⟨hI.rdi, fun a ha ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · rw [QState.setMem_mem, ite_no (ha.2.2 k hk)]; exact hI.out a ha
  · rw [QState.setMem_mem, ite_no (P.scr_ne_work hj hk)]; exact hI.scr j hj
  · rw [QState.setMem_mem, ite_no (P.dec_ne_work hj hk)]; exact hI.dec j hj
  · rw [QState.setMem_mem, Function.update_apply]
    by_cases h : j = k
    · subst h; simp
    · rw [ite_no fun e' ↦ h (adr_inj P.fk hj hk e'), ite_no h]; exact hI.work j hj

theorem Inv.storeDec {s : QState} {D W : Nat → UInt64} (hI : Inv e s D W) {k : Nat}
    (hk : k < e.dn) (v : UInt64) :
    Inv e (s.setMem (adr e.da k) v) (Function.update D k v) W := by
  refine ⟨hI.rdi, fun a ha ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · rw [QState.setMem_mem, ite_no (ha.2.1 k hk)]; exact hI.out a ha
  · rw [QState.setMem_mem, ite_no (P.scr_ne_dec hj hk)]; exact hI.scr j hj
  · rw [QState.setMem_mem, Function.update_apply]
    by_cases h : j = k
    · subst h; simp
    · rw [ite_no fun e' ↦ h (adr_inj P.fd hj hk e'), ite_no h]; exact hI.dec j hj
  · rw [QState.setMem_mem, ite_no (P.dec_ne_work hk hj).symm]; exact hI.work j hj

/-! ## Loads and stores at the head of a block -/

variable {s : QState} {D W : Nat → UInt64} {Q F : QState → Prop} {rest : List Stmt}

theorem blk_load_ctx (hI : Inv e s D W) {d : Reg64} {ad : Addr} {k : Nat} {v : UInt64}
    (ha : ad.eval s = adr e.x k) (hk : k < cScr) (hv : e.m0 (adr e.x k) = some v)
    (h : WP (blk rest) (s.setReg d v) Q F) : WP (blk (I (.load d ad) :: rest)) s Q F := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hI.out _ (P.out_ctx hk), hv, Option.map_some]
  exact h

theorem blk_load_wire (hI : Inv e s D W) {d : Reg64} {ad : Addr} {i : Nat}
    (ha : ad.eval s = adr e.wa i) (hi : i < e.ws.length)
    (h : WP (blk rest) (s.setReg d (e.ws.getD i 0)) Q F) :
    WP (blk (I (.load d ad) :: rest)) s Q F := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hI.out _ (P.out_wire hi), P.wire i hi, Option.map_some]
  exact h

omit P in
theorem blk_load_work (hI : Inv e s D W) {d : Reg64} {ad : Addr} {k : Nat}
    (ha : ad.eval s = adr e.wk k) (hk : k < workWords)
    (h : WP (blk rest) (s.setReg d (W k)) Q F) : WP (blk (I (.load d ad) :: rest)) s Q F := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hI.work k hk, Option.map_some]
  exact h

omit P in
theorem blk_load_dec (hI : Inv e s D W) {d : Reg64} {ad : Addr} {k : Nat}
    (ha : ad.eval s = adr e.da k) (hk : k < e.dn)
    (h : WP (blk rest) (s.setReg d (D k)) Q F) : WP (blk (I (.load d ad) :: rest)) s Q F := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hI.dec k hk, Option.map_some]
  exact h

/-- A store to the working area's word `k`, the state after it abstracted. -/
theorem blk_store_work (hI : Inv e s D W) {r : Reg64} {ad : Addr} {k : Nat}
    (ha : ad.eval s = adr e.wk k) (hk : k < workWords)
    (h : ∀ s', Inv e s' D (Function.update W k (s.reg r)) → s'.reg = s.reg →
      WP (blk rest) s' Q F) : WP (blk (I (.store ad r) :: rest)) s Q F := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hI.work k hk, Option.map_some]
  exact h _ (hI.storeWork P hk _) rfl

theorem blk_storei_work (hI : Inv e s D W) {c : Int64} {ad : Addr} {k : Nat}
    (ha : ad.eval s = adr e.wk k) (hk : k < workWords)
    (h : ∀ s', Inv e s' D (Function.update W k c.toUInt64) → s'.reg = s.reg →
      WP (blk rest) s' Q F) : WP (blk (I (.storei ad c) :: rest)) s Q F := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hI.work k hk, Option.map_some]
  exact h _ (hI.storeWork P hk _) rfl

/-- A store to the decoded area's word `k`, the state after it abstracted. -/
theorem blk_store_dec (hI : Inv e s D W) {r : Reg64} {ad : Addr} {k : Nat}
    (ha : ad.eval s = adr e.da k) (hk : k < e.dn)
    (h : ∀ s', Inv e s' (Function.update D k (s.reg r)) W → s'.reg = s.reg →
      WP (blk rest) s' Q F) : WP (blk (I (.store ad r) :: rest)) s Q F := by
  apply WP.blk_cons
  apply WP.ins'
  simp only [QInstr.step, ha, hI.dec k hk, Option.map_some]
  exact h _ (hI.storeDec P hk _) rfl

end Pre

/-- An instruction that does not touch memory, at the head of a block. -/
theorem blk_ins {s : QState} {Q F : QState → Prop} {i : QInstr} {rest : List Stmt}
    (h : match i.step s with | some s' => WP (blk rest) s' Q F | none => False) :
    WP (blk (I i :: rest)) s Q F :=
  WP.blk_cons (WP.ins' h)

@[simp] theorem QState.setReg_setReg_same (s : QState) (r : Reg64) (a b : UInt64) :
    (s.setReg r a).setReg r b = s.setReg r b := by
  simp [QState.setReg]

/-- Run one instruction that does not touch memory at the head of a block. -/
macro "step" : tactic => `(tactic| (apply blk_ins; simp only [QInstr.step, QState.setReg_reg,
  QState.setReg_setReg_same, QState.setMem_reg, reduceCtorEq, ite_true, ite_false]))

end NativeVm.Wire
