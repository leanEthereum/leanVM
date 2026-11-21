module

public import NativeVm.Code.Data
public import NativeVm.Equiv.Field

/-!
# Phase 6's scratch as a function

Phase 6 keeps all its working values in the scratch region (`scratchR`), viewed as `scrN` elements
of `E`, element `k` in the region's words `2 k`, `2 k + 1` (limb `0` first). `Scr mem p f`: the
scratch at `p` holds `f`, every element; a store of an element updates `f` there (`Scr.store`), and a
run that writes no scratch word keeps `f`. Counters and constant tables are elements too, a word
`w` as `EW.ofK w`.

`tab o bound val`: a loop over `m` from `0` while `m < bound`, the counter in `r15`, that writes
the element `o + m` from `(r9, r10)` as `val` leaves them; `tab_spec` proves it writes `F m` there
from `val`'s spec, the scratch `f0` overwritten on `[o, o + m)` (`ovr`) while it runs, so a `val`
may read anything outside the elements written so far.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model
open NativeVm.Transcript (wd wd_add wd_zero wd_inj wdisp wdisp_toUInt64)
open NativeVm.Field (eOf eOf_inj)

/-! ## The scratch -/

/-- The scratch's elements. -/
def scrN : Nat := scratchWords / 2

theorem scrN_val : scrN = 16384 := by decide

/-- The scratch holds `f`: element `k` in the words `2 k`, `2 k + 1` from `p`. -/
def Scr (mem : UInt64 → Option UInt64) (p : UInt64) (f : Nat → EW) : Prop :=
  ∀ k < scrN, mem (wd p (2 * k)) = some (f k).c0 ∧ mem (wd p (2 * k + 1)) = some (f k).c1

/-- The address `a` is a word of the scratch. -/
def InScr (p : UInt64) (a : UInt64) : Prop := ∃ k < 2 * scrN, a = wd p k

/-- `f0`, its elements `[o, o + m)` overwritten by `F`. -/
def ovr (f0 : Nat → EW) (o m : Nat) (F : Nat → EW) (k : Nat) : EW :=
  if o ≤ k ∧ k < o + m then F (k - o) else f0 k

theorem ovr_zero (f0 : Nat → EW) (o : Nat) (F : Nat → EW) : ovr f0 o 0 F = f0 := by
  funext k; simp only [ovr]; split <;> [omega; rfl]

theorem ovr_out {f0 : Nat → EW} {o m : Nat} {F : Nat → EW} {k : Nat} (h : k < o ∨ o + m ≤ k) :
    ovr f0 o m F k = f0 k := by
  simp only [ovr]; split <;> [omega; rfl]

theorem ovr_in {f0 : Nat → EW} {o m : Nat} {F : Nat → EW} {k : Nat} (h1 : o ≤ k) (h2 : k < o + m) :
    ovr f0 o m F k = F (k - o) := by
  simp only [ovr]; split <;> [rfl; omega]

theorem ovr_succ (f0 : Nat → EW) (o m : Nat) (F : Nat → EW) :
    Function.update (ovr f0 o m F) (o + m) (F m) = ovr f0 o (m + 1) F := by
  funext k
  rw [Function.update_apply]
  split
  · subst k; rw [ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]
  · simp only [ovr]; split <;> split <;> first | rfl | omega

theorem scrN_lt : scrN < 2 ^ 20 := by rw [scrN_val]; norm_num

theorem wd_ne_el {p : UInt64} {a b : Nat} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (h : a ≠ b) :
    wd p a ≠ wd p b := fun e ↦ h ((wd_inj ha hb).mp e)

/-- **A store of element `k`**: the scratch holds `f` updated at `k`. -/
theorem Scr.store {mem : UInt64 → Option UInt64} {p : UInt64} {f : Nat → EW} (h : Scr mem p f)
    {k : Nat} (hk : k < scrN) (x : EW) :
    Scr (Function.update (Function.update mem (wd p (2 * k)) (some x.c0)) (wd p (2 * k + 1))
      (some x.c1)) p (Function.update f k x) := by
  have hN := scrN_lt
  intro j hj
  rw [Function.update_apply, Function.update_apply, Function.update_apply, Function.update_apply,
    Function.update_apply]
  by_cases hjk : j = k
  · subst hjk
    simp only [wd_ne_el (p := p) (a := 2 * j) (b := 2 * j + 1) (by omega) (by omega) (by omega),
      ite_true, ite_false]
    exact ⟨trivial, trivial⟩
  · have e1 := wd_ne_el (p := p) (a := 2 * j) (b := 2 * k + 1) (by omega) (by omega) (by omega)
    have e2 := wd_ne_el (p := p) (a := 2 * j) (b := 2 * k) (by omega) (by omega) (by omega)
    have e3 := wd_ne_el (p := p) (a := 2 * j + 1) (b := 2 * k + 1) (by omega) (by omega) (by omega)
    have e4 := wd_ne_el (p := p) (a := 2 * j + 1) (b := 2 * k) (by omega) (by omega) (by omega)
    simp only [e1, e2, e3, e4, hjk, ite_false]
    exact h j hj

/-- A word outside the scratch survives a store of an element. -/
theorem store_out {mem : UInt64 → Option UInt64} {p a : UInt64} (ha : ¬ InScr p a) {k : Nat}
    (hk : k < scrN) (x : EW) :
    Function.update (Function.update mem (wd p (2 * k)) (some x.c0)) (wd p (2 * k + 1))
      (some x.c1) a = mem a := by
  rw [Function.update_apply, Function.update_apply]
  have n1 : a ≠ wd p (2 * k + 1) := fun e ↦ ha ⟨_, by omega, e⟩
  have n2 : a ≠ wd p (2 * k) := fun e ↦ ha ⟨_, by omega, e⟩
  simp only [n1, n2, ite_false]

theorem Scr.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {f : Nat → EW} (h : Scr mem p f)
    (he : ∀ a, InScr p a → mem' a = mem a) : Scr mem' p f := fun k hk ↦ by
  rw [he _ ⟨_, by omega, rfl⟩, he _ ⟨_, by omega, rfl⟩]
  exact h k hk

theorem Scr.word0 {mem : UInt64 → Option UInt64} {p : UInt64} {f : Nat → EW} (h : Scr mem p f)
    {k : Nat} (hk : k < scrN) : mem (wd p (2 * k)) = some (f k).c0 := (h k hk).1

theorem Scr.word1 {mem : UInt64 → Option UInt64} {p : UInt64} {f : Nat → EW} (h : Scr mem p f)
    {k : Nat} (hk : k < scrN) : mem (wd p (2 * k + 1)) = some (f k).c1 := (h k hk).2

/-! ## Addresses -/

theorem eval_at' (r : Reg64) (d : Int64) (s : QState) :
    (at_ r d).eval s = s.reg r + d.toUInt64 := by
  simp [Addr.eval, at_]

/-- Element `k` of the scratch at a constant displacement from `rbp`. -/
theorem eval_el {s : QState} {p : UInt64} (hp : s.reg .rbp = p) (j : Nat) :
    (at_ .rbp (wdisp j)).eval s = wd p j := by
  rw [eval_at', hp, wdisp_toUInt64, show (8 * j).toUInt64 = (8 * j).toUInt64 from rfl]
  rfl

theorem shl4_toUInt64 (m : Nat) : m.toUInt64 <<< (4 : UInt64) = (8 * (2 * m)).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
  norm_num
  omega

/-- The element `o + m` from `rbp`, `16 m` in `rax`. -/
theorem eval_idx {s : QState} {p : UInt64} (hp : s.reg .rbp = p) {i : Nat}
    (hi : s.reg .rax = (8 * i).toUInt64) (j : Nat) :
    ({ base := .rbp, idx := some (.rax, .W8), disp := wdisp j } : Addr).eval s = wd p (i + j) := by
  simp only [Addr.eval, hp, hi, wdisp_toUInt64]
  rw [show Width.W8.bytes.toUInt64 = 1 from rfl, UInt64.mul_one, ← wd_add p i j]
  rfl

/-! ## Tabulation -/

/-- The element `o + d + m`, `m` the counter in `r15` and `d` in `r14`, from `(r9, r10)`, then the
counter's step. -/
def tabStore (o : Nat) : List Stmt := [I (.mov .rax .r15), I (.add .rax .r14), I (.shli .rax 4),
  I (.store { base := .rbp, idx := some (.rax, .W8), disp := wdisp (2 * o) } .r9),
  I (.store { base := .rbp, idx := some (.rax, .W8), disp := wdisp (2 * o + 1) } .r10),
  I (.addi .r15 1)]

/-- **Tabulate**: for `m` from `0` while `m < bound`, `val` then the element `o + d + m` written, `d`
in `r14`. -/
def tab (o : Nat) (bound : Rhs) (val : Stmt) : Stmt :=
  blk [I (.movi .r15 0), .loop (.cmp .ltu .r15 bound) (blk (val :: tabStore o))]

theorem toUInt64_lt' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a.toUInt64 < b.toUInt64 ↔ a < b := NativeVm.Transcript.toUInt64_lt ha hb

theorem toNat_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n :=
  NativeVm.Transcript.toNat_toUInt64 h

/-- The store of `tab`'s pass: the element `o + d + m` from `(r9, r10)`, the counter stepped. -/
theorem tabStore_spec {o d m : Nat} {p : UInt64} {f : Nat → EW} {s : QState} {E : QState → Prop}
    (hk : o + d + m < scrN) (hp : s.reg .rbp = p) (h14 : s.reg .r14 = d.toUInt64)
    (h15 : s.reg .r15 = m.toUInt64) (hs : Scr s.mem p f)
    (x : EW) (h9 : s.reg .r9 = x.c0) (h10 : s.reg .r10 = x.c1) :
    WP (blk (tabStore o)) s (fun s' ↦ Scr s'.mem p (Function.update f (o + d + m) x) ∧
      (∀ a, ¬ InScr p a → s'.mem a = s.mem a) ∧ RegsFrame [.rax, .r15] s s' ∧
      s'.reg .r15 = (m + 1).toUInt64) E := by
  have hN := scrN_lt
  have hrax : (m.toUInt64 + d.toUInt64) <<< (4 : Nat).toUInt64 = (8 * (2 * (m + d))).toUInt64 := by
    rw [NativeVm.Transcript.toUInt64_add]; exact shl4_toUInt64 _
  have e0 : 2 * (m + d) + 2 * o = 2 * (o + d + m) := by omega
  have e1 : 2 * (m + d) + (2 * o + 1) = 2 * (o + d + m) + 1 := by omega
  unfold tabStore
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine NativeVm.Transcript.wp_store (eval_idx (p := p) (i := 2 * (m + d)) (by simp [hp])
    (by simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false, h15, h14]; exact hrax) _)
    (by rw [e0, QState.setReg_mem, QState.setReg_mem, QState.setReg_mem, (hs _ hk).1]; rfl) ?_
  refine NativeVm.Transcript.wp_store (eval_idx (p := p) (i := 2 * (m + d)) (by simp [hp])
    (by simp only [QState.setMem_reg, QState.setReg_reg, ite_true, reduceCtorEq, ite_false, h15,
      h14]; exact hrax) _)
    (by
      rw [e1]
      simp only [QState.setMem_mem, QState.setReg_mem]
      split
      · rfl
      · rw [(hs _ hk).2]; rfl) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_)
  rw [e0, e1]
  refine ⟨?_, fun a ha ↦ ?_, ?_, ?_⟩
  · have := hs.store hk x
    simpa [QState.setMem, QState.setReg, h9, h10] using this
  · have := store_out (mem := s.mem) ha hk x
    simpa [QState.setMem, QState.setReg, h9, h10] using this
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [QState.setReg_reg, QState.setMem_reg, ite_true, reduceCtorEq, ite_false, h15]
    exact NativeVm.Transcript.toUInt64_succ m

theorem regsFrame_cons_of {l : List Reg64} {r : Reg64} {s t : QState} (h : RegsFrame l s t) :
    RegsFrame (r :: l) s t := fun q hq ↦ h q fun h' ↦ hq (List.mem_cons_of_mem _ h')

/-- **`tab` writes `F`.** `val` leaves `F m` in `(r9, r10)` from any state that keeps `s`'s registers
outside `rax`, `r15` and `val`'s, with `m` in `r15` and the scratch `f0` overwritten by `F` from
`o + d` below `o + d + m`, without storing; the loop's bound is `N` throughout. -/
theorem tab_spec {o d N : Nat} {bound : Rhs} {val : Stmt} {Lv : List Reg64} {p : UInt64}
    {f0 F : Nat → EW} {s : QState} {E : QState → Prop}
    (hN : o + d + N ≤ scrN) (hp : s.reg .rbp = p) (h14 : s.reg .r14 = d.toUInt64)
    (hscr : Scr s.mem p f0) (hLv : Reg64.rbp ∉ Lv ∧ Reg64.r15 ∉ Lv ∧ Reg64.r14 ∉ Lv)
    (hb : ∀ t, RegsFrame (.rax :: .r15 :: Lv) s t → bound.eval t = N.toUInt64)
    (hval : ∀ m < N, ∀ t, RegsFrame (.rax :: .r15 :: Lv) s t → t.reg .r15 = m.toUInt64 →
      Scr t.mem p (ovr f0 (o + d) m F) → (∀ a, ¬ InScr p a → t.mem a = s.mem a) →
      WP val t (fun t' ↦ eOf (t'.reg .r9) (t'.reg .r10) = (F m).toE ∧ t'.mem = t.mem ∧
        RegsFrame Lv t t') E) :
    WP (tab o bound val) s (fun s' ↦ Scr s'.mem p (ovr f0 (o + d) N F) ∧
      (∀ a, ¬ InScr p a → s'.mem a = s.mem a) ∧ RegsFrame (.rax :: .r15 :: Lv) s s' ∧
      s'.reg .r15 = N.toUInt64) E := by
  have hN' := scrN_lt
  unfold tab
  refine WP.blk_cons (WP.ins (by rfl) ?_)
  apply WP.blk_cons
  refine WP.mono (P := fun s' ↦ Scr s'.mem p (ovr f0 (o + d) N F) ∧
      (∀ a, ¬ InScr p a → s'.mem a = s.mem a) ∧ RegsFrame (.rax :: .r15 :: Lv) s s' ∧
      s'.reg .r15 = N.toUInt64) ?_ (fun _ h ↦ WP.blk_nil h) (fun _ h ↦ h)
  apply WP.loop (fun t ↦ ∃ m ≤ N, t.reg .r15 = m.toUInt64 ∧ Scr t.mem p (ovr f0 (o + d) m F) ∧
      (∀ a, ¬ InScr p a → t.mem a = s.mem a) ∧ RegsFrame (.rax :: .r15 :: Lv) s t)
    (fun t ↦ N - (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, fun _ _ ↦ rfl, ?_⟩
    · simp [QState.setReg]; rfl
    · rw [ovr_zero]; exact hscr
    · intro r hr
      simp only [QState.setReg_reg]
      split
      · subst r; exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) hr
      · rfl
  · intro t ⟨m, _, t15, tS, tM, tR⟩ hc
    have hlt : m < N := by
      have := hb t tR
      simp only [Cond.eval, t15, this, decide_eq_true_eq] at hc
      exact (toUInt64_lt' (by omega) (by omega)).mp hc
    refine WP.blk_cons (WP.mono (hval m hlt t tR t15 tS tM) (fun t₁ ⟨e1, e2, e3⟩ ↦ ?_)
      (fun _ h ↦ h))
    obtain ⟨v9, v10⟩ := eOf_inj.mp (e1.trans (rfl : (F m).toE = eOf (F m).c0 (F m).c1))
    have r15 : t₁.reg .r15 = m.toUInt64 := by rw [e3 .r15 hLv.2.1]; exact t15
    have rbp : t₁.reg .rbp = p := by
      rw [e3 .rbp hLv.1]; exact (tR .rbp (by simp [hLv.1])).trans hp
    have r14 : t₁.reg .r14 = d.toUInt64 := by
      rw [e3 .r14 hLv.2.2]; exact (tR .r14 (by simp [hLv.2.2])).trans h14
    refine WP.mono (tabStore_spec (o := o) (d := d) (m := m) (by omega) rbp r14 r15
      (tS.congr fun a _ ↦ by rw [e2])
      (F m) v9 v10) (fun t' ⟨h1, h2, h3, h4⟩ ↦ ⟨⟨m + 1, hlt, h4, by rw [← ovr_succ]; exact h1,
        fun a ha ↦ by rw [h2 a ha, e2, tM a ha], ?_⟩, ?_⟩) (fun _ h ↦ h)
    · intro r hr
      have hr' : r ∉ [Reg64.rax, Reg64.r15] := fun h ↦ hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
      rw [h3 r hr', e3 r (fun h ↦ hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))]
      exact tR r hr
    · rw [h4, t15]
      rw [toNat_toUInt64' (by omega), toNat_toUInt64' (by omega)]
      omega
  · intro t ⟨m, hm, t15, tS, tM, tR⟩ hc
    have hge : ¬ m < N := by
      have := hb t tR
      simp only [Cond.eval, t15, this, decide_eq_false_iff_not] at hc
      exact fun h ↦ hc ((toUInt64_lt' (by omega) (by omega)).mpr h)
    obtain rfl : m = N := by omega
    exact ⟨tS, tM, tR, t15⟩

end NativeVm.Code.P6
