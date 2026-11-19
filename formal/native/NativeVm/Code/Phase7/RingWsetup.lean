module

public import NativeVm.Code.Phase7.RingBuf

/-!
# `weightRing`'s first part: the buffer

`ringSetup` stores, in the buffer at `rbx`, the coefficients' address (word `0`), twice their
count (word `1`), the point's address (word `2`), the common length `m = min |r| vc |x|`
(word `3`) and a zero sum (words `4`, `5`), and copies `r`'s first `m` elements from word `8` on.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64 wp_store wp_storei)

variable {s : QState} {F : QState → Prop}

/-- The buffer's state, then `r`'s first `m` elements. -/
def ringSetup : Stmt := blk [
  I (.shli .r12 1), minReg .r15 .rdx, minReg .r15 .rbp,
  I (.store (at_ .rbx (wdisp 0)) .r11), I (.store (at_ .rbx (wdisp 1)) .r12),
  I (.store (at_ .rbx (wdisp 2)) .r14), I (.store (at_ .rbx (wdisp 3)) .r15),
  I (.storei (at_ .rbx (wdisp 4)) 0), I (.storei (at_ .rbx (wdisp 5)) 0),
  I (.lea .r8 (at_ .rbx (wdisp 8))), copyLoop]

/-- The buffer's first six words. -/
def setupWords (cp xp : UInt64) (nC m : Nat) : List UInt64 :=
  [cp, (2 * nC).toUInt64, xp, m.toUInt64, 0, 0]

/-- What `ringSetup` leaves. -/
structure SetupPost (s t : QState) (b cp xp : UInt64) (R : List E) (nC m : Nat) : Prop where
  words : ∀ j < 6, t.mem (ew b j) = some ((setupWords cp xp nC m).getD j 0)
  rs : EArr t.mem (ew b 8) (R.take m)
  frame : ∀ a, (∀ k < bufWords, a ≠ ew b k) → t.mem a = s.mem a

theorem ew8 (b : UInt64) (k : Nat) : ew (ew b 8) k = ew b (8 + k) := ew_ew b 8 k

/-- The copy, from a state holding the buffer's first six words. -/
theorem setupTail_spec {u : QState} {R : List E} {b cp rp xp : UInt64} {nC m : Nat}
    (hbx : u.reg .rbx = b) (h13 : u.reg .r13 = rp) (h15 : u.reg .r15 = m.toUInt64)
    (hmR : m ≤ R.length) (hRl : R.length ≤ 36)
    (hW : ∀ j < 6, u.mem (ew b j) = some ((setupWords cp xp nC m).getD j 0))
    (hF : ∀ a, (∀ k < bufWords, a ≠ ew b k) → u.mem a = s.mem a)
    (hdom : ∀ k < bufWords, (u.mem (ew b k)).isSome) (hR : EArr s.mem rp R)
    (hsR : ∀ k < bufWords, ∀ j < 2 * R.length, ew b k ≠ ew rp j) :
    WP (blk [I (.lea .r8 (at_ .rbx (wdisp 8))), copyLoop]) u
      (fun t ↦ SetupPost s t b cp xp R nC m) F := by
  have hl : (R.take m).length = m := by rw [List.length_take]; omega
  fstep
  rw [eval_w hbx 8]
  refine WP.then (copyLoop_spec (xs := R.take m) (p := rp) (q := ew b 8) (by rsimp; exact h13)
    (by rsimp) (EArr_apart hF (fun k hk j hj ↦ hsR k hk j (by rw [hl] at hj; omega))
      (Ring.EArr.take hR m)) (by rsimp; rw [hl]; exact h15) (by rw [hl]; omega)
    (fun k hk ↦ by rw [ew8]; exact hdom _ (by rw [hl] at hk; unfold bufWords; omega))
    (fun k hk j hj ↦ by
      rw [ew8]; exact hsR _ (by rw [hl] at hk; unfold bufWords; omega) j (by rw [hl] at hj; omega)))
    fun t ⟨hc, hcF⟩ ↦ ?_
  fdone
  have off : ∀ j < 8, ∀ k < 2 * (R.take m).length, ew b j ≠ ew (ew b 8) k := fun j hj k hk ↦ by
    rw [ew8]; exact ew_ne _ (by omega) (by rw [hl] at hk; omega) (by omega)
  refine ⟨fun j hj ↦ ?_, hc, fun a ha ↦ ?_⟩
  · rw [hcF _ (off j (by omega))]
    exact hW j hj
  · rw [hcF a fun k hk ↦ by
      rw [ew8]; exact ha _ (by rw [hl] at hk; unfold bufWords; omega)]
    exact hF a ha

/-- **`ringSetup` fills the buffer.** -/
theorem ringSetup_spec {R : List E} {b cp rp xp : UInt64} {nC vc nX : Nat}
    (hbx : s.reg .rbx = b) (h11 : s.reg .r11 = cp) (h12 : s.reg .r12 = nC.toUInt64)
    (h13 : s.reg .r13 = rp) (h14 : s.reg .r14 = xp) (h15 : s.reg .r15 = R.length.toUInt64)
    (hdx : s.reg .rdx = vc.toUInt64) (hbp : s.reg .rbp = nX.toUInt64) (hR : EArr s.mem rp R)
    (hRl : R.length ≤ 36) (hnX : nX < 2 ^ 32) (hvc : vc < 2 ^ 64)
    (hdom : ∀ k < bufWords, (s.mem (ew b k)).isSome)
    (hsR : ∀ k < bufWords, ∀ j < 2 * R.length, ew b k ≠ ew rp j) :
    WP ringSetup s (fun t ↦ SetupPost s t b cp xp R nC (min (min R.length vc) nX)) F := by
  unfold ringSetup
  fstep
  refine WP.then (minReg_spec (x := R.length) (y := vc) (by rsimp; exact h15) (by rsimp; exact hdx)
    (by omega) hvc) fun t1 e1 ↦ ?_
  subst e1
  refine WP.then (minReg_spec (x := min R.length vc) (y := nX) (by rsimp) (by rsimp; exact hbp)
    (by omega) (by omega)) fun t2 e2 ↦ ?_
  subst e2
  have d : ∀ j < 6, (s.mem (ew b j)).isSome := fun j hj ↦ hdom j (by unfold bufWords; omega)
  refine wp_store (eval_w (by rsimp; exact hbx) 0) (by rsimp; exact d 0 (by decide)) ?_
  refine wp_store (eval_w (by rsimp; exact hbx) 1)
    (by rsimp; exact isSome_setMem (d 1 (by decide)) _ _) ?_
  refine wp_store (eval_w (by rsimp; exact hbx) 2)
    (by rsimp; exact isSome_setMem (isSome_setMem (d 2 (by decide)) _ _) _ _) ?_
  refine wp_store (eval_w (by rsimp; exact hbx) 3)
    (by rsimp; exact isSome_setMem (isSome_setMem (isSome_setMem (d 3 (by decide)) _ _) _ _) _ _) ?_
  refine wp_storei (eval_w (by rsimp; exact hbx) 4)
    (by rsimp; exact isSome_setMem (isSome_setMem (isSome_setMem (isSome_setMem
      (d 4 (by decide)) _ _) _ _) _ _) _ _) ?_
  refine wp_storei (eval_w (by rsimp; exact hbx) 5)
    (by rsimp; exact isSome_setMem (isSome_setMem (isSome_setMem (isSome_setMem (isSome_setMem
      (d 5 (by decide)) _ _) _ _) _ _) _ _) _ _) ?_
  refine setupTail_spec (by rsimp; exact hbx) (by rsimp; exact h13) (by rsimp)
    (by omega) hRl (fun j hj ↦ ?_) (fun a ha ↦ ?_) (fun k hk ↦ ?_) hR hsR
  · interval_cases j <;>
      simp (disch := omega) only [setMem_ew, QState.setMem_reg, QState.setReg_reg, Nat.reduceEqDiff,
        ↓reduceIte, reduceCtorEq, setupWords, List.getD_cons_zero, List.getD_cons_succ] <;>
      simp only [h11, h12, h14, shl1, int64Zero_toUInt64]
  · simp only [QState.setMem_mem, QState.setReg_mem, ha 0 (by decide), ha 1 (by decide),
      ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ↓reduceIte]
  · exact isSome_setMem (isSome_setMem (isSome_setMem (isSome_setMem (isSome_setMem
      (isSome_setMem (hdom k hk) _ _) _ _) _ _) _ _) _ _) _ _

end NativeVm.Code.Ring
