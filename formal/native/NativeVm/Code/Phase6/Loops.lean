module

public import NativeVm.Code.Phase6.Gad

/-!
# Reading and sampling runs of elements into the scratch

`rdN o n` reads `n` scalars into the elements `[o, o + n)` (`rdN_refines`, against
`readScalars n`), `smpN o n` samples `n` challenges there (`smpN_refines`, against
`sampleChallenges n`); the counter is `r15`, `r14` is `0` (`tab`'s store).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code
open NativeVm.Transcript (wd wd_add wd_zero wd_inj wdisp wdisp_toUInt64 Env Foot clobbers Keeps)

variable {env : Env} {inp : Input} {s0 s s' : QState} {t : TState} {f f' : Nat → EW}

/-- The array `a` written from `o`: `f` overwritten on `[o, o + a.size)`. -/
def wrA (f : Nat → EW) (o : Nat) (a : Array EW) : Nat → EW := ovr f o a.size fun i ↦ a.getD i 0

theorem wrA_empty (f : Nat → EW) (o : Nat) : wrA f o #[] = f := ovr_zero f o _

theorem wrA_push (f : Nat → EW) (o : Nat) (a : Array EW) (x : EW) :
    Function.update (wrA f o a) (o + a.size) x = wrA f o (a.push x) := by
  rw [wrA, wrA, Array.size_push]
  funext k
  rw [Function.update_apply]
  split
  · subst k; rw [ovr_in (by omega) (by omega), Nat.add_sub_cancel_left, Array.getD_eq_getD_getElem?,
      Array.getElem?_push_size]; rfl
  · simp only [ovr]
    split <;> split
    · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push]
      split
      · omega
      · rfl
    · omega
    · omega
    · rfl

theorem wrA_in {f : Nat → EW} {o : Nat} {a : Array EW} {i : Nat} (hi : i < a.size) :
    wrA f o a (o + i) = a.getD i 0 := by
  rw [wrA, ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]

theorem wrA_out {f : Nat → EW} {o : Nat} {a : Array EW} {k : Nat} (h : k < o ∨ o + a.size ≤ k) :
    wrA f o a k = f k := ovr_out h

/-- Stability of `X6` with fixed registers outside the clobbers. -/
def XR (env : Env) (f : Nat → EW) (k : Nat) (s : QState) : Prop :=
  X6 env f s ∧ s.reg .r15 = k.toUInt64 ∧ s.reg .r14 = (0 : Nat).toUInt64

theorem stable_XR (hin : Inputs env inp s0.mem) (k : Nat) : Stable env (XR env f k) :=
  fun s s' ⟨hx, h15, h14⟩ hk ↦ ⟨stable_X6 hin s s' hx hk, (hk.regs .r15 (by decide)).trans h15,
    (hk.regs .r14 (by decide)).trans h14⟩

/-- `n` elements read or sampled into `[o, o + n)`, by `g` (`readScalar` or `sampleChallenge`). -/
def gN (g : Stmt) (o n : Nat) : Stmt := blk [I (.movi .r14 0), I (.movi .r15 0),
  .loop (.cmp .ltu .r15 (.imm (Int64.ofNat n))) (blk (g :: tabStore o))]

/-- `readScalars` into `[o, o + n)`. -/
def rdN (o n : Nat) : Stmt := gN Transcript.readScalar o n

/-- `sampleChallenges` into `[o, o + n)`. -/
def smpN (o n : Nat) : Stmt := gN Transcript.sampleChallenge o n

theorem foldlM_push_run (m : VM EW) (n : Nat) :
    ((List.range n).foldlM (fun acc _ ↦ do pure (acc.push (← m))) (#[] : Array EW)) =
      (List.range n).foldlM (fun acc _ ↦ m >>= fun x ↦ pure (acc.push x)) #[] := rfl

variable (env inp s0)

theorem gN_refines {g : Stmt} {m : VM EW} (hin : Inputs env inp s0.mem) {o n : Nat}
    (hn : o + n ≤ scrN) (hn' : n < 2 ^ 63)
    (hg : ∀ (k : Nat) (f : Nat → EW), Refines (fun t s ↦ CodeRel env t s ∧ Fr env rs6 s0 (XR env f k) s)
      g m (fun x t' s' ↦ CodeRel env t' s' ∧ Fr env rs6 s0 (XR env f k) s' ∧ s'.reg .r9 = x.c0 ∧
        s'.reg .r10 = x.c1) (Kept env rs6 s0))
    (f : Nat → EW) :
    Refines (St env s0 f) (gN g o n)
      ((List.range n).foldlM (fun acc _ ↦ m >>= fun x ↦ pure (acc.push x)) #[])
      (fun xs t s ↦ xs.size = n ∧ St env s0 (wrA f o xs) t s) (Kept env rs6 s0) := by
  have hN := scrN_lt
  unfold gN
  refine Refines.pre_blk (P' := fun t s ↦ St env s0 f t s ∧ s.reg .r14 = (0 : Nat).toUInt64)
    (fun t s ⟨hc, hb, hp, hs⟩ ↦ WP.ins (by rfl)
      ⟨⟨hc.setReg (r := .r14) (by decide) _, hb.setReg (d := .r14) (by decide) _,
        by rw [QState.setReg_reg]; exact hp, hs.congr fun _ _ ↦ rfl⟩,
        by simp only [QState.setReg_reg, ↓reduceIte]; rfl⟩) ?_
  refine Refines.pre_blk (P' := fun t s ↦ CodeRel env t s ∧ Fr env rs6 s0 (XR env (wrA f o #[]) 0) s)
    (fun t s ⟨⟨hc, hb, hp, hs⟩, h14⟩ ↦ WP.ins (by rfl)
      ⟨hc.setReg (r := .r15) (by decide) _, hb.setReg (d := .r15) (by decide) _,
        ⟨by rw [QState.setReg_reg]; exact hp,
        by rw [wrA_empty]; exact hs.congr fun _ _ ↦ rfl⟩,
        by simp only [QState.setReg_reg, ↓reduceIte]; rfl,
        by rw [QState.setReg_reg, NativeVm.Transcript.ite_of_not (by decide)]; exact h14⟩) ?_
  refine Refines.mono (Refines.foldlM
    (Inv := fun k acc t s ↦ k ≤ n ∧ acc.size = k ∧ CodeRel env t s ∧
      Fr env rs6 s0 (XR env (wrA f o acc) k) s)
    (fun k acc t s ⟨hk, _, _, _, ⟨_, h15, _⟩⟩ ↦ by
      simp only [Cond.eval, h15, Rhs.eval, decide_eq_true_eq, List.length_range]
      rw [show (Int64.ofNat n).toUInt64 = n.toUInt64 from rfl]
      exact toUInt64_lt' (a := k) (b := n) (by omega) (by omega)) ?_)
    (fun t s h ↦ ⟨Nat.zero_le _, rfl, h⟩)
    (fun xs t s ⟨_, h1, h2, h3, h4, _⟩ ↦ ⟨by simpa using h1, h2, h3, h4.1, h4.2⟩) (fun _ h ↦ h)
  intro k hk acc
  rw [List.length_range] at hk
  refine Refines.intro fun _ ↦ Refines.intro fun hacc ↦ Refines.blk_cons (hg k (wrA f o acc))
    fun x ↦ Refines.pure fun t s ⟨hc, ⟨hb, ⟨hp, hs⟩, h15, h14⟩, h9, h10⟩ ↦ ?_
  have := St.step (f' := Function.update (wrA f o acc) (o + 0 + k) x)
    (R := fun s' ↦ s'.reg .r15 = (k + 1).toUInt64 ∧ s'.reg .r14 = (0 : Nat).toUInt64)
    (c := blk (tabStore o)) (E := fun _ ↦ False) hin ⟨hc, hb, hp, hs⟩
    (WP.mono (tabStore_spec (o := o) (d := 0) (m := k) (by omega) hp h14 h15 hs x h9 h10)
      (fun s' ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2, h3 .rdi (by decide), h3 .rbp (by decide), h4,
        (h3 .r14 (by decide)).trans h14⟩) (fun _ h ↦ h))
  refine WP.mono this (fun s' ⟨⟨hc', hb', hp', hs'⟩, h15', h14'⟩ ↦ ⟨by omega, by simp [hacc], hc',
    hb', ⟨hp', ?_⟩, h15', h14'⟩) (fun _ h ↦ h)
  rw [← wrA_push, hacc]
  simpa using hs'

theorem rdN_refines (hin : Inputs env inp s0.mem) {o n : Nat} (hn : o + n ≤ scrN) (hn' : n < 2 ^ 63)
    (f : Nat → EW) :
    Refines (St env s0 f) (rdN o n) (readScalars n)
      (fun xs t s ↦ xs.size = n ∧ St env s0 (wrA f o xs) t s) (Kept env rs6 s0) :=
  gN_refines env inp s0 hin hn hn' (fun k _f ↦ readScalar_fr (stable_XR hin k)) f

theorem smpN_refines (hin : Inputs env inp s0.mem) {o n : Nat} (hn : o + n ≤ scrN) (hn' : n < 2 ^ 63)
    (f : Nat → EW) :
    Refines (St env s0 f) (smpN o n) (sampleChallenges n)
      (fun xs t s ↦ xs.size = n ∧ St env s0 (wrA f o xs) t s) (Kept env rs6 s0) :=
  gN_refines env inp s0 hin hn hn' (fun k _f ↦ sampleChallenge_fr (stable_XR hin k)) f

end NativeVm.Code.P6
