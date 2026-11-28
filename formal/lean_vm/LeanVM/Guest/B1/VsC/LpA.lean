/-
  LeanVM.Guest.B1.VsC.LpA

  The statement of `level_positions`' placed completeness: its decodes' frames from its cursor.
-/

module

public import LeanVM.Guest.B1.VsC.QwA
public import LeanVM.Guest.B1.Whir.LpSound

/-!
# `level_positions`, placed: the statement

`level_positions__L{d}_L{cd}` at `S` squeezes allocates its squeeze run `sqz` (`5(S + 1)` words at
its cursor `c`), decodes the first word with `decode_query_windows` (`dq`), then runs its loop
(`loop`), one squeeze and one decode an iteration. Each decode stores pointers to its own frame's
`wins` run, so the honest pointers are a function of the layout: `lpDqFrame … j` is decode `j`'s
frame (decode `0` after `sqz`, the loop's frames after it, decode `j ≥ 1` at the loop's cursor,
each decode's block `fs dq` and nothing after, `lpDqStep`).

`LpA`: at frame `fp` and cursor `c`, on the word `w0`, the capacity `fsv`, the positions' and the
pointers' buffers and the window table (cells of `R`), holding the honest positions and pointers,
the call returns the capacity after `S - 1` squeezes, claims the decodes' windows as its data and
holds them, quiet and exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- A decode's end from the cursor `x`: its aligned frame, its block. -/
def lpDqStep (fs : String → ℕ) (al : String → Bool) (dq : String) (x : ℕ) : ℕ := allocBase (al dq) x + fs dq

/-- Decode `j`'s frame in `level_positions` at `S` squeezes placed from the cursor `c`. -/
def lpDqFrame (fs : String → ℕ) (al : String → Bool) (dq loop : String) (S c j : ℕ) : ℕ :=
  if j = 0 then allocBase (al dq) (c + 5 * (S + 1))
  else allocBase (al dq) ((lpDqStep fs al dq)^[j - 1]
    (allocBase (al loop) (lpDqStep fs al dq (c + 5 * (S + 1))) + lpB fs loop S 1))

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) in
/-- **What `level_positions__L{d}_L{cd}`'s placed completeness gives**, `loop` its loop and `dq`
its decode. -/
def LpA (kd : ℕ) (name loop dq : String) (d cd : ℕ) : Prop :=
  ∀ (S : ℕ) (w0 : E) (fsv : List E) (ipos iptr it : ℕ) (R : ℕ → Prop), 1 ≤ S → S < 2 ^ 20 →
    fsv.length = 5 → 7 ≤ kd → (∀ k < S * (128 / d), R (ipos + k)) → (∀ k < S * (128 / d), R (iptr + k)) →
    (∀ n < 2 ^ winTabBits, R (it + n)) → ∀ fp c, fp + fs name ≤ c → ∃ e, CallAtA fs al cert kd name
      (w0 :: fsv ++ [ptrAt ipos, ptrAt iptr, ptrAt it, gen ^ S]) ((⟨fsv, []⟩ : Fs).squeezeN (S - 1)).2.cap R
      (fun i => ∃ j < S, lpDqFrame fs al dq loop S c j + cert dq (.n 5) ≤ i ∧
        i < lpDqFrame fs al dq loop S c j + cert dq (.n 5) + 128 / d * qwN d cd)
      (fun rd => ∀ j < S, ReadsAt rd (ptrAt (lpDqFrame fs al dq loop S c j + cert dq (.n 5)))
        (qwRunList d cd (sqSample w0 fsv j)))
      (fun rd => WinTabs rd (ptrAt it) ∧
        ReadsAt rd (ptrAt ipos) ((List.range (S * (128 / d))).map fun k =>
          eOfNat (qwPosOf d (sqSample w0 fsv (k / (128 / d))) (k % (128 / d)))) ∧
        ReadsAt rd (ptrAt iptr) ((List.range (S * (128 / d))).map fun k =>
          ptrAt (lpDqFrame fs al dq loop S c (k / (128 / d)) + cert dq (.n 5) + k % (128 / d) * qwN d cd)))
      PostQuiet (fs name) fp c e

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) in
/-- **`LpA` with its end bounded** by its squeezes and the frames it places. -/
def LpAE (kd : ℕ) (name loop dq : String) (d cd : ℕ) : Prop :=
  ∀ (S : ℕ) (w0 : E) (fsv : List E) (ipos iptr it : ℕ) (R : ℕ → Prop), 1 ≤ S → S < 2 ^ 20 →
    fsv.length = 5 → 7 ≤ kd → (∀ k < S * (128 / d), R (ipos + k)) → (∀ k < S * (128 / d), R (iptr + k)) →
    (∀ n < 2 ^ winTabBits, R (it + n)) → ∀ fp c, fp + fs name ≤ c → ∃ e, e ≤ c + (S + 1) * (fs dq + fs loop + fs (tailKey loop) + 64) ∧ CallAtA fs al cert kd name
      (w0 :: fsv ++ [ptrAt ipos, ptrAt iptr, ptrAt it, gen ^ S]) ((⟨fsv, []⟩ : Fs).squeezeN (S - 1)).2.cap R
      (fun i => ∃ j < S, lpDqFrame fs al dq loop S c j + cert dq (.n 5) ≤ i ∧
        i < lpDqFrame fs al dq loop S c j + cert dq (.n 5) + 128 / d * qwN d cd)
      (fun rd => ∀ j < S, ReadsAt rd (ptrAt (lpDqFrame fs al dq loop S c j + cert dq (.n 5)))
        (qwRunList d cd (sqSample w0 fsv j)))
      (fun rd => WinTabs rd (ptrAt it) ∧
        ReadsAt rd (ptrAt ipos) ((List.range (S * (128 / d))).map fun k =>
          eOfNat (qwPosOf d (sqSample w0 fsv (k / (128 / d))) (k % (128 / d)))) ∧
        ReadsAt rd (ptrAt iptr) ((List.range (S * (128 / d))).map fun k =>
          ptrAt (lpDqFrame fs al dq loop S c (k / (128 / d)) + cert dq (.n 5) + k % (128 / d) * qwN d cd)))
      PostQuiet (fs name) fp c e

/-- The bounded form gives `LpA`. -/
theorem LpAE.toA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {kd : ℕ} {name loop dq : String}
    {d cd : ℕ} (h : LpAE fs al cert kd name loop dq d cd) : LpA fs al cert kd name loop dq d cd := by
  intro S w0 fsv ipos iptr it R h1 h2 h3 h4 h5 h6 h7 fp c hfc
  obtain ⟨e, -, he⟩ := h S w0 fsv ipos iptr it R h1 h2 h3 h4 h5 h6 h7 fp c hfc
  exact ⟨e, he⟩


end
end LeanVM.Guest.B1.VsC
