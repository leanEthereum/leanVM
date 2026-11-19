module

public import NativeVm.Code.Phase6.Tables

/-!
# A Keccak claim in phase 6's scratch, and the scratch's address

`ClaimIn g c`: the scratch `g` holds the claim `c` (`KeccakClaimW`): its value at `eCV`, its
instance weights (at most `16`) at `eMu` with their count at `eMuN`, its point (fewer than `32`
coordinates) at `ePt` with its size at `ePtN`, its `keccakBits` weights at `eW`.

`ldSb` points `rbp` at the scratch again, from the context's working-area pointer, after code that
uses `rbp` (`emle`): `ldSb_st` gives back the phase's state.

`OpenW`: the elements a Keccak opening (`keccakOpen`) and the final check may write.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code
open NativeVm.Transcript (wd wdisp Env cw ctxWork)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- **The scratch `g` holds the claim `c`.** -/
structure ClaimIn (g : Nat → EW) (c : KeccakClaimW) : Prop where
  value : g eCV = c.value
  muSize : c.mu.size ≤ 16
  muN : g eMuN = EW.ofK c.mu.size.toUInt64
  mu : ∀ i < c.mu.size, g (eMu + i) = c.mu.getD i 0
  ptSize : c.point.size < 32
  ptN : g ePtN = EW.ofK c.point.size.toUInt64
  pt : ∀ i < c.point.size, g (ePt + i) = c.point.getD i 0
  wSize : c.weights.size = 1600
  w : ∀ i < 1600, g (eW + i) = c.weights.getD i 0

/-- The elements a Keccak opening and the final check write: the sumcheck's temporaries, two
counters, the slot point, the area from `eG` to `eWF` (`g`, the columns, the rows) and the opening's
weights. -/
def OpenW (i : Nat) : Prop :=
  Tmp i ∨ i = eKn ∨ i = eKd ∨ (eSlot ≤ i ∧ i < eSlot + 6) ∨ (eG ≤ i ∧ i < eWF) ∨
    (eOW ≤ i ∧ i < eOW + 64)

/-! ## The scratch's address -/

/-- `rbp := ` the scratch, from the context's working-area pointer. -/
def ldSb : List Stmt := [I (.load .rbp (cw ctxWork)), I (.addi .rbp (wdisp scratchR.off))]

theorem ldSb_spec {xs : List Stmt} {P E : QState → Prop} (h : CodeRel env t s)
    (hrdi : s.reg .rdi = env.ctx) (k : WP (blk xs) (s.setReg .rbp (sb env)) P E) :
    WP (blk (ldSb ++ xs)) s P E := by
  unfold ldSb
  refine NativeVm.Transcript.wp_load (NativeVm.Transcript.eval_cw hrdi _) h.layout.workPtr ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  simp only [QState.setReg_reg, ↓reduceIte, wdisp, sb] at k ⊢
  have e : env.work + (Int64.ofNat (8 * scratchR.off)).toUInt64 = wd env.work scratchR.off := rfl
  rw [e]
  simpa [QState.setReg] using k

/-- **The phase's state back** after code that wrote `rbp`: the model's state, the frame and the
scratch `g` held, then `ldSb`. -/
theorem ldSb_st {xs : List Stmt} {P E : QState → Prop} (h : CodeRel env t s)
    (hb : Base env rs6 s0 s) (hs : Scr s.mem (sb env) g)
    (k : ∀ s', St env s0 g t s' → s'.mem = s.mem → RegsFrame [.rbp] s s' → WP (blk xs) s' P E) :
    WP (blk (ldSb ++ xs)) s P E :=
  ldSb_spec h hb.1.1 (k _ ⟨h.setReg (by decide) _, hb.setReg (by decide) _,
    by rw [QState.setReg_reg]; simp, hs.congr fun _ _ ↦ rfl⟩ rfl (by rf_tac))

end NativeVm.Code.P6
