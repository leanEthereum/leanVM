/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.StreamEnd

  `verify_sub`'s stream reads before its end cursor (`VsStreamQ`), given `open_stacked`'s returned cursor
  (`OsCurSpec`): the cursor's advances from `stream` to `cursor@5`.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamRun
public import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamCur
public import LeanVM.Guest.B1.VerifySub.PhOpen

/-!
# The stream's reads lie before the end

`OsCurSpec` (proved in `OsCur.lean`): at the hypotheses of `open_stacked_sound_w_SpecP`, its sixth return is
its cursor argument times `g^k`, `osRoom[μ - 16] ≤ k < 2^32`. `vs_cEnd`: then `cursor@5 = cursor@4·g·g^k` at
`verify_sub`'s dispatch, `size_sel = g^m`. `vsPos`: the positions of the cursors past `stream` (`StreamCur.lean`) and
the end's, `4009 = g^E` with `E` the end's position. `vsStreamQ_of : OsCurSpec → VsStreamQ al D`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash
open LeanVM.Guest.CoreMode (CCond CRes CRun CCell)
open LeanVM.Guest.CoreMode.Own.verify_sub (osRoom lrsRoom armOf streamCell streamRun)

@[expose] public section

/-- **`open_stacked`'s returned cursor**: under `open_stacked_sound_w_SpecP`'s hypotheses, its returned cursor
is its cursor argument times `g^k`, `k` at least the words its contract reads (`osRoom`), below `2^32`. -/
def OsCurSpec : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → winTabBits ≤ κ → ∀ (L : MemoryImage κ) (C : CallRel) (V : FrameMap),
    UnfoldsV L.read C V → CallRel.Le C (coreProgram.Rel L.read) →
    ∀ (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
      ∀ (root : Digest) (fs : List E) (target root0 root1 cur tabs : E) (rets : List E) (fn : Fn) (σ : Val),
        fs.length = 5 → (root0, root1) = digestHalves root → WinTabs L.read tabs →
        coreProgram.find? (openName μ) = some fn →
        fn.params.map σ = rateSel r :: fs ++ [target, root0, root1, cur, tabs] →
        Stmt.HoldsList C L.read σ fn.body False (fun rs ↦ rs = rets) →
        ∃ k < 2 ^ 32, osRoom.getD (μ - minOpenLog) 0 ≤ k ∧ rets.getD 5 0 = cur * gen ^ k

end

public section

variable {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap} {σ : Val} {rets : List E}

/-- **Past the opening**: `cursor@5 = cursor@4·g·g^k`, `size_sel = g^m`, `osRoom[m] ≤ k`. -/
theorem vs_cEnd (hOs : OsCurSpec) (R : VsRun bytecode L C V σ rets) :
    ∃ m < 15, σ (.n 489) = ofK (addressOfIndex m) ∧
      ∃ k < 2 ^ 32, osRoom.getD m 0 ≤ k ∧ σ (.n 3996) = σ (.n 2920) * gen * gen ^ k := by
  have S := R.sizesOk
  obtain ⟨-, hwin, -⟩ := R.pre
  have aO : ∀ {x : Atom}, Stmt.atom x ∈ vsOpenT → x.Holds L.read σ := fun h ↦ R.atom_in vsOpenT_eq h
  have e3987 : σ (.n 3987) = word 2 0 :=
    aO (x := .const (.n 3987) (word 2 0)) (membB_sound (by decide +kernel))
  have e3988 : σ (.n 3988) = σ (.n 2920) * σ (.n 3987) :=
    aO (x := .mul (.n 3988) (.n 2920) (.n 3987)) (membB_sound (by decide +kernel))
  have e3989 : σ (.n 3989) = word 365917469723852800 0 :=
    aO (x := .const (.n 3989) (word 365917469723852800 0)) (membB_sound (by decide +kernel))
  have e3990 : σ (.n 3990) = σ (.n 4) * σ (.n 3989) :=
    aO (x := .mul (.n 3990) (.n 4) (.n 3989)) (membB_sound (by decide +kernel))
  have hdisp := R.mem_slice vsOpenT_eq (s := vsOsDispatch) (membB_sound (by decide +kernel))
  simp only [vsOsDispatch, Stmt.Holds, List.map_cons, List.map_nil] at hdisp
  obtain ⟨⟨j, hj, hsel, hC⟩, -⟩ := hdisp
  have hjμ : j = (vsLayout bytecode σ).stackLog - minOpenLog :=
    (dispatchIdx_eq hj hsel).symm.trans (dispatchIdx_eq (by
      have := S.st2; have := S.st1
      simp only [openArms, minOpenLog] at *; omega) S.sizeSel)
  have hnm : vsOsNames[j] = openName (vsLayout bytecode σ).stackLog := by
    rw [vsOsNames_get j hj, openName_eq (by
      have := S.st2; have := S.st1; simp only [ligNSizes, minOpenLog] at *; omega), ← hjμ]
  rw [hnm] at hC
  obtain ⟨fn, hfind, hpar, hbody⟩ := R.hU _ _ _ hC
  have hp : fn.params.map (V (openName (vsLayout bytecode σ).stackLog)
      [σ (.n 96), σ (.n 3033), σ (.n 3034), σ (.n 3035), σ (.n 3036), σ (.n 3037), σ (.n 3986),
        σ (.n 134), σ (.n 137), σ (.n 3988), σ (.n 3990)]
      [σ (.n 3991), σ (.n 3992), σ (.n 3993), σ (.n 3994), σ (.n 3995), σ (.n 3996)]) =
      rateSel (vsLir σ) :: [σ (.n 3033), σ (.n 3034), σ (.n 3035), σ (.n 3036), σ (.n 3037)] ++
        [σ (.n 3986), σ (.n 134), σ (.n 137), σ (.n 3988), σ (.n 3990)] := by
    rw [hpar, ← S.rateSel]; rfl
  have hwt : WinTabs L.read (σ (.n 3990)) := by
    rw [e3990, e3989, word_winTab]; exact winTabs_of_expWinTab hwin
  have hwb := winTabBits_le_of_winTabs R.hκ L hwt
  obtain ⟨k, hk, hroom, hret⟩ := hOs R.hκ hwb L C V R.hU R.hle (vsLayout bytecode σ).stackLog (vsLir σ) S.st1 S.st2
    S.lir1 S.lir4 (vsRoot σ) [σ (.n 3033), σ (.n 3034), σ (.n 3035), σ (.n 3036), σ (.n 3037)] (σ (.n 3986))
    (σ (.n 134)) (σ (.n 137)) (σ (.n 3988)) (σ (.n 3990)) _ fn _ rfl
    (digestScalars_digestOfScalars _).symm hwt hfind hp hbody
  have h15 : (vsLayout bytecode σ).stackLog - minOpenLog < 15 := by
    have := S.st2; simp only [minOpenLog] at *; omega
  refine ⟨_, h15, S.sizeSel, k, hk, hroom, ?_⟩
  have e : σ (.n 3996) = σ (.n 3988) * gen ^ k := hret
  rw [e, e3988, e3987, word_gen]

end

end LeanVM.Guest.EndExec
