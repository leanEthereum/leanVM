/-
  LeanVM.Guest.B1.Main.MainStaticB

  `main`'s statically bounded callees within their words: the pure ones (`__loop0`…`__loop3`,
  `statement_digest`) within the bounds the static certificates give every valid tree (`TotalLe`,
  `TotalLeOn`).
-/

module

public import LeanVM.Guest.B1.Main.KidCoverAtB
public import LeanVM.Guest.B1.Main.RawAt
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.B1.Main.IterK

/-!
# `main`'s static callees, bounded

The static bounds' convention: `SB g` bounds every valid tree of a statically bounded callee `g`
(`TotalLe coreProgram fs g (fun _ => SB g)`), `SK g` an iteration of a statically bounded loop
helper `g` (`TotalLeOn coreProgram fs g LoopPre (fun a => logG (a.getD 1 0) * SK g)`), the phantom
frame `fs g` its run leaves once (its last iteration's untaken tail call) charged to each iteration;
a call site charges it once, `iterK fs SK g` words per iteration and `fs g` for the run.
`rawX_completeAtB`, `rawS_completeAtB`: the raw signatures' loops within those bounds
(`statement_completeAtB` is in `KidCoverAtB`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (relAtIn_atoms RunIn SlOk slEvs_holds regionL_of_mem limb0_gen_pow_mul)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns DisjL Within disj_append within_append LowDef
  completeAt_of_rel_pureD completeAt_of_rel_pureBat completeAtDTB_of_relIn)

@[expose] public section

/-- A loop helper's call from `g^i` to `g^e`, `i < e < 2^64 - 1`, satisfies `LoopPre`. -/
theorem loopPre_pow {i e : ℕ} (hie : i < e) (he : e < 2 ^ 64 - 1) (rest : List E) :
    LoopPre (gen ^ i :: gen ^ e :: rest) :=
  ⟨i, e, by simp [gen_pow_eq_ofK], by simp [gen_pow_eq_ofK], hie, he⟩

theorem logG_gen {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gen ^ e) = e := by
  rw [gen_pow_eq_ofK]; exact logG_spec he

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`__loop2` within its static bound**, from every counter below the count. -/
theorem rawX_completeAtB (hc : Sig.verify_lean_xmss_complete_Spec) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 16) (hnrx : nrx < 2 ^ 34) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs "__loop2" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop2" + fs "__loop2")) :
    ∀ i < nrx, CompleteAtDTB fs cert 16 "__loop2" Lin
      ([gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] ++ lxTagWords) (Returns []) (fun _ => True)
      (nrx * iterK fs SK "__loop2" + fs "__loop2") := fun i hi =>
  completeAtDTB_of_relIn raw3_pure (by simp)
    (fun rd t rets' hn hv hb => by
      have := hT rd t _ rets' hn (loopPre_pow hi (by omega) _) hv hb
      simpa [logG_gen (show nrx < 2 ^ 64 - 1 by omega)] using this)
    fun rd hl hL => rawX_relIn hc D hX hnrx hl hL i hi

/-- **`__loop3` within its static bound**, from every counter below the count. -/
theorem rawS_completeAtB (hc : Sig.SphincsCompleteSpecs)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin)
    (hY : Y ≤ 2 ^ 16) (hnrs : nrs < 2 ^ 34) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs "__loop3" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop3" + fs "__loop3")) :
    ∀ j < nrs, CompleteAtDTB fs cert 16 "__loop3" Lin
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] (Returns [])
      (fun _ => True) (nrs * iterK fs SK "__loop3" + fs "__loop3") := fun j hj =>
  completeAtDTB_of_relIn raw4_pure (by simp)
    (fun rd t rets' hn hv hb => by
      have := hT rd t _ rets' hn (loopPre_pow hj (by omega) _) hv hb
      simpa [logG_gen (show nrs < 2 ^ 64 - 1 by omega)] using this)
    fun rd hl hL => rawS_relIn hc D hY hnrs hl hL j hj

end
end LeanVM.Guest.B1.Main
