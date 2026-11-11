/-
  LeanVM.Guest.B1.Whir.CHonBodyRun1

  OsHonest's body on an accepting run.
-/

module

public import LeanVM.Guest.B1.Whir.CHonBodyRun0
public import LeanVM.Guest.B1.Whir.CHonAllocAll
public import LeanVM.Guest.B1.Whir.CHonStaticAll
public import LeanVM.Guest.B1.Whir.CHonNamesAll

/-!
# The body on a run

`HonRun.bodyFacts`: an accepting run's honest data (`hdOf`) has the body's facts (`BodyFacts`) at
the call's arguments `capOf S ++ [target, root's cells, cur, tabs]`. `HonRun.body_run`: OsHonest's
`body` field on the run.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **The run's honest data has the body's facts.** -/
theorem bodyFacts (cur tabs : E) :
    BodyFacts (hdOf μ r Ls) (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs]) xs
      ((cfg.head?.map (·.fold)).getD 0) w := by
  have hy := hR.yr
  have hm := hR.m28
  refine ⟨bodyStatic_all _ hm, honStatic_all _ hm, honNames_all _ hm,
    (honNames_all _ hm).2.2.2.2.2.2.2.1, hR.len, fun l hl ↦ hR.step hl,
    fun l hl ↦ hR.mid hl, hR.last, hR.fin, hR.alphas, fun l hl ↦ (hR.recs l hl).1,
    fun l hl ↦ lvsAt_suffix hR.run l (by rw [hR.len]; exact hl), hR.br_cap5, fun l hl ↦ hR.br_rootN hl,
    hR.br_G, hR.br_rl, hR.br_ht, fun l hl ↦ ?_, fun l hl ↦ ?_, hR.br_ag, hR.br_ps, hR.br_q0, hR.br_lane,
    hR.br_tsuf, hR.br_pl, br_f3, hR.finStatic_run, hR.recRun_run, hR.hylen, hR.hfold, hR.hffm, ?_, ?_, ?_, ?_⟩
  · show capCellH (heightAt Ls l) _ _ = _
    rw [heightAt, hR.br_ht l hl]
    rfl
  · show capFlH (heightAt Ls l) _ _ _ = _
    rw [heightAt, hR.br_ht l hl]
    rfl
  · rw [OsHD.capAt_of _ (Nat.zero_le _)]
    show _ = (Ls.getD 0 default).cap
    rw [hR.start.2.1]
    rfl
  · rw [OsHD.claimAt_of _ (Nat.zero_le _)]
    show _ = (Ls.getD 0 default).s.claim + recsDeficit (lvsRecs μ Ls 0) (Ls.getD 0 default).s.alphas
    rw [hR.start.1]
    simp only [lvsRecs, List.take_zero, List.map_nil, recsDeficit, List.sum_nil, add_zero]
    rfl
  · rw [OsHD.xsAt_of _ (Nat.zero_le _)]
    show (Ls.getD 0 default).xs.length = _
    rw [hR.start.2.2.2]
  · show _ = digestHalves ((Ls.getD 0 default).R.getD 0 default).1
    rw [hR.start.2.2.1]
    rfl

/-- **OsHonest's body on the run.** -/
theorem body_run {cur tabs : E} (b : ℕ) :
    ∃ (kEnd : ℕ) (f : ℕ → E), ∀ (C : CallRel) (rd : Reader),
      OsH C rd (osCfg (candidate μ r)) b (hdOf μ r Ls).own cur tabs xs →
      BlkF C rd (Val.ofArgs (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs]))
        10 kEnd f (osBodyA (osCfg (candidate μ r)))
        (OsOutF (osCfg (candidate μ r)) b tabs
          ((hdOf μ r Ls).tr.2.1 + (hdOf μ r Ls).T.prod * recsDeficit (hdOf μ r Ls).recs (hdOf μ r Ls).G)
          (((hdOf μ r Ls).recs.flatMap recGlued).foldl
            (fun w g ↦ w + g.scalar * g.weightAt (((hdOf μ r Ls).G ++ (hdOf μ r Ls).T).drop g.foldStart)) 0)
          (multilinearEval ((hdOf μ r Ls).Lf.fw.fold.take (osCfg (candidate μ r)).yrLen) (hdOf μ r Ls).T)
          (hdOf μ r Ls).word (hdOf μ r Ls).lamInv (hdOf μ r Ls).bat (hdOf μ r Ls).li) :=
  body_gen (hR.bodyFacts cur tabs) rfl rfl b

end HonRun

end
end LeanVM.Guest.B1.Whir
