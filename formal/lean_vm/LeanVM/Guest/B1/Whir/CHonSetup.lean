/-
  LeanVM.Guest.B1.Whir.CHonSetup

  The honest data of an accepting run of the stacked opening and what the run gives of it.
-/

module

public import LeanVM.Guest.B1.Whir.CHonRun
public import LeanVM.Guest.B1.Whir.CHonBuf
public import LeanVM.Guest.B1.Whir.CCaps
public import LeanVM.Guest.B1.Whir.FactsAll
public import LeanVM.Guest.B1.Place.OsSpec

/-!
# The honest data of a run

`hdOf μ r Ls`: the honest data at candidate `candidate μ r` of the levels `Ls`, each level's cap
cells and flags its phase's (`capCellH`, `capFlH`) at its root's height. `HonRun h …`: `h` is the
honest data of an accepting run (`whirOpen_honest`, `LvsRun.data`, `lvsAt_run`), its levels'
combiners nonzero at their positions and their openings agreeing, the candidate's checked facts.
`honRun_of`: every accepting run with no zero challenge, no vanishing combiner and agreeing caps has
one.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Level `l`'s root's height. -/
def heightAt (Ls : List LvAt) (l : ℕ) : ℕ := ((Ls.getD l default).R.getD l default).2.1

/-- **The honest data** of the levels `Ls` at the candidate of `μ`, `r`. -/
noncomputable def hdOf (μ r : ℕ) (Ls : List LvAt) : OsHD :=
  ⟨osCfg (candidate μ r), μ, Ls,
    fun l ↦ capCellH (heightAt Ls l) ((Ls.getD l default).qs μ) (Ls.getD l default).phase,
    fun l ↦ capFlH (heightAt Ls l) (osLvAt (osCfg (candidate μ r)) l).capDepth
      ((Ls.getD l default).qs μ) (Ls.getD l default).phase⟩

/-- **The run's facts** about its honest data. -/
structure HonRun (μ r : ℕ) (target : E) (S : KeccakState) (root : Digest) (xs : List E)
    (os : List (List Opening)) (w : WhirEnd) (cfg : List Whir.Level) (Ls : List LvAt) : Prop where
  m28 : candidate μ r < 28
  hcfg : Whir.ladder μ r = some cfg
  cand : CandOk (candidate μ r) μ r cfg
  run : LvsAtRun μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [], []⟩ (capOf S)
    [(root, stackShape μ r)] xs os w Ls
  nz : ∀ i < Ls.length, Limits.CombinersNZ ((Ls.getD i default).qs μ) (Ls.getD i default).rounds
  agree : ∀ i < Ls.length, ∀ root height width, (Ls.getD i default).R[i]? = some (root, height, width) →
    Guest.Limits.OpeningsAgree height (((Ls.getD i default).qs μ).zip (Ls.getD i default).phase)

/-- **Every accepting run has its honest data.** -/
theorem honRun_of {μ r : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4) {S : KeccakState}
    {root : Digest} {target : E} {xs : List E} {os : List (List Opening)} {w : WhirEnd} {s' : Fs}
    {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : NoZeroChallenge μ r target S xs os root) (hnc : NoZeroCombiner μ r target S xs os root)
    (hca : CapsAgree μ r target S xs os root) :
    ∃ cfg Ls, HonRun μ r target S root xs os w cfg Ls := by
  obtain ⟨cfg, hcfg, hL⟩ := whirOpen_honest h1 h2 h3 h4 hrun hnz
  obtain ⟨ds, hD⟩ := LvsRun.data _ _ _ _ _ _ _ _ _ _ hL
  obtain ⟨cfg', hcfg', hC⟩ := candB_sound (candB_all μ r h1 h2 h3 h4)
  rw [hcfg] at hcfg'
  cases hcfg'
  obtain ⟨w', s'', roots'', hnc'⟩ := hnc
  have hN := whirOpenNZ_lvs (ladderOk_of h1 h2 h3 h4) hcfg hD hnc'
  have hA := whirOpen_agree (ladderOk_of h1 h2 h3 h4) hcfg hD hrun hca
  refine ⟨cfg, _, by unfold candidate; omega, hcfg, hC, lvsAt_run _ _ _ _ _ _ _ _ _ _ _ hD,
    fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · exact lvsAt_nz _ _ _ _ _ _ _ _ _ _ _ hD hN i hi
  · have := lvsAt_agree _ _ _ _ _ _ _ _ _ _ _ hD hA i hi
    simpa using this

end
end LeanVM.Guest.B1.Whir
