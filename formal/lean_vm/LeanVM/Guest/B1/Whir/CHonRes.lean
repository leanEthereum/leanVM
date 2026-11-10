/-
  LeanVM.Guest.B1.Whir.CHonRes

  The residual loops on memory holding the honest buffers.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFinRun
public import LeanVM.Guest.B1.Whir.CHonFields1
public import LeanVM.Guest.B1.Whir.CResLoop
public import LeanVM.Guest.B1.Whir.DataAll

/-!
# The residual loops, honestly

`resRel_gen`: on memory holding the honest buffers, a non-final level's residual loop runs at the
values the finish calls it with (`resLoop_complete`), from the finish's static facts and the
level's record facts. `HonRun.fld_resRel`: OsHonest's `resRel` on a run.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **A non-final level's residual loop** on memory holding the honest buffers. -/
theorem resRel_gen {h : OsHD} {b : ℕ} {rd : Reader} (hHS : HonStatic h.c)
    (hF : FinStatic h.c h.G h.T h.recs) (hL : h.Ls.length = h.c.levels.length)
    (hrun : ∀ i < h.c.yrLevel, RecRun h i) (hm : OsMemF rd h.c b h.own) {l : ℕ} (hl : l < h.c.yrLevel)
    (hfn : FnIs (h.c.resLoop l) (osParams 7) (resLoopBody l (osLvAt h.c l) (h.c.resLoop l)))
    (hn0 : 0 < (osLvAt h.c l).queries / resBatch) :
    coreProgram.Rel rd (h.c.resLoop l) [1, gen ^ ((osLvAt h.c l).queries / resBatch), osPtrF h.c b 11,
      osPtrF h.c b (osIxBD h.c), osPtrF h.c b 8, osPtrF h.c b (osIxRC h.c l), h.li l] [] := by
  have hy := hHS.yr
  have lf := hF.lv l hl
  have hst := hF.rs l hl
  have hR := hrun l hl
  have hr : h.recs.getD l default = (h.L l).osRec h.logN := h.recs_getD hL hy hl
  refine resLoop_complete (D := finD h.c h.G h.T h.recs l)
    (Pos := fun k ↦ eOfNat ((h.recs.getD l default).qs.getD k 0)) hfn hst lf.posOff hn0
    (fun k hk ↦ ?_) (fun t ht ↦ ?_) (fun c hc ↦ ?_) ?_ ?_
  · show LoadHolds rd (osPtrF h.c b 11) ((osLvAt h.c l).posOff + k) (eOfNat ((h.recs.getD l default).qs.getD k 0))
    rw [hr, hR.qs k hk]
    exact h.pos_load hHS hm (by omega) (by have := hR.Q; omega)
  · have ht' : t < (finLv h.c l).prefixLen + h.c.yrLog := by rw [lf.pre]; exact ht
    obtain ⟨hbl, eb⟩ := finBdC_get (G := h.G) (T := h.T) (recs := h.recs) hl (by omega) ht'
      (by rw [lf.pre]; exact hF.cols l hl)
    have hrd := h.bd_reads hHS hm
    rw [show 13 + 2 * h.c.levels.length + 3 = osIxBD h.c by unfold osIxBD; omega] at hrd
    have := readsAt_getD' hrd (j := l * ligColsCap + t) (by
      rw [hbl]
      have : (l + 1) * ligColsCap ≤ h.c.levels.length * ligColsCap := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      have : (osLvAt h.c l).logCols ≤ ligColsCap := hF.cols l hl
      omega)
    rwa [eb] at this
  · rw [show (hsvOf (finLv h.c l) (h.recs.getD l default)).getD c 0 = (h.recs.getD l default).high.getD c 0 *
        word (hsScale (finLv h.c l).vanish (finLv h.c l).highBits c
          (vanishInv ((finLv h.c l).vanish + (finLv h.c l).logCols))) 0 by
      simp only [hsvOf]
      rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]]
    rw [hr, (h.L l).osRec_high h.logN]
    exact (h.mid_hs hHS hm hl hc).2
  · have := h.rc_reads hHS hm hl (by simp only [finRcC, rcC_length]; exact le_rfl)
    exact this
  · intro h0
    have e := (e_add_eq_zero_iff.mp h0).symm
    have hn0' : 0 < (finLv h.c l).queries / resBatch := hn0
    rw [gen_pow_eq_one_iff lf.nbo] at e
    omega

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **OsHonest's `resRel`** on a run. -/
theorem fld_resRel : ∀ b rd, OsMemF rd (osCfg (candidate μ r)) b (hdOf μ r Ls).own →
    ∀ l < (osCfg (candidate μ r)).yrLevel,
      coreProgram.Rel rd ((osCfg (candidate μ r)).resLoop l)
        [1, gen ^ ((osLvAt (osCfg (candidate μ r)) l).queries / resBatch), osPtrF (osCfg (candidate μ r)) b 11,
          osPtrF (osCfg (candidate μ r)) b (osIxBD (osCfg (candidate μ r))), osPtrF (osCfg (candidate μ r)) b 8,
          osPtrF (osCfg (candidate μ r)) b (osIxRC (osCfg (candidate μ r)) l), (hdOf μ r Ls).li l] [] := by
  intro b rd hm l hl
  have hy := hR.yr
  have hfn := (osData_all _ hR.m28).2.2 l hl
  rw [← osLvAt_osCfg (by rw [← osCfg_len]; omega)] at hfn
  exact resRel_gen (h := hdOf μ r Ls) (honStatic_all _ hR.m28) hR.finStatic_run hR.len hR.recRun_run hm hl
    hfn (fieldStatic_all _ hR.m28 l hl)

end HonRun

end
end LeanVM.Guest.B1.Whir
