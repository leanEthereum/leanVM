/-
  LeanVM.Guest.B1.Whir.OsInstBase

  The certificate facts `open_stacked`'s queries loops take, and a level's callees from their parts.
-/

module

public import LeanVM.Guest.B1.Whir.OsFinal3
public import LeanVM.Guest.B1.Whir.QueriesAtSpec0
public import LeanVM.Guest.B1.Whir.QueriesAtSpec1
public import LeanVM.Guest.B1.Whir.CapAt
public import LeanVM.Guest.B1.Whir.StackedData0
public import LeanVM.Guest.B1.Whir.StackedData1
public import LeanVM.Guest.B1.Whir.StackedData2
public import LeanVM.Guest.B1.Whir.StackedData3

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-!
# The queries loops' frame runs, and a level's callees

`OsOqFits fs cert`: each of `opening_queries`' loop helpers' frame runs fits its frame (the
certificate facts `oq_completeAt_*` take). `osLvKidsAt_mk`: a level's callees from their parts.
-/

/-- **The queries loops' frame runs fit their frames.** -/
structure OsOqFits (fs : String → ℕ) (cert : String → V → ℕ) : Prop where
  f430 : cert "__loop430" (.n (oqP 1 64 8)) + 4 * 9 ≤ fs "__loop430"
  f432 : cert "__loop432" (.n (oqP 0 16 6)) + 4 * 10 ≤ fs "__loop432"
  f434 : cert "__loop434" (.n (oqP 0 16 6)) + 4 * 10 ≤ fs "__loop434"
  f435 : cert "__loop435" (.n (oqP 0 16 6)) + 4 * 9 ≤ fs "__loop435"
  f436 : cert "__loop436" (.n (oqP 1 64 8)) + 4 * 10 ≤ fs "__loop436"
  f437 : cert "__loop437" (.n (oqP 0 16 6)) + 4 * 11 ≤ fs "__loop437"
  f438 : cert "__loop438" (.n (oqP 0 16 6)) + 4 * 11 ≤ fs "__loop438"
  f439 : cert "__loop439" (.n (oqP 1 64 8)) + 4 * 11 ≤ fs "__loop439"
  f440 : cert "__loop440" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop440"
  f441 : cert "__loop441" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop441"
  f442 : cert "__loop442" (.n (oqP 1 64 8)) + 4 * 12 ≤ fs "__loop442"
  f443 : cert "__loop443" (.n (oqP 0 16 6)) + 4 * 13 ≤ fs "__loop443"
  f444 : cert "__loop444" (.n (oqP 0 16 6)) + 4 * 13 ≤ fs "__loop444"
  f445 : cert "__loop445" (.n (oqP 1 64 8)) + 4 * 13 ≤ fs "__loop445"
  f446 : cert "__loop446" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop446"
  f447 : cert "__loop447" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop447"
  f448 : cert "__loop448" (.n (oqP 1 64 8)) + 4 * 14 ≤ fs "__loop448"
  f449 : cert "__loop449" (.n (oqP 0 16 6)) + 4 * 15 ≤ fs "__loop449"
  f450 : cert "__loop450" (.n (oqP 0 16 6)) + 4 * 15 ≤ fs "__loop450"
  f451 : cert "__loop451" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop451"
  f452 : cert "__loop452" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop452"
  f453 : cert "__loop453" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop453"
  f455 : cert "__loop455" (.n (oqP 0 16 6)) + 4 * 14 ≤ fs "__loop455"
  f457 : cert "__loop457" (.n (oqP 1 64 8)) + 4 * 11 ≤ fs "__loop457"
  f458 : cert "__loop458" (.n (oqP 1 64 8)) + 4 * 12 ≤ fs "__loop458"
  f459 : cert "__loop459" (.n (oqP 1 64 8)) + 4 * 13 ≤ fs "__loop459"
  f460 : cert "__loop460" (.n (oqP 0 16 6)) + 4 * 12 ≤ fs "__loop460"
  f461 : cert "__loop461" (.n (oqP 1 64 8)) + 4 * 14 ≤ fs "__loop461"
  f462 : cert "__loop462" (.n (oqP 0 16 6)) + 4 * 13 ≤ fs "__loop462"
  f463 : cert "__loop463" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop463"
  f464 : cert "__loop464" (.n (oqP 1 64 8)) + 4 * 16 ≤ fs "__loop464"
  f465 : cert "__loop465" (.n (oqP 0 16 6)) + 4 * 15 ≤ fs "__loop465"
  f466 : cert "__loop466" (.n (oqP 1 64 8)) + 4 * 17 ≤ fs "__loop466"
  f467 : cert "__loop467" (.n (oqP 0 16 6)) + 4 * 17 ≤ fs "__loop467"
  f468 : cert "__loop468" (.n (oqP 0 16 6)) + 4 * 17 ≤ fs "__loop468"
  f469 : cert "__loop469" (.n (oqP 0 16 6)) + 4 * 16 ≤ fs "__loop469"
  f470 : cert "__loop470" (.n (oqP 1 64 8)) + 4 * 18 ≤ fs "__loop470"
  f471 : cert "__loop471" (.n (oqP 0 16 6)) + 4 * 18 ≤ fs "__loop471"
  f472 : cert "__loop472" (.n (oqP 0 16 6)) + 4 * 18 ≤ fs "__loop472"
  f473 : cert "__loop473" (.n (oqP 0 16 6)) + 4 * 17 ≤ fs "__loop473"
  f474 : cert "__loop474" (.n (oqP 1 64 8)) + 4 * 14 ≤ fs "__loop474"
  f475 : cert "__loop475" (.n (oqP 1 64 8)) + 4 * 15 ≤ fs "__loop475"
  f476 : cert "__loop476" (.n (oqP 1 64 8)) + 4 * 16 ≤ fs "__loop476"
  f477 : cert "__loop477" (.n (oqP 1 64 8)) + 4 * 17 ≤ fs "__loop477"
  f478 : cert "__loop478" (.n (oqP 1 64 8)) + 4 * 18 ≤ fs "__loop478"
  f479 : cert "__loop479" (.n (oqP 1 64 8)) + 4 * 19 ≤ fs "__loop479"
  f480 : cert "__loop480" (.n (oqP 0 16 6)) + 4 * 19 ≤ fs "__loop480"
  f481 : cert "__loop481" (.n (oqP 1 64 8)) + 4 * 20 ≤ fs "__loop481"
  f482 : cert "__loop482" (.n (oqP 0 16 6)) + 4 * 20 ≤ fs "__loop482"
  f483 : cert "__loop483" (.n (oqP 0 16 6)) + 4 * 18 ≤ fs "__loop483"

/-- **A level's callees, from their parts.** -/
theorem osLvKidsAt_mk {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {cfg : OsCfg} {l : ℕ}
    (hrw : OsRowWeightsAtD fs cert κ (cfg.lv l).rowWeights (cfg.lv l).folds (if l = 0 then 1 else 0))
    (hcap : VmcCompleteAt fs cert κ (cfg.lv l).capDepth (cfg.lv l).verifyCap)
    (hq : OqCompleteAt fs cert κ (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds) (cfg.lv l).depth
      (cfg.lv l).capDepth (cfg.lv l).queriesFn)
    (hdec : OsDecodeAtD fs cert κ (cfg.lv l).depth (cfg.lv l).decode) (hpl : sqPlaceB (cfg.lv l) = true)
    {fn : Fn} (hsf : coreProgram.find? (cfg.lv l).sqLoop = some fn) (hsp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hsb : fn.body = sqLoopOf (cfg.lv l)) (hsl : coreProgram.loop (cfg.lv l).sqLoop = true) {fr : Fn}
    (hrf : coreProgram.find? (cfg.lv l).resLoop = some fr)
    (hrp : fr.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) (hrb : fr.body = resLoopOf cfg l (cfg.lv l))
    (hpure : Stmt.pureList [(cfg.lv l).resLoop] (resLoopOf cfg l (cfg.lv l)) = true) :
    OsLvKidsAt fs cert κ cfg l where
  rw := hrw
  cap := hcap
  queries := hq
  decode := hdec
  sqPlace := sqPlace_of hpl
  sqFn := ⟨fn, hsf, hsp, hsb⟩
  sqLoop := hsl
  resPure := fun g hg f hf => by
    simp only [List.mem_singleton] at hg
    subst hg
    rw [hrf] at hf
    cases hf
    rw [hrb]
    exact hpure
  resFn := ⟨fr, hrf, hrp, hrb⟩

end
end LeanVM.Guest.B1
