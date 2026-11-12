/-
  LeanVM.Guest.B1.Whir.HsScaleCert

  The high parts' normalizers `hsScale` the template bakes, recomputed with `mulN` (the product
  of `K` on words), for every level of every candidate, decided by the kernel.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Whir.Vanish
public import LeanVM.Guest.Pow

/-!
# The normalizers, certified

`hsScale v bits c init` (`Template.lean`) multiplies `init` by `LIG_VANISH_INVS[v + i]` over the set
bits `i < bits` of `c` with `kmulN`, the compiler's constant folding. `hsScaleM` is the same fold
with `Pow.mulN`, which `Pow.ofBits_mulN` proves the product of `K`. `hsScale_all`: at every level
the mid-level normalizers (`osHsMid`, `c < folds`, `init = LIG_VANISH_INVS[vanish + logCols]`) and
at the final level the lane's (`osHsFinal`, `c < yrLen + folds`, `init = 1`) agree, the high bits
are at most `logCols + 1`, and the final level's tables hold `yrLog + 1` roots (`vanishOk`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters

@[expose] public section

/-- `hsScale` with `Pow.mulN`. -/
def hsScaleM (v bits c init : ℕ) : ℕ :=
  (List.range bits).foldl (fun sc i ↦ if c.testBit i then Pow.mulN sc (vanishInv (v + i)) else sc) init

/-- Level `l`'s mid-level normalizers agree and its high bits fit. -/
def hsMidOk (m l : ℕ) : Bool :=
  decide ((osLv m l).highBits ≤ (osLv m l).logCols + 1) &&
    (List.range (osLv m l).folds).all fun c ↦
      hsScale (osLv m l).vanish (osLv m l).highBits c (vanishInv ((osLv m l).vanish + (osLv m l).logCols)) ==
        hsScaleM (osLv m l).vanish (osLv m l).highBits c (vanishInv ((osLv m l).vanish + (osLv m l).logCols))

/-- The final level's tables hold `yrLog + 1` roots and its lane's normalizers agree. -/
def hsFinOk (m : ℕ) (lv : OsLv) : Bool :=
  vanishOk lv.vanish ((osCfg m).yrLog + 1) &&
    (List.range ((osCfg m).yrLen + lv.folds)).all fun c ↦
      hsScale lv.vanish ((osCfg m).yrLog + 1) c 1 == hsScaleM lv.vanish ((osCfg m).yrLog + 1) c 1

/-- Candidate `m`'s normalizers. -/
def hsScaleOk (m : ℕ) : Bool :=
  ((List.range (osNLevels m)).all fun l ↦ hsMidOk m l) && hsFinOk m (osLv m (osCfg m).yrLevel)

/-- **Every candidate's normalizers.** -/
theorem hsScale_all : ∀ m < ligNSizes, hsScaleOk m = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Whir
