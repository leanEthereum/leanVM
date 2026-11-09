/-
  LeanVM.Guest.B1.Place.OsSqB

  open_stacked's squeeze loops, placed on the honest trace, within their frame total.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsSp2
public import LeanVM.Guest.B1.Place.OsKidsB

/-!
# The squeeze loops within their total

**`os_sq_completeAtPB`**: `os_sq_completeAtP` within `sqTot fs (lvAt c l) (c.sqLoop l)
(lvAt c l).squeezes 0`, the loop's frames and its decoders' frames (`sqLoop_relAtIn`'s total), so
`OsCompleteAtPB`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`os_sq_completeAtP` within the loop's total.** -/
theorem os_sq_completeAtPB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {c : OsCfg}
    {tr : OsTr} {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {l : ℕ} (hl : l < c.levels.length) {fn : Fn}
    (hfind : coreProgram.find? (c.sqLoop l) = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = sqLoopBody (lvAt c l) (c.sqLoop l)) (hlp : coreProgram.loop (c.sqLoop l) = true)
    (hdec : QwDecodeAtD fs cert κ (lvAt c l).depth (lvAt c l).capDepth (sqDecName (lvAt c l)))
    (b : ℕ) (Lin : Layout) :
    OsCompleteAtPB fs cert κ (c.sqLoop l) (fun p ↦ osLk c tr b Lin ++ osW fs cert c b l p)
      [1, gen ^ (lvAt c l).squeezes, osPtrAt c b (osIxSqz l), osPtrAt c b 7, osPtrAt c b 8,
        osPtrAt c b 9] []
      (osS fs cert c tr l) (sqTot fs (lvAt c l) (c.sqLoop l) (lvAt c l).squeezes 0) := fun fp ↦
  let ⟨Lown, hW, hD, hR⟩ := os_sq_rel fs cert κ hF h hs hl hfind hp hb hlp hdec b Lin fp
  ⟨_, Lown, hW, hD, le_rfl, hR⟩

end
end LeanVM.Guest.B1
