module

public import LeanVM.Guest.Fast.Xmss
public import LeanVM.Guest.Fast.Sphincs
public import LeanVM.Guest.Fast.Whir
public import LeanVM.Guest.Fast.Da
public import LeanVM.Guest.B1.Main.Interface
public import LeanVM.Guest.B1.Main.Aggregate

/-!
# `main`'s witness, its frames numbered

`decWitV σ rd V piOf` (`B1/Main/SoundV.lean`) assembles `main`'s witness (`decWit`) from its
callees' witnesses, each read off the frame the frame map `V` gives the call by the callee's name.
`decWitN σ rd Vn cl` (here, importing no soundness proof, so the compiled chain does not rebuild
with them) assembles it from the restated readers (`xmssSigOfN`, `sphincsSigOfN` (its
three `sp_wots` frames by the frame map too), `dvWitN`, `vsPiOfN`, `aggHints`), every frame by its
function's index, `cl` the
cursor's length; `decWitN_eq` (`Fast/Decode.lean`): at `Vn k = V (decoderFunctionName k)` and `cl = cursorLen` it is
`decWitV σ rd V vsPiOf`, the deployed decoder's witness. `ReaderTabs`, `readerTabs`: the tables
of the readers off arrays, built once.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.Node

@[expose] public section

/-- **`main`'s witness** (`decWitV`), its frames numbered. -/
noncomputable def decWitN (σ : Val) (rd : Reader) (Vn : NFrames) (cl : E → E → ℕ) : NodeWitness :=
  decWit σ rd (fun args ↦ xmssSigOfN (Vn 37 args []))
    (fun p ↦ sphincsSigOfN (Vn 21 [p, σ (.n 68)] []) Vn)
    (fun args rets ↦ dvWitN (Vn 28 args rets) Vn)
    (fun args ↦ vsPiOfN rd (Vn 19 args []) Vn cl)
    (fun args ↦ aggHints rd (Vn 34 args []))

/-- **The readers' tables, as arrays**, built once per decoding and passed to the readers off
arrays (`xmssSigOfA`, `sphincsSigOfA`, `vsPiOfA`). -/
structure ReaderTabs where
  xmss : XmssTabs
  sphincs : SpTabs
  whir : WhirTabs

/-- **The readers' tables**, built from the literals. -/
def readerTabs : ReaderTabs := ⟨xmssTabs, spTabs, whirTabs⟩

end
end LeanVM.Guest.Fast
