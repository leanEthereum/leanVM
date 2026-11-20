module

public import LeanVM.Cost.Extractor.Top
public import LeanVM.Protocol.Whir.Sound.NewtonK
import all LeanVM.Protocol.Whir.Sound.NewtonK
import all LeanVM.Protocol.Whir.Sound.Newton

/-!
# One-error Newton decoding, compiled

The agreement-set extractor's decoder (`Whir.Sound.Newton.decode1K`, nodes in `K`) and its parts.
-/

namespace LeanVM.Cost.AS

open LeanVM.Cost LeanVM.Parameters LeanVM.Protocol.Whir.Sound.Newton

public section

cost_compile nodalKC := nodalK

cost_compile nStepKC := nStepK

cost_compile nFormKC := nFormK

cost_compile dropLocC := dropLoc

cost_compile decode1KC := decode1K

end

end LeanVM.Cost.AS
