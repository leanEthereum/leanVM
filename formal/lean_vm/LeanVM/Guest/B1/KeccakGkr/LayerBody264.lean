/-
  LeanVM.Guest.B1.KeccakGkr.LayerBody264

  `keccak_layer__L1`'s body is the template `layerT 1`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

open LeanVM.Guest.KernelLit in
kernel_rfl layer_body264 : (fn% «keccak_layer__L1»).body = layerT 1

end
end LeanVM.Guest.B1.VerifySub
