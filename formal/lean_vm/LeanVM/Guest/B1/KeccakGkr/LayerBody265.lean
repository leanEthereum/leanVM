/-
  LeanVM.Guest.B1.KeccakGkr.LayerBody265

  `keccak_layer__L0`'s body is the template `layerT 0`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

open LeanVM.Guest.KernelLit in
kernel_rfl layer_body265 : (fn% «keccak_layer__L0»).body = layerT 0

end
end LeanVM.Guest.B1.VerifySub
