module

/-!
# Concrete parameters

This layer binds versioned constants and encodings to their authoritative upstream sources: the
fields and the generator (`Field`, `Generator`), the BLAKE2s constants (`Blake2s`), the opcode
codes and instance caps (`Isa`), and Clean's field interface (`CleanField`). Generic VM
semantics and proof-system theory should not depend on these concrete bindings unless the
statement is intentionally deployment-specific.
-/

namespace LeanVM.Parameters

public section

end
end LeanVM.Parameters
