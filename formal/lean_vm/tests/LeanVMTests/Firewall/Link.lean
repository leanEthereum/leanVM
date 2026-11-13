/-
  LeanVMTests.Firewall.Link

  The firewall canary's glue: it imports the check privately, so what imports it does not see the
  data.
-/

module

import LeanVMTests.Firewall.Check

namespace LeanVMTests.Firewall

public section

theorem linked : (1 : Nat) = 1 := by
  have := ok
  rfl

end
end LeanVMTests.Firewall
