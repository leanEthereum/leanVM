/-
  LeanVMTests.Firewall.Legacy

  The firewall canary's file outside the module system, which sees everything below it.
-/

import LeanVMTests.Firewall.Link

namespace LeanVMTests.Firewall

theorem seen : (1 : Nat) = 1 := linked

end LeanVMTests.Firewall
