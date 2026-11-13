/-
  LeanVMTests.Firewall.Use

  The firewall canary's consumer of the glue: an edit of the data rebuilds none of it.
-/

module

public import LeanVMTests.Firewall.Link

namespace LeanVMTests.Firewall

public section

theorem used : (1 : Nat) = 1 := linked

end
end LeanVMTests.Firewall
