/-
  LeanVMTests.Firewall.Data

  The firewall canary's data (`tools/firewall-canary.py`, which edits this file and restores it).
-/

module

namespace LeanVMTests.Firewall

@[expose] public section

def value : Nat := 1

theorem value_pos : 0 < value := by decide

end
end LeanVMTests.Firewall
