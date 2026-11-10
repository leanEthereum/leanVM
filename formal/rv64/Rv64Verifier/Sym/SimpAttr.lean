import Lean

/-!
# The `rv_simp` simp set

Ported from sig.golf's `SigGolfCandidate.Rv`. It turns symbolic-execution results into readable
concrete terms (`s.getReg .x10 + 16#64`, `s.getMem (...)`, `if ... then ... else ...`).
-/

register_simp_attr rv_simp
