import Lean

/-!
# The `rv_addr` simp set

The definitions `addr_omega` unfolds before it reads a goal as linear arithmetic on `toNat`:
byte ranges (`Within`, `Apart`), and a proof's own address abbreviations (a frame pointer).
-/

register_simp_attr rv_addr
