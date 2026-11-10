/-
  LeanVM.Guest.B1.Opening.QueriesBody0

  The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are the
  templates (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem oqBody_413 : Data.core434.body = oqMainT ⟨1, 64, 9, 8⟩ 0 (oqWalkOf ⟨1, 64, 9, 8⟩) "__loop103" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_827 : Data.core1119.body = oqLoop1T ⟨1, 64, 9, 8⟩ 0 (oqWalkOf ⟨1, 64, 9, 8⟩) "__loop103" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_449 : Data.core470.body = oqMainT ⟨1, 64, 11, 8⟩ 0 (oqWalkOf ⟨1, 64, 11, 8⟩) "__loop340" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_839 : Data.core860.body = oqLoop1T ⟨1, 64, 11, 8⟩ 0 (oqWalkOf ⟨1, 64, 11, 8⟩) "__loop340" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_701 : Data.core722.body = oqMainT ⟨1, 64, 15, 6⟩ 0 (oqWalkOf ⟨1, 64, 15, 6⟩) "__loop110" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_885 : Data.core1134.body = oqLoop1T ⟨1, 64, 15, 6⟩ 0 (oqWalkOf ⟨1, 64, 15, 6⟩) "__loop110" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_575 : Data.core596.body = oqMainT ⟨1, 64, 15, 7⟩ 0 (oqWalkOf ⟨1, 64, 15, 7⟩) "__loop357" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_865 : Data.core906.body = oqLoop1T ⟨1, 64, 15, 7⟩ 0 (oqWalkOf ⟨1, 64, 15, 7⟩) "__loop357" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_598 : Data.core619.body = oqMainT ⟨1, 64, 17, 7⟩ 0 (oqWalkOf ⟨1, 64, 17, 7⟩) "__loop360" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_869 : Data.core912.body = oqLoop1T ⟨1, 64, 17, 7⟩ 0 (oqWalkOf ⟨1, 64, 17, 7⟩) "__loop360" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_623 : Data.core644.body = oqMainT ⟨1, 64, 13, 7⟩ 1 (oqWalkOf ⟨1, 64, 13, 7⟩) "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_874 : Data.core922.body = oqLoop1T ⟨1, 64, 13, 7⟩ 1 (oqWalkOf ⟨1, 64, 13, 7⟩) "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_654 : Data.core675.body = oqMainT ⟨1, 64, 16, 7⟩ 1 (oqWalkOf ⟨1, 64, 16, 7⟩) "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_877 : Data.core928.body = oqLoop1T ⟨1, 64, 16, 7⟩ 1 (oqWalkOf ⟨1, 64, 16, 7⟩) "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_425 : Data.core446.body = oqMainT ⟨0, 16, 9, 5⟩ 0 (oqWalkOf ⟨0, 16, 9, 5⟩) "__loop106" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_833 : Data.core1128.body = oqLoop0T ⟨0, 16, 9, 5⟩ (oqWalkOf ⟨0, 16, 9, 5⟩) "__loop106" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_418 : Data.core439.body = oqMainT ⟨0, 16, 10, 6⟩ 0 (oqWalkOf ⟨0, 16, 10, 6⟩) "__loop104" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_829 : Data.core1126.body = oqLoop0T ⟨0, 16, 10, 6⟩ (oqWalkOf ⟨0, 16, 10, 6⟩) "__loop104" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_524 : Data.core545.body = oqMainT ⟨0, 16, 14, 4⟩ 0 (oqWalkOf ⟨0, 16, 14, 4⟩) "__loop350" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_858 : Data.core892.body = oqLoop0T ⟨0, 16, 14, 4⟩ (oqWalkOf ⟨0, 16, 14, 4⟩) "__loop350" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_491 : Data.core512.body = oqMainT ⟨0, 16, 14, 5⟩ 0 (oqWalkOf ⟨0, 16, 14, 5⟩) "__loop343" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_849 : Data.core876.body = oqLoop0T ⟨0, 16, 14, 5⟩ (oqWalkOf ⟨0, 16, 14, 5⟩) "__loop343" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_489 : Data.core510.body = oqMainT ⟨0, 16, 14, 6⟩ 0 (oqWalkOf ⟨0, 16, 14, 6⟩) "__loop342" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_848 : Data.core874.body = oqLoop0T ⟨0, 16, 14, 6⟩ (oqWalkOf ⟨0, 16, 14, 6⟩) "__loop342" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_761 : Data.core782.body = oqMainT ⟨0, 16, 18, 4⟩ 0 (oqWalkOf ⟨0, 16, 18, 4⟩) "__loop643" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_894 : Data.core1744.body = oqLoop0T ⟨0, 16, 18, 4⟩ (oqWalkOf ⟨0, 16, 18, 4⟩) "__loop643" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_600 : Data.core621.body = oqMainT ⟨0, 16, 17, 6⟩ 0 (oqWalkOf ⟨0, 16, 17, 6⟩) "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_870 : Data.core914.body = oqLoop0T ⟨0, 16, 17, 6⟩ (oqWalkOf ⟨0, 16, 17, 6⟩) "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
