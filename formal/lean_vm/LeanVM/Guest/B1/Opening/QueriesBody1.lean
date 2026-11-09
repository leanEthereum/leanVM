/-
  LeanVM.Guest.B1.Opening.QueriesBody1

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
theorem oqBody_533 : Data.core554.body = oqMainT ⟨1, 64, 11, 7⟩ 0 (oqWalkOf ⟨1, 64, 11, 7⟩) "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_859 : Data.core894.body = oqLoop1T ⟨1, 64, 11, 7⟩ 0 (oqWalkOf ⟨1, 64, 11, 7⟩) "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_692 : Data.core713.body = oqMainT ⟨1, 64, 14, 6⟩ 0 (oqWalkOf ⟨1, 64, 14, 6⟩) "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_884 : Data.core940.body = oqLoop1T ⟨1, 64, 14, 6⟩ 0 (oqWalkOf ⟨1, 64, 14, 6⟩) "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_563 : Data.core584.body = oqMainT ⟨1, 64, 14, 7⟩ 0 (oqWalkOf ⟨1, 64, 14, 7⟩) "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_863 : Data.core902.body = oqLoop1T ⟨1, 64, 14, 7⟩ 0 (oqWalkOf ⟨1, 64, 14, 7⟩) "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_721 : Data.core742.body = oqMainT ⟨1, 64, 17, 6⟩ 0 (oqWalkOf ⟨1, 64, 17, 6⟩) "__loop417" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_887 : Data.core943.body = oqLoop1T ⟨1, 64, 17, 6⟩ 0 (oqWalkOf ⟨1, 64, 17, 6⟩) "__loop417" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_743 : Data.core764.body = oqMainT ⟨1, 64, 19, 6⟩ 0 (oqWalkOf ⟨1, 64, 19, 6⟩) "__loop419" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_889 : Data.core946.body = oqLoop1T ⟨1, 64, 19, 6⟩ 0 (oqWalkOf ⟨1, 64, 19, 6⟩) "__loop419" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_632 : Data.core653.body = oqMainT ⟨1, 64, 14, 7⟩ 1 (oqWalkOf ⟨1, 64, 14, 7⟩) "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_875 : Data.core924.body = oqLoop1T ⟨1, 64, 14, 7⟩ 1 (oqWalkOf ⟨1, 64, 14, 7⟩) "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_515 : Data.core536.body = oqMainT ⟨1, 64, 15, 8⟩ 1 (oqWalkOf ⟨1, 64, 15, 8⟩) "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_855 : Data.core886.body = oqLoop1T ⟨1, 64, 15, 8⟩ 1 (oqWalkOf ⟨1, 64, 15, 8⟩) "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_422 : Data.core443.body = oqMainT ⟨0, 16, 10, 5⟩ 0 (oqWalkOf ⟨0, 16, 10, 5⟩) "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_831 : Data.core850.body = oqLoop0T ⟨0, 16, 10, 5⟩ (oqWalkOf ⟨0, 16, 10, 5⟩) "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_568 : Data.core589.body = oqMainT ⟨0, 16, 13, 4⟩ 0 (oqWalkOf ⟨0, 16, 13, 4⟩) "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_864 : Data.core904.body = oqLoop0T ⟨0, 16, 13, 4⟩ (oqWalkOf ⟨0, 16, 13, 4⟩) "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_474 : Data.core495.body = oqMainT ⟨0, 16, 13, 5⟩ 0 (oqWalkOf ⟨0, 16, 13, 5⟩) "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_845 : Data.core870.body = oqLoop0T ⟨0, 16, 13, 5⟩ (oqWalkOf ⟨0, 16, 13, 5⟩) "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_471 : Data.core492.body = oqMainT ⟨0, 16, 13, 6⟩ 0 (oqWalkOf ⟨0, 16, 13, 6⟩) "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_844 : Data.core868.body = oqLoop0T ⟨0, 16, 13, 6⟩ (oqWalkOf ⟨0, 16, 13, 6⟩) "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_683 : Data.core704.body = oqMainT ⟨0, 16, 17, 4⟩ 0 (oqWalkOf ⟨0, 16, 17, 4⟩) "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_883 : Data.core939.body = oqLoop0T ⟨0, 16, 17, 4⟩ (oqWalkOf ⟨0, 16, 17, 4⟩) "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_602 : Data.core623.body = oqMainT ⟨0, 16, 17, 5⟩ 0 (oqWalkOf ⟨0, 16, 17, 5⟩) "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_871 : Data.core916.body = oqLoop0T ⟨0, 16, 17, 5⟩ (oqWalkOf ⟨0, 16, 17, 5⟩) "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_745 : Data.core766.body = oqMainT ⟨0, 16, 19, 5⟩ 0 (oqWalkOf ⟨0, 16, 19, 5⟩) "__loop420" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_890 : Data.core948.body = oqLoop0T ⟨0, 16, 19, 5⟩ (oqWalkOf ⟨0, 16, 19, 5⟩) "__loop420" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
