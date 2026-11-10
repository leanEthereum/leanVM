/-
  LeanVM.Guest.B1.Opening.QueriesBody3

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
theorem oqBody_542 : Data.core1199.body = oqMainT ⟨1, 64, 12, 7⟩ 0 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_860 : Data.core896.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_468 : Data.core1345.body = oqMainT ⟨1, 64, 12, 8⟩ 0 (oqWalkOf ⟨1, 64, 12, 8⟩) "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_843 : Data.core866.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 (oqWalkOf ⟨1, 64, 12, 8⟩) "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_710 : Data.core731.body = oqMainT ⟨1, 64, 16, 6⟩ 0 (oqWalkOf ⟨1, 64, 16, 6⟩) "__loop111" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_886 : Data.core1135.body = oqLoop1T ⟨1, 64, 16, 6⟩ 0 (oqWalkOf ⟨1, 64, 16, 6⟩) "__loop111" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_732 : Data.core1385.body = oqMainT ⟨1, 64, 18, 6⟩ 0 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop113" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_888 : Data.core1137.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop113" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_614 : Data.core1235.body = oqMainT ⟨1, 64, 12, 7⟩ 1 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_873 : Data.core920.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_501 : Data.core522.body = oqMainT ⟨1, 64, 14, 8⟩ 1 (oqWalkOf ⟨1, 64, 14, 8⟩) "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_851 : Data.core879.body = oqLoop1T ⟨1, 64, 14, 8⟩ 1 (oqWalkOf ⟨1, 64, 14, 8⟩) "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_676 : Data.core1459.body = oqMainT ⟨1, 64, 18, 7⟩ 1 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_880 : Data.core933.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_439 : Data.core460.body = oqMainT ⟨0, 16, 11, 5⟩ 0 (oqWalkOf ⟨0, 16, 11, 5⟩) "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_837 : Data.core858.body = oqLoop0T ⟨0, 16, 11, 5⟩ (oqWalkOf ⟨0, 16, 11, 5⟩) "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_436 : Data.core457.body = oqMainT ⟨0, 16, 11, 6⟩ 0 (oqWalkOf ⟨0, 16, 11, 6⟩) "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_836 : Data.core856.body = oqLoop0T ⟨0, 16, 11, 6⟩ (oqWalkOf ⟨0, 16, 11, 6⟩) "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_591 : Data.core612.body = oqMainT ⟨0, 16, 15, 4⟩ 0 (oqWalkOf ⟨0, 16, 15, 4⟩) "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_867 : Data.core910.body = oqLoop0T ⟨0, 16, 15, 4⟩ (oqWalkOf ⟨0, 16, 15, 4⟩) "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_505 : Data.core526.body = oqMainT ⟨0, 16, 15, 5⟩ 0 (oqWalkOf ⟨0, 16, 15, 5⟩) "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_853 : Data.core883.body = oqLoop0T ⟨0, 16, 15, 5⟩ (oqWalkOf ⟨0, 16, 15, 5⟩) "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_503 : Data.core524.body = oqMainT ⟨0, 16, 15, 6⟩ 0 (oqWalkOf ⟨0, 16, 15, 6⟩) "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_852 : Data.core881.body = oqLoop0T ⟨0, 16, 15, 6⟩ (oqWalkOf ⟨0, 16, 15, 6⟩) "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_680 : Data.core1388.body = oqMainT ⟨0, 16, 18, 5⟩ 0 (oqWalkOf ⟨0, 16, 18, 5⟩) "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_882 : Data.core937.body = oqLoop0T ⟨0, 16, 18, 5⟩ (oqWalkOf ⟨0, 16, 18, 5⟩) "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_757 : Data.core778.body = oqMainT ⟨0, 16, 20, 5⟩ 0 (oqWalkOf ⟨0, 16, 20, 5⟩) "__loop117" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_893 : Data.core1141.body = oqLoop0T ⟨0, 16, 20, 5⟩ (oqWalkOf ⟨0, 16, 20, 5⟩) "__loop117" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
