/-
  LeanVM.Guest.B1.Opening.QueriesBody2

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
theorem oqBody_433 : Data.core454.body = oqMainT ⟨1, 64, 10, 8⟩ 0 (oqWalkOf ⟨1, 64, 10, 8⟩) "__loop107" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_835 : Data.core929.body = oqLoop1T ⟨1, 64, 10, 8⟩ 0 (oqWalkOf ⟨1, 64, 10, 8⟩) "__loop107" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_551 : Data.core572.body = oqMainT ⟨1, 64, 13, 7⟩ 0 (oqWalkOf ⟨1, 64, 13, 7⟩) "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_861 : Data.core898.body = oqLoop1T ⟨1, 64, 13, 7⟩ 0 (oqWalkOf ⟨1, 64, 13, 7⟩) "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_487 : Data.core508.body = oqMainT ⟨1, 64, 13, 8⟩ 0 (oqWalkOf ⟨1, 64, 13, 8⟩) "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_847 : Data.core872.body = oqLoop1T ⟨1, 64, 13, 8⟩ 0 (oqWalkOf ⟨1, 64, 13, 8⟩) "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_586 : Data.core607.body = oqMainT ⟨1, 64, 16, 7⟩ 0 (oqWalkOf ⟨1, 64, 16, 7⟩) "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_866 : Data.core908.body = oqLoop1T ⟨1, 64, 16, 7⟩ 0 (oqWalkOf ⟨1, 64, 16, 7⟩) "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_755 : Data.core776.body = oqMainT ⟨1, 64, 20, 6⟩ 0 (oqWalkOf ⟨1, 64, 20, 6⟩) "__loop116" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_892 : Data.core940.body = oqLoop1T ⟨1, 64, 20, 6⟩ 0 (oqWalkOf ⟨1, 64, 20, 6⟩) "__loop116" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_643 : Data.core664.body = oqMainT ⟨1, 64, 15, 7⟩ 1 (oqWalkOf ⟨1, 64, 15, 7⟩) "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_876 : Data.core926.body = oqLoop1T ⟨1, 64, 15, 7⟩ 1 (oqWalkOf ⟨1, 64, 15, 7⟩) "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_665 : Data.core686.body = oqMainT ⟨1, 64, 17, 7⟩ 1 (oqWalkOf ⟨1, 64, 17, 7⟩) "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_878 : Data.core930.body = oqLoop1T ⟨1, 64, 17, 7⟩ 1 (oqWalkOf ⟨1, 64, 17, 7⟩) "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_556 : Data.core577.body = oqMainT ⟨0, 16, 12, 4⟩ 0 (oqWalkOf ⟨0, 16, 12, 4⟩) "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_862 : Data.core900.body = oqLoop0T ⟨0, 16, 12, 4⟩ (oqWalkOf ⟨0, 16, 12, 4⟩) "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_455 : Data.core476.body = oqMainT ⟨0, 16, 12, 5⟩ 0 (oqWalkOf ⟨0, 16, 12, 5⟩) "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_841 : Data.core864.body = oqLoop0T ⟨0, 16, 12, 5⟩ (oqWalkOf ⟨0, 16, 12, 5⟩) "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_452 : Data.core473.body = oqMainT ⟨0, 16, 12, 6⟩ 0 (oqWalkOf ⟨0, 16, 12, 6⟩) "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_840 : Data.core862.body = oqLoop0T ⟨0, 16, 12, 6⟩ (oqWalkOf ⟨0, 16, 12, 6⟩) "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_605 : Data.core626.body = oqMainT ⟨0, 16, 16, 4⟩ 0 (oqWalkOf ⟨0, 16, 16, 4⟩) "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_872 : Data.core918.body = oqLoop0T ⟨0, 16, 16, 4⟩ (oqWalkOf ⟨0, 16, 16, 4⟩) "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_519 : Data.core540.body = oqMainT ⟨0, 16, 16, 5⟩ 0 (oqWalkOf ⟨0, 16, 16, 5⟩) "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_857 : Data.core890.body = oqLoop0T ⟨0, 16, 16, 5⟩ (oqWalkOf ⟨0, 16, 16, 5⟩) "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_517 : Data.core538.body = oqMainT ⟨0, 16, 16, 6⟩ 0 (oqWalkOf ⟨0, 16, 16, 6⟩) "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_856 : Data.core888.body = oqLoop0T ⟨0, 16, 16, 6⟩ (oqWalkOf ⟨0, 16, 16, 6⟩) "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_678 : Data.core699.body = oqMainT ⟨0, 16, 18, 6⟩ 0 (oqWalkOf ⟨0, 16, 18, 6⟩) "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_881 : Data.core935.body = oqLoop0T ⟨0, 16, 18, 6⟩ (oqWalkOf ⟨0, 16, 18, 6⟩) "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
