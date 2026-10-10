import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5ed2965256430c3649e86755f9576b54eca72435"
require whirVerification from git
  "https://github.com/kevaundray/leanVM.git" @ "929791a799b7cb2db22591a260c815869469c9dc" / "verification/whir"

package whirAeneas

lean_lib Aeneas where
  srcDir := ".tools/backend-4.34"
lean_lib AeneasMeta where
  srcDir := ".tools/backend-4.34"
@[default_target] lean_lib WhirAeneas
