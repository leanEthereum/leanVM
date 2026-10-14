import Lake
open Lake DSL

require whirVerification from git
  "https://github.com/kevaundray/leanVM.git" @ "fa13f619f560c1aa99200edbdd48480b4849b3f1" / "verification/whir"
require LeanVMCircuits from git
  "https://github.com/kevaundray/leanVM.git" @ "404c8fd0928ea6abea1facd220b91ee7464bd810" / "verification/circuits"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5ed2965256430c3649e86755f9576b54eca72435"
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "df591bb8c6745126d1d72f5243faae3022b0432a"

package whirAeneas

lean_lib Aeneas where
  srcDir := ".tools/backend-4.34"
lean_lib AeneasMeta where
  srcDir := ".tools/backend-4.34"
@[default_target] lean_lib WhirAeneas
