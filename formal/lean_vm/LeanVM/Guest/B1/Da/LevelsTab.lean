/-
  LeanVM.Guest.B1.Da.LevelsTab

  `da_levels`' eleven specializations and their level loops, and the soundness of a checked
  specialization.
-/

module

public import LeanVM.Guest.B1.Da.Levels

/-!
# The specializations of `da_levels`

`dlTab` lists, for `k ≤ 10`, the specialization `da_levels__L{2^k}_L{k}`, its core function
and its `k` level loops. `dlEntryOk k` checks the entry (`dlOk`, every loop's `lvlOk`, the names);
the `LevelsChk*` modules evaluate it, and `dl_sound` turns a checked entry into
`MeaningDaLevels k`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- The specializations: `k`, the name, the core function, the level loops. -/
def dlTab : List (ℕ × String × ℕ × List String) :=
  [(0, "da_levels__L1_L0", 378, []),
    (1, "da_levels__L2_L1", 379, ["__loop41"]),
    (2, "da_levels__L4_L2", 380, ["__loop42", "__loop43"]),
    (3, "da_levels__L8_L3", 381, ["__loop44", "__loop45", "__loop46"]),
    (4, "da_levels__L16_L4", 382, ["__loop47", "__loop48", "__loop49", "__loop50"]),
    (5, "da_levels__L32_L5", 383, ["__loop51", "__loop52", "__loop53", "__loop54", "__loop55"]),
    (6, "da_levels__L64_L6", 384, ["__loop56", "__loop57", "__loop58", "__loop59", "__loop60", "__loop61"]),
    (7, "da_levels__L128_L7", 385, ["__loop62", "__loop63", "__loop64", "__loop65", "__loop66", "__loop67", "__loop68"]),
    (8, "da_levels__L256_L8", 386, ["__loop69", "__loop70", "__loop71", "__loop72", "__loop73", "__loop74", "__loop75", "__loop76"]),
    (9, "da_levels__L512_L9", 387, ["__loop77", "__loop78", "__loop79", "__loop80", "__loop81", "__loop82", "__loop83", "__loop84", "__loop85"]),
    (10, "da_levels__L1024_L10", 388, ["__loop86", "__loop87", "__loop88", "__loop89", "__loop90", "__loop91", "__loop92", "__loop93", "__loop94", "__loop95"])]
/-- A level loop, found and checked. -/
noncomputable def loopOk (f : String) (offA offB : ℕ) : Bool :=
  match coreProgram.indexOf? f with
  | some j => decide (j < coreProgram.length) && lvlOk (coreProgram.getD j default) f offA offB
  | none => false

/-- **Entry `k` of `dlTab`, checked.** -/
noncomputable def dlEntryOk (k : ℕ) : Bool :=
  let e := dlTab.getD k (0, "", 0, [])
  decide (e.1 = k) && decide (e.2.1 = daLevelsName k) &&
  decide (coreProgram.indexOf? e.2.1 = some e.2.2.1) && decide (e.2.2.1 < coreProgram.length) &&
  dlOk (coreProgram.getD e.2.2.1 default) k e.2.2.2 &&
  (List.range k).all fun lvl => loopOk (e.2.2.2.getD lvl "") (off k lvl) (off k (lvl + 1))

end
end LeanVM.Guest.B1.Da
