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
  [(0, "da_levels__L1_L0", 420, []),
    (1, "da_levels__L2_L1", 421, ["__loop285"]),
    (2, "da_levels__L4_L2", 422, ["__loop286", "__loop287"]),
    (3, "da_levels__L8_L3", 423, ["__loop288", "__loop289", "__loop290"]),
    (4, "da_levels__L16_L4", 424, ["__loop291", "__loop292", "__loop293", "__loop294"]),
    (5, "da_levels__L32_L5", 425, ["__loop295", "__loop296", "__loop297", "__loop298", "__loop299"]),
    (6, "da_levels__L64_L6", 426, ["__loop300", "__loop301", "__loop302", "__loop303", "__loop304", "__loop305"]),
    (7, "da_levels__L128_L7", 427, ["__loop306", "__loop307", "__loop308", "__loop309", "__loop310", "__loop311", "__loop312"]),
    (8, "da_levels__L256_L8", 428, ["__loop313", "__loop314", "__loop315", "__loop316", "__loop317", "__loop318", "__loop319", "__loop320"]),
    (9, "da_levels__L512_L9", 429, ["__loop321", "__loop322", "__loop323", "__loop324", "__loop325", "__loop326", "__loop327", "__loop328", "__loop329"]),
    (10, "da_levels__L1024_L10", 430, ["__loop330", "__loop331", "__loop332", "__loop333", "__loop334", "__loop335", "__loop336", "__loop337", "__loop338", "__loop339"])]
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
