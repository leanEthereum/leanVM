/-
  LeanVM.Guest.B1.Da.LevelsTab

  `da_levels`' specializations and their level loops, and the soundness of a checked
  specialization.
-/

module

public import LeanVM.Guest.B1.Da.Levels
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Data.NameStrings

/-!
# The specializations of `da_levels`

`dlTab` lists, for each depth `k` of `DlDepth`, the specialization `da_levels__L{2^k}_L{k}`, its
core function and its `k` level loops; `dlEntry k` is the entry of depth `k`. `dlEntryOk k` checks it (`dlOk`, every loop's `lvlOk`, the names);
the `LevelsChk*` modules evaluate it, and `dl_sound` turns a checked entry into
`MeaningDaLevels k`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- The specializations, one per depth of `DlDepth`: `k`, the name, the core function, the level
loops. -/
def dlTab : List (ℕ × String × ℕ × List String) :=
  [(0, "da_levels__L1_L0", 407, []),
    (1, "da_levels__L2_L1", 408, [name% «da_levels__L2_L1_loop0»]),
    (2, "da_levels__L4_L2", 409, [name% «da_levels__L4_L2_loop0»,
        name% «da_levels__L4_L2_loop1»]),
    (3, "da_levels__L8_L3", 410, [name% «da_levels__L8_L3_loop0», name% «da_levels__L8_L3_loop1»,
        name% «da_levels__L8_L3_loop2»]),
    (4, "da_levels__L16_L4", 411, [name% «da_levels__L16_L4_loop0»,
        name% «da_levels__L16_L4_loop1», name% «da_levels__L16_L4_loop2»,
        name% «da_levels__L16_L4_loop3»]),
    (5, "da_levels__L32_L5", 412, [name% «da_levels__L32_L5_loop0»,
        name% «da_levels__L32_L5_loop1», name% «da_levels__L32_L5_loop2»,
        name% «da_levels__L32_L5_loop3», name% «da_levels__L32_L5_loop4»]),
    (7, "da_levels__L128_L7", 940, [name% «da_levels__L128_L7_loop0»,
        name% «da_levels__L128_L7_loop1», name% «da_levels__L128_L7_loop2»,
        name% «da_levels__L128_L7_loop3», name% «da_levels__L128_L7_loop4»,
        name% «da_levels__L128_L7_loop5», name% «da_levels__L128_L7_loop6»])]

/-- The entry of depth `k`. -/
def dlEntry (k : ℕ) : ℕ × String × ℕ × List String := (dlTab.find? (·.1 == k)).getD (0, "", 0, [])

/-- Entry `k`'s first level loop's core function, by depth; the others follow it. -/
def dlLoop0 : List (ℕ × ℕ) := [(0, 0), (1, 941), (2, 942), (3, 944), (4, 947), (5, 951), (7, 1463)]

/-- Entry `k`'s level loop `lvl`'s core function. -/
def dlLoopAt (k lvl : ℕ) : ℕ := ((dlLoop0.find? (·.1 == k)).map (·.2)).getD 0 + lvl

/-- A level loop, at core function `j0`, found and checked. -/
noncomputable def loopOk (f : String) (j0 offA offB : ℕ) : Bool :=
  match coreIdx? f j0 with
  | some j => decide (j < coreProgram.length) && lvlOk (coreProgram.getD j default) f offA offB
  | none => false

/-- **Entry `k` of `dlTab`, checked.** -/
noncomputable def dlEntryOk (k : ℕ) : Bool :=
  let e := dlEntry k
  decide (e.1 = k) && decide (e.2.1 = daLevelsName k) &&
  decide (coreIdx? e.2.1 e.2.2.1 = some e.2.2.1) && decide (e.2.2.1 < coreProgram.length) &&
  dlOk (coreProgram.getD e.2.2.1 default) k e.2.2.2 &&
  (List.range k).all fun lvl =>
    loopOk (e.2.2.2.getD lvl "") (dlLoopAt k lvl) (off k lvl) (off k (lvl + 1))

end
end LeanVM.Guest.B1.Da
