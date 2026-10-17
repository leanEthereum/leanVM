import XmssSecurity.Proof.ChainHiddenTable
import XmssSecurity.Proof.ChainTrajectoryComposition
import Init.Data.Vector.OfFn

open OracleComp OracleSpec ENNReal

namespace XmssSecurity


theorem fullChainTrajectory_length_eq : chainLength - 1 + 1 = chainLength := by
  decide

def FullChainTrajectory.toDigitTable
    (values : FullChainTrajectory) : Digit → Digest := fun digit =>
  values[digit.val]'(by
    have hdigit := digit.isLt
    omega)

def FullChainTrajectory.ofDigitTable
  (values : Digit → Digest) : FullChainTrajectory :=
  Vector.ofFn fun index => values ⟨index.val, by
    have hindex := index.isLt
    simpa only [fullChainTrajectory_length_eq] using hindex⟩

noncomputable def chainKeyPosition (key : ChainKey) : Fin allChainKeys.length :=
  ⟨allChainKeys.idxOf key, List.idxOf_lt_length_iff.mpr (mem_allChainKeys key)⟩

@[simp]
theorem allChainKeys_get_chainKeyPosition (key : ChainKey) :
    allChainKeys.get (chainKeyPosition key) = key := by
  exact List.idxOf_get (List.idxOf_lt_length_iff.mpr (mem_allChainKeys key))

noncomputable def listOfChainValueTable
    (table : ChainValueIndex → Digest) : List FullChainTrajectory :=
  allChainKeys.map fun key =>
    FullChainTrajectory.ofDigitTable fun digit => table (key, digit)

@[simp]
noncomputable def chainValueTableOfList
    (values : List FullChainTrajectory) : ChainValueIndex → Digest := fun index =>
  if hlength : allChainKeys.length = values.length then
    (values[(chainKeyPosition index.1).val]'(by
      have hposition := (chainKeyPosition index.1).isLt
      omega)).toDigitTable index.2
  else
    0

@[simp]
theorem listOfChainValueTable_chainValueTableOfList
    (values : List FullChainTrajectory) (hlength : values.length = Fintype.card ChainKey) :
    listOfChainValueTable (chainValueTableOfList values) = values := by
  apply List.ext_getElem
  · simp [listOfChainValueTable, allChainKeys_length, hlength]
  · intro index hleft hright
    simp only [listOfChainValueTable, List.getElem_map]
    apply Vector.ext
    intro digit hdigit
    unfold FullChainTrajectory.ofDigitTable chainValueTableOfList
    rw [Vector.getElem_ofFn]
    split
    · rename_i htableLength
      have hindex : index < allChainKeys.length := by
        rw [allChainKeys_length, ← hlength]
        exact hright
      have hposition : (chainKeyPosition allChainKeys[index]).val = index := by
        exact List.get_idxOf allChainKeys_nodup ⟨index, hindex⟩
      have hvalue :
          values[(chainKeyPosition allChainKeys[index]).val] = values[index] := by
        rw [← Option.some_inj, ← List.getElem?_eq_getElem,
          ← List.getElem?_eq_getElem, hposition]
      dsimp only
      rw [hvalue]
      unfold FullChainTrajectory.toDigitTable
      rfl
    · rename_i htableLength
      exact (htableLength (allChainKeys_length.trans hlength.symm)).elim

end XmssSecurity
