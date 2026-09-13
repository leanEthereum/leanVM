import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.UniformTableSplit
namespace SphincsSecurity.Concrete.UniformTableSplit

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Index Cell Answer : Type}

noncomputable def overwrite (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (table : Cell → Answer) : Cell → Answer :=
  join embed hinj rows (fun cell => table cell.val)

theorem overwrite_embed (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (table : Cell → Answer) (index : Index) :
    overwrite embed hinj rows table (embed index) = rows index :=
  join_embed embed hinj rows _ index

theorem overwrite_outside (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (table : Cell → Answer) (cell : Cell) (hcell : cell ∉ Set.range embed) :
    overwrite embed hinj rows table cell = table cell :=
  join_outside embed hinj rows _ ⟨cell, hcell⟩

theorem overwrite_join (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows previous : Index → Answer) (outside : Outside embed → Answer) :
    overwrite embed hinj rows (join embed hinj previous outside) = join embed hinj rows outside := by
  unfold overwrite
  congr 1
  funext cell
  exact join_outside embed hinj previous outside cell

variable [Fintype Index] [Fintype Cell] [Fintype Answer] [Nonempty Answer]
  [DecidableEq Index] [DecidableEq Cell]

theorem uniform_overwrite (embed : Index → Cell) (hinj : Function.Injective embed) (rows : Index → Answer) :
    (PMF.uniformOfFintype (Cell → Answer)).map (overwrite embed hinj rows) =
      (PMF.uniformOfFintype (Outside embed → Answer)).map (join embed hinj rows) := by
  rw [uniform_join embed hinj]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, overwrite_join, PMF.bind_const]

end SphincsSecurity.Concrete.UniformTableSplit
