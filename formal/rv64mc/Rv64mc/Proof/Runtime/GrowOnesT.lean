/-
  Rv64mc.Proof.Runtime.GrowOnesT

  `RawVec<T>::grow_one` is total for each `T` the image keeps, `GrowOneT.total` at its template: `T`'s alignment
  and size are its generated layout's (a primitive's, `u16`, `u64`, `usize`, its own), as `GrowOnes.lean` has them.

  ## Main results

  * `columnClaim_total`, `e_total`, `foldRound_total`, `gluedClaim_total`, `k_total`, `kVecU16_total`,
    `stackClaim_total`, `vecEVecE_total`, `vecUsizeE_total`, `u16_total`, `u64_total`, `usize_total`,
    `vecForm_total`
-/

import Rv64mc.Proof.Runtime.GrowOneT
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecColumnClaim.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecE.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecFoldRound.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecGluedClaim.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecK.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecTKVecU16E.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecTStackWeightEE.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecTVecEVecEE.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecTVecUsizeEE.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecU16.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecU64.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecUsize.GrowOne
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecVecForm.GrowOne

namespace Rv64mc.Proof.Runtime.GrowOnesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.Alloc.RawVec
open Rv64mc.Proof.Runtime.GrowOneT (GrowOneSpecT)
open Rv64mc.Proof.Runtime.GrowAmortizedT (GrowAmortizedSpecT)

variable {env : Env} {p : Lprog (Op Reg) Reg} {i nga : Nat}

theorem columnClaim_total (L : RawVecColumnClaim.GrowOne.Link) (hp : p[i]? = some (RawVecColumnClaim.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.ColumnClaim.byteAlign Layouts.ColumnClaim.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem e_total (L : RawVecE.GrowOne.Link) (hp : p[i]? = some (RawVecE.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.E.byteAlign Layouts.E.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem foldRound_total (L : RawVecFoldRound.GrowOne.Link) (hp : p[i]? = some (RawVecFoldRound.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.FoldRound.byteAlign Layouts.FoldRound.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem gluedClaim_total (L : RawVecGluedClaim.GrowOne.Link) (hp : p[i]? = some (RawVecGluedClaim.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.GluedClaim.byteAlign Layouts.GluedClaim.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem k_total (L : RawVecK.GrowOne.Link) (hp : p[i]? = some (RawVecK.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.K.byteAlign Layouts.K.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem kVecU16_total (L : RawVecTKVecU16E.GrowOne.Link) (hp : p[i]? = some (RawVecTKVecU16E.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.KVecU16.byteAlign Layouts.KVecU16.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem stackClaim_total (L : RawVecTStackWeightEE.GrowOne.Link) (hp : p[i]? = some (RawVecTStackWeightEE.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.StackClaim.byteAlign Layouts.StackClaim.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem vecEVecE_total (L : RawVecTVecEVecEE.GrowOne.Link) (hp : p[i]? = some (RawVecTVecEVecEE.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.VecEVecE.byteAlign Layouts.VecEVecE.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem vecUsizeE_total (L : RawVecTVecUsizeEE.GrowOne.Link) (hp : p[i]? = some (RawVecTVecUsizeEE.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.VecUsizeE.byteAlign Layouts.VecUsizeE.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem u16_total (L : RawVecU16.GrowOne.Link) (hp : p[i]? = some (RawVecU16.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env 2 2 p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem u64_total (L : RawVecU64.GrowOne.Link) (hp : p[i]? = some (RawVecU64.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env 8 8 p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem usize_total (L : RawVecUsize.GrowOne.Link) (hp : p[i]? = some (RawVecUsize.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env 8 8 p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem vecForm_total (L : RawVecVecForm.GrowOne.Link) (hp : p[i]? = some (RawVecVecForm.GrowOne.tmpl L))
    (hL : L.WF p) (hGa : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hHe : Aborts env p L.handleError.idx nga) :
    GrowOneSpecT env Layouts.Vec.byteAlign Layouts.Vec.byteSize p i (16 + nga) :=
  GrowOneT.total hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

end Rv64mc.Proof.Runtime.GrowOnesT
