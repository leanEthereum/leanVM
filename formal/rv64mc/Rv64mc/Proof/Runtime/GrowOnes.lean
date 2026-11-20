/-
  Rv64mc.Proof.Runtime.GrowOnes

  `RawVec<T>::grow_one` for each `T` the image keeps, `GrowOne.ok` at its template: `T`'s alignment and size are
  its generated layout's (a primitive's, `u16`, `u64`, `usize`, its own).
-/

import Rv64mc.Proof.Runtime.GrowOne
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

namespace Rv64mc.Proof.Runtime.GrowOnes

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.Alloc.RawVec

variable {env : Env} {p : Lprog (Op Reg) Reg} {i nga : Nat}

theorem columnClaim_ok (L : RawVecColumnClaim.GrowOne.Link) (hp : p[i]? = some (RawVecColumnClaim.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.ColumnClaim.byteAlign Layouts.ColumnClaim.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem e_ok (L : RawVecE.GrowOne.Link) (hp : p[i]? = some (RawVecE.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.E.byteAlign Layouts.E.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem foldRound_ok (L : RawVecFoldRound.GrowOne.Link) (hp : p[i]? = some (RawVecFoldRound.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.FoldRound.byteAlign Layouts.FoldRound.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem gluedClaim_ok (L : RawVecGluedClaim.GrowOne.Link) (hp : p[i]? = some (RawVecGluedClaim.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.GluedClaim.byteAlign Layouts.GluedClaim.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem k_ok (L : RawVecK.GrowOne.Link) (hp : p[i]? = some (RawVecK.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.K.byteAlign Layouts.K.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem kVecU16_ok (L : RawVecTKVecU16E.GrowOne.Link) (hp : p[i]? = some (RawVecTKVecU16E.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.KVecU16.byteAlign Layouts.KVecU16.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem stackClaim_ok (L : RawVecTStackWeightEE.GrowOne.Link) (hp : p[i]? = some (RawVecTStackWeightEE.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.StackClaim.byteAlign Layouts.StackClaim.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem vecEVecE_ok (L : RawVecTVecEVecEE.GrowOne.Link) (hp : p[i]? = some (RawVecTVecEVecEE.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.VecEVecE.byteAlign Layouts.VecEVecE.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem vecUsizeE_ok (L : RawVecTVecUsizeEE.GrowOne.Link) (hp : p[i]? = some (RawVecTVecUsizeEE.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.VecUsizeE.byteAlign Layouts.VecUsizeE.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem u16_ok (L : RawVecU16.GrowOne.Link) (hp : p[i]? = some (RawVecU16.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env 2 2 p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem u64_ok (L : RawVecU64.GrowOne.Link) (hp : p[i]? = some (RawVecU64.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env 8 8 p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem usize_ok (L : RawVecUsize.GrowOne.Link) (hp : p[i]? = some (RawVecUsize.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env 8 8 p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

theorem vecForm_ok (L : RawVecVecForm.GrowOne.Link) (hp : p[i]? = some (RawVecVecForm.GrowOne.tmpl L)) (hL : L.WF p)
    (hGa : GrowAmortizedSpec env p L.growAmortized.idx nga) (hHe : NoReturn env p L.handleError.idx nga) :
    GrowOneSpec env Layouts.Vec.byteAlign Layouts.Vec.byteSize p i (16 + nga) :=
  GrowOne.ok hp rfl hL.growAmortized hL.handleError hL.s0 hL.s1 (by decide) (by decide) hGa hHe

end Rv64mc.Proof.Runtime.GrowOnes
