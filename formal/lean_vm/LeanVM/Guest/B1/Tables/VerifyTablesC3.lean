/-
  LeanVM.Guest.B1.Tables.VerifyTablesC3

  `verify_tables`' completeness: the table sumcheck's setup, its rounds and the equality prefix.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesC1
public import LeanVM.Guest.B1.Tables.VerifyTablesCLoops
public import LeanVM.Guest.B1.Tables.VerifyTablesCTrace
public import LeanVM.Guest.B1.Tables.VerifyTablesCIface

/-!
# The table sumcheck, forward (G:1690-1742)

`vtPre`'s statements `4273 ..< 4374` (values `4554 ..< 4660`): `g^n` hinted and pinned against the
tables' log-heights, `n ≤ μ`, `ξ` squeezed, the bus target `ξ²·T₀ + ξ³·T₁ + ξ⁴·T₂`, the rounds
(`__loop79`) over the honest round states, the challenges' products and the equality prefix
(`__loop80`). `vt_c_zc`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- `vtPre`'s statements `4273 ..< 4374` as items. -/
def vtItZc : List FItem :=
  [.hint (.witness "zc_tau_max" (.stack [.n 4554])),
    .atom (.load (.n 4555) (.n 7) 1),
    .atom (.const (.n 4556) (word 4294967296 0 0)),
    .atom (.mul (.n 4554) (.n 4557) (.n 4555)),
    .atom (.rangeCheck (.n 4557) (.n 4558) (.n 4559) (.n 4560) (.n 4556)),
    .atom (.add (.n 4561) (.n 4554) (.n 4555)),
    .atom (.load (.n 4562) (.n 7) 2),
    .atom (.const (.n 4563) (word 4294967296 0 0)),
    .atom (.mul (.n 4554) (.n 4564) (.n 4562)),
    .atom (.rangeCheck (.n 4564) (.n 4565) (.n 4566) (.n 4567) (.n 4563)),
    .atom (.add (.n 4568) (.n 4554) (.n 4562)),
    .atom (.mul (.n 4569) (.n 4561) (.n 4568)),
    .atom (.load (.n 4570) (.n 7) 3),
    .atom (.const (.n 4571) (word 4294967296 0 0)),
    .atom (.mul (.n 4554) (.n 4572) (.n 4570)),
    .atom (.rangeCheck (.n 4572) (.n 4573) (.n 4574) (.n 4575) (.n 4571)),
    .atom (.add (.n 4576) (.n 4554) (.n 4570)),
    .atom (.mul (.n 4577) (.n 4569) (.n 4576)),
    .atom (.load (.n 4578) (.n 7) 4),
    .atom (.const (.n 4579) (word 4294967296 0 0)),
    .atom (.mul (.n 4554) (.n 4580) (.n 4578)),
    .atom (.rangeCheck (.n 4580) (.n 4581) (.n 4582) (.n 4583) (.n 4579)),
    .atom (.add (.n 4584) (.n 4554) (.n 4578)),
    .atom (.mul (.n 4585) (.n 4577) (.n 4584)),
    .atom (.load (.n 4586) (.n 7) 5),
    .atom (.const (.n 4587) (word 4294967296 0 0)),
    .atom (.mul (.n 4554) (.n 4588) (.n 4586)),
    .atom (.rangeCheck (.n 4588) (.n 4589) (.n 4590) (.n 4591) (.n 4587)),
    .atom (.add (.n 4592) (.n 4554) (.n 4586)),
    .atom (.mul (.n 4593) (.n 4585) (.n 4592)),
    .atom (.load (.n 4594) (.n 7) 6),
    .atom (.const (.n 4595) (word 4294967296 0 0)),
    .atom (.mul (.n 4554) (.n 4596) (.n 4594)),
    .atom (.rangeCheck (.n 4596) (.n 4597) (.n 4598) (.n 4599) (.n 4595)),
    .atom (.add (.n 4600) (.n 4554) (.n 4594)),
    .atom (.mul (.n 4601) (.n 4593) (.n 4600)),
    .atom (.const (.n 4602) (word 0 0 0)),
    .atom (.assertEq (.n 4601) (.n 4602)),
    .atom (.const (.n 4603) (word 4294967296 0 0)),
    .atom (.mul (.n 6) (.n 4604) (.n 4554)),
    .atom (.rangeCheck (.n 4604) (.n 4605) (.n 4606) (.n 4607) (.n 4603)),
    .sq (.n 3422) (.n 3423) 4608,
    .atom (.const (.n 4622) (word 1 0 0)),
    .atom (.mul (.n 4623) (.n 4622) (.n 4621)),
    .atom (.mul (.n 4624) (.n 4623) (.n 4621)),
    .atom (.mul (.n 4625) (.n 4624) (.n 4621)),
    .atom (.mul (.n 4626) (.n 4625) (.n 4621)),
    .atom (.mul (.n 4627) (.n 4624) (.n 3326)),
    .atom (.mul (.n 4628) (.n 4625) (.n 3705)),
    .atom (.add (.n 4629) (.n 4627) (.n 4628)),
    .atom (.mul (.n 4630) (.n 4626) (.n 4553)),
    .atom (.add (.n 4631) (.n 4629) (.n 4630)),
    .atom (.const (.n 4632) (word 2 0 0)),
    .atom (.mul (.n 4633) (.n 4554) (.n 4632)),
    .atom (.mul (.n 4634) (.n 4633) (.n 4633)),
    .atom (.mul (.n 4635) (.n 4634) (.n 4634)),
    .hint (.allocDyn (.n 4636) (.n 4635)),
    .atom (.const (.n 4637) (word 2 0 0)),
    .atom (.mul (.n 4638) (.n 4554) (.n 4637)),
    .hint (.allocDyn (.n 4639) (.n 4638)),
    .atom (.load (.n 4613) (.n 4636) 0),
    .atom (.load (.n 4614) (.n 4636) 1),
    .atom (.const (.n 4640) (word 32 0 0)),
    .atom (.mul (.n 4641) (.n 2) (.n 4640)),
    .atom (.load (.n 4641) (.n 4636) 2),
    .atom (.load (.n 4631) (.n 4636) 3),
    .atom (.const (.n 4642) (word 1 0 0)),
    .atom (.load (.n 4642) (.n 4639) 0),
    .atom (.const (.n 4643) (word 1 0 0)),
    .atom (.add (.n 4644) (.n 4643) (.n 4554)),
    .atom (.const (.n 4645) (word 1 0 0)),
    .callIf (.n 4644) "__loop79" [.n 4645, .n 4554, .n 4636, .n 15, .n 4554, .n 4639],
    .atom (.mul (.n 4646) (.n 4554) (.n 4554)),
    .atom (.mul (.n 4647) (.n 4646) (.n 4646)),
    .atom (.mul (.n 4648) (.n 4636) (.n 4647)),
    .atom (.load (.n 4649) (.n 4648) 0),
    .atom (.load (.n 4650) (.n 4648) 1),
    .atom (.load (.n 4651) (.n 4648) 2),
    .atom (.load (.n 4652) (.n 4648) 3),
    .atom (.const (.n 4653) (word 2 0 0)),
    .atom (.mul (.n 4654) (.n 4554) (.n 4653)),
    .hint (.allocDyn (.n 4655) (.n 4654)),
    .atom (.const (.n 4656) (word 1 0 0)),
    .atom (.load (.n 4656) (.n 4655) 0),
    .atom (.const (.n 4657) (word 1 0 0)),
    .atom (.add (.n 4658) (.n 4657) (.n 4554)),
    .atom (.const (.n 4659) (word 1 0 0)),
    .callIf (.n 4658) "__loop80" [.n 4659, .n 4554, .n 4655, .n 5, .n 15]]

set_option maxRecDepth 100000 in
theorem vtItZc_eq : vtItZc.flatMap FItem.stmts = (vtPre.drop 4273).take 101 :=
  stmtsEqb_sound (by decide +kernel)

/-- Its obligations. -/
def vtItZcOb : List IOb :=
  [.ob (.ld (.n 7) 1),
    .ob (.nz (.n 4555)),
    .ob (.rc (.n 4557) (.n 4558)),
    .ob (.ld (.n 7) 2),
    .ob (.nz (.n 4562)),
    .ob (.rc (.n 4564) (.n 4565)),
    .ob (.ld (.n 7) 3),
    .ob (.nz (.n 4570)),
    .ob (.rc (.n 4572) (.n 4573)),
    .ob (.ld (.n 7) 4),
    .ob (.nz (.n 4578)),
    .ob (.rc (.n 4580) (.n 4581)),
    .ob (.ld (.n 7) 5),
    .ob (.nz (.n 4586)),
    .ob (.rc (.n 4588) (.n 4589)),
    .ob (.ld (.n 7) 6),
    .ob (.nz (.n 4594)),
    .ob (.rc (.n 4596) (.n 4597)),
    .ob (.holds (.assertEq (.n 4601) (.n 4602))),
    .ob (.nz (.n 4554)),
    .ob (.rc (.n 4604) (.n 4605)),
    .sq (.n 3422) (.n 3423),
    .ob (.holds (.load (.n 4613) (.n 4636) 0)),
    .ob (.holds (.load (.n 4614) (.n 4636) 1)),
    .ob (.holds (.load (.n 4641) (.n 4636) 2)),
    .ob (.holds (.load (.n 4631) (.n 4636) 3)),
    .ob (.holds (.load (.n 4642) (.n 4639) 0)),
    .callIf (.n 4644) "__loop79" [.n 4645, .n 4554, .n 4636, .n 15, .n 4554, .n 4639],
    .ob (.ld (.n 4648) 0),
    .ob (.ld (.n 4648) 1),
    .ob (.ld (.n 4648) 2),
    .ob (.ld (.n 4648) 3),
    .ob (.holds (.load (.n 4656) (.n 4655) 0)),
    .callIf (.n 4658) "__loop80" [.n 4659, .n 4554, .n 4655, .n 5, .n 15]]

set_option maxRecDepth 100000 in
theorem vtItZc_obs : iObs 4554 [] vtItZc = vtItZcOb := listEqb_sound iobEqb_sound (by decide +kernel)


set_option maxRecDepth 100000 in
theorem vtItZc_ok : fOkI 4554 4660 [] vtItZc = true := by decide +kernel

/-- Its definitions. -/
def vtItZcEq : List FEq :=
  [.item (.hint (.witness "zc_tau_max" (.stack [.n 4554]))),
    .ld (.n 4555) (.n 7) 1,
    .def (.const (.n 4556) (word 4294967296 0 0)),
    .sv (.n 4557) (.n 4554) (.n 4555),
    .rc (.n 4557) (.n 4558) (.n 4559) (.n 4560) (.n 4556),
    .def (.add (.n 4561) (.n 4554) (.n 4555)),
    .ld (.n 4562) (.n 7) 2,
    .def (.const (.n 4563) (word 4294967296 0 0)),
    .sv (.n 4564) (.n 4554) (.n 4562),
    .rc (.n 4564) (.n 4565) (.n 4566) (.n 4567) (.n 4563),
    .def (.add (.n 4568) (.n 4554) (.n 4562)),
    .def (.mul (.n 4569) (.n 4561) (.n 4568)),
    .ld (.n 4570) (.n 7) 3,
    .def (.const (.n 4571) (word 4294967296 0 0)),
    .sv (.n 4572) (.n 4554) (.n 4570),
    .rc (.n 4572) (.n 4573) (.n 4574) (.n 4575) (.n 4571),
    .def (.add (.n 4576) (.n 4554) (.n 4570)),
    .def (.mul (.n 4577) (.n 4569) (.n 4576)),
    .ld (.n 4578) (.n 7) 4,
    .def (.const (.n 4579) (word 4294967296 0 0)),
    .sv (.n 4580) (.n 4554) (.n 4578),
    .rc (.n 4580) (.n 4581) (.n 4582) (.n 4583) (.n 4579),
    .def (.add (.n 4584) (.n 4554) (.n 4578)),
    .def (.mul (.n 4585) (.n 4577) (.n 4584)),
    .ld (.n 4586) (.n 7) 5,
    .def (.const (.n 4587) (word 4294967296 0 0)),
    .sv (.n 4588) (.n 4554) (.n 4586),
    .rc (.n 4588) (.n 4589) (.n 4590) (.n 4591) (.n 4587),
    .def (.add (.n 4592) (.n 4554) (.n 4586)),
    .def (.mul (.n 4593) (.n 4585) (.n 4592)),
    .ld (.n 4594) (.n 7) 6,
    .def (.const (.n 4595) (word 4294967296 0 0)),
    .sv (.n 4596) (.n 4554) (.n 4594),
    .rc (.n 4596) (.n 4597) (.n 4598) (.n 4599) (.n 4595),
    .def (.add (.n 4600) (.n 4554) (.n 4594)),
    .def (.mul (.n 4601) (.n 4593) (.n 4600)),
    .def (.const (.n 4602) (word 0 0 0)),
    .def (.const (.n 4603) (word 4294967296 0 0)),
    .sv (.n 4604) (.n 6) (.n 4554),
    .rc (.n 4604) (.n 4605) (.n 4606) (.n 4607) (.n 4603),
    .item (.sq (.n 3422) (.n 3423) 4608),
    .def (.const (.n 4622) (word 1 0 0)),
    .def (.mul (.n 4623) (.n 4622) (.n 4621)),
    .def (.mul (.n 4624) (.n 4623) (.n 4621)),
    .def (.mul (.n 4625) (.n 4624) (.n 4621)),
    .def (.mul (.n 4626) (.n 4625) (.n 4621)),
    .def (.mul (.n 4627) (.n 4624) (.n 3326)),
    .def (.mul (.n 4628) (.n 4625) (.n 3705)),
    .def (.add (.n 4629) (.n 4627) (.n 4628)),
    .def (.mul (.n 4630) (.n 4626) (.n 4553)),
    .def (.add (.n 4631) (.n 4629) (.n 4630)),
    .def (.const (.n 4632) (word 2 0 0)),
    .def (.mul (.n 4633) (.n 4554) (.n 4632)),
    .def (.mul (.n 4634) (.n 4633) (.n 4633)),
    .def (.mul (.n 4635) (.n 4634) (.n 4634)),
    .item (.hint (.allocDyn (.n 4636) (.n 4635))),
    .def (.const (.n 4637) (word 2 0 0)),
    .def (.mul (.n 4638) (.n 4554) (.n 4637)),
    .item (.hint (.allocDyn (.n 4639) (.n 4638))),
    .def (.const (.n 4640) (word 32 0 0)),
    .def (.mul (.n 4641) (.n 2) (.n 4640)),
    .def (.const (.n 4642) (word 1 0 0)),
    .def (.const (.n 4643) (word 1 0 0)),
    .def (.add (.n 4644) (.n 4643) (.n 4554)),
    .def (.const (.n 4645) (word 1 0 0)),
    .item (.callIf (.n 4644) "__loop79" [.n 4645, .n 4554, .n 4636, .n 15, .n 4554, .n 4639]),
    .def (.mul (.n 4646) (.n 4554) (.n 4554)),
    .def (.mul (.n 4647) (.n 4646) (.n 4646)),
    .def (.mul (.n 4648) (.n 4636) (.n 4647)),
    .ld (.n 4649) (.n 4648) 0,
    .ld (.n 4650) (.n 4648) 1,
    .ld (.n 4651) (.n 4648) 2,
    .ld (.n 4652) (.n 4648) 3,
    .def (.const (.n 4653) (word 2 0 0)),
    .def (.mul (.n 4654) (.n 4554) (.n 4653)),
    .item (.hint (.allocDyn (.n 4655) (.n 4654))),
    .def (.const (.n 4656) (word 1 0 0)),
    .def (.const (.n 4657) (word 1 0 0)),
    .def (.add (.n 4658) (.n 4657) (.n 4554)),
    .def (.const (.n 4659) (word 1 0 0)),
    .item (.callIf (.n 4658) "__loop80" [.n 4659, .n 4554, .n 4655, .n 5, .n 15])]

set_option maxRecDepth 100000 in
theorem vtItZc_eqsB : vtItZcEq.all (fun e => (fEqs 4554 [] vtItZc).any (feqEqb e)) = true := by
  decide +kernel

/-! ## Obligations by kind -/

theorem ob_ld_of {rd : Reader} {σf : Val} {pv : V} {p w : E} {off : ℕ} (hp : σf pv = p)
    (h : LoadHolds rd p off w) : Ob.Holds rd σf (.ld pv off) :=
  ⟨by rw [hp]; exact h.1, by rw [hp]; exact isSome_of_loadHolds h⟩

theorem ob_rc_gen {κ : ℕ} {rd : Reader} (hlow : LowDef κ rd) {σf : Val} {x y : V} {a b : ℕ}
    (hx : σf x = gen ^ a) (hy : σf y = gen ^ b) (ha : a < 2 ^ κ) (hb : b < 2 ^ κ) :
    Ob.Holds rd σf (.rc x y) := by
  have h1 := low_gen_pow hlow ha
  have h2 := low_gen_pow hlow hb
  show σf x ≠ 0 ∧ IsInK (σf x) ∧ _ ∧ IsInK (σf y) ∧ _
  rw [hx, hy]
  exact ⟨gen_pow_ne_zero _, h1.1, h1.2, h2.1, h2.2⟩

/-- The window's oracle: `g^n` and the three pointers. -/
noncomputable def vtHvZc (n : ℕ) (pR pC pP : E) (k : ℕ) : E :=
  if k = 4554 then gen ^ n else if k = 4636 then pR else if k = 4639 then pC else pP

end
end LeanVM.Guest.B1.VerifySub
