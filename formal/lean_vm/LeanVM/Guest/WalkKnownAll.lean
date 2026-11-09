/-
  LeanVM.Guest.WalkKnownAll

  The walks' obligations, proved: every function the certificates hand something on at its cuts,
  but `main` and `verify_sub`.
-/

module

public import LeanVM.Guest.WalkOq0
public import LeanVM.Guest.WalkOq1
public import LeanVM.Guest.WalkOq2
public import LeanVM.Guest.WalkOq3
public import LeanVM.Guest.WalkWp
public import LeanVM.Guest.WalkOs0
public import LeanVM.Guest.WalkOs1
public import LeanVM.Guest.WalkOs2
public import LeanVM.Guest.WalkOs3
public import LeanVM.Guest.WalkGkr

/-!
# `WalkKnown`, proved

`walkKnown_proved : WalkKnown`: the cut obligations (`CutsKnown`) of every function of
`Checked.oblFns` but `main` (`1`) and `verify_sub` (`19`): `opening_queries`' specializations and
loops (`WalkOq0.lean` to `WalkOq3.lean`, whir's `QueriesWalk` through b2's `WalkKnown.lean`),
`open_stacked`'s candidates (`WalkOs0.lean` to `WalkOs3.lean`, from the decodes before each level's
call, `WalkOsPre.lean`), `walk_path`'s specializations (`WalkWp.lean`, from their windows' tag),
and `verify_bus_gkr` (`10`) and its layer loop `__loop6` (`90`), whose
obligations (the layers' parities, `GkrPar`) the gkr track proves (`WalkGkr.lean`;
`walkKnown_of_gkr`).
-/

namespace LeanVM.Guest.End

@[expose] public section

/-- **The walks' obligations**, given `verify_bus_gkr`'s and its layer loop's. -/
theorem walkKnown_of_gkr (h10 : CutsKnown 10) (h91 : CutsKnown 90) : WalkKnown := by
  -- One conjunct per function of `Checked.oblFns`, in order: linear, where `rcases` over the
  -- membership disjunction is quadratic.
  have key : List.Forall (fun j ↦ j ≠ 1 → j ≠ 19 → CutsKnown j) Checked.oblFns :=
    ⟨fun h _ ↦ absurd rfl h, fun _ _ ↦ h10, fun _ h ↦ absurd rfl h, fun _ _ ↦ h91,
      fun _ _ ↦ walk_303, fun _ _ ↦ walk_304, fun _ _ ↦ walk_305, fun _ _ ↦ walk_306,
      fun _ _ ↦ walk_307, fun _ _ ↦ walk_308, fun _ _ ↦ walk_309, fun _ _ ↦ walk_310,
      fun _ _ ↦ walk_311, fun _ _ ↦ walk_312, fun _ _ ↦ walk_313, fun _ _ ↦ walk_314,
      fun _ _ ↦ walk_315, fun _ _ ↦ walk_316, fun _ _ ↦ walk_317, fun _ _ ↦ walk_318,
      fun _ _ ↦ walk_319, fun _ _ ↦ walk_320, fun _ _ ↦ walk_321, fun _ _ ↦ walk_322,
      fun _ _ ↦ walk_323, fun _ _ ↦ walk_324, fun _ _ ↦ walk_325, fun _ _ ↦ walk_326,
      fun _ _ ↦ walk_327, fun _ _ ↦ walk_328, fun _ _ ↦ walk_329, fun _ _ ↦ walk_330,
      fun _ _ ↦ walk_435, fun _ _ ↦ walk_440, fun _ _ ↦ walk_444, fun _ _ ↦ walk_447,
      fun _ _ ↦ walk_455, fun _ _ ↦ walk_458, fun _ _ ↦ walk_461, fun _ _ ↦ walk_471,
      fun _ _ ↦ walk_474, fun _ _ ↦ walk_477, fun _ _ ↦ walk_490, fun _ _ ↦ walk_493,
      fun _ _ ↦ walk_496, fun _ _ ↦ walk_509, fun _ _ ↦ walk_511, fun _ _ ↦ walk_513,
      fun _ _ ↦ walk_523, fun _ _ ↦ walk_525, fun _ _ ↦ walk_527, fun _ _ ↦ walk_537,
      fun _ _ ↦ walk_539, fun _ _ ↦ walk_541, fun _ _ ↦ walk_546, fun _ _ ↦ walk_555,
      fun _ _ ↦ walk_564, fun _ _ ↦ walk_573, fun _ _ ↦ walk_578, fun _ _ ↦ walk_585,
      fun _ _ ↦ walk_590, fun _ _ ↦ walk_597, fun _ _ ↦ walk_608, fun _ _ ↦ walk_613,
      fun _ _ ↦ walk_620, fun _ _ ↦ walk_622, fun _ _ ↦ walk_624, fun _ _ ↦ walk_627,
      fun _ _ ↦ walk_636, fun _ _ ↦ walk_645, fun _ _ ↦ walk_654, fun _ _ ↦ walk_665,
      fun _ _ ↦ walk_676, fun _ _ ↦ walk_687, fun _ _ ↦ walk_698, fun _ _ ↦ walk_700,
      fun _ _ ↦ walk_702, fun _ _ ↦ walk_705, fun _ _ ↦ walk_714, fun _ _ ↦ walk_723,
      fun _ _ ↦ walk_732, fun _ _ ↦ walk_743, fun _ _ ↦ walk_754, fun _ _ ↦ walk_765,
      fun _ _ ↦ walk_767, fun _ _ ↦ walk_777, fun _ _ ↦ walk_779, fun _ _ ↦ walk_783,
      fun _ _ ↦ walk_847, fun _ _ ↦ walk_849, fun _ _ ↦ walk_851, fun _ _ ↦ walk_853,
      fun _ _ ↦ walk_855, fun _ _ ↦ walk_857, fun _ _ ↦ walk_859, fun _ _ ↦ walk_861,
      fun _ _ ↦ walk_863, fun _ _ ↦ walk_865, fun _ _ ↦ walk_867, fun _ _ ↦ walk_869,
      fun _ _ ↦ walk_871, fun _ _ ↦ walk_873, fun _ _ ↦ walk_875, fun _ _ ↦ walk_877,
      fun _ _ ↦ walk_879, fun _ _ ↦ walk_880, fun _ _ ↦ walk_882, fun _ _ ↦ walk_884,
      fun _ _ ↦ walk_886, fun _ _ ↦ walk_887, fun _ _ ↦ walk_889, fun _ _ ↦ walk_891,
      fun _ _ ↦ walk_893, fun _ _ ↦ walk_895, fun _ _ ↦ walk_897, fun _ _ ↦ walk_899,
      fun _ _ ↦ walk_901, fun _ _ ↦ walk_903, fun _ _ ↦ walk_905, fun _ _ ↦ walk_907,
      fun _ _ ↦ walk_909, fun _ _ ↦ walk_911, fun _ _ ↦ walk_913, fun _ _ ↦ walk_915,
      fun _ _ ↦ walk_917, fun _ _ ↦ walk_919, fun _ _ ↦ walk_920, fun _ _ ↦ walk_921,
      fun _ _ ↦ walk_922, fun _ _ ↦ walk_923, fun _ _ ↦ walk_924, fun _ _ ↦ walk_925,
      fun _ _ ↦ walk_926, fun _ _ ↦ walk_927, fun _ _ ↦ walk_928, fun _ _ ↦ walk_929,
      fun _ _ ↦ walk_930, fun _ _ ↦ walk_931, fun _ _ ↦ walk_933, fun _ _ ↦ walk_934,
      fun _ _ ↦ walk_936, fun _ _ ↦ walk_938, fun _ _ ↦ walk_940, fun _ _ ↦ walk_941,
      fun _ _ ↦ walk_942, fun _ _ ↦ walk_943, fun _ _ ↦ walk_944, fun _ _ ↦ walk_945,
      fun _ _ ↦ walk_947, fun _ _ ↦ walk_949, fun _ _ ↦ walk_951, fun _ _ ↦ walk_953,
      fun _ _ ↦ walk_955, fun _ _ ↦ walk_956, fun _ _ ↦ walk_957, fun _ _ ↦ walk_958,
      fun _ _ ↦ walk_959, fun _ _ ↦ walk_960, fun _ _ ↦ walk_961, fun _ _ ↦ walk_962,
      fun _ _ ↦ walk_963, fun _ _ ↦ walk_964, fun _ _ ↦ walk_965, fun _ _ ↦ walk_966,
      fun _ _ ↦ walk_967, fun _ _ ↦ walk_968, fun _ _ ↦ walk_969, fun _ _ ↦ walk_970,
      fun _ _ ↦ walk_971, fun _ _ ↦ walk_972, fun _ _ ↦ walk_973, fun _ _ ↦ walk_974,
      fun _ _ ↦ walk_975, fun _ _ ↦ walk_976, fun _ _ ↦ walk_977, fun _ _ ↦ walk_978,
      fun _ _ ↦ walk_979, fun _ _ ↦ walk_980, fun _ _ ↦ walk_981, fun _ _ ↦ walk_982,
      fun _ _ ↦ walk_983, fun _ _ ↦ walk_984, fun _ _ ↦ walk_985, fun _ _ ↦ walk_986,
      fun _ _ ↦ walk_987, fun _ _ ↦ walk_988, fun _ _ ↦ walk_989, fun _ _ ↦ walk_990,
      fun _ _ ↦ walk_991⟩
  exact List.forall_iff_forall_mem.mp key

/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown

end
end LeanVM.Guest.End
