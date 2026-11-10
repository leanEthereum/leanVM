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
and `verify_bus_gkr` (`10`) and its layer loop `__loop6` (`91`), whose
obligations (the layers' parities, `GkrPar`) the gkr track proves (`WalkGkr.lean`;
`walkKnown_of_gkr`).
-/

namespace LeanVM.Guest.End

@[expose] public section

/-- **The walks' obligations**, given `verify_bus_gkr`'s and its layer loop's. -/
theorem walkKnown_of_gkr (h10 : CutsKnown 10) (h91 : CutsKnown 91) : WalkKnown := by
  -- One conjunct per function of `Checked.oblFns`, in order: linear, where `rcases` over the
  -- membership disjunction is quadratic.
  have key : List.Forall (fun j ↦ j ≠ 1 → j ≠ 19 → CutsKnown j) Checked.oblFns :=
    ⟨fun h _ ↦ absurd rfl h, fun _ _ ↦ h10, fun _ h ↦ absurd rfl h, fun _ _ ↦ h91,
      fun _ _ ↦ walk_332, fun _ _ ↦ walk_333, fun _ _ ↦ walk_334, fun _ _ ↦ walk_335,
      fun _ _ ↦ walk_336, fun _ _ ↦ walk_337, fun _ _ ↦ walk_338, fun _ _ ↦ walk_339,
      fun _ _ ↦ walk_340, fun _ _ ↦ walk_341, fun _ _ ↦ walk_342, fun _ _ ↦ walk_343,
      fun _ _ ↦ walk_344, fun _ _ ↦ walk_345, fun _ _ ↦ walk_346, fun _ _ ↦ walk_347,
      fun _ _ ↦ walk_348, fun _ _ ↦ walk_349, fun _ _ ↦ walk_350, fun _ _ ↦ walk_351,
      fun _ _ ↦ walk_352, fun _ _ ↦ walk_353, fun _ _ ↦ walk_354, fun _ _ ↦ walk_355,
      fun _ _ ↦ walk_356, fun _ _ ↦ walk_357, fun _ _ ↦ walk_358, fun _ _ ↦ walk_359,
      fun _ _ ↦ walk_483, fun _ _ ↦ walk_490, fun _ _ ↦ walk_496, fun _ _ ↦ walk_500,
      fun _ _ ↦ walk_509, fun _ _ ↦ walk_514, fun _ _ ↦ walk_519, fun _ _ ↦ walk_522,
      fun _ _ ↦ walk_531, fun _ _ ↦ walk_536, fun _ _ ↦ walk_541, fun _ _ ↦ walk_547,
      fun _ _ ↦ walk_557, fun _ _ ↦ walk_562, fun _ _ ↦ walk_567, fun _ _ ↦ walk_573,
      fun _ _ ↦ walk_583, fun _ _ ↦ walk_586, fun _ _ ↦ walk_589, fun _ _ ↦ walk_592,
      fun _ _ ↦ walk_601, fun _ _ ↦ walk_604, fun _ _ ↦ walk_607, fun _ _ ↦ walk_610,
      fun _ _ ↦ walk_618, fun _ _ ↦ walk_621, fun _ _ ↦ walk_624, fun _ _ ↦ walk_630,
      fun _ _ ↦ walk_639, fun _ _ ↦ walk_643, fun _ _ ↦ walk_649, fun _ _ ↦ walk_653,
      fun _ _ ↦ walk_659, fun _ _ ↦ walk_664, fun _ _ ↦ walk_671, fun _ _ ↦ walk_676,
      fun _ _ ↦ walk_683, fun _ _ ↦ walk_688, fun _ _ ↦ walk_695, fun _ _ ↦ walk_700,
      fun _ _ ↦ walk_707, fun _ _ ↦ walk_710, fun _ _ ↦ walk_713, fun _ _ ↦ walk_717,
      fun _ _ ↦ walk_720, fun _ _ ↦ walk_730, fun _ _ ↦ walk_738, fun _ _ ↦ walk_747,
      fun _ _ ↦ walk_757, fun _ _ ↦ walk_767, fun _ _ ↦ walk_777, fun _ _ ↦ walk_784,
      fun _ _ ↦ walk_787, fun _ _ ↦ walk_790, fun _ _ ↦ walk_794, fun _ _ ↦ walk_796,
      fun _ _ ↦ walk_803, fun _ _ ↦ walk_807, fun _ _ ↦ walk_812, fun _ _ ↦ walk_816,
      fun _ _ ↦ walk_821, fun _ _ ↦ walk_826, fun _ _ ↦ walk_832, fun _ _ ↦ walk_837,
      fun _ _ ↦ walk_843, fun _ _ ↦ walk_848, fun _ _ ↦ walk_855, fun _ _ ↦ walk_858,
      fun _ _ ↦ walk_862, fun _ _ ↦ walk_869, fun _ _ ↦ walk_872, fun _ _ ↦ walk_877,
      fun _ _ ↦ walk_879, fun _ _ ↦ walk_940, fun _ _ ↦ walk_941, fun _ _ ↦ walk_942,
      fun _ _ ↦ walk_943, fun _ _ ↦ walk_944, fun _ _ ↦ walk_945, fun _ _ ↦ walk_946,
      fun _ _ ↦ walk_947, fun _ _ ↦ walk_948, fun _ _ ↦ walk_949, fun _ _ ↦ walk_950,
      fun _ _ ↦ walk_951, fun _ _ ↦ walk_952, fun _ _ ↦ walk_953, fun _ _ ↦ walk_954,
      fun _ _ ↦ walk_955, fun _ _ ↦ walk_956, fun _ _ ↦ walk_957, fun _ _ ↦ walk_958,
      fun _ _ ↦ walk_959, fun _ _ ↦ walk_960, fun _ _ ↦ walk_961, fun _ _ ↦ walk_962,
      fun _ _ ↦ walk_963, fun _ _ ↦ walk_964, fun _ _ ↦ walk_965, fun _ _ ↦ walk_966,
      fun _ _ ↦ walk_967, fun _ _ ↦ walk_968, fun _ _ ↦ walk_969, fun _ _ ↦ walk_970,
      fun _ _ ↦ walk_971, fun _ _ ↦ walk_972, fun _ _ ↦ walk_973, fun _ _ ↦ walk_974,
      fun _ _ ↦ walk_975, fun _ _ ↦ walk_976, fun _ _ ↦ walk_977, fun _ _ ↦ walk_978,
      fun _ _ ↦ walk_979, fun _ _ ↦ walk_980, fun _ _ ↦ walk_981, fun _ _ ↦ walk_982,
      fun _ _ ↦ walk_983, fun _ _ ↦ walk_984, fun _ _ ↦ walk_985, fun _ _ ↦ walk_986,
      fun _ _ ↦ walk_987, fun _ _ ↦ walk_988, fun _ _ ↦ walk_989, fun _ _ ↦ walk_990,
      fun _ _ ↦ walk_991, fun _ _ ↦ walk_992, fun _ _ ↦ walk_993, fun _ _ ↦ walk_994,
      fun _ _ ↦ walk_995, fun _ _ ↦ walk_996, fun _ _ ↦ walk_997, fun _ _ ↦ walk_998,
      fun _ _ ↦ walk_999, fun _ _ ↦ walk_1000, fun _ _ ↦ walk_1001, fun _ _ ↦ walk_1002,
      fun _ _ ↦ walk_1003, fun _ _ ↦ walk_1004, fun _ _ ↦ walk_1005, fun _ _ ↦ walk_1006,
      fun _ _ ↦ walk_1007, fun _ _ ↦ walk_1008, fun _ _ ↦ walk_1009, fun _ _ ↦ walk_1010,
      fun _ _ ↦ walk_1011, fun _ _ ↦ walk_1012, fun _ _ ↦ walk_1013, fun _ _ ↦ walk_1014,
      fun _ _ ↦ walk_1015, fun _ _ ↦ walk_1016, fun _ _ ↦ walk_1017, fun _ _ ↦ walk_1018,
      fun _ _ ↦ walk_1019, fun _ _ ↦ walk_1020, fun _ _ ↦ walk_1021, fun _ _ ↦ walk_1022,
      fun _ _ ↦ walk_1023, fun _ _ ↦ walk_1024, fun _ _ ↦ walk_1025, fun _ _ ↦ walk_1026,
      fun _ _ ↦ walk_1027, fun _ _ ↦ walk_1028, fun _ _ ↦ walk_1029, fun _ _ ↦ walk_1030,
      fun _ _ ↦ walk_1031, fun _ _ ↦ walk_1032, fun _ _ ↦ walk_1033, fun _ _ ↦ walk_1034,
      fun _ _ ↦ walk_1035, fun _ _ ↦ walk_1036, fun _ _ ↦ walk_1037, fun _ _ ↦ walk_1038,
      fun _ _ ↦ walk_1039, fun _ _ ↦ walk_1040, fun _ _ ↦ walk_1041, fun _ _ ↦ walk_1042,
      fun _ _ ↦ walk_1043, fun _ _ ↦ walk_1044, fun _ _ ↦ walk_1045, fun _ _ ↦ walk_1046,
      fun _ _ ↦ walk_1047, fun _ _ ↦ walk_1048, fun _ _ ↦ walk_1049, fun _ _ ↦ walk_1050,
      fun _ _ ↦ walk_1051, fun _ _ ↦ walk_1052, fun _ _ ↦ walk_1053, fun _ _ ↦ walk_1054,
      fun _ _ ↦ walk_1055⟩
  exact List.forall_iff_forall_mem.mp key

/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown

end
end LeanVM.Guest.End
