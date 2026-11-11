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
      fun _ _ ↦ walk_482, fun _ _ ↦ walk_488, fun _ _ ↦ walk_493, fun _ _ ↦ walk_497,
      fun _ _ ↦ walk_505, fun _ _ ↦ walk_509, fun _ _ ↦ walk_513, fun _ _ ↦ walk_516,
      fun _ _ ↦ walk_524, fun _ _ ↦ walk_528, fun _ _ ↦ walk_532, fun _ _ ↦ walk_536,
      fun _ _ ↦ walk_545, fun _ _ ↦ walk_549, fun _ _ ↦ walk_553, fun _ _ ↦ walk_558,
      fun _ _ ↦ walk_567, fun _ _ ↦ walk_570, fun _ _ ↦ walk_573, fun _ _ ↦ walk_576,
      fun _ _ ↦ walk_584, fun _ _ ↦ walk_587, fun _ _ ↦ walk_590, fun _ _ ↦ walk_593,
      fun _ _ ↦ walk_600, fun _ _ ↦ walk_603, fun _ _ ↦ walk_606, fun _ _ ↦ walk_612,
      fun _ _ ↦ walk_621, fun _ _ ↦ walk_625, fun _ _ ↦ walk_631, fun _ _ ↦ walk_635,
      fun _ _ ↦ walk_641, fun _ _ ↦ walk_646, fun _ _ ↦ walk_653, fun _ _ ↦ walk_658,
      fun _ _ ↦ walk_665, fun _ _ ↦ walk_670, fun _ _ ↦ walk_677, fun _ _ ↦ walk_682,
      fun _ _ ↦ walk_689, fun _ _ ↦ walk_692, fun _ _ ↦ walk_695, fun _ _ ↦ walk_700,
      fun _ _ ↦ walk_710, fun _ _ ↦ walk_718, fun _ _ ↦ walk_727, fun _ _ ↦ walk_737,
      fun _ _ ↦ walk_747, fun _ _ ↦ walk_758, fun _ _ ↦ walk_765, fun _ _ ↦ walk_768,
      fun _ _ ↦ walk_771, fun _ _ ↦ walk_775, fun _ _ ↦ walk_777, fun _ _ ↦ walk_784,
      fun _ _ ↦ walk_788, fun _ _ ↦ walk_793, fun _ _ ↦ walk_797, fun _ _ ↦ walk_802,
      fun _ _ ↦ walk_807, fun _ _ ↦ walk_813, fun _ _ ↦ walk_818, fun _ _ ↦ walk_824,
      fun _ _ ↦ walk_829, fun _ _ ↦ walk_836, fun _ _ ↦ walk_839, fun _ _ ↦ walk_843,
      fun _ _ ↦ walk_850, fun _ _ ↦ walk_853, fun _ _ ↦ walk_858, fun _ _ ↦ walk_860,
      fun _ _ ↦ walk_921, fun _ _ ↦ walk_922, fun _ _ ↦ walk_923, fun _ _ ↦ walk_924,
      fun _ _ ↦ walk_925, fun _ _ ↦ walk_926, fun _ _ ↦ walk_927, fun _ _ ↦ walk_928,
      fun _ _ ↦ walk_929, fun _ _ ↦ walk_930, fun _ _ ↦ walk_931, fun _ _ ↦ walk_932,
      fun _ _ ↦ walk_933, fun _ _ ↦ walk_934, fun _ _ ↦ walk_935, fun _ _ ↦ walk_936,
      fun _ _ ↦ walk_937, fun _ _ ↦ walk_938, fun _ _ ↦ walk_939, fun _ _ ↦ walk_940,
      fun _ _ ↦ walk_941, fun _ _ ↦ walk_942, fun _ _ ↦ walk_943, fun _ _ ↦ walk_944,
      fun _ _ ↦ walk_945, fun _ _ ↦ walk_946, fun _ _ ↦ walk_947, fun _ _ ↦ walk_948,
      fun _ _ ↦ walk_949, fun _ _ ↦ walk_950, fun _ _ ↦ walk_951, fun _ _ ↦ walk_952,
      fun _ _ ↦ walk_953, fun _ _ ↦ walk_954, fun _ _ ↦ walk_955, fun _ _ ↦ walk_956,
      fun _ _ ↦ walk_957, fun _ _ ↦ walk_958, fun _ _ ↦ walk_959, fun _ _ ↦ walk_960,
      fun _ _ ↦ walk_961, fun _ _ ↦ walk_962, fun _ _ ↦ walk_963, fun _ _ ↦ walk_964,
      fun _ _ ↦ walk_965, fun _ _ ↦ walk_966, fun _ _ ↦ walk_967, fun _ _ ↦ walk_968,
      fun _ _ ↦ walk_969, fun _ _ ↦ walk_970, fun _ _ ↦ walk_971, fun _ _ ↦ walk_972,
      fun _ _ ↦ walk_973, fun _ _ ↦ walk_974, fun _ _ ↦ walk_975, fun _ _ ↦ walk_976,
      fun _ _ ↦ walk_977, fun _ _ ↦ walk_978, fun _ _ ↦ walk_979, fun _ _ ↦ walk_980,
      fun _ _ ↦ walk_981, fun _ _ ↦ walk_982, fun _ _ ↦ walk_983, fun _ _ ↦ walk_984,
      fun _ _ ↦ walk_985, fun _ _ ↦ walk_986, fun _ _ ↦ walk_987, fun _ _ ↦ walk_988,
      fun _ _ ↦ walk_989, fun _ _ ↦ walk_990, fun _ _ ↦ walk_991, fun _ _ ↦ walk_992,
      fun _ _ ↦ walk_993, fun _ _ ↦ walk_994, fun _ _ ↦ walk_995, fun _ _ ↦ walk_996,
      fun _ _ ↦ walk_997, fun _ _ ↦ walk_998, fun _ _ ↦ walk_999, fun _ _ ↦ walk_1000,
      fun _ _ ↦ walk_1001, fun _ _ ↦ walk_1002, fun _ _ ↦ walk_1003, fun _ _ ↦ walk_1004,
      fun _ _ ↦ walk_1005, fun _ _ ↦ walk_1006, fun _ _ ↦ walk_1007, fun _ _ ↦ walk_1008,
      fun _ _ ↦ walk_1009, fun _ _ ↦ walk_1010, fun _ _ ↦ walk_1011, fun _ _ ↦ walk_1012,
      fun _ _ ↦ walk_1013, fun _ _ ↦ walk_1014, fun _ _ ↦ walk_1015, fun _ _ ↦ walk_1016,
      fun _ _ ↦ walk_1017, fun _ _ ↦ walk_1018, fun _ _ ↦ walk_1019, fun _ _ ↦ walk_1020,
      fun _ _ ↦ walk_1021, fun _ _ ↦ walk_1022, fun _ _ ↦ walk_1023, fun _ _ ↦ walk_1024,
      fun _ _ ↦ walk_1025, fun _ _ ↦ walk_1026, fun _ _ ↦ walk_1027, fun _ _ ↦ walk_1028,
      fun _ _ ↦ walk_1029, fun _ _ ↦ walk_1030, fun _ _ ↦ walk_1031, fun _ _ ↦ walk_1032,
      fun _ _ ↦ walk_1033, fun _ _ ↦ walk_1034, fun _ _ ↦ walk_1035⟩
  exact List.forall_iff_forall_mem.mp key

/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown

end
end LeanVM.Guest.End
