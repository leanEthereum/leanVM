/-
  LeanVM.Guest.B1.VerifySub.PhOpenT

  The statements of `verify_sub`'s body the opening phase reads, as templates checked against the
  core IR by the kernel.
-/

module

public import LeanVM.Guest.B1.VerifySub.Flat
public import LeanVM.Guest.B1.Bits.Templates
public import LeanVM.Guest.B1.Whir.Split
public import LeanVM.Guest.B1.Whir.Config

/-!
# The opening phase's statements

* `vsPubT` (statements `2906 .. 2919`): the public input's two halves split into limbs
  (`split_limbs`), the low limbs' line at `rm` (`pi_m0`, value `2905`), the high limbs' sum;
* `vsMergeT` (`3592 .. 3913`): the merged slices `kslices[i] + rho · link_slices[i]` at `3553`, then
  `ring_switch_target` on them and the map's challenges;
* `vsOpenT` (`3914 .. 4111`): the claims after the ring claim by Horner in `lam` (`target@2`), the
  cursor handed on, `open_stacked`'s dispatch, the stream bound, `check_stack_terminal`'s call.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1

@[expose] public section

/-- `verify_sub`'s statements 2906 to 2919. -/
def vsPubT : List Stmt :=
  splitLimbsT (.n 0) 2895 ++ splitLimbsT (.n 1) 2899 ++
    [.atom (.add (.n 2903) (.n 2895) (.n 2899)), .atom (.mul (.n 2904) (.n 1287) (.n 2903)),
      .atom (.add (.n 2905) (.n 2895) (.n 2904)), .atom (.add (.n 2906) (.n 2898) (.n 2902))]

theorem vsPubT_eq : (vsPre.drop 2906).take 14 = vsPubT := stmtsEqb_sound (by decide +kernel)

/-- Slice `i` of the merged claim: `merged[i] = kslices[i] + rho · cursor@3[80 + i]`. -/
def vsMergeBlk (i : ℕ) : List Stmt :=
  [.atom (.load (.n (3554 + 4 * i)) (.n 21) i), .atom (.load (.n (3555 + 4 * i)) (.n 1076) (80 + i)),
    .atom (.mul (.n (3556 + 4 * i)) (.n 3026) (.n (3555 + 4 * i))),
    .atom (.add (.n (3557 + 4 * i)) (.n (3554 + 4 * i)) (.n (3556 + 4 * i))),
    .atom (.load (.n (3557 + 4 * i)) (.n 3553) i)]

/-- `verify_sub`'s statements 3592 to 3913. -/
def vsMergeT : List Stmt :=
  .atom (.hint (.alloc (.n 3553) 64)) :: ((List.range 64).map vsMergeBlk).flatten ++
    [.call "ring_switch_target" [.n 3553, .n 3039] [.n 3810]]

theorem vsMergeT_eq : (vsPre.drop 3592).take 322 = vsMergeT := stmtsEqb_sound (by decide +kernel)

/-- Horner's step `jj`: `acc ← (acc + sent[54 - jj]) · lam`. -/
def vsHornBlk (j : ℕ) : List Stmt :=
  [.atom (.load (.n (3819 + 3 * j)) (.n 1076) (54 - j)),
    .atom (.add (.n (3820 + 3 * j)) (.n (3818 + 3 * j)) (.n (3819 + 3 * j))),
    .atom (.mul (.n (3821 + 3 * j)) (.n (3820 + 3 * j)) (.n 3027))]

/-- `open_stacked`'s specializations, as the dispatch names them. -/
def vsOsNames : List String :=
  ["open_stacked__L0", "open_stacked__L1", "open_stacked__L2", "open_stacked__L3", "open_stacked__L4",
    "open_stacked__L5", "open_stacked__L6", "open_stacked__L7", "open_stacked__L8", "open_stacked__L9",
    "open_stacked__L10", "open_stacked__L11", "open_stacked__L12", "open_stacked__L13", "open_stacked__L14"]

theorem vsOsNames_get : ∀ j (h : j < vsOsNames.length), vsOsNames[j] = "open_stacked__L" ++ Whir.natStr j := by
  decide +kernel

/-- `open_stacked`'s dispatch. -/
def vsOsDispatch : Stmt :=
  .dispatch (.n 489) vsOsNames
    [.n 96, .n 3033, .n 3034, .n 3035, .n 3036, .n 3037, .n 3986, .n 134, .n 137, .n 3988, .n 3990]
    [.n 3991, .n 3992, .n 3993, .n 3994, .n 3995, .n 3996]

/-- `check_stack_terminal`'s call. -/
def vsCstCall : Stmt :=
  .call "check_stack_terminal" [.n 4, .n 112, .n 486, .n 487, .n 485, .n 15, .n 408, .n 12, .n 101,
    .n 1287, .n 20, .n 17, .n 3040, .n 3026, .n 3027, .n 802, .n 4014, .n 3992, .n 3993, .n 3994,
    .n 3995, .n 3991, .n 22] []

/-- `verify_sub`'s statements 3914 to 4111. -/
def vsOpenT : List Stmt :=
  [.atom (.load (.n 3811) (.n 23) 0), .atom (.mul (.n 3812) (.n 3811) (.n 3027)),
    .atom (.add (.n 3813) (.n 3812) (.n 2921)), .atom (.mul (.n 3814) (.n 3813) (.n 3027)),
    .atom (.add (.n 3815) (.n 3814) (.n 2908)), .atom (.mul (.n 3816) (.n 3815) (.n 3027)),
    .atom (.add (.n 3817) (.n 3816) (.n 2905)), .atom (.mul (.n 3818) (.n 3817) (.n 3027))] ++
  ((List.range 55).map vsHornBlk).flatten ++
  [.atom (.add (.n 3984) (.n 3983) (.n 779)), .atom (.mul (.n 3985) (.n 3984) (.n 3027)),
    .atom (.add (.n 3986) (.n 3810) (.n 3985)), .atom (.const (.n 3987) (word 2 0)),
    .atom (.mul (.n 3988) (.n 2920) (.n 3987)), .atom (.const (.n 3989) (word 365917469723852800 0)),
    .atom (.mul (.n 3990) (.n 4) (.n 3989)), vsOsDispatch,
    .atom (.mul (.n 3997) (.n 42) (.n 42)), .atom (.mul (.n 3998) (.n 3997) (.n 3997)),
    .atom (.mul (.n 3999) (.n 3998) (.n 3998)), .atom (.mul (.n 4000) (.n 3999) (.n 3999)),
    .atom (.mul (.n 4001) (.n 4000) (.n 4000)), .atom (.mul (.n 4002) (.n 4001) (.n 4001)),
    .atom (.mul (.n 4003) (.n 4002) (.n 4002)), .atom (.mul (.n 4004) (.n 4003) (.n 4003)),
    .atom (.const (.n 4005) (word 2 0)), .atom (.mul (.n 4006) (.n 4004) (.n 4005)),
    .atom (.const (.n 4007) (word 9223372036854775821 0)), .atom (.mul (.n 4008) (.n 4006) (.n 4007)),
    .atom (.mul (.n 3996) (.n 4009) (.n 55)),
    .atom (.rangeCheck (.n 4009) (.n 4010) (.n 4011) (.n 4012) (.n 4008)),
    .atom (.const (.n 4013) (word 0 1)), .atom (.mul (.n 4014) (.n 4013) (.n 802)), vsCstCall]

theorem vsOpenT_eq : (vsPre.drop 3914).take 198 = vsOpenT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 376 to 409: the tallest table's height `g_n` is one of the six. -/
def vsTallT : List Stmt := (
  .atom (.load (.n 408) (.n 9) 0) ::
  .atom (.load (.n 409) (.n 9) 1) ::
  .atom (.load (.n 410) (.n 9) 2) ::
  .atom (.const (.n 411) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 412) (.n 115)) ::
  .atom (.rangeCheck (.n 412) (.n 413) (.n 414) (.n 415) (.n 411)) ::
  .atom (.add (.n 416) (.n 408) (.n 115)) ::
  .atom (.const (.n 417) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 418) (.n 116)) ::
  .atom (.rangeCheck (.n 418) (.n 419) (.n 420) (.n 421) (.n 417)) ::
  .atom (.add (.n 422) (.n 408) (.n 116)) ::
  .atom (.mul (.n 423) (.n 416) (.n 422)) ::
  .atom (.const (.n 424) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 425) (.n 117)) ::
  .atom (.rangeCheck (.n 425) (.n 426) (.n 427) (.n 428) (.n 424)) ::
  .atom (.add (.n 429) (.n 408) (.n 117)) ::
  .atom (.mul (.n 430) (.n 423) (.n 429)) ::
  .atom (.const (.n 431) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 432) (.n 118)) ::
  .atom (.rangeCheck (.n 432) (.n 433) (.n 434) (.n 435) (.n 431)) ::
  .atom (.add (.n 436) (.n 408) (.n 118)) ::
  .atom (.mul (.n 437) (.n 430) (.n 436)) ::
  .atom (.const (.n 438) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 439) (.n 119)) ::
  .atom (.rangeCheck (.n 439) (.n 440) (.n 441) (.n 442) (.n 438)) ::
  .atom (.add (.n 443) (.n 408) (.n 119)) ::
  .atom (.mul (.n 444) (.n 437) (.n 443)) ::
  .atom (.const (.n 445) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 446) (.n 120)) ::
  .atom (.rangeCheck (.n 446) (.n 447) (.n 448) (.n 449) (.n 445)) ::
  .atom (.add (.n 450) (.n 408) (.n 120)) ::
  .atom (.mul (.n 451) (.n 444) (.n 450)) ::
  .atom (.const (.n 452) (word 0 0)) ::
  .atom (.assertEq (.n 451) (.n 452)) ::
  [])

theorem vsTallT_eq : (vsPre.drop 376).take 34 = vsTallT := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.VerifySub
