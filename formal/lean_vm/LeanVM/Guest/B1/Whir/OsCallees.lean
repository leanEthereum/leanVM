/-
  LeanVM.Guest.B1.Whir.OsCallees

  The placed completeness `open_stacked` assumes of its callees from group 1.
-/

module

public import LeanVM.Guest.B1.FiatShamir
public import LeanVM.Guest.B1.Opening
public import LeanVM.Guest.B1.RowWeights
public import LeanVM.Guest.B1.FoldFinal
public import LeanVM.Guest.B1.OpeningOod
public import LeanVM.Guest.B1.Grind
public import LeanVM.Guest.B1.QueryBits
public import LeanVM.Guest.B1.Uniform

/-!
# `open_stacked`'s callees from group 1, placed

What `open_stacked`'s completeness takes of the callees other groups prove, in the uniform placed
form (`Uniform.lean`):

* the functions returning fixed words, `CompleteRel` on their meaning without their own scratch:
  `opening_fold`, `assert_canonical`, `opening_ood_point` (its states' run its own),
  `grind_check` (its frame run its own, at most 64 bits);
* those whose meaning reads words its arguments and returns do not pin, on every memory holding
  the caller's words (`LowDef` dropped, as `CompleteMem`): `opening_final_message__L{n}`,
  `opening_row_weights__L{folds}_L{rev}`, `fold_final_msg__L{n}`;
* `decode_query_bits__L{d}`, which stores pointers into its own frame run in the caller's buffer,
  in an explicit form: at every frame pointer `fp`, a tree of `fs name` words whose data holds the
  run of the word's 192 bits at its certificate cell (`dqRunL`), on every memory where the
  caller's words hold the decoded positions and the run's pointers.

`OsCalleesAt` collects them at the names and shapes the 28 configurations call.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **`opening_fold`, placed** (TRIAGE #31). -/
def OsFoldAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop := CompleteRel fs cert k "opening_fold" MeaningOpeningFold

/-- **`assert_canonical`, placed** (TRIAGE #2). -/
def OsAssertCanonicalAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  CompleteRel fs cert k "assert_canonical" fun _ args rets => MeaningAssertCanonical args rets

/-- `opening_ood_point`'s meaning without its states' run. -/
def OodPointPre (rd : Reader) : List E → List E → Prop
  | [fs0, fs1, point, ng], rets =>
      ∃ m < ordG, 2 * m + 2 < ordG ∧ ng = gen ^ m ∧
        ((m = 0 ∧ rets = [fs0, fs1]) ∨
          (0 < m ∧ ∃ cv rs cv', (fs0, fs1) = digestScalars cv ∧ RunsTo (Prog.sampleN m) cv [] rs cv' ∧
            ReadsAt rd point rs ∧ rets = [(digestScalars cv').1, (digestScalars cv').2]))
  | _, _ => False

/-- **`opening_ood_point`, placed** (TRIAGE #32). -/
def OsOodPointAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop := CompleteRel fs cert k "opening_ood_point" OodPointPre

/-- `grind_check`'s meaning without its frame run. -/
def GrindPre (_rd : Reader) : List E → List E → Prop
  | [s0, s1, nonce, ng], rets =>
      rets = [] ∧ ∃ m < ordG, m ≤ 64 ∧ ng = gen ^ m ∧ ∃ cv, (s0, s1) = digestScalars cv ∧
        powOk m nonce (gcDigest cv nonce) = true
  | _, _ => False

/-- **`grind_check`, placed** (TRIAGE #18). -/
def OsGrindAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop := CompleteRel fs cert k "grind_check" GrindPre

/-- **`opening_final_message__L{n}`, placed** (TRIAGE #33). -/
def OsFinalMsgAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (n : ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningOpeningFinalMessage n rd args rets) →
    CompleteAt fs cert k name Lin args (Returns rets)

/-- **`opening_row_weights__L{folds}_L{rev}`, placed** (TRIAGE #34). -/
def OsRowWeightsAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (folds rev : ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningOpeningRowWeights folds rev rd args rets) →
    CompleteAt fs cert k name Lin args (Returns rets)

/-- **`fold_final_msg__L{n}`, placed** (TRIAGE #24). -/
def OsFoldFinalAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (n : ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningFoldFinalMsg n rd args rets) →
    CompleteAt fs cert k name Lin args (Returns rets)

/-- `decode_query_bits`' frame run at `fp`: the 192 bits of the word `w` at the certificate's
cell of its first value `.n 3`. -/
def dqRunL (cert : String → V → ℕ) (name : String) (fp : ℕ) (w : E) : Main.Layout :=
  [(fp + cert name (.n 3), (List.range 192).map fun i => bitE ((eToNat w).testBit i))]

/-- **`decode_query_bits__L{d}`, placed** (TRIAGE #17): at every frame pointer `fp`, on every
memory where the caller's words `Lin` hold the decoded positions at `pos` and the run's pointers
`g^(fp + cert name (.n 3))·g^(j·d)` at `ptrs`, a tree of `fs name` words holds, its data holding
the run `dqRunL`, its other words `Lown`, its loads in its data or `Lin`. -/
def OsDecodeAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d : ℕ) (name : String) : Prop :=
  ∀ (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ),
    (∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert name (.n 3))) * gen ^ (j * d))) →
    ∃ Lown : Main.Layout, Within (dqRunL cert name fp w ++ Lown) fp (fs name) ∧
      ∀ rd, LowDef k rd → MemL rd (dqRunL cert name fp w ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (dqRunL cert name fp w)) fp (fs name) name
          [w, pos, ptrs] []

/-- The depths `decode_query_bits` is specialized at, with their names. -/
def osDqNames : List (ℕ × String) :=
  [(14, "decode_query_bits__L14"),
    (15, "decode_query_bits__L15"),
    (16, "decode_query_bits__L16"),
    (17, "decode_query_bits__L17"),
    (18, "decode_query_bits__L18"),
    (19, "decode_query_bits__L19"),
    (20, "decode_query_bits__L20"),
    (21, "decode_query_bits__L21"),
    (22, "decode_query_bits__L22"),
    (23, "decode_query_bits__L23"),
    (24, "decode_query_bits__L24"),
    (25, "decode_query_bits__L25"),
    (26, "decode_query_bits__L26")]

/-- **The callees of `open_stacked` from group 1**, at the names and shapes its 28
configurations call. -/
structure OsCalleesAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop where
  fold : OsFoldAt fs cert k
  canonical : OsAssertCanonicalAt fs cert k
  ood : OsOodPointAt fs cert k
  grind : OsGrindAt fs cert k
  finalMsg4 : OsFinalMsgAt fs cert k "opening_final_message__L4" 4
  finalMsg8 : OsFinalMsgAt fs cert k "opening_final_message__L8" 8
  finalMsg16 : OsFinalMsgAt fs cert k "opening_final_message__L16" 16
  finalMsg32 : OsFinalMsgAt fs cert k "opening_final_message__L32" 32
  rowWeights4 : OsRowWeightsAt fs cert k "opening_row_weights__L4_L0" 4 0
  rowWeights6 : OsRowWeightsAt fs cert k "opening_row_weights__L6_L1" 6 1
  foldFinal2 : OsFoldFinalAt fs cert k "fold_final_msg__L2" 2
  foldFinal3 : OsFoldFinalAt fs cert k "fold_final_msg__L3" 3
  foldFinal4 : OsFoldFinalAt fs cert k "fold_final_msg__L4" 4
  foldFinal5 : OsFoldFinalAt fs cert k "fold_final_msg__L5" 5
  decode : ∀ p ∈ osDqNames, OsDecodeAt fs cert k p.1 p.2

/-! ## On disjoint layouts

The same callees in the `CompleteAtD` form (`Uniform.lean`): their layouts pairwise disjoint. -/

/-- `OsFoldAt` on disjoint layouts. -/
def OsFoldAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  CompleteRelD fs cert k "opening_fold" MeaningOpeningFold

/-- `OsAssertCanonicalAt` on disjoint layouts. -/
def OsAssertCanonicalAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  CompleteRelD fs cert k "assert_canonical" fun _ args rets => MeaningAssertCanonical args rets

/-- `OsOodPointAt` on disjoint layouts. -/
def OsOodPointAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  CompleteRelD fs cert k "opening_ood_point" OodPointPre

/-- `OsGrindAt` on disjoint layouts. -/
def OsGrindAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  CompleteRelD fs cert k "grind_check" GrindPre

/-- `OsFinalMsgAt` on disjoint layouts. -/
def OsFinalMsgAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (n : ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningOpeningFinalMessage n rd args rets) →
    CompleteAtD fs cert k name Lin args (Returns rets)

/-- `OsRowWeightsAt` on disjoint layouts. -/
def OsRowWeightsAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (folds rev : ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningOpeningRowWeights folds rev rd args rets) →
    CompleteAtD fs cert k name Lin args (Returns rets)

/-- `OsFoldFinalAt` on disjoint layouts. -/
def OsFoldFinalAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (n : ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningFoldFinalMsg n rd args rets) →
    CompleteAtD fs cert k name Lin args (Returns rets)

/-- `OsDecodeAt` on disjoint layouts. -/
def OsDecodeAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d : ℕ) (name : String) : Prop :=
  ∀ (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ),
    (∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert name (.n 3))) * gen ^ (j * d))) →
    ∃ Lown : Main.Layout, Within (dqRunL cert name fp w ++ Lown) fp (fs name) ∧
      DisjL (dqRunL cert name fp w ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd (dqRunL cert name fp w ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (dqRunL cert name fp w)) fp (fs name) name
          [w, pos, ptrs] []

/-- **The callees of `open_stacked` from group 1, on disjoint layouts.** -/
structure OsCalleesAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop where
  fold : OsFoldAtD fs cert k
  canonical : OsAssertCanonicalAtD fs cert k
  ood : OsOodPointAtD fs cert k
  grind : OsGrindAtD fs cert k
  finalMsg4 : OsFinalMsgAtD fs cert k "opening_final_message__L4" 4
  finalMsg8 : OsFinalMsgAtD fs cert k "opening_final_message__L8" 8
  finalMsg16 : OsFinalMsgAtD fs cert k "opening_final_message__L16" 16
  finalMsg32 : OsFinalMsgAtD fs cert k "opening_final_message__L32" 32
  rowWeights4 : OsRowWeightsAtD fs cert k "opening_row_weights__L4_L0" 4 0
  rowWeights6 : OsRowWeightsAtD fs cert k "opening_row_weights__L6_L1" 6 1
  foldFinal2 : OsFoldFinalAtD fs cert k "fold_final_msg__L2" 2
  foldFinal3 : OsFoldFinalAtD fs cert k "fold_final_msg__L3" 3
  foldFinal4 : OsFoldFinalAtD fs cert k "fold_final_msg__L4" 4
  foldFinal5 : OsFoldFinalAtD fs cert k "fold_final_msg__L5" 5
  decode : ∀ p ∈ osDqNames, OsDecodeAtD fs cert k p.1 p.2

/-! ## On disjoint layouts, by bounded trees

The same callees in the `CompleteAtB` form, each bound a function of the call's arguments (a
loop's trip count depends on them). -/

/-- `CompleteRelB` with a bound depending on the arguments. -/
def CompleteRelBA (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtB fs cert k f Lin args (Returns rets) (B args)

/-- `OsFinalMsgAtD` by bounded trees. -/
def OsFinalMsgAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (n : ℕ)
    (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningOpeningFinalMessage n rd args rets) →
    CompleteAtB fs cert k name Lin args (Returns rets) (B args)

/-- `OsRowWeightsAtD` by bounded trees. -/
def OsRowWeightsAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (folds rev : ℕ)
    (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningOpeningRowWeights folds rev rd args rets) →
    CompleteAtB fs cert k name Lin args (Returns rets) (B args)

/-- `OsFoldFinalAtD` by bounded trees. -/
def OsFoldFinalAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (n : ℕ)
    (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningFoldFinalMsg n rd args rets) →
    CompleteAtB fs cert k name Lin args (Returns rets) (B args)

/-- `OsDecodeAtD`, its tree `fs name` words (the decoder calls nothing). -/
def OsDecodeAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d : ℕ) (name : String) : Prop :=
  OsDecodeAtD fs cert k d name

/-- **The callees of `open_stacked` from group 1, by bounded trees**, each with its bound. -/
structure OsCalleesAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Type where
  foldB : List E → ℕ
  fold : CompleteRelBA fs cert k "opening_fold" MeaningOpeningFold foldB
  canonicalB : List E → ℕ
  canonical : CompleteRelBA fs cert k "assert_canonical" (fun _ args rets => MeaningAssertCanonical args rets)
    canonicalB
  oodB : List E → ℕ
  ood : CompleteRelBA fs cert k "opening_ood_point" OodPointPre oodB
  grindB : List E → ℕ
  grind : CompleteRelBA fs cert k "grind_check" GrindPre grindB
  finalMsg4B : List E → ℕ
  finalMsg4 : OsFinalMsgAtB fs cert k "opening_final_message__L4" 4 finalMsg4B
  finalMsg8B : List E → ℕ
  finalMsg8 : OsFinalMsgAtB fs cert k "opening_final_message__L8" 8 finalMsg8B
  finalMsg16B : List E → ℕ
  finalMsg16 : OsFinalMsgAtB fs cert k "opening_final_message__L16" 16 finalMsg16B
  finalMsg32B : List E → ℕ
  finalMsg32 : OsFinalMsgAtB fs cert k "opening_final_message__L32" 32 finalMsg32B
  rowWeights4B : List E → ℕ
  rowWeights4 : OsRowWeightsAtB fs cert k "opening_row_weights__L4_L0" 4 0 rowWeights4B
  rowWeights6B : List E → ℕ
  rowWeights6 : OsRowWeightsAtB fs cert k "opening_row_weights__L6_L1" 6 1 rowWeights6B
  foldFinal2B : List E → ℕ
  foldFinal2 : OsFoldFinalAtB fs cert k "fold_final_msg__L2" 2 foldFinal2B
  foldFinal3B : List E → ℕ
  foldFinal3 : OsFoldFinalAtB fs cert k "fold_final_msg__L3" 3 foldFinal3B
  foldFinal4B : List E → ℕ
  foldFinal4 : OsFoldFinalAtB fs cert k "fold_final_msg__L4" 4 foldFinal4B
  foldFinal5B : List E → ℕ
  foldFinal5 : OsFoldFinalAtB fs cert k "fold_final_msg__L5" 5 foldFinal5B
  decode : ∀ p ∈ osDqNames, OsDecodeAtB fs cert k p.1 p.2

end
end LeanVM.Guest.B1
