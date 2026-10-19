/-
  LeanVM.Guest.B2C.CertFacts

  The certificate facts other groups take as hypotheses, at the deployed frame sizes and
  certificates.
-/

module

public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.B1.G1Placed
public import LeanVM.Guest.B1.Da.VectorT
public import LeanVM.Guest.B1.Whir.OsInstBase

/-!
# The certificate facts

Each is a frame run that fits its frame, read off the certificate (`cert`) and the compiler's
frame sizes (`fsOf`) by the kernel, then at `fs`, which is never smaller (`fsOf_le_fs`):

* `g1Certs`: `grind_check`'s and `decode_query_bits__L{d}`'s (`B1.G1Certs`);
* `dvc20`, `dvc4`: `da_verify`'s and `da_vector_cell__L{0,1}`'s (`B1.Main.CalleesHyps`);
* `osOqFits`: the `opening_queries` loop helpers' (`B1.OsOqFits`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- `fs` is the compiler's frame size, `main`'s holding the jump table, at least the header. -/
theorem fsOf_le_fs (f : String) : fsOf f ≤ fs f := by
  unfold fsOf fs
  rcases coreProgram.indexOf? f with _ | _ | i
  · exact Nat.zero_le _
  · show fsAt 1 ≤ mainFrame
    decide +kernel
  · exact Nat.le_max_right _ _

theorem g1Certs_fsOf : G1Certs fsOf cert where
  grind := by decide +kernel
  decode := by
    have h : ∀ d ∈ List.range' 14 13, cert (dqName d) (.n 3) + 192 ≤ fsOf (dqName d) := by decide +kernel
    intro d h1 h2
    exact h d (List.mem_range'_1.mpr ⟨h1, by omega⟩)

theorem g1Certs : G1Certs fs cert where
  grind := g1Certs_fsOf.grind.trans (fsOf_le_fs _)
  decode := fun d h1 h2 => (g1Certs_fsOf.decode d h1 h2).trans (fsOf_le_fs _)

theorem dvc20_fsOf : cert "da_verify" (.n 20) + 385 ≤ fsOf "da_verify" := by decide +kernel

theorem dvc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify" := dvc20_fsOf.trans (fsOf_le_fs _)

theorem dvc4_fsOf : ∀ f, cert (Digest.vxName f) (.n 4) + 256 ≤ fsOf (Digest.vxName f)
  | false => by decide +kernel
  | true => by decide +kernel

theorem dvc4 : ∀ f, cert (Digest.vxName f) (.n 4) + 256 ≤ fs (Digest.vxName f) :=
  fun f => (dvc4_fsOf f).trans (fsOf_le_fs _)

private theorem oqFit_430 : cert "__loop430" (.n (oqP 1 64 8)) + 4 * 9 ≤ fsOf "__loop430" := by decide +kernel

private theorem oqFit_432 : cert "__loop432" (.n (oqP 0 16 6)) + 4 * 10 ≤ fsOf "__loop432" := by decide +kernel

private theorem oqFit_434 : cert "__loop434" (.n (oqP 0 16 6)) + 4 * 10 ≤ fsOf "__loop434" := by decide +kernel

private theorem oqFit_435 : cert "__loop435" (.n (oqP 0 16 6)) + 4 * 9 ≤ fsOf "__loop435" := by decide +kernel

private theorem oqFit_436 : cert "__loop436" (.n (oqP 1 64 8)) + 4 * 10 ≤ fsOf "__loop436" := by decide +kernel

private theorem oqFit_437 : cert "__loop437" (.n (oqP 0 16 6)) + 4 * 11 ≤ fsOf "__loop437" := by decide +kernel

private theorem oqFit_438 : cert "__loop438" (.n (oqP 0 16 6)) + 4 * 11 ≤ fsOf "__loop438" := by decide +kernel

private theorem oqFit_439 : cert "__loop439" (.n (oqP 1 64 8)) + 4 * 11 ≤ fsOf "__loop439" := by decide +kernel

private theorem oqFit_440 : cert "__loop440" (.n (oqP 0 16 6)) + 4 * 12 ≤ fsOf "__loop440" := by decide +kernel

private theorem oqFit_441 : cert "__loop441" (.n (oqP 0 16 6)) + 4 * 12 ≤ fsOf "__loop441" := by decide +kernel

private theorem oqFit_442 : cert "__loop442" (.n (oqP 1 64 8)) + 4 * 12 ≤ fsOf "__loop442" := by decide +kernel

private theorem oqFit_443 : cert "__loop443" (.n (oqP 0 16 6)) + 4 * 13 ≤ fsOf "__loop443" := by decide +kernel

private theorem oqFit_444 : cert "__loop444" (.n (oqP 0 16 6)) + 4 * 13 ≤ fsOf "__loop444" := by decide +kernel

private theorem oqFit_445 : cert "__loop445" (.n (oqP 1 64 8)) + 4 * 13 ≤ fsOf "__loop445" := by decide +kernel

private theorem oqFit_446 : cert "__loop446" (.n (oqP 0 16 6)) + 4 * 14 ≤ fsOf "__loop446" := by decide +kernel

private theorem oqFit_447 : cert "__loop447" (.n (oqP 0 16 6)) + 4 * 14 ≤ fsOf "__loop447" := by decide +kernel

private theorem oqFit_448 : cert "__loop448" (.n (oqP 1 64 8)) + 4 * 14 ≤ fsOf "__loop448" := by decide +kernel

private theorem oqFit_449 : cert "__loop449" (.n (oqP 0 16 6)) + 4 * 15 ≤ fsOf "__loop449" := by decide +kernel

private theorem oqFit_450 : cert "__loop450" (.n (oqP 0 16 6)) + 4 * 15 ≤ fsOf "__loop450" := by decide +kernel

private theorem oqFit_451 : cert "__loop451" (.n (oqP 1 64 8)) + 4 * 15 ≤ fsOf "__loop451" := by decide +kernel

private theorem oqFit_452 : cert "__loop452" (.n (oqP 0 16 6)) + 4 * 16 ≤ fsOf "__loop452" := by decide +kernel

private theorem oqFit_453 : cert "__loop453" (.n (oqP 0 16 6)) + 4 * 16 ≤ fsOf "__loop453" := by decide +kernel

private theorem oqFit_455 : cert "__loop455" (.n (oqP 0 16 6)) + 4 * 14 ≤ fsOf "__loop455" := by decide +kernel

private theorem oqFit_457 : cert "__loop457" (.n (oqP 1 64 8)) + 4 * 11 ≤ fsOf "__loop457" := by decide +kernel

private theorem oqFit_458 : cert "__loop458" (.n (oqP 1 64 8)) + 4 * 12 ≤ fsOf "__loop458" := by decide +kernel

private theorem oqFit_459 : cert "__loop459" (.n (oqP 1 64 8)) + 4 * 13 ≤ fsOf "__loop459" := by decide +kernel

private theorem oqFit_460 : cert "__loop460" (.n (oqP 0 16 6)) + 4 * 12 ≤ fsOf "__loop460" := by decide +kernel

private theorem oqFit_461 : cert "__loop461" (.n (oqP 1 64 8)) + 4 * 14 ≤ fsOf "__loop461" := by decide +kernel

private theorem oqFit_462 : cert "__loop462" (.n (oqP 0 16 6)) + 4 * 13 ≤ fsOf "__loop462" := by decide +kernel

private theorem oqFit_463 : cert "__loop463" (.n (oqP 1 64 8)) + 4 * 15 ≤ fsOf "__loop463" := by decide +kernel

private theorem oqFit_464 : cert "__loop464" (.n (oqP 1 64 8)) + 4 * 16 ≤ fsOf "__loop464" := by decide +kernel

private theorem oqFit_465 : cert "__loop465" (.n (oqP 0 16 6)) + 4 * 15 ≤ fsOf "__loop465" := by decide +kernel

private theorem oqFit_466 : cert "__loop466" (.n (oqP 1 64 8)) + 4 * 17 ≤ fsOf "__loop466" := by decide +kernel

private theorem oqFit_467 : cert "__loop467" (.n (oqP 0 16 6)) + 4 * 17 ≤ fsOf "__loop467" := by decide +kernel

private theorem oqFit_468 : cert "__loop468" (.n (oqP 0 16 6)) + 4 * 17 ≤ fsOf "__loop468" := by decide +kernel

private theorem oqFit_469 : cert "__loop469" (.n (oqP 0 16 6)) + 4 * 16 ≤ fsOf "__loop469" := by decide +kernel

private theorem oqFit_470 : cert "__loop470" (.n (oqP 1 64 8)) + 4 * 18 ≤ fsOf "__loop470" := by decide +kernel

private theorem oqFit_471 : cert "__loop471" (.n (oqP 0 16 6)) + 4 * 18 ≤ fsOf "__loop471" := by decide +kernel

private theorem oqFit_472 : cert "__loop472" (.n (oqP 0 16 6)) + 4 * 18 ≤ fsOf "__loop472" := by decide +kernel

private theorem oqFit_473 : cert "__loop473" (.n (oqP 0 16 6)) + 4 * 17 ≤ fsOf "__loop473" := by decide +kernel

private theorem oqFit_474 : cert "__loop474" (.n (oqP 1 64 8)) + 4 * 14 ≤ fsOf "__loop474" := by decide +kernel

private theorem oqFit_475 : cert "__loop475" (.n (oqP 1 64 8)) + 4 * 15 ≤ fsOf "__loop475" := by decide +kernel

private theorem oqFit_476 : cert "__loop476" (.n (oqP 1 64 8)) + 4 * 16 ≤ fsOf "__loop476" := by decide +kernel

private theorem oqFit_477 : cert "__loop477" (.n (oqP 1 64 8)) + 4 * 17 ≤ fsOf "__loop477" := by decide +kernel

private theorem oqFit_478 : cert "__loop478" (.n (oqP 1 64 8)) + 4 * 18 ≤ fsOf "__loop478" := by decide +kernel

private theorem oqFit_479 : cert "__loop479" (.n (oqP 1 64 8)) + 4 * 19 ≤ fsOf "__loop479" := by decide +kernel

private theorem oqFit_480 : cert "__loop480" (.n (oqP 0 16 6)) + 4 * 19 ≤ fsOf "__loop480" := by decide +kernel

private theorem oqFit_481 : cert "__loop481" (.n (oqP 1 64 8)) + 4 * 20 ≤ fsOf "__loop481" := by decide +kernel

private theorem oqFit_482 : cert "__loop482" (.n (oqP 0 16 6)) + 4 * 20 ≤ fsOf "__loop482" := by decide +kernel

private theorem oqFit_483 : cert "__loop483" (.n (oqP 0 16 6)) + 4 * 18 ≤ fsOf "__loop483" := by decide +kernel

theorem osOqFits_fsOf : OsOqFits fsOf cert where
  f430 := oqFit_430
  f432 := oqFit_432
  f434 := oqFit_434
  f435 := oqFit_435
  f436 := oqFit_436
  f437 := oqFit_437
  f438 := oqFit_438
  f439 := oqFit_439
  f440 := oqFit_440
  f441 := oqFit_441
  f442 := oqFit_442
  f443 := oqFit_443
  f444 := oqFit_444
  f445 := oqFit_445
  f446 := oqFit_446
  f447 := oqFit_447
  f448 := oqFit_448
  f449 := oqFit_449
  f450 := oqFit_450
  f451 := oqFit_451
  f452 := oqFit_452
  f453 := oqFit_453
  f455 := oqFit_455
  f457 := oqFit_457
  f458 := oqFit_458
  f459 := oqFit_459
  f460 := oqFit_460
  f461 := oqFit_461
  f462 := oqFit_462
  f463 := oqFit_463
  f464 := oqFit_464
  f465 := oqFit_465
  f466 := oqFit_466
  f467 := oqFit_467
  f468 := oqFit_468
  f469 := oqFit_469
  f470 := oqFit_470
  f471 := oqFit_471
  f472 := oqFit_472
  f473 := oqFit_473
  f474 := oqFit_474
  f475 := oqFit_475
  f476 := oqFit_476
  f477 := oqFit_477
  f478 := oqFit_478
  f479 := oqFit_479
  f480 := oqFit_480
  f481 := oqFit_481
  f482 := oqFit_482
  f483 := oqFit_483

theorem osOqFits : OsOqFits fs cert where
  f430 := (oqFit_430).trans (fsOf_le_fs _)
  f432 := (oqFit_432).trans (fsOf_le_fs _)
  f434 := (oqFit_434).trans (fsOf_le_fs _)
  f435 := (oqFit_435).trans (fsOf_le_fs _)
  f436 := (oqFit_436).trans (fsOf_le_fs _)
  f437 := (oqFit_437).trans (fsOf_le_fs _)
  f438 := (oqFit_438).trans (fsOf_le_fs _)
  f439 := (oqFit_439).trans (fsOf_le_fs _)
  f440 := (oqFit_440).trans (fsOf_le_fs _)
  f441 := (oqFit_441).trans (fsOf_le_fs _)
  f442 := (oqFit_442).trans (fsOf_le_fs _)
  f443 := (oqFit_443).trans (fsOf_le_fs _)
  f444 := (oqFit_444).trans (fsOf_le_fs _)
  f445 := (oqFit_445).trans (fsOf_le_fs _)
  f446 := (oqFit_446).trans (fsOf_le_fs _)
  f447 := (oqFit_447).trans (fsOf_le_fs _)
  f448 := (oqFit_448).trans (fsOf_le_fs _)
  f449 := (oqFit_449).trans (fsOf_le_fs _)
  f450 := (oqFit_450).trans (fsOf_le_fs _)
  f451 := (oqFit_451).trans (fsOf_le_fs _)
  f452 := (oqFit_452).trans (fsOf_le_fs _)
  f453 := (oqFit_453).trans (fsOf_le_fs _)
  f455 := (oqFit_455).trans (fsOf_le_fs _)
  f457 := (oqFit_457).trans (fsOf_le_fs _)
  f458 := (oqFit_458).trans (fsOf_le_fs _)
  f459 := (oqFit_459).trans (fsOf_le_fs _)
  f460 := (oqFit_460).trans (fsOf_le_fs _)
  f461 := (oqFit_461).trans (fsOf_le_fs _)
  f462 := (oqFit_462).trans (fsOf_le_fs _)
  f463 := (oqFit_463).trans (fsOf_le_fs _)
  f464 := (oqFit_464).trans (fsOf_le_fs _)
  f465 := (oqFit_465).trans (fsOf_le_fs _)
  f466 := (oqFit_466).trans (fsOf_le_fs _)
  f467 := (oqFit_467).trans (fsOf_le_fs _)
  f468 := (oqFit_468).trans (fsOf_le_fs _)
  f469 := (oqFit_469).trans (fsOf_le_fs _)
  f470 := (oqFit_470).trans (fsOf_le_fs _)
  f471 := (oqFit_471).trans (fsOf_le_fs _)
  f472 := (oqFit_472).trans (fsOf_le_fs _)
  f473 := (oqFit_473).trans (fsOf_le_fs _)
  f474 := (oqFit_474).trans (fsOf_le_fs _)
  f475 := (oqFit_475).trans (fsOf_le_fs _)
  f476 := (oqFit_476).trans (fsOf_le_fs _)
  f477 := (oqFit_477).trans (fsOf_le_fs _)
  f478 := (oqFit_478).trans (fsOf_le_fs _)
  f479 := (oqFit_479).trans (fsOf_le_fs _)
  f480 := (oqFit_480).trans (fsOf_le_fs _)
  f481 := (oqFit_481).trans (fsOf_le_fs _)
  f482 := (oqFit_482).trans (fsOf_le_fs _)
  f483 := (oqFit_483).trans (fsOf_le_fs _)

end
end LeanVM.Guest.B2C
