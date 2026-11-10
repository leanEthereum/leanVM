import Rv64Verifier.Proofs.Walk.TmpA11
import Rv64Verifier.Proofs.Walk.ExtB10

/-!
# `walk` from `0x80003038` (R11, `kappas`): what is proved so far

`r11head` (`AtR11` to the loop's header, `Kap11 .. 0`), `kapCheck` (a table's opcode, height and
width), `kapTmpB` and `kapTmpA` (`vec![h; w]` for `h = 0` and `h ≠ 0`, to `Tmp11` at `0x800031a4`),
`fillLoop`, `tryCall`. The axioms: Lean's three.
-/

/-- info: 'Rv64Verifier.Proofs.Walk.r11head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r11head

/-- info: 'Rv64Verifier.Proofs.Walk.kapCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.kapCheck

/-- info: 'Rv64Verifier.Proofs.Walk.kapTmpA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.kapTmpA

/-- info: 'Rv64Verifier.Proofs.Walk.kapTmpB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.kapTmpB

/-- info: 'Rv64Verifier.Proofs.Walk.extendBlocks_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.extendBlocks_proved
