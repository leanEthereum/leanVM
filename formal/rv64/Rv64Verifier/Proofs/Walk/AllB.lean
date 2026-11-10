import Rv64Verifier.Proofs.Walk.Tl12
import Rv64Verifier.Proofs.Walk.Lay14
import Rv64Verifier.Proofs.Walk.R13
import Rv64Verifier.Proofs.Walk.ExtB10
import Rv64Verifier.Proofs.Walk.R16B

/-!
# `walk` from `0x80003038` (R11, `kappas`): what is proved so far

`r11` (`AtR11` to `0x800031dc`, `kappas` built: `Lat11 .. 6`), from `r11head` (`AtR11` to the loop's
header, `Kap11 .. 0`) and `kapTable` (`kapCheck`, `kapTmpB` or `kapTmpA` (`vec![h; w]`),
`kapReserve`, `kapCopy`). `r12` (`0x800031dc` to `stack_offsets`' call, `AtR13`: `blocks` and
`block_kappas` built), from `blkFilter`, `bkAlloc`, `bkMap`. `r13` (`AtR13` to `AtR14` at
`0x800033f0`: `stack_offsets`, `offsets`, `stack_log`, the placements). `r14` (`AtR14` at
`0x800033f0`, the placements built, to `AtR15` at `0x800034c0`: the `Layout` at `sp + 576`,
`build_layout`'s value `layoutOf A k`, `stack_log` checked, `walk` running `bodyRest`; or `Err` 26).
`r1516` (`AtR15` to `AtR17` at `0x800035f0`), from `r15` (`next_scalars(2)` and the root's bytes, to
`verify_bus_balance`'s call, `AtBus`) and `r16` (the call, under `BusBalanceSpec BcOk bev` and
`BcWalk BcOk bev`: `busPre`, `busArgs`). The axioms: Lean's three.
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

/-- info: 'Rv64Verifier.Proofs.Walk.r11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r11

/-- info: 'Rv64Verifier.Proofs.Walk.r12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r12

/-- info: 'Rv64Verifier.Proofs.Walk.r14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r14

/-- info: 'Rv64Verifier.Proofs.Walk.r13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r13

/-- info: 'Rv64Verifier.Proofs.Walk.r15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r15

/-- info: 'Rv64Verifier.Proofs.Walk.busPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.busPre

/-- info: 'Rv64Verifier.Proofs.Walk.busArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.busArgs

/-- info: 'Rv64Verifier.Proofs.Walk.r16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r16

/-- info: 'Rv64Verifier.Proofs.Walk.r1516' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r1516
