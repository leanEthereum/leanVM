import Rv64Verifier.Proofs.Walk.Loop10

/-!
# `walk` from `0x80002e40`: what is proved

`r10` runs the bus blocks' loop from `AtR10` to `0x80003038` (`AtR11`), given `extend_trusted`'s
contract (`ExtendBlocksSpec`, stated in `Blocks10.lean`, not proved), `Vec<BusBlock>::reserve`'s,
`alloc`'s, `col`'s and `Vec<Form>::clone`'s. The axioms: Lean's three.
-/

/-- info: 'Rv64Verifier.Proofs.Walk.r10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.r10
