module

public import Qrom.QromSearch

/-! # Generic results in the quantum random-oracle model

`Qrom.qrom_search_le`: a program making at most `t` calls to the quantum random oracle and
outputting at most `k` inputs outputs one whose value is good with probability at most
`λ (√6 t + 2 k)²`, where every input has a fraction at most `λ` of good values. The build fails if
its axiom footprint grows beyond Lean's three standard axioms. -/

/-- info: 'Qrom.qrom_search_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qrom.qrom_search_le
