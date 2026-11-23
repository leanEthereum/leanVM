module

public import NativeVm.Input

/-!
# The wire decoder's working-area layout
-/

@[expose] public section

namespace NativeVm.Wire


/-- Phases left. -/
def wPN : Nat := 0
/-- The current phase's address in the decoded area. -/
def wPB : Nat := 1
/-- The nodes of the current level. -/
def wN : Nat := 2
/-- The parents found so far. -/
def wK : Nat := 3
/-- The current entry of the level's sibling table. -/
def wSP : Nat := 4
/-- The node of the current query at the current level. -/
def wX : Nat := 5
/-- The two digests a parent hashes. -/
def wH : Nat := 8
/-- The queries. -/
def wQ : Nat := 16
/-- The distinct positions, ascending. -/
def wP : Nat := wQ + 256
/-- Whether each node of the level has its sibling among the level's nodes. -/
def wFL : Nat := wP + 256
/-- The level's nodes: the node and its digest, five words each. -/
def wNode : Nat := wFL + 256
/-- The next level's nodes. -/
def wPar : Nat := wNode + 1280
/-- Each level's node count. -/
def wSibN : Nat := wPar + 1280
/-- Each level's nodes and their siblings, five words each, `1280` words a level. -/
def wSib : Nat := wSibN + 32
/-- The leaves at the distinct positions, `wireMaxLeafWords` words each. -/
def wLeaf : Nat := wSib + 32 * 1280
/-- The working area's words. -/
def workWords : Nat := wLeaf + 256 * 64

end NativeVm.Wire
