import LeanVM.Guest.Complete.Claims.Field
import LeanVM.Guest.Complete.Claims.MonoCore
import LeanVM.Guest.Complete.Claims.MonoAt
import LeanVM.Guest.Complete.Claims.Kids

/-!
# `main`'s two claim lists, placed, pinned

Loop helpers with heap hints, the frame loops, `list_split`, `claim_list_last__L{r}`,
`claim_list_tail`, `claim_list_chain` and `claim_list_digest` placed, the claim lists' pops, and the
fields `clx`, `csp` of `MainCalleesOpenAt`. Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.loopFH_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loopFH_callAtA

/-- info: 'LeanVM.Guest.Complete.grpL_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.grpL_callAtA

/-- info: 'LeanVM.Guest.Complete.list_split_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.list_split_callAtA

/-- info: 'LeanVM.Guest.Complete.clLast_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.clLast_callAtA

/-- info: 'LeanVM.Guest.Complete.tail_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.tail_callAtA

/-- info: 'LeanVM.Guest.Complete.chain_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.chain_callAtA

/-- info: 'LeanVM.Guest.Complete.digest_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.digest_callAtA

/-- info: 'LeanVM.Guest.B1.Digest.cl_valid_pops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.cl_valid_pops

/-- info: 'LeanVM.Guest.Complete.claimList_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.claimList_atEvery

/-- info: 'LeanVM.Guest.Complete.mainClx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainClx

/-- info: 'LeanVM.Guest.Complete.mainCsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainCsp

/-- info: 'LeanVM.Guest.Complete.mainClaimLists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainClaimLists

/-- info: 'LeanVM.Guest.B1.Digest.any_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.any_core

/-- info: 'LeanVM.Guest.B1.Digest.ccl_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.ccl_core

/-- info: 'LeanVM.Guest.B1.Digest.recMem_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.recMem_group

/-- info: 'LeanVM.Guest.B1.Digest.mono_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.mono_core

/-- info: 'LeanVM.Guest.B1.Digest.mlc_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.mlc_core

/-- info: 'LeanVM.Guest.B1.Digest.mRec_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.mRec_group

/-- info: 'LeanVM.Guest.B1.Digest.anyBody_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.anyBody_core

/-- info: 'LeanVM.Guest.Complete.anyL_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.anyL_callAtA

/-- info: 'LeanVM.Guest.Complete.ccl_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.ccl_callAtA

/-- info: 'LeanVM.Guest.Complete.any_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.any_callAtA

/-- info: 'LeanVM.Guest.B1.Digest.monoBody_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.monoBody_core

/-- info: 'LeanVM.Guest.B1.Digest.monoRec_of_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Digest.monoRec_of_reads

/-- info: 'LeanVM.Guest.Complete.monoL_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.monoL_callAtA

/-- info: 'LeanVM.Guest.Complete.mlc_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mlc_callAtA

/-- info: 'LeanVM.Guest.Complete.mono_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mono_callAtA

/-- info: 'LeanVM.Guest.Complete.chEnd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.chEnd_le

/-- info: 'LeanVM.Guest.Complete.clEnd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.clEnd_le

/-- info: 'LeanVM.Guest.Complete.anyEnd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.anyEnd_le

/-- info: 'LeanVM.Guest.Complete.monoEnd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.monoEnd_le

/-- info: 'LeanVM.Guest.Complete.mainClaimListsE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainClaimListsE

/-- info: 'LeanVM.Guest.Complete.loopFHP_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loopFHP_callAtA

/-- info: 'LeanVM.Guest.Complete.ccd0_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.ccd0_callAtA

/-- info: 'LeanVM.Guest.Complete.ccdNe_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.ccdNe_callAtA

/-- info: 'LeanVM.Guest.Complete.kidList_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidList_atEvery

/-- info: 'LeanVM.Guest.Complete.mainKidx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainKidx

/-- info: 'LeanVM.Guest.Complete.mainKids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainKids

/-- info: 'LeanVM.Guest.Complete.kidsListsOpenE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidsListsOpenE

/-- info: 'LeanVM.Guest.Complete.kidsListsOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidsListsOpen
