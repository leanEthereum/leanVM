import LeanVM.Guest.B1.Link.Suffixes
import LeanVM.Guest.B1.Link.Ends
import LeanVM.Guest.B1.Link.IndexSide
import LeanVM.Guest.B1.Link.IndexMle
import LeanVM.Guest.B1.Link.TablePoint
import LeanVM.Guest.B1.Link.Terminal
import LeanVM.Guest.B1.Link.RoundsMain
import LeanVM.Guest.B1.Link.RowSide
import LeanVM.Guest.B1.Link.SqueezePacked
import LeanVM.Guest.B1.Link.PackedMessage
import LeanVM.Guest.B1.Link.ChunkD
import LeanVM.Guest.B1.Link.TableSize
import LeanVM.Guest.B1.Link.RoundRun
import LeanVM.Guest.B1.Link.RoundsRun

/-!
# B1 for the link's callees, pinned

The core IR of each function the link section of `verify_sub` calls implies its B1 meaning, and the
packed moves and sum-check rounds run as the Statement's, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.Link.one_plus_suffixes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.one_plus_suffixes_sound

/-- info: 'LeanVM.Guest.B1.Link.state_ends_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.state_ends_sound

/-- info: 'LeanVM.Guest.B1.Link.index_side_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.index_side_sound

/-- info: 'LeanVM.Guest.B1.Link.index_mle_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.index_mle_holds

/-- info: 'LeanVM.Guest.B1.Link.table_point_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.table_point_sound

/-- info: 'LeanVM.Guest.B1.Link.link_terminal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_terminal_sound

/-- info: 'LeanVM.Guest.B1.Link.link_rounds_L1_L0_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_rounds_L1_L0_sound

/-- info: 'LeanVM.Guest.B1.Link.link_rounds_L6_L0_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_rounds_L6_L0_sound

/-- info: 'LeanVM.Guest.B1.Link.link_rounds_L7_L0_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_rounds_L7_L0_sound

/-- info: 'LeanVM.Guest.B1.Link.link_rounds_L8_L1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_rounds_L8_L1_sound

/-- info: 'LeanVM.Guest.B1.Link.link_rounds_L9_L1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_rounds_L9_L1_sound

/-- info: 'LeanVM.Guest.B1.Link.link_rounds_L10_L1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_rounds_L10_L1_sound

/-- info: 'LeanVM.Guest.B1.Link.link_row_side_L6_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_row_side_L6_sound

/-- info: 'LeanVM.Guest.B1.Link.link_row_side_L7_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_row_side_L7_sound

/-- info: 'LeanVM.Guest.B1.Link.link_row_side_L8_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_row_side_L8_sound

/-- info: 'LeanVM.Guest.B1.Link.link_row_side_L9_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.link_row_side_L9_sound

/-- info: 'LeanVM.Guest.B1.Link.squeeze_packed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.squeeze_packed_sound

/-- info: 'LeanVM.Guest.B1.Link.runsTo_samplePacked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.runsTo_samplePacked

/-- info: 'LeanVM.Guest.B1.Link.packed_message_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.packed_message_sound

/-- info: 'LeanVM.Guest.B1.Link.runsTo_readPacked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.runsTo_readPacked

/-- info: 'LeanVM.Guest.B1.Link.chunk_d_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.chunk_d_sound

/-- info: 'LeanVM.Guest.B1.Link.table_size_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.table_size_sound

/-- info: 'LeanVM.Guest.B1.Link.runsTo_sumcheck_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.runsTo_sumcheck_round

/-- info: 'LeanVM.Guest.B1.Link.chain_runsTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.chain_runsTo
