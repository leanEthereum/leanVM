/-
  LeanVM.Guest.B1.VerifySub.MuteSet

  The functions `verify_sub`'s and `verify_tables`' callees reach that pop no witness stream: every callee of both but `certify_placement`, `verify_tables` and `open_stacked`, and everything they call.
-/

module

public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The callees of `verify_sub` and `verify_tables` popping nothing, closed under calls, in the program's order. -/
def vsMuteSet : List String := [
  "g_power_of_word", "assert_small_g_power", "eq_prefix_chain", "rs_eq_run", "sumcheck_round4", "opening_tail_round",
  "verify_bus_gkr", "shared_selector_tables", "verify_keccak", "ring_switch_target", "ring_switch_weight",
  "selector_tables", "check_opening_terminal", "eq_prefix_run__L0", "eq_prefix_run__L1", "eq_prefix_run__L2",
  "eq_prefix_run__L3", "eq_prefix_run__L4", "eq_prefix_run__L5", "eq_prefix_run__L6", "eq_prefix_run__L7",
  "eq_prefix_run__L8", "eq_prefix_run__L9", "eq_prefix_run__L10", "eq_prefix_run__L11", "eq_prefix_run__L12",
  "eq_prefix_run__L13", "eq_prefix_run__L14", "eq_prefix_run__L15", "eq_prefix_run__L16", "eq_prefix_run__L17",
  "eq_prefix_run__L18", "eq_prefix_run__L19", "eq_prefix_run__L20", "eq_prefix_run__L21", "eq_prefix_run__L22",
  "eq_prefix_run__L23", "eq_prefix_run__L24", "eq_prefix_run__L25", "eq_prefix_run__L26", "eq_prefix_run__L27",
  "eq_prefix_run__L28", "eq_prefix_run__L29", "eq_prefix_run__L30", "eq_prefix_run__L31", "eq_prefix_run__L32",
  "eq_prefix_run__L33", "eq_prefix_run__L34", "eq_prefix_run__L35", "eq_prefix_run__L36", "eq_prefix_run__L37",
  "eq_prefix_run__L38", "eq_prefix_run__L39", "eq_prefix_run__L40", name% «rs_eq_run_loop0», "rs_eq_rows__L0",
  "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6",
  "rs_eq_rows__L7", name% «verify_bus_gkr_loop0», name% «verify_bus_gkr_loop1», name% «shared_selector_tables_loop0»,
  "sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2", "sel_partial_nibble__L3",
  "padding_weight__L0", "padding_weight__L1", "padding_weight__L2", "padding_weight__L3", "padding_weight__L4",
  "padding_weight__L5", "padding_weight__L6", "padding_weight__L7", "padding_weight__L8", "padding_weight__L9",
  "padding_weight__L10", "padding_weight__L11", "padding_weight__L12", "padding_weight__L13", "padding_weight__L14",
  "padding_weight__L15", "padding_weight__L16", "padding_weight__L17", "padding_weight__L18", "padding_weight__L19",
  "padding_weight__L20", "padding_weight__L21", "padding_weight__L22", "padding_weight__L23", "padding_weight__L24",
  "padding_weight__L25", "padding_weight__L26", "padding_weight__L27", "padding_weight__L28", "padding_weight__L29",
  "padding_weight__L30", "plus_one_run__L0", "plus_one_run__L1", "plus_one_run__L2", "plus_one_run__L3",
  "plus_one_run__L4", "plus_one_run__L5", "plus_one_run__L6", "plus_one_run__L7", "plus_one_run__L8",
  "plus_one_run__L9", "plus_one_run__L10", "plus_one_run__L11", "plus_one_run__L12", "plus_one_run__L13",
  "plus_one_run__L14", "plus_one_run__L15", "plus_one_run__L16", "plus_one_run__L17", "plus_one_run__L18",
  "plus_one_run__L19", "plus_one_run__L20", "plus_one_run__L21", "plus_one_run__L22", "plus_one_run__L23",
  "plus_one_run__L24", "plus_one_run__L25", "plus_one_run__L26", "plus_one_run__L27", "plus_one_run__L28",
  "plus_one_run__L29", "plus_one_run__L30", "plus_one_run__L31", "plus_one_run__L32", "plus_one_run__L33",
  "block_selector__L0", "block_selector__L1", "block_selector__L2", "block_selector__L3", "block_selector__L4",
  "block_selector__L5", "block_selector__L6", "block_selector__L7", "block_selector__L8", "block_selector__L9",
  "block_selector__L10", "block_selector__L11", "block_selector__L12", "block_selector__L13", "block_selector__L14",
  "block_selector__L15", "block_selector__L16", "block_selector__L17", "block_selector__L18", "block_selector__L19",
  "block_selector__L20", "block_selector__L21", "block_selector__L22", "block_selector__L23", "block_selector__L24",
  "block_selector__L25", "block_selector__L26", "block_selector__L27", "block_selector__L28", "block_selector__L29",
  "block_selector__L30", "block_selector__L31", "block_selector__L32", "block_selector__L33", "index_mle__L0",
  "index_mle__L1", "index_mle__L2", "index_mle__L3", "index_mle__L4", "index_mle__L5", "index_mle__L6",
  "index_mle__L7", "index_mle__L8", "index_mle__L9", "index_mle__L10", "index_mle__L11", "index_mle__L12",
  "index_mle__L13", "index_mle__L14", "index_mle__L15", "index_mle__L16", "index_mle__L17", "index_mle__L18",
  "index_mle__L19", "index_mle__L20", "index_mle__L21", "index_mle__L22", "index_mle__L23", "index_mle__L24",
  "index_mle__L25", "index_mle__L26", "index_mle__L27", "index_mle__L28", "index_mle__L29", "index_mle__L30",
  "index_mle__L31", "index_mle__L32", "index_mle__L33", "block_selector_tab__L0", "block_selector_tab__L1",
  "block_selector_tab__L2", "block_selector_tab__L3", "block_selector_tab__L4", "block_selector_tab__L5",
  "block_selector_tab__L6", "block_selector_tab__L7", "block_selector_tab__L8", "block_selector_tab__L9",
  "block_selector_tab__L10", "block_selector_tab__L11", "block_selector_tab__L12", "block_selector_tab__L13",
  "block_selector_tab__L14", "block_selector_tab__L15", "block_selector_tab__L16", "block_selector_tab__L17",
  "block_selector_tab__L18", "block_selector_tab__L19", "block_selector_tab__L20", "block_selector_tab__L21",
  "block_selector_tab__L22", "block_selector_tab__L23", "block_selector_tab__L24", "block_selector_tab__L25",
  "block_selector_tab__L26", "block_selector_tab__L27", "block_selector_tab__L28", "block_selector_tab__L29",
  "block_selector_tab__L30", "block_selector_tab__L31", "block_selector_tab__L32", "block_selector_tab__L33",
  name% «verify_tables_loop0», name% «verify_keccak_loop0», "keccak_layer__L1", "keccak_layer__L0",
  "keccak_plain_rounds__L6_L0", name% «verify_keccak_loop1», "keccak_plain_rounds__L4_L1",
  name% «verify_keccak_loop2», name% «ring_switch_target_loop0», name% «check_opening_terminal_loop0»,
  "column_selector__L0", "column_selector__L1", "column_selector__L2", "column_selector__L3", "column_selector__L4",
  "column_selector__L5", "column_selector__L6", "column_selector__L7", "column_selector__L8", "column_selector__L9",
  "column_selector__L10", "column_selector__L11", "column_selector__L12", "column_selector__L13",
  "column_selector__L14", "column_selector__L15", "column_selector__L16", "column_selector__L17",
  "column_selector__L18", "column_selector__L19", "column_selector__L20", "column_selector__L21",
  "column_selector__L22", "column_selector__L23", "column_selector__L24", "column_selector__L25",
  "column_selector__L26", "column_selector__L27", "column_selector__L28", "column_selector__L29",
  "column_selector__L30", "log2_ceil_in_the_exponent__L0_L34", "log2_ceil_in_the_exponent__L16_L34",
  "grind_check__L15", "squeeze_point_from__L20", "squeeze_point_from__L21", "squeeze_point_from__L22",
  "squeeze_point_from__L23", "squeeze_point_from__L24", "squeeze_point_from__L25", "squeeze_point_from__L26",
  "squeeze_point_from__L27", "squeeze_point_from__L28", "squeeze_point_from__L29", "squeeze_point_from__L30",
  "opening_message__L1_L1", "bus_grind_check__L0", "bus_grind_check__L1", "bus_grind_check__L2",
  "bus_grind_check__L3", "bus_grind_check__L4", "bus_grind_check__L5", "bus_grind_check__L6", "bus_grind_check__L7",
  "bus_grind_check__L8", "bus_grind_check__L9", "bus_grind_check__L10", "bus_grind_check__L11",
  "bus_grind_check__L12", "bus_grind_check__L13", "grind_check__L13", "rs_eq_rows__L8",
  name% «verify_bus_gkr_loop0_loop0», "gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6",
  "gkr_rounds__L1", "grind_check__L3", name% «keccak_layer__L1_loop0», name% «keccak_layer__L1_loop1»,
  name% «keccak_layer__L0_loop0», name% «keccak_layer__L0_loop1», "grind_check__L17", "grind_check__L18",
  "grind_check__L19", "grind_check__L20", "grind_check__L21", "grind_check__L22", "grind_check__L23",
  "grind_check__L24", "grind_check__L25", "grind_check__L26", "grind_check__L27", "grind_check__L28",
  "grind_check__L29", "grind_check__L30"]

end
end LeanVM.Guest.B1.VerifySub
