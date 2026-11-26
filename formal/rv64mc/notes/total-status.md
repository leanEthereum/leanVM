# Status of the total-correctness campaign

Which of the functions `main` reaches have a total contract (`HoldsT`, `Core/HoldsT.lean`), toward `main`'s `MainSpecT` (`Final/MainSpecT.lean`), as `notes/status.md` tracks the partial ones. A function is **total** here when it has a total contract over its template in `Proof/**` (a `T` module) and a `Table` instance at the image (`Rv64mc/Table/*T.lean`: `liftProg Gen.fns`, `Gen.Idx`, `Gen.Needs`, its callees' `Table` instances as arguments). Indices and instruction counts are `Rv64mc/Gen/index.tsv`'s; heights are the call graph's from the leaves (0 a leaf); the partial class is `notes/status.md`'s (A proved at the image, C a contract only, D nothing). The call graph has 229 functions (`_start` is not counted: `Final/StartT.lean` proves it from `MainSpecT`).

Open hypotheses of a `Table` theorem: `none`; `env`, the environment's two facts about the image that `alloc` reads (`NEXT`'s data reference is `env.nextAddr`, `env.heapEnd = 0x78000000`); `clmul table`, `clmul_low`'s constant in the static data (`DataRef.InData`, `FieldT.ClmulTable`); `WHIR query tables (InData)`; `N_CONSTRAINTS table (InData)` and `COUNT_COLUMNS tables (InData, CountColumnsData)`, the tables `Table::n_constraints` and `Table::count_columns` read in the static data (the second also its contents, as `Table/Layout.lean` has it); `from_elem bound (InData)` and `from_iter bound (InData)`, the words bounding `Vec<Option<E>>`'s size that `from_elem::<Option<E>>` and its `spec_from_iter_nested` (141) read in the static data; `keccak tables (InData)`, `keccak_f`'s round constants, `π` and `ρ` tables in the static data (`Table/HashT.lean`'s `KeccakTables`); `TABLE_WIDTHS table (InData)`, the widths `column_kappas` (181) reads in the static data (`[13, 13, 7, 14, 14, 92]`; its fill loop is safe only for widths of at least `2`); `lane constant (InData)`, the word `try_from_fn` (142) reads in the static data; `Vec<Form> clone bounds (InData)`, the two words (`isize::MAX / 24` and `/ 40`) `<Vec<Form> as Clone>::clone` (168) reads in the static data (only their addresses matter for safety); `KECCAK_PI`, `KECCAK_RHO`, `magic word tables (InData)` and `KECCAK_RHO as u32s (RhoAt)`, the tables `linear_transpose` (36) reads in the static data (the last also their contents, `LinearTranspose.RhoAt`, as the partial `Table` instance has it). All are environment facts about the image. (`compiler_builtins`' `memcpy` and `memmove` are proved: `Table/MemT.lean`'s `memcpyT`, which `Table/CopyUseT.lean` and `Table/AllocT.lean` compose into the instances that call it, and `Table/MemT6a.lean`'s `memmoveT`, over which `memmoveWrapT` instantiates the C wrapper (228); `Table/RuntimeT.lean`'s `memmove` keeps the hypothesis and is superseded.)

## Summary

| | functions | instructions |
| --- | --- | --- |
| total, with a `Table` instance | 136 | 6432 (30.8%) |
| of which no open hypothesis | 47 | 1537 |
| of which only environment facts open | 135 | 6430 |
| stated, not proved here | 1 | 268 |
| no total contract | 92 | 14178 |
| reachable from `main` | 229 | 20878 |

Every total function has its `Table` instance, and every `Table` theorem's axioms are pinned by `#guard_msgs` to `[propext, Classical.choice, Quot.sound]`. The counts are the table's below, recounted by `awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` (all total functions; add `&& $10 ~ /none/` for those with no open hypothesis, or match `$2 ~ /^ [0-9]+ $/` for every row).

## Obligations on functions not yet total

A total proof steps through each call with the callee's total contract, so its callee's `Pre` is a closed goal there. Where the caller is not yet total, the callee's `Pre` was checked against the image's call sites by reading the templates, and becomes a goal of the caller's proof. Some of those goals need a fact from another function's postcondition; the ones named so far:

* ~~`from_elem` (58): its post must give `VecT env m' sret 16` with `vecLen` the length asked for.~~ Met: `FromElemT.FromElemSpecT`'s postcondition is `CloneT.ClonePostT env 16` (`VecT`, `vecLen` the count `a2`, the buffer fresh unless empty). `walk` (42) passes that vector's buffer to `Vec<E>::clone` (55) at template steps 429 and 477, and `CloneSpecT`'s `BufT` follows from it by `BufT.of_le`; `walk`'s proof discharges it there.
* `spec_from_iter_nested` for `Vec<Option<E>>` (141): its `SrcT` asks the source `[a1, a2)` to be whole 16-byte elements in a window, 8-byte aligned. `verify_gkr_grand_products` (152, template step 106: `(x25, x25 + x12)`) and `keccak::verify_layer` (138, step 201: the slice at `x27 + 0x20`) pass a source that is a vector's elements or empty (152's first pass has `x20 := 0`, `x25 := 8`: the empty slice `[8, 8)`, which `SrcT`'s `b = e` case covers); not checked further here: their proofs discharge it, from that vector's `VecT` (`BufT.of_le`) where it is one, so the vector's builder's post must give `VecT`.
* ~~`Sponge::absorb` (112), `sample` (52), `absorb_nonce` (149): each calls `Sponge::duplex` (113), whose `DuplexT.PreT` asks the sponge `SpongeT` and `Owned` at the call's stack pointer.~~ Met: their total contracts (`AbsorbT`, `SampleT`, `AbsorbNonceT`) take `SpongeT` and `Owned` themselves and their proofs discharge `DuplexT.PreT` at each call. The transcript's window reaches their callers as `TranscriptReprT.TranscriptAtT`'s `InWin a 360` conjunct, with `OwnedT` for the transcript and its proof.
* `<[&[E]] as Concat<E>>::concat` (87), `<[Vec<E>] as Concat<E>>::concat` (110): each calls `Vec<E>::spec_extend` (106), whose `SpecExtendT.PreT` asks the vector `VecT` and `Owned`, its header apart from its buffer (`HdrApart`), and the source `[a1, a2)` whole 16-byte elements that, unless empty, lie in a window, apart from the stack below the stack pointer, from the heap not yet allocated (`a2 ≤ NEXT` or `heapEnd ≤ a1`) and from the vector's buffer (`SrcT`). At both callers the vector is a header in the caller's frame (110: `sp + 0`, steps 61 and 67; 87: `sp + 8`, step 53) with a buffer from `alloc` (or none), so `VecT` follows from `RawVecT.of_alloc` or `of_empty` and `HdrApart` from `HdrApart.of_stack`; the sources are the elements of the caller's input slices (110: the two vectors' buffers, `BufT.of_le` from their `VecT`; 87: the slices its own precondition must put in a window, below `NEXT` or above the heap's end), apart from the buffer `alloc` returned after them (`Fresh`). At the second and later calls `SpecExtendT.PostT`'s last conjunct (the buffer the one at entry or fresh) keeps that apartness. Not checked further here: their proofs discharge it.
* `keccak::verify_layer` (138): it calls `Vec<E>`'s `spec_from_iter_nested` (143) at template step 385 with the result's slot `sp + 0x230` and the iterator at `sp + 0x248` (the array `try_from_fn` wrote at `sp + 0xa0`, the vector at `sp + 0x70`, the range `0..1600`), all in its frame. `FromIterET.PreT` asks `SretPre` and the slot in a window, aligned; the iterator, the array and the vector's header caller's objects in windows, aligned (frame facts), and the vector at `sp + 0x70` a vector's (`VecT`), which its builder's post must give. Not checked further here: 138's proof discharges it.
* `keccak::verify_layer` (138): it calls `try_from_fn` (142) at template step 375 with `sret = sp + 0xa0` (its frame's 400-byte array) and the slice `(*(sp + 0x90), *(sp + 0x98))`, the elements of the vector `eq_kernel` (137) built at `sp + 0x88`. `TryFromFnT.PreT` asks `sret` `Owned`, in a window and 8-byte aligned (frame facts), and the slice `SliceT`, which `SliceT.of_buf` gives from that vector's `VecT` (`BufT` and `len ≤ cap`): `eq_kernel`'s total postcondition must give it.
* `build_layout` (45): it calls `GenericShunt::next` over its placements (183) at template steps 361 and 414, with `sret = sp + 0x188` and `sp + 0x1a0`, the shunt at `sp + 0x148` and `sp + 0xd8` (the second a copy of the first's five words), the closure's environment `c = sp + 0xd0` holding `sp + 0xb8`, the header of `offsets` (`stack`'s (182) first result), and the residual `r = sp + 0x138`, all in its frame. `PlacementNextT.PreT` asks those frame objects at or above the stack pointer (`StackObj`), aligned, `c` and the header below the shunt, `sret` above it, `r` apart from the cursor's word (all by the offsets); the slice `[cur, end)` (the `kappas` vector's elements, `column_kappas` (181)) whole words in a window unless empty, and `offsets` `VecT`, which `stack`'s total postcondition must give. Its `PostT` (the end, or the cursor advanced by a word below the end) is the caller's loop's measure; its `OutT` (the result, the shunt's cursor at `+ 0` and count at `+ 16`, the residual) leaves the shunt's `end` at `+ 8`, which the caller keeps through `Env.Frame` since `r` and `sret` lie apart from it (`sp + 0x138`, `sp + 0x188`, `sp + 0x1a0` against `sp + 0x150` and `sp + 0xe0`).
* `bus::table_sumcheck` (54): it calls `Table::constraints` (145) at template step 365 with `sret = sp + 0x90` (its frame) and the columns in `(a2, a3)`. `ConstraintsT.PreT` asks `sret` `SretPre`, in a window, aligned (frame facts) and the columns `SliceT` (`TryFromFnT.SliceT`: none, or in a window and aligned), which `SliceT.of_buf` gives where they are a vector's elements: 54's proof discharges it from the columns' builder.
* `verify_bus_balance` (48): it calls `<[usize; 2]>::try_map` (153) at template step 177 with the result's slot `sp + 0x2c8` and the closure at `sp + 0x3d0` (the point's buffer and length from `sp + 0xf0` and `x19`, the values' vector at `sp + 0x1e0`), in its frame. `TryMapT.PreT` asks the slot and the closure caller's objects in windows, aligned (frame facts), the point `BufT` with its length (from its vector's `VecT` by `BufT.of_le`), and the values a vector's (`VecT`, from its builder's post) and a caller's object. Not checked further here: 48's proof discharges it.
* `verify_bus_balance::{closure#2}` (158), `verify_keccak` (60): each calls `dot` (28) with a slice in its own frame: 158 passes `x12 = sp + 0x8`, `sp + 0x38`, `sp + 0x88` (template steps 47, 80, 99: the array literals of `bus.rs`'s `framework` closure), 60 passes `x10 = sp + 0x160` (template step 578). `DotT.PreT` keeps the partial `Dot.Pre`, whose `env.Live m ptr (16 * len)` asks `ptr + 16 len ≤ NEXT`, and every stack address is at or above `stackLimit > NEXT` (`Env.layout`, `NEXT ≤ heapEnd`), so at these four sites the callee's precondition is unsatisfiable and neither `dot`'s partial nor its total contract can be used. Addressed by a second total contract, `DotOwnT.specT` (`Table/DotT2.dotOwn`), with `DotT`'s postcondition and each slice `Owned` (below `NEXT` or at or above the stack pointer) where `DotT` asks `Live`; `DotT.PreT` implies its precondition, so it gives `DotT.specT` (`DotOwnT.specT.dotT`). The four sites' slices are in the callers' frames, above `dot`'s stack pointer. Discharged at 158's three sites by `FrameworkT`'s proof (through `DotSafeT.dotSafe`, `DotOwnT.specT` at the elements the slices hold); 60's proof discharges the fourth. The same reading is still owed for the `Live` of `eq_eval`'s, `poly_eval`'s, `index_mle`'s, `padding_weight`'s and `ring_psi`'s preconditions.
* `Placement::eq_above` (101), `Placement::stack_point` (131): each calls `selector_point` (102) with `sret` a slot of its frame (101: `sp + 0`; 131: `sp + 8`, both 16-byte aligned frames), which `SelectorPointT.PreT`'s three conjuncts (`Owned` at the call's stack pointer, `InWin`, 8-byte aligned) ask; read from the templates, the callers' proofs discharge it. Its `PostT` gives the partial `Post` and `ClonePostT`'s `VecT` of the result.
* `walk` (42), `verify_stacked_opening` (66), `verify_whir::<verify_stacked_opening::{closure#1}>` (74): each calls `powers` (53) with `sret` a slot of its frame (42: `sp + 0x3b0`, step 250; 66: `sp + 0`, step 70; 74: `sp + 0x240`, step 342), which `PowersT.PreT` (`Owned` at the call's stack pointer, `InWin`, 8-byte aligned) asks; read from the templates, the callers' proofs discharge it. Its `PostT` gives `Powers.Post` (the powers) and `VecT` of the result, length `a3`.
* `keccak::verify_layer` (138): it calls `linear_transpose::<E>` (36) at template step 420 with `sret = x23 + 0x30` (a field of its own result object, so `Owned`, `InWin` and alignment come from 138's precondition on its `sret`) and the slice `(*(sp + 0x238), *(sp + 0x240))`, the elements of the vector `spec_from_iter_nested` (143) built at `sp + 0x230`: `LinearTransposeT.PreT`'s `SliceT` follows from `FromIterET.PostT`'s `VecT` by `SliceT.of_buf`, and its length is the code's `assert_eq!` (another length aborts). Not checked further here: 138's proof discharges it.
* The transcript chain's callers (`Transcript::new` from `walk` (42); `next_scalar`, `grind_check`, `samples`, `next` and `Sponge::sample` from `sumcheck` (85), `read_ood` (47), `sumcheck_round_poly` (107), `ring_switch` (61), `verify_keccak` (60), `keccak::verify_layer` (138), `verify_gkr_grand_products` (152), `verify_bus_balance` (48), `sample_queries` (77), `verify_whir` (74), `verify_stacked_opening` (66), `walk` (42), and the `GenericShunt` closure 212 of `next_scalars`): their proofs must establish `TranscriptAtT` and `OwnedT` of the transcript (`walk`'s frame at `sp + 0x98`, so `InWin` by the stack window and `Owned` by `top ≤ a`), and of its proof (`main`'s, through `ProofT`: 8-aligned, `InWin` 48 bytes, the stream's buffer in a window unless empty, `NextT.StreamWin`), its proof apart from the transcript; a result's slot in a window, aligned, `Owned`, apart from the transcript and its proof (`next_scalar`, `next`); `samples`' slot likewise, apart from the sponge; `Transcript::new`'s digests in windows apart from the stack below the stack pointer (`walk`, template step 22, passes its own arguments `x11 + 0x20` and `x12`). Argued from the call sites (`sites2.py new`, `next`, `nextScalar`), not proved here.
* `verify_bus_balance` (48) calls `verify_bus_balance::{closure#2}` (158) at its two calls (lines 940 and 968 of `Gen/Tmpl/Verifier/Bus/VerifyBusBalance.lean`: `framework(gpow(0), ONE, ONE)`, `framework(final_pc, ...)`): `FrameworkT.PreT` asks the result's slot, the captures and each object a capture points to (the `weights` and `memory` headers, `memory_index`, `bytecode_index`, `bytecode_share`) at or above the callee's stack pointer, in windows and 8-byte aligned, and each vector's buffer `Live`, in a window and aligned unless empty. At both sites the slot (`sp + 0x2d8`, `sp + 0x328`), the captures (`sp + 0x258`) and the five objects (`sp + 0x1c8`, `0x210`, `0x1e0`, `0x220`, `0x230`) are 48's frame; the buffers are heap vectors (`weights`, and `memory` from `next_scalars`), `Live` by their `VecT` (`BufT.live`, the length at most the capacity). Argued from the template; 48's proof discharges it.
* ~~`MerklePath::root` (119) calls `hash_pair` (121): `HashPairT.PreT` asks the slot `InWin` and `OffStack`, the left digest `InWin`, the right one `inWindow` and `OffStack`; its proof discharges it. It calls `hash_leaf` (120) at template step 13 with the slot `sp + 0` (its frame: `InWin` by the stack window, `OffStack` as at or above the callee's stack pointer) and the leaf `Vec<K>`'s pointer and length (`x11 + 8`, `x11 + 16`): `HashLeafT.PreT` asks the words, unless there are none, `Live` and `InWin`, which the leaf's `VecT` gives (`BufT.live`, `BufT.inWin`, the length at most the capacity).~~ Met: `RootT`'s proof discharges both at their call sites (`hash_leaf` at step 13; `hash_pair` in the loop, the sibling on either side).
* `Transcript::merkle` (78) calls `MerklePath::root` (119) at template step 86 with the slot `sp + 0` (its frame: `Owned` by `top ≤ a`, `InWin` by the stack window) and the path `x11`, a `MerklePath` of a proof's phase: `RootT.PreT` asks the path owned, in a window and 8-byte aligned, and its leaf's words and siblings' digests, unless none, `Live` and in windows, which the partial `Root.Pre`'s `PathAt` (two `LiveVecAt`) and `Live` of the path give with the windows of the bump allocator's blocks. Argued from the template; 78's proof discharges it.
* `verify_whir`'s stacked-opening closure (74) calls `fold_row` (83) at lines 1141 and 1619 of `Gen/Tmpl/Verifier/Whir/VerifyWhirVerifyStackedOpeningClosure1.lean`: `FoldRowT.PreT` asks the row's header (`a0`: `sp + 0x228`, a copy of the vector at `sp + 0x1e8`, at the first; `sp + 0x1e8` at the second) at or above the callee's stack pointer and `VecT`, and the rounds (`a2 = x26`, `a3 = x22`) in a window and 8-byte aligned unless there are none. The header is 74's frame; its words are the `Vec<E>` that `ext_row` (82) or the closure 86 returned, so their total contracts must give `VecT` of it; the rounds are the buffer and length of the `Vec<FoldRound>` 74 builds with `RawVec<FoldRound>::grow_one` (line 601), `BufT` with the length at most the capacity. Argued from the template; 74's proof discharges it.
* `StackWeight::evaluate` (99) calls `RingWeight::evaluate` (100) at lines 93 (a tail call) and 163 of `Gen/Tmpl/Verifier/StackWeight/Evaluate.lean` with the ring variant's weight (`a0`) and a prefix of the point (`a1`, `a2`): `RingWeightEvaluateT.PreT` asks the weight's two `Vec<E>` headers (offsets `0`, `24`) `VecT` and the point's slice, unless empty, in a window and 8-byte aligned. The partial `RingWeightAt` (two `EVecAt`, their buffers `Live`) gives the buffers; the headers' windows and the vectors' capacities are what 99's own total precondition must add. `ring_weight`'s `PreT` follows at the tail call (`RingWeightEvaluateT.preR_of_preT`, machine-checked). Argued from the template; 99's proof discharges it.
* `Flushes::state_derived` (194), `Flushes::counted` (198): each calls `Flushes::pair` (200) with `push` and `pull` slots of its frame (194: `sp + 0`, `sp + 0x30`, template step 147; 198: `sp + 0`, `sp + 0x18`, step 107) and `self` its own `a0`. `PairT.PreT` asks `self` `FlushesT` (its two vectors of 24-byte elements `VecT`, their buffers apart (`BufsApart`: either empty, or the two blocks disjoint), its 48 bytes at or above the stack pointer and below the stack window's end, `StackObj`), 8-byte aligned, and `push` and `pull` `StackObj`, 8-byte aligned and apart from `self`'s 48 bytes (`Apart`; frame facts: they are slots of the caller's frame, `self` lies in `tables`' frame above it). `self` is a `Flushes` the `flushes_*` builders return through `sret`, which `tables` (175) puts in its frame (`sp + 0x20`, `sp + 0x118`, `sp + 0x330`), so the callers' own preconditions must carry `FlushesT` of it (a fresh `Flushes` of two empty vectors has it); `PairT.PostT` gives it back, each vector one longer, its earlier elements kept and its last one `push`'s (`pull`'s) three words at entry (`PushedT`), and each buffer the entry's (pointer and capacity) or allocated since the entry (`KeptOrFresh`); `PairT.OutT` is `self` and each vector's next slot when it has room, so what the pushed `Vec<Form>` headers point to survives the call where it lies apart from those slots. The slots lie in the buffer's spare capacity: where the buffer is fresh they lie above every block allocated before the call, and a caller that calls `pair` again on the same `Flushes` carries `KeptOrFresh` through its loop to show the pushed `Form` blocks lie apart from the later calls' slots. A `Flushes` starts with two empty vectors, so a buffer with capacity was allocated by some call's growth: a `Form` block allocated before that growth lies below the buffer, one allocated after it at or above the buffer's end (`NEXT` only grows), provided the `Form`s' builders state their blocks fresh. That is what `build_layout` (45) needs to clone each pushed `Vec<Form>` (168 through 176, below): the builders must push headers that are `BufT` and `FormsT` at the call. Not checked further here: their proofs discharge it.
* `block_members` (217): it calls `counting_sort::<usize, block_members::{closure#0}>` (219) at template step 105 with `sret = sp + 0x18` (its frame), the items the `order` vector's elements and length (`(0..members.len()).collect()`), `keys = block.len() + 1` and the members the `group_by_word` (218) result's buffer and length (`*(sp + 8)`, `x9`). `CountingSortUsizeT.PreT` asks `SretPre`, the slot in a window and aligned (frame facts), each slice `BufT` (a block allocated before, or no elements), which `BufT.of_le` gives from each vector's `VecT` (so `group_by_word`'s total postcondition and the collect's must give it), and `1 ≤ keys < 2 ^ 59` (the block a slice of `u64`s in a window). Not checked further here: 217's proof discharges it.
* `group_by_word` (218): it calls `counting_sort::<(u64, u16), group_by_word::{closure#2}>` (220) eight times (template steps 139, 153, 165, 177, ...) with `sret = sp + 0` and the items the vector at `sp + 0` before the call (its pointer and length loaded from `sp + 8`, `sp + 16`). `CountingSortPairsT.PreT` asks `SretPre`, the slot in a window and aligned (frame facts) and the items `BufT` (16-byte elements), which `BufT.of_le` gives from that vector's `VecT`: the first call's from the `filter`/`map` collect's postcondition, each later one's from the previous call's `ClonePostT`. Not checked further here: 218's proof discharges it.
* `build_layout` (45): it calls `column_kappas` (181) at template step 661 with `sret = sp + 0xa0` (its frame), the tables (`*(sp + 0x38)`, `*(sp + 0x10)`: the `tables()` vector) and the heights (`x19`, `x24`: the `table_log_heights` vector collected before). `ColumnKappasT.PreT` asks `SretPre`, the slot in a window and aligned (frame facts), and both slices `BufT`, which `BufT.of_le` gives from each vector's `VecT` (their builders' total postconditions must give it). Its `PostT` (`VecT` of the kappas, buffer fresh) is what `PlacementNextT`'s slice `[cur, end)` above and `stack`'s `kappas` argument need. Not checked further here: 45's proof discharges it.
* `<Vec<Form> as Clone>::clone` (168), `Proof/Layout/FormReprT`'s `FormsT`: its callers pass a heap source and a frame `sret`. `from_elem` for `Vec<Form>` (160, template step 34: `sret = sp + 0`, the element vector's pointer and length loaded from `elem + 8`, `elem + 16`), `Vec<BusBlock>::extend_trusted` (176, step 45: `sret = sp + 8`, a `Vec<Form>`'s pointer and length at `x22 - 8`, `x22`, the iterated element of a `Flushes`' `push` or `pull` vector of `Vec<Form>` headers) and `build_layout` (45, step 577: `sret = sp + 0xd8`, the 24-byte block `alloc(24)` returned at step 551 that `col` (179) filled, length `1`). `CloneFormsT.PreT` asks `SretPre`, the slot in a window and aligned (frame facts), the source `BufT` (`BufT.of_le` from the vector's `VecT`, or `bufT_of_alloc` at 45) and its elements `FormsT` (each `Form` a `VecT` of 40-byte terms, each term's monomial a `VecT` of words), which the `Form`s' builders' total postconditions must give: at 45, `col`'s; at 160, what built the vector cloned; at 176, the headers `Flushes::pair` (200) pushed, whose words `PairT.PostT` keeps (`PushedT`) and whose blocks the caller keeps through `PairT.OutT` where they lie apart from the two slots, which `PairT.PostT`'s `KeptOrFresh` gives for blocks allocated before a buffer that grew. Not checked further here: their proofs discharge it.
* `stack` (182): it calls `stacked_blocks` (186) at template step 33 with `sret = sp + 0` (its frame, below the saved registers at `sp + 0x38`) and the count `x12` (its `kappas` length). `StackedBlocksT.PreT` asks `SretPre`, the slot in a window and aligned: frame facts, which 182's proof discharges. Its `PostT` (`ColumnKappasT.PostT`: `VecT` of the blocks, buffer fresh unless no capacity) is what 182's loops over `blocks` (template steps 115 and 179, each index checked against the kappas' length) need.
* `stack` (182), `bus_layout` (150): each calls `stack_offsets` (174) with `sret` a slot of its frame (182: `sp + 0x18`, template step 141; 150: `sp + 0`, step 127; 32 bytes below the saved registers in both) and the sizes a vector's buffer and length (182: the buffer at `sp + 0x20` that `reserve` grew and the count pushed, `x11`, `x12`; 150: `x19`, `x18`, the block `alloc` returned or the empty vector). `StackOffsetsT.PreT` asks the slot's 32 bytes `Owned`, in a window and 8-byte aligned (frame facts) and the sizes `BufT`, which `BufT.of_le` gives from that vector's `VecT`. Its `PostT` (`ClonePostT env 8`: `VecT` of the offsets, length the sizes') is what 182's zip loop (steps 179 to 201, reading `offsets[j]` for `j` below that length) needs. Not checked further here: their proofs discharge it.

* `Form::add_scaled` (163), `subspace_roots` (126): each calls the C `memmove` (228, `Table/MemT6a.memmoveWrapT`), whose `CopyPreT true` asks, unless there are no bytes, the destination in the heap window up to the heap's end or in the stack window, the source in a window, both apart from the stack below the stack pointer, and neither range wrapping. 163 (template line 269) moves a vector's 40-byte terms one place up inside its buffer (`dst = x21 + 40`, `src = x21`, `n = 40 * (x25 - x27)`: the overlapping case, which `memmove` copies backward); 126 (template line 305) moves a buffer's words one place down (`dst = x20`, the source and length reloaded from `sp + 8` and `sp + 16`). Both ranges lie in a vector's heap block, so `BufT` with the length below the capacity gives the windows. Read from the templates, not checked further here: their proofs discharge it. 163's is discharged: `AddScaledT.move` proves `CopyPreT true` at the call from the buffer's window (`BufT` with the capacity, the length below it after the growth check); 126's is still owed.

* `verify_bus_balance` (48), `<Form as Add>::add` (193): each calls `Form::add_scaled` (163). `AddScaledT.PreT` asks `self` (`a0`) `FormT` and `Owned` at the call's stack pointer, `other`'s terms (`a1`, `a2`) a buffer's (`BufT`, the length for the capacity) with each monomial `VecT` (`TermsT`), `self`'s header apart from its buffer, and `other`'s terms apart from `self`'s header and buffer (`PairT.Apart`, each unless empty). 48 calls it at lines 725 and 740 of its template's labels: at 725 in a loop with `self = sp + 0x3d0` (the `Form` `constant` (162) returned there, in the frame) and `other` the terms of each `Form` of a vector of `Form`s (`(*(x23 - 8), *x23)`, 24 bytes apart); at 740 with `self` a `Form` in a heap array (`*(sp + 0xf8) + 8 x9 + *(sp + 0x100)`) and `other` the terms of `sp + 0x3d0`'s. 193 passes its own `self` (`a1`, a `Form` its caller owns) and `other`'s terms (`a2`, `a3`). At 725's loop each call's `PostT` keeps `self` `FormT` and its buffer the one before or fresh (`KeptOrFresh`), and `OutT` is `self`'s header and that buffer, so the other `Form`s' blocks, allocated before `constant`'s, stay apart from it and are kept. Argued from the templates; their proofs discharge it.

## Owed by contracts already total

Gaps a total contract here leaves, for a later proof that needs more than it gives:

* `fold_row` (83) and `ring_weight` (103) have safety contracts only (`FoldRowT`, `RingWeightT`). Their functional contracts (`Spec.Whir.FoldRow`, `Spec.Whir.RingWeight.spec`) are still unproved, so the partial proofs of `RingWeight::evaluate` (100) and `StackWeight::evaluate` (99) still rest on `Spec.Whir.RingWeight.spec` (`notes/status.md`); `ring_weight`'s functional contract is owed for them.
* `Transcript::samples` (132, `SamplesT.PostT`) and `verify_bus_balance::{closure#2}` (158, `FrameworkT.PostT`) give the result `VecT` and its length, not its buffer fresh (`CloneT.ClonePostT`'s clause: the length `0` or the buffer `Fresh`). A caller that needs the vector's buffer apart from its own heap objects (to write it, or to keep another object through a write to it) must first add that clause to their posts; no proved caller needs it yet.

## By function

| height | # | function | instr | partial | total | proof | `Table` theorem | open hypotheses |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 1 | `verifier_rv64::halt` | 4 | A | yes | Proof/Runtime/HaltT | RuntimeT.halt | none |
| 0 | 21 | `verifier::field::reduce` | 14 | A | yes | Proof/Field/ReduceT | FieldT.reduce | none |
| 0 | 22 | `verifier::field::clmul_low` | 72 | A | yes | Proof/Field/ClmulLowT | FieldT.clmulLow | clmul table |
| 0 | 34 | `<verifier::field::E>::sum::<core::iter::adapters::chain::Chain<allo...` | 32 | D | yes | Proof/Field/SumChainT | FieldSumT.sumChainT | none |
| 0 | 35 | `<verifier::field::E>::sum::<core::iter::adapters::copied::Copied<co...` | 19 | A | yes | Proof/Field/ESumCopiedT | FieldT.eSumCopied | none |
| 0 | 46 | `<verifier::hash::Digest>::from_halves` | 61 | A | yes | Proof/Hash/DigestFromHalvesT | DigestT.digestFromHalves | none |
| 0 | 50 | `verifier::transcript::grinding_bits` | 88 | A | yes | Proof/Transcript/GrindingBitsT | TranscriptT.grindingBits | none |
| 0 | 57 | `<verifier::layout::Layout>::committed` | 21 | A | yes | Proof/Layout/CommittedT | LayoutLeafT.committed | none |
| 0 | 67 | `<verifier::transcript::Transcript>::finish` | 13 | A | yes | Proof/Transcript/FinishT | TranscriptT.finish | none |
| 0 | 68 | `core::ptr::drop_glue::<alloc::vec::Vec<(verifier::StackWeight, veri...` | 1 | A | yes | Proof/Runtime/DropT | RuntimeT.dropVecStackClaim | none |
| 0 | 73 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::Form>> @ve...` | 1 | A | yes | Proof/Runtime/DropT | RuntimeT.dropVecForm | none |
| 0 | 105 | `verifier::field::spread` | 54 | A | yes | Proof/Field/SpreadT | FieldT.spread | none |
| 0 | 111 | `<verifier::transcript::Transcript>::next` | 19 | A | yes | Proof/Transcript/NextT; NextSafeT (second contract, over `TranscriptAtT`) | TranscriptT.next, TranscriptT3.nextSafe | none |
| 0 | 123 | `verifier::hash::xor_block` | 430 | C | yes | Proof/Hash/XorBlockT | HashT.xorBlockT | none |
| 0 | 128 | `verifier::whir::whir_queries` | 21 | A | yes | Proof/Whir/WhirQueriesT | WhirT.whirQueries | WHIR query tables (InData) |
| 0 | 184 | `verifier::layout::qkeccak_slot` | 12 | A | yes | Proof/Layout/QkeccakSlotT | LayoutLeafT.qkeccakSlot | none |
| 0 | 185 | `verifier::layout::is_output_lane` | 3 | A | yes | Proof/Layout/IsOutputLaneT | LayoutLeafT.isOutputLane | none |
| 0 | 206 | `<[core::mem::maybe_uninit::MaybeUninit<verifier::layout::Form>] as ...` | 1 | D | yes | Proof/Runtime/DropT | RuntimeT.partialDropForm | none |
| 0 | 208 | `verifier::layout::keccak_cell_lanes` | 59 | D | yes | Proof/Layout/KeccakCellLanesT | CellLanesT.keccakCellLanesT | none |
| 0 | 223 | `compiler_builtins::mem::memcpy` | 127 | C | yes | Proof/Runtime/MemcpyT | MemT.memcpyT | none |
| 0 | 224 | `compiler_builtins::mem::memset` | 38 | C | yes | Proof/Runtime/MemsetT, MemsetBytesT | RuntimeT.memsetBuiltin, VecT.memsetBuiltin | none |
| 0 | 225 | `compiler_builtins::mem::memmove` | 268 | C | yes | Proof/Runtime/MemmoveProofT (`MemmoveT.MemmoveSpecT`; parts in MoveT, MemmoveFwdT, MemmoveBwdT) | MemT6a.memmoveT | none |
| 0 | 226 | `memcmp` | 12 | A | yes | Proof/Runtime/MemcmpT | RuntimeT.memcmp | none |
| 1 | 2 | `__rustc::rust_begin_unwind` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.rustBeginUnwind | none |
| 1 | 4 | `<verifier_rv64::Input>::word` | 12 | A | yes | Proof/Runtime/InputWordT | RuntimeT.inputWord | none |
| 1 | 6 | `<verifier_rv64::Bump as core::alloc::global::GlobalAlloc>::alloc` | 17 | A | yes | Proof/Runtime/AllocT | RuntimeT.alloc | env |
| 1 | 20 | `verifier::field::clmul` | 156 | A | yes | Proof/Field/ClmulT | FieldT.clmul | clmul table |
| 1 | 69 | `core::ptr::drop_glue::<alloc::vec::Vec<alloc::vec::Vec<verifier::la...` | 21 | C | yes | Proof/Runtime/DropSliceT | VecT.dropVecVecForm | none |
| 1 | 72 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::BusBlock>>...` | 21 | C | yes | Proof/Runtime/DropSliceT | VecT.dropVecBusBlock | none |
| 1 | 104 | `<verifier::field::E>::square` | 36 | A | yes | Proof/Field/ESquareT | FieldT.eSquare | none |
| 1 | 151 | `verifier::bus::bus_grinding_bits` | 10 | A | yes | Proof/Bus/BusGrindingBitsT | BusT.busGrindingBits | none |
| 1 | 227 | `memcpy` | 2 | A | yes | Proof/Runtime/MemWrappersT | CopyUseT.memcpy | none |
| 1 | 228 | `memmove` | 2 | A | yes | Proof/Runtime/MemWrappersT | MemT6a.memmoveWrapT (RuntimeT.memmove over MemT6a.memmoveT) | none |
| 1 | 229 | `memset` | 2 | A | yes | Proof/Runtime/MemsetT, MemsetBytesT | RuntimeT.memset, VecT.memset | none |
| 2 | 3 | `<alloc::raw_vec::RawVecInner>::try_allocate_in @verifier_rv64` | 47 | C | yes | Proof/Runtime/TryAllocateInT | AllocT.tryAllocateInRv64 | env |
| 2 | 5 | `<verifier_rv64::Input>::digest` | 92 | C | no | - | - | - |
| 2 | 13 | `core::panicking::panic_fmt` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.panicFmt | none |
| 2 | 17 | `core::panicking::panic_nounwind_fmt` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.panicNounwindFmt | none |
| 2 | 19 | `verifier::field::base_mul` | 8 | A | yes | Proof/Field/BaseMulT | FieldT.baseMul | clmul table |
| 2 | 25 | `<verifier::field::E as core::ops::arith::Mul>::mul` | 61 | A | yes | Proof/Field/EMulT | FieldT.eMul | clmul table |
| 2 | 37 | `<alloc::raw_vec::RawVecInner>::try_allocate_in @verifier` | 56 | C | yes | Proof/Runtime/TryAllocateInT, TryAllocateInZT | AllocT.tryAllocateIn, VecT.tryAllocateIn | env |
| 2 | 41 | `<alloc::raw_vec::RawVecInner>::finish_grow @verifier` | 66 | A | yes | Proof/Runtime/FinishGrowT, FinishGrowAT (block aligned) | CopyUseT.finishGrow | env |
| 2 | 71 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::Table>> @v...` | 25 | C | no | - | - | - |
| 2 | 114 | `verifier::hash::keccak_f` | 391 | C | yes | Proof/Hash/KeccakFT | HashT.keccakFT | keccak tables (InData) |
| 2 | 136 | `verifier::ring_switch::frobenius_8` | 13 | A | yes | Proof/Whir/Frobenius8T | WhirT.frobenius8 | none |
| 2 | 144 | `<verifier::hash::Digest>::words` | 3 | A | yes | Proof/Hash/DigestWordsT | CopyUseT.digestWords | none |
| 3 | 9 | `alloc::raw_vec::capacity_overflow` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.capacityOverflow | none |
| 3 | 10 | `<alloc::vec::Vec<_, _>>::remove::assert_failed` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.removeAssertFailed | none |
| 3 | 11 | `<alloc::vec::Vec<_, _>>::split_off::assert_failed` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.splitOffAssertFailed | none |
| 3 | 12 | `core::panicking::assert_failed_inner` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.assertFailedInner | none |
| 3 | 15 | `core::slice::index::slice_index_fail` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.sliceIndexFail | none |
| 3 | 16 | `core::panicking::panic_bounds_check` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.panicBoundsCheck | none |
| 3 | 18 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 62 | D | no | - | - | - |
| 3 | 40 | `<alloc::raw_vec::RawVecInner>::grow_amortized @verifier` | 41 | A | yes | Proof/Runtime/GrowAmortizedT | AllocT.growAmortized | env |
| 3 | 56 | `<verifier::hash::Digest>::halves` | 19 | A | yes | Proof/Hash/DigestHalvesT | HashT.digestHalvesT | none |
| 3 | 63 | `alloc::boxed::box_new_uninit` | 11 | A | yes | Proof/Runtime/BoxNewUninitT | AllocT.boxNewUninit | env |
| 3 | 70 | `core::ptr::drop_glue::<verifier::layout::Layout> @verifier` | 23 | A | no | - | - | - |
| 3 | 108 | `verifier::multilinear::poly_eval` | 39 | A | yes | Proof/Multilinear/PolyEvalT | MultilinearT.polyEval | clmul table |
| 3 | 122 | `verifier::hash::keccak_hash` | 136 | C | yes | Proof/Hash/KeccakHashT | HashT.keccakHashT | keccak tables (InData) |
| 3 | 127 | `<verifier::field::K>::inv` | 291 | A | no | - | - | - |
| 3 | 135 | `verifier::ring_switch::ring_psi` | 46 | A | yes | Proof/Whir/RingPsiT | MultilinearT.ringPsi | clmul table |
| 3 | 154 | `<alloc::vec::Vec<verifier::bus::ColumnClaim> as core::convert::From...` | 28 | D | yes | Proof/Bus/ClaimsFromT | VecT.claimsFrom | env |
| 3 | 156 | `verifier::multilinear::index_mle` | 52 | A | yes | Proof/Multilinear/IndexMleT | MultilinearT.indexMle | clmul table |
| 3 | 164 | `verifier::multilinear::padding_weight` | 68 | A | yes | Proof/Multilinear/PaddingWeightT | MultilinearT.paddingWeight | clmul table |
| 3 | 167 | `<verifier::layout::Form>::term` | 35 | A | yes | Proof/Layout/TermT | LayoutT.term | env |
| 3 | 170 | `<verifier::field::E>::pow` | 45 | A | yes | Proof/Field/EPowT | LayoutT.ePow | clmul table |
| 3 | 213 | `<verifier::transcript::Sponge>::new` | 37 | C | yes | Proof/Transcript/SpongeNewT (safety, `SpongeT` given) | TranscriptT3.spongeNew | keccak tables (InData) |
| 4 | 8 | `alloc::raw_vec::handle_error` | 5 | A | yes | Proof/Runtime/PanicsT | RuntimeT.handleError | none |
| 4 | 14 | `core::panicking::assert_failed::<usize, usize> @core` | 3 | A | yes | Proof/Runtime/PanicsT | RuntimeT.assertFailedUsizeUsize | none |
| 4 | 26 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 30 | D | yes | Proof/Field/ESumU16T | SumT.eSumU16 | none |
| 4 | 29 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 51 | D | no | - | - | - |
| 4 | 30 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 36 | C | yes | Proof/Field/ESumEmbedBitsT | SumT.eSumEmbedBits | none |
| 4 | 31 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 35 | D | yes | Proof/Field/ESumRcBitsT | SumT.eSumRcBits | none |
| 4 | 33 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 72 | D | no | - | - | - |
| 4 | 43 | `<verifier::transcript::Transcript>::new` | 20 | A | yes | Proof/Transcript/TranscriptNewT (safety, `TranscriptAtT` given) | TranscriptT3.transcriptNew | keccak tables (InData) |
| 4 | 49 | `<verifier::layout::Table>::n_constraints` | 11 | A | yes | Proof/Layout/TableT | LayoutT.nConstraints | N_CONSTRAINTS table (InData) |
| 4 | 95 | `<verifier::field::Scaled>::mul` | 177 | A | yes | Proof/Field/ScaledMulT | MultilinearT.scaledMul | none |
| 4 | 113 | `<verifier::transcript::Sponge>::duplex` | 68 | A | yes | Proof/Transcript/DuplexT (over SpongeReprT) | TranscriptT2.duplex | keccak tables (InData) |
| 4 | 121 | `verifier::merkle::hash_pair` | 111 | C | yes | Proof/Merkle/HashPairT (safety) | MerkleT.hashPair | keccak tables (InData) |
| 4 | 142 | `core::array::try_from_fn::<core::ops::try_trait::NeverShortCircuit<...` | 110 | D | yes | Proof/Keccak/TryFromFnT | BuildT.tryFromFnLanes | clmul table; lane constant (InData) |
| 4 | 148 | `verifier::layout::jump_constraints` | 67 | D | yes | Proof/Layout/JumpConstraintsT | LayoutT2.jumpConstraints | env; clmul table |
| 4 | 157 | `verifier::layout::gpow` | 2 | A | yes | Proof/Layout/GpowT | LayoutT.gpow | clmul table |
| 4 | 162 | `verifier::layout::constant` | 14 | A | yes | Proof/Layout/ConstantT | LayoutT.constant | env |
| 4 | 177 | `<verifier::layout::Table>::count_columns` | 12 | A | yes | Proof/Layout/TableT | LayoutT.countColumns | COUNT_COLUMNS tables (InData, CountColumnsData) |
| 4 | 180 | `verifier::layout::keccak_shape` | 7 | A | yes | Proof/Layout/KeccakShapeT | LayoutT.keccakShape | none |
| 4 | 183 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 78 | D | yes | Proof/Layout/PlacementNextT | LayoutT2.placementNext | none |
| 4 | 216 | `verifier::bytecode::is_valid_encoding_of_a_leanisa_program` | 287 | A | no | - | - | - |
| 5 | 24 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 60 | D | no | - | - | - |
| 5 | 28 | `verifier::multilinear::dot` | 44 | A | yes | Proof/Multilinear/DotT (`Pre` unsatisfiable at four call sites, see Obligations); DotOwnT (second contract, slices `Owned`, gives `DotT`'s) | MultilinearT.dot, DotT2.dotOwn | clmul table |
| 5 | 32 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::op...` | 69 | D | no | - | - | - |
| 5 | 39 | `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<...` | 11 | A | yes | Proof/Runtime/DoReserveT | AllocT.doReserve | env |
| 5 | 52 | `<verifier::transcript::Sponge>::sample` | 19 | A | yes | Proof/Transcript/SampleT (safety, `SpongeT` kept) | TranscriptT3.sample | keccak tables (InData) |
| 5 | 55 | `<alloc::vec::Vec<verifier::field::E> as core::clone::Clone>::clone ...` | 49 | C | yes | Proof/Runtime/CloneT | VecT.cloneE | env |
| 5 | 62 | `<alloc::raw_vec::RawVec<verifier::bus::ColumnClaim>>::grow_one @ver...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneColumnClaim | env |
| 5 | 65 | `<alloc::raw_vec::RawVec<(verifier::StackWeight, verifier::field::E)...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneStackClaim | env |
| 5 | 81 | `<alloc::raw_vec::RawVec<verifier::whir::GluedClaim>>::grow_one @ver...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneGluedClaim | env |
| 5 | 83 | `verifier::whir::fold_row` | 104 | C | yes | Proof/Whir/FoldRowT (safety; two loops by `Total.loop`) | WhirT2.foldRow | clmul table |
| 5 | 91 | `<alloc::raw_vec::RawVec<verifier::field::E>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneE | env |
| 5 | 92 | `<alloc::raw_vec::RawVec<verifier::whir::FoldRound>>::grow_one @veri...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneFoldRound | env |
| 5 | 94 | `<verifier::multilinear::Scaler>::mul` | 17 | A | yes | Proof/Multilinear/ScalerMulT | MultilinearT.scalerMul | clmul table |
| 5 | 98 | `verifier::multilinear::eq_eval` | 40 | A | yes | Proof/Multilinear/EqEvalT | MultilinearT.eqEval | clmul table |
| 5 | 103 | `verifier::ring_switch::ring_weight` | 106 | C | yes | Proof/Whir/RingWeightT (safety; two loops by `Total.loop`) | WhirT2.ringWeight | env; clmul table |
| 5 | 112 | `<verifier::transcript::Sponge>::absorb` | 43 | A | yes | Proof/Transcript/AbsorbT (safety, `SpongeT` kept) | TranscriptT3.absorb | keccak tables (InData) |
| 5 | 118 | `<alloc::raw_vec::RawVec<verifier::field::K>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneK | env |
| 5 | 125 | `<alloc::raw_vec::RawVec<u64>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneU64 | env |
| 5 | 129 | `<alloc::raw_vec::RawVec<usize>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneUsize | env |
| 5 | 145 | `<verifier::layout::Table>::constraints` | 11 | D | yes | Proof/Layout/ConstraintsT | LayoutT2.constraints | env; clmul table |
| 5 | 146 | `<verifier::layout::Form>::evaluate` | 16 | D | no | - | - | - |
| 5 | 147 | `<alloc::raw_vec::RawVec<(alloc::vec::Vec<verifier::field::E>, alloc...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneVecEVecE | env |
| 5 | 153 | `<[usize; 2]>::try_map::<core::ops::try_trait::NeverShortCircuit<ver...` | 114 | D | yes | Proof/Bus/TryMapT | BuildT.tryMapClaims | env |
| 5 | 155 | `verifier::bus::verify_bus_balance::{closure#0} @verifier` | 52 | D | yes | Proof/Bus/ColumnClaimT | VecT.columnClaim | env |
| 5 | 165 | `<alloc::vec::Vec<usize> as core::clone::Clone>::clone @verifier` | 49 | D | yes | Proof/Runtime/CloneT | VecT.cloneUsize | env |
| 5 | 166 | `<alloc::raw_vec::RawVec<(alloc::vec::Vec<usize>, verifier::field::E...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneVecUsizeE | env |
| 5 | 174 | `verifier::multilinear::stack_offsets` | 122 | C | yes | Proof/Multilinear/StackOffsetsT (safety only) | MultilinearT5a.stackOffsets | env |
| 5 | 179 | `verifier::layout::col` | 34 | A | yes | Proof/Layout/ColT | LayoutT.col | env; clmul table |
| 5 | 192 | `verifier::layout::prod` | 43 | A | yes | Proof/Layout/ProdT | LayoutT.prod | env; clmul table |
| 5 | 201 | `<alloc::raw_vec::RawVec<alloc::vec::Vec<verifier::layout::Form>>>::...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneVecForm | env |
| 5 | 219 | `verifier::bytecode::counting_sort::<usize, verifier::bytecode::bloc...` | 130 | C | yes | Proof/Bytecode/CountingSortUsizeT (safety only) | BytecodeT.countingSortUsize | env |
| 5 | 220 | `verifier::bytecode::counting_sort::<(u64, u16), verifier::bytecode:...` | 105 | D | yes | Proof/Bytecode/CountingSortPairsT | BytecodeT.countingSortPairs | env |
| 5 | 221 | `<alloc::raw_vec::RawVec<(verifier::field::K, alloc::vec::Vec<u16>)>...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneKVecU16 | env |
| 5 | 222 | `<alloc::raw_vec::RawVec<u16>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneU16 | env |
| 6 | 23 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 67 | D | no | - | - | - |
| 6 | 27 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 79 | D | no | - | - | - |
| 6 | 38 | `<alloc::vec::Vec<verifier::field::E>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveE | env |
| 6 | 53 | `verifier::field::powers` | 87 | C | yes | Proof/Field/PowersT | FieldT2.powers | env; clmul table |
| 6 | 75 | `verifier::whir::derive_config` | 150 | C | no | - | - | - |
| 6 | 77 | `verifier::whir::sample_queries` | 139 | C | no | - | - | - |
| 6 | 79 | `<verifier::whir::Subspace>::at` | 96 | C | no | - | - | - |
| 6 | 100 | `<verifier::ring_switch::RingWeight>::evaluate` | 10 | A | yes | Proof/Whir/RingWeightEvaluateT (safety; the partial proof rests on `ring_weight`'s partial spec) | WhirT2.ringWeightEvaluate | env; clmul table |
| 6 | 109 | `<verifier::transcript::Transcript>::next_scalar` | 34 | A | yes | Proof/Transcript/NextScalarT (safety, `TranscriptAtT` kept) | TranscriptT3.nextScalar | keccak tables (InData) |
| 6 | 115 | `<alloc::vec::Vec<core::option::Option<verifier::field::E>>>::reserv...` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveOptionE | env |
| 6 | 117 | `<alloc::vec::Vec<verifier::field::K>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveK | env |
| 6 | 124 | `<alloc::vec::Vec<u8>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveU8 | env |
| 6 | 149 | `<verifier::transcript::Sponge>::absorb_nonce` | 21 | A | yes | Proof/Transcript/AbsorbNonceT (safety, `SpongeT` kept) | TranscriptT3.absorbNonce | keccak tables (InData) |
| 6 | 158 | `verifier::bus::verify_bus_balance::{closure#2} @verifier` | 145 | D | yes | Proof/Bus/FrameworkT (safety, the result `VecT` of three elements; `dot` through `DotSafeT.dotSafe`) | BusT2.framework | env; clmul table |
| 6 | 163 | `<verifier::layout::Form>::add_scaled` | 177 | D | yes | Proof/Layout/AddScaledT (safety only; `FormT` of `self` and its buffer `KeptOrFresh`; the search in AddScaledSearchT) | FormT6a.addScaled | env; clmul table |
| 6 | 168 | `<alloc::vec::Vec<verifier::layout::Form> as core::clone::Clone>::cl...` | 142 | D | yes | Proof/Layout/CloneFormsT (safety only; `FormsT` of the result) | FormT5a.cloneForms | env, Vec<Form> clone bounds (InData) |
| 6 | 169 | `<alloc::vec::Vec<verifier::layout::Form>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveForm | env |
| 6 | 173 | `<alloc::vec::Vec<usize>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveUsize | env |
| 6 | 178 | `<alloc::vec::Vec<verifier::layout::BusBlock>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveBusBlock | env |
| 6 | 200 | `<verifier::layout::Flushes>::pair` | 54 | D | yes | Proof/Layout/PairT | FlushesT.pair | env |
| 6 | 218 | `verifier::bytecode::group_by_word` | 193 | D | no | - | - | - |
| 7 | 36 | `verifier::keccak::linear_transpose::<verifier::field::E> @verifier` | 196 | A | yes | Proof/Keccak/LinearTransposeT | KeccakT.linearTranspose | env; KECCAK_PI, KECCAK_RHO, magic word tables (InData), KECCAK_RHO as u32s (RhoAt) |
| 7 | 51 | `<verifier::transcript::Transcript>::grind_check` | 42 | A | yes | Proof/Transcript/GrindCheckT (safety, `TranscriptAtT` kept) | TranscriptT3.grindCheck | keccak tables (InData) |
| 7 | 58 | `<verifier::field::E as alloc::vec::spec_from_elem::SpecFromElem>::f...` | 72 | C | yes | Proof/Runtime/FromElemT | VecT2.fromElemE | env |
| 7 | 82 | `verifier::whir::ext_row` | 57 | C | no | - | - | - |
| 7 | 84 | `<core::option::Option<verifier::field::E> as alloc::vec::spec_from_...` | 89 | D | yes | Proof/Runtime/FromElemOptT | VecT2.fromElemOptionE | env; from_elem bound (InData) |
| 7 | 102 | `verifier::multilinear::selector_point` | 67 | A | yes | Proof/Multilinear/SelectorPointT | MultilinearT2.selectorPoint | env |
| 7 | 106 | `<alloc::vec::Vec<verifier::field::E> as alloc::vec::spec_extend::Sp...` | 34 | D | yes | Proof/Runtime/SpecExtendT | BuildT.specExtendE | env |
| 7 | 116 | `verifier::whir::novel_basis` | 108 | C | no | - | - | - |
| 7 | 120 | `verifier::merkle::hash_leaf` | 53 | C | yes | Proof/Merkle/HashLeafT (safety) | MerkleT.hashLeaf | env; keccak tables (InData) |
| 7 | 126 | `verifier::whir::subspace_roots` | 165 | C | no | - | - | - |
| 7 | 132 | `<verifier::transcript::Transcript>::samples` | 68 | A | yes | Proof/Transcript/SamplesT (safety, `VecT` of `count` elements, `SpongeT` kept) | TranscriptT3.samples | env; keccak tables (InData) |
| 7 | 133 | `verifier::ring_switch::ring_coefficients` | 116 | C | no | - | - | - |
| 7 | 134 | `verifier::ring_switch::ring_target` | 109 | C | no | - | - | - |
| 7 | 140 | `verifier::keccak::instance_weights` | 132 | C | no | - | - | - |
| 7 | 141 | `<alloc::vec::Vec<core::option::Option<verifier::field::E>> as alloc...` | 74 | D | yes | Proof/Runtime/FromIterOptT | VecT2.fromIterOptionE | env; from_iter bound (InData) |
| 7 | 143 | `<alloc::vec::Vec<verifier::field::E> as alloc::vec::spec_from_iter_...` | 106 | D | yes | Proof/Runtime/FromIterET | BuildT.fromIterE | env; clmul table |
| 7 | 150 | `verifier::bus::bus_layout` | 147 | D | no | - | - | - |
| 7 | 159 | `<verifier::layout::Form as alloc::vec::spec_from_elem::SpecFromElem...` | 188 | D | no | - | - | - |
| 7 | 160 | `<alloc::vec::Vec<verifier::layout::Form> as alloc::vec::spec_from_e...` | 75 | D | no | - | - | - |
| 7 | 176 | `<alloc::vec::Vec<verifier::layout::BusBlock>>::extend_trusted::<cor...` | 73 | D | no | - | - | - |
| 7 | 181 | `verifier::layout::column_kappas` | 159 | D | yes | Proof/Layout/ColumnKappasT (safety only) | LayoutT5a.columnKappas | env, TABLE_WIDTHS table (InData) |
| 7 | 186 | `verifier::layout::stacked_blocks` | 90 | D | yes | Proof/Layout/StackedBlocksT (safety only) | LayoutT5a.stackedBlocks | env |
| 7 | 193 | `<verifier::layout::Form as core::ops::arith::Add>::add` | 25 | D | no | - | - | - |
| 7 | 194 | `<verifier::layout::Flushes>::state_derived` | 82 | D | no | - | - | - |
| 7 | 202 | `<alloc::vec::Vec<verifier::layout::Form> as alloc::vec::spec_extend...` | 127 | D | no | - | - | - |
| 7 | 212 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 35 | C | no | - | - | - |
| 7 | 217 | `verifier::bytecode::block_members` | 123 | D | no | - | - | - |
| 8 | 44 | `<verifier::transcript::Transcript>::next_scalars` | 97 | C | no | - | - | - |
| 8 | 47 | `verifier::read_ood` | 50 | C | no | - | - | - |
| 8 | 61 | `verifier::ring_switch::ring_switch` | 77 | C | no | - | - | - |
| 8 | 76 | `<verifier::whir::Subspace>::new` | 80 | C | no | - | - | - |
| 8 | 80 | `verifier::whir::novel_eval` | 35 | C | no | - | - | - |
| 8 | 86 | `verifier::whir::verify_whir::<verifier::verify_stacked_opening::{cl...` | 79 | D | no | - | - | - |
| 8 | 87 | `<[&[verifier::field::E]] as alloc::slice::Concat<verifier::field::E...` | 70 | D | no | - | - | - |
| 8 | 96 | `<verifier::field::Scaled>::new` | 222 | C | no | - | - | - |
| 8 | 101 | `<verifier::multilinear::Placement>::eq_above` | 34 | C | no | - | - | - |
| 8 | 110 | `<[alloc::vec::Vec<verifier::field::E>] as alloc::slice::Concat<veri...` | 66 | D | no | - | - | - |
| 8 | 119 | `<verifier::merkle::MerklePath>::root` | 144 | C | yes | Proof/Merkle/RootT (safety; loop by `Total.loop`) | MerkleT.root | env; keccak tables (InData) |
| 8 | 182 | `verifier::layout::stack` | 126 | D | no | - | - | - |
| 8 | 199 | `<[&[verifier::layout::Form]] as alloc::slice::Concat<verifier::layo...` | 80 | D | no | - | - | - |
| 8 | 203 | `<verifier::layout::Form>::sum::<core::iter::adapters::chain::Chain<...` | 146 | D | no | - | - | - |
| 8 | 204 | `<verifier::layout::Form>::sum::<[verifier::layout::Form; 3]> @verifier` | 63 | D | no | - | - | - |
| 8 | 205 | `<verifier::layout::Flushes>::state_step` | 23 | D | no | - | - | - |
| 8 | 207 | `<verifier::layout::Form>::sum::<core::iter::adapters::map::Map<core...` | 84 | D | no | - | - | - |
| 8 | 211 | `<verifier::layout::Form>::sum::<core::iter::adapters::flatten::Flat...` | 70 | D | no | - | - | - |
| 8 | 215 | `<verifier::bytecode::Bytecode>::new` | 147 | C | no | - | - | - |
| 9 | 78 | `<verifier::transcript::Transcript>::merkle` | 148 | C | no | - | - | - |
| 9 | 93 | `<verifier::multilinear::Scaler>::new` | 9 | A | no | - | - | - |
| 9 | 97 | `verifier::whir::induced_weight` | 115 | C | no | - | - | - |
| 9 | 99 | `<verifier::StackWeight>::evaluate` | 83 | A | no | - | - | - |
| 9 | 107 | `<verifier::transcript::Transcript>::sumcheck_round_poly` | 159 | C | no | - | - | - |
| 9 | 131 | `<verifier::multilinear::Placement>::stack_point` | 32 | C | no | - | - | - |
| 9 | 171 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 62 | D | no | - | - | - |
| 9 | 198 | `<verifier::layout::Flushes>::counted` | 65 | D | no | - | - | - |
| 9 | 209 | `verifier::layout::layout_limb` | 117 | D | no | - | - | - |
| 10 | 59 | `verifier::multilinear::multilinear_eval::<verifier::field::K> @veri...` | 110 | C | no | - | - | - |
| 10 | 85 | `verifier::transcript::sumcheck` | 116 | C | no | - | - | - |
| 10 | 88 | `verifier::verify_stacked_opening::{closure#1} @verifier` | 83 | C | no | - | - | - |
| 10 | 89 | `<verifier::whir::GluedWeight>::evaluate` | 31 | A | no | - | - | - |
| 10 | 90 | `verifier::multilinear::multilinear_eval::<verifier::field::E> @veri...` | 146 | C | no | - | - | - |
| 10 | 130 | `<verifier::bus::ColumnClaim>::on_stack` | 45 | A | no | - | - | - |
| 10 | 137 | `verifier::multilinear::eq_kernel` | 102 | C | no | - | - | - |
| 10 | 195 | `<verifier::layout::Flushes>::bytecode` | 117 | D | no | - | - | - |
| 10 | 197 | `<verifier::layout::Flushes>::memory` | 41 | D | no | - | - | - |
| 10 | 210 | `<verifier::layout::Flushes>::memory_if` | 68 | D | no | - | - | - |
| 11 | 54 | `verifier::bus::table_sumcheck` | 517 | C | no | - | - | - |
| 11 | 64 | `<alloc::vec::Vec<(verifier::StackWeight, verifier::field::E)>>::ext...` | 55 | D | no | - | - | - |
| 11 | 74 | `verifier::whir::verify_whir::<verifier::verify_stacked_opening::{cl...` | 928 | C | no | - | - | - |
| 11 | 138 | `verifier::keccak::verify_layer` | 481 | D | no | - | - | - |
| 11 | 139 | `verifier::keccak::open` | 208 | D | no | - | - | - |
| 11 | 161 | `<verifier::bytecode::Bytecode>::evaluate` | 72 | C | no | - | - | - |
| 11 | 172 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 39 | D | no | - | - | - |
| 11 | 187 | `verifier::layout::flushes_keccak` | 370 | D | no | - | - | - |
| 11 | 196 | `<verifier::layout::Flushes>::memory_cols` | 85 | D | no | - | - | - |
| 12 | 60 | `verifier::keccak::verify_keccak` | 626 | D | no | - | - | - |
| 12 | 66 | `verifier::verify_stacked_opening` | 101 | C | no | - | - | - |
| 12 | 152 | `verifier::bus::verify_gkr_grand_products` | 462 | D | no | - | - | - |
| 12 | 188 | `verifier::layout::flushes_arith` | 261 | D | no | - | - | - |
| 12 | 189 | `verifier::layout::flushes_set` | 111 | D | no | - | - | - |
| 12 | 190 | `verifier::layout::flushes_deref` | 223 | D | no | - | - | - |
| 12 | 191 | `verifier::layout::flushes_jump` | 199 | D | no | - | - | - |
| 13 | 48 | `verifier::bus::verify_bus_balance` | 949 | C | no | - | - | - |
| 13 | 175 | `verifier::layout::tables` | 222 | D | no | - | - | - |
| 14 | 45 | `verifier::layout::build_layout` | 509 | C | no | - | - | - |
| 15 | 42 | `verifier::walk` | 762 | C | no | - | - | - |
| 16 | 214 | `verifier::verify_execution` | 2 | A | no | - | - | - |
| 17 | 7 | `main` | 287 | C | no | - | - | - |
