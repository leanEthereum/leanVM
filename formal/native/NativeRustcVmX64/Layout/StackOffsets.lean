module

public import NativeRustcVmX64.Layout.StackOffsets.End
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.InsertionSortOfStackOffsets.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names

/-!
# `stack_offsets` on x86-64

**`stackOffsets_spec`**: rustc's `stack_offsets(sizes, offsets)`, placed anywhere in the program,
meets `StackOffsetsPre`/`StackOffsetsPost` given `memset`'s, `insertion_sort`'s and
`bit_length`'s contracts. `b0` returns `None` (`b1`) when `offsets` is shorter than `sizes`
(`entry`). Else the prologue `b2` pushes six registers below the 1264-byte order array and zeroes
it (`memset`); `b3` to `b12` write `0, …, n - 1` into it (`fill`), `b13` sorts it
(`insertion_sort`: the model's `ord`, `sorted`), the main loop places the blocks along the order
(`P`, `loop`) or fails (the blocks not fitting a `u64`, `fail_end`), `b23` takes the total's
`bit_length(total - 1)` (`log2Ceil`) and the epilogue returns it with the offsets (`finish`).
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeRustcVmX64.Vm.StackOffsets

public section

variable [Host] {k : Nat}

/-- **`stack_offsets` meets its contract.** -/
theorem stackOffsets_spec (hp : Placed code k)
    (hmemset : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hsort : Spec (label NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.entryLabel) InsertionSortPre InsertionSortPost)
    (hbl : Spec (label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) :
    Spec (label NativeRustcVmX64.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost := by
  intro m0 hpre
  refine Eventually.bind (entry hp hmemset hpre) fun s h ↦ ?_
  rcases h with h | h
  · exact .done _ h
  · have hcap := h.2.1
    refine Eventually.bind (fill hp hpre.1 hpre.2.1 h) fun s1 h1 ↦ ?_
    refine Eventually.bind (sorted hp hsort hpre h1) fun s2 h2 ↦ ?_
    refine Eventually.bind (loop hp hpre hcap h2.1 h2.2) fun s3 h3 ↦ ?_
    rcases h3 with h3 | h3
    · exact fail_end hp hpre h3
    · exact finish hp hbl hpre hcap h3

end

end NativeRustcVmX64.Layout.StackOffsets
