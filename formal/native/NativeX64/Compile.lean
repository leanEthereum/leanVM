module

public import NativeX64.Compile.Code
public import NativeX64.Compile.Correct

/-!
# The compiler from statements to Kraken's x86-64

`Compile.program body onFail` is a program's machine code (`NativeX64.Compile.Code`), and
`Compile.program_correct` (`NativeX64.Compile.Correct`) proves that, in any layout, its run from
the entry reaches the body's `ret` as `Exec` says, or the failure handler's `ret` when the body
fails.
-/
