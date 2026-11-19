import NativeVm.Test.Ring

/-- Ring switching's kernels against the model (`NativeVm.Test.Ring`); exit code 1 on a mismatch. -/
def main : IO UInt32 := do
  let r := NativeVm.Test.RingTest.all
  IO.println s!"ring kernels: {r}"
  return if r.all id then 0 else 1
