module

public import NativeVm.Field.KInv
public import NativeVm.Field.EPow
public import NativeVm.Field.Powers
public import NativeVm.Field.Mle

/-!
# The field kernels

The leanVM verifier's arithmetic on the shared machine, each kernel a `Stmt` with a `WP`
specification against `Statement.Field`'s `K` and `E` and `Statement.LeanVmVerifier`'s functions.
A `K` element is one word, its lane (`K.ofLane`); an `E` element two, limb `0` then limb `1`
(`eOf`), in registers `A = (r9, r10)` and `B = (r11, r12)`, and in memory at consecutive words
(`EAt`, `EArr`). No kernel reads or writes `rdi` or `rsp`.

* `NativeVm.Field.K`: `kmul` (`rax := rax · rbx`), `ksq` (`rax := rax²`);
* `NativeVm.Field.KInv`: `ksqn` (`rax := rax^(2^rdx)`), `sqMul`, `kinv` (`rax := rax⁻¹`);
* `NativeVm.Field.E`: `eadd`, `emul`, `esq`, `escale` (`A := A · ofK r11`);
* `NativeVm.Field.EPow`: `esqn` (`A := A^(2^rdx)`, the Frobenius), `epow` (`A := A^r13`);
* `NativeVm.Field.Arrays`: `edot`, `eeqEval`, `epolyEval` over lists at `r13`, `r14`;
* `NativeVm.Field.Fold`: `efold` (`foldPairs`), `NativeVm.Field.Mle`: `emle` (`multilinearEval`),
  `NativeVm.Field.Powers`: `epowers` (`powers`).
-/
