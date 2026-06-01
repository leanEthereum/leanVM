# zkDSL Language Reference

The zkDSL is a Python-syntax language that compiles to leanVM bytecode (4 basic instructions and 2 special ones (precompile): poseidon / extension operations). For the underlying VM, and proving system, see [`minimal_zkVM.pdf`](../../minimal_zkVM.pdf).

Source files use the `.py` extension. They are **not** currently runnable as
real Python, but the syntax is kept Python-compatible so that one day they
could be (TODO).

## Dev experience

To recycle python tooling/linting on zkDSL files (which import [`snark_lib`](snark_lib.py)), point your editor at the compiler crate. With VSCode (for instance in `leanVM/.vscode/settings.json`):

```json
{
    "python.analysis.extraPaths": [
        "./crates/lean_compiler"
    ]
}
```

## Entrypoint

Programs are organized as one or more `.py` files. The toplevel of each file is a
sequence of:

1. `from <module> import *` statements (optional)
2. Top-level constant declarations (optional)
3. Function definitions

Execution starts at `def main(): ...`.

```python
from snark_lib import *        # only there to keep the Python linter happy; stripped by the zkDSL compiler
from utils import *        # import other file

X = 42                          # constants must come before functions
# array constants (or arbitrary dimmensions: 1D, 2D, etc)
ARR_1D = [1, 2, 3]
ARR_2D = [[1, 2, 3], [], [10, 4]]
ARR_3D = [[[1, 2, 3], [7, 8], [9]], [], [[10], [10, 4]]]

def main():                     # required entry point
    ...

def helper():                   # other functions
    ...
```

## Imports

```python
from utils import *               # imports utils.py (resolved from the import root)
from dir.subdir.file import *     # nested module
from ..module import *            # parent-directory import (relative to current file)
```

Imports are wildcard-only (`import *`). Each module is loaded once even if imported
multiple times; circular imports are rejected. Constants with the same
name in two imported files cause a compile-time error.

## Constants

Constants live at the top of the file, outside any function.

```python
X = 42
ARR = [1, 2, 3]
NESTED = [[1, 2], [3]]
```

### Nested (multi-dimensional, possibly ragged) constant arrays

```python
MATRIX = [[1, 2, 3], [4, 5], [6, 7, 8, 9]]
DEEP   = [[[1, 2], [3]], [[4, 5, 6]]]
```

Indexed access uses chained subscripts at compile time:

```python
x = MATRIX[0][2]       # 3
y = DEEP[1][0][1]      # 5
```

`len()` works at every depth, including on a row addressed by a constant index:

```python
len(MATRIX)            # 3
len(MATRIX[0])         # 3
len(DEEP[0][0])        # 2
```

When `len()` is applied with a variable index (`len(ARR[i])`), `i` must be a
compile-time constant. `: Const` parameters always qualify (see [Functions]
below), as do iterator variables of an `unroll` loop (see [For loops] below).

Example: iterating a ragged 2D table:

```python
MATRIX = [[1, 2, 3], [4, 5], [6, 7, 8, 9]]

def main():
    total: Mut = 0
    for row in unroll(0, len(MATRIX)):
        for col in unroll(0, len(MATRIX[row])):
            total = total + MATRIX[row][col]
    assert total == 45
    return
```

### Compile-time placeholders

The Rust compiler API (`CompilationFlags::replacements`) substitutes values into the source before
parsing. By convention a placeholder is named `<NAME>_PLACEHOLDER` and used as a constant value:

```python
V = V_PLACEHOLDER          # replaced by the configured value
```

Only whole identifiers are matched, so a placeholder is never replaced inside a larger name like
`xV_PLACEHOLDER` or `V_PLACEHOLDER_2`.

## Functions

```python
def add(a, b):
    return a + b

def swap(a, b):
    return b, a

def main():
    x, y = swap(1, 2)
    return
```

Every function must contain at least one `return`. The compiler infers the number
of returned values from the `return` statements; all `return`s in a function must
agree. A function that "returns nothing" uses a bare `return`.


### Parameter types

| Syntax     | Meaning                              |
| ---------- | ------------------------------------ |
| `x`        | normal (immutable) runtime parameter |
| `x: Const` | compile-time parameter               |

```python
def repeat(n: Const):            # Const enables unroll(0, n)
    sum: Mut = 0
    for i in unroll(0, n):
        sum = sum + i
    return sum

def double(x):                   # parameter is immutable; shadow with a local
    y: Mut = x
    y = y * 2
    return y
```

### Inline functions

`@inline` expands a function at every call site instead of generating a JUMP 
instruction to another part of the bytecode. Useful for performance (calling a function costs a few cycles).

```python
@inline
def square(x):
    return x * x
```

Constraints on inline functions (compiler limitations): Exactly one `return`, placed as the last statement of the body, not nested inside `if`, a loop, or `match`. Inlining rewrites the `return` into a plain assignment in place, so early or conditional returns cannot be expressed.

## Variables

| Declaration   | Mutability | Notes                                          |
| ------------- | ---------- | ---------------------------------------------- |
| `x = 10`      | immutable  | cannot be reassigned                           |
| `x: Mut = 10` | mutable    | reassignable                                   |
| `x: Imm`      | immutable  | forward declaration; assign exactly once later |
| `x: Mut`      | mutable    | forward declaration; reassignable later        |

### Forward declarations

Use `x: Imm` when you want an immutable binding but the value comes from a
branch:

```python
result: Imm
if cond == 1:
    result = 10
else:
    result = 20
# result is now immutable
```

Use `x: Mut` when you want to keep mutating the variable after the branch:

```python
x: Mut
if cond == 1:
    x = 10
else:
    x = 20
x = x + 1   # OK: x is mutable
```

### Mutability inside tuple assignments

To make a single component of a tuple-return mutable, forward-declare it:

```python
b: Mut
a, b, c = some_function()
b = b + 1            # OK
# a = 5              # ERROR: a is immutable
```

## Memory and arrays

```python
buffer = Array(16)            # allocate 16 field elements
buffer[0] = 42
buffer[0] = 42                # Valid
# buffer[0] = 41              # ERROR: conflicting write (read only memory)
buffer[5] = 34
x = buffer[5]                 # x = 34

matrix = Array(64)            # 2D via manual indexing
matrix[row * 8 + col] = value

ptr2 = buffer + 5             # pointer arithmetic
ptr2[0] = 100                 # same as buffer[5] = 100
```

`Array(n)` returns a pointer to a freshly allocated block of `n` field
elements. `n` may be a compile-time constant (more efficient, analogy: allocated on the stack) or a runtime
value (less efficient, analogy: allocated on the heap). Memory is **write-once**: a cell may be
written more than once only if all writes store the same value.

## Control flow

### `if` / `elif` / `else`

```python
if x == 0:
    y = 1
elif x == 1:
    y = 2
else:
    y = 3
```

Comparison operators on conditions: `==`, `!=`, `<`, `<=`. There is **no** `>`
or `>=` (flip the operands to get the same effect).

### `match`

Patterns must be a set of integers of the form [n, n+1, n + 2, ...]:

```python
match value:
    case 5:
        result = 500
        do_stuf()
    case 6:
        result = 600
        do_other_stuf()
    case 7:
        result = 700
        ...
```

The matched value must lie inside the listed range; out-of-range values produce
undefined behaviour: **It's the responsability of the program to ensure this** (no checks added by the compiler). Letting a prover-controlled value escape the range in a `range` is a critical vulnerability.

### `match_range`

`match_range` enables to automatically generate a `match` with repeated arms.

```python
result = match_range(n, range(1, 5), lambda i: compute(i))
```

is expanded by the compiler to:

```python
result: Imm
match n:
    case 1: result = compute(1)
    case 2: result = compute(2)
    case 3: result = compute(3)
    case 4: result = compute(4)
```

It's possible to chain several `(range, lambda)` pairs, provided the ranges are
**contiguous** (the end of one is the start of the next):

```python
result = match_range(n,
    range(0, 1), lambda i: special_case(),
    range(1, 8), lambda i: normal_case(i))
```

Multiple return values are supported via tuple unpacking. Like any binding, a
`match_range` result is immutable; declare the target `: Mut` if you assign it
more than once in a scope (assigning it once per `unroll` iteration stays
immutable, each iteration is a fresh scope):

```python
a: Mut
a, b = match_range(n, range(0, 4), lambda i: two_values(i))
a += 1                                                   # second assign in this scope ⇒ a is : Mut

for k in unroll(0, n):
    c = match_range(k, range(0, 4), lambda i: one_value(i))  # immutable: a fresh binding each iteration
```

Idiomatic use: enables to dispatch a runtime value to a const-parameter function.

```python
def helper_const(n: Const):
    return n * n

def compute(value):
    assert value < 10
    return match_range(value, range(0, 10), lambda i: helper_const(i))
```
Similar to `match`, range validity of the matched value is the responsibility of the program, not the compiler. Letting a prover-controlled value escape the range in a `match_range` is a critical vulnerability.

### For loops

Three loop forms, all written `for i in <range_kind>(start, end):`. The
iterator visits `start, start + 1, ..., end - 1`.

Restrictions shared by all three forms:

- No `break` or `continue` (not in the grammar).

**Empty / reversed bounds (`start >= end`).** The two loop kinds behave differently:

- `unroll(start, end)` with `start >= end` expands to **nothing** (zero iterations).
- `range(start, end)` / `parallel_range(start, end)` count up until the counter *equals*
  `end`, so `start > end` wraps around modulo `p` and may run up to ≈ `p` steps.
  A runtime `range` must always have `start <= end`.

#### `range(a, b)`: runtime loop

The general-purpose runtime loop. `a` and `b` may be runtime values. The
compiler lowers the loop to a recursive function.

```python
sum: Mut = 0
for i in range(1, 11):
    sum += i
assert sum == 55
```

Mutable variables carried across iterations are supported transparently.

*Under the hood: the compiler inserts a buffer array, stores the per-iteration value into it, and reads the final value back after the loop.*

Restrictions: No `return` inside the body

*Under the hood: because the loop is lowered to a recursive function.*

#### `unroll(a, b)`: compile-time unrolling

The loop is expanded at compile time: the body is duplicated once per iteration
with `i` substituted by its concrete value. Both `a` and `b` must be
compile-time constants.

```python
for i in unroll(0, 4):
    buffer[i] = i * i
```

#### `parallel_range(a, b)` — parallel runtime loop

**`parallel_range` compiles to exactly the same bytecode as `range`.** It
differs only in the runner's scheduling policy: iterations are dispatched
concurrently across worker threads rather than evaluated in sequence. The only advantage is faster witness generation.
Iteration `a` is executed first, in isolation, to determine the per-iteration
memory footprint; the remaining iterations are then evaluated in parallel
without inter-iteration synchronization.

```python
for i in parallel_range(0, n):
    process(i, inputs[i], outputs[i])
```

Because there is no synchronization, the loop body must be
iteration-independent:

- No `Mut` variables carried across iterations (each iteration writes only to
  its own call frame and to addresses disjoint from every other iteration).
- Identical memory footprint per iteration.
- Identical hint consumption per iteration (witness hints, XMSS-specific
  decomposition hints, Merkle hints, etc.).

These constraints are **not** checked at compile time. Violating them produces
silently wrong proofs.

### Statements without effect are rejected

Every line must either be a declaration, an assignment, a control-flow form, an
assertion, a `return`, or a side-effecting call (`hint_witness`, precompile,
`print`, or a function call). A bare expression like `x + 1` on its own line is
a compile error.

## Expressions

### Arithmetic

`+`, `-`, `*`, `/` are field operations and work at runtime, modulo `p = 2^31 - 2^24 + 1` (koalabear prime).

**Division by zero is undefined behaviour.**

`%` (modulo) and `**` (exponentiation) are **compile-time only** — both operands
must be constants known at compile time.

### Compound assignment

```python
x: Mut = 10
x += 5    # x = x + 5
x -= 3    # x = x - 3
x *= 2    # x = x * 2
x /= 4    # x = x / 4
```

Only a single target is allowed on the LHS of a compound assignment.

### Compile-time built-ins

These functions are evaluated at compile time only — their arguments must be
constants:

```python
log2_ceil(x)              # ceil(log2(x))
next_multiple_of(x, n)    # smallest multiple of n that is >= x
div_ceil(a, b)            # (a + b - 1) // b
div_floor(a, b)           # a // b
saturating_sub(a, b)      # max(0, a - b)
len(array)                # length of a constant array (any depth)
```


### `_` (the discard target)

Inside a tuple-unpacking LHS, `_` discards the value at that position. The
compiler rewrites each `_` to a fresh anonymous name so they don't collide.

```python
_, b = swap(a, b)             # only keep b
_ = compute()                  # discard a single return value
```

## Assertions

The zkDSL provides two assertion forms with very different semantics:

| Form           | Enforced by                             | Use for                                                             |
| -------------- | --------------------------------------- | ------------------------------------------------------------------- |
| `assert`       | The proof system                        | Invariants the verifier must check                                  |
| `debug_assert` | The prover only (at witness generation) | Sanity checks; preconditions the verifier does not need to re-check |

### `assert`: proof-enforced constraint

```python
assert x == y
assert x != y
assert x <  y
assert x <= y
```

The four supported comparison operators are `==`, `!=`, `<`, `<=` (no `>` or
`>=`; flip the operands).


### Range checks: `assert a < b` and `assert a <= b`

- When the inequality is strict: `assert a < b`, **The program must ensure `b <= 2^16`.**
- When the inequality is non-strict: `assert a <= b`, **The program must ensure `b < 2^16`.**

The compiler does not check this (`b` may be a runtime value). Violating the bound is a critical soundness vulnerability.

*Under the hood: the compiler proves `a < b` by emitting two DEREF instructions,
which check that `a` and `b - 1 - a` are both valid memory addresses. An
address is valid iff it is `< M`, where `M` is the memory size. To stay sound
for every admissible memory size, the construction relies on the smallest one,
`M_min = 2^16` (= `2^MIN_LOG_MEMORY_SIZE`), giving the bound `b <= 2^16`.*

#### Explicit panic

`assert False` is the unconditional failure form. It compiles to a Panic and
accepts an optional message:

```python
assert False
assert False, "human-readable message"
```

### `debug_assert`: sanity checks at witness generation

```python
debug_assert(x < y)
```

`debug_assert` accepts the same four comparison operators. It is evaluated by
the prover at trace-generation time and does **not** emit any constraint, so
the verifier never re-checks it. Use it for invariants the prover is expected
to maintain but that the verifier can take for granted — typically the
range-validity preconditions of `match` / `match_range` dispatches.

## Comments

```python
# single-line comment

"""
block comment
"""
```

## Line continuation

As in Python:

- **Implicit** continuation inside `(...)` or `[...]`.
- **Explicit** continuation with `\` at end of line.

```python
result = function_call(arg1,
                       arg2,
                       arg3)   # implicit continuation inside parens
y = 1 + 2 + \
    3 + 4                      # explicit continuation with backslash
```

## Hints (prover-supplied data)

A hint is data the *prover* writes into memory without adding any constraint —
the program must still constrain the written value if it wants the verifier to
believe anything about it. There are two flavours of hint:

### `hint_witness("name", ptr)`

Writes the next buffer queued under the label `name` into memory starting at
`ptr`. The guest must allocate `ptr` large enough to hold the data; no length
is checked at runtime.

The buffer comes from the host (Rust side), not from the guest. Before
running the program, the host fills `ExecutionWitness::hints` with one queue
of buffers per label; each `hint_witness("name", ptr)` call pops the next
buffer from `hints["name"]`.

`ExecutionWitness` lives in `crates/lean_vm/src/execution/runner.rs`:

```rust
pub struct ExecutionWitness {
    ...
    pub hints: HashMap<String, Vec<Vec<F>>>,
    ...
}
```

Each map key is a label; the value is the **ordered list of buffers** the
guest will consume under that label. The N-th `hint_witness("name", ptr)` call
the guest executes pops the N-th `Vec<F>` from `hints["name"]` and writes it
at `ptr`.

For example, the guest below issues three `hint_witness` calls — two against
`"input_data"` and one against `"other_stuff"`:

```python
data_buf_1 = Array(64)
hint_witness("input_data", data_buf_1)
n = data_buf_1[0]

data_buf_2 = Array(64)
hint_witness("input_data", data_buf_2)
m = data_buf_2[3]
assert n == m + 8

data_buf_3 = Array(10)
hint_witness("other_stuff", data_buf_3)
...
```

The matching Rust side must register two buffers under `"input_data"` (in
the order the guest will read them) and one under `"other_stuff"`:

```rust
let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
hints.insert(
    "input_data".to_string(),
    vec![
        first_input_buffer,   // consumed by the first  hint_witness("input_data", ...)
        second_input_buffer,  // consumed by the second hint_witness("input_data", ...)
    ],
);
hints.insert("other_stuff".to_string(), vec![other_buffer]);

let witness = ExecutionWitness { hints, ..Default::default() };
```

A missing label, or running out of buffers under a label, is a runner-side
panic: each call requires its corresponding entry to exist.

### Custom hints

Custom hints are a fixed set of built-in calls the prover uses to compute
values that would be expensive to derive in-circuit — bit
decompositions, comparisons, integer division, etc. Each is invoked like an
ordinary function and writes its result into a caller-supplied memory
location.

Like every hint, **the result is unconstrained**: the verifier checks
nothing about the hinted value. The guest program must add its own
constraints binding the hinted bits / quotient / remainder / boolean to the
original input — otherwise a malicious prover can substitute any value. The
typical pattern is "hint, then assert the relationship":

```python
# hint the bits...
bits = Array(8)
hint_decompose_bits(value, bits, 8)
# ...then constrain them to actually equal `value`
acc: Mut = 0
for i in unroll(0, 8):
    assert bits[i] * (bits[i] - 1) == 0    # boolean
    acc = acc * 2 + bits[i]
assert acc == value
```

The full list:

| Hint                              | Arguments                                                          | Effect                                                                                                                                  |
| --------------------------------- | ------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------- |
| `hint_decompose_bits`             | `(value, ptr, n_bits)`                                             | Writes `n_bits` big-endian 0/1 field elements at `ptr` (MSB at `ptr[0]`). Requires `n_bits <= 31`.                                      |
| `hint_decompose_bits_merkle_whir` | `(decomposed_ptr, value, chunk_size)`                              | Writes `24 / chunk_size` little-endian `chunk_size`-bit chunks of `value` at `decomposed_ptr` (`chunk_size` must divide 24).            |
| `hint_decompose_bits_xmss`        | `(decomposed_ptr, to_decompose_ptr, num_to_decompose, chunk_size)` | For each of `num_to_decompose` values at `to_decompose_ptr[..]`, writes its `24 / chunk_size` little-endian chunks at `decomposed_ptr`. |
| `hint_less_than`                  | `(a, b, result_ptr)`                                               | `1` at `result_ptr` if `a < b` (canonical integer compare), else `0`.                                                                   |
| `hint_log2_ceil`                  | `(n, result_ptr)`                                                  | `ceil(log2(n))` at `result_ptr`.                                                                                                        |
| `hint_div_floor`                  | `(a, b, q_ptr, r_ptr)`                                             | `floor(a / b)` at `q_ptr`, `a mod b` at `r_ptr` (requires `b != 0`).                                                                    |

## Precompiles

Precompiles are special instructions in the leanVM ISA, alongside the four
basic ones (ADD, MUL, DEREF, JUMP). The zkDSL exposes them as built-in
functions. There are two families: Poseidon hashing and extension-field
operations.

### Poseidon16 family

The variants are as follows:

- **compress vs. permute** — `compress` applies the feed-forward addition
  (`Poseidon(L || R) + L`); `permute` is the raw permutation, no feed-forward.
- **output length** — the suffix is the fraction of the 16-cell permutation
  kept: no suffix = full 16 (permute only), `_half` = 8, `_quarter` = 4.
  Cells beyond the kept prefix are unconstrained.
- **hardcoded-left** — `_hardcoded_left` reads the first 4 cells of the left
  input from a compile-time address instead of from `m[L..L+4]` (the last 4
  cells still come from `m[L..L+4]`); composes with both compress and permute.

Common arguments: `L`, `R` are 8-cell input buffers; `O` is the output
buffer; `off` (where present) is a compile-time address.

| Function                                                | Cells written to `O` | Notes                                     |
| ------------------------------------------------------- | -------------------- | ----------------------------------------- |
| `poseidon16_compress_half(L, R, O)`                     | `O[0..8]`            | `Poseidon(L \|\| R) + L`                  |
| `poseidon16_compress_quarter(L, R, O)`                     | `O[0..4]`            | `O[4..8]` is unconstrained                |
| `poseidon16_compress_half_hardcoded_left(L, R, O, off)` | `O[0..8]`            | left = `m[off..off+4] \|\| m[L..L+4]`     |
| `poseidon16_compress_quarter_hardcoded_left(L, R, O, off)` | `O[0..4]`            | quarter-output + hardcoded-left composition |
| `poseidon16_permute(L, R, O)`                           | `O[0..16]`           | raw Poseidon permutation, no feed-forward |
| `poseidon16_permute_half(L, R, O)`                      | `O[0..8]`            | permutation, low 8 only (high 8 discarded) |
| `poseidon16_permute_half_hardcoded_left(L, R, O, off)`  | `O[0..8]`            | permute (low 8) + hardcoded-left          |

### Extension-field operations

Six built-in functions, each reading two length-`n` vectors `a` and `b` and
writing one extension-field element to `result`. `n` defaults to `1` and must
be a compile-time constant when given.

```python
add_ee(a, b, result, n=1)         # result = sum_i (a[i] + b[i])
dot_product_ee(a, b, result, n=1) # result = sum_i  a[i] * b[i]
poly_eq_ee(a, b, result, n=1)     # result = prod_i (a[i]*b[i] + (1-a[i])*(1-b[i]))
```

The `_ee` suffix means both `a` and `b` are vectors of *extension*-field
elements (each occupying `DIM = 5` consecutive cells). The `_be` variants
(`add_be`, `dot_product_be`, `poly_eq_be`) are identical except `a` is a
vector of *base*-field elements (1 cell each); `b` and `result` are still
extension-field.

`result` always points to a single extension-field element (5 cells).

For a runtime `n`, dispatch through `match_range`:

```python
def dot_product_ee_dynamic(a, b, res, n):
    debug_assert(n <= 256)
    match_range(n, range(1, 257), lambda i: dot_product_ee(a, b, res, i))
```

Common idioms:

```python
# Multiply two extension elements (n defaults to 1)
dot_product_ee(x, y, z)                       # z = x * y

# Copy an extension element by multiplying by 1
# (ONE_EF_PTR is a constant materialized in the preamble)
dot_product_ee(src, ONE_EF_PTR, dst)

# Extension subtraction: write-once memory turns "c = a + b" into
# the constraint "b + c = a", i.e. c = a - b
add_ee(b, c, a)                               # c = a - b
```

## Debugging

```python
print(value)
print(a, b, c)
```

`print` flushes its output during execution; **a Rust-side panic mid-program drops
buffered prints**. When you need a print to survive a panic, temporarily change
the print hint in `lean_vm/src/isa/hint.rs (Self::Print)` to `eprint!` directly.

## Memory layout

The runner lays out memory as

```python
[ public_input (PUBLIC_INPUT_LEN cells) | preamble_memory | runtime ]
```

- `public_input` is fixed at `PUBLIC_INPUT_LEN = DIGEST_LEN = 8` cells (a hash
  digest), occupying `memory[0..8]`.
- `preamble_memory` is a region of `witness.preamble_memory_len` cells the
  runner reserves immediately after the public input but does **not**
  initialize. The guest program is expected to fill this region with whatever
  helper constants it relies on (e.g. a vector of zeros for
  `dot_product_ee`-as-copy, an extension-field one for multiply-by-one tricks,
  a vector of ones for batched accumulations, …) at the start of `main`. The
  names and offsets of these constants are not enshrined within leanVM. See
  `crates/rec_aggregation/zkdsl_implem/utils.py (build_preamble_memory)` for
  a concrete example.
- The runtime region holds the program's stack frames, working memory, and any
  prover-supplied witness data, all governed by the write-once rule.

## Tips

1. Prefer `unroll` over `range` for small, fixed-size loops.
2. Reach for `: Const` parameters when the function body needs `unroll` over the
   parameter.
3. `if` / `elif` branches that assign to the same outer variable should
   forward-declare it (`x: Imm` or `x: Mut`) before the branch.
7. Function parameters are always immutable. To mutate a parameter's value
   inside a function, introduce a local `: Mut` alias at the top of the body
   (e.g. `y: Mut = x`).

## Example

Look at the recursive aggregation program (to aggregate XMSS) at its entrypoint [main.py](../rec_aggregation/zkdsl_implem/main.py).

## Compilation step-by-step: zkDSL -> ISA

Starting program:

```python
def main():
    x: Mut = 0
    y: Mut = 3
    x += y
    y += x
    for i in range(4, 6):
        x += i
        x += y
        y = i
        y += x
    assert x == 35
    assert y == 40
    return
```

Step 1 — the compiler replaces mutable-across-loop variables with index buffers, since memory
is write-once:

```python
def main():
    x: Mut = 0
    y: Mut = 3
    x += y
    y += x
    size = 6 - 4
    x_buff = Array(size + 1)
    x_buff[0] = x
    y_buff = Array(size + 1)
    y_buff[0] = y
    for i in range(4, 6):
        buff_idx = i - 4
        x_body: Mut = x_buff[buff_idx]
        y_body: Mut = y_buff[buff_idx]
        x_body += i
        x_body += y_body
        y_body = i
        y_body += x_body
        next_idx = buff_idx + 1
        x_buff[next_idx] = x_body
        y_buff[next_idx] = y_body
    x = x_buff[size]
    y = y_buff[size]
    assert x == 35
    assert y == 40
    return
```

Step 2 — SSA-rename all reassignments to fresh names:

```python
def main():
    x = 0
    y = 3
    x2 = x + y
    y2 = y + x2
    size = 6 - 4
    x_buff = Array(size + 1)
    x_buff[0] = x2
    y_buff = Array(size + 1)
    y_buff[0] = y2
    for i in range(4, 6):
        buff_idx = i - 4
        x_body1 = x_buff[buff_idx]
        y_body1 = y_buff[buff_idx]
        x_body2 = x_body1 + i
        x_body3 = x_body2 + y_body1
        y_body2 = i
        y_body3 = y_body2 + x_body3
        next_idx = buff_idx + 1
        x_buff[next_idx] = x_body3
        y_buff[next_idx] = y_body3
    x3 = x_buff[size]
    y3 = y_buff[size]
    assert x3 == 35
    assert y3 == 40
    return
```

Step 3 — lower the runtime loop to a recursive function:

```python
def main():
    x = 0
    y = 3
    x2 = x + y
    y2 = y + x2
    size = 6 - 4
    x_buff = Array(size + 1)
    x_buff[0] = x2
    y_buff = Array(size + 1)
    y_buff[0] = y2
    loop_helper(4, x_buff, y_buff)
    x3 = x_buff[size]
    y3 = y_buff[size]
    assert x3 == 35
    assert y3 == 40
    return

def loop_helper(i, x_buff, y_buff):
    if i == 6:
        return
    else:
        buff_idx = i - 4
        x_body1 = x_buff[buff_idx]
        y_body1 = y_buff[buff_idx]
        x_body2 = x_body1 + i
        x_body3 = x_body2 + y_body1
        y_body2 = i
        y_body3 = y_body2 + x_body3
        next_idx = buff_idx + 1
        x_buff[next_idx] = x_body3
        y_buff[next_idx] = y_body3
        loop_helper(i + 1, x_buff, y_buff)
    return
```

