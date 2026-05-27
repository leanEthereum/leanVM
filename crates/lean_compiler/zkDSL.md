# zkDSL Language Reference

The zkDSL is a Python-syntax language that compiles to leanVM bytecode (4 instructions
+ 2 precompile tables). It is restricted enough that every `.py` source file also
runs as plain Python (using `crates/lean_compiler/snark_lib.py` as a stub library),
which lets you sanity-check programs with a regular interpreter before compiling.

Programs are organized as one or more `.py` files. The toplevel of each file is a
sequence of:

1. `from <module> import *` statements (optional)
2. Top-level constant declarations (optional)
3. Function definitions

Execution starts at `def main(): ...`.

```
from snark_lib import *        # Python compatibility shim, stripped by the compiler
from dir.file import *         # other .py files in the import root
from ..parent_module import *  # parent-directory imports

X = 42                          # constants must come before functions
ARR = [1, 2, 3]

def main():                     # required entry point
    ...

def helper():                   # other functions
    ...
```

The compiler strips the `from snark_lib import *` line (and only that line) so the
same source is valid Python. To run a `.py` file under regular Python for testing:

```bash
export PYTHONPATH=/path/to/repo/crates/lean_compiler
python program.py
```

## Imports

```
from utils import *               # imports utils.py (resolved from the import root)
from dir.subdir.file import *     # nested module
from ..module import *            # parent-directory import (relative to current file)
```

Imports are wildcard-only (`import *`). Each module is loaded once even if imported
multiple times; circular imports are detected and rejected. Constants with the same
name in two imported files cause a compile-time error.

## Constants

Constants live at the top of the file, outside any function. By convention they are
UPPERCASE.

```
X = 42
ARR = [1, 2, 3]
NESTED = [[1, 2], [3]]
```

### Nested (multi-dimensional, possibly ragged) constant arrays

```
MATRIX = [[1, 2, 3], [4, 5], [6, 7, 8, 9]]
DEEP   = [[[1, 2], [3]], [[4, 5, 6]]]
```

Indexed access uses chained subscripts at compile time:

```
x = MATRIX[0][2]       # 3
y = DEEP[1][0][1]      # 5
```

`len()` works at every depth, including on a row addressed by a constant index:

```
len(MATRIX)            # 3
len(MATRIX[0])         # 3
len(DEEP[0][0])        # 2
```

When `len()` is applied with a variable index (`len(ARR[i])`), `i` must be a
compile-time constant. `: Const` parameters always qualify (see [Functions]
below), as do iterator variables of an `unroll` loop (see [For loops] below) —
those are the two ways to get a value the compiler can substitute at expansion
time. Example: iterating a ragged 2D table:

```
MATRIX = [[1, 2, 3], [4, 5], [6, 7, 8, 9]]

def main():
    total: Mut = 0
    for row in unroll(0, len(MATRIX)):
        for col in unroll(0, len(MATRIX[row])):
            total = total + MATRIX[row][col]
    assert total == 45
    return
```

## Functions

```
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

### Parameter modifiers

| Syntax     | Meaning                                                                           |
| ---------- | --------------------------------------------------------------------------------- |
| `x`        | normal (immutable) parameter                                                      |
| `x: Const` | compile-time-known value; enables `unroll`/array sizes that depend on the param   |
| `x: Mut`   | locally mutable parameter (reassignable inside the function — caller is unaffected) |

All parameters are pass-by-value. Use return values to propagate results — there
are no out-parameters.

```
def repeat(n: Const):            # Const enables unroll(0, n)
    sum: Mut = 0
    for i in unroll(0, n):
        sum = sum + i
    return sum

def double(x: Mut):              # Mut: only the local copy is reassignable
    x = x * 2
    return x
```

### Inline functions

`@inline` expands a function at every call site instead of generating a call
instruction. Useful for small helpers, and for cases where the body must "see" the
caller's `: Const` context.

```
@inline
def square(x):
    return x * x
```

Constraints on inline functions:

- No `: Mut` parameters allowed.
- Exactly one `return`, placed at the top level of the body — not nested inside
  `if`, a loop, or `match`. Inlining rewrites the `return` into a plain
  assignment, so early or conditional returns cannot be expressed.

If you need conditional returns, use a normal (non-`@inline`) function. Combine
it with `: Const` parameters when you need compile-time specialization at the
call site.

## Variables

| Declaration   | Mutability | Notes                                          |
| ------------- | ---------- | ---------------------------------------------- |
| `x = 10`      | immutable  | cannot be reassigned                           |
| `x: Mut = 10` | mutable    | reassignable                                   |
| `x: Imu`      | immutable  | forward declaration; assign exactly once later |
| `x: Mut`      | mutable    | forward declaration; reassignable later        |

### Forward declarations

Use `x: Imu` when you want an immutable binding but the value comes from a
branch:

```
result: Imu
if cond == 1:
    result = 10
else:
    result = 20
# result is now immutable
```

Use `x: Mut` when you want to keep mutating the variable after the branch:

```
x: Mut
if cond == 1:
    x = 10
else:
    x = 20
x = x + 1   # OK: x is mutable
```

### Mutability inside tuple assignments

To make a single component of a tuple-return mutable, forward-declare it:

```
b: Mut
a, b, c = some_function()
b = b + 1            # OK
# a = 5              # ERROR: a is immutable
```

## Memory and arrays

```
buffer = Array(16)            # allocate 16 field elements
buffer[0] = 42
x = buffer[5]

matrix = Array(64)            # 2D via manual indexing
matrix[row * 8 + col] = value

ptr2 = buffer + 5             # pointer arithmetic
ptr2[0] = 100                 # same as buffer[5] = 100
```

`Array(n)` returns a pointer to a freshly allocated block of `n` field
elements. `n` may be a compile-time constant (the common case) or a runtime
value; the runner handles both. Memory is **write-once**: a cell may be
written more than once only if all writes store the same value. The second
write of a different value is a runtime error at the point of the write.

```
arr = Array(3)
arr[0] = 10
arr[0] = 10      # OK: same value
arr[0] = 20      # ERROR: conflicting write
```

`Array` cells are not implicitly mutable — if you need a running accumulator,
use `x: Mut` for the variable and only commit final values to memory. Pointer
arithmetic (`ptr + offset`) is the way to address into sub-regions.

## Control flow

### `if` / `elif` / `else`

```
if x == 0:
    y = 1
elif x == 1:
    y = 2
else:
    y = 3
```

Comparison operators on conditions: `==`, `!=`, `<`, `<=`. There is **no** `>`
or `>=` — flip the operands to get the same effect.

### `match`

Patterns must be a contiguous run of integers:

```
match value:
    case 5:
        result = 500
    case 6:
        result = 600
    case 7:
        result = 700
```

The matched value must lie inside the listed range; out-of-range values produce
undefined behaviour. Use a `debug_assert` (or `assert`, if you want it to be
enforced by the proof) to guard the input.

### `match_range`

`match_range` is the workhorse for *dispatching a runtime value to a const-
parameter function*. It is a compile-time construct that expands into a
forward-declared variable plus a `match` over a contiguous range of integers.

```
result = match_range(n, range(1, 5), lambda i: compute(i))
```

expands to

```
result: Imu
match n:
    case 1: result = compute(1)
    case 2: result = compute(2)
    case 3: result = compute(3)
    case 4: result = compute(4)
```

You can chain several `(range, lambda)` pairs, provided the ranges are
**contiguous** (the end of one is the start of the next):

```
result = match_range(
    n,
    range(0, 1),  lambda i: special_case(),
    range(1, 8),  lambda i: normal_case(i),
)
```

Multiple return values are supported via tuple unpacking. The bindings produced
by `match_range` are always immutable — forward-declare with `: Mut` (and then
reassign) if you need them mutable later:

```
a, b = match_range(n, range(0, 4), lambda i: two_values(i))
```

Idiomatic use — dispatching a runtime length to a function that requires a
compile-time length:

```
def helper_const(n: Const):
    return n * n

def compute(value):
    debug_assert(value < 10)
    return match_range(value, range(0, 10), lambda i: helper_const(i))
```

**Range validity is the caller's job.** A `match_range` whose input falls
outside any listed range is undefined behaviour at runtime — always pair it
with a `debug_assert` (or `assert`, if you want the proof to enforce it) on the
dispatched value. Skipping this guard is by far the most common source of
silent bugs in zkDSL.

### For loops

Three loop forms, all written `for i in <range_kind>(start, end):`. Bounds and
behaviour:

| Loop form                    | When                                                                      |
| ---------------------------- | ------------------------------------------------------------------------- |
| `for i in range(a, b):`      | Runtime loop. Compiled into a recursive function (no `break`/`continue`). |
| `for i in unroll(a, b):`     | Compile-time expansion; `a` and `b` must both be compile-time constants.  |
| `for i in parallel_range(a, b):` | Runtime loop; iterations are executed in parallel by the runner via rayon. |

`parallel_range` requires the loop body to be iteration-independent. The
runner executes the first iteration sequentially to learn its memory footprint,
then runs the rest of the iterations concurrently — so anything cross-iteration
must hold a-priori, since there is no synchronization:

- No `Mut` variables carried across iterations (each iteration writes only to
  its own call frame and to addresses disjoint from every other iteration).
- Identical memory footprint per iteration.
- Identical hint consumption per iteration (witness hints, XMSS-specific
  decomposition hints, Merkle hints, etc.).

These constraints are **not** checked at compile time. Violating them produces
silently wrong proofs.

Mutable variables inside non-unrolled loops are supported transparently — the
compiler inserts a buffer array, stores per-iteration values into it, and reads
the final value back after the loop:

```
sum: Mut = 0
for i in range(1, 11):
    sum += i
assert sum == 55
```

Loop limitations (current):

- No `break` or `continue` (these forms are not in the grammar).
- No `return` inside the body of a non-unrolled loop (because such loops are
  lowered to recursive functions). The compiler emits "Function return inside
  a loop is not currently supported" if you try.

### Statements without effect are rejected

Every line must either be a declaration, an assignment, a control-flow form, an
assertion, a `return`, or a side-effecting call (`hint_witness`, precompile,
`print`, or a function call). A bare expression like `x + 1` on its own line is
a compile error.

## Expressions

### Arithmetic

`+`, `-`, `*`, `/` are field operations and work at runtime.

`%` (modulo) and `**` (exponentiation) are **compile-time only** — both operands
must be constants known at compile time.

### Compound assignment

```
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

```
log2_ceil(x)              # ceil(log2(x))
next_multiple_of(x, n)    # smallest multiple of n that is >= x
div_ceil(a, b)            # (a + b - 1) // b
div_floor(a, b)           # a // b
saturating_sub(a, b)      # max(0, a - b)
len(array)                # length of a constant array (any depth)
```

### Reserved names

These identifiers cannot be redefined as user functions, because the parser or
compiler intercepts calls to them:

- Built-ins: `print`, `Array`, `len`, `hint_witness`
- Compile-time math: `log2_ceil`, `next_multiple_of`, `saturating_sub`,
  `div_ceil`, `div_floor`
- Loop / control-flow forms: `range`, `parallel_range`, `match_range`
- Custom hints: every `hint_*` name (see [Hints] below)
- Poseidon16 precompiles: `poseidon16_compress`, `poseidon16_compress_half`,
  `poseidon16_compress_hardcoded_left`,
  `poseidon16_compress_half_hardcoded_left`, `poseidon16_permute`
- Extension-op precompiles: `add_ee`, `add_be`, `dot_product_ee`,
  `dot_product_be`, `poly_eq_ee`, `poly_eq_be`

### `_` (the discard target)

Inside a tuple-unpacking LHS, `_` discards the value at that position. The
compiler rewrites each `_` to a fresh anonymous name so they don't collide.

```
_, b = swap(a, b)             # only keep b
_ = compute()                  # discard a single return value
```

## Assertions

```
# Snark constraint (enforced by the proof)
assert x == y
assert x != y
assert x <  y
assert x <= y

# Unconditional failure (compiles to a Panic)
assert False
assert False, "human-readable message"

# Runtime-only check; not part of the constraint system
debug_assert(x == y)
debug_assert(x != y)
debug_assert(x <  y)
debug_assert(x <= y)
```

`debug_assert` is for invariants the prover must respect but that the verifier
doesn't need to re-check — typically range-validity preconditions for `match` /
`match_range` dispatches.

### Range checks: `assert a < b` and `assert a <= b`

A signed inequality is implemented using DEREF (memory-access soundness on a
read-only memory of size `<= 2^MIN_LOG_MEMORY_SIZE`). The compiler automatically
emits the necessary helper hints, but **the right-hand side `b` must fit in
`2^16` (MIN_LOG_MEMORY_SIZE bits)** for the constraint to be sound. Compare
against larger constants by decomposing the value into bits first.

## Comments

```
# single-line comment

"""
block comment
"""
```

Both forms are stripped before the grammar runs. There is no docstring concept —
a `"""..."""` block is purely a comment.

## Line continuation

As in Python:

- **Implicit** continuation inside `(...)`, `[...]`, or `{...}`.
- **Explicit** continuation with `\` at end of line.

```
result = function_call(
    arg1,
    arg2,
    arg3,
)

ARR = [
    1,
    2,
    3,
]

x = very_long_function_name(arg1, \
    arg2, \
    arg3)
```

## Hints (prover-supplied data)

A hint is data the *prover* writes into memory without adding any constraint —
the program must still constrain the written value if it wants the verifier to
believe anything about it. There are two flavours of hint:

### `hint_witness("name", ptr)`

Pulls the next chunk of witness data registered under the string label `name`,
and writes it into the buffer at `ptr`. Witness data lives in the
`ExecutionWitness::hints: HashMap<String, Vec<Vec<F>>>` map (each name has a
list of byte-buffers, consumed in order). The guest is responsible for
allocating `ptr` large enough; the length is implicit and trusted.

```
data_buf = Array(64)
hint_witness("input_data", data_buf)
n = data_buf[0]
```

### Custom hints

Each hint has a fixed argument count and writes its result(s) into caller-provided
buffers. The hint *suggests* a value — your program must add the constraints
that bind the value to its specification.

| Hint                              | Arguments                                                             | Effect                                                                                                                                  |
| --------------------------------- | --------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------- |
| `hint_decompose_bits`             | `(value, ptr, n_bits)`                                                | Writes `n_bits` big-endian 0/1 field elements at `ptr` (MSB at `ptr[0]`). Requires `n_bits <= 31`.                                       |
| `hint_decompose_bits_merkle_whir` | `(decomposed_ptr, value, chunk_size)`                                 | Writes `24 / chunk_size` little-endian `chunk_size`-bit chunks of `value` at `decomposed_ptr` (`chunk_size` must divide 24).             |
| `hint_decompose_bits_xmss`        | `(decomposed_ptr, to_decompose_ptr, num_to_decompose, chunk_size)`    | For each of `num_to_decompose` values at `to_decompose_ptr[..]`, writes its `24 / chunk_size` little-endian chunks at `decomposed_ptr`. |
| `hint_less_than`                  | `(a, b, result_ptr)`                                                  | `1` at `result_ptr` if `a < b` (canonical integer compare), else `0`.                                                                   |
| `hint_log2_ceil`                  | `(n, result_ptr)`                                                     | `ceil(log2(n))` at `result_ptr`.                                                                                                        |
| `hint_div_floor`                  | `(a, b, q_ptr, r_ptr)`                                                | `floor(a / b)` at `q_ptr`, `a mod b` at `r_ptr` (requires `b != 0`).                                                                    |

## Precompiles

### Poseidon16 family

leanVM has one Poseidon2 width-16 precompile table; the zkDSL exposes five
specializations that all hit the same table.

```
poseidon16_compress(left, right, output)
```

Standard compression: writes the 8-cell compressed output of `Poseidon2(left || right) + left`
to `m[output..output+8]`. `left` and `right` are 8-cell buffers; `output` is an
8-cell destination.

```
poseidon16_compress_half(left, right, output)
```

Same as `poseidon16_compress`, but only the first 4 output cells are
constrained — `output[4..8]` is unconstrained. Useful when the consumer only
cares about half of the digest.

```
poseidon16_compress_hardcoded_left(left, right, output, offset)
```

Like `poseidon16_compress`, except the first 4 cells of the *left* input are
read from the **compile-time** address `offset` instead of `m[left..left+4]`.
The remaining 4 cells of the left input still come from `m[left..left+4]`. Used
e.g. for XMSS Merkle hashing where one half of the input is the public parameter
(stored at a fixed address).

```
poseidon16_compress_half_hardcoded_left(left, right, output, offset)
```

Composition of `_compress_half` and `_compress_hardcoded_left`: hardcoded left
prefix at `offset`, only the first 4 output cells constrained.

```
poseidon16_permute(left, right, output)
```

Raw Poseidon2 permutation (no feed-forward addition). Writes the full 16 output
cells to `m[output..output+16]` in natural order. Used for the Fiat-Shamir
sponge.

### Extension field operations

Six built-in functions all route through one `extension_op` precompile table.
Each combines a fixed element-wise operation with an accumulation over `length`
element pairs:

| Function                            | Element-wise                      | Accumulation         |
| ----------------------------------- | --------------------------------- | -------------------- |
| `add_ee` / `add_be`                 | `e_i = a_i + b_i`                 | `result = sum(e_i)`  |
| `dot_product_ee` / `dot_product_be` | `e_i = a_i * b_i`                 | `result = sum(e_i)`  |
| `poly_eq_ee` / `poly_eq_be`         | `e_i = a_i*b_i + (1-a_i)*(1-b_i)` | `result = prod(e_i)` |

```
func(ptr_a, ptr_b, ptr_result)           # length defaults to 1
func(ptr_a, ptr_b, ptr_result, length)   # explicit length (N element pairs)
```

**Operand suffix:**

- `_ee`: both `ptr_a` and `ptr_b` point to *extension* field elements (5 base-field
  cells each, stride `DIM = 5`).
- `_be`: `ptr_a` points to *base* field elements (stride 1); `ptr_b` points to
  *extension* field elements (stride `DIM = 5`).

`ptr_result` always points to a single extension-field element (5 cells).

**`length` must be a compile-time constant.** For a runtime length, dispatch
through `match_range`:

```
def dot_product_ee_dynamic(a, b, res, n):
    debug_assert(n <= 256)
    match_range(n, range(1, 257), lambda i: dot_product_ee(a, b, res, i))
```

Common idioms:

```
# Multiply two extension elements (length defaults to 1)
dot_product_ee(x, y, z)                   # z = x * y

# Copy an extension element by multiplying by [1, 0, 0, 0, 0]
# ONE_EF_PTR is a guest-program constant that you materialize in the preamble
dot_product_ee(src, ONE_EF_PTR, dst)

# Dot products
dot_product_ee(coeffs, basis, result, N)
dot_product_be(alpha_powers, coeffs, result, N)

# Extension addition / subtraction
add_ee(a, b, c)            # c = a + b
add_ee(b, c, a)            # c = a - b, expressed as a constraint  (b + c = a)

# Equality polynomial: eq(a, b) = a*b + (1-a)*(1-b)
poly_eq_ee(a, b, eq_result)
poly_eq_ee(a, b, result, n)   # multi-point eq: prod_i eq(a[i], b[i])
```

## Debugging

```
print(value)
print(a, b, c)
```

`print` flushes its output during execution; **a Rust-side panic mid-program drops
buffered prints**. When you need a print to survive a panic, temporarily change
the print hint in `lean_vm/src/isa/hint.rs (Self::Print)` to `eprint!` directly.

## Memory layout

The runner lays out memory as

```
[ public_input (zero-padded) | preamble_memory | runtime ]
```

- `public_input` lives at `memory[0..public_input.len()]` and is zero-padded to
  the next power of two by the runner, so it can be evaluated as a multilinear
  polynomial.
- `preamble_memory` is a region of `witness.preamble_memory_len` cells the
  runner reserves but does **not** initialize. The guest program is expected
  to fill this region with whatever helper constants it relies on (e.g. a
  vector of zeros for `dot_product_ee`-as-copy, an extension-field one for
  multiply-by-one tricks, a vector of ones for batched accumulations, …) at
  the start of `main`. The names and offsets of these constants are not part
  of the VM contract — each program defines its own. See
  `crates/rec_aggregation/zkdsl_implem/utils.py (build_preamble_memory)` for
  a concrete example.
- The runtime region holds the program's stack frames, working memory, and any
  prover-supplied witness data, all governed by the write-once rule.

## Tips and gotchas

1. Prefer `unroll` over `range` for small, fixed-size loops — no buffer
   bookkeeping, no recursive-function overhead.
2. Reach for `: Const` parameters when the function body needs `unroll` over the
   parameter, or when array sizes depend on it.
3. `if` / `elif` branches that assign to the same outer variable should
   forward-declare it (`x: Imu` or `x: Mut`) before the branch.
4. **`match`** / **`match_range`** dispatch is undefined for out-of-range
   values — always pair it with a `debug_assert` (or `assert`) on the value.
5. `match` patterns must be contiguous integers; if you need gaps, restructure
   into an `if` chain or pad with an empty arm.
6. `assert a < b` and `assert a <= b` are range-checked under the assumption
   that `b <= 2^MIN_LOG_MEMORY_SIZE = 2^16`. Larger comparisons must be done
   with explicit bit decomposition (`hint_decompose_bits` + manual checks).
7. Inline functions cannot have `: Mut` parameters and cannot return
   conditionally — use a regular function for those cases.
8. `parallel_range` requires per-iteration determinism in memory and hints; a
   single divergent iteration breaks proving.
9. **A variable that's assigned inside an `if` nested in an `unroll` loop may
   silently fail to remain in scope after the loop.** When you're dispatching
   over per-iteration compile-time constants, prefer a flat top-level
   `if`/`elif` chain (one branch per iteration value) over `unroll` + nested
   `if`. This affects compile-time dispatch only; runtime `if` inside `range`
   loops is unaffected.

## A simple example

```
SIZE = 8

def main():
    arr = Array(SIZE)
    for i in unroll(0, SIZE):
        arr[i] = i * i
    sum = compute_sum(arr, SIZE)
    assert sum == 140
    return

def compute_sum(ptr, n: Const):
    acc: Mut = 0
    for i in unroll(0, n):
        acc = acc + ptr[i]
    return acc
```

## Worked example: sugar -> ISA

This shows how the front-end normalizes a small program with mutable variables in
a runtime loop down to a form close to the ISA. The compiler does this
automatically; you don't have to write the intermediate forms.

Starting program:

```
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

Step 1 — replace mutable-across-loop variables with index buffers, since memory
is write-once:

```
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

```
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

```
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
    loop(4, x_buff, y_buff)
    x3 = x_buff[size]
    y3 = y_buff[size]
    assert x3 == 35
    assert y3 == 40
    return

def loop(i, x_buff, y_buff):
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
        loop(i + 1, x_buff, y_buff)
    return
```

## Dev experience

For Python tooling/linting on zkDSL files (which import `snark_lib` at the top),
point your editor at the compiler crate. With VSCode:

```json
{
    "python.analysis.extraPaths": [
        "./crates/lean_compiler"
    ]
}
```

This makes the stubs in `crates/lean_compiler/snark_lib.py` visible to your
language server, so completion / type-checks light up correctly inside `.py`
zkDSL sources.
