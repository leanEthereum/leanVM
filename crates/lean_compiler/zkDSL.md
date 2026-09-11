# zkDSL Language Reference (leanVM)

The zkDSL is a Python-syntax language that compiles to the leanVM ISA: six instructions (`XOR`, `MUL`, `SET`, `DEREF`, `JUMP`, `BLAKE2s`) over the binary field GF(2^192), with write-once memory and all indices carried "in the exponent" as powers of a fixed generator. For the underlying VM and proving system, see [`doc/leanvm/main.tex`](../../doc/leanvm/main.tex).

Source files use the `.py` extension and are **Python-shaped**: they import the [`snark_lib`](snark_lib.py) stub, which defines `GEN`, `log`, `mul_range`, `HeapBuf`, `StackBuf`, `assert_in_k`, and `blake2s`, so editors and linters resolve the intrinsic names. The compiler skips the import. Ordinary helpers such as `pack64x2` are defined in the single-file guest. A program that uses placeholders is not a runnable Python file: its `*_PLACEHOLDER` identifiers are undefined until the host fills them in, so importing it raises `NameError`.

Entry points: `lean_compiler::parse` / `parse_file_with_replacements` → `lean_compiler::compile` → `lean_vm::cpu::prove` / `verify`.

## Dev experience

The repo ships a root [`pyrightconfig.json`](../../pyrightconfig.json) with `"extraPaths": ["crates/lean_compiler"]`, so any `.py` program anywhere in the repo resolves `snark_lib` when the repo root is opened in the editor. A placeholder-free program also runs as plain Python (`PYTHONPATH=crates/lean_compiler python3 crates/lean_compiler/tests/programs/foo.py`); the stubs are no-ops, so this only checks that the file is well-formed.

## The field, and indices in the exponent

The fields are

`K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` and `E = K[y]/(y^3 + y + 1) = GF(2^192)`.

Machine **words** (the contents of a memory cell, an immediate, a hashed value, the `JUMP` condition) are elements of `E`. **Addresses**, the program counter, the frame pointer, read counters, operands, opcodes, and domain separators live in the 64-bit subfield `K = GF(2^64)`. There are no runtime integers.

- `+` is field addition = bitwise **XOR** (192-bit on words, so `x + x == 0`),
- `*` is multiplication in `E`; for g-powers and addresses it stays within `K`,
- `/` is runtime field division, `a / b = a · b⁻¹`. It costs one `MUL`: the compiler leaves the quotient cell unset and emits the checked relation `quotient · b == a`, which witness generation back-solves. Division by zero is undefined. This is distinct from `//`, compile-time integer floor division in sizes and indices,
- an integer literal `n` supplies up to 128 raw bits and is embedded as `F192(c0, c1, 0)`. This is a source-syntax limit, not the machine-word width: words have three 64-bit limbs. Thus `5` is `1 + x^2`, not the integer five, and the literal `18446744073709551616` is the tower element `y`. Written `2 ** 64` in a value position it is not: `**` there is a field power, so it is `x^64` reduced. `const(2 ** 64)` is the literal. Full-width constants use `f192(c0, c1, c2)`, with each limb an unsigned 64-bit compile-time integer,
- `GEN` is the fixed generator `g = x` of the 64-bit subfield `K^×` (multiplicative order `2^64 − 1`),
- `GEN ** e` is the compile-time constant `g^e ∈ K` (`**` takes base `GEN` and a compile-time integer exponent: a literal, a constant, an `unroll` variable, `len(...)`, or index arithmetic of those). So `buf[GEN ** i]` names heap cell `i` directly inside an `unroll` loop, with no running-pointer cursor.
- constant arithmetic means different things in the two positions, and this is a silent trap: `a + b` on two constants is **integer** addition in an index, a bound or a keyword (`buf[GEN ** (i + 1)]`, `unroll(0, n + 1)`, `counter=64 * (q + 1)`), and **XOR** in a value, where `1 + 1` is `0`. So a literal built in a value position must not add overlapping integers: `tweak = base + (level + 1) * SHIFT` drops the whole term on odd levels. Products are safe (an integer times a power of two is that shift, as long as the top bit stays inside the limb); to add, name the regime with `const(...)`: `tweak = base + const((level + 1) * SHIFT)`.
- a **global constant** and a **`Const` parameter** are integer-arithmetic throughout, which is deliberate (it is what makes a derived size right) but means the same text means different things in the two places: `STEP = 3 + 1` is the integer `4` everywhere it appears, while the identical `x = 3 + 1` written inside a function is the field element `2`. Neither is wrong; they are two regimes, and a name crossing between them is where the trap bites.
- a **compile-time `if`** must say which regime it means when the two disagree. The fold decides on the integer reading while the runtime test of the same condition compares field values, so `if 3 + 1 == 4` is true one way and false the other. Such a condition is **rejected**; write `if const(3 + 1 == 4):` to decide it with integer arithmetic, or spell the operands so the two readings agree (a product or a shift rather than a sum of overlapping integers). A condition whose readings already agree needs no wrapper.
- `base ** e` with a **non-`GEN`** base and a compile-time exponent `e` is square-and-multiply: integer arithmetic in an index/bound position (`2 ** c`), or field arithmetic in a value position (`x ** k`, e.g. a loop counter `g^i` raised to a stride to reach cell `i·stride`). The base may be runtime.

A logical **index** `i` is carried as `g^i` in the 64-bit subfield (order `2^64 − 1`): incrementing is one multiplication by `GEN`, and memory/bytecode addresses are g-powers. This is the design idiom of the whole VM: loops, heap addressing, and range checks below all live in the exponent, in `K`.

## Program shape

A program is a **single** `.py` file:

```python
from snark_lib import *   # for Python tooling; skipped by the compiler


def main():               # required entry point
    ...
    return

def helper(a, b):         # other functions
    ...
    return a * b
```

`import snark_lib` / `from snark_lib import *` are the only imports accepted; anything else is a compile error (no multi-file programs yet). Comments (`#`) and blank lines are free. Indentation is block structure, as in Python.

Ordinary functions may return scalars, `HeapBuf` pointers, and `StackBuf` values, including mixtures in a tuple return. A returned `StackBuf(n)` has a compile-time-known size: its `n` cells are copied through `n` consecutive return slots and the caller binds the result as a new `StackBuf(n)`. A `HeapBuf` return is just its one-cell pointer; the allocation hint already ran where the buffer was created, so no size metadata needs to cross the call.

## Public input

Memory cells `m[0]` and `m[1]` hold the two public-input words, each an F192 machine word. A program *publishes* results by asserting them against those cells through the write-once heap store (the pointer `g^0` addresses absolute memory):

```python
p = GEN ** 0
p[1] = result_a     # m[p·1]  = m[0], an equality assert against the public input
p[GEN] = result_b   # m[p·g] = m[1]
```

Test programs under `tests/programs/` declare the public input they expect with a top-of-file annotation of two constant elements (or omit it to run with two zeros); the generic harness `tests/py_source.rs` proves and verifies every program in the directory:

```python
# public_input: GEN ** 89, 101229015297003380629709256178361811305
```

## Global constants and placeholders

Above the functions (after the optional `snark_lib` import) a program may declare **global constants**, top-level `NAME = <const-expr>`:

```python
from snark_lib import *

N = 8                    # an integer size / value
STEP = GEN ** 2          # a g-power constant (index carried in the exponent)
WIDE = N + 1             # compile-time INTEGER arithmetic (`+ - * / **`);
                         # references to *earlier* constants are allowed

def main():
    buf = StackBuf(N)    # a constant is a plain literal: usable as a size,
    x = GEN ** N         # a `**` exponent, a stack/slice index, an operand,
    assert log x < N     # an `assert log _ < _` bound, or a `Const` argument
    return
```

Each constant is **evaluated as a compile-time integer expression** (or an `f192` literal, or a field-valued one such as `GEN ** 2`) and substituted as a single literal everywhere its name appears below, so unlike a `Const` parameter it needs no call site and works in every literal position. Integer arithmetic is the point: it is what makes a derived size come out right, as in `N_TWEAK_WORDS = 2 + CHAIN_STEPS * V + LOG_LIFETIME`. Constants must precede the `def`s and are resolved *before* variables, so a constant name is **reserved**: do not reuse it as a parameter or local name. (Syntactically, `N = 8` is just a Python module global.)

**Placeholders** let a host fill values at compile time without editing the source. Any identifier may be mapped to replacement text before parsing (`parse_with_replacements` / `parse_file_with_replacements`, taking a `BTreeMap<String, String>`); the replacement is identifier-bounded (`FOO` does not touch `FOOBAR`). The idiom is a placeholder feeding a constant:

```python
V = V_PLACEHOLDER        # with replacement  "V_PLACEHOLDER" ↦ "128"
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER

def main():
    ...                  # V is the constant 128 throughout
```

so one source template compiles at many sizes. An unfilled placeholder (no replacement, no matching constant) is a compile error, not a silent variable.

### Constant arrays

A global constant may be a **list literal**, `NAME = [a, b, c]`, of compile-time values (integers or field values, each a `<const-expr>`). Unlike a scalar constant it is **not** textually substituted; it is carried to lowering and consumed at compile time:

```python
QUERIES = [290, 177, 145]          # or QUERIES = QUERIES_PLACEHOLDER, filled "[290, 177, 145]"
Z       = [Z0_PLACEHOLDER, Z1_PLACEHOLDER, Z2_PLACEHOLDER]   # arbitrary field values

def main():
    for lvl in unroll(0, len(QUERIES)):     # len(NAME) is a compile-time count
        n = QUERIES[lvl]                     # NAME[i] with a compile-time index i
        row = buf[GEN ** QUERIES[lvl]]       #   (i a literal / constant / unroll var)
        ...
```

`NAME[i]` yields the element (as a field value in value position, or as an integer where an index / slice bound / `unroll` count / `**` exponent is expected), and `len(NAME)` its length. The index `i` must be compile-time (a literal, a constant, or an `unroll` variable). This is what lets one source file adapt to a per-level config vector (query counts, fold factors, sizes) without Rust-side code generation. Nested lists are not (yet) supported: flatten a 2-D table into one array plus an offsets array.

## Functions

```python
def f(a, b):
    return a + b, a * b   # multiple returns

x, y = f(p, q)            # tuple assignment
z = f(p, q)               # expression position: first return
f(p, q)                   # statement: returns discarded
```

Functions may recurse. Each call gets a **fresh frame**: the frame pointer is prover-hinted (write-once memory makes an unconstrained cell prover-chosen), arguments and the return address/frame are stored with `DEREF`s, and control transfers with one `JUMP`. Cost: about `n_args + n_returns + 4` instructions per call. Every non-`main` function must end in an explicit `return`; in `main`, `return` is a no-op (main halts at a sentinel automatically).

### `StackBuf` parameters

```python
def compress(cv: StackBuf(2), block: StackBuf(2)):
    out = StackBuf(2)
    blake2s(cv, block, out)
    return out
```

`s: StackBuf(n)` marks a parameter as a **run of n cells**, passed whole. The caller must pass a `StackBuf` of exactly that size (a whole named one: a slice is not yet accepted), and the run is copied into the callee's frame.

Those cells arrive **already written**, unlike a local `StackBuf`'s, so a store into one is the write-once equality *assertion* rather than a fresh store. That is what makes a callee able to pin its caller's values: `s[k] = <checked value>` inside the callee asserts that the caller's cell already held it. It also means a run parameter initializes nothing, so passing a partly-written buffer passes its unwritten cells, which the prover then chooses, exactly as anywhere else.

A `match` arm cannot pass one: the fused dispatch writes one cell per argument, so give such arms `Const` arguments and let each specialize instead. This is otherwise the same mechanism a `StackBuf` **return** already used, in the other direction: the argument area is a width rather than a count, and a run occupies the cells its size asks for. Without it a two-cell value could come out of a function whole but only go in through a `HeapBuf` pointer or an `@inline` expansion, which grows the caller's frame at every call site.

### `Const` parameters

```python
def hash_pair(buf, k: Const):
    h = StackBuf(2)
    blake2s(buf[k * 2:k * 2 + 2], buf[k * 2:k * 2 + 2], h)
    return h[0], h[1]
```

`k: Const` marks a **compile-time parameter**: the call site must pass a constant (an integer literal, `GEN ** k`, or a literal-bound name), and the compiler *specializes* the function per distinct constant tuple, a monomorphized copy (`hash_pair__L1`) with the parameter substituted as its literal, shared by every call with the same constants; only the runtime arguments are passed. Inside the body the parameter *is* the literal, so it works in compile-time positions: stack indexes, slice bounds. A function with a `Const` parameter is a template: it is never lowered itself. The idiomatic pairing dispatches a runtime index to a const-indexed helper:

```python
r = match(log(x), range(0, 4), lambda i: hash_pair(buf, i))
```

### `@inline`: inline a function at its call sites

```python
@inline
def combine(a, b, k: Const):
    s = StackBuf(2)
    if k % 2 == 0:      # a folded `if` (see below): baked per Const value
        s[0] = a
    else:
        s[0] = b
    s[1] = a + b
    return s[k % 2]
```

An `@inline` function is **expanded at each call site** instead of emitting a real call: no frame, no argument/return `DEREF`s, no call/return `JUMP`s. Its body must end with one top-level `return`. Builtins, ordinary calls, nested inline calls, `if`, and `unroll` are allowed; `mul_range` loops, `match`, tuple assignments within the body, and nested/early returns are rejected. Ordinary calls retain their own frames; nested inline calls expand recursively, with direct or indirect recursive expansion rejected.

An `@inline` function may also **return a `StackBuf`**: the caller's binding aliases the returned cell run (zero copies), and `StackBuf` arguments alias likewise.

An `@inline` call may also sit in **expression position**: embedded in arithmetic, as a store's RHS, or as a single-target `match` arm. An aliased return (a folded g-address) then materializes into a plain cell (free for a var; one `MUL` for a shifted pointer); a multi-cell `StackBuf` return still needs a `let` binding, since only a name can alias a cell run.

An `@inline` function that also takes a `Const` parameter and is used as a `match` arm is specialized rather than expanded: the fused dispatch enters one real function, so `@inline` is simply not honoured there. One without a `Const` parameter has no entry to dispatch to and is rejected.

Because the body runs in the *caller's* frame, a `Const` parameter whose `if`s fold (below) bakes straight-line, per-case code, the idiom for a `match` arm that must specialize on the arm value. The trade-off is frame cells: each call site gets its own copy, so `@inline` pays off for small, hot callees; inlining a large body at many sites grows the committed witness (more data memory), so it is opt-in, not automatic.

## Variables

Bindings are **immutable**: `x = e` names a fresh cell. Re-binding a name is allowed (it's a new cell; the old value is unaffected), but there is no mutation. Compound assignment (`+=`, `-=`, `*=`, `//=`, `%=`) is sugar for a re-binding: `x += e` desugars to `x = x + e`.

A name bound to an integer literal (`x = 2`) additionally acts as a **compile-time index constant**, usable in stack indexes and slice bounds (see below). Any other re-binding clears that role.

Two families of binding are folded and carried **virtually**, costing no instruction until used as a value:

- **g-powers and shifted pointers**: a cursor like `s = s * GEN` or a pointer view `p = buf * GEN ** k`. The offset folds into the `DEREF` address of each access; only a scalar use materializes it.
- **field constants**: a value built from literals / `GEN ** k` by field `+` and `*`, e.g. a running weight `w = w * CHAIN_LENGTH` in an unrolled loop. The arithmetic that advances it is compile-time (zero instructions); each use is one `SET` of the folded constant.
A store into a stack cell is NOT virtual: `sa[k] = other` always emits. If the cell already holds a value the store is the write-once equality *assertion* below, which is what makes `s[k] = <checked value>` pin a hint and a pre-written `blake2s` output verify a digest; if it does not, the store is what gives the cell its value. The compiler tracks nothing to tell those apart, the machine's write-once memory being what distinguishes them.

## Debugging

`print(expr)` / `print("label", expr)` displays a value at witness generation (prover side only, with no constraints and nothing entering the transcript). The label defaults to the argument's source text; output goes to stderr as `[print] label = ...`, showing the decimal reading for small integers, `g^k` when the value is a small g-power (both when they overlap: `8 (g^3)`), or `c2:c1:c0` hex otherwise, from the most significant limb to the least significant. Each print costs one anchor instruction, so the witness differs from a print-free build: strip prints before benchmarking.

## Memory

All memory is **write-once**: a cell is set once; a second write of the same value is a no-op, of a different value a proof failure. This turns stores into equality assertions and is used throughout (publishing, `blake2s` outputs). Reading a cell nobody ever writes yields an unconstrained value (fixed to zero at the end of witness generation): don't.

### `HeapBuf(n)`: heap buffers, indexed in the exponent

```python
buf = HeapBuf(4)      # fresh, disjoint region; `buf` is its pointer (a g-power)
buf[1] = 5            # m[buf·1]   is cell g^0
buf[GEN] = 7          # m[buf·g]   is cell g^1
v = buf[i]            # m[buf·i], i any runtime g-power (e.g. a loop counter)
buf[i * GEN] = v      # the next cell along
```

The index is a field element; cell `k` of the buffer lives at address `buf · g^k`. A read or store is one `DEREF`. A **runtime** index costs one extra `MUL` for the `buf·i` pointer, but a **compile-time g-power** offset (`buf[1]`, `buf[GEN ** k]`, or a cursor advanced by `× GEN ** m`) folds into the `DEREF`'s address immediate for free: no `MUL`, no `SET`, and the cursor arithmetic itself vanishes (so a `× GEN` walk over consecutive cells is zero instructions).

**Compile-time indices are bounds-checked.** When the whole index is a compile-time exponent and the pointer resolves to a declared `HeapBuf` (directly, or through shifted aliases like `row = buf * GEN ** k`), the compiler rejects `index >= size`, and the same for the spans of `hint_witness` and `blake2s` slices. **Runtime** indices are not checked (their value is unknown at compile time): there the buffer remains a region convention, and a stray access surfaces at proving time as a write-once conflict or wild deref.

### `StackBuf(n)`: frame-cell runs, indexed by compile-time integers

```python
sa = StackBuf(3)      # n consecutive cells of the current frame
sa[0] = 3             # direct frame cell: no DEREF, but the store is an instruction
sa[2] = sa[0] + sa[1]
x = 1
v = sa[x + 1]         # indexes: literals, literal-bound names, and + * // % of those
tg = [v, 7]           # list literal: an initialized StackBuf, one cell per element
```

A **list literal** `x = [a, b, …]` is an initialized `StackBuf`: it allocates one cell per element and writes each element in place, exactly the alloc-then-store idiom above, in one line. Elements are arbitrary runtime expressions; each write goes through the same stack-store path. It exists only as the RHS of a plain assignment inside a function; a *top-level* `NAME = [...]` is a constant array (see "Constant arrays"). The elements are lowered before the name rebinds, so `s = [s[1], s[0]]` swaps through the old binding.

Stack indexes and slice bounds are **compile-time integers**, and index arithmetic (`+ * // %`) is *integer* arithmetic (`x + 1` above is 2, `k // 2` floor-divides, `k % 2` is a remainder: index space, not the field, where XOR is what `+` means and `//`/`%` have no meaning at all: using one as a runtime field value is a compile error). Bounds are checked at compile time. A `StackBuf` name is a run of cells, not a scalar: using it as one is an error, and it cannot be captured into a `for` loop body (carry state through a `HeapBuf` instead).

`p = addr(sb)` names the run's first cell as a **pointer** (`GEN ** k` times the frame pointer), so `p[i]` reads the same cells at a runtime index, `p` can be passed to a callee or stored, and `sb[k]` stays a direct frame cell throughout. Only valid as a whole right-hand side. It costs one materialization of `fp` per function (2 `DEREF`s, amortized with `if`'s; free in `main` and in loops with reserved frames), which is the price of the ISA having no fp-read. This is what lets a bit buffer live in the frame and still be walked by a `mul_range` loop.

A runtime index through such a pointer is unchecked, as on the heap, but it fails more quietly: every frame cell is a real cell, so `p[i]` with a hinted `i` reaches any of them and usually neither faults nor conflicts. The program owes the range check itself (`assert log i < n`) wherever `i` is not a loop counter the compiler produced.

### Slices: `buf[lo:hi]`

`buf[lo:hi]` names a run of cells (`hi` exclusive). BLAKE2s operands must span exactly two cells; `hint_witness` accepts any supported literal length. Two forms:

- **compile-time bounds** (integers, as for stack indexes): frame cells `base+lo .. base+hi` of a `StackBuf`, or heap cells `ptr·g^lo .. ptr·g^hi` of a `HeapBuf`, so `hb[2:4]` is the pair `g^2, g^3`;
- **runtime start, heap only**: `buf[i:i + k]` with a runtime g-power index `i` (e.g. a loop counter) and literal length `k` names the cells `buf·i`, `buf·i·g`, and so on; one `MUL` folds `i` into the pointer. The `hi` bound cannot be evaluated, only shape-checked: it must be syntactically `lo + k` (`buf[b * GEN ** 2 : b * GEN ** 2 + 2]` is fine). A `StackBuf` slice cannot have a runtime start: frame offsets are baked into the bytecode operands.

Note the two index spaces, consistent with plain indexing: compile-time bounds are integer exponents (`hb[2:4]` ≡ `hb[GEN ** 2 : GEN ** 2 + 2]`), runtime starts are g-power elements.

## Control flow

### `for i in mul_range(start, stop)`: loops in the exponent

```python
for i in mul_range(1, GEN ** 10):   # i = g^0, g^1, …, g^9
    buf[i * GEN * GEN] = buf[i] * buf[i * GEN]
```

The counter walks multiplicatively: it starts at `start`, advances by `×GEN` each iteration, and stops on reaching `stop` (exclusive). The start is a compile-time power of `GEN` (`1`, `GEN`, or `GEN ** k`); the stop is either compile-time too (an empty range compiles to nothing) or a **runtime** g-power element, e.g. a hinted count:

```python
hint_witness(nb[0:1], "n_blocks")
n = nb[0]
assert log(n) < 16       # the walk terminates only by REACHING the bound:
for j in mul_range(1, n):   # bound its log first, or it never does
    ...
```

A runtime bound is evaluated once at entry and threaded through the loop as an extra parameter (+1 argument per iteration call); entry itself is the same `!=` test, so a bound equal to the start runs zero iterations.

Lowering: the body becomes a tail-recursive helper function whose exit test is folded into the recursion's `JUMP` condition: one call per iteration, no separate is-zero gadget. Free variables of the body are captured **by value** as extra parameters; a `HeapBuf` pointer threads through fine, a `StackBuf` does not (compile error).

The compiler reserves consecutive frames for a loop that has no early return and does not rebind its counter. Its back edge advances by the frame size and copies arguments directly into the next frame, while ordinary function calls and heap allocations remain disjoint from the reserved run. Each iteration still owns fresh write-once cells, so a pointer to an earlier iteration remains valid. Loops with an early return or counter rebinding keep incremental allocation.

### `for i in unroll(a, b)`: compile-time unrolling

```python
for i in unroll(0, 7):
    sb[i + 1] = sb[i] * GEN          # i is the integer literal of each copy

def chain(buf, n: Const):
    for i in unroll(0, n):           # a Const parameter as a bound
        blake2s(buf[i * 2:i * 2 + 2], buf[i * 2:i * 2 + 2], buf[i * 2 + 2:i * 2 + 4])
    return
```

The body is replicated `b − a` times with `i` substituted by each integer literal in turn, usable anywhere a literal is (stack indexes, slice bounds, `Const` arguments). Zero loop overhead: no call, no frame, no counter; the price is code size. Bounds are compile-time integer expressions, evaluated after `Const` specialization, so `unroll(0, n)` with `n: Const` works (unlike `mul_range`, whose bounds are parse-time literals). Every copy executes (this is straight-line code, not a branch), so bindings simply rebind, a fresh binding per iteration.

### `if` / `elif` / `else`

```python
if x == GEN ** 3:
    r[1] = 5
elif x != y:
    r[1] = 7
else:
    r[1] = 9
```

Conditions are field-equality tests: `a == b` or `a != b` (there are no other predicates: order facts come from range-check asserts). The lowering is one `XOR` plus one conditional `JUMP` on it; the taken jump goes to whichever block the test doesn't fall into, so no negation gadget is needed. An `elif` is sugar for an `else` holding a nested `if`.

When **both sides are compile-time integers** (e.g. after a `Const` parameter is substituted, `if k % 2 == 0:`), the condition is known at compile time and the `if` **folds** to just the taken branch: no `XOR`, no `JUMP`, no `self-fp`. This is what lets an `@inline` function bake different straight-line code per `Const` value. A side whose integer reading and field reading disagree (`3 + 1` is the integer 4 and the field element 2) is **rejected** rather than folded either way, since the fold and a runtime test of the same condition would answer differently; write `if const(...)` below to decide it with integer arithmetic. Note that the rejection is per side, so it fires however the OTHER side is spelled.

Two write-once-flavored rules:

- **bindings made inside a branch are local to it**: the compile-time scope reverts at the join. Branches communicate through memory: only one branch executes, so both may write the *same* cell (`r[1]` above), and the join reads it.
- a cell nobody wrote (e.g. skipped-branch territory) stays unconstrained, the same rule as everywhere else in write-once memory.

Local jumps must carry the frame pointer, which the ISA cannot read directly; each branching function materializes its own `fp` once (2 `DEREF`s through a 1-cell heap bounce; free in `main`, where `fp = g^0 = 1`).

### `match`

```python
r = match(log(x), range(0, 6), lambda j: f(j))
a, b = match(log(x), range(0, 2), lambda j: g(1), range(2, 6), lambda j: g(j))
```

The one dispatch construct. It matches the **log** of a g-power scrutinee against integer arms, which must cover consecutive integers from 0 (the dispatch table is dense; there is no default arm). Arm `j` is the lambda body with the parameter replaced by the **integer literal** `j`, usable as a field constant or a compile-time index, expanded at parse time over the contiguous `(range, lambda)` pairs. The whole call sits on one line, there being no line continuation.

Arms produce VALUES: every arm writes its results into the same cells, which is sound under write-once because exactly one arm runs. A target may be a name, bound after the join, or a **`StackBuf` element**, which the arms write into directly and which costs one instruction less than a name plus a store. The ABI returns into cells the CALLER picks, the same reason `sb[i] = f(x)` never needed a temporary, so reach for the element form wherever a returned value's home is a buffer slot. A target index must be a compile-time integer inside the buffer, both errors naming the line; a `HeapBuf` element is not a target, its cells not being frame cells. Multiple targets take a multi-return call as the arm body.

A branch body with statements in it goes in a function, and the arm calls it: that is the idiom the recursion guest uses throughout (`lambda k: walk(chain_start, tweaks, pp, k)`), and it names the body instead of inlining it. Where the arms only PRODUCE values, as there, this costs nothing. Where each arm's real work is a WRITE, it costs: the writer function needs a return value and the statement a target, both dead, and the natural translation measures about twice the instructions of a body inlined into the dispatching frame. An arm cannot take a `StackBuf` parameter either, so it cannot hash or hint into the caller's frame buffer. If that shape matters to a program, dispatch on a value and write after the join.

**Lowering** is two jumps through a *trampoline table* in the bytecode: the dispatch jumps to `g^T · x²`, the j-th two-instruction slot (`SET` the arm's address, `JUMP` to it) of a table at base `T`, and the slot jumps to the arm, which can sit anywhere, unaligned and of any length. Cost is about 7 cycles, independent of the arm count.

(Why not leanVM's single-jump `pc = a + b·x`: that affine address needs integer *scaling* by the common block size `b`, which in the exponent becomes `x^b`, log₂ b squarings, plus padding every block to the longest; the trampoline collapses the aligned region to 2-instruction slots, so the scaling is the single squaring `x²`. Other layouts exist, e.g. a memory-resident address table dispatched with a single jump, worthwhile for many repeated small matches, but only the trampoline is implemented.)

**Soundness**: nothing in the dispatch bounds `x`, so a scrutinee outside `[0, n)` jumps to an arbitrary pc. A hinted value must be range-checked first (`assert log(x) < n`, 3 cycles), as in leanVM.

**Dispatched-call fusion.** When *every* arm is a call to the same function with identical runtime arguments (the common `lambda k: f(a, b, k)`, where only a `Const` argument varies), the compiler builds the callee frame **once** and the dispatch jumps straight into the selected specialization's entry, which returns past the join. Each taken arm is then just the trampoline's two instructions (`SET entry; JUMP`) instead of a full call: no per-arm frame setup, call jump, or return jump. (The `walk`-per-digit dispatch in the XMSS verifier is the motivating case.)

Statements without effect are rejected.

### `if const(...)`: a branch decided while compiling

```python
if const(level + 1 == DEPTH):   # decided now, with integer arithmetic
    tail = 0
```

Wrapping a condition in `const(...)` asks for the branch to be decided while compiling. Two things follow. The condition must be decidable then, so both sides must be compile-time integers, and a runtime one is an error rather than a silent fallback to a runtime test. And it is read with **integer** arithmetic, the regime a compile-time constant lives in, which is what makes `const(...)` the answer when a condition's two readings disagree (see "The field, and indices in the exponent").

A folded branch emits no test and no jump, and its body is straight-line code, so **its bindings outlive it** where a runtime branch's are branch-local. That is the other reason to reach for the wrapper: it states that the arm's bindings are meant to escape.

A plain `if` still folds on its own when both sides are compile-time integers and neither side's two readings disagree, so the wrapper is needed only where one does, where the condition is decidable only in the field (`GEN ** 3 == GEN ** 3`, which a plain `if` lowers to a real runtime branch), or where you want the compiler to insist.

### `const(...)` in a value position

```python
tweak = TW_NODE + const((level + 1) * P_MUL) + tau   # (level+1)*P_MUL as integers
```

The same wrapper, the same meaning: read this with **integer** arithmetic and emit the literal. It is needed because `+` in a value position is XOR, so `level + 1` with `level = 3` is 2 rather than 4, and silently: the value is well-formed, just not the one the arithmetic reads like. `-`, `//` and `%` have no field meaning at all, so `const(...)` is the only way to write them in a value position.

The inner expression must be a compile-time integer (a literal, a global constant, a `Const` parameter, an `unroll` counter, a name bound to one, a constant-array element, and `+ - * // % **` of those), and one that is not says so rather than falling back to a runtime computation. The result is one pooled `SET`, so a repeat costs nothing.

In a position that is ALREADY integer arithmetic (a size, a count, an exponent, a bound, a stack index, a global constant) the wrapper is transparent: it asks for the only reading there is, so it changes nothing and is allowed rather than redundant. Where it earns its keep is a value, a condition, and anywhere `-`, `//` or `%` has to appear.

The wrapper reinterprets the **operators**, not the leaves, and that is the whole of its meaning. Two consequences. A leaf whose own two readings disagree is rejected rather than silently read one way, so `n = 2 + 3` (the cell holds `2 XOR 3` = 1, the name's integer reading is 5) may not appear inside one: bind it in one regime and name that one. And the arithmetic runs on a leaf's **bit pattern**, so an element of a field-valued constant array is read as the integer those bits spell, which is not what field arithmetic on it would give: `const(TABLE[i] * 2)` doubles the bit pattern where `TABLE[i] * 2` is a field product.

## Assertions

### `assert a == b`

A proof-enforced equality: 1 cycle (`XOR` into the frame's zero cell, whose write-once double write is the assert).

### `assert a != b`

A proof-enforced inequality, in **3 instructions and no branch**: `XOR` for `x = a + b`, a prover-hinted `inv = x⁻¹`, then `MUL p = x·inv` and `SET p = 1`, where the write-once conflict is the assertion, exactly as for `assert a == b`. It is sound because `x = 0` forces `p = 0` whatever the prover hints, and `p` cannot then also be `1`; the hint needs no checking of its own, which is why an unconstrained value is safe here. Since there is no `JUMP` there is no self-frame or branch setup to amortize either. A compile-time assertion such as `assert 5 != 5` is rejected while compiling.

### Range checks: `assert log x < log Y` and `assert log x < k`

The *range check in the exponent*: proves `x ∈ {g^0, g^1, …, g^{k-1}}`, i.e. `log_g(x) < k`. A compile-time bound is either `log GEN ** k` or a plain integer exponent `k`, with `1 ≤ k ≤ 2^16` (the minimum memory size, which keeps the gadget provable at every memory size the prover may announce). `log x` and `log(x)` both parse; the parenthesized form is the valid-Python spelling. A bare `assert x < y` is rejected: field elements have no order, only their logs do.

```python
assert log(x) < log(GEN ** 8)
assert log(x) < 8               # the same check
assert log(x) < log(n)          # n = g^k runtime: same gadget, +1 cycle
```

A **runtime** bound costs one extra `MUL` for `g^{k-1} = n·g⁻¹` and is otherwise identical, except that the `k ≤ 2^16` cap becomes the program's to enforce: range-check the bound itself first, with `assert log n < 2^16`. That check is not optional: without it the gadget is unsound.

Cost: **3 cycles** (leanVM's DEREF range-check trick, in the exponent) plus one amortized `SET` per distinct bound per frame:

1. `DEREF` through `x`: the dereferenced address must be one of the memory's `2^h` g-power addresses, so the memory bus itself proves `x = g^e`, `e < 2^h`;
2. `MUL x·y` into the write-once cell holding `g^{k-1}`: the runner back-solves the complement `y = g^{k-1-e}` (the one unknown operand of a known product), and the double-write asserts `x·y = g^{k-1}`;
3. `DEREF` through `y`: bounds the complement; a "negative" `k-1-e` would wrap to `≈ 2^64`, far beyond any memory size, so together `e ≤ k-1`.

The two `DEREF` target cells are unconstrained touches, back-filled at the end of execution. A failing check surfaces at witness generation as the complement's `DEREF` panic ("not a small g-power … a failed range check").

## K membership and packing

```python
assert_in_k(lo, hi)
```

`assert_in_k(a, b)` is the sole packing-related compiler intrinsic. It proves that both source memory words are in the base field GF(2^64) with one untaken `JUMP`: its condition is a known zero, while its destination and frame operands are `a` and `b`. Although neither value affects the successor state, both memory reads carry literal-zero upper limbs, so a source outside GF(2^64) cannot balance the memory permutation.

Packing is ordinary zkDSL built on that assertion:

```python
@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + f192(0, 1, 0) * b
```

The inline helper takes three cycles, one `JUMP`, one `MUL` and one `XOR`, and returns the canonical 128-bit packing `(a.c0, b.c0, 0)`. Assignment-target lowering writes its return directly into the destination, including an already-written cell whose second write is an equality assertion. A caller needing only membership uses `assert_in_k` directly and pays no packing arithmetic.

The recursion transcript uses `challenge_from_state(state)` to reinterpret the first three 64-bit lanes of a canonical two-cell BLAKE2s digest as one extension field challenge. For `state = [s0, s1]`, it lowers exactly as follows (the limb hints cost no cycles, but are not trusted):

```python
d2 = StackBuf(1)
hint_f192_limbs(d2, state[1])
d3 = (state[1] + d2[0]) * Y_INV
assert_in_k(d2[0], d3)
challenge = state[0] + d2[0] * f192(0, 0, 1)
```

Both state words are BLAKE2s outputs, so their top limbs are already zero. Only `d2` must be exposed separately; deriving `d3 = (s1+d2)/Y` and proving both values lie in GF(2^64) binds the one hinted limb by uniqueness of the tower representation. The challenge is `s0+d2·Y² = d0+d1·Y+d2·Y²`, while `d3` is checked but deliberately discarded. `challenge_from_state` is not a compiler intrinsic: this is the complete `@inline` helper used by the recursion guest.

## BLAKE2s

```python
h = StackBuf(2)
blake2s(a, b, h)                    # digest of (a, b) written into h
blake2s(t[0:2], t[x:x + 2], t[4:6])  # slices of one large StackBuf
blake2s(h, hb[0:2], hb[2:4])         # HeapBuf slices, input and output
blake2s(hb[i:i + 2], h, hb[j:j + 2])  # runtime-indexed heap slices (i, j g-powers)

# A standard 80-byte hash as two blocks. Keyword values are compile-time.
block0 = [1, 2, 3, 4]  # 64 bytes
tail = [5, 0, 0, 0]    # 16 more, the rest of the block zero-filled
blake2s(block0[0:2], block0[2:4], cv, counter=64, final=0)
blake2s(tail[0:2], tail[2:4], out, cv=cv, counter=80, final=1)

# The same, with the second block's metadata computed at run time.
blake2s(tail[0:2], tail[2:4], out, cv=cv, md=high + f192(16, 4294967295, 0))
```

The three positional arguments form a **statement**: one standard BLAKE2s compression consumes the two 256-bit message operands `a`, `b` (64 bytes) and writes its 32-byte result into the 2-cell run `out`. With no keywords it computes the standard hash of exactly 64 bytes: the parameterized BLAKE2s-256 initial chaining value (digest length 32, unkeyed, fanout and depth 1), byte counter 64, final-block flag `f0` set. That is `blake2s(a || b)`, the form every Fiat-Shamir step and Merkle node uses.

Every compression also has a 256-bit chaining value and a 128-bit metadata word. The optional keywords are:

- `cv=<pair>`: a consecutive 2-cell chaining value, the previous block's output; omitting it selects the parameterized IV above. On each runtime path, a function emits two `SET`s at its first such hash only and reuses those cells thereafter. Supplying `cv=` also requires one of the four below, since a chained block is never the default one-block hash;
- `counter=<u64>`: BLAKE2s's byte counter `t`, **cumulative** through this block, so `64 * whole_blocks_before + bytes_in_this_block`. Defaults to 64;
- `final=<0|1>`: BLAKE2s's final-block flag `f0`. It defaults to 1 for the bare three-argument call, but to **0** as soon as `counter=` or `last_node=` appears, so a chained hash must set `final=1` on its last block and a single short block needs `counter=<len>, final=1`. Any compile-time expression works, nonzero meaning set, which is what lets the guests write a predicate like `final=(q + 1) // BLOCKS_PER_HASH`;
- `last_node=<0|1>`: BLAKE2s's tree-mode flag `f1`. Defaults to 0, and nothing here uses tree mode;
- `md=<value>`: the whole 128-bit metadata word, as a value the program computed, for a hash whose block count is only known at run time. It replaces the three keywords above (giving both is an error) and it owes the same canonical embedding as every other operand, its top limb being read as a literal zero. The cheap way to build one is the disjoint-bit split of `doc/leanvm` §Byte counters for a hash of runtime length: XOR a runtime high part against a compile-time `metadata(64·j, f0, f1)` constant, one instruction per block.

The metadata is packed as `counter:u64 | f0:u32 | f1:u32`, little-endian, into one memory cell the instruction reads, like every other operand. With compile-time keywords that cell is one pooled `SET`: a frame emits it once per distinct metadata value, however many compressions read it, and the immediate that wrote it is public bytecode. There is no block-length field: the counter is what states how many of the 64 bytes are message, so only the last block may be partial and the program must zero-fill the bytes past its real length, which the compression circuit does not enforce. A multi-block hash therefore feeds each result back with `cv=`, advances `counter=` by the bytes actually absorbed, and sets `final=1` on the last block.

Operands are size-2 `StackBuf`s or 2-cell slices:

- an **input operand written as a list**, `blake2s([a, b], [c, d], out)`, names its two words directly and allocates nothing: the opcode addresses its four input chunks independently, so an operand whose words live in different places never has to be gathered into a consecutive run. This is the spelling to reach for instead of `p = StackBuf(2); p[0] = a; p[1] = b`;
- **stack operands** are read in place, at zero copies; a self-hash `blake2s(h, h, out)` names one 2-cell pair as both inputs;
- the instruction addresses its **four canonical 128-bit message chunks independently** (each is a full F192 memory cell constrained at this use to the BLAKE2s subspace `c2 = 0`), so an operand gathered into a buffer (`p = StackBuf(2); p[0] = t0; p[1] = t1; blake2s(p, …)`) costs one instruction per assembling store, which the list form above avoids entirely;
- the chaining value has only one opcode offset and therefore must be consecutive. If a 2-cell `cv` was assembled from non-adjacent copied cells, the compiler materializes those two cells into a fresh consecutive run;
- **heap slices** are still bridged through the stack for the *input pull* (the operand's words come from the heap): +1 `DEREF` per heap cell, and the output, if a heap slice, is stored after: write-once memory fills whichever side is unset.

If `out` was already written, the statement *asserts* the digest equals it, write-once turning the hash into a verification, which is exactly what a signature verifier wants.

The compression, including its chaining value and metadata, is proven by the flock-derived BLAKE2s R1CS (`crates/flock`, see `doc.pdf` §BLAKE2s); one instruction is one 64-byte-block compression.

## Hints: `hint_witness(dest, "name")`

```python
sb = StackBuf(2)
hint_witness(sb, "r")        # fill the whole StackBuf
hint_witness(hb[0:3], "h")   # or any StackBuf/HeapBuf slice (any length)
assert log(sb[0]) < 8        # hinted values are UNCONSTRAINED: pin them down
```

A single hinted value needs no destination at all:

```python
m = hint_witness("m")        # one value, bound to a name
assert log m < 8             # still unconstrained: pin it
```

which is the one-line form of allocating a `StackBuf(1)`, filling a slice of it, and reading the cell back out, and costs exactly the same (nothing). Everything below about a stream's entries applies to it: each such binding pops one entry, whose length must be 1.

Prover-supplied data (leanVM's `hint_witness`): a stream is a sequence of **entries**, one slice of values per `hint_witness` call, and the same symbol may be hinted many times. Each call pops the stream's next entry (whose length must match the destination run) and writes it into `dest` through the hint mechanism, at **zero cycles**. The values are completely unconstrained; the program must constrain them itself (asserts, range checks, hashes): an unconstrained hint consumed by anything security-relevant is a critical vulnerability. Runtime-start heap slices (`buf[i:i + k]`, `k` a literal) work too.

The prover supplies streams with `program.set_witness("name", entries)` (`Vec<Vec<extension-field>>`); test programs declare them as annotations, one line per entry, and repeated lines with the same name are its successive entries:

```python
# witness r: GEN ** 5, 12
# witness r: 9
```

### Computed-advice hints

Three builtins have the prover compute the values at witness generation instead of popping a stream entry. Like `hint_witness`, the results are completely unconstrained: the program must re-verify them in-circuit.

- `hint_decompose_bits(bits, value, nbits)`: writes the low `nbits` bits of `value` into the buffer `bits`, one field element (`0`/`1`) per bit.
- `hint_decompose_bits_exponent(bits, x, nbits)`: writes the `nbits` bits of the exponent `n` where `x = GEN ** n` into `bits` (a bounded dlog at witness generation).
- `g = hint_log2_ceil(bits, nbits, floor)`: returns `GEN ** log2_ceil(v)` for the value `v` held bitwise in the `nbits`-bit buffer `bits`, floored at `floor`.

`bits` is a `HeapBuf` or a `StackBuf` (of at least `nbits` cells). Prefer the `StackBuf`: a frame cell is addressed directly, so `bits[i]` at a compile-time index is free where a heap read is a `DEREF`, and the booleanity pin `bits[i] = b * b` is then one `MUL` rather than a `MUL` and a `DEREF`. Use `addr` below where the run must also be indexed at runtime or reached from elsewhere.

## Cost cheat sheet

| construct | instructions |
|---|---|
| `x = <literal>` / `GEN ** k` | 1 `SET` |
| `a + b` | 1 `XOR` |
| `a * b` | 1 `MUL` |
| `a / b` | 1 `MUL` (write-once back-solve; division by zero is undefined) |
| heap read / store `buf[i]` | 1 `DEREF`; +1 `MUL` for a *runtime* index (a compile-time g-power offset folds into the `DEREF`, for free) |
| stack read `sa[k]` | 0 (direct cell addressing); a *store* is 1, like any other write |
| `assert a == b` | 1 (+ 1 `SET` amortized per frame for the zero cell) |
| `assert a != b` | 3 (`XOR`, `MUL`, `SET`), no branch, one hinted inverse |
| `assert log x < k` | 3 (+1 `SET` amortized per bound per frame; a runtime bound costs 1 `MUL` instead) |
| `if a == b: …` | 3 (+2 to skip a non-empty `else`; +2 amortized `self-fp` per branching function); **0 if the condition is compile-time** |
| `… = match(log(x), …)` | ≈ 7 for the dispatch + the arm; results written into the targets directly. Uniform-call arms (`lambda k: f(a, b, k)`) **fuse**: one shared frame + dispatch to entry, each arm just `SET`+`JUMP` |
| function call | ≈ `n_args + n_returns + 4` (0 when the callee is `@inline`) |
| `mul_range` iteration | body + ≈ 1 `MUL` + 1 `XOR` + call overhead |
| `unroll` iteration | body only (compile-time replication) |
| `blake2s(a, b, out, ...)` | 1; plus one `SET` once per frame per distinct metadata value (nothing with `md=`, which costs whatever building the word costs), and two more when `cv` is omitted; message/CV words are read in place, +1 `DEREF` per heap input or CV word, +1 `MUL` per runtime slice start |
| `hint_witness(dest, "name")` | 0 (+1 `MUL` for a runtime slice start) |

Every cost above is the FIRST occurrence. Two identical pure operations in one function share one cell and the second is free, so `hb[i]` twice, or `row[i]` where `row = hb * GEN ** 2`, costs one pointer `MUL` between them. The sharing stops at a branch: a cell whose instruction sits inside an `if` is not reused after the join, because the other path leaves it unwritten and therefore prover-chosen.

## Example

Fibonacci in the exponent (`tests/programs/fibonacci.py`): `fib[g^k]` holds `GEN ** F_k`, so one field `MUL` is one Fibonacci step.

```python
# public_input: GEN ** 89, GEN ** 89
from snark_lib import *


def main():
    fib = HeapBuf(12)
    fib[1] = GEN ** 0  # F_0 = 0
    fib[GEN] = GEN     # F_1 = 1
    for i in mul_range(1, GEN ** 10):
        fib[i * GEN * GEN] = fib[i] * fib[i * GEN]
    out = fib[GEN ** 11]
    assert out == GEN ** 89  # F_11 = 89
    assert log(out) < log(GEN ** 128)
    p = GEN ** 0
    p[1] = out
    p[GEN] = out
    return
```

## Not (yet) supported

Mutable variables; conditions other than field (in)equality; `match` default and non-contiguous arms; multi-file imports; `Const` parameters as `mul_range` or range-check bounds (a substituted literal is a bit-pattern element, not the g-power a bound needs); runtime slice starts on a `StackBuf`; precompiles beyond `BLAKE2s`.
