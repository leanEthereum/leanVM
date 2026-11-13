/-
  LeanVM.Guest.B1.Bits.QueryWindowsT

  The template of `decode_query_windows`: its core IR at every depth and cap depth, generated as
  the expansion numbers it.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.WalkWindows

/-!
# The template of `decode_query_windows` (`crates/rec_aggregation/guests/lean_ethereum.py`)

`decode_query_windows(word, positions, win_ptrs, tabs, d, cd)` hints the squeezed word's bits in
windows: each of the `128 / d` positions `j` (from bit `j·d`) in `qwN d cd` windows (`qwWin`: the
path bits six at a time from the bottom, the last path window the remainder, the cap child bit,
the cap parent index), each hinted as `g^n` into the frame run `wins` (cells `5 ..`, its address
at `4`), range checked below `2^w` and read back as `n`'s bit pattern through the table `tabs`
(`tabs[g^n] = n`), shifted to its place (`COORD_BASIS[off]`) and summed into the position's low
run (below the next limb boundary `cut`) or high run. A window crossing the boundary is split
(`query_window_split`): its two runs hinted apart into fresh cells, each range checked and read
back, and joined in the exponent into its `wins` cell. Each position is stored at `positions[j]`,
the pointer to the `wins` run from its first window (`addr` of the run's tail) at `win_ptrs[j]`, and the word is
rebuilt from the positions and 7-bit windows of the bits above them (`qwRest`).

`qwBody d cd` is the expansion, value by value; `QueryWindowsData.lean` checks the 43
specializations against it by kernel evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest

@[expose] public section

/-- `COORD_BASIS[i]` as the data writes it. -/
def cbWord (i : ℕ) : E := word (2 ^ i % 2 ^ 64) (2 ^ i / 2 ^ 64 % 2 ^ 64)

/-- Window `i`'s value of the position `q`: its bits at the window's place. -/
def qwVal (d cd q i : ℕ) : ℕ := (q >>> (qwWin d cd i).1) % 2 ^ (qwWin d cd i).2

/-- `p` names a frame run of `n` cells holding `f`: every readable word at `p·g^i`, `i < n`, is
`f i` (`addr(run)`). -/
def FrameRun (rd : Reader) (p : E) (n : ℕ) (f : ℕ → E) : Prop :=
  IsInK p ∧ ∀ i < n, ∀ v, rd (p.limb 0 * Parameters.addressOfIndex i) = some v → v = f i

/-- The range check's bound for a window of `w` bits: `g^(2^w - 1)`. -/
def qwBound (w : ℕ) : E := E.ofLimbs (gpowK (2 ^ w - 1)) 0

/-- `x·COORD_BASIS[c]` from `k`, the unit factor folded: the statements, the next free value and
the product. -/
def qwScale (x : V) (c k : ℕ) : List Stmt × ℕ × V :=
  if c = 0 then ([], k, x)
  else ([.atom (.const (.n k) (cbWord c)), .atom (.mul (.n (k + 1)) x (.n k))], k + 2, .n (k + 1))

/-- `acc + t` from `k`, the zero sum folded. -/
def qwAcc (acc : Option V) (t : V) (k : ℕ) : List Stmt × ℕ × Option V :=
  match acc with
  | none => ([], k, some t)
  | some a => ([.atom (.add (.n k) a t)], k + 1, some (.n k))

/-- A window of `w` bits from bit `start` hinted into the cell `c` from `k`: the range check, the
table read. The statements, the next free value and the bit pattern's value. -/
def qwRead (c : V) (start w k : ℕ) : List Stmt × ℕ × V :=
  ([.atom (.hint (.windowsExp (.n 0) start w 1 (.stack [c]))),
    .atom (.const (.n k) (qwBound w)),
    .atom (.rangeCheck c (.n (k + 1)) (.n (k + 2)) (.n (k + 3)) (.n k)),
    .atom (.mul (.n (k + 4)) (.n 3) c), .atom (.load (.n (k + 5)) (.n (k + 4)) 0)],
    k + 6, .n (k + 5))

/-- The squares `x^(2^a)` from `k`: the statements and the result. -/
def qwSquares (x : V) : ℕ → ℕ → List Stmt × V
  | 0, _ => ([], x)
  | a + 1, k =>
    let r := qwSquares (.n k) a (k + 1)
    (.atom (.mul (.n k) x x) :: r.1, r.2)

/-- A window crossing the limb boundary `a` bits in, from `k` (`query_window_split`): the two
runs hinted into `k`, `k + 1`, range checked, joined into the `wins` cell `c`, read back. The
statements, the next free value, the low run's pattern and the high run's. -/
def qwSplit (c : V) (start a w k : ℕ) : List Stmt × ℕ × V × V :=
  let sq := qwSquares (.n (k + 1)) a (k + 10)
  ([.atom (.hint (.windowsExp (.n 0) start a 1 (.stack [.n k]))),
    .atom (.hint (.windowsExp (.n 0) (start + a) (w - a) 1 (.stack [.n (k + 1)]))),
    .atom (.const (.n (k + 2)) (qwBound a)),
    .atom (.rangeCheck (.n k) (.n (k + 3)) (.n (k + 4)) (.n (k + 5)) (.n (k + 2))),
    .atom (.const (.n (k + 6)) (qwBound (w - a))),
    .atom (.rangeCheck (.n (k + 1)) (.n (k + 7)) (.n (k + 8)) (.n (k + 9)) (.n (k + 6)))] ++
    sq.1 ++
    [.atom (.mul c (.n k) sq.2),
      .atom (.mul (.n (k + 10 + a)) (.n 3) (.n k)),
      .atom (.load (.n (k + 11 + a)) (.n (k + 10 + a)) 0),
      .atom (.mul (.n (k + 12 + a)) (.n 3) (.n (k + 1))),
      .atom (.load (.n (k + 13 + a)) (.n (k + 12 + a)) 0)],
    k + 14 + a, .n (k + 11 + a), .n (k + 13 + a))

/-- Window `i` of the position at bit `base` (limb boundary `cut` bits in, windows from `at0`), from
`k`, onto the runs' sums `lo`, `hi`. -/
def qwWindow (d cd base cut at0 i k : ℕ) (lo hi : Option V) :
    List Stmt × ℕ × Option V × Option V :=
  let off := (qwWin d cd i).1
  let w := (qwWin d cd i).2
  let c : V := .n (5 + at0 + i)
  if off + w ≤ cut then
    let r := qwRead c (base + off) w k
    let s := qwScale r.2.2 off r.2.1
    let a := qwAcc lo s.2.2 s.2.1
    (r.1 ++ s.1 ++ a.1, a.2.1, a.2.2, hi)
  else if off < cut then
    let r := qwSplit c (base + off) (cut - off) w k
    let s := qwScale r.2.2.1 off r.2.1
    let a := qwAcc lo s.2.2 s.2.1
    let b := qwAcc hi r.2.2.2 a.2.1
    (r.1 ++ s.1 ++ a.1 ++ b.1, b.2.1, a.2.2, b.2.2)
  else
    let r := qwRead c (base + off) w k
    let s := qwScale r.2.2 (off - cut) r.2.1
    let a := qwAcc hi s.2.2 s.2.1
    (r.1 ++ s.1 ++ a.1, a.2.1, lo, a.2.2)

/-- Windows `i ..< i + n` of a position. -/
def qwWindows (d cd base cut at0 : ℕ) : ℕ → ℕ → ℕ → Option V → Option V →
    List Stmt × ℕ × Option V × Option V
  | _, 0, k, lo, hi => ([], k, lo, hi)
  | i, n + 1, k, lo, hi =>
    let r := qwWindow d cd base cut at0 i k lo hi
    let rest := qwWindows d cd base cut at0 (i + 1) n r.2.1 r.2.2.1 r.2.2.2
    (r.1 ++ rest.1, rest.2)

/-- Position `j`'s store and its reconstruction term from `k` (`dqPr`), `recon` the sum so far. -/
def qwPr (j base cut d k : ℕ) (lo hi : V) (recon : Option V) : List Stmt × ℕ × Option V :=
  if cut < d then
    ([.atom (.const (.n k) (cbWord cut)), .atom (.mul (.n (k + 1)) (.n k) hi),
      .atom (.add (.n (k + 2)) lo (.n (k + 1))), .atom (.load (.n (k + 2)) (.n 1) j),
      .atom (.const (.n (k + 3)) (cbWord base)), .atom (.mul (.n (k + 4)) (.n (k + 3)) lo),
      .atom (.const (.n (k + 5)) (cbWord (base + cut))),
      .atom (.mul (.n (k + 6)) (.n (k + 5)) hi), .atom (.add (.n (k + 7)) (.n (k + 4)) (.n (k + 6))),
      .atom (.add (.n (k + 8)) (recon.getD (.n 0)) (.n (k + 7)))], k + 9, some (.n (k + 8)))
  else match recon with
    | none => ([.atom (.load lo (.n 1) j)], k, some lo)
    | some rc => ([.atom (.load lo (.n 1) j), .atom (.const (.n k) (cbWord base)),
        .atom (.mul (.n (k + 1)) (.n k) lo), .atom (.add (.n (k + 2)) rc (.n (k + 1)))],
        k + 3, some (.n (k + 2)))

/-- Position `j`'s window pointer from `k`: `addr` of the `wins` run from its first window on
(a shifted `addr` pointer is the `addr` of the run's tail). The statements, the next free value and
the pointer's value. -/
def qwPtr (j n k : ℕ) : List Stmt × ℕ × ℕ :=
  if j = 0 then ([.atom (.load (.n 4) (.n 2) 0)], k, 4) else
    ([.atom (.frameAddr (.n k) ((List.range (36 - j * n)).map fun i => .n (5 + j * n + i))),
      .atom (.load (.n k) (.n 2) j)], k + 1, k)

/-- Position `j` from `k`: its windows, store and reconstruction term, pointer. -/
def qwPos (d cd j k : ℕ) (recon : Option V) : List Stmt × ℕ × Option V :=
  let base := j * d
  let cut := 64 - base % 64
  let w := qwWindows d cd base cut (j * qwN d cd) 0 (qwN d cd) k none none
  let p := qwPr j base cut d w.2.1 (w.2.2.1.getD (.n 0)) (w.2.2.2.getD (.n 0)) recon
  let q := qwPtr j (qwN d cd) p.2.1
  (w.1 ++ p.1 ++ q.1, q.2.1, p.2.2)

/-- Positions `j ..< j + n`. -/
def qwPositions (d cd : ℕ) : ℕ → ℕ → ℕ → Option V → List Stmt × ℕ × Option V
  | _, 0, k, recon => ([], k, recon)
  | j, n + 1, k, recon =>
    let r := qwPos d cd j k recon
    let rest := qwPositions d cd (j + 1) n r.2.1 r.2.2
    (r.1 ++ rest.1, rest.2)

/-- The rest windows' count: 7-bit windows over the bits above the last position. -/
def qwRestN (d : ℕ) : ℕ := (128 - 128 / d * d + 6) / 7

/-- Rest window `i`'s start and width. -/
def qwRestWin (d i : ℕ) : ℕ × ℕ :=
  let start := 128 / d * d + 7 * i
  (start, if start + 7 ≤ 128 then 7 else 128 - start)

/-- Rest windows `i ..< i + n` from `k`, onto the reconstruction `recon`. -/
def qwRest (d : ℕ) : ℕ → ℕ → ℕ → Option V → List Stmt × ℕ × Option V
  | _, 0, k, recon => ([], k, recon)
  | i, n + 1, k, recon =>
    let r := qwRead (.n k) (qwRestWin d i).1 (qwRestWin d i).2 (k + 1)
    let s := qwScale r.2.2 (qwRestWin d i).1 r.2.1
    let a := qwAcc recon s.2.2 s.2.1
    let rest := qwRest d (i + 1) n a.2.1 a.2.2
    (r.1 ++ s.1 ++ a.1 ++ rest.1, rest.2)

/-- The `wins` frame run (`QUERY_WINDOWS_CAP = 36`): cells `5 .. 40`. -/
def qwRun : List V := (List.range 36).map fun i => .n (5 + i)

/-- **The expansion of `decode_query_windows__L{d}_L{cd}`.** -/
def qwBody (d cd : ℕ) : List Stmt :=
  let p := qwPositions d cd 0 (128 / d) 41 none
  let r := qwRest d 0 (qwRestN d) p.2.1 p.2.2
  [.atom (.frameAddr (.n 4) qwRun)] ++ p.1 ++ r.1 ++
    [.atom (.assertEq (r.2.2.getD (.n 0)) (.n 0)), .ret []]

/-- A core function of the name with the parameters `0 .. 3` and the body. -/
def QwIs (name : String) (body : List Stmt) : Prop :=
  ∃ fn, coreProgram.find? name = some fn ∧ fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = body

/-- The deployed specializations: `(name, depth, cap depth)`. -/
def queryWindowsShapes : List (String × ℕ × ℕ) :=
  [("decode_query_windows__L12_L6", 12, 6),
    ("decode_query_windows__L13_L7", 13, 7),
    ("decode_query_windows__L14_L2", 14, 2),
    ("decode_query_windows__L15_L3", 15, 3),
    ("decode_query_windows__L16_L4", 16, 4),
    ("decode_query_windows__L17_L5", 17, 5),
    ("decode_query_windows__L18_L6", 18, 6),
    ("decode_query_windows__L19_L7", 19, 7),
    ("decode_query_windows__L20_L2", 20, 2),
    ("decode_query_windows__L20_L8", 20, 8),
    ("decode_query_windows__L21_L3", 21, 3),
    ("decode_query_windows__L22_L4", 22, 4),
    ("decode_query_windows__L23_L5", 23, 5),
    ("decode_query_windows__L24_L6", 24, 6),
    ("decode_query_windows__L25_L7", 25, 7),
    ("decode_query_windows__L26_L2", 26, 2),
    ("decode_query_windows__L27_L3", 27, 3),
    ("decode_query_windows__L28_L4", 28, 4)]

end
end LeanVM.Guest.B1
