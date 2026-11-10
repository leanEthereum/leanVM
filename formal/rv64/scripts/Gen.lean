import Rv64Verifier.Sym.Facts
import Rv64Verifier.Image

/-!
# Block specifications of a function of the image, generated

  lake exe rv64-gen NAME OUT.lean      (NAME: a part of the function's name, or its index in `Image.functions`)

Splits the function of the image whose name contains `NAME` into basic blocks (leaders: its entry,
the targets of its branches and jumps that land inside it, and every instruction after a branch, a
jump or a call), runs the symbolic executor over each, and writes a module with, per block, its
`Expect` (the final pc, every register, every doubleword written with its value, every side
condition) and its `BlockSpec`, both checked by the kernel when the module builds, then a summary
of the block in a comment and lemmas that read its `Holds` in `rv_eval`'s normal form
(`Sym/Facts.lean`):

* `b<pc>_x<n>`: the final value of register `x<n>`, for each register the block changes;
* `b<pc>_keeps`: the registers it leaves unchanged;
* `b<pc>_m_x<n>_<off>` (or `b<pc>_m<i>`): each doubleword it writes, at its address;
* `b<pc>_pc`, or `b<pc>_pc_taken`/`b<pc>_pc_not_taken` under the branch's condition;
* `b<pc>_frame`: its writes lie in `[x<n> + lo, x<n> + hi)` (all at one register), as a
  `MemFrame`, given that the range does not wrap; `b<pc>_mem_same` if it writes nothing.

An expression outside the printable operations (or too long) gets no lemma; read it from the
`Expect` with `Expect.Holds.reg_eq` and `rv_eval`. The output is generated: regenerate it, never
edit it. Nothing here is trusted: a wrong expectation or lemma fails the module's build.
-/

open Rv64Verifier Rv64Verifier.Sym RiscvZkvm.Rv64

deriving instance Repr for Expect

def cfg : Config := { noAlias := true }

def maxBlock : Nat := 128

def allRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- The successors a control-flow instruction at `pc` names inside `[lo, hi)`, and whether the next
instruction starts a block. -/
def successors (pc : Word) (i : Instruction) : List Word × Bool :=
  match classify i with
  | some (.branch _ _ _ off) => ([pc + off, pc + 4], true)
  | some (.jal _ off) => ([pc + off], true)
  | some (.jalr ..) => ([], true)
  | _ => match i with
    | .base .ECALL | .base .EBREAK => ([], true)
    | _ => ([], false)

def leaders (code : Code) (lo hi : Word) : List Word := Id.run do
  let n := (hi.toNat - lo.toNat) / 4
  let mut ls : List Word := [lo]
  for k in List.range n do
    let pc := lo + BitVec.ofNat 64 (4 * k)
    match code.fetch pc with
    | none => ls := (pc + 4) :: ls
    | some i =>
      let (ts, next) := successors pc i
      for t in ts do
        if lo.toNat ≤ t.toNat ∧ t.toNat < hi.toNat then ls := t :: ls
      if next then ls := (pc + 4) :: ls
  return (ls.filter (fun a ↦ a.toNat < hi.toNat)).mergeSort (fun a b ↦ a.toNat ≤ b.toNat) |>.eraseDups

def fmt {α : Type} [Repr α] (a : α) : String :=
  "\n    ".intercalate ((repr a).pretty 100 |>.splitOn "\n")

def hex (w : Word) : String := String.ofList (Nat.toDigits 16 w.toNat)

/-! ## Printing expressions -/

def regName (r : Reg) : String := s!"x{r.toNat}"

/-- A numeral as one writes it: decimal when small, else hexadecimal. -/
def lit (n : Nat) : String :=
  if n < 65536 then toString n else "0x" ++ String.ofList (Nat.toDigits 16 n)

def isBin : E → Bool
  | .bin .. => true
  | _ => false

/-- `b + k` in the normal form: `b + k` or `b - k'` with `0 < k, k' < 2^63`, or `b`; the
constant typed when `ty`. -/
def affineT (ty : Bool) (b : String) (k : Nat) : String :=
  let k := k % 2 ^ 64
  let l (n : Nat) := if ty then s!"({lit n} : Word)" else lit n
  if k == 0 then b else if k < 2 ^ 63 then s!"{b} + {l k}" else s!"{b} - {l (2 ^ 64 - k)}"

def affine (b : String) (k : Nat) : String := affineT false b k

/-- `e` mixes operations beyond offsets: its numerals are printed typed, or Lean's elaboration of
the mixed tree would coerce some of them from `Nat`. -/
partial def mixed : E → Bool
  | .ld a => mixed a
  | .bin .add a (.c _) | .bin .sub a (.c _) => mixed a
  | .bin _ _ _ => true
  | _ => false

/-- `e` as Lean syntax over the initial state `s`, in `rv_eval`'s normal form, or `none` if it
uses an operation outside the printable ones. -/
partial def leanE' (ty : Bool) (e : E) : Option String := do
  let par (e : E) : Option String := do
    let x ← leanE' ty e
    return if isBin e then s!"({x})" else match e with
      | .c _ => s!"({x} : Word)"
      | _ => x
  match e with
  | .c v => return lit v.toNat
  | .reg r => return s!"s.getReg .{regName r}"
  | .ld a => return s!"s.getMem ({← leanE' ty a})"
  | .bin .add (.c _) (.c _) => none
  | .bin .sub (.c _) (.c _) => none
  | .bin .add a (.c k) => return affineT ty (← par a) k.toNat
  | .bin .sub a (.c k) => return affineT ty (← par a) (2 ^ 64 - k.toNat)
  | .bin .sll a (.c k) => return s!"{← par a} * ({lit (2 ^ (k.toNat % 64) % 2 ^ 64)} : Word)"
  | .bin .srl a (.c k) => return s!"{← par a} >>> {k.toNat % 64}"
  | .bin op a b => do
    let sym ← match op with
      | .add => some "+" | .sub => some "-" | .xor => some "^^^" | .and => some "&&&"
      | .or => some "|||" | .mul => some "*" | _ => none
    return s!"{← par a} {sym} {← par b}"
  | _ => none

def leanE (e : E) : Option String := leanE' (mixed e) e

/-- `e` for a reader: registers by name, loads in brackets. -/
partial def shortE : E → String
  | .c v => lit v.toNat
  | .reg r => regName r
  | .ld a => s!"[{shortE a}]"
  | .un op a => s!"{repr op}({shortE a})"
  | .bin op a b =>
    let par (e : E) := if isBin e then s!"({shortE e})" else shortE e
    match op, b with
    | .add, .c k => affine (par a) k.toNat
    | .sub, .c k => affine (par a) (2 ^ 64 - k.toNat)
    | _, _ =>
      let sym := match op with
        | .add => "+" | .sub => "-" | .xor => "^^^" | .and => "&&&" | .or => "|||" | .mul => "*"
        | .sll => "<<<" | .srl => ">>>" | .sra => ">>>ₛ" | .sltu => "<ᵤ" | .slt => "<ₛ"
        | op => s!"{repr op}"
      s!"{par a} {sym} {par b}"
  | .ite op x y a b =>
    let sym := match op with
      | .eq => "=" | .ne => "≠" | .lt => "<ₛ" | .ge => "≥ₛ"
      | .ltu => "<ᵤ" | .geu => "≥ᵤ"
    s!"if {shortE x} {sym} {shortE y} then {shortE a} else {shortE b}"

def clip (s : String) : String := if s.length ≤ 160 then s else (s.take 157).toString ++ "..."

def addrE (k : Addr) : E := match k.base with
  | none => .c k.off
  | some b => .bin .add b (.c k.off)

/-- The register and signed offset of an address `x<n> + off`. -/
def regOff (k : Addr) : Option (Reg × Int) := match k.base with
  | some (.reg r) =>
    some (r, if k.off.toNat < 2 ^ 63 then k.off.toNat else (k.off.toNat : Int) - 2 ^ 64)
  | _ => none

/-- The branch conditions of `if op x y` as propositions, taken and not taken, with proofs of
the executor's condition (`= true`) and of its negation from them (`hc`). -/
def conds (op : CmpOp) (x y : String) : (String × String) × (String × String) :=
  match op with
  | .eq => ((s!"{x} = {y}", "beq_iff_eq.mpr hc"),
      (s!"{x} ≠ {y}", "fun h ↦ hc (beq_iff_eq.mp h)"))
  | .ne => ((s!"{x} ≠ {y}", "bne_iff_ne.mpr hc"), (s!"{x} = {y}", "fun h ↦ bne_iff_ne.mp h hc"))
  | .ltu => ((s!"({x}).toNat < ({y}).toNat", "decide_eq_true hc"),
      (s!"({y}).toNat ≤ ({x}).toNat", "fun h ↦ Nat.not_lt.mpr hc (of_decide_eq_true h)"))
  | .geu => ((s!"({y}).toNat ≤ ({x}).toNat",
        "bnot_of_false (decide_eq_false (Nat.not_lt.mpr hc))"),
      (s!"({x}).toNat < ({y}).toNat", "fun h ↦ of_decide_eq_false (false_of_bnot h) hc"))
  | .lt => ((s!"BitVec.slt ({x}) ({y}) = true", "hc"),
      (s!"BitVec.slt ({x}) ({y}) = false", "fun h ↦ Bool.false_ne_true (hc.symm.trans h)"))
  | .ge => ((s!"BitVec.slt ({x}) ({y}) = false", "bnot_of_false hc"),
      (s!"BitVec.slt ({x}) ({y}) = true",
        "fun h ↦ Bool.false_ne_true ((false_of_bnot h).symm.trans hc)"))

def maxLemma : Nat := 400

/-- The summary and the reading lemmas of block `name` with expectation `x`. -/
def lemmas (name : String) (pc : Word) (x : Expect) : String := Id.run do
  let hd := s!"theorem {name}"
  let hs := s!"\{s t : MachineState} (h : {name}.Holds s t)"
  let changed := x.regs.filter fun p ↦ !E.beq p.2 (.reg p.1)
  let kept := x.regs.filter fun p ↦ E.beq p.2 (.reg p.1)
  -- the summary
  let mut sum := s!"/- 0x{hex pc}: {x.steps} steps, then pc := {clip (shortE x.pc)}\n"
  for (r, e) in changed do sum := sum ++ s!"     {regName r} := {clip (shortE e)}\n"
  for (k, v) in x.mem do sum := sum ++ s!"     [{shortE (addrE k)}] := {clip (shortE v)}\n"
  unless x.obl.isEmpty do
    let os := x.obl.map fun
      | .valid k w => s!"valid{w} {shortE (addrE k)}"
      | .align8 b => s!"aligned8 {shortE b}"
      | .ne a b => s!"{shortE (addrE a)} ≠ {shortE (addrE b)}"
    sum := sum ++ s!"     needs {clip (", ".intercalate os)}\n"
  let mut out := sum ++ "-/\n\n"
  -- registers
  for (r, e) in changed do
    if let some v := leanE e then
      if v.length ≤ maxLemma then
        out := out ++ s!"{hd}_{regName r} {hs} :\n    t.getReg .{regName r} = {v} :=\n" ++
          s!"  h.reg_eq .{regName r} rfl (by rv_eval [])\n\n"
  unless kept.isEmpty do
    let rs := ", ".intercalate (kept.map fun p ↦ s!".{regName p.1}")
    out := out ++
      s!"{hd}_keeps {hs} :\n    ∀ r ∈ ([{rs}] : List Reg), t.getReg r = s.getReg r :=\n" ++
      "  h.keeps rfl\n\n"
  -- written doublewords
  for ((k, v), i) in x.mem.zipIdx do
    let tag := match regOff k with
      | some (r, o) => s!"m_{regName r}_" ++ (if o < 0 then s!"n{-o}" else s!"{o}")
      | none => s!"m{i}"
    if let (some a, some v) := (leanE (addrE k), leanE v) then
      if v.length ≤ maxLemma then
        out := out ++ s!"{hd}_{tag} {hs} :\n    t.getMem ({a}) = {v} :=\n" ++
          s!"  h.mem_eq {i} (by decide) (by rv_eval []) (by rv_eval [])\n\n"
  -- the pc
  match x.pc with
  | .c v => out := out ++ s!"{hd}_pc {hs} : t.pc = {lit v.toNat} :=\n  h.pc_eq rfl\n\n"
  | .ite op a b (.c u) (.c v) =>
    let ty := mixed a || mixed b
    let typed (e : E) : Option String := match e with
      | .c v => some s!"({lit v.toNat} : Word)"
      | e => leanE' ty e
    if let (some a, some b) := (typed a, typed b) then
      let ((yes, pyes), (no, pno)) := conds op a b
      out := out ++ s!"{hd}_pc_taken {hs} (hc : {yes}) :\n    t.pc = {lit u.toNat} :=\n" ++
        s!"  h.pc_eq (by rv_eval []; exact ite_eq_left_of_eq_true _ _ (eq_true ({pyes})))\n\n"
      out := out ++ s!"{hd}_pc_not_taken {hs} (hc : {no}) :\n    t.pc = {lit v.toNat} :=\n" ++
        s!"  h.pc_eq (by rv_eval []; exact ite_eq_right_of_eq_false _ _ (eq_false ({pno})))\n\n"
  | e =>
    if let some v := leanE e then
      out := out ++ s!"{hd}_pc {hs} :\n    t.pc = {v} :=\n  h.pc_eq (by rv_eval [])\n\n"
  -- the frame
  if x.writes.isEmpty then
    out := out ++ s!"{hd}_mem_same {hs} (a : Word) : t.getMem a = s.getMem a :=\n" ++
      "  h.mem_same rfl a\n\n"
  else
    let ros := x.writes.filterMap regOff
    if let (r, o) :: _ := ros then
      if ros.length == x.writes.length && ros.all (fun p ↦ p.1 == r) then
        let lo := (ros.map (·.2)).foldl min o
        let hi := (ros.map (·.2)).foldl max o + 8
        let base := s!"s.getReg .{regName r}"
        let b := s!"(s.getReg .{regName r}).toNat"
        let lower := if lo < 0 then [s!"{-lo} ≤ {b}"] else []
        let upper := if hi > 0 then [s!"{b} + {hi} ≤ 2 ^ 64"] else []
        let hb := " ∧ ".intercalate (lower ++ upper)
        let loS := affine base (if lo < 0 then (2 ^ 64 + lo).toNat else lo.toNat)
        out := out ++
          s!"{hd}_frame {hs} (hb : {hb}) :\n    MemFrame s t ({loS}) {(hi - lo).toNat} :=\n" ++
          s!"  h.memFrame (by rv_eval []; and_intros <;> addr_omega [hb])\n\n"
  return out

def block (code : Code) (pc : Word) (n : Nat) : Except String String := do
  let i := (pc.toNat - code.base.toNat) / 4
  let words := (code.words.drop i).take n
  let some r := symRun cfg words pc n | throw s!"symbolic execution failed in the block at 0x{hex pc}"
  let mut obl := r.st.obl
  let mut mem : List (Addr × E) := []
  for (k, _) in r.st.mem do
    match readMem cfg k r.st.mem with
    | some (v, os) => mem := mem ++ [(k, v)]; obl := obl ++ os
    | none => throw s!"unreadable write in the block at 0x{hex pc}"
  let x : Expect := {
    steps := r.steps, pc := r.pc, regs := allRegs.map (fun reg ↦ (reg, r.st.regs.get reg)),
    mem := mem, writes := r.st.mem.map Prod.fst, obl := Oblig.dedup obl }
  let name := s!"b{hex pc}"
  return s!"def {name} : Expect :=\n  {fmt x}\n\n" ++
    s!"theorem {name}_spec : BlockSpec Image.code {fmt pc} {r.steps}\n" ++
    s!"    (fun s ↦ Oblig.all s {name}.obl) {name}.Holds :=\n" ++
    s!"  BlockSpec.of_expect (cfg := cfg) (fuel := {n}) (x := {name})\n" ++
    s!"    (words := (Image.code.words.drop {i}).take {n}) (by decide +kernel)\n" ++
    s!"    (CodeAt.slice Image.code {i} {n} {fmt pc} (by decide +kernel) (by decide +kernel)\n" ++
    s!"      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)\n\n" ++
    lemmas name pc x

def main (args : List String) : IO UInt32 := do
  let [pat, out] := args | IO.eprintln "usage: rv64-gen NAME OUT.lean"; return 2
  let found := match pat.toNat? with
    | some i => (Image.functions[i]?).toList
    | none => Image.functions.filter (fun f ↦ (f.1.splitOn pat).length > 1)
  let [(name, lo, size)] := found
    | IO.eprintln s!"{found.length} functions match {pat}: {found.map (·.1)}"; return 2
  let hi := lo + BitVec.ofNat 64 size
  -- Long straight-line runs split every `maxBlock` instructions: a block's kernel check grows
  -- faster than its length.
  let ls0 := leaders Image.code lo hi
  let ls := (ls0.zip (ls0.drop 1 ++ [hi])).flatMap fun (a, b) ↦
    (List.range ((b.toNat - a.toNat - 1) / 4 / maxBlock + 1)).map fun j ↦
      a + BitVec.ofNat 64 (4 * maxBlock * j)
  let mut body := ""
  for (a, b) in ls.zip (ls.drop 1 ++ [hi]) do
    -- A block runs up to its first word that does not decode (`unimp`, the panic paths' trap):
    -- the machine traps there, and a trap is not a step.
    let n := ((List.range ((b.toNat - a.toNat) / 4)).takeWhile fun k ↦
      (Image.code.fetch (a + BitVec.ofNat 64 (4 * k))).isSome).length
    if n == 0 then
      body := body ++ s!"-- 0x{hex a}: a word that does not decode; the machine traps here.\n\n"
      continue
    match block Image.code a n with
    | .ok s => body := body ++ s
    | .error e => IO.eprintln e; return 1
  let ns := s!"Rv64Verifier.Blocks.{((out.splitOn "/").getLast!.dropEnd 5).toString}"
  let header := s!"-- Generated by `lake exe rv64-gen` from `{name}` ({size} bytes at 0x{hex lo}, " ++
    s!"{ls.length} blocks). Do not edit.\n\nimport Rv64Verifier.Sym.Facts\nimport Rv64Verifier.Image\n\n" ++
    s!"namespace {ns}\n\nopen Rv64Verifier Rv64Verifier.Sym RiscvZkvm.Rv64\n\n" ++
    "def cfg : Config := { noAlias := true }\n\n"
  IO.FS.writeFile out (header ++ body ++ s!"end {ns}\n")
  IO.println s!"{name}: {ls.length} blocks -> {out}"
  return 0
