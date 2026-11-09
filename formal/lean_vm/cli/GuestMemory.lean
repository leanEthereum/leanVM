import LeanVM.Guest.Data.Source
import LeanVM.Guest.Expand
import LeanVM.Guest.Renumber
import LeanVM.Guest.Memory.Fresh
import LeanVM.Guest.Memory.Tree
import LeanVM.Guest.Memory.SizeTotal

/-!
# `guest-memory`: the guest's kernel-checked memory-layer facts

`lake exe guest-memory` writes three families of kernel checks about the guest's core IR
(`coreProgram`, computed here as `guest-core` computes it: `Expand.expandProgram Data.guest`,
renumbered):

* `LeanVM/Guest/Memory/GuestFresh*`: `coreProgram_fresh : coreProgram.Fresh`, every function's
  range-check temporaries fresh (`Fn.freshB` on ranges of functions, `FreshRange`; a function too
  large for one check by ranges of its statements, `RangeFresh`);
* `LeanVM/Guest/Memory/GuestWf*`: `coreProgram_wf : coreProgram.Wf` (`Stmt.wfList` on ranges of
  functions, `WfRange`; a function too large by ranges of its statements, `WfStmts`);
* `LeanVM/Guest/Memory/GuestMainFree*`: `coreProgram_callsIn_noMain`, no function calls `main`
  (`Stmt.blockCallees` on ranges of functions, `MainFreeRange`).

The ranges are cut by an estimate of their kernel cost (`freshCost`, `wfCost`) and spread over
modules of a few checks each, which build in parallel. `--check` writes nothing and fails when a
file differs; `--stats` prints the costs. Run it from `lean_vm`.
-/

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

namespace GuestMemory

def memDir : System.FilePath := "LeanVM/Guest/Memory"

/-! ## Costs -/

mutual
def callIfs : Stmt → Nat
  | .ite _ z n => callIfsList z + callIfsList n
  | .match_ _ arms => callIfsArms arms
  | .callIf .. => 1
  | _ => 0
def callIfsList : List Stmt → Nat
  | [] => 0
  | s :: ss => callIfs s + callIfsList ss
def callIfsArms : List (List Stmt) → Nat
  | [] => 0
  | a :: as => callIfsList a + callIfsArms as
end

mutual
def stmtCount : Stmt → Nat
  | .ite _ z n => 1 + stmtCountList z + stmtCountList n
  | .match_ _ arms => 1 + stmtCountArms arms
  | _ => 1
def stmtCountList : List Stmt → Nat
  | [] => 0
  | s :: ss => stmtCount s + stmtCountList ss
def stmtCountArms : List (List Stmt) → Nat
  | [] => 0
  | a :: as => stmtCountList a + stmtCountArms as
end

/-- The largest index a list of values names. -/
def maxIdx (vs : List V) : Nat := vs.foldl (fun m v => max m v.idx) 0

/-- The kernel cost of `Fn.freshB`-style checks of statements: the values they name (the size of
the terms the kernel unfolds), weighted up by the words of the masks past `2^16` values. -/
def freshCost (ss : List Stmt) (params : List V) : Nat :=
  let us := Stmt.usesList ss ++ params
  let ts := Stmt.tmpsList ss
  (us.length + ts.length + stmtCountList ss) * (maxIdx (us ++ ts) / 65536 + 1)

/-- The kernel cost of `Stmt.wfList` on statements: their statements, and a callee lookup over
the whole program per `callIf`. -/
def wfCost (n : Nat) (ss : List Stmt) : Nat := stmtCountList ss + n * callIfsList ss

/-- One freshness declaration's cost at most this (`freshCost` units). -/
def freshBudget : Nat := 25000

/-- One well-formedness declaration's cost at most this (`wfCost` units, a callee lookup about a
millisecond of the kernel per function of the program). -/
def wfBudget : Nat := 15000

/-- A range holds at most this many functions. -/
def maxFns : Nat := 150

/-- A module holds at most this many declarations, so that its kernel checks stay short. -/
def declsPerModule : Nat := 6

/-! ## Ranges -/

/-- Cut `0 .. costs.length` into ranges of cost at most `budget`, a range of one item if it alone
exceeds it: `(start, length, cost)`. -/
def cut (costs : Array Nat) (budget : Nat) (lo hi : Nat) : List (Nat × Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat × Nat) := #[]
  let mut a := lo
  let mut fuel := hi - lo + 1
  while a < hi && fuel > 0 do
    fuel := fuel - 1
    let mut n := 1
    let mut w := costs[a]!
    while a + n < hi && n < maxFns && w + costs[a + n]! ≤ budget do
      w := w + costs[a + n]!
      n := n + 1
    out := out.push (a, n, w)
    a := a + n
  return out.toList

/-- Group declarations into modules, at most `budget` of cost and `declsPerModule` each. -/
def modules {α : Type} (budget : Nat) (items : List (α × Nat)) : List (List α) := Id.run do
  let mut out : Array (List α) := #[]
  let mut cur : Array α := #[]
  let mut w := 0
  for (x, c) in items do
    if !cur.isEmpty && (w + c > budget || cur.size ≥ declsPerModule) then
      out := out.push cur.toList
      cur := #[]
      w := 0
    cur := cur.push x
    w := w + c
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList

def lst (l : List Nat) : String := s!"[{", ".intercalate (l.map toString)}]"

/-- A long list literal as `::` (elaborated without nested `have`s). -/
def natList (l : List Nat) : String :=
  if l.length < 32 then lst l else s!"({" :: ".intercalate (l.map toString)} :: [])"

def pad2 (k : Nat) : String := if k < 10 then s!"0{k}" else toString k

/-! ## Files -/

structure Out where
  files : Array (System.FilePath × String) := #[]

def header (name doc : String) : String :=
  s!"/-\n  {name}\n\n  Generated by `lake exe guest-memory` (lean_vm/cli/GuestMemory.lean); do not edit.\n  {doc}\n-/\n\nmodule\n\n"

def nsOpen : String := "namespace LeanVM.Guest\n\nopen Core Memory\n\n@[expose] public section\n"

def nsClose : String := "\nend\nend LeanVM.Guest\n"

/-- The steps of a chain `h0 … hk` concatenating ranges `(start, length)` from `lo`. -/
def chain (pre what : String) (lo : Nat) (rs : List (Nat × Nat × String)) : List String × String × Nat :=
  Id.run do
    let mut steps : Array String := #[]
    let mut tot := 0
    let mut i := 0
    let mut last := ""
    for (a, n, proof) in rs do
      if i == 0 then
        steps := steps.push s!"  have {pre}{i} : {what} {lo} {n} := {proof}"
      else
        steps := steps.push
          s!"  have {pre}{i} : {what} {lo} {tot + n} :=\n    {pre}{i - 1}.append' ({proof}) rfl rfl"
      tot := tot + n
      last := s!"{pre}{i}"
      i := i + 1
      let _ := a
    return (steps.toList, last, tot)

/-! ### Freshness -/

/-- The functions checked by ranges, and those too large for one check (by their statements),
for the checks that unfold the functions' bodies (freshness, the temporaries' cells). -/
def freshPlan (P : Program) : List (Nat × Nat × Nat) × List Nat :=
  let costs := (P.map fun fn => freshCost fn.body fn.params).toArray
  let big := (List.range P.length).filter fun j => costs[j]! > freshBudget
  -- the small functions' ranges, between the big ones
  let bounds := (0 :: big.map (· + 1)).zip (big ++ [P.length])
  (bounds.flatMap fun (lo, hi) => cut costs freshBudget lo hi, big)

def freshFiles (P : Program) : Array (System.FilePath × String) := Id.run do
  let (small, big) := freshPlan P
  let mut files : Array (System.FilePath × String) := #[]
  files := files.push (memDir / "GuestFresh" / "Range.lean", header "LeanVM.Guest.Memory.GuestFresh.Range"
    "Ranges of the guest's core IR whose range-check temporaries the kernel checks fresh." ++
    "public import LeanVM.Guest.Memory.Fresh\npublic import LeanVM.Guest.CoreData\n\n" ++ nsOpen ++ "
/-- The `n` functions of `coreProgram` from its `a`-th have fresh temporaries, decided. -/
def FreshRange (a n : ℕ) : Prop :=
  ((coreProgram.drop a).take n).all (fun fn => fn.freshB) = true

/-- The `n` functions of `coreProgram` from its `a`-th have fresh temporaries. -/
def FreshOn (a n : ℕ) : Prop := ∀ fn ∈ (coreProgram.drop a).take n, fn.Fresh

theorem FreshRange.on {a n : ℕ} (h : FreshRange a n) : FreshOn a n := by
  intro fn hfn
  unfold FreshRange at h
  rw [List.all_eq_true] at h
  exact fn_fresh_of_freshB (h fn hfn)

theorem freshOn_one {j : ℕ} {fn : Fn} (hj : coreProgram[j]? = some fn) (h : fn.Fresh) :
    FreshOn j 1 := by
  intro fn' hfn
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons, List.take_zero,
    List.mem_singleton] at hfn
  exact hfn ▸ h

/-- Two adjacent ranges are one. -/
theorem FreshOn.append' {a n m b k : ℕ} (h : FreshOn a n) (h' : FreshOn b m)
    (hb : a + n = b) (hk : n + m = k) : FreshOn a k := by
  subst hb hk
  intro fn hfn
  rw [List.take_add, List.mem_append, List.drop_drop] at hfn
  exact hfn.elim (h fn) (h' fn)

theorem fresh_of_freshOn (h : FreshOn 0 coreProgram.length) : coreProgram.Fresh := by
  intro fn hfn
  exact h fn (by rw [List.drop_zero, List.take_length]; exact hfn)
" ++ nsClose)
  -- small ranges
  let decls := small.map fun (a, n, w) =>
    (s!"\nset_option maxRecDepth 100000 in\ntheorem freshRange_{a} : FreshRange {a} {n} := by\n  unfold FreshRange; decide +kernel\n", w)
  let mods := modules (4 * freshBudget) decls
  let mut imports : Array String := #[]
  for (m, k) in mods.zipIdx do
    let nm := s!"Part{pad2 k}"
    imports := imports.push s!"public import LeanVM.Guest.Memory.GuestFresh.{nm}\n"
    files := files.push (memDir / "GuestFresh" / s!"{nm}.lean",
      header s!"LeanVM.Guest.Memory.GuestFresh.{nm}" "Kernel checks of freshness on ranges of the guest's functions." ++
      "public import LeanVM.Guest.Memory.GuestFresh.Range\n\n" ++ nsOpen ++ String.join m ++ nsClose)
  -- big functions, by ranges of statements
  for j in big do
    let fn := P[j]!
    let body := fn.body.toArray
    let scosts := body.map fun s => freshCost [s] []
    let rngs := cut scosts freshBudget 0 body.size
    let tsOf := fun (a n : Nat) => (Stmt.tmpsList ((fn.body.drop a).take n)).map V.idx
    let allT := (Stmt.tmpsList fn.body).map V.idx
    files := files.push (memDir / "GuestFresh" / s!"Temps{j}.lean",
      header s!"LeanVM.Guest.Memory.GuestFresh.Temps{j}" s!"The temporaries of `{fn.name}`'s range checks." ++
      "public import LeanVM.Guest.Memory.GuestFresh.Range\n\n" ++ nsOpen ++
      s!"\nset_option maxRecDepth 100000 in\n/-- The temporaries of `{fn.name}`'s range checks, in order. -/\ndef temps{j} : List ℕ := {natList allT}\n" ++ nsClose)
    let rdecls := rngs.map fun (a, n, w) =>
      (s!"\nset_option maxRecDepth 100000 in\n/-- The temporaries of statements `{a}` to `{a + n - 1}`. -/\ndef ts{j}_{a} : List ℕ := {natList (tsOf a n)}\n" ++
        s!"\nset_option maxRecDepth 100000 in\ntheorem fresh{j}_{a} : RangeFresh ((Data.core{j}.body.drop {a}).take {n}) ts{j}_{a} temps{j} := by\n  unfold RangeFresh ts{j}_{a}; decide +kernel\n", w)
    let rmods := modules (4 * freshBudget) rdecls
    let mut names : Array String := #[]
    for (m, k) in rmods.zipIdx do
      let nm := s!"Big{j}_{k}"
      names := names.push nm
      files := files.push (memDir / "GuestFresh" / s!"{nm}.lean",
        header s!"LeanVM.Guest.Memory.GuestFresh.{nm}" s!"Kernel checks of freshness on ranges of `{fn.name}`'s statements." ++
        s!"public import LeanVM.Guest.Memory.GuestFresh.Temps{j}\n\n" ++ nsOpen ++ String.join m ++ nsClose)
    -- assembly, from the end, a theorem a step
    let mut steps : Array String :=
      #[s!"\nset_option maxRecDepth 100000 in\ntheorem from{j}_{body.size} : RangeFresh (Data.core{j}.body.drop {body.size}) [] temps{j} :=\n  rangeFresh_end (l := Data.core{j}.body) (by decide +kernel) temps{j}\n"]
    let mut prev := body.size
    let mut suffix : String := "[]"
    for (a, n, _) in rngs.reverse do
      let prevSuffix := suffix
      suffix := s!"ts{j}_{a} ++ {suffix}"
      steps := steps.push s!"\ntheorem from{j}_{a} : RangeFresh (Data.core{j}.body.drop {a}) ({suffix}) temps{j} :=\n  rangeFresh_drop (l := Data.core{j}.body) (a := {a}) (n := {n}) (ts := ts{j}_{a}) (ts' := {prevSuffix}) fresh{j}_{a} from{j}_{prev}\n"
      prev := a
    steps := steps.push s!"\nset_option maxRecDepth 100000 in\ntheorem all{j} : ({suffix}) = temps{j} := by decide +kernel\n"
    -- increasing temporaries are distinct by one pass, not by comparing every pair
    let increasing := (allT.zip allT.tail).all fun (x, y) => x < y
    steps := steps.push (if increasing then
      s!"\nset_option maxRecDepth 100000 in\ntheorem nodup{j} : temps{j}.Nodup :=\n  (List.isChain_iff_pairwise.mp (by decide +kernel : temps{j}.IsChain (· < ·))).nodup\n"
    else s!"\nset_option maxRecDepth 100000 in\ntheorem nodup{j} : temps{j}.Nodup := by decide +kernel\n")
    steps := steps.push s!"\nset_option maxRecDepth 100000 in\ntheorem params{j} : (temps{j}.all fun t => !(idxMask Data.core{j}.params).testBit t) = true := by\n  decide +kernel\n"
    let imps := String.join (names.toList.map fun nm => s!"public import LeanVM.Guest.Memory.GuestFresh.{nm}\n")
    imports := imports.push s!"public import LeanVM.Guest.Memory.GuestFresh.Fresh{j}\n"
    files := files.push (memDir / "GuestFresh" / s!"Fresh{j}.lean",
      header s!"LeanVM.Guest.Memory.GuestFresh.Fresh{j}" s!"`{fn.name}`'s temporaries are fresh, by ranges of its statements." ++
      imps ++ "\n" ++ nsOpen ++ String.join steps.toList ++
      s!"\n/-- `{fn.name}`'s temporaries are fresh. -/\ntheorem core{j}_fresh : Data.core{j}.Fresh := by\n  have h0 := from{j}_0\n  rw [List.drop_zero, all{j}] at h0\n  exact fn_fresh_of_rangeFresh (fn := Data.core{j}) h0 nodup{j} params{j}\n" ++
      s!"\n/-- `{fn.name}`'s temporaries, by index. -/\ntheorem tmps{j} : (Stmt.tmpsList Data.core{j}.body).map V.idx = temps{j} := by\n  have h0 := (from{j}_0).1\n  rw [List.drop_zero, all{j}] at h0\n  exact h0\n" ++ nsClose)
  -- the whole program
  let pieces : List (Nat × Nat × String) := (small.map (fun ((a, n, _) : Nat × Nat × Nat) => (a, n, s!"freshRange_{a}.on")) ++
      big.map (fun j => (j, 1, s!"freshOn_one (j := {j}) rfl core{j}_fresh"))).mergeSort
    (fun (x y : Nat × Nat × String) => x.1 ≤ y.1)
  let (steps, last, tot) := chain "h" "FreshOn" 0 pieces
  files := files.push (memDir / "GuestFresh.lean",
    header "LeanVM.Guest.Memory.GuestFresh"
      "The guest's core IR has fresh range-check temporaries (`Program.Fresh`)." ++
    String.join imports.toList ++ "
/-!
# The guest's temporaries are fresh

`Fn.freshB` is evaluated by the kernel on ranges of `coreProgram`'s functions (`FreshRange`, one
declaration each, `GuestFresh/Part*.lean`); a function too large for one check is certified by
ranges of its statements (`RangeFresh`, `GuestFresh/Fresh*.lean`). The ranges concatenate to the
whole program.
-/

" ++ nsOpen ++ s!"
set_option maxRecDepth 100000 in
/-- **The guest's range-check temporaries are fresh.** -/
theorem coreProgram_fresh : coreProgram.Fresh := by
" ++ "\n".intercalate steps ++ s!"
  exact fresh_of_freshOn (coreProgram_length ▸ {last})
" ++ nsClose)
  let _ := tot
  return files

/-! ### Well-formedness -/

def wfFiles (P : Program) : Array (System.FilePath × String) := Id.run do
  let costs := (P.map fun fn => wfCost P.length fn.body).toArray
  let big := (List.range P.length).filter fun j => costs[j]! > wfBudget
  let bounds := (0 :: big.map (· + 1)).zip (big ++ [P.length])
  let small := bounds.flatMap fun (lo, hi) => cut costs wfBudget lo hi
  let mut files : Array (System.FilePath × String) := #[]
  files := files.push (memDir / "GuestWf" / "Range.lean", header "LeanVM.Guest.Memory.GuestWf.Range"
    "Ranges of the guest's core IR whose well-formedness the kernel checks." ++
    "public import LeanVM.Guest.Memory.Tree\npublic import LeanVM.Guest.CoreData\n\n" ++ nsOpen ++ "
/-- The `n` functions of `coreProgram` from its `a`-th are well formed, decided. -/
def WfRange (a n : ℕ) : Prop :=
  ((coreProgram.drop a).take n).all (fun fn => Stmt.wfList coreProgram fn.body) = true

/-- The `n` functions of `coreProgram` from its `a`-th are well formed. -/
def WfOn (a n : ℕ) : Prop := ∀ fn ∈ (coreProgram.drop a).take n, Stmt.wfList coreProgram fn.body = true

theorem WfRange.on {a n : ℕ} (h : WfRange a n) : WfOn a n := by
  intro fn hfn
  unfold WfRange at h
  rw [List.all_eq_true] at h
  exact h fn hfn

theorem wfOn_one {j : ℕ} {fn : Fn} (hj : coreProgram[j]? = some fn)
    (h : Stmt.wfList coreProgram fn.body = true) : WfOn j 1 := by
  intro fn' hfn
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons, List.take_zero,
    List.mem_singleton] at hfn
  exact hfn ▸ h

/-- Two adjacent ranges are one. -/
theorem WfOn.append' {a n m b k : ℕ} (h : WfOn a n) (h' : WfOn b m)
    (hb : a + n = b) (hk : n + m = k) : WfOn a k := by
  subst hb hk
  intro fn hfn
  rw [List.take_add, List.mem_append, List.drop_drop] at hfn
  exact hfn.elim (h fn) (h' fn)

theorem wf_of_wfOn (h : WfOn 0 coreProgram.length) : coreProgram.Wf := by
  intro fn hfn
  exact h fn (by rw [List.drop_zero, List.take_length]; exact hfn)

theorem wfList_append (P : Program) : ∀ (l l' : List Stmt),
    Stmt.wfList P (l ++ l') = (Stmt.wfList P l && Stmt.wfList P l')
  | [], _ => by simp [Stmt.wfList]
  | s :: l, l' => by
    rw [List.cons_append, Stmt.wfList, Stmt.wfList, wfList_append P l l', Bool.and_assoc]

/-- A range of statements, decided well formed. -/
def WfStmts (l : List Stmt) (a n : ℕ) : Prop := Stmt.wfList coreProgram ((l.drop a).take n) = true

/-- The ranges from `a` and from `a + n` make the range from `a`. -/
theorem wfStmts_drop {l : List Stmt} {a n : ℕ} (h : WfStmts l a n)
    (h' : Stmt.wfList coreProgram (l.drop (a + n)) = true) :
    Stmt.wfList coreProgram (l.drop a) = true := by
  rw [← List.take_append_drop n (l.drop a), wfList_append, List.drop_drop]
  exact Bool.and_eq_true_iff.mpr ⟨h, h'⟩

theorem wfStmts_end {l : List Stmt} {a : ℕ} (ha : l.length ≤ a) :
    Stmt.wfList coreProgram (l.drop a) = true := by
  rw [List.drop_eq_nil_of_le ha]; rfl
" ++ nsClose)
  let decls := small.map fun (a, n, w) =>
    (s!"\nset_option maxRecDepth 100000 in\ntheorem wfRange_{a} : WfRange {a} {n} := by\n  unfold WfRange; decide +kernel\n", w)
  let mods := modules (4 * wfBudget) decls
  let mut imports : Array String := #[]
  for (m, k) in mods.zipIdx do
    let nm := s!"Part{pad2 k}"
    imports := imports.push s!"public import LeanVM.Guest.Memory.GuestWf.{nm}\n"
    files := files.push (memDir / "GuestWf" / s!"{nm}.lean",
      header s!"LeanVM.Guest.Memory.GuestWf.{nm}" "Kernel checks of well-formedness on ranges of the guest's functions." ++
      "public import LeanVM.Guest.Memory.GuestWf.Range\n\n" ++ nsOpen ++ String.join m ++ nsClose)
  for j in big do
    let fn := P[j]!
    let body := fn.body.toArray
    let scosts := body.map fun s => wfCost P.length [s]
    let rngs := cut scosts wfBudget 0 body.size
    let rdecls := rngs.map fun (a, n, w) =>
      (s!"\nset_option maxRecDepth 100000 in\ntheorem wf{j}_{a} : WfStmts Data.core{j}.body {a} {n} := by\n  unfold WfStmts; decide +kernel\n", w)
    let rmods := modules (4 * wfBudget) rdecls
    let mut names : Array String := #[]
    for (m, k) in rmods.zipIdx do
      let nm := s!"Big{j}_{k}"
      names := names.push nm
      files := files.push (memDir / "GuestWf" / s!"{nm}.lean",
        header s!"LeanVM.Guest.Memory.GuestWf.{nm}" s!"Kernel checks of well-formedness on ranges of `{fn.name}`'s statements." ++
        "public import LeanVM.Guest.Memory.GuestWf.Range\n\n" ++ nsOpen ++ String.join m ++ nsClose)
    let mut steps : Array String :=
      #[s!"  have h{body.size} : Stmt.wfList coreProgram (Data.core{j}.body.drop {body.size}) = true :=\n    wfStmts_end (by decide +kernel)"]
    let mut prev := body.size
    for (a, n, _) in rngs.reverse do
      steps := steps.push s!"  have h{a} : Stmt.wfList coreProgram (Data.core{j}.body.drop {a}) = true :=\n    wfStmts_drop (a := {a}) (n := {n}) wf{j}_{a} h{prev}"
      prev := a
    let imps := String.join (names.toList.map fun nm => s!"public import LeanVM.Guest.Memory.GuestWf.{nm}\n")
    imports := imports.push s!"public import LeanVM.Guest.Memory.GuestWf.Wf{j}\n"
    files := files.push (memDir / "GuestWf" / s!"Wf{j}.lean",
      header s!"LeanVM.Guest.Memory.GuestWf.Wf{j}" s!"`{fn.name}` is well formed, by ranges of its statements." ++
      imps ++ "\n" ++ nsOpen ++
      s!"\nset_option maxRecDepth 100000 in\n/-- `{fn.name}` is well formed. -/\ntheorem core{j}_wf : Stmt.wfList coreProgram Data.core{j}.body = true := by\n" ++
      "\n".intercalate steps.toList ++ "\n  simpa using h0\n" ++ nsClose)
  let pieces : List (Nat × Nat × String) := (small.map (fun ((a, n, _) : Nat × Nat × Nat) => (a, n, s!"wfRange_{a}.on")) ++
      big.map (fun j => (j, 1, s!"wfOn_one (j := {j}) rfl core{j}_wf"))).mergeSort
    (fun (x y : Nat × Nat × String) => x.1 ≤ y.1)
  let (steps, last, _) := chain "h" "WfOn" 0 pieces
  files := files.push (memDir / "GuestWf.lean",
    header "LeanVM.Guest.Memory.GuestWf"
      "The guest's core IR is well formed (`Program.Wf`)." ++
    String.join imports.toList ++ "
/-!
# The guest is well formed

`Stmt.wfList` is evaluated by the kernel on ranges of `coreProgram`'s functions (`WfRange`, one
declaration each, `GuestWf/Part*.lean`), the ranges cut by their statements and their `callIf`s,
whose callee lookups the kernel's cost is in; a function too large for one check by ranges of its
statements (`WfStmts`, `GuestWf/Wf*.lean`). Every `callIf` names a loop helper taking its
arguments, and every `match` and fused dispatch has at most `2^64 - 1` arms; so every derivation
of the guest's `Program.Rel` is an honest evaluation (`Program.Rel.tree`).
-/

" ++ nsOpen ++ s!"
set_option maxRecDepth 100000 in
/-- **The guest's core IR is well formed.** -/
theorem coreProgram_wf : coreProgram.Wf := by
" ++ "\n".intercalate steps ++ s!"
  exact wf_of_wfOn (coreProgram_length ▸ {last})
" ++ nsClose)
  return files

/-! ### No call of `main` -/

/-- One `main`-freedom declaration's cost at most this: callees named (a string comparison each)
and statements walked. -/
def mainFreeBudget : Nat := 25000

def mainFreeFiles (P : Program) : Array (System.FilePath × String) := Id.run do
  let costs := (P.map fun fn => 50 * (Stmt.blockCallees fn.body).length + stmtCountList fn.body).toArray
  let rngs := cut costs mainFreeBudget 0 P.length
  let mut files : Array (System.FilePath × String) := #[]
  files := files.push (memDir / "GuestMainFree" / "Range.lean", header "LeanVM.Guest.Memory.GuestMainFree.Range"
    "Ranges of the guest's core IR none of whose functions calls `main`." ++
    "public import LeanVM.Guest.Memory.SizeTotal\npublic import LeanVM.Guest.CoreData\n\n" ++ nsOpen ++ "
/-- No callee of function `j` is `main`. -/
noncomputable def mainFreeJ (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => (Stmt.blockCallees fn.body).all fun g => decide (g ≠ \"main\")

/-- The `n` functions from the `a`-th call no `main`, decided. -/
def MainFreeRange (a n : ℕ) : Prop := (List.range' a n).all mainFreeJ = true

/-- The `n` functions from the `a`-th call no `main`. -/
def MainFreeOn (a n : ℕ) : Prop := ∀ j, a ≤ j → j < a + n → mainFreeJ j = true

theorem MainFreeRange.on {a n : ℕ} (h : MainFreeRange a n) : MainFreeOn a n := by
  intro j h1 h2
  unfold MainFreeRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

/-- Two adjacent ranges are one. -/
theorem MainFreeOn.append' {a n m b k : ℕ} (h : MainFreeOn a n) (h' : MainFreeOn b m)
    (hb : a + n = b) (hk : n + m = k) : MainFreeOn a k := by
  intro j h1 h2
  by_cases hj : j < a + n
  · exact h j h1 hj
  · exact h' j (by omega) (by omega)
" ++ nsClose)
  let decls := rngs.map fun (a, n, w) =>
    (s!"\nset_option maxRecDepth 100000 in\ntheorem mainFreeRange_{a} : MainFreeRange {a} {n} := by\n  unfold MainFreeRange; decide +kernel\n", w)
  let mods := modules (4 * mainFreeBudget) decls
  let mut imports : Array String := #[]
  for (m, k) in mods.zipIdx do
    let nm := s!"Part{pad2 k}"
    imports := imports.push s!"public import LeanVM.Guest.Memory.GuestMainFree.{nm}\n"
    files := files.push (memDir / "GuestMainFree" / s!"{nm}.lean",
      header s!"LeanVM.Guest.Memory.GuestMainFree.{nm}" "Kernel checks that ranges of the guest's functions call no `main`." ++
      "public import LeanVM.Guest.Memory.GuestMainFree.Range\n\n" ++ nsOpen ++ String.join m ++ nsClose)
  let pieces : List (Nat × Nat × String) :=
    rngs.map (fun ((a, n, _) : Nat × Nat × Nat) => (a, n, s!"mainFreeRange_{a}.on"))
  let (steps, last, _) := chain "h" "MainFreeOn" 0 pieces
  files := files.push (memDir / "GuestMainFree.lean",
    header "LeanVM.Guest.Memory.GuestMainFree"
      "No function of the guest calls `main` (`coreProgram_callsIn_noMain`)." ++
    String.join imports.toList ++ "public import LeanVM.Guest.Memory.SizeTransfer\n" ++ "
/-!
# No function of the guest calls `main`

`Stmt.blockCallees` is evaluated by the kernel on ranges of `coreProgram`'s functions
(`MainFreeRange`, `GuestMainFree/Part*.lean`); the ranges concatenate to the whole program
(`mainFree_all`), so the paths of every function call only functions other than `main`
(`coreProgram_callsIn_noMain`), and bounds transfer between frame sizes agreeing but at `main`.
-/

" ++ nsOpen ++ "
/-- **No function calls `main`**, function by function. -/
theorem mainFree_all : ∀ j < coreProgram.length, mainFreeJ j = true := by
" ++ "\n".intercalate steps ++ s!"
  intro j hj
  exact {last} j (Nat.zero_le _) (by rw [coreProgram_length] at hj; omega)

/-- **No path of the guest calls `main`.** -/
theorem coreProgram_callsIn_noMain : CallsIn coreProgram (· ≠ \"main\") := by
  refine callsIn_of_callees fun f _ fn hfn g hg => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hfn)
  have hc := mainFree_all j hj
  unfold mainFreeJ at hc
  rw [List.getElem?_eq_getElem hj] at hc
  simpa using List.all_eq_true.mp hc g hg
" ++ nsClose)
  return files

end GuestMemory

open GuestMemory

/-- Every generated file under a family's directory, to delete stale ones. -/
partial def listLean (d : System.FilePath) : IO (List System.FilePath) := do
  if !(← d.pathExists) then return []
  let es ← d.readDir
  return (es.filter (·.path.extension == some "lean")).toList.map (·.path)

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let program ← match Expand.expandProgram Data.guest with
    | .ok fns => pure (fns.map Fn.renumber)
    | .error e => throw (IO.userError s!"expansion: {e}")
  if args.contains "--stats" then
    for (fn, j) in program.zipIdx do
      IO.println s!"{j} {fn.name} fresh {freshCost fn.body fn.params} wf {wfCost program.length fn.body} stmts {fn.body.length}"
    return 0
  let files := freshFiles program ++ wfFiles program ++ mainFreeFiles program
  let mut bad := false
  if check then
    for (p, s) in files do
      -- Two steps: a `(← …)` is run before the `||`, so a missing file must not be read.
      let same ← if ← p.pathExists then pure ((← IO.FS.readFile p) == s) else pure false
      if !same then
        IO.eprintln s!"stale: {p}"
        bad := true
    for d in [memDir / "GuestFresh", memDir / "GuestWf", memDir / "GuestMainFree"] do
      for p in ← listLean d do
        if !files.any (·.1 == p) then
          IO.eprintln s!"stale: {p}"
          bad := true
  else
    for d in [memDir / "GuestFresh", memDir / "GuestWf", memDir / "GuestMainFree"] do
      for p in ← listLean d do
        if !files.any (·.1 == p) then IO.FS.removeFile p
      IO.FS.createDirAll d
    for (p, s) in files do
      IO.FS.writeFile p s
    IO.println s!"wrote {files.size} files"
  return if bad then 1 else 0
