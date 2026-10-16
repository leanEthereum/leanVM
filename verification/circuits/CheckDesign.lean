import LeanVMCircuits.Rec.DesignClaims
import LeanVMCircuits.Rec.EdgeMarks

/-!
`lake exe checkdesign <summaries> [<dump>...]`: compare the Lean model of `Design` with the Rust design.

The summaries (`fixtures/design-summaries.txt`, written by `rec::tree::design_tests`) hold, for a grid of tree shapes, whether `Tree::new` refuses the shape's arities or small tier, and else its design: `Place::all`, each tier's range, each position's kind, `Design::position` of the kinds below 40, each position's union shape, the dense variables and fixed stacks' variables, and the statement's length and polynomials. Each must be the model's (`Shape.check`, `Shape.places`, `Shape.start`, `Shape.stop`, `Shape.code`, `Shape.position`, `Shape.union`, `Shape.vars`, `Shape.layout`), given the program's two dense variables, which the summary states. They also hold the two scalars `NodeClaims::bind_state` binds of a final state of words 1 to 4 (`bindOk`, `bindState`), for a tree of outputs the digest `Kind::Node::digest_rows` computes of its node's children's labeled digests (`nodeDigestOk`: the tree statement digest `treeDigest`, which `digestRows_good` proves the rows compute), and the design's claims, each compared with `DesignClaims`: the statement's edge layout (`edgeLayout`); the claims `Design::carried` takes from a statement of labeled words (`carriedOk`); the statement `Reduced::statement` exposes for labeled reduction outputs, after as many rounds as the point has coordinates with every polynomial reduced and after the bytecode's rounds with only the bytecode and image reduced (`exposedOk`); and each tier's fixed claim `Design::fixed_claim` on labeled hints of every fixed column, at zero heights and at heights differing per table (`fixedOk`), whose columns' variables place the stack, so each tier's fixed stack's variables are the model's `kappa` of them.

Each dump is a tracked circuit (`cargo leanvm circuits`), named by its tree and position. Its calls are replayed through the builder model; each child's statement is a run of as many `free_e` calls as the circuit exposes words, and the calls after it must add to the circuit exactly what `Model.kindRows` adds from the same state, for the child's tier, then exactly what `Model.limbRows` adds for its words: the same unions, rows, public rows, wires and units. A node must read as many children as `Shape.children` says, a first-level circuit none, and the statement's length must leave the dense point a nonnegative number of words. The circuit's first exposure, at statement position zero, must be of the constant of its own kind `Shape.code` (`Model.kind_exposed`, `Model.kindConst_ev`).
-/

open LeanVMCircuits.Rec
open LeanVMCircuits.Rec.Model
open LeanVMCircuits.Rec.Design

namespace CheckDesign

def placeStr : Place → String
  | ⟨t, .first⟩ => s!"{t}:F"
  | ⟨t, .node a⟩ => s!"{t}:N:{a}"
  | ⟨t, .wrap⟩ => s!"{t}:W"

def unionStr : Option UnionShape → String
  | none => "-"
  | some u => s!"{u.arity}:{u.children}:{u.declared}:{if u.optional then 1 else 0}"

def words (xs : List String) : String := " ".intercalate xs

/-- The model's summary of an accepted shape's design. -/
def summary (sh : Shape) (v0 v1 : ℕ) (kappas : List ℕ) : List String :=
  let kappa := fun t => kappas.getD t 0
  let ps := List.range sh.size
  [ "places " ++ words (sh.places.map placeStr),
    "tiers " ++ words ((List.range sh.nTiers).map fun t => s!"{sh.start t}-{sh.stop t}"),
    "codes " ++ words (ps.map fun p => toString (sh.code p)),
    "positions " ++ words ((List.range 40).map fun c => (sh.position c).elim "-" toString),
    "unions " ++ words (ps.map fun p => unionStr (sh.union p)),
    "vars " ++ words ((sh.vars v0 v1 kappa).map toString),
    "kappas " ++ words ((List.range sh.nTiers).map fun t => toString (kappa t)),
    s!"statement {(sh.layout v0 v1 kappa).len} {sh.nPolys}" ]

def nat! (s : String) : Except String ℕ := match s.toNat? with
  | some n => pure n
  | none => .error s!"not a number: {s}"

def parseShape (ws : List String) : Except String Shape := do
  match ws with
  | [a0, a, "none"] => pure ⟨← nat! a0, ← nat! a, none⟩
  | [a0, a, c, g, "-"] => pure ⟨← nat! a0, ← nat! a, some ⟨⟨← nat! c, ← nat! g⟩, none⟩⟩
  | [a0, a, c, g, sa, sc, sg] =>
    pure ⟨← nat! a0, ← nat! a, some ⟨⟨← nat! c, ← nat! g⟩, some ⟨← nat! sa, ⟨← nat! sc, ← nat! sg⟩⟩⟩⟩
  | _ => .error s!"not a shape: {words ws}"

def verdict : Option Refusal → String
  | none => "accept"
  | some .arity => "reject arity"
  | some .smallTier => "reject small"

/-- Edge lines joined by ` | `, as the claims they mark. -/
def marksOf (line : String) : Except String Edges.Marks :=
  ((line.splitOn " | ").filter (· ≠ "")).foldlM (fun m part => m.add ((part.splitOn " ").filter (· ≠ ""))) {}

def claimsOf (m : Edges.Marks) : Edges.Claims ℕ := ⟨m.dense.toList, m.matrices.toList⟩

def word! (s : String) : Except String DesignClaims.Word := do
  match s.splitOn ":" with
  | [a, b, c] => pure (← nat! a, ← nat! b, ← nat! c)
  | _ => .error s!"not a word: {s}"

/-- A `fixed` or `hfixed` line: the tier, its kind bits, its columns' variables, its fixed claim. Checks the claim is `fixedModel`'s, the kind bits the shape's, and returns the tier and the stack's `kappa`. -/
def checkFixed (sh : Shape) (line : String) : Except String (ℕ × ℕ) := do
  let (head, rest) := match line.splitOn " | " with
    | h :: r => (h, " | ".intercalate r)
    | [] => ("", "")
  let ws := (head.splitOn " ").drop 1
  let (tier, kb, n) ← match ws with
    | t :: k :: n :: _ => pure (← nat! t, ← nat! k, ← nat! n)
    | _ => .error s!"not a fixed claim: {head.take 60}"
  let taus ← (ws.drop 3).mapM nat!
  unless taus.length = n do .error s!"tier {tier}: {taus.length} columns, said {n}"
  unless kb = sh.kindBits tier do .error s!"tier {tier}: {kb} kind bits, the model {sh.kindBits tier}"
  let c := claimsOf (← marksOf rest)
  unless DesignClaims.fixedOk tier kb taus c do .error s!"tier {tier}: the fixed claim is not the model's"
  return (tier, DesignClaims.kappa taus)

/-- Compare every summary with the model; the number of shapes checked. -/
def checkSummaries (text : String) : Except String ℕ := do
  let lines := text.splitOn "\n" |>.filter (· ≠ "")
  let some first := lines.head? | .error "empty summaries"
  unless first = s!"consts {maxKLog} {nFlocks}" do .error s!"constants differ: {first}"
  let bound ← match (lines.getD 1 "").splitOn " " with
    | "bind" :: ws => ws.mapM word!
    | _ => .error "no bound state"
  unless DesignClaims.bindOk bound do .error s!"the bound state's scalars are not the model's: {lines.getD 1 ""}"
  let mut rest := lines.drop 2
  let mut n := 0
  while !rest.isEmpty do
    let shapeLine := rest.headD ""
    let sh ← match shapeLine.splitOn " " with
      | "shape" :: ws => parseShape ws
      | _ => .error s!"expected a shape: {shapeLine}"
    let v := rest.getD 1 ""
    unless v = verdict sh.check do .error s!"{shapeLine}: Rust says {v}, the model {verdict sh.check}"
    let block := (rest.drop 2).takeWhile (· ≠ "end")
    rest := rest.drop (2 + block.length)
    if sh.check = none then
      let vars ← match (block.getD 5 "").splitOn " " with
        | ["vars", v0, v1, _, _] => pure (← nat! v0, ← nat! v1)
        | _ => .error s!"{shapeLine}: no variables"
      let kappaLine := fun (name : String) => do
        match ((block.find? (·.startsWith (name ++ " "))).getD "").splitOn " " with
        | k :: ks => if k = name then ks.mapM nat! else .error s!"{shapeLine}: no {name}"
        | [] => .error s!"{shapeLine}: no {name}"
      let kappas ← kappaLine "kappas"
      let hkappas ← kappaLine "hkappas"
      let model := summary sh vars.1 vars.2 kappas
      for (r, m) in block.zip model do
        unless r = m do .error s!"{shapeLine}: Rust `{r}`, the model `{m}`"
      unless sh.places = (List.range sh.size).map sh.placeAt do .error s!"{shapeLine}: places not closed form"
      let L := DesignClaims.edgeLayout sh vars.1 vars.2 fun t => kappas.getD t 0
      let mut seen : List String := []
      for line in block.drop 8 do
        let key := (line.splitOn " ").headD ""
        match key with
        | "layout" =>
          let m ← (({} : Edges.Marks).add (line.splitOn " ")).mapError (s!"{shapeLine}: " ++ ·)
          unless m.layout = some L do .error s!"{shapeLine}: the layout is not the model's"
        | "carried" =>
          let c := claimsOf (← (marksOf (line.drop 8).toString).mapError (s!"{shapeLine}: " ++ ·))
          unless DesignClaims.carriedOk L c do .error s!"{shapeLine}: the carried claims are not the model's"
        | "exposed" =>
          let (rounds, present, ws) ← match line.splitOn " " with
            | _ :: r :: p :: ws => pure (← nat! r, p.toList.map (· == '1'), ← ws.mapM word!)
            | _ => .error s!"{shapeLine}: not an exposure"
          unless DesignClaims.exposedOk L rounds present ws do
            .error s!"{shapeLine}: the statement exposed after {rounds} rounds is not the model's"
        | "fixed" | "hfixed" =>
          let (t, k) ← (checkFixed sh line).mapError (s!"{shapeLine}: " ++ ·)
          let ks := if key = "fixed" then kappas else hkappas
          unless ks.getD t 0 = k ∧ t < ks.length do .error s!"{shapeLine}: tier {t}'s stack of {k} variables, Rust's {ks}"
        | "digest" =>
          let (a, ws) ← match line.splitOn " " with
            | _ :: a :: ws => pure (← nat! a, ← ws.mapM nat!)
            | _ => .error s!"{shapeLine}: not a digest"
          unless sh.claims = none ∧ sh.children 1 = some (a, 0) do .error s!"{shapeLine}: a node digest of {a} items"
          unless DesignClaims.nodeDigestOk a ws do .error s!"{shapeLine}: the node's digest of {a} items is not the model's"
        | "hkappas" => pure ()
        | _ => .error s!"{shapeLine}: an unknown line {line.take 40}"
        seen := key :: seen
      let tiers := sh.nTiers
      let want := [("layout", 1), ("carried", 1), ("exposed", 2), ("fixed", tiers), ("hkappas", 1), ("hfixed", tiers),
        ("digest", if sh.claims = none then 1 else 0)]
      for (k, c) in want do
        unless seen.count k = c do .error s!"{shapeLine}: {seen.count k} {k} lines, expected {c}"
      unless kappas.length = tiers ∧ hkappas.length = tiers do .error s!"{shapeLine}: a stack per tier"
    unless rest.headD "" = "end" do .error s!"{shapeLine}: no end"
    rest := rest.tail
    n := n + 1
  return n

def isFreeE : Model.Call → Bool
  | .freeE => true
  | _ => false

def isExpose : Model.Call → Bool
  | .exposeE _ => true
  | _ => false

/-- What a state adds to the circuit, besides its caches. -/
def sameCircuit (a b : State) : Bool :=
  a.next == b.next && a.unions == b.unions && a.emul == b.emul && a.exk == b.exk && a.hash == b.hash &&
    a.split == b.split && a.cast == b.cast && a.pub == b.pub && a.statement == b.statement &&
    a.units.eZero == b.units.eZero && a.units.eOne == b.units.eOne && a.units.kZero == b.units.kZero &&
    a.units.kOne == b.units.kOne

/-- How many calls `kindRows sh t` makes. -/
def kindCalls (sh : Shape) (t : ℕ) : ℕ :=
  if sh.size = 2 then 2
  else 2 + 3 * (sh.stop t - sh.start t) + 3 + 64 + (if t = 0 then 2 * sh.kindBits t + 1 else 0)

def checkDump (path : System.FilePath) : IO Bool := do
  let some (sh, position) := DesignClaims.dumpShape (path.fileStem.getD "")
    | IO.eprintln s!"{path}: not a tracked circuit's name"; return false
  let text ← IO.FS.readFile path
  let (lines, _, _) ← match Dump.sections text with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"{path}: {e}"; return false
  let mut calls : Array Model.Call := #[]
  for line in lines do
    match Dump.parseLine line with
    | .ok (.call c) => calls := calls.push c
    | .ok _ => pure ()
    | .error e => do IO.eprintln s!"{path}: {e}"; return false
  let len := (calls.filter isExpose).size
  let fixed := 3 + sh.nPolys + 2 * maxKLog + 2 * nFlocks
  unless fixed ≤ len do
    IO.eprintln s!"{path}: a statement of {len} words leaves no dense point"; return false
  let (expected, tier) := match sh.children position with
    | some (a, ct) => (a, ct)
    | none => (0, 0)
  let mut s : State := {}
  let mut i := 0
  let mut children := 0
  while i < calls.size do
    -- A child's statement: a run of exactly `len` `free_e` calls.
    let run := (calls.extract i (i + len + 1)).toList
    let starts := i = 0 || !isFreeE (calls.getD (i - 1) .freeE)
    if starts && run.length = len + 1 && (run.take len).all isFreeE && !isFreeE (run.getD len .freeE) then
      let kind := s.next
      for c in run.take len do
        s := (c.exec.run s).2
      i := i + len
      let model := ((kindRows sh tier kind).run s).2
      for c in (calls.extract i (i + kindCalls sh tier)).toList do
        unless c.args.all (· < s.next) && c.ok do
          IO.eprintln s!"{path}: call {i} names a wire not yet made"; return false
        s := (c.exec.run s).2
      unless sameCircuit model s do
        IO.eprintln s!"{path}: child {children}'s kind rows differ from the model's at call {i}"; return false
      i := i + kindCalls sh tier
      -- Then the words' limbs: as many calls as `limbRows` makes, adding what it adds.
      let ws := (List.range len).map (kind + ·)
      let limbs := ((limbRows ws).run s).2
      for c in (calls.extract i (i + 1 + len)).toList do
        unless c.args.all (· < s.next) && c.ok do
          IO.eprintln s!"{path}: call {i} names a wire not yet made"; return false
        s := (c.exec.run s).2
      unless sameCircuit limbs s do
        IO.eprintln s!"{path}: child {children}'s limbs differ from the model's at call {i}"; return false
      i := i + 1 + len
      children := children + 1
    else
      let c := calls.getD i .freeE
      unless c.args.all (· < s.next) && c.ok do
        IO.eprintln s!"{path}: call {i} names a wire not yet made"; return false
      s := (c.exec.run s).2
      i := i + 1
  unless children = expected do
    IO.eprintln s!"{path}: {children} children's kind rows, the model {expected}"; return false
  -- The statement's first word is the circuit's kind: the exposure at position zero of the `e_const` of its code, or of
  -- the cached `zero` or `one` for those codes (`Model.kindConst_ev`, `Model.kind_exposed`).
  let mut s2 : State := {}
  let mut maker : Std.HashMap ℕ Model.Call := {}
  let mut kindOk := false
  let mut exposed := false
  for c in calls do
    let (outs, s') := c.exec.run s2
    s2 := s'
    if let .exposeE w := c then
      unless exposed do
        exposed := true
        let code := sh.code position
        kindOk := outs == [0] && match maker[w]? with
          | some (.eConst c 0 0) => c == code
          | some .zero => code == 0
          | some .one => code == 1
          | _ => false
    for o in outs do
      unless maker.contains o do maker := maker.insert o c
  unless kindOk do
    IO.eprintln s!"{path}: the statement's first word is not the constant {sh.code position}"; return false
  IO.println s!"{path}: position {position}, {children} children's kind rows and limbs are the model's, \
    statement {len} words, the first its kind {sh.code position}"
  return true

end CheckDesign

def main (args : List String) : IO UInt32 := do
  let some summaries := args.head? | IO.eprintln "usage: checkdesign <summaries> [<dump>...]"; return 2
  let mut ok := true
  match CheckDesign.checkSummaries (← IO.FS.readFile summaries) with
  | .ok n => IO.println s!"{summaries}: {n} shapes, the model's design is Rust's"
  | .error e => IO.eprintln s!"{summaries}: {e}"; ok := false
  for path in args.tail do
    ok := (← CheckDesign.checkDump path) && ok
  return if ok then 0 else 1
