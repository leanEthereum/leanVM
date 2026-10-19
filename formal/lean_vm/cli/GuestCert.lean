import LeanVM.Guest.Data.Source
import LeanVM.Guest.Data.Bytecode
import LeanVM.Guest.Expand
import LeanVM.Guest.Renumber
import LeanVM.Guest.Check

/-!
# `guest-cert`: the certificates of the guest's compiled functions

`lake exe guest-cert` writes `LeanVM/Guest/Data/Cert*.lean`: for each compiled function, the
executor's facts and the frame cell of each core value (`Check.Cert`), with the jump table and the
powers of `g` the guest names. `lake exe guest-cert --check` writes nothing and fails when the
files differ. Run it from `formal/lean_vm`.

Nothing here is trusted: the checker (`Check.checkFn`) validates every certificate, so a wrong
cell here makes a check fail, never a false theorem. The cells are inferred by walking the core
function along a mirror of `Exec.exec` (same segments, items and exits, computed with hash maps),
matching each core atom with the first instruction that fits the cells known so far, as the
compiler emits them in order; a constant takes the cell of the instruction that uses it, and a
frame run (`addr`) its consecutive cells.
-/

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.Check

namespace GuestCert

instance : Inhabited OInstr := ⟨.pad⟩
instance : Inhabited Exec.Atom := ⟨.nz 0⟩
instance : Inhabited CompiledFn := ⟨⟨"", 0, 0, []⟩⟩

def dataDir : System.FilePath := "LeanVM/Guest/Data"

/-! ## Powers of `g` -/

/-- The bits of `g^e` for `e < 2^19`, by exponent. -/
def logTable : Std.HashMap ℕ ℕ := Id.run do
  let mut m : Std.HashMap ℕ ℕ := {}
  let mut x : K := 1
  for e in List.range (2 ^ 19) do
    let k := x.toBitVec.toNat
    unless m.contains k do m := m.insert k e
    x := x * g
  return m

/-! ## The executor, with hash maps -/

abbrev Env := Std.HashMap ℕ Sym

structure GExit where
  kind : Kind
  env : Env
  succ : List ℕ

inductive GItem where
  | ins (a : Exec.Atom)
  | fact (a : Exec.Atom)
  | branch (oc od of : ℕ) (x : GExit)

structure GSeg where
  start : ℕ
  env : Env
  items : Array GItem
  exit : GExit

structure GFacts where
  pows : Std.HashMap ℕ ℕ
  env : List (ℕ × Sym)
  fpOne : Bool
  arms : Std.HashMap ℕ (List ℕ)

def envGet (e : Env) (o : ℕ) : Option Sym := e.get? o

def inter (a b : Env) : Env := a.fold (fun m k v => if b.get? k == some v then m.insert k v else m) {}

def symOf (F : GFacts) (k0 k1 k2 : ℕ) : Option Sym :=
  if k1 == 0 && k2 == 0 then
    if k0 == 0 then some .zero else if k0 == 1 then some (.gp 0) else (F.pows.get? k0).map .gp
  else none

def tgtOf (s : Option Sym) (o : ℕ) : Tgt :=
  match s with
  | some (.fpg e) => .fpg e
  | some (.gp e) => .gp e
  | _ => .cell o

def expo : Option Sym → Option ℕ
  | some (.gp e) => some e
  | _ => none

def memFind : List (ℕ × ℕ × Sym) → ℕ → ℕ → Option Sym
  | [], _, _ => none
  | (q, off, v) :: m, q', off' => if q == q' && off == off' then some v else memFind m q' off'

def learn (e : Env) (o : ℕ) (v : Sym) : Env := if e.contains o then e else e.insert o v

structure GSt where
  env : Env
  mem : List (ℕ × ℕ × Sym)
  prev : List (ℕ × OInstr)

structure GCur where
  start : ℕ
  env : Env
  acc : Array GItem
  st : GSt

/-- `Exec.exec` with hash maps, over offsets `a` to `b`, starting with `env0`. -/
def execG (F : GFacts) (f : CompiledFn) (a b : ℕ) (env0 : Env) : Array GSeg := Id.run do
  let code := f.code.toArray
  let E := f.entry
  let n := code.size
  let selff : Tgt → Bool := fun t => t == .fpg 0 || (t == .gp 0 && F.fpOne)
  let mut cur : Option GCur := some ⟨a, env0, #[], ⟨env0, [], []⟩⟩
  let mut pend : Std.HashMap ℕ Env := {}
  let mut out : Array GSeg := #[]
  for i in [a:b] do
    let ins := code[i]!
    if let some ea := pend.get? i then
      pend := pend.erase i
      match cur with
      | some c =>
        let e := inter ea c.st.env
        if c.start < i then
          out := out.push ⟨c.start, c.env, c.acc, ⟨.next i, c.st.env, [i]⟩⟩
        cur := some ⟨i, e, #[], ⟨e, [], []⟩⟩
      | none => cur := some ⟨i, ea, #[], ⟨ea, [], []⟩⟩
    let some c := cur | continue
    let env := c.st.env
    let mem := c.st.mem
    let prev := c.st.prev
    let pc := E + i
    match ins with
    | .jump oc od of =>
      let cv := envGet env oc
      let kindSucc : Kind × List ℕ :=
        if od == 0 && of == 1 then (.ret, [])
        else
          let pt := tgtOf (envGet env od) od
          let ft := tgtOf (envGet env of) of
          if selff ft then
            match pt with
            | .gp e => if E + i < e && e < E + n then (.next (e - E), [e - E]) else (.jump pt ft, [])
            | .cell _ => (.jump pt ft, (F.arms.get? i).getD [])
            | .fpg _ => (.jump pt ft, [])
          else
            match ft with
            | .cell q =>
              match expo (memFind mem q 0), memFind mem q 1 with
              | some r, some (.fpg 0) => (.call pt q r, if E + i < r && r < E + n then [r - E] else [])
              | _, _ => (.jump pt ft, [])
            | _ => (.jump pt ft, [])
      let x : GExit := ⟨kindSucc.1, env, kindSucc.2⟩
      match cv with
      | some .zero => cur := some { c with acc := c.acc.push (.ins (.jump oc od of)) }
      | some (.gp _) =>
        out := out.push ⟨c.start, c.env, c.acc.push (.ins (.jump oc od of)), x⟩
        for t in x.succ do
          pend := pend.insert t (match pend.get? t with | some e' => inter e' env | none => env)
        cur := none
      | _ =>
        for t in x.succ do
          pend := pend.insert t (match pend.get? t with | some e' => inter e' env | none => env)
        cur := some { c with acc := c.acc.push (.branch oc od of x) }
    | _ =>
      let mut fs : Array Exec.Atom := #[]
      let mut env2 := env
      let mut mem2 := mem
      match ins with
      | .xor a' b' c' => if envGet env c' == some .zero then fs := fs.push (.eq a' b')
      | .mul a' b' c' =>
        let va := envGet env a'
        let vb := envGet env b'
        if a' == b' && b' == c' then fs := fs.push (.bool c')
        if vb == some (.gp 0) then fs := fs.push (.copy c' a')
        else if va == some (.gp 0) then fs := fs.push (.copy c' b')
        if F.env.any (·.1 == a') then
          match va with
          | some (.fpg e) => match expo vb with
            | some e' => env2 := learn env c' (.fpg (e + e'))
            | none => pure ()
          | _ => pure ()
      | .set o k0 k1 k2 =>
        if k0 == 1 && k1 == 0 && k2 == 0 then
          match prev with
          | (_, .mul x _ p') :: rest =>
            if p' == o then
              fs := fs.push (.nz x)
              match rest with
              | [(_, .xor a' b' x')] => if x' == x then fs := fs.push (.ne a' b')
              | _ => pure ()
          | _ => pure ()
        if let some v := symOf F k0 k1 k2 then env2 := env.insert o v
      | .deref o1 o2 o3 mode =>
        if o2 == 0 && mode == .cell then
          match prev with
          | [(_, .mul x y' z), (_, .deref x' 0 _ .cell)] =>
            if y' == o1 && x' == x then
              match expo (envGet env z) with
              | some k => fs := fs.push (if k < 2 ^ 63 then .range x o1 (k + 1) else .powPair x o1 z)
              | none => fs := fs.push (.powPair x o1 z)
          | _ => pure ()
        match mode with
        | .fp => mem2 := ((o1, o2, .fpg 0) :: mem).take 4
        | .pc => mem2 := ((o1, o2, .gp (pc + 2)) :: mem).take 4
        | .cell =>
          match memFind mem o1 o2 with
          | some v => env2 := learn env o3 v
          | none =>
            if o2 == 0 then
              match envGet env o3 with
              | some v => mem2 := ((o1, o2, v) :: mem).take 4
              | none => pure ()
      | _ => pure ()
      let acc := (fs.map GItem.fact).foldl (·.push ·) (c.acc.push (.ins (.instr pc ins)))
      cur := some { c with acc := acc, st := ⟨env2, mem2, (pc, ins) :: prev.take 1⟩ }
  if let some c := cur then
    if c.start < b then
      out := out.push ⟨c.start, c.env, c.acc, ⟨.next b, c.st.env, if b < n then [b] else []⟩⟩
  return out

/-! ## The program's tables -/

/-- Immediate bits of `SET`s that are powers of `g`, each function's. -/
def setPows (f : CompiledFn) : List (ℕ × ℕ) :=
  f.code.filterMap fun
    | .set _ k0 0 0 => if k0 == 0 || k0 == 1 then none else (logTable.get? k0).map (k0, ·)
    | _ => none

/-- The jump table: slot to target pc, from `__jump_tables`. -/
def jumpTable (f0 : CompiledFn) : Std.HashMap ℕ ℕ :=
  f0.code.foldl (fun m ins => match ins with
    | .set s k0 0 0 => match logTable.get? k0 with
      | some e => m.insert s e
      | none => m
    | _ => m) {}

/-- The table bases of every table jump `DEREF *(fp[x]·g^t) = fp[c]; JUMP .., fp[c], ..`, and the
size of each table region, up to the next base. -/
def tableRegions (fns : List CompiledFn) (jtEnd : ℕ) : Std.HashMap ℕ ℕ := Id.run do
  let mut bases : Array ℕ := #[]
  for f in fns do
    let c := f.code.toArray
    for i in [1:c.size] do
      match c[i - 1]!, c[i]! with
      | .deref _ t o3 .cell, .jump _ od _ => if o3 == od then bases := bases.push t
      | _, _ => pure ()
  let bs := (bases.toList.eraseDups.mergeSort)
  let mut m : Std.HashMap ℕ ℕ := {}
  for (t, k) in bs.zipIdx do
    m := m.insert t ((bs[k + 1]?.getD jtEnd) - t)
  return m

/-- The self frame pointer cell of each loop, by entry pc: a callee frame `fp[q]` storing itself
at `fp[q]·g^o` before the jump into it. -/
def selfCells (fns : List CompiledFn) : Std.HashMap ℕ ℕ := Id.run do
  let mut m : Std.HashMap ℕ ℕ := {}
  for f in fns do
    let c := f.code.toArray
    for i in [0:c.size] do
      match c[i]! with
      | .deref q o q' .cell =>
        if q == q' then
          let js := (List.range 4).filterMap fun d =>
            if i + 1 + d < c.size then (match c[i + 1 + d]! with
              | .jump _ od _ => some od
              | _ => none) else none
          if let some od := js.head? then
            let lo := if i ≥ 40 then i - 40 else 0
            let sets := ((List.range (i - lo)).map (i - 1 - ·)).filterMap fun k =>
              match c[k]! with
              | .set o k0 0 0 => if o == od then logTable.get? k0 else none
              | _ => none
            if let some e := sets.head? then m := m.insert e o
      | _ => pure ()
  return m

/-! ## Inferring the cells -/

abbrev Loc := Std.HashMap ℕ ℕ

/-- A position: a segment's start and an item index. -/
abbrev Pos := ℕ × ℕ

structure WSt where
  loc : Loc := {}
  pend : Std.HashMap ℕ (ℕ × ℕ × ℕ) := {}
  used : Std.HashSet String := {}
  fa : Array (ℕ × List ℕ) := #[]
  nr : ℕ := 0
  /-- Before each top-level statement: its index, the position, the number of facts passed (a
  prefix of `spine`), and the returned words of a call before it still to read back
  `(q, o, n)`. -/
  marks : Array (ℕ × Pos × ℕ × Option (ℕ × ℕ × ℕ)) := #[]
  /-- The facts passed at the top level, by the end. -/
  spine : Array Exec.Atom := #[]
  /-- The top-level statement being walked. -/
  curTop : ℕ := 0
  /-- A passed fact found for an atom: the top-level statement and the fact's index on the
  path (on the spine below the facts passed at the branch it is on). -/
  uses : Array (ℕ × ℕ) := #[]

structure WCtx where
  segs : Std.HashMap ℕ GSeg
  setCells : Std.HashMap (ℕ × ℕ × ℕ) (List ℕ)
  entry : ℕ
  na : ℕ
  main : Bool

abbrev WM := ReaderT WCtx (StateT WSt (Except String))

def atomKey (a : Exec.Atom) : String := reprStr a

def getSeg (g : ℕ) : WM GSeg := do
  match (← read).segs.get? g with
  | some s => return s
  | none => throw s!"no segment {g}"

/-- Pass the next item, if no branch. -/
def consume (p : Pos) (facts : Array Exec.Atom) : WM (Option (Pos × Array Exec.Atom)) := do
  let s ← getSeg p.1
  match s.items[p.2]? with
  | some (.ins a) => return some ((p.1, p.2 + 1), facts.push a)
  | some (.fact a) => return some ((p.1, p.2 + 1), facts.push a)
  | _ => return none

/-- Bindings of values (by number) to cells, if consistent with what is known. -/
def unify (pairs : List (ℕ × ℕ)) : WM (Option (List (ℕ × ℕ))) := do
  let st ← get
  let ctx ← read
  let mut b : Std.HashMap ℕ ℕ := {}
  for (v, c) in pairs do
    let have_ := (st.loc.get? v).orElse fun _ => b.get? v
    match have_ with
    | some c' => if c' != c then return none
    | none =>
      if let some lim := st.pend.get? v then
        unless ((ctx.setCells.get? lim).getD []).contains c do return none
    b := b.insert v c
  return some (pairs.filterMap fun (v, _) => (b.get? v).map (v, ·)).eraseDups

def bind (bs : List (ℕ × ℕ)) : WM Bool := do
  let st ← get
  for (v, c) in bs do
    if let some c' := st.loc.get? v then
      if c' != c then return false
  modify fun st => { st with loc := bs.foldl (fun m (v, c) => m.insert v c) st.loc }
  return true

/-- The fact `pred` matches, among those passed (one fully known first), else forward, else any
unused, else any. -/
def find (p : Pos) (facts : Array Exec.Atom)
    (pred : Exec.Atom → WM (Option (List (ℕ × ℕ)))) :
    WM (Pos × Array Exec.Atom × Exec.Atom × List (ℕ × ℕ)) := do
  let mut cons : Array (Exec.Atom × List (ℕ × ℕ) × ℕ) := #[]
  for h : k in [0:facts.size] do
    let ft := facts[k]
    if let some r ← pred ft then cons := cons.push (ft, r, k)
  let st ← get
  let use (k : ℕ) : WM Unit := modify fun st => { st with uses := st.uses.push (st.curTop, k) }
  for (ft, r, k) in cons do
    if r.all fun (v, c) => st.loc.get? v == some c then use k; return (p, facts, ft, r)
  let mut q := p
  let mut fs := facts
  repeat
    match ← consume q fs with
    | none => break
    | some (q', fs') =>
      q := q'
      fs := fs'
      if let some r ← pred fs.back! then return (q, fs, fs.back!, r)
  for (ft, r, k) in cons do
    if !st.used.contains (atomKey ft) then use k; return (p, facts, ft, r)
  match cons[0]? with
  | some (ft, r, k) => use k; return (p, facts, ft, r)
  | none => throw s!"not found at {p}"

def go (p : Pos) (facts : Array Exec.Atom) (pred : Exec.Atom → WM (Option (List (ℕ × ℕ)))) :
    WM (Pos × Array Exec.Atom) := do
  let (p, facts, ft, r) ← find p facts pred
  modify fun st => { st with used := st.used.insert (atomKey ft) }
  let _ ← bind r
  return (p, facts)

def vi (v : Core.V) : ℕ := v.idx

def limbsOfE (x : E) : ℕ × ℕ × ℕ := limbsOf x

def xorPred (d a b : ℕ) (ft : Exec.Atom) : WM (Option (List (ℕ × ℕ))) := do
  match ft with
  | .instr _ (.xor x y z) =>
    for (p, q, r) in [(x, y, z), (y, x, z), (z, y, x), (y, z, x), (x, z, y), (z, x, y)] do
      if let some bs ← unify [(a, p), (b, q), (d, r)] then return some bs
    return none
  | _ => return none

def mulPred (d a b : ℕ) (ft : Exec.Atom) : WM (Option (List (ℕ × ℕ))) := do
  match ft with
  | .instr _ (.mul x y z) =>
    if let some bs ← unify [(a, x), (b, y), (d, z)] then return some bs
    unify [(a, y), (b, x), (d, z)]
  | _ => return none

def setPred (c : ℕ) (l : ℕ × ℕ × ℕ) (ft : Exec.Atom) : WM (Option (List (ℕ × ℕ))) := do
  match ft with
  | .instr _ (.set o k0 k1 k2) => return if o == c && (k0, k1, k2) == l then some [] else none
  | _ => return none

def derefPred (off : ℕ) (p d : ℕ) (ft : Exec.Atom) : WM (Option (List (ℕ × ℕ))) := do
  match ft with
  | .instr _ (.deref o1 o2 o3 .cell) => if o2 == off then unify [(p, o1), (d, o3)] else return none
  | _ => return none

def copyPred (d x : ℕ) (ft : Exec.Atom) : WM (Option (List (ℕ × ℕ))) := do
  match ft with
  | .copy a b | .eq a b =>
    if let some bs ← unify [(d, a), (x, b)] then return some bs
    unify [(d, b), (x, a)]
  | _ => return none

/-- Infer the cells of one atom's values. -/
def atom (a : Core.Atom) (p : Pos) (facts : Array Exec.Atom) : WM (Pos × Array Exec.Atom) := do
  let loc := (← get).loc
  match a with
  | .hint _ => return (p, facts)
  | .const d x =>
    match loc.get? (vi d) with
    | some c => go p facts (setPred c (limbsOfE x))
    | none =>
      modify fun st => { st with pend := st.pend.insert (vi d) (limbsOfE x) }
      return (p, facts)
  | .add d a b => go p facts (xorPred (vi d) (vi a) (vi b))
  | .mul d a b => go p facts (mulPred (vi d) (vi a) (vi b))
  | .copy d x =>
    match loc.get? (vi d), loc.get? (vi x) with
    | some c, some c' => if c == c' then return (p, facts) else go p facts (copyPred (vi d) (vi x))
    | none, some cx =>
      try
        go p facts fun ft => match ft with
          | .copy a b => if b == cx then unify [(vi d, a)] else return none
          | _ => return none
      catch _ =>
        modify fun st => { st with loc := st.loc.insert (vi d) cx }
        return (p, facts)
    | _, _ => go p facts (copyPred (vi d) (vi x))
  | .load d q off => go p facts (derefPred off (vi q) (vi d))
  | .assertEq x y =>
    match loc.get? (vi x), loc.get? (vi y) with
    | some c, some c' => if c == c' then return (p, facts) else go p facts (copyPred (vi x) (vi y))
    | cx, cy =>
      try go p facts (copyPred (vi x) (vi y))
      catch e =>
        match cx, cy with
        | some c, none => modify fun st => { st with loc := st.loc.insert (vi y) c }; return (p, facts)
        | none, some c => modify fun st => { st with loc := st.loc.insert (vi x) c }; return (p, facts)
        | _, _ => throw e
  | .assertNe x i q =>
    let (p, facts) ← go p facts (mulPred (vi q) (vi x) (vi i))
    let c := ((← get).loc.get? (vi q)).getD 0
    go p facts (setPred c (1, 0, 0))
  | .rangeCheck x y t1 t2 k =>
    let (p, facts) ← go p facts (derefPred 0 (vi x) (vi t1))
    let (p, facts) ← go p facts (mulPred (vi k) (vi x) (vi y))
    go p facts (derefPred 0 (vi y) (vi t2))
  | .assertInK x y =>
    go p facts fun ft => match ft with
      | .jump _ od of => unify [(vi x, od), (vi y, of)]
      | _ => return none
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
    go p facts fun ft => match ft with
      | .instr _ (.blake2s n0 n1 n2 n3 cv out d) =>
        unify [(vi m0, n0), (vi m1, n1), (vi m2, n2), (vi m3, n3), (vi cv0, cv), (vi cv1, cv + 1),
          (vi o0, out), (vi o1, out + 1), (vi md, d)]
      | _ => return none
  | .frameAddr q run =>
    modify fun st => { st with fa := st.fa.push (vi q, run.map vi) }
    return (p, facts)

/-- Pass every item before the next branch or the end; the position and the segment's exit
there, if at its end. -/
def toEnd (p : Pos) (facts : Array Exec.Atom) : WM (Pos × Array Exec.Atom × Option GExit) := do
  let mut q := p
  let mut fs := facts
  repeat
    match ← consume q fs with
    | none => break
    | some (q', fs') => q := q'; fs := fs'
  let s ← getSeg q.1
  return (q, fs, if q.2 ≥ s.items.size then some s.exit else none)

def toBranch (p : Pos) (facts : Array Exec.Atom) :
    WM (Pos × Array Exec.Atom × ℕ × GExit) := do
  let (q, fs, _) ← toEnd p facts
  let s ← getSeg q.1
  match s.items[q.2]? with
  | some (.branch oc _ _ x) => return (q, fs, oc, x)
  | _ => throw s!"no branch at {q}"

/-- The offsets a block's end leads to by local jumps: its own segment when fresh. -/
partial def chain (p : Pos) (n : ℕ := 6) : WM (List ℕ) := do
  if n == 0 then return []
  let s ← getSeg p.1
  let here := if p.2 == 0 then [p.1] else []
  if s.items.toList.drop p.2 |>.any (fun | .branch .. => true | _ => false) then return here
  match s.exit.kind with
  | .next t => if (← read).segs.contains t then return here ++ (← chain (t, 0) (n - 1)) else return here
  | _ => return here

def meet (ends : List Pos) : WM (Option ℕ) := do
  let cs ← ends.mapM (chain ·)
  match cs with
  | [] => return none
  | c :: rest =>
    match c.find? fun J => rest.all (·.contains J) with
    | some J => return some J
    | none => throw s!"no join for {ends}"

/-- Bind the cells stored into `fp[q]` from offset `o`. -/
def bindStores (facts : Array Exec.Atom) (q o : ℕ) (args : List Core.V) : WM Unit := do
  for (a, i) in args.zipIdx do
    for ft in facts do
      match ft with
      | .instr _ (.deref q' o' o3 .cell) =>
        if q' == q && o' == o + i then
          if ← bind [(vi a, o3)] then break
      | _ => pure ()

mutual
/-- Walk a block; where it ends (`none` after a return). -/
partial def block (ss : List Core.Stmt) (p : Pos) (facts : Array Exec.Atom) (top : Bool := false) :
    WM (Option Pos) := do
  let mut p := p
  let mut facts := facts
  let mut loads : Option (ℕ × ℕ × ℕ) := none
  for (s, idx) in ss.zipIdx do
    if top then modify fun st => { st with marks := st.marks.push (idx, p, facts.size, loads), curTop := idx }
    loads := none
    match s with
    | .atom a =>
      let (p', f') ← atom a p facts
      p := p'
      facts := f'
    | .ite c z n =>
      let (q, fs, oc, x) ← toBranch p facts
      let _ ← bind [(vi c, oc)]
      let .next t := x.kind | throw "ite kind"
      let rz ← block z (q.1, q.2 + 1) fs
      let rn ← block n (t, 0) fs
      match ← meet ([rz, rn].filterMap id) with
      | some J => p := (J, 0); facts := fs
      | none => return none
    | .match_ _ arms =>
      let (q, fs, x?) ← toEnd p facts
      let some x := x? | throw "match end"
      let rs ← (arms.zip x.succ).mapM fun (a, t) => block a (t, 0) fs
      match ← meet (rs.filterMap id) with
      | some J => p := (J, 0); facts := fs; let _ := q
      | none => return none
    | .call _ args rets | .dispatch _ _ args rets =>
      let (_, fs, x?) ← toEnd p facts
      let some x := x? | throw "call end"
      let .call _ q r := x.kind | throw "call kind"
      bindStores fs q 2 args
      let e := (← read).entry
      let p' : Pos := (r - e, 0)
      let (_, fs', _) ← toEnd p' fs
      bindStores (fs'.extract fs.size fs'.size) q (2 + args.length) rets
      p := p'
      facts := fs
      unless rets.isEmpty do loads := some (q, 2 + args.length, rets.length)
    | .callIf c _ args =>
      let (q, fs, oc, x) ← toBranch p facts
      let _ ← bind [(vi c, oc)]
      match x.kind with
      | .call _ fq r =>
        bindStores fs fq 2 args
        p := (r - (← read).entry, 0)
        facts := fs
      | .jump _ (.fpg S) =>
        for (a, i) in args.zipIdx do
          for ft in fs do
            match ft with
            | .copy d src => if d == S + 2 + i then if ← bind [(vi a, src)] then break
            | _ => pure ()
        p := (q.1, q.2 + 1)
        facts := fs
      | _ => throw "callIf kind"
    | .ret vs =>
      if top then modify fun st => { st with spine := facts }
      let _ ← toEnd p facts
      let na := (← read).na
      for (v, i) in vs.zipIdx do
        let _ ← bind [(vi v, 2 + na + i)]
      modify fun st => { st with nr := vs.length }
      let _ := idx
      return none
  return some p
end

/-- The cells of a function's values, by number, `0` for a value on no path. -/
def inferLocs (segs : Array GSeg) (f : CompiledFn) (cf : Core.Fn) (main : Bool) :
    Except String (List ℕ × ℕ × Array (ℕ × Pos × ℕ × Option (ℕ × ℕ × ℕ)) × Array Exec.Atom ×
      Array (ℕ × ℕ)) := do
  let segMap := segs.foldl (fun m s => m.insert s.start s) ({} : Std.HashMap ℕ GSeg)
  let setCells := f.code.foldl (fun m ins => match ins with
    | .set o k0 k1 k2 => m.insert (k0, k1, k2) (o :: (m.get? (k0, k1, k2)).getD [])
    | _ => m) ({} : Std.HashMap (ℕ × ℕ × ℕ) (List ℕ))
  let ctx : WCtx := ⟨segMap, setCells, f.entry, cf.params.length, main⟩
  let loc0 : Loc := (cf.params.zipIdx.map fun (v, i) => (vi v, 2 + i)).foldl
    (fun m (v, c) => m.insert v c) {}
  let init : WSt := { loc := loc0 }
  let (_, st) ← ((block cf.body (0, 0) #[] true).run ctx).run init
  let mut loc := st.loc
  for (q, run) in st.fa do
    let _ := q
    match (run.zipIdx.find? fun (v, _) => loc.contains v) with
    | some (v, j) =>
      let base := loc.get! v - j
      for (v', j') in run.zipIdx do
        unless loc.contains v' do loc := loc.insert v' (base + j')
    | none => pure ()
  for (v, l) in st.pend.toList do
    unless loc.contains v do
      let cs := (setCells.get? l).getD []
      loc := loc.insert v (cs.foldl min (cs.headD 0))
  let m := loc.fold (fun m v _ => max m (v + 1)) 0
  return ((List.range m).map fun v => loc.getD v 0, st.nr, st.marks, st.spine, st.uses)

end GuestCert

namespace GuestCert

/-! ## The facts and the certificates -/

/-- A trie literal: key `0` at the root, `2m+1` at key `m` of the left child, `2m+2` of the
right one. -/
inductive T where
  | nil
  | node (v : Option String) (l r : T)

def T.ins : T → ℕ → String → T
  | .nil, 0, v => .node (some v) .nil .nil
  | .node _ l r, 0, v => .node (some v) l r
  | t, n + 1, v =>
    let (o, l, r) := match t with
      | .nil => (none, T.nil, T.nil)
      | .node o l r => (o, l, r)
    if n % 2 == 0 then .node o (l.ins (n / 2) v) r else .node o l (r.ins (n / 2) v)

def T.text : T → String
  | .nil => ".nil"
  | .node v l r =>
    let v := match v with
      | some s => s!"(some {s})"
      | none => "none"
    s!"(.node {v} {l.text} {r.text})"

def trieLit (kvs : List (ℕ × String)) : String :=
  (kvs.foldl (fun t (k, v) => t.ins k v) T.nil).text

def symText : Sym → String
  | .zero => ".zero"
  | .gp e => s!"(.gp {e})"
  | .fpg e => s!"(.fpg {e})"

/-- A balanced search tree of the pairs, as a `PowTree` literal. -/
partial def powTreeText (ps : Array (ℕ × ℕ)) : String :=
  if ps.isEmpty then ".leaf"
  else
    let m := ps.size / 2
    let (k, e) := ps[m]!
    s!"(.node {k} {e} {powTreeText (ps.extract 0 m)} {powTreeText (ps.extract (m + 1) ps.size)})"

/-- What the program's tables give the generator. -/
structure Tables where
  pows : Std.HashMap ℕ ℕ
  jt : Std.HashMap ℕ ℕ
  regions : Std.HashMap ℕ ℕ
  self : Std.HashMap ℕ ℕ

def tables (fns : List CompiledFn) : Tables :=
  let f0 := fns.head!
  let jt := jumpTable f0
  let jtEnd := (jt.fold (fun m s _ => max m s) 0) + 1
  let pows := (fns.flatMap setPows).foldl (fun m (k, e) => m.insert k e) {}
  ⟨pows, jt, tableRegions fns jtEnd, selfCells fns⟩

/-- The executor's facts of a function. -/
def factsOf (T : Tables) (f : CompiledFn) (main : Bool) : GFacts := Id.run do
  let c := f.code.toArray
  let n := c.size
  let env := match T.self.get? f.entry with
    | some o => [(o, Sym.fpg 0)]
    | none => []
  let mut arms : Std.HashMap ℕ (List ℕ) := {}
  for i in [1:n] do
    match c[i - 1]!, c[i]! with
    | .deref _ t o3 .cell, .jump _ od _ =>
      if o3 == od then
        let size := (T.regions.get? t).getD 0
        let tg := (List.range size).map fun s => (T.jt.get? (t + s)).getD 0
        if tg.all fun x => f.entry < x && x < f.entry + n then
          arms := arms.insert i (tg.map (· - f.entry))
    | _, _ => pure ()
  return ⟨T.pows, env, main, arms⟩

/-- The callees of a core function, by name. -/
partial def calleesOf : List Core.Stmt → List String
  | [] => []
  | s :: ss => (match s with
    | .call f _ _ => [f]
    | .callIf _ f _ => [f]
    | .dispatch _ fs _ _ => fs
    | .ite _ z n => calleesOf z ++ calleesOf n
    | .match_ _ arms => arms.flatMap calleesOf
    | _ => []) ++ calleesOf ss

/-- The memory bounds a function's top-level calls need of their arguments, `(statement, value,
len, n)`: obligations its proof takes from the statements before the call. -/
def knownOf (body : List Core.Stmt) (memOf : String → List (ℕ × ℕ × ℕ)) :
    List (ℕ × ℕ × ℕ × ℕ) :=
  body.zipIdx.flatMap fun
    | (.call g args _, i) => (memOf g).filterMap fun (o, len, n) =>
        (args[o - 2]?).map fun v => (i, v.idx, len, n)
    | _ => []

/-- The pairs of frame cells a function assumes in the semantic relation (`Glob.sem`, the
exponent tables): `verify_sub`'s arguments 4 and 5, and the loop calling it, which receives
them as arguments 16 and 6. -/
def semOf (name : String) : List (ℕ × ℕ) :=
  if name == "verify_sub" then [(6, 7)] else if name == "__loop5" then [(18, 8)] else []

/-- The semantic pairs a function learns from a top-level call, `(statement after it, value,
value)`: the two tables `exponent_tables` returns. -/
def semsOf (body : List Core.Stmt) : List (ℕ × ℕ × ℕ) :=
  body.zipIdx.filterMap fun
    | (.call "exponent_tables" [] [p, q], i) => some (i + 1, p.idx, q.idx)
    | _ => none

/-- The bounds of the functions whose table jumps are bounded outside them (DESIGN.md): before,
after, and on memory, and the memory bounds they take from named obligations. -/
def bounds (name : String) :
    List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) :=
  if name == "da_list_digest" then ([(3, 17)], [], [], [])
  else if name == "da_row_shape" then ([], [(3, 11)], [], [])
  else if name == "check_opening_terminal" then ([], [], [(12, 92, 29)], [])
  else if name == "__loop90" || name == "__loop91" || name == "da_verify_column__L0" ||
    name == "da_verify_column__L1" then ([(6, 11)], [], [], [])
  else ([], [], [], [])

/-! ## Windows -/

/-- The cells an atom is filed under (`Check.keys`). -/
def keysG : Exec.Atom → List ℕ
  | .instr _ (.xor _ _ c) => [c]
  | .instr _ (.mul _ _ c) => [c]
  | .instr _ (.set o _ _ _) => [o]
  | .instr _ (.deref _ _ o3 .cell) => [o3]
  | .instr _ (.deref o1 _ _ .fp) => [o1]
  | .instr _ (.blake2s _ _ _ _ _ out _) => [out]
  | .jump _ od _ => [od]
  | .copy d s => [d, s]
  | .eq a b => [a, b]
  | .range x _ _ => [x]
  | _ => []

/-- The cells whose facts a handed-on fact may need (`Check.addrOkC`: the factors of a frame
address and the pointer of a bounce). -/
def needsG : Exec.Atom → List ℕ
  | .instr _ (.mul x y _) => [x, y]
  | .instr _ (.deref h _ _ .cell) => [h]
  | _ => []

def modeText : LeanVM.Semantics.DerefMode → String
  | .cell => ".cell"
  | .fp => ".fp"
  | .pc => ".pc"

def instrText : OInstr → String
  | .xor a b c => s!"(.xor {a} {b} {c})"
  | .mul a b c => s!"(.mul {a} {b} {c})"
  | .set o k0 k1 k2 => s!"(.set {o} {k0} {k1} {k2})"
  | .deref a b c m => s!"(.deref {a} {b} {c} {modeText m})"
  | .jump a b c => s!"(.jump {a} {b} {c})"
  | .blake2s a b c d e f g => s!"(.blake2s {a} {b} {c} {d} {e} {f} {g})"

def atomText : Exec.Atom → String
  | .instr pc i => s!"(.instr {pc} {instrText i})"
  | .jump a b c => s!"(.jump {a} {b} {c})"
  | .copy a b => s!"(.copy {a} {b})"
  | .eq a b => s!"(.eq {a} {b})"
  | .nz x => s!"(.nz {x})"
  | .ne a b => s!"(.ne {a} {b})"
  | .bool x => s!"(.bool {x})"
  | .range x y k => s!"(.range {x} {y} {k})"
  | .powPair x y z => s!"(.powPair {x} {y} {z})"

/-- A window's start after the first, as `Check.Cut`, with the previous window's end `b`. -/
structure CutG where
  J : ℕ
  env : List (ℕ × Sym)
  start : ℕ
  facts : List (ℕ × Exec.Atom)
  bnd : List (ℕ × ℕ)
  known : List (ℕ × ℕ × ℕ)
  sems : List (ℕ × ℕ)
  b : ℕ

/-- The instructions a window runs over at most, when a function is cut for its size. -/
def maxWin : ℕ := 1000

/-- Where a window can start at a mark: its offset `J` and the previous window's end `b` (`J + 1`
at a segment's start the walk enters, `J` when the walk reaches `J` by the end of its segment),
with the facts passed there after the mark's (the returned words read back). -/
def cutAtMark (segMap : Std.HashMap ℕ GSeg) (entry : ℕ)
    (m : ℕ × Pos × ℕ × Option (ℕ × ℕ × ℕ)) : Option (ℕ × ℕ × Array Exec.Atom) := do
  let (_, p, _, loads) := m
  let s ← segMap.get? p.1
  let mut i := p.2
  let mut fs : Array Exec.Atom := #[]
  if let some (q, o, n) := loads then
    let mut need := n
    while need > 0 do
      match s.items[i]? with
      | some (.ins a) | some (.fact a) =>
        fs := fs.push a
        i := i + 1
        match a with
        | .instr _ (.deref q' o' _ .cell) => if q' == q && o ≤ o' && o' < o + n then need := need - 1
        | _ => pure ()
      | _ => none
  if i == 0 && loads.isNone then return (p.1, p.1 + 1, fs)
  let mut j := i
  repeat
    match s.items[j]? with
    | some (.ins (.instr pc _)) => return (pc - entry, pc - entry, fs)
    | some (.fact a) | some (.ins a) => fs := fs.push a; j := j + 1
    | some (.branch ..) => none
    | none => break
  match s.exit.kind with
  | .next t => if s.exit.succ == [t] then return (t, t, fs) else none
  | _ => none

/-- What later statements look up beyond the facts they find: the cells of frame addresses,
selectors and bounded call arguments, and the constants' cells and limbs. -/
partial def laterNeeds (cellOf : Core.V → ℕ) : List Core.Stmt → List ℕ × List (ℕ × ℕ × ℕ × ℕ)
  | [] => ([], [])
  | s :: ss =>
    let preCells (g : String) (args : List Core.V) : List ℕ :=
      (bounds g).1.filterMap fun (o, _) => (args[o - 2]?).map cellOf
    let (a, b) := laterNeeds cellOf ss
    let (a', b') : List ℕ × List (ℕ × ℕ × ℕ × ℕ) := match s with
      | .atom (.frameAddr q _) => ([cellOf q], [])
      | .atom (.const v x) => let (k0, k1, k2) := limbsOfE x; ([], [(cellOf v, k0, k1, k2)])
      | .match_ x arms => arms.foldl (fun (a, b) arm => let (a2, b2) := laterNeeds cellOf arm; (a ++ a2, b ++ b2))
          ([cellOf x], [])
      | .ite _ z n => let (a1, b1) := laterNeeds cellOf z; let (a2, b2) := laterNeeds cellOf n; (a1 ++ a2, b1 ++ b2)
      | .dispatch x fs args _ => (cellOf x :: fs.flatMap (preCells · args), [])
      | .call g args _ => (preCells g args, [])
      | .callIf _ g args => (preCells g args, [])
      | _ => ([], [])
    (a' ++ a, b' ++ b)

/-- The windows of a function: a cut before each statement in `forced` (with the memory bounds
and semantic pairs it starts knowing), and, in a function longer than `maxWin`, wherever the
next window would grow past it. -/
def planCuts (F : GFacts) (f : CompiledFn) (cf : Core.Fn) (locs : List ℕ)
    (marks : Array (ℕ × Pos × ℕ × Option (ℕ × ℕ × ℕ))) (spine : Array Exec.Atom)
    (uses : Array (ℕ × ℕ)) (segMap : Std.HashMap ℕ GSeg)
    (pre : List (ℕ × ℕ)) (forced : List (ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ))) :
    Except String (List CutG) := do
  let cellOf (v : Core.V) : ℕ := locs.getD v.idx 0
  -- the first `SET` of each top-level constant's cell and limbs: a window ends after it
  let setAt := f.code.zipIdx.foldl (fun (m : Std.HashMap (ℕ × ℕ × ℕ × ℕ) ℕ) (ins, i) =>
    match ins with
    | .set o k0 k1 k2 => if m.contains (o, k0, k1, k2) then m else m.insert (o, k0, k1, k2) i
    | _ => m) {}
  let constAt : Array ℕ := (cf.body.toArray.map fun
    | .atom (.const v x) => let (k0, k1, k2) := limbsOfE x; (setAt.get? (cellOf v, k0, k1, k2)).getD f.len
    | _ => 0)
  let constMax : Array ℕ := constAt.foldl (fun acc o => acc.push (max o (acc.back?.getD 0))) #[0]
  let cands := marks.filterMap fun m => (cutAtMark segMap f.entry m).bind fun c =>
    if constMax.getD m.1 0 < c.1 then some (m.1, c) else none
  for (i, _, _) in forced do
    unless cands.any (·.1 == i) do throw s!"{f.name}: no window can start at statement {i}"
  let big := f.len > 3 * maxWin
  let mut a := 0
  let mut env : List (ℕ × Sym) := F.env
  let mut known : List (ℕ × ℕ × ℕ) := []
  let mut sems : List (ℕ × ℕ) := []
  let mut out : Array CutG := #[]
  -- what the previous window starts with and the facts it passes: a window hands on only those
  let mut prevN := 0
  let mut prevHanded : Std.HashSet String := {}
  for k in [0:cands.size] do
    let (idx, J, b, extra) := cands[k]!
    let force := forced.find? (·.1 == idx)
    let nextJ := if k + 1 < cands.size then cands[k + 1]!.2.1 else f.len
    unless force.isSome || (big && nextJ - a > maxWin && J ≥ a + maxWin / 4 && f.len - J > maxWin / 4) do continue
    if J ≤ a then throw s!"{f.name}: cut {idx} at {J} not after {a}"
    if let some (_, kn, sm) := force then
      known := known ++ kn
      sems := sems ++ sm
    let segs := execG F f a b (env.foldl (fun m (o, s) => m.insert o s) {})
    let env' ← match segs.find? (fun s => s.start == J) with
      | some s => if b == J + 1 then pure s.env else throw s!"{f.name}: cut {idx}"
      | none => match segs.find? (fun s => s.exit.kind == .next J) with
        | some s => pure s.exit.env
        | none => throw s!"{f.name}: no exit to {J}"
    let n := ((marks.find? (·.1 == idx)).map (·.2.2.1)).getD 0
    -- the passed facts later statements found, and those under the cells of later frame
    -- addresses and selectors
    let later := cf.body.drop idx
    let (selL, consts) := laterNeeds cellOf later
    let sel : Std.HashSet ℕ := selL.foldl (·.insert ·) {}
    let constSet : Std.HashSet (ℕ × ℕ × ℕ × ℕ) := consts.foldl (·.insert ·) {}
    let isConst : Exec.Atom → Bool
      | .instr _ (.set o k0 k1 k2) => constSet.contains (o, k0, k1, k2)
      | _ => false
    let used : Std.HashSet ℕ := uses.foldl (fun h (t, k) => if t ≥ idx && k < n + extra.size then h.insert k else h) {}
    let fs := spine.extract 0 n ++ extra
    let avail (a : Exec.Atom) (k : ℕ) : Bool := k ≥ prevN || prevHanded.contains (atomText a)
    let direct := fs.zipIdx.filter fun (a, k) =>
      avail a k && (used.contains k || isConst a || (keysG a).any sel.contains)
    let need : Std.HashSet ℕ := direct.foldl (fun h (a, _) => (needsG a).foldl (·.insert ·) h) {}
    let hand := direct ++ fs.zipIdx.filter fun (a, k) => avail a k && (keysG a).any need.contains
    let (handed, seen) := (hand.toList.flatMap fun (a, _) => (keysG a).map (·, a)).foldl
      (fun (acc, seen) (k, a) => let key := s!"{k}{atomText a}"
        if seen.contains key then (acc, seen) else (acc.push (k, a), seen.insert key))
      ((#[] : Array (ℕ × Exec.Atom)), ({} : Std.HashSet String))
    let _ := seen
    let handed := handed.toList
    prevN := n + extra.size
    prevHanded := handed.foldl (fun h (_, a) => h.insert (atomText a)) {}
    let envL := (env'.toList.mergeSort (·.1 ≤ ·.1))
    out := out.push ⟨J, envL, idx, handed, pre, known, sems, b⟩
    a := J
    env := envL
  return out.toList

structure CertOut where
  name : String
  text : String

def listText (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"

def pairText (p : ℕ × ℕ) : String := s!"({p.1}, {p.2})"

def tripText (p : ℕ × ℕ × ℕ) : String := s!"({p.1}, {p.2.1}, {p.2.2})"

/-- The values per definition of a certificate's cells. -/
def locChunk : ℕ := 2000

/-- The certificate of function `j`. -/
def certOf (T : Tables) (fns : Array CompiledFn) (index : Std.HashMap String ℕ) (j : ℕ)
    (cf : Core.Fn) : Except String (String × List ℕ) := do
  let f := fns[j]!
  let main := j == 1
  let F := factsOf T f main
  let segs := execG F f 0 f.len (F.env.foldl (fun m (o, s) => m.insert o s) {})
  let (locs, nr, marks, spine, uses) ← (inferLocs segs f cf main).mapError (s!"{f.name}: " ++ ·)
  let callees := ((calleesOf cf.body).filterMap index.get?).eraseDups.mergeSort
  let (pre, post, mem, _) := bounds f.name
  let cell (v : ℕ) : ℕ := locs.getD v 0
  let forced := (knownOf cf.body (fun g => (bounds g).2.2.1)).map (fun (i, v, len, n) =>
      (i, [(cell v, len, n)], ([] : List (ℕ × ℕ)))) ++
    (semsOf cf.body).map fun (i, p, q) => (i, ([] : List (ℕ × ℕ × ℕ)), [(cell p, cell q)])
  let segMap := segs.foldl (fun m s => m.insert s.start s) ({} : Std.HashMap ℕ GSeg)
  let cuts ← planCuts F f cf locs marks spine uses segMap pre forced
  let cutT := listText (cuts.map fun c =>
    s!"⟨{c.J}, {listText (c.env.map fun (o, s) => s!"({o}, {symText s})")}, {c.start},\n      " ++
    s!"{listText (c.facts.map fun (k, a) => s!"({k}, {atomText a})")},\n      " ++
    s!"{listText (c.bnd.map pairText)}, {listText (c.known.map tripText)}, {listText (c.sems.map pairText)}⟩")
  let envT := listText (F.env.map fun (o, s) => s!"({o}, {symText s})")
  let armsT := listText ((F.arms.toList.mergeSort (·.1 ≤ ·.1)).map fun (i, a) =>
    s!"({i}, {listText (a.map toString)})")
  let scaled := listText (F.env.map (toString ·.1))
  -- each window's cells: the values from where the previous window's end, up to the last value
  -- its statements name, and the earlier values they name with the window holding them
  let wStarts := (0 :: cuts.map (·.start)).toArray
  let nw := wStarts.size
  let mut los : Array ℕ := #[]
  let mut his : Array ℕ := #[]
  let mut insW : Array (List (ℕ × ℕ × ℕ)) := #[]
  let mut hi := 0
  for w in [0:nw] do
    let a := wStarts[w]!
    let b := if w + 1 < nw then wStarts[w + 1]! else cf.body.length
    let vs := (Check.stmtsVals ((cf.body.drop a).take (b - a))).map (·.idx) ++
      (if w == 0 then cf.params.map (·.idx) else [])
    let lo := hi
    hi := vs.foldl (fun h v => max h (v + 1)) hi
    if w + 1 == nw then hi := max hi locs.length
    los := los.push lo
    his := his.push hi
    let homeOf (v : ℕ) : ℕ := ((List.range w).reverse.find? fun u => los[u]! ≤ v).getD 0
    let ins := (vs.filter (· < lo)).eraseDups.mergeSort
    insW := insW.push (ins.map fun v => (v, locs.getD v 0, homeOf v))
  let litOf (l : List ℕ) : String := if l.length < 32 then listText (l.map toString)
    else "(" ++ " :: ".intercalate (l.map toString) ++ " :: [])"
  let mut locDefs := ""
  let mut cellT : Array String := #[]
  for w in [0:nw] do
    let cs := (locs.drop los[w]!).take (his[w]! - los[w]!)
    let chunks := (List.range ((cs.length + locChunk - 1) / locChunk)).map fun c =>
      (cs.drop (c * locChunk)).take locChunk
    locDefs := locDefs ++ String.join (chunks.zipIdx.map fun (l, c) =>
      s!"/-- `{f.name}`: window {w}'s cells, of values {los[w]! + c * locChunk} on. -/\n" ++
      s!"def cert{j}_w{w}_{c} : List ℕ := {litOf l}\n\n")
    cellT := cellT.push (if chunks.isEmpty then "[]"
      else "(" ++ " ++ ".intercalate (chunks.zipIdx.map fun (_, c) => s!"cert{j}_w{w}_{c}") ++ ")")
  let insT := listText (insW.toList.map fun l => listText (l.map fun (v, c, h) => s!"({v}, {c}, {h})"))
  let starts := 0 :: cuts.map (·.J)
  let stops := cuts.map (·.b) ++ [f.len]
  let sizes := (starts.zip stops).map fun (a, b) => b - a
  return (·, sizes) <| locDefs ++ s!"/-- `{f.name}`. -/
noncomputable def cert{j} : Check.Cert where
  facts := \{ env := {envT}, fpOne := {main}, arms := {armsT}, scaled := {scaled} }
  los := {listText (los.toList.map toString)}
  cells := {listText cellT.toList}
  ins := {insT}
  nret := {nr}
  callees := {listText (callees.map toString)}
  pre := {listText (pre.map pairText)}
  post := {listText (post.map pairText)}
  mem := {listText (mem.map tripText)}
  sem := {listText ((semOf f.name).map pairText)}
  cuts := {cutT}
  ends := {listText (cuts.map (toString ·.b))}
"

end GuestCert

namespace GuestCert

/-! ## Files -/

def maxFile : ℕ := 1500000

def header (mod what : String) : String :=
  s!"/-
  LeanVM.Guest.Data.{mod}

  Generated by `lake exe guest-cert` (formal/lean_vm/cli/GuestCert.lean); do not edit.
  {what}
-/

module

"

def fileName (k : ℕ) : String := if k < 10 then s!"Cert0{k}" else s!"Cert{k}"

def preamble : String := "
namespace LeanVM.Guest.Data

open LeanVM.Guest LeanVM.Guest.Exec

set_option maxRecDepth 100000
set_option linter.all false

@[expose] public section

"

def tail : String := "
end
end LeanVM.Guest.Data
"

/-- The levels of the power tree written out in `powTree`, its subtrees below them defined
apart (`powT{i}`), so that each is checked in a module of its own. -/
def powCut : ℕ := 4

/-- The top of a balanced tree over `ps`, the subtrees at depth `d` named `powT{i}` from `i`. -/
partial def powTop (ps : Array (ℕ × ℕ)) (d : ℕ) (i : ℕ) : String × List (Array (ℕ × ℕ)) :=
  if d == 0 then (s!"powT{i}", [ps])
  else if ps.isEmpty then (".leaf", [])
  else
    let m := ps.size / 2
    let (k, e) := ps[m]!
    let (l, ls) := powTop (ps.extract 0 m) (d - 1) i
    let (r, rs) := powTop (ps.extract (m + 1) ps.size) (d - 1) (i + ls.length)
    (s!"(.node {k} {e} {l} {r})", ls ++ rs)

/-- The proof of `powTree.OkW` from its subtrees', in the shape of `powTop`. -/
partial def powTopProof (ps : Array (ℕ × ℕ)) (d : ℕ) (i : ℕ) : String × ℕ :=
  if d == 0 then (s!"powT{i}_ok", 1)
  else if ps.isEmpty then ("trivial", 0)
  else
    let m := ps.size / 2
    let (l, nl) := powTopProof (ps.extract 0 m) (d - 1) i
    let (r, nr) := powTopProof (ps.extract (m + 1) ps.size) (d - 1) (i + nl)
    (s!"⟨by decide, by decide +kernel, {l}, {r}⟩", nl + nr)

/-- `g^(d·16^w)` for `w < 5`, `d < 16`. -/
def gtabText : String := Id.run do
  let mut rows : Array String := #[]
  let mut x : K := g
  for _ in List.range 5 do
    let mut row : Array String := #[]
    let mut y : K := 1
    for _ in List.range 16 do
      row := row.push (toString y.toBitVec.toNat)
      y := y * x
    rows := rows.push ("[" ++ ", ".intercalate row.toList ++ "]")
    x := y
  return "[" ++ ",\n  ".intercalate rows.toList ++ "]"

/-- The tables: the powers of `g` the guest names, the digit table and the jump table. -/
def powsFile (T : Tables) : String :=
  let ps := (T.pows.toArray.qsort (·.1 < ·.1))
  let (top, subs) := powTop ps powCut 0
  let jt := trieLit ((T.jt.toList.mergeSort (·.1 ≤ ·.1)).map fun (s, e) => (s, toString e))
  header "Pows" "The powers of `g` the guest's constants name, and its jump table." ++
  "public import LeanVM.Guest.Exec\n" ++ preamble ++
  String.join (subs.zipIdx.map fun (sub, i) =>
    s!"/-- Subtree {i} of `powTree`. -/\nnoncomputable def powT{i} : PowTree := {powTreeText sub}\n\n") ++
  s!"/-- The powers of `g` the guest's `SET`s name, bits to exponent, a search tree. -/
noncomputable def powTree : PowTree := {top}

/-- `g^(d·16^w)` at row `w`, column `d`, as bits. -/
def gtab : List (List ℕ) := {gtabText}

/-- The jump table: slot of `main`'s frame to the pc it holds (`__jump_tables`). -/
noncomputable def jtTrie : Trie ℕ := {jt}
" ++ tail

/-! ## The checks -/

def checkedDir : System.FilePath := "LeanVM/Guest/Checked"

/-- The instructions a module of checks holds at most, a function larger than it alone. -/
def maxChecked : ℕ := 2500

def checkedHeader (mod what : String) : String :=
  s!"/-
  LeanVM.Guest.Checked{if mod.isEmpty then "" else "." ++ mod}

  Generated by `lake exe guest-cert` (formal/lean_vm/cli/GuestCert.lean); do not edit.
  {what}
-/

module

"

def checkedName (k : ℕ) : String := if k < 10 then s!"Fn0{k}" else s!"Fn{k}"

def powName (k : ℕ) : String := if k < 10 then s!"Pow0{k}" else s!"Pow{k}"

/-- The modules deciding the checks: each window's (`(function, window, instructions)`), in
modules of consecutive windows, and each subtree of the power tree's. -/
def checkedFiles (wins : Array (ℕ × ℕ × ℕ)) (ps : Array (ℕ × ℕ)) (nPow : ℕ) :
    List (String × String) := Id.run do
  let fns := Data.functions.toArray
  let mut groups : Array (Array (ℕ × ℕ)) := #[#[]]
  let mut size := 0
  for (j, w, l) in wins do
    if size + l > maxChecked && size > 0 then
      groups := groups.push #[]
      size := 0
    groups := groups.modify (groups.size - 1) (·.push (j, w))
    size := size + l
  let pairs (js : Array (ℕ × ℕ)) : String := listText (js.toList.map pairText)
  let fnFiles := groups.toList.zipIdx.map fun (js, k) =>
    (checkedName k, checkedHeader (checkedName k) "The kernel's checks of windows of compiled functions." ++
      "public import LeanVM.Guest.Glob\n\nnamespace LeanVM.Guest.Checked\n\n" ++
      String.join (js.toList.map fun (j, w) =>
        s!"/-- `{fns[j]!.name}`, window {w}. -/\ntheorem w{j}_{w} : WinOk {j} {w} := by decide +kernel\n\n") ++
      s!"theorem wins{k} : ∀ p ∈ ({pairs js} : List (ℕ × ℕ)), WinOk p.1 p.2 :=\n  " ++
      String.join (js.toList.map fun (j, w) => s!"List.forall_mem_cons.2 ⟨w{j}_{w}, ") ++
      "fun _ h ↦ by cases h" ++ String.join (js.toList.map fun _ => "⟩") ++
      "\n\nend LeanVM.Guest.Checked\n")
  let powFiles := (List.range nPow).map fun i =>
    (powName i, checkedHeader (powName i) "The kernel's check of a subtree of the powers of `g`." ++
      s!"public import LeanVM.Guest.Pow\n\nnamespace LeanVM.Guest.Checked\n\n" ++
      s!"theorem powT{i}_ok : Data.powT{i}.OkW := by decide +kernel\n\nend LeanVM.Guest.Checked\n")
  let lists := " ++ ".intercalate (groups.toList.map pairs)
  let proofs := (groups.toList.zipIdx.map fun (_, k) => s!"wins{k}").foldr
    (fun w acc => if acc.isEmpty then w else s!"List.forall_mem_append.2 ⟨{w}, {acc}⟩") ""
  let index := ("Checked", checkedHeader "" "Every compiled function checked, and the powers of `g`." ++
    String.join ((fnFiles ++ powFiles).map fun (n, _) => s!"public import LeanVM.Guest.Checked.{n}\n") ++
    "\nnamespace LeanVM.Guest.Checked\n\nopen LeanVM.Guest.Exec\n\n" ++
    s!"/-- The windows checked. -/\ndef windows : List (ℕ × ℕ) :=\n  {lists}\n\n" ++
    "/-- Every function but `__jump_tables` is checked. -/\n" ++
    "theorem all_ok : ∀ j, 1 ≤ j → j < nFns → CheckOk j :=\n" ++
    s!"  checkOk_of_covers (ws := windows)\n    ({proofs})\n    (by decide +kernel)\n\n" ++
    "/-- Every power of `g` the guest names is one. -/\ntheorem powTree_ok : Data.powTree.OkW :=\n  " ++
    (powTopProof ps powCut 0).1 ++ "\n\nend LeanVM.Guest.Checked\n")
  return fnFiles ++ powFiles ++ [index]

def files (P : Core.Program) : Except String (List (System.FilePath × String)) := do
  let fns := Data.functions.toArray
  let T := tables Data.functions
  let index := (fns.toList.zipIdx.map fun (f, j) => (f.name, j)).foldl
    (fun m (n, j) => if m.contains n then m else m.insert n j) ({} : Std.HashMap String ℕ)
  let mut certs : Array String := #[]
  let mut wins : Array (ℕ × ℕ × ℕ) := #[]
  for (cf, i) in P.zipIdx do
    let (c, sizes) ← certOf T fns index (i + 1) cf
    certs := certs.push c
    wins := wins ++ (sizes.zipIdx.map fun (sz, w) => (i + 1, w, sz)).toArray
  let mut fs : Array (Array String) := #[#[]]
  let mut size := 0
  for c in certs do
    if size + c.length > maxFile && size > 0 then
      fs := fs.push #[]
      size := 0
    fs := fs.modify (fs.size - 1) (·.push c)
    size := size + c.length
  let certFiles := fs.toList.zipIdx.map fun (cs, k) =>
    (fileName k, header (fileName k) "Certificates of the guest's compiled functions." ++
      "public import LeanVM.Guest.Check\n" ++ preamble ++
      "\n".intercalate cs.toList ++ tail)
  let n := P.length
  let names := "cert0" :: (List.range n).map fun i => s!"cert{i + 1}"
  let rows := (List.range ((names.length + 15) / 16)).map fun r =>
    "  " ++ " ".intercalate (((names.drop (16 * r)).take 16).map (· ++ " ::"))
  let index := header "Cert" "The certificates of the guest's compiled functions, by index." ++
    String.join (certFiles.map fun (m, _) => s!"public import LeanVM.Guest.Data.{m}\n") ++
    preamble ++ "/-- `__jump_tables`: its facts only. -/
noncomputable def cert0 : Check.Cert where
  facts := {}
  los := []
  cells := []
  ins := []
  nret := 0
  callees := []

/-- The certificates, by compiled function index. -/
noncomputable def certs : List Check.Cert :=
" ++ "\n".intercalate rows ++ " []
" ++ tail
  let nPow := (powTop (T.pows.toArray.qsort (·.1 < ·.1)) powCut 0).2.length
  return (([("Pows", powsFile T)] ++ certFiles ++ [("Cert", index)]).map fun (n, t) =>
    (dataDir / (n ++ ".lean"), t)) ++
    (checkedFiles wins (T.pows.toArray.qsort (·.1 < ·.1)) nPow).map fun (n, t) =>
      (if n == "Checked" then ("LeanVM/Guest" : System.FilePath) / "Checked.lean"
        else checkedDir / (n ++ ".lean"), t)

/-- The generated files on disk. -/
def existing : IO (List System.FilePath) := do
  let gen (pre : String) (n : String) : Bool :=
    let cs := n.toList
    cs.take pre.length == pre.toList && cs.reverse.take 5 == ".lean".toList.reverse &&
      ((cs.drop pre.length).take (cs.length - pre.length - 5)).all Char.isDigit
  let ds ← dataDir.readDir
  let cs ← if ← checkedDir.isDir then checkedDir.readDir else pure #[]
  return (ds.toList.filter (gen "Cert" ·.fileName)).map (·.path) ++
    (cs.toList.filter fun e => gen "Fn" e.fileName || gen "Pow" e.fileName).map (·.path)

end GuestCert

open GuestCert in
def main (args : List String) : IO UInt32 := do
  let check := args == ["--check"]
  unless args.isEmpty || check do
    IO.eprintln "usage: guest-cert [--check]"
    return 2
  unless ← dataDir.isDir do
    IO.eprintln s!"{dataDir} not found: run from formal/lean_vm"
    return 2
  let P ← match Expand.expandProgram Data.guest with
    | .ok P => pure (P.map Core.Fn.renumber)
    | .error e => do IO.eprintln s!"expansion failed: {e}"; return 1
  let fs ← match files P with
    | .ok fs => pure fs
    | .error e => do IO.eprintln s!"certificate failed: {e}"; return 1
  unless check do IO.FS.createDirAll checkedDir
  let paths := fs.map (·.1)
  let stale := (← existing).filter (!paths.contains ·)
  let mut bad := false
  for (path, text) in fs do
    if check then
      let old ← if ← path.pathExists then IO.FS.readFile path else pure ""
      if old != text then
        IO.eprintln s!"{path} is stale"
        bad := true
    else
      IO.FS.writeFile path text
  for path in stale do
    if check then
      IO.eprintln s!"{path} is not generated"
      bad := true
    else
      IO.FS.removeFile path
  if bad then
    IO.eprintln "regenerate with `lake exe guest-cert`"
    return 1
  unless check do
    IO.println s!"{P.length} certificates in {fs.length} files"
  return 0
