import LeanVM.Guest.Data.Source
import LeanVM.Guest.Data.Bytecode
import LeanVM.Guest.Expand
import LeanVM.Guest.Renumber
import LeanVM.Guest.Check
import LeanVM.Guest.Memory.Fresh

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

/-- The instructions a window runs over at most, when a function is cut for its size; `coarse`,
the larger windows for a function whose sharing check needs them. -/
def maxWin (coarse : Bool) (name : String) : ℕ :=
  if coarse then (if name == "verify_sig_lean_sphincs" then 600 else 1000)
  else if name == "verify_sig_lean_sphincs" then 150 else 600

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
and semantic pairs it starts knowing), and, in a function longer than `maxWin` and a half (`coarse`:
three times `maxWin`), wherever the next window would grow past it. -/
def planCuts (coarse : Bool) (F : GFacts) (f : CompiledFn) (cf : Core.Fn) (locs : List ℕ)
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
  let mw := maxWin coarse f.name
  let big := if coarse then f.len > 3 * mw else f.len > mw + mw / 2
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
    unless force.isSome || (big && nextJ - a > mw && J ≥ a + mw / 4 && f.len - J > mw / 4) do continue
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

/-- The largest frame cell an instruction names. -/
def offTop : OInstr → ℕ
  | .xor a b c | .mul a b c | .jump a b c => max a (max b c)
  | .set o _ _ _ => o
  | .deref o1 _ o3 _ => max o1 o3
  | .blake2s m0 m1 m2 m3 cv out md => max (max (max m0 m1) (max m2 m3)) (max (max (cv + 1) (out + 1)) md)

structure CertOut where
  name : String
  text : String

def listText (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"

def pairText (p : ℕ × ℕ) : String := s!"({p.1}, {p.2})"

def tripText (p : ℕ × ℕ × ℕ) : String := s!"({p.1}, {p.2.1}, {p.2.2})"

/-- The values per definition of a certificate's cells. -/
def locChunk : ℕ := 2000

/-- The certificate of function `j`, its windows `coarse` or not (`planCuts`). -/
def certOf (coarse : Bool) (T : Tables) (fns : Array CompiledFn) (index : Std.HashMap String ℕ) (j : ℕ)
    (cf : Core.Fn) : Except String (String × List ℕ × ℕ × List ℕ × Array GSeg ×
      (Array ℕ × Array ℕ × Array ℕ × Array (List (ℕ × ℕ × ℕ))) × List (ℕ × List (ℕ × Sym) × ℕ)) := do
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
  let cuts ← planCuts coarse F f cf locs marks spine uses segMap pre forced
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
    let ws := (cf.body.drop a).take (b - a)
    let vs := (Check.stmtsVals ws ++ Memory.Stmt.usesList ws ++ Memory.Stmt.tmpsList ws).map (·.idx) ++
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
  -- the frame size: a loop helper's is where its tail call puts the next frame, any other's past
  -- every frame cell its code names
  let tailS : Option ℕ := segs.toList.findSome? fun s =>
    let tail (x : GExit) : Option ℕ := match x.kind with
      | .jump (.gp e) (.fpg S) => if e == f.entry then some S else none
      | _ => none
    (tail s.exit).orElse fun _ => s.items.toList.findSome? fun
      | .branch _ _ _ x => tail x
      | _ => none
  let fsz := tailS.getD (f.code.foldl (fun m ins => max m (offTop ins)) (locs.foldl max 0) + 1)
  let wInfo := (starts.zip stops).zipIdx.map fun ((a, b), i) =>
    (a, if i == 0 then F.env else (cuts[i - 1]?.map (·.env)).getD [], b)
  return (·, sizes, fsz, locs, segs, (wStarts, los, his, insW), wInfo) <| locDefs ++ s!"/-- `{f.name}`. -/
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

/-- Every atom of a block, in order, in every branch. -/
partial def allAtoms : List Core.Stmt → List Core.Atom
  | [] => []
  | s :: ss => (match s with
    | .atom a => [a]
    | .ite _ z n => allAtoms z ++ allAtoms n
    | .match_ _ arms => arms.flatMap allAtoms
    | _ => []) ++ allAtoms ss

/-- A short signature of an atom: kind, cells of its values, immediate or offset. -/
def atomSig (cell : Core.V → ℕ) : Core.Atom → String × List ℕ × String
  | .const d x => ("const", [cell d], toString (limbsOf x))
  | .add d a b => ("add", [cell d, cell a, cell b], "")
  | .mul d a b => ("mul", [cell d, cell a, cell b], "")
  | .copy d s => ("copy", [cell d, cell s], "")
  | .load d p off => ("load", [cell d, cell p], toString off)
  | .assertEq a b => ("assertEq", [cell a, cell b], "")
  | .assertNe x i p => ("assertNe", [cell x, cell i, cell p], "")
  | .rangeCheck x y t1 t2 k => ("range", [cell x, cell y, cell t1, cell t2, cell k], "")
  | .assertInK a b => ("inK", [cell a, cell b], "")
  | .blake2s m0 m1 m2 m3 c0 c1 o0 o1 md => ("blake", [m0, m1, m2, m3, c0, c1, o0, o1, md].map cell, "")
  | .frameAddr p run => ("addr", (p :: run).map cell, "")
  | .hint h => ("hint", (Core.Hint.vals h).map cell, "")

/-- The first occurrence of each value: its statement's signature. -/
partial def firsts (cell : Core.V → ℕ) (m : Std.HashMap ℕ (String × List ℕ × String × Core.Stmt))
    (ss : List Core.Stmt) : Std.HashMap ℕ (String × List ℕ × String × Core.Stmt) :=
  ss.foldl (fun m s =>
    let sig : String × List ℕ × String := match s with
      | .atom a => atomSig cell a
      | .call f args rets => ("call " ++ f, (args ++ rets).map cell, "")
      | .callIf _ f args => ("callIf " ++ f, args.map cell, "")
      | .dispatch _ fs args rets => ("dispatch " ++ toString fs.length, (args ++ rets).map cell, "")
      | .ite c _ _ => ("ite", [cell c], "")
      | .match_ x _ => ("match", [cell x], "")
      | .ret vs => ("ret", vs.map cell, "")
    let own := match s with
      | .ite c _ _ => [c]
      | .match_ x _ => [x]
      | s => Core.Stmt.vals s
    let m := own.foldl (fun m v => if m.contains v.idx then m else m.insert v.idx (sig.1, sig.2.1, sig.2.2, s)) m
    match s with
    | .ite _ z n => firsts cell (firsts cell m z) n
    | .match_ _ arms => arms.foldl (firsts cell) m
    | _ => m) m

end GuestCert

/-! ## Completeness certificates

The completeness walk (`Cpl.block`): the core function walked along the executor's segments as
the checker does, every instruction passed justified by what holds on the honest memory of a run
on the path (a core atom on the path, a fixed cell, a callee frame), and the sharing of cells
by values checked. It finds the call sites and table jumps `Data/Plumb*.lean` lists. -/


namespace GuestCert
namespace Cpl

/-- Static plumbing content of a non-value cell. -/
inductive PC where
  | k (l : ℕ × ℕ × ℕ)
  | fpg (e : ℕ)
  deriving BEq, Repr

/-- A callee frame cell's content. -/
inductive FC where
  | val (c : ℕ)
  | self
  | fp
  | pc (r : ℕ)
  | hdr (i : ℕ)
  | fpg (e : ℕ)
  deriving BEq, Repr

structure Ctx where
  fname : String
  cell : ℕ → ℕ
  vcells : Std.HashSet ℕ
  plumb : Std.HashMap ℕ PC
  pows : Std.HashMap ℕ ℕ
  segs : Std.HashMap ℕ GSeg
  entry : ℕ
  nargs : ℕ
  main : Bool
  envOf : ℕ → List ℕ   -- callee entry pc ↦ its self cells
  fsz : ℕ
  bitsOf : ℕ → ℕ
  /-- The selectors of the `match`es whose arms are counted separately. -/
  keyed : Std.HashSet ℕ := {}


structure St where
  book : Std.HashMap ℕ (List Core.Atom) := {}
  inK : Std.HashSet ℕ := {}
  know : Std.HashMap ℕ (ℕ × ℕ × ℕ) := {}
  occ : Std.HashSet ℕ := {}
  unk : Std.HashSet ℕ := {}
  keys : Std.HashMap String (ℕ × ℕ × List ℕ) := {}
  vconst : Std.HashMap ℕ (ℕ × ℕ × ℕ) := {}
  vkeys : Std.HashMap ℕ (List (String × List ℕ)) := {}
  veqs : Std.HashMap ℕ (List ℕ) := {}
  named : Std.HashSet ℕ := {}
  pend : List (ℕ × ℕ) := []
  frames : Std.HashMap ℕ (List (ℕ × FC)) := {}
  targets : Std.HashMap ℕ (ℕ × ℕ) := {}
  next : List (ℕ × FC) := []
  passed : Array OInstr := #[]
  /-- The instructions passed on this path, per opcode. -/
  cnt : List ℕ := [0, 0, 0, 0, 0, 0]
  /-- The callee frame pointer and dispatch target cells set up on this path, a bit set. -/
  uq : ℕ := 0

/-- What the walk finds: failures, the call sites `(args, rets, q, r, target)` and the table
jumps `(selector, target, base)`. -/
structure Out where
  fails : Array String := #[]
  sites : Array (List ℕ × List ℕ × ℕ × ℕ × Option ℕ) := #[]
  arms : Array (ℕ × ℕ × ℕ) := #[]
  /-- The most instructions of each opcode a path to a return passes. -/
  best : List ℕ := [0, 0, 0, 0, 0, 0]
  /-- Before each top-level statement: its index, the position, the counts and set-up cells
  there, and whether the walk stands at a segment's start (`1`: after a statement a part may
  follow, `2`: after another, `0`: not at a start). -/
  marks : Array (ℕ × Pos × List ℕ × ℕ × ℕ) := #[]
  /-- The callee frames and table reads in flight before each top-level atom after another
  statement. -/
  flight : Std.HashMap ℕ (Std.HashMap ℕ (List (ℕ × FC)) × Std.HashMap ℕ (ℕ × ℕ)) := {}
  /-- Each separately counted `match`: its selector and each arm's counts to the join. -/
  armCosts : Array (ℕ × List (List ℕ)) := #[]

abbrev M := ReaderT Ctx (StateT Out (Except String))

/-- The opcode index of an instruction (`Opcode`'s constructor order). -/
def opIdx : OInstr → ℕ
  | .xor .. => 0
  | .mul .. => 1
  | .set .. => 2
  | .deref .. => 3
  | .jump .. => 4
  | .blake2s .. => 5

def bump (l : List ℕ) (i : ℕ) : List ℕ := l.mapIdx fun k x => if k == i then x + 1 else x

def maxL (a b : List ℕ) : List ℕ := (a.zip b).map fun (x, y) => max x y

def fail (msg : String) : M Unit := do
  let c ← read
  modify fun o => { o with fails := o.fails.push s!"{c.fname}: {msg}" }

def isK (l : ℕ × ℕ × ℕ) : Bool := l.2.1 == 0 && l.2.2 == 0

/-! ## Book and sharing -/

def addKey (st : St) (k : String) (d : ℕ) (ins : List ℕ) (c : ℕ) : St :=
  let st := { st with vkeys := st.vkeys.insert d ((k, ins) :: (st.vkeys.getD d [])) }
  if st.keys.contains k then st else { st with keys := st.keys.insert k (c, d, ins) }

def factOf (cell : ℕ → ℕ) (st : St) : Core.Atom → St
  | .const d x =>
    let l := limbsOf x
    let st := { st with vconst := st.vconst.insert d.idx l }
    let st := if isK l then { st with inK := st.inK.insert (cell d.idx) } else st
    if st.know.contains (cell d.idx) then st else { st with know := st.know.insert (cell d.idx) l }
  | .add d a b =>
    let (cd, ca, cb) := (cell d.idx, cell a.idx, cell b.idx)
    let st := addKey st s!"+{[ca, cb].mergeSort}" d.idx [a.idx, b.idx] cd
    let st := addKey st s!"+{[cd, cb].mergeSort}" a.idx [d.idx, b.idx] ca
    addKey st s!"+{[cd, ca].mergeSort}" b.idx [d.idx, a.idx] cb
  | .mul d a b => addKey st s!"*{[cell a.idx, cell b.idx].mergeSort}" d.idx [a.idx, b.idx] (cell d.idx)
  | .copy d x | .assertEq d x =>
    let e := (st.veqs.insert d.idx (x.idx :: st.veqs.getD d.idx [])).insert x.idx (d.idx :: st.veqs.getD x.idx [])
    { st with veqs := e }
  | .load d p off =>
    let st := { st with inK := st.inK.insert (cell p.idx) }
    addKey st s!"L{cell p.idx},{off}" d.idx [p.idx] (cell d.idx)
  | .blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    let ins := [m0, m1, m2, m3, c0, c1, md].map (cell ·.idx)
    let iv := [m0, m1, m2, m3, c0, c1, md].map (·.idx)
    addKey (addKey st s!"B0{ins}" o0.idx iv (cell o0.idx)) s!"B1{ins}" o1.idx iv (cell o1.idx)
  | .assertInK a b => { st with inK := (st.inK.insert (cell a.idx)).insert (cell b.idx) }
  | .assertNe _ _ p =>
    if st.know.contains (cell p.idx) then st else { st with know := st.know.insert (cell p.idx) (1, 0, 0) }
  | .rangeCheck x y _ _ _ => { st with inK := (st.inK.insert (cell x.idx)).insert (cell y.idx) }
  | .frameAddr p _ => { st with inK := st.inK.insert (cell p.idx) }
  | _ => st

def fileAtom (cell : ℕ → ℕ) (st : St) (a : Core.Atom) : St :=
  let cs := ((Core.Atom.vals a).map (cell ·.idx)).eraseDups
  { st with book := cs.foldl (fun b c => b.insert c (a :: b.getD c [])) st.book }

def nameV (cell : ℕ → ℕ) (st : St) (v : ℕ) : St :=
  if st.named.contains v then st
  else
    let c := cell v
    let st := { st with named := st.named.insert v }
    if c == 0 then st
    else if st.occ.contains c || st.unk.contains c then { st with pend := (v, c) :: st.pend }
    else { st with occ := st.occ.insert c }

def discharge (cell : ℕ → ℕ) (st : St) : St :=
  let ok (v c : ℕ) (pend : List (ℕ × ℕ)) : Bool :=
    let good (x : ℕ) : Bool := st.named.contains x && !pend.any (·.1 == x)
    let constOk := match st.vconst.get? v, st.know.get? c with
      | some X, some Y => X == Y
      | _, _ => false
    let keyOk := !st.unk.contains c && (st.vkeys.getD v []).any fun (k, ins) => match st.keys.get? k with
      | some (c', o, ins') => c' == c && o != v && good o && ins.all good && ins'.all good
      | none => false
    let eqOk := !st.unk.contains c && (st.veqs.getD v []).any fun x => x != v && cell x == c && good x
    constOk || keyOk || eqOk
  let rec go (n : ℕ) (p : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
    match n with
    | 0 => p
    | n + 1 => let p' := p.filter fun (v, c) => !ok v c p; if p'.length == p.length then p' else go n p'
  { st with pend := go 1000 st.pend }

def mayRet : Core.Stmt → Bool
  | .ret _ => true
  | .ite _ z n => Core.Stmt.noRetList z = false || Core.Stmt.noRetList n = false
  | .match_ _ arms => arms.any (Core.Stmt.noRetList · = false)
  | _ => false

/-- The statements up to and including the first that may return. -/
def run : List Core.Stmt → List Core.Stmt
  | [] => []
  | s :: ss => if mayRet s then [s] else s :: run ss

def stmtNames : Core.Stmt → List Core.V
  | .atom a => Core.Atom.vals a
  | .call _ args rets | .dispatch _ _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .ret vs => vs
  | .ite c _ _ => [c]
  | .match_ x _ => [x]

def lookahead (cell : ℕ → ℕ) (st : St) (ss : List Core.Stmt) : St × List (ℕ × ℕ) :=
  let r := run ss
  let st := r.foldl (fun st s => match s with
    | .atom a => fileAtom cell (factOf cell st a) a
    | .ite c _ _ => { st with inK := st.inK.insert (cell c.idx) }
    | .callIf c _ _ => { st with inK := st.inK.insert (cell c.idx) }
    | _ => st) st
  let st := r.foldl (fun st s => (stmtNames s).foldl (fun st v => nameV cell st v.idx) st) st
  let st := discharge cell st
  (({ st with pend := [] }), st.pend)

/-! ## Justifying instructions -/

def contentK (c : Ctx) (st : St) (o : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match c.plumb.get? o with
  | some (.k l) => some l
  | _ => st.know.get? o

def isOne (c : Ctx) (st : St) (o : ℕ) : Bool := contentK c st o == some (1, 0, 0)
def isZero (c : Ctx) (st : St) (o : ℕ) : Bool := contentK c st o == some (0, 0, 0)

def bookAt (st : St) (o : ℕ) : List Core.Atom := st.book.getD o []

def cellK (c : Ctx) (st : St) (o : ℕ) : Bool :=
  o == 0 || o == 1 || st.inK.contains o || st.frames.contains o || st.targets.contains o ||
  (match c.plumb.get? o with
    | some (.k l) => isK l
    | some (.fpg _) => true
    | none => false) ||
  (match st.know.get? o with
    | some l => isK l
    | none => false)

def perm3 (x y z p q r : ℕ) : Bool :=
  [x, y, z].mergeSort == [p, q, r].mergeSort

/-- Two cells hold one word: one cell, or a copy/`assert ==` in the book. -/
def sameW (c : Ctx) (st : St) (a b : ℕ) : Bool :=
  a == b || (bookAt st a).any fun x => match x with
    | .copy d s | .assertEq d s => let (cd, cs) := (c.cell d.idx, c.cell s.idx)
        (cd == a && cs == b) || (cd == b && cs == a)
    | _ => false

def justify (c : Ctx) (st : St) (pc : ℕ) (ins : OInstr) : Bool :=
  let cell := c.cell
  match ins with
  | .set o k0 k1 k2 => contentK c st o == some (k0, k1, k2)
  | .xor a b d =>
    (bookAt st d).any (fun x => match x with
      | .add d' x y => perm3 a b d (cell d'.idx) (cell x.idx) (cell y.idx)
      | _ => false) ||
    (isZero c st d && sameW c st a b) || (a == d && isZero c st b) || (b == d && isZero c st a) ||
    (b == d && (bookAt st a).any fun x => match x with
      | .assertEq u w => (cell u.idx == a && isZero c st (cell w.idx)) || (cell w.idx == a && isZero c st (cell u.idx))
      | _ => false)
  | .mul a b d =>
    (bookAt st d).any (fun x => match x with
      | .mul d' x y => cell d'.idx == d && ((cell x.idx == a && cell y.idx == b) || (cell x.idx == b && cell y.idx == a))
      | .rangeCheck x y _ _ k => cell k.idx == d && ((cell x.idx == a && cell y.idx == b) || (cell x.idx == b && cell y.idx == a))
      | .assertNe x i p => cell p.idx == d && ((cell x.idx == a && cell i.idx == b) || (cell x.idx == b && cell i.idx == a))
      | .frameAddr p run => cell p.idx == d &&
          (match c.plumb.get? a, contentK c st b with
            | some (.fpg e1), some (k0, 0, 0) => match (if k0 == 1 then some 0 else c.pows.get? k0), run with
              | some e2, r :: _ => e1 + e2 == cell r.idx
              | _, _ => false
            | _, _ => false)
      | _ => false) ||
    (isOne c st b && sameW c st a d) || (isOne c st a && sameW c st b d) ||
    (match c.plumb.get? d, c.plumb.get? a, contentK c st b with
      | some (.fpg e), some (.fpg e1), some (k0, 0, 0) =>
        (if k0 == 1 then some 0 else c.pows.get? k0) == some (e - e1)  && e1 ≤ e
      | _, _, _ => false) ||
    (d ≥ c.fsz && isOne c st b && (match st.next.find? (·.1 == d - c.fsz) with
      | some (_, .val cv) => sameW c st a cv
      | some (_, .hdr i) => a == i
      | some (_, .fpg e) => (match c.plumb.get? a with
          | some (.fpg e') => e' == e
          | _ => false)
      | _ => false))
  | .deref o1 o2 o3 .cell =>
    (bookAt st o3).any (fun x => match x with
      | .load d p off => cell d.idx == o3 && cell p.idx == o1 && off == o2
      | .rangeCheck x y t1 t2 _ => o2 == 0 && ((cell x.idx == o1 && cell t1.idx == o3) || (cell y.idx == o1 && cell t2.idx == o3))
      | _ => false) ||
    (match st.frames.get? o1 with
      | some fcs => fcs.any fun (o, fc) => o == o2 && (match fc with
        | .val cv => sameW c st cv o3
        | .self => o3 == o1
        | .pc r => contentK c st o3 == some (c.bitsOf r, 0, 0)
        | _ => false)
      | none => false) ||
    (st.targets.get? o3 == some (o1, o2)) ||
    (o2 == 0 && c.plumb.get? o1 == some (.fpg o3))
  | .deref o1 o2 _ .fp =>
    (match st.frames.get? o1 with
      | some fcs => fcs.any fun (o, fc) => o == o2 && fc == .fp
      | none => false) ||
    (o2 == 0 && (match c.plumb.get? o1 with
      | some (.fpg x) => c.plumb.get? x == some (.fpg 0)
      | _ => false))
  | .deref o1 o2 _ .pc =>
    match st.frames.get? o1 with
    | some fcs => fcs.any fun (o, fc) => o == o2 && fc == .pc (pc + 2)
    | none => false
  | .blake2s m0 m1 m2 m3 cv out md =>
    (bookAt st out).any fun x => match x with
      | .blake2s n0 n1 n2 n3 c0 c1 o0 o1 d =>
        [n0, n1, n2, n3, c0, c1, o0, o1, d].map (cell ·.idx) == [m0, m1, m2, m3, cv, cv + 1, out, out + 1, md]
      | _ => false
  | .jump .. => false

def passItem (st : St) (it : GItem) : M St := do
  let c ← read
  match it with
  | .ins (.instr pc ins) =>
    unless justify c st pc ins do fail s!"@{pc - c.entry} {instrText ins}"
    pure { st with passed := st.passed.push ins, cnt := bump st.cnt (opIdx ins) }
  | .ins (.jump oc od of) =>
    unless cellK c st oc && cellK c st od && cellK c st of do fail s!"jump K {oc} {od} {of}"
    pure { st with cnt := bump st.cnt 4 }
  | _ => pure st

def getSeg (g : ℕ) : M GSeg := do
  match (← read).segs.get? g with
  | some s => pure s
  | none => throw (s!"no segment {g}")

/-- Check a segment's entry environment against what is known. -/
def envCheck (st : St) (s : GSeg) : M Unit := do
  let c ← read
  for (o, sym) in s.env.toList do
    let ok : Bool := match sym with
      | .zero => contentK c st o == some (0, 0, 0)
      | .gp e => match contentK c st o with
        | some (k0, 0, 0) => (if k0 == 1 then some 0 else c.pows.get? k0) == some e
        | _ => false
      | .fpg e => c.plumb.get? o == some (.fpg e)
    unless ok do fail s!"env {o} {symText sym} at seg {s.start}"

/-- Pass items to the next branch or the end. -/
def toEnd (p : Pos) (st : St) : M (Pos × St × Option GExit) := do
  let s ← getSeg p.1
  let mut i := p.2
  let mut st := st
  repeat
    match s.items[i]? with
    | some (.branch ..) => break
    | some it => st ← passItem st it; i := i + 1
    | none => break
  return ((p.1, i), st, if i ≥ s.items.size then some s.exit else none)

/-- The next branch, without passing the items before it. -/
def peekBranch (p : Pos) : M (Pos × ℕ × ℕ × ℕ × GExit) := do
  let s ← getSeg p.1
  let mut i := p.2
  repeat
    match s.items[i]? with
    | some (.branch oc od of x) => return ((p.1, i), oc, od, of, x)
    | some _ => i := i + 1
    | none => break
  throw (s!"no branch after {p}")

def toBranch (p : Pos) (st : St) : M (Pos × St × ℕ × ℕ × ℕ × GExit) := do
  let (q, st, _) ← toEnd p st
  let s ← getSeg q.1
  match s.items[q.2]? with
  | some (.branch oc od of x) => return (q, st, oc, od, of, x)
  | _ => throw (s!"no branch at {q}")

partial def chain (p : Pos) (n : ℕ := 6) : M (List ℕ) := do
  if n == 0 then return []
  let s ← getSeg p.1
  let here := if p.2 == 0 then [p.1] else []
  if s.items.toList.drop p.2 |>.any (fun | .branch .. => true | _ => false) then return here
  match s.exit.kind with
  | .next t => if (← read).segs.contains t then return here ++ (← chain (t, 0) (n - 1)) else return here
  | _ => return here

def meetJ (ends : List Pos) : M (Option ℕ) := do
  let cs ← ends.mapM (chain ·)
  match cs with
  | [] => return none
  | c :: rest => return c.find? fun J => rest.all (·.contains J)

/-- After a join: the facts from before, the values named on every path, the cells occupied in
a branch unknown unless every branch knows one constant there. -/
def joinSt (pre : St) (bs : List St) : St :=
  let named := match bs with
    | [] => pre.named
    | b :: rest => b.named.fold (fun h v => if rest.all (·.named.contains v) then h.insert v else h) pre.named
  let newCells : Std.HashSet ℕ := bs.foldl (fun h b => b.occ.fold (fun h c => if pre.occ.contains c then h else h.insert c) h) {}
  let (know, unk) := newCells.fold (fun (know, unk) c =>
    let ks := bs.map fun b => if b.occ.contains c || b.unk.contains c then b.know.get? c else some (0, 0, 0)
    match ks with
    | some k :: rest => if rest.all (· == some k) && !pre.know.contains c then (know.insert c k, unk.insert c) else (know, unk.insert c)
    | _ => (know, unk.insert c)) (pre.know, pre.unk)
  let unk := bs.foldl (fun h b => b.unk.fold (·.insert ·) h) unk
  let cnt := bs.foldl (fun c b => maxL c b.cnt) pre.cnt
  let uq := bs.foldl (fun u b => u ||| b.uq) pre.uq
  { pre with named := named, know := know, unk := unk, passed := pre.passed, cnt := cnt, uq := uq }

/-- The counts after passing a segment's items from `i` to its end, unchecked. -/
def countRest (s : GSeg) (i : ℕ) (cnt : List ℕ) : List ℕ :=
  (s.items.toList.drop i).foldl (fun c it => match it with
    | .ins (.instr _ ins) => bump c (opIdx ins)
    | .ins (.jump ..) => bump c 4
    | _ => c) cnt

/-- Where a part of statements `ss` may stop inside segment `s`, from item `i`, with the callee
frames and table reads `fl` in flight: the first item their facts (and the fixed cells of `st`) do
not justify, before any branch. -/
def midStop (c : Ctx) (st : St) (fl : Std.HashMap ℕ (List (ℕ × FC)) × Std.HashMap ℕ (ℕ × ℕ))
    (ss : List Core.Stmt) (s : GSeg) (i : ℕ) : ℕ := Id.run do
  let st := (lookahead c.cell { st with frames := fl.1, targets := fl.2 } ss).1
  let mut k := i
  repeat
    match s.items[k]? with
    | some (.ins (.instr pc ins)) => if justify c st pc ins then k := k + 1 else break
    | some (.ins (.jump oc od of)) => if cellK c st oc && cellK c st od && cellK c st of then k := k + 1 else break
    | some (.fact _) => k := k + 1
    | _ => break
  return k

mutual
partial def block (ss : List Core.Stmt) (p : Pos) (st : St) (top : Bool := false) :
    M (Option (Pos × St)) := do
  let c ← read
  let (st0, pend) := lookahead c.cell st ss
  for (v, cc) in pend do fail s!"share {v} at cell {cc}"
  let mut st := st0
  let mut p := p
  let mut ss := ss
  -- whether the walk passed items since it last stood at a segment's start
  let mut moved := p.2 != 0
  let mut nTop := 0
  let mut prevOk := false
  let mut prevAtom := false
  repeat
    if top then
      let fl := if moved then 0 else if prevOk then 1 else 2
      modify fun o => { o with marks := o.marks.push (nTop, p, st.cnt, st.uq, fl) }
      if !prevAtom then
        modify fun o => { o with flight := o.flight.insert nTop (st.frames, st.targets) }
    nTop := nTop + 1
    prevAtom := match ss with
      | .atom _ :: _ => true
      | _ => false
    prevOk := match ss with
      | .ite .. :: _ | .match_ .. :: _ | .callIf .. :: _ => true
      | .call _ _ [] :: _ | .dispatch _ _ _ [] :: _ => true
      | _ => false
    match ss with
    | [] =>
      -- a block's end at a segment's start stays; otherwise it passes its segment
      if !moved then return some (p, st)
      let (q, st1, _) ← toEnd p st
      return some (q, st1)
    | s :: rest =>
      ss := rest
      moved := true
      match s with
      | .atom _ => pure ()
      | .ite cv z n =>
        let (q, st1, oc, od, of, x) ← toBranch p st
        let st1 := { st1 with cnt := bump st1.cnt 4 }
        unless oc == c.cell cv.idx do fail s!"ite cond cell {oc}"
        unless cellK c st1 od && cellK c st1 of do fail s!"ite jump K {od} {of}"
        let .next t := x.kind | throw ("ite kind")
        let rz ← block z (q.1, q.2 + 1) st1
        let sn ← getSeg t
        envCheck st1 sn
        let rn ← block n (t, 0) st1
        let ends := [rz, rn].filterMap id
        match ← meetJ (ends.map (·.1)) with
        | some J =>
          let sj ← getSeg J
          let st2 := joinSt st1 (ends.map (·.2))
          envCheck st2 sj
          p := (J, 0); st := st2; moved := false
        | none => return none
      | .match_ xv arms =>
        let (_, st1, x?) ← toEndPeek p st xv
        let some x := x? | throw ("match end")
        -- a separately counted match's arms each count from zero, and the path after it from the jump
        let keyed := c.keyed.contains xv.idx
        let rs ← (arms.zip x.succ).mapM fun (a, t) => do
          let s ← getSeg t
          envCheck st1 s
          block a (t, 0) (if keyed then { st1 with cnt := [0, 0, 0, 0, 0, 0] } else st1)
        let ends := rs.filterMap id
        if keyed then
          modify fun o => { o with armCosts := o.armCosts.push (xv.idx, rs.map fun r =>
            (r.map (·.2.cnt)).getD [0, 0, 0, 0, 0, 0]) }
        match ← meetJ (ends.map (·.1)) with
        | some J =>
          let sj ← getSeg J
          let st2 := joinSt st1 (ends.map (·.2))
          let st2 := if keyed then { st2 with cnt := st1.cnt } else st2
          envCheck st2 sj
          p := (J, 0); st := st2; moved := false
        | none => return none
      | .call _ args rets | .dispatch _ _ args rets =>
        let s0 ← getSeg p.1
        let x := s0.exit
        let .call pt q r := x.kind | throw (s!"call kind at {p}")
        let envCells := match pt with
          | .gp e => c.envOf e
          | _ => []
        let fcs := (args.zipIdx.map fun (a, k) => (2 + k, FC.val (c.cell a.idx))) ++
          envCells.map (·, FC.self) ++ [(1, FC.fp), (0, FC.pc r)]
        if st.frames.contains q then fail s!"frame cell {q} reused"
        let tg : Option ℕ := match pt with
          | .cell t => some t
          | _ => none
        modify fun o => { o with sites := o.sites.push (args.map (·.idx), rets.map (·.idx), q, r, tg) }
        let uq := st.uq ||| (1 <<< q) ||| (match pt with
          | .cell t => 1 <<< t
          | _ => 0)
        let mut st1 := { st with frames := st.frames.insert q fcs, uq := uq }
        if let .cell t := pt then
          -- the table read into `t`
          let base := s0.items.toList.findSome? fun
            | .ins (.instr _ (.deref o1 o2 o3 .cell)) => if o3 == t then some (o1, o2) else none
            | _ => none
          match base with
          | some b => st1 := { st1 with targets := st1.targets.insert t b }
          | none => fail s!"dispatch base {t}"
        let (_, st2, _) ← toEnd p st1
        let rr := r - c.entry
        let sr ← getSeg rr
        envCheck st2 sr
        let fcs' := fcs ++ rets.zipIdx.map fun (v, k) => (2 + args.length + k, FC.val (c.cell v.idx))
        p := (rr, 0); st := { st2 with frames := st2.frames.insert q fcs' }; moved := !rets.isEmpty
      | .callIf cv _ args =>
        let (q, oc, od, of, x) ← peekBranch p
        unless oc == c.cell cv.idx do fail s!"callIf cond cell {oc}"
        match x.kind with
        | .call (.gp e) fq r =>
          let fcs := (args.zipIdx.map fun (a, k) => (2 + k, FC.val (c.cell a.idx))) ++
            (c.envOf e).map (·, FC.self) ++ [(1, FC.fp), (0, FC.pc r)]
          if st.frames.contains fq then fail s!"frame cell {fq} reused"
          modify fun o => { o with sites := o.sites.push (args.map (·.idx), [], fq, r, none) }
          -- the setup is before the branch: re-pass with the frame known
          let (_, st2, _) ← toEnd p { st with frames := st.frames.insert fq fcs }
          let st2 := { st2 with cnt := bump st2.cnt 4 }
          unless cellK c st2 od && cellK c st2 of do fail s!"callIf jump K {od} {of}"
          -- the path not taken passes the rest of the branch's segment
          let sq ← getSeg q.1
          let st2 := { st2 with cnt := countRest sq (q.2 + 1) st2.cnt, uq := st2.uq ||| (1 <<< fq) }
          let rr := r - c.entry
          let sr ← getSeg rr
          envCheck st2 sr
          p := (rr, 0); st := st2; moved := false
          let _ := q
        | .jump (.gp _) (.fpg S) =>
          let nxt := (args.zipIdx.map fun (a, k) => (2 + k, FC.val (c.cell a.idx))) ++
            [(0, FC.hdr 0), (1, FC.hdr 1)] ++ (c.envOf (c.entry)).map (·, FC.fpg S)
          let (_, st2, _) ← toEnd p { st with next := nxt }
          let st2 := { st2 with cnt := bump st2.cnt 4 }
          unless cellK c st2 od && cellK c st2 of do fail s!"tail jump K {od} {of}"
          p := (q.1, q.2 + 1); st := st2
        | _ => throw ("callIf kind")
      | .ret _ =>
        let (_, st1, x?) ← toEnd p st
        if x?.isNone then fail "ret not at end"
        modify fun o => { o with best := maxL o.best st1.cnt }
        return none
  return some (p, st)

/-- `toEnd` for a `match`: the target cell registered from the table read before the items are
passed. -/
partial def toEndPeek (p : Pos) (st : St) (xv : Core.V) : M (Pos × St × Option GExit) := do
  let c ← read
  let s0 ← getSeg p.1
  let mut st := st
  match s0.exit.kind with
  | .jump (.cell t) _ =>
    let base := s0.items.toList.findSome? fun
      | .ins (.instr _ (.deref o1 o2 o3 .cell)) => if o3 == t then some (o1, o2) else none
      | _ => none
    match base with
    | some (o1, o2) =>
      unless o1 == c.cell xv.idx do fail s!"match selector {o1}"
      modify fun o => { o with arms := o.arms.push (xv.idx, t, o2) }
      st := { st with targets := st.targets.insert t (o1, o2) }
    | none => fail s!"match base {t}"
  | _ => fail "match kind"
  toEnd p st
end

end Cpl

/-- Static plumbing of a function: its non-value cells' contents. -/
def plumbOf (f : CompiledFn) (F : GFacts) (vcells : Std.HashSet ℕ) (pows : Std.HashMap ℕ ℕ)
    (constCell : ℕ → (ℕ × ℕ × ℕ) → Bool) :
    Std.HashMap ℕ Cpl.PC × List String := Id.run do
  let code := f.code.toArray
  let mut m : Std.HashMap ℕ Cpl.PC := {}
  let mut errs : List String := []
  let put (m : Std.HashMap ℕ Cpl.PC) (o : ℕ) (v : Cpl.PC) : Std.HashMap ℕ Cpl.PC × Option String :=
    match m.get? o with
    | some v' => if v' == v then (m, none) else (m, some s!"{f.name}: plumbing conflict at {o}")
    | none => (m.insert o v, none)
  for (o, _) in F.env do
    let (m', e) := put m o (.fpg 0); m := m'; if let some e := e then errs := e :: errs
  let mut sets : Std.HashMap ℕ (List (ℕ × ℕ × ℕ)) := {}
  for ins in code do
    match ins with
    | .set o k0 k1 k2 => sets := sets.insert o (((sets.get? o).getD []).insert (k0, k1, k2))
    | _ => pure ()
  for (o, ks) in sets.toList do
    match ks with
    | [l] => if !vcells.contains o || constCell o l then
        let (m', e) := put m o (.k l); m := m'; if let some e := e then errs := e :: errs
    | _ => if !vcells.contains o then errs := s!"{f.name}: several SETs at non-value cell {o}" :: errs
  -- the next frame `MUL nfp = self · g^S`, and bounces
  for i in [0:code.size] do
    match code[i]! with
    | .mul a b c => if !vcells.contains c then
        match m.get? a, m.get? b with
        | some (.fpg e1), some (.k (k0, 0, 0)) =>
          match (if k0 == 1 then some 0 else pows.get? k0) with
          | some e2 => let (m', e) := put m c (.fpg (e1 + e2)); m := m'; if let some e := e then errs := e :: errs
          | none => pure ()
        | _, _ => pure ()
    | .deref h 0 0 .fp =>
      match code[i + 1]? with
      | some (.deref h' 0 x .cell) => if h' == h then
          let (m', e) := put m h (.fpg x); m := m'; if let some e := e then errs := e :: errs
          let (m', e) := put m x (.fpg 0); m := m'; if let some e := e then errs := e :: errs
      | _ => pure ()
    | _ => pure ()
  return (m, errs)


end GuestCert

/-! ## The sharing check's snapshots

An executable mirror of `B2C.Share`'s walk (`ShareM.swL`), run over each function's windows to
find the state each window after the first starts from (`B2C.Snap`). The kernel reruns the walk
and checks each window's end state refines the next snapshot, so nothing here is trusted. -/

namespace GuestCert
namespace ShareM

structure PF where
  v : ℕ
  c : ℕ
  kc : Option (ℕ × ℕ × ℕ)
  keys : List (ℕ × List ℕ)
  eqs : List ℕ

structure SS where
  occ : Std.HashSet ℕ := {}
  cst : Std.HashMap ℕ (ℕ × ℕ × ℕ) := {}
  keys : Std.HashMap ℕ (List (ℕ × List ℕ)) := {}
  named : Std.HashSet ℕ := {}
  pend : List PF := []

structure Ctx where
  cell : ℕ → ℕ
  sh : Std.HashSet ℕ
  tmpAt : Std.HashMap ℕ ℕ
  runs : List (ℕ × ℕ)

def constOf (a : Core.Atom) (v : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match a with
  | .const d x => if d.idx == v then some (limbNat x 0, limbNat x 1, limbNat x 2) else none
  | .assertNe _ _ p => if p.idx == v then some (1, 0, 0) else none
  | _ => none

def keysOf (a : Core.Atom) (v : ℕ) : List (ℕ × List ℕ) :=
  match a with
  | .add d x y => (if d.idx == v then [(0, [x.idx, y.idx])] else []) ++
      (if x.idx == v then [(0, [d.idx, y.idx])] else []) ++
      (if y.idx == v then [(0, [d.idx, x.idx])] else [])
  | .mul d x y => if d.idx == v then [(1, [x.idx, y.idx])] else []
  | .blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    (if o0.idx == v then [(2, [m0.idx, m1.idx, m2.idx, m3.idx, c0.idx, c1.idx, md.idx])] else []) ++
      (if o1.idx == v then [(3, [m0.idx, m1.idx, m2.idx, m3.idx, c0.idx, c1.idx, md.idx])] else [])
  | .load d p off => if d.idx == v then [(off + 4, [p.idx])] else []
  | _ => []

def eqsOf (a : Core.Atom) (v : ℕ) : List ℕ :=
  match a with
  | .copy d x | .assertEq d x => (if d.idx == v then [x.idx] else []) ++ (if x.idx == v then [d.idx] else [])
  | _ => []

def keyCells (op : ℕ) (cs : List ℕ) : List ℕ :=
  match op, cs with
  | 0, [a, b] | 1, [a, b] => if a ≤ b then [a, b] else [b, a]
  | _, cs => cs

def cellKeys (X : Ctx) : Core.Atom → List (ℕ × ℕ × List ℕ)
  | .add d x y => [(X.cell d.idx, 0, keyCells 0 [X.cell x.idx, X.cell y.idx]),
      (X.cell x.idx, 0, keyCells 0 [X.cell d.idx, X.cell y.idx]),
      (X.cell y.idx, 0, keyCells 0 [X.cell d.idx, X.cell x.idx])]
  | .mul d x y => [(X.cell d.idx, 1, keyCells 1 [X.cell x.idx, X.cell y.idx])]
  | .blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    let ins := [m0, m1, m2, m3, c0, c1, md].map (X.cell ·.idx)
    [(X.cell o0.idx, 2, ins), (X.cell o1.idx, 3, ins)]
  | .load d p off => [(X.cell d.idx, off + 4, [X.cell p.idx])]
  | _ => []

def isPend (st : SS) (v : ℕ) : Bool := st.pend.any (·.v == v)

def nameV (X : Ctx) (kc : ℕ → Option (ℕ × ℕ × ℕ)) (st : SS) (v : Core.V) : SS :=
  if st.named.contains v.idx || isPend st v.idx then st
  else
    let c := X.cell v.idx
    if c < 2 then { st with named := st.named.insert v.idx }
    else if st.occ.contains c then { st with pend := ⟨v.idx, c, none, [], []⟩ :: st.pend }
    else
      let cst := match kc v.idx with
        | some x => if X.sh.contains c then st.cst.insert c x else st.cst
        | none => st.cst
      { st with occ := st.occ.insert c, cst := cst, named := st.named.insert v.idx }

def nameAll (X : Ctx) (kc : ℕ → Option (ℕ × ℕ × ℕ)) (st : SS) (vs : List Core.V) : SS :=
  vs.foldl (nameV X kc) st

def addFacts (a : Core.Atom) (ps : List PF) : List PF :=
  ps.map fun p => ⟨p.v, p.c, (match p.kc with
    | some x => some x
    | none => constOf a p.v), keysOf a p.v ++ p.keys, eqsOf a p.v ++ p.eqs⟩

def knownIn (X : Ctx) (st : SS) (v : ℕ) : Bool := st.named.contains v && 2 ≤ X.cell v

def keyOk (X : Ctx) (st : SS) (c : ℕ) (k : ℕ × List ℕ) : Bool :=
  k.2.all (knownIn X st) && (st.keys.getD c []).any fun k' => k'.1 == k.1 && k'.2 == keyCells k.1 (k.2.map X.cell)

def pfOk (X : Ctx) (st : SS) (p : PF) : Bool :=
  (match p.kc, st.cst.get? p.c with
    | some x, some y => x == y
    | _, _ => false) ||
  p.keys.any (keyOk X st p.c) || p.eqs.any fun x => st.named.contains x && X.cell x == p.c

def discharge (X : Ctx) : ℕ → SS → SS
  | 0, st => st
  | n + 1, st =>
    let ok := st.pend.filter (pfOk X st)
    let named := ok.foldl (fun s p => s.insert p.v) st.named
    let rest := st.pend.filter (!pfOk X st ·)
    if ok.isEmpty then st
    else discharge X n { st with named := named, pend := rest }

def recCst (X : Ctx) (a : Core.Atom) (cst : Std.HashMap ℕ (ℕ × ℕ × ℕ)) : Std.HashMap ℕ (ℕ × ℕ × ℕ) :=
  match a with
  | .const d x => let c := X.cell d.idx
    if !cst.contains c && 2 ≤ c && X.sh.contains c then cst.insert c (limbNat x 0, limbNat x 1, limbNat x 2) else cst
  | .assertNe _ _ p => let c := X.cell p.idx
    if !cst.contains c && 2 ≤ c && X.sh.contains c then cst.insert c (1, 0, 0) else cst
  | _ => cst

def record (X : Ctx) (a : Core.Atom) (st : SS) : SS :=
  let keys := (cellKeys X a).foldl (fun t k => if 2 ≤ k.1 && X.sh.contains k.1 && k.2.2.all (2 ≤ ·) then
    t.insert k.1 ((k.2.1, k.2.2) :: t.getD k.1 []) else t) st.keys
  let cst := recCst X a st.cst
  if (Memory.atomUses a).all (st.named.contains ·.idx) then { st with cst := cst, keys := keys }
  else st

def stepAtom (X : Ctx) (st : SS) (a : Core.Atom) : SS :=
  let st := nameAll X (constOf a) st (Memory.atomUses a)
  let st := discharge X (st.pend.length + 1) { st with pend := addFacts a st.pend }
  record X a st

def nameStep (X : Ctx) (st : SS) (vs : List Core.V) : SS :=
  let st := nameAll X (fun _ => none) st vs
  discharge X (st.pend.length + 1) st

def listedT (X : Ctx) (v : Core.V) (c : ℕ) : Bool := v == Core.V.n v.idx && X.tmpAt.get? c == some v.idx

def listed (l : List (ℕ × ℕ)) (v : Core.V) (c : ℕ) : Bool := v == Core.V.n v.idx && l.any fun p => p.1 == v.idx && p.2 == c

def atomListed (X : Ctx) : Core.Atom → Bool
  | .rangeCheck _ _ t1 t2 _ => listedT X t1 (X.cell t1.idx) && listedT X t2 (X.cell t2.idx)
  | .frameAddr _ (r :: rs) => let base := X.cell r.idx
    ((r :: rs).zipIdx.all fun (v, k) => X.cell v.idx == base + k && listed X.runs v (base + k))
  | _ => true

def stmtNames : Core.Stmt → List Core.V
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: (args ++ rets)
  | .ret vs => vs
  | .ite c _ _ => [c]
  | .match_ x _ => [x]
  | .atom _ => []

def mayRet : Core.Stmt → Bool
  | .ret _ => true
  | .ite _ z n => !Core.Stmt.noRetList z || !Core.Stmt.noRetList n
  | .match_ _ arms => arms.any (!Core.Stmt.noRetList ·)
  | _ => false

def joinSt (pre : SS) (bs : List SS) : SS :=
  let occ := bs.foldl (fun o b => b.occ.fold (·.insert ·) o) pre.occ
  let named := match bs with
    | [] => pre.named
    | b :: rest => b.named.fold (fun h v => if rest.all (·.named.contains v) then h.insert v else h) {}
  { pre with occ := occ, named := named, pend := [] }

abbrev M := Except String

mutual
partial def swL (X : Ctx) (st : SS) : List Core.Stmt → M SS
  | [] => if st.pend.isEmpty then pure st else throw s!"pending at a block end: {st.pend.map (·.v)}"
  | s :: ss => do
    let st' ← swS X st s
    if mayRet s && !st'.pend.isEmpty then throw s!"pending after a return: {st'.pend.map (·.v)}"
    swL X st' ss

partial def swS (X : Ctx) (st : SS) : Core.Stmt → M SS
  | .atom a => if atomListed X a then pure (stepAtom X st a) else throw "temporary or run not listed"
  | .ite c z n => do
    let st1 := nameStep X st [c]
    unless st1.pend.isEmpty do throw s!"pending at a branch: {st1.pend.map (·.v)}"
    let sz ← swL X st1 z
    let sn ← swL X st1 n
    pure (joinSt st1 [sz, sn])
  | .match_ x arms => do
    let st1 := nameStep X st [x]
    unless st1.pend.isEmpty do throw s!"pending at a match: {st1.pend.map (·.v)}"
    let bs ← arms.mapM (swL X st1)
    pure (joinSt st1 bs)
  | s => pure (nameStep X st (stmtNames s))
end

/-- The bit set of a set of naturals. -/
def bitsOfSet (s : Std.HashSet ℕ) : ℕ := s.fold (fun n c => n ||| (1 <<< c)) 0

/-- The most cost (values its statements name) of a sharing window; half that in a function of
over 4000 statements, whose windows each also walk the body to their start. -/
def maxShareWin : ℕ := 1200

/-- The sharing check's windows of a function and their snapshots: each soundness window cut where
its statements so far cost `maxShareWin` and nothing is pending, each window after the first
starting from the walk's state at its start, handing on the values, constants and keys later
statements name. Returns the `B2C.Snap` literals and each window's cost. -/
def snaps (j : ℕ) (cf : Core.Fn) (locs : List ℕ) (starts : Array ℕ) (los his : Array ℕ)
    (insW : Array (List (ℕ × ℕ × ℕ))) (stat : List (ℕ × Cpl.PC)) (sh : List ℕ) (tmps runs : List (ℕ × ℕ)) :
    Except String (List String × List ℕ) := do
  let nw := starts.size
  let locA := locs.toArray
  let body := cf.body.toArray
  let shS : Std.HashSet ℕ := sh.foldl (·.insert ·) {}
  let tmpAt : Std.HashMap ℕ ℕ := tmps.foldl (fun m (v, c) => m.insert c v) {}
  let ctxAt (w : ℕ) : Ctx :=
    let lo := los[w]!
    let hi := his[w]!
    let ins := insW[w]!
    ⟨fun v => if lo ≤ v && v < min hi locA.size then locA[v]! else
      match ins.find? (·.1 == v) with
      | some (_, c, _) => c
      | none => 0, shS, tmpAt, runs⟩
  let init : SS := stat.foldl (fun st (o, pc) => match pc with
    | .k l => { st with occ := st.occ.insert o, cst := st.cst.insert o l }
    | .fpg _ => { st with occ := st.occ.insert o }) {}
  -- the snapshot at statement `a`, read from window `w`'s cells, of the state `m`
  let snap (a w : ℕ) (m : SS) : String × SS :=
    let rest := cf.body.drop a
    let used : Std.HashSet ℕ := (Check.stmtsVals rest ++ Memory.Stmt.usesList rest ++ Memory.Stmt.tmpsList rest).foldl
      (fun h v => h.insert v.idx) {}
    let cellsUsed : Std.HashSet ℕ := used.fold (fun h v => h.insert (locA.getD v 0)) {}
    let named := (m.named.toList.filter used.contains).mergeSort
    let cst := (m.cst.toList.filter fun (c, _) => cellsUsed.contains c).mergeSort (·.1 ≤ ·.1)
    let keys := ((m.keys.toList.filter fun (c, _) => cellsUsed.contains c).flatMap fun (c, ks) =>
      ks.map fun k => (c, k)).mergeSort (·.1 ≤ ·.1)
    let cstM : Std.HashMap ℕ (ℕ × ℕ × ℕ) := cst.foldl (fun h (c, x) => h.insert c x) {}
    let keysM : Std.HashMap ℕ (List (ℕ × List ℕ)) := keys.foldl (fun h (c, k) => h.insert c (k :: h.getD c [])) {}
    let namedS : Std.HashSet ℕ := named.foldl (·.insert ·) {}
    let st : SS := { occ := m.occ, cst := cstM, keys := keysM, named := namedS, pend := [] }
    (s!"⟨{a}, {w}, {bitsOfSet m.occ}, {listText (named.map toString)}, " ++
      s!"{listText (cst.map fun (c, (x, y, z)) => s!"({c}, {x}, {y}, {z})")}, " ++
      s!"{listText (keys.map fun (c, (op, ins)) => s!"({c}, {op}, {listText (ins.map toString)})")}⟩", st)
  let mut st := nameStep (ctxAt 0) init cf.params
  let mut out : List String := []
  let mut costs : List ℕ := []
  let mut cost := 0
  for w in [0:nw] do
    let X := ctxAt w
    let a := starts[w]!
    let b := if w + 1 < nw then starts[w + 1]! else body.size
    if w > 0 then
      let (t, st') := snap a w st
      out := out ++ [t]
      costs := costs ++ [cost]
      cost := 0
      st := st'
    for idx in [a:b] do
      if cost ≥ (if cf.body.length > 4000 then maxShareWin / 2 else maxShareWin) && idx > a && st.pend.isEmpty then
        let (t, st') := snap idx w st
        out := out ++ [t]
        costs := costs ++ [cost]
        cost := 0
        st := st'
      let s := body[idx]!
      let lo := los[w]!
      let hi := min his[w]! locA.size
      for v in Memory.Stmt.usesList [s] ++ Memory.Stmt.tmpsList [s] do
        unless (lo ≤ v.idx && v.idx < hi) || (insW[w]!).any (·.1 == v.idx) do
          throw s!"sharing of function {j}, statement {idx}: value {v.idx} has no cell in window {w}"
      st ← (swS X st s).mapError (s!"sharing of function {j}, statement {idx}: " ++ ·)
      if mayRet s && !st.pend.isEmpty then throw s!"sharing of function {j}, statement {idx}: pending after a return"
      cost := cost + (Check.stmtsVals [s]).length
    unless st.pend.isEmpty do throw s!"sharing of function {j}: pending at the end of window {w}"
  return (out, costs ++ [cost])

end ShareM
end GuestCert

namespace GuestCert

/-- The functions whose top-level `match`es have their arms counted separately (`Data.cplArms`). -/
def armedFns : List String := ["verify_lean_xmss"]

/-- The completeness data of function `j`: the fixed cells, call sites, table jumps, temporaries
and runs, as a `B2C.Plumb` literal; fails if the completeness walk does. -/
def plumbOfFn (T : Tables) (fns : Array CompiledFn) (selfByEntry : Std.HashMap ℕ (List ℕ))
    (expTable : Std.HashMap ℕ ℕ) (j : ℕ) (cf : Core.Fn) (locs : List ℕ) (segs : Array GSeg)
    (fsz : ℕ) : Except String (String × List (ℕ × Cpl.PC) × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) ×
      Array (ℕ × Pos × List ℕ × ℕ × ℕ) × (ℕ → List Core.Stmt → GSeg → ℕ → ℕ) ×
      Array (ℕ × List (List ℕ))) := do
  let f := fns[j]!
  let F := factsOf T f (j == 1)
  let vcells : Std.HashSet ℕ := locs.foldl (·.insert ·) {}
  let fm := firsts (fun v => locs.getD v.idx 0) {} cf.body
  let byCell : Std.HashMap ℕ (List ℕ) := locs.zipIdx.foldl (fun m (c, v) => m.insert c (v :: m.getD c [])) {}
  let constCell (o : ℕ) (l : ℕ × ℕ × ℕ) : Bool := (byCell.getD o []).all fun v => match fm.get? v with
    | some (k, _, imm, _) => k == "const" && imm == toString l
    | none => true
  let (plumb, errs) := plumbOf f F vcells T.pows constCell
  unless errs.isEmpty do throw s!"{errs}"
  -- cells past the frame are the next iteration's
  let plumb := plumb.filter fun o _ => o < fsz
  let segMap := segs.foldl (fun m s => m.insert s.start s) ({} : Std.HashMap ℕ GSeg)
  let cell (v : ℕ) : ℕ := locs.getD v 0
  let ctx : Cpl.Ctx := ⟨f.name, cell, vcells, plumb, T.pows, segMap, f.entry, cf.params.length,
    j == 1, fun e => selfByEntry.getD e [], fsz, fun r => expTable.getD r 0,
    if armedFns.contains f.name then (cf.body.filterMap fun
      | .match_ v _ => some v.idx
      | _ => none).foldl (·.insert ·) {} else {}⟩
  let st00 : Cpl.St := plumb.fold (fun st o pc => match pc with
    | .k l => if vcells.contains o then { st with know := st.know.insert o l, occ := st.occ.insert o } else st
    | _ => st) {}
  let st0 : Cpl.St := cf.params.foldl (fun st v => Cpl.nameV cell st v.idx) st00
  let (_, out) ← ((Cpl.block cf.body (0, 0) st0 (top := true)).run ctx).run {}
  unless out.fails.isEmpty do throw s!"completeness: {out.fails.toList.take 5}"
  -- one site per key, its cells apart from the values and the fixed cells, and from each other
  let mut byKey : Std.HashMap (List ℕ × List ℕ) (ℕ × ℕ × Option ℕ) := {}
  let mut used : Std.HashSet ℕ := {}
  for (a, r, q, rp, tg) in out.sites do
    match byKey.get? (a, r) with
    | some x => if x != (q, rp, tg) then throw s!"{f.name}: site {a} {r} ambiguous"
    | none =>
      byKey := byKey.insert (a, r) (q, rp, tg)
      for c in q :: tg.toList do
        if vcells.contains c || plumb.contains c || used.contains c then
          throw s!"{f.name}: site cell {c} not apart"
        used := used.insert c
  let arms := out.arms.toList.eraseDups
  for (_, t, _) in arms do
    if vcells.contains t || plumb.contains t || used.contains t then
      throw s!"{f.name}: table cell {t} not apart"
    used := used.insert t
  let pcText : Cpl.PC → String
    | .k (k0, k1, k2) => s!"(.k {k0} {k1} {k2})"
    | .fpg e => s!"(.fpg {e})"
  let stat := (plumb.toList.mergeSort (·.1 ≤ ·.1)).map fun (o, pc) => s!"({o}, {pcText pc})"
  let sites := (byKey.toList.mergeSort (fun a b => a.2.2.1 ≤ b.2.2.1)).map fun ((a, r), (q, rp, tg)) =>
    s!"⟨{listText (a.map toString)}, {listText (r.map toString)}, {q}, {rp}, {tg.getD 0}⟩"
  let atoms := allAtoms cf.body
  let tmps := atoms.flatMap fun
    | .rangeCheck _ _ t1 t2 _ => [t1, t2]
    | _ => []
  let runs := (atoms.flatMap fun
    | .frameAddr _ run => run
    | _ => []).eraseDups
  let vc (v : Core.V) : String := s!"({v.idx}, {cell v.idx})"
  let pmax := out.best
  let sh := ((byCell.toList.filter fun (c, vs) => 2 ≤ c && 2 ≤ vs.length).map (·.1)).mergeSort (· ≤ ·)
  let statL := plumb.toList.mergeSort (·.1 ≤ ·.1)
  return (·, statL, sh, tmps.map (fun v => (v.idx, cell v.idx)), runs.map (fun v => (v.idx, cell v.idx)),
    out.marks, fun t => Cpl.midStop ctx st0 (out.flight.getD t ({}, {})), out.armCosts) <|
    s!"/-- `{f.name}`. -/
noncomputable def plumb{j} : B2C.Plumb where
  stat := {listText stat}
  sites := {listText sites}
  arms := {listText (arms.map tripText)}
  tmps := {listText (tmps.map vc)}
  runs := {listText (runs.map vc)}
  pmax := {listText (pmax.map toString)}
  sh := {listText (sh.map toString)}
"

end GuestCert

namespace GuestCert

/-! ## Files -/

def maxFile : ℕ := 800000

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
def powCut : ℕ := 6

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

/-- The frame sizes, by compiled function index. -/
def framesFile (fsz : List ℕ) : String :=
  header "FrameSizes" "The frame size of each compiled function, by index." ++
  "public import LeanVM.Guest.Exec\n" ++ preamble ++
  "/-- Frame sizes by compiled function index (`__jump_tables` shares `main`'s frame): a loop\n" ++
  "helper's is where its tail call puts the next frame, any other's past every frame cell its\n" ++
  "code and certificate name. -/\n" ++
  s!"def frameSizes : List ℕ := {listText (fsz.map toString)}\n" ++ tail

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
def maxChecked : ℕ := 2000

def checkedHeader (mod what : String) : String :=
  s!"/-
  LeanVM.Guest.Checked{if mod.isEmpty then "" else "." ++ mod}

  Generated by `lake exe guest-cert` (formal/lean_vm/cli/GuestCert.lean); do not edit.
  {what}
-/

module

"

/-- A module of checks, named after its first window. -/
def checkedName (p : ℕ × ℕ) : String := s!"F{p.1}_{p.2}"

def powName (k : ℕ) : String := if k < 10 then s!"Pow0{k}" else s!"Pow{k}"

/-- A proof for `j` from `lo` to `lo + n`, by halving the range, `leaf k` at `j = k`. -/
partial def okTree (leaf : ℕ → String) (lo n : ℕ) : String :=
  if n ≤ 1 then s!"(by obtain rfl : j = {lo} := (by omega); exact {leaf lo})"
  else
    let m := lo + n / 2
    s!"(if h : j < {m} then {okTree leaf lo (n / 2)} else {okTree leaf m (n - n / 2)})"

/-- The functions per module of `CheckOk` and `Plain` proofs (`Checked/Fn*.lean`). -/
def fnBlock : ℕ := 100

/-- The modules deciding the checks: each window's (`(function, window, instructions)`), in
modules of consecutive windows, and each subtree of the power tree's. -/
def checkedFiles (wins : Array (ℕ × ℕ × ℕ)) (ps : Array (ℕ × ℕ)) (nPow : ℕ) :
    List (String × String) := Id.run do
  let fns := Data.functions.toArray
  -- a function cut in windows has a module per window
  let cut (j : ℕ) : Bool := wins.any fun (j', w, _) => j' == j && w > 0
  let mut groups : Array (Array (ℕ × ℕ)) := #[#[]]
  let mut size := 0
  for (j, w, l) in wins do
    if (size + l > maxChecked || cut j) && size > 0 then
      groups := groups.push #[]
      size := 0
    groups := groups.modify (groups.size - 1) (·.push (j, w))
    size := if cut j then maxChecked + 1 else size + l
  let key (js : Array (ℕ × ℕ)) : String := checkedName (js[0]?.getD (0, 0))
  let fnFiles := groups.toList.map fun js =>
    (key js, checkedHeader (key js) "The kernel's checks of windows of compiled functions." ++
      "public import LeanVM.Guest.CheckWinC\n\nnamespace LeanVM.Guest.Checked\n\nopen LeanVM.Guest.Check\n\n@[expose] public section\n\n" ++
      String.join (js.toList.map fun (j, w) =>
        s!"/-- `{fns[j]!.name}`, window {w}. -/\ntheorem w{j}_{w} : WinOk {j} {w} := winOk_of_C (by decide +kernel)\n\n") ++
      String.join ((js.toList.filter fun (j, _) => !cut j).map fun (j, _) =>
        s!"theorem ok{j} : CheckOk {j} := checkOk_one (by decide +kernel) w{j}_0\n\n") ++
      "end\nend LeanVM.Guest.Checked\n")
  let powFiles := (List.range nPow).map fun i =>
    (powName i, checkedHeader (powName i) "The kernel's check of a subtree of the powers of `g`." ++
      s!"public import LeanVM.Guest.Pow\n\nnamespace LeanVM.Guest.Checked\n\n@[expose] public section\n\n" ++
      s!"theorem powT{i}_ok : Data.powT{i}.OkW := by decide +kernel\n\nend\nend LeanVM.Guest.Checked\n")
  -- the functions cut in windows, from their windows' modules
  let cutFns := (wins.toList.filterMap fun (j, w, _) => if w > 0 then some j else none).eraseDups
  let cutOk (j : ℕ) : String :=
    let ws := (wins.toList.filter (·.1 == j)).map (·.2.1)
    s!"theorem ok{j} : CheckOk {j} := fun i hi ↦ by\n" ++
    s!"  have h : (certOf {j}).cuts.length = {ws.length - 1} := by decide +kernel\n" ++
    s!"  rw [h] at hi\n  interval_cases i\n" ++
    String.join (ws.map fun w => s!"  · exact w{j}_{w}\n") ++ "\n" ++
    (if j == 1 || j == 16 then "" else s!"theorem plain{j} : Plain {j} := by\n  unfold Plain\n  decide +kernel\n\n")
  -- each function's `CheckOk` and `Plain`, in modules of `fnBlock` consecutive functions
  let modsOf (j : ℕ) : List String :=
    (groups.toList.filter fun js => js.any (·.1 == j)).map key
  let blocks := ((List.range ((fns.size - 1 + fnBlock - 1) / fnBlock)).map fun b =>
    ((List.range fnBlock).map (b * fnBlock + 1 + ·)).filter (· < fns.size))
  let okFiles := blocks.zipIdx.map fun (js, b) =>
    let imps := (js.filter cutFns.contains).flatMap modsOf
    (s!"Fn{b}", checkedHeader s!"Fn{b}" "Each compiled function checked, every window, and its windows' obligations." ++
      "public import LeanVM.Guest.CheckWinC\n" ++
      String.join (imps.map fun n => s!"public import LeanVM.Guest.Checked.{n}\n") ++
      "\nnamespace LeanVM.Guest.Checked\n\n@[expose] public section\n\n" ++
      String.join (js.map fun j =>
        if cutFns.contains j then cutOk j
        else if j == 1 || j == 16 then ""
        else s!"theorem plain{j} : Plain {j} := plain_of_nil (by decide +kernel)\n\n") ++
      "end\nend LeanVM.Guest.Checked\n")
  let index := ("Checked", checkedHeader "" "Every compiled function checked, and the powers of `g`." ++
    String.join ((fnFiles ++ powFiles ++ okFiles).map fun (n, _) => s!"public import LeanVM.Guest.Checked.{n}\n") ++
    "\nnamespace LeanVM.Guest.Checked\n\nopen LeanVM.Guest.Exec\n\n@[expose] public section\n\n" ++
    "/-- Every function but `__jump_tables` is checked. -/\n" ++
    "theorem all_ok : ∀ j, 1 ≤ j → j < nFns → CheckOk j := fun j h1 h2 ↦\n  " ++
    s!"have h2 : j < {fns.size} := h2\n  " ++
    okTree (fun k => s!"ok{k}") 1 (fns.size - 1) ++ "\n\n" ++
    "/-- No function but `main` and `verify_sub` takes anything from obligations. -/\n" ++
    "theorem all_plain : ∀ j, 1 ≤ j → j < nFns → j ≠ 1 → j ≠ 16 → Plain j := fun j h1 h2 n1 n16 ↦\n  " ++
    s!"have h2 : j < {fns.size} := h2\n  " ++
    okTree (fun k => if k == 1 then "absurd rfl n1" else if k == 16 then "absurd rfl n16" else s!"plain{k}")
      1 (fns.size - 1) ++ "\n\n" ++
    "/-- Every power of `g` the guest names is one. -/\ntheorem powTree_ok : Data.powTree.OkW :=\n  " ++
    (powTopProof ps powCut 0).1 ++ "\n\nend\nend LeanVM.Guest.Checked\n")
  return fnFiles ++ powFiles ++ okFiles ++ [index]

def sharedDir : System.FilePath := "LeanVM/Guest/B2C/Shared"

/-- The most cost (values named) of the sharing windows one module decides. -/
def maxShared : ℕ := 2400

/-- The modules deciding the sharing check: each function's static check (`(function, cost)`) and
windows (`(function, window, cost)`), in modules of at most `maxShared` cost; a function of one
window has its static check, window and `ShareOk` together, one of several its `ShareOk` in the
index. -/
def sharedFiles (statics : Array (ℕ × ℕ)) (wins : Array (ℕ × ℕ × ℕ)) (n : ℕ) :
    List (System.FilePath × String) := Id.run do
  let fns := Data.functions.toArray
  let cut (j : ℕ) : Bool := wins.any fun (j', w, _) => j' == j && w > 0
  -- items: `(function, none)` a static check, `(function, some w)` a window
  let mut items : Array (ℕ × Option ℕ × ℕ) := #[]
  for (j, sc) in statics do
    if cut j then
      items := items.push (j, none, sc)
      for (j', w, l) in wins do
        if j' == j then items := items.push (j, some w, l)
    else
      let l := (wins.toList.find? (·.1 == j)).map (·.2.2) |>.getD 0
      items := items.push (j, some 0, sc + l)
  let mut groups : Array (Array (ℕ × Option ℕ)) := #[#[]]
  let mut size := 0
  for (j, w, l) in items do
    if size + l > maxShared && size > 0 then
      groups := groups.push #[]
      size := 0
    groups := groups.modify (groups.size - 1) (·.push (j, w))
    size := size + l
  let name (k : ℕ) : String := if k < 10 then s!"S00{k}" else if k < 100 then s!"S0{k}" else s!"S{k}"
  let stText (j : ℕ) : String :=
    s!"set_option maxRecDepth 100000 in\n/-- `{fns[j]!.name}`, once. -/\n" ++
    s!"theorem st{j} : shareStatic {j} = true := by decide +kernel\n\n"
  let winText (j w : ℕ) : String :=
    s!"set_option maxRecDepth 100000 in\n/-- `{fns[j]!.name}`, window {w}. -/\n" ++
    s!"theorem w{j}_{w} : shareWin {j} (snapsOf {j}) {w} = true := by decide +kernel\n\n"
  let files := groups.toList.zipIdx.map fun (js, k) =>
    (sharedDir / (name k ++ ".lean"), checkedHeader ("B2C.Shared." ++ name k)
      "The kernel's sharing checks of compiled functions." ++
      "public import LeanVM.Guest.B2C.Share\n\nnamespace LeanVM.Guest.B2C.Shared\n\n@[expose] public section\n\n" ++
      String.join (js.toList.map fun (j, w) => match w with
        | none => stText j
        | some w => if cut j then winText j w else
          stText j ++ winText j w ++
          s!"theorem ok{j} : ShareOk {j} := ⟨st{j}, fun i hi ↦ by\n" ++
          s!"  have h : (snapsOf {j}).length = 0 := by decide +kernel\n" ++
          s!"  obtain rfl : i = 0 := by omega\n  exact w{j}_0⟩\n\n") ++
      "end\nend LeanVM.Guest.B2C.Shared\n")
  let cutFns := (wins.toList.filterMap fun (j, w, _) => if w > 0 then some j else none).eraseDups
  let cutOk := String.join (cutFns.map fun j =>
    let ws := (wins.toList.filter (·.1 == j)).map (·.2.1)
    s!"theorem ok{j} : ShareOk {j} := ⟨st{j}, fun i hi ↦ by\n" ++
    s!"  have h : (snapsOf {j}).length = {ws.length - 1} := by decide +kernel\n" ++
    s!"  rw [h] at hi\n  interval_cases i\n" ++
    String.join (ws.map fun w => s!"  · exact w{j}_{w}\n") ++ "⟩\n\n")
  let index := ("LeanVM/Guest/B2C" : System.FilePath) / "Shared.lean"
  let text := checkedHeader "B2C.Shared" "Every compiled function's sharing check." ++
    "public import Mathlib.Tactic.IntervalCases\n" ++ String.join (files.map fun (p, _) => s!"public import LeanVM.Guest.B2C.Shared.{(p.fileStem.getD "")}\n") ++
    "\nnamespace LeanVM.Guest.B2C.Shared\n\n@[expose] public section\n\n" ++ cutOk ++
    "/-- Every function but `__jump_tables` passes the sharing check. -/\n" ++
    "theorem all : ∀ j, 1 ≤ j → j < nFns → ShareOk j := fun j h1 h2 ↦\n  " ++
    s!"have h2 : j < {n + 1} := h2\n  " ++ okTree (fun k => s!"ok{k}") 1 n ++ "\n\nend\nend LeanVM.Guest.B2C.Shared\n"
  return files ++ [(index, text)]

/-- The sharing check's snapshots: one definition each, in files `Data/SnapsNN.lean` of at most
300000 characters, and their index `Data/Snaps.lean`. -/
def snapsFiles (ss : List (ℕ × List String)) : List (String × String) := Id.run do
  let ss := ss.filter (!·.2.isEmpty)
  let defs := ss.flatMap fun (j, l) => l.zipIdx.map fun (t, k) =>
    s!"/-- Function {j}'s window {k + 1} starts from this. -/\nnoncomputable def snap{j}_{k + 1} : B2C.Snap :=\n  {t}\n"
  let mut fs : Array (Array String) := #[#[]]
  let mut size := 0
  for d in defs do
    if size + d.length > 300000 && size > 0 then
      fs := fs.push #[]
      size := 0
    fs := fs.modify (fs.size - 1) (·.push d)
    size := size + d.length
  let name (k : ℕ) : String := if k < 10 then s!"Snaps0{k}" else s!"Snaps{k}"
  let parts := fs.toList.zipIdx.map fun (ds, k) =>
    (name k, header (name k) "The sharing check's snapshots of the guest's compiled functions." ++
      "public import LeanVM.Guest.Exec\npublic import LeanVM.Guest.B2C.Types\n" ++ preamble ++
      "\n".intercalate ds.toList ++ tail)
  let index := header "Snaps" "The sharing check's snapshots, by compiled function index." ++
    String.join (parts.map fun (m, _) => s!"public import LeanVM.Guest.Data.{m}\n") ++
    "public import LeanVM.Guest.B2C.Types\n" ++ preamble ++
    String.join (ss.map fun (j, l) =>
      s!"/-- Function {j}'s windows after the first start from these. -/\n" ++
      s!"noncomputable def snaps{j} : List B2C.Snap :=\n  " ++
      listText ((List.range l.length).map fun k => s!"snap{j}_{k + 1}") ++ "\n\n") ++
    "/-- The snapshots, by compiled function index (functions of one window omitted). -/\n" ++
    "noncomputable def snaps : List (ℕ × List B2C.Snap) :=\n  " ++
    listText (ss.map fun (j, _) => s!"({j}, snaps{j})") ++ "\n" ++ tail
  return parts ++ [("Snaps", index)]

namespace CplK

/-!
## The completeness walk's parts

`B2C.cplWin j i k` walks part `k` of window `i` of function `j` by its own kernel evaluation,
from the data `Data.cplParts` gives it (`[s, J, x, m, set, d, jp, b, u]`): its first statement
`s` in the window, the code offset `J` of the segment it starts at, the most instructions of each
opcode a path passes up to there, and the callee frame pointer and dispatch target cells set up
on the paths there (a bit set). The data are the completeness walk's (`Cpl.block`'s marks), the
same counts the kernel's walk takes. A part starts at a segment's start after a statement the
kernel's walk may stop after (`ite`, `match_`, a call or dispatch returning nothing, a `callIf`),
never between a `match` or `dispatch` and the top-level atom naming its selector; a costly window
whose statements are mostly atoms is cut inside its first segment, after the items the earlier
statements' facts justify (`Cpl.midStop`). A window is
cut in parts so that each part's walk is cheap enough (`partCost`), and the checks are grouped in
modules (`modCost`).
-/

/-- The most a part may cost (instructions passed, plus `stmtCost` per statement). -/
def partCost : ℕ := 3000


/-- What a statement costs the walk besides its instructions. -/
def stmtCost : ℕ := 2

/-- The most a module of checks may cost (its parts' costs and windows' instructions). -/
def modCost : ℕ := 20000

/-- A part this costly has a module of its own. -/
def heavyCost : ℕ := 4000

/-- One function's parts: per window, its parts' data and their costs. -/
structure FnParts where
  j : ℕ
  name : String
  wins : List (List (List ℕ))
  costs : List (List ℕ)

/-- The selectors of the `match`es and dispatches of a statement. -/
partial def selectors : Core.Stmt → List Core.V
  | .ite _ z n => z.flatMap selectors ++ n.flatMap selectors
  | .match_ v arms => v :: arms.flatMap (·.flatMap selectors)
  | .dispatch v _ _ _ => [v]
  | _ => []

/-- The statements a part may not start at: between the last top-level atom before a `match` or
dispatch naming its selector and it. -/
def forbidden (body : Array Core.Stmt) (nargs : ℕ) : Std.HashSet ℕ := Id.run do
  let mut out : Std.HashSet ℕ := {}
  for t in [0:body.size] do
    for v in selectors body[t]! do
      if v.idx < nargs then continue
      let d? := (List.range t).reverse.find? fun d => match body[d]! with
        | .atom a => (Memory.atomUses a).contains v
        | _ => false
      if let some d := d? then
        for m in [d + 1:t + 1] do out := out.insert m
  return out

/-- The counts and set-up cells at code offset `J` from a mark at statement `a`: the mark's, and
the items of its segment before `J`. -/
def atOffset (segMap : Std.HashMap ℕ GSeg) (entry J : ℕ) (m : ℕ × Pos × List ℕ × ℕ × ℕ) :
    List ℕ × ℕ :=
  let (_, (sg, i), cnt, uq, _) := m
  if i == 0 && sg == J then (cnt, uq) else
    match segMap.get? sg with
    | some s =>
      -- each instruction's pc: an executed instruction carries it, a `JUMP` follows the last
      let pcs := (s.items.toList.foldl (fun (acc : List (Option ℕ) × ℕ) it => match it with
        | .ins (.instr pc _) => (some pc :: acc.1, pc + 1)
        | .ins (.jump ..) | .branch .. => (some acc.2 :: acc.1, acc.2 + 1)
        | _ => (none :: acc.1, acc.2)) ([], entry + s.start)).1.reverse
      let before := ((s.items.toList.zip pcs).drop i).filter fun (_, pc) => match pc with
        | some pc => pc < entry + J
        | none => false
      (Cpl.countRest ⟨s.start, s.env, (before.map (·.1)).toArray, s.exit⟩ 0 cnt, uq)
    | none => (cnt, uq)

/-- The instructions a path passes up to a mark. -/
def insAt (m : ℕ × Pos × List ℕ × ℕ × ℕ) : ℕ := m.2.2.1.foldl (· + ·) 0

/-- **The parts of function `j`'s windows** (`starts` their first statements, `offs` their code
offsets, `sizes` their instructions), from the completeness walk's marks. -/
def partsOf (j : ℕ) (f : CompiledFn) (F : GFacts) (cf : Core.Fn) (segs : Array GSeg) (starts : Array ℕ)
    (wins0 : List (ℕ × List (ℕ × Sym) × ℕ)) (sizes : List ℕ) (marks : Array (ℕ × Pos × List ℕ × ℕ × ℕ))
    (stopAt : ℕ → List Core.Stmt → GSeg → ℕ → ℕ) : FnParts := Id.run do
  let segMap := segs.foldl (fun m s => m.insert s.start s) ({} : Std.HashMap ℕ GSeg)
  let offs := wins0.map (·.1)
  let body := cf.body.toArray
  let bad := forbidden body cf.params.length
  let nw := starts.size
  let zero : List ℕ := [0, 0, 0, 0, 0, 0]
  let mut wins : Array (List (List ℕ)) := #[]
  let mut costs : Array (List ℕ) := #[]
  for w in [0:nw] do
    let a := starts[w]!
    let b := if w + 1 < nw then starts[w + 1]! else body.size
    let (c0, u0) := if w == 0 then (zero, 0) else
      match marks[a]? with
      | some m => atOffset segMap f.entry (offs.getD w 0) m
      | none => (zero, 0)
    let cost (s e : ℕ) : ℕ :=
      let ins (t : ℕ) : ℕ := (marks[t]?.map insAt).getD (insAt (marks.back?.getD (0, (0, 0), zero, 0, 0)))
      (ins e - ins s) + stmtCost * (e - s)
    let cands := (List.range (b - a)).filterMap fun d =>
      let t := a + d
      if d == 0 || bad.contains t then none
      else match marks[t]? with
        | some (_, (_, 0), _, _, 1) => some t
        | _ => none
    -- as many parts as the window's cost needs, each cut at the start nearest its share
    let total := cost a b
    let n := (total + partCost - 1) / partCost
    let mut cuts : Array ℕ := #[]
    for k in [1:n] do
      let goal := total * k / n
      let prev := cuts.back?.getD a
      let best := (cands.filter (prev < ·)).foldl (fun (o : Option ℕ) t => match o with
        | some u => if (if cost a t ≥ goal then cost a t - goal else goal - cost a t) <
            (if cost a u ≥ goal then cost a u - goal else goal - cost a u) then some t else some u
        | none => some t) none
      if let some t := best then cuts := cuts.push t
    -- each part: its first statement, segment and counts and set-up cells there
    let starts0 : List (ℕ × ℕ × List ℕ × ℕ) := (a, offs.getD w 0, c0, u0) :: cuts.toList.map fun t =>
      match marks[t]? with
      | some (_, (sg, _), cnt, uq, _) => (t, sg, cnt, uq)
      | none => (t, 0, zero, 0)
    let ends0 := cuts.toList ++ [b]
    let stmtsOf (x y : ℕ) : List Core.Stmt := (body.toList.drop x).take (y - x)
    let mut ps : List (List ℕ) := []
    let mut partCosts : List ℕ := []
    for ((sa, J, cS, uS), se) in starts0.zip ends0 do
      let pc := cost sa se + sizes.getD w 0
      ps := ps ++ [(sa - a) :: (if sa == a then 0 else J) :: cS ++ [uS]]
      -- a costly part that is mostly a run of atoms walked inside one segment (from its start):
      -- cut that run inside the segment, by statements
      let isAtom (x : ℕ) : Bool := match body[x]? with
        | some (.atom _) => true
        | _ => false
      let runs := (List.range (se - sa)).filterMap fun d =>
        let x := sa + d
        let fresh := x == sa || (match marks[x]? with
          | some (_, (_, 0), _, _, _) => true
          | _ => false)
        if isAtom x && (x == sa || !isAtom (x - 1)) && fresh then
          some (x, ((List.range (se - x)).takeWhile fun e => isAtom (x + e)).length)
        else none
      let best := runs.foldl (fun (o : Option (ℕ × ℕ)) r => match o with
        | some q => if r.2 > q.2 then some r else some q
        | none => some r) none
      let mut mids : Array (ℕ × ℕ) := #[]
      if let some (t0, len) := best then
        let (sg, c1, u1) := if t0 == sa then (J, cS, uS) else match marks[t0]? with
          | some (_, (sg, _), cnt, uq, _) => (sg, cnt, uq)
          | none => (J, cS, uS)
        if pc > partCost && 2 * len ≥ se - sa then
          -- the window's own segments, as the kernel's walk has them
          let (J0, env0, e0) := wins0.getD w (0, [], f.len)
          let segW := execG F f J0 e0 (env0.foldl (fun m (o, s) => m.insert o s) {})
          if let some s0 := segW.find? (·.start == sg) then
            let nm := (pc + partCost - 1) / partCost
            let mut prevS := sa
            let mut prevM := 0
            for k in [1:nm] do
              let s := t0 + len * k / nm
              if s ≤ prevS || bad.contains s then continue
              let m := stopAt t0 (stmtsOf prevS s) s0 prevM
              if m ≤ prevM || m ≥ s0.items.size then continue
              mids := mids.push (s, m)
              prevS := s
              prevM := m
            ps := ps ++ mids.toList.map fun (s, m) =>
              let cnt := Cpl.countRest ⟨s0.start, s0.env, (s0.items.toList.take m).toArray, s0.exit⟩ 0 c1
              (s - a) :: sg :: cnt ++ [u1, m]
      partCosts := partCosts ++ (List.range (mids.size + 1)).map fun _ => pc / (mids.size + 1)
    wins := wins.push (if ps.length == 1 && c0 == zero && u0 == 0 then [] else ps)
    costs := costs.push partCosts
  return ⟨j, f.name, wins.toList, costs.toList⟩

def header (mod what : String) : String :=
  s!"/-
  LeanVM.Guest.{mod}

  Generated by `lake exe guest-cert` (formal/lean_vm/cli/GuestCert.lean); do not edit.
  {what}
-/

module

"

def cplwDir : System.FilePath := "LeanVM/Guest/B2C/Cplw"

def partText (p : List ℕ) : String := listText (p.map toString)

/-- `Data/CplArms.lean`: by compiled function, its separately counted `match`es, the counts of
each arm. -/
def armsFile (rows : List (Array (ℕ × List (List ℕ)))) : String :=
  let n := (rows.zipIdx.filter (!·.1.isEmpty)).foldl (fun m (_, j) => max m (j + 1)) 0
  let rowText (r : Array (ℕ × List (List ℕ))) : String :=
    listText (r.toList.map fun (x, cs) => s!"({x}, {listText (cs.map partText)})")
  header "Data.CplArms" "The per-arm instruction counts of the `match`es whose arms the completeness walk counts\n  separately." ++
    "public import LeanVM.Guest.Code\n\n/-!\nFunction `j`'s entry is a list of `(x, costs)`: the `match` on the renumbered value `x` has its\n" ++
    "arms counted separately, arm `k` at most `costs[k]` instructions of each opcode (in `Opcode`'s\n" ++
    "order) from its segment to the join, the callees' apart. Every other `match` counts its arms by\n" ++
    "their maximum. Checked by `B2C.cplWin`.\n-/\n\nnamespace LeanVM.Guest.Data\n\n@[expose] public section\n\n" ++
    "/-- The per-arm counts, by function. -/\ndef cplArms : List (List (ℕ × List (List ℕ))) := " ++
    (if n == 0 then "[]" else "[\n  " ++ ",\n  ".intercalate ((rows.take n).map rowText) ++ "]") ++
    "\n\nend\nend LeanVM.Guest.Data\n"

/-- `Data/CplParts.lean`, the decide modules `B2C/Cplw/C*.lean` and their index `B2C/Cplw.lean`. -/
def cplFiles (fps : List FnParts) : List (System.FilePath × String) := Id.run do
  let n := fps.length
  let rows := fps.map fun fp =>
    if fp.wins.all (·.isEmpty) then "  []"
    else "  [" ++ ",\n   ".intercalate (fp.wins.map fun w => listText (w.map partText)) ++ "]"
  let data := header "Data.CplParts" "The parts of the completeness walk's windows, and what each part's start is handed." ++
    "public import LeanVM.Guest.Code\n\n/-!\nPart `k` of window `i` of function `j` is `[s, J, x, m, c, d, jp, b, u, mo]`: it starts at the\n" ++
    "window's statement `s` and code offset `J` (the window's start for the first part), with the\n" ++
    "counts of each opcode (in `Opcode`'s order) the walk's paths pass at most up to there, and the\n" ++
    "bit set `u` of the callee frame pointer and dispatch target cells they set up, and, for a part\n" ++
    "starting inside the segment at `J`, the number `mo` of its items before (`0` if absent). A window\n" ++
    "of one part with nothing handed on is `[]`. Checked by `B2C.cplWin`.\n-/\n\nnamespace LeanVM.Guest.Data\n\n@[expose] public section\n\n" ++
    "/-- The parts of each window, by function and window. -/\ndef cplParts : List (List (List (List ℕ))) := [\n  [],\n" ++
    ",\n".intercalate rows ++ "]\n\nend\nend LeanVM.Guest.Data\n"
  -- the checks, in modules of consecutive parts
  -- a heavy part (a costly one, or one of a function cut in windows) has a module of its own
  let items := fps.flatMap fun fp => (fp.costs.zipIdx.flatMap fun (cs, i) =>
    cs.zipIdx.map fun (c, k) => (fp.j, i, k, if fp.wins.length > 1 || heavyCost ≤ c then modCost else c))
  let mut groups : Array (Array (ℕ × ℕ × ℕ)) := #[#[]]
  let mut size := 0
  for (j, i, k, c) in items do
    if size + c > modCost && size > 0 then
      groups := groups.push #[]
      size := 0
    groups := groups.modify (groups.size - 1) (·.push (j, i, k))
    size := size + c
  let names := (fps.map fun fp => (fp.j, fp.name)).foldl (fun m (j, s) => m.insert j s) ({} : Std.HashMap ℕ String)
  let mname (js : Array (ℕ × ℕ × ℕ)) : String := let p := js[0]?.getD (0, 0, 0); s!"C{p.1}_{p.2.1}_{p.2.2}"
  -- a function's `CplOk` goes with its parts when they share a module, else in the index
  let modOf : Std.HashMap ℕ (List ℕ) := groups.toList.zipIdx.foldl (fun m (js, g) =>
    js.foldl (fun m (j, _, _) => m.insert j ((g :: m.getD j []).eraseDups)) m) {}
  let okText (fp : FnParts) : String :=
    let nw := fp.wins.length
    s!"theorem ok{fp.j} : CplOk {fp.j} := by\n  intro i hi k hk\n" ++
    s!"  have hc : (certOf {fp.j}).cuts.length = {nw - 1} := by decide +kernel\n  rw [hc] at hi\n  interval_cases i\n" ++
    String.join (fp.costs.zipIdx.map fun (cs, i) =>
      s!"  · have hn : nParts {fp.j} {i} = {cs.length} := by decide +kernel\n    rw [hn] at hk\n    interval_cases k\n" ++
      String.join ((List.range cs.length).map fun k => s!"    · exact cw{fp.j}_{i}_{k}\n")) ++ "\n"
  let homeOf (fp : FnParts) : Option ℕ := match modOf.getD fp.j [] with
    | [g] => some g
    | _ => none
  let files := groups.toList.zipIdx.map fun (js, g) =>
    (cplwDir / (mname js ++ ".lean"), header ("B2C.Cplw." ++ mname js)
      "The kernel's completeness checks of parts of windows of compiled functions." ++
      "public import LeanVM.Guest.B2C.Cpl\npublic import Mathlib.Tactic.IntervalCases\n\n" ++
      "namespace LeanVM.Guest.B2C.Cplw\n\n@[expose] public section\n\n" ++
      String.join (js.toList.map fun (j, i, k) =>
        s!"/-- `{names.getD j ""}`, window {i}, part {k}. -/\n" ++
        s!"theorem cw{j}_{i}_{k} : cplWin {j} {i} {k} = true := by decide +kernel\n\n") ++
      String.join ((fps.filter fun fp => homeOf fp == some g).map okText) ++
      "end\nend LeanVM.Guest.B2C.Cplw\n")
  let oks := String.join ((fps.filter fun fp => (homeOf fp).isNone).map okText)
  let index := header "B2C.Cplw" "Every compiled function passes the completeness check, part by part of every window." ++
    "public import Mathlib.Tactic.IntervalCases\n" ++
    String.join (files.map fun (p, _) => s!"public import LeanVM.Guest.B2C.Cplw.{(p.fileStem.getD "")}\n") ++
    "\nnamespace LeanVM.Guest.B2C.Cplw\n\n@[expose] public section\n\n" ++ oks ++
    "/-- **Every compiled function passes the completeness check.** -/\n" ++
    "theorem cplOk_all : ∀ j, 1 ≤ j → j < nFns → CplOk j := fun j h1 h2 ↦\n  " ++
    s!"have h2 : j < {n + 1} := h2\n  " ++ okTree (fun k => s!"ok{k}") 1 n ++
    "\n\nend\nend LeanVM.Guest.B2C.Cplw\n"
  return [(dataDir / "CplParts.lean", data)] ++ files ++ [(("LeanVM/Guest/B2C" : System.FilePath) / "Cplw.lean", index)]

end CplK

def files (P : Core.Program) : Except String (List (System.FilePath × String)) := do
  let fns := Data.functions.toArray
  let T := tables Data.functions
  let index := (fns.toList.zipIdx.map fun (f, j) => (f.name, j)).foldl
    (fun m (n, j) => if m.contains n then m else m.insert n j) ({} : Std.HashMap String ℕ)
  let mut certs : Array String := #[]
  let mut plumbs : Array String := #[]
  let mut wins : Array (ℕ × ℕ × ℕ) := #[]
  let mut frames : Array ℕ := #[0]
  let selfByEntry : Std.HashMap ℕ (List ℕ) := (fns.toList.drop 1).foldl (fun m f =>
    m.insert f.entry ((factsOf T f false).env.map (·.1))) {}
  let expTable : Std.HashMap ℕ ℕ := logTable.fold (fun m k e => m.insert e k) {}
  let mut shareWins : Array (ℕ × ℕ × ℕ) := #[]
  let mut shareStatics : Array (ℕ × ℕ) := #[]
  let mut snapTexts : Array (ℕ × List String) := #[]
  let mut cplFns : Array CplK.FnParts := #[]
  let mut armRows : Array (Array (ℕ × List (List ℕ))) := #[#[]]
  for (cf, i) in P.zipIdx do
    -- the smaller windows, or the larger ones where the sharing check cannot cut the smaller, and
    -- for `main` and `verify_sub`, whose windows `Sound`'s obligations name
    let attempt (coarse : Bool) := do
      let (c, sizes, fsz, locs, segs, (starts, los, his, insW), offs) ← certOf coarse T fns index (i + 1) cf
      let (pt, statL, sh, tmps, runs, marks, stopAt, acs) ← plumbOfFn T fns selfByEntry expTable (i + 1) cf locs segs fsz
      let (sts, costs) ← ShareM.snaps (i + 1) cf locs starts los his insW statL sh tmps runs
      pure (c, sizes, fsz, locs, segs, starts, offs, pt, marks, stopAt, acs, sts, costs)
    let (c, sizes, fsz, locs, segs, starts, offs, pt, marks, stopAt, acs, sts, costs) ←
      if i + 1 == 1 || i + 1 == 16 then attempt true
      else match attempt false with
        | .ok r => pure r
        | .error _ => attempt true
    certs := certs.push c
    armRows := armRows.push acs
    cplFns := cplFns.push (CplK.partsOf (i + 1) fns[i + 1]! (factsOf T fns[i + 1]! (i == 0)) cf segs starts offs sizes marks
      stopAt)
    plumbs := plumbs.push pt
    snapTexts := snapTexts.push (i + 1, sts)
    frames := frames.push fsz
    wins := wins ++ (sizes.zipIdx.map fun (sz, w) => (i + 1, w, sz)).toArray
    -- a window's fixed cost: its setup, and in a long body the walk to its start
    let fixed := if cf.body.length > 4000 then maxShared else 300
    shareWins := shareWins ++ (costs.zipIdx.map fun (c, k) => (i + 1, k, c + fixed)).toArray
    shareStatics := shareStatics.push (i + 1, locs.length / 4)
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
  let mut pfs : Array (Array String) := #[#[]]
  let mut psize := 0
  for c in plumbs do
    if psize + c.length > maxFile && psize > 0 then
      pfs := pfs.push #[]
      psize := 0
    pfs := pfs.modify (pfs.size - 1) (·.push c)
    psize := psize + c.length
  let plumbName (k : ℕ) : String := if k < 10 then s!"Plumb0{k}" else s!"Plumb{k}"
  let plumbFiles := pfs.toList.zipIdx.map fun (cs, k) =>
    (plumbName k, header (plumbName k) "Completeness data of the guest's compiled functions." ++
      "public import LeanVM.Guest.Exec\npublic import LeanVM.Guest.B2C.Types\n" ++ preamble ++
      "\n".intercalate cs.toList ++ tail)
  let n := P.length
  let pnames := "plumb0" :: (List.range n).map fun i => s!"plumb{i + 1}"
  let prows := (List.range ((pnames.length + 15) / 16)).map fun r =>
    "  " ++ " ".intercalate (((pnames.drop (16 * r)).take 16).map (· ++ " ::"))
  let plumbIndex := header "Plumb" "The completeness data of the guest's compiled functions, by index." ++
    String.join (plumbFiles.map fun (m, _) => s!"public import LeanVM.Guest.Data.{m}\n") ++
    preamble ++ "/-- `__jump_tables`: nothing. -/\ndef plumb0 : B2C.Plumb := {}\n\n" ++
    "/-- The completeness data, by compiled function index. -/\nnoncomputable def plumbs : List B2C.Plumb :=\n" ++
    "\n".intercalate prows ++ " []\n" ++ tail
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
  return (([("Pows", powsFile T), ("FrameSizes", framesFile frames.toList)] ++ certFiles ++
      [("Cert", index)] ++ plumbFiles ++ [("Plumb", plumbIndex)]).map fun (n, t) =>
    (dataDir / (n ++ ".lean"), t)) ++
    (checkedFiles wins (T.pows.toArray.qsort (·.1 < ·.1)) nPow).map (fun (n, t) =>
      (if n == "Checked" then ("LeanVM/Guest" : System.FilePath) / "Checked.lean"
        else checkedDir / (n ++ ".lean"), t)) ++ sharedFiles shareStatics shareWins P.length ++
    (snapsFiles snapTexts.toList).map (fun (n, t) => (dataDir / (n ++ ".lean"), t)) ++ CplK.cplFiles cplFns.toList ++ [(dataDir / "CplArms.lean", CplK.armsFile armRows.toList)]

/-- The generated files on disk. -/
def existing : IO (List System.FilePath) := do
  let gen (pre : String) (n : String) : Bool :=
    let cs := n.toList
    cs.take pre.length == pre.toList && cs.reverse.take 5 == ".lean".toList.reverse &&
      ((cs.drop pre.length).take (cs.length - pre.length - 5)).all fun c => c.isDigit || c == '_'
  let ds ← dataDir.readDir
  let cs ← if ← checkedDir.isDir then checkedDir.readDir else pure #[]
  let ss ← if ← sharedDir.isDir then sharedDir.readDir else pure #[]
  let ws ← if ← CplK.cplwDir.isDir then CplK.cplwDir.readDir else pure #[]
  return (ds.toList.filter (fun e => gen "Cert" e.fileName || gen "Plumb" e.fileName ||
      gen "Snaps" e.fileName)).map (·.path) ++
    (cs.toList.filter fun e => gen "F" e.fileName || gen "Fn" e.fileName || gen "Pow" e.fileName).map (·.path) ++
    (ss.toList.filter fun e => gen "S" e.fileName).map (·.path) ++
    (ws.toList.filter fun e => gen "C" e.fileName).map (·.path)

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
  unless check do
    IO.FS.createDirAll checkedDir
    IO.FS.createDirAll sharedDir
    IO.FS.createDirAll CplK.cplwDir
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
