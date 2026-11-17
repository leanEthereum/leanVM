import LeanVM.Guest.Compiled.Input
import LeanVM.Guest.Interp

/-!
# `guest-ptrcheck`: pointer discipline and load shapes of the guest

Run from `lean_vm` as `lake exe guest-ptrcheck [--detail]`, or `--selftest`. No proof: compiled
execution only.

**Pointer discipline.** Every value of every core function, every parameter and every return
cell gets a type, a pointer or a data word, by unification over the whole program: a copy, an
argument and its parameter, a returned value and its return cell have one type; a `HeapBuf`
pointer, a `frameAddr` pointer, the base of a load and the destination of a hint's heap write are
pointers; `add`, the assertions, the range check's operands, `KECCAK`, a branch condition and a
selector are data; a product is a pointer times data or data times data; a constant is either (an
absolute address, as `main`'s reads of the public input). A value forced both ways is reported
with the two reasons.

The discipline is necessary for re-placing a run's pointers, not sufficient: the self test's
accepted programs include one whose valid core runs all store two `HeapBuf` pointers into one word
(valid only when the two coincide, which no placement allows), and one loading at an offset the
prover chooses, which no check bounds.

**Load shapes.** Each `load d p off` is classified by where `p` comes from in its function
(following copies and products): a constant, a `HeapBuf` or a `frameAddr` with a static offset
(inside or outside its size), a parameter, a loaded pointer or a callee's return, with a static
or a runtime offset.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Compiler LeanVM.Guest.Compiled
  LeanVM.Guest.Compiled.GuestInput

namespace PtrCheck

/-- A typed thing: a value of function `f`, or return cell `k` of function `f`. -/
inductive Node where
  | val (f : Nat) (v : V)
  | ret (f : Nat) (k : Nat)
  deriving BEq, Hashable

/-- A type: unconstrained, data, pointer, or both (a conflict). -/
inductive Ty where
  | bot | data | ptr | top
  deriving BEq, Inhabited, Repr

def Ty.join : Ty → Ty → Ty
  | .bot, t => t
  | t, .bot => t
  | .top, _ => .top
  | _, .top => .top
  | .data, .data => .data
  | .ptr, .ptr => .ptr
  | _, _ => .top

/-- A constraint, with the reason a force records. -/
inductive Con where
  | eq (a b : Node)
  | force (a : Node) (t : Ty) (why : String)
  | mul (d a b : Node) (why : String)

/-- The union-find state. -/
structure St where
  ids : Std.HashMap Node Nat := {}
  parent : Array Nat := #[]
  ty : Array Ty := #[]
  whyP : Array String := #[]
  whyD : Array String := #[]
  changed : Bool := false

abbrev M := StateM St

def node (n : Node) : M Nat := do
  let s ← get
  match s.ids[n]? with
  | some i => return i
  | none =>
    let i := s.parent.size
    set { s with ids := s.ids.insert n i, parent := s.parent.push i, ty := s.ty.push .bot,
                 whyP := s.whyP.push "", whyD := s.whyD.push "" }
    return i

partial def find (i : Nat) : M Nat := do
  let s ← get
  let p := s.parent[i]!
  if p == i then return i
  let r ← find p
  modify fun s => { s with parent := s.parent.set! i r }
  return r

def setTy (r : Nat) (t : Ty) (why : String) : M Unit := do
  let s ← get
  let old := s.ty[r]!
  let new := old.join t
  let whyP := if t == .ptr && s.whyP[r]! == "" then s.whyP.set! r why else s.whyP
  let whyD := if t == .data && s.whyD[r]! == "" then s.whyD.set! r why else s.whyD
  set { s with ty := s.ty.set! r new, whyP, whyD, changed := s.changed || !(new == old) }

def tyOf (n : Node) : M Ty := do
  let r ← find (← node n)
  return (← get).ty[r]!

def force (n : Node) (t : Ty) (why : String) : M Unit := do
  let r ← find (← node n)
  setTy r t why

def union (a b : Node) : M Unit := do
  let ra ← find (← node a)
  let rb ← find (← node b)
  if ra == rb then return
  let s ← get
  let (tb, pb, db) := (s.ty[rb]!, s.whyP[rb]!, s.whyD[rb]!)
  set { s with parent := s.parent.set! rb ra }
  if pb != "" then setTy ra .ptr pb
  if db != "" then setTy ra .data db
  if tb == .bot then pure () else setTy ra tb (if tb == .ptr then pb else db)

/-- One pass over the products. -/
def mulPass (ms : Array (Node × Node × Node × String)) : M Unit := do
  for (d, a, b, why) in ms do
    let td ← tyOf d
    let ta ← tyOf a
    let tb ← tyOf b
    if ta == .ptr || ta == .top then
      force d .ptr why
      force b .data s!"{why} (the other factor of a pointer)"
    if tb == .ptr || tb == .top then
      force d .ptr why
      force a .data s!"{why} (the other factor of a pointer)"
    if td == .data then
      force a .data s!"{why} (a factor of a data product)"
      force b .data s!"{why} (a factor of a data product)"
    if td == .ptr then
      if ta == .data then force b .ptr s!"{why} (the pointer factor)"
      if tb == .data then force a .ptr s!"{why} (the pointer factor)"

def solve (cs : Array Con) : M Unit := do
  let mut ms := #[]
  for c in cs do
    match c with
    | .eq a b => union a b
    | .force a t why => force a t why
    | .mul d a b why => ms := ms.push (d, a, b, why)
  let mut go := true
  let mut n := 0
  while go && n < 1000 do
    modify fun s => { s with changed := false }
    mulPass ms
    go := (← get).changed
    n := n + 1

/-! ## Constraints of a program -/

def showV := Interp.showV

def showA : Atom → String
  | .const d c => s!"const {showV d} {Interp.showE c}"
  | .add d a b => s!"add {showV d} {showV a} {showV b}"
  | .mul d a b => s!"mul {showV d} {showV a} {showV b}"
  | .copy d s => s!"copy {showV d} {showV s}"
  | .load d p off => s!"load {showV d} {showV p} {off}"
  | .assertEq a b => s!"assertEq {showV a} {showV b}"
  | .assertNe x i p => s!"assertNe {showV x} {showV i} {showV p}"
  | .rangeCheck x y t1 t2 k =>
      s!"rangeCheck {showV x} {showV y} {showV t1} {showV t2} {showV k}"
  | .assertInK a b => s!"assertInK {showV a} {showV b}"
  | .keccak ins outs _ _ => s!"keccak ({ins.length} in, {outs.length} out)"
  | .frameAddr p run => s!"frameAddr {showV p} (run of {run.length})"
  | .hint h => match h with
    | .alloc d n => s!"alloc {showV d} {n}"
    | .allocDyn d n => s!"allocDyn {showV d} {showV n}"
    | _ => "hint"
  | .touch t p => s!"touch {showV t} {showV p}"

/-- The values a hint reads, and its heap destination's pointer. -/
def Dest.ptr? : Dest → Option V
  | .heap p _ _ => some p
  | .stack _ => none

def Hint.dest? : Hint → Option Dest
  | .witness _ d | .bits _ _ _ d | .bitsExp _ _ d | .digitsExp _ _ _ _ _ _ d
  | .windowsExp _ _ _ _ d | .log2Ceil d _ _ _ => some d
  | _ => none

/-- The constraints of an atom of function `fi` (named `fn`). -/
def atomCons (fi : Nat) (fn : String) (a : Atom) : Array Con :=
  let x := Node.val fi
  let w := s!"{fn}: {showA a}"
  let dat (vs : List V) (what : String) := (vs.map fun v => Con.force (x v) .data s!"{w} ({what})").toArray
  match a with
  | .const _ _ => #[]
  | .add d a b => dat [d, a, b] "an addition"
  | .mul d a b => #[.mul (x d) (x a) (x b) w]
  | .copy d s => #[.eq (x d) (x s)]
  | .load _ p _ => #[.force (x p) .ptr s!"{w} (a load base)"]
  | .assertEq a b => dat [a, b] "an equality assertion"
  | .assertNe y i p => dat [y, i, p] "a disequality assertion"
  | .rangeCheck y z _ _ k => dat [y, z, k] "a range check"
  | .assertInK _ _ => #[]
  | .keccak ins outs _ _ => dat (ins ++ outs) "KECCAK"
  | .frameAddr p _ => #[.force (x p) .ptr s!"{w} (a frame address)"]
  | .hint (.alloc d _) => #[.force (x d) .ptr s!"{w} (a HeapBuf)"]
  | .hint (.allocDyn d _) => #[.force (x d) .ptr s!"{w} (a HeapBuf)"]
  | .hint h => match (Hint.dest? h).bind Dest.ptr? with
    | some p => #[.force (x p) .ptr s!"{w} (a hint's heap destination)"]
    | none => #[]
  | .touch _ _ => #[]

/-- The constraints of a body of function `fi`, given the functions' indices and parameters. -/
partial def bodyCons (P : Array Fn) (idx : Std.HashMap String Nat) (fi : Nat) (fn : String) :
    List Stmt → Array Con × Array String
  | [] => (#[], #[])
  | s :: ss =>
    let x := Node.val fi
    let callCons (g : String) (args : List V) (rets : Option (List V)) : Array Con × Array String :=
      match idx[g]? with
      | none => (#[], #[s!"{fn}: call of unknown {g}"])
      | some gi =>
        let ps := P[gi]!.params
        let a := (args.zip ps).map fun (v, p) => Con.eq (x v) (.val gi p)
        let r := match rets with
          | some rs => (rs.zipIdx).map fun (v, k) => Con.eq (x v) (.ret gi k)
          | none => []
        let bad := if args.length != ps.length then #[s!"{fn}: call of {g} with {args.length} arguments for {ps.length} parameters"] else #[]
        ((a ++ r).toArray, bad)
    let (c, b) : Array Con × Array String := match s with
      | .atom a => (atomCons fi fn a, #[])
      | .ite c z n =>
        let (c1, b1) := bodyCons P idx fi fn z
        let (c2, b2) := bodyCons P idx fi fn n
        (#[.force (x c) .data s!"{fn}: branch on {showV c}"] ++ c1 ++ c2, b1 ++ b2)
      | .match_ y arms =>
        arms.foldl (fun (cs, bs) arm => let (c', b') := bodyCons P idx fi fn arm; (cs ++ c', bs ++ b'))
          (#[.force (x y) .data s!"{fn}: match on {showV y}"], #[])
      | .call g args rets => callCons g args (some rets)
      | .callIf c g args =>
        let (c', b') := callCons g args none
        (#[.force (x c) .data s!"{fn}: callIf on {showV c}"] ++ c', b')
      | .dispatch y gs args rets =>
        gs.foldl (fun (cs, bs) g => let (c', b') := callCons g args (some rets); (cs ++ c', bs ++ b'))
          (#[.force (x y) .data s!"{fn}: dispatch on {showV y}"], #[])
      | .ret vs => ((vs.zipIdx.map fun (v, k) => Con.eq (x v) (.ret fi k)).toArray, #[])
    let (c', b') := bodyCons P idx fi fn ss
    (c ++ c', b ++ b')

/-- All constraints of a program. -/
def progCons (P : Array Fn) : Array Con × Array String := Id.run do
  let mut idx : Std.HashMap String Nat := {}
  for h : i in [0:P.size] do
    idx := idx.insert P[i].name i
  let mut cs := #[]
  let mut bs := #[]
  for h : i in [0:P.size] do
    let (c, b) := bodyCons P idx i P[i].name P[i].body
    cs := cs ++ c
    bs := bs ++ b
  return (cs, bs)

/-- The conflicts of a program: for each class typed both ways, the reasons. -/
def conflicts (P : Array Fn) : Array (String × String) × Array String × St :=
  let (cs, bad) := progCons P
  let ((), s) := (solve cs).run {}
  let roots := (List.range s.parent.size).filter fun i => s.parent[i]! == i && s.ty[i]! == .top
  (roots.toArray.map fun r => (s.whyP[r]!, s.whyD[r]!), bad, s)

/-! ## Load shapes -/

/-- The atoms and calls of a body in order, with the values they mention. -/
partial def events : List Stmt → List (Sum Atom Stmt)
  | [] => []
  | s :: ss => (match s with
      | .atom a => [Sum.inl a]
      | .ite _ z n => events z ++ events n
      | .match_ _ arms => arms.flatMap events
      | s => [Sum.inr s]) ++ events ss

def atomVals : Atom → List V
  | .const d _ => [d]
  | .add d a b | .mul d a b => [d, a, b]
  | .copy d s => [d, s]
  | .load d p _ => [d, p]
  | .assertEq a b | .assertInK a b => [a, b]
  | .assertNe x i p => [x, i, p]
  | .rangeCheck x y t1 t2 k => [x, y, t1, t2, k]
  | .keccak ins outs _ _ => ins ++ outs
  | .frameAddr p run => p :: run
  | .hint h => match h with
    | .alloc d _ => [d]
    | .allocDyn d s => [d, s]
    | .witness _ (.stack cs) => cs
    | .limbs v ds => v :: ds
    | .inverse x d => [x, d]
    | .log2Ceil (.stack cs) _ _ d => cs ++ [d]
    | .bits _ _ _ (.stack cs) | .bitsExp _ _ (.stack cs) | .digitsExp _ _ _ _ _ _ (.stack cs)
    | .windowsExp _ _ _ _ (.stack cs) => cs
    | _ => []
  | .touch t p => [t, p]

def stmtDefs : Stmt → List V
  | .call _ _ rets | .dispatch _ _ _ rets => rets
  | _ => []

/-- Where a pointer comes from: its root and its offset from the root, static or runtime. -/
structure Origin where
  root : String
  /-- The root's size (a `HeapBuf`'s, a run's), when static. -/
  size : Option Nat := none
  /-- The offset's static part; `none` once a runtime factor is met. -/
  off : Option Int := some 0
  /-- A runtime factor met. -/
  rt : Option V := none
  /-- The root value. -/
  src : String := ""
  deriving Inhabited

def Origin.shift (o : Origin) (k : Option Int) (v : V) : Origin :=
  match k with
  | some k => { o with off := o.off.map (· + k) }
  | none => { o with off := none, rt := o.rt.orElse fun _ => some v }

/-- The kind of a hint, for the report. -/
def hintKind : Hint → String
  | .witness s d => s!"witness {s} into {match d with | .heap .. => "heap" | .stack .. => "frame"}"
  | .bits .. => "bits"
  | .bitsExp .. => "bitsExp"
  | .digitsExp .. => "digitsExp"
  | .windowsExp .. => "windowsExp"
  | .limbs .. => "limbs"
  | .log2Ceil .. => "log2Ceil"
  | .inverse .. => "inverse"
  | .alloc .. => "alloc"
  | .allocDyn .. => "allocDyn"

/-- The origin of `v` in a function, given the first event mentioning each value. -/
partial def origin (defs : Std.HashMap V (Sum Atom Stmt)) (params : List V) (ptrTy : V → Bool)
    (dlog : E → Option Nat) (consts : Std.HashMap V E) (fuel : Nat) (v : V) : Origin :=
  let konst (x : V) : Option Int := (consts[x]?.bind dlog).map Int.ofNat
  let mk (r : String) : Origin := { root := r, src := showV v }
  if fuel == 0 then mk "deep" else
  if params.contains v then mk "param" else
  match defs[v]? with
  | none => mk "undefined"
  | some (.inr _) => mk "callee return"
  | some (.inl a) => match a with
    | .copy d s => if d == v then origin defs params ptrTy dlog consts (fuel - 1) s else mk "copy source"
    | .mul d a b =>
      if d == v then
        let (q, y) := if ptrTy a then (a, b) else (b, a)
        (origin defs params ptrTy dlog consts (fuel - 1) q).shift (konst y) y
      else
        let y := if v == a then b else a
        (origin defs params ptrTy dlog consts (fuel - 1) d).shift ((konst y).map (- ·)) y
    | .hint (.alloc _ n) => { mk "HeapBuf" with size := some n }
    | .hint (.allocDyn _ _) => mk "HeapBuf (dynamic size)"
    | .frameAddr _ run => { mk "frameAddr" with size := some run.length }
    | .load d _ _ => if d == v then mk "loaded" else mk "load base first"
    | .const _ c => match dlog c with
      | some k => { mk "constant" with off := some k }
      | none => mk "constant (not a power of g)"
    | .hint h => mk s!"hint ({hintKind h})"
    | a => mk s!"{showA a}"

/-- A load's shape: its class and a description. -/
def shapeOf (o : Origin) (off : Nat) : String :=
  let total := o.off.map (· + (off : Int))
  match o.root, total, o.size with
  | "constant", some t, _ => if t < 2 then "constant address in the public input (< 2)" else "constant address (>= 2)"
  | r, some t, some n =>
      if 0 ≤ t ∧ t < n then s!"{r}, static offset inside" else s!"{r}, static offset OUTSIDE its size"
  | r, some _, none => s!"{r}, static offset"
  | r, none, _ => s!"{r}, runtime offset"

/-- A load's record: its shape, the load, its root (function and value), its static offset from
the root, the type of its word, and whether its word's value is mentioned before it (or is a
parameter), so that the load checks or stores rather than defines it. -/
structure LoadRec where
  shape : String
  ex : String
  root : String
  off : Option Int
  wordTy : Ty
  fixed : Bool

/-- Per function: each load's record. -/
def loadShapes (dlog : E → Option Nat) (tyAt : Nat → V → Ty) (fi : Nat) (f : Fn) :
    Array LoadRec := Id.run do
  let ptrTy (v : V) : Bool := tyAt fi v == .ptr || tyAt fi v == .top
  let evs := events f.body
  let mut defs : Std.HashMap V (Sum Atom Stmt) := {}
  let mut consts : Std.HashMap V E := {}
  let mut checked : Std.HashSet V := {}
  let mut out := #[]
  let mut seen : Std.HashSet V := {}
  for e in evs do
    if let .inl (.load d p off) := e then
      let o := origin defs f.params ptrTy dlog consts 4096 p
      let sh := shapeOf o off
      let sh := match o.rt with
        | some y => sh ++ (if checked.contains y then " (factor range-checked here)" else "")
        | none => sh
      let ex := s!"{f.name}: {showA (.load d p off)}"
      let root := s!"{f.name}:{o.root}:{o.src}"
      let offT : Option Int := o.off.map (· + (off : Int))
      let rec_ : LoadRec := ⟨sh, ex, root, offT, tyAt fi d, seen.contains d || f.params.contains d⟩
      out := out.push rec_
    let vs := match e with
      | .inl a => atomVals a
      | .inr s => stmtDefs s
    for v in vs do
      unless defs.contains v || f.params.contains v do defs := defs.insert v e
      seen := seen.insert v
    match e with
    | .inl (.const d c) => consts := consts.insert d c
    | .inl (.rangeCheck x _ _ _ k) => checked := (checked.insert x).insert k
    | _ => pure ()
  return out

/-- The atoms of a function that relate two pointers already made (mentioned before, or
parameters): a product whose pointer is made before it (an equation of two pointers, or the
quotient of two pointers as a data value) and a copy between two pointers. Each holds after
re-placing the pointers only if both point into one region. -/
def ptrEqs (tyAt : Nat → V → Ty) (fi : Nat) (f : Fn) : Array String := Id.run do
  let ptrTy (v : V) : Bool := tyAt fi v == .ptr || tyAt fi v == .top
  let mut seen : Std.HashSet V := f.params.foldl (·.insert ·) {}
  let mut out := #[]
  for e in events f.body do
    match e with
    | .inl (.mul d a b) =>
      if ptrTy d && seen.contains d then
        let kind := if seen.contains a && seen.contains b then "equation" else "quotient of two pointers"
        out := out.push s!"{f.name}: {showA (.mul d a b)} ({kind})"
    | .inl (.copy d x) =>
      if ptrTy d && seen.contains d && seen.contains x then
        out := out.push s!"{f.name}: {showA (.copy d x)}"
    | _ => pure ()
    let vs := match e with
      | .inl a => atomVals a
      | .inr s => stmtDefs s
    for v in vs do seen := seen.insert v
  return out

end PtrCheck

open PtrCheck

/-! ## Self test -/

def vv (k : Nat) : V := ⟨[], 1, k⟩

def mkFn (name : String) (params : List V) (body : List Stmt) : Fn := { name, params, body }

/-- Programs the check must refuse (`false`) or accept (`true`). -/
def selftests : List (String × Bool × List Fn) :=
  let p0 := V.param 0
  let a := fun x => Stmt.atom x
  [("phase 2: a HeapBuf pointer compared to a constant", false,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)), a (.const (vv 2) 0), a (.assertEq (vv 1) (vv 2)), .ret []]]),
   ("phase 2: a frameAddr pointer compared to a constant", false,
      [mkFn "main" [] [a (.const (vv 3) 5), a (.frameAddr (vv 1) [vv 3]), a (.const (vv 2) 0),
        a (.assertEq (vv 1) (vv 2)), .ret []]]),
   ("a pointer added", false,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)), a (.const (vv 2) 1), a (.add (vv 3) (vv 1) (vv 2)), .ret []]]),
   ("a pointer times a pointer", false,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)), a (.hint (.alloc (vv 2) 1)), a (.mul (vv 3) (vv 1) (vv 2)), .ret []]]),
   ("a pointer hashed", false,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)),
        a (.keccak ((List.range 13).map fun _ => vv 1) [vv 2] false false), .ret []]]),
   ("a pointer range-checked", false,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)), a (.rangeCheck (vv 1) (vv 2) (vv 3) (vv 4) (vv 5)), .ret []]]),
   ("a branch on a pointer", false,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)), .ite (vv 1) [] [], .ret []]]),
   ("a pointer passed where the callee adds", false,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)), .call "f" [vv 1] [], .ret []],
       mkFn "f" [p0] [a (.add (vv 2) p0 p0), .ret []]]),
   ("a pointer returned and compared", false,
      [mkFn "main" [] [.call "f" [] [vv 1], a (.const (vv 2) 0), a (.assertEq (vv 1) (vv 2)), .ret []],
       mkFn "f" [] [a (.hint (.alloc (vv 1) 2)), .ret [vv 1]]]),
   ("a pointer stored: product with data, load through it, passed and returned", true,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 4)), a (.const (vv 2) (gpowE 2)), a (.mul (vv 3) (vv 1) (vv 2)),
        a (.load (vv 4) (vv 3) 1), .call "f" [vv 3] [vv 5], a (.load (vv 6) (vv 5) 0),
        a (.add (vv 7) (vv 4) (vv 6)), .ret []],
       mkFn "f" [p0] [a (.const (vv 1) (gpowE 1)), a (.mul (vv 2) (vv 1) p0), a (.load (vv 3) (vv 2) 0),
        .ret [vv 2]]]),
   ("accepted, yet no placed run: two HeapBuf pointers stored into one word", true,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)), a (.hint (.alloc (vv 2) 1)), a (.hint (.alloc (vv 3) 1)),
        a (.load (vv 1) (vv 3) 0), a (.load (vv 2) (vv 3) 0), .ret []]]),
   ("accepted, yet loads anywhere: a pointer times a prover's gap, only touched", true,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 1)), a (.hint (.witness "gap" (.stack [vv 2]))),
        a (.touch (vv 3) (vv 2)), a (.mul (vv 4) (vv 1) (vv 2)), a (.load (vv 5) (vv 4) 0), .ret []]]),
   ("a runtime index: pointer times a computed power, divided back", true,
      [mkFn "main" [] [a (.hint (.alloc (vv 1) 4)), a (.hint (.witness "w" (.stack [vv 2]))),
        a (.rangeCheck (vv 2) (vv 8) (vv 9) (vv 10) (vv 11)),
        a (.mul (vv 3) (vv 1) (vv 2)), a (.load (vv 4) (vv 3) 0), a (.mul (vv 3) (vv 5) (vv 2)),
        a (.load (vv 6) (vv 5) 0), a (.frameAddr (vv 7) [vv 4, vv 6]), a (.load (vv 4) (vv 7) 0), .ret []]])]

def runSelftest : IO UInt32 := do
  let mut fails := 0
  for (what, want, P) in selftests do
    let (cfl, bad, _) := conflicts P.toArray
    let ok := cfl.isEmpty && bad.isEmpty
    let reason := match cfl[0]? with
      | some (p, d) => s!"pointer by [{p}], data by [{d}]"
      | none => if bad.isEmpty then "" else bad[0]!
    IO.println s!"{if ok == want then "ok  " else "FAIL"} {what}: {if ok then "accepted" else "rejected"} {reason}"
    if ok != want then fails := fails + 1
  IO.println s!"selftest: {selftests.length - fails} of {selftests.length} as expected"
  return if fails == 0 then 0 else 1

/-! ## The guest -/

def countBy (xs : Array String) : List (String × Nat) :=
  let m := xs.foldl (fun (m : Std.HashMap String Nat) x => m.insert x (m.getD x 0 + 1)) {}
  (m.toList.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))).toList

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← runSelftest
  let detail := args.contains "--detail"
  let lim := if detail then 100000 else 12
  let P ← input
  let F := (P.map (·.core)).toArray
  if let some name := (args.dropWhile (· != "--fn")).drop 1 |>.head? then
    for f in F do
      if f.name == name then IO.println (Interp.showFn f)
    return 0
  IO.println s!"core functions: {F.size}"
  let (cfl, bad, s) := conflicts F
  IO.println s!"structural problems: {bad.size}"
  for b in bad.toList.take lim do IO.println s!"  {b}"
  IO.println s!"pointer discipline: {cfl.size} conflicting classes"
  for (p, d) in cfl.toList.take (if detail then 100000 else 40) do
    IO.println s!"  pointer by [{p}]"
    IO.println s!"     data by [{d}]"
  let fnsOf (w : String) := (w.splitOn ":").head!
  let rej := (cfl.toList.flatMap fun (p, d) => [fnsOf p, fnsOf d]).eraseDups
  IO.println s!"functions named in a conflict: {rej.length}"
  -- Types after solving.
  let tyAt (fi : Nat) (v : V) : Ty :=
    match s.ids[Node.val fi v]? with
    | none => .bot
    | some i =>
      let rec go : Nat → Nat → Nat
        | i, 0 => i
        | i, n + 1 => let p := s.parent[i]!; if p == i then i else go p n
      s.ty[go i 100000]!
  let ptrTy (fi : Nat) (v : V) : Bool := tyAt fi v == .ptr || tyAt fi v == .top
  let tables := Interp.DlogTables.build
  let dlog (c : E) : Option Nat :=
    if (limbsOf c).2 == 0 then Interp.dlogWith tables (c.limb 0) else none
  let mut recs : Array LoadRec := #[]
  let mut nRc := 0
  let mut nTouch := 0
  let mut constPtrs := #[]
  for h : fi in [0:F.size] do
    let f := F[fi]
    for e in PtrCheck.events f.body do
      match e with
      | .inl (.rangeCheck ..) => nRc := nRc + 1
      | .inl (.touch ..) => nTouch := nTouch + 1
      | .inl (.const d c) =>
        if ptrTy fi d then constPtrs := constPtrs.push s!"{f.name}: {showA (.const d c)}"
      | _ => pure ()
    recs := recs ++ loadShapes dlog tyAt fi f
  let eqs := (List.range F.size).foldl (fun acc fi => acc ++ ptrEqs tyAt fi F[fi]!) #[]
  IO.println s!"products or copies relating two pointers already made: {eqs.size}"
  for (k, n) in countBy (eqs.map fun w => (w.splitOn ":").head!.splitOn "__L" |>.head!) do
    IO.println s!"  {n}  {k}"
  for w in eqs.toList.take lim do IO.println s!"  e.g. {w}"
  IO.println s!"constants typed as pointers (absolute addresses): {constPtrs.size}"
  for w in constPtrs.toList.take lim do IO.println s!"  {w}"
  let isP (t : Ty) := t == .ptr || t == .top
  let pw := recs.filter (isP ·.wordTy)
  let nD := (recs.filter (·.wordTy == .data)).size
  IO.println s!"loads: {recs.size}; the word a pointer: {pw.size} ({(pw.filter (·.fixed)).size} with the word's value mentioned before the load), data: {nD}, unconstrained: {recs.size - pw.size - nD}"
  for (k, n) in countBy (pw.map (·.shape)) do
    IO.println s!"  {n}  {k}"
    for r in (pw.filter (·.shape == k)).toList.take 2 do
      IO.println s!"       e.g. {r.ex}{if r.fixed then " (value mentioned before)" else ""}"
  -- Word types per root: a static offset accessed both ways, or a runtime offset mixed.
  let mut byRoot : Std.HashMap String (Array LoadRec) := {}
  for r in recs do
    byRoot := byRoot.insert r.root ((byRoot.getD r.root #[]).push r)
  let mut mixed := #[]
  for (root, rs) in byRoot.toList do
    let typed := rs.filter (·.wordTy != .bot)
    let clash := typed.any fun a => typed.any fun b =>
      isP a.wordTy != isP b.wordTy && (a.off == b.off || a.off.isNone || b.off.isNone)
    if clash then mixed := mixed.push (root, typed)
  IO.println s!"roots whose words are read both as pointers and as data at one offset (or a runtime one): {mixed.size} of {byRoot.size}"
  for (root, rs) in mixed.toList.take lim do
    IO.println s!"  {root}: {(rs.filter (isP ·.wordTy)).size} pointer, {(rs.filter (! isP ·.wordTy)).size} data"
    for r in rs.toList.take 3 do IO.println s!"       e.g. {r.ex} : {if isP r.wordTy then "pointer" else "data"}"
  IO.println s!"range checks: {nRc}; touches: {nTouch} (addresses through data values, not loads)"
  IO.println "load shapes:"
  for (k, n) in countBy (recs.map (·.shape)) do
    IO.println s!"  {n}  {k}"
    for r in (recs.filter (·.shape == k)).toList.take (if detail then lim else 3) do
      IO.println s!"       e.g. {r.ex}"
  let nPtrParams := (List.range F.size).foldl (fun n fi => n + (F[fi]!.params.filter (ptrTy fi)).length) 0
  IO.println s!"pointer parameters: {nPtrParams}"
  return if cfl.isEmpty && bad.isEmpty then 0 else 1
