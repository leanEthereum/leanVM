import Whir.WHIRCallerSource

/-! Source-operation accounting, not CPU timing. One unit is a constructor,
branch, fixed-width field operation, or Nat arithmetic operation. List scans
pay one per visited cell plus their terminal test; allocating a list pays one
per cell. Array lookup pays its bounds test and lookup. Powers and logarithms
use the explicit multiplication/division recurrences below, rather than an
opaque primitive-work hypothesis. Field operations are fixed-width source
operations, not machine instructions. The administrative machinery of the
cost monad (including `pure`, `bind`, and the instrumentation itself) is not a
source operation; source constructors and branches are charged by `tick`.
Delayed ring-value functions have separate per-access charges: constructing
a closure does not execute its body. Failure retains the visited-prefix work.
Literal local charges account for fixed source expressions, not a reservation
for an entire parser. List-size charges are traversals, not unit-cost calls. -/
namespace Whir.PCSBCSCallerParserCost
open Concrete WHIRCallerClaims

structure Run (A : Type) where
  result : Option (A × List CallerToken)
  work : Nat

abbrev Parser (A : Type) := List CallerToken → Run A

 def pure {A : Type} (a : A) : Parser A := fun ts => ⟨some (a,ts),0⟩
 def bind {A B : Type} (p : Parser A) (f : A → Parser B) : Parser B := fun ts =>
  let r := p ts
  match r.result with
  | none => ⟨none,r.work⟩
  | some (a,rest) => let s := f a rest; ⟨s.result,r.work+s.work⟩
instance : Monad Parser where
  pure := pure
  bind := bind

instance : LawfulMonad Parser := by
  refine LawfulMonad.mk' Parser ?_ ?_ ?_
  · intro A p
    funext ts
    change bind p (fun a => pure (id a)) ts = p ts
    simp only [bind]
    cases h : p ts with
    | mk result work => cases result with
      | none => rfl
      | some v => cases v; simp [pure]
  · intro A B a f
    funext ts
    change bind (pure a) f ts = f a ts
    simp [bind,pure]
  · intro A B C p f g
    funext ts
    change bind (bind p f) g ts = bind p (fun a => bind (f a) g) ts
    simp only [bind]
    cases hr : (p ts).result with
    | none => rfl
    | some v =>
      rcases v with ⟨a,rest⟩
      cases hs : (f a rest).result with
      | none => simp [hs]
      | some w => rcases w with ⟨b,tail⟩; simp [hs,Nat.add_assoc]

 def erase {A : Type} (p : Parser A) : CallerParser A := fun ts => (p ts).result
@[simp] theorem erase_pure {A : Type} (a : A) : erase (Pure.pure a : Parser A) = Pure.pure a := rfl
@[simp] theorem pure_erasure {A : Type} (a : A) : erase (pure a) = Pure.pure a := rfl
@[simp] theorem erase_bind {A B : Type} (p : Parser A) (f : A → Parser B) :
    erase (p >>= f) = erase p >>= fun a => erase (f a) := by
  funext ts
  change (match (p ts).result with
    | none => (⟨none,(p ts).work⟩ : Run B)
    | some (a,rest) => ⟨(f a rest).result,(p ts).work+(f a rest).work⟩).result =
      (p ts).result.bind (fun (a,rest) => (f a rest).result)
  cases (p ts).result with
  | none => rfl
  | some v => cases v; rfl

@[simp] theorem erase_map {A B : Type} (f : A → B) (p : Parser A) :
    erase (f <$> p) = f <$> erase p := by
  simp only [← bind_pure_comp,erase_bind,erase_pure]
@[simp] theorem erase_ite {A : Type} (q : Prop) [Decidable q] (p r : Parser A) :
    erase (if q then p else r) = if q then erase p else erase r := by
  split <;> rfl
@[simp] theorem erase_option_match {A B : Type} (x : Option A) (p : Parser B)
    (f : A → Parser B) :
    erase (match x with | none => p | some a => f a) =
      match x with | none => erase p | some a => erase (f a) := by cases x <;> rfl
@[simp] theorem erase_prod_match {A B C : Type} (x : A × B) (f : A → B → Parser C) :
    erase (match x with | (a,b) => f a b) =
      match x with | (a,b) => erase (f a b) := by cases x; rfl
@[simp] theorem erase_pairOption_match {A B C : Type} (x : Option (A × B))
    (p : Parser C) (f : A → B → Parser C) :
    erase (match x with | some (a,b) => f a b | none => p) =
      match x with | some (a,b) => erase (f a b) | none => erase p := by
  cases x with
  | none => rfl
  | some v => cases v; rfl
@[simp] theorem erase_list_match {A B : Type} (xs : List A) (p : Parser B)
    (f : A → List A → Parser B) :
    erase (match xs with | [] => p | a::as => f a as) =
      match xs with | [] => erase p | a::as => erase (f a as) := by cases xs <;> rfl
@[simp] theorem erase_coord_match {A : Type} (c : BusCoord) (col : Nat → Parser A)
    (pub table : Parser A) :
    erase (match c with | .column n => col n | .publicValue => pub | .tableExpression => table) =
      match c with | .column n => erase (col n) | .publicValue => erase pub |
        .tableExpression => erase table := by cases c <;> rfl

@[simp] theorem erase_mapM {A B : Type} (xs : List A) (f : A → Parser B) :
    erase (xs.mapM f) = xs.mapM (fun a => erase (f a)) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.mapM_cons,ih]

@[simp] theorem erase_forIn {A B : Type} (xs : List A) (initial : B)
    (body : A → B → Parser (ForInStep B)) :
    erase (forIn xs initial body) = forIn xs initial (fun a b => erase (body a b)) := by
  induction xs generalizing initial with
  | nil => simp [List.forIn_nil]
  | cons x xs ih =>
    simp only [List.forIn_cons,erase_bind]
    congr 1
    funext step
    cases step <;> simp [ih]

 def tick (n : Nat) : Parser Unit := fun ts => ⟨some ((),ts),n⟩
@[simp] theorem tick_erasure (n : Nat) : erase (tick n) = Pure.pure () := rfl
 def liftOption {A : Type} (n : Nat) (x : Option A) : Parser A := fun ts =>
  ⟨x.map (fun a => (a,ts)),n⟩
@[simp] theorem liftOption_erasure {A : Type} (n : Nat) (x : Option A) :
    erase (liftOption n x) =
      match x with | some a => Pure.pure a | none => fun _ => none := by cases x <;> rfl

structure Costed (A : Type) where
  value : A
  work : Nat

 def readScalar : Parser E
  | .sent x :: rest => ⟨some (x,rest),4⟩
  | _ => ⟨none,3⟩
 def drawScalar : Parser E
  | .draw x :: rest => ⟨some (x,rest),4⟩
  | _ => ⟨none,3⟩
 def check (ok : Bool) : Parser Unit := fun ts =>
  if ok then ⟨some ((),ts),3⟩ else ⟨none,2⟩
 def nonce (bits : Nat) : Parser Unit
  | .nonce actual _ :: rest =>
    if actual = bits then ⟨some ((),rest),5⟩ else ⟨none,4⟩
  | _ => ⟨none,3⟩
 def readScalars : Nat → Parser (List E)
  | 0 => do tick 2; return []
  | n+1 => do
    tick 3
    let x ← readScalar
    let xs ← readScalars n
    tick 2
    return x :: xs
 def drawScalars : Nat → Parser (List E)
  | 0 => do tick 2; return []
  | n+1 => do
    tick 3
    let x ← drawScalar
    let xs ← drawScalars n
    tick 2
    return x :: xs

@[simp] theorem readScalar_erasure : erase readScalar = WHIRCallerClaims.readScalar := by
  funext ts; cases ts with
  | nil => rfl
  | cons t ts => cases t <;> rfl
@[simp] theorem drawScalar_erasure : erase drawScalar = WHIRCallerClaims.drawScalar := by
  funext ts; cases ts with
  | nil => rfl
  | cons t ts => cases t <;> rfl
@[simp] theorem check_erasure (ok : Bool) : erase (check ok) = WHIRCallerClaims.check ok := by
  cases ok <;> rfl
@[simp] theorem nonce_erasure (n : Nat) : erase (nonce n) = WHIRCallerClaims.nonce n := by
  funext ts; cases ts with
  | nil => rfl
  | cons t ts => cases t <;> simp [erase,nonce,WHIRCallerClaims.nonce]; split <;> rfl
@[simp] theorem readScalars_erasure (n : Nat) : erase (readScalars n) = WHIRCallerClaims.readScalars n := by
  induction n with
  | zero => simp [readScalars,WHIRCallerClaims.readScalars]
  | succ n ih => simp [readScalars,WHIRCallerClaims.readScalars,ih]
@[simp] theorem drawScalars_erasure (n : Nat) : erase (drawScalars n) = WHIRCallerClaims.drawScalars n := by
  induction n with
  | zero => simp [drawScalars,WHIRCallerClaims.drawScalars]
  | succ n ih => simp [drawScalars,WHIRCallerClaims.drawScalars,ih]

 theorem readScalar_work_le (ts : List CallerToken) : (readScalar ts).work ≤ 4 := by
  cases ts with
  | nil => decide
  | cons t ts => cases t <;> simp [readScalar]
 theorem drawScalar_work_le (ts : List CallerToken) : (drawScalar ts).work ≤ 4 := by
  cases ts with
  | nil => decide
  | cons t ts => cases t <;> simp [drawScalar]
theorem check_work_le (ok : Bool) (ts : List CallerToken) : (check ok ts).work ≤ 3 := by
  cases ok <;> simp [check]
theorem nonce_work_le (bits : Nat) (ts : List CallerToken) : (nonce bits ts).work ≤ 5 := by
  cases ts with
  | nil => simp [nonce]
  | cons t ts =>
    cases t with
    | sent x => simp [nonce]
    | draw x => simp [nonce]
    | nonce actual value => simp only [nonce]; split <;> simp
 theorem readScalars_work_le (n : Nat) (ts : List CallerToken) :
    (readScalars n ts).work ≤ 9*n+2 := by
  induction n generalizing ts with
  | zero => change 2 ≤ 2; omega
  | succ n ih =>
    cases ts with
    | nil => change 6 ≤ 9*(n+1)+2; omega
    | cons t ts =>
      cases t <;> dsimp only [readScalars,Bind.bind,Pure.pure,bind,tick,pure,readScalar]
      · have h := ih ts
        cases (readScalars n ts).result <;> simp only [] <;> omega
      · omega
      · omega
 theorem drawScalars_work_le (n : Nat) (ts : List CallerToken) :
    (drawScalars n ts).work ≤ 9*n+2 := by
  induction n generalizing ts with
  | zero => change 2 ≤ 2; omega
  | succ n ih =>
    cases ts with
    | nil => change 6 ≤ 9*(n+1)+2; omega
    | cons t ts =>
      cases t <;> dsimp only [drawScalars,Bind.bind,Pure.pure,bind,tick,pure,drawScalar]
      · omega
      · have h := ih ts
        cases (drawScalars n ts).result <;> simp only [] <;> omega
      · omega

theorem readScalars_success (n : Nat) (ts : List CallerToken) (xs : List E)
    (rest : List CallerToken) (h : (readScalars n ts).result = some (xs,rest)) :
    xs.length = n ∧ rest.length+n = ts.length := by
  induction n generalizing ts xs rest with
  | zero =>
    simp [readScalars,Bind.bind,Pure.pure,bind,tick,pure] at h
    rcases h with ⟨rfl,rfl⟩
    simp
  | succ n ih =>
    cases ts with
    | nil => change none = some (xs,rest) at h; cases h
    | cons t ts =>
      cases t <;> dsimp only [readScalars,Bind.bind,Pure.pure,bind,tick,pure,readScalar] at h
      · cases hr : (readScalars n ts).result with
        | none => simp [hr] at h
        | some v =>
          rcases v with ⟨ys,tail⟩
          simp only [hr] at h
          have ht := ih ts ys tail hr
          cases h
          simp only [List.length_cons]
          omega
      · simp at h
      · simp at h

theorem drawScalars_success (n : Nat) (ts : List CallerToken) (xs : List E)
    (rest : List CallerToken) (h : (drawScalars n ts).result = some (xs,rest)) :
    xs.length = n ∧ rest.length+n = ts.length := by
  induction n generalizing ts xs rest with
  | zero =>
    simp [drawScalars,Bind.bind,Pure.pure,bind,tick,pure] at h
    rcases h with ⟨rfl,rfl⟩
    simp
  | succ n ih =>
    cases ts with
    | nil => change none = some (xs,rest) at h; cases h
    | cons t ts =>
      cases t <;> dsimp only [drawScalars,Bind.bind,Pure.pure,bind,tick,pure,drawScalar] at h
      · simp at h
      · cases hr : (drawScalars n ts).result with
        | none => simp [hr] at h
        | some v =>
          rcases v with ⟨ys,tail⟩
          simp only [hr] at h
          have ht := ih ts ys tail hr
          cases h
          simp only [List.length_cons]
          omega
      · simp at h
theorem readScalars_success_length (n : Nat) (ts : List CallerToken) (xs : List E)
    (rest : List CallerToken) (h : (readScalars n ts).result = some (xs,rest)) :
    xs.length = n := (readScalars_success n ts xs rest h).1
theorem drawScalars_success_length (n : Nat) (ts : List CallerToken) (xs : List E)
    (rest : List CallerToken) (h : (drawScalars n ts).result = some (xs,rest)) :
    xs.length = n := (drawScalars_success n ts xs rest h).1

theorem bind_work_le {A B : Type} (p : Parser A) (f : A → Parser B)
    (ts : List CallerToken) (m n : Nat) (hp : (p ts).work ≤ m)
    (hf : ∀ a rest, (p ts).result = some (a,rest) → (f a rest).work ≤ n) :
    ((p >>= f) ts).work ≤ m+n := by
  change (bind p f ts).work ≤ m+n
  simp only [bind]
  cases h : (p ts).result with
  | none => simp; omega
  | some v => rcases v with ⟨a,rest⟩; have ht := hf a rest h; simp; omega


/-- A list length inspects the terminal constructor as well as all cells. -/
def lengthCost {A : Type} (xs : List A) : Nat := xs.length+1
def appendCost {A : Type} (xs : List A) : Nat := 2*xs.length+1
def takeCost {A : Type} (n : Nat) (xs : List A) : Nat := 2*min n xs.length+1
def dropCost {A : Type} (n : Nat) (xs : List A) : Nat := min n xs.length+1
def indexCost {A : Type} (n : Nat) (xs : List A) : Nat := min (n+1) xs.length+1
def allCost {A : Type} (p : A → Bool) (cost : A → Nat) : List A → Nat
  | [] => 1
  | x :: xs => cost x + 1 + if p x then allCost p cost xs else 0
def memberCost {A : Type} [DecidableEq A] (x : A) (comparison : Nat) : List A → Nat
  | [] => 1
  | y :: ys => comparison+1 + if x = y then 0 else memberCost x comparison ys
def eraseDupsCost {A : Type} [DecidableEq A] (comparison : Nat) :
    List A → List A → Nat
  | [], seen => 2*seen.length+2
  | x :: xs, seen => memberCost x comparison seen + 2 +
      if x ∈ seen then eraseDupsCost comparison xs seen
      else 1 + eraseDupsCost comparison xs (x :: seen)

theorem allCost_le {A : Type} (p : A → Bool) (cost : A → Nat)
    (xs : List A) (k : Nat) (h : ∀ x ∈ xs, cost x ≤ k) :
    allCost p cost xs ≤ (k+1)*xs.length+1 := by
  induction xs with
  | nil => simp [allCost]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [allCost,List.length_cons]
    split <;> nlinarith

theorem memberCost_le {A : Type} [DecidableEq A] (x : A) (k : Nat) (xs : List A) :
    memberCost x k xs ≤ (k+1)*xs.length+1 := by
  induction xs with
  | nil => simp [memberCost]
  | cons y ys ih =>
    simp only [memberCost,List.length_cons]
    split <;> nlinarith

theorem eraseDupsCost_le {A : Type} [DecidableEq A] (k : Nat) (xs seen : List A) :
    eraseDupsCost k xs seen ≤
      (k+1)*xs.length*(xs.length+seen.length)+4*xs.length+2*(xs.length+seen.length)+2 := by
  induction xs generalizing seen with
  | nil => simp [eraseDupsCost]
  | cons x xs ih =>
    have hc := memberCost_le x k seen
    simp only [eraseDupsCost,List.length_cons]
    split
    · have ht := ih seen; nlinarith
    · have ht := ih (x::seen); simp only [List.length_cons] at ht; nlinarith

theorem sum_map_le {A : Type} (xs : List A) (f : A → Nat) (n : Nat)
    (h : ∀ x ∈ xs, f x ≤ n) : (xs.map f).sum ≤ xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Repeated multiplication: no opaque exponentiation work assumption. -/
def pow2 : Nat → Costed Nat
  | 0 => ⟨1,2⟩
  | n+1 => let r := pow2 n; ⟨r.value*2,r.work+3⟩
@[simp] theorem pow2_erasure (n : Nat) : (pow2 n).value = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pow2,ih,Nat.pow_succ]
theorem pow2_work (n : Nat) : (pow2 n).work = 3*n+2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow2,ih]; omega

/-- The source's `Nat.log2_def` division recurrence, with reached branches. -/
def log2 (n : Nat) : Costed Nat :=
  if h : 2 ≤ n then
    let r := log2 (n/2)
    ⟨r.value+1,r.work+4⟩
  else ⟨0,2⟩
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)
@[simp] theorem log2_erasure (n : Nat) : (log2 n).value = Nat.log2 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [log2,Nat.log2_def]
    split
    · next hn => simp only []; rw [ih (n/2) (Nat.div_lt_self (by omega) (by decide))]
    · rfl
theorem log2_work_le (n : Nat) : (log2 n).work ≤ 4*n+2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [log2]
    split
    · next hn =>
        have hd : n/2 < n := Nat.div_lt_self (by omega) (by decide)
        have ht := ih (n/2) hd
        simp only []
        omega
    · simp only []; omega
theorem log2_work (n : Nat) : (log2 n).work = 4*Nat.log2 n+2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [log2,Nat.log2_def]
    split
    · next hn =>
        have hd : n/2 < n := Nat.div_lt_self (by omega) (by decide)
        have ht := ih (n/2) hd
        simp only []
        omega
    · rfl

def mu (l : BusLayout) : Costed Nat :=
  let push := (l.push.map (fun b => (pow2 b.kappa).value)).sum +
    (l.producers.map (fun p => p.bits * (pow2 p.kappa).value)).sum
  let pull := (l.pull.map (fun b => (pow2 b.kappa).value)).sum
  let logarithm := log2 (max (max push pull) 1 - 1)
  ⟨logarithm.value + if max push pull ≤ 1 then 0 else 1,
    (l.push.map (fun b => (pow2 b.kappa).work+4)).sum +
    (l.producers.map (fun p => (pow2 p.kappa).work+5)).sum +
    (l.pull.map (fun b => (pow2 b.kappa).work+4)).sum +
    logarithm.work+15⟩
@[simp] theorem mu_erasure (l : BusLayout) : (mu l).value = l.mu := by
  simp only [mu,BusLayout.mu,pow2_erasure,log2_erasure]

theorem mu_work_le (l : BusLayout) :
    (mu l).work ≤
      (l.push.map (fun b => 3*b.kappa+6)).sum +
      (l.producers.map (fun p => 3*p.kappa+7)).sum +
      (l.pull.map (fun b => 3*b.kappa+6)).sum +4*l.mu+17 := by
  simp only [mu,BusLayout.mu,pow2_work,pow2_erasure,log2_work,Nat.add_assoc,Nat.reduceAdd]
  omega

def fieldOf (column : Nat) : List BitField → Nat → Costed (Option (BitField × Nat))
  | [], _ => ⟨none,2⟩
  | f :: fs, offset =>
    if f.column = column then ⟨some (f,offset),5⟩
    else let r := fieldOf column fs (offset+f.width); ⟨r.value,4+r.work⟩
@[simp] theorem fieldOf_erasure (column : Nat) (fs : List BitField) (offset : Nat) :
    (fieldOf column fs offset).value = WHIRCallerClaims.fieldOf column fs offset := by
  induction fs generalizing offset with
  | nil => rfl
  | cons f fs ih => simp only [fieldOf,WHIRCallerClaims.fieldOf]; split <;> simp [ih]
theorem fieldOf_work_le (column : Nat) (fs : List BitField) (offset : Nat) :
    (fieldOf column fs offset).work ≤ 5*fs.length+2 := by
  induction fs generalizing offset with
  | nil => simp [fieldOf]
  | cons f fs ih =>
    simp only [fieldOf,List.length_cons]
    split
    · simp; omega
    · have h := ih (offset+f.width); simp; omega

def combineBits (bits : List E) : Costed E :=
  ⟨(bits.zipIdx.map (fun (x,b) => x * E.ofK (UInt64.ofNat (pow2 b).value))).foldl (· + ·) 0,
    (bits.zipIdx.map (fun (_,b) => (pow2 b).work+12)).sum+3⟩
@[simp] theorem combineBits_erasure (bits : List E) :
    (combineBits bits).value = WHIRCallerClaims.combineBits bits := by
  simp only [combineBits,WHIRCallerClaims.combineBits,pow2_erasure]
theorem combineBits_work_le (bits : List E) :
    (combineBits bits).work ≤ bits.length*(3*bits.length+14)+3 := by
  have h := sum_map_le bits.zipIdx (fun p => (pow2 p.2).work+12) (3*bits.length+14) (by
    intro p hp
    have hat := List.mem_zipIdx_iff_getElem?.mp hp
    have hi := (List.getElem?_eq_some_iff.mp hat).1
    rw [pow2_work]
    omega)
  simpa [combineBits] using Nat.add_le_add_right h 3

def placeClaim (p : Placement) (c : ColumnClaim) : Costed (Option RingPCSGame.PointClaim) :=
  match p with
  | .committed offset _ => ⟨some (.point offset c.point.toArray c.value),2*c.point.length+4⟩
  | .port offset slot stride =>
    ⟨some (.strided offset slot stride c.point.toArray c.value),2*c.point.length+4⟩
  | .sliced => ⟨none,2⟩
@[simp] theorem placeClaim_erasure (p : Placement) (c : ColumnClaim) :
    (placeClaim p c).value = WHIRCallerClaims.placeClaim p c := by cases p <;> rfl
theorem placeClaim_work_le (p : Placement) (c : ColumnClaim) :
    (placeClaim p c).work ≤ 2*c.point.length+4 := by cases p <;> simp [placeClaim]

def placeClaimsLoop (placements : Array Placement) :
    List ColumnClaim → Costed (Option (List (Option RingPCSGame.PointClaim)))
  | [] => ⟨some [],2⟩
  | c :: cs =>
    match placements[c.column]? with
    | none => ⟨none,4⟩
    | some p =>
      let located := placeClaim p c
      let later := placeClaimsLoop placements cs
      ⟨later.value.map (located.value :: ·),located.work+later.work+6⟩

def filterMapCost {A : Type} : List (Option A) → Nat
  | [] => 1
  | none :: xs => filterMapCost xs+2
  | some _ :: xs => filterMapCost xs+3
theorem filterMapCost_le {A : Type} (xs : List (Option A)) :
    filterMapCost xs ≤ 3*xs.length+1 := by
  induction xs with
  | nil => simp [filterMapCost]
  | cons x xs ih => cases x <;> simp only [filterMapCost,List.length_cons] <;> omega

def placeClaims (placements : Array Placement) (claims : List ColumnClaim) :
    Costed (Option (Array RingPCSGame.PointClaim)) :=
  let located := placeClaimsLoop placements claims
  match located.value with
  | none => ⟨none,located.work+1⟩
  | some xs => ⟨some ((xs.filterMap id).toArray),
      located.work+filterMapCost xs+2*(xs.filterMap id).length+3⟩

theorem placeClaimsLoop_erasure (placements : Array Placement) (claims : List ColumnClaim) :
    (placeClaimsLoop placements claims).value =
      claims.mapM (fun c => do
        let p ← placements[c.column]?
        Pure.pure (WHIRCallerClaims.placeClaim p c)) := by
  induction claims with
  | nil => rfl
  | cons c cs ih =>
    simp only [placeClaimsLoop,List.mapM_cons]
    cases placements[c.column]? <;> simp [ih,Option.map_eq_bind]
@[simp] theorem placeClaims_erasure (placements : Array Placement) (claims : List ColumnClaim) :
    (placeClaims placements claims).value = WHIRCallerClaims.placeClaims placements claims := by
  simp only [placeClaims,placeClaimsLoop_erasure,WHIRCallerClaims.placeClaims]
  cases claims.mapM (fun c => do
    let p ← placements[c.column]?
    Pure.pure (WHIRCallerClaims.placeClaim p c)) <;> rfl

def tableColumns (base : Nat) (claims : TableClaims) : Costed (List ColumnClaim) :=
  ⟨claims.evals.zipIdx.map (fun (x,i) => ⟨base+i,claims.point,x⟩),
    6*claims.evals.length+2⟩
@[simp] theorem tableColumns_erasure (base : Nat) (claims : TableClaims) :
    (tableColumns base claims).value = WHIRCallerClaims.tableColumns base claims := rfl

def paddedRing (offset : Nat) (point slices : List E) :
    Costed (Option RingPCSGame.FamilyClaim) :=
  if slices.length ≤ 64 then
    ⟨some ⟨offset,point.toArray,fun i => slices[i.val]?.getD 0⟩,
      lengthCost slices+2*point.length+5⟩
  else ⟨none,lengthCost slices+2⟩
@[simp] theorem paddedRing_erasure (offset : Nat) (point slices : List E) :
    (paddedRing offset point slices).value = WHIRCallerClaims.paddedRing offset point slices := by
  unfold paddedRing WHIRCallerClaims.paddedRing; split <;> rfl
/-- Work of a reached invocation of the ring's delayed slice getter. -/
def paddedRingGetterWork (slices : List E) (i : Fin 64) : Nat := indexCost i.val slices+2
theorem paddedRingGetterWork_le (slices : List E) (i : Fin 64) :
    paddedRingGetterWork slices i ≤ 67 := by
  unfold paddedRingGetterWork indexCost
  have := i.isLt
  omega
theorem paddedRing_work_le (offset : Nat) (point slices : List E) :
    (paddedRing offset point slices).work ≤ slices.length+2*point.length+6 := by
  simp only [paddedRing]
  split <;> simp [lengthCost] <;> omega

theorem tableColumns_work (base : Nat) (claims : TableClaims) :
    (tableColumns base claims).work = 6*claims.evals.length+2 := rfl
theorem tableColumns_length (base : Nat) (claims : TableClaims) :
    (tableColumns base claims).value.length = claims.evals.length := by
  simp [tableColumns]
theorem tableColumns_point (base : Nat) (claims : TableClaims) (c : ColumnClaim)
    (h : c ∈ (tableColumns base claims).value) : c.point = claims.point := by
  simp only [tableColumns,List.mem_map] at h
  obtain ⟨⟨x,i⟩,hx,hc⟩ := h
  cases hc
  rfl

theorem paddedRing_success_point_size (offset : Nat) (point slices : List E)
    (claim : RingPCSGame.FamilyClaim) (h : (paddedRing offset point slices).value = some claim) :
    claim.point.size = point.length := by
  simp only [paddedRing] at h
  split at h
  · cases h; simp
  · simp at h

theorem placeClaimsLoop_work_le (placements : Array Placement)
    (claims : List ColumnClaim) (pointCap : Nat)
    (h : ∀ c ∈ claims, c.point.length ≤ pointCap) :
    (placeClaimsLoop placements claims).work ≤ claims.length*(2*pointCap+10)+2 := by
  induction claims with
  | nil => simp [placeClaimsLoop]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun c hc => h c (by simp [hc]))
    have hp := placeClaim_work_le
    simp only [placeClaimsLoop,List.length_cons]
    split
    · simp only []; nlinarith
    · next p hp' =>
        have hh := hp p c
        simp only []
        nlinarith

theorem placeClaimsLoop_length (placements : Array Placement)
    (claims : List ColumnClaim) (xs : List (Option RingPCSGame.PointClaim))
    (h : (placeClaimsLoop placements claims).value = some xs) :
    xs.length = claims.length := by
  induction claims generalizing xs with
  | nil => simp [placeClaimsLoop] at h; subst xs; rfl
  | cons c cs ih =>
    simp only [placeClaimsLoop] at h
    split at h
    · simp at h
    · next p =>
      cases hr : (placeClaimsLoop placements cs).value with
      | none => simp [hr] at h
      | some ys =>
        simp only [hr,Option.map_some,Option.some.injEq] at h
        subst xs
        simp [ih ys hr]

theorem placeClaims_work_le (placements : Array Placement) (claims : List ColumnClaim)
    (pointCap : Nat) (h : ∀ c ∈ claims, c.point.length ≤ pointCap) :
    (placeClaims placements claims).work ≤ claims.length*(2*pointCap+15)+6 := by
  have hw := placeClaimsLoop_work_le placements claims pointCap h
  simp only [placeClaims]
  split
  · simp only []; nlinarith
  · next xs hs =>
      have hl := placeClaimsLoop_length placements claims xs hs
      have hf := filterMapCost_le xs
      have hk := List.length_filterMap_le (f := id) (l := xs)
      simp only []
      nlinarith

theorem placeClaims_success_size (placements : Array Placement)
    (claims : List ColumnClaim) (points : Array RingPCSGame.PointClaim)
    (h : (placeClaims placements claims).value = some points) :
    points.size ≤ claims.length := by
  simp only [placeClaims] at h
  split at h
  · simp at h
  · next xs hs =>
    have hl := placeClaimsLoop_length placements claims xs hs
    cases h
    simpa only [List.size_toArray,hl] using List.length_filterMap_le id xs


def flockChecksWork (layout : FlockLayout) (zc lc : List E) : Nat :=
  if layout.kLog < 6 then 3 else
  if layout.logN < 13 then 6 else
  if lc.length < layout.kLog-6 then lengthCost lc+8 else
    lengthCost lc+lengthCost zc+11

def assembleFlock (layout : FlockLayout) (zc lc slices : List E) :
    Costed (Option RingPCSGame.FamilyClaim) :=
  let rest := layout.kLog-6
  let checks := flockChecksWork layout zc lc
  if layout.kLog < 6 || layout.logN < 13 || lc.length < rest ||
      zc.length < layout.logN-6 then ⟨none,checks+1⟩
  else
    if h : slices.length = 64 then
      let left := (lc.take rest).reverse
      let right := (zc.drop rest).take layout.instanceLog
      ⟨some ⟨layout.offset,(left++right).toArray,
          fun i => slices[i.val]'(by omega)⟩,
        checks+lengthCost slices+takeCost rest lc+2*left.length+1+
        dropCost rest zc+takeCost layout.instanceLog (zc.drop rest)+
        appendCost left+2*(left.length+right.length)+6⟩
    else ⟨none,checks+lengthCost slices+3⟩
@[simp] theorem assembleFlock_erasure (layout : FlockLayout) (zc lc slices : List E) :
    (assembleFlock layout zc lc slices).value =
      WHIRCallerClaims.assembleFlock layout zc lc slices := by
  dsimp only [assembleFlock,WHIRCallerClaims.assembleFlock]
  split
  · rfl
  · split <;> rfl

theorem assembleFlock_work_le (layout : FlockLayout) (zc lc slices : List E) :
    (assembleFlock layout zc lc slices).work ≤
      9*lc.length+6*zc.length+slices.length+30 := by
  have hc : flockChecksWork layout zc lc ≤ lc.length+zc.length+13 := by
    unfold flockChecksWork
    split
    · omega
    · split
      · omega
      · split <;> simp [lengthCost] <;> omega
  simp only [assembleFlock]
  split
  · simp only []; omega
  · split
    · simp only [lengthCost,takeCost,dropCost,appendCost,List.length_reverse,
        List.length_take,List.length_drop] at ⊢
      omega
    · simp only [lengthCost]
      omega

/-- Work of a reached Flock slice getter, whose successful layout has 64 cells. -/
def assembleFlockGetterWork (i : Fin 64) : Nat := i.val+2
theorem assembleFlockGetterWork_le (i : Fin 64) : assembleFlockGetterWork i ≤ 65 := by
  unfold assembleFlockGetterWork
  have := i.isLt
  omega


/-- One actual nested radix-four sumcheck round. Exposed so the work proof can
track the source-created point length without changing interpretation. -/
def gkrRound (point : List E) : Parser (List E) := do
  tick (lengthCost point+2*point.length+3)
  let rounds ← (List.range point.length).mapM (fun _ => do
    tick 2
    let _ ← readScalars 4
    drawScalar)
  let _ ← readScalars 8
  let low ← drawScalar
  let high ← drawScalar
  let _ ← drawScalar
  tick 3
  pure (low :: high :: rounds)

/-- Actual odd leading sumcheck round, or the empty even seed. -/
def gkrSeed (mu : Nat) : Parser (List E) := do
  if mu % 2 = 1 then
    let _ ← readScalars 4
    let x ← drawScalar
    let _ ← drawScalar
    tick 1
    pure [x]
  else
    pure []

def gkrPoint (mu : Nat) : Parser (List E) := do
  let _ ← readScalar
  let _ ← drawScalar
  tick 4
  let mut point ← gkrSeed mu
  tick (2*(mu/2)+2)
  for _ in List.range (mu / 2) do
    point ← gkrRound point
  tick 1
  pure point

def busClaims (layout : BusLayout) : Parser (List E × List ColumnClaim) := do
  tick 2
  if layout.grinding > 0 then nonce layout.grinding
  let _ ← drawScalars 4
  let _ ← drawScalar
  let m := mu layout
  tick m.work
  let point ← gkrPoint m.value
  let mut known : List (Nat × Nat) := []
  let mut claims := []
  tick (appendCost layout.push+2)
  for block in layout.push ++ layout.pull do
    tick (lengthCost point+4)
    check (block.kappa ≤ point.length)
    if !block.tableOwned then
      for coord in block.coords do
        tick 2
        match coord with
        | .column col =>
          tick (memberCost (col,block.kappa) 2 known+1)
          if (col,block.kappa) ∉ known then
            let value ← readScalar
            tick (appendCost known+appendCost claims+takeCost block.kappa point+5)
            known := known ++ [(col,block.kappa)]
            claims := claims ++ [⟨col,point.take block.kappa,value⟩]
        | .publicValue => pure ()
        | .tableExpression => check false
  tick 3
  pure (point,claims)

def receiveTable (layout : AirLayout) (point : List E) : Parser TableClaims := do
  tick (if layout.publicColumns ≤ layout.columns then lengthCost point+4 else 2)
  check (layout.publicColumns ≤ layout.columns && layout.tau ≤ point.length)
  tick 1
  let n := layout.columns-layout.publicColumns
  tick (allCost (fun f => f.column < n && f.width ≤ 64)
    (fun f => if f.column < n then 3 else 2) layout.fields)
  check (layout.fields.all (fun f => f.column < n && f.width ≤ 64))
  let columns := layout.fields.map BitField.column
  tick (2*layout.fields.length+1+eraseDupsCost 1 columns []+
    lengthCost columns.eraseDups+lengthCost layout.fields+1)
  check (columns.eraseDups.length == layout.fields.length)
  tick (lengthCost layout.fields+1)
  let sent ← readScalars (n-layout.fields.length)
  tick (4*layout.fields.length+2)
  let slices ← readScalars ((layout.fields.map BitField.width).sum)
  let mut cursor := sent
  let mut evals := []
  tick (2*n+3)
  for c in List.range n do
    let found := fieldOf c layout.fields 0
    tick (found.work+2)
    match found.value with
    | some (f,start) =>
      let combined := combineBits ((slices.drop start).take f.width)
      tick (dropCost start slices+takeCost f.width (slices.drop start)+
        combined.work+appendCost evals+1)
      evals := evals ++ [combined.value]
    | none =>
      tick 1
      match cursor with
      | [] => check false
      | x :: xs =>
        tick (appendCost evals+2)
        evals := evals ++ [x]
        cursor := xs
  tick 1
  check cursor.isEmpty
  tick (takeCost layout.tau point+3)
  pure ⟨point.take layout.tau,evals,slices⟩

def constraintClaims (layouts : List AirLayout) (busPoint : List E) :
    Parser (List TableClaims) := do
  tick (4*layouts.length+lengthCost busPoint+3)
  let n := (layouts.map AirLayout.tau).foldl max 0
  check (n ≤ busPoint.length)
  tick (2*n+2)
  let rounds ← (List.range n).mapM (fun _ => do
    tick 2
    let _ ← readScalars 3
    drawScalar)
  layouts.mapM (fun l => do
    tick (2*rounds.length+3)
    receiveTable l rounds.reverse)

def flockClaims (layouts : List FlockLayout) : Parser (List RingPCSGame.FamilyClaim) := do
  tick (3+if layouts.isEmpty then 0 else
    allCost (fun l => 6 ≤ l.kLog && 13 ≤ l.logN)
      (fun l => if 6 ≤ l.kLog then 4 else 2) layouts)
  check (!layouts.isEmpty && layouts.all (fun l => 6 ≤ l.kLog && 13 ≤ l.logN))
  tick (10*layouts.length+6)
  let m := (layouts.map FlockLayout.logN).foldl max 0
  let rounds := (layouts.map (fun l => l.kLog-6)).foldl max 0
  let _ ← drawScalars (m-13)
  let _ ← drawScalar
  let _ ← readScalars 64
  let _ ← drawScalar
  tick (2*(m-6)+3)
  let zc ← (List.range (m-6)).mapM (fun _ => do
    tick 2
    let _ ← readScalars 2
    drawScalar)
  tick (lengthCost layouts+1)
  let _ ← readScalars (3*layouts.length)
  let _ ← drawScalar
  tick (2*rounds+2)
  let lc ← (List.range rounds).mapM (fun _ => do
    tick 2
    let _ ← readScalars 2
    drawScalar)
  layouts.mapM (fun layout => do
    tick 2
    let slices ← readScalars 64
    let _ ← readScalar
    let assembled := assembleFlock layout zc lc slices
    tick (assembled.work+1)
    match assembled.value with
    | some claim => pure claim
    | none => liftOption 0 none)

@[simp] theorem gkrPoint_erasure (m : Nat) : erase (gkrPoint m) = WHIRCallerClaims.gkrPoint m := by
  by_cases parity : m % 2 = 1 <;>
    simp [gkrPoint,gkrSeed,gkrRound,WHIRCallerClaims.gkrPoint,parity,bind_assoc]
@[simp] theorem busClaims_erasure (l : BusLayout) : erase (busClaims l) = WHIRCallerClaims.busClaims l := by
  simp [busClaims,WHIRCallerClaims.busClaims]
  rfl
@[simp] theorem receiveTable_erasure (l : AirLayout) (p : List E) :
    erase (receiveTable l p) = WHIRCallerClaims.receiveTable l p := by
  simp [receiveTable,WHIRCallerClaims.receiveTable]
  congr! 32
  all_goals first | rfl | (split <;> simp_all)
  all_goals split <;> simp_all
@[simp] theorem constraintClaims_erasure (ls : List AirLayout) (p : List E) :
    erase (constraintClaims ls p) = WHIRCallerClaims.constraintClaims ls p := by
  simp [constraintClaims,WHIRCallerClaims.constraintClaims]
set_option maxHeartbeats 1000000 in
@[simp] theorem flockClaims_erasure (ls : List FlockLayout) :
    erase (flockClaims ls) = WHIRCallerClaims.flockClaims ls := by
  simp [flockClaims,WHIRCallerClaims.flockClaims]
  congr! 32
  all_goals first | rfl | (split <;> simp_all)


/-! Kernel-checked, scoped accepted/rejected token cases. These exercise actual
counted execution, including an early failure after a successful scalar read. -/
namespace Smoke
theorem read_accepts (xs : List E) (rest : List CallerToken) :
    (readScalars xs.length (xs.map CallerToken.sent ++ rest)).result = some (xs,rest) := by
  change erase (readScalars xs.length) _ = _
  rw [readScalars_erasure,WHIRCallerClaims.readScalars_sent]
theorem draw_accepts (xs : List E) (rest : List CallerToken) :
    (drawScalars xs.length (xs.map CallerToken.draw ++ rest)).result = some (xs,rest) := by
  change erase (drawScalars xs.length) _ = _
  rw [drawScalars_erasure,WHIRCallerClaims.drawScalars_draw]
theorem read_rejects_draw : (readScalar [.draw 0]).result = none := rfl
theorem draw_rejects_sent : (drawScalar [.sent 0]).result = none := rfl
theorem failed_prefix_is_charged :
    (readScalars 10 [.sent 0,.draw 0]).result = none ∧
    (readScalars 10 [.sent 0,.draw 0]).work = 13 := by constructor <;> rfl
theorem nonce_rejects_wrong_bits :
    (nonce 4 [.nonce 8 (fun _ => 0)]).result = none ∧
    (nonce 4 [.nonce 8 (fun _ => 0)]).work = 4 := by constructor <;> rfl
theorem gkr_zero_accepts :
    (gkrPoint 0 [.sent 0,.draw 0]).result = some ([],[]) := rfl
theorem gkr_odd_accepts :
    (gkrPoint 1 [.sent 0,.draw 0,.sent 0,.sent 0,.sent 0,.sent 0,.draw 1,.draw 0]).result =
      some ([1],[]) := rfl
theorem gkr_nested_accepts (x z low high : E) :
    (gkrPoint 3 ([.sent 0,.draw 0] ++ List.replicate 4 (.sent 0) ++ [.draw x,.draw 0] ++
      List.replicate 4 (.sent 0) ++ [.draw z] ++ List.replicate 8 (.sent 0) ++
      [.draw low,.draw high,.draw 0])).result = some ([low,high,z],[]) := rfl
def busTokens : List CallerToken := [.draw 0,.draw 0,.draw 0,.draw 0,.draw 0,.sent 0,.draw 0]
theorem empty_bus_accepts :
    (busClaims ⟨[],[],[],0⟩ busTokens).result = some (([],[]),[]) := by
  change erase (busClaims _) _ = _
  rw [busClaims_erasure]
  rfl
theorem invalid_bus_coord_rejects :
    (busClaims ⟨[⟨0,false,[.tableExpression]⟩],[],[],0⟩ busTokens).result = none := by
  change erase (busClaims _) _ = _
  rw [busClaims_erasure]
  rfl
theorem bus_deduplicates :
    (busClaims ⟨[⟨0,false,[.column 2,.column 2]⟩],[],[],0⟩
      (busTokens ++ [.sent 1])).result = some (([],[⟨2,[],1⟩]),[]) := by
  change erase (busClaims _) _ = _
  rw [busClaims_erasure]
  rfl
theorem ordinary_table_accepts :
    (receiveTable ⟨1,2,0,[]⟩ [1] [.sent 0,.sent 1]).result =
      some (⟨[1],[0,1],[]⟩,[]) := rfl
theorem public_columns_reject :
    (receiveTable ⟨0,0,1,[]⟩ [] []).result = none := rfl
theorem duplicate_bit_columns_reject :
    (receiveTable ⟨0,1,0,[⟨0,1⟩,⟨0,1⟩]⟩ [] []).result = none := rfl
theorem bit_table_accepts :
    (receiveTable ⟨0,2,0,[⟨0,2⟩]⟩ [] [.sent 7,.sent 0,.sent 1]).result =
      some (⟨[],[WHIRCallerClaims.combineBits [0,1],7],[0,1]⟩,[]) := by
  change erase (receiveTable _ _) _ = _
  rw [receiveTable_erasure]
  rfl
theorem empty_flock_rejects : (flockClaims [] []).result = none := rfl
theorem invalid_flock_rejects : (flockClaims [⟨0,5,10⟩] []).result = none := rfl
def flockTokens : List CallerToken :=
  [.draw 0] ++ List.replicate 64 (.sent 0) ++ [.draw 0] ++
    (List.replicate 7 [.sent 0,.sent 0,.draw 0]).flatten ++
    List.replicate 3 (.sent 0) ++ [.draw 0] ++ List.replicate 65 (.sent 0)
set_option maxRecDepth 4096 in
theorem minimal_flock_accepts :
    ∃ claims, (flockClaims [⟨0,6,7⟩] flockTokens).result = some (claims,[]) := by
  refine ⟨[⟨0,(List.replicate 7 (0 : E)).toArray,
    fun i => (List.replicate 64 (0 : E))[i.val]'(by simp only [List.length_replicate]; exact i.isLt)⟩],?_⟩
  change erase (flockClaims _) _ = _
  rw [flockClaims_erasure]
  rfl
end Smoke

#print axioms gkrPoint_erasure
#print axioms busClaims_erasure
#print axioms receiveTable_erasure
#print axioms constraintClaims_erasure
#print axioms flockClaims_erasure
#print axioms readScalars_work_le
#print axioms placeClaims_work_le
#print axioms Smoke.invalid_bus_coord_rejects
#print axioms Smoke.gkr_nested_accepts
#print axioms Smoke.minimal_flock_accepts
#print axioms log2_work
#print axioms mu_work_le

end Whir.PCSBCSCallerParserCost
