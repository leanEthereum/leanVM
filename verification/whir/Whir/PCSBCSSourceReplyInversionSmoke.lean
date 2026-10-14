import Whir.PCSBCSSourceReplyInversion

/-! Executable toy-shape smoke, not a production-profile measurement or a
Merkle/Fiat-Shamir endpoint test. Frozen rows below are explicit supplied data. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceReplyInversionSmoke
open Concrete Protocol CausalGame CausalProbability WHIRHistory
open PCSBCSSourceReplyInversion

def toy : Config := ⟨5, #[2,1], #[2,2], #[16,8], #[0,1]⟩
def e (n : Nat) : E := ⟨UInt64.ofNat n,UInt64.ofNat (n+100),UInt64.ofNat (n+200)⟩
def digest : FiatShamirGame.Digest32 := fun i => ⟨i.val,by omega⟩
def rows : Oracle := #[#[e 901,e 902],#[e 903,e 904]]
def nextRows : Oracle := #[#[e 801],#[e 802],#[e 803]]
def frozen : FrozenOracles toy := ⟨fun _ => rows,fun _ _ => nextRows⟩
def m : Message E := ⟨e 11,e 12⟩
def first : Coordinate toy := .initial
def middle : Coordinate toy := .fold ⟨0,by decide⟩ ⟨0,by decide⟩
def boundary : Coordinate toy := .fold ⟨0,by decide⟩ ⟨1,by decide⟩
def finalFold : Coordinate toy := .fold ⟨1,by decide⟩ ⟨0,by decide⟩
def ood : Coordinate toy := .ood ⟨0,by decide⟩ ⟨0,by decide⟩
def query : Coordinate toy := .query ⟨0,by decide⟩
def tail : Coordinate toy := .tail ⟨0,by decide⟩

def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def get (q : Coordinate toy) (scalars : List E)
    (nonce : Option (Nat × E) := none) : IO Inverted :=
  match inverse frozen q (stage q) ⟨scalars,nonce⟩ with
  | some r => pure r
  | none => throw (IO.userError s!"valid inverse rejected at {repr (stage q)}")

/-- Public-shaped source messages at every boundary of the toy schedule. -/
def fields (q : Coordinate toy) : List E :=
  match q with
  | .fold i j => messageScalars m ++
      if j.val+1 = toy.folds[i.val]! then
        if i.val+1 < toy.folds.size then rootScalars digest
        else (List.range (2 ^ remaining toy i.val)).map e
      else []
  | .ood _ _ => e 21 :: messageScalars m
  | _ => messageScalars m

def sourcePrefix (count : Nat) : List Pending :=
  ((List.range (count+1)).map fun n =>
    let q := ((schedule toy)[n]?).getD .initial
    let previous := ((schedule toy)[n-1]?).getD .initial
    (⟨if n = 0 then [] else fields previous,
      match q with | .query _ => some (0,E.zero) | _ => none⟩ : Pending)).reverse

def smoke : IO Unit := do
  let initial ← get first (messageScalars m)
  match initial.reply with
  | .initial msg => check (messageScalars msg == messageScalars m) "initial coefficients"
  | _ => throw (IO.userError "initial tag")
  let mid ← get middle (messageScalars m)
  match mid.reply with
  | .fold msg next residual =>
    check (messageScalars msg == messageScalars m && next.isNone && residual.isEmpty)
      "middle fold normalization"
  | _ => throw (IO.userError "middle fold tag")
  let bound ← get boundary (messageScalars m ++ rootScalars digest)
  match bound.reply with
  | .fold msg next residual =>
    check (messageScalars msg == messageScalars m && next == some nextRows && residual.isEmpty)
      "nonterminal root must use supplied frozen next oracle"
  | _ => throw (IO.userError "nonterminal fold tag")
  check (((announcedRoot boundary ⟨messageScalars m ++ rootScalars digest,none⟩).map
    (fun d => List.ofFn d)) == some (List.ofFn digest)) "exact root digest"
  let residual := (List.range (2 ^ remaining toy 1)).map e
  let final ← get finalFold (messageScalars m ++ residual)
  match final.reply with
  | .fold msg next tailValues =>
    check (messageScalars msg == messageScalars m && next.isNone && tailValues.toList == residual)
      "terminal residual must be exact, ordered and unpadded"
  | _ => throw (IO.userError "terminal fold tag")
  let claim ← get ood (e 21 :: messageScalars m)
  match claim.reply with
  | .ood value =>
    check (value.value == e 21 && messageScalars value.intro == messageScalars m)
      "OOD value precedes coefficients"
  | _ => throw (IO.userError "OOD tag")
  let answer ← get query (messageScalars m) (some (5,e 77))
  match answer.reply with
  | .query actual intro =>
    check (actual == rows && messageScalars intro == messageScalars m)
      "query must preserve supplied frozen rows"
  | _ => throw (IO.userError "query tag")
  check (answer.nonce == some (5,e 77)) "nonce metadata changed"
  let tailAnswer ← get tail (messageScalars m)
  match tailAnswer.reply with
  | .tail msg => check (messageScalars msg == messageScalars m) "tail coefficients"
  | _ => throw (IO.userError "tail tag")
  for q in [first,middle,ood,query,tail] do
    check ((inverse frozen q (stage q) ⟨[],none⟩).isNone) "empty fields accepted"
    check ((inverse frozen q (stage q) ⟨[e 1],none⟩).isNone) "short fields accepted"
    let long := (List.range (replyScalarCount q + 1)).map e
    check ((inverse frozen q (stage q) ⟨long,none⟩).isNone) "extra fields accepted"
  for fields in [messageScalars m, messageScalars m ++ [e 31],
      messageScalars m ++ rootScalars digest ++ [e 32]] do
    check ((inverse frozen boundary (stage boundary) ⟨fields,none⟩).isNone)
      "malformed nonterminal boundary length accepted"
  let noncanonical : List E := [⟨0,0,1⟩,⟨0,0,0⟩]
  check ((inverse frozen boundary (stage boundary) ⟨messageScalars m ++ noncanonical,none⟩).isNone)
    "noncanonical root spare limbs accepted"
  for fields in [messageScalars m ++ residual.dropLast, messageScalars m ++ residual ++ [e 33]] do
    check ((inverse frozen finalFold (stage finalFold) ⟨fields,none⟩).isNone)
      "wrong terminal residual length accepted"
  check ((inverse frozen boundary (.fold 1 1)
    ⟨messageScalars m ++ rootScalars digest,none⟩).isNone) "foreign source phase accepted"
  check ((inverse frozen query (.ood 0 0) ⟨messageScalars m,none⟩).isNone)
    "foreign source stage accepted"
  let messages : List Pending := [⟨messageScalars m,none⟩,⟨[],none⟩]
  check (scheduledAdmissible toy messages) "toy initial source prefix not admitted"
  match replies frozen messages with
  | none => throw (IO.userError "admitted initial reply prefix rejected")
  | some answers => check (answers.size == 1) "source response off-by-one"
  check ((inverseAt frozen messages 1).isNone) "late/current reply read"
  check ((inverseAt frozen messages 100).isNone) "future reply read"
  check ((replies frozen []).isNone) "empty source packet accepted"
  check ((replies frozen [⟨[e 1],none⟩]).isNone) "malformed initial Pending accepted"
  for count in List.range (depth toy) do
    let source := sourcePrefix count
    check (scheduledAdmissible toy source) s!"source admission failed at {count}"
    match replies frozen source with
    | none => throw (IO.userError s!"full source prefix rejected at {count}")
    | some answers =>
      check (answers.size == count) "strict source-prefix array length"
      for n in List.range count do
        let q := ((schedule toy)[n]?).getD .initial
        check ((answers[n]?).bind (replyScalars q digest) == some (fields q))
          s!"source scalar re-projection at {count}/{n}"
      check ((inverseAt frozen source count).isNone) "current response present in source prefix"
      check ((inverseAt frozen source (count+1)).isNone) "future response present in source prefix"
    match ((schedule toy)[count]?).getD .initial with
    | .query _ =>
      let noNonce := source.map fun p => {p with nonce := none}
      check ((replies frozen noNonce).isNone) "missing query rejection nonce accepted"
      let hard := source.map fun p => {p with nonce := p.nonce.map fun (_,x) => (64,x)}
      check ((replies frozen hard).isNone) "over-limit source nonce accepted"
    | _ => pure ()
  IO.println "source reply inverse PASS: initial/middle-fold/OOD/query/tail, frozen rows, exact nonterminal root and terminal residual, nonce metadata, malformed lengths/root/stage/phase, strict prefix indexes"

end Whir.PCSBCSSourceReplyInversionSmoke

def main : IO Unit := Whir.PCSBCSSourceReplyInversionSmoke.smoke
