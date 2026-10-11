import Whir.Protocol
import Whir.CausalGame
import Whir.CommitmentAmbiguity
import Whir.ConcreteRowExtraction

open Whir.Concrete Whir.Protocol

def seed (i : Nat) : UInt64 :=
  let x := UInt64.ofNat (i+1) * 11400714819323198485
  (x ^^^ (x >>> 29)) * 13787848793156543929

def fixture (i : Nat) : E := ⟨seed (3*i), seed (3*i+1), seed (3*i+2)⟩

def emitN (key : String) (xs : Array Nat) : IO Unit :=
  IO.println (key ++ "=" ++ String.intercalate "," (xs.toList.map toString))

def emitE (key : String) (xs : Array E) : IO Unit :=
  emitN key (xs.flatMap fun x => #[x.c0.toNat, x.c1.toNat, x.c2.toNat])

def requireIO (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def smoke : IO Unit := do
  let c : Config := ⟨7, #[2,2,1], #[1,2,2], #[5,3,3], #[0,1,1]⟩
  let ch : Challenges := ⟨#[
    ⟨#[fixture 1, fixture 2], #[tab 5 (fun i => fixture (10+i))], #[fixture 20], fixture 21⟩,
    ⟨#[fixture 3, fixture 4], #[tab 3 (fun i => fixture (30+i))], #[fixture 40], fixture 41⟩,
    ⟨#[fixture 5], #[], #[fixture 50], fixture 51⟩], #[fixture 6, fixture 7]⟩
  let witness := tab 96 seed
  let b := tab 128 fun i => if i < 96 then fixture (100+i) else E.zero
  let target := dot (witness.map E.ofK) b
  let (root, p) ← match prove c ch witness b target with
    | .ok result => pure result
    | .error e => throw (IO.userError ("honest prover: " ++ e))
  let check := fun proof => (verify c ch 3 root b target proof).isOk
  requireIO (check p) "honest multilevel opening rejected"
  requireIO (!check {p with levels := p.levels.pop}) "short opening accepted"
  requireIO (!check {p with residual := p.residual.pop}) "short final accepted"
  requireIO (!check {p with residual := p.residual.set! 0 (p.residual[0]! + E.one)}) "bad final accepted"
  requireIO (!(verify c ch 3 root b (target+E.one) p).isOk) "bad target accepted"
  let l0 := p.levels[0]!
  requireIO (!check {p with levels := p.levels.set! 0 {l0 with rows := l0.rows.pop}}) "missing query accepted"
  let row := l0.rows[0]!
  let rows := l0.rows.set! 0 (row.set! 0 (row[0]!+E.one))
  requireIO (!check {p with levels := p.levels.set! 0 {l0 with rows}}) "bad authenticated row accepted"
  let ood := l0.oods[0]!
  let oods := l0.oods.set! 0 {ood with value := ood.value+E.one}
  requireIO (!check {p with levels := p.levels.set! 0 {l0 with oods}}) "bad OOD accepted"
  requireIO (!check {p with levels := p.levels.set! 0 {l0 with oods := #[]}}) "missing OOD accepted"
  let badCh := {ch with levels := ch.levels.set! 0 {ch.levels[0]! with querySqueezes := #[]}}
  requireIO (!(verify c badCh 3 root b target p).isOk) "missing query challenge accepted"
  requireIO (!(verify c ch 0 root b target p).isOk) "empty lane layout accepted"
  let badPublic : Whir.CausalGame.Public := ⟨c, 3, #[], #[⟨b.pop, target⟩]⟩
  let tape : Whir.CausalGame.Tape c := ⟨E.zero,
    (fun _ => ⟨(fun _ => E.zero), (fun _ _ => E.zero), (fun _ => E.zero), E.zero⟩),
    fun _ => E.zero⟩
  requireIO (!Whir.CausalGame.experiment badPublic (fun _ _ _ => .initial default) tape)
    "malformed public claim accepted"
  IO.println "lean_smoke=honest,multilevel,truncated_lanes,bad_target,short_opening,short_final,bad_final,missing_query,bad_row,bad_ood,missing_ood,missing_challenge,bad_layout,malformed_public_claim"

def ambiguitySmoke : IO Unit := do
  requireIO (Whir.CommitmentAmbiguity.smallSession false).isOk
    "zero branch of immutable spliced commitment rejected"
  requireIO (Whir.CommitmentAmbiguity.smallSession true).isOk
    "one branch of immutable spliced commitment rejected"
  IO.println "ambiguity_smoke=same_immutable_root,incompatible_claims,small_kernel_fixture,both_sessions_accepted"

def extractionSmoke : IO Unit := do
  let words : Array K := #[3, 5, 8, 13]
  let honest := encode 2 2 (words.map E.ofK)
  for errors in [0, 3, 6] do
    let received : Vector E (Whir.ConcreteRowExtraction.domain 4 (by decide)).n :=
      Vector.ofFn fun i =>
        if i.val < errors then honest[i.val]! + E.ofK 1 else honest[i.val]!
    let result := Whir.ConcreteRowExtraction.countedExtractRow 2 2 (by decide) received
    requireIO (result.1 == some words) ("source-word Gao recovery failed with " ++ toString errors ++ " errors")
    requireIO (result.2 ≤ Whir.ConcreteRowExtraction.rowArithmeticPolynomial 16)
      "source-word decoder exceeded its proved field-arithmetic budget"
    IO.println ("extraction_smoke=actual_word_encoder,N16,k4,errors" ++ toString errors ++
      ",recovered3_5_8_13,field_arithmetic" ++ toString result.2)

def vectors : IO Unit := do
  emitN "kmul" (tab 40 fun i => (kmul (seed i) (seed (i+41))).toNat)
  emitN "kinv" (tab 12 fun i => (kinv (seed i)).toNat)
  emitE "emul" (tab 32 fun i => fixture i * fixture (i+33))
  emitE "eq" (eqTable (tab 4 fixture))
  emitN "roots" ((subspaceRoots 8).map UInt64.toNat)
  for lanes in #[1,3,4] do
    let w := tab (lanes*8) seed
    emitE s!"base_{lanes}" ((encodeBase w 5 2 1).flatten)
  let f := tab 32 fixture
  emitE "ext" ((encodeExt f 5 2 1).flatten)
  let r := fixture 70
  emitE "lane_fold" (foldLane f 8 r)
  emitE "low_fold" (foldLow f r)
  let rs := tab 5 fixture
  emitE "rotation" (rotatePoint 2 rs)
  emitE "rotation_mle" #[mle f (rotatePoint 2 rs)]
  let qs := #[0, 5, 5, 13]
  let ws := powers (fixture 80) qs.size
  let point := tab 3 fixture
  let b := induced 3 qs ws
  requireIO (mle b point == inducedAt 3 qs ws point) "dense/succinct induced disagreement"
  emitE "induced" b
  emitE "induced_at" #[inducedAt 3 qs ws point]
  for rate in [1:5] do
    for n in [15:29] do
      let c := (productionConfig n rate).getD default
      requireIO c.valid "invalid production configuration"
      emitN s!"config_{n}_{rate}" (c.folds ++ c.rates ++ c.queries ++ c.oodCounts)
  for (n, rate) in #[(14,1), (29,1), (15,0), (15,5)] do
    requireIO (productionConfig n rate).isNone "unsupported production configuration accepted"

def parseNat (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError ("invalid natural: " ++ s))

def main (args : List String) : IO Unit := do
  match args with
  | "query" :: d :: count :: limbs =>
    let depth ← parseNat d
    let count ← parseNat count
    let ns ← limbs.toArray.mapM parseNat
    requireIO (ns.size % 3 == 0) "query requires triples of limbs"
    let squeezes := tab (ns.size/3) fun i => E.mk (UInt64.ofNat ns[3*i]!) (UInt64.ofNat ns[3*i+1]!) (UInt64.ofNat ns[3*i+2]!)
    match deriveQueries depth count squeezes with
    | none => throw (IO.userError "malformed query challenge vector")
    | some qs => emitN "queries" qs
  | ["ambiguity"] => ambiguitySmoke
  | ["extraction"] => extractionSmoke
  | [] => vectors; smoke
  | _ => throw (IO.userError "usage: whirModel [ambiguity | extraction | query DEPTH COUNT LIMB ...]")
