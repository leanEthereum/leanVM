module

public import LeanVMCircuits.Rec.UnionRows
public import LeanVMCircuits.Rec.WhirRounds

@[expose] public section

/-!
The checker's verdict on a recursion circuit.

`Cert.accepts`: every rule is justified, every transcript is a chain of compressions, the unions' rows are where the
certificate says (`Cert.unionsOk`), every field equality reading a challenge is a test, for every test some
transcript's `certifyT` gives both its wires a binding time, each union's coverage entry holds (`Cert.coversOk`), and
each named sumcheck's rounds, proof-of-work check, GKR odd layer, GKR radix-four top layer, claim split and WHIR
sumcheck are where the certificate says (`Cert.sumchecksOk`, `PowCert.ok`, `Cert.oddsOk`, `Cert.lateOk`).

- `tests_by`: each test's wires, at their binding time `k`, are in the closure of what one transcript's first `k`
  blocks absorb, and of the statement only once `k` passes its last block; `checkbind_sound` is its weaker form.
- `unionsValid`: on two assignments holding every constraint but the tests, under collision resistance of the
  compression, the union products are functions of their inputs.
- `tests_determined`: on two such assignments, under collision resistance of the compression and of the duplex's
  output window, agreeing on what that transcript's first `k` blocks absorb (and the statement past its last block),
  each test's wires agree.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model

attribute [local irreducible] LeanVMCircuits.Blake2s.program


/-! Which equalities are tests. -/

/-- An equality made outside the builder's methods between field elements: `eq_e`, `eq_k`, `eq_e_const`,
`eq_k_const`. -/
def _root_.LeanVMCircuits.Rec.Model.Call.isFieldEq : Call → Bool
  | .eqE .. | .eqK .. | .eqConstE .. | .eqConstK .. => true
  | _ => false

/-- One call of the scan for wires that read a challenge: the call reads one if it is a squeeze or reads a wire that
does, and so does each wire it makes, but a constant. -/
def taintStep (c : Call) (relax : Bool) (s : State) (tw : Array Bool) : State × Array Bool :=
  let g := c.isSqueeze || c.args.any (tw.getD · false)
  let s' := ((c.execR relax).run s).2
  let isConst := fun w => (s'.pub.extract s.pub.size s'.pub.size).any fun p => p.1 == w && match p.2 with
    | .const _ => true
    | .statement _ => false
  (s', (List.range (s'.next - s.next)).foldl (fun t k => t.push (g && !isConst (s.next + k))) tw)

/-- The scan before call `i`: the state, and whether each wire reads a challenge. -/
def taintUpTo (calls : Array Call) (relax : Array Bool) : ℕ → State × Array Bool
  | 0 => ({}, #[])
  | i + 1 => taintStep (calls.getD i .zero) (relax.getD i false) (taintUpTo calls relax i).1
    (taintUpTo calls relax i).2

/-- The scan from call `i`, checking each field equality the replay keeps reads no challenge. -/
def taintOk (calls : Array Call) (relax : Array Bool) (i : ℕ) (s : State) (tw : Array Bool) : Bool :=
  if h : i < calls.size then
    let c := calls[i]
    if c.isFieldEq && !relax.getD i false && c.args.any (tw.getD · false) then false
    else
      let r := taintStep c (relax.getD i false) s tw
      taintOk calls relax (i + 1) r.1 r.2
  else true
termination_by calls.size - i

theorem taintOk_sound (calls : Array Call) (relax : Array Bool) :
    ∀ i, i ≤ calls.size → taintOk calls relax i (taintUpTo calls relax i).1 (taintUpTo calls relax i).2 = true →
      ∀ j, i ≤ j → j < calls.size → (calls.getD j .zero).isFieldEq = true → relax.getD j false = false →
        ∀ a ∈ (calls.getD j .zero).args, (taintUpTo calls relax j).2.getD a false = false := by
  intro i hi h
  induction h' : calls.size - i generalizing i with
  | zero => intro j hj hj'; omega
  | succ d ih =>
    have hlt : i < calls.size := by omega
    rw [taintOk, dif_pos hlt] at h
    intro j hj hjs hfe hrl a ha
    have hget : calls[i] = calls.getD i .zero := by simp [Array.getD_eq_getD_getElem?, hlt]
    dsimp only at h
    split at h
    · simp at h
    · rename_i hc
      rcases Nat.eq_or_lt_of_le hj with hij | hj
      · subst hij
        rw [← hget] at hfe ha
        simp only [hfe, hrl, Bool.not_false, Bool.true_and, Bool.and_true, List.any_eq_true, not_exists, not_and,
          Bool.not_eq_true] at hc
        exact hc a ha
      · have h1 : taintOk calls relax (i + 1) (taintUpTo calls relax (i + 1)).1
            (taintUpTo calls relax (i + 1)).2 = true := by
          simp only [taintUpTo, ← hget]; exact h
        exact ih (i + 1) (by omega) h1 (by omega) j (by omega) hjs hfe hrl a ha

/-! The verdict. -/

/-- A transcript: its absorb blocks as `HASH` row indices in order, the firings that bind its tests, and its squeezes
as `HASH` row indices. -/
structure Transcript where
  blocks : List ℕ
  firings : Array ℕ
  squeezes : List ℕ := []
  /-- The firings that bind with `rulesRO`, the random-oracle view's rules. -/
  firingsRO : Array ℕ := #[]
  /-- The rules of the transcript's random-oracle view: none reads a hash row it drops (`dropOf`). -/
  rulesRO : Rules Just := {}
  deriving Inhabited

/-- The words block `k` absorbs, as nodes. -/
def wordsOf (s : State) (k : ℕ) : List ℕ := (List.range 8).map fun j => limb ((s.hash.getD k []).getD (8 + j) 0) 0

/-- The words the blocks absorb, as nodes. -/
def absorbed (s : State) (blocks : List ℕ) : List ℕ := blocks.flatMap (wordsOf s)

/-- The statement's nodes. -/
def statementNodes (s : State) : List ℕ :=
  s.pub.toList.flatMap fun e => match e.2 with
    | .statement _ => limbs4 e.1
    | .const _ => []

/-- The place among `blocks` of the block whose output is a row's chaining value. -/
def readsBlock (s : State) (blocks : List ℕ) (row : List ℕ) : Option ℕ :=
  blocks.findIdx? fun b => (s.hash.getD b []).getD 6 0 == row.getD 0 0

/-- A transcript's challenges with their times: each of its squeeze rows' outputs, the random oracle's answer, one
after the number of blocks its chaining value needs. A challenge is so a seed of what is absorbed after it, and not of
the round that draws it. -/
def chalSeeds (s : State) (t : Transcript) : List (ℕ × ℕ) :=
  t.squeezes.flatMap fun k =>
    match isSqueezeRow s (s.hash.getD k []), readsBlock s t.blocks (s.hash.getD k []) with
    | true, some i => (hashOut (s.hash.getD k [])).map ((i + 2), ·)
    | _, _ => []

/-- A transcript's seeds: what its blocks absorb, its challenges, and the statement. -/
def seedsOf (s : State) (t : Transcript) : List ℕ :=
  absorbed s t.blocks ++ (chalSeeds s t).map (·.2) ++ statementNodes s

/-- A transcript's seeds with their times: block `i`'s words at `i + 1`, a challenge one after the block it reads,
the statement after the last block. -/
def seedsT (s : State) (t : Transcript) : List (ℕ × ℕ) :=
  (List.range t.blocks.length).flatMap (fun i => (wordsOf s (t.blocks.getD i 0)).map ((i + 1), ·)) ++ chalSeeds s t ++
    (statementNodes s).map ((t.blocks.length + 1), ·)

/-- What a transcript's first `k` blocks absorb, the challenges seeded by `k`, and the statement once `k` passes its
last block. -/
def seedsBefore (s : State) (t : Transcript) (k : ℕ) : List ℕ :=
  absorbed s (t.blocks.take k) ++ ((chalSeeds s t).filter (·.1 ≤ k)).map (·.2) ++
    if t.blocks.length < k then statementNodes s else []

/-- The words a transcript squeezes from the chaining value a challenge drawn after its first `time` blocks reads,
but the challenge's own words `own`: a squeeze row's outputs are the oracle's answers, each word independent of the
others, so the words squeezed with a challenge (WHIR's query positions, squeezed with its batching challenge) fix
nothing about it. -/
def sibSeeds (s : State) (t : Transcript) (time : ℕ) (own : List ℕ) : List ℕ :=
  ((chalSeeds s t).filter fun p => p.1 == time + 1 && !own.contains p.2).map (·.2)

theorem seedsBy_seedsT {s : State} {t : Transcript} {k : ℕ} :
    ∀ n ∈ seedsBy (seedsT s t) k, n ∈ seedsBefore s t k := by
  intro n hn
  simp only [seedsBy, seedsT, List.mem_map, List.mem_filter, List.mem_append, List.mem_flatMap, List.mem_range,
    decide_eq_true_eq] at hn
  obtain ⟨p, ⟨hp, hk⟩, rfl⟩ := hn
  simp only [seedsBefore, absorbed, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  rcases hp with (⟨i, hi, hp⟩ | hp) | ⟨w, hw, rfl⟩
  · obtain ⟨w, hw, rfl⟩ := hp
    left; left
    refine ⟨t.blocks.getD i 0, ?_, hw⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  · exact Or.inl (Or.inr ⟨p, ⟨hp, hk⟩, rfl⟩)
  · right
    rw [if_pos (by simp only at hk; omega)]
    exact hw

theorem seedsBefore_mono {s : State} {t : Transcript} {k k' : ℕ} (h : k ≤ k') :
    ∀ n ∈ seedsBefore s t k, n ∈ seedsBefore s t k' := by
  intro n hn
  simp only [seedsBefore, absorbed, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hn ⊢
  rcases hn with (⟨b, hb, hn⟩ | ⟨p, ⟨hp, hk⟩, rfl⟩) | hn
  · exact Or.inl (Or.inl ⟨b, (List.take_prefix_take_left h).subset hb, hn⟩)
  · exact Or.inl (Or.inr ⟨p, ⟨hp, by omega⟩, rfl⟩)
  · split at hn
    · rw [if_pos (by omega)]; exact Or.inr hn
    · simp at hn

theorem seedsBefore_seedsOf {s : State} {t : Transcript} {k : ℕ} :
    ∀ n ∈ seedsBefore s t k, n ∈ seedsOf s t := by
  intro n hn
  simp only [seedsBefore, seedsOf, absorbed, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hn ⊢
  rcases hn with (⟨b, hb, hn⟩ | ⟨p, ⟨hp, -⟩, rfl⟩) | hn
  · exact Or.inl (Or.inl ⟨b, List.mem_of_mem_take hb, hn⟩)
  · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
  · split at hn
    · exact Or.inr hn
    · simp at hn

/-- Whether a wire is a constant. -/
def isConst (s : State) (w : ℕ) : Bool :=
  s.pub.any fun e => e.1 == w && match e.2 with
    | .const _ => true
    | .statement _ => false

/-- Each block's chaining value is the previous block's output. -/
def links (s : State) (k : ℕ) : List ℕ → Bool
  | [] => true
  | k' :: ks => k' < s.hash.size && (s.hash.getD k' []).getD 0 0 == (s.hash.getD k []).getD 6 0 && links s k' ks

/-- The blocks are a chain of compressions from a constant chaining value. -/
def chainOk (s : State) : List ℕ → Bool
  | [] => true
  | k :: ks => k < s.hash.size && isConst s ((s.hash.getD k []).getD 0 0) && links s k ks

/-- A union's coverage test: its equality, its two products (the children's selected claims, the declared claims),
and the transcript that draws its point. -/
structure Cover where
  test : ℕ
  sel : ℕ
  decl : ℕ
  transcript : ℕ
  deriving Inhabited, Repr

/-- What `CheckBind` claims of a circuit: its justified rules, which equalities are tests, the union products, and
its transcripts; and to read the unions' rows, the calls that built it, the calls whose equality is a test, where
each union's pools and products are, and each union's coverage test. -/
structure Cert where
  rules : Rules Just
  nodes : ℕ
  isTest : Array Bool
  claims : Array UnionClaim
  transcripts : List Transcript
  calls : Array Call
  relax : Array Bool
  pools : Array PoolCert
  prods : Array ProdCert
  /-- Each product's point. -/
  points : Array PointCert
  covers : Array Cover
  sumchecks : Array SumcheckCert := #[]
  pows : Array PowCert := #[]
  odds : Array OddCert := #[]
  /-- The radix-four top layers, claim splits and WHIR sumchecks the certificate names. -/
  tops : Array TopCert := #[]
  splits : Array SplitCert := #[]
  whirs : Array WhirCert := #[]

def Cert.test (c : Cert) (u : ℕ) : Bool := c.isTest.getD u false

/-- The time a transcript's firings bind each node at: the number of its blocks it needs, one more than their number
if it needs the statement. -/
def Cert.times (c : Cert) (s : State) (t : Transcript) : Array (Option ℕ) :=
  certifyT c.rules c.nodes (seedsT s t) t.firings

/-- Each transcript with its times. -/
def Cert.marks (c : Cert) (s : State) : List (Transcript × Array (Option ℕ)) :=
  c.transcripts.map fun t => (t, c.times s t)

/-- The hash rows a transcript's random-oracle view drops: those writing one of its own absorb blocks' or squeezes'
outputs, the compressions whose answers vary with its challenges. The other transcripts' rows hold. -/
def dropOf (s : State) (t : Transcript) (row : List ℕ) : Bool :=
  (t.blocks ++ t.squeezes).any fun k => (s.hash.getD k []).getD 6 0 == row.getD 6 0

/-- The times in the random-oracle view: the transcript's `rulesRO` and their firings. -/
def Cert.timesRO (c : Cert) (s : State) (t : Transcript) : Array (Option ℕ) :=
  certifyT t.rulesRO c.nodes (seedsT s t) t.firingsRO

/-- Each transcript with its random-oracle times. -/
def Cert.marksRO (c : Cert) (s : State) : List (Transcript × Array (Option ℕ)) :=
  c.transcripts.map fun t => (t, c.timesRO s t)

/-- The times in the random-oracle view with `extra` seeds too, by `firings`. -/
def Cert.timesX (c : Cert) (s : State) (t : Transcript) (extra : List (ℕ × ℕ)) (firings : Array ℕ) :
    Array (Option ℕ) :=
  certifyT t.rulesRO c.nodes (seedsT s t ++ extra) firings

/-- The output words of its squeezes a challenge reads: for each word, its `d_to_k` call's place in the squeeze's
digest. -/
def ChalCert.own (os : Array (List ℕ)) (cc : ChalCert) : List ℕ :=
  cc.words.map fun e => limb (outAt os e.2.2 0) e.2.1

/-- What a WHIR round's polynomial is read with: the seeds before its challenge, and for a batch round the words
squeezed with `λ`, its query positions. -/
def WhirRound.seeds (s : State) (t : Transcript) : WhirRound → List ℕ
  | .fold _ cc .. => seedsBefore s t cc.time
  | .batch cc _ own _ => seedsBefore s t cc.time ++ sibSeeds s t cc.time own

/-- When a transcript binds two wires: their limbs' latest time. -/
def bindTime (m : Array (Option ℕ)) (a b : ℕ) : Option ℕ := latest m (some 0) (limbs4 a ++ limbs4 b)

/-- Product `i`'s pool. -/
def Cert.poolOf (c : Cert) (i : ℕ) : PoolCert := c.pools.getD (c.prods.getD i default).pool default

/-- The unions' rows, given the replay with the tests' equalities relaxed: it builds the circuit without its tests,
each product's pool, product and point calls are where the certificate says, and the claims are the products'. -/
def Cert.unionsAt (c : Cert) (s t : State) (os : Array (List ℕ)) : Bool :=
  sameSat (keep s c.test) t &&
    c.claims == c.prods.map (fun qc => qc.claim os (c.pools.getD qc.pool default)) &&
    c.prods.all (fun qc => (c.pools.getD qc.pool default).ok os c.calls c.relax &&
      qc.ok os (c.pools.getD qc.pool default) c.calls c.relax) &&
    (List.range c.prods.size).all fun i => (c.points.getD i default).ok os c.calls c.relax (c.prods.getD i default)

/-- The unions' rows are where the certificate says. -/
def Cert.unionsOk (c : Cert) (s : State) : Bool :=
  match replayR c.calls c.relax 0 {} #[] with
  | none => false
  | some (t, os) => c.unionsAt s t os

/-- The relaxed replay's outputs, which a certificate's wires are read from. -/
def Cert.outs (c : Cert) : Array (List ℕ) :=
  match replayR c.calls c.relax 0 {} #[] with
  | some (_, os) => os
  | none => #[]

/-- Some transcript's marks cover every test's wires. -/
def Cert.testsBound (c : Cert) (s : State) (ms : List (Transcript × Array (Option ℕ))) : Bool :=
  (List.range s.unions.size).all fun u => !c.test u || match s.unions[u]? with
    | some (a, b) => ms.any fun m => (bindTime m.2 a b).isSome
    | none => true

/-- Each product is in a coverage entry, and each entry's equality is a test of its two products' outputs at one
point, whose transcript's marks cover what both pools commit to; the declared pool has one digest and does not select,
and the children's pool's run one-hot closes at its last digest. -/
def Cert.coversOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) :
    Bool :=
  (List.range c.prods.size).all (fun i => c.covers.any fun cv => cv.sel == i || cv.decl == i) &&
  c.covers.all fun cv => cv.sel < c.prods.size && cv.decl < c.prods.size && cv.transcript < ms.length &&
    c.test cv.test && c.points.getD cv.sel default == c.points.getD cv.decl default &&
    s.unions[cv.test]? == some (ProdCert.out os (c.poolOf cv.sel) (c.prods.getD cv.sel default),
      ProdCert.out os (c.poolOf cv.decl) (c.prods.getD cv.decl default)) &&
    (((c.poolOf cv.sel).committed os ++ (c.poolOf cv.decl).committed os).flatMap limbs4).all
      (fun n => ((ms.getD cv.transcript default).2.getD n none).isSome) &&
    !(c.poolOf cv.decl).selecting && (c.poolOf cv.decl).runs == 1 && (c.poolOf cv.sel).endOk os c.calls c.relax

/-- A challenge is drawn after its transcript's first `time` blocks: its `k_to_e` call reads three words, each a word
of a `d_to_k` of a squeeze whose chaining value is block `time`'s output. -/
def ChalCert.ok (s : State) (os : Array (List ℕ)) (cs : Array Call) (blocks : List ℕ) (cc : ChalCert) : Bool :=
  let wd := fun k => let e := cc.words.getD k default; outAt os e.1 e.2.1
  0 < cc.time && cc.time ≤ blocks.length && outAt os cc.chalAt 0 == cc.chal && cc.words.length == 3 &&
    cs[cc.chalAt]? == some (.kToE (wd 0) (wd 1) (wd 2)) &&
    cc.words.all fun e => cs[e.1]? == some (.dToK (outAt os e.2.2 0)) && match cs[e.2.2]? with
      | some (.leafBlock h _ t _) => t / 2 ^ 56 == 6 && h == (s.hash.getD (blocks.getD (cc.time - 1) 0) []).getD 6 0
      | _ => false

/-- A round's challenge is drawn after its transcript's first `time` blocks. -/
def RoundCert.chalOk (s : State) (os : Array (List ℕ)) (cs : Array Call) (blocks : List ℕ) (rc : RoundCert) : Bool :=
  ChalCert.ok s os cs blocks ⟨rc.chal, rc.chalAt, rc.words, rc.time⟩

/-- Wires a transcript binds by `time`: every limb of their `E` view. -/
def boundBy (m : Array (Option ℕ)) (ws : List ℕ) (time : ℕ) : Bool :=
  (ws.flatMap limbs3).all fun n => match m.getD n none with
    | some k => decide (k ≤ time)
    | none => false

/-- Each GKR odd layer's calls are in the replay, its test is a test of its claim and expected value, its input claims
are bound before `λ` is drawn, and its children before the next challenge is. -/
def Cert.oddsOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) : Bool :=
  c.odds.all fun oc =>
    let t := ms.getD oc.transcript default
    oc.transcript < ms.length && oc.ok os c.calls c.relax && c.test oc.test &&
      (s.unions[oc.test]? == some (oc.claim os, oc.expected os) ||
        s.unions[oc.test]? == some (oc.expected os, oc.claim os)) &&
      oc.lam.ok s os c.calls t.1.blocks && oc.next.ok s os c.calls t.1.blocks &&
      boundBy t.2 oc.values oc.lam.time &&
      boundBy t.2 ((List.range oc.m).flatMap fun k => [oc.left k, oc.right k]) oc.next.time

/-- What round `i`'s prover sends, its weight, and for the first round the input claim unless it is hinted, are bound
by the round's time. -/
def SumcheckCert.boundOk (m : Array (Option ℕ)) (sc : SumcheckCert) (i : ℕ) : Bool :=
  let rc := sc.rounds.getD i default
  ((rc.sent ++ rc.weight.toList ++ (if i = 0 ∧ sc.hints = [] then [sc.claim0] else [])).flatMap limbs3).all
    fun n =>
    match m.getD n none with
    | some k => decide (k ≤ rc.time)
    | none => false

/-- The seeds a hinted input claim is bound with: its hints' limbs, at the start. -/
def SumcheckCert.hintSeeds (sc : SumcheckCert) : List (ℕ × ℕ) := (sc.hints.flatMap limbs3).map (0, ·)

/-- Each named sumcheck's rounds are in the replay, its test is a test of its last side (the last claim, or the
residual from it), each round's challenge is drawn after the blocks binding what the prover sends in it, and a hinted
input claim is bound before the first challenge with its hints as seeds. -/
def Cert.sumchecksOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) :
    Bool :=
  c.sumchecks.all fun sc => sc.transcript < ms.length && sc.ok os c.calls c.relax && c.test sc.test &&
    (s.unions[sc.test]? == some (sc.side os, sc.final) || s.unions[sc.test]? == some (sc.final, sc.side os)) &&
    ((List.range sc.rounds.length).all fun i =>
      (sc.rounds.getD i default).chalOk s os c.calls (ms.getD sc.transcript default).1.blocks &&
        sc.boundOk (ms.getD sc.transcript default).2 i) &&
    (sc.hints.isEmpty || boundBy (c.timesX s (ms.getD sc.transcript default).1 sc.hintSeeds sc.hintFirings)
      [sc.claim0] (sc.rounds.getD 0 default).time)

/-- Each GKR radix-four top layer's calls are in the replay, its test is a test of its claim and expected value, its
challenges are drawn where it says, its input claims are bound before `λ` is drawn, and its children before `low`
is. -/
def Cert.topsOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) : Bool :=
  c.tops.all fun tc =>
    let t := ms.getD tc.transcript default
    tc.transcript < ms.length && tc.ok os c.calls c.relax && c.test tc.test &&
      (s.unions[tc.test]? == some (tc.claim os, tc.expected os) ||
        s.unions[tc.test]? == some (tc.expected os, tc.claim os)) &&
      tc.lam.ok s os c.calls t.1.blocks && tc.low.ok s os c.calls t.1.blocks && tc.high.ok s os c.calls t.1.blocks &&
      boundBy t.2 tc.values tc.lam.time &&
      boundBy t.2 ((List.range tc.m).flatMap fun k => (List.range 4).map (tc.kid k)) tc.low.time

/-- Each claim split's calls are in the replay, and its test is a test of its total and the claim's value. -/
def Cert.splitsOk (c : Cert) (s : State) (os : Array (List ℕ)) : Bool :=
  c.splits.all fun pc => pc.ok os c.calls c.relax && c.test pc.test &&
    (s.unions[pc.test]? == some (pc.total os, pc.value) || s.unions[pc.test]? == some (pc.value, pc.total os))

/-- A WHIR round's polynomial is bound by its challenge: a fold round's coefficients by its time; a batch round's
atoms by `λ`'s time with the words squeezed with `λ` as seeds at that time, `own` being the words `λ` reads, each a
squeeze's output one step after `λ`'s time. -/
def Cert.whirBound (c : Cert) (s : State) (os : Array (List ℕ)) (t : Transcript × Array (Option ℕ)) :
    WhirRound → Bool
  | wr@(.fold _ cc ..) => boundBy t.2 (wr.atoms os) cc.time
  | wr@(.batch cc _ own fs) => own == cc.own os && own.all (fun n => (chalSeeds s t.1).contains (cc.time + 1, n)) &&
      boundBy (c.timesX s t.1 ((sibSeeds s t.1 cc.time own).map (cc.time, ·)) fs) (wr.atoms os) cc.time

/-- Each WHIR sumcheck's rounds are in the replay, its test is a test of its last claim, each round's challenge is
drawn where it says, the input claim is bound before the first challenge, and what each round's polynomial reads
before its challenge (`Cert.whirBound`). -/
def Cert.whirsOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) : Bool :=
  c.whirs.all fun wc =>
    let t := ms.getD wc.transcript default
    wc.transcript < ms.length && wc.ok os c.calls c.relax && c.test wc.test &&
      (s.unions[wc.test]? == some (wc.claimAt os wc.rounds.length, wc.final) ||
        s.unions[wc.test]? == some (wc.final, wc.claimAt os wc.rounds.length)) &&
      boundBy t.2 [wc.claim0] (wc.rounds.getD 0 default).chal.time &&
      (List.range wc.rounds.length).all fun i =>
        (wc.rounds.getD i default).chal.ok s os c.calls t.1.blocks && c.whirBound s os t (wc.rounds.getD i default)

/-- The later checks: the radix-four top layers, the claim splits and the WHIR sumchecks. -/
def Cert.lateOk (c : Cert) (s : State) (os : Array (List ℕ)) (ms : List (Transcript × Array (Option ℕ))) : Bool :=
  c.topsOk s os ms && c.splitsOk s os && c.whirsOk s os ms

/-- A round's challenge as a `ChalCert`. -/
def RoundCert.cc (rc : RoundCert) : ChalCert := ⟨rc.chal, rc.chalAt, rc.words, rc.time⟩

/-- A challenge's own words are the oracle's: each word's place is one of its digest's four, and each own word is a
challenge seed of its transcript one step after the challenge's time, and at no other time. -/
def ChalCert.ownOk (s : State) (os : Array (List ℕ)) (t : Transcript) (cc : ChalCert) : Bool :=
  cc.words.all (fun e => decide (e.2.1 < 4)) &&
    (cc.own os).all fun n => (chalSeeds s t).contains (cc.time + 1, n) &&
      (chalSeeds s t).all fun p => p.2 != n || p.1 == cc.time + 1

/-- Challenges a check draws in order from one transcript: each challenge's own words are the oracle's, no two
challenges share a word, and their times do not decrease (`strict`: increase). -/
def chalsOk (s : State) (os : Array (List ℕ)) (t : Transcript) (strict : Bool) (ccs : List ChalCert) : Bool :=
  ccs.all (·.ownOk s os t) && decide (ccs.flatMap (·.own os)).Nodup &&
    if strict then decide (ccs.Pairwise fun a b => a.time < b.time)
    else decide (ccs.Pairwise fun a b => a.time ≤ b.time)

/-- Every certified check's challenges are drawn in order from its transcript (`chalsOk`), a WHIR sumcheck's at
increasing times, since a batch round's polynomial reads the other words squeezed with its challenge. -/
def Cert.chalsOk (c : Cert) (s : State) (os : Array (List ℕ)) : Bool :=
  c.sumchecks.all (fun sc => Bind.chalsOk s os (c.transcripts.getD sc.transcript default) false
    (sc.rounds.map RoundCert.cc)) &&
  c.odds.all (fun oc => Bind.chalsOk s os (c.transcripts.getD oc.transcript default) false [oc.lam, oc.next]) &&
  c.tops.all (fun tc => Bind.chalsOk s os (c.transcripts.getD tc.transcript default) false
    [tc.lam, tc.low, tc.high]) &&
  c.whirs.all fun wc => Bind.chalsOk s os (c.transcripts.getD wc.transcript default) true
    (wc.rounds.map (·.chal))

/-- The verdict: every rule is justified, every transcript is a chain, the unions' rows are certified, every field
equality reading a challenge is a test, some transcript marks every test's wires, the coverage entries hold, the
named sumchecks' rounds, proof-of-work checks, GKR layers, claim splits and WHIR sumchecks are certified, and their
challenges are drawn in order from the oracle's words. -/
def Cert.accepts (c : Cert) (s : State) : Bool :=
  match replayR c.calls c.relax 0 {} #[] with
  | none => false
  | some (t, os) =>
    rulesOk s c.test c.claims (fun _ => false) c.rules && c.transcripts.all (fun t => chainOk s t.blocks) &&
      c.unionsAt s t os && taintOk c.calls c.relax 0 {} #[] &&
      let ms := c.marks s
      let mr := c.marksRO s
      c.testsBound s ms && c.coversOk s os ms && c.sumchecksOk s os mr && c.pows.all (·.ok os c.calls c.relax) &&
        c.oddsOk s os mr && c.transcripts.all (fun t => rulesOk s c.test c.claims (dropOf s t) t.rulesRO) &&
        c.lateOk s os mr && c.chalsOk s os

theorem Cert.accepts_parts {c : Cert} {s : State} (h : c.accepts s = true) :
    rulesOk s c.test c.claims (fun _ => false) c.rules = true ∧ c.transcripts.all (fun t => chainOk s t.blocks) = true ∧
      c.unionsOk s = true ∧ taintOk c.calls c.relax 0 {} #[] = true ∧ c.testsBound s (c.marks s) = true ∧
      c.coversOk s c.outs (c.marks s) = true := by
  unfold Cert.accepts at h
  unfold Cert.unionsOk Cert.outs
  split at h
  · simp at h
  · rename_i t os hr
    rw [hr]
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hr, hc⟩, hu⟩, ht⟩, ⟨⟨⟨⟨⟨⟨⟨hb, hcv⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := h
    exact ⟨hr, hc, hu, ht, hb, hcv⟩

theorem Cert.accepts_rounds {c : Cert} {s : State} (h : c.accepts s = true) :
    c.sumchecksOk s c.outs (c.marksRO s) = true ∧ c.pows.all (·.ok c.outs c.calls c.relax) = true ∧
      c.oddsOk s c.outs (c.marksRO s) = true ∧
      c.transcripts.all (fun t => rulesOk s c.test c.claims (dropOf s t) t.rulesRO) = true ∧
      c.lateOk s c.outs (c.marksRO s) = true := by
  unfold Cert.accepts at h
  unfold Cert.outs
  split at h
  · simp at h
  · rename_i t os hr
    rw [hr]
    simp only [Bool.and_eq_true] at h
    exact ⟨h.2.1.1.1.1.1.2, h.2.1.1.1.1.2, h.2.1.1.1.2, h.2.1.1.2, h.2.1.2⟩

theorem Cert.accepts_chals {c : Cert} {s : State} (h : c.accepts s = true) : c.chalsOk s c.outs = true := by
  unfold Cert.accepts at h
  unfold Cert.outs
  split at h
  · simp at h
  · rename_i t os hr
    rw [hr]
    simp only [Bool.and_eq_true] at h
    exact h.2.2

/-- A node a transcript binds at time `k` is in the closure of what its first `k` blocks absorb, and of the statement
once `k` passes its last block. -/
theorem Cert.times_sound (c : Cert) (s : State) (t : Transcript) {n k : ℕ}
    (h : (c.times s t).getD n none = some k) : Closure c.rules (seedsBefore s t k) n :=
  (certifyT_sound _ _ _ _ n k h).mono seedsBy_seedsT

/-- The same for the random-oracle view's rules. -/
theorem Cert.timesRO_sound (c : Cert) (s : State) (t : Transcript) {n k : ℕ}
    (h : (c.timesRO s t).getD n none = some k) : Closure t.rulesRO (seedsBefore s t k) n :=
  (certifyT_sound _ _ _ _ n k h).mono seedsBy_seedsT

theorem seedsBy_append (a b : List (ℕ × ℕ)) (k : ℕ) : seedsBy (a ++ b) k = seedsBy a k ++ seedsBy b k := by
  simp [seedsBy]

/-- The same with `extra` seeds: a node marked at `k` is in the closure of what `k` gives and the extra seeds by `k`. -/
theorem Cert.timesX_sound (c : Cert) (s : State) (t : Transcript) (extra : List (ℕ × ℕ)) (fs : Array ℕ) {n k : ℕ}
    (h : (c.timesX s t extra fs).getD n none = some k) : Closure t.rulesRO (seedsBefore s t k ++ seedsBy extra k) n :=
  (certifyT_sound _ _ _ _ n k h).mono fun m hm => by
    rw [seedsBy_append, List.mem_append] at hm
    rcases hm with hm | hm
    · exact List.mem_append_left _ (seedsBy_seedsT _ hm)
    · exact List.mem_append_right _ hm

/-- A round's seeds include those before its challenge. -/
theorem WhirRound.seedsBefore_sub (s : State) (t : Transcript) (wr : WhirRound) :
    ∀ m ∈ seedsBefore s t wr.chal.time, m ∈ wr.seeds s t := by
  intro m hm
  cases wr with
  | fold => exact hm
  | batch => exact List.mem_append_left _ hm

/-- A passing verdict: every rule is justified, and each test's wires are bound by one transcript at a time `k`: in
the closure of what its first `k` blocks absorb, and of the statement once `k` passes its last block. -/
theorem tests_by (c : Cert) (s : State) (h : c.accepts s = true) :
    rulesOk s c.test c.claims (fun _ => false) c.rules = true ∧
    ∀ u a b, s.unions[u]? = some (a, b) → c.test u = true →
      ∃ t ∈ c.transcripts, chainOk s t.blocks = true ∧ ∃ k, bindTime (c.times s t) a b = some k ∧
        ∀ n ∈ limbs4 a ++ limbs4 b, Closure c.rules (seedsBefore s t k) n := by
  obtain ⟨hr, hc, -, -, ht, -⟩ := Cert.accepts_parts h
  simp only [Cert.testsBound, List.all_eq_true, List.mem_range] at ht hc
  refine ⟨hr, fun u a b hab htu => ?_⟩
  have hu : u < s.unions.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hab
    simp at hab
  have := ht u hu
  rw [htu, hab] at this
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Cert.marks, List.mem_map] at this
  obtain ⟨_, ⟨t, htm, rfl⟩, hk⟩ := this
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
  refine ⟨t, htm, hc t htm, k, hk, fun n hn => ?_⟩
  obtain ⟨tn, htn, hle⟩ := (latest_some _ _ _ _ hk).2 n hn
  exact (Cert.times_sound c s t htn).mono (seedsBefore_mono hle)

/-- A passing verdict: every rule is justified, and each test's wires are in the closure of one transcript's absorbed
words and the statement. -/
theorem checkbind_sound (c : Cert) (s : State) (h : c.accepts s = true) :
    rulesOk s c.test c.claims (fun _ => false) c.rules = true ∧
    ∀ u a b, s.unions[u]? = some (a, b) → c.test u = true →
      ∃ t ∈ c.transcripts, chainOk s t.blocks = true ∧
        ∀ n ∈ limbs4 a ++ limbs4 b, Closure c.rules (seedsOf s t) n := by
  obtain ⟨hr, hall⟩ := tests_by c s h
  refine ⟨hr, fun u a b hab htu => ?_⟩
  obtain ⟨t, htm, hch, k, -, hcl⟩ := hall u a b hab htu
  exact ⟨t, htm, hch, fun n hn => (hcl n hn).mono seedsBefore_seedsOf⟩


theorem rows_of_hash {c : Call} {t s : State} {outs : List ℕ} (h : c.Rows t outs) (hh : t.hash = s.hash) :
    c.Rows s outs := by
  cases c
  case hashBlock => simp only [Call.Rows] at h ⊢; rw [← hh]; exact h
  all_goals trivial

/-- The unions' parse uniqueness, from their rows: on two assignments holding every constraint but the tests whose
compressions do not collide, each union product is a function of its claim's inputs. -/
theorem unionsValid {st st' : ℕ → Fin 4 → K} {val val' : Val} (c : Cert) (s : State) (h : c.unionsOk s = true)
    (hv : Holds st s c.test val) (hv' : Holds st' s c.test val') (hcr : HashCR s val val') :
    UnionsValid c.claims val val' := by
  unfold Cert.unionsOk at h
  split at h
  · simp at h
  · rename_i t os hr
    simp only [Cert.unionsAt, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
    obtain ⟨⟨⟨hsame, hcl⟩, hall⟩, -⟩ := h
    obtain ⟨-, -, -, hfacts⟩ := replayR_sound c.calls c.relax 0 {} #[] t os inv_empty rfl (Nat.zero_le _)
      (fun j hj => absurd hj (Nat.not_lt_zero j)) hr
    have hsat : Sat st t val := sat_of_sameSat hsame hv
    have hsat' : Sat st' t val' := sat_of_sameSat hsame hv'
    have hF : Facts c.calls c.relax os st val := fun j hj hrl _ => (hfacts j hj hj).1 st val hsat hrl
    have hF' : Facts c.calls c.relax os st' val' := fun j hj hrl _ => (hfacts j hj hj).1 st' val' hsat' hrl
    have hhash : t.hash = s.hash := by
      simp only [sameSat, Bool.and_eq_true, beq_iff_eq] at hsame
      exact hsame.1.1.1.2.symm
    have hR : RowsIn c.calls os s := fun j hj => rows_of_hash (hfacts j hj hj).2 hhash
    intro uc huc hin
    rw [hcl] at huc
    obtain ⟨qc, hq, rfl⟩ := Array.mem_map.mp huc
    obtain ⟨hp, hqk⟩ := hall qc hq
    exact claim_valid hF hF' hR hp hqk hcr hin

/-- On two assignments holding every constraint but the tests, under collision resistance of the compression and of
the duplex's output window, a test's wires are a function of what one transcript's first `k` blocks absorb, `k` its
binding time, and of the statement once `k` passes the transcript's last block. -/
theorem tests_determined {st st' : ℕ → Fin 4 → K} {val val' : Val} (c : Cert) (s : State) (h : c.accepts s = true)
    (hv : Holds st s c.test val) (hv' : Holds st' s c.test val') (hcr : HashCR s val val')
    (hw : WindowCR s val val') {u a b : ℕ}
    (hab : s.unions[u]? = some (a, b)) (ht : c.test u = true) :
    ∃ t ∈ c.transcripts, chainOk s t.blocks = true ∧ ∃ k, bindTime (c.times s t) a b = some k ∧
      ((∀ n ∈ seedsBefore s t k, nu val n = nu val' n) → val a = val' a ∧ val b = val' b) := by
  obtain ⟨hr, hall⟩ := tests_by c s h
  have hu : UnionsValid c.claims val val' := unionsValid c s (Cert.accepts_parts h).2.2.1 hv hv' hcr
  obtain ⟨t, htm, hch, k, hk, hcl⟩ := hall u a b hab ht
  refine ⟨t, htm, hch, k, hk, fun hs => ?_⟩
  have key : ∀ n ∈ limbs4 a ++ limbs4 b, nu val n = nu val' n :=
    fun n hn => closure_agree (fun i hi => rules_valid (L := fun _ => True) hr (hv.toP _) (hv'.toP _) (hcr.toP _ _)
      (hw.toP _ _) hu i hi fun _ _ => trivial) hs (hcl n hn)
  exact ⟨eq_of_limbs4 fun n hn => key n (List.mem_append_left _ hn),
    eq_of_limbs4 fun n hn => key n (List.mem_append_right _ hn)⟩

/-- An accepted certificate's tests hold every field equality reading a challenge: no field equality its replay keeps
as a constraint reads a wire the scan marks (`taintStep`: a squeeze's output, or a wire a call makes from one, but a
constant). The kept equalities are the circuit's equalities that are not tests (`Cert.unionsOk`). -/
theorem tests_cover (c : Cert) (s : State) (h : c.accepts s = true) :
    ∀ j < c.calls.size, (c.calls.getD j .zero).isFieldEq = true → c.relax.getD j false = false →
      ∀ a ∈ (c.calls.getD j .zero).args, (taintUpTo c.calls c.relax j).2.getD a false = false := by
  intro j hj
  exact taintOk_sound c.calls c.relax 0 (Nat.zero_le _) (Cert.accepts_parts h).2.2.2.1 j (Nat.zero_le _) hj

/-- The table sumcheck as a child's verifier names it (`TableArgument::verify`): certified sumcheck `sc`, closed by a
residual and reading every round with no eq weight factored out; its input claim the output of the `mul_add` call
`target`, `σ_0 + ξ σ_1` from the bus totals `tot0` and `tot1` at the batch's challenge `xi` (`target = mul_add(xi,
totals[1], totals[0])`); and the bus GKR's root `root`, read as both trees' value by a GKR first layer (a radix-four top
layer or an odd layer whose values are `[root, root]`, `gkr::verify_products`' one root for both trees) made before the
target. `checkbind` names the latest such layer from which the GKR's layers reach the table's totals (`GkrCert`). -/
structure TableCert where
  sc : ℕ
  target : ℕ
  xi : ℕ
  tot0 : ℕ
  tot1 : ℕ
  root : ℕ
  deriving Inhabited, Repr

/-- `TableCert`'s check on a certificate's parts. -/
def TableCert.okIn (tc : TableCert) (scs : Array SumcheckCert) (tops : Array TopCert) (odds : Array OddCert)
    (cs : Array Call) (rl : Array Bool) (os : Array (List ℕ)) : Bool :=
  (match scs[tc.sc]? with
    | some sc => !sc.resid.isEmpty && sc.rounds.all (fun rc => rc.weight.isNone) && o os tc.target == sc.claim0
    | none => false) &&
  callsOk cs rl [(tc.target, .mulAdd tc.xi tc.tot1 tc.tot0)] &&
  (tops.any (fun t => t.values == [tc.root, tc.root] && decide (t.claimZero < tc.target)) ||
    odds.any (fun t => t.values == [tc.root, tc.root] && decide (t.claimZero < tc.target)))

/-- `TableCert`'s check on a certificate. -/
def TableCert.ok (tc : TableCert) (c : Cert) (os : Array (List ℕ)) : Bool :=
  tc.okIn c.sumchecks c.tops c.odds c.calls c.relax os

/-- A radix-four GKR layer past the top, run as certified sumcheck `sc` (`gkr::verify_products`): a top layer's calls
(`layer`, its test unused), the sumcheck's input claim the layer's claim `Σ_t λ^t values_t` and its final side the
expected `Σ_t λ^t Π_c kids_{t,c}`. `fs` are the firings binding its values by `λ`'s time with the words squeezed with
`λ` as seeds (`LayerCert.lamOk`). -/
structure LayerCert where
  sc : ℕ
  layer : TopCert
  fs : Array ℕ := #[]
  deriving Inhabited, Repr

/-- A layer's link to the one before: its sumcheck closed by no residual, its values the previous layer's next claims `outs`, its claim and expected the sumcheck's input claim and final side, its rounds' eq weights the point `pt` the previous layer leaves, and its input claim reading no hints (the values are bound by `λ`'s time). -/
def LayerCert.linkOk (lc : LayerCert) (sc : SumcheckCert) (os : Array (List ℕ)) (outs pt : List ℕ) : Bool :=
  sc.resid.isEmpty && lc.layer.values == outs && lc.layer.claim os == sc.claim0 && lc.layer.expected os == sc.final &&
    sc.rounds.map (·.weight) == pt.map some && sc.hints.isEmpty

/-- The layers from the next claims `outs` and the point `pt` of the layer before, each linked to the one before, its
calls in the replay and over two trees; the last layer's next claims. -/
def LayerCert.chain (scs : Array SumcheckCert) (cs : Array Call) (rl : Array Bool) (os : Array (List ℕ)) :
    List LayerCert → List ℕ → List ℕ → Option (List ℕ)
  | [], outs, _ => some outs
  | lc :: rest, outs, pt => match scs[lc.sc]? with
    | some sc =>
      if lc.linkOk sc os outs pt && lc.layer.ok os cs rl && lc.layer.m == 2 then
        LayerCert.chain scs cs rl os rest ((List.range 2).map (lc.layer.out os))
          ([lc.layer.low.chal, lc.layer.high.chal] ++ sc.rounds.map (·.chal))
      else none
    | none => none

/-- A table sumcheck's bus GKR (`TableCert`): its first layer (top layer `first`, or with `odd` odd layer `first`)
reading the table's root as both trees' value, its layers past it (`LayerCert.chain` from the first layer's next claims
and point, `[low, high]` or `[r]` past an odd layer), and the table's totals each the `add` at `totAt` of a framework
share `fw` and the last layer's next claim (`bus::verify_balance`: `totals[s] = framework + values[s]`). -/
structure GkrCert where
  odd : Bool
  first : ℕ
  layers : List LayerCert
  totAt : ℕ × ℕ
  fw : ℕ × ℕ
  deriving Inhabited, Repr

/-- The first layer's values, next claims and point. -/
def GkrCert.start (g : GkrCert) (tops : Array TopCert) (odds : Array OddCert) (os : Array (List ℕ)) :
    List ℕ × List ℕ × List ℕ :=
  if g.odd then
    let oc := odds.getD g.first default
    (oc.values, (List.range 2).map (oc.out os), [oc.next.chal])
  else
    let t := tops.getD g.first default
    (t.values, (List.range 2).map (t.out os), [t.low.chal, t.high.chal])

/-- `GkrCert`'s check for table sumcheck `tc` on a certificate's parts. -/
def GkrCert.okIn (g : GkrCert) (tc : TableCert) (scs : Array SumcheckCert) (tops : Array TopCert)
    (odds : Array OddCert) (cs : Array Call) (rl : Array Bool) (os : Array (List ℕ)) : Bool :=
  decide (g.first < if g.odd then odds.size else tops.size) &&
  (g.start tops odds os).1 == [tc.root, tc.root] &&
  match LayerCert.chain scs cs rl os g.layers (g.start tops odds os).2.1 (g.start tops odds os).2.2 with
  | some [v0, v1] =>
    callsOk cs rl [(g.totAt.1, .add g.fw.1 v0), (g.totAt.2, .add g.fw.2 v1)] && o os g.totAt.1 == tc.tot0 &&
      o os g.totAt.2 == tc.tot1
  | _ => false

/-- `GkrCert`'s check on a certificate. -/
def GkrCert.ok (g : GkrCert) (tc : TableCert) (c : Cert) (os : Array (List ℕ)) : Bool :=
  g.okIn tc c.sumchecks c.tops c.odds c.calls c.relax os

/-- A layer's children bound by `low`'s time, in a transcript's times. -/
def LayerCert.boundOk (times : Array (Option ℕ)) (lc : LayerCert) : Bool :=
  boundBy times ((List.range lc.layer.m).flatMap fun k => (List.range 4).map (lc.layer.kid k)) lc.layer.low.time

/-- A layer's values bound by `λ`'s time with the words squeezed with `λ` but its own as seeds at that time, by the
firings `fs` (`Cert.whirBound`'s batch rounds). Its values, the previous layer's next claims, read the previous layer's
`high`, squeezed from the chaining value `λ` is squeezed from: words independent of `λ`'s own. -/
def LayerCert.lamOk (c : Cert) (s : State) (os : Array (List ℕ)) (t : Transcript) (lc : LayerCert) : Bool :=
  boundBy (c.timesX s t ((sibSeeds s t lc.layer.lam.time (lc.layer.lam.own os)).map (lc.layer.lam.time, ·)) lc.fs)
    lc.layer.values lc.layer.lam.time

/-- A layer's challenges as a top layer's (`Cert.topsOk`, `Cert.chalsOk`): `λ`, `low` and `high` drawn in order from
its transcript, its values bound by `λ`'s time with the words squeezed with `λ` (`LayerCert.lamOk`) and its children by
`low`'s, in the random-oracle view. -/
def LayerCert.chalOk (c : Cert) (s : State) (os : Array (List ℕ)) (lc : LayerCert) : Bool :=
  let t := (c.marksRO s).getD lc.layer.transcript default
  lc.layer.transcript < (c.marksRO s).length &&
    chalsOk s os (c.transcripts.getD lc.layer.transcript default) false [lc.layer.lam, lc.layer.low, lc.layer.high] &&
    lc.layer.lam.ok s os c.calls t.1.blocks && lc.layer.low.ok s os c.calls t.1.blocks &&
    lc.layer.high.ok s os c.calls t.1.blocks && lc.boundOk t.2 && lc.lamOk c s os t.1

/-- Every layer of a `GkrCert` draws its challenges as `LayerCert.chalOk` says. -/
def GkrCert.layersOk (g : GkrCert) (c : Cert) (s : State) (os : Array (List ℕ)) : Bool :=
  g.layers.all (·.chalOk c s os)

end LeanVMCircuits.Rec.Bind
