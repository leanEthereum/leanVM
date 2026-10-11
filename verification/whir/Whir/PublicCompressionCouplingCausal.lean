import Whir.PublicCompressionCouplingInspection

/-! Source-cost-bounded causal inspection of the pinned ideal simulator. Hidden
prefix calls precede their construction's RO call, but neither their answers nor
records enter the public log. This is the actual whole-view simulator, not a new
simulator or an assumed cache correspondence. -/
namespace Whir.PublicCompressionCouplingMixed
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler

/-- The actual ideal construction, with private seed prefixes sampled before
its terminal RO coordinate. Counts charges the prefix and terminal together. -/
def causalConstruction (Q : Nat) (iv : Digest32) (coordinate : Coordinate)
    (valid : DuplexEncoding.Admissible coordinate) (budget : pathCost coordinate ≤ Q) :
    Computation Q InspectedConstruction (pathCost coordinate) :=
  Sampling.pad (n := (DuplexEncoding.plan coordinate).dropLast.length+1) (by
    have positive := DuplexRawProgram.pathCost_pos coordinate
    simp only [List.length_dropLast]
    unfold pathCost at positive ⊢
    omega)
    (Sampling.bind (bodyCalls Q iv (DuplexEncoding.plan coordinate).dropLast)
      (fun body => .draw (.inr (constructionKey Q iv coordinate budget)) (fun answer =>
        .ret ⟨coordinate,valid,answer,body.1,body.2⟩)))

 theorem causalConstruction_eval (Q : Nat) (iv : Digest32) (coordinate : Coordinate)
    (valid : DuplexEncoding.Admissible coordinate) (budget : pathCost coordinate ≤ Q)
    (table : Key Q → Digest32) :
    Sampling.eval table (causalConstruction Q iv coordinate valid budget) =
      let body := Sampling.eval table (bodyCalls Q iv (DuplexEncoding.plan coordinate).dropLast)
      ⟨coordinate,valid,table (.inr (constructionKey Q iv coordinate budget)),body.1,body.2⟩ := by
  simp only [causalConstruction,Sampling.eval_pad,Sampling.eval_bind,Sampling.eval]

/-- Every construction's hidden calls occur at its causal position. The sole
state passed between public calls remains the pinned public primitive log. -/
def causalCompile (Q : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog) :
    (p : Program R) → (remaining : Nat) → remaining ≤ Q → Counts remaining p →
      Computation Q (View R × List InspectedConstruction) remaining
  | .done result, _, _, _ => .ret (⟨[],result⟩,[])
  | .ask (.primitive purpose input) next, remaining, cap, counted =>
      Sampling.pad (n := 1+(remaining-1)) (m := remaining)
        (by have hc : 1 ≤ remaining := counted.1; omega)
        (Sampling.bind (primitiveCalls Q log input) (fun result =>
          Computation.map (fun rest =>
            (DuplexRawProgram.observe (.primitive purpose input) result.2 rest.1,rest.2))
            (causalCompile Q iv result.1 (next result.2) (remaining-1)
              (by omega) (counted.2 _))))
  | .ask (.construction coordinate valid) next, remaining, cap, counted =>
      Sampling.pad (n := pathCost coordinate+(remaining-pathCost coordinate)) (m := remaining)
        (by have hc : pathCost coordinate ≤ remaining := counted.1; omega)
        (Sampling.bind (causalConstruction Q iv coordinate valid (counted.1.trans cap))
          (fun construction => Computation.map (fun rest =>
            (DuplexRawProgram.observe (.construction coordinate valid) construction.advertised rest.1,
              construction::rest.2))
            (causalCompile Q iv log (next construction.advertised)
              (remaining-pathCost coordinate) (by omega) (counted.2 _))))

set_option backward.isDefEq.respectTransparency false in
/-- Exact causal/posthoc correspondence under the SAME memoized seed/RO table.
This is pointwise, including repeated queries and every adaptive continuation. -/
 theorem causalCompile_eval (Q : Nat) (iv : Digest32) (log : DuplexPublicSimulator.PublicLog)
    (p : Program R) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p)
    (table : Key Q → Digest32) :
    Sampling.eval table (causalCompile Q iv log p remaining cap counted) =
      let view := Sampling.eval table (compile Q iv log p remaining cap counted)
      (view,Sampling.eval table (inspect Q iv view.observations)) := by
  induction p generalizing log remaining with
  | done result => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      have viewEq :
          Sampling.eval table (compile Q iv log (.ask (.primitive purpose input) next)
            remaining cap counted) =
          DuplexRawProgram.observe (.primitive purpose input)
            (Sampling.eval table (primitiveCalls Q log input)).2
            (Sampling.eval table (compile Q iv
              (Sampling.eval table (primitiveCalls Q log input)).1
              (next (Sampling.eval table (primitiveCalls Q log input)).2)
              (remaining-1) (by omega) (counted.2 _))) := by
        simp only [compile,Sampling.eval_pad,Sampling.eval_bind,Computation.eval_map]
      rw [viewEq]
      dsimp only
      simp only [causalCompile,Sampling.eval_pad,Sampling.eval_bind,Computation.eval_map]
      rw [ih]
      simp only [DuplexRawProgram.observe,inspect]
    | construction coordinate valid =>
      have viewEq :
          Sampling.eval table (compile Q iv log (.ask (.construction coordinate valid) next)
            remaining cap counted) =
          DuplexRawProgram.observe (.construction coordinate valid)
            (table (.inr (constructionKey Q iv coordinate (counted.1.trans cap))))
            (Sampling.eval table (compile Q iv log
              (next (table (.inr (constructionKey Q iv coordinate (counted.1.trans cap)))))
              (remaining-pathCost coordinate) (by omega) (counted.2 _))) := by
        simp only [compile,Sampling.eval_pad,Sampling.eval,Computation.eval_map]
      rw [viewEq]
      dsimp only
      simp only [causalCompile,Sampling.eval_pad,Sampling.eval_bind,
        Computation.eval_map,causalConstruction_eval]
      rw [ih]
      simp only [DuplexRawProgram.observe,inspect,Sampling.eval_bind,Computation.eval_map]

 theorem causalCompile_public (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (seed : DuplexPublicSimulator.Seed) (ro : RawKey Q → Digest32) :
    (Sampling.eval (oracle seed ro) (causalCompile Q iv [] p Q (by rfl) counted)).1 =
      (runIdeal (DuplexPublicSimulator.simulator Q) ro iv
        ((DuplexPublicSimulator.simulator Q).initial seed) p Q (by rfl) counted).view := by
  rw [causalCompile_eval]
  exact compile_actual Q seed ro iv [] p Q (by rfl) counted

/- Executable finite-table smoke of the actual construction, with two finite
table parameters. This checks interpreter behavior, not uniform 256-bit
probabilities or concrete BLAKE2s security. -/
#eval do
  let digest (n : Nat) : Digest32 := fun _ => ⟨n % 256,Nat.mod_lt _ (by decide)⟩
  let coordinate : Coordinate := ⟨⟨digest 3,digest 4,[]⟩,.output 0⟩
  have valid : DuplexEncoding.Admissible coordinate := by
    simp [coordinate,DuplexEncoding.Admissible,DuplexEncoding.TerminalValid]
  let seedNode : Node := ⟨digest 0,
    ByteCodec.pairBytes (coordinate.history.domain,coordinate.history.statement),
    UInt64.ofNat (2^56),true⟩
  let program : Program Digest32 :=
    .ask (.construction coordinate valid) (fun _ =>
      .ask (.construction coordinate valid) Program.done)
  have counted : Counts 8 program := by
    simp [program,Counts,Query.cost,pathCost,DuplexEncoding.plan,coordinate]
  for x in List.range 4 do
    for z in List.range 4 do
      let seed : DuplexPublicSimulator.Seed := fun n =>
        if isSeed n then digest (x+1) else digest 7
      let ro : RawKey 8 → Digest32 := fun _ => digest (z+20)
      let table := oracle seed ro
      let causal := Sampling.eval table (causalCompile 8 (digest 0) [] program 8 (by omega) counted)
      let actual := runIdeal (DuplexPublicSimulator.simulator 8) ro (digest 0)
        ((DuplexPublicSimulator.simulator 8).initial seed) program 8 (by omega) counted
      unless decide (causal.1.observations.map Observation.answer =
          actual.view.observations.map Observation.answer) &&
          decide (causal.1.observations.map Observation.answer = [digest (z+20),digest (z+20)]) &&
          decide (causal.2.map InspectedConstruction.prefixEnd = [digest (x+1),digest (x+1)]) do
        throw (IO.userError "causal repeated raw construction: FAILED")
      let terminal := terminalNode (digest (x+1)) coordinate.terminal
      let initial := (DuplexPublicSimulator.simulator 8).initial seed
      let missed := runRO ro ((DuplexPublicSimulator.simulator 8).answer initial terminal)
      let late := runRO ro ((DuplexPublicSimulator.simulator 8).answer missed.1.1 seedNode)
      let cached := runRO ro ((DuplexPublicSimulator.simulator 8).answer late.1.1 terminal)
      unless missed.2 == 0 && cached.2 == 0 &&
          decide (cached.1.2 = digest 7) &&
          (DuplexPublicSimulator.recognized late.1.1.publicLog terminal).isSome &&
          (DuplexPublicSimulator.privateKey 8 late.1.1.publicLog terminal).isNone &&
          decide (late.1.2 = terminal.cv) do
        throw (IO.userError "cached missed recognition and actual late match: FAILED")
      let chosen := { seedNode with cv := digest 42 }
      let known := runRO ro ((DuplexPublicSimulator.simulator 8).answer initial chosen)
      let forward := runRO ro ((DuplexPublicSimulator.simulator 8).answer known.1.1 terminal)
      let repeated := runRO ro ((DuplexPublicSimulator.simulator 8).answer forward.1.1 terminal)
      unless forward.2 == 1 && repeated.2 == 0 &&
          decide (forward.1.2 = digest (z+20)) &&
          decide (repeated.1.2 = forward.1.2) &&
          decide ((DuplexPublicSimulator.privateKey 8 known.1.1.publicLog terminal).map
            (fun key => (expandKey key).message) =
            some [(none,terminal.block),(some (digest 42),chosen.block)]) do
        throw (IO.userError "legitimate chosen-known-CV forward probe: FAILED")
  IO.println "causal finite-table smoke: 16 actual seed/RO cases passed"

#print axioms causalCompile_eval
#print axioms causalCompile_public
end Whir.PublicCompressionCouplingMixed
