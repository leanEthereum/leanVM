import Whir.PublicCompressionCouplingSourceStream

/-! Executable actual-program fresh-stream checks. These finite cases are not a
proof of universal correspondence or a concrete compression security claim. -/
namespace Whir.PublicCompressionCouplingSourceStreamSmoke
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed PublicCompressionCouplingStreams PublicCompressionCouplingJoint

private def nodeDecEq (a b : Node) : Decidable (a=b) :=
  if h : a.cv=b.cv ∧ a.block=b.block ∧ a.tweak=b.tweak ∧ a.last=b.last then
    isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro equal; apply h; cases equal; exact ⟨rfl,rfl,rfl,rfl⟩)

private instance : DecidableEq Node := nodeDecEq

def smoke : IO Unit := do
  let digest (n : Nat) : Digest32 := fun _ => ⟨n % 256,Nat.mod_lt _ (by decide)⟩
  let coordinate : Coordinate := ⟨⟨digest 3,digest 4,[]⟩,.output 0⟩
  have valid : DuplexEncoding.Admissible coordinate := by
    simp [coordinate,DuplexEncoding.Admissible,DuplexEncoding.TerminalValid]
  let seedNode : Node := ⟨digest 0,ByteCodec.pairBytes (digest 3,digest 4),UInt64.ofNat (2^56),true⟩
  for x in List.range 4 do
    for z in List.range 4 do
      let terminal := terminalNode (digest (x+1)) coordinate.terminal
      let program : Program Digest32 := .ask (.construction coordinate valid) (fun answer =>
        .ask (.primitive .direct seedNode) (fun _ =>
          .ask (.primitive .verification terminal) (fun _ =>
            .ask (.construction coordinate valid) (fun repeated =>
              .ask (.primitive .auxiliary terminal) (fun _ => Program.done (if answer= repeated then answer else digest 255))))))
      have counted : Counts 8 program := by
        simp [program,Counts,Query.cost,pathCost,DuplexEncoding.plan,coordinate]
      let stream := [digest (x+1),digest (z+20),digest 99]
      let real := run (PublicCompressionProgram.compile (digest 0) program 8 counted) (fun _ => none) stream
      let ideal := run (causalCompile 8 (digest 0) [] program 8 (by omega) counted) (fun _ => none) stream
      match real,ideal with
      | some (r,rc,rr),some (s,sc,sr) =>
        unless decide (r.view.observations.map Observation.answer=s.1.observations.map Observation.answer) &&
            decide (r.view.result=s.1.result) && decide (rr=sr) && decide (rr=[digest 99]) &&
            decide (rc seedNode=some (digest (x+1))) && decide (rc terminal=some (digest (z+20))) &&
            decide (sc (.inl seedNode)=some (digest (x+1))) &&
            decide (s.1.observations.map Observation.answer=
              [digest (z+20),digest (x+1),digest (z+20),digest (z+20),digest (z+20)]) do
          throw (IO.userError "actual source stream/cache/whole-view smoke: FAILED")
      | _,_ => throw (IO.userError "actual source stream unexpectedly exhausted")
  IO.println "actual source fresh-stream smoke: 16 adaptive construction/public-recognition/repetition cases passed"

#eval smoke

end Whir.PublicCompressionCouplingSourceStreamSmoke

def main : IO Unit := Whir.PublicCompressionCouplingSourceStreamSmoke.smoke
