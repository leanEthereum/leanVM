import Whir.PublicCompressionCouplingCertified

/-! Hidden construction prefixes are read from the very same pinned simulator
seed table, after fixing the full public view. No inspection result reaches the
adversary. All of these actual compression queries are explicitly charged. -/
namespace Whir.PublicCompressionCouplingMixed
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler

abbrev BodyLog := List (Node × Digest32)

def bodyCalls (Q : Nat) (cv : Digest32) :
    (xs : List DuplexEncoding.Instruction) → Computation Q (Digest32 × BodyLog) xs.length
  | [] => .ret (cv,[])
  | instruction :: rest =>
    let node : Node := ⟨cv,instruction.1,instruction.2,true⟩
    .draw (.inl node) (fun answer =>
      Computation.map (fun result => (result.1,(node,answer)::result.2))
        (bodyCalls Q answer rest))

 theorem bodyCalls_eval (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (cv : Digest32) (xs : List DuplexEncoding.Instruction) :
    (Sampling.eval (oracle seed ro) (bodyCalls Q cv xs)).1 =
      evalPlan (compressionOf seed) cv xs := by
  induction xs generalizing cv with
  | nil => rfl
  | cons instruction rest ih =>
    simpa only [bodyCalls,Sampling.eval,Computation.eval_map,oracle,evalPlan,
      List.foldl_cons,compressionOf] using ih _

 theorem bodyCalls_length (Q : Nat) (table : Key Q → Digest32) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction) :
    (Sampling.eval table (bodyCalls Q cv xs)).2.length = xs.length := by
  induction xs generalizing cv with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [bodyCalls,Sampling.eval,Computation.eval_map,List.length_cons,ih]

structure InspectedConstruction where
  coordinate : Coordinate
  valid : DuplexEncoding.Admissible coordinate
  advertised : Digest32
  prefixEnd : Digest32
  prefixLog : BodyLog

def inspectionCost : List Observation → Nat
  | [] => 0
  | observation :: rest =>
    match observation.query with
    | .primitive _ _ => inspectionCost rest
    | .construction coordinate _ =>
      (DuplexEncoding.plan coordinate).dropLast.length + inspectionCost rest

def inspect (Q : Nat) (iv : Digest32) :
    (observations : List Observation) →
      Computation Q (List InspectedConstruction) (inspectionCost observations)
  | [] => .ret []
  | ⟨.primitive _ _,_⟩ :: rest => inspect Q iv rest
  | ⟨.construction coordinate valid,answer⟩ :: rest =>
    Sampling.bind (bodyCalls Q iv (DuplexEncoding.plan coordinate).dropLast)
      (fun result => Computation.map
        (fun others => ⟨coordinate,valid,answer,result.1,result.2⟩::others)
        (inspect Q iv rest))

 theorem inspectionCost_le (observations : List Observation) :
    inspectionCost observations ≤
      (observations.map (fun observation => observation.query.cost)).sum := by
  induction observations with
  | nil => rfl
  | cons observation rest ih =>
    have ih' := ih
    simp only [Query.cost] at ih'
    cases query : observation.query with
    | primitive => simp only [inspectionCost,query,List.map_cons,List.sum_cons,Query.cost]; omega
    | construction coordinate valid =>
      simp only [inspectionCost,query,List.map_cons,List.sum_cons,Query.cost,
        List.length_dropLast]
      unfold pathCost at ih' ⊢
      omega

/-- A literal finite adaptive mixed-table experiment: first execute the pinned
simulator, then inspect the actual seed-table prefixes of every construction.
The private cap follows from the proved operational postcondition. -/
def inspectedGame {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) :
    Computation Q (View R × List InspectedConstruction) (Q+Q) :=
  Sampling.bind
    (Computation.certify (compile Q iv [] p Q (by rfl) counted)
      (compile_every_viewCost Q iv [] p Q (by rfl) counted))
    (fun view => Sampling.pad
      (le_trans (inspectionCost_le view.val.observations) view.property)
      (Computation.map (fun bodies => (view.val,bodies))
        (inspect Q iv view.val.observations)))

 theorem inspectedGame_public {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) :
    (Sampling.eval (oracle seed ro) (inspectedGame Q iv p counted)).1 =
      (runIdeal (DuplexPublicSimulator.simulator Q) ro iv ⟨seed,[]⟩ p Q (by rfl) counted).view := by
  simp only [inspectedGame,Sampling.eval_bind,Sampling.eval_pad,Computation.eval_map,
    Computation.eval_certify,compile_actual]

 theorem inspectedGame_private_count {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) (table : Key Q → Digest32) :
    inspectionCost (Sampling.eval table (inspectedGame Q iv p counted)).1.observations ≤ Q := by
  simp only [inspectedGame,Sampling.eval_bind,Sampling.eval_pad,Computation.eval_map]
  exact le_trans (inspectionCost_le _) (Sampling.eval table
    (Computation.certify (compile Q iv [] p Q (by rfl) counted)
      (compile_every_viewCost Q iv [] p Q (by rfl) counted))).property

#print axioms bodyCalls_eval
#print axioms inspectedGame_public
#print axioms inspectedGame_private_count
end Whir.PublicCompressionCouplingMixed
