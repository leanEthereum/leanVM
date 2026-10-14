import Whir.SpongefishCurrentAnchorHeader

/-! Successful current commitment receive: capture the actual preheader state,
read the guarded raw-root header, sample the complete anchor vector, read its
advertised value, and retain one immutable record. This hand-port does not model
Rust error identity/poisoning, prove Rows constraints, or assert uniformity. -/
namespace Whir.SpongefishCurrentCommitmentReceive
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishSessionAdapter SpongefishPCSRoundFrames SpongefishRecordBindingParser
set_option autoImplicit false

/-- The point and saved context are computed by the source operations, not
provided as matching certificates or a caller-selected saved record. -/
def receive (c : Compression) (cur : Cursor) (shape : Shape) : Option (Cursor × Record) := do
  let (header,root) ← SpongefishCurrentAnchorHeader.readHeader c cur shape
  let (sampled,bytes) ← match squeezeGroup c header (.anchor (shape.logN-1)) with
    | .error _ => none
    | .ok value => some value
  let (point,rest) ← (vectorCodec shape.logN).parse bytes
  if rest ≠ [] then none else do
    let (next,value) ← read c sampled .scalar
    pure (next,{shape,root,context := capture cur.state,point := List.ofFn point,value})

/-- Successful source execution exposes the genuine header, sampler and scalar
read subruns. The retained record is their literal result, not an assumption. -/
theorem receive_runs (c : Compression) (cur next : Cursor) (shape : Shape) (r : Record)
    (accepted : receive c cur shape = some (next,r)) :
    ∃ header root sampled bytes, ∃ (point : Fin shape.logN → E), ∃ value,
      SpongefishCurrentAnchorHeader.readHeader c cur shape = some (header,root) ∧
      squeezeGroup c header (.anchor (shape.logN-1)) = .ok (sampled,bytes) ∧
      (vectorCodec shape.logN).parse bytes = some (point,[]) ∧
      read c sampled .scalar = some (next,value) ∧
      r = {shape,root,context := capture cur.state,point := List.ofFn point,value} := by
  unfold receive at accepted
  obtain ⟨⟨header,root⟩,readHeader,accepted⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at accepted
  cases drawn : squeezeGroup c header (.anchor (shape.logN-1)) with
  | error error => simp [drawn] at accepted
  | ok sampledBytes =>
    obtain ⟨sampled,bytes⟩ := sampledBytes
    simp only [drawn] at accepted
    change Option.bind ((vectorCodec shape.logN).parse bytes) _ = some (next,r) at accepted
    obtain ⟨⟨point,rest⟩,decoded,accepted⟩ := Option.bind_eq_some_iff.mp accepted
    dsimp only at accepted
    split at accepted
    · contradiction
    · rename_i empty
      have restEmpty : rest = [] := by simpa only [ne_eq,not_not] using empty
      subst rest
      obtain ⟨⟨after,value⟩,readValue,equal⟩ := Option.bind_eq_some_iff.mp accepted
      have same := Option.some.inj equal
      cases same
      exact ⟨header,root,sampled,bytes,point,value,readHeader,drawn,decoded,readValue,rfl⟩

/-- The entire sampled vector is retained; its canonical bytes and the actual
preheader context can be recovered from every successful result. -/
theorem receive_retains (c : Compression) (cur next : Cursor) (shape : Shape) (r : Record)
    (accepted : receive c cur shape = some (next,r)) :
    r.shape = shape ∧ r.context = capture cur.state ∧ r.point.length = shape.logN ∧
    ∃ header sampled bytes, ∃ (point : Fin shape.logN → E),
      SpongefishCurrentAnchorHeader.readHeader c cur shape = some (header,r.root) ∧
      squeezeGroup c header (.anchor (shape.logN-1)) = .ok (sampled,bytes) ∧
      bytes = (vectorCodec shape.logN).bytes point ∧ r.point = List.ofFn point ∧
      read c sampled .scalar = some (next,r.value) := by
  obtain ⟨header,root,sampled,bytes,point,value,readHeader,drawn,decoded,readValue,rfl⟩ :=
    receive_runs c cur next shape r accepted
  exact ⟨rfl,rfl,List.length_ofFn,header,sampled,bytes,point,readHeader,drawn,
    by simpa only [List.append_nil] using Codec.canonical_read (vectorCodec shape.logN) bytes [] point decoded,
    rfl,readValue⟩

private theorem squeezeGroup_source (c : Compression) (cur sampled : Cursor)
    (g : Group) (bytes : List Byte)
    (accepted : squeezeGroup c cur g = .ok (sampled,bytes)) :
    squeeze c cur.state g.bytes = .ok (sampled.state,bytes) := by
  cases actual : squeeze c cur.state g.bytes with
  | error error => simp [squeezeGroup,actual] at accepted
  | ok result =>
    obtain ⟨state,output⟩ := result
    have same : ({cur with
        state := state
        pending := draw cur.pending g.bytes
        events := cur.events ++ [.verifier output]} : Cursor) = sampled ∧ output = bytes := by
      simpa [squeezeGroup,actual] using accepted
    simp only [← same.1,← same.2]

/-- The entire actual commitment-receive operation yields its sampled point
bytes and the root-bearing raw key BEFORE those bytes are answered. The anchor
value is subsequently read from the prover, not assumed or supplied to a parser.
Prior mode representation, frame geometry and total path work remain explicit. -/
theorem receive_anchor_source {Q : Nat} (c : Compression) (iv : Digest32)
    (cur next : Cursor) (shape : Shape) (r : Record)
    (accepted : receive c cur shape = some (next,r))
    (represented : RepresentsCurrent c iv cur.pending cur.state)
    (framed : SpongefishCurrentModeQueries.FrameDomain cur.pending) :
    ∃ header sampled bytes, ∃ (point : Fin shape.logN → E),
      SpongefishCurrentAnchorHeader.readHeader c cur shape = some (header,r.root) ∧
      bytes = (vectorCodec shape.logN).bytes point ∧ r.point = List.ofFn point ∧
      read c sampled .scalar = some (next,r.value) ∧
      ∃ (squeezed : squeeze c header.state (24*shape.logN) = .ok (sampled.state,bytes)),
      ∀ (j : Nat) (within : j < 24*shape.logN)
        (work : DuplexFraming.pathCost (SpongefishCurrentModeQueries.coordinate header.pending
          ((header.pending.consumed+j)/32)) ≤ Q),
        let q := SpongefishCurrentModeQueries.coordinate header.pending ((header.pending.consumed+j)/32)
        DuplexEncoding.Admissible q ∧
          SpongefishCurrentAnchorHeader.rawHeader shape iv (constructionKey Q iv q work) = some r.root ∧
          bytes[j]'(by
            obtain ⟨_,len⟩ := squeeze_exact_cursor c header.state sampled.state (24*shape.logN) bytes squeezed
            omega) =
            evalCoordinate c iv q ⟨(header.pending.consumed+j)%32,Nat.mod_lt _ (by decide)⟩ := by
  obtain ⟨_,_,_,header,sampled,bytes,point,readHeader,drawn,encoded,pointEq,readValue⟩ :=
    receive_retains c cur next shape r accepted
  have valid := ((SpongefishCurrentAnchorHeader.readHeader_exact c cur header shape r.root).mp
    readHeader).1
  have count : (Group.anchor (shape.logN-1)).bytes = 24*shape.logN := by
    simp only [Group.bytes,Group.elements]
    have positive := valid.1
    omega
  have squeezed := squeezeGroup_source c header sampled (.anchor (shape.logN-1)) bytes drawn
  rw [count] at squeezed
  refine ⟨header,sampled,bytes,point,readHeader,encoded,pointEq,readValue,squeezed,?_⟩
  intro j within work
  exact SpongefishCurrentAnchorHeader.readHeader_anchor_byte c iv cur header shape r.root
    readHeader represented framed sampled.state bytes squeezed j within work

#print axioms receive_anchor_source

#print axioms receive_runs
#print axioms receive_retains
end Whir.SpongefishCurrentCommitmentReceive
