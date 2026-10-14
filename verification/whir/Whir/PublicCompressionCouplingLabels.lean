import Whir.PublicCompressionCouplingTerminalUnique
import Whir.WHIRRealSimulator

/-! A raw terminal coordinate has a deterministic full primitive-node label
from its actual seed body. This preserves chosen root CVs and all raw fields. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed

/-- Terminal-first raw evaluation's first full primitive input. Malformed raw
names are totalized, but no protocol recognition rule is changed. -/
def terminalLabel {Q : Nat} (seedTable : Seed) (key : RawKey Q) : Node :=
  match (expandKey key).message,(expandKey key).template with
  | (leaf,block)::message,(tweak,last)::template =>
      ⟨leaf.getD (WHIRRealSimulator.evalRaw seedTable message template),block,tweak,last⟩
  | _,_ => ⟨zeroDigest,(fun _ => 0),0,false⟩

def coordinateLabel {Q : Nat} (seedTable : Seed) : Key Q → Node
  | .inl node => node
  | .inr key => terminalLabel seedTable key

 theorem terminalNode_cv (cv : Digest32) (terminal : Terminal) :
    (terminalNode cv terminal).cv = cv := by
  cases terminal <;> rfl

 theorem terminalLabel_witness {Q : Nat} {seedTable : Seed} {input : Node} {key : RawKey Q}
    (witness : CoordinateWitness Q seedTable input (.inr key)) :
    terminalLabel seedTable key = input := by
  cases witness with
  | terminal key rest complete tree extracted =>
    have parsed := (complete?_correct _).mpr complete
    have terminal : isTerminal input := by
      simp only [complete?,Bool.and_eq_true,decide_eq_true_eq] at parsed
      exact parsed.1
    have nonseed := terminal_not_seed terminal
    have fields : expandKey key =
        ⟨(input::rest).map payload,(input::rest).map (fun n => (n.tweak,n.last))⟩ := by
      simpa only [extract,(complete?_correct _).mpr complete,↓reduceIte,Option.some.injEq] using extracted.symm
    simp only [terminalLabel,fields,List.map_cons,payload,nonseed,↓reduceIte,
      Option.getD_none,WHIRRealSimulator.evalRaw_tree seedTable tree]

 theorem terminalLabel_same_key {Q : Nat} {seedTable : Seed} {a b : Node} {key : RawKey Q}
    (left : CoordinateWitness Q seedTable a (.inr key))
    (right : CoordinateWitness Q seedTable b (.inr key)) : a=b :=
  (terminalLabel_witness left).symm.trans (terminalLabel_witness right)

#print axioms terminalLabel_witness
end Whir.PublicCompressionCouplingRecognition
