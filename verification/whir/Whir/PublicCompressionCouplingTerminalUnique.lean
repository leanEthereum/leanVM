import Whir.PublicCompressionCouplingCoordinates

/-! Reverse terminal-coordinate uniqueness on actual consumed seed nodes.
Together with forward full-key uniqueness, this is the injective cache graph
needed to align repeated terminal calls and construction RO coordinates. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed

 theorem expandShort_injective {α : Type} {Q : Nat} :
    Function.Injective (expandShort (α:=α) (Q:=Q)) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ equal
  have lengths : n=m := Fin.ext (by simpa only [expandShort,List.length_ofFn] using congrArg List.length equal)
  cases lengths
  have functions : f=g := List.ofFn_injective equal
  cases functions
  rfl

 theorem expandKey_injective {Q : Nat} : Function.Injective (expandKey (Q:=Q)) := by
  intro a b equal
  apply Prod.ext
  · exact expandShort_injective (congrArg Extracted.message equal)
  · exact expandShort_injective (congrArg Extracted.template equal)

 theorem Tree.output_unique {seedTable : Seed} {a b : Digest32} {ns ms : List Node}
    (left : Tree (compressionOf seedTable) a ns) (right : Tree (compressionOf seedTable) b ms)
    (same : a=b)
    (injective : ∀ n ∈ ns, ∀ m ∈ ms, seedTable n = seedTable m → n=m) : ns=ms := by
  induction left generalizing b ms with
  | seed node valid =>
    cases right with
    | seed other valid' =>
      have nodes := injective node (by simp) other (by simp) same
      subst other
      rfl
    | step other rest internal child =>
      have nodes := injective node (by simp) other (by simp) same
      subst other
      exact False.elim (seed_not_internal valid internal)
  | step node rest valid child ih =>
    cases right with
    | seed other seed =>
      have nodes := injective node (by simp) other (by simp) same
      subst other
      exact False.elim (seed_not_internal seed valid)
    | step other rest' internal child' =>
      have nodes := injective node (by simp) other (by simp) same
      subst other
      have tails := ih child' rfl (fun n hn m hm values =>
        injective n (List.mem_cons_of_mem _ hn) m (List.mem_cons_of_mem _ hm) values)
      subst rest'
      rfl

/-- A terminal's two complete seed-tree witnesses cannot allocate different
raw RO keys when the actually consumed mixed Seed cache is answer-injective. -/
 theorem terminal_rawKey_unique {Q : Nat} {seedTable : Seed} {input : Node}
    {leftKey rightKey : RawKey Q} {ns ms : List Node}
    (left : Tree (compressionOf seedTable) input.cv ns)
    (right : Tree (compressionOf seedTable) input.cv ms)
    (leftExtract : extract (input::ns) = some (expandKey leftKey))
    (rightExtract : extract (input::ms) = some (expandKey rightKey))
    (cache : Key Q → Option Digest32)
    (leftStored : ∀ n ∈ ns, cache (.inl n) = some (seedTable n))
    (rightStored : ∀ n ∈ ms, cache (.inl n) = some (seedTable n))
    (injective : ∀ a b d, cache a=some d → cache b=some d → a=b) : leftKey=rightKey := by
  have trees := Tree.output_unique left right rfl (by
    intro n hn m hm values
    have keys := injective (.inl n) (.inl m) (seedTable n) (leftStored n hn)
      (by simpa only [values] using rightStored m hm)
    exact Sum.inl.inj keys)
  subst ms
  apply expandKey_injective
  exact Option.some.inj (leftExtract.symm.trans rightExtract)

#print axioms terminal_rawKey_unique
end Whir.PublicCompressionCouplingRecognition
