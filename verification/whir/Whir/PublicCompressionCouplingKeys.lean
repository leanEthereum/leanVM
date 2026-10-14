import Whir.PublicCompressionCouplingRecognition

/-! Raw message/template equality determines the entire actual seed-table tree.
This uses the retained chosen seed CV, not a fixed-CV observer restriction. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame

 theorem node_fields_equal {n m : Node} (cv : n.cv=m.cv) (block : n.block=m.block)
    (tweak : n.tweak=m.tweak) (last : n.last=m.last) : n=m := by
  cases n
  cases m
  simp_all

 theorem tree_key_unique {c : Compression} {a b : Digest32} {ns ms : List Node}
    (left : Tree c a ns) (right : Tree c b ms)
    (message : ns.map payload = ms.map payload)
    (template : ns.map (fun n => (n.tweak,n.last)) = ms.map (fun n => (n.tweak,n.last))) :
    ns=ms ∧ a=b := by
  induction left generalizing b ms with
  | seed n hn =>
    cases right with
    | seed m hm =>
      have hm' : payload n=payload m := by simpa using message
      have ht : (n.tweak,n.last)=(m.tweak,m.last) := by simpa using template
      have hp : n.cv=m.cv ∧ n.block=m.block := by
        simpa only [payload,hn,hm,↓reduceIte,Prod.mk.injEq,Option.some.injEq] using hm'
      have eq := node_fields_equal hp.1 hp.2 (congrArg Prod.fst ht) (congrArg Prod.snd ht)
      subst m
      exact ⟨rfl,rfl⟩
    | step m rest hm child =>
      have length := congrArg List.length message
      have nonempty := body_nonempty child.body
      simp only [List.length_map,List.length_cons,List.length_nil] at length
      cases rest with
      | nil => exact False.elim (nonempty rfl)
      | cons head tail => simp only [List.length_cons] at length; omega
  | step n rest hn child ih =>
    cases right with
    | seed m hm =>
      have length := congrArg List.length message
      have nonempty := body_nonempty child.body
      simp only [List.length_map,List.length_cons,List.length_nil] at length
      cases rest with
      | nil => exact False.elim (nonempty rfl)
      | cons head tail => simp only [List.length_cons] at length; omega
    | step m rest' hm child' =>
      simp only [List.map_cons,List.cons.injEq] at message template
      obtain ⟨tails,cv⟩ := ih child' message.2 template.2
      have block := congrArg Prod.snd message.1
      have eq := node_fields_equal cv block (congrArg Prod.fst template.1)
        (congrArg Prod.snd template.1)
      subst m
      subst rest'
      exact ⟨rfl,rfl⟩

 theorem complete_key_unique {c : Compression} {n m : Node} {ns ms : List Node}
    (left : Complete (n::ns)) (right : Complete (m::ms))
    (leftTree : Tree c n.cv ns) (rightTree : Tree c m.cv ms)
    (key : extract (n::ns)=extract (m::ms)) : n=m ∧ ns=ms := by
  have leftParsed := (complete?_correct _).mpr left
  have rightParsed := (complete?_correct _).mpr right
  simp only [extract,leftParsed,rightParsed,↓reduceIte,Option.some.injEq] at key
  have message := congrArg Extracted.message key
  have template := congrArg Extracted.template key
  simp only [List.map_cons,List.cons.injEq] at message template
  obtain ⟨tails,cv⟩ := tree_key_unique leftTree rightTree message.2 template.2
  exact ⟨node_fields_equal cv (congrArg Prod.snd message.1)
    (congrArg Prod.fst template.1) (congrArg Prod.snd template.1),tails⟩

#print axioms tree_key_unique
#print axioms complete_key_unique
end Whir.PublicCompressionCouplingRecognition
