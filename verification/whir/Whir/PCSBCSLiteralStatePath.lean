import Whir.PCSBCSVerifierPacketWalk

/-! Local before/after identities suffice to construct the latent restoration
path from the verifier's recorded requests. This is a path-construction lemma,
not a substitute for proving the literal source identities. -/
set_option autoImplicit false
namespace Whir.PCSBCSLiteralStatePath
open TypedOracleCompiler TypedFiatShamirGame PCSStateRestoration.Latent

universe u v w
variable {Key : Type u} {Answer : Key → Type v} {Public : Type w}

/-- All neighbouring round states agree, and the two endpoints are literal.
Every key is an actual verifier lookup, not an auxiliary oracle query. -/
theorem of_round_links (model : NodeModel Key Answer Public) (table : Table Key Answer)
    (exposed : List (Sigma Answer)) (keys : List Key) (first last : Bool)
    (recorded : ∀ key ∈ keys, (⟨key,table key⟩ : Sigma Answer) ∈ exposed)
    (links : ∀ i (hi : i + 1 < keys.length),
      after model (keys[i]'(by omega)) table = before model (keys[i+1]'hi) table)
    (initial : ∀ key, keys.head? = some key → before model key table = first)
    (terminal : ∀ key, keys.getLast? = some key → after model key table = last)
    (empty : keys = [] → first = last) : StatePath model table exposed first last := by
  induction keys generalizing first with
  | nil => simpa only [empty rfl] using (StatePath.nil (model := model) (table := table) (exposed := exposed) last)
  | cons key rest ih =>
    rw [← initial key rfl]
    apply StatePath.step key (recorded key (by simp))
    apply ih (first := after model key table)
    · intro other member
      exact recorded other (List.mem_cons_of_mem key member)
    · intro i hi
      have bound : (i+1)+1 < (key::rest).length := by
        simpa only [List.length_cons] using Nat.succ_lt_succ hi
      simpa only [List.getElem_cons_succ] using links (i+1) bound
    · intro next head
      cases rest with
      | nil => cases head
      | cons next' tail =>
        cases head
        simpa using (links 0 (by simp)) |>.symm
    · intro other final
      cases rest with
      | nil => cases final
      | cons next tail => exact terminal other (by simpa using final)
    · intro isEmpty
      subst rest
      exact terminal key rfl

#print axioms of_round_links
end Whir.PCSBCSLiteralStatePath
