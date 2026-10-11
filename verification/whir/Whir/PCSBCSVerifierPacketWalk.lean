import Whir.PCSStateRestorationLatent

/-! The verifier suffix requests its actual source packets in protocol order.
Prior adversarial requests, repetitions and child-prefix prequeries remain in
the ordinary operational trace; no ancestor-warming program is introduced. -/
set_option autoImplicit false
namespace Whir.PCSBCSVerifierPacketWalk
open TypedOracleCompiler TypedFiatShamirGame
open PCSStateRestoration.Latent

universe u v
variable {Key : Type u} {Answer : Key → Type v}

def request : (keys : List Key) → Sampling Key Answer Unit keys.length
  | [] => .ret ()
  | key :: rest => .draw key (fun _ => request rest)

/-- This is the exact operational transcript, including repeated requests. -/
theorem execute_request (keys : List Key) (table : Table Key Answer) :
    (Sampling.execute table (request keys)).2 = keys.map (fun key => ⟨key,table key⟩) := by
  induction keys with
  | nil => rfl
  | cons key rest ih => simp only [request,Sampling.execute,List.map_cons,ih]

/-- Every verifier lookup is recorded after an arbitrary adaptive adversary
prefix. The proof does not reorder the prefix or require ancestor disclosure. -/
theorem verifier_lookup_recorded {R : Type} {Q : Nat}
    (adversary : Sampling Key Answer R Q) (keys : R → List Key) (k : Nat)
    (length : ∀ result, (keys result).length = k)
    (table : Table Key Answer) (key : Key)
    (member : key ∈ keys (Sampling.execute table adversary).1) :
    (⟨key,table key⟩ : Sigma Answer) ∈
      (Sampling.execute table (Sampling.bind adversary (fun result =>
        (Sampling.pad (by simpa only [length] using Nat.le_refl k) (request (keys result)) :
          Sampling Key Answer Unit k)))).2 := by
  rw [Sampling.execute_bind]
  apply List.mem_append_right
  simp only [Sampling.execute_pad,execute_request]
  apply List.mem_map.mpr
  exact ⟨key,by simpa only [Sampling.execute_value] using member,rfl⟩

#print axioms execute_request
#print axioms verifier_lookup_recorded
end Whir.PCSBCSVerifierPacketWalk
