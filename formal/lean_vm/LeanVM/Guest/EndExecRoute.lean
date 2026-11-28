module

public import LeanVM.Guest.EndExecH
public import LeanVM.Guest.EndExecFrame

/-!
# `ExecGaps` from the hint bridge and the core route

The hint tracks (`YH`) keep the cells the hints touch within the reference's `2^κ` (`hintsUsed_cur`),
and an instruction from a state on the reference touches no cell past them (`used_step`), so a step
keeps the memory within `2^κ`: `usedNextAll_of`, the core route's `UsedNextAll`. `ExecGaps.ofRoute`
is `ExecGaps.ofHints` with `frame` and `ctMain` from the core route (`frame_core`, `ctMain_core`):
what is left of the core route is each function's frame interface (`FnSpec`), each frame of a
function on the route an honest instance (`CoreHonAll`), the certificates (`ModeCerts`, `MainOk`),
the residuals (`ResRef`) and the termination facts (`TermRef`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Prover.Exec

@[expose] public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop} {Ya : Ref → St → Prop}

/-- **A step keeps the memory within the reference's `2^κ` cells** on the hint tracks. -/
theorem usedNextAll_of (hH : HintHyps L D A) (hA : AllocTrack R Ya) (hRH : ∀ r, R r → RefH L (D r) r) :
    UsedNextAll R (XOf (YH L D A Ya)) := fun r hR hr C hC s _ s1 _ hon hop e1 hm e ↦
  used_step hr.log hC hon.2.2 hop hm e (hintsUsed_cur hH hA hRH r hR hr C hC s s1 hon e1 hm)

/-- **`ExecGaps` from the hint bridge and the core route**, at the core route's contracts
(`ctCore tab`) and frame predicates (`qCore tab T`). -/
theorem ExecGaps.ofRoute {Ks : List Cert} {Km : Cert} {E0 : Env} {tab : List CoreMode.HcEnt}
    {T : List CoreMode.CFun} (hH : HintHyps L D A) (hA : AllocTrack R Ya) (hRH : ∀ r, R r → RefH L (D r) r)
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0) (hfn : ∀ K ∈ Ks, FnSpec tab T K)
    (hmc : CoreMode.hcNone tab Km.F.entry = true) (hon : CoreHonAll R T Ks (XOf (YH L D A Ya)))
    (res : ∀ r, R r → r.Ok → ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D A Ya) r s))
    (term : TermRef R Ks (XOf (YH L D A Ya))) :
    ExecGaps R Ks Km E0 (ctCore tab) (qCore tab T) (YH L D A Ya) :=
  ExecGaps.ofHints hH hA hRH certs main (frame_core certs hfn hon (usedNextAll_of hH hA hRH))
    (ctMain_core hmc) res term

/-! ## The residuals and termination facts, certificate by certificate -/

/-- **The residuals on the reference from the certificates carrying any**: a certificate with no
residual meets `ResRef` vacuously. -/
theorem resRef_of_sub {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ} {n : ℕ} {Ks Kr : List Cert}
    {X : St → Prop} (hsub : ∀ K ∈ Ks, K.F.res = .nil ∨ K ∈ Kr) (h : ResRef prog img n Kr X) :
    ResRef prog img n Ks X := by
  intro K hK s i hX hs hon hi hpc x hx hin
  rcases hsub K hK with h0 | hm
  · rw [h0, Exec.Trie.get_nil, Option.getD_none] at hx
    exact absurd hx List.not_mem_nil
  · exact h K hm s i hX hs hon hi hpc x hx hin

/-- **The termination facts on the reference from the certificates carrying any**: a certificate
with no termination fact meets `TermRef` vacuously. -/
theorem termRef_of_sub {R : Ref → Prop} {Ks Kt : List Cert} {X : Ref → St → Prop}
    (hsub : ∀ K ∈ Ks, K.F.sig.term = [] ∨ K ∈ Kt) (h : TermRef R Kt X) : TermRef R Ks X := by
  intro r hR hr K hK s hon hpc p hp hin
  rcases hsub K hK with h0 | hm
  · rw [h0] at hp
    exact absurd hp List.not_mem_nil
  · exact h r hR hr K hm s hon hpc p hp hin

end

end LeanVM.Guest.EndExec
