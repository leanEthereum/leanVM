module

public import LeanVM.Guest.EndExecRoute
public import LeanVM.Guest.EndExecTop
public import LeanVM.Guest.CoreMode.Assemble

/-!
# `ExecGaps` from the assembled certificates

`ExecGaps.ofAssembled`: on the hint bridge's references (`ExecGaps.ofRoute`), the certificates the
core route assembles (`EndExec.assemble`: the routed ones with their facts, the off ones `offK G` of
the functions `offs` with theirs, `OffOk`) give `certs`, `main`, `frame` and `ctMain`; the residuals
and termination facts are left only at the certificates carrying any (`hasRes`, `hasTerm`:
`resRef_of_sub`, `termRef_of_sub`), as statements about the honest tree (`ResTrack`, at the tree
track's frames; `TermNodeA`, at the entered honest instances), and each frame of a routed function
an honest instance (`CoreHonAll`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Prover.Exec

@[expose] public section

/-- A certificate carries residuals. -/
def hasRes (K : Cert) : Bool := match K.F.res with
  | .nil => false
  | _ => true

/-- A certificate carries termination facts. -/
def hasTerm (K : Cert) : Bool := !K.F.sig.term.isEmpty

theorem res_or_filter (Ks : List Cert) : ∀ K ∈ Ks, K.F.res = .nil ∨ K ∈ Ks.filter hasRes := by
  intro K hK
  cases h : K.F.res with
  | nil => exact .inl rfl
  | node v l r => exact .inr (List.mem_filter.2 ⟨hK, by simp [hasRes, h]⟩)

theorem term_or_filter (Ks : List Cert) : ∀ K ∈ Ks, K.F.sig.term = [] ∨ K ∈ Ks.filter hasTerm := by
  intro K hK
  cases h : K.F.sig.term with
  | nil => exact .inl rfl
  | cons a l => exact .inr (List.mem_filter.2 ⟨hK, by simp [hasTerm, h]⟩)

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop} {Ya : Ref → St → Prop}
  {tab : List CoreMode.HcEnt}

/-- **`ExecGaps` from the assembled certificates**: the core route's fields from the assembly, but
the residuals and termination facts of the certificates carrying any and each routed frame an honest
instance. -/
theorem ExecGaps.ofAssembled (ls : List (List (CertE tab))) (offs : List Sig) (offK : Sig → Cert)
    (Toff : List CoreMode.CFun) {Km : Cert}
    (hasm : ModeCerts (certsOf ls offs offK) Km guestE0 ∧
      (∀ K ∈ certsOf ls offs offK, FnSpec tab (tableOf ls Toff) K) ∧ MainOk Km guestE0 ∧
      CoreMode.hcNone tab Km.F.entry = true ∧ ∀ K ∈ certsOf ls offs offK, K.F.entry ≠ 0)
    (hH : HintHyps L D A) (hA : AllocTrack R Ya) (hRH : ∀ r, R r → RefH L (D r) r)
    (hon : CoreHonAll R (tableOf ls Toff) (certsOf ls offs offK) (XOf (YH L D A Ya)))
    (res : ResTrack L D A R ((certsOf ls offs offK).filter hasRes))
    (term : TermNodeA L D A R ((certsOf ls offs offK).filter hasTerm)) :
    ExecGaps R (certsOf ls offs offK) Km guestE0 (ctCore tab) (qCore tab (tableOf ls Toff)) (YH L D A Ya) :=
  ExecGaps.ofRoute hH hA hRH hasm.1 hasm.2.2.1 hasm.2.1 hasm.2.2.2.1 hon
    (fun r hR hr ↦ resRef_of_sub (res_or_filter _)
      (res_of_track hasm.1 (fun _ h ↦ (List.mem_filter.1 h).1) hasm.2.2.2.2 hH hRH res r hR hr))
    (termRef_of_sub (term_or_filter _)
      (term_of_nodeA hasm.1 (fun _ h ↦ (List.mem_filter.1 h).1) hasm.2.2.2.2 hH hRH term))

end

end LeanVM.Guest.EndExec
