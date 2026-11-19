/-
  LeanVM.Guest.CoreMode.Assemble

  The certificates closed from the core route's (`CoreFacts`) and the functions' off it
  (`OffFacts`), their residuals and termination facts with them.
-/

module

public import LeanVM.Guest.Mode.CertAssemble
public import LeanVM.Guest.EndExecRS

/-!
# The certificates, the core route's and the rest

The end theorem's certificates are the core route's `Kc` (each function on the route, its frame
interface the core route's `FnSpecC`) followed by the certificates `Ko` of the functions still off
it. `CoreFacts` is what the core route's data gives of `Kc`: each one's static facts, frame
interface, code, termination facts and residuals (`NzOnly`: none but listed parameters' nonzero
values), its callees' signatures among `Kc` or among `offSigs`, the callees off the route, by
entry; no entry twice; `main` among them. `OffFacts` is what the functions off the route give of
`Ko`: the same facts and that each of `offSigs` is a certificate's of `Ko`. `assemble` closes
`Kc ++ Ko` (`ModeCerts`) with the residuals (`ResTop`) and termination facts (`TermNode`) the
end theorem's assembly takes. With no function off the route, `OffFacts.nil` gives the second part
from the first alone.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf fn_of_idx)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (allV allV_get)
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Residuals: listed parameters' nonzero values -/

/-- A residual a core-route certificate may carry at function `j`: a listed parameter's nonzero
value (`Res.nzB`), or a name. -/
noncomputable def nzOnlyB (nzs : List (String × V)) (j : ℕ) : Mode.Res → Bool
  | .nz o => Res.nzB nzs j o
  | .name _ => true
  | _ => false

/-- **A certificate's residuals are listed parameters' nonzero values**: it has none, or each is,
at its function's index `j`. -/
def NzOnly (nzs : List (String × V)) (K : Mode.Cert) : Prop :=
  K.F.res = .nil ∨ ∃ j, j < nFns ∧ (fnOf j).entryPc = K.F.entry ∧ allV (fun l ↦ l.all (nzOnlyB nzs j)) K.F.res = true

theorem nzOnly_nil {nzs : List (String × V)} {K : Mode.Cert} (h : K.F.res = .nil) : NzOnly nzs K := .inl h

theorem nzOnly_of {nzs : List (String × V)} {K : Mode.Cert} {j : ℕ}
    (h : (decide (j < nFns) && (fnOf j).entryPc == K.F.entry && allV (fun l ↦ l.all (nzOnlyB nzs j)) K.F.res) = true) :
    NzOnly nzs K := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact .inr ⟨j, h.1.1, h.1.2, h.2⟩

/-- **The residuals at the honest frames** of certificates whose residuals are listed parameters'
nonzero values. -/
theorem resTop_nzOnly {Ks : List Mode.Cert} {nzs : List (String × V)} {A : String → FnAl}
    (hok : ∀ K ∈ Ks, NzOnly nzs K) (hnz : ∀ p ∈ nzs, NzVal p.1 p.2) : ResTop Ks A := by
  intro r hr K hK i hi e j t x hx hin
  rcases hok K hK with h0 | ⟨j0, hj0, hent, hall⟩
  · rw [h0] at hx
    simp [Exec.Trie.get] at hx
  obtain rfl : j = j0 := by
    obtain ⟨_, -, -, -, -, -, -, -, -, hj⟩ := fn_of_idx t.idx
    refine fnOf_entry_inj hj hj0 ?_
    have := t.entry
    simp only [entryOf, t.idx] at this
    rw [this, hent]
  cases hg : K.F.res.get i with
  | none => rw [hg] at hx; cases hx
  | some l =>
    rw [hg, Option.getD_some] at hx
    have hf := List.all_eq_true.mp (allV_get hall hg) x hx
    cases x with
    | nz o => exact nzPar_top t hr hnz hf
    | name o => exact rres_name
    | lt a b => simp [nzOnlyB] at hf
    | sub a bs => simp [nzOnlyB] at hf

/-! ## The two parts -/

theorem fa_append {α : Type} {P : α → Prop} {l₁ l₂ : List α} (h₁ : ∀ x ∈ l₁, P x) (h₂ : ∀ x ∈ l₂, P x) :
    ∀ x ∈ l₁ ++ l₂, P x := fun x hx ↦ (List.mem_append.1 hx).elim (h₁ x) (h₂ x)

theorem SigIn.left {Ks Ko : List Mode.Cert} {p : ℕ × Sig} (h : SigIn Ks p) : SigIn (Ks ++ Ko) p :=
  let ⟨K, hK, h⟩ := h; ⟨K, List.mem_append_left _ hK, h⟩

theorem SigIn.right {Ks Ko : List Mode.Cert} {p : ℕ × Sig} (h : SigIn Ko p) : SigIn (Ks ++ Ko) p :=
  let ⟨K, hK, h⟩ := h; ⟨K, List.mem_append_right _ hK, h⟩

/-- A callee signature of `K` is a certificate's of `Kc` or among `offSigs`. -/
def SigsOr (Kc : List Mode.Cert) (offSigs : List (ℕ × Sig)) (K : Mode.Cert) : Prop :=
  ∀ p ∈ K.E.sigs.entries, SigIn Kc p ∨ p ∈ offSigs

theorem sigsOr_of {Kc : List Mode.Cert} {offSigs : List (ℕ × Sig)} {K : Mode.Cert} {l : List (ℕ × Sig)}
    (h : K.E.sigs.entries = l) (h' : ∀ p ∈ l, SigIn Kc p ∨ p ∈ offSigs) : SigsOr Kc offSigs K := by
  unfold SigsOr; rw [h]; exact h'

/-- **What the core route's data gives of its certificates `Kc`**, at its core data `T`, the
residuals' listed parameters `nzs`, the callees off the route `offSigs` and `main`'s `Km`. -/
structure CoreFacts (tab : List CoreMode.HcEnt) (Kc : List Mode.Cert) (T : List CoreMode.CFun) (nzs : List (String × V))
    (offSigs : List (ℕ × Sig)) (Km : Mode.Cert) : Prop where
  table : ∀ Cf ∈ T, CoreMode.CfOk Cf
  st : ∀ K ∈ Kc, CertSt K
  spec : ∀ K ∈ Kc, FnSpec tab T K
  fn : ∀ K ∈ Kc, FnLink K
  sigs : ∀ K ∈ Kc, SigsOr Kc offSigs K
  term : ∀ K ∈ Kc, TermOk K
  res : ∀ K ∈ Kc, NzOnly nzs K
  nzs : ∀ p ∈ nzs, NzVal p.1 p.2
  nodup : nodupB (Kc.map (·.F.entry)) 0 = true
  main : Km ∈ Kc
  mainF : Km.F.main = true
  mainR : Km.code.all (fun i ↦ !isRet i) = true
  mainT : Km.F.sig.term = []
  mainC : CoreMode.hcNone tab Km.F.entry = true

/-- **What the functions off the core route give of their certificates `Ko`**, beside the core
route's `Kc`, at the residuals' alignment `A`: the same facts, and each callee off the route a
certificate's of `Ko`. -/
structure OffFacts (tab : List CoreMode.HcEnt) (Kc Ko : List Mode.Cert) (T : List CoreMode.CFun) (offSigs : List (ℕ × Sig))
    (A : String → FnAl) : Prop where
  st : ∀ K ∈ Ko, CertSt K
  spec : ∀ K ∈ Ko, FnSpec tab T K
  fn : ∀ K ∈ Ko, FnLink K
  sigs : ∀ K ∈ Ko, SigsIn (Kc ++ Ko) K
  off : ∀ p ∈ offSigs, SigIn Ko p
  nodup : nodupB ((Kc ++ Ko).map (·.F.entry)) 0 = true
  res : ResTop Ko A
  term : TermNode Ko

/-- **No function off the route**: the second part from the first. -/
theorem OffFacts.nil {tab : List CoreMode.HcEnt} {Kc : List Mode.Cert} {T : List CoreMode.CFun} {A : String → FnAl}
    (h : nodupB (Kc.map (·.F.entry)) 0 = true) : OffFacts tab Kc [] T [] A where
  st _ h := absurd h List.not_mem_nil
  spec _ h := absurd h List.not_mem_nil
  fn _ h := absurd h List.not_mem_nil
  sigs _ h := absurd h List.not_mem_nil
  off _ h := absurd h List.not_mem_nil
  nodup := by rw [List.append_nil]; exact h
  res _ _ _ h := absurd h List.not_mem_nil
  term _ _ _ h := absurd h List.not_mem_nil

/-- **The certificates closed**, the core route's and those off it, with their residuals and
termination facts and no entry `__jump_tables`'s. -/
theorem assemble {tab : List CoreMode.HcEnt} {Kc Ko : List Mode.Cert} {T : List CoreMode.CFun} {nzs : List (String × V)}
    {offSigs : List (ℕ × Sig)} {Km : Mode.Cert} {A : String → FnAl} (hc : CoreFacts tab Kc T nzs offSigs Km)
    (ho : OffFacts tab Kc Ko T offSigs A) :
    ModeCerts (Kc ++ Ko) Km guestE0 ∧ (∀ K ∈ Kc ++ Ko, K.F.entry ≠ 0) ∧ ResTop (Kc ++ Ko) A ∧
      TermNode (Kc ++ Ko) := by
  have hst := fa_append hc.st ho.st
  refine ⟨modeCerts_of hc.table hst (fa_append hc.spec ho.spec) (fa_append hc.fn ho.fn)
      (fa_append (fun K hK p hp ↦ (hc.sigs K hK p hp).elim SigIn.left fun h ↦ SigIn.right (ho.off p h)) ho.sigs)
      ho.nodup (List.mem_append_left _ hc.main) hc.mainF hc.mainR hc.mainT hc.mainC,
    entry_ne_zero hst, ?_, ?_⟩
  · intro r hr K hK
    rcases List.mem_append.1 hK with hK | hK
    · exact resTop_nzOnly (A := A) hc.res hc.nzs r hr K hK
    · exact ho.res r hr K hK
  · intro r hr K hK
    rcases List.mem_append.1 hK with hK | hK
    · exact termNode_of hc.term r hr K hK
    · exact ho.term r hr K hK

end

end LeanVM.Guest.EndExec
