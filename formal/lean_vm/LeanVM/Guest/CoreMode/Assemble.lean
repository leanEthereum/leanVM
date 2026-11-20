/-
  LeanVM.Guest.CoreMode.Assemble

  The certificates closed from the core route's (`CoreFacts`), their residuals and termination facts
  with them.
-/

module

public import LeanVM.Guest.CoreMode.CertAssemble
public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.ListLit
public import LeanVM.Guest.CoreMode.SigTrie

/-!
# The core route's certificates closed

The end theorem's certificates are the core route's `Kc` (every function, its frame interface the
core route's `FnSpecC`). `CoreFacts` is what the core route's data gives of `Kc`: each one's static
facts, frame interface, code, termination facts and residuals (`NzOnly`: none but listed parameters'
nonzero values), its callees' signatures among `Kc`, no entry twice, `main` among them. `assemble`
closes `Kc` (`ModeCerts`) with the residuals (`ResTop`) and termination facts (`TermNode`) the end
theorem's assembly takes.
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

/-- An entry of a trie is its value at that key. -/
theorem trie_get_of_mem_entries {α : Type} :
    ∀ {t : Exec.Trie α} {n : ℕ} {a : α}, (n, a) ∈ t.entries → t.get n = some a
  | .nil, _, _, h => by simp [Exec.Trie.entries] at h
  | .node v l r, n, a, h => by
    rw [Exec.Trie.get_node]
    simp only [Exec.Trie.entries, List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨⟨m, b⟩, hm, he⟩) | ⟨⟨m, b⟩, hm, he⟩
    · cases v with
      | none => simp at h
      | some w =>
        simp only [Option.toList_some, Option.map_some, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h0 : 2 * m + 1 ≠ 0 := by omega
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      simp only [h0, h1, ↓reduceIte, show (2 * m + 1) / 2 = m by omega]
      exact trie_get_of_mem_entries hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h0 : 2 * m + 2 ≠ 0 := by omega
      have h1 : ¬ (2 * m + 2) % 2 = 1 := by omega
      simp only [h0, h1, ↓reduceIte, show (2 * m + 2) / 2 - 1 = m by omega]
      exact trie_get_of_mem_entries hm

theorem foldl_sigTrie_get : ∀ {l : List Sig} {t : Exec.Trie Sig} {n : ℕ} {a : Sig},
    (l.foldl (fun t G ↦ t.set G CoreMode.sigDepth G.pc) t).get n = some a → (a ∈ l ∧ n = a.pc) ∨ t.get n = some a
  | [], _, _, _, h => Or.inr h
  | G :: l, t, n, a, h => by
    rcases foldl_sigTrie_get (l := l) h with ⟨hm, hn⟩ | h'
    · exact Or.inl ⟨List.mem_cons_of_mem _ hm, hn⟩
    · rcases Exec.Trie.get_set h' with ⟨rfl, rfl⟩ | h''
      · exact Or.inl ⟨List.mem_cons_self, rfl⟩
      · exact Or.inr h''

/-- **A signature trie's entries are its list's signatures, each at its entry.** -/
theorem sigTrie_entries {l : List Sig} {p : ℕ × Sig} (h : p ∈ (CoreMode.sigTrie l).entries) :
    p.2 ∈ l ∧ p.1 = p.2.pc := by
  rcases foldl_sigTrie_get (trie_get_of_mem_entries h) with h' | h'
  · exact h'
  · simp at h'

/-- `SigsIn` from the environment's list of callee signatures (`CoreMode.envOf l`), in any order. -/
theorem sigsIn_of_list {Kc : List Mode.Cert} {K : Mode.Cert} {l : List Sig}
    (h : K.E.sigs = CoreMode.sigTrie l) (h' : ∀ G ∈ l, SigIn Kc (G.pc, G)) : SigsIn Kc K := by
  intro p hp
  rw [h] at hp
  obtain ⟨hm, he⟩ := sigTrie_entries hp
  obtain ⟨n, G⟩ := p
  simp only at hm he
  subst he
  exact h' G hm

/-- **What the core route's data gives of its certificates `Kc`**, at its core data `T`, the
residuals' listed parameters `nzs` and `main`'s `Km`. -/
structure CoreFacts (tab : List CoreMode.HcEnt) (Kc : List Mode.Cert) (T : List CoreMode.CFun) (nzs : List (String × V))
    (Km : Mode.Cert) : Prop where
  table : ∀ Cf ∈ T, CoreMode.CfOk Cf
  st : ∀ K ∈ Kc, CertSt K
  spec : ∀ K ∈ Kc, FnSpec tab T K
  fn : ∀ K ∈ Kc, FnLink K
  sigs : ∀ K ∈ Kc, SigsIn Kc K
  term : ∀ K ∈ Kc, TermOk K
  res : ∀ K ∈ Kc, NzOnly nzs K
  nzs : ∀ p ∈ nzs, NzVal p.1 p.2
  nodup : nodupB (Kc.map (·.F.entry)) 0 = true
  main : Km ∈ Kc
  mainF : Km.F.main = true
  mainR : Km.code.all (fun i ↦ !isRet i) = true
  mainT : Km.F.sig.term = []
  mainC : CoreMode.hcNone tab Km.F.entry = true

/-- **The certificates closed**, with their residuals and termination facts and no entry `__jump_tables`'s. -/
theorem assemble {tab : List CoreMode.HcEnt} {Kc : List Mode.Cert} {T : List CoreMode.CFun} {nzs : List (String × V)}
    {Km : Mode.Cert} {A : String → FnAl} (hc : CoreFacts tab Kc T nzs Km) :
    ModeCerts Kc Km guestE0 ∧ (∀ K ∈ Kc, K.F.entry ≠ 0) ∧ ResTop Kc A ∧ TermNode Kc :=
  ⟨modeCerts_of hc.table hc.st hc.spec hc.fn hc.sigs hc.nodup hc.main hc.mainF hc.mainR hc.mainT hc.mainC,
    entry_ne_zero hc.st, resTop_nzOnly hc.res hc.nzs, termNode_of hc.term⟩


/-! ## The core route's certificates with their facts -/

/-- **A routed function's certificate `K` with its core data `cf`** and the facts `CoreFacts` takes of
each: its core data the deployed guest's, its static facts, its frame interface the core route's at
`cf` (agreeing with the table `tab`), its code, its termination facts and its residuals. -/
structure CertE (tab : List CoreMode.HcEnt) (nzs : List (String × V)) where
  K : Mode.Cert
  cf : CoreMode.CFun
  ok : CoreMode.CfOk cf
  st : CertSt K
  entry : cf.frame.entry = K.F.entry
  spec : FnSpecC K cf
  ct : CoreMode.ctB tab K cf = true
  fn : FnLink K
  term : TermOk K
  nz : NzOnly nzs K

/-- A fact of each certificate of a list of lists of `CertE`s, list by list. -/
theorem CertE.fa {tab : List CoreMode.HcEnt} {nzs : List (String × V)} {P : Mode.Cert → Prop}
    {ls : List (List (CertE tab nzs))} (h : ∀ l ∈ ls, ∀ e ∈ l, P e.K) : ∀ K ∈ ls.flatten.map (·.K), P K := by
  intro K hK
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hK
  obtain ⟨l, hl, he⟩ := List.mem_flatten.1 he
  exact h l hl e he

/-- A certificate of one of the lists is among the certificates. -/
theorem CertE.mem {tab : List CoreMode.HcEnt} {nzs : List (String × V)} {ls : List (List (CertE tab nzs))}
    {l : List (CertE tab nzs)} (e : CertE tab nzs) (hl : l ∈ ls) (he : e ∈ l) : e.K ∈ ls.flatten.map (·.K) :=
  List.mem_map_of_mem (List.mem_flatten.2 ⟨l, hl, he⟩)

/-- **What the core route's data gives of its certificates** `ls`, list by list: their facts, with
their callees' signatures, no entry twice and `main` among them. -/
theorem CoreFacts.of {tab : List CoreMode.HcEnt} {nzs : List (String × V)} {Km : Mode.Cert}
    (ls : List (List (CertE tab nzs)))
    (sigs : ∀ K ∈ ls.flatten.map (·.K), SigsIn (ls.flatten.map (·.K)) K)
    (nzs_ok : ∀ p ∈ nzs, NzVal p.1 p.2) (nodup : nodupB ((ls.flatten.map (·.K)).map (·.F.entry)) 0 = true)
    (main : Km ∈ ls.flatten.map (·.K)) (mainF : Km.F.main = true) (mainR : Km.code.all (fun i ↦ !isRet i) = true)
    (mainT : Km.F.sig.term = []) (mainC : CoreMode.hcNone tab Km.F.entry = true) :
    CoreFacts tab (ls.flatten.map (·.K)) (ls.flatten.map (·.cf)) nzs Km := by
  have fa {P : Mode.Cert → Prop} (h : ∀ e : CertE tab nzs, P e.K) : ∀ K ∈ ls.flatten.map (·.K), P K := by
    intro K hK
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hK
    exact h e
  refine ⟨?_, fa (·.st), ?_, fa (·.fn), sigs, fa (·.term), fa (·.nz), nzs_ok, nodup, main, mainF, mainR, mainT, mainC⟩
  · intro Cf hCf
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hCf
    exact e.ok
  · intro K hK
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hK
    exact fnSpec_core (List.mem_map_of_mem he) e.entry e.spec e.ct

end

end LeanVM.Guest.EndExec
