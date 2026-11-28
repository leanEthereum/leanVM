module

public import LeanVM.Guest.CoreMode.CertAssemble
public import LeanVM.Guest.CoreMode.ListLit
public import LeanVM.Guest.CoreMode.SigTrie
public import LeanVM.Guest.CoreMode.Fam.TermOk
public import LeanVM.Guest.CoreMode.Fam.NzOnly

/-!
# The core route's certificates closed, the functions off it as hypotheses

A routed function's certificate comes with its facts (`CertE`: its static facts, its frame
interface the core route's `FnSpecC` at its core data, agreeing with the contracts' table, its code
the guest's, its termination facts a loop helper's `TermOk`, its residuals listed parameters' nonzero values, `Res.NzOnly`). A function off the route is named by its signature `G` (its entry `G.pc`) and stands
for a certificate `offK G` with the facts its callers and `ModeCerts` read (`OffCert`), its frame
interface among them: the hypothesis, until it is on the route. `assemble`: the routed certificates
and the off ones are closed (`ModeCerts`), each meets its frame interface (`FnSpec`), `main`'s starts
as the prologue leaves it (`MainOk`) with no contract.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode

@[expose] public section

/-- **A routed function's certificate `K` with its core data `cf`** and its facts: its static
facts, its frame interface the core route's at `cf` (agreeing with the table `tab`), its code. -/
structure CertE (tab : List CoreMode.HcEnt) where
  K : Mode.Cert
  cf : CoreMode.CFun
  st : CertSt K
  entry : cf.frame.entry = K.F.entry
  spec : FnSpecC K cf
  ct : CoreMode.ctB tab K cf = true
  fn : FnLink K
  term : TermOk K
  res : Res.NzOnly CoreMode.FnReg.nzs K

/-- **A function off the route**, of signature `G`: a certificate at its entry, of its signature,
not `main`'s, with its static facts and code, its callee signatures among `Ks`, and its frame
interface at the table `tab` and core data `T`. -/
structure OffCert (tab : List CoreMode.HcEnt) (T : List CoreMode.CFun) (Ks : List Mode.Cert) (G : Sig)
    (K : Mode.Cert) : Prop where
  entry : K.F.entry = G.pc
  sig : K.F.sig = G
  main : K.F.main = false
  st : CertSt K
  fn : FnLink K
  sigs : SigsIn Ks K
  spec : FnSpec tab T K
  term : TermOk K
  res : Res.NzOnly CoreMode.FnReg.nzs K

variable {tab : List CoreMode.HcEnt}

/-- The routed certificates `ls`, then those of the functions `offs` off the route. -/
abbrev certsOf (ls : List (List (CertE tab))) (offs : List Sig) (offK : Sig → Mode.Cert) : List Mode.Cert :=
  ls.flatten.map (·.K) ++ offs.map offK

/-- The routed core data, then the off functions' `Toff`. -/
abbrev tableOf (ls : List (List (CertE tab))) (Toff : List CoreMode.CFun) : List CoreMode.CFun :=
  ls.flatten.map (·.cf) ++ Toff

/-- The off functions' hypothesis: each one's certificate with its facts. -/
def OffOk (ls : List (List (CertE tab))) (offs : List Sig) (offK : Sig → Mode.Cert)
    (Toff : List CoreMode.CFun) : Prop :=
  ∀ G ∈ offs, OffCert tab (tableOf ls Toff) (certsOf ls offs offK) G (offK G)

/-- A routed certificate is among the certificates. -/
theorem CertE.mem {ls : List (List (CertE tab))} {offs : List Sig} {offK : Sig → Mode.Cert}
    {l : List (CertE tab)} (e : CertE tab) (hl : l ∈ ls) (he : e ∈ l) : e.K ∈ certsOf ls offs offK :=
  List.mem_append_left _ (List.mem_map_of_mem (List.mem_flatten.2 ⟨l, hl, he⟩))

/-- **An off callee's signature is a certificate's**, by the hypothesis. -/
theorem sigIn_off {ls : List (List (CertE tab))} {offs : List Sig} {offK : Sig → Mode.Cert}
    {Toff : List CoreMode.CFun} (h : OffOk ls offs offK Toff) {G : Sig} (hG : G ∈ offs) :
    SigIn (certsOf ls offs offK) (G.pc, G) :=
  ⟨offK G, List.mem_append_right _ (List.mem_map_of_mem hG), (h G hG).entry, (h G hG).sig, (h G hG).main⟩

/-- **The certificates closed and their frame interfaces**, the off functions' from the hypothesis:
`ModeCerts`, `FnSpec` of each, `main`'s start and its contract none. -/
theorem assemble (ls : List (List (CertE tab))) (offs : List Sig) (offK : Sig → Mode.Cert)
    (Toff : List CoreMode.CFun) (hoff : OffOk ls offs offK Toff)
    (sigs : ∀ l ∈ ls, ∀ e ∈ l, SigsIn (certsOf ls offs offK) e.K)
    (nodup : nodupB (ls.flatten.map (·.K.F.entry) ++ offs.map (·.pc)) 0 = true) {Km : Mode.Cert}
    (main : Km ∈ ls.flatten.map (·.K)) (mainF : Km.F.main = true) (mainR : Km.code.all (fun i ↦ !isRet i) = true)
    (mainT : Km.F.sig.term = []) (mainC : CoreMode.hcNone tab Km.F.entry = true)
    (mainS : mainSigB Km.F.sig = true) (mainE : Km.F.entry = proLen) :
    ModeCerts (certsOf ls offs offK) Km guestE0 ∧
      (∀ K ∈ certsOf ls offs offK, FnSpec tab (tableOf ls Toff) K) ∧ MainOk Km guestE0 ∧
      CoreMode.hcNone tab Km.F.entry = true ∧ ∀ K ∈ certsOf ls offs offK, K.F.entry ≠ 0 := by
  have hall : ∀ K ∈ certsOf ls offs offK, (∃ l ∈ ls, ∃ e ∈ l, e.K = K) ∨ ∃ G ∈ offs, offK G = K := by
    intro K hK
    rcases List.mem_append.1 hK with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      obtain ⟨l, hl, he⟩ := List.mem_flatten.1 he
      exact .inl ⟨l, hl, e, he, rfl⟩
    · obtain ⟨G, hG, rfl⟩ := List.mem_map.1 h
      exact .inr ⟨G, hG, rfl⟩
  have hent : (certsOf ls offs offK).map (·.F.entry) = ls.flatten.map (·.K.F.entry) ++ offs.map (·.pc) := by
    simp only [List.map_append, List.map_map]
    congr 1
    exact List.map_congr_left fun G hG ↦ (hoff G hG).entry
  have hst : ∀ K ∈ certsOf ls offs offK, CertSt K := by
    intro K hK
    rcases hall K hK with ⟨l, hl, e, he, rfl⟩ | ⟨G, hG, rfl⟩
    · exact e.st
    · exact (hoff G hG).st
  refine ⟨modeCerts_of hst ?_ ?_ (hent ▸ nodup) (List.mem_append_left _ main) mainF mainR mainT, ?_,
    mainOk_guest mainS mainE, mainC, entry_ne_zero hst⟩
  · intro K hK
    rcases hall K hK with ⟨l, hl, e, he, rfl⟩ | ⟨G, hG, rfl⟩
    · exact e.fn
    · exact (hoff G hG).fn
  · intro K hK
    rcases hall K hK with ⟨l, hl, e, he, rfl⟩ | ⟨G, hG, rfl⟩
    · exact sigs l hl e he
    · exact (hoff G hG).sigs
  · intro K hK
    rcases hall K hK with ⟨l, hl, e, he, rfl⟩ | ⟨G, hG, rfl⟩
    · exact fnSpec_core (List.mem_append_left _ (List.mem_map_of_mem (List.mem_flatten.2 ⟨l, hl, he⟩)))
        e.entry e.spec e.ct
    · exact (hoff G hG).spec

/-- **Every certificate's termination facts are `TermOk`**, the off functions' from the hypothesis. -/
theorem termOk_all {ls : List (List (CertE tab))} {offs : List Sig} {offK : Sig → Mode.Cert}
    {Toff : List CoreMode.CFun} (hoff : OffOk ls offs offK Toff) : ∀ K ∈ certsOf ls offs offK, TermOk K := by
  intro K hK
  rcases List.mem_append.1 hK with h | h
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 h
    exact e.term
  · obtain ⟨G, hG, rfl⟩ := List.mem_map.1 h
    exact (hoff G hG).term

/-- **Every certificate's residuals are listed parameters' nonzero values**, the off functions' from
the hypothesis. -/
theorem nzOnly_all {ls : List (List (CertE tab))} {offs : List Sig} {offK : Sig → Mode.Cert}
    {Toff : List CoreMode.CFun} (hoff : OffOk ls offs offK Toff) :
    ∀ K ∈ certsOf ls offs offK, Res.NzOnly CoreMode.FnReg.nzs K := by
  intro K hK
  rcases List.mem_append.1 hK with h | h
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 h
    exact e.res
  · obtain ⟨G, hG, rfl⟩ := List.mem_map.1 h
    exact (hoff G hG).res

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

/-- `SigsIn` from the environment's list of callee signatures, in any order. -/
theorem sigsIn_of_list {Kc : List Mode.Cert} {K : Mode.Cert} {l : List Sig}
    (h : K.E.sigs = CoreMode.sigTrie l) (h' : ∀ G ∈ l, SigIn Kc (G.pc, G)) : SigsIn Kc K := by
  intro p hp
  rw [h] at hp
  obtain ⟨hm, he⟩ := sigTrie_entries hp
  obtain ⟨n, G⟩ := p
  simp only at hm he
  subst he
  exact h' G hm

end

end LeanVM.Guest.EndExec
