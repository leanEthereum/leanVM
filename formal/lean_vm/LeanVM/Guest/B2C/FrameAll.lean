/-
  LeanVM.Guest.B2C.FrameAll

  Every running instance's frame holds what the completeness check reads (`FrameHolds`), on the
  honest memory of a placed tree of `main`.
-/

module

public import LeanVM.Guest.B2C.Frame
public import LeanVM.Guest.B2C.KFacts
public import LeanVM.Guest.B2C.Cpl
public import LeanVM.Guest.Sound

/-!
# The frames of the honest memory

`frameHolds_all`: for a placed honest tree of `main`, every node instance's frame holds the
header, its path's values, temporaries, fixed cells, frame addresses, table targets and call
sites, and its callees' frames their headers, arguments and frame pointers (`Frame`'s reads),
given that the completeness check keeps a path's call sites apart (`SitesApart`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

theorem idxOf_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : ∃ j, idxOf f = some j := by
  have h' : List.find? (fun g ↦ g.name == f) coreProgram = some fn := h
  have hany : coreProgram.any (fun g ↦ g.name == f) = true :=
    List.any_eq_true.mpr ⟨fn, List.mem_of_find?_eq_some h', List.find?_some (p := fun g : Fn ↦ g.name == f) h'⟩
  rw [← List.findIdx?_isSome] at hany
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hany
  exact ⟨i + 1, by unfold idxOf Core.Program.indexOf?; rw [hi]; rfl⟩

theorem idxOf_main : idxOf "main" = some 1 := by decide +kernel

/-- The header of the `i`-th callee, as the check reads it. -/
theorem H_eq_kidHdr {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {j : ℕ}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) (i : ℕ) : H I i = kidHdr j I.fp I.hdr es i := by
  obtain ⟨hev, -⟩ := node_path ht hj hw
  obtain ⟨n, rfl, hn, -, hf, hc, -⟩ := fn_of_idx hj
  have hl : coreProgram.loop f = (coreOf (n + 1)).loop := by
    simp only [Core.Program.loop, hf, hc]
  have hev' : (Memory.Tree.node f σ bufs kids).events coreProgram = es := ht ▸ hev
  unfold H kidHdr
  rw [ht]
  simp only [Tree.name, hj, hev', hl]
  rfl

/-- **A call site's cells hold its callee frame and target.** -/
theorem read_site {hdr : E × E} {T : Tree} {rd : Reader} {args rets : List E} {j : ℕ} {G : Glob}
    {fc : CompiledFn} {main : Bool}
    (h : Honest coreProgram fs H C hdr T rd args rets) (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G fc (coreOf j) (certOf j) main i = true)
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) (hsa : SitesApart j es)
    (i : ℕ) (c : Call) (kfp : ℕ) (s : Site) (hc : (calls es)[i]? = some c) (hp : I.kidFps[i]? = some kfp)
    (hs : siteOf j c = some s) :
    (2 ≤ s.q → s.q < fsN j → (honest coreProgram fs H C hdr T).read (gpow (I.fp + s.q)) = some (ofK (gpow kfp))) ∧
    (s.tgt ≠ 0 → 2 ≤ s.tgt → s.tgt < fsN j →
      (honest coreProgram fs H C hdr T).read (gpow (I.fp + s.tgt)) = some (ofK (gpow (entryOf c.f)))) := by
  have AP := apart_j hS
  obtain ⟨n, rfl, -, -, -, -, hfs, -⟩ := fn_of_idx hj
  have hsm := siteOf_mem hs
  have hsq : s.q ∈ siteCells (plumbOf (n + 1)) := by
    simp only [siteCells, List.mem_flatMap]; exact ⟨s, hsm, List.mem_cons_self⟩
  have hst : s.tgt ≠ 0 → s.tgt ∈ siteCells (plumbOf (n + 1)) := fun ht0 ↦ by
    have hb : Nat.beq s.tgt 0 = false := Bool.eq_false_iff.mpr fun hb ↦ ht0 (nbeq_iff.mp hb)
    simp only [siteCells, List.mem_flatMap]
    exact ⟨s, hsm, by simp [hb]⟩
  -- the call's own candidates in siteE
  have hin : ∀ x, (x = (s.q, ofK (gpow kfp)) ∨ (s.tgt ≠ 0 ∧ x = (s.tgt, ofK (gpow (entryOf c.f))))) →
      x ∈ siteE (n + 1) I es := by
    intro x hx
    obtain ⟨hi1, hc1⟩ := List.getElem?_eq_some_iff.mp hc
    obtain ⟨hi2, hp1⟩ := List.getElem?_eq_some_iff.mp hp
    simp only [siteE, List.mem_flatMap]
    refine ⟨((calls es)[i], I.kidFps[i]), List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩, ?_⟩
    simp only [hc1, hp1, hs, List.mem_cons]
    rcases hx with rfl | ⟨ht0, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (by simp [ht0])
  refine ⟨fun h2 hn ↦ ?_, fun ht0 h2 hn ↦ ?_⟩
  · have hmem : (s.q, ofK (gpow kfp)) ∈ C I := by
      rw [C_node ht hj, hfs]
      refine frameE_cell ⟨(s.q, ofK (gpow kfp)), ?_, rfl⟩ h2 hn fun x hx hxc ↦ ?_
      · obtain ⟨hev, -⟩ := node_path ht hj hw
        simp only [nodeE, List.mem_append, hev]
        exact Or.inl (Or.inl (Or.inr (by rw [← hev]; exact hev ▸ hin _ (Or.inl rfl))))
      have hx' := cand_site hS hchk ht hj hw hsq h2 hx hxc
      obtain ⟨i', c', kfp', s', hc', hp', hs', hx''⟩ := siteE_cases hx'
      by_cases hii : i' = i
      · subst hii
        rw [hc] at hc'; cases hc'
        rw [hp] at hp'; cases hp'
        rw [hs] at hs'; cases hs'
        rcases hx'' with rfl | ⟨ht0, rfl⟩
        · rfl
        · exact absurd hxc.symm (site_q_tgt AP hsm ht0)
      · rcases hx'' with rfl | ⟨ht0, rfl⟩
        · exact absurd hxc.symm (hsa i i' c c' s s' (Ne.symm hii) hc hc' hs hs').1
        · exact absurd hxc ((hsa i' i c' c s' s hii hc' hc hs' hs).2 ht0).2
    rw [gpow, pow_add]
    exact h.read_C hI hmem
  · have hmem : (s.tgt, ofK (gpow (entryOf c.f))) ∈ C I := by
      rw [C_node ht hj, hfs]
      refine frameE_cell ⟨(s.tgt, ofK (gpow (entryOf c.f))), ?_, rfl⟩ h2 hn fun x hx hxc ↦ ?_
      · obtain ⟨hev, -⟩ := node_path ht hj hw
        simp only [nodeE, List.mem_append, hev]
        exact Or.inl (Or.inl (Or.inr (by rw [← hev]; exact hev ▸ hin _ (Or.inr ⟨ht0, rfl⟩))))
      have hx' := cand_site hS hchk ht hj hw (hst ht0) h2 hx hxc
      obtain ⟨i', c', kfp', s', hc', hp', hs', hx''⟩ := siteE_cases hx'
      by_cases hii : i' = i
      · subst hii
        rw [hc] at hc'; cases hc'
        rw [hs] at hs'; cases hs'
        rcases hx'' with rfl | ⟨-, rfl⟩
        · exact absurd hxc (site_q_tgt AP hsm ht0)
        · rfl
      · rcases hx'' with rfl | ⟨ht0', rfl⟩
        · exact absurd hxc.symm ((hsa i i' c c' s s' (Ne.symm hii) hc hc' hs hs').2 ht0).2
        · exact absurd hxc.symm ((hsa i i' c c' s s' (Ne.symm hii) hc hc' hs hs').2 ht0).1
    rw [gpow, pow_add]
    exact h.read_C hI hmem

/-- A callee's instance, as the reads take it: a node on its path, or a phantom, with its
parameters' words the arguments. -/
theorem kid_shape {rd : Reader} {J : Inst} {c : Call} {σ : Val} (hn : J.t.name = c.f)
    (hv : if c.taken then J.t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
      else (∃ f σ', J.t = .phantom f σ') ∧ Phantom coreProgram J.t (c.args.map σ)) :
    ∃ jc, idxOf c.f = some jc ∧ (coreOf jc).params.map J.t.val = c.args.map σ ∧
      ((∃ σJ bufs kids es vs, J.t = .node c.f σJ bufs kids ∧ walk σJ (coreOf jc).body = .ret es vs ∧
        ∀ e ∈ es, e.Holds rd σJ) ∨ ∃ σJ, J.t = .phantom c.f σJ) := by
  split_ifs at hv
  · cases ht : J.t with
    | node g σJ bufs kids =>
      rw [ht] at hv hn
      simp only [Tree.name] at hn
      subst hn
      obtain ⟨fn, hf, hpar, es, vs, hw, -, he, -⟩ := hv
      obtain ⟨jc, hjc⟩ := idxOf_of_find hf
      obtain ⟨i, rfl, hi, hi', hf', hc, -⟩ := fn_of_idx hjc
      rw [hf'] at hf; cases hf
      refine ⟨i + 1, hjc, by rw [hc]; exact hpar, Or.inl ⟨σJ, bufs, kids, es, vs, rfl, by rw [hc]; exact hw, he⟩⟩
    | phantom g σJ => rw [ht] at hv; exact hv.elim
  · obtain ⟨⟨g, σJ, ht⟩, fn, hf, hpar⟩ := hv
    rw [ht] at hn hf hpar
    simp only [Tree.name] at hn hf
    subst hn
    obtain ⟨jc, hjc⟩ := idxOf_of_find hf
    obtain ⟨i, rfl, hi, hi', hf', hc, -⟩ := fn_of_idx hjc
    rw [hf'] at hf; cases hf
    exact ⟨i + 1, hjc, by rw [hc, ht]; exact hpar, Or.inr ⟨σJ, ht⟩⟩

/-- **Every node instance's frame holds what the completeness check reads**, the check keeping
each path's call sites apart. -/
theorem frameHolds_all (hsa : ∀ j σ es vs, 1 ≤ j → j < nFns → walk σ (coreOf j).body = .ret es vs →
      SitesApart j es) :
    ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" → HonestAt coreProgram fs H C hdr T cert rd [] [] →
      ∀ I ∈ honestInsts coreProgram fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids → ∀ j,
        idxOf f = some j → ∀ es vs, walk σ (coreOf j).body = .ret es vs →
          FrameHolds (honest coreProgram fs H C hdr T) j I.fp σ es vs I.kidFps I.hdr := by
  intro hdr rd T hT h I hI f σ bufs kids ht j hj es vs hw
  have hH := h.toHonest
  obtain ⟨n, rfl, hn0, hn1, hf, hc, hfs, hcert, h1, h2⟩ := fn_of_idx hj
  have hS := shareOk_of h1 h2
  have hchk := End.winOk_of h1 h2
  obtain ⟨es', vs', hw', he, hk⟩ := node_valid ht hj (insts_good T 0 hdr hH.valid I hI)
  rw [hw] at hw'
  obtain ⟨rfl, rfl⟩ : es = es' ∧ vs = vs' := by cases hw'; exact ⟨rfl, rfl⟩
  have hgp : ∀ a o, (honest coreProgram fs H C hdr T).read (gpow a * gpow o) =
      (honest coreProgram fs H C hdr T).read (gpow (a + o)) := fun a o ↦ by rw [gpow, gpow, gpow, pow_add]
  refine ⟨?_, ?_, fun hj1 ↦ ?_, fun v hv h2 hn ↦ read_val hH hS hchk hI ht hj hw he hv h2 hn,
    fun e he' t ht' h2 hn ↦ ?_, fun p hp h2 hn ↦ read_stat hH hS hchk hI ht hj hw he hp h2 hn,
    frame_addr h hI ht hj hw, fun a ha h2 hn ↦ read_arm hH hS hchk hI ht hj hw ha h2 hn,
    frame_len hI ht hk, fun i c kfp s hc hp hs ↦ read_site hH hS hchk hI ht hj hw (hsa _ σ es vs h1 h2 hw) i c kfp s hc hp hs,
    fun i c kfp hc hp ↦ ?_, fun hl kfp hk' ↦ frame_tail hI ht hj hl hk'⟩
  · rw [← hgp]; exact (hH.read_hdr hI).1
  · rw [← hgp]; exact (hH.read_hdr hI).2
  · refine honest_hdrK hT hI fun hm ↦ hj1 ?_
    rw [ht] at hm
    simp only [Tree.name] at hm
    subst hm
    rw [idxOf_main] at hj; exact (Option.some.inj hj).symm
  · -- a temporary of the path is one of its function's
    have hwi := walk_within (σ := σ) (coreOf (n + 1)).body
    rw [hw] at hwi
    have htl : t ∈ Stmt.tmpsList (coreOf (n + 1)).body :=
      hwi.2.1.subset (List.mem_flatMap.mpr ⟨e, he', ht'⟩)
    have htm : t ∈ coreProgram.temps f := by
      unfold Program.temps; rw [hf, ← hc]; exact htl
    exact read_tmp hH hS hchk hI ht hj hw htm h2 hn
  · obtain ⟨J, hJ, rfl, hJh, hJn, hJv⟩ := kid_inst hI ht hk hc hp
    obtain ⟨jc, hjc, hpar, hgood⟩ := kid_shape hJn hJv
    obtain ⟨m, rfl, hm0, hm00, -, -, -, -, hm1, hm2⟩ := fn_of_idx hjc
    have hSc := shareOk_of hm1 hm2
    have hchkc := End.winOk_of hm1 hm2
    have hgood' : (∃ σJ bufs kids es vs, J.t = .node c.f σJ bufs kids ∧ walk σJ (coreOf (m + 1)).body =
        .ret es vs ∧ ∀ e ∈ es, e.Holds rd σJ) ∨ ∃ σJ, J.t = .phantom c.f σJ := hgood
    refine ⟨?_, ?_, fun k hk ↦ ?_, fun o ho ↦ ?_⟩
    · rw [← hgp, ← H_eq_kidHdr ht hj hw, ← hJh]; exact (hH.read_hdr hJ).1
    · rw [← hgp, ← H_eq_kidHdr ht hj hw, ← hJh]; exact (hH.read_hdr hJ).2
    · have hlen : (coreOf (m + 1)).params.length = c.args.length := by
        have := congrArg List.length hpar; simpa using this
      have hk' : k < (coreOf (m + 1)).params.length := by omega
      rw [read_args hH hSc hchkc hJ hjc hgood' k hk']
      have := congrArg (fun l ↦ l[k]?) hpar
      simp only [List.getElem?_map, List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk,
        Option.map_some, Option.some.injEq] at this
      rw [this]
    · have ho' : o ∈ (certOf (m + 1)).facts.env.map Prod.fst := by
        unfold selfCells at ho; rw [hjc] at ho; exact ho
      exact read_self hH hSc hchkc hJ hjc hgood' ho'

end
end LeanVM.Guest.B2C
