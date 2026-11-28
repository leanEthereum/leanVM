/-
  LeanVM.Guest.B1.VsC.QwA

  `decode_query_windows` completes placed: its `wins` run in its frame, its stores in its caller's
  buffers, its table reads in its caller's region.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsCompleteAll
public import LeanVM.Guest.B1.VsC.LeafA
public import LeanVM.Guest.B1.VsC.LrA
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«decode_query_windows__L»

/-!
# `decode_query_windows`, placed

`decode_query_windows__L{d}_L{cd}` is a leaf with no `HeapBuf`: its `wins` run is a run of its own
frame (`frameAddr`, from the value `.n 5`), whose cells `QwCert` asks `cert` to lay out one after
another inside the frame. Placed at frame `fp`, its own words are the honest windows
(`qwRunList`) at `fp + cert name (.n 5)`, which it claims as its data; it stores the honest
positions and the pointers into that run in its caller's buffers (`Pre`), and reads the window
table at `tabs`.

* `callAtA_leafD`: `callAtA_leaf` claiming data in the leaf's own data (its frame runs too).
* `qwA_complete'`: one specialization, on the honest valuation of `qw_holds`, the archive's.
* `qwA_complete`: every deployed specialization, `QwCert` of each its hypothesis.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **A leaf completes placed** from a valuation per memory, claiming data among its own. -/
theorem callAtA_leafD {k : ℕ} {f : String} {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c : ℕ} (bufs : List ℕ) (W : Words) (hlp : coreProgram.loop f = false)
    (hW : WordsInA W (fp + 2) (fp + fs f) c (c + bufs.sum)) (hO : ∀ rd, HoldsWords rd W → Out rd)
    (h : ∀ rd, LowDef k rd → HoldsWords rd W → Pre rd → ∃ (σ : Val) (fn : Fn) (es : List Ev) (vs : List V),
      coreProgram.find? f = some fn ∧ fn.params.map σ = args ∧ walk σ fn.body = .ret es vs ∧
      vs.map σ = rets ∧ calls es = [] ∧ allocs σ es = bufs ∧ NodeAt cert (fp, c) f σ bufs es ∧
      (∀ ev ∈ es, ev.Holds rd σ) ∧
      (∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧ ((c ≤ i ∧ i < c + bufs.sum) ∨ R i)) ∧
      (∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧ ((c ≤ i ∧ i < c + bufs.sum) ∨ R i)) ∧
      (∀ i, D i → ownData cert fp c f bufs es i) ∧ Post rd (.node f σ bufs [])) :
    CallAtA fs al cert k f args rets R D Out Pre Post (fs f) fp c (c + bufs.sum) := by
  refine ⟨W, hW, by omega, hO, fun rd hl hw hp => ?_⟩
  obtain ⟨σ, fn, es, vs, hf, hpar, hwk, hret, hcalls, hbufs, hnode, hev, hlo, hhi, hD, hpost⟩ := h rd hl hw hp
  have hev' : (Memory.Tree.node f σ bufs []).events coreProgram = es := Complete.events_node hf hwk
  have hown : ∀ i, ((c ≤ i ∧ i < c + bufs.sum) ∨ R i) →
      (Memory.Tree.node f σ bufs []).DataA coreProgram fs al cert (fp, c) i ∨ R i := fun i hi => by
    rcases hi with hi | hi
    · exact Or.inl (dataA_node.mpr (Or.inl (Or.inl (bufs_cover bufs c i hi.1 hi.2))))
    · exact Or.inr hi
  refine ⟨.node f σ bufs [], rfl, ⟨fn, hf, hpar, es, vs, hwk, hret, hev, by rw [hcalls]; exact kidsValid_nil⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, hpost⟩
  · rw [Tree.BufsOk, hev', hbufs]; exact ⟨rfl, by rw [Tree.BufsOkKids]; trivial⟩
  · rw [Tree.block, hlp]; simp
  · rw [endA_node, hlp]; simp [endF_nil]
  · rw [placedA_node, hev']; exact ⟨hnode, placedKidsA_nil⟩
  · rw [loadsInA_node, hev']
    refine ⟨fun A hA => ?_, loadsInKidsA_nil⟩
    obtain ⟨i, hi, hm⟩ := hlo A hA
    exact ⟨i, hi, hown i hm⟩
  · rw [hintsIn_node, hev']
    refine ⟨fun A hA => ?_, hintsInKids_nil⟩
    obtain ⟨i, hi, hm⟩ := hhi A hA
    exact ⟨i, hi, hown i hm⟩
  · exact dataA_node.mpr (Or.inl (by rw [hev']; exact hD i hi))

/-! ## Paths of atoms -/

theorem calls_atoms (as : List Atom) : calls (as.map Ev.atom) = [] := by
  show List.filterMap Ev.call? _ = _
  rw [List.filterMap_map]; exact filterMap_callAtom as

theorem allocs_atoms {σ : Val} : ∀ as : List Atom, (∀ a ∈ as, atomAllocB a = false) → allocs σ (as.map Ev.atom) = []
  | [], _ => rfl
  | a :: as, h => by
    have ih := allocs_atoms (σ := σ) as fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha := h a List.mem_cons_self
    simp only [allocs, List.map_cons, List.filterMap_cons] at ih ⊢
    cases a with
    | hint hh => cases hh <;> simp_all [atomAllocB, Ev.alloc?]
    | _ => simpa [Ev.alloc?] using ih

theorem allocDsts_atoms : ∀ as : List Atom, (∀ a ∈ as, atomAllocB a = false) → allocDsts (as.map Ev.atom) = []
  | [], _ => rfl
  | a :: as, h => by
    have ih := allocDsts_atoms as fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha := h a List.mem_cons_self
    simp only [allocDsts, List.map_cons, List.filterMap_cons] at ih ⊢
    cases a with
    | hint hh => cases hh <;> simp_all [atomAllocB, Ev.allocDst?]
    | _ => simpa [Ev.allocDst?] using ih

theorem mem_addrs_atoms {as : List Atom} {q : V × V} (h : q ∈ addrs (as.map Ev.atom)) :
    ∃ r rs, Atom.frameAddr q.1 (r :: rs) ∈ as ∧ q.2 = r := by
  simp only [addrs, List.filterMap_map, List.mem_filterMap, Function.comp] at h
  obtain ⟨a, ha, he⟩ := h
  cases a with
  | frameAddr p run =>
    cases run with
    | nil => simp [Ev.addr?] at he
    | cons r rs =>
      simp only [Ev.addr?, Option.some.injEq] at he
      subst he
      exact ⟨r, rs, ha, rfl⟩
  | _ => simp [Ev.addr?] at he

/-! ## `decode_query_windows` -/

/-- What `decode_query_windows__L{d}_L{cd}`'s placed proof needs of the frame layout: its `wins`
run's values `5 ..< 5 + qwW` at consecutive cells past the frame's header, inside the frame. -/
def QwCert (fs : String → ℕ) (cert : String → V → ℕ) (name : String) (d cd : ℕ) : Prop :=
  2 ≤ cert name (.n 5) ∧ cert name (.n 5) + qwW d cd ≤ fs name ∧
    ∀ x < qwW d cd, cert name (.n (5 + x)) = cert name (.n 5) + x

variable (fs al cert) in
/-- What `decode_query_windows__L{d}_L{cd}`'s placed completeness gives: at frame `fp` (any
cursor `c`, where it ends), on a word `w`, the positions' buffer at `ptrAt ipos`, the pointers'
at `ptrAt iptr` and the window table at `ptrAt it` (cells of the region `R`), holding the honest
positions and the pointers into its run, its own words the honest windows at
`fp + cert name (.n 5)`, which it claims, quiet and exact. -/
def QwA (kd : ℕ) (name : String) (d cd : ℕ) : Prop :=
  ∀ (w : E) (ipos iptr it : ℕ) (R : ℕ → Prop), 7 ≤ kd →
    (∀ j < 128 / d, R (ipos + j)) → (∀ j < 128 / d, R (iptr + j)) → (∀ n < 128, R (it + n)) →
    ∀ fp c, CallAtA fs al cert kd name [w, ptrAt ipos, ptrAt iptr, ptrAt it] [] R
      (fun i => fp + cert name (.n 5) ≤ i ∧ i < fp + cert name (.n 5) + 128 / d * qwN d cd)
      (fun rd => ReadsAt rd (ptrAt (fp + cert name (.n 5))) (qwRunList d cd w))
      (fun rd => WinTabs rd (ptrAt it) ∧
        ReadsAt rd (ptrAt ipos) ((List.range (128 / d)).map fun j => eOfNat (qwPosOf d w j)) ∧
        ReadsAt rd (ptrAt iptr) ((List.range (128 / d)).map fun j => ptrAt (fp + cert name (.n 5) + j * qwN d cd)))
      PostQuiet (fs name) fp c c

theorem atoms_ret_eq (X : List Stmt) (a : Atom) (h : AllAtoms X) :
    ∃ as : List Atom, X ++ [.atom a, .ret []] = as.map Stmt.atom ++ [.ret []] :=
  ⟨atomsOf X ++ [a], by rw [List.map_append, ← eq_map_atomsOf h]; simp⟩

theorem qwBody_eq (d cd : ℕ) : ∃ as : List Atom, qwBody d cd = as.map Stmt.atom ++ [.ret []] := by
  simp only [qwBody]
  exact atoms_ret_eq _ _ (allAtoms_of_all (qwBody_atoms d cd))

/-- **`decode_query_windows` completes placed.** -/
theorem qwA_complete' {kd : ℕ} {name : String} {d cd : ℕ} (hs : QwShape d cd)
    (hq : QwIs name (qwBody d cd)) (hc : QwCert fs cert name d cd) : QwA fs al cert kd name d cd := by
  intro w ipos iptr it R hk hRp hRq hRt fp c
  obtain ⟨fn, hfind, hps, hbody⟩ := hq
  obtain ⟨hc2, hcfs, hcx⟩ := hc
  obtain ⟨as, has⟩ := qwBody_eq d cd
  have hM : 128 / d * qwN d cd ≤ qwW d cd := hs.2.2.1
  have hW1 : 1 ≤ qwW d cd := by simp only [qwW]; split_ifs <;> omega
  have hlp : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hfind, Fn.loop, hbody, has, List.reverse_append]
    rcases hr : (as.map Stmt.atom).reverse with _ | ⟨s, t⟩
    · rfl
    · have : s ∈ as.map Stmt.atom := List.mem_reverse.mp (hr ▸ List.mem_cons_self)
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp this
      rfl
  have hfa : Atom.frameAddr (.n (valf% «decode_query_windows» "s5#0")) (qwRun (qwW d cd)) ∈ as := by
    have h : Stmt.atom (.frameAddr (.n (valf% «decode_query_windows» "s5#0")) (qwRun (qwW d cd))) ∈ qwBody d cd := by
      simp [qwBody]
    rw [has] at h
    simpa using h
  have hrunM : ((V.n 5), qwW d cd) ∈ runs (as.map Ev.atom) := by
    rw [runs, List.mem_filterMap]
    refine ⟨_, List.mem_map_of_mem hfa, ?_⟩
    obtain ⟨W', hW'⟩ : ∃ W', qwW d cd = W' + 1 := ⟨qwW d cd - 1, by omega⟩
    rw [hW', qwRun_eq]
    simp [Ev.run?]
  set b := fp + cert name (.n 5) with hb
  have hWords : WordsInA [(b, qwRunList d cd w)] (fp + 2) (fp + fs name) c (c + ([] : List ℕ).sum) := by
    refine ⟨fun q hq => Or.inl ?_, List.pairwise_singleton _ _⟩
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [qwRunList, List.length_map, List.length_range]
    omega
  refine callAtA_leafD [] [(b, qwRunList d cd w)] hlp hWords (fun rd h => h _ List.mem_cons_self)
    fun rd hl hW hP => ?_
  obtain ⟨hT, hpos, hptr⟩ := hP
  have hrunR : ReadsAt rd (ptrAt b) (qwRunList d cd w) := hW _ List.mem_cons_self
  have hlow : ∀ i < 128, (rd (addressOfIndex i)).isSome := fun i hi =>
    hl i (lt_of_lt_of_le hi (le_trans (by decide : (128 : ℕ) ≤ 2 ^ 7) (Nat.pow_le_pow_right (by decide) hk)))
  have hrun : FrameRun rd (ptrAt b) (128 / d * qwN d cd) (qwRunW d cd w) := by
    refine ⟨ofK_isInK _, fun i hi v hv => ?_⟩
    have h2 := (hrunR i (by simp [qwRunList]; exact hi)).2
    rw [hv, Option.some.injEq] at h2
    rw [h2]; simp [qwRunList]
  have hrd : ∀ j < 128 / d, LoadHolds rd (ptrAt ipos) j (eOfNat (qwPosOf d w j)) ∧
      LoadHolds rd (ptrAt iptr) j (ptrAt b * gen ^ (j * qwN d cd)) := fun j hj => by
    have h1 := hpos j (by simpa using hj)
    have h2 := hptr j (by simpa using hj)
    simp only [List.getElem_map, List.getElem_range] at h1 h2
    exact ⟨h1, by rw [ptrAt_mul_gen]; exact h2⟩
  obtain ⟨σ, hpar, hAK, -⟩ := qw_holds hs hlow hT hrun hrd
  have hσw : σ (.n (valf% «decode_query_windows» "squeezed_word")) = w := by
    have := congrArg (fun l => l.headD 0) hpar
    simpa using this
  have hA : ∀ a ∈ as, a.Holds rd σ ∧ QwEnv.Ok ⟨ptrAt ipos, ptrAt iptr, ptrAt it, ptrAt b, 128 / d, w, qwW d cd⟩ σ a :=
    fun a ha => hAK a (by rw [has]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
  have hnoalloc : ∀ a ∈ as, atomAllocB a = false := fun a ha => by
    have h := (hA a ha).2
    cases a with
    | hint hh => cases hh <;> first | rfl | (simp [QwEnv.Ok] at h)
    | _ => rfl
  refine ⟨σ, fn, as.map Ev.atom, [], hfind, by rw [hps]; exact hpar, by rw [hbody, has]; exact walk_atoms σ as [],
    rfl, calls_atoms as, allocs_atoms as hnoalloc, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [allocDsts_atoms as hnoalloc]; rfl
  · intro q hq
    obtain ⟨r, rs, hmem, hr⟩ := mem_addrs_atoms hq
    have hok := (hA _ hmem).2
    simp only [QwEnv.Ok] at hok
    obtain ⟨hri, h5, hW', hσ⟩ := hok
    obtain ⟨x, rfl⟩ : ∃ x, r = .n x := ⟨_, hri⟩
    have e : cert name (.n x) = cert name (.n 5) + (x - 5) := by
      have := hcx (x - 5) (by simp only at hW' h5; omega)
      rwa [show 5 + (x - 5) = x by simp only at h5; omega] at this
    rw [hσ, hr, ptrAt_mul_gen, e]
    show ofK (addressOfIndex (b + ((V.n x).idx - 5))) = ofK (addressOfIndex (fp + (cert name (.n 5) + (x - 5))))
    rw [hb, Nat.add_assoc]
  · intro ev hev
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hev
    exact (hA a ha).1
  · intro A hA'
    obtain ⟨d', p, off, hm, rfl⟩ := mem_loadAddrs hA'
    have hok := (hA _ hm).2
    simp only [QwEnv.Ok] at hok
    rcases hok with ⟨hp, ho⟩ | ⟨hp, ho⟩ | ⟨e, he, hp, rfl⟩
    · rw [hp]; exact ⟨ipos + off, Main.addr_ofK _ _, Or.inr (hRp off ho)⟩
    · rw [hp]; exact ⟨iptr + off, Main.addr_ofK _ _, Or.inr (hRq off ho)⟩
    · rw [hp, ptrAt_mul_gen]; exact ⟨it + e + 0, Main.addr_ofK _ _, Or.inr (by simpa using hRt e he)⟩
  · have h0 : heapHintAddrs σ (as.map Ev.atom) = [] := heapHintAddrs_atoms as (List.all_eq_true.mpr fun a ha => by
      have h := (hA a ha).2
      cases a with
      | hint hh =>
        cases hh with
        | windowsExp v st wd ct dd =>
          cases dd with
          | stack ds => rfl
          | heap p o l => simp [QwEnv.Ok] at h
        | _ => simp [QwEnv.Ok] at h
      | _ => rfl)
    intro A hA'
    rw [h0] at hA'
    exact absurd hA' List.not_mem_nil
  · intro i hi
    exact Or.inr ⟨(.n 5, qwW d cd), hrunM, by simp only at hi ⊢; omega, by simp only at hi ⊢; omega⟩
  · refine postQuiet_node hfind (by rw [hbody, has]; exact walk_atoms σ as []) (fun a ha => ?_) (fun ev hev => ?_)
      (by rw [calls_atoms]; exact kidsValid_nil) (by rw [calls_atoms]; simp [KidsPost]) []
    · obtain ⟨a', ha', he⟩ := List.mem_map.mp ha
      cases he
      have h := (hA a ha').2
      cases a with
      | hint hh => cases hh <;> first | rfl | (simp [QwEnv.Ok] at h)
      | _ => rfl
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hev
      have h := (hA a ha).2
      cases a with
      | hint hh =>
        cases hh with
        | windowsExp v st wd ct dd =>
          cases dd with
          | stack ds =>
            simp only [QwEnv.Ok] at h
            obtain ⟨hv, hds⟩ := h
            show ds.map σ = _
            rw [hds, hv, hσw]
          | heap p o l => simp [QwEnv.Ok] at h
        | _ => simp [QwEnv.Ok] at h
      | _ => trivial

/-- **Every `decode_query_windows` completes placed**, on its frame layout. -/
theorem qwA_complete (kd : ℕ) : ∀ p ∈ queryWindowsShapes, QwCert fs cert p.1 p.2.1 p.2.2 →
    QwA fs al cert kd p.1 p.2.1 p.2.2 :=
  fun p hp hc => qwA_complete' (qwShape_all p hp) (queryWindows_data p hp) hc

end
end LeanVM.Guest.B1.VsC
