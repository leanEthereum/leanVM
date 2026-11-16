/-
  LeanVM.Guest.Backend.Guest.Cpl.Frames

  The composition's hypotheses at the instance through the back end: every function runs on a
  frame holding the frame family's words (`cplRunG`, from `FrameConsistentStmt`, `fnComplete`
  and `pathOpsStmt`), and every frame of the honest memory holds them (`frameG`).
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Inst
public import LeanVM.Guest.Backend.Guest.Cpl.Compose
public import LeanVM.Guest.Backend.Complete.Fn
public import LeanVM.Guest.Backend.Complete.PathOps

/-!
# The frames and the runs

`FHG L j fp σ es vs kfps hdr` is what a frame of function `j` holds at the instance (`main`'s at
`0`): its callees are functions, its frame addresses point at the back end's cells, and the memory
holds the frame family `FSG` (`Complete.FrameOK`). `frameG`: every frame of the honest memory at
the instance's cells `CG` and headers `HG` holds it; the frame family's clauses
(`Complete.FrameClauses`) give the words of the cells the instance's candidates name. `cplRunG`:
on a frame holding it, the frame family's instructions' meaning (`FSOk`) and the back end's run
(`Complete.fnCompleteStmt`) give `CplRunG`, its counts within `pathCount` by `Complete.pathOpsStmt`
and the per-function test's counts. The jump tables are written when `main`'s table cells are
(`JTCells`).
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory GuestPiece
open LeanVM.Guest.Deployed

@[expose] public section

/-- **The jump table slots the back end writes are `main`'s table cells**: each slot's word is a
table cell's, at the slot's address. -/
def JTCells : Prop := ∀ (s : ℕ) (k : KVal) (w : E), W0.slots[s]? = some k →
  SlotWord W0.layout k = some w → ∃ q ∈ tableCells,
    addressOfIndex q.1 = addressOfIndex (W0.layout.tablesBase + s) ∧ q.2 = w

/-- **What a frame of function `j` holds** at the instance, `main`'s frame at `0`. -/
def FHG {κ : ℕ} (L : MemoryImage κ) (j fp : ℕ) (σ : Val) (es : List Ev) (_vs : List V)
    (kfps : List ℕ) (hdr : E × E) : Prop :=
  (j = 1 → fp = 0) →
    (∀ c ∈ calls es, ∃ i, coreProgram.indexOf? c.f = some i) ∧
    (∀ q ∈ addrs es, σ q.1 =
      ofK (addressOfIndex (fp + (Complete.cellP (placedG (j - 1)).locs q.2).getD 0))) ∧
    Complete.FrameOK L (loopTable W0.p) (tfG (j - 1)) (placedG (j - 1)).fn.frameSize fp
      (FSG (j - 1) fp kfps hdr σ) σ es kfps hdr

/-- **The frame family is `FrameConsistentStmt`'s** for an entry at a frame `main` may have. -/
theorem FSG_ok (hok : CplOkAll) (hFC : Complete.FrameConsistentStmt) {i : ℕ}
    (hi : i < coreProgram.length) {fp : ℕ} (hm : (tfG i).core.name = "main" → fp = 0) (kfps : List ℕ)
    (hdr : E × E) : FSOk i fp kfps hdr (FSG i fp kfps hdr) := by
  have E := entryOk hok hi
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi guestTraced_length.symm
  have hex : ∃ FS, FSOk i fp kfps hdr FS :=
    hFC W0 W0_compiled (tfG i) (tf_mem hi') E.facts.isScoped (placedG i) E.placedAs E.facts.apart
      E.facts.noSelf fp hm kfps hdr
  unfold FSG
  split
  · exact Classical.choose_spec ‹_›
  · exact absurd hex ‹_›

theorem withL_compiled {κ κ' : ℕ} (W : World κ) (L : MemoryImage κ') (h : W.Compiled) :
    (Complete.World.withL W L).Compiled := h

theorem withL_prog {κ κ' : ℕ} (W : World κ) (L : MemoryImage κ') :
    (Complete.World.withL W L).prog = W.prog := rfl

theorem withL_ent {κ κ' : ℕ} (W : World κ) (L : MemoryImage κ') (g : String) :
    (Complete.World.withL W L).ent g = W.ent g := rfl

theorem withL_mem {κ κ' : ℕ} (W : World κ) (L : MemoryImage κ') {tf : TracedFn} (h : tf ∈ W.p) :
    tf ∈ (Complete.World.withL W L).p := h

theorem withL_placedAs {κ κ' : ℕ} (W : World κ) (L : MemoryImage κ') {tf : TracedFn} {pf : Placed}
    (h : Complete.World.PlacedAs W tf pf) : Complete.World.PlacedAs (Complete.World.withL W L) tf pf :=
  h

theorem tfG_core {i : ℕ} (hi : i < coreProgram.length) : (tfG i).core = coreOf (i + 1) := by
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi guestTraced_length.symm
  show (guestTraced.getD i default).core = _
  rw [List.getD_eq_getElem _ _ hi', guestTraced_getElem hi']

theorem name_main {i : ℕ} (hi : i < coreProgram.length) : (tfG i).core.name = "main" ↔ i = 0 := by
  rw [tfG_core hi]
  constructor
  · intro h
    have := coreOf_name_inj (j := i + 1) (j' := 1) (by omega)
      (lt_of_lt_of_eq (Nat.add_lt_add_right hi 1) coreProgram_length_succ) le_rfl (by decide)
      (h.trans (coreOf_one ▸ core0_main.1).symm)
    omega
  · rintro rfl
    exact coreOf_one ▸ core0_main.1

theorem main_not_loopG : coreProgram.loop "main" = false := by decide +kernel

theorem readsP_param {ps : List V} {body : List Stmt} {σ : Val} {es : List Ev} {vs : List V} {v : V}
    (h : v ∈ ps) : v ∈ Complete.readsP ps body σ es vs := by
  unfold Complete.readsP
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl h)))

theorem readsP_use {ps : List V} {body : List Stmt} {σ : Val} {es : List Ev} {vs : List V} {v : V}
    {e : Ev} (he : e ∈ es) (h : v ∈ e.uses) : v ∈ Complete.readsP ps body σ es vs := by
  unfold Complete.readsP
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨e, he, h⟩)))

theorem readsP_ret {ps : List V} {body : List Stmt} {σ : Val} {es : List Ev} {vs : List V} {v : V}
    (h : v ∈ vs) : v ∈ Complete.readsP ps body σ es vs := by
  unfold Complete.readsP
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))

/-! ## The frames of the honest memory -/

section Honest

variable {hdr : E × E} {rd : Reader} {T : Tree}

/-- **An instance of the honest memory that runs**: its path, its frame addresses, the frame
family's clauses, and its own frame holding the frame words. -/
theorem node_at (hok : CplOkAll) (hFC : Complete.FrameConsistentStmt)
    (h : HonestAt coreProgram fs HG CG hdr T certG rd [] [])
    {I : Inst} (hI : I ∈ honestInsts coreProgram fs HG hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) {i : ℕ} (hix : coreProgram.indexOf? f = some i)
    (hm : f = "main" → I.fp = 0) :
    ∃ es vs, walk σ (tfG i).core.body = .ret es vs ∧ (∀ e ∈ es, e.Holds rd σ) ∧
      Tree.KidsValid coreProgram rd σ (calls es) kids ∧ I.t.events coreProgram = es ∧
      (∀ q ∈ addrs es, σ q.1 =
        ofK (addressOfIndex (I.fp + (Complete.cellP (placedG i).locs q.2).getD 0))) ∧
      Complete.FrameClauses (loopTable W0.p) (tfG i) (placedG i) I.fp σ es vs I.hdr (FSI i I σ) ∧
      ∀ n, 2 ≤ n → n < (placedG i).fn.frameSize →
        (honest coreProgram fs HG CG hdr T).read (addressOfIndex (I.fp + n)) = some ((FSI i I σ).Ψ n) := by
  have F := fnAt hix
  have E := entryOk hok F.lt
  have hj : idxOf f = some (i + 1) := by unfold idxOf; rw [hix]; rfl
  obtain ⟨es, vs, hw, he, hk⟩ := node_valid ht hj (insts_good T 0 hdr h.toHonest.valid I hI)
  have hw' : walk σ (tfG i).core.body = .ret es vs := by rw [F.core]; exact hw
  have hev : I.t.events coreProgram = es := node_events ht hj hw
  have haddr : ∀ q ∈ addrs es, σ q.1 =
      ofK (addressOfIndex (I.fp + (Complete.cellP (placedG i).locs q.2).getD 0)) := by
    intro q hq
    rw [(h.nodeAt hI ht).2 q (by rw [hev]; exact hq), F.cert]
  have hok' := FSG_ok hok hFC F.lt (fp := I.fp)
    (fun hn => hm (by rw [F.core, F.name] at hn; exact hn)) I.kidFps I.hdr
  have hcl := (hok'.2 σ es vs hw' haddr).1 rd he
  refine ⟨es, vs, hw', he, hk, hev, haddr, hcl, fun n h2 hn => ?_⟩
  have hfs : n < fs f := by
    rw [F.fs_eq]
    exact lt_of_lt_of_le (E.facts.sfacts.frame ▸ hn) (fsWant_le i)
  have hmem : (n, (FSI i I σ).Ψ n) ∈ CG I := by
    rw [CG_node ht hix]
    refine frameE_cell ?_ h2 hfs fun x hx hxn => ?_
    · by_cases htc : ∃ t ∈ coreProgram.temps f, certG f t = n
      · obtain ⟨t, htm, rfl⟩ := htc
        exact ⟨(certG f t, σ t), List.mem_append_left _ (List.mem_map_of_mem htm), rfl⟩
      · refine ⟨(n, (FSI i I σ).Ψ n), List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_left _ ?_)), rfl⟩
        exact List.mem_filterMap.mpr ⟨n, List.mem_range.mpr hn, by simp only [htc, ↓reduceIte]⟩
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨t, htm, rfl⟩ := List.mem_map.mp hx
        rw [tmps_tfG F] at htm
        obtain ⟨c, hc, -⟩ := E.facts.sfacts.tmpIn t htm
        have hcn : c = n := by
          have h' : certG f t = n := hxn
          rw [F.cert, hc] at h'
          exact h'
        subst hcn
        exact (hcl.tmp E.facts.apart t htm c hc).2.2.symm
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨p, r, rs, he', k, hk', rfl⟩ := mem_runsG hx
        obtain ⟨i', hix', ha⟩ := events_atomG ht he'
        rw [hix] at hix'; cases hix'
        obtain ⟨hck, -, -, -⟩ := run_cells hok hix ha k hk'
        have hxn' : certG f r + k = n := hxn
        rw [hxn'] at hck
        have hread : (r :: rs)[k] ∈ Complete.readsP (tfG i).core.params (tfG i).core.body σ es vs :=
          readsP_use (by rw [← hev]; exact he') (by
            simp only [Ev.uses, atomUses]
            exact List.mem_cons_of_mem _ (List.getElem_mem _))
        exact (hcl.cell _ hread n hck).2.2.symm
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨n', -, hx'⟩ := List.mem_filterMap.mp hx
        by_cases htc : ∃ t ∈ coreProgram.temps f, certG f t = n'
        · simp only [htc, ↓reduceIte] at hx'; cases hx'
        · simp only [htc, ↓reduceIte, Option.some.injEq] at hx'
          subst hx'
          have hn' : n' = n := hxn
          subst hn'
          rfl
      · by_cases hi0 : i = 0
        · simp only [hi0, ↓reduceIte] at hx
          have hlo : Deployed.Data.mainCells ≤ x.1 := by
            have := tableCells_offsets ▸ List.mem_map_of_mem (f := Prod.fst) hx
            rw [List.mem_range'_1] at this
            exact this.1
          have hn0 : n < Deployed.Data.mainCells := by
            rw [E.facts.sfacts.frame] at hn
            subst hi0
            exact hn
          omega
        · simp only [hi0, ↓reduceIte] at hx
          cases hx
  rw [addressOfIndex, pow_add]
  exact h.toHonest.read_C hI hmem

/-- **Every frame of the honest memory holds the frame family's words.** -/
theorem frameG (hok : CplOkAll) (hFC : Complete.FrameConsistentStmt) :
    ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
      HonestAt coreProgram fs HG CG hdr T certG rd [] [] → ∀ I ∈ honestInsts coreProgram fs HG hdr T,
        ∀ f σ bufs kids, I.t = .node f σ bufs kids → ∀ j, idxOf f = some j → ∀ es vs,
          walk σ (coreOf j).body = .ret es vs →
            FHG (honest coreProgram fs HG CG hdr T) j I.fp σ es vs I.kidFps I.hdr := by
  intro hdr rd T hT h I hI f σ bufs kids ht j hj es vs hw hm1
  obtain ⟨i, rfl, hix⟩ := ix_of_idx hj
  have F := fnAt hix
  have E := entryOk hok F.lt
  simp only [Nat.add_sub_cancel]
  have hm : f = "main" → I.fp = 0 := fun hf => hm1 ((idx_one_iff hj).mpr hf)
  obtain ⟨es', vs', hw', he, hk, hev, haddr, hcl, hown⟩ := node_at hok hFC h hI ht hix hm
  have hw'' : walk σ (tfG i).core.body = .ret es vs := by rw [F.core]; exact hw
  rw [hw''] at hw'
  obtain ⟨rfl, rfl⟩ : es = es' ∧ vs = vs' := by cases hw'; exact ⟨rfl, rfl⟩
  have hgp : ∀ a o, (honest coreProgram fs HG CG hdr T).read (addressOfIndex a * addressOfIndex o) =
      (honest coreProgram fs HG CG hdr T).read (addressOfIndex (a + o)) := fun a o => by
    rw [addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
  have hlen := frame_len hI ht hk
  have hname : (tfG i).core.name = f := by rw [F.core, F.name]
  have hhdrK : (tfG i).core.name ≠ "main" → IsInK I.hdr.1 ∧ IsInK I.hdr.2 := fun hn =>
    honest_hdrK HG_K hT hI (by rw [ht]; simp only [Tree.name]; rw [← hname]; exact hn)
  -- the callees
  have hkid : ∀ (i' : ℕ) (c : Call) (kfp : ℕ), (calls es)[i']? = some c → I.kidFps[i']? = some kfp →
      ∃ J ∈ honestInsts coreProgram fs HG hdr T, J.fp = kfp ∧ J.hdr = HG I i' ∧ J.t.name = c.f ∧
        ∃ ic, coreProgram.indexOf? c.f = some ic ∧
          (coreOf (ic + 1)).params.map J.t.val = c.args.map σ ∧
          ((c.taken = true ∧ ∃ σJ bufsJ kidsJ, J.t = .node c.f σJ bufsJ kidsJ) ∨
            (c.taken = false ∧ ∃ σJ, J.t = .phantom c.f σJ)) := by
    intro i' c kfp hc hp
    obtain ⟨J, hJ, hfp, hJh, hJn, hJv⟩ := kid_inst hI ht hk hc hp
    obtain ⟨jc, hjc, hpar, hgood⟩ := kid_shape hJn hJv
    obtain ⟨ic, rfl, hixc⟩ := ix_of_idx hjc
    refine ⟨J, hJ, hfp, hJh, hJn, ic, hixc, hpar, ?_⟩
    rcases hgood with ⟨htk, σJ, bJ, kJ, hJt, -⟩ | ⟨htk, σJ, hJt⟩
    · exact Or.inl ⟨htk, σJ, bJ, kJ, hJt⟩
    · exact Or.inr ⟨htk, σJ, hJt⟩
  refine ⟨fun c hc => ?_, haddr, ?_⟩
  · obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp hc
    have hlt : i' < I.kidFps.length := by
      rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi').1
    obtain ⟨-, -, -, -, -, ic, hixc, -⟩ := hkid i' c _ hi' (List.getElem?_eq_getElem hlt)
    exact ⟨ic, hixc⟩
  refine { hdr0 := ?_, hdr1 := ?_, hdrK := hhdrK, own := hown, len := hlen, kid := ?_, tail := ?_ }
  · rw [← hgp]; exact (h.toHonest.read_hdr hI).1
  · rw [← hgp]; exact (h.toHonest.read_hdr hI).2
  · intro i' c kfp hc hp
    obtain ⟨J, hJ, rfl, hJh, hJn, ic, hixc, hpar, hgood⟩ := hkid i' c kfp hc hp
    have hKh : IsInK ((FSI i I σ).kh i').1 ∧ IsInK ((FSI i I σ).kh i').2 := hcl.khK i' c hc hhdrK
    have hH : HG I i' = (FSG i I.fp I.kidFps I.hdr σ).kh i' := HG_node ht hix i' hKh
    have Fc := fnAt hixc
    have Ec := entryOk hok Fc.lt
    have hplen : (coreOf (ic + 1)).params.length = c.args.length := by
      simpa using congrArg List.length hpar
    have hcm : c.f ≠ "main" := calls_ne_main F.find hw (List.mem_of_getElem? hc)
    have hpk : ∀ k (hk : k < (coreOf (ic + 1)).params.length),
        Complete.cellP (placedG ic).locs (coreOf (ic + 1)).params[k] = some (2 + k) := by
      have := Ec.facts.sfacts.params
      rw [Fc.core] at this
      exact this
    have hpin : 2 + (coreOf (ic + 1)).params.length ≤ fs c.f := by
      have := Ec.facts.sfacts.paramsIn
      rw [Fc.core] at this
      rw [Fc.fs_eq]
      exact this.trans (fsWant_le ic)
    have hloops : loopTable W0.p = loopsG := W0_loops
    refine ⟨?_, ?_, fun k hk' => ?_, fun hreg => ?_⟩
    · rw [← hgp, ← hH, ← hJh]; exact (h.toHonest.read_hdr hJ).1
    · rw [← hgp, ← hH, ← hJh]; exact (h.toHonest.read_hdr hJ).2
    · have hkp : k < (coreOf (ic + 1)).params.length := by omega
      have hσ : J.t.val (coreOf (ic + 1)).params[k] = σ c.args[k] := by
        have := congrArg (fun l => l[k]?) hpar
        simp only [List.getElem?_map, List.getElem?_eq_getElem hkp, List.getElem?_eq_getElem hk',
          Option.map_some, Option.some.injEq] at this
        exact this
      rcases hgood with ⟨-, σJ, bJ, kJ, hJt⟩ | ⟨-, σJ, hJt⟩
      · obtain ⟨esJ, vsJ, -, -, -, -, -, hclJ, hownJ⟩ :=
          node_at hok hFC h hJ hJt hixc (fun hf => absurd hf hcm)
        have hcellJ := hclJ.cell (coreOf (ic + 1)).params[k]
          (by rw [Fc.core]; exact readsP_param (List.getElem_mem _)) (2 + k) (hpk k hkp)
        rw [← hσ, hJt]
        rw [hownJ (2 + k) (by omega) hcellJ.2.1, hcellJ.2.2]
        rfl
      · rw [← hσ, hJt]
        have hmem : (2 + k, σJ (coreOf (ic + 1)).params[k]) ∈ CG J := by
          rw [CG_phantom hJt hixc]
          refine frameE_cell ⟨(certG c.f (coreOf (ic + 1)).params[k], σJ (coreOf (ic + 1)).params[k]),
            List.mem_append_left _ (List.mem_map_of_mem (List.getElem_mem _)), by
              rw [Fc.cert, hpk k hkp]; rfl⟩ (by omega) (by omega) fun x hx hxn => ?_
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
            obtain ⟨k', hk'', rfl⟩ := List.getElem_of_mem hp'
            have hc' : certG c.f (coreOf (ic + 1)).params[k'] = 2 + k := hxn
            rw [Fc.cert, hpk k' hk''] at hc'
            have hkk : k' = k := by simp only [Option.getD_some] at hc'; omega
            subst hkk
            rfl
          · split at hx
            · rcases List.mem_singleton.mp hx with rfl
              have : 2 + (coreOf (ic + 1)).params.length = 2 + k := hxn
              omega
            · cases hx
        have := h.toHonest.read_C hJ hmem
        rw [← hgp]
        exact this
    · have hreg' : (loopsG[c.f]?).any (·.registered) = true := by
        have := hreg; unfold Complete.registered at this; rw [hloops] at this; exact this
      rcases hgood with ⟨-, σJ, bJ, kJ, hJt⟩ | ⟨-, σJ, hJt⟩
      · obtain ⟨esJ, vsJ, -, -, -, -, -, hclJ, hownJ⟩ :=
          node_at hok hFC h hJ hJt hixc (fun hf => absurd hf hcm)
        have hregJ : Complete.registered (loopTable W0.p) (tfG ic).core.name := by
          rw [Fc.core, Fc.name]; exact hreg
        have hself := hclJ.self hregJ
        have hlt := Ec.facts.sfacts.self (by rw [← hloops]; exact hregJ)
        rw [Fc.core] at hself hlt
        rw [← hplen, hownJ (2 + (coreOf (ic + 1)).params.length) (by omega)
          (by rw [Ec.facts.sfacts.frame]; exact hlt), hself]
      · have hsl : (2 + (coreOf (ic + 1)).params.length, ofK (addressOfIndex J.fp)) ∈
            phantomG ic c.f σJ J := by
          unfold phantomG
          simp only [hreg', ↓reduceIte]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hslt : 2 + (coreOf (ic + 1)).params.length < fs c.f := by
          have := Ec.facts.sfacts.self (by
            unfold Complete.registered; rw [Fc.core, Fc.name]; exact hreg')
          rw [Fc.core] at this
          rw [Fc.fs_eq]
          exact lt_of_lt_of_le this (fsWant_le ic)
        have hmem : (2 + (coreOf (ic + 1)).params.length, ofK (addressOfIndex J.fp)) ∈ CG J := by
          rw [CG_phantom hJt hixc]
          refine frameE_cell ⟨_, hsl, rfl⟩ (by omega) hslt fun x hx hxn => ?_
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
            obtain ⟨k', hk'', rfl⟩ := List.getElem_of_mem hp'
            have hc' : certG c.f (coreOf (ic + 1)).params[k'] = 2 + (coreOf (ic + 1)).params.length := hxn
            rw [Fc.cert, hpk k' hk''] at hc'
            simp only [Option.getD_some] at hc'
            omega
          · simp only [hreg', ↓reduceIte, List.mem_singleton] at hx
            rw [hx]
        rw [← hplen, ← hgp]
        exact h.toHonest.read_C hJ hmem
  · intro hl kfp hk'
    have hlp' : (tfG i).core.loop = true := by rw [← E.facts.sfacts.loop]; exact hl
    have hlp : coreProgram.loop I.t.name = true := by
      rw [ht]; simp only [Tree.name]; rw [Program.loop_of_find? F.find, ← F.core]; exact hlp'
    have hi0 : i ≠ 0 := by
      rintro rfl
      have hfm : f = "main" := by rw [← hname]; exact (name_main F.lt).mpr rfl
      rw [ht] at hlp; simp only [Tree.name] at hlp
      rw [hfm, main_not_loopG] at hlp
      cases hlp
    have hne : I.t.kids ≠ [] := by
      intro he'
      have hl0 := congrArg List.length (honest_kidFps hI)
      rw [length_kidPos, List.length_map, he'] at hl0
      rw [List.length_eq_zero_iff.mp hl0] at hk'
      cases hk'
    rw [honest_kidFps_getLast? hI hlp hne] at hk'
    rw [← Option.some.inj hk', ht]
    simp only [Tree.name]
    rw [E.facts.sfacts.frame, fsWant_eq hi0, ← F.fs_eq]

end Honest

/-! ## The runs -/

theorem opIx_eq : Complete.opIx = opIdx := by
  funext op
  cases op <;> rfl

mutual
theorem cost1_eq (acs : List (ℕ × List (List ℕ))) (σ : Val) :
    ∀ s : Stmt, Complete.cost1 acs σ s = Deployed.cost1 acs σ s
  | .atom _ => rfl
  | .ite _ z n => by rw [Complete.cost1, Deployed.cost1, armsCost_eq acs σ z, armsCost_eq acs σ n]
  | .match_ x arms => by rw [Complete.cost1, Deployed.cost1, costArms_eq acs σ x _ 0 arms]
  | .call .. => rfl
  | .callIf .. => rfl
  | .dispatch .. => rfl
  | .ret _ => rfl

theorem armsCost_eq (acs : List (ℕ × List (List ℕ))) (σ : Val) :
    ∀ ss : List Stmt, Complete.armsCost acs σ ss = Deployed.costW acs σ ss
  | [] => rfl
  | s :: ss => by rw [Complete.armsCost, Deployed.costW, cost1_eq acs σ s, armsCost_eq acs σ ss]

theorem costArms_eq (acs : List (ℕ × List (List ℕ))) (σ : Val) (x : V)
    (key : Option (List (List ℕ))) : ∀ (k : ℕ) (arms : List (List Stmt)),
      Complete.costArms acs σ x key k arms = Deployed.costArms acs σ x key k arms
  | _, [] => rfl
  | k, a :: as => by
    rw [Complete.costArms, Deployed.costArms, armsCost_eq acs σ a, costArms_eq acs σ x key (k + 1) as,
      opIx_eq]
    by_cases hx : σ x = ofK (addressOfIndex k)
    · simp only [hx, ↓reduceIte]
      congr 1
    · simp only [hx, ↓reduceIte]
end

theorem getD_ofCnt (c : Opcode → ℕ) (op : Opcode) : (Complete.ofCnt c).getD (opIdx op) 0 = c op := by
  cases op <;> rfl

/-- **Every function runs, counted, on a frame holding the frame family's words.** -/
theorem cplRunG (hok : CplOkAll) (hFC : Complete.FrameConsistentStmt) (hjt : JTCells) :
    ∀ j, 1 ≤ j → j < nFns → CplRunG FHG j := by
  intro j h1 h2 κ L _ htab fp hfp σ es vs hw hev kfps hdr hF ck hK
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < coreProgram.length :=
    Nat.lt_of_add_lt_add_right (lt_of_lt_of_eq h2 coreProgram_length_succ.symm)
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi guestTraced_length.symm
  have E := entryOk hok hi
  have hcore := tfG_core hi
  have hm : (tfG i).core.name = "main" → fp = 0 := fun hn => hfp (by
    have := (name_main hi).mp hn; omega)
  obtain ⟨hcallees, haddr, hfok⟩ := hF hfp
  simp only [Nat.add_sub_cancel] at haddr hfok
  have hw' : walk σ (tfG i).core.body = .ret es vs := by rw [hcore]; exact hw
  have hok' := FSG_ok hok hFC hi hm kfps hdr
  obtain ⟨hcl, hrun⟩ := hok'.2 σ es vs hw' haddr
  have hcl' := hcl L.read hev
  set W := Complete.World.withL W0 L with hW
  have hWc : W.Compiled := withL_compiled W0 L W0_compiled
  have hprog : W.prog = guestProgram :=
    (withL_prog W0 L).trans (guestWorld_prog guest_compiles : W0.prog = guestProgram)
  have hent : ∀ ic, ic + 1 < nFns → W.ent (coreOf (ic + 1)).name = (fnOf (ic + 1)).entryPc :=
    fun ic hic => (withL_ent W0 L _).trans (ent_eq guest_compiles (by omega) hic : W0.ent _ = _)
  have hJT : JTHolds L W0.layout W0.slots := fun s k w hs hk => by
    obtain ⟨q, hq, ha, hqw⟩ := hjt s k w hs hk
    rw [← ha, ← hqw]
    exact htab q hq
  have hKP : Complete.World.KidsRunP W σ es kfps ck := by
    refine ⟨hK.1, fun i' c kfp hc hp ht => ?_⟩
    obtain ⟨⟨r, hr, hrc⟩, hrets⟩ := hK.2 i' c kfp hc hp ht
    refine ⟨⟨r, hr, ?_⟩, hrets⟩
    obtain ⟨ic, hixc⟩ := hcallees c (List.mem_of_getElem? hc)
    have Fc := fnAt hixc
    have hjc : idxOf c.f = some (ic + 1) := by unfold idxOf; rw [hixc]; rfl
    show RunC W.prog L ⟨addressOfIndex (W.ent c.f), addressOfIndex kfp⟩ r (ck.getD i' 0)
    rw [hprog, ← Fc.name, hent ic Fc.nfns, ← entryOf_of hjc]
    exact hrc
  have hbody := hrun L ck hfok hev hJT hKP
  obtain ⟨r, c, hr, hrunC, hle⟩ := Complete.fnCompleteStmt W hWc (tfG i)
    (withL_mem W0 L (tf_mem hi')) (placedG i) (withL_placedAs W0 L E.placedAs) fp hm σ (kfps.zip ck)
    hbody
  have hlen : kfps.length = ck.length := by rw [hfok.len, hK.1]
  have hzip : (kfps.zip ck).map Prod.snd = ck := List.map_snd_zip (by omega)
  refine ⟨r, c, ?_, ?_, fun op => ?_, fun k hk => ?_⟩
  · by_cases h0 : i = 0
    · have hn : (tfG i).core.name = "main" := (name_main hi).mpr h0
      simp only [hn, ↓reduceIte] at hr
      rw [hprog] at hr
      simp only [h0, Nat.zero_add, ↓reduceIte]
      exact hr
    · have hn : (tfG i).core.name ≠ "main" := fun hn => h0 ((name_main hi).mp hn)
      have h1' : i + 1 ≠ 1 := by omega
      simp only [hn, ↓reduceIte] at hr
      simp only [h1', ↓reduceIte]
      exact hr
  · rw [hprog, hcore, hent i (by omega)] at hrunC
    exact hrunC
  · have hops := Complete.pathOpsStmt (tfG i) (placedG i) E.facts.aligned (keyedOf i) E.facts.armsNodup
      σ es vs hw' op
    have hsum : ((kfps.zip ck).map (·.2 op)).sum = (ck.map (· op)).sum := by
      conv_rhs => rw [← hzip, List.map_map]
      rfl
    have hpc : pathCount (i + 1) σ op =
        Complete.pmaxP (keyedOf i) (placedG i) op +
          Complete.armsCost (Complete.armsP (keyedOf i) (tfG i) (placedG i)) σ (tfG i).core.body op := by
      rw [pathCount, Deployed.pmaxOf, ← E.facts.pmax, getD_ofCnt, E.facts.arms, armsCost_eq, hcore]
      rfl
    have := hle op
    rw [hsum] at this
    rw [hpc]
    omega
  · have hvs := walk_ret _ hw'
    have hrk := E.facts.sfacts.rets vs hvs k hk
    have hcellv := hcl'.cell vs[k] (readsP_ret (List.getElem_mem _)) _ hrk
    have := hfok.own _ hcellv.1 hcellv.2.1
    rw [hcellv.2.2] at this
    rw [← hcore]
    exact this

end
end LeanVM.Guest.Backend.Cpl
