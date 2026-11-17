/-
  LeanVM.Compiler.Complete.CoreHonest
  The honest memory at the back end's data from a core run: its temporaries re-chosen, a run of
  `main` placed by the back end and loading in its data is `HonestAt` the back end's cells.
-/

module

public import LeanVM.Compiler.Complete.CoreCells
public import LeanVM.Compiler.Complete.CoreRuns

/-!
# `HonestAt` from a core run

`Memory.honestAt_retemp` (`Memory/Discharge.lean`) builds `HonestAt` from a placed run loading in
its data, at cells `C` given with facts about them. It is applied here at the cells `cellsT`: the
back end's cells off the temporaries' cells (`cellsK`), and at each temporary's cell the instance's
own value of it, so that every re-choice of the temporaries keeps them right. Its hypotheses:

* the cells fit and agree (`cellsOk_T`), at the instances of a run, whose functions are the
  program's and of which only the root is `main`'s (`insts_facts`);
* a `frameAddr` run's cells hold its values (`FrameClauses.cell` of the frame family, at cells
  placement makes consecutive, `placeFn_runs`), none a temporary's (`TmpsApart.apart`);
* a temporary's cells hold only it, the others are kept (`CoreCells.lean`).

Then the back end's own cells `cellsB` of the re-chosen tree are among `cellsT`'s: at a temporary's
cell the frame family holds the re-chosen value, by `FrameClauses.tmp` on the re-chosen run, valid
on the honest memory. So `cross` and the rest carry over (`honestAt_of_core`).
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {κ₀ : ℕ} {W : World κ₀}

/-! ## The instances of a run of `main` -/

section Insts

variable {fs : String → ℕ} {lp : String → Bool} {H : Memory.Inst → ℕ → E × E} {rd : Reader}

mutual
/-- **Every instance of a run is of a function of the program**, and only its root may be
`main`'s. -/
theorem insts_facts (hW : W.Compiled) : ∀ (t : Tree) (fp : ℕ) (hdr : E × E) {args rets : List E},
    t.Valid W.core rd args rets → ∀ I ∈ t.insts fs lp H fp hdr,
      (∃ fn, W.core.find? I.t.name = some fn) ∧ (I.t.name = "main" → I.fp = fp ∧ t.name = "main")
  | .node f σ bufs kids, fp, hdr, args, rets, hv, I, hI => by
      obtain ⟨fn, hf, _, es, vs, hw, _, _, hk⟩ := hv
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact ⟨⟨fn, hf⟩, fun h => ⟨rfl, h⟩⟩
      · obtain ⟨tf, htf, rfl, -⟩ := core_find hf
        obtain ⟨h1, h2⟩ := instsKids_facts hW kids σ (calls es) _ 0 _ hk
          (no_main_call hW htf hw) I hI
        exact ⟨h1, fun h => absurd h h2⟩
  | .phantom .., _, _, _, _, hv, _, _ => hv.elim

/-- `insts_facts` for the callees: none is `main`'s. -/
theorem instsKids_facts (hW : W.Compiled) : ∀ (ks : List Tree) (σ : Val) (cs : List Call)
    (I : Memory.Inst) (j : ℕ) (ps : List ℕ), Tree.KidsValid W.core rd σ cs ks →
    (∀ c ∈ cs, c.f ≠ "main") → ∀ J ∈ Tree.instsKids fs lp H I j ps ks,
      (∃ fn, W.core.find? J.t.name = some fn) ∧ J.t.name ≠ "main"
  | [], _, _, _, _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, _, _, _, _, [], _, _, J, hJ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, σ, c :: cs, I, j, p :: ps, ⟨hn, hc, hks⟩, hm, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · by_cases ht : c.taken = true
        · simp only [ht, ↓reduceIte] at hc
          obtain ⟨h1, h2⟩ := insts_facts hW k p _ hc J hJ
          exact ⟨h1, fun h => hm c List.mem_cons_self (by rw [← hn]; exact (h2 h).2)⟩
        · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc
          obtain ⟨⟨f, σ', rfl⟩, fn, hf, -⟩ := hc
          rw [insts_phantom, List.mem_singleton] at hJ
          subst hJ
          exact ⟨⟨fn, hf⟩, fun h => hm c List.mem_cons_self (by rw [← hn]; exact h)⟩
      · exact instsKids_facts hW ks σ cs I (j + 1) ps hks
          (fun c' hc' => hm c' (List.mem_cons_of_mem _ hc')) J hJ
  | _ :: _, _, [], _, _, _ :: _, h, _, _, _ => h.elim
end

end Insts

/-- The instances of the re-chosen tree are of functions of the program. -/
theorem retemp_found (hW : W.Compiled) {ν : ℕ → String → Val → V → E} {hdr : E × E} {T : Tree}
    {rd : Reader} {args rets : List E} (hv : T.Valid W.core rd args rets) :
    ∀ I' ∈ honestInsts W.core W.fsB W.hdrB hdr (T.retemp W.core W.fsB ν 0),
      ∃ fn, W.core.find? I'.t.name = some fn := by
  intro I' hI'
  obtain ⟨I, hI, -, ht, -, -⟩ := insts_retempB T 0 hdr I' hI'
  rw [ht, name_retemp]
  exact (insts_facts hW T 0 hdr hv I hI).1

/-! ## The back end's cells, a frame family's word -/

/-- **A running instance's placed cells hold its frame family's words.** -/
theorem own_mem (hW : W.Compiled) {I : Memory.Inst} {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) {tf : TracedFn} {pf : Placed}
    (hfo : W.fnOf f = some (tf, pf)) {n : ℕ} (h2 : 2 ≤ n) (hn : n < pf.fn.frameSize) :
    (n, (W.famB tf pf I.fp I.kidFps I.hdr σ).Ψ n) ∈ W.cellsB I := by
  obtain ⟨htf, hname, hpa, -⟩ := fnOf_spec hfo
  have hle := frame_le_fsB hW htf hpa
  rw [hname] at hle
  rw [cellsB_node ht hfo]
  refine mem_frameB (List.mem_append_left _ (List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩))
    h2 (by simp only; omega) fun q' hq' he => ?_
  rcases List.mem_append.mp hq' with hq' | hq'
  · obtain ⟨n', -, rfl⟩ := List.mem_map.mp hq'
    simp only at he
    subst he
    rfl
  · split at hq'
    · next hm =>
      obtain ⟨s, -, hs, -⟩ := tableB_off hq'
      have := (fsB_main hW hpa (hname.trans hm)).1
      simp only at he
      omega
    · exact absurd hq' List.not_mem_nil

/-- **The frame clauses at an instance of a placed run of `main`.** -/
theorem clauses_at (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) {rd : Reader} {T : Tree}
    {hdr : E × E} {args rets : List E} (hv : T.Valid W.core rd args rets)
    (hp : T.Placed W.core W.fsB W.cellB 0) {I : Memory.Inst}
    (hI : I ∈ honestInsts W.core W.fsB W.hdrB hdr T) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    ∃ tf pf es vs, W.fnOf f = some (tf, pf) ∧ walk σ tf.core.body = .ret es vs ∧
      I.t.events W.core = es ∧
      FrameClauses (loopTable W.p) tf pf I.fp σ es vs I.hdr (W.famB tf pf I.fp I.kidFps I.hdr σ) := by
  rcases insts_good T 0 hdr hv I hI with ⟨a, r, hvI⟩ | ⟨g, σ', hph⟩
  · rw [ht] at hvI
    obtain ⟨fn, hf, -, es, vs, hw, -, hes, -⟩ := hvI
    obtain ⟨tf, htf, rfl, hname⟩ := core_find hf
    obtain ⟨pf, hfo, hpa⟩ := fnOf_of_mem hW htf
    rw [hname] at hfo
    have hev : I.t.events W.core = es := by rw [ht]; exact Memory.events_node hf hw
    have hmain : tf.core.name = "main" → I.fp = 0 := fun h =>
      ((insts_facts hW T 0 hdr hv I hI).2 (by rw [ht]; exact hname ▸ h)).1
    have hok := famB_ok hW htf (hC tf htf) hpa hmain I.kidFps I.hdr
    have haddr : ∀ q ∈ addrs es,
        σ q.1 = ofK (addressOfIndex (I.fp + (cellP pf.locs q.2).getD 0)) := by
      intro q hq
      have := (Inst.nodeAt (insts_placedAt T 0 hdr hp I hI) (insts_placed T 0 hdr I hI) ht).2 q
        (by rw [hev]; exact hq)
      rw [this]
      unfold World.cellB
      rw [(fnOf_spec hfo).2.2.2]
    exact ⟨tf, pf, es, vs, hfo, hw, hev, (hok.2 σ es vs hw haddr).1 rd hes⟩
  · rw [ht] at hph; cases hph

/-! ## The cells given to the discharge -/

/-- **The cells given to the discharge**: the back end's off the temporaries' cells, and at a
running instance's temporary's cell its own value of it. -/
noncomputable def cellsT (W : World κ₀) (I : Memory.Inst) : List (ℕ × E) :=
  cellsK W I ++
    match I.t with
    | .node f σ _ _ => (W.core.temps f).map fun t => (W.cellB f t, σ t)
    | .phantom .. => []

theorem mem_cellsT {I : Memory.Inst} {q : ℕ × E} (hq : q ∈ cellsT W I) :
    q ∈ cellsK W I ∨ ∃ f σ bufs kids, I.t = .node f σ bufs kids ∧
      ∃ t ∈ W.core.temps f, q = (W.cellB f t, σ t) := by
  unfold cellsT at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl hq
  · right
    rcases ht : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩ <;> rw [ht] at hq <;> simp only at hq
    · obtain ⟨t, htm, rfl⟩ := List.mem_map.mp hq
      exact ⟨f, σ, bufs, kids, rfl, t, htm, rfl⟩
    · exact absurd hq List.not_mem_nil

theorem tmp_mem_cellsT {I : Memory.Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {t : V} (htm : t ∈ W.core.temps f) :
    (W.cellB f t, σ t) ∈ cellsT W I := by
  unfold cellsT
  rw [ht]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨t, htm, rfl⟩)

/-- **The cells given to the discharge fit and agree.** -/
theorem cellsOk_T (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) {Is : List Memory.Inst}
    (hfound : ∀ I ∈ Is, ∃ fn, W.core.find? I.t.name = some fn) : CellsOk W.fsB (cellsT W) Is where
  two_le I hI := by
    obtain ⟨fn, hf⟩ := hfound I hI
    exact two_le_fsB hW hf
  off I _ q hq := by
    rcases mem_cellsT hq with hq | ⟨f, σ, bufs, kids, ht, t, htm, rfl⟩
    · exact cellsB_off (mem_cellsK.mp hq).1
    · have hn : I.t.name = f := by rw [ht]; rfl
      rw [hn]
      exact cert_lt hW hC f t htm
  agree I _ q hq q' hq' he := by
    rcases mem_cellsT hq with hq | ⟨f, σ, bufs, kids, ht, t, htm, rfl⟩ <;>
      rcases mem_cellsT hq' with hq' | ⟨f', σ', bufs', kids', ht', t', htm', rfl⟩
    · rw [cellsB_unique (mem_cellsK.mp hq).1 (mem_cellsK.mp hq').1 he]
    · exact ((mem_cellsK.mp hq).2 ⟨f', σ', bufs', kids', ht', t', htm', he⟩).elim
    · exact ((mem_cellsK.mp hq').2 ⟨f, σ, bufs, kids, ht, t, htm, he.symm⟩).elim
    · rw [ht] at ht'
      cases ht'
      obtain rfl := cert_inj hW hC f t htm t' htm' he
      rfl

/-- **The back end's cells fit and agree.** -/
theorem cellsOk_B (hW : W.Compiled) {Is : List Memory.Inst}
    (hfound : ∀ I ∈ Is, ∃ fn, W.core.find? I.t.name = some fn) : CellsOk W.fsB W.cellsB Is where
  two_le I hI := by
    obtain ⟨fn, hf⟩ := hfound I hI
    exact two_le_fsB hW hf
  off _ _ _ hq := cellsB_off hq
  agree _ _ _ hq _ hq' he := by rw [cellsB_unique hq hq' he]

/-! ## The discharge -/

/-- **A placed run of `main` loading in its data meets the discharge's hypotheses** at the cells
`cellsT`. -/
theorem dischargeHyps_core (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) {hdr : E × E}
    {T : Tree} {M : MemoryImage (logMem (T.total W.fsB))}
    (hv : T.Valid W.core M.read [] []) (hb : T.BufsOk W.core)
    (hp : T.Placed W.core W.fsB W.cellB 0)
    (hl : T.LoadsIn W.core W.fsB W.cellB (fun i => i < 2) 0)
    (h0 : M.read (addressOfIndex 0) = some hdr.1) (h1 : M.read (addressOfIndex 1) = some hdr.2)
    (hs : T.total W.fsB ≤ 2 ^ 30)
    (ha : ∀ q ∈ T.eqns W.core, ∃ i : Fin (2 ^ logMem (T.total W.fsB)), q.1 = addressOfIndex i) :
    DischargeHyps W.core W.fsB W.cellB W.hdrB (cellsT W) hdr T (fun i => i < 2) M [] [] where
  fresh := core_fresh hW hC
  valid := hv
  bufsOk := hb
  placed := hp
  loads := hl
  region := fun _ hi => Or.inl hi
  hdr_read := ⟨h0, h1⟩
  size := hs
  addr := ha
  cells := cellsOk_T hW hC fun I hI => (insts_facts hW T 0 hdr hv I hI).1
  cells' := fun _ => cellsOk_T hW hC (retemp_found hW hv)
  cert_lt := cert_lt hW hC
  cert_inj := cert_inj hW hC
  run := by
    intro I hI f σ bufs kids ht p r rs ha' k hk
    obtain ⟨tf, pf, es, vs, hfo, hw, hev, hcl⟩ := clauses_at hW hC hv hp hI ht
    obtain ⟨htf, -, hpa, hlocs⟩ := fnOf_spec hfo
    have haes : Ev.atom (.frameAddr p (r :: rs)) ∈ es := hev ▸ ha'
    have hatom : Atom.frameAddr p (r :: rs) ∈ lAtomsK tf.core.body :=
      walk_atomsK (σ := σ) _ (by rw [hw]; exact haes)
    obtain ⟨ti, ti', hpl⟩ := placed_of hW htf hpa
    obtain ⟨b, hb'⟩ := placeFn_runs hpl hatom
    have hb0 : W.cellB f r = b := by
      unfold World.cellB
      rw [hlocs]
      have := hb' 0 (by simp)
      simp only [List.getElem_cons_zero] at this
      simp [cellP, this]
    have hloc : pf.locs[(r :: rs)[k]]? = some (.cell (W.cellB f r + k)) := by
      rw [hb0]; exact hb' k hk
    have hck : cellP pf.locs (r :: rs)[k] = some (W.cellB f r + k) := by simp [cellP, hloc]
    have huse : (r :: rs)[k] ∈ Ev.uses (Ev.atom (.frameAddr p (r :: rs))) := by
      simp [Ev.uses, atomUses]
    have hmemR : (r :: rs)[k] ∈ readsP tf.core.params tf.core.body σ es vs := by
      simp only [readsP, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨_, haes, huse⟩)))
    have hwi := walk_within (σ := σ) tf.core.body
    rw [hw] at hwi
    have hU : (r :: rs)[k] ∈ Stmt.usesList tf.core.body ++ tf.core.params :=
      List.mem_append_left _ (hwi.1 _ haes _ huse)
    have hapart : ∀ t ∈ W.core.temps f, W.cellB f r + k ≠ W.cellB f t := by
      intro t htm he
      rw [temps_of_fnOf hfo] at htm
      have := ((hC tf htf).tmps pf hpa).apart hU hloc htm
      obtain ⟨n, hn⟩ := ((hC tf htf).tmps pf hpa).cell htm
      have hcb : W.cellB f t = n := by unfold World.cellB; rw [hlocs, hn]; rfl
      apply this
      rw [hn, he, hcb]
      rfl
    obtain ⟨h2, hlt, hΨ⟩ := hcl.cell _ hmemR _ hck
    refine ⟨List.mem_append_left _ (mem_cellsK.mpr ⟨?_, ?_⟩), hapart⟩
    · rw [← hΨ]; exact own_mem hW ht hfo h2 hlt
    · rintro ⟨f', σ', b', k', ht', t, htm, he⟩
      rw [ht] at ht'
      cases ht'
      exact hapart t htm he
  tmp := by
    intro ν I' _ f σ bufs kids ht t htm q hq hq1
    rcases mem_cellsT hq with hq | ⟨f', σ', bufs', kids', ht', t', htm', rfl⟩
    · exact ((mem_cellsK.mp hq).2 ⟨f, σ, bufs, kids, ht, t, htm, hq1⟩).elim
    · rw [ht] at ht'
      cases ht'
      obtain rfl := cert_inj hW hC f t' htm' t htm hq1
      rfl
  keep := by
    intro ν I hI I' hI' hfp ht q hq hno
    obtain ⟨J, hJ, hJfp, hJt, hJh, hJk⟩ := insts_retempB T 0 hdr I' hI'
    have hfI := insts_facts hW T 0 hdr hv I hI
    obtain ⟨fn, hf⟩ := hfI.1
    have h2 := two_le_fsB hW hf
    obtain rfl : J = I := by
      refine insts_same hJ hI (i := I.fp) ⟨by omega, ?_⟩ ⟨le_rfl, by omega⟩
      have hn : J.t.name = I.t.name := by
        rw [← name_retemp (P := W.core) (fs := W.fsB) (ν := ν) J.fp J.t, ← hJt,
          ← name_retemp (P := W.core) (fs := W.fsB) (ν := ν) I.fp I.t, ← ht]
      rw [hn]; omega
    simp only [Inst.cells, List.mem_cons] at hq ⊢
    rcases hq with rfl | rfl | hq
    · exact Or.inl (by rw [hJh])
    · exact Or.inr (Or.inl (by rw [hJh]))
    · refine Or.inr (Or.inr ?_)
      rcases mem_cellsT hq with hq | ⟨f, σ', bufs, kids, ht', t, htm, rfl⟩
      · exact List.mem_append_left _ (mem_cellsK.mpr
          ⟨cellsB_retemp_keep hW hJt hJfp.symm hJh hJk (mem_cellsK.mp hq).1 hno, hno⟩)
      · exfalso
        rw [hJt] at ht'
        obtain ⟨σ₀, kids₀, hIt, -⟩ := node_of_retemp ht'
        exact hno ⟨f, σ₀, bufs, kids₀, hIt, t, htm, rfl⟩

/-! ## `HonestAt` from a core run -/

/-- **The honest memory at the back end's data from a core run**: a placed run loading
in its data or the public input, its temporaries re-chosen, is `HonestAt` the back end's frame
sizes, headers, cells and frame-address cells. -/
theorem honestAt_of_core (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) {hdr : E × E}
    {T : Tree} {M : MemoryImage (logMem (T.total W.fsB))}
    (hv : T.Valid W.core M.read [] []) (hb : T.BufsOk W.core)
    (hp : T.Placed W.core W.fsB W.cellB 0)
    (hl : T.LoadsIn W.core W.fsB W.cellB (fun i => i < 2) 0)
    (h0 : M.read (addressOfIndex 0) = some hdr.1) (h1 : M.read (addressOfIndex 1) = some hdr.2)
    (hs : T.total W.fsB ≤ 2 ^ 30)
    (ha : ∀ q ∈ T.eqns W.core, ∃ i : Fin (2 ^ logMem (T.total W.fsB)), q.1 = addressOfIndex i) :
    ∃ (ν : ℕ → String → Val → V → E) (rd : Reader),
      HonestAt W.core W.fsB W.hdrB W.cellsB hdr (T.retemp W.core W.fsB ν 0) W.cellB rd [] [] := by
  obtain ⟨ν, hH⟩ := honestAt_retemp (dischargeHyps_core hW hC hv hb hp hl h0 h1 hs ha)
  set T' := T.retemp W.core W.fsB ν 0
  have hsub : ∀ a ∈ frameWrites W.cellsB (honestInsts W.core W.fsB W.hdrB hdr T'),
      a ∈ frameWrites (cellsT W) (honestInsts W.core W.fsB W.hdrB hdr T') := by
    intro a ha'
    obtain ⟨J, hJ, c, hc, rfl⟩ := Memory.mem_frameWrites ha'
    refine honest_mem_frameWrites hJ ?_
    simp only [Inst.cells, List.mem_cons] at hc ⊢
    rcases hc with rfl | rfl | hc
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr ?_)
      by_cases hto : TmpOff W.core W.cellB J.t c.1
      · obtain ⟨f, σ, bufs, kids, hJt, t, htm, hc1⟩ := hto
        obtain ⟨tf, pf, es, vs, hfo, hw, -, hcl⟩ :=
          clauses_at hW hC hH.valid hH.placed hJ hJt
        obtain ⟨htf, -, hpa, hlocs⟩ := fnOf_spec hfo
        have htm' : t ∈ Stmt.tmpsList tf.core.body := by rw [← temps_of_fnOf hfo]; exact htm
        obtain ⟨n, hn⟩ := ((hC tf htf).tmps pf hpa).cell htm'
        have hcb : W.cellB f t = n := by unfold World.cellB; rw [hlocs, hn]; rfl
        obtain ⟨h2, hlt, hΨ⟩ := hcl.tmp ((hC tf htf).tmps pf hpa) t htm' n hn
        have hown := own_mem hW hJt hfo h2 hlt
        have hceq := cellsB_unique hc hown (by rw [hc1, hcb])
        rw [hceq, hΨ, ← hcb]
        exact tmp_mem_cellsT hJt htm
      · exact List.mem_append_left _ (mem_cellsK.mpr ⟨hc, hto⟩)
  exact ⟨ν, _,
    { valid := hH.valid
      size := hH.size
      cells := cellsOk_B hW (retemp_found hW hv)
      addr := hH.addr
      eqns := hH.eqns
      cross := fun a ha' b hb' he => hH.cross a (hsub a ha') b hb' he
      bufsOk := hH.bufsOk
      placed := hH.placed }⟩

end
end LeanVM.Compiler.Complete
