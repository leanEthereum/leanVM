/-
  LeanVM.Compiler.Complete.CoreCells
  The back end's cells and headers at a core run: the cells fit and agree, the temporaries' cells
  are apart and in the frame, and re-choosing the temporaries keeps every other cell and every
  header.
-/

module

public import LeanVM.Compiler.Complete.ProgramCore
public import LeanVM.Compiler.Complete.ProgFrames
public import LeanVM.Compiler.Complete.InFrameFn

/-!
# The back end's cells at a core run

* `cellsB_off`, `cellsB_unique`: a frame's cells lie in `[2, fsB)`, one word per offset.
* `cellsK`: the cells off the temporaries' cells (`TmpOff`); `cellsOk_K`: they fit and agree at
  any instances of functions of the program (`insts_found`: every instance of a run of `main`).
* `core_fresh`, `cert_lt`, `cert_inj`: the temporaries are fresh, in the frame, in cells of their
  own (`TmpsApart`).
* `famB_congr`: the frame family is blind to the temporaries (`FrameCongr`), so re-choosing them
  keeps every header (`hdrB_retemp`, `insts_retempB`) and every cell off theirs
  (`cellsB_retemp_keep`).
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Frames from candidates -/

theorem dedupB_unique : ∀ {L : List (ℕ × E)} {q q' : ℕ × E}, q ∈ dedupB L → q' ∈ dedupB L →
    q.1 = q'.1 → q = q'
  | [], _, _, h, _, _ => by simp [dedupB] at h
  | x :: xs, q, q', h, h', he => by
    rw [dedupB] at h h'
    rcases List.mem_cons.mp h with rfl | h <;> rcases List.mem_cons.mp h' with rfl | h'
    · rfl
    · simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at h'
      exact (h'.2 he.symm).elim
    · simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at h
      exact (h.2 he).elim
    · exact dedupB_unique (List.mem_filter.mp h).1 (List.mem_filter.mp h').1 he

/-- Candidates changed only at offsets in `S` keep the frame's cells off `S`. -/
theorem dedupB_map_congr {α : Type} (g g' : α → ℕ × E) (S : ℕ → Prop) (p : ℕ → Bool)
    (hfst : ∀ a, (g' a).1 = (g a).1) :
    ∀ (A : List α), (∀ a ∈ A, ¬ S (g' a).1 → g' a = g a) → ∀ {q : ℕ × E},
      q ∈ dedupB ((A.map g').filter fun q => p q.1) → ¬ S q.1 →
      q ∈ dedupB ((A.map g).filter fun q => p q.1)
  | [], _, _, h, _ => by simp [dedupB] at h
  | a :: A, hS, q, h, hq => by
    rw [List.map_cons] at h ⊢
    by_cases hp : p (g a).1 = true
    · rw [List.filter_cons_of_pos (p := fun q : ℕ × E => p q.1) (by rw [hfst]; exact hp), dedupB] at h
      rw [List.filter_cons_of_pos (p := fun q : ℕ × E => p q.1) hp, dedupB]
      rcases List.mem_cons.mp h with rfl | h
      · rw [hS a List.mem_cons_self hq]; exact List.mem_cons_self
      · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
        refine List.mem_cons_of_mem _ (List.mem_filter.mpr
          ⟨dedupB_map_congr g g' S p hfst A (fun b hb => hS b (List.mem_cons_of_mem _ hb)) h1 hq, ?_⟩)
        rwa [← hfst]
    · rw [List.filter_cons_of_neg (p := fun q : ℕ × E => p q.1) (by rw [hfst]; exact hp)] at h
      rw [List.filter_cons_of_neg (p := fun q : ℕ × E => p q.1) hp]
      exact dedupB_map_congr g g' S p hfst A (fun b hb => hS b (List.mem_cons_of_mem _ hb)) h hq

variable {κ₀ : ℕ} {W : World κ₀}

/-- **A frame's cells lie past the header and in the frame.** -/
theorem cellsB_off {I : Memory.Inst} {q : ℕ × E} (hq : q ∈ W.cellsB I) :
    2 ≤ q.1 ∧ q.1 < W.fsB I.t.name := by
  unfold World.cellsB at hq
  rcases ht : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩ <;> rw [ht] at hq <;> simp only at hq
  · split at hq
    · exact (frameB_sub hq).2
    · exact absurd hq List.not_mem_nil
  · split at hq
    · exact (frameB_sub hq).2
    · exact absurd hq List.not_mem_nil

/-- **A frame holds one word per offset.** -/
theorem cellsB_unique {I : Memory.Inst} {q q' : ℕ × E} (hq : q ∈ W.cellsB I)
    (hq' : q' ∈ W.cellsB I) (he : q.1 = q'.1) : q = q' := by
  unfold World.cellsB at hq hq'
  rcases ht : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩ <;> rw [ht] at hq hq' <;> simp only at hq hq'
  · split at hq
    · next hfo => rw [hfo] at hq'; exact dedupB_unique hq hq' he
    · exact absurd hq List.not_mem_nil
  · split at hq
    · next hfo => rw [hfo] at hq'; exact dedupB_unique hq hq' he
    · exact absurd hq List.not_mem_nil

open Classical in
/-- **The back end's cells off the temporaries' cells.** -/
noncomputable def cellsK (W : World κ₀) (I : Memory.Inst) : List (ℕ × E) :=
  (W.cellsB I).filter fun q => !decide (TmpOff W.core W.cellB I.t q.1)

theorem mem_cellsK {I : Memory.Inst} {q : ℕ × E} :
    q ∈ cellsK W I ↔ q ∈ W.cellsB I ∧ ¬ TmpOff W.core W.cellB I.t q.1 := by
  unfold cellsK
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]

/-- A function of the program has a frame of at least its header and arguments. -/
theorem two_le_fsB (hW : W.Compiled) {f : String} {fn : Fn} (hf : W.core.find? f = some fn) :
    2 ≤ W.fsB f := by
  obtain ⟨tf, htf, rfl, rfl⟩ := core_find hf
  obtain ⟨pf, -, hpa⟩ := fnOf_of_mem hW htf
  have := (placed_size hW htf hpa).1
  have := frame_le_fsB hW htf hpa
  omega

/-- **The cells off the temporaries' fit and agree**, at instances of functions of the program. -/
theorem cellsOk_K (hW : W.Compiled) {Is : List Memory.Inst}
    (hfound : ∀ I ∈ Is, ∃ fn, W.core.find? I.t.name = some fn) : CellsOk W.fsB (cellsK W) Is where
  two_le I hI := by
    obtain ⟨fn, hf⟩ := hfound I hI
    exact two_le_fsB hW hf
  off _ _ _ hq := cellsB_off (mem_cellsK.mp hq).1
  agree _ _ _ hq _ hq' he := by
    rw [cellsB_unique (mem_cellsK.mp hq).1 (mem_cellsK.mp hq').1 he]

/-! ## The temporaries -/

/-- A function found by name is the program's. -/
theorem find_of_fnOf {f : String} {tf : TracedFn} {pf : Placed} (h : W.fnOf f = some (tf, pf)) :
    W.core.find? f = some tf.core := by
  unfold World.fnOf at h
  split at h
  · next tf' pf' h1 h2 =>
    cases h
    unfold World.core Program.find?
    rw [List.find?_map]
    simp only [Function.comp_def, h1, Option.map_some]
  · cases h

theorem temps_of_fnOf {f : String} {tf : TracedFn} {pf : Placed} (h : W.fnOf f = some (tf, pf)) :
    W.core.temps f = Stmt.tmpsList tf.core.body := by
  unfold Program.temps
  rw [find_of_fnOf h]

/-- **The temporaries are fresh.** -/
theorem core_fresh (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) : W.core.Fresh := by
  intro fn hfn
  unfold World.core at hfn
  obtain ⟨tf, htf, rfl⟩ := List.mem_map.mp hfn
  obtain ⟨pf, -, hpa⟩ := fnOf_of_mem hW htf
  exact ((hC tf htf).tmps pf hpa).fresh

/-- A temporary's cell is the back end's cell of it. -/
theorem temp_cellP (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) {f : String} {fn : Fn}
    (hf : W.core.find? f = some fn) {t : V} (ht : t ∈ Stmt.tmpsList fn.body) :
    ∃ tf pf, tf ∈ W.p ∧ tf.core = fn ∧ W.fnOf f = some (tf, pf) ∧ World.PlacedAs W tf pf ∧
      cellP pf.locs t = some (W.cellB f t) := by
  obtain ⟨tf, htf, rfl, hname⟩ := core_find hf
  obtain ⟨pf, hfo, hpa⟩ := fnOf_of_mem hW htf
  rw [hname] at hfo
  obtain ⟨n, hn⟩ := ((hC tf htf).tmps pf hpa).cell ht
  refine ⟨tf, pf, htf, rfl, hfo, hpa, ?_⟩
  unfold World.cellB
  rw [(fnOf_spec hfo).2.2.2, hn]
  rfl

/-- **The temporaries' cells are past the header and in the frame.** -/
theorem cert_lt (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) :
    ∀ f, ∀ t ∈ W.core.temps f, 2 ≤ W.cellB f t ∧ W.cellB f t < W.fsB f := by
  intro f t ht
  unfold Program.temps at ht
  split at ht
  · next fn hf =>
    obtain ⟨tf, pf, htf, rfl, hfo, hpa, hn⟩ := temp_cellP hW hC hf ht
    obtain ⟨ti, ti', hpl⟩ := placed_of hW htf hpa
    obtain ⟨hb1, hb2⟩ := placeFn_inFrame _ _ _ _ tf pf hpl (hC tf htf).isScoped t _ hn
    have hle := frame_le_fsB hW htf hpa
    rw [(fnOf_spec hfo).2.1] at hle
    exact ⟨hb1, lt_of_lt_of_le hb2 hle⟩
  · simp at ht

/-- **The temporaries have cells of their own.** -/
theorem cert_inj (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) :
    ∀ f, ∀ t ∈ W.core.temps f, ∀ t' ∈ W.core.temps f, W.cellB f t = W.cellB f t' → t = t' := by
  intro f t ht t' ht' he
  unfold Program.temps at ht ht'
  split at ht
  · next fn hf =>
    rw [hf] at ht'
    simp only at ht'
    obtain ⟨tf, pf, htf, rfl, hfo, hpa, hn⟩ := temp_cellP hW hC hf ht
    obtain ⟨tf2, pf2, -, -, hfo2, -, hn2⟩ := temp_cellP hW hC hf ht'
    simp only [hfo, Option.some.injEq, Prod.mk.injEq] at hfo2
    obtain ⟨rfl, rfl⟩ := hfo2
    rw [he] at hn
    exact ((hC tf htf).tmps pf hpa).inj t ht t' ht' _ hn hn2
  · simp at ht

/-! ## Re-choosing the temporaries -/

variable (W) in
/-- **The frame family is blind to the temporaries.** -/
theorem famB_congr (tf : TracedFn) (pf : Placed) (fp : ℕ) (kfps : List ℕ) (hdr : E × E)
    {σ σ' : Val} (hσ : ∀ v, v ∉ Stmt.tmpsList tf.core.body → σ' v = σ v) :
    (∀ n, (∀ t ∈ Stmt.tmpsList tf.core.body, cellP pf.locs t ≠ some n) →
      (W.famB tf pf fp kfps hdr σ').Ψ n = (W.famB tf pf fp kfps hdr σ).Ψ n) ∧
    (W.famB tf pf fp kfps hdr σ').kh = (W.famB tf pf fp kfps hdr σ).kh := by
  unfold World.famB
  split
  · next h => exact (Classical.choose_spec h).1 σ σ' hσ
  · exact ⟨fun _ _ => rfl, rfl⟩

variable {ν : ℕ → String → Val → V → E}

theorem retemp_off {f : String} {tf : TracedFn} {pf : Placed} (hfo : W.fnOf f = some (tf, pf))
    (fp : ℕ) (σ : Val) :
    ∀ v, v ∉ Stmt.tmpsList tf.core.body → retempVal W.core ν fp f σ v = σ v := by
  intro v hv
  unfold retempVal
  simp only [temps_of_fnOf hfo, hv, ↓reduceIte]

/-- **Re-choosing the temporaries keeps the callees' headers.** -/
theorem hdrB_retemp {J J' : Memory.Inst} (ht : J'.t = J.t.retemp W.core W.fsB ν J.fp)
    (hfp : J'.fp = J.fp) (hh : J'.hdr = J.hdr) (hk : J'.kidFps = J.kidFps) (j : ℕ) :
    W.hdrB J' j = W.hdrB J j := by
  unfold World.hdrB World.wordsB
  rw [ht, hfp, hh, hk]
  rcases hJ : J.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
  · rw [retemp_node]
    cases hfo : W.fnOf f with
    | none => simp only [hfo, Option.map_none]
    | some p =>
      obtain ⟨tf, pf⟩ := p
      simp only [hfo, Option.map_some]
      rw [(famB_congr W tf pf J.fp J.kidFps J.hdr (retemp_off hfo J.fp σ)).2]
  · rw [retemp_phantom]

mutual
/-- **Every instance of the re-chosen tree is an instance of the tree re-chosen**, at the same
frame, header and callee frames. -/
theorem insts_retempB : ∀ (t : Tree) (fp : ℕ) (hdr : E × E),
    ∀ I' ∈ (t.retemp W.core W.fsB ν fp).insts W.fsB W.core.loop W.hdrB fp hdr,
      ∃ I ∈ t.insts W.fsB W.core.loop W.hdrB fp hdr, I.fp = I'.fp ∧
        I'.t = I.t.retemp W.core W.fsB ν I.fp ∧ I'.hdr = I.hdr ∧ I'.kidFps = I.kidFps
  | .node f σ bufs kids, fp, hdr, I', hI' => by
      rw [retemp_node, insts_node, List.mem_cons] at hI'
      rw [map_total_retempKids_kidPos] at hI'
      rcases hI' with rfl | hI'
      · refine ⟨⟨.node f σ bufs kids, fp, hdr,
          kidPos W.fsB W.core.loop fp f bufs (kids.map (Tree.total W.fsB)),
          bases (bufBase W.fsB W.core.loop fp f (kids.map (Tree.total W.fsB))) bufs⟩,
          by rw [insts_node]; exact List.mem_cons_self, rfl, ?_, rfl, rfl⟩
        simp only
        rw [retemp_node]
      · obtain ⟨I, hI, h⟩ := instsKids_retempB kids
          (kidPos W.fsB W.core.loop fp f bufs (kids.map (Tree.total W.fsB)))
          ⟨.node f σ bufs kids, fp, hdr,
            kidPos W.fsB W.core.loop fp f bufs (kids.map (Tree.total W.fsB)),
            bases (bufBase W.fsB W.core.loop fp f (kids.map (Tree.total W.fsB))) bufs⟩
          ⟨.node f (retempVal W.core ν fp f σ) bufs (Tree.retempKids W.core W.fsB ν
              (kidPos W.fsB W.core.loop fp f bufs (kids.map (Tree.total W.fsB))) kids), fp, hdr,
            kidPos W.fsB W.core.loop fp f bufs (kids.map (Tree.total W.fsB)),
            bases (bufBase W.fsB W.core.loop fp f (kids.map (Tree.total W.fsB))) bufs⟩ 0
          (by simp only; rw [retemp_node]) rfl rfl rfl I' hI'
        exact ⟨I, by rw [insts_node]; exact List.mem_cons_of_mem _ hI, h⟩
  | .phantom f σ, fp, hdr, I', hI' => by
      rw [retemp_phantom, insts_phantom, List.mem_singleton] at hI'
      subst hI'
      exact ⟨⟨.phantom f σ, fp, hdr, [], []⟩, by rw [insts_phantom]; exact List.mem_singleton_self _,
        rfl, by simp only; rw [retemp_phantom], rfl, rfl⟩

/-- `insts_retempB` for the callees at `ps`. -/
theorem instsKids_retempB : ∀ (ks : List Tree) (ps : List ℕ) (J J' : Memory.Inst) (j : ℕ),
    J'.t = J.t.retemp W.core W.fsB ν J.fp → J'.fp = J.fp → J'.hdr = J.hdr →
    J'.kidFps = J.kidFps →
    ∀ I' ∈ Tree.instsKids W.fsB W.core.loop W.hdrB J' j ps (Tree.retempKids W.core W.fsB ν ps ks),
      ∃ I ∈ Tree.instsKids W.fsB W.core.loop W.hdrB J j ps ks, I.fp = I'.fp ∧
        I'.t = I.t.retemp W.core W.fsB ν I.fp ∧ I'.hdr = I.hdr ∧ I'.kidFps = I.kidFps
  | [], _, _, _, _, _, _, _, _, I', hI' => by
      rw [retempKids_nil, instsKids_nil] at hI'; exact (List.not_mem_nil hI').elim
  | _ :: _, [], _, _, _, _, _, _, _, I', hI' => by
      rw [instsKids_nil_left] at hI'; exact (List.not_mem_nil hI').elim
  | k :: ks, p :: ps, J, J', j, ht, hfp, hh, hk, I', hI' => by
      rw [retempKids_cons, instsKids_cons, List.mem_append] at hI'
      rw [instsKids_cons]
      rcases hI' with hI' | hI'
      · rw [hdrB_retemp ht hfp hh hk j] at hI'
        obtain ⟨I, hI, h⟩ := insts_retempB k p (W.hdrB J j) I' hI'
        exact ⟨I, List.mem_append_left _ hI, h⟩
      · obtain ⟨I, hI, h⟩ := instsKids_retempB ks ps J J' (j + 1) ht hfp hh hk I' hI'
        exact ⟨I, List.mem_append_right _ hI, h⟩
end

/-- **Re-choosing the temporaries keeps every cell off theirs.** -/
theorem cellsB_retemp_keep (hW : W.Compiled) {I I' : Memory.Inst}
    (ht : I'.t = I.t.retemp W.core W.fsB ν I.fp) (hfp : I'.fp = I.fp) (hh : I'.hdr = I.hdr)
    (hk : I'.kidFps = I.kidFps) {q : ℕ × E} (hq : q ∈ W.cellsB I')
    (hno : ¬ TmpOff W.core W.cellB I.t q.1) : q ∈ W.cellsB I := by
  rcases hI : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
  · rw [hI, retemp_node] at ht
    cases hfo : W.fnOf f with
    | none =>
      unfold World.cellsB at hq
      rw [ht] at hq
      simp only [hfo] at hq
      exact absurd hq List.not_mem_nil
    | some p =>
      obtain ⟨tf, pf⟩ := p
      rw [cellsB_node ht hfo, hfp, hh, hk] at hq
      rw [cellsB_node hI hfo]
      obtain ⟨htf, hname, hpa, hlocs⟩ := fnOf_spec hfo
      have hcg := famB_congr W tf pf I.fp I.kidFps I.hdr (retemp_off hfo I.fp σ (ν := ν))
      set Ψ := (W.famB tf pf I.fp I.kidFps I.hdr σ).Ψ
      set Ψ' := (W.famB tf pf I.fp I.kidFps I.hdr (retempVal W.core ν I.fp f σ)).Ψ
      set A := (List.range pf.fn.frameSize).map (fun n => (n, Ψ n)) ++
        (if f = "main" then W.tableB else [])
      have hA' : (List.range pf.fn.frameSize).map (fun n => (n, Ψ' n)) ++
          (if f = "main" then W.tableB else []) =
          A.map (fun q => if q.1 < pf.fn.frameSize then (q.1, Ψ' q.1) else q) := by
        simp only [A, List.map_append, List.map_map]
        congr 1
        · refine List.map_congr_left fun n hn => ?_
          simp only [Function.comp_apply, List.mem_range.mp hn, ↓reduceIte]
        · split
          · next hm =>
            refine (List.map_congr_left fun q hq => ?_).trans (List.map_id _) |>.symm
            obtain ⟨s, -, hs, -⟩ := tableB_off hq
            have := (fsB_main hW hpa (hname.trans hm)).1
            simp only [id_eq, show ¬ q.1 < pf.fn.frameSize by omega, ↓reduceIte]
          · rfl
      have hmap : ∀ L : List (ℕ × E), L = L.map id := fun L => (List.map_id L).symm
      unfold frameB at hq ⊢
      rw [hA'] at hq
      rw [hmap A] at ⊢
      refine dedupB_map_congr id (fun q => if q.1 < pf.fn.frameSize then (q.1, Ψ' q.1) else q)
        (fun n => TmpOff W.core W.cellB I.t n) (fun i => Nat.ble 2 i && Nat.blt i (W.fsB f))
        (fun q => by simp only [id_eq]; split <;> rfl) A (fun q hqA hq' => ?_) hq hno
      by_cases hlt : q.1 < pf.fn.frameSize
      · simp only [hlt, ↓reduceIte, id_eq] at hq' ⊢
        have hqΨ : q = (q.1, Ψ q.1) := by
          rcases List.mem_append.mp hqA with h | h
          · obtain ⟨n, -, rfl⟩ := List.mem_map.mp h; rfl
          · split at h
            · next hm =>
              obtain ⟨s, -, hs, -⟩ := tableB_off h
              have := (fsB_main hW hpa (hname.trans hm)).1
              omega
            · exact absurd h List.not_mem_nil
        rw [hcg.1 q.1 fun t htm he => hq' ⟨f, σ, bufs, kids, hI, t,
          by rw [temps_of_fnOf hfo]; exact htm, by unfold World.cellB; rw [hlocs, he]; rfl⟩]
        exact hqΨ.symm
      · simp only [hlt, ↓reduceIte, id_eq]
  · rw [hI, retemp_phantom] at ht
    rw [← hI] at ht
    unfold World.cellsB at hq ⊢
    rw [ht, hfp, hh, hk] at hq
    exact hq
end
end LeanVM.Compiler.Complete
