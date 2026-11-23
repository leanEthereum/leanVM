/-
  LeanVM.Guest.CoreMode.LoopPtr

  A loop helper's signature with pointer runs at a frame: its entry facts, its preconditions and its
  guarantees at return, as the heap signature's.
-/

module

public import LeanVM.Guest.CoreMode.CoreLoop
public import LeanVM.Guest.CoreMode.LoopSigP

/-!
# A loop helper's pointer runs at a frame

A loop helper's mode signature against its heap signature at a frame, pointer runs included (`SigLP`): its
termination facts are the heap check's entry facts (`termAt_entryFP`); its preconditions at entry are the heap
signature's (`preSet_of_entryP`, and back, `entry_of_preP`); its guarantees at return follow from the heap
signature's written (`retAll_of_wrkP`, and back, `postSet_of_retAllP`); the entry abstraction holds of a frame
with its entry cells and preconditions written (`holds_entryP`). A mode pointer run (`PW`) and its heap pointer
run are read through a reader consistent with the memory (`RdW`, mode to heap) or reading its written cells
(`RdM`, heap to mode).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Prover.Exec (St Mem maxCells)
open LeanVM.Guest.Mode (IdxVal RW HW PW MonoVal LTF TermAt RetAll entryAbs stOf)

@[expose] public section

/-- **The termination facts are the heap check's entry facts**, for `SigLP`. -/
theorem termAt_entryFP {G : Mode.Sig} {h : HSig} {np : ℕ} {ps : List ℕ} {gl : List (ℕ × ℕ × ℕ)} (hs : SigLP G h np ps gl) {s : St} {ws : List E}
    (hP : ParAt G np s ws) (hT : ∀ p ∈ G.term, LTF s p.1 p.2) : ∀ p ∈ h.term, LtF (slotW ws) (idxC p.1) (idxC p.2) := by
  obtain ⟨hi, ei, hG, hh, h2, hei⟩ := hs.term
  intro p hp
  rw [hh, List.mem_singleton] at hp
  subst hp
  obtain ⟨xa, xb, ha, hb, hab⟩ := hT _ (by rw [hG]; exact List.mem_singleton_self _)
  have h0 : idxT G np (.ex (.fr 2) 0) = some (.val 0) := by simp [idxT, h2]
  exact ⟨xa, xb, (idxVal_iff hP h0).mp ha, (idxVal_iff hP hei).mp hb, hab⟩

/-- **The guarantees at return**, from their heap cells written, its pointer runs' words read by a
reader of the memory's written cells. -/
theorem retAll_of_wrkP {G : Mode.Sig} {h : HSig} {np : ℕ} {ps : List ℕ} {gl : List (ℕ × ℕ × ℕ)} (hs : SigLP G h np ps gl) {m : Mem} {fp : ℕ} {ws : List E}
    (hP : ParAt G np (stOf m fp) ws) (hT : ∀ p ∈ G.term, LTF (stOf m fp) p.1 p.2)
    (hX : ExpM G (expCells G) (stOf m fp)) (hpost : ∀ c ∈ h.post, WrK m (c.addrW (slotW ws)))
    (hpostR : ∀ r ∈ h.postR, ∀ x, r.Set (slotW ws) x → WrK m x) {rd : Reader} (hrd : RdM rd m)
    (hptr : ∀ x, PtrSigSet rd h.postP h.postPR ws x → WrK m x) : RetAll m fp G := by
  have hRW : ∀ r ∈ G.postR ++ G.postL, RW (stOf m fp) r := fun r hr ↦ by
    obtain ⟨q, hq, hrq⟩ := (mapM_mem hs.postR).2 r hr
    have hk := hs.kpostR r hr
    simp only [rngKX, Bool.and_eq_true] at hk
    exact slot_rwT hP hrq (idxKX_val hT hX hk.1) (idxKX_val hT hX hk.2) (hpostR q hq)
  refine ⟨⟨fun o ho ↦ (by rw [hs.ret] at ho; cases ho), fun m0 hm0 ↦ ?_, fun r hr ↦ hRW r (List.mem_append_left _ hr),
    fun q hq ↦ (by rw [hs.postP] at hq; cases hq), fun p hp ↦ (by rw [hs.retV] at hp; cases hp),
    fun p hp ↦ (by rw [hs.postT] at hp; cases hp), fun q hq ↦ (by rw [hs.postC] at hq; cases hq)⟩,
    fun r hr ↦ hRW r (List.mem_append_right _ hr), fun q hq ↦ ?_⟩
  · obtain ⟨c, hc, hmc⟩ := (mapM_mem hs.post).2 m0 hm0
    exact slot_hwT hP hmc (hpost c hc)
  · obtain ⟨p, hp, hqp⟩ := (mapM_mem hs.postLP).2 q hq
    obtain ⟨hrq, hos⟩ := prT_spec hqp
    have hk := hs.kpostLP q hq
    simp only [rngKX, Bool.and_eq_true] at hk
    rw [← hos]
    exact slot_pwT hP hrq hrd (idxKX_val hT hX hk.1) (idxKX_val hT hX hk.2) (hpostR p.1 (hs.inPost p hp))
      fun x ⟨a, ha, hpa⟩ ↦ hptr x (Or.inr ⟨p, hp, a, ha, hpa⟩)

/-- **What a frame guarantees at return is its heap signature's guarantees written**, its pointer runs'
words read by a reader consistent with the memory. -/
theorem postSet_of_retAllP {G : Mode.Sig} {h : HSig} {np : ℕ} {ps : List ℕ} {gl : List (ℕ × ℕ × ℕ)} (hs : SigLP G h np ps gl) {m : Mem} {fp : ℕ} {ws : List E}
    (hP : ParAt G np (stOf m fp) ws) (hR : RetAll m fp G) {rd : Reader} (hrd : RdW rd m) :
    ∀ x, PostSet rd h ws x → WrK m x := by
  intro x hx
  replace hx := hx.imp_right fun h ↦ h.resolve_right fun ⟨q, hq, _⟩ ↦ by rw [hs.hpostQ] at hq; cases hq
  revert x hx
  rintro x ((⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, -⟩ | ⟨p, hp, a, ha, hpa⟩))
  · obtain ⟨m0, hm0, hmc⟩ := (mapM_mem hs.post).1 c hc
    exact hw_slotT hP hmc (hR.1.2.1 m0 hm0)
  · obtain ⟨r0, hr0, hrq⟩ := (mapM_mem hs.postR).1 r hr
    have hRW : RW (stOf m fp) r0 := by
      rcases List.mem_append.mp hr0 with h1 | h1
      · exact hR.1.2.2.1 r0 h1
      · exact hR.2.1 r0 h1
    exact rw_slotT hP hrq hRW x hx
  · rw [hs.hpostP] at hp; cases hp
  · obtain ⟨q, hq, hqp⟩ := (mapM_mem hs.postLP).1 p hp
    obtain ⟨hrq, hos⟩ := prT_spec hqp
    have hPW := hR.2.2 q hq
    rw [← hos] at hPW
    exact pw_slotT hP hrq hrd hPW x ⟨a, ha, hpa⟩

/-- **The preconditions at entry are the heap signature's written**, pointer runs included. -/
theorem preSet_of_entryP {G : Mode.Sig} {h : HSig} {np : ℕ} {ps : List ℕ} {gl : List (ℕ × ℕ × ℕ)} (hs : SigLP G h np ps gl) {s : St} {ws : List E}
    (hP : ParAt G np s ws) (hL : LinkM s gl ws) (hpre : ∀ m ∈ G.pre, HW s m) (hpreR : ∀ r ∈ G.preR, RW s r)
    (hpreP : ∀ q ∈ G.preP, PW s q.1 q.2) {rd : Reader} (hrd : RdW rd s.mem) :
    ∀ x, PreSet rd h ws x → WrK s.mem x := by
  rintro x ((⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, -⟩ | ⟨p, hp, a, ha, hpa⟩))
  · obtain ⟨m0, hm0, hmc⟩ := (mapM_mem hs.pre).1 c hc
    exact hw_slotT hP hmc (hpre m0 hm0)
  · obtain ⟨l, hl, hle⟩ := Option.map_eq_some_iff.mp hs.preR
    rw [← hle] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r0, hr0, hrq⟩ := (mapM_mem hl).1 r hr
      unfold rngTG at hrq
      split at hrq
      · rename_i q hq
        cases hrq
        exact rw_rngH hL hq (hpreR r0 hr0) x hx
      · exact rw_slotT hP hrq (hpreR r0 hr0) x hx
    · obtain ⟨d, hd, rfl⟩ := addrRs_mem hr
      rw [addr_set] at hx
      subst hx
      obtain ⟨-, ⟨b, k, hb⟩, hF⟩ := lgOk_link hs.hghost hd
      obtain ⟨r1, hr1, hbs⟩ := List.any_eq_true.mp (List.all_eq_true.mp hs.dsIn d hd)
      obtain ⟨vq, -, xhi, hv, -, hih, -⟩ := hpreR r1 hr1
      rcases Bool.or_eq_true_iff.mp hbs with hbs | hbs
      · rw [show r1.q = ⟨r1.q.fp, r1.q.k, [(.hp 1 d, 1)]⟩ by rw [← of_decide_eq_true hbs]] at hv
        obtain ⟨u, hu⟩ := baseVal_of_mono hv
        exact addr_wrk hL hb hF hu
      · rw [of_decide_eq_true hbs] at hih
        obtain ⟨u, hu⟩ := baseVal_of_idx hih
        exact addr_wrk hL hb hF hu
  · rw [hs.hpreP] at hp; cases hp
  · obtain ⟨q, hq, hqp⟩ := (mapM_mem hs.preP).1 p hp
    obtain ⟨hrq, hos⟩ := prT_spec hqp
    have hPW := hpreP q hq
    rw [← hos] at hPW
    exact pw_slotT hP hrq hrd hPW x ⟨a, ha, hpa⟩

/-- **The entry facts are the heap signature's preconditions**, pointer runs included, their words read
by a reader of the memory's written cells. -/
theorem entry_of_preP {G : Mode.Sig} {h : HSig} {np : ℕ} {ps : List ℕ} {gl : List (ℕ × ℕ × ℕ)} (hs : SigLP G h np ps gl) {s : St} {ws : List E}
    (hP : ParAt G np s ws) (hL : LinkM s gl ws) (hT : ∀ p ∈ G.term, LTF s p.1 p.2) (hX : ExpM G ps s) {W : K → Prop}
    (hW : ∀ x, W x → WrK s.mem x)
    (hpre : SigOk W h.pre h.preR ws) {rd : Reader} (hptr : PtrOk W rd h.preP h.prePR ws) (hrd : RdM rd s.mem)
    (hE : ∀ r ∈ G.preR, ∀ q, rngH gl r = some q → ∃ y, rep ((idxC q.hi).valW (slotW ws)) = some y) :
    (∀ m ∈ G.pre, HW s m) ∧ (∀ r ∈ G.preR, RW s r) ∧ ∀ q ∈ G.preP, PW s q.1 q.2 := by
  obtain ⟨l, hl, hle⟩ := Option.map_eq_some_iff.mp hs.preR
  refine ⟨fun m hm ↦ ?_, fun r hr ↦ ?_, fun q hq ↦ ?_⟩
  · obtain ⟨c, hc, hmc⟩ := (mapM_mem hs.pre).2 m hm
    exact slot_hwT hP hmc (hW _ (hpre.1 c hc))
  · obtain ⟨q, hq, hrq⟩ := (mapM_mem hl).2 r hr
    have hq' : q ∈ h.preR := by rw [← hle]; exact List.mem_append_left _ hq
    unfold rngTG at hrq
    split at hrq
    · rename_i q' hq''
      cases hrq
      obtain ⟨d, b, -, hi, hrq', -, hhi, hlk, hd0, -⟩ := rngH_spec hq''
      have hds := lgOk_ds hs.hghost (lookup_memL hlk) hd0
      obtain ⟨-, -, hF⟩ := lgOk_link hs.hghost hds
      refine rngH_rw hL hq'' hF (fun d' hd' ↦ ?_) (hE r hr _ hq'') fun x hx ↦ hW x (hpre.2 q hq' x hx)
      have hds' : d' ∈ glDs gl := by
        rcases hd' with hd' | hd'
        · have hdd : d' = d := by
            rw [hrq'] at hd'
            simpa using hd'.symm
          exact hdd ▸ hds
        · rcases hiH_spec hhi with ⟨n, hn, -⟩ | ⟨d'', b'', k'', hd'', hd0'', hl'', -, -⟩
          · rw [hn] at hd'; cases hd'
          · rw [hd''] at hd'
            cases hd'
            exact lgOk_ds hs.hghost (lookup_memL hl'') hd0''
      have hA : (⟨⟨[(glFs gl, 1)], d'⟩, 1, .num 0, .num 1⟩ : CRun) ∈ h.preR := by
        rw [← hle]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨d', hds', rfl⟩)
      exact hW _ (hpre.2 _ hA _ (addr_set.mpr rfl))
    · rename_i hq0
      have hk := (hs.kpreR r hr).resolve_left (by simp [hq0])
      simp only [rngKX, Bool.and_eq_true] at hk
      exact slot_rwT hP hrq (idxKX_val hT hX hk.1) (idxKX_val hT hX hk.2) fun x hx ↦ hW x (hpre.2 q hq' x hx)
  · obtain ⟨p, hp, hqp⟩ := (mapM_mem hs.preP).2 q hq
    obtain ⟨hrq, hos⟩ := prT_spec hqp
    have hk := hs.kpreP q hq
    simp only [rngKX, Bool.and_eq_true] at hk
    rw [← hos]
    exact slot_pwT hP hrq hrd (idxKX_val hT hX hk.1) (idxKX_val hT hX hk.2)
      (fun x hx ↦ hW x (hpre.2 p.1 (hs.inPre p hp) x hx)) fun x ⟨a, ha, hpa⟩ ↦ hW x (hptr x (Or.inr ⟨p, hp, a, ha, hpa⟩))

/-- **The entry abstraction's pointer runs**: the signature's preconditions `preP`. -/
theorem entry_preP {E0 : Mode.Env} {G : Mode.Sig} {s : St} (h : Mode.Holds s (entryAbs E0 G)) :
    ∀ q ∈ G.preP, PW s q.1 q.2 := by
  unfold entryAbs at h
  rcases hs : G.self with _ | o
  · rw [hs] at h
    exact h.p
  · rw [hs] at h
    simp only [Mode.Abs.addW, Mode.Abs.addV, Mode.Abs.addNz] at h
    exact h.p

/-- **The entry abstraction holds** of a frame with its entry cells written, its preconditions
(pointer runs included), the jump table, its termination facts, its self cell holding its frame's
address. -/
theorem holds_entryP {E0 : Mode.Env} {G : Mode.Sig} {s : St} (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true)
    (hpre : ∀ m ∈ G.pre, HW s m) (hjt : RW s (Mode.jtRng E0)) (hpreR : ∀ r ∈ G.preR, RW s r)
    (hpreP : ∀ q ∈ G.preP, PW s q.1 q.2) (hT : ∀ p ∈ G.term, LTF s p.1 p.2)
    (hself : ∀ o, G.self = some o → s.mem.written (s.fp + o) = true ∧ s.mem.get (s.fp + o) = some (ofK (g ^ s.fp))) :
    Mode.Holds s (entryAbs E0 G) := by
  have h0 : Mode.Holds s ⟨Mode.foldlT .nil G.entry, .nil, .nil, [], G.pre, Mode.jtRng E0 :: G.preR, G.term, [], .nil,
      G.preP, []⟩ :=
    ⟨fun o ho ↦ hw o (foldlT_nil_get ho), fun o x hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
      fun o hx ↦ (by rw [trieNil_get rfl] at hx; cases hx), fun p hp ↦ (by cases hp), hpre,
      fun r hr ↦ (List.mem_cons.mp hr).elim (fun h ↦ h ▸ hjt) (hpreR r), hT, fun p hp ↦ (by cases hp),
      fun c a b hx ↦ (by rw [trieNil_get rfl] at hx; cases hx), hpreP,
      fun q hq ↦ (by cases hq)⟩
  unfold entryAbs
  rcases hs : G.self with _ | o
  · exact h0
  · obtain ⟨hwo, hgo⟩ := hself o hs
    refine ((h0.addW hwo).addV ⟨_, hgo, ?_⟩).addNz ⟨_, hgo, Mode.ofK_gpow_ne_zero _⟩
    exact ⟨1, rfl, by simp [Mode.Mono.own]⟩

end

end LeanVM.Guest.CoreMode
