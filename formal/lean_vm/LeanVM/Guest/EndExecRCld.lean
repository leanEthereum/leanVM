/-
  LeanVM.Guest.EndExecRCld

  `claim_list_digest`'s residuals at its honest frames: the dispatch's selector, `list_split`'s
  `rest`, read through the callee's frame, below `17`, and the tiles of its count by the split.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.EndExecRA
public import LeanVM.Guest.Res.CldChk
public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.EndExecRTile

/-!
# `claim_list_digest`'s residual

Its one residual, `[[23]·g^5] < 17` at offset `99` (`Res.cld_res`), is the dispatch on `rest`
inside the nonempty list's branch. At an honest frame there (`TopAt`), the frame's position is the
alignment's at `99`, atoms then the dispatch (`Res.cld_al`), so the path's rest calls a last
claim (`dispatch_call`), and the path took the branch (the empty list's calls nothing). Its first
call is `list_split`'s: cell `23` holds the callee's frame pointer (`FrameHolds.site`,
`Res.cld_site`), the callee's frame holds its last return `rest` at cell `5` (`FrameHolds.val`,
`Res.ls_cell`, `Res.ls_ret`), and `rest = g^c`, `c < 17` (`list_split_sound`).

Its tiles (`Res.tileListB`) are of its count `n_g` into `list_split`'s returns: `tile_cld`, at every
honest frame, `n_g = 1` (the test `n_g + 1 = 0`, `Res.cld_wit`), or the nonempty list's branch,
whose first call is `list_split`'s (`cld_else_calls`), its returns `g^a`, `g^b`, `g^c` at cells `3`,
`4`, `5` of the callee's frame and `n_g = g^(136a + 17b + c)` (`list_split_sound`). `tiles_ok`,
`tileFam_top`: the tile families at the honest frames.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf siteOf)
open LeanVM.Guest.Bridge (alignA)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

theorem headDispatch_sound : ∀ {p : List Stmt}, Res.headDispatch p = true →
    ∃ (bs : List Atom) (x : V) (fs : List String) (args rets : List V) (rest : List Stmt),
      p = bs.map Stmt.atom ++ .dispatch x fs args rets :: rest
  | [], h => by simp [Res.headDispatch] at h
  | .atom a :: ss, h => by
    obtain ⟨bs, x, fs, args, rets, rest, rfl⟩ := headDispatch_sound (p := ss) h
    exact ⟨a :: bs, x, fs, args, rets, rest, rfl⟩
  | .dispatch x fs args rets :: rest, _ => ⟨[], x, fs, args, rets, rest, rfl⟩
  | .ite .. :: _, h | .match_ .. :: _, h | .call .. :: _, h | .callIf .. :: _, h | .ret _ :: _, h => by
    simp [Res.headDispatch] at h

theorem pick_cases {σ : Core.Val} {x : V} {args rets : List V} : ∀ (j : ℕ) (fs : List String),
    Memory.pick σ x args rets j fs = .stuck ∨ ∃ g, Memory.pick σ x args rets j fs = .fall [.call g args rets]
  | _, [] => Or.inl rfl
  | j, f :: fs => by
    unfold Memory.pick
    split_ifs
    · exact Or.inr ⟨f, rfl⟩
    · exact pick_cases (j + 1) fs

/-- **A dispatch past atoms calls**, on a returning path. -/
theorem dispatch_call {σ : Core.Val} {bs : List Atom} {x : V} {fs : List String} {args rets : List V}
    {rest : List Stmt} {es : List Ev} {vs : List V}
    (h : Memory.walk σ (bs.map Stmt.atom ++ .dispatch x fs args rets :: rest) = .ret es vs) :
    ∃ g, Ev.call g args rets ∈ es := by
  rw [Bridge.walk_atoms_pre] at h
  obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
  rw [Memory.walk, Memory.walk1] at h'
  rcases pick_cases (σ := σ) (x := x) (args := args) (rets := rets) 0 fs with hp | ⟨g, hp⟩
  · rw [hp] at h'; simp [Out.seq] at h'
  · rw [hp, Out.seq] at h'
    obtain ⟨es'', -, rfl⟩ := Bridge.pre_eq_ret h'
    exact ⟨g, List.mem_append_right _ List.mem_cons_self⟩

/-- **A body of atoms then a `ret` returns its words.** -/
theorem retLast_sound {σ : Core.Val} : ∀ {ss : List Stmt} {vs0 : List V} {es : List Ev} {vs : List V},
    Res.retLast ss = some vs0 → Memory.walk σ ss = .ret es vs → vs = vs0
  | [.ret v], vs0, es, vs, h, hw => by
    simp only [Res.retLast, Option.some.injEq] at h
    subst h
    simp only [Memory.walk, Memory.walk1, Out.seq] at hw
    exact (Out.ret.inj hw).2.symm
  | .atom a :: ss, vs0, es, vs, h, hw => by
    rw [Bridge.walk_atom_cons] at hw
    obtain ⟨es', hw', -⟩ := Bridge.pre_eq_ret hw
    exact retLast_sound (ss := ss) h hw'
  | [], _, _, _, h, _ => by simp [Res.retLast] at h
  | .ret _ :: _ :: _, _, _, _, h, _ => by simp [Res.retLast] at h
  | .ite .. :: _, _, _, _, h, _ | .match_ .. :: _, _, _, _, h, _ | .call .. :: _, _, _, _, h, _
  | .callIf .. :: _, _, _, _, h, _ | .dispatch .. :: _, _, _, _, h, _ => by simp [Res.retLast] at h

theorem kidsValid_some {P : Program} {rd : Reader} {σ : Core.Val} : ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValid P rd σ cs ks → ∀ {i : ℕ} {c : Call}, cs[i]? = some c → ∃ k, ks[i]? = some k
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], h, _, _, _ => h.elim
  | _ :: _, k :: _, _, 0, _, _ => ⟨k, rfl⟩
  | _ :: cs, _ :: ks, h, i + 1, c, hc => kidsValid_some (cs := cs) (ks := ks) h.2.2 (i := i) (c := c) hc

/-- The empty list's branch and what follows call nothing. -/
theorem cl_zero_callees : Stmt.blockCallees (B1.Digest.cl23Zero ++
    [.atom (.copy (.n 76) (.n 10)), .atom (.copy (.n 77) (.n 11)), .ret [.n 76, .n 77]]) = [] := by
  decide +kernel

theorem cl_else_head : B1.Digest.cl23Else.take 1 = [.call "list_split" [.n 1] [.n 12, .n 13, .n 14]] :=
  B1.stmtsEqb_sound (by decide +kernel)

theorem walk_call_cons {σ : Core.Val} (f : String) (args rets : List V) (ps : List Stmt) :
    Memory.walk σ (.call f args rets :: ps) = (Memory.walk σ ps).pre [.call f args rets] := by
  rw [Memory.walk, Memory.walk1, Out.seq]

/-- **The nonempty list's branch first calls `list_split`**, on its test. -/
theorem cld_else_calls {σ : Core.Val} {es : List Ev} {vs : List V}
    (hw : Memory.walk σ (Fn.body fn% «claim_list_digest») = .ret es vs) (h3 : σ (.n 3) ≠ 0) :
    (calls es)[0]? = some Res.cldSplit := by
  rw [B1.Digest.claim_list_digest_shape, Bridge.walk_atom_cons, Bridge.walk_atom_cons, Bridge.walk_ite_cons,
    Bridge.out_pre_pre, Bridge.out_pre_pre] at hw
  rw [ite_eq_right h3, ← List.take_append_drop 1 B1.Digest.cl23Else, cl_else_head] at hw
  simp only [List.singleton_append] at hw
  obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
  rw [List.cons_append, walk_call_cons] at hw'
  obtain ⟨es'', -, rfl⟩ := Bridge.pre_eq_ret hw'
  rfl

/-- **The nonempty list's branch first calls `list_split`.** -/
theorem cld_calls {σ : Core.Val} {es : List Ev} {vs : List V}
    (hw : Memory.walk σ (Fn.body fn% «claim_list_digest») = .ret es vs) {g : String} {args rets : List V}
    (hg : Ev.call g args rets ∈ es) : (calls es)[0]? = some Res.cldSplit := by
  have hw0 := hw
  rw [B1.Digest.claim_list_digest_shape, Bridge.walk_atom_cons, Bridge.walk_atom_cons, Bridge.walk_ite_cons,
    Bridge.out_pre_pre, Bridge.out_pre_pre] at hw
  by_cases h3 : σ (.n 3) = 0
  · rw [ite_eq_left h3] at hw
    obtain ⟨es', hw', rfl⟩ := Bridge.pre_eq_ret hw
    have hc : (⟨g, args, rets, true⟩ : Call) ∈ calls (Memory.walk σ (B1.Digest.cl23Zero ++
        [.atom (.copy (.n 76) (.n 10)), .atom (.copy (.n 77) (.n 11)), .ret [.n 76, .n 77]])).evs := by
      rw [hw']
      have := mem_calls_of_call hg
      simpa [calls, Ev.call?, Out.evs] using this
    have := walk_callees _ hc
    rw [cl_zero_callees] at this
    cases this
  · exact cld_else_calls hw0 h3

/-- **`claim_list_digest`'s count at its honest frames**: `n_g = 1`, or `list_split`'s frame (cell
`23`) holds `g^a`, `g^b`, `g^c` at cells `3`, `4`, `5` and `n_g = g^(136a + 17b + c)`. -/
theorem tile_cld {A : String → Bridge.FnAl} : TileAt A fn_idx% «claim_list_digest» (.fr 3)
    [(.hp 23 3, 136), (.hp 23 4, 17), (.hp 23 5, 1)] := by
  intro r K i e hr t
  obtain ⟨hj0, -, -⟩ := Res.cld_idx
  -- the frame's function
  obtain ⟨ia, hja, hia, hna, hfa, hca, -⟩ := fn_of_idx t.idx
  obtain ⟨ib, hjb, hib, hnb, -⟩ := fn_of_idx hj0
  obtain rfl : ia = ib := by omega
  have hname : e.I.t.name = "claim_list_digest" := by rw [← hna, hnb]
  have hfn : e.fn = fn% «claim_list_digest» := by
    rw [← t.fn, hca]; exact Option.some.inj (hfa.symm.trans (hname ▸ B1.Digest.find_claim_list_digest))
  obtain ⟨vs, hw, hF, hev⟩ := t.events hr
  have hw' : Memory.walk e.σ (Fn.body fn% «claim_list_digest») = .ret (e.pre ++ e.es) vs := by
    rw [← hfn, ← t.fn]; exact hw
  have hfb := t.fb
  -- the count's cell
  obtain ⟨hc3, hfs3, hp1⟩ := Res.cld_n1
  have hn1 := t.cell hr hF (x := .n 1) (List.mem_append_left _ (List.mem_append_left _ hp1))
    (by rw [hc3]; norm_num) (by rw [hc3]; exact hfs3)
  rw [hc3] at hn1
  by_cases h3 : e.σ (.n 3) = 0
  · -- `n_g = 1`
    obtain ⟨-, -, -, -, hwa, -⟩ := t.wit hr Res.cld_wit
    have c2 : e.σ (.n 2) = word 1 0 := hev _ (hwa (.const (.n 2) (word 1 0)) (by simp))
    have a3 : e.σ (.n 3) = e.σ (.n 1) + e.σ (.n 2) := hev _ (hwa (.add (.n 3) (.n 1) (.n 2)) (by simp))
    have h1 : e.σ (.n 1) = 1 := by rw [a3, c2, B1.word_one] at h3; exact Value.e_add_eq_zero_iff.mp h3
    refine ⟨0, by norm_num, ?_, Or.inl rfl⟩
    change refMem r.img (e.I.fp + 3) = _
    rw [hn1, h1, pow_zero, ofK_one_E]
  · -- the nonempty list's branch: `list_split`'s call
    have hc0 := cld_else_calls hw' h3
    obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[0]? = some kfp := by
      have hl := hF.len
      have : 0 < (calls (e.pre ++ e.es)).length := by
        rcases h : calls (e.pre ++ e.es) with _ | _
        · rw [h] at hc0; cases hc0
        · simp
      exact ⟨e.I.kidFps[0], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hsq, hfs23⟩ := Res.cld_site
    obtain ⟨s, hs, hsq'⟩ := Option.map_eq_some_iff.mp hsq
    have h23 := (hF.site 0 _ kfp s hc0 hkfp hs).1 (by omega) (by rw [hsq']; exact hfs23)
    rw [hsq'] at h23
    obtain ⟨-, hm23⟩ := ref_read hr (by omega) h23
    -- the callee
    obtain ⟨f0, bufs, kids, hnode⟩ := t.node
    obtain ⟨args0, rets0, hv⟩ := inst_valid' hr t.inst hnode
    obtain ⟨fn', hf', -, es', vs'', hw'', -, -, hk⟩ := hv
    have hf0 : f0 = "claim_list_digest" := by rw [← hname, hnode]; rfl
    subst hf0
    obtain rfl : fn' = fn% «claim_list_digest» := Option.some.inj (hf'.symm.trans B1.Digest.find_claim_list_digest)
    rw [hw'] at hw''
    obtain ⟨rfl, -⟩ := Out.ret.inj hw''
    obtain ⟨k, hk0⟩ := kidsValid_some hk hc0
    obtain ⟨hkn, hkv, -⟩ := Res.kidsValid_at hk hc0 hk0
    have hkv' := hkv rfl
    have hI' : e.I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := t.inst
    obtain ⟨J, hJ, hJt, hJfp, -⟩ := insts_kid r.T _ r.hdr e.I hI' 0 k (by rw [hnode]; exact hk0)
    rw [hkfp, Option.some.injEq] at hJfp
    subst hJfp
    have hrel := Tree.Valid.rel _ hkv'
    rw [hkn] at hrel
    cases k with
    | phantom => exact hkv'.elim
    | node fk σJ bufsJ kidsJ =>
      obtain ⟨hls, hcell, hfs5⟩ := Res.ls_cell
      obtain ⟨hc28, hc29⟩ := Res.ls_cells
      obtain ⟨il, hil, hil', hnl, hfl, hcl, -, -, -, -⟩ := fn_of_idx hls
      simp only [Tree.name] at hkn
      subst hkn
      obtain ⟨fnJ, hfJ, -, esJ, vsJ, hwJ, hvsJ, -, -⟩ := hkv'
      obtain rfl : fnJ = coreProgram[il] := Option.some.inj (hfJ.symm.trans hfl)
      rw [← hcl] at hwJ
      have hvs := retLast_sound Res.ls_ret hwJ
      subst hvs
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvsJ
      obtain ⟨h28, h29, h30⟩ := hvsJ
      have hFJ := inst_frame hr hJ hJt hls hwJ
      have hJb := inst_fb hr hJ (by rw [hJt]; rfl) hls
      have hrd3 := hFJ.val (.n 28) (List.mem_append_right _ (by simp)) (by omega) (by omega)
      have hrd4 := hFJ.val (.n 29) (List.mem_append_right _ (by simp)) (by omega) (by omega)
      have hrd5 := hFJ.val (.n 30) (List.mem_append_right _ (by simp)) (by omega) (by omega)
      rw [hc28] at hrd3
      rw [hc29] at hrd4
      rw [hcell] at hrd5
      obtain ⟨hlt3, hm3⟩ := ref_read hr (by omega) hrd3
      obtain ⟨hlt4, hm4⟩ := ref_read hr (by omega) hrd4
      obtain ⟨hlt5, hm5⟩ := ref_read hr (by omega) hrd5
      -- the split
      obtain ⟨a, ha, b, hb, c, hc, hng, hrets⟩ := B1.Digest.list_split_sound _ (ref_memOk hr) _ _ hrel
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hrets
      obtain ⟨h12, h13, h14⟩ := hrets
      have hb' : b < 8 := by simpa [B1.Digest.bigGroups] using hb
      have hc' : c < 17 := by simpa [B1.Digest.claimGroup] using hc
      have hp23 : (refMem r.img (e.I.fp + 23)).limb 0 = Parameters.g ^ J.fp := by
        rw [hm23]; simp [limb_ofK, addressOfIndex]
      refine ⟨136 * a + 17 * b + c, by omega, ?_, Or.inr ⟨[a, b, c],
        ⟨⟨_, names_shift hp23 hlt3, by rw [hm3, h28, h12, Value.gen_pow_eq_ofK]⟩, by omega,
          ⟨_, names_shift hp23 hlt4, by rw [hm4, h29, h13, Value.gen_pow_eq_ofK]⟩, by omega,
          ⟨_, names_shift hp23 hlt5, by rw [hm5, h30, h14, Value.gen_pow_eq_ofK]⟩, by omega, trivial⟩,
        by simp only [partsSum]; omega⟩⟩
      change refMem r.img (e.I.fp + 3) = _
      rw [hn1, hng, Value.gen_pow_eq_ofK]

/-- **The frames' tiles' sums at the honest frames.** -/
theorem tiles_ok {A : String → Bridge.FnAl} : ∀ p ∈ Res.tiles, TileAt A p.1 p.2.1 p.2.2 := by
  simp only [Res.tiles, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact tile_cld

/-- **The tile families at an honest frame.** -/
theorem tileFam_top {A : String → Bridge.FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}
    {w : Res.Wit} (t : TopAt A r K i e j) (hr : r.Ok) (hW : Res.witOk j w = true) {x : Mode.Res}
    (hx : Res.tileFamB j w x = true) : RRes (refMem r.img) e.I.fp x :=
  tileFam_top_of tiles_ok t hr hW hx

/-- The function of `claim_list_digest`'s honest frames. -/
theorem cld_j {r : Ref} {i : ℕ} {e : Bridge.Ent} {j : ℕ}
    (t : TopAt alignA r Fn.«claim_list_digest».modeCert i e j) : j = fn_idx% «claim_list_digest» := by
  obtain ⟨hj0, hent0, -⟩ := Res.cld_idx
  obtain ⟨ia, rfl, -, -, -, -, -, -, -, hlta⟩ := fn_of_idx t.idx
  obtain ⟨ib, hib, -, -, -, -, -, -, -, hltb⟩ := fn_of_idx hj0
  refine fnOf_entry_inj hlta hltb ?_
  have := t.entry
  simp only [entryOf, t.idx] at this
  rw [this, hent0]

/-- **`claim_list_digest`'s residuals at its honest frames.** -/
theorem resCld_alignA : ResCert alignA Fn.«claim_list_digest».modeCert := by
  intro r hr i hi e j t x hx hin
  rcases Res.cld_res i hi x hx with ⟨rfl, rfl⟩ | htl
  swap
  · obtain rfl := cld_j t
    exact tileList_top tiles_ok t hr htl
  obtain ⟨hj0, hent0, hentA⟩ := Res.cld_idx
  have hκ := logMemorySize_le_28 (e := r.exec) hr.size
  -- the frame's function
  obtain ⟨ia, rfl, hia, hna, hfa, hca, -, -, h1a, hlta⟩ := fn_of_idx t.idx
  obtain ⟨ib, hib, hib', hnb, hfb, hcb, -, -, h1b, hltb⟩ := fn_of_idx hj0
  have hjj : ia + 1 = fn_idx% «claim_list_digest» := by
    refine fnOf_entry_inj hlta hltb ?_
    have := t.entry
    simp only [entryOf, t.idx] at this
    rw [this, hent0]
  obtain rfl : ia = ib := by omega
  have hname : e.I.t.name = "claim_list_digest" := by rw [← hna, hnb]
  have hfn : e.fn = fn% «claim_list_digest» := by
    rw [← t.fn, hca]; exact Option.some.inj (hfa.symm.trans (hname ▸ B1.Digest.find_claim_list_digest))
  -- the frame's position: atoms, then the dispatch
  obtain ⟨off, hoff, p, hal, as, -, hpos⟩ := t.at'
  rw [hname, hentA] at hoff
  obtain rfl : off = 99 := by omega
  rw [hname] at hal
  have hd := Res.cld_al
  rw [hal] at hd
  obtain ⟨bs, x, fs, args, rets, rest, rfl⟩ := headDispatch_sound (Option.some.inj hd)
  obtain ⟨vs', hrest⟩ := t.rest
  obtain ⟨g, hg⟩ := dispatch_call (bs := as ++ bs) (by rw [List.map_append, List.append_assoc, ← hpos]; exact hrest)
  -- the path's first call, `list_split`'s
  obtain ⟨vs, hw, hF⟩ := t.path
  rw [hfn] at hw
  have hc0 := cld_calls hw (List.mem_append_right _ hg)
  obtain ⟨kfp, hkfp⟩ : ∃ kfp, e.I.kidFps[0]? = some kfp := by
    have hl := hF.len
    have : 0 < (calls (e.pre ++ e.es)).length := by
      rcases h : calls (e.pre ++ e.es) with _ | _
      · rw [h] at hc0; cases hc0
      · simp
    exact ⟨e.I.kidFps[0], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨hsq, hfs23⟩ := Res.cld_site
  obtain ⟨s, hs, hsq'⟩ := Option.map_eq_some_iff.mp hsq
  rw [hjj] at hF
  have h23 := (hF.site 0 _ kfp s hc0 hkfp hs).1 (by omega) (by rw [hsq']; exact hfs23)
  rw [hsq'] at h23
  have hfb := t.fb
  rw [← hjj] at hfs23
  obtain ⟨-, hm23⟩ := ref_read hr (by omega) h23
  -- the callee
  obtain ⟨f0, bufs, kids, hnode⟩ := t.node
  obtain ⟨args0, rets0, hv⟩ := inst_valid' hr t.inst hnode
  obtain ⟨fn', hf', -, es', vs'', hw', -, -, hk⟩ := hv
  have hf0 : f0 = "claim_list_digest" := by rw [← hname, hnode]; rfl
  subst hf0
  obtain rfl : fn' = fn% «claim_list_digest» := Option.some.inj (hf'.symm.trans B1.Digest.find_claim_list_digest)
  rw [hw] at hw'
  obtain ⟨rfl, -⟩ := Out.ret.inj hw'
  obtain ⟨k, hk0⟩ := kidsValid_some hk hc0
  obtain ⟨hkn, hkv, -⟩ := Res.kidsValid_at hk hc0 hk0
  have hkv' := hkv rfl
  have hI' : e.I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := t.inst
  obtain ⟨J, hJ, hJt, hJfp, -⟩ := insts_kid r.T _ r.hdr e.I hI' 0 k (by rw [hnode]; exact hk0)
  rw [hkfp, Option.some.injEq] at hJfp
  subst hJfp
  have hrel := Tree.Valid.rel _ hkv'
  rw [hkn] at hrel
  cases k with
  | phantom => exact hkv'.elim
  | node fk σJ bufsJ kidsJ =>
    obtain ⟨hls, hcell, hfs5⟩ := Res.ls_cell
    obtain ⟨il, hil, hil', hnl, hfl, hcl, -, -, -, -⟩ := fn_of_idx hls
    simp only [Tree.name] at hkn
    subst hkn
    obtain ⟨fnJ, hfJ, -, esJ, vsJ, hwJ, hvsJ, -, -⟩ := hkv'
    obtain rfl : fnJ = coreProgram[il] := Option.some.inj (hfJ.symm.trans hfl)
    rw [← hcl] at hwJ
    have hvs := retLast_sound Res.ls_ret hwJ
    subst hvs
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvsJ
    obtain ⟨-, -, h30⟩ := hvsJ
    have hFJ := inst_frame hr hJ hJt hls hwJ
    have hrd := hFJ.val (.n 30) (List.mem_append_right _ (by simp)) (by omega) (by omega)
    rw [hcell] at hrd
    have hJb := inst_fb hr hJ (by rw [hJt]; rfl) hls
    obtain ⟨hlt5, hm5⟩ := ref_read hr (by omega) hrd
    -- `rest = g^c`, `c < 17`
    obtain ⟨a, -, b, -, c, hc, -, hrets⟩ := B1.Digest.list_split_sound _ (ref_memOk hr) _ _ hrel
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hrets
    obtain ⟨-, -, h14⟩ := hrets
    have hc17 : c < 17 := by simpa [B1.Digest.claimGroup] using hc
    refine obl_rres hin ⟨by norm_num, fun y hy ↦ ⟨c, hc17, ?_⟩⟩
    obtain ⟨hy, hylt⟩ := hy
    simp only [hm23, limb_mul_ofK, limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte, addressOfIndex] at hy
    rw [← pow_add] at hy
    have hy' := gpow_inj (by unfold maxCells at hlt5; omega) (by unfold maxCells at hylt; omega) hy
    rw [← hy', hm5, h30, h14, Value.gen_pow_eq_ofK]

end

end LeanVM.Guest.EndExec
