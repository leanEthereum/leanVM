/-
  LeanVM.Guest.B2C.CplWalk

  The completeness walk is sound: on a frame holding what the honest memory puts there, the run
  follows the path a valuation takes through a window, from its start to its end, counted.
-/

module

public import LeanVM.Guest.B2C.CplSem

/-!
# The walk along a path

`WH` is what the walk of one window assumes: its context and segments hold, the instance's frame
holds what the check reads (`FrameHolds`), its callees run (`KidsRun`), and the path's events
hold. `PosZ st W0 n` says the run is at the walk's position `st`: from the window's start `W0` it
reached the start of `st`'s segment, the items of the segment before `st` holding with every
branch falling through, counted within the walk's counts and the first `n` callees'. The moves
(`segAtC_pos`, `endAtC_reach`, `brAtC_pos`) step a position along a segment and into the next.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

/-- The counts of the callees of the first `n` calls. -/
def ksum (ck : List (Opcode → ℕ)) (n : ℕ) (op : Opcode) : ℕ := ((ck.take n).map (· op)).sum

theorem ksum_mono (ck : List (Opcode → ℕ)) {n m : ℕ} (h : n ≤ m) (op : Opcode) :
    ksum ck n op ≤ ksum ck m op := by
  unfold ksum
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

theorem ksum_succ (ck : List (Opcode → ℕ)) (n : ℕ) (op : Opcode) :
    ksum ck (n + 1) op = ksum ck n op + (ck.getD n 0) op := by
  unfold ksum
  rcases Nat.lt_or_ge n ck.length with h | h
  · rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le h, List.getD_eq_default _ _ h]
    simp

/-! ## Functions and calls -/

theorem idxOf_coreOf {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) : idxOf (coreOf j).name = some j := by
  have hl : j - 1 < coreProgram.length := by
    have := coreProgram_length
    have : nFns = 1044 := rfl
    omega
  have hc : coreOf j = coreProgram[j - 1] := by unfold coreOf; exact nth_eq hl
  unfold idxOf Core.Program.indexOf?
  rw [hc]
  have : coreProgram.findIdx? (·.name == coreProgram[j - 1].name) = some (j - 1) := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hl, by simp, fun k hk he ↦ ?_⟩
    have hn := coreProgram_names_nodup
    have hk' : k < (coreProgram.map (·.name)).length := by simp; omega
    have hj' : j - 1 < (coreProgram.map (·.name)).length := by simp; omega
    have := (List.Nodup.getElem_inj_iff hn (hi := hk') (hj := hj')).mp (by simpa using he)
    omega
  rw [this]
  simp only [Option.map_some, Option.some.injEq]
  omega

/-- A callee the code reaches, by its entry. -/
theorem calleeC_some {X : CX} (hG : X.G = glob) {e j' : ℕ} (h : calleeC X e = some j') :
    2 ≤ j' ∧ j' < nFns ∧ (fnOf j').entry = e := by
  have hp := List.find?_some h
  simp only [hG, Bool.and_eq_true] at hp
  obtain ⟨hg, he⟩ := hp
  simp only [glob, good, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hg
  exact ⟨hg.1, hg.2, Nat.eq_of_beq_eq_true he⟩

theorem entryOf_callee {j' : ℕ} (h1 : 2 ≤ j') (h2 : j' < nFns) :
    entryOf (coreOf j').name = (fnOf j').entry := by
  unfold entryOf
  rw [idxOf_coreOf (by omega) h2]

theorem selfCells_callee {j' : ℕ} (h1 : 2 ≤ j') (h2 : j' < nFns) :
    selfCells (coreOf j').name = (certOf j').facts.env.map (·.1) := by
  unfold selfCells
  rw [idxOf_coreOf (by omega) h2]

/-- The call of an event, at its position among the path's calls. -/
theorem calls_at {ebef rest : List Ev} {ev : Ev} {c : Call} (hc : ev.call? = some c) :
    (calls (ebef ++ ev :: rest))[(calls ebef).length]? = some c := by
  simp [calls, List.filterMap_append, hc]

theorem calls_len_gt {ebef rest : List Ev} {ev : Ev} {c : Call} (hc : ev.call? = some c)
    (hr : ∃ e ∈ rest, (Ev.call? e).isSome) :
    (calls ebef).length + 1 < (calls (ebef ++ ev :: rest)).length := by
  obtain ⟨e, he, hs⟩ := hr
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hs
  have : 0 < (calls rest).length := List.length_pos_of_mem (List.mem_filterMap.mpr ⟨e, he, hc'⟩)
  have hl : (calls (ebef ++ ev :: rest)).length = (calls ebef).length + 1 + (calls rest).length := by
    simp [calls, List.filterMap_append, hc]
    omega
  omega

theorem calls_append_one {ebef : List Ev} {ev : Ev} {c : Call} (hc : ev.call? = some c) :
    (calls (ebef ++ [ev])).length = (calls ebef).length + 1 := by
  simp [calls, List.filterMap_append, hc]

theorem calls_append_none {ebef : List Ev} {ev : Ev} (hc : ev.call? = none) :
    calls (ebef ++ [ev]) = calls ebef := by
  simp [calls, List.filterMap_append, hc]

theorem noRetList_append : ∀ (A B : List Stmt),
    Stmt.noRetList (A ++ B) = (Stmt.noRetList A && Stmt.noRetList B)
  | [], _ => by simp [Stmt.noRetList]
  | a :: A, B => by simp only [List.cons_append, Stmt.noRetList, noRetList_append A B, Bool.and_assoc]

/-- A loop's closing `callIf` is on a path through a block ending with it. -/
theorem tail_call_in {j : ℕ} {σ : Val} {ss : List Stmt}
    (ht : ∃ A c args, ss = A ++ [.callIf c (coreOf j).name args, .ret []])
    (hs : Stmt.noRetList ss = true ∨ lastOkC ss = true) {o : Out} (hw : walk σ ss = o)
    (hst : o ≠ .stuck) : ∃ e ∈ o.evs, (Ev.call? e).isSome := by
  obtain ⟨A, c, args, rfl⟩ := ht
  have hA : Stmt.noRetList A = true := by
    rcases hs with hs | hs
    · rw [noRetList_append] at hs
      simp [Stmt.noRetList, Stmt.noRet] at hs
    · obtain ⟨A', vs, he, hA'⟩ := lastOkC_split hs
      rw [show A ++ [Stmt.callIf c (coreOf j).name args, .ret []] =
        (A ++ [.callIf c (coreOf j).name args]) ++ [.ret []] by simp] at he
      obtain ⟨rfl, -⟩ := List.append_inj' he rfl
      rw [noRetList_append] at hA'
      exact (Bool.and_eq_true _ _).mp hA' |>.1
  rw [walk_appendC] at hw
  rcases walk_noRetC A hA with ⟨eA, h1⟩ | h1
  · rw [h1] at hw
    subst hw
    refine ⟨if σ c = 0 then .skip (coreOf j).name args else .call (coreOf j).name args [], ?_, ?_⟩
    · simp [walk, walk1, Out.seq, Out.pre, Out.evs]
    · split_ifs <;> rfl
  · rw [h1] at hw
    exact absurd hw.symm (by simpa [Out.seq] using hst)

section Walk

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)} {segs : List Exec.Seg} {X : CX}
  {wJ : ℕ} {wenv : Trie Sym}

/-- **What the walk of a window assumes.** -/
structure WH (L : MemImage κ) (j fp : ℕ) (X : CX) (segs : List Exec.Seg) (wJ : ℕ) (wenv : Trie Sym)
    (σ : Val) (es : List Ev) (vs : List V) (kfps : List ℕ) (hdr : E × E)
    (ck : List (Opcode → ℕ)) : Prop where
  hX : CXOk L fp X
  ctx : Exec.Ctx X.F κ (gpow fp)
  segz : ∀ s ∈ segs, SegZ L (gpow fp) guest X.entry s
  exits : ∀ s ∈ segs, ∀ x, x = s.exit ∨ x ∈ branchExits s.items → x ∈ s.exits
  idx : X.idx = index segs
  linked : linkedWeak X.idx segs wJ wenv = true
  loc : LocOk j X.loc
  fs : X.fs = fsN j
  G : X.G = glob
  main : X.main = (j == 1)
  name : X.name = (coreOf j).name
  nargs : X.nargs = (coreOf j).params.length
  sites : X.sites = (plumbOf j).sites
  arms : X.arms = (plumbOf j).arms
  self : X.self = (certOf j).facts.env.map (·.1)
  entry : X.entry = (fnOf j).entry
  frame : FrameHolds L j fp σ es vs kfps hdr
  kids : KidsRun L σ es kfps ck
  hev : ∀ e ∈ es, e.Holds L.read σ
  jt : JTHolds glob L
  tab : ∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2
  j1 : 1 ≤ j
  jn : j < nFns

/-- **The run is at the walk's position `st`**, from `W0`, the first `n` callees run. -/
structure PosZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (st : CW) (W0 : Regs K)
    (n : ℕ) : Prop where
  seg : st.seg ∈ segs
  ok : CWOk L fp X st
  run : ∃ pre c, pre ++ st.its = st.seg.items ∧ Fall L (gpow fp) pre ∧
    RunC guest L W0 ⟨gpow (X.entry + st.seg.start), gpow fp⟩ c ∧
    ∀ op, c op + itemOps pre op ≤ st.cnt.get op + ksum ck n op
  fresh : ∀ t, st.fresh = some t → st.seg.start = t ∧ st.its = st.seg.items ∧ getF X.idx t = some st.seg

/-- The environment of the segment at offset `J` holds; at the window's end, where none starts,
the next window's. -/
def EnvAt (L : MemImage κ) (fp : ℕ) (X : CX) (wJ : ℕ) (wenv : Trie Sym) (J : ℕ) : Prop :=
  (∀ s, getF X.idx J = some s → s.start = J → EnvHolds L (gpow fp) s.env) ∧
    (J = wJ → getF X.idx J = none → EnvHolds L (gpow fp) wenv)

/-- **The run arrives at offset `J`**, from `W0`, within the counts `c` and the first `n`
callees'. -/
def Arr (L : MemImage κ) (fp : ℕ) (X : CX) (wJ : ℕ) (wenv : Trie Sym) (ck : List (Opcode → ℕ))
    (W0 : Regs K) (J : ℕ) (c : Cnt) (n : ℕ) : Prop :=
  (∃ cr, RunC guest L W0 ⟨gpow (X.entry + J), gpow fp⟩ cr ∧ ∀ op, cr op ≤ c.get op + ksum ck n op) ∧
    EnvAt L fp X wJ wenv J

/-! ## Moves -/

theorem segAtC_eq {t : ℕ} {st sn : CW} (h : segAtC X t st = some sn) :
    ∃ s, getF X.idx t = some s ∧ s.start = t ∧
      sn = ⟨s, s.items, st.book, st.fr, st.tg, st.nx, st.cnt, st.uq, some t⟩ := by
  unfold segAtC at h
  split at h
  · rename_i s hs
    cases hb : Nat.beq s.start t
    · rw [hb] at h; cases h
    · rw [hb] at h
      exact ⟨s, hs, Nat.eq_of_beq_eq_true hb, (Option.some.inj h).symm⟩
  · cases h

/-- Entering offset `t`, in its environment: the run is at the segment starting there. -/
theorem segAtC_pos (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {t : ℕ} {st sn : CW}
    (h : segAtC X t st = some sn) (hb : BookOk L fp st.book) (hfr : FrOk L fp st.fr)
    (htg : TgOk L fp st.tg) (hnx : NxOk L fp X.fs st.nx) (he : EnvAt L fp X wJ wenv t)
    {W0 : Regs K} {n : ℕ} {c : Opcode → ℕ} (hr : RunC guest L W0 ⟨gpow (X.entry + t), gpow fp⟩ c)
    (hc : ∀ op, c op ≤ st.cnt.get op + ksum ck n op) :
    PosZ H sn W0 n ∧ sn.book = st.book ∧ sn.fr = st.fr ∧ sn.tg = st.tg ∧ sn.nx = st.nx ∧
      sn.cnt = st.cnt ∧ sn.uq = st.uq ∧ sn.seg.start = t := by
  obtain ⟨s, hs, hst, rfl⟩ := segAtC_eq h
  have hmem : s ∈ segs := by
    rw [H.idx, getF_eq] at hs
    exact index_get hs
  refine ⟨⟨hmem, ⟨he.1 s hs hst, hb, hfr, htg, hnx⟩, ⟨[], c, rfl, trivial, hst ▸ hr, fun op ↦ ?_⟩,
    fun t' ht' ↦ ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, hst⟩
  · simpa [itemOps] using hc op
  · obtain rfl := Option.some.inj ht'
    exact ⟨hst, rfl, hs⟩

/-- The successor `t` of an exit whose environment holds has its environment holding. -/
theorem envAt_of_exit (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {s : Exec.Seg}
    (hs : s ∈ segs) {x : Exit} (hx : x ∈ s.exits) {t : ℕ} (ht : t ∈ x.succ)
    (he : EnvHolds L (gpow fp) x.env) : EnvAt L fp X wJ wenv t := by
  refine ⟨fun s' hs' _ ↦ ?_, fun htJ hn ↦ ?_⟩
  · rw [getF_eq] at hs'
    exact he.sub (linkedWeak_get H.linked hs hx ht hs').2
  · subst htJ
    rw [getF_eq] at hn
    exact he.sub (linkedWeak_none H.linked hs hx ht hn)

theorem endAtC_eq {st se : CW} (h : endAtC X st = .ok se) :
    ∃ c, passL X st st.its st.cnt = .ok ([], c) ∧
      se = ⟨st.seg, [], st.book, st.fr, st.tg, st.nx, c, st.uq, none⟩ := by
  unfold endAtC at h
  split at h
  · rename_i c hp
    rw [Cnt.seq_eq] at h
    exact ⟨c, hp, (Except.ok.inj h).symm⟩
  · cases h
  · cases h

/-- **At the end of its segment the run reaches the segment exit's registers**, its environment
holding there. -/
theorem endAtC_reach (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {st se : CW} {W0 : Regs K}
    {n : ℕ} (hp : PosZ H st W0 n) (he : endAtC X st = .ok se) :
    se.seg = st.seg ∧ se.book = st.book ∧ se.fr = st.fr ∧ se.tg = st.tg ∧ se.nx = st.nx ∧
      se.uq = st.uq ∧
      ∀ r, st.seg.exit.kind.Regs L (gpow fp) X.entry r → ∃ cr, RunC guest L W0 r cr ∧
        (∀ op, cr op ≤ se.cnt.get op + ksum ck n op) ∧ EnvHolds L (gpow fp) st.seg.exit.env := by
  obtain ⟨c, hpl, rfl⟩ := endAtC_eq he
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr ↦ ?_⟩
  obtain ⟨pre2, hpre2, hf2, hc2, -⟩ := passL_sound H.hX hp.ok st.its st.cnt hpl
  obtain ⟨pre, c0, hpre, hf, hrun, hc0⟩ := hp.run
  rw [List.append_nil] at hpre2
  subst hpre2
  have hfall : Fall L (gpow fp) st.seg.items := by
    rw [← hpre]
    exact (fall_append _ _).mpr ⟨hf, hf2⟩
  obtain ⟨cs, hcs, hle, henv⟩ := (H.segz _ hp.seg hp.ok.env).1 hfall r hr
  refine ⟨c0 + cs, hrun.trans hcs, fun op ↦ ?_, henv⟩
  have h1 := hle op
  have h2 := hc0 op
  rw [← hpre, itemOps_append] at h1
  rw [Pi.add_apply, hc2 op]
  omega

theorem brAtC_eq {st st' : CW} {oc od of : ℕ} {x : Exit}
    (h : brAtC X st = .ok (st', oc, od, of, x)) :
    ∃ its c, passL X st st.its st.cnt = .ok (.branch oc od of x :: its, c) ∧
      st' = ⟨st.seg, its, st.book, st.fr, st.tg, st.nx, c.bumpJ, st.uq, none⟩ := by
  unfold brAtC at h
  split at h
  · rename_i oc' od' of' x' its c hp
    rw [Cnt.seq_eq] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨its, c, hp, rfl⟩
  · cases h
  · cases h

/-- **At a branch**, the run falls through when its condition is `0`, and leaves by the branch's
exit, its environment holding, when it is taken. -/
theorem brAtC_pos (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {st st' : CW} {oc od of : ℕ}
    {x : Exit} {W0 : Regs K} {n : ℕ} (hp : PosZ H st W0 n) (hb : brAtC X st = .ok (st', oc, od, of, x)) :
    st'.seg = st.seg ∧ st'.book = st.book ∧ st'.fr = st.fr ∧ st'.tg = st.tg ∧ st'.nx = st.nx ∧
      st'.uq = st.uq ∧ st'.fresh = none ∧ x ∈ st.seg.exits ∧ CWOk L fp X st' ∧
      ((Atom.jump oc od of).Holds L (gpow fp) → rdc L fp oc = some 0 → PosZ H st' W0 n) ∧
      (Taken L (gpow fp) oc od of → ∀ r, x.kind.Regs L (gpow fp) X.entry r → ∃ cr,
        RunC guest L W0 r cr ∧ (∀ op, cr op ≤ st'.cnt.get op + ksum ck n op) ∧
        EnvHolds L (gpow fp) x.env) := by
  obtain ⟨its, c, hpl, rfl⟩ := brAtC_eq hb
  obtain ⟨pre2, hpre2, hf2, hc2, -⟩ := passL_sound H.hX hp.ok st.its st.cnt hpl
  obtain ⟨pre, c0, hpre, hf, hrun, hc0⟩ := hp.run
  have hitems : st.seg.items = (pre ++ pre2) ++ .branch oc od of x :: its := by
    rw [← hpre, ← hpre2, List.append_assoc]
  have hx : x ∈ st.seg.exits := H.exits _ hp.seg x (Or.inr (by
    rw [hitems, branchExits_append]
    simp [branchExits]))
  have hok : CWOk L fp X ⟨st.seg, its, st.book, st.fr, st.tg, st.nx, c.bumpJ, st.uq, none⟩ :=
    ⟨hp.ok.env, hp.ok.book, hp.ok.fr, hp.ok.tg, hp.ok.nx⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx, hok, fun hj h0 ↦ ?_, fun ht r hr ↦ ?_⟩
  · refine ⟨hp.seg, hok, ⟨pre ++ pre2 ++ [.branch oc od of x], c0, by rw [hitems]; simp, ?_, hrun,
      fun op ↦ ?_⟩, fun t ht ↦ by cases ht⟩
    · rw [fall_append, fall_append]
      exact ⟨⟨hf, hf2⟩, hj, h0, trivial⟩
    · have h1 := hc0 op
      simp only [itemOps_append, Cnt.get_bumpJ, hc2 op]
      simp only [itemOps_cons, itemOps_nil, itemOp]
      omega
  · have hfall : Fall L (gpow fp) (pre ++ pre2) := (fall_append _ _).mpr ⟨hf, hf2⟩
    obtain ⟨cs, hcs, hle, henv⟩ := (H.segz _ hp.seg hp.ok.env).2 _ oc od of x its hitems hfall ht r hr
    refine ⟨c0 + cs, hrun.trans hcs, fun op ↦ ?_, henv⟩
    have h1 := hle op
    have h2 := hc0 op
    simp only [itemOps_append, itemOps_cons, itemOps_nil, itemOp] at h1
    rw [Pi.add_apply, Cnt.get_bumpJ, hc2 op]
    omega

/-! ## The walk -/

/-- A block ending with a loop's closing `callIf` to its function and `ret []`. -/
def TailB (j : ℕ) (ss : List Stmt) : Prop :=
  ∃ A c args, ss = A ++ [.callIf c (coreOf j).name args, .ret []]

/-- **How the walk of a window ends by the return**: the run reaches the return registers
(`main`: the final ones) within the most a path runs and the first `n` callees' counts, its
returned values at the cells after its parameters. -/
def FinZ (L : MemImage κ) (j fp : ℕ) (X : CX) (ck : List (Opcode → ℕ)) (W0 : Regs K) (n : ℕ)
    (vs' : List V) : Prop :=
  (∃ r cr, (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
    RunC guest L W0 r cr ∧ ∀ op, cr op ≤ X.pmax.get op + ksum ck n op) ∧
  ∀ k (hk : k < vs'.length), X.loc.cell vs'[k] = 2 + X.nargs + k ∧ 2 ≤ X.loc.cell vs'[k] ∧
    X.loc.cell vs'[k] < X.fs

/-- **What the walk of a block from a position gives**: on a path through the block, from a
position the run is at, the run arrives where the walk ends, or returns. -/
def WGood (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (ss : List Stmt) (st : CW) : Prop :=
  ∀ (ebef eaft : List Ev) (o : Out) (W0 : Regs K) (pre : List Stmt),
    walk σ ss = o → es = ebef ++ o.evs ++ eaft → o ≠ .stuck →
    (Stmt.noRetList ss = true ∨ (lastOkC ss = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ ss)) →
    ((coreOf j).loop = true → ¬ TailB j ss → ∃ e ∈ eaft, (Ev.call? e).isSome) →
    PosZ H st W0 (calls ebef).length → (cw X ss st).ok = true →
    (∀ J c u, cw X ss st = .join J c u → ∃ es', o = .fall es' ∧
      Arr L fp X wJ wenv ck W0 J c (calls (ebef ++ es')).length) ∧
    (cw X ss st = .done → ∃ es' vs', o = .ret es' vs' ∧ FinZ L j fp X ck W0 (calls (ebef ++ es')).length vs')

theorem walk_nilZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (st : CW) : WGood H [] st := by
  intro ebef eaft o W0 pre hw hes hs hshape htail hp hok
  rw [walk] at hw
  subst hw
  rw [cw_nil] at hok ⊢
  refine ⟨fun J c u hj ↦ ⟨[], rfl, ?_⟩, fun hd ↦ ?_⟩
  · rw [List.append_nil]
    rcases endC_ok hok with ⟨t, hf, he⟩ | ⟨hf, se, t, hse, hk, hsu, he⟩
    · rw [he] at hj
      simp only [RC.join.injEq] at hj
      obtain ⟨rfl, rfl, rfl⟩ := hj
      obtain ⟨hst, hits, hidx⟩ := hp.fresh _ hf
      obtain ⟨pre, c, hpre, -, hrun, hc⟩ := hp.run
      have : pre = [] := by
        rw [hits] at hpre
        simpa using hpre
      subst this
      refine ⟨⟨c, hst ▸ hrun, fun op ↦ by simpa [itemOps] using hc op⟩, fun s hs _ ↦ ?_,
        fun _ hn ↦ by rw [hidx] at hn; cases hn⟩
      rw [hidx] at hs
      obtain rfl := Option.some.inj hs
      exact hp.ok.env
    · rw [he] at hj
      simp only [RC.join.injEq] at hj
      obtain ⟨rfl, rfl, rfl⟩ := hj
      obtain ⟨hseg, -, -, -, -, -, hr⟩ := endAtC_reach H hp hse
      rw [hseg] at hk hsu
      obtain ⟨cr, hcr, hle, henv⟩ := hr _ (by rw [hk]; rfl)
      exact ⟨⟨cr, hcr, hle⟩, envAt_of_exit H hp.seg (H.exits _ hp.seg _ (Or.inl rfl))
        (by rw [hsu]; exact List.mem_singleton_self _) henv⟩
  · rcases endC_ok hok with ⟨t, -, he⟩ | ⟨-, se, t, -, -, -, he⟩ <;> rw [he] at hd <;> cases hd

theorem tailB_cons {s : Stmt} {ss : List Stmt} (h : TailB j (s :: ss)) :
    (∃ c args, s = .callIf c (coreOf j).name args ∧ ss = [.ret []]) ∨ TailB j ss := by
  obtain ⟨A, c, args, he⟩ := h
  cases A with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at he
    exact Or.inl ⟨c, args, he.1, he.2⟩
  | cons a A =>
    simp only [List.cons_append, List.cons.injEq] at he
    exact Or.inr ⟨A, c, args, he.2⟩

theorem lastOkC_cons {s : Stmt} {ss : List Stmt} (h : lastOkC (s :: ss) = true)
    (hs : ∀ vs, s ≠ .ret vs) : Stmt.noRet s = true ∧ lastOkC ss = true := by
  cases ss with
  | nil => cases s <;> simp_all [lastOkC]
  | cons s' ss => cases s <;> simp_all [lastOkC]

/-- **A statement falling through, then the rest of the block.** -/
theorem walk_step (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {s : Stmt} {ss : List Stmt}
    (ih : ∀ st, WGood H ss st) (hs : Stmt.noRet s = true)
    (hnt : ∀ c args, s = .callIf c (coreOf j).name args → ss ≠ [.ret []])
    {st st'' : CW} {ebef eaft e1 : List Ev} {o : Out} {W0 : Regs K} {pre : List Stmt}
    (hw1 : walk1 σ s = .fall e1) (hw : walk σ (s :: ss) = o) (hes : es = ebef ++ o.evs ++ eaft)
    (hstk : o ≠ .stuck)
    (hshape : Stmt.noRetList (s :: ss) = true ∨
      (lastOkC (s :: ss) = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ s :: ss))
    (htail : (coreOf j).loop = true → ¬ TailB j (s :: ss) → ∃ e ∈ eaft, (Ev.call? e).isSome)
    (hp'' : PosZ H st'' W0 (calls (ebef ++ e1)).length) (hcw : cw X (s :: ss) st = cw X ss st'')
    (hok : (cw X (s :: ss) st).ok = true) :
    (∀ J c u, cw X (s :: ss) st = .join J c u → ∃ es', o = .fall es' ∧
      Arr L fp X wJ wenv ck W0 J c (calls (ebef ++ es')).length) ∧
    (cw X (s :: ss) st = .done → ∃ es' vs', o = .ret es' vs' ∧
      FinZ L j fp X ck W0 (calls (ebef ++ es')).length vs') := by
  rw [walk, hw1] at hw
  subst hw
  have hstk' : walk σ ss ≠ .stuck := fun h ↦ hstk (by rw [h]; rfl)
  have hes' : es = (ebef ++ e1) ++ (walk σ ss).evs ++ eaft := by
    rw [hes]
    cases hws : walk σ ss with
    | fall _ => simp [Out.seq, Out.pre, Out.evs, List.append_assoc]
    | ret _ _ => simp [Out.seq, Out.pre, Out.evs, List.append_assoc]
    | stuck => exact absurd hws hstk'
  have hshape' : Stmt.noRetList ss = true ∨
      (lastOkC ss = true ∧ eaft = [] ∧ (coreOf j).body = (pre ++ [s]) ++ ss) := by
    rcases hshape with h | ⟨h, he, hb⟩
    · simp only [Stmt.noRetList, Bool.and_eq_true] at h
      exact Or.inl h.2
    · refine Or.inr ⟨(lastOkC_cons h fun vs hv ↦ by subst hv; simp [Stmt.noRet] at hs).2, he, ?_⟩
      rw [hb, List.append_assoc]
      rfl
  have htail' : (coreOf j).loop = true → ¬ TailB j ss → ∃ e ∈ eaft, (Ev.call? e).isSome := by
    intro hl hnt'
    refine htail hl fun ht ↦ ?_
    rcases tailB_cons ht with ⟨c, args, rfl, he⟩ | ht
    · exact hnt c args rfl he
    · exact hnt' ht
  rw [hcw] at hok ⊢
  obtain ⟨h1, h2⟩ := ih st'' (ebef ++ e1) eaft _ W0 (pre ++ [s]) rfl hes' hstk' hshape' htail' hp'' hok
  refine ⟨fun J c u hj ↦ ?_, fun hd ↦ ?_⟩
  · obtain ⟨es', he, ha⟩ := h1 J c u hj
    refine ⟨e1 ++ es', by rw [he]; rfl, ?_⟩
    rw [← List.append_assoc]
    exact ha
  · obtain ⟨es', vs', he, hf⟩ := h2 hd
    refine ⟨e1 ++ es', vs', by rw [he]; rfl, ?_⟩
    rw [← List.append_assoc]
    exact hf

theorem walk_atomZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (a : Core.Atom)
    (ss : List Stmt) (st : CW) (ih : ∀ st, WGood H ss st) : WGood H (.atom a :: ss) st := by
  intro ebef eaft o W0 pre hw hes hs hshape htail hp hok
  refine walk_step H ih rfl (fun c args h ↦ by cases h) rfl hw hes hs hshape htail ?_ (cw_atom a ss st) hok
  have hc : calls (ebef ++ [.atom a]) = calls ebef := by simp [calls, Ev.call?]
  rw [hc]
  exact ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, hp.ok.tg, hp.ok.nx⟩, hp.run, fun t ht ↦ by cases ht⟩

/-! ## Calls -/

theorem argFC_mem {loc : CLoc} : ∀ {o : ℕ} {vs : List V} {p : ℕ × FC}, p ∈ argFC loc o vs →
    ∃ k, ∃ hk : k < vs.length, p = (o + k, .val (loc.cell vs[k]))
  | _, [], _, h => (List.not_mem_nil h).elim
  | o, v :: vs, p, h => by
    simp only [argFC, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨k, hk, rfl⟩ := argFC_mem h
      exact ⟨k + 1, by simpa using hk, by simp [Nat.add_assoc, Nat.add_comm 1 k]⟩

theorem posZ_fr (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {st : CW} {W0 : Regs K} {n : ℕ}
    (hp : PosZ H st W0 n) {q : ℕ} {fcs : List (ℕ × FC)} {kfp : ℕ}
    (hq : rdc L fp q = some (ofK (gpow kfp))) (hf : ∀ p ∈ fcs, FCHolds L fp kfp p.1 p.2) :
    PosZ H { st with fr := (q, fcs) :: st.fr } W0 n :=
  ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, fun x hx ↦ by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨kfp, hq, hf⟩
    · exact hp.ok.fr x hx, hp.ok.tg, hp.ok.nx⟩, hp.run, hp.fresh⟩

theorem siteC_eq {X : CX} (hs : X.sites = (plumbOf j).sites) (c : Call) :
    siteC X c.args c.rets = siteOf j c := by
  unfold siteC siteOf
  rw [hs]

theorem siteOk_spec {X : CX} {args rets : List V} {q r t : ℕ} (h : siteOk X args rets q r t = true) :
    ∃ s, siteC X args rets = some s ∧ s.q = q ∧ s.r = r ∧ s.tgt = t := by
  unfold siteOk at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true] at h
    exact ⟨s, hs, Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2,
      Nat.eq_of_beq_eq_true h.2⟩
  · cases h

/-- **A call's callee frame**, its `n`-th on the path, not a loop's closing one: its pointer cell
holds it, it holds the arguments, the self frame pointer cells, the caller's frame pointer and
the return pc, and it returns there. -/
theorem call_frame (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {n : ℕ} {c : Call}
    (hci : (calls es)[n]? = some c) {j' : ℕ} (hj1 : 2 ≤ j') (hj2 : j' < nFns)
    (hf : c.f = (coreOf j').name) {s0 : Site} (hs0 : siteC X c.args c.rets = some s0)
    (hnl : (coreOf j).loop = true → n + 1 < (calls es).length)
    (hin : inFrame X.fs (s0.q :: c.args.map X.loc.cell) = true) {selfs : List ℕ}
    (hsf : ∀ o ∈ selfs, o ∈ (certOf j').facts.env.map (·.1)) :
    ∃ kfp, kfps[n]? = some kfp ∧ rdc L fp s0.q = some (ofK (gpow kfp)) ∧
      (∀ p ∈ callFC X c.args selfs s0.r, FCHolds L fp kfp p.1 p.2) ∧
      retRegs L (gpow kfp) = some ⟨gpow s0.r, gpow fp⟩ := by
  have hlen : n < kfps.length := by
    rw [H.frame.len]
    exact (List.getElem?_eq_some_iff.mp hci).1
  refine ⟨kfps[n], List.getElem?_eq_getElem hlen, ?_⟩
  have hkfp := List.getElem?_eq_getElem hlen
  have hfr := inFrame_mem hin
  have hq : rdc L fp s0.q = some (ofK (gpow kfps[n])) := by
    have := (H.frame.site n c kfps[n] s0 hci hkfp (by rw [← siteC_eq H.sites]; exact hs0)).1
      (hfr _ List.mem_cons_self).1 (by rw [← H.fs]; exact (hfr _ List.mem_cons_self).2)
    rw [gpow_addC] at this
    exact this
  obtain ⟨h0, h1, hargs, hself⟩ := H.frame.kid n c kfps[n] hci hkfp
  have hhdr : kidHdr j fp hdr es n = (ofK (gpow s0.r), ofK (gpow fp)) := by
    unfold kidHdr
    rw [hci]
    simp only
    split_ifs with hh
    · have := hnl hh.1
      omega
    · rw [← siteC_eq H.sites, hs0]
  rw [hhdr] at h0 h1
  rw [gpow_addC] at h0 h1
  refine ⟨hq, fun p hp ↦ ?_, retRegs_eq_some_iff.mpr ⟨_, _, h0, h1, by simp⟩⟩
  unfold callFC at hp
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (hp | ⟨o, ho, rfl⟩) | (rfl | rfl)
  · obtain ⟨k, hk, rfl⟩ := argFC_mem hp
    have hv : X.loc.cell c.args[k] ∈ c.args.map X.loc.cell := List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩
    have hc := hfr _ (List.mem_cons_of_mem _ hv)
    obtain ⟨e', hm, hc'⟩ := List.mem_filterMap.mp (List.mem_of_getElem? hci)
    have huses : c.args[k] ∈ e'.uses := by
      rcases e' with _ | _ | ⟨f', a', r'⟩ | ⟨f', a'⟩ <;> simp only [Ev.call?, Option.some.injEq,
        reduceCtorEq] at hc'
      · subst hc'; simp [Ev.uses, List.getElem_mem]
      · subst hc'; simp [Ev.uses, List.getElem_mem]
    refine ⟨σ c.args[k], val_cell H.frame H.loc (uses_named hm huses) hc.1 (H.fs ▸ hc.2), ?_⟩
    have := hargs k hk
    rw [gpow_addC] at this
    exact this
  · have hm : o ∈ selfCells c.f := by
      rw [hf, selfCells_callee hj1 hj2]
      exact hsf o ho
    have := hself o hm
    rw [gpow_addC] at this
    exact this
  · exact h1
  · exact h0

end Walk




end
end LeanVM.Guest.B2C
