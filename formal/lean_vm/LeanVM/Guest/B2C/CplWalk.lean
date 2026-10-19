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
  unfold calleeC at h
  obtain ⟨⟨j, sg⟩, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨h1, h2, h3, -⟩ := calleeS_spec hG hs
  exact ⟨h1, h2, h3⟩

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

/-! ## Bit sets -/

theorem bitK_eq (s n : ℕ) : bitK s n = s.testBit n := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  show Nat.beq ((s >>> n) % 2) 1 = _
  rw [Nat.shiftRight_eq_div_pow]
  cases h : Nat.beq (s / 2 ^ n % 2) 1
  · simp only [Bool.false_eq, decide_eq_false_iff_not]
    exact fun h' ↦ by rw [h', Nat.beq_refl] at h; cases h
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem testBit_setK (s n m : ℕ) : (setK s n).testBit m = (s.testBit m || decide (n = m)) := by
  show (s ||| 1 <<< n).testBit m = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem nvVals_spec : ∀ (l : List V) (s n : ℕ), (nvVals l s).testBit n = true →
    s.testBit n = true ∨ V.n n ∈ l
  | [], s, n, h => Or.inl h
  | v :: l, s, n, h => by
    simp only [nvVals] at h
    cases hb : (v.path.isEmpty && Nat.beq v.tag 0)
    · rw [hb, Bool.cond_false] at h
      exact (nvVals_spec l s n h).imp id fun h' ↦ List.mem_cons_of_mem _ h'
    · rw [hb, Bool.cond_true, natSeq_eq] at h
      rcases nvVals_spec l _ n h with h' | h'
      · rw [testBit_setK, Bool.or_eq_true, decide_eq_true_eq] at h'
        rcases h' with h' | rfl
        · exact Or.inl h'
        · right
          simp only [Bool.and_eq_true, List.isEmpty_iff] at hb
          obtain ⟨vp, vt, vi⟩ := v
          simp only at hb
          obtain ⟨rfl, hb⟩ := hb
          obtain rfl := Nat.eq_of_beq_eq_true hb
          exact List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h')

/-- A renumbered value whose bit a block's atoms set is a value of one of its atoms. -/
theorem nvOf_spec : ∀ (ss : List Stmt) (s n : ℕ), (nvOf ss s).testBit n = true →
    s.testBit n = true ∨ ∃ a, Stmt.atom a ∈ ss ∧ V.n n ∈ atomUses a
  | [], s, n, h => Or.inl h
  | .atom a :: ss, s, n, h => by
    simp only [nvOf, natSeq_eq] at h
    rcases nvOf_spec ss _ n h with h' | ⟨b, hb, hm⟩
    · rcases nvVals_spec _ s n h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr ⟨a, List.mem_cons_self, h''⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hm⟩
  | .ite .. :: ss, s, n, h => (nvOf_spec ss s n h).imp id fun ⟨b, hb, hm⟩ ↦ ⟨b, List.mem_cons_of_mem _ hb, hm⟩
  | .match_ .. :: ss, s, n, h => (nvOf_spec ss s n h).imp id fun ⟨b, hb, hm⟩ ↦ ⟨b, List.mem_cons_of_mem _ hb, hm⟩
  | .call .. :: ss, s, n, h => (nvOf_spec ss s n h).imp id fun ⟨b, hb, hm⟩ ↦ ⟨b, List.mem_cons_of_mem _ hb, hm⟩
  | .callIf .. :: ss, s, n, h => (nvOf_spec ss s n h).imp id fun ⟨b, hb, hm⟩ ↦ ⟨b, List.mem_cons_of_mem _ hb, hm⟩
  | .dispatch .. :: ss, s, n, h => (nvOf_spec ss s n h).imp id fun ⟨b, hb, hm⟩ ↦ ⟨b, List.mem_cons_of_mem _ hb, hm⟩
  | .ret _ :: ss, s, n, h => (nvOf_spec ss s n h).imp id fun ⟨b, hb, hm⟩ ↦ ⟨b, List.mem_cons_of_mem _ hb, hm⟩

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
  /-- A parameter, or a value of one of the body's atoms, is a value the path names. -/
  named : ∀ n, (Nat.blt n X.nargs || bitK X.nv n) = true → V.n n ∈ namedOf (coreOf j).params es vs
  frame : FrameHolds L j fp σ es vs kfps hdr
  kids : KidsRun L σ es kfps ck
  hev : ∀ e ∈ es, e.Holds L.read σ
  /-- A loop helper's last call is its closing one. -/
  lastCall : (coreOf j).loop = true → ∀ c, (calls es).getLast? = some c → c.f = (coreOf j).name
  jt : JTHolds glob L
  tab : ∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2
  j1 : 1 ≤ j
  jn : j < nFns

/-- **The run is at the walk's position `st`**, from `W0`, the first `n` callees run, the
separately counted arms passed counting `x`. -/
structure PosZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (st : CW) (W0 : Regs K)
    (n : ℕ) (x : Opcode → ℕ) : Prop where
  seg : st.seg ∈ segs
  ok : CWOk L fp X st
  run : ∃ pre c, pre ++ st.its = st.seg.items ∧ Fall L (gpow fp) pre ∧
    RunC guest L W0 ⟨gpow (X.entry + st.seg.start), gpow fp⟩ c ∧
    ∀ op, c op + itemOps pre op ≤ st.cnt.get op + x op + ksum ck n op
  fresh : ∀ t, st.fresh = some t → st.seg.start = t ∧ st.its = st.seg.items ∧ getF X.idx t = some st.seg
  nm : ∀ n, st.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs
  ix : getF X.idx st.seg.start = some st.seg

/-- **A selector the check accepts is a value the path names.** -/
theorem PosZ.sel {H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck} {st : CW} {W0 : Regs K} {n : ℕ}
    {x : Opcode → ℕ} (hp : PosZ H st W0 n x) {v : V} (hv : v = V.n v.idx) (hs : selOk X st v = true) :
    v ∈ namedOf (coreOf j).params es vs := by
  unfold selOk at hs
  rw [hv]
  rcases Bool.or_eq_true_iff.mp hs with h | h
  · exact H.named _ h
  · rw [bitK_eq] at h
    exact hp.nm _ h

/-- The environment of the segment at offset `J` holds; at the window's end, where none starts,
the next window's. -/
def EnvAt (L : MemImage κ) (fp : ℕ) (X : CX) (wJ : ℕ) (wenv : Trie Sym) (J : ℕ) : Prop :=
  (∀ s, getF X.idx J = some s → s.start = J → EnvHolds L (gpow fp) s.env) ∧
    (J = wJ → getF X.idx J = none → EnvHolds L (gpow fp) wenv)

/-- **The run arrives at offset `J`**, from `W0`, within the counts `c` and the first `n`
callees'. -/
def Arr (L : MemImage κ) (fp : ℕ) (X : CX) (wJ : ℕ) (wenv : Trie Sym) (ck : List (Opcode → ℕ))
    (W0 : Regs K) (J : ℕ) (c : Cnt) (n : ℕ) (x : Opcode → ℕ) : Prop :=
  (∃ cr, RunC guest L W0 ⟨gpow (X.entry + J), gpow fp⟩ cr ∧ ∀ op, cr op ≤ c.get op + x op + ksum ck n op) ∧
    EnvAt L fp X wJ wenv J

/-- **The run is inside the segment starting at `J`**, its first `m` items passed, within the
counts `c` and the first `n` callees'. -/
def ArrMid (L : MemImage κ) (fp : ℕ) (X : CX) (ck : List (Opcode → ℕ)) (W0 : Regs K) (J m : ℕ)
    (c : Cnt) (n : ℕ) (x : Opcode → ℕ) : Prop :=
  ∃ s, getF X.idx J = some s ∧ s.start = J ∧ m ≤ s.items.length ∧ EnvHolds L (gpow fp) s.env ∧
    ∃ cr, Fall L (gpow fp) (s.items.take m) ∧ RunC guest L W0 ⟨gpow (X.entry + J), gpow fp⟩ cr ∧
      ∀ op, cr op + itemOps (s.items.take m) op ≤ c.get op + x op + ksum ck n op

/-! ## Moves -/

theorem segAtC_eq {t : ℕ} {st sn : CW} (h : segAtC X t st = some sn) :
    ∃ s, getF X.idx t = some s ∧ s.start = t ∧
      sn = ⟨s, s.items, st.book, st.fr, st.tg, st.nx, st.cnt, st.uq, some t, st.nm⟩ := by
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
    {W0 : Regs K} {n : ℕ} {xc : Opcode → ℕ} {c : Opcode → ℕ}
    (hr : RunC guest L W0 ⟨gpow (X.entry + t), gpow fp⟩ c)
    (hc : ∀ op, c op ≤ st.cnt.get op + xc op + ksum ck n op)
    (hnm : ∀ n, st.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs) :
    PosZ H sn W0 n xc ∧ sn.book = st.book ∧ sn.fr = st.fr ∧ sn.tg = st.tg ∧ sn.nx = st.nx ∧
      sn.cnt = st.cnt ∧ sn.uq = st.uq ∧ sn.seg.start = t := by
  obtain ⟨s, hs, hst, rfl⟩ := segAtC_eq h
  have hmem : s ∈ segs := by
    rw [H.idx, getF_eq] at hs
    exact index_get hs
  refine ⟨⟨hmem, ⟨he.1 s hs hst, hb, hfr, htg, hnx⟩, ⟨[], c, rfl, trivial, hst ▸ hr, fun op ↦ ?_⟩,
    fun t' ht' ↦ ?_, hnm, by rw [hst]; exact hs⟩, rfl, rfl, rfl, rfl, rfl, rfl, hst⟩
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
      se = ⟨st.seg, [], st.book, st.fr, st.tg, st.nx, c, st.uq, none, st.nm⟩ := by
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
    {n : ℕ} {xc : Opcode → ℕ} (hp : PosZ H st W0 n xc) (he : endAtC X st = .ok se) :
    se.seg = st.seg ∧ se.book = st.book ∧ se.fr = st.fr ∧ se.tg = st.tg ∧ se.nx = st.nx ∧
      se.uq = st.uq ∧
      ∀ r, st.seg.exit.kind.Regs L (gpow fp) X.entry r → ∃ cr, RunC guest L W0 r cr ∧
        (∀ op, cr op ≤ se.cnt.get op + xc op + ksum ck n op) ∧ EnvHolds L (gpow fp) st.seg.exit.env := by
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

theorem endAtC_nm {st se : CW} (he : endAtC X st = .ok se) : se.nm = st.nm := by
  obtain ⟨c, -, rfl⟩ := endAtC_eq he
  rfl

theorem segAtC_nm {t : ℕ} {st sn : CW} (h : segAtC X t st = some sn) : sn.nm = st.nm := by
  obtain ⟨s, -, -, rfl⟩ := segAtC_eq h
  rfl

theorem brAtC_eq {st st' : CW} {oc od of : ℕ} {x : Exit}
    (h : brAtC X st = .ok (st', oc, od, of, x)) :
    ∃ its c, passL X st st.its st.cnt = .ok (.branch oc od of x :: its, c) ∧
      st' = ⟨st.seg, its, st.book, st.fr, st.tg, st.nx, c.bumpJ, st.uq, none, st.nm⟩ := by
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
theorem brAtC_nm {st st' : CW} {oc od of : ℕ} {x : Exit} (h : brAtC X st = .ok (st', oc, od, of, x)) :
    st'.nm = st.nm := by
  obtain ⟨its, c, -, rfl⟩ := brAtC_eq h
  rfl

theorem brAtC_pos (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {st st' : CW} {oc od of : ℕ}
    {x : Exit} {W0 : Regs K} {n : ℕ} {xc : Opcode → ℕ} (hp : PosZ H st W0 n xc)
    (hb : brAtC X st = .ok (st', oc, od, of, x)) :
    st'.seg = st.seg ∧ st'.book = st.book ∧ st'.fr = st.fr ∧ st'.tg = st.tg ∧ st'.nx = st.nx ∧
      st'.uq = st.uq ∧ st'.fresh = none ∧ x ∈ st.seg.exits ∧ CWOk L fp X st' ∧
      ((Atom.jump oc od of).Holds L (gpow fp) → rdc L fp oc = some 0 → PosZ H st' W0 n xc) ∧
      (Taken L (gpow fp) oc od of → ∀ r, x.kind.Regs L (gpow fp) X.entry r → ∃ cr,
        RunC guest L W0 r cr ∧ (∀ op, cr op ≤ st'.cnt.get op + xc op + ksum ck n op) ∧
        EnvHolds L (gpow fp) x.env) := by
  obtain ⟨its, c, hpl, rfl⟩ := brAtC_eq hb
  obtain ⟨pre2, hpre2, hf2, hc2, -⟩ := passL_sound H.hX hp.ok st.its st.cnt hpl
  obtain ⟨pre, c0, hpre, hf, hrun, hc0⟩ := hp.run
  have hitems : st.seg.items = (pre ++ pre2) ++ .branch oc od of x :: its := by
    rw [← hpre, ← hpre2, List.append_assoc]
  have hx : x ∈ st.seg.exits := H.exits _ hp.seg x (Or.inr (by
    rw [hitems, branchExits_append]
    simp [branchExits]))
  have hok : CWOk L fp X ⟨st.seg, its, st.book, st.fr, st.tg, st.nx, c.bumpJ, st.uq, none, st.nm⟩ :=
    ⟨hp.ok.env, hp.ok.book, hp.ok.fr, hp.ok.tg, hp.ok.nx⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx, hok, fun hj h0 ↦ ?_, fun ht r hr ↦ ?_⟩
  · refine ⟨hp.seg, hok, ⟨pre ++ pre2 ++ [.branch oc od of x], c0, by rw [hitems]; simp, ?_, hrun,
      fun op ↦ ?_⟩, fun t ht ↦ (by cases ht), hp.nm, hp.ix⟩
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

/-- **How the walk of a window ends by the return**: the run reaches the return registers
(`main`: the final ones) within the most a path runs and the first `n` callees' counts, its
returned values at the cells after its parameters. -/
def FinZ (L : MemImage κ) (j fp : ℕ) (X : CX) (ck : List (Opcode → ℕ)) (W0 : Regs K) (n : ℕ)
    (x : Opcode → ℕ) (vs' : List V) : Prop :=
  (∃ r cr, (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
    RunC guest L W0 r cr ∧ ∀ op, cr op ≤ X.pmax.get op + x op + ksum ck n op) ∧
  ∀ k (hk : k < vs'.length), X.loc.cell vs'[k] = 2 + X.nargs + k ∧ 2 ≤ X.loc.cell vs'[k] ∧
    X.loc.cell vs'[k] < X.fs

/-- **What the walk of a block from a position gives**: on a path through the block, from a
position the run is at, the run arrives where the walk ends, or returns. -/
def WGood (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (ss : List Stmt) (st : CW) : Prop :=
  ∀ (ebef eaft : List Ev) (o : Out) (W0 : Regs K) (pre : List Stmt) (xc : Opcode → ℕ),
    walk σ ss = o → es = ebef ++ o.evs ++ eaft → o ≠ .stuck →
    (Stmt.noRetList ss = true ∨ (lastOkC ss = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ ss)) →
    PosZ H st W0 (calls ebef).length xc → (cw X ss st).ok = true →
    (∀ J c u, cw X ss st = .join J c u → ∃ es', o = .fall es' ∧
      Arr L fp X wJ wenv ck W0 J c (calls (ebef ++ es')).length (xc + costW X.acs σ ss)) ∧
    (∀ J m c u, cw X ss st = .mid J m c u → ∃ es', o = .fall es' ∧
      ArrMid L fp X ck W0 J m c (calls (ebef ++ es')).length (xc + costW X.acs σ ss)) ∧
    (cw X ss st = .done → ∃ es' vs', o = .ret es' vs' ∧
      FinZ L j fp X ck W0 (calls (ebef ++ es')).length (xc + costW X.acs σ ss) vs')

theorem walk_nilZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (st : CW) : WGood H [] st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  rw [walk] at hw
  subst hw
  rw [cw_nil] at hok ⊢
  refine ⟨fun J c u hj ↦ ⟨[], rfl, ?_⟩, fun J m c u hj ↦ ⟨[], rfl, ?_⟩, fun hd ↦ ?_⟩
  · rw [List.append_nil]
    rcases endC_ok hok with ⟨t, hf, he⟩ | ⟨hf, -, se, t, hse, hk, hsu, he⟩ | ⟨-, _, _, _, -, -, -, -, -, he⟩
    · rw [he] at hj
      simp only [RC.join.injEq] at hj
      obtain ⟨rfl, rfl, rfl⟩ := hj
      obtain ⟨hst, hits, hidx⟩ := hp.fresh _ hf
      obtain ⟨pre, c, hpre, -, hrun, hc⟩ := hp.run
      have : pre = [] := by
        rw [hits] at hpre
        simpa using hpre
      subst this
      refine ⟨⟨c, hst ▸ hrun, fun op ↦ by simpa [itemOps, costW] using hc op⟩, fun s hs _ ↦ ?_,
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
    · rw [he] at hj
      cases hj
  · rw [List.append_nil]
    rcases endC_ok hok with ⟨t, -, he⟩ | ⟨-, -, se, t, -, -, -, he⟩ |
      ⟨-, J', m', c', -, hJ, hm, hlen, hpl, he⟩
    · rw [he] at hj
      cases hj
    · rw [he] at hj
      cases hj
    · rw [he] at hj
      simp only [RC.mid.injEq] at hj
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hj
      obtain ⟨pre2, hpre2, hf2, hc2, -⟩ := passL_sound H.hX hp.ok _ st.cnt hpl
      obtain ⟨pre, c0, hpre, hf, hrun, hc0⟩ := hp.run
      rw [List.append_nil] at hpre2
      have hl : pre.length + st.its.length = st.seg.items.length := by
        rw [← hpre, List.length_append]
      have ht : st.seg.items.take m' = pre ++ pre2 := by
        have hk : m' = pre.length + (st.its.length - (st.seg.items.length - m')) := by omega
        calc st.seg.items.take m'
            = (pre ++ st.its).take (pre.length + (st.its.length - (st.seg.items.length - m'))) := by
              rw [hpre, ← hk]
          _ = pre ++ pre2 := by
              rw [List.take_append, hpre2, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
      refine ⟨st.seg, by rw [← hJ]; exact hp.ix, hJ, hm, hp.ok.env, c0, ?_, by rw [← hJ]; exact hrun,
        fun op ↦ ?_⟩
      · rw [ht, fall_append]
        exact ⟨hf, hf2⟩
      · rw [ht, itemOps_append, hc2 op]
        have := hc0 op
        simp only [Pi.add_apply, costW, Pi.zero_apply, Nat.add_zero]
        omega
  · rcases endC_ok hok with ⟨t, -, he⟩ | ⟨-, -, se, t, -, -, -, he⟩ | ⟨-, _, _, _, -, -, -, -, -, he⟩ <;>
      rw [he] at hd <;> cases hd

theorem lastOkC_cons {s : Stmt} {ss : List Stmt} (h : lastOkC (s :: ss) = true)
    (hs : ∀ vs, s ≠ .ret vs) : Stmt.noRet s = true ∧ lastOkC ss = true := by
  cases ss with
  | nil => cases s <;> simp_all [lastOkC]
  | cons s' ss => cases s <;> simp_all [lastOkC]

/-- **A statement falling through, then the rest of the block.** -/
theorem walk_step (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {s : Stmt} {ss : List Stmt}
    (ih : ∀ st, WGood H ss st) (hs : Stmt.noRet s = true)
    {st st'' : CW} {ebef eaft e1 : List Ev} {o : Out} {W0 : Regs K} {pre : List Stmt}
    (hw1 : walk1 σ s = .fall e1) (hw : walk σ (s :: ss) = o) (hes : es = ebef ++ o.evs ++ eaft)
    (hstk : o ≠ .stuck)
    (hshape : Stmt.noRetList (s :: ss) = true ∨
      (lastOkC (s :: ss) = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ s :: ss))
    {xc : Opcode → ℕ} (hp'' : PosZ H st'' W0 (calls (ebef ++ e1)).length (xc + cost1 X.acs σ s))
    (hcw : cw X (s :: ss) st = cw X ss st'') (hok : (cw X (s :: ss) st).ok = true) :
    (∀ J c u, cw X (s :: ss) st = .join J c u → ∃ es', o = .fall es' ∧
      Arr L fp X wJ wenv ck W0 J c (calls (ebef ++ es')).length (xc + costW X.acs σ (s :: ss))) ∧
    (∀ J m c u, cw X (s :: ss) st = .mid J m c u → ∃ es', o = .fall es' ∧
      ArrMid L fp X ck W0 J m c (calls (ebef ++ es')).length (xc + costW X.acs σ (s :: ss))) ∧
    (cw X (s :: ss) st = .done → ∃ es' vs', o = .ret es' vs' ∧
      FinZ L j fp X ck W0 (calls (ebef ++ es')).length (xc + costW X.acs σ (s :: ss)) vs') := by
  have ex : xc + costW X.acs σ (s :: ss) = (xc + cost1 X.acs σ s) + costW X.acs σ ss := by
    rw [costW, add_assoc]
  rw [ex]
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
  rw [hcw] at hok ⊢
  obtain ⟨h1, hm, h2⟩ := ih st'' (ebef ++ e1) eaft _ W0 (pre ++ [s]) _ rfl hes' hstk' hshape' hp'' hok
  refine ⟨fun J c u hj ↦ ?_, fun J m c u hj ↦ ?_, fun hd ↦ ?_⟩
  · obtain ⟨es', he, ha⟩ := h1 J c u hj
    refine ⟨e1 ++ es', by rw [he]; rfl, ?_⟩
    rw [← List.append_assoc]
    exact ha
  · obtain ⟨es', he, ha⟩ := hm J m c u hj
    refine ⟨e1 ++ es', by rw [he]; rfl, ?_⟩
    rw [← List.append_assoc]
    exact ha
  · obtain ⟨es', vs', he, hf⟩ := h2 hd
    refine ⟨e1 ++ es', vs', by rw [he]; rfl, ?_⟩
    rw [← List.append_assoc]
    exact hf

theorem walk_atomZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (a : Core.Atom)
    (ss : List Stmt) (st : CW) (ih : ∀ st, WGood H ss st) : WGood H (.atom a :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  refine walk_step H ih rfl rfl hw hes hs hshape ?_ (cw_atom a ss st) hok
  have hc : calls (ebef ++ [.atom a]) = calls ebef := by simp [calls, Ev.call?]
  rw [hc]
  refine ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, hp.ok.tg, hp.ok.nx⟩, hp.run, fun t ht ↦ (by cases ht),
    fun n hn ↦ ?_, hp.ix⟩
  rcases nvVals_spec _ _ n hn with h | h
  · exact hp.nm n h
  · refine uses_named (e := .atom a) ?_ h
    have hst : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [← hw, walk, h]; rfl)
    rw [hes, ← hw]
    cases h : walk σ ss with
    | fall e => simp [walk, walk1, h, Out.seq, Out.pre, Out.evs]
    | ret e v => simp [walk, walk1, h, Out.seq, Out.pre, Out.evs]
    | stuck => exact absurd h hst

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
    {xc : Opcode → ℕ} (hp : PosZ H st W0 n xc) {q : ℕ} {fcs : List (ℕ × FC)} {kfp : ℕ}
    (hq : rdc L fp q = some (ofK (gpow kfp))) (hf : ∀ p ∈ fcs, FCHolds L fp kfp p.1 p.2) :
    PosZ H { st with fr := (q, fcs) :: st.fr } W0 n xc :=
  ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, fun x hx ↦ by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨kfp, hq, hf⟩
    · exact hp.ok.fr x hx, hp.ok.tg, hp.ok.nx⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩

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

theorem inFrame_append (n : ℕ) : ∀ (l₁ l₂ : List ℕ), inFrame n (l₁ ++ l₂) = (inFrame n l₁ && inFrame n l₂)
  | [], _ => by simp [inFrame]
  | c :: l₁, l₂ => by simp only [List.cons_append, inFrame, inFrame_append n l₁ l₂, Bool.and_assoc]

/-- A call on the path, other than to the function itself, is not a loop's last. -/
theorem notLast (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {n : ℕ} {c : Call}
    (hc : (calls es)[n]? = some c) (hf : c.f ≠ (coreOf j).name) :
    (coreOf j).loop = true → n + 1 < (calls es).length := by
  intro hl
  have hlt : n < (calls es).length := (List.getElem?_eq_some_iff.mp hc).1
  refine lt_of_le_of_ne hlt fun he ↦ hf (H.lastCall hl c ?_)
  rw [List.getLast?_eq_getElem?, ← he, Nat.add_sub_cancel]
  exact hc

theorem walk_pre_evs {e1 : List Ev} {o' : Out} (hst : o' ≠ .stuck) : (o'.pre e1).evs = e1 ++ o'.evs := by
  cases o' with
  | fall _ => rfl
  | ret _ _ => rfl
  | stuck => exact absurd rfl hst

theorem walk_callZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (f : String)
    (args rets : List V) (ss : List Stmt) (st : CW) (ih : ∀ st, WGood H ss st) :
    WGood H (.call f args rets :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨e, q, r, j', sr, hk, hj, hf, hna, hnr, hle, hsu, hsite, hbit, hin, hself, haf, hcw⟩ :=
    cw_call H.G hok
  obtain ⟨se, s', hse, hs', rfl⟩ := afterC_ok haf
  obtain ⟨hj1, hj2, he⟩ := calleeC_some H.G hj
  have hfn : f = (coreOf j').name := by rw [hf, H.G]; rfl
  have hw' : o = (walk σ ss).pre [.call f args rets] := by rw [← hw]; rfl
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hw', h]; rfl)
  have hes2 : es = ebef ++ Ev.call f args rets :: ((walk σ ss).evs ++ eaft) := by
    rw [hes, hw', walk_pre_evs hst']
    simp
  set n := (calls ebef).length with hn
  have hci : (calls es)[n]? = some ⟨f, args, rets, true⟩ := by rw [hes2]; exact calls_at rfl
  obtain ⟨s0, hs0, hq0, hr0, ht0⟩ := siteOk_spec hsite
  have hnl := notLast H hci fun h ↦ hself (h.trans H.name.symm)
  have hin' : inFrame X.fs (s0.q :: args.map X.loc.cell) = true := by
    rw [hq0]
    simp only [inFrame, Bool.and_eq_true] at hin ⊢
    refine ⟨hin.1, ?_⟩
    have h2 := hin.2
    rw [List.map_append, inFrame_append, Bool.and_eq_true] at h2
    exact h2.1
  obtain ⟨kfp, hkfp, hq, hfcs, hret⟩ := call_frame H hci hj1 hj2 hfn hs0 hnl hin'
    (selfs := (X.G.sig j').env.map (·.1)) (fun o ho ↦ by rw [H.G] at ho; exact ho)
  rw [hq0] at hq
  rw [hr0] at hfcs hret
  obtain ⟨-, hkid⟩ := H.kids
  obtain ⟨⟨rr, hrr, hrun⟩, hrets⟩ := hkid n _ kfp hci hkfp rfl
  rw [hret] at hrr
  obtain rfl := Option.some.inj hrr
  have hp1 := posZ_fr H hp hq hfcs
  obtain ⟨hseg, hbk, hfr, htg, hnx, huq, hreach⟩ := endAtC_reach H hp1 hse
  simp only at hseg hbk hfr htg hnx huq hreach
  obtain ⟨cr, hcr, hcle, henv⟩ := hreach ⟨gpow e, gpow kfp⟩ (by
    rw [hk]
    exact ⟨_, gpow e, hq, isInK_ofK _, rfl, by simp⟩)
  have hent : entryOf f = e := by rw [hfn, entryOf_callee hj1 hj2, he]
  rw [hent] at hrun
  have hgr : gpow r = gpow (X.entry + (r - X.entry)) := by rw [Nat.add_sub_cancel' hle]
  have hrun2 : RunC guest L W0 ⟨gpow (X.entry + (r - X.entry)), gpow fp⟩ (cr + ck.getD n 0) := by
    rw [← hgr]
    exact hcr.trans hrun
  have henvR : EnvAt L fp X wJ wenv (r - X.entry) :=
    envAt_of_exit H hp.seg (H.exits _ hp.seg _ (Or.inl rfl)) (by rw [hsu]; simp) henv
  obtain ⟨hps, hbk', hfr', htg', hnx', hcnt', huq', hstart'⟩ :=
    segAtC_pos H (xc := xc) hs' (by rw [hbk]; exact hp.ok.book) (by rw [hfr]; exact hp1.ok.fr)
      (by rw [htg]; exact hp.ok.tg) (by rw [hnx]; exact hp.ok.nx) henvR (n := n + 1) hrun2
      (fun op ↦ by rw [Pi.add_apply, ksum_succ]; have := hcle op; omega)
      (by rw [endAtC_nm hse]; exact hp.nm)
  have hc1 : (calls (ebef ++ [.call f args rets])).length = n + 1 := calls_append_one rfl
  refine walk_step H ih rfl rfl hw hes hs hshape ?_ hcw ?_
  · rw [hc1]
    refine ⟨hps.seg, ⟨hps.ok.env, hps.ok.book, fun x hx ↦ ?_, hps.ok.tg, hps.ok.nx⟩, hps.run,
      fun t ht ↦ ?_, hps.nm, hps.ix⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨kfp, hq, fun p hp' ↦ ?_⟩
        rcases List.mem_append.mp hp' with hp' | hp'
        · exact hfcs p hp'
        · obtain ⟨k, hk', rfl⟩ := argFC_mem hp'
          have hv : X.loc.cell rets[k] ∈ (args ++ rets).map X.loc.cell :=
            List.mem_map.mpr ⟨_, List.mem_append_right _ (List.getElem_mem hk'), rfl⟩
          have hc := inFrame_mem hin _ (List.mem_cons_of_mem _ hv)
          have hm : Ev.call f args rets ∈ es := by rw [hes2]; simp
          refine ⟨σ rets[k], val_cell H.frame H.loc (uses_named hm (by simp [Ev.uses, List.getElem_mem]))
            hc.1 (H.fs ▸ hc.2), ?_⟩
          have := hrets k hk'
          rw [gpow_addC] at this
          exact this
      · exact hp.ok.fr x hx
    · simp only at ht
      cases hre : rets.isEmpty
      · rw [hre] at ht; cases ht
      · rw [hre] at ht
        exact hps.fresh t ht
  · exact hok

/-! ## Branches -/

theorem posZ_book (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {st : CW} {W0 : Regs K} {n : ℕ}
    {xc : Opcode → ℕ} (hp : PosZ H st W0 n xc) {B : BookC} (hB : BookOk L fp B) : PosZ H { st with book := B } W0 n xc :=
  ⟨hp.seg, ⟨hp.ok.env, hB, hp.ok.fr, hp.ok.tg, hp.ok.nx⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩

/-- Entering offset `t` with given counts and set-up cells. -/
theorem segAtC_posW (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {t : ℕ} {st sn : CW}
    (h : segAtC X t st = some sn) (hok : CWOk L fp X st) (he : EnvAt L fp X wJ wenv t)
    {W0 : Regs K} {n : ℕ} {xc : Opcode → ℕ} {c : Opcode → ℕ}
    (hr : RunC guest L W0 ⟨gpow (X.entry + t), gpow fp⟩ c)
    {C : Cnt} {U : ℕ} (hc : ∀ op, c op ≤ C.get op + xc op + ksum ck n op)
    (hnm : ∀ n, st.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs) :
    PosZ H { sn with cnt := C, uq := U } W0 n xc ∧ sn.book = st.book ∧ sn.fr = st.fr ∧
      sn.tg = st.tg ∧ sn.nx = st.nx := by
  obtain ⟨s, hs, hst, rfl⟩ := segAtC_eq h
  have hmem : s ∈ segs := by
    rw [H.idx, getF_eq] at hs
    exact index_get hs
  refine ⟨⟨hmem, ⟨he.1 s hs hst, hok.book, hok.fr, hok.tg, hok.nx⟩,
    ⟨[], c, rfl, trivial, hst ▸ hr, fun op ↦ ?_⟩, fun t' ht' ↦ ?_, hnm, by rw [hst]; exact hs⟩, rfl, rfl,
    rfl, rfl⟩
  · simpa [itemOps] using hc op
  · obtain rfl := Option.some.inj ht'
    exact ⟨hst, rfl, hs⟩

theorem noRet_of_shape {s : Stmt} {ss : List Stmt} (hs : ∀ vs, s ≠ .ret vs) {eaft : List Ev}
    {pre : List Stmt} (h : Stmt.noRetList (s :: ss) = true ∨
      (lastOkC (s :: ss) = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ s :: ss)) :
    Stmt.noRet s = true := by
  rcases h with h | ⟨h, -, -⟩
  · simp only [Stmt.noRetList, Bool.and_eq_true] at h
    exact h.1
  · exact (lastOkC_cons h hs).1

theorem walk_iteZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (c : V) (z n ss : List Stmt)
    (st : CW) (ihz : ∀ st, WGood H z st) (ihn : ∀ st, WGood H n st) (ih : ∀ st, WGood H ss st) :
    WGood H (.ite c z n :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨st', od, of, x, t, sn, J, c1, u1, c2, u2, sj, hb, hk, hfr, hod, hof, hsu, hsn, hz, hn,
    hsj, hcw⟩ := cw_ite hok
  obtain ⟨hseg', hbk', hfr', htg', hnx', huq', hfresh', hx, hok', hfall, htaken⟩ := brAtC_pos H hp hb
  have hnr := noRet_of_shape (fun _ h ↦ by cases h) hshape
  simp only [Stmt.noRet, Bool.and_eq_true] at hnr
  -- the branch the path takes
  set wb := if σ c = 0 then walk σ z else walk σ n with hwb
  have hw1 : walk1 σ (.ite c z n) = wb.pre [.inK c] := rfl
  have hwo : o = (wb.pre [.inK c]).seq (walk σ ss) := by rw [← hw, walk, hw1]
  have hwb_ns : wb ≠ .stuck := fun h ↦ hs (by rw [hwo, h]; rfl)
  obtain ⟨eb, hweb⟩ : ∃ eb, wb = .fall eb := by
    rcases (show (∃ es, wb = .fall es) ∨ wb = .stuck by
      rw [hwb]; split_ifs
      · exact walk_noRetC z hnr.1
      · exact walk_noRetC n hnr.2) with h | h
    · exact h
    · exact absurd h hwb_ns
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hwo, hweb, h]; rfl)
  have hes2 : es = ebef ++ (Ev.inK c :: eb) ++ ((walk σ ss).evs ++ eaft) := by
    rw [hes, hwo, hweb]
    cases hws : walk σ ss with
    | fall _ => simp [Out.seq, Out.pre, Out.evs]
    | ret _ _ => simp [Out.seq, Out.pre, Out.evs]
    | stuck => exact absurd hws hst'
  have hinK : Ev.inK c ∈ es := by rw [hes2]; simp
  have hcK : IsInK (σ c) := H.hev _ hinK
  have hfc := inFrame_mem hfr _ List.mem_cons_self
  have hcell : rdc L fp (X.loc.cell c) = some (σ c) :=
    val_cell H.frame H.loc (uses_named hinK (by simp [Ev.uses])) hfc.1 (H.fs ▸ hfc.2)
  obtain ⟨vd, hvd, hKd⟩ := cellK_sound H.hX hok' hod
  obtain ⟨vf, hvf, hKf⟩ := cellK_sound H.hX hok' hof
  have hjump : (Atom.jump (X.loc.cell c) od of).Holds L (gpow fp) :=
    ⟨σ c, vd, vf, hcell, hvd, hvf, hcK, hKd, hKf⟩
  -- the rest of the path after the branch
  have hatoms : ∀ b : List Stmt, walk σ b = .fall eb → ∀ a, Stmt.atom a ∈ b → Ev.atom a ∈ es :=
    fun b hb a ha ↦ by rw [hes2]; simp [atom_on_pathC hb ha]
  have hn1 : (calls (ebef ++ [Ev.inK c])).length = (calls ebef).length := by
    rw [calls_append_none rfl]
  -- the branch's walk, to its join
  obtain ⟨cb, hcb, crun⟩ : ∃ cb : Cnt, (cb = c1 ∨ cb = c2) ∧
      Arr L fp X wJ wenv ck W0 J cb (calls (ebef ++ [Ev.inK c] ++ eb)).length
        (xc + cost1 X.acs σ (.ite c z n)) := by
    by_cases h0 : σ c = 0
    · have hwz : walk σ z = .fall eb := by rw [← hweb, hwb]; simp only [h0, ↓reduceIte]
      have hpz := posZ_book H (hfall hjump (h0 ▸ hcell))
        (fileB_ok H.frame H.loc H.hev z st'.book (hbk' ▸ hp.ok.book) (hatoms z hwz))
      have hpz' : PosZ H { st' with book := fileB X.loc X.fs z st'.book } W0
          (calls (ebef ++ [Ev.inK c])).length xc := by
        rw [hn1, H.fs]
        exact hpz
      obtain ⟨h1, -, -⟩ := ihz _ (ebef ++ [Ev.inK c]) ((walk σ ss).evs ++ eaft) _ W0 [] xc hwz
        (by rw [hes2, show (Out.fall eb).evs = eb from rfl]; simp) (by simp) (Or.inl hnr.1) hpz' (by rw [hz]; rfl)
      obtain ⟨es', he', ha⟩ := h1 J c1 u1 hz
      simp only [Out.fall.injEq] at he'
      subst he'
      have e : cost1 X.acs σ (.ite c z n) = costW X.acs σ z := by simp only [cost1, h0, ↓reduceIte]
      exact ⟨c1, Or.inl rfl, by rw [e]; exact ha⟩
    · have hwn : walk σ n = .fall eb := by rw [← hweb, hwb]; simp only [h0, ↓reduceIte]
      obtain ⟨cr, hcr, hcle, henv⟩ := htaken ⟨hjump, σ c, hcell, h0⟩ _ (by rw [hk]; rfl)
      have henvT : EnvAt L fp X wJ wenv t :=
        envAt_of_exit H hp.seg hx (by rw [hsu]; simp) henv
      obtain ⟨hps, hbkn, -, -, -, -, -, -⟩ := segAtC_pos H (xc := xc) hsn hok'.book hok'.fr hok'.tg hok'.nx
        henvT hcr hcle (by rw [brAtC_nm hb]; exact hp.nm)
      have hpn : PosZ H { sn with book := fileB X.loc X.fs n st'.book } W0
          (calls (ebef ++ [Ev.inK c])).length xc := by
        rw [hn1, H.fs]
        exact posZ_book H hps (fileB_ok H.frame H.loc H.hev n st'.book (hbk' ▸ hp.ok.book)
          (hatoms n hwn))
      obtain ⟨h1, -, -⟩ := ihn _ (ebef ++ [Ev.inK c]) ((walk σ ss).evs ++ eaft) _ W0 [] xc hwn
        (by rw [hes2, show (Out.fall eb).evs = eb from rfl]; simp) (by simp) (Or.inl hnr.2) hpn (by rw [hn]; rfl)
      obtain ⟨es', he', ha⟩ := h1 J c2 u2 hn
      simp only [Out.fall.injEq] at he'
      subst he'
      have e : cost1 X.acs σ (.ite c z n) = costW X.acs σ n := by simp only [cost1, h0, ↓reduceIte]
      exact ⟨c2, Or.inr rfl, by rw [e]; exact ha⟩
  -- the join, then the rest
  obtain ⟨⟨cr, hcr, hcle⟩, henvJ⟩ := crun
  obtain ⟨hpj, -⟩ := segAtC_posW H (xc := xc + cost1 X.acs σ (.ite c z n)) hsj hok' henvJ hcr
    (C := Cnt.max c1 c2) (U := Nat.lor u1 u2)
    (n := (calls (ebef ++ [Ev.inK c] ++ eb)).length)
    (fun op ↦ by
      have := hcle op
      have h1 : c1.get op ≤ Nat.max (c1.get op) (c2.get op) := Nat.le_max_left _ _
      have h2 : c2.get op ≤ Nat.max (c1.get op) (c2.get op) := Nat.le_max_right _ _
      rw [Cnt.get_max]
      rcases hcb with rfl | rfl <;> omega)
    (by rw [brAtC_nm hb]; exact hp.nm)
  have hw1' : walk1 σ (.ite c z n) = .fall (Ev.inK c :: eb) := by rw [hw1, hweb]; rfl
  refine walk_step H ih (by simp [Stmt.noRet, hnr.1, hnr.2]) hw1' hw hes hs hshape ?_ hcw hok
  rw [show ebef ++ Ev.inK c :: eb = ebef ++ [Ev.inK c] ++ eb by simp]
  exact hpj

/-! ## Conditional calls -/

theorem passL_peek {st : CW} : ∀ {its : List Item} {c : Cnt} {oc od of : ℕ} {x : Exit}
    {rest : List Item} {c' : Cnt}, passL X st its c = .ok (.branch oc od of x :: rest, c') →
    peekBr its = some (oc, x)
  | [], _, _, _, _, _, _, _, h => by simp [passL] at h
  | .ins (.instr pc ins) :: its, c, oc, od, of, x, rest, c', h => by
    simp only [passL] at h
    cases hj : justI X st pc ins
    · rw [hj] at h; cases h
    · rw [hj, Bool.cond_true, Cnt.seq_eq] at h
      exact passL_peek (its := its) h
  | .ins (.jump a b d) :: its, c, oc, od, of, x, rest, c', h => by
    simp only [passL] at h
    cases hj : cellK X st a && cellK X st b && cellK X st d
    · rw [hj] at h; cases h
    · rw [hj, Bool.cond_true, Cnt.seq_eq] at h
      exact passL_peek (its := its) h
  | .ins (.copy ..) :: _, _, _, _, _, _, _, _, h => by simp [passL] at h
  | .ins (.eq ..) :: _, _, _, _, _, _, _, _, h => by simp [passL] at h
  | .ins (.nz ..) :: _, _, _, _, _, _, _, _, h => by simp [passL] at h
  | .ins (.ne ..) :: _, _, _, _, _, _, _, _, h => by simp [passL] at h
  | .ins (.bool ..) :: _, _, _, _, _, _, _, _, h => by simp [passL] at h
  | .ins (.range ..) :: _, _, _, _, _, _, _, _, h => by simp [passL] at h
  | .ins (.powPair ..) :: _, _, _, _, _, _, _, _, h => by simp [passL] at h
  | .fact _ :: its, c, oc, od, of, x, rest, c', h => by
    simp only [passL] at h
    exact passL_peek (its := its) h
  | .branch oc' od' of' x' :: its, c, oc, od, of, x, rest, c', h => by
    simp only [passL, Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Item.branch.injEq] at h
    obtain ⟨⟨⟨rfl, rfl, rfl, rfl⟩, -⟩, -⟩ := h
    rfl

theorem brAtC_peek {st st' : CW} {oc od of : ℕ} {x : Exit}
    (h : brAtC X st = .ok (st', oc, od, of, x)) : peekBr st.its = some (oc, x) := by
  obtain ⟨its, c, hpl, -⟩ := brAtC_eq h
  exact passL_peek hpl

theorem posZ_nx (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) {st : CW} {W0 : Regs K} {n : ℕ}
    {xc : Opcode → ℕ} (hp : PosZ H st W0 n xc) {nx : List (ℕ × FC)} (hn : NxOk L fp X.fs nx) :
    PosZ H { st with nx := nx } W0 n xc :=
  ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, hp.ok.tg, hn⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩

/-- A conditional call's event, `.skip` or `.call` as its condition says. -/
theorem callIf_ev (c : V) (f : String) (args : List V) :
    Ev.call? (if σ c = 0 then Ev.skip f args else Ev.call f args []) =
      some ⟨f, args, [], !(decide (σ c = 0))⟩ := by
  split_ifs with h <;> simp [Ev.call?, h]

theorem Cnt.le_spec {c c' : Cnt} (h : c.le c' = true) : ∀ op, c.get op ≤ c'.get op := by
  simp only [Cnt.le, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  intro op
  cases op
  exacts [h1, h2, h3, h4, h5, h6]

/-- **A conditional call**, along the path: of another function, or a loop's closing one. -/
theorem walk_callIfZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (c : V) (f : String)
    (args : List V) (ss : List Stmt) (st : CW) (ih : ∀ st, WGood H ss st) :
    WGood H (.callIf c f args :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨x, hpk, hin, hcase⟩ := cw_callIf H.G hok
  set ev : Ev := if σ c = 0 then Ev.skip f args else Ev.call f args [] with hev
  have hwo : o = (walk σ ss).pre [.inK c, ev] := by rw [← hw]; rfl
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hwo, h]; rfl)
  have hes2 : es = (ebef ++ [Ev.inK c]) ++ ev :: ((walk σ ss).evs ++ eaft) := by
    rw [hes, hwo, walk_pre_evs hst']
    simp
  have hinK : Ev.inK c ∈ es := by rw [hes2]; simp
  have hcK : IsInK (σ c) := H.hev _ hinK
  have hfr0 := inFrame_mem hin _ List.mem_cons_self
  have hcell : rdc L fp (X.loc.cell c) = some (σ c) :=
    val_cell H.frame H.loc (uses_named hinK (by simp [Ev.uses])) hfr0.1 (H.fs ▸ hfr0.2)
  set n := (calls ebef).length with hn
  have hn' : (calls (ebef ++ [Ev.inK c])).length = n := by rw [calls_append_none rfl]
  have hci : (calls es)[n]? = some ⟨f, args, [], !(decide (σ c = 0))⟩ := by
    rw [hes2, ← hn']
    exact calls_at (callIf_ev c f args)
  have hc1 : (calls (ebef ++ [Ev.inK c, ev])).length = n + 1 := by
    rw [show ebef ++ [Ev.inK c, ev] = (ebef ++ [Ev.inK c]) ++ [ev] by simp,
      calls_append_one (callIf_ev c f args), hn']
  have hargs : ∀ k (hk : k < args.length), rdc L fp (X.loc.cell args[k]) = some (σ args[k]) := by
    intro k hk
    have hv : X.loc.cell args[k] ∈ X.loc.cell c :: args.map X.loc.cell :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩)
    have hc := inFrame_mem hin _ hv
    have hevm : ev ∈ es := by rw [hes2]; simp
    refine val_cell H.frame H.loc (uses_named hevm ?_) hc.1 (H.fs ▸ hc.2)
    rw [hev]
    split_ifs <;> simp [Ev.uses, List.getElem_mem]
  rcases hcase with ⟨e, q, r, j', st', oc', od, of, x', se, t, sr, hk, hj, hf, hna, hnr, hle, hsu,
      hsite, hbit, hinq, hfne, hb, hod, hof, hse, ht, hrt, hsu', hsr, hcw⟩ |
    ⟨e, S, st', oc', od, of, x', se, hk, hss, he, hf, hS, hna, hnr, hmain, hsn, hb, hod, hof,
      hle1, hse, hkr, hle2, hcw⟩
  · -- a call of another function
    obtain ⟨hj1, hj2, hent⟩ := calleeC_some H.G hj
    have hfn : f = (coreOf j').name := by rw [hf, H.G]; rfl
    obtain ⟨s0, hs0, hq0, hr0, -⟩ := siteOk_spec hsite
    have hnl := notLast H hci fun h ↦ hfne (h.trans H.name.symm)
    have hin' : inFrame X.fs (s0.q :: args.map X.loc.cell) = true := by
      rw [hq0]
      simp only [inFrame, Bool.and_eq_true] at hin hinq ⊢
      exact ⟨hinq.1, hin.2⟩
    obtain ⟨kfp, hkfp, hq, hfcs, hret⟩ := call_frame H hci hj1 hj2 hfn hs0 hnl hin'
      (selfs := (X.G.sig j').env.map (·.1)) (fun o ho ↦ by rw [H.G] at ho; exact ho)
    rw [hq0] at hq
    rw [hr0] at hfcs hret
    have hp1 := posZ_fr H hp hq hfcs
    obtain ⟨hseg', -, -, -, -, -, -, hx, hok', hfall, htaken⟩ := brAtC_pos H hp1 hb
    have hpk' := brAtC_peek hb
    simp only at hpk' hseg' hx
    rw [hpk] at hpk'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpk')
    obtain ⟨vd, hvd, hKd⟩ := cellK_sound H.hX hok' hod
    obtain ⟨vf, hvf, hKf⟩ := cellK_sound H.hX hok' hof
    have hjump : (Atom.jump (X.loc.cell c) od of).Holds L (gpow fp) :=
      ⟨σ c, vd, vf, hcell, hvd, hvf, hcK, hKd, hKf⟩
    have hgr : gpow r = gpow (X.entry + (r - X.entry)) := by rw [Nat.add_sub_cancel' hle]
    obtain ⟨cr, hcr, hcle, henvR⟩ : ∃ cr,
        RunC guest L W0 ⟨gpow (X.entry + (r - X.entry)), gpow fp⟩ cr ∧
        (∀ op, cr op ≤ (Cnt.max se.cnt st'.cnt).get op + xc op + ksum ck (n + 1) op) ∧
        EnvAt L fp X wJ wenv (r - X.entry) := by
      by_cases h0 : σ c = 0
      · have hp' := hfall hjump (h0 ▸ hcell)
        obtain ⟨hsg, -, -, -, -, -, hr⟩ := endAtC_reach H hp' hse
        rw [hsg] at ht hsu'
        obtain ⟨cr, hcr, hle', henv⟩ := hr ⟨gpow (X.entry + t), gpow fp⟩ (by rw [ht]; rfl)
        rw [hrt] at hcr
        refine ⟨cr, hcr, fun op ↦ ?_, ?_⟩
        · have := hle' op
          have h1 : se.cnt.get op ≤ Nat.max (se.cnt.get op) (st'.cnt.get op) := Nat.le_max_left _ _
          have h2 := ksum_mono ck (show n ≤ n + 1 by omega) op
          rw [Cnt.get_max]
          omega
        · rw [← hrt]
          exact envAt_of_exit H hp'.seg (H.exits _ hp'.seg _ (Or.inl rfl)) (by rw [hsu']; simp) henv
      · obtain ⟨cr, hcr, hle', henv⟩ := htaken ⟨hjump, σ c, hcell, h0⟩ ⟨gpow e, gpow kfp⟩
          (by rw [hk]; exact ⟨_, gpow e, hq, isInK_ofK _, rfl, by simp⟩)
        obtain ⟨-, hkid⟩ := H.kids
        obtain ⟨⟨rr, hrr, hrun⟩, -⟩ := hkid n _ kfp hci hkfp (by simp [h0])
        rw [hret] at hrr
        obtain rfl := Option.some.inj hrr
        have hentf : entryOf f = e := by rw [hfn, entryOf_callee hj1 hj2, hent]
        rw [hentf] at hrun
        refine ⟨cr + ck.getD n 0, by rw [← hgr]; exact hcr.trans hrun, fun op ↦ ?_, ?_⟩
        · have h2 : st'.cnt.get op ≤ (Cnt.max se.cnt st'.cnt).get op := by
            rw [Cnt.get_max]
            exact Nat.le_max_right _ _
          rw [Pi.add_apply, ksum_succ]
          have := hle' op
          omega
        · exact envAt_of_exit H hp.seg hx (by rw [hsu]; simp) henv
    obtain ⟨hpr, -⟩ := segAtC_posW H (xc := xc) hsr hok' (by rw [hrt]; exact henvR) (n := n + 1)
      (C := Cnt.max se.cnt st'.cnt) (U := setK st.uq q) (by rw [hrt]; exact hcr) hcle
      (by rw [brAtC_nm hb]; exact hp.nm)
    refine walk_step H ih rfl rfl hw hes hs hshape (by rw [hc1]; exact hpr) hcw hok
  · -- a loop's closing call
    subst hss
    have hwo' : o = .ret [Ev.inK c, ev] [] := by rw [hwo]; rfl
    rcases hshape with hsh | ⟨-, heaft, hbody⟩
    · simp [Stmt.noRetList, Stmt.noRet] at hsh
    subst heaft
    have hloop : (coreOf j).loop = true := by
      unfold Core.Fn.loop
      rw [hbody]
      simp [hf, H.name]
    have hj1' : j ≠ 1 := fun h ↦ by simp [H.main, h] at hmain
    have hj2 : 2 ≤ j := by have := H.j1; omega
    have hes3 : es = (ebef ++ [Ev.inK c]) ++ [ev] := by
      rw [hes2]
      simp [walk, walk1, Out.seq, Out.evs]
    have hlen : (calls es).length = n + 1 := by
      rw [hes3, calls_append_one (callIf_ev c f args), hn']
    have hlenk : n < kfps.length := by rw [H.frame.len, hlen]; omega
    set kfp := kfps[n] with hkfpd
    have hkfp : kfps[n]? = some kfp := List.getElem?_eq_getElem hlenk
    have hlast : kfps.getLast? = some kfp := by
      rw [List.getLast?_eq_getElem?, show kfps.length - 1 = n by rw [H.frame.len, hlen]; omega]
      exact hkfp
    have hkt := H.frame.tail hloop kfp hlast
    have hkh : kidHdr j fp hdr es n = hdr := by
      unfold kidHdr
      rw [hci]
      simp [hloop, hlen]
    obtain ⟨h0', h1', hargsK, hselfK⟩ := H.frame.kid n _ kfp hci hkfp
    rw [hkh] at h0' h1'
    have hd0 := H.frame.hdr0
    have hd1 := H.frame.hdr1
    rw [gpow_addC] at hd0 hd1 h0' h1'
    have hnx : NxOk L fp X.fs (argFC X.loc 2 args ++ [(0, .hdr 0), (1, .hdr 1)] ++
        X.self.map (fun o ↦ (o, FC.self))) := by
      intro p hp'
      rw [show fp + X.fs = kfp by rw [hkt, H.fs]]
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with (hp' | (rfl | rfl)) | ⟨o, ho, rfl⟩
      · obtain ⟨k, hk', rfl⟩ := argFC_mem hp'
        refine ⟨σ args[k], hargs k hk', ?_⟩
        have := hargsK k hk'
        rw [gpow_addC] at this
        exact this
      · exact ⟨hdr.1, hd0, h0'⟩
      · exact ⟨hdr.2, hd1, h1'⟩
      · have hm : o ∈ selfCells f := by
          rw [hf, H.name, selfCells_callee hj2 H.jn, ← H.self]
          exact ho
        have := hselfK o hm
        rw [gpow_addC] at this
        exact this
    have hpN := posZ_nx H hp hnx
    obtain ⟨hseg', -, -, -, -, -, -, hx, hok', hfall, htaken⟩ := brAtC_pos H hpN hb
    have hpk' := brAtC_peek hb
    simp only at hpk' hseg' hx
    rw [hpk] at hpk'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpk')
    obtain ⟨vd, hvd, hKd⟩ := cellK_sound H.hX hok' hod
    obtain ⟨vf, hvf, hKf⟩ := cellK_sound H.hX hok' hof
    have hjump : (Atom.jump (X.loc.cell c) od of).Holds L (gpow fp) :=
      ⟨σ c, vd, vf, hcell, hvd, hvf, hcK, hKd, hKf⟩
    have hrT : retRegs L (gpow fp) = some ⟨hdr.1.limb 0, hdr.2.limb 0⟩ :=
      retRegs_eq_some_iff.mpr ⟨_, _, hd0, hd1, rfl⟩
    obtain ⟨cr, hcr, hcle⟩ : ∃ cr, RunC guest L W0 ⟨hdr.1.limb 0, hdr.2.limb 0⟩ cr ∧
        ∀ op, cr op ≤ X.pmax.get op + xc op + ksum ck (n + 1) op := by
      by_cases h0 : σ c = 0
      · have hp' := hfall hjump (h0 ▸ hcell)
        obtain ⟨hsg, -, -, -, -, -, hr⟩ := endAtC_reach H hp' hse
        rw [hsg] at hkr
        obtain ⟨cr, hcr, hle', -⟩ := hr _ (by rw [hkr]; exact hrT)
        refine ⟨cr, hcr, fun op ↦ ?_⟩
        have := hle' op
        have h1 := Cnt.le_spec hle2 op
        have h2 := ksum_mono ck (show n ≤ n + 1 by omega) op
        omega
      · obtain ⟨cr, hcr, hle', -⟩ := htaken ⟨hjump, σ c, hcell, h0⟩ ⟨gpow e, gpow fp * gpow S⟩
          (by rw [hk]; exact ⟨_, _, rfl, rfl, rfl⟩)
        obtain ⟨-, hkid⟩ := H.kids
        obtain ⟨⟨rr, hrr, hrun⟩, -⟩ := hkid n _ kfp hci hkfp (by simp [h0])
        have hrr' : retRegs L (gpow kfp) = some ⟨hdr.1.limb 0, hdr.2.limb 0⟩ :=
          retRegs_eq_some_iff.mpr ⟨_, _, h0', h1', rfl⟩
        rw [hrr'] at hrr
        obtain rfl := Option.some.inj hrr
        have hentf : entryOf f = e := by
          rw [hf, H.name, entryOf_callee hj2 H.jn, ← H.entry, he]
        have hkf : gpow fp * gpow S = gpow kfp := by rw [hkt, hS, H.fs, gpow_addC]
        rw [hentf, ← hkf] at hrun
        refine ⟨cr + ck.getD n 0, hcr.trans hrun, fun op ↦ ?_⟩
        rw [Pi.add_apply, ksum_succ]
        have := hle' op
        have h2 := Cnt.le_spec hle1 op
        omega
    refine ⟨fun J c' u hj ↦ (by rw [hcw] at hj; cases hj), fun J m c' u hj ↦ (by rw [hcw] at hj; cases hj),
      fun _ ↦ ⟨[Ev.inK c, ev], [], hwo', ?_⟩⟩
    rw [hc1]
    unfold FinZ
    refine ⟨⟨_, cr, ?_, hcr, hcle⟩, fun k hk ↦ absurd hk (Nat.not_lt_zero _)⟩
    simp only [hj1', ↓reduceIte]
    exact hrT

/-! ## The return -/

theorem runCells_get : ∀ {base : ℕ} {cs : List ℕ}, runCells base cs = true →
    ∀ k (hk : k < cs.length), cs[k] = base + k
  | _, [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | base, c :: cs, h, k, hk => by
    simp only [runCells, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [runCells_get h.2 k (by simpa using hk)]
      omega

theorem final_guest : Regs.final guest = ⟨gpow (2 ^ 18 - 1), gpow 0⟩ := by
  simp [Regs.final, Program.finalPc, guest_logSize]

theorem walk_retZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) (vs' : List V)
    (ss : List Stmt) (st : CW) : WGood H (.ret vs' :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨se, hse, hkind, hle, hlen, hrun, hin, hcw⟩ := cw_ret hok
  have hwo : o = .ret [] vs' := by
    rw [← hw, walk]
    rfl
  refine ⟨fun J c u hj ↦ (by rw [hcw] at hj; cases hj), fun J m c u hj ↦ (by rw [hcw] at hj; cases hj),
    fun _ ↦ ⟨[], vs', hwo, ?_⟩⟩
  obtain ⟨hsg, -, -, -, -, -, hr⟩ := endAtC_reach H hp hse
  rw [hsg] at hkind
  have hd0 := H.frame.hdr0
  have hd1 := H.frame.hdr1
  rw [gpow_addC] at hd0 hd1
  have hrT : retRegs L (gpow fp) = some ⟨hdr.1.limb 0, hdr.2.limb 0⟩ :=
    retRegs_eq_some_iff.mpr ⟨_, _, hd0, hd1, rfl⟩
  obtain ⟨r, hrg, hregs⟩ : ∃ r, (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
      st.seg.exit.kind.Regs L (gpow fp) X.entry r := by
    by_cases hj1 : j = 1
    · have hm : X.main = true := by rw [H.main, hj1]; rfl
      simp only [hm, ↓reduceIte] at hkind
      refine ⟨_, by simp only [hj1, ↓reduceIte]; exact final_guest, ?_⟩
      rw [hkind]
      exact ⟨_, _, rfl, rfl, rfl⟩
    · have hm : X.main = false := by rw [H.main]; simpa using hj1
      simp only [hm, Bool.false_eq_true, ↓reduceIte] at hkind
      refine ⟨_, by simp only [hj1, ↓reduceIte]; exact hrT, ?_⟩
      rw [hkind]
      exact hrT
  obtain ⟨cr, hcr, hcle, -⟩ := hr r hregs
  rw [List.append_nil]
  refine ⟨⟨r, cr, hrg, hcr, fun op ↦ ?_⟩, fun k hk ↦ ?_⟩
  · have h1 := hcle op
    have h2 := Cnt.le_spec hle op
    simp only [Pi.add_apply] at h1 ⊢
    omega
  have hk' : k < (vs'.map X.loc.cell).length := by simpa using hk
  have hc := runCells_get hrun k hk'
  have hf := inFrame_mem hin _ (List.getElem_mem hk')
  simp only [List.getElem_map] at hc hf
  exact ⟨hc, hf.1, hf.2⟩

end Walk








end
end LeanVM.Guest.B2C
