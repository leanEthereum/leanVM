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
  fresh : ∀ t, st.fresh = some t → st.seg.start = t ∧ st.its = st.seg.items

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
    exact ⟨hst, rfl⟩

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

end Walk


end
end LeanVM.Guest.B2C
