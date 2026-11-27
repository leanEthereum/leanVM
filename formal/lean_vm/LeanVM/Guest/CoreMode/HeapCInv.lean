/-
  LeanVM.Guest.CoreMode.HeapCInv

  The heap check's soundness: the pass's invariant, kept by each step of the pass.
-/

module

public import LeanVM.Guest.CoreMode.HeapCRun

/-!
# The pass's invariant

`StOk rd W σ st`: the environment's monomials are the values' words, the scope's cells and runs written in `W`, the runs' exponents existing; each step of the pass (`chkC`'s) keeps it, and a witness of a cell or a run gives it written (`ptOk_ok`, `rnOk_ok`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq natSeq_eq)
open LeanVM.Guest.Check (getF setF getF_eq setF_eq)

@[expose] public section

/-! ## The pass's invariant -/

section Inv

variable {σ : Val} {rd : Reader} {W W' : K → Prop}

/-- **The run scope is written**: each run's cells are in `W`. -/
def RsOk (W : K → Prop) (σ : Val) (rs : Trie PRun) : Prop :=
  ∀ r R, getF rs r = some R → RunF W (vw σ) R.base R.stride R.lo R.hi

/-- **The sums seen hold**: each value the sum of its operands' monomials' words. -/
def AdOk (σ : Val) (ad : Trie (CCell × CCell)) : Prop :=
  ∀ k p, getF ad k = some p → σ (V.n k) = p.1.valW (vw σ) + p.2.valW (vw σ)

/-- **The words stored are in memory**: each load event's word, at its cell. -/
def SvOk (rd : Reader) (σ : Val) (sv : Trie (CCell × CCell)) : Prop :=
  ∀ n p, getF sv n = some p → rd (p.1.addr σ) = some (p.2.valW (vw σ))

/-- **The values loaded are in memory**: each value's word at the cell it was loaded from. -/
def SrcOk (rd : Reader) (σ : Val) (src : Trie CCell) : Prop :=
  ∀ k c, getF src k = some c → rd (c.addr σ) = some (σ (V.n k))

/-- **The pointer facts in scope are written**: past the word at each fact's cell. -/
def PfOk (rd : Reader) (W : K → Prop) (σ : Val) (pf : Trie (CCell × List ℕ)) : Prop :=
  ∀ n p, getF pf n = some p → ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W x

/-- **The pointer runs in scope are written**: past the word at each cell of each run. -/
def PrOk (rd : Reader) (W : K → Prop) (σ : Val) (pr : Trie (PRun × List ℕ)) : Prop :=
  ∀ n p, getF pr n = some p → ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W x

/-- **A dispatch arm's guarantees hold**: written. -/
def CdAOk (rd : Reader) (W : K → Prop) (σ : Val) (e : CdA) : Prop :=
  (∀ c ∈ e.cs, W (c.addr σ)) ∧ (∀ q ∈ e.rs, RunF W (vw σ) q.base q.stride q.lo q.hi) ∧
    (∀ p ∈ e.ps, ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W x) ∧
    ∀ p ∈ e.prs, ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W x

/-- **The guarantees under selectors hold**: a dispatch's arm `j`'s where the selector's word is `g^j`. -/
def CdOk (rd : Reader) (W : K → Prop) (σ : Val) (cd : List CdE) : Prop :=
  ∀ e ∈ cd, ∀ j a, nth e.arms j = some a → e.mx.valW (vw σ) = ofK (addressOfIndex j) → CdAOk rd W σ a

theorem CdOk.mono (hw : ∀ x, W x → W' x) {cd : List CdE} (h : CdOk rd W σ cd) : CdOk rd W' σ cd :=
  fun e he j a ha hj ↦ let ⟨h1, h2, h3, h4⟩ := h e he j a ha hj
    ⟨fun c hc ↦ hw _ (h1 c hc), fun q hq ↦ (h2 q hq).mono hw, fun p hp x hx ↦ hw _ (h3 p hp x hx),
      fun p hp a ha x hx ↦ hw _ (h4 p hp a ha x hx)⟩

/-- **The equations hold**: each one's sides one word. -/
def EqsOk (σ : Val) (E : List (CCell × CCell)) : Prop := ∀ p ∈ E, p.1.valW (vw σ) = p.2.valW (vw σ)

/-- **The runs at words are written**: at each cell holding a word, the run at that word. -/
def DqOk (rd : Reader) (W : K → Prop) (σ : Val) (dq : List (CCell × PRun)) : Prop :=
  ∀ p ∈ dq, ∀ w, rd (p.1.addr σ) = some w → ∀ x, RunSetB (vw σ) w p.2.base p.2.stride p.2.lo p.2.hi x → W x

/-- **The state is valid**: its monomials, its written cells and runs, its sums, its stored words,
the cells its values were loaded from, its pointer facts and runs, its guarantees under selectors. -/
structure StOk (rd : Reader) (W : K → Prop) (σ : Val) (st : CSt) : Prop where
  env : EnvOk σ st.env
  sc : ScOk W σ st.sc
  rs : RsOk W σ st.rs
  ad : AdOk σ st.ad
  sv : SvOk rd σ st.sv
  src : SrcOk rd σ st.src
  pf : PfOk rd W σ st.pf
  pr : PrOk rd W σ st.pr
  cd : CdOk rd W σ st.cd
  eqs : EqsOk σ st.eqs
  dq : DqOk rd W σ st.dq

theorem StOk.mono (hw : ∀ x, W x → W' x) {st : CSt} (h : StOk rd W σ st) : StOk rd W' σ st :=
  ⟨h.env, h.sc.mono hw, fun r R hr ↦ (h.rs r R hr).mono hw, h.ad, h.sv, h.src,
    fun n p hp x hx ↦ hw _ (h.pf n p hp x hx), fun n p hp a ha x hx ↦ hw _ (h.pr n p hp a ha x hx),
    h.cd.mono hw, h.eqs, fun p hp w hw' x hx ↦ hw _ (h.dq p hp w hw' x hx)⟩

theorem StOk.cnt {st : CSt} (h : StOk rd W σ st) (s : CSt) : StOk rd W σ (st.cnt s) :=
  ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩

theorem StOk.nextC {st : CSt} (h : StOk rd W σ st) : StOk rd W σ st.nextC :=
  ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩

theorem push_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {c : CCell} (hc : W' (c.addr σ)) :
    StOk rd W' σ (st.push c) := by
  have hs' := hs.mono hw
  obtain ⟨h1, h2⟩ := push_ok (W := W') (st := st.toH) hs'.sc hc
  exact ⟨by rw [CSt.push, CSt.ofH]; exact h1 ▸ hs.env, h2, hs'.rs, hs.ad, hs.sv, hs.src, hs'.pf, hs'.pr, hs'.cd, hs.eqs, hs'.dq⟩

theorem def_stOk {st : CSt} (hs : StOk rd W σ st) {k : ℕ} {c : CCell} (hc : σ (V.n k) = c.val σ) :
    StOk rd W σ (st.def k c) :=
  ⟨(def_ok (st := st.toH) hs.env hc).1, hs.sc, hs.rs, hs.ad, hs.sv, hs.src, hs.pf, hs.pr, hs.cd, hs.eqs, hs.dq⟩

theorem pushV_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {c m : CCell} (hc : W' (c.addr σ))
    (hm : rd (c.addr σ) = some (m.valW (vw σ))) : StOk rd W' σ (st.pushV c m) := by
  unfold CSt.pushV
  rw [CCell.seq_eq, Trie.seq_eq, CSt.seq_eq]
  have h := push_stOk hs hw hc
  refine ⟨h.env, h.sc, h.rs, h.ad, fun n p hp ↦ ?_, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩
  change getF (setF (c, m) Exec.indexDepth st.sv st.n) n = some p at hp
  rcases Check.getF_setF hp with ⟨-, rfl⟩ | hp
  · exact hm
  · exact hs.sv n p hp

theorem srcPut_stOk {st : CSt} (hs : StOk rd W σ st) {d : V} {c : CCell} (hd : rd (c.addr σ) = some (σ d)) :
    StOk rd W σ (st.srcPut d c) := by
  unfold CSt.srcPut
  cases hk : vnum d with
  | none => exact hs
  | some k =>
    dsimp only
    cases hc : getF st.src k with
    | some _ => exact hs
    | none =>
      dsimp only
      rw [Trie.seq_eq]
      refine ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, fun k' c' hk' ↦ ?_, hs.pf, hs.pr, hs.cd, hs.eqs, hs.dq⟩
      change getF (setF c Exec.indexDepth st.src k) k' = some c' at hk'
      rcases Check.getF_setF hk' with ⟨rfl, rfl⟩ | hk'
      · rw [hd, vnum_eq hk]
      · exact hs.src k' c' hk'

theorem pushP_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {p : CCell × List ℕ}
    (hp : ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W' x) : StOk rd W' σ (st.pushP p) := by
  unfold CSt.pushP
  rw [CCell.seq_eq, Trie.seq_eq]
  have h := hs.mono hw
  refine ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, fun n q hq ↦ ?_, h.pr, h.cd, h.eqs, h.dq⟩
  change getF (setF (p.1, p.2) Exec.indexDepth st.pf st.n) n = some q at hq
  rcases Check.getF_setF hq with ⟨-, rfl⟩ | hq
  · exact hp
  · exact h.pf n q hq

theorem pushPR_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {p : PRun × List ℕ}
    (hp : ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W' x) :
    StOk rd W' σ (st.pushPR p) := by
  unfold CSt.pushPR
  rw [PRun.seq_eq, Trie.seq_eq]
  have h := hs.mono hw
  refine ⟨h.env, h.sc, h.rs, h.ad, h.sv, h.src, h.pf, fun n q hq ↦ ?_, h.cd, h.eqs, h.dq⟩
  change getF (setF (p.1, p.2) Exec.indexDepth st.pr st.nr) n = some q at hq
  rcases Check.getF_setF hq with ⟨-, rfl⟩ | hq
  · exact hp
  · exact h.pr n q hq

theorem pushPL_ok : ∀ {W W' : K → Prop} {ps : List (CCell × List ℕ)} {st : CSt}, StOk rd W σ st →
    (∀ x, W x → W' x) → (∀ p ∈ ps, ∀ x, PtrSet rd (p.1.addr σ) p.2 x → W' x) → StOk rd W' σ (pushPL ps st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, p :: ps, st, hs, hw, hp => by
    rw [pushPL, CSt.seq_eq]
    exact pushPL_ok (pushP_stOk hs hw (hp p List.mem_cons_self)) (fun _ h ↦ h)
      fun p' h ↦ hp p' (List.mem_cons_of_mem _ h)

theorem pushPRL_ok : ∀ {W W' : K → Prop} {ps : List (PRun × List ℕ)} {st : CSt}, StOk rd W σ st →
    (∀ x, W x → W' x) →
    (∀ p ∈ ps, ∀ a, RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a → ∀ x, PtrSet rd a p.2 x → W' x) →
    StOk rd W' σ (pushPRL ps st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, p :: ps, st, hs, hw, hp => by
    rw [pushPRL, CSt.seq_eq]
    exact pushPRL_ok (pushPR_stOk hs hw (hp p List.mem_cons_self)) (fun _ h ↦ h)
      fun p' h ↦ hp p' (List.mem_cons_of_mem _ h)

theorem pushL_ok : ∀ {W W' : K → Prop} {cs : List CCell} {st : CSt}, StOk rd W σ st → (∀ x, W x → W' x) →
    (∀ c ∈ cs, W' (c.addr σ)) → StOk rd W' σ (pushL cs st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, c :: cs, st, hs, hw, hc => by
    rw [pushL, CCell.seq_eq, CSt.seq_eq]
    exact pushL_ok (push_stOk hs hw (hc c List.mem_cons_self)) (fun _ h ↦ h)
      fun c' h ↦ hc c' (List.mem_cons_of_mem _ h)

theorem pushR_stOk {st : CSt} (hs : StOk rd W σ st) (hw : ∀ x, W x → W' x) {q : PRun}
    (hq : RunF W' (vw σ) q.base q.stride q.lo q.hi) : StOk rd W' σ (st.pushR q) := by
  have h := hs.mono hw
  unfold CSt.pushR
  rw [Trie.seq_eq]
  refine ⟨h.env, h.sc, fun r R hr ↦ ?_, h.ad, h.sv, h.src, h.pf, h.pr, h.cd, h.eqs, h.dq⟩
  change getF (setF q Exec.indexDepth st.rs st.nr) r = some R at hr
  rcases Check.getF_setF hr with ⟨-, rfl⟩ | hr
  · exact hq
  · exact h.rs r R hr

theorem pushRL_ok : ∀ {W W' : K → Prop} {qs : List PRun} {st : CSt}, StOk rd W σ st → (∀ x, W x → W' x) →
    (∀ q ∈ qs, RunF W' (vw σ) q.base q.stride q.lo q.hi) → StOk rd W' σ (pushRL qs st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, q :: qs, st, hs, hw, hq => by
    rw [pushRL, PRun.seq_eq, CSt.seq_eq]
    exact pushRL_ok (pushR_stOk hs hw (hq q List.mem_cons_self)) (fun _ h ↦ h)
      fun q' h ↦ hq q' (List.mem_cons_of_mem _ h)

/-- **What the pass reads, valid**: `heapOk`'s, the signatures, the parameters, the residuals,
and the facts true at the instance. -/
structure XOk (sigOf : String → HSig) (H : HCert) (rd : Reader) (f : Fn) (σ : Val) (X : CX) : Prop where
  R : X.R = H.readT
  pre : ∀ k c, getF X.pre k = some c → c ∈ H.sig.pre
  pows : X.pows.Ok
  sigOf : X.sigOf = sigOf
  ga : X.ga = H.gargs
  sig : X.sig = H.sig
  params : X.params = f.params
  res : ∀ i c, getF X.res i = some c → c ∈ H.res
  term : ∀ p ∈ H.sig.term, LtF (vw σ) (idxC p.1) (idxC p.2)
  resF : ResF H σ
  path : ∀ c ∈ X.path, c.Holds σ
  fas : X.fas = H.fas
  ders : X.ders = H.ders
  der : DerOk H rd σ
  gw : GwOk H.sig rd σ

/-- The site under further branch conditions that hold. -/
theorem XOk.ext {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X) {l : List CCond}
    (hl : ∀ c ∈ l, c.Holds σ) : XOk sigOf H rd f σ (X.ext l) :=
  ⟨hX.R, hX.pre, hX.pows, hX.sigOf, hX.ga, hX.sig, hX.params, hX.res, hX.term, hX.resF,
    fun c hc ↦ (List.mem_append.mp hc).elim (hl c) (hX.path c), hX.fas, hX.ders, hX.der, hX.gw⟩

theorem CCond.beq_eq : ∀ {a b : CCond}, CCond.beq a b = true → a = b
  | .arm x j, .arm x' j', h => by
    simp only [CCond.beq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2]
  | .zero c, .zero c', h => by rw [Nat.eq_of_beq_eq_true h]
  | .nonzero c, .nonzero c', h => by rw [Nat.eq_of_beq_eq_true h]
  | .arm .., .zero _, h | .arm .., .nonzero _, h | .zero _, .arm .., h | .zero _, .nonzero _, h
  | .nonzero _, .arm .., h | .nonzero _, .zero _, h => by simp [CCond.beq] at h

theorem onPath_ok {path g : List CCond} (h : onPath path g = true) (hp : ∀ c ∈ path, c.Holds σ) :
    ∀ c ∈ g, c.Holds σ := fun c hc ↦ by
  obtain ⟨c', hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h c hc)
  rw [CCond.beq_eq he]
  exact hp c' hc'

theorem unU_ok {path : List CCond} (hp : ∀ c ∈ path, c.Holds σ) : ∀ {r0 r : CRes}, unU path r0 = some r →
    r0.Holds σ → r.Holds σ
  | .under g r0, r, h, h0 => by
    simp only [unU] at h
    cases hb : onPath path g with
    | false => rw [hb] at h; cases h
    | true => rw [hb, Bool.cond_true] at h; exact unU_ok hp h (h0 (onPath_ok hb hp))
  | .lt .., _, h, h0 | .nz _, _, h, h0 | .sub .., _, h, h0 | .subR .., _, h, h0 | .subP .., _, h, h0 => by
    simp only [unU, Option.some.injEq] at h
    subst h
    exact h0

/-- **A residual at the site holds.** -/
theorem resAt_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X) {i : ℕ}
    {r : CRes} (h : resAt X i = some r) : r.Holds σ := by
  unfold resAt at h
  cases hg : getF X.res i with
  | none => rw [hg] at h; cases h
  | some r0 => rw [hg] at h; exact unU_ok hX.path h (hX.resF r0 (hX.res i r0 hg))

theorem czero_ok {c : V} (h : σ c = 0) : ∀ d ∈ czero c, d.Holds σ := fun d hd ↦ by
  unfold czero at hd
  cases hk : vnum c with
  | none => rw [hk] at hd; cases hd
  | some k => rw [hk] at hd; rw [List.mem_singleton.mp hd]; show σ (V.n k) = 0; rw [← vnum_eq hk]; exact h

theorem cnz_ok {c : V} (h : σ c ≠ 0) : ∀ d ∈ cnz c, d.Holds σ := fun d hd ↦ by
  unfold cnz at hd
  cases hk : vnum c with
  | none => rw [hk] at hd; cases hd
  | some k => rw [hk] at hd; rw [List.mem_singleton.mp hd]; show σ (V.n k) ≠ 0; rw [← vnum_eq hk]; exact h

theorem carm_ok {x : V} {j : ℕ} (h : σ x = ofK (addressOfIndex j)) : ∀ d ∈ carm x j, d.Holds σ := fun d hd ↦ by
  unfold carm at hd
  cases hk : vnum x with
  | none => rw [hk] at hd; cases hd
  | some k =>
    rw [hk] at hd; rw [List.mem_singleton.mp hd]; show σ (V.n k) = _; rw [← vnum_eq hk]; exact h

theorem idxF_val {env : Trie CCell} (he : EnvOk σ env) (i : CIdx) : (idxF env i).valW (vw σ) = (idxC i).valW (vw σ) := by
  cases i with
  | num n => rfl
  | val k =>
    rw [idxC, valW_baseC, idxF]
    cases hk : getF env k with
    | none => rw [Option.getD_none, valW_baseC]
    | some c => rw [Option.getD_some, ← val_eq, ← he k c hk]; rfl
  | mono c => rfl

theorem ltF_congr {w w' : ℕ → E} {a a' b b' : CCell} (ha : a.valW w = a'.valW w') (hb : b.valW w = b'.valW w') :
    LtF w a b ↔ LtF w' a' b' := by
  simp only [LtF, ha, hb]

theorem expFacts_ok {w : ℕ → E} {m : CCell} {e : ℕ} (hm : m.valW w = ofK (addressOfIndex e)) :
    FOk w (expFacts m e) := by
  unfold expFacts
  cases hb : Nat.blt (e + 1) capE with
  | false => intro p hp; simp at hp
  | true =>
    have he := Nat.blt_eq.mp hb
    have hr : rep (m.valW w) = some e := by rw [hm]; exact rep_of (by omega)
    rw [Bool.cond_true]
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · cases h0 : Nat.beq e 0 with
      | true => rw [h0] at hp; cases hp
      | false =>
        rw [h0] at hp
        rw [List.mem_singleton.mp hp]
        have := Nat.ne_of_beq_eq_false h0
        exact ⟨e - 1, e, rep_const (by omega), hr, by omega⟩
    · rw [List.mem_singleton.mp hp]
      exact ⟨e, e + 1, hr, rep_const he, by omega⟩

theorem baseFacts_ok {w : ℕ → E} {m : CCell} {j : ℕ} (hm : m.valW w = ofK (addressOfIndex j)) :
    FOk w (baseFacts m j) := by
  obtain ⟨bs, t⟩ := m
  unfold baseFacts
  dsimp only
  split
  · rename_i _ b
    cases hle : Nat.ble t j with
    | false => intro p hp; simp at hp
    | true =>
      rw [Bool.cond_true]
      have hle := Nat.le_of_ble_eq_true hle
      refine expFacts_ok ?_
      have hne : ofK (addressOfIndex t) ≠ 0 := fun h ↦
        pow_ne_zero t g_ne_zero (ofK_injective (h.trans (map_zero (algebraMap K E)).symm))
      refine mul_right_cancel₀ hne ?_
      rw [valW_baseC]
      have : w b * ofK (addressOfIndex t) = (⟨[(b, 1)], t⟩ : CCell).valW w := by
        simp [CCell.valW, prodW]
      rw [this, hm, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, Nat.sub_add_cancel hle]
  · intro p hp; simp at hp

/-- **A path's facts hold** where its conditions do. -/
theorem pathF_ok {env : Trie CCell} (he : EnvOk σ env) : ∀ {path : List CCond}, (∀ c ∈ path, c.Holds σ) →
    FOk (vw σ) (pathF env path)
  | [], _ => fun p hp ↦ by simp [pathF] at hp
  | .zero _ :: l, hp => by
    simp only [pathF]; exact pathF_ok he fun c hc ↦ hp c (List.mem_cons_of_mem _ hc)
  | .nonzero _ :: l, hp => by
    simp only [pathF]; exact pathF_ok he fun c hc ↦ hp c (List.mem_cons_of_mem _ hc)
  | .arm x j :: l, hp => by
    have hl := pathF_ok he fun c hc ↦ hp c (List.mem_cons_of_mem _ hc)
    have hx : (idxF env (.val x)).valW (vw σ) = ofK (addressOfIndex j) := by
      rw [idxF_val he, idxC, valW_baseC]; exact hp _ List.mem_cons_self
    simp only [pathF]
    intro p hp'
    rcases List.mem_append.mp hp' with hp' | hp'
    rcases List.mem_append.mp hp' with hp' | hp'
    · exact expFacts_ok hx p hp'
    · exact baseFacts_ok hx p hp'
    · exact hl p hp'

theorem facts_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    {env : Trie CCell} (he : EnvOk σ env) (res : List ℕ) : FOk (vw σ) (facts X env res) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [hX.sig] at hq
    exact (ltF_congr (idxF_val he _) (idxF_val he _)).mpr (hX.term q hq)
  · obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hp
    cases hr : resAt X i with
    | none => rw [hr] at hi; cases hi
    | some c =>
      rw [hr] at hi
      cases c with
      | lt a b =>
        cases hi
        exact (ltF_congr (idxF_val he _) (idxF_val he _)).mpr (resAt_ok hX hr)
      | nz => cases hi
      | sub => cases hi
      | subR => cases hi
      | under => cases hi
      | subP => cases hi
  · exact pathF_ok he hX.path p hp

theorem PRun.beq_eq {a b : PRun} (h : a.beq b = true) : a = b := by
  unfold PRun.beq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h
  obtain ⟨b1, s1, l1, h1⟩ := a
  obtain ⟨b2, s2, l2, h2⟩ := b
  simp only at e1 e2 e3 e4
  rw [CCell.beq_eq e1, Nat.eq_of_beq_eq_true e2, CCell.beq_eq e3, CCell.beq_eq e4]

theorem runF_set {env : Trie CCell} (he : EnvOk σ env) (r : CRun) {x : K} :
    RunSet (vw σ) (runF env r).base (runF env r).stride (runF env r).lo (runF env r).hi x ↔ r.Set (vw σ) x :=
  runSet_congr rfl (idxF_val he _) (idxF_val he _)

/-- **A residual placing a cell in a written run**: the cell written. -/
theorem subPt_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    {env : Trie CCell} (he : EnvOk σ env) {F : List (CCell × CCell)} (hF : FOk (vw σ) F) {res : List ℕ}
    {R : PRun} {c : CCell} (hR : RunF W (vw σ) R.base R.stride R.lo R.hi) (h : subPt X F env res R c = true) :
    W (c.addr σ) := by
  obtain ⟨i, -, hb⟩ := List.any_eq_true.mp h
  split at hb
  · rename_i c' r' hi
    simp only [Bool.and_eq_true] at hb
    rw [← PRun.beq_eq hb.2] at hR
    rw [addr_eq, ← CCell.beq_eq hb.1]
    exact hR _ ((runF_set he r').mpr (resAt_ok (r := .sub c' r') hX hi))
  · rename_i q r' hi
    simp only [Bool.and_eq_true] at hb
    rw [← PRun.beq_eq hb.1] at hR
    have hq := ptRun_ok (W := fun x ↦ RunSet (vw σ) (runF env q).base (runF env q).stride (runF env q).lo
      (runF env q).hi x) hF (fun _ hx ↦ hx) hb.2
    rw [addr_eq]
    exact hR _ ((runF_set he r').mpr (resAt_ok (r := .subR q r') hX hi _ ((runF_set he q).mp hq)))
  · cases hb

/-- **A residual placing a run in a written run**: the run written. -/
theorem subRun_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    {env : Trie CCell} (he : EnvOk σ env) {res : List ℕ} {Q R : PRun}
    (hR : RunF W (vw σ) R.base R.stride R.lo R.hi) (h : subRun X env res Q R = true) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  obtain ⟨i, -, hb⟩ := List.any_eq_true.mp h
  split at hb
  · rename_i q r' hi
    simp only [Bool.and_eq_true] at hb
    rw [← PRun.beq_eq hb.1]
    rw [← PRun.beq_eq hb.2] at hR
    exact fun x hx ↦ hR _ ((runF_set he r').mpr (resAt_ok (r := .subR q r') hX hi _ ((runF_set he q).mp hx)))
  · cases hb

/-- The cell the word under a cell was loaded from: that word at it. -/
theorem srcOf_ok {st : CSt} (hs : StOk rd W σ st) {c a : CCell} (h : srcOf st c = some a) :
    ∃ w, rd (a.addr σ) = some w ∧ c.addr σ = w.limb 0 * addressOfIndex c.off := by
  obtain ⟨bs, o⟩ := c
  unfold srcOf at h
  split at h
  · rename_i b e hb
    simp only at hb
    subst hb
    cases he : Nat.beq e 1 with
    | false => rw [he] at h; cases h
    | true =>
      rw [he, Bool.cond_true] at h
      have he1 := Nat.eq_of_beq_eq_true he
      subst he1
      refine ⟨σ (V.n b), hs.src b a h, ?_⟩
      simp only [CCell.addr, CCell.val, prodB, pow_one, mul_one, limb0_mul_ofK]
  · cases h

/-- A run with constant bounds, the upper at most the lower: no cell. -/
theorem emptyR_ok {w : ℕ → E} {Q : PRun} (h : emptyR Q = true) {x : K} :
    ¬ RunSet w Q.base Q.stride Q.lo Q.hi x := by
  unfold emptyR at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hl, hh⟩, hle⟩, hlc⟩ := h
  have hle := Nat.le_of_ble_eq_true hle
  have hlc := Nat.blt_eq.mp hlc
  rintro ⟨ylo, yhi, j, h1, h2, h3, h4, -⟩
  rw [rep_nil hl hlc, Option.some.injEq] at h1
  rw [rep_nil hh (by omega), Option.some.injEq] at h2
  omega

/-- A run with no cell (`emptyE`), the kept equations holding. -/
theorem emptyE_ok {w : ℕ → E} {L : List (CCell × CCell)} (hE : ∀ p ∈ L, p.1.valW w = p.2.valW w) {Q : PRun}
    (h : emptyE L Q = true) {x : K} : ¬ RunSet w Q.base Q.stride Q.lo Q.hi x := by
  unfold emptyE at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact emptyR_ok h
  · rintro ⟨ylo, yhi, j, h1, h2, h3, h4, -⟩
    rw [← eqV_ok hE h, h2, Option.some.injEq] at h1
    omega

theorem ptrSet_sub {a : K} {offs o : List ℕ} (h : subL offs o = true) {x : K} (hx : PtrSet rd a offs x) :
    PtrSet rd a o x := by
  obtain ⟨w, hw, o', ho', rfl⟩ := hx
  obtain ⟨o'', ho'', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h o' ho')
  exact ⟨w, hw, o'', ho'', by rw [Nat.eq_of_beq_eq_true he]⟩

theorem permW_ok {st : CSt} (hs : StOk rd W σ st) : ∀ {cs : List CCell} {ns : List ℕ}, permW st cs ns = true →
    ∀ c ∈ cs, W (c.addr σ)
  | [], [], _, c, hc => by simp at hc
  | c :: cs, n :: ns, h, c0, hc0 => by
    simp only [permW, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hc0 with rfl | hc0
    · cases hn : getF st.sc n with
      | none => rw [hn] at h1; cases h1
      | some c' => rw [hn] at h1; rw [← CCell.beq_eq h1]; exact hs.sc n c' hn
    · exact permW_ok hs h2 c0 hc0
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => by simp [permW] at h

theorem evsW_ok {st : CSt} (hs : StOk rd W σ st) {Q : CCell} {n : ℕ} :
    ∀ {k : ℕ}, evsW st Q n k = true → ∀ t < k, W ((Q.shift t).addr σ)
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | k + 1, h, t, ht => by
    simp only [evsW, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · exact evsW_ok hs h.1 t ht
    · cases hn : getF st.sc (n + t) with
      | none => rw [hn] at h; exact absurd h.2 (by simp)
      | some c' => rw [hn] at h; rw [← CCell.beq_eq h.2]; exact hs.sc _ c' hn

/-- **The run of consecutive write events** written. -/
theorem evs_run {st : CSt} (hs : StOk rd W σ st) {Q : CCell} {n k : ℕ} (h : evsW st Q n k = true)
    (hk : k < capE) : RunF W (vw σ) (evsR Q k).base (evsR Q k).stride (evsR Q k).lo (evsR Q k).hi := by
  rintro x ⟨ylo, yhi, j, -, hhi, -, h2, hx⟩
  rw [show (evsR Q k).hi = ⟨[], k⟩ from rfl, rep_const hk, Option.some.injEq] at hhi
  have := evsW_ok hs h j (by omega)
  rw [addr_eq, CCell.addrW, valW_shift] at this
  rw [hx, show (evsR Q k).base = Q from rfl, show (evsR Q k).stride = 1 from rfl, one_mul]
  exact this

theorem backW_ok {st : CSt} (hs : StOk rd W σ st) {R : PRun} {k : ℕ} :
    ∀ {y0 : ℕ} {ns : List ℕ}, backW st R k y0 ns = true → ∀ i < ns.length,
      R.stride * k ≤ R.base.off + R.stride * (y0 + i) ∧
        W ((⟨R.base.bases, R.base.off + R.stride * (y0 + i) - R.stride * k⟩ : CCell).addr σ)
  | _, [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | y0, n :: ns, h, i, hi => by
    simp only [backW, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases i with
    | zero =>
      refine ⟨by simpa using h1, ?_⟩
      cases hn : getF st.sc n with
      | none => rw [hn] at h2; cases h2
      | some c' => rw [hn] at h2; rw [Nat.add_zero, ← CCell.beq_eq h2]; exact hs.sc n c' hn
    | succ i =>
      have := backW_ok hs h3 i (by simp only [List.length_cons] at hi; omega)
      rwa [show y0 + 1 + i = y0 + (i + 1) by omega] at this

/-- **A cell some indices below a run's upper bound**: in the run, or one of the write events. -/
theorem back_ok {st : CSt} (hs : StOk rd W σ st) {F : List (CCell × CCell)} (hF : FOk (vw σ) F) {R : PRun}
    (hR : RunF W (vw σ) R.base R.stride R.lo R.hi) {c : CCell} {ns : List ℕ} (h : backC F R c ns = true)
    (hw : backW st R (backK R c) 0 ns = true) : W (c.addr σ) := by
  unfold backC at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨hk, hc⟩, hlb⟩, hlc⟩, hex⟩, hlen⟩ := h
  have hlen := Nat.eq_of_beq_eq_true hlen
  set k := backK R c
  obtain ⟨yh, hyh⟩ := hasExp_ok hF hex
  have hhv := (rep_spec hyh).2
  have hcv : c.valW (vw σ) * ofK (addressOfIndex (R.stride * k)) =
      R.base.valW (vw σ) * ofK (addressOfIndex (R.stride * yh)) := by
    rw [← valW_shift, CCell.beq_eq hc, valW_mul, valW_pow, hhv, ← ofK_pow, addressOfIndex, addressOfIndex,
      ← pow_mul, mul_comm yh]
  have hne := ofK_gpow_ne_zero (R.stride * k)
  rcases Nat.lt_or_ge yh (R.lo.off + k) with hlt | hge
  · obtain ⟨hle, hW⟩ := backW_ok hs hw yh (by omega)
    rw [Nat.zero_add] at hle hW
    have hv : c.valW (vw σ) =
        (⟨R.base.bases, R.base.off + R.stride * yh - R.stride * k⟩ : CCell).valW (vw σ) := by
      refine mul_right_cancel₀ hne ?_
      rw [hcv]
      simp only [CCell.valW, mul_assoc, ← ofK_mul, addressOfIndex, ← pow_add]
      rw [Nat.sub_add_cancel hle]
    rw [addr_eq, CCell.addrW, hv, ← CCell.addrW, ← addr_eq]
    exact hW
  · rw [addr_eq]
    refine hR _ ⟨R.lo.off, yh, yh - k, rep_nil hlb hlc, hyh, by omega, by omega, ?_⟩
    have hv : c.valW (vw σ) = R.base.valW (vw σ) * ofK (addressOfIndex (R.stride * (yh - k))) := by
      refine mul_right_cancel₀ hne ?_
      rw [hcv, mul_assoc, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, ← Nat.mul_add,
        Nat.sub_add_cancel (by omega : k ≤ yh)]
    rw [CCell.addrW, hv]

/-- **A cell's witness**: the cell written. -/
theorem ptOk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {c : CCell} {w : Wit}
    (h : ptOk X st c w = true) : W (c.addr σ) := by
  induction w generalizing c with
  | ev n =>
    simp only [ptOk] at h
    cases hn : getF st.sc n with
    | none => rw [hn] at h; cases h
    | some c' => rw [hn] at h; rw [← CCell.beq_eq h]; exact hs.sc n c' hn
  | pre k =>
    simp only [ptOk] at h
    cases hk : getF X.pre k with
    | none => rw [hk] at h; cases h
    | some c' => rw [hk] at h; rw [← CCell.beq_eq h]; exact hpre c' (hX.pre k c' hk)
  | run r res =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · rw [addr_eq]
        exact ptRun_ok (facts_ok hX hs.env res) (hs.rs r R hr) h
      · exact subPt_ok hX hs.env (facts_ok hX hs.env res) (hs.rs r R hr) h
  | pf n =>
    simp only [ptOk] at h
    cases hn : getF st.pf n with
    | none => simp [hn] at h
    | some p =>
      cases ha : srcOf st c with
      | none => simp [hn, ha] at h
      | some a =>
        simp only [hn, ha, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨w, hw, hc⟩ := srcOf_ok hs ha
        obtain ⟨o, ho, ho'⟩ := List.any_eq_true.mp h2
        refine hs.pf n p hn _ ⟨w, ?_, o, ho, ?_⟩
        · rw [← CCell.beq_eq h1]; exact hw
        · rw [hc, Nat.eq_of_beq_eq_true ho']
  | pfr r res =>
    simp only [ptOk] at h
    cases hr : getF st.pr r with
    | none => simp [hr] at h
    | some p =>
      cases ha : srcOf st c with
      | none => simp [hr, ha] at h
      | some a =>
        simp only [hr, ha, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨w, hw, hc⟩ := srcOf_ok hs ha
        obtain ⟨o, ho, ho'⟩ := List.any_eq_true.mp h2
        have hR := ptRun_ok (W := fun x ↦ RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi x)
          (facts_ok hX hs.env res) (fun _ hx ↦ hx) h1
        rw [← addr_eq] at hR
        refine hs.pr r p hr _ hR _ ⟨w, hw, o, ho, ?_⟩
        rw [hc, Nat.eq_of_beq_eq_true ho']
  | res => simp [ptOk] at h
  | word => simp [ptOk] at h
  | pts => simp [ptOk] at h
  | empty => simp [ptOk] at h
  | skip => simp [ptOk] at h
  | cat => simp [ptOk] at h
  | mrg => simp [ptOk] at h
  | vp => simp [ptOk] at h
  | catM => simp [ptOk] at h
  | mrgE => simp [ptOk] at h
  | ab => simp [ptOk] at h
  | abx => simp [ptOk] at h
  | perm k ns =>
    simp only [ptOk] at h
    cases hk : resAt X k with
    | none => rw [hk] at h; cases h
    | some r =>
      rw [hk] at h
      cases r with
      | subP c' cs =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨c0, hc0, he⟩ := (resAt_ok hX hk : CRes.Holds σ (.subP c' cs))
        rw [← CCell.beq_eq h1, addr_eq, he, ← addr_eq]
        exact permW_ok hs h2 c0 hc0
      | _ => simp at h
  | prep r q res ih =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.and_eq_true] at h
      rw [addr_eq]
      exact prep_ok (facts_ok hX hs.env res) (hs.rs r R hr) h.1 (by rw [← addr_eq]; exact ih h.2)
  | app r q res ih =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.and_eq_true] at h
      rw [addr_eq]
      exact app_ok (facts_ok hX hs.env res) (hs.rs r R hr) h.1 (by rw [← addr_eq]; exact ih h.2)
  | keep => simp [ptOk] at h
  | prep2 r q q2 res ih ih2 =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.and_eq_true] at h
      rw [addr_eq]
      exact prep2_ok (facts_ok hX hs.env res) (hs.rs r R hr) h.1.1 (by rw [← addr_eq]; exact ih h.1.2)
        (by rw [← addr_eq]; exact ih2 h.2)
  | back r ns res =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.and_eq_true] at h
      exact back_ok hs (facts_ok hX hs.env res) (hs.rs r R hr) h.1 h.2
  | evs n k res =>
    simp only [ptOk] at h
    cases hn : getF st.sc n with
    | none => rw [hn] at h; cases h
    | some Q =>
      rw [hn] at h
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨⟨hk, he⟩, h⟩ := h
      have hR := evs_run hs he hk
      rcases Bool.or_eq_true_iff.mp h with h | h
      · rw [addr_eq]
        exact ptRun_ok (facts_ok hX hs.env res) hR h
      · exact subPt_ok hX hs.env (facts_ok hX hs.env res) hR h
  | der => simp [ptOk] at h
  | wnil => simp [ptOk] at h
  | wcons => simp [ptOk] at h
  | drv => simp [ptOk] at h

/-- **A run's witness**: the run written. -/
theorem rnOk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    {st : CSt} (hs : StOk rd W σ st) {Q : PRun} {w : Wit} (h : rnOk X st Q w = true) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  cases w with
  | run r res =>
    simp only [rnOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      simp only [Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact runRun_ok (facts_ok hX hs.env res) hs.eqs (hs.rs r R hr) h
      · exact subRun_ok hX hs.env (hs.rs r R hr) h
      · exact runRunS_ok (facts_ok hX hs.env res) hs.eqs (hs.rs r R hr) h
  | empty =>
    simp only [rnOk] at h
    exact fun x hx ↦ absurd hx (emptyE_ok hs.eqs h)
  | ev => simp [rnOk] at h
  | pre => simp [rnOk] at h
  | res => simp [rnOk] at h
  | pf => simp [rnOk] at h
  | pfr => simp [rnOk] at h
  | word => simp [rnOk] at h
  | pts => simp [rnOk] at h
  | skip => simp [rnOk] at h
  | cat => simp [rnOk] at h
  | mrg => simp [rnOk] at h
  | perm => simp [rnOk] at h
  | prep => simp [rnOk] at h
  | app => simp [rnOk] at h
  | keep => simp [rnOk] at h

  | prep2 => simp [rnOk] at h
  | vp => simp [rnOk] at h
  | catM => simp [rnOk] at h
  | mrgE => simp [rnOk] at h
  | ab => simp [rnOk] at h
  | abx => simp [rnOk] at h
  | evs => simp [rnOk] at h
  | back => simp [rnOk] at h
  | der => simp [rnOk] at h
  | wnil => simp [rnOk] at h
  | wcons => simp [rnOk] at h
  | drv => simp [rnOk] at h

/-- The cells past a word, each witnessed: written. -/
theorem ptsW_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {m : CCell} :
    ∀ {offs : List ℕ} {wl wl' : List Wit}, ptsW X st m offs wl = some wl' → ∀ o ∈ offs, W ((m.shift o).addr σ)
  | [], _, _, _, o, ho => by simp at ho
  | o :: os, [], _, h, _, _ => by simp [ptsW] at h
  | o :: os, w :: wl, wl', h, o0, ho0 => by
    simp only [ptsW] at h
    cases hp : ptOk X st (m.shift o) w with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp, Bool.cond_true] at h
      rcases List.mem_cons.mp ho0 with rfl | ho0
      · exact ptOk_ok hX hpre hs hp
      · exact ptsW_ok hX hpre hs h o0 ho0

theorem lt_offHi {offs : List ℕ} : ∀ {o : ℕ}, o ∈ offs → o < offHi offs := by
  induction offs with
  | nil => intro o ho; cases ho
  | cons a l ih =>
    intro o ho
    have h := @ih o
    simp only [offHi, List.foldr_cons] at h ⊢
    rcases List.mem_cons.mp ho with rfl | ho
    · omega
    · have := h ho; omega

/-- The cells past a word, each witnessed or inside one run witnessed: written. -/
theorem ptsWR_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {m : CCell} {offs : List ℕ}
    {wl wl' : List Wit} (h : ptsWR X st m offs wl = some wl') : ∀ o ∈ offs, W ((m.shift o).addr σ) := by
  rcases wl with _ | ⟨w0, _ | ⟨w, wl⟩⟩
  · exact ptsW_ok hX hpre hs (by simpa only [ptsWR] using h)
  · exact ptsW_ok hX hpre hs (by simpa only [ptsWR] using h)
  · simp only [ptsWR] at h
    cases hb : (w0.isPts && !offs.isEmpty) with
    | false => rw [hb, Bool.cond_false] at h; exact ptsW_ok hX hpre hs h
    | true =>
      rw [hb, Bool.cond_true] at h
      cases hr : (Nat.blt (offHi offs) capE && rnOk X st ⟨m, 1, ⟨[], 0⟩, ⟨[], offHi offs⟩⟩ w) with
      | false => rw [hr] at h; simp at h
      | true =>
        simp only [Bool.and_eq_true, Nat.blt_eq] at hr
        have hR := rnOk_ok hX hs hr.2
        intro o ho
        have hlt := lt_offHi ho
        have hx := hR _ (runSet_of (S := 1) (rep_const (by rw [capE_eq]; norm_num)) (rep_const hr.1) (Nat.zero_le o) hlt)
        rw [addr_eq, CCell.addrW, valW_shift]; simpa only [Nat.one_mul] using hx

/-- **A pointer fact's witness**: the cells past the word at the cell written. -/
theorem ptrOk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {c : CCell} {offs : List ℕ}
    {wl wl' : List Wit} (h : ptrOk X st c offs wl = some wl') : ∀ x, PtrSet rd (c.addr σ) offs x → W x := by
  cases wl with
  | nil => simp [ptrOk] at h
  | cons w wl =>
    cases w
    case pf n =>
      simp only [ptrOk] at h
      cases hn : getF st.pf n with
      | none => simp [hn] at h
      | some p =>
        simp only [hn] at h
        cases hb : (p.1.beq c && subL offs p.2) with
        | false => rw [hb] at h; simp at h
        | true =>
          simp only [Bool.and_eq_true] at hb
          intro x hx
          refine hs.pf n p hn x ?_
          rw [CCell.beq_eq hb.1]
          exact ptrSet_sub hb.2 hx
    case pfr r res =>
      simp only [ptrOk] at h
      cases hr : getF st.pr r with
      | none => simp [hr] at h
      | some p =>
        simp only [hr] at h
        cases hb : (ptRun (facts X st.env res) p.1 c && subL offs p.2) with
        | false => rw [hb] at h; simp at h
        | true =>
          simp only [Bool.and_eq_true] at hb
          have hR := ptRun_ok (W := fun x ↦ RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi x)
            (facts_ok hX hs.env res) (fun _ hx ↦ hx) hb.1
          rw [← addr_eq] at hR
          exact fun x hx ↦ hs.pr r p hr _ hR x (ptrSet_sub hb.2 hx)
    case word m =>
      simp only [ptrOk] at h
      cases hm : getF st.sv m with
      | none => simp [hm] at h
      | some p =>
        simp only [hm] at h
        cases hb : p.1.beq c with
        | false => rw [hb] at h; simp at h
        | true =>
          rw [hb, Bool.cond_true] at h
          have hrd := hs.sv m p hm
          rw [CCell.beq_eq hb] at hrd
          have hcells := ptsWR_ok hX hpre hs h
          rintro x ⟨w, hw, o, ho, rfl⟩
          rw [hrd, Option.some.injEq] at hw
          subst hw
          have := hcells o ho
          rwa [addr_eq, CCell.addrW, valW_shift, limb0_mul_ofK] at this
    all_goals simp [ptrOk] at h

/-- Pointer facts witnessed at a run's cells: written. -/
theorem ptrPts_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {b : CCell} {S : ℕ}
    {offs : List ℕ} : ∀ {j n : ℕ} {wl wl' : List Wit}, ptrPts X st b S offs j n wl = some wl' →
      ∀ i, j ≤ i → i < j + n → ∀ x, PtrSet rd ((b.shift (S * i)).addr σ) offs x → W x
  | _, 0, _, _, _, i, h1, h2 => by omega
  | j, n + 1, wl, wl', h, i, h1, h2 => by
    simp only [ptrPts] at h
    cases hp : ptrOk X st (b.shift (S * j)) offs wl with
    | none => rw [hp] at h; cases h
    | some wl1 =>
      rw [hp] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact ptrOk_ok hX hpre hs hp
      · exact ptrPts_ok hX hpre hs h i (by omega) (by omega)

/-- **A pointer run's witness**: the cells past the word at each of its cells written. -/
theorem ptrROk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H rd f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st) {Q : PRun} {offs : List ℕ}
    {wl wl' : List Wit} (h : ptrROk X st Q offs wl = some wl') :
    ∀ a, RunSet (vw σ) Q.base Q.stride Q.lo Q.hi a → ∀ x, PtrSet rd a offs x → W x := by
  cases wl with
  | nil => simp [ptrROk] at h
  | cons w wl =>
    cases w
    case pfr r res =>
      simp only [ptrROk] at h
      cases hr : getF st.pr r with
      | none => simp [hr] at h
      | some p =>
        simp only [hr] at h
        cases hb : (runRun (facts X st.env res) st.eqs Q p.1 && subL offs p.2) with
        | false => rw [hb] at h; simp at h
        | true =>
          simp only [Bool.and_eq_true] at hb
          have hQ := runRun_ok (W := fun a ↦ RunSet (vw σ) p.1.base p.1.stride p.1.lo p.1.hi a)
            (facts_ok hX hs.env res) hs.eqs (fun _ hx ↦ hx) hb.1
          exact fun a ha x hx ↦ hs.pr r p hr a (hQ a ha) x (ptrSet_sub hb.2 hx)
    case empty =>
      simp only [ptrROk] at h
      cases hb : emptyE st.eqs Q with
      | false => rw [hb] at h; simp at h
      | true => exact fun a ha ↦ absurd ha (emptyE_ok hs.eqs hb)
    case pts =>
      simp only [ptrROk] at h
      cases hb : constR Q with
      | false => rw [hb] at h; simp at h
      | true =>
        rw [hb, Bool.cond_true] at h
        unfold constR at hb
        simp only [Bool.and_eq_true] at hb
        obtain ⟨⟨⟨hl, hh⟩, hlc⟩, hhc⟩ := hb
        rintro a ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ x hx
        rw [rep_nil hl (Nat.blt_eq.mp hlc), Option.some.injEq] at h1
        rw [rep_nil hh (Nat.blt_eq.mp hhc), Option.some.injEq] at h2
        subst h1 h2
        have := ptrPts_ok hX hpre hs h j h3 (by omega) x
        rw [addr_eq, CCell.addrW, valW_shift] at this
        exact this hx
    all_goals simp [ptrROk] at h

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX}

theorem reqP_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {cs : List CCell} {wl wl' : List Wit}, reqP X st ms cs wl = some wl' → ∀ c ∈ cs, W (c.addrW (slotW ws))
  | [], _, _, _, c, hc => by simp at hc
  | c :: cs, [], _, h, _, _ => by simp [reqP] at h
  | c :: cs, w :: wl, wl', h, c0, hc0 => by
    simp only [reqP] at h
    cases hi : instC ms c with
    | none => rw [hi] at h; cases h
    | some c' =>
      simp only [hi] at h
      cases hp : ptOk X st c' w with
      | false => rw [hp] at h; cases h
      | true =>
        rw [hp, Bool.cond_true] at h
        rcases List.mem_cons.mp hc0 with rfl | hc0
        · have := ptOk_ok hX hpre hs hp
          rwa [addr_eq, CCell.addrW, instC_ok hms hi] at this
        · exact reqP_ok hX hpre hs hms h c0 hc0

/-- Points witnessed at a run's cells: written. -/
theorem ptsRun_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {b : CCell} {S : ℕ} : ∀ {j n : ℕ} {wl wl' : List Wit},
      ptsRun X st b S j n wl = some wl' → ∀ i, j ≤ i → i < j + n → W ((b.shift (S * i)).addr σ)
  | _, 0, _, _, _, i, h1, h2 => by omega
  | j, n + 1, [], _, h, _, _, _ => by simp [ptsRun] at h
  | j, n + 1, w :: wl, wl', h, i, h1, h2 => by
    simp only [ptsRun] at h
    cases hp : ptOk X st (b.shift (S * j)) w with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp, Bool.cond_true] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact ptOk_ok hX hpre hs hp
      · exact ptsRun_ok hX hpre hs h i (by omega) (by omega)

/-- A run's part's witnesses: written. -/
theorem runOk1_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOk1 X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  cases wl with
  | nil => simp [runOk1] at h
  | cons w wl =>
    by_cases hw : w = .pts
    · subst hw
      simp only [runOk1] at h
      cases hb : constR Q with
      | false => rw [hb] at h; simp at h
      | true =>
        rw [hb, Bool.cond_true] at h
        unfold constR at hb
        simp only [Bool.and_eq_true] at hb
        obtain ⟨⟨⟨hl, hh⟩, hlc⟩, hhc⟩ := hb
        rintro a ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩
        rw [rep_nil hl (Nat.blt_eq.mp hlc), Option.some.injEq] at h1
        rw [rep_nil hh (Nat.blt_eq.mp hhc), Option.some.injEq] at h2
        subst h1 h2
        have := ptsRun_ok hX hpre hs h j h3 (by omega)
        rwa [addr_eq, CCell.addrW, valW_shift] at this
    · have h' : (bif rnOk X st Q w then some wl else none) = some wl' := by
        cases w <;> first | exact absurd rfl hw | exact h
      cases hp : rnOk X st Q w with
      | false => rw [hp] at h'; cases h'
      | true => exact rnOk_ok hX hs hp

theorem mrgW_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {S : ℕ} {lo hi : CCell} : ∀ {r n : ℕ} {wl wl' : List Wit},
      mrgW X st Q S lo hi r n wl = some wl' → ∀ r', r ≤ r' → r' < r + n →
        RunF W (vw σ) (mrgPart Q S r' lo hi).base (mrgPart Q S r' lo hi).stride lo hi
  | _, 0, _, _, _, r', h1, h2 => by omega
  | r, n + 1, wl, wl', h, r', h1, h2 => by
    simp only [mrgW] at h
    cases hp : runOk1 X st (mrgPart Q S r lo hi) wl with
    | none => rw [hp] at h; cases h
    | some ws' =>
      rw [hp] at h
      by_cases hr : r' = r
      · subst hr
        exact runOk1_ok hX hpre hs hp
      · exact mrgW_ok hX hpre hs h r' (by omega) (by omega)

/-- **A merge**: a run of stride `S'` whose cells are those of its `S` residue runs of stride `S'·S`, its
lower bound a constant multiple of `S`, its upper bound the `S`-th power of a root with an exponent (the
upper bound's exponent is at most `S` times the root's). -/
theorem mrg_le {Q : PRun} {S : ℕ} {R : CCell} (hS : 0 < S) (hlb : Q.lo.bases.isEmpty = true) (hlc : Q.lo.off < capE)
    {yr : ℕ} (hyr : rep (R.valW (vw σ)) = some yr) (hle : ∀ y, rep (Q.hi.valW (vw σ)) = some y → y ≤ yr * S)
    (hparts : ∀ r < S, RunF W (vw σ) (mrgPart Q S r ⟨[], Q.lo.off / S⟩ R).base
      (mrgPart Q S r ⟨[], Q.lo.off / S⟩ R).stride ⟨[], Q.lo.off / S⟩ R) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  rintro x ⟨ylo, yhi, i, h1, h2, h3, h4, rfl⟩
  rw [rep_nil hlb hlc, Option.some.injEq] at h1
  subst h1
  have hle := hle yhi h2
  have hi : i % S + S * (i / S) = i := Nat.mod_add_div i S
  have hj : i / S < yr := (Nat.div_lt_iff_lt_mul hS).mpr (by omega)
  have hj0 : Q.lo.off / S ≤ i / S := Nat.div_le_div_right h3
  refine hparts (i % S) (Nat.mod_lt _ hS) _ ⟨Q.lo.off / S, yr, i / S, rep_const (by
    have := Nat.div_le_self Q.lo.off S; omega), hyr, hj0, hj, ?_⟩
  simp only [mrgPart]
  rw [valW_shift, mul_assoc, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add,
    Nat.mul_assoc, ← Nat.mul_add, hi]

theorem mrg_ok {Q : PRun} {S : ℕ} {R : CCell} (hS : 0 < S) (hlb : Q.lo.bases.isEmpty = true) (hlc : Q.lo.off < capE)
    (hroot : Q.hi.valW (vw σ) = R.valW (vw σ) ^ S) {yr : ℕ} (hyr : rep (R.valW (vw σ)) = some yr)
    (hparts : ∀ r < S, RunF W (vw σ) (mrgPart Q S r ⟨[], Q.lo.off / S⟩ R).base
      (mrgPart Q S r ⟨[], Q.lo.off / S⟩ R).stride ⟨[], Q.lo.off / S⟩ R) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  rintro x ⟨ylo, yhi, i, h1, h2, h3, h4, rfl⟩
  rw [rep_nil hlb hlc, Option.some.injEq] at h1
  subst h1
  have hhi : Q.hi.valW (vw σ) = ofK (addressOfIndex (yr * S)) := by
    rw [hroot, (rep_spec hyr).2, ← ofK_pow, addressOfIndex, addressOfIndex, ← pow_mul]
  have hle := rep_le h2 hhi
  have hi : i % S + S * (i / S) = i := Nat.mod_add_div i S
  have hj : i / S < yr := (Nat.div_lt_iff_lt_mul hS).mpr (by omega)
  have hj0 : Q.lo.off / S ≤ i / S := Nat.div_le_div_right h3
  refine hparts (i % S) (Nat.mod_lt _ hS) _ ⟨Q.lo.off / S, yr, i / S, rep_const (by
    have := Nat.div_le_self Q.lo.off S; omega), hyr, hj0, hj, ?_⟩
  simp only [mrgPart]
  rw [valW_shift, mul_assoc, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add,
    Nat.mul_assoc, ← Nat.mul_add, hi]

/-- **A run's witnesses, one level**: the run written. -/
theorem runOk0_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOk0 X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  cases wl with
  | nil => simp [runOk0, runOk1] at h
  | cons w wl =>
    by_cases hw : ∃ k, w = .cat k
    · obtain ⟨k, rfl⟩ := hw
      simp only [runOk0] at h
      cases hk : Nat.blt k capE with
      | false => rw [hk] at h; simp at h
      | true =>
        rw [hk, Bool.cond_true] at h
        split at h
        · rename_i ws1 h1
          have R1 := runOk1_ok hX hpre hs h1
          have R2 := runOk1_ok hX hpre hs h
          have hkc := Nat.blt_eq.mp hk
          rintro x ⟨ylo, yhi, j, h1', h2', h3, h4, rfl⟩
          by_cases hj : j < k
          · exact R1 _ ⟨ylo, k, j, h1', rep_const hkc, h3, hj, rfl⟩
          · exact R2 _ ⟨k, yhi, j, rep_const hkc, h2', by omega, h4, rfl⟩
        · cases h
    · by_cases hm : ∃ S res, w = .mrg S res
      · obtain ⟨S, res, rfl⟩ := hm
        simp only [runOk0] at h
        cases hb : (Nat.blt 0 S && Q.lo.bases.isEmpty && Nat.beq (Q.lo.off % S) 0 && Nat.blt Q.lo.off capE &&
            ((rootC Q.hi S).pow S).beq Q.hi && hasExp (facts X st.env res) (rootC Q.hi S)) with
        | false => rw [hb] at h; simp at h
        | true =>
          rw [hb, Bool.cond_true] at h
          simp only [Bool.and_eq_true] at hb
          obtain ⟨⟨⟨⟨⟨hS, hlb⟩, -⟩, hlc⟩, hroot⟩, hex⟩ := hb
          obtain ⟨yr, hyr⟩ : ∃ yr, rep ((rootC Q.hi S).valW (vw σ)) = some yr := by
            unfold hasExp at hex
            simp only [Bool.or_eq_true, Bool.and_eq_true] at hex
            rcases hex with ⟨h1, h2⟩ | hf
            · exact ⟨_, rep_nil h1 (Nat.blt_eq.mp h2)⟩
            · obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hf
              obtain ⟨ya, yb, ha, hb, -⟩ := facts_ok hX hs.env res p hp
              simp only [Bool.or_eq_true] at hpe
              rcases hpe with he | he
              · rw [CCell.beq_eq he] at ha
                exact ⟨_, ha⟩
              · rw [CCell.beq_eq he] at hb
                exact ⟨_, hb⟩
          exact mrg_ok (Nat.blt_eq.mp hS) hlb (Nat.blt_eq.mp hlc)
            (((valW_pow _ _).symm.trans (congrArg _ (CCell.beq_eq hroot))).symm) hyr
            fun r hr ↦ mrgW_ok hX hpre hs h r (Nat.zero_le _) (by omega)
      · by_cases he : ∃ S r res, w = .mrgE S r res
        · obtain ⟨S, R, res, rfl⟩ := he
          simp only [runOk0] at h
          cases hb : (Nat.blt 0 S && Q.lo.bases.isEmpty && Nat.beq (Q.lo.off % S) 0 && Nat.blt Q.lo.off capE &&
              (eqV st.eqs (R.pow S) Q.hi || hasF (facts X st.env res) Q.hi ((R.pow S).shift 1)) &&
              hasExp (facts X st.env res) R) with
          | false => rw [hb] at h; simp at h
          | true =>
            rw [hb, Bool.cond_true] at h
            simp only [Bool.and_eq_true] at hb
            obtain ⟨⟨⟨⟨⟨hS, hlb⟩, -⟩, hlc⟩, hroot⟩, hex⟩ := hb
            obtain ⟨yr, hyr⟩ := hasExp_ok (facts_ok hX hs.env res) hex
            have hparts := fun r (hr : r < S) ↦ mrgW_ok hX hpre hs h r (Nat.zero_le _) (by omega)
            rcases Bool.or_eq_true_iff.mp hroot with hroot | hroot
            · exact mrg_ok (Nat.blt_eq.mp hS) hlb (Nat.blt_eq.mp hlc)
                (by rw [← eqV_ok hs.eqs hroot, valW_pow]) hyr hparts
            · refine mrg_le (Nat.blt_eq.mp hS) hlb (Nat.blt_eq.mp hlc) hyr (fun y hy ↦ ?_) hparts
              obtain ⟨ya, yb, ha, hb2, hab⟩ := hasF_ok (facts_ok hX hs.env res) hroot
              rw [hy, Option.some.injEq] at ha
              subst ha
              obtain ⟨-, hrv⟩ := rep_spec hyr
              have h2 : ((R.pow S).shift 1).valW (vw σ) = ofK (addressOfIndex (yr * S + 1)) := by
                rw [valW_shift, valW_pow, hrv, ← ofK_pow, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex,
                  ← pow_mul, ← pow_add]
              have := rep_le hb2 h2
              omega
        · have h' : runOk1 X st Q (w :: wl) = some wl' := by
            cases w <;> first | exact absurd ⟨_, rfl⟩ hw | exact absurd ⟨_, _, rfl⟩ hm | exact absurd ⟨_, _, _, rfl⟩ he | exact h
          exact runOk1_ok hX hpre hs h'

/-- **A split at a symbolic index**: the upper bound's word `k·h`, `k`'s and `h`'s exponents existing, the part
below `k` and the part from `k` (base `base·k^S`, from `g^0` to `h`) written: the run written. -/
theorem catM_ok {w : ℕ → E} {Q : PRun} {k h : CCell} (hkh : (k.mul h).valW w = Q.hi.valW w) {yk yh : ℕ}
    (hyk : rep (k.valW w) = some yk) (hyh : rep (h.valW w) = some yh)
    (R1 : RunF W w Q.base Q.stride Q.lo k) (R2 : RunF W w (Q.base.mul (k.pow Q.stride)) Q.stride ⟨[], 0⟩ h) :
    RunF W w Q.base Q.stride Q.lo Q.hi := by
  rintro x ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩
  have hk := (rep_spec hyk)
  have hh := (rep_spec hyh)
  have hhi : Q.hi.valW w = ofK (addressOfIndex (yk + yh)) := by
    rw [← hkh, valW_mul, hk.2, hh.2, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
  have hle : yhi = yk + yh := by
    have h2' := h2
    rw [hhi] at h2'
    have := rep_spec h2'
    rw [capE_eq] at hk hh
    rw [capE_eq] at this
    exact (gpow_inj_lt (by omega) (by omega) this.2).symm
  by_cases hj : j < yk
  · exact R1 _ ⟨ylo, yk, j, h1, hyk, h3, hj, rfl⟩
  · refine R2 _ ⟨0, yh, j - yk, rep_const (by rw [capE_eq]; norm_num), hyh, Nat.zero_le _, by omega, ?_⟩
    have e : (Q.base.mul (k.pow Q.stride)).valW w * ofK (addressOfIndex (Q.stride * (j - yk))) =
        Q.base.valW w * ofK (addressOfIndex (Q.stride * j)) := by
      rw [valW_mul, valW_pow, hk.2, ← ofK_pow, mul_assoc, ← ofK_mul, addressOfIndex, addressOfIndex,
        addressOfIndex, ← pow_mul, ← pow_add, show yk * Q.stride + Q.stride * (j - yk) = Q.stride * j by
          rw [Nat.mul_comm yk, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)]]
    rw [e]

/-- **A run's witnesses**: the run written. -/
theorem runOkL_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOkL X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  by_cases hc : ∃ k h res wl1, wl = .catM k h res :: wl1
  · obtain ⟨k, hh, res, wl1, rfl⟩ := hc
    simp only [runOkL] at h
    cases hb : (eqV st.eqs (k.mul hh) Q.hi && hasExp (facts X st.env res) k && hasExp (facts X st.env res) hh) with
    | false => rw [hb] at h; simp at h
    | true =>
      rw [hb, Bool.cond_true] at h
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨he, hk⟩, hh'⟩ := hb
      obtain ⟨yk, hyk⟩ := hasExp_ok (facts_ok hX hs.env res) hk
      obtain ⟨yh, hyh⟩ := hasExp_ok (facts_ok hX hs.env res) hh'
      cases h1 : runOk0 X st ⟨Q.base, Q.stride, Q.lo, k⟩ wl1 with
      | none => rw [h1] at h; cases h
      | some ws' =>
        rw [h1] at h
        have R1 := runOk0_ok hX hpre hs h1
        have R2 := runOk0_ok hX hpre hs h
        exact catM_ok (eqV_ok hs.eqs he) hyk hyh R1 R2
  · have h' : runOk0 X st Q wl = some wl' := by
      cases wl with
      | nil => exact h
      | cons w wl1 =>
        cases w <;> first | exact absurd ⟨_, _, _, _, rfl⟩ hc | exact h
    exact runOk0_ok hX hpre hs h'

theorem runOk_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOk X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  by_cases hc : ∃ k h res wl1, wl = .catM k h res :: wl1
  · obtain ⟨k, hh, res, wl1, rfl⟩ := hc
    simp only [runOk] at h
    cases hb : (eqV st.eqs (k.mul hh) Q.hi && hasExp (facts X st.env res) k && hasExp (facts X st.env res) hh) with
    | false => rw [hb] at h; simp at h
    | true =>
      rw [hb, Bool.cond_true] at h
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨he, hk⟩, hh'⟩ := hb
      obtain ⟨yk, hyk⟩ := hasExp_ok (facts_ok hX hs.env res) hk
      obtain ⟨yh, hyh⟩ := hasExp_ok (facts_ok hX hs.env res) hh'
      cases h1 : runOk0 X st ⟨Q.base, Q.stride, Q.lo, k⟩ wl1 with
      | none => rw [h1] at h; cases h
      | some ws' =>
        rw [h1] at h
        have R1 := runOk0_ok hX hpre hs h1
        have R2 := runOkL_ok hX hpre hs h
        exact catM_ok (eqV_ok hs.eqs he) hyk hyh R1 R2
  · have h' : runOk0 X st Q wl = some wl' := by
      cases wl with
      | nil => exact h
      | cons w wl1 =>
        cases w <;> first | exact absurd ⟨_, _, _, _, rfl⟩ hc | exact h
    exact runOk0_ok hX hpre hs h'

/-- **A read's witness** (`ptOkD`): the cell written. -/
theorem ptOkD_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {c : CCell} {w : Wit} (h : ptOkD X st c w = true) : W (c.addr σ) := by
  cases w with
  | der b S lo hi res ws =>
    simp only [ptOkD, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i hr
      rw [addr_eq]
      exact ptRun_ok (facts_ok hX hs.env res) (runOk_ok hX hpre hs hr) h1
    · cases h2
  | _ => exact ptOk_ok hX hpre hs h

/-- **A run needed's witnesses** (`runOkD`): the run written. -/
theorem runOkD_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {Q : PRun} {wl wl' : List Wit} (h : runOkD X st Q wl = some wl') :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  by_cases hc : ∃ b S lo hi res wl1, wl = .drv b S lo hi res :: wl1
  · obtain ⟨b, S, lo, hi, res, wl1, rfl⟩ := hc
    simp only [runOkD] at h
    split at h
    · rename_i ws' hr
      have hR := runOk_ok hX hpre hs hr
      cases hb : (runRun (facts X st.env res) st.eqs Q ⟨b, S, lo, hi⟩ || subRun X st.env res Q ⟨b, S, lo, hi⟩) with
      | false => rw [hb] at h; cases h
      | true =>
        rcases Bool.or_eq_true_iff.mp hb with hb | hb
        · exact runRun_ok (facts_ok hX hs.env res) hs.eqs hR hb
        · exact subRun_ok hX hs.env hR hb
    · cases h
  · have h' : runOk X st Q wl = some wl' := by
      cases wl with
      | nil => exact h
      | cons w wl1 =>
        cases w <;> first | exact absurd ⟨_, _, _, _, _, _, rfl⟩ hc | exact h
    exact runOk_ok hX hpre hs h'

theorem reqR_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {rs : List CRun} {wl wl' : List Wit}, reqR X st ms rs wl = some wl' → ∀ r ∈ rs, r.F W (slotW ws)
  | [], _, _, _, r, hr => by simp at hr
  | r :: rs, wl, wl', h, r0, hr0 => by
    simp only [reqR] at h
    cases hi : instR ms r with
    | none => simp [hi] at h
    | some q =>
      simp only [hi] at h
      cases hp : runOkD X st q wl with
      | none => simp [hp] at h
      | some wl1 =>
        simp only [hp] at h
        rcases List.mem_cons.mp hr0 with rfl | hr0
        · exact (instR_runF hms hi).mp (runOkD_ok hX hpre hs hp)
        · exact reqR_ok hX hpre hs hms h r0 hr0

theorem reqPP_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {ps : List (CCell × List ℕ)} {wl wl' : List Wit}, reqPP X st ms ps wl = some wl' →
      ∀ p ∈ ps, ∀ x, PtrSet rd (p.1.addrW (slotW ws)) p.2 x → W x
  | [], _, _, _, p, hp => by simp at hp
  | p :: ps, wl, wl', h, p0, hp0 => by
    simp only [reqPP] at h
    cases hi : instC ms p.1 with
    | none => simp [hi] at h
    | some c =>
      simp only [hi] at h
      cases hq : ptrOk X st c p.2 wl with
      | none => simp [hq] at h
      | some wl1 =>
        simp only [hq] at h
        rcases List.mem_cons.mp hp0 with rfl | hp0
        · have hc := ptrOk_ok hX hpre hs hq
          rwa [addr_eq, CCell.addrW, instC_ok hms hi] at hc
        · exact reqPP_ok hX hpre hs hms h p0 hp0

theorem reqPR_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {ps : List (CRun × List ℕ)} {wl wl' : List Wit}, reqPR X st ms ps wl = some wl' →
      ∀ p ∈ ps, ∀ a, p.1.Set (slotW ws) a → ∀ x, PtrSet rd a p.2 x → W x
  | [], _, _, _, p, hp => by simp at hp
  | p :: ps, wl, wl', h, p0, hp0 => by
    simp only [reqPR] at h
    cases hi : instR ms p.1 with
    | none => simp [hi] at h
    | some q =>
      simp only [hi] at h
      cases hq : ptrROk X st q p.2 wl with
      | none => simp [hq] at h
      | some wl1 =>
        simp only [hq] at h
        rcases List.mem_cons.mp hp0 with rfl | hp0
        · exact fun a ha ↦ ptrROk_ok hX hpre hs hq a ((instR_set hms hi).mpr ha)
        · exact reqPR_ok hX hpre hs hms h p0 hp0

/-- Pointer facts and runs at the slots, witnessed: written. -/
theorem ptrOk_of {ps : List (CCell × List ℕ)} {prs : List (CRun × List ℕ)} {ws : List E}
    (h1 : ∀ p ∈ ps, ∀ x, PtrSet rd (p.1.addrW (slotW ws)) p.2 x → W x)
    (h2 : ∀ p ∈ prs, ∀ a, p.1.Set (slotW ws) a → ∀ x, PtrSet rd a p.2 x → W x) : PtrOk W rd ps prs ws := by
  rintro x (⟨p, hp, hx⟩ | ⟨p, hp, a, ha, hx⟩)
  · exact h1 p hp x hx
  · exact h2 p hp a ha x hx

theorem reqS_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {G : HSig} {wl wl' : List Wit}
    (h : reqS X st ms G wl = some wl') : SigOk W G.pre G.preR ws ∧ PtrOk W rd G.preP G.prePR ws := by
  unfold reqS at h
  cases h1 : reqP X st ms G.pre wl with
  | none => rw [h1] at h; cases h
  | some wl1 =>
    rw [h1] at h
    dsimp only at h
    cases h2 : reqR X st ms G.preR wl1 with
    | none => rw [h2] at h; cases h
    | some wl2 =>
      rw [h2] at h
      dsimp only at h
      cases h3 : reqPP X st ms G.preP wl2 with
      | none => rw [h3] at h; cases h
      | some wl3 =>
        rw [h3] at h
        exact ⟨⟨reqP_ok hX hpre hs hms h1, reqR_ok hX hpre hs hms h2⟩,
          ptrOk_of (reqPP_ok hX hpre hs hms h3) (reqPR_ok hX hpre hs hms h)⟩

/-- The cells of the words at cells, each witnessed: written. -/
theorem derWs_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk rd W σ st) : ∀ {ks : List ℕ} {wl wl' : List Wit}, derWs X st ks wl = some wl' →
      ∀ k ∈ ks, ∀ c, H.ders[k]? = some c → W (c.addrW (vw σ))
  | [], _, _, _, k, hk, _, _ => by simp at hk
  | k :: ks, wl, wl', h, k', hk', c', hc' => by
    cases wl with
    | nil => simp [derWs] at h
    | cons w wl =>
      simp only [derWs] at h
      cases hn : nth X.ders k with
      | none => rw [hn] at h; cases h
      | some c =>
        rw [hn] at h
        dsimp only at h
        cases hb : ptOk X st c w with
        | false => rw [hb] at h; cases h
        | true =>
          rw [hb, Bool.cond_true] at h
          rcases List.mem_cons.mp hk' with rfl | hk'
          · rw [hX.ders, nth_eq, hc', Option.some.injEq] at hn
            subst hn
            rw [← addr_eq]
            exact ptOk_ok hX hpre hs hb
          · exact derWs_ok hX hpre hs h k' hk' c' hc'

/-- A word at a cell, loaded from its cell (`src`), the cell in memory. -/
theorem setSrc_stOk {st : CSt} (hs : StOk rd W σ st) {k : ℕ} {c : CCell} (hd : rd (c.addr σ) = some (σ (V.n k))) :
    StOk rd W σ (st.setSrc k c) := by
  unfold CSt.setSrc
  rw [Trie.seq_eq]
  refine ⟨hs.env, hs.sc, hs.rs, hs.ad, hs.sv, fun k' c' hk' ↦ ?_, hs.pf, hs.pr, hs.cd, hs.eqs, hs.dq⟩
  change getF (setF c Exec.indexDepth st.src k) k' = some c' at hk'
  rcases Check.getF_setF hk' with ⟨rfl, rfl⟩ | hk'
  · exact hd
  · exact hs.src k' c' hk'

/-- **The words at cells loaded from their cells**, those cells in memory. -/
theorem derSt_ok (hX : XOk sigOf H rd f σ X) : ∀ {ks : List ℕ} {st : CSt}, StOk rd W σ st →
    (∀ k ∈ ks, ∀ c, H.ders[k]? = some c → (rd (c.addrW (vw σ))).isSome) → StOk rd W σ (derSt X ks st)
  | [], _, hs, _ => hs
  | k :: ks, st, hs, hd => by
    simp only [derSt]
    have hd' : ∀ k ∈ ks, ∀ c, H.ders[k]? = some c → (rd (c.addrW (vw σ))).isSome :=
      fun k hk ↦ hd k (List.mem_cons_of_mem _ hk)
    cases hn : nth X.ders k with
    | none => exact derSt_ok hX hs hd'
    | some c =>
      dsimp only
      rw [CSt.seq_eq]
      refine derSt_ok hX (setSrc_stOk hs ?_) hd'
      have hc : H.ders[k]? = some c := by rw [← hX.ders, ← nth_eq]; exact hn
      have hsome := hd k List.mem_cons_self c hc
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
      rw [addr_eq, hw]
      exact congrArg some (hX.der k c hc w hw).symm

/-- **A callee's preconditions at a call**, witnessed: the cells its ghost words read written, and, those in
memory, its preconditions written, at its arguments and ghost words. -/
theorem reqG_ok (hX : XOk sigOf H rd f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk rd W σ st)
    {ma : List CCell} {args : List V} (hma : MsOk (vw σ) ma (slotW (args.map σ))) (hla : ma.length = args.length)
    {g : String} {wl wl' : List Wit} (h : reqG X st ma g args wl = some wl') : CallReq sigOf H rd σ W g args := by
  unfold reqG at h
  rw [hX.ga] at h
  cases hb : Nat.beq (gargsOf H.gargs g args).length (X.sigOf g).ghosts with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb, Bool.cond_true] at h
    rw [hX.sigOf] at h hb
    cases hw : derWs X st (derKs (gargsOf H.gargs g args)) wl with
    | none => rw [hw] at h; cases h
    | some wl1 =>
      rw [hw] at h
      dsimp only at h
      refine ⟨derWs_ok hX hpre hs hw, fun hd ↦ ?_⟩
      have hms := msOk_append hma (msOk_map (σ := σ) (gargsOf H.gargs g args)) (by simpa using hla)
      exact ⟨Nat.eq_of_beq_eq_true hb, reqS_ok hX hpre (derSt_ok hX hs hd) hms h⟩

/-- A dispatch arm left out: the selector is not its power of `g`. -/
theorem armSkip_ok (hX : XOk sigOf H rd f σ X) {st : CSt} (hs : StOk rd W σ st) {mx : CCell} {j : ℕ}
    {wl wl' : List Wit} (h : armSkip X st mx j wl = some wl') : mx.valW (vw σ) ≠ ofK (addressOfIndex j) := by
  cases wl with
  | nil => simp [armSkip] at h
  | cons w wl =>
    cases w
    case skip res =>
      simp only [armSkip] at h
      cases hb : (Nat.blt j capE && hasFU (facts X st.env res) mx j) with
      | false => rw [hb] at h; simp at h
      | true =>
        simp only [Bool.and_eq_true] at hb
        obtain ⟨hj, hu⟩ := hb
        obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp hu
        simp only [Bool.and_eq_true] at hq
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hq
        obtain ⟨ya, yb, ha, hb', hlt⟩ := facts_ok hX hs.env res p hp
        rw [CCell.beq_eq h1] at ha
        rw [rep_nil h2 (Nat.blt_eq.mp h4), Option.some.injEq] at hb'
        intro he
        rw [he, rep_of (Nat.blt_eq.mp hj), Option.some.injEq] at ha
        have := Nat.le_of_ble_eq_true h3
        omega
    all_goals simp [armSkip] at h

/-- **Guarantees under a selector, pushed**: valid when the selector's word is `g^j`. -/
theorem condSt_ok {mx : CCell} {j : ℕ} (hj : mx.valW (vw σ) = ofK (addressOfIndex j)) {cd : List CdE}
    (hcd : CdOk rd W σ cd) : ∀ (l : List CdE), (∀ e ∈ l, e ∈ cd) → ∀ {st : CSt}, StOk rd W σ st →
      StOk rd W σ (condSt mx j l st)
  | [], _, _, hs => hs
  | e :: l, hl, st, hs => by
    simp only [condSt]
    cases hb : e.mx.beq mx with
    | false => exact condSt_ok hj hcd l (fun e' h ↦ hl e' (List.mem_cons_of_mem _ h)) hs
    | true =>
      rw [Bool.cond_true]
      cases ha : nth e.arms j with
      | none => exact condSt_ok hj hcd l (fun e' h ↦ hl e' (List.mem_cons_of_mem _ h)) hs
      | some a =>
        simp only [CSt.seq_eq]
        obtain ⟨h1, h2, h3, h4⟩ := hcd e (hl e List.mem_cons_self) j a ha
          (by rw [CCell.beq_eq hb]; exact hj)
        exact condSt_ok hj hcd l (fun e' h ↦ hl e' (List.mem_cons_of_mem _ h))
          (pushPRL_ok (pushRL_ok (pushPL_ok (pushL_ok hs (fun _ h ↦ h) h1) (fun _ h ↦ h) h3) (fun _ h ↦ h) h2)
            (fun _ h ↦ h) h4)

end Inv

end

end LeanVM.Guest.CoreMode
