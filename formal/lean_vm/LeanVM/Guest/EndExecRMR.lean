/-
  LeanVM.Guest.EndExecRMR

  The gap walk's table reads at the honest frames: each claim's entry below the caller's bound,
  from its frame's gaps and the walk's records.
-/

module

public import LeanVM.Guest.EndExecRM

/-!
# The gap walk's reads

At an honest frame of a frame loop (or of the last claims), the body's atoms hold on the reference
and name their values (`atoms_on_path'`). The walk (`monoWalk_vals`) puts the gaps at `g^(e_i)`,
`e_i < 2^32`, the coverage pointer after `j` claims at `cov0 · g^(Σ_{i<j} e_i)` and the table
pointer at `ent0 · g^(4 Σ_{i<j} e_i)`. With the record's pointers at offset `O` (`MonoQ`), claim
`jj` reads from `entries · g^(4 o)`, `o = O + Σ_{i ≤ jj} e_i + jj`; the walk ends at
`O + Σ e_i + m`, which a frame loop writes into the next record, at an offset `O' ≤ L` (`MonoQ`,
the two equal: no wrap, `region ≠ 0` where a claim is marked), and which the last claims bound by
their range check. So `o < L`, the exponent of the caller's `limit` (`tabRead_rsub`). The
residual's product is the read's (`bs_val`, either order of its bases).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1 (loadHolds_unique loadHolds_mul_gen_pow word_two_pow)
open LeanVM.Guest.B1.Digest
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Sums of gaps -/

/-- The gaps' exponents below `j`, summed. -/
def gsum (es : ℕ → ℕ) (j : ℕ) : ℕ := ((List.range j).map es).sum

theorem gsum_succ (es : ℕ → ℕ) (j : ℕ) : gsum es (j + 1) = gsum es j + es j := by
  simp [gsum, List.range_succ]

theorem gsum_mono (es : ℕ → ℕ) {j k : ℕ} (h : j ≤ k) : gsum es j ≤ gsum es k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [gsum_succ]; omega

theorem gsum_le {es : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, es i < 2 ^ 32) : ∀ j ≤ n, gsum es j ≤ j * 2 ^ 32
  | 0, _ => by simp [gsum]
  | j + 1, hj => by
    rw [gsum_succ, Nat.succ_mul]
    have := gsum_le h j (by omega)
    have := h j (by omega)
    omega

theorem prod_gaps {σ : Core.Val} {g0 n : ℕ} {es : ℕ → ℕ} (hes : ∀ i < n, σ (.n (g0 + 10 * i)) = gen ^ es i) :
    ∀ j ≤ n, ((List.range j).map fun i => σ (.n (g0 + 10 * i)) ^ 4).prod = gen ^ (4 * gsum es j)
  | 0, _ => by simp [gsum]
  | j + 1, hj => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_gaps hes j (by omega), gsum_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hes j (by omega)]
    rw [← pow_mul, ← pow_add]
    ring_nf

/-! ## The walk at a frame -/

/-- **The walk's values at a valuation**: the gaps `g^(e_i)`, named by atoms; the pointers after `j`
claims; the coverage pointer nonzero once a claim is marked. -/
theorem monoWalk_vals {rd : Reader} (hm : MemOk rd) {σ : Core.Val} {atoms : List Atom}
    {p0 g0 cov0 ent0 : ℕ} {mark : V} {n : ℕ}
    (h : monoRecs atoms p0 g0 cov0 ent0 mark n 0 n = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ es : ℕ → ℕ, (∀ i < n, es i < 2 ^ 32 ∧ σ (.n (g0 + 10 * i)) = gen ^ es i ∧
        ∃ a ∈ atoms, .n (g0 + 10 * i) ∈ atomUses a) ∧
      (∀ j ≤ n, σ (.n (mCov g0 cov0 j)) = σ (.n cov0) * gen ^ gsum es j ∧
        σ (.n (mEnt g0 ent0 j)) = σ (.n ent0) * gen ^ (4 * gsum es j)) ∧
      (0 < n → σ (.n cov0) ≠ 0) := by
  simp only [monoRecs, List.all_eq_true, List.mem_range', Bool.or_eq_true, decide_eq_true_eq] at h
  have hok : ∀ i < n, monoClaimOk (monoWin atoms p0 i) i (g0 + 10 * i) (mCov g0 cov0 i)
      (mEnt g0 ent0 i) mark = true := fun i hi ↦ by
    rcases h i ⟨i, by omega, by omega⟩ with h' | h'
    · omega
    · exact h'
  have hwin : ∀ i, ∀ a ∈ monoWin atoms p0 i, a ∈ atoms :=
    fun i a ha ↦ List.mem_of_mem_drop (List.mem_of_mem_take ha)
  have hex : ∀ i, i < n → ∃ e, e < 2 ^ 32 ∧ σ (.n (g0 + 10 * i)) = gen ^ e ∧
      ∃ a ∈ atoms, .n (g0 + 10 * i) ∈ atomUses a := fun i hi ↦ by
    have hc := hok i hi
    simp only [monoClaimOk, Bool.and_eq_true] at hc
    obtain ⟨a, ha, hd⟩ := List.any_eq_true.mp hc.1.1.1.1.1.1
    have := monoWin_holds hat p0 i a ha
    cases a <;> simp only [isDerefOf, Bool.false_eq_true, decide_eq_true_eq] at hd
    subst hd
    obtain ⟨e, he, hg⟩ := load_gpow hm this
    exact ⟨e, he, hg, _, hwin i _ ha, by simp [atomUses]⟩
  choose! es hes using hex
  refine ⟨es, hes, fun j ↦ ?_, fun h0 ↦ ?_⟩
  · induction j with
    | zero => intro _; simp [mCov, mEnt, gsum]
    | succ j ih =>
      intro hj
      obtain ⟨hcv, hev⟩ := ih (by omega)
      have hc := hok j (by omega)
      simp only [monoClaimOk, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩, -⟩, -⟩ := hc
      have hw := monoWin_holds hat p0 j
      obtain ⟨-, hg, -⟩ := hes j (by omega)
      rw [mCov_succ, mEnt_succ, gsum_succ]
      refine ⟨by rw [mulOf_sound h2 hw, hcv, hg, pow_add, mul_assoc], ?_⟩
      rw [mulOf_sound h5 hw, mulOf_sound h4 hw, mulOf_sound h3 hw, hev, hg]
      ring
  · have hc := hok 0 h0
    simp only [monoClaimOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, hmk⟩, -⟩ := hc
    have hw := monoWin_holds hat p0 0
    have hl := load_sound hmk hw
    rw [mulOf_sound h2 hw] at hl
    intro hz
    apply Res.ne_zero_of_load hm hl
    simp [mCov, hz]

/-- Atoms heading a block are on its path. -/
theorem atoms_on_path' {σ : Core.Val} : ∀ (bs : List Atom) {ps : List Stmt} {es : List Ev} {vs : List V},
    Memory.walk σ (bs.map Stmt.atom ++ ps) = .ret es vs → ∀ a ∈ bs, Ev.atom a ∈ es
  | [], _, _, _, _, a, ha => absurd ha List.not_mem_nil
  | b :: bs, ps, es, vs, hw, a, ha => by
    rw [List.map_cons, List.cons_append, Memory.walk] at hw
    simp only [walk1, Out.seq] at hw
    cases h2 : Memory.walk σ (bs.map Stmt.atom ++ ps) with
    | fall _ => rw [h2] at hw; simp [Out.pre] at hw
    | ret es2 vs2 =>
      rw [h2] at hw
      simp only [Out.pre, Out.ret.injEq] at hw
      obtain ⟨rfl, -⟩ := hw
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (atoms_on_path' bs h2 a ha)
    | stuck => rw [h2] at hw; simp [Out.pre] at hw

/-! ## The read -/

/-- A base list's product, each base's word known. -/
theorem rbs_prod {M : ℕ → E} {fp : ℕ} (val : Base → E) :
    ∀ {bs : List (Base × ℕ)} {w : E}, (∀ p ∈ bs, RBase M fp p.1 (val p.1)) → RBs M fp bs w →
      w = (bs.map fun p => val p.1 ^ p.2).prod
  | [], _, _, hw => hw
  | (b, e) :: bs, _, h, ⟨u, w', hu, hw', rfl⟩ => by
    rw [rbase_uniq hu (h _ List.mem_cons_self), rbs_prod val (fun p hp ↦ h p (List.mem_cons_of_mem _ hp)) hw']
    simp

/-- **The read's product**, its bases in either order. -/
theorem bs_val {M : ℕ → E} {fp : ℕ} {q : Mono} {entB : Base} {gs : List (Base × ℕ)} (val : Base → E)
    (hbs : q.bs = (entB, 1) :: gs ∨ q.bs = gs ++ [(entB, 1)]) (hent : RBase M fp entB (val entB))
    (hgs : ∀ p ∈ gs, RBase M fp p.1 (val p.1)) :
    ∀ w, RBs M fp q.bs w → w = val entB * (gs.map fun p => val p.1 ^ p.2).prod := by
  intro w hw
  have hall : ∀ p ∈ q.bs, RBase M fp p.1 (val p.1) := by
    rcases hbs with h | h <;> rw [h] <;> intro p hp <;> simp only [List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hp
    · rcases hp with rfl | hp
      · exact hent
      · exact hgs p hp
    · rcases hp with hp | rfl
      · exact hgs p hp
      · exact hent
  rw [rbs_prod val hall hw]
  rcases hbs with h | h <;> rw [h] <;> simp [List.prod_append, mul_comm]

/-- **A read inside the caller's table**: header cell `1` names frame `a`, whose cells `2` and `5`
hold the table base `vE` and `g^L`; every word of the read's product is `vE · g^(4 o)`, `o < L`. -/
theorem tabRead_rsub {M : ℕ → E} {fp a o L : ℕ} {vE : E} {q : Mono} (hT : M (fp + 1) = ofK (Parameters.g ^ a))
    (ha : a + 5 < maxCells) (hE : M (a + 2) = vE) (hL : M (a + 5) = gen ^ L)
    (hq : ∀ vq, RMono M fp q vq → vq = vE * gen ^ (4 * o)) (ho : o < L) (hL' : L < 2 ^ 33) :
    RSub M fp ⟨q, .num 0, .num 4, 1, 0⟩ Res.anyTab := by
  have hl : (M (fp + 1)).limb 0 = Parameters.g ^ a := by rw [hT]; simp
  refine ⟨0, 4, rfl, rfl, fun vq hvq j _ hj ↦ ?_⟩
  refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, fun vb ylo yhi hvb hlo hhi ↦ ?_⟩
  obtain ⟨w, ⟨u, w', ⟨x, hxn, hxM⟩, hw', rfl⟩, rfl⟩ := hvb
  change w' = 1 at hw'
  subst hw'
  change ylo = 0 at hlo
  subst hlo
  obtain ⟨v, e5, ⟨x5, hx5n, hx5M⟩, hve, he5, hy⟩ := hhi
  obtain rfl : x = a + 2 := names_uniq hxn (names_shift hl (by omega))
  obtain rfl : x5 = a + 5 := names_uniq hx5n (names_shift hl (by omega))
  have hv : v = gen ^ L := by rw [← hx5M, hL]
  rw [hve, ofK_gpow] at hv
  have he5' : e5 = L := by
    rw [Value.gen_pow_eq_ofK, Value.gen_pow_eq_ofK] at hv
    exact gpow_inj (by omega) (by omega) (ofK_injective hv)
  refine ⟨o, Nat.zero_le _, by omega, ?_⟩
  dsimp only
  rw [hq vq hvq, ← hxM, hE]
  simp only [ofK_gpow]
  ring

/-- A load's cell, named. -/
theorem names_of_load {r : Ref} (hr : r.Ok) {p v : E} {off : ℕ} (h : LoadHolds r.img.read p off v) :
    ∃ x, Names (p * ofK (Parameters.g ^ off)) x ∧ refMem r.img x = v := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff (by omega) r.img).mp h.2
  have hi28 : (i : ℕ) < 2 ^ 28 := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  have hrd : r.img.read (addressOfIndex i) = some v := by rw [← hi]; exact h.2
  obtain ⟨hlt, hM⟩ := ref_read hr (by omega) hrd
  exact ⟨i, ⟨by rw [B1.limb0_mul_ofK, hi], hlt⟩, hM⟩


/-! ## At the honest frames -/

section

variable {A : String → Bridge.FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- A base inside the frame. -/
theorem baseIn_fr {c : ℕ} (h : Res.baseIn j (.fr c) = true) : 2 ≤ c ∧ c < fsN j := by
  simpa [Res.baseIn] using h

theorem baseIn_hp {c d : ℕ} (h : Res.baseIn j (.hp c d) = true) : 2 ≤ c ∧ c < fsN j := by
  simpa [Res.baseIn] using h

/-- The gaps' product at the frame. -/
theorem gaps_val (t : TopAt A r K i e j) (hr : r.Ok) {vs : List V}
    (hF0 : FrameHolds r.img j e.I.fp e.σ (e.pre ++ e.es) vs e.I.kidFps e.I.hdr) {g0 jj n : ℕ}
    (hjj : jj < n) (hnamed : ∀ i < n, .n (g0 + 10 * i) ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs)
    (hin : ∀ p ∈ Res.gapBs j g0 jj, Res.baseIn j p.1 = true) (val : Base → E)
    (hval : ∀ c, val (.fr c) = refMem r.img (e.I.fp + c)) :
    ((Res.gapBs j g0 jj).map fun p => val p.1 ^ p.2) =
      (List.range (jj + 1)).map fun i => e.σ (.n (g0 + 10 * i)) ^ 4 := by
  unfold Res.gapBs
  rw [List.map_map]
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  obtain ⟨h2, hlt⟩ := baseIn_fr (hin _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  simp only [Function.comp, hval]
  rw [t.cell hr hF0 (hnamed i (by omega)) h2 hlt]

theorem gapBs_rbase {M : ℕ → E} {fp j g0 jj : ℕ} (val : Base → E) (hval : ∀ c, val (.fr c) = M (fp + c)) :
    ∀ p ∈ Res.gapBs j g0 jj, RBase M fp p.1 (val p.1) := by
  intro p hp
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
  exact (hval _).symm

/-- **A frame loop's read**: claim `jj`'s entry, from the record at offset `O`, lies below the next
record's offset, at most `L`. -/
theorem loopRead (t : TopAt A r K i e j) (hr : r.Ok) (hO : MonoOk) {f : String} {jf m p0 st0 cw ew : ℕ}
    (hfl : f = name% «child_claim_list_mono_loop0» ∨ f = name% «child_claim_list_mono_loop1»)
    (hidx : coreProgram.indexOf? f = some jf)
    (hok : monoOk (coreProgram.getD jf default) f m p0 st0 cw ew = true) (hcw : word cw 0 = gen ^ m)
    (hm136 : m ≤ 136) (hname : (coreOf j).name = f) {jj : ℕ} (hjj : jj < m) {q : Mono} (hq0 : q.fp = 0)
    (hqk : q.k = 4 * jj)
    (hbs : q.bs = (.fr (cellJ j (.n 12)), 1) :: Res.gapBs j 13 jj ∨
      q.bs = Res.gapBs j 13 jj ++ [(.fr (cellJ j (.n 12)), 1)])
    (hin : ∀ p ∈ Res.gapBs j 13 jj, Res.baseIn j p.1 = true)
    (hin12 : Res.baseIn j (.fr (cellJ j (.n 12))) = true) :
    RSub (refMem r.img) e.I.fp ⟨q, .num 0, .num 4, 1, 0⟩ Res.anyTab := by
  obtain ⟨f', bufs, kids, hIt⟩ := t.node
  have hj := t.idx
  rw [hIt] at hj
  obtain ⟨i', -, hi', hname', hfind, hc, -⟩ := fn_of_idx hj
  simp only [Tree.name] at hname' hfind
  obtain rfl : f' = f := by rw [← hname', ← hname, hc]
  have hfn : coreProgram[i'] = coreProgram.getD jf default :=
    Option.some.inj (hfind.symm.trans (find_of_idx hidx))
  obtain ⟨aP, L, n, qc, ⟨hh2, ha5, hm5, hL⟩, hq0', hqn, hn, hn1, hrec⟩ :=
    (monoQ_all hO hr e.I t.inst f' e.σ bufs kids hIt).1 hfl
  obtain ⟨vs, hw, hF0, hev⟩ := t.events hr
  have hfb := t.fb
  have hw' : Memory.walk e.σ (coreProgram.getD jf default).body = .ret (e.pre ++ e.es) vs := by
    rw [← hfn, ← hc]; exact hw
  simp only [monoOk, monoHead, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, -⟩, -⟩, -⟩, -⟩, hm10⟩, hl11⟩, hl12⟩, hoc⟩, -⟩, -⟩, hrecs⟩ := hok
  -- the body's atoms, on the path
  have hpath : ∀ a ∈ loopAtoms (coreProgram.getD jf default), Ev.atom a ∈ e.pre ++ e.es := by
    simp only [B1.Digest.loopShape, Bool.and_eq_true, decide_eq_true_eq] at hshape
    obtain ⟨-, hsp⟩ := hshape
    unfold loopAtoms
    split at hsp
    · rename_i atoms c g args hsl
      rw [hsl]
      rw [splitLoop_eq hsl] at hw'
      exact atoms_on_path' atoms hw'
    · exact absurd hsp (by simp)
  have hat : ∀ a ∈ loopAtoms (coreProgram.getD jf default), a.Holds r.img.read e.σ :=
    fun a ha ↦ hev _ (hpath a ha)
  have hnamed : ∀ a ∈ loopAtoms (coreProgram.getD jf default), ∀ x ∈ atomUses a,
      x ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := fun a ha x hx ↦ namedOf_atom (hpath a ha) hx
  -- the record's pointers
  have h10 : e.σ (.n 10) = e.σ (.n 2) * gen ^ (15 * qc) := by
    rw [monoIs_sound hm10 hat, hq0', gen_pow_pow]
  obtain ⟨O, hOL, h13, h14⟩ := hrec qc hqn.le
  rw [← h10] at h13 h14
  have h11 : e.σ (.n 11) = refMem r.img (aP + 3) * gen ^ O := loadHolds_unique (load_sound hl11 hat) h13
  have h12 : e.σ (.n 12) = refMem r.img (aP + 2) * gen ^ (4 * O) :=
    loadHolds_unique (load_sound hl12 hat) h14
  -- the walk
  obtain ⟨es, hes, hvals, hnz⟩ := monoWalk_vals (ref_memOk hr) hrecs hat
  have hreg : refMem r.img (aP + 3) ≠ 0 := fun h0 ↦ hnz (by omega) (by rw [h11, h0, zero_mul])
  obtain ⟨hlc, hcc⟩ := outOk_sound hoc hat
  obtain ⟨O', hO'L, h13', -⟩ := hrec (qc + 1) (by omega)
  have h28 : LoadHolds r.img.read (e.σ (.n 10)) 28 (refMem r.img (aP + 3) * gen ^ O') := by
    rw [h10, loadHolds_mul_gen_pow, show 15 * qc + 28 = 15 * (qc + 1) + 13 by ring, ← loadHolds_mul_gen_pow]
    exact h13'
  have heq := loadHolds_unique h28 hlc
  rw [hcc, (hvals m le_rfl).1, h11, hcw, mul_assoc, mul_assoc, ← pow_add, ← pow_add] at heq
  have hgs := gsum_le (fun i hi ↦ (hes i hi).1) m le_rfl
  have hO' : O' = O + (gsum es m + m) :=
    gen_pow_inj (by omega) (by omega) (mul_left_cancel₀ hreg heq)
  have hgjj := gsum_mono es (show jj + 1 ≤ m by omega)
  -- the read's product
  obtain ⟨a12, ha12, hp12⟩ := List.any_eq_true.mp hl12
  have hn12 : V.n 12 ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs := by
    cases a12 <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp12
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hp12
    exact hnamed _ ha12 _ (by simp [atomUses])
  obtain ⟨h2c, hltc⟩ := baseIn_fr hin12
  have hv12 := t.cell hr hF0 hn12 h2c hltc
  let val : Base → E := fun b => match b with
    | .fr c => refMem r.img (e.I.fp + c)
    | .hp _ _ => 0
  have hval : ∀ c, val (.fr c) = refMem r.img (e.I.fp + c) := fun _ ↦ rfl
  have hgap := gaps_val t hr hF0 hjj (fun i hi ↦ by
    obtain ⟨-, -, a, ha, hx⟩ := hes i hi
    exact hnamed a ha _ hx) hin val hval
  have hT : refMem r.img (e.I.fp + 1) = ofK (Parameters.g ^ aP) := by
    have := (ref_read hr (by omega) hF0.hdr1).2
    rw [this, hh2]
  refine tabRead_rsub (o := O + gsum es (jj + 1) + jj) hT ha5 rfl hm5 (fun vq hvq ↦ ?_) (by omega) hL
  obtain ⟨w, hw, rfl⟩ := hvq
  rw [bs_val val hbs rfl (gapBs_rbase val hval) w hw, hval, hgap, prod_gaps (fun i hi ↦ (hes i hi).2.1)
    (jj + 1) (by omega), hv12, h12, hq0, hqk]
  simp only [ofK_gpow]
  ring

/-- The parts of `mlOk` the reads use. -/
theorem mlOk_parts {k : ℕ} (hk0 : k ≠ 0) {F : Fn} (h : mlOk k F = true) :
    F.params = [.n 0, .n 1, .n 2, .n 3] ∧ ∃ (atoms : List Atom) (r0 r1 : V),
      F.body = atoms.map Stmt.atom ++ [.ret [r0, r1]] ∧
      atoms.any (isLoadAt (.n 4) (.n 0) 13) = true ∧ atoms.any (isLoadAt (.n 5) (.n 0) 14) = true ∧
      monoRecs atoms 2 6 4 5 (.n 2) k 0 k = true ∧
      (∃ c, mulOf atoms (.n (mlEnd k)) = some (.n (mCov 6 4 k), c) ∧ atoms.any (isConstAt c (2 ^ k) 0) = true) ∧
      ∃ tv, endOf atoms (.n (mlEnd k)) = some tv ∧ rcOf atoms tv = some (.n 3) := by
  simp only [mlOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpar, h⟩ := h
  refine ⟨hpar, ?_⟩
  split at h
  · rename_i atoms r0 r1 hsb
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hwalk⟩, hend⟩ := h
    simp only [hk0, ↓reduceIte, Bool.and_eq_true] at hwalk
    obtain ⟨⟨⟨hl4, hl5⟩, hrec⟩, hmul⟩ := hwalk
    refine ⟨atoms, r0, r1, splitBody_eq hsb, hl4, hl5, hrec, ?_, ?_⟩
    · split at hmul
      · rename_i a c hac
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmul
        obtain ⟨rfl, hc⟩ := hmul
        exact ⟨c, hac, hc⟩
      · exact absurd hmul (by simp)
    · split at hend
      · rename_i tv ht
        simp only [decide_eq_true_eq] at hend
        exact ⟨tv, ht, hend⟩
      · exact absurd hend (by simp)
  · exact absurd h (by simp)

/-- **The last claims' read**: claim `jj`'s entry, from the record at offset `O`, lies below the
walk's end, which the range check bounds by the exponent of `limit`. -/
theorem mlRead (t : TopAt A r K i e j) (hr : r.Ok) (hO : MonoOk) {k : ℕ} (hk17 : k < 17)
    (hname : (coreOf j).name = mlNames.getD k "") {jj : ℕ} (hjj : jj < k) {q : Mono} (hq0 : q.fp = 0)
    (hqk : q.k = 4 * jj)
    (hbs : q.bs = (.hp (cellJ j (.n 0)) 14, 1) :: Res.gapBs j 6 jj ∨
      q.bs = Res.gapBs j 6 jj ++ [(.hp (cellJ j (.n 0)) 14, 1)])
    (hin : ∀ p ∈ Res.gapBs j 6 jj, Res.baseIn j p.1 = true)
    (hin0 : Res.baseIn j (.hp (cellJ j (.n 0)) 14) = true) :
    RSub (refMem r.img) e.I.fp ⟨q, .num 0, .num 4, 1, 0⟩ Res.anyTab := by
  obtain ⟨f', bufs, kids, hIt⟩ := t.node
  have hj := t.idx
  rw [hIt] at hj
  obtain ⟨i', -, hi', hname', hfind, hc, -⟩ := fn_of_idx hj
  simp only [Tree.name] at hname' hfind
  obtain rfl : f' = mlNames.getD k "" := by rw [← hname', ← hname, hc]
  have hfn : coreProgram[i'] = coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default :=
    Option.some.inj (hfind.symm.trans (find_of_idx (ml_idx k hk17)))
  have hmem : mlNames.getD k "" ∈ mlNames := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [mlNames] using hk17)]
    exact List.getElem_mem _
  obtain ⟨aP, L, ⟨hh2, ha5, hm5, hL⟩, hσ3, hσ1, -, O, hOL, h13, h14⟩ :=
    (monoQ_all hO hr e.I t.inst _ e.σ bufs kids hIt).2.1 hmem
  obtain ⟨vs, hw, hF0, hev⟩ := t.events hr
  have hfb := t.fb
  have hw' : Memory.walk e.σ (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + k) default).body =
      .ret (e.pre ++ e.es) vs := by
    rw [← hfn, ← hc]; exact hw
  obtain ⟨hpar, atoms, r0, r1, hbody, hl4, hl5, hrecs, ⟨cm, hac, hcm⟩, tv, ht, hend⟩ :=
    mlOk_parts (by omega) (ml_all k hk17)
  rw [hbody] at hw'
  have hpath := atoms_on_path' atoms hw'
  have hat : ∀ a ∈ atoms, a.Holds r.img.read e.σ := fun a ha ↦ hev _ (hpath a ha)
  have hnamed : ∀ a ∈ atoms, ∀ x ∈ atomUses a, x ∈ namedOf (coreOf j).params (e.pre ++ e.es) vs :=
    fun a ha x hx ↦ namedOf_atom (hpath a ha) hx
  -- the record's pointers
  have h4 : e.σ (.n 4) = refMem r.img (aP + 3) * gen ^ O := loadHolds_unique (load_sound hl4 hat) h13
  have h5 : e.σ (.n 5) = refMem r.img (aP + 2) * gen ^ (4 * O) := loadHolds_unique (load_sound hl5 hat) h14
  -- the walk and its bound
  obtain ⟨es, hes, hvals, hnz⟩ := monoWalk_vals (ref_memOk hr) hrecs hat
  have hreg : refMem r.img (aP + 3) ≠ 0 := fun h0 ↦ hnz (by omega) (by rw [h4, h0, zero_mul])
  have hce : e.σ (.n (mlEnd k)) = refMem r.img (aP + 3) * gen ^ (O + (gsum es k + k)) := by
    rw [mulOf_sound hac hat, const_sound hcm hat, word_two_pow (by omega), (hvals k le_rfl).1, h4,
      pow_add, pow_add]
    ring
  obtain ⟨y, t1, t2, hy1, hy2, hy3⟩ := rcOf_sound hend hat
  obtain ⟨e0, e0', he0, he0', hx0, hk0'⟩ := rc_sound (ref_memOk hr) ⟨hy1, hy2, hy3⟩
  have hb := endOf_sound ht hat
  rw [hce, hx0, hσ1, mul_comm (gen ^ e0)] at hb
  have hgs := gsum_le (fun i hi ↦ (hes i hi).1) k le_rfl
  have hend' : O + (gsum es k + k) = e0 :=
    gen_pow_inj (by omega) (by omega) (mul_left_cancel₀ hreg hb)
  have hLe : L = e0 + e0' := gen_pow_inj (by omega) (by omega) (hσ3.symm.trans hk0')
  have hgjj := gsum_mono es (show jj + 1 ≤ k by omega)
  -- the read's product
  obtain ⟨h2c, hltc⟩ := baseIn_hp hin0
  have hc0 : refMem r.img (e.I.fp + cellJ j (.n 0)) = e.σ (.n 0) := by
    refine t.cell hr hF0 (List.mem_append_left _ (List.mem_append_left _ ?_)) h2c hltc
    rw [hc, hfn, hpar]; simp
  obtain ⟨x5, hx5, hM5⟩ := names_of_load hr (load_sound hl5 hat)
  let val : Base → E := fun b => match b with
    | .fr c => refMem r.img (e.I.fp + c)
    | .hp _ _ => e.σ (.n 5)
  have hval : ∀ c, val (.fr c) = refMem r.img (e.I.fp + c) := fun _ ↦ rfl
  have hent : RBase (refMem r.img) e.I.fp (.hp (cellJ j (.n 0)) 14) (val (.hp (cellJ j (.n 0)) 14)) :=
    ⟨x5, by rw [hc0]; exact hx5, hM5⟩
  have hgap := gaps_val t hr hF0 hjj (fun i hi ↦ by
    obtain ⟨-, -, a, ha, hx⟩ := hes i hi
    exact hnamed a ha _ hx) hin val hval
  have hT : refMem r.img (e.I.fp + 1) = ofK (Parameters.g ^ aP) := by
    have := (ref_read hr (by omega) hF0.hdr1).2
    rw [this, hh2]
  refine tabRead_rsub (o := O + gsum es (jj + 1) + jj) hT ha5 rfl hm5 (fun vq hvq ↦ ?_) (by omega) hL
  obtain ⟨w, hw, rfl⟩ := hvq
  rw [bs_val val hbs hent (gapBs_rbase val hval) w hw, hgap, prod_gaps (fun i hi ↦ (hes i hi).2.1)
    (jj + 1) (by omega), hq0, hqk]
  show _ * (e.σ (.n 5) * _) = _
  rw [h5]
  simp only [ofK_gpow]
  ring

/-- **A read of the walk at an honest frame.** -/
theorem monoRes_top (t : TopAt A r K i e j) (hr : r.Ok) (hO : MonoOk) {x : Mode.Res}
    (hx : Res.monoResB j x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub ⟨q, lo, hi, S, d⟩ bs, hx =>
    simp only [Res.monoResB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
    obtain ⟨⟨⟨⟨⟨⟨rfl, hq0⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hx⟩ := hx
    show RSub _ _ ⟨q, .num 0, .num 4, 1, 0⟩ Res.anyTab
    split at hx
    · rename_i g0 n entB hfam
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Bool.or_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hx
      obtain ⟨⟨⟨⟨hk4, hjj⟩, hbs⟩, hin⟩, hinE⟩ := hx
      have hqk : q.k = 4 * (q.k / 4) := by omega
      unfold Res.monoFam at hfam
      split_ifs at hfam with h0 h1
      · simp only [Option.some.injEq, Prod.mk.injEq] at hfam
        obtain ⟨rfl, rfl, rfl⟩ := hfam
        exact loopRead t hr hO (Or.inl rfl) mono136_idx mono136_ok word_g136 (by norm_num)
          (beq_iff_eq.mp h0) hjj hq0 hqk hbs hin hinE
      · simp only [Option.some.injEq, Prod.mk.injEq] at hfam
        obtain ⟨rfl, rfl, rfl⟩ := hfam
        exact loopRead t hr hO (Or.inr rfl) mono17_idx mono17_ok word_g17 (by norm_num)
          (beq_iff_eq.mp h1) hjj hq0 hqk hbs hin hinE
      · obtain ⟨k, hk, hkeq⟩ := Option.map_eq_some_iff.mp hfam
        simp only [Prod.mk.injEq] at hkeq
        obtain ⟨rfl, rfl, rfl⟩ := hkeq
        have hk17 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
        have hkn := List.find?_some hk
        simp only [beq_iff_eq] at hkn
        exact mlRead t hr hO hk17 hkn.symm hjj hq0 hqk hbs hin hinE
    · cases hx
  | .lt _ _, hx => simp [Res.monoResB] at hx
  | .nz _, hx => simp [Res.monoResB] at hx
  | .name _, hx => simp [Res.monoResB] at hx

end

/-- **The `sub` residuals open, less the walk's reads.** -/
theorem resOpen_mono {Ks : List Mode.Cert} {A : String → Bridge.FnAl} (hO : MonoOk)
    {p : ℕ → Mode.Res → Prop} (h : ResOpen Ks A fun j x ↦ p j x ∧ Res.monoResB j x = false) :
    ResOpen Ks A p := by
  intro r hr K hK i hi e j t x hx hp hin
  cases hb : Res.monoResB j x
  · exact h r hr K hK i hi e j t x hx ⟨hp, hb⟩ hin
  · exact monoRes_top t hr hO hb

end

end LeanVM.Guest.EndExec
