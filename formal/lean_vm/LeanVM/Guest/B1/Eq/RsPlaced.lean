/-
  LeanVM.Guest.B1.Eq.RsPlaced

  `rs_eq_run` is complete in the uniform placed form (`CompleteAtD`), its chain at the bump
  allocator's position and returned, and within a bound (`CompleteAtB`).
-/

module

public import LeanVM.Guest.B1.Eq.RsWords
public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«rs_eq_run»
import LeanVM.Guest.StmtsAppend

/-!
# `rs_eq_run`, placed

On the caller's words, `count < 64` coordinates `zs` at `g^bz` and `ps` at `g^bp`, `rs_eq_run` is
complete at every frame pointer: its chain (`HeapBuf` of `64 (count / 8 + 2)`
words) at `fp + fs "rs_eq_run"` holds the honest rows `rsChain` and is returned with the last row's
pointer (`RsOut`); its callees, `rs_eq_run_loop0` (entered unless `count < 8`) and the remainder's
`rs_eq_rows__L{count % 8}`, are pure, complete from their relations (`rs_kids_rel`), and its body
holds on its honest valuation (`rs_honest`). `rs_completeAtB`: within `Brs` words when the
callees' words are within the bounds `RsBound` names (on at most `34` coordinates).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The chain -/

/-- **The honest chain**: `64 (count / 8 + 2)` words, row `0` ones, row `h ≥ 1` the products over
the first `min (8h) count` coordinates. -/
def rsChain (zs ps : List E) (count : ℕ) : List E :=
  (List.range (64 * (count / 8 + 2))).map fun t ↦
    if t / 64 = 0 then 1
    else ringRow 1 (zs.take (min (8 * (t / 64)) count)) (ps.take (min (8 * (t / 64)) count)) (t % 64)

theorem rsChain_length (zs ps : List E) (count : ℕ) :
    (rsChain zs ps count).length = 64 * (count / 8 + 2) := by simp [rsChain]

/-- The chain's rows, read through `g^b`. -/
theorem rsChain_rows {rd : Reader} {zs ps : List E} {count b : ℕ}
    (h : ReadsAt rd (ofK (addressOfIndex b)) (rsChain zs ps count)) :
    (∀ k < 64, LoadHolds rd (ofK (addressOfIndex b)) k 1) ∧
    (∀ hh, 1 ≤ hh → hh ≤ (count + 7) / 8 → ∀ k < 64,
      LoadHolds rd (ofK (addressOfIndex b)) (64 * hh + k)
        (ringRow 1 (zs.take (min (8 * hh) count)) (ps.take (min (8 * hh) count)) k)) := by
  have hget : ∀ t (ht : t < 64 * (count / 8 + 2)), LoadHolds rd (ofK (addressOfIndex b)) t
      (if t / 64 = 0 then 1
        else ringRow 1 (zs.take (min (8 * (t / 64)) count)) (ps.take (min (8 * (t / 64)) count))
          (t % 64)) := by
    intro t ht
    have := h t (by rw [rsChain_length]; exact ht)
    simpa [rsChain] using this
  refine ⟨fun k hk ↦ ?_, fun hh h1 h2 k hk ↦ ?_⟩
  · have := hget k (by omega)
    rwa [ite_pos' (by omega : k / 64 = 0)] at this
  · have := hget (64 * hh + k) (by omega)
    rwa [ite_neg' (by omega : ¬ (64 * hh + k) / 64 = 0), show (64 * hh + k) / 64 = hh by omega,
      show (64 * hh + k) % 64 = k by omega] at this

/-- **What `rs_eq_run` returns**: the pointer to its chain's last row, the chain its buffer. -/
def RsOut (zs ps : List E) (count : ℕ) : List E → Main.Layout → Prop := fun rets L ↦
  ∃ b, rets = [ofK (addressOfIndex b) * gen ^ (64 * ((count + 7) / 8))] ∧ L = [(b, rsChain zs ps count)]

/-! ## The callees -/

/-- The callees' names: `rs_eq_run_loop0` and `rs_eq_rows__L{n}`, `n ≤ 8`. -/
def rsKidNames : List String := name% «rs_eq_run_loop0» :: rsEqRowsNames

theorem rsKid_pure : coreProgram.PureIn rsKidNames := Tables.pureIn_of_pureInB (by decide +kernel)

theorem rsRows_mem {r : ℕ} (hr : r < 8) : rsEqRowsNames.getD r "" ∈ rsKidNames := by
  interval_cases r <;> decide

/-- The words the callees read: the chain, the coordinates, the point. -/
def rsKLin (b bz bp count : ℕ) (zs ps : List E) : Main.Layout :=
  [(b, rsChain zs ps count), (bz, zs), (bp, ps)]

/-- The callees, the chain at `g^b`. -/
def rsKidsAt (b bz bp count : ℕ) (zs ps : List E) : List Kid :=
  [⟨name% «rs_eq_run_loop0», decide (1 + gen ^ (count / 8) ≠ 0),
      [1, gen ^ (count / 8), ofK (addressOfIndex b), ofK (addressOfIndex bz), ofK (addressOfIndex bp)],
      rsKLin b bz bp count zs ps, Returns []⟩,
    ⟨rsEqRowsNames.getD (count % 8) "", true,
      [ofK (addressOfIndex b) * gen ^ (64 * (count / 8)), ofK (addressOfIndex bz) * gen ^ (8 * (count / 8)),
        ofK (addressOfIndex bp) * gen ^ (8 * (count / 8))],
      rsKLin b bz bp count zs ps, Returns [ofK (addressOfIndex b) * gen ^ (64 * ((count + 7) / 8))]⟩]

theorem rsK_rel {rd : Reader} {b bz bp count : ℕ} {zs ps : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hL : MemL rd (rsKLin b bz bp count zs ps)) :
    (IsInK (1 + gen ^ (count / 8)) ∧ (1 + gen ^ (count / 8) ≠ 0 →
      coreProgram.Rel rd name% «rs_eq_run_loop0» [1, gen ^ (count / 8), ofK (addressOfIndex b),
        ofK (addressOfIndex bz), ofK (addressOfIndex bp)] [])) ∧
    coreProgram.Rel rd (rsEqRowsNames.getD (count % 8) "")
      [ofK (addressOfIndex b) * gen ^ (64 * (count / 8)), ofK (addressOfIndex bz) * gen ^ (8 * (count / 8)),
        ofK (addressOfIndex bp) * gen ^ (8 * (count / 8))]
      [ofK (addressOfIndex b) * gen ^ (64 * ((count + 7) / 8))] := by
  have hch := hL (b, rsChain zs ps count) (by simp [rsKLin])
  have hzs : ReadsAt rd (ofK (addressOfIndex bz)) zs := hL (bz, zs) (by simp [rsKLin])
  have hps : ReadsAt rd (ofK (addressOfIndex bp)) ps := hL (bp, ps) (by simp [rsKLin])
  obtain ⟨hone, hr⟩ := rsChain_rows hch
  exact rs_kids_rel hcount hz hp hzs hps hone hr

/-! ## The body -/

theorem rs_not_loop : coreProgram.loop "rs_eq_run" = false := by decide +kernel

theorem rs_addrs : rsPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem rs_noLoadIte : rsPre.all noLoadIte = true := by decide +kernel

theorem rs_loads : rsPre.filterMap Stmt.loadS =
    (List.range 64).map fun k ↦ ((.n (val% «rs_eq_run» "chain") : V), k) := by decide +kernel

theorem rs_body' : Fn.body fn% «rs_eq_run» = rsPre ⧺ [.ret [.n (val% «rs_eq_run» "s12#0")]] := by
  rw [rs_eq_run_body, rsBody_split]

theorem rs_params : Fn.params fn% «rs_eq_run» =
    [.n (val% «rs_eq_run» "z_vals"), .n (val% «rs_eq_run» "point1"), .n (val% «rs_eq_run» "count_g")] := rfl

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`rs_eq_run`'s honest valuation, placed**: on a memory holding its chain at `g^b` and the
caller's words, a valuation satisfying `completeAt_flatOutDTB`'s conditions. -/
theorem rs_hσ {b bz bp count : ℕ} {zs ps : List E} (hcount : count < 64) (hz : zs.length = count)
    (hp : ps.length = count) (outs : List (List E × Main.Layout)) (ho : OutsOk (rsKidsAt b bz bp count zs ps) outs)
    (rd : Reader) (hB : MemL rd [(b, rsChain zs ps count)]) (hLin : MemL rd [(bz, zs), (bp, ps)]) :
    ∃ σ : Val, (Fn.params fn% «rs_eq_run»).map σ =
        [ofK (addressOfIndex bz), ofK (addressOfIndex bp), gen ^ count] ∧ (∀ s ∈ rsPre, DispOk σ s) ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (Fn.body fn% «rs_eq_run») False
        (fun r => r = [ofK (addressOfIndex b) * gen ^ (64 * ((count + 7) / 8))]) ∧
      (rsPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) =
        [64 * (count / 8 + 2)] ∧
      ((rsPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b [64 * (count / 8 + 2)]).map (fun b => ofK (addressOfIndex b)) ∧
      CallsMatch σ ((rsPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (rsKidsAt b bz bp count zs ps)
        outs ∧
      ∀ q ∈ rsPre.flatMap (loadsEv σ), ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
        (RegionL [(bz, zs), (bp, ps)] i ∨ RegionL [(b, rsChain zs ps count)] i) := by
  have hch : ReadsAt rd (ofK (addressOfIndex b)) (rsChain zs ps count) := hB (b, rsChain zs ps count) (by simp)
  have hzs : ReadsAt rd (ofK (addressOfIndex bz)) zs := hLin (bz, zs) (by simp)
  have hps : ReadsAt rd (ofK (addressOfIndex bp)) ps := hLin (bp, ps) (by simp)
  obtain ⟨hone, hr⟩ := rsChain_rows hch
  obtain ⟨σ, hpar, hh, ech, e7, erg, eqg, e81, e82, erow, el1, el2, elast⟩ :=
    rs_honest hcount hz hp hzs hps hone hr
  have hr8 : count % 8 < 2 ^ 64 - 1 := by omega
  have hlog : logG (σ (.n (val% «rs_eq_run» "r_g@3"))) = count % 8 := by
    rw [erg, gen_pow_eq_ofK, logG_spec hr8]
  rcases outs with _ | ⟨o1, _ | ⟨o2, _ | ⟨o3, os⟩⟩⟩
  · exact absurd ho (by simp [OutsOk, rsKidsAt])
  · exact absurd ho (by simp [OutsOk, rsKidsAt])
  swap
  · exact absurd ho (by simp [OutsOk, rsKidsAt])
  obtain ⟨ho1, ho2, -⟩ := ho
  obtain ⟨ho2', -⟩ := ho2 rfl
  refine ⟨σ, by rw [rs_params]; exact hpar, rs_dispOk ⟨count % 8, by omega, by rw [erg, gen_pow_eq_ofK]⟩,
    by rw [rs_eq_run_body]; exact hh, ?_, ?_, ?_, ?_⟩
  · rw [rs_allocSz]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, e7, gen_pow_eq_ofK]
    rw [logG_spec (by omega)]
  · rw [rs_allocSz]
    simp [bases, ech]
  · rw [rs_callSF]
    have hpar' := hpar
    simp only [List.cons.injEq, and_true] at hpar'
    obtain ⟨ez, ep, -⟩ := hpar'
    refine ⟨rfl, ?_, fun ht ↦ ⟨?_, ((ho1 ht).1).symm⟩, ?_, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
    · show decide (σ (.n (val% «rs_eq_run» "s8#1")) ≠ 0) = _
      rw [e81]
    · show [σ (.n (val% «rs_eq_run» "s8#2")), σ (.n (val% «rs_eq_run» "q_g@3")), σ (.n (val% «rs_eq_run» "chain")), σ (.n (val% «rs_eq_run» "z_vals")),
        σ (.n (val% «rs_eq_run» "point1"))] = _
      rw [e82, eqg, ech, ez, ep]
    · show ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
        "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD (logG (σ (.n (val% «rs_eq_run» "r_g@3")))) "" = _
      rw [hlog, rsNames_getD _ (by omega)]
    · show [σ (.n (val% «rs_eq_run» "row")), σ (.n (val% «rs_eq_run» "last~1")), σ (.n (val% «rs_eq_run» "last~2"))] = _
      rw [erow, el1, el2]
    · show [σ (.n (val% «rs_eq_run» "last"))] = _
      rw [elast, ho2']
  · intro q hq
    rw [flatMap_loadsEv σ rsPre rs_noLoadIte, rs_loads] at hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have hk' := List.mem_range.mp hk
    refine ⟨b + k, by rw [ech, Main.addr_ofK], Or.inr ⟨_, List.mem_singleton_self _, by simp, ?_⟩⟩
    simp only [rsChain_length]
    omega

/-- The callees' words lie among the caller's and the chain's. -/
theorem rsKids_region {b bz bp count : ℕ} {zs ps : List E} :
    ∀ k ∈ rsKidsAt b bz bp count zs ps, ∀ i, RegionL k.Lin i →
      RegionL [(bz, zs), (bp, ps)] i ∨ RegionL (bufL b [64 * (count / 8 + 2)] [rsChain zs ps count]) i := by
  intro k hk i hi
  simp only [rsKidsAt, List.mem_cons, List.not_mem_nil, or_false] at hk
  obtain ⟨q, hq, hi⟩ := hi
  have hq' : q ∈ rsKLin b bz bp count zs ps := by rcases hk with rfl | rfl <;> exact hq
  simp only [rsKLin, List.mem_cons, List.not_mem_nil, or_false] at hq'
  rcases hq' with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [bufL, bases], hi⟩
  · exact Or.inl ⟨_, by simp, hi⟩
  · exact Or.inl ⟨_, by simp, hi⟩

/-- A memory holding the caller's words and the chain holds the callees'. -/
theorem rsKids_memL {rd : Reader} {b bz bp count : ℕ} {zs ps : List E}
    (hB : MemL rd (bufL b [64 * (count / 8 + 2)] [rsChain zs ps count])) (hLin : MemL rd [(bz, zs), (bp, ps)]) :
    ∀ k ∈ rsKidsAt b bz bp count zs ps, MemL rd k.Lin := by
  have h : MemL rd (rsKLin b bz bp count zs ps) := by
    intro q hq
    simp only [rsKLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hB (b, rsChain zs ps count) (by simp [bufL, bases])
    · exact hLin (bz, zs) (by simp)
    · exact hLin (bp, ps) (by simp)
  intro k hk
  simp only [rsKidsAt, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> exact h

/-! ## Within a bound -/

/-- **`rs_eq_run`'s callees' words**: the skipped loop's tail within its frame, the loop's run within
`K6` per iteration and its frame, each remainder's `rs_eq_rows__L{r}` within `R`, and `rs_eq_run`'s
frame, those and its chain on at most `34` coordinates (`64 · 6`) within `Brs`. -/
def RsBound (fs : String → ℕ) (Brs : ℕ) : Prop :=
  (∀ f, fs (Memory.tailKey f) ≤ fs f) ∧ ∃ K6 R : ℕ,
    TotalLeOn coreProgram fs name% «rs_eq_run_loop0» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K6 + fs name% «rs_eq_run_loop0») ∧
    (∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) ∧
    fs "rs_eq_run" + (fs name% «rs_eq_run_loop0» + 4 * K6) + R + 384 ≤ Brs

/-- **`rs_eq_run` is complete, placed, within `Brs` words** on at most `34` coordinates, its
callees' words as `RsBound` says. -/
theorem rs_completeAtB (κ : ℕ) {bz bp count : ℕ} {zs ps : List E} (hc34 : count ≤ 34)
    (hz : zs.length = count) (hp : ps.length = count) {Brs : ℕ} (hBrs : RsBound fs Brs) :
    CompleteAtB fs cert κ "rs_eq_run" [(bz, zs), (bp, ps)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), gen ^ count] (RsOut zs ps count) Brs := by
  obtain ⟨htl, K6, R, h6, hR, hle⟩ := hBrs
  have hcount : count < 64 := by omega
  refine ((completeAt_flatOutDTB (fs := fs) (cert := cert) find_rs_eq_run rs_not_loop κ _ _
    (fun fp ↦ [ofK (addressOfIndex (fp + fs "rs_eq_run")) * gen ^ (64 * ((count + 7) / 8))]) _ rs_body'
    rs_flat rs_addrs [64 * (count / 8 + 2)] (fun _ ↦ [rsChain zs ps count])
    (fun _ ↦ by simp [rsChain_length]) (fun fp ↦ ⟨_, rfl, by simp [bufL, bases]⟩)
    (fun fp ↦ rsKidsAt (fp + fs "rs_eq_run") bz bp count zs ps) (fun _ ↦ True)
    [fun _ ↦ True, fun _ ↦ True] [count / 8 * K6 + fs name% «rs_eq_run_loop0», R]
    (fs name% «rs_eq_run_loop0» + count / 8 * K6 + R) ?_ ?_ (fun _ ↦ by simp [rsKidsAt])
    (fun _ k hk _ ↦ rsKids_region k hk) (fun _ _ hB hLin ↦ rsKids_memL hB hLin)
    (fun fp outs ho rd _ hB hLin ↦ by
      obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ :=
        rs_hσ hcount hz hp outs ho rd (by simpa [bufL, bases] using hB) hLin
      exact ⟨σ, h1, h2, h3, h4, h5, h6, h7, trivial⟩)).toCompleteAtB).mono le_rfl ?_
  · intro fp
    refine ⟨fun ht ↦ ?_, fun _ ↦ ?_, trivial⟩
    · simp only [decide_eq_true_eq] at ht
      have hq0 : 0 < count / 8 := by
        rcases Nat.eq_zero_or_pos (count / 8) with h0 | h0
        · exact absurd (by rw [h0, pow_zero]; exact e_add_self 1) ht
        · exact h0
      refine (completeAt_of_rel_pureBat rsKid_pure (by simp [rsKidNames])
        (fun rd hL ↦ (rsK_rel hcount hz hp hL).1.2 ht) κ fun rd t hn hv hb ↦ ?_).toDTB
      have := h6 rd t _ _ hn (loopPre_gen hq0 (by omega) _) hv hb
      simp only [List.getD_cons_succ, List.getD_cons_zero, gen_pow_eq_ofK,
        logG_spec (show count / 8 < 2 ^ 64 - 1 by omega)] at this
      exact this
    · exact (completeAt_of_rel_pureBat rsKid_pure
        (rsRows_mem (by omega))
        (fun rd hL ↦ (rsK_rel hcount hz hp hL).2) κ fun rd t hn hv hb ↦
          hR _ (by omega) rd t _ _ hn hv hb).toDTB
  · intro fp
    have := htl name% «rs_eq_run_loop0»
    simp only [rsKidsAt, kidsBoundL, List.headD, List.tail, ↓reduceIte, add_zero]
    generalize count / 8 * K6 = X
    split <;> omega
  · have h4 := Nat.mul_le_mul_right K6 (show count / 8 ≤ 4 by omega)
    simp only [List.sum_cons, List.sum_nil, add_zero]
    generalize count / 8 * K6 = X at h4 ⊢
    omega

end
end LeanVM.Guest.B1
