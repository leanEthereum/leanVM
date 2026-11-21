/-
  LeanVM.Guest.B1.Ring.WeightComplete

  `rs_eq_run` and `ring_switch_weight` are complete in the uniform placed form (`CompleteAtD`):
  `rs_eq_run`'s chain at the bump allocator's position, returned with its last row;
  `ring_switch_weight` reading that row.
-/

module

public import LeanVM.Guest.B1.Ring.Weight
public import LeanVM.Guest.B1.Ring.TargetComplete
public import LeanVM.Guest.B1.Eq.RsWords
public import LeanVM.Guest.B1.Terminal.KidsDep
public import LeanVM.Guest.Data.NameStrings

/-!
# `rs_eq_run` and `ring_switch_weight`, placed (TRIAGE G #66)

On `n < 64` coordinates `zs` at `g^bz` and `ps` (the point's `1 + r'`) at `g^bp`, `rs_eq_run` is
complete at every frame pointer (`rs_completeAt`): its chain (`HeapBuf` of `64 (n / 8 + 2)` words,
by `allocDyn`) at the bump allocator's position holds the honest rows `rswChain` (row `0` its ones,
row `h ≥ 1` the products over the first `min (8h, n)` coordinates), its callees
`rs_eq_run_loop0` and `rs_eq_rows__L{n % 8}` (pure) are complete from their relations
(`rs_kids_rel`), its valuation is the honest one (`rsVal`), and it returns its last row's pointer
with the chain (`RsOut`). With the 64 coefficients `cs` at `g^bc`, `ring_switch_weight` is complete
at every frame pointer (`rsw_completeAt`): it calls `rs_eq_run` (a callee returning a buffer,
`completeAt_flatDepR`), reads the last row of the chain it returns and returns
`ringWeight zs (ps.map (1 + ·)) cs` (`ringWeight_eq`, `rwProd_eq_ringRow`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Core.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The honest chain -/

/-- The chain's last row: `⌈n/8⌉` (`RS_CHUNK = 8` coordinates a row). -/
def rswH (count : ℕ) : ℕ := (count + 7) / 8

/-- **The honest chain**: row `0` ones, row `h ≥ 1` the products over the first `min(2h, n)`
coordinates (`rs_eq_run`'s rows), up to row `⌈n/8⌉`. -/
def rswChain (zs ps : List E) (count : ℕ) : List E :=
  (List.range (64 * (rswH count + 1))).map fun t ↦
    if t / 64 = 0 then 1
    else ringRow 1 (zs.take (min (8 * (t / 64)) count)) (ps.take (min (8 * (t / 64)) count)) (t % 64)

theorem rswChain_length (zs ps : List E) (count : ℕ) :
    (rswChain zs ps count).length = 64 * (rswH count + 1) := by simp [rswChain]

theorem rswChain_get (zs ps : List E) (count : ℕ) {t : ℕ} (ht : t < (rswChain zs ps count).length) :
    (rswChain zs ps count)[t] = if t / 64 = 0 then 1
      else ringRow 1 (zs.take (min (8 * (t / 64)) count)) (ps.take (min (8 * (t / 64)) count))
        (t % 64) := by
  simp [rswChain]

theorem rswChain_le (zs ps : List E) (count : ℕ) :
    (rswChain zs ps count).length ≤ 64 * (count + 1) := by
  rw [rswChain_length, rswH]
  rcases Nat.eq_zero_or_pos count with rfl | h
  · simp
  · exact Nat.mul_le_mul_left _ (by omega)

/-- The chain read through `g^b`. -/
theorem rswChain_load {rd : Reader} {zs ps : List E} {count b : ℕ}
    (h : ReadsAt rd (ofK (addressOfIndex b)) (rswChain zs ps count)) {t : ℕ}
    (ht : t < 64 * (rswH count + 1)) :
    LoadHolds rd (ofK (addressOfIndex b)) t (if t / 64 = 0 then 1
      else ringRow 1 (zs.take (min (8 * (t / 64)) count)) (ps.take (min (8 * (t / 64)) count))
        (t % 64)) := by
  have := h t (by rw [rswChain_length]; exact ht)
  rwa [rswChain_get] at this

/-! ## `rs_eq_run`, placed -/

/-- `rs_eq_run`'s callees: `rs_eq_run_loop0` and `rs_eq_rows__L{n}`, `n ≤ 8`. -/
def rsPureNames : List String := [name% «rs_eq_run_loop0»] ++ rsEqRowsNames

theorem rs_pure : coreProgram.PureIn rsPureNames := Tables.pureIn_of_pureInB (by decide +kernel)

theorem rows_mem_pure (r : ℕ) (hr : r < 8) : rsEqRowsNames.getD r "" ∈ rsPureNames := by
  interval_cases r <;> simp [rsPureNames, rsEqRowsNames]

/-- `rs_eq_run`'s words: the chain, the coordinates, the point. -/
def rsLin (bb bz bp count : ℕ) (zs ps : List E) : Main.Layout :=
  [(bb, rswChain zs ps count), (bz, zs), (bp, ps)]

/-- The chain's words: `64 (count / 8 + 2)`. -/
def rsSize (count : ℕ) : ℕ := 64 * (count / 8 + 2)

theorem rswChain_le_size (zs ps : List E) (count : ℕ) :
    (rswChain zs ps count).length ≤ rsSize count := by
  rw [rswChain_length, rswH, rsSize]; omega

/-- **The words `rs_eq_run` runs on**, from its chain's honest rows. -/
theorem rsMem_of {rd : Reader} {bb bz bp count : ℕ} {zs ps : List E} (hz : zs.length = count)
    (hp : ps.length = count) (hL : MemL rd (rsLin bb bz bp count zs ps)) :
    RsMem rd (ofK (addressOfIndex bz)) (ofK (addressOfIndex bp)) (ofK (addressOfIndex bb)) count
      zs ps := by
  have hch : ReadsAt rd (ofK (addressOfIndex bb)) (rswChain zs ps count) :=
    hL (bb, rswChain zs ps count) (by simp [rsLin])
  refine ⟨hz, hp, hL (bz, zs) (by simp [rsLin]), hL (bp, ps) (by simp [rsLin]), fun k hk ↦ ?_,
    fun h hh1 hh2 k hk ↦ ?_⟩
  · simp only [List.length_replicate] at hk
    have := rswChain_load hch (t := k) (by rw [rswH]; omega)
    simp only [List.getElem_replicate]
    rwa [ite_pos' (by omega : k / 64 = 0)] at this
  · have := rswChain_load hch (t := 64 * h + k) (by unfold rswH; omega)
    rwa [ite_neg' (by omega : ¬ (64 * h + k) / 64 = 0), show (64 * h + k) / 64 = h by omega,
      show (64 * h + k) % 64 = k by omega] at this

/-- **What `rs_eq_run` returns**: its last row's pointer, its chain the buffer. -/
def RsOut (zs ps : List E) (count : ℕ) : List E → Main.Layout → Prop := fun rets L ↦
  ∃ b, rets = [ofK (addressOfIndex b) * gen ^ (64 * rswH count)] ∧ L = [(b, rswChain zs ps count)]

/-- `rs_eq_run`'s callees, its chain at `g^bb`: the loop over the full chunks (entered unless
`count < 8`), the remainder's rows. -/
noncomputable def rsKids (bb bz bp count : ℕ) (zs ps : List E) : List Kid :=
  [⟨name% «rs_eq_run_loop0», decide (1 + gen ^ (count / 8) ≠ 0),
      [1, gen ^ (count / 8), ofK (addressOfIndex bb), ofK (addressOfIndex bz),
        ofK (addressOfIndex bp)], rsLin bb bz bp count zs ps, Returns []⟩,
    ⟨rsEqRowsNames.getD (count % 8) "", true,
      [ofK (addressOfIndex bb) * gen ^ (64 * (count / 8)), ofK (addressOfIndex bz) * gen ^ (8 * (count / 8)),
        ofK (addressOfIndex bp) * gen ^ (8 * (count / 8))], rsLin bb bz bp count zs ps,
      Returns [ofK (addressOfIndex bb) * gen ^ (64 * rswH count)]⟩]

theorem rs_not_loop : coreProgram.loop "rs_eq_run" = false := by decide +kernel

theorem rs_body' : Fn.body fn% «rs_eq_run» = (rsA ++ rsT) ++ [.ret [.n 130]] := by
  rw [rs_eq_run_body, rsBody_split]

theorem rs_addrs : (rsA ++ rsT).filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem rs_notIte : (rsA ++ rsT).all rtNotIte = true := by decide +kernel

theorem rs_loadS : (rsA ++ rsT).filterMap Stmt.loadS = (List.range 64).map fun k ↦ (.n 49, k) := by
  decide +kernel

theorem rs_rows_name (count : ℕ) :
    ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"].getD
        (logG (gen ^ (count % 8))) "" = rsEqRowsNames.getD (count % 8) "" := by
  rw [gen_pow_eq_ofK, logG_spec (by omega)]
  exact rsNames_getD _ (by omega)

/-- **`rs_eq_run`'s honest valuation on its words**: what a flat function's placed completeness
asks of it, the chain at `g^bb`. -/
theorem rs_hσ {rd : Reader} {bb bz bp count : ℕ} {zs ps : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) {outs : List (List E × Main.Layout)}
    (ho : OutsOk (rsKids bb bz bp count zs ps) outs) (hL : MemL rd (rsLin bb bz bp count zs ps)) :
    ∃ σ : Val, (Fn.params fn% «rs_eq_run»).map σ =
        [ofK (addressOfIndex bz), ofK (addressOfIndex bp), gen ^ count] ∧
      (∀ s ∈ rsA ++ rsT, DispOk σ s) ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (Fn.body fn% «rs_eq_run») False
        (fun r ↦ r = [ofK (addressOfIndex bb) * gen ^ (64 * rswH count)]) ∧
      ((rsA ++ rsT).filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) =
        [rsSize count] ∧
      (((rsA ++ rsT).filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        [ofK (addressOfIndex bb)] ∧
      CallsMatch σ (((rsA ++ rsT).filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (rsKids bb bz bp count zs ps) outs ∧
      ∀ q ∈ (rsA ++ rsT).flatMap (loadsEv σ), ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
        addressOfIndex i ∧ RegionL [(bb, rswChain zs ps count)] i := by
  refine ⟨rsVal (ofK (addressOfIndex bz)) (ofK (addressOfIndex bp)) (ofK (addressOfIndex bb)) count,
    ?_⟩
  obtain ⟨e0, e1, e2, e36, e22, e48, e49, e115, e116, e126, e127, e128, e129, -, -⟩ :=
    rsVal_vals (ofK (addressOfIndex bz)) (ofK (addressOfIndex bp)) (ofK (addressOfIndex bb)) hcount
  rcases outs with _ | ⟨o1, _ | ⟨o2, _ | ⟨o3, os⟩⟩⟩
  · exact absurd ho (by simp [OutsOk, rsKids])
  · exact absurd ho (by simp [OutsOk, rsKids])
  swap
  · exact absurd ho.2.2 (by simp [OutsOk])
  obtain ⟨ho1, ho2, -⟩ := ho
  refine ⟨?_, rs_dispOk ⟨count % 8, by omega, by rw [e22, gen_pow_eq_ofK]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show [rsVal _ _ _ count (.n 0), rsVal _ _ _ count (.n 1), rsVal _ _ _ count (.n 2)] = _
    rw [e0, e1, e2]
  · rw [rs_eq_run_body]
    exact rsVal_holds hcount (rsMem_of hz hp hL)
  · rw [rs_allocSz]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, e48, gen_pow_eq_ofK, rsSize]
    rw [logG_spec (by omega)]
  · rw [rs_allocSz]
    simp only [List.map_cons, List.map_nil, e49]
  · rw [rs_callSF, e22, rs_rows_name count]
    simp only [List.map_cons, List.map_nil, Main.mkCall, rsKids]
    refine ⟨rfl, by rw [e115], fun ht ↦ ⟨?_, ?_⟩, rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
    · simp only [List.map_cons, List.map_nil, e116, e36, e49, e0, e1]
    · exact ((ho1 ht).1).symm
    · simp only [List.map_cons, List.map_nil, e126, e127, e128]
    · simp only [List.map_cons, List.map_nil, e129]
      rw [(ho2 rfl).1]; rfl
  · intro q hq
    have hq' := rt_filterMap_of_loadsEv rs_notIte hq
    rw [rs_loadS] at hq'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq'
    have hk' := List.mem_range.mp hk
    refine ⟨bb + k, ?_, ⟨_, List.mem_singleton_self _, Nat.le_add_right bb k, ?_⟩⟩
    · show (rsVal _ _ _ count (.n 49)).limb 0 * addressOfIndex k = _
      rw [e49, Main.addr_ofK]
    · show bb + k < bb + (rswChain zs ps count).length
      rw [rswChain_length]; omega

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The callees' words: the caller's and the chain. -/
theorem rs_kids_region {bb bz bp count : ℕ} {zs ps : List E} {L : Main.Layout}
    (hL : (bz, zs) ∈ L ∧ (bp, ps) ∈ L) :
    ∀ k ∈ rsKids bb bz bp count zs ps, ∀ i, RegionL k.Lin i →
      RegionL L i ∨ RegionL [(bb, rswChain zs ps count)] i := by
  intro k hk i hi
  have hkL : k.Lin = rsLin bb bz bp count zs ps := by
    simp only [rsKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> rfl
  rw [hkL] at hi
  obtain ⟨q, hq, hi⟩ := hi
  simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact Or.inr ⟨_, List.mem_singleton_self _, hi⟩
  · exact Or.inl ⟨_, hL.1, hi⟩
  · exact Or.inl ⟨_, hL.2, hi⟩

theorem rs_kids_mem {rd : Reader} {bb bz bp count : ℕ} {zs ps : List E} {L : Main.Layout}
    (hL : (bz, zs) ∈ L ∧ (bp, ps) ∈ L) (hB : MemL rd [(bb, rswChain zs ps count)]) (hLin : MemL rd L) :
    ∀ k ∈ rsKids bb bz bp count zs ps, MemL rd k.Lin := by
  intro k hk q hq
  have hkL : k.Lin = rsLin bb bz bp count zs ps := by
    simp only [rsKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> rfl
  rw [hkL] at hq
  simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact hB _ (List.mem_singleton_self _)
  · exact hLin _ hL.1
  · exact hLin _ hL.2

theorem bufL_rs (b count : ℕ) (zs ps : List E) :
    bufL b [rsSize count] [rswChain zs ps count] = [(b, rswChain zs ps count)] := by
  simp [bufL, bases]

/-- **`rs_eq_run` is complete, placed**: on the coordinates and the point, at every frame
pointer, its chain at the bump allocator's position, returning its last row with the chain. -/
theorem rs_completeAt (κ : ℕ) {bz bp count : ℕ} {zs ps : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) :
    CompleteAtD fs cert κ "rs_eq_run" [(bz, zs), (bp, ps)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), gen ^ count] (RsOut zs ps count) := by
  refine completeAt_flatOutD (fs := fs) (cert := cert) find_rs_eq_run rs_not_loop κ _ _
    (fun fp ↦ [ofK (addressOfIndex (fp + fs "rs_eq_run")) * gen ^ (64 * rswH count)]) _ rs_body'
    rs_flat rs_addrs [rsSize count] (fun _ ↦ [rswChain zs ps count])
    (fun _ ↦ by simpa using rswChain_le_size zs ps count)
    (fun fp ↦ ⟨_, rfl, bufL_rs _ _ _ _⟩)
    (fun fp ↦ rsKids (fp + fs "rs_eq_run") bz bp count zs ps) ?_ ?_ ?_ ?_
  · intro fp k hk ht
    simp only [rsKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp only [decide_eq_true_eq] at ht
      exact completeAt_of_rel_pureD rs_pure (by simp [rsPureNames])
        (fun rd hL ↦ (rs_kids_rel hcount (rsMem_of hz hp hL)).1.2 ht) κ
    · exact completeAt_of_rel_pureD rs_pure (rows_mem_pure _ (by omega))
        (fun rd hL ↦ (rs_kids_rel hcount (rsMem_of hz hp hL)).2) κ
  · intro fp k hk _ i hi
    rw [bufL_rs]
    exact rs_kids_region ⟨by simp, by simp⟩ k hk i hi
  · intro fp rd hB hLin
    rw [bufL_rs] at hB
    exact rs_kids_mem ⟨by simp, by simp⟩ hB hLin
  · intro fp outs ho rd _ hB hLin
    rw [bufL_rs] at hB ⊢
    have hL : MemL rd (rsLin (fp + fs "rs_eq_run") bz bp count zs ps) := by
      intro q hq
      simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      exacts [hB _ (by simp), hLin _ (by simp), hLin _ (by simp)]
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := rs_hσ hcount hz hp ho hL
    refine ⟨_, h1, h2, h3, h4, by rw [h5]; simp [bases], h6, fun q hq ↦ ?_⟩
    obtain ⟨i, hi, hr⟩ := h7 q hq
    exact ⟨i, hi, Or.inr hr⟩

/-! ## `ring_switch_weight`'s body -/

theorem rsw_chk : chk 4 rswT = some 261 := by decide +kernel

theorem rsw_stores : storesOf 4 rswT = [] := by decide +kernel

/-- `ring_switch_weight`'s statements before its `ret`. -/
def rswPre : List Stmt :=
  [.call "rs_eq_run" [.n 0, .n 1, .n 3] [.n 4]] ++ ((List.range 64).map rswTerm).flatten ++
    [.atom (.copy (.n 260) (.n 259))]

theorem rswT_split : rswT = rswPre ++ [.ret [.n 260]] := by
  simp only [rswT, rswPre, List.append_assoc, List.cons_append, List.nil_append]

theorem rsw_body' : Fn.body fn% «ring_switch_weight» = rswPre ++ [.ret [.n 260]] := by
  rw [show Fn.body fn% «ring_switch_weight» = rswT from rsw_body, rswT_split]

theorem rsw_flat : rswPre.all Stmt.flat = true := by decide +kernel

theorem rsw_addrs : rswPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem rsw_allocs : rswPre.filterMap Main.Stmt.allocSz = [] := by decide +kernel

theorem rsw_not_loop : coreProgram.loop "ring_switch_weight" = false := by decide +kernel

theorem rsw_notIte : rswPre.all notIteB = true := by decide +kernel

/-- The loads `ring_switch_weight` makes: the coefficients (`2`), `rs_eq_run`'s last row (`4`). -/
def rswLoadOk : Atom → Bool
  | .load _ p off => decide (off < 64) && (decide (p = .n 2) || decide (p = .n 4))
  | _ => true

/-- The atoms of `ring_switch_weight`'s statements. -/
def rswA : List Atom := rswPre.filterMap fun s => match s with | .atom a => some a | _ => none

theorem rsw_loadOk : rswA.all rswLoadOk = true := by decide +kernel

theorem rsw_needs : rswA.all (fun a => !needsSide a ||
    (match a with | .load _ p _ => decide (p = .n 2) || decide (p = .n 4) | _ => false)) = true := by
  decide +kernel

theorem rsw_atom_mem {a : Atom} (h : Stmt.atom a ∈ rswPre) : a ∈ rswA :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem rsw_mem_atom {a : Atom} (h : a ∈ rswA) : Stmt.atom a ∈ rswPre := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem rswTerm_mem {k : ℕ} (hk : k < 64) (s : Stmt) (hs : s ∈ rswTerm k) : s ∈ rswPre := by
  simp only [rswPre, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨rswTerm k, ⟨k, hk, rfl⟩, hs⟩)

/-! ## The honest valuation -/

/-- The oracle of `ring_switch_weight`'s body: `rs_eq_run`'s return. -/
noncomputable def rswW (row : E) : ℕ → E := fun i => if i = 4 then row else 0

/-- The evaluated valuation of `ring_switch_weight`'s body. -/
noncomputable def rswσ (rd : Reader) (args : List E) (row : E) : Val :=
  B1.Val.ofArgs (ev rd (rswW row) args rswT)

/-- **`ring_switch_weight`'s statements hold** on their evaluated valuation, over the coefficients
and the last row of the chain `rs_eq_run` returns at `g^bb`. -/
theorem rsw_block {rd : Reader} {bz bp bc bb count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64)
    (hcs : ReadsAt rd (ofK (addressOfIndex bc)) cs)
    (hch : ReadsAt rd (ofK (addressOfIndex bb)) (rswChain zs ps count)) :
    ∃ σ : Val, (∀ a ∈ rswA, a.Holds rd σ) ∧ σ (.n 0) = ofK (addressOfIndex bz) ∧
      σ (.n 1) = ofK (addressOfIndex bp) ∧ σ (.n 2) = ofK (addressOfIndex bc) ∧
      σ (.n 3) = gen ^ count ∧ σ (.n 4) = ofK (addressOfIndex bb) * gen ^ (64 * rswH count) ∧
      σ (.n 260) = ringWeight zs (ps.map (1 + ·)) cs := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp),
      ofK (addressOfIndex bc), gen ^ count] (ofK (addressOfIndex bb) * gen ^ (64 * rswH count)) :=
    ⟨_, rfl⟩
  refine ⟨σ, ?_⟩
  have hpar : ∀ i (hi : i < 4), σ (.n i) = [ofK (addressOfIndex bz), ofK (addressOfIndex bp),
      ofK (addressOfIndex bc), gen ^ count].getD i 0 := by
    intro i hi
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp),
      ofK (addressOfIndex bc), gen ^ count]) rsw_chk (by simpa using hi)
  have e0 := hpar 0 (by omega)
  have e1 := hpar 1 (by omega)
  have e2 := hpar 2 (by omega)
  have e3 := hpar 3 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3
  obtain ⟨-, -, hgs⟩ := ev_spec rd (rswW (ofK (addressOfIndex bb) * gen ^ (64 * rswH count))) rswT
    [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
    rsw_chk
  rw [show [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^
      count].length = 4 from rfl, rsw_stores, ← rswσ, ← hσdef] at hgs
  have hgS : ∀ s ∈ rswPre, GoodS rd [] (rswW (ofK (addressOfIndex bb) * gen ^ (64 * rswH count)))
      σ s := fun s hs => hgs s (by rw [rswT_split]; exact List.mem_append_left _ hs)
  have hg : ∀ a ∈ rswA, Good rd [] (rswW (ofK (addressOfIndex bb) * gen ^ (64 * rswH count))) σ a :=
    fun a ha => hgS _ (rsw_mem_atom ha)
  have mulE : ∀ d u v : ℕ, u < d → v < d → Stmt.atom (.mul (.n d) (.n u) (.n v)) ∈ rswPre →
      σ (.n d) = σ (.n u) * σ (.n v) := by
    intro d u v hu hv hm
    have := hg _ (rsw_atom_mem hm)
    simp only [Good] at this
    rwa [ite_pos' ⟨hu, hv⟩] at this
  have e4 : σ (.n 4) = ofK (addressOfIndex bb) * gen ^ (64 * rswH count) := by
    have := hgS (.call "rs_eq_run" [.n 0, .n 1, .n 3] [.n 4]) (by simp [rswPre])
    simpa [GoodS, rswW] using this
  have loadE : ∀ d p off, Stmt.atom (.load (.n d) p off) ∈ rswPre →
      σ (.n d) = rdAt rd (σ p) off := by
    intro d p off hm
    rcases (hg _ (rsw_atom_mem hm) : Good rd [] _ σ _) with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  -- the coefficients and the chain's last row
  have hrowH : ∀ k < 64, LoadHolds rd (σ (.n 4)) k (ringRow 1 zs ps k) := by
    intro k hk
    rw [e4, loadHolds_mul_gen_pow]
    have := rswChain_load hch (t := 64 * rswH count + k) (by omega)
    rcases Nat.eq_zero_or_pos count with h0 | hpos
    · subst h0
      have hz0 : zs = [] := List.length_eq_zero_iff.mp hz
      have hp0 : ps = [] := List.length_eq_zero_iff.mp hp
      subst hz0 hp0
      simp only [rswH, Nat.zero_add, Nat.reduceDiv, mul_zero, Nat.zero_add] at this ⊢
      rw [ite_pos' (by omega)] at this
      simpa [ringRow] using this
    · have hH : 1 ≤ rswH count := by unfold rswH; omega
      rw [ite_neg' (by omega), show (64 * rswH count + k) / 64 = rswH count by omega,
        show (64 * rswH count + k) % 64 = k by omega,
        show min (8 * rswH count) count = count by unfold rswH; omega,
        List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this
      exact this
  have hcsk : ∀ k < 64, LoadHolds rd (σ (.n 2)) k (cs.getD k 0) := by
    intro k hk
    rw [e2, List.getD_eq_getElem _ _ (by omega)]
    exact hcs k (by omega)
  have hterm : ∀ k < 64, σ (.n (rswC k)) = cs.getD k 0 ∧ σ (.n (rswP k)) = ringRow 1 zs ps k ∧
      σ (.n (rswM k)) = σ (.n (rswC k)) * σ (.n (rswP k)) ∧
      (k ≠ 0 → σ (.n (4 * k + 7)) = σ (.n (4 * (k - 1) + 7)) + σ (.n (rswM k))) := by
    intro k hk
    have mem := rswTerm_mem hk
    unfold rswTerm at mem
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte] at mem
      have l1 := loadE 5 (.n 2) 0 (mem _ (by simp))
      have l2 := loadE 6 (.n 4) 0 (mem _ (by simp))
      have m := mulE 7 5 6 (by omega) (by omega) (mem _ (by simp))
      refine ⟨?_, ?_, m, fun h ↦ absurd rfl h⟩
      · rw [show rswC 0 = 5 from rfl, l1, rt_rdAt_of_load (hcsk 0 (by omega))]
      · rw [show rswP 0 = 6 from rfl, l2, rt_rdAt_of_load (hrowH 0 (by omega))]
    · simp only [hk0, ↓reduceIte] at mem
      have l1 := loadE (4 * k + 4) (.n 2) k (mem _ (by simp))
      have l2 := loadE (4 * k + 5) (.n 4) k (mem _ (by simp))
      have m := mulE (4 * k + 6) (4 * k + 4) (4 * k + 5) (by omega) (by omega) (mem _ (by simp))
      have a := (hg _ (rsw_atom_mem (mem (.atom (.add (.n (4 * k + 7)) (.n (4 * k + 3))
        (.n (4 * k + 6)))) (by simp))) : σ (.n (4 * k + 7)) = σ (.n (4 * k + 3)) +
          σ (.n (4 * k + 6)))
      simp only [rswC, rswP, rswM, hk0, ↓reduceIte]
      refine ⟨by rw [l1, rt_rdAt_of_load (hcsk k hk)], by rw [l2, rt_rdAt_of_load (hrowH k hk)], m,
        fun _ ↦ ?_⟩
      rw [a, show 4 * (k - 1) + 7 = 4 * k + 3 by omega]
  -- the atoms
  have hside : ∀ a ∈ rswA, a ∉ ([] : List Atom) → needsSide a = true →
      a.Holds rd σ ∨ Side rd [] σ a := by
    intro a ha _ hns
    right
    have hok := List.all_eq_true.mp rsw_needs a ha
    have hld := List.all_eq_true.mp rsw_loadOk a ha
    simp only [hns, Bool.not_true, Bool.false_or] at hok
    cases a with
    | load d p off =>
      simp only [rswLoadOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hld hok
      simp only [Side, List.not_mem_nil, ↓reduceIte]
      rcases hok with rfl | rfl
      · exact rt_side_of_load (hcsk off hld.1)
      · exact rt_side_of_load (hrowH off hld.1)
    | _ => simp at hok
  have hat : ∀ a ∈ rswA, a.Holds rd σ :=
    atoms_holds_stores (S := []) hg hside (fun _ a _ haS => absurd haS List.not_mem_nil)
  refine ⟨hat, e0, e1, e2, e3, e4, ?_⟩
  have hcopy : σ (.n 260) = σ (.n 259) :=
    hg _ (rsw_atom_mem (by simp [rswPre] : Stmt.atom (.copy (.n 260) (.n 259)) ∈ rswPre))
  rw [hcopy, show (259 : ℕ) = 4 * 63 + 7 from rfl,
    rsw_acc (fun k hk => (hterm k hk).2.2.2) 63 (by decide), ringWeight_eq, hc]
  refine gsum_congr fun k hk => ?_
  rw [(hterm k hk).2.2.1, (hterm k hk).1, (hterm k hk).2.1,
    rwProd_eq_ringRow k zs ps _ (by rw [hz, hp])]

/-! ## `ring_switch_weight`, placed -/

theorem rsw_kinds : rswPre.all atomOrCall = true := by decide +kernel

theorem rsw_callS : rswPre.filterMap Main.Stmt.callS =
    [(none, "rs_eq_run", [.n 0, .n 1, .n 3], [.n 4])] := by decide +kernel

theorem rsw_callSF (σ : Val) : rswPre.filterMap (Stmt.callSF σ) =
    [(none, "rs_eq_run", [.n 0, .n 1, .n 3], [.n 4])] := by
  rw [← rsw_callS]
  refine List.filterMap_congr fun s hs => ?_
  have := List.all_eq_true.mp rsw_kinds s hs
  cases s <;> simp_all [Stmt.callSF, atomOrCall]

theorem rsw_loads_ok {q : V × ℕ} (hq : q ∈ rswPre.filterMap Stmt.loadS) :
    q.2 < 64 ∧ (q.1 = .n 2 ∨ q.1 = .n 4) := by
  obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
  cases s with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Stmt.loadS, Option.some.injEq] at hsq
      subst hsq
      have := List.all_eq_true.mp rsw_loadOk _ (rsw_atom_mem hs)
      simp only [rswLoadOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1, this.2⟩
    | _ => simp [Stmt.loadS] at hsq
  | _ => simp [Stmt.loadS] at hsq

/-- `ring_switch_weight`'s callee: `rs_eq_run` on the coordinates and the point. -/
noncomputable def rswKid (bz bp count : ℕ) (zs ps : List E) : KidD := fun _ ↦
  ⟨"rs_eq_run", true, [ofK (addressOfIndex bz), ofK (addressOfIndex bp), gen ^ count],
    [(bz, zs), (bp, ps)], RsOut zs ps count⟩

/-- **`ring_switch_weight`'s callee reads the caller's words.** -/
theorem rsw_regions {bz bp bc count : ℕ} {zs ps cs : List E} {R : ℕ → Prop}
    (hR : ∀ i, RegionL [(bz, zs), (bp, ps), (bc, cs)] i → R i) :
    ∀ outs : List (List E × Main.Layout),
      RegionsOk R (fun _ => False) (kidsAt [rswKid bz bp count zs ps] [] outs) outs
  | [] => trivial
  | o :: _ => ⟨fun _ i ⟨q, hq, hi⟩ ↦ Or.inl (hR i ⟨q, by
      simp only [rswKid, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp, hi⟩), trivial⟩

theorem rsw_lins {rd : Reader} {bz bp bc count : ℕ} {zs ps cs : List E}
    (hLin : MemL rd [(bz, zs), (bp, ps), (bc, cs)]) :
    ∀ outs : List (List E × Main.Layout),
      MemL rd (Kid.lins (kidsAt [rswKid bz bp count zs ps] [] outs))
  | [] => fun q hq => by simp [kidsAt, Kid.lins] at hq
  | o :: _ => fun q hq => by
    simp only [kidsAt, Kid.lins, List.flatMap_cons, List.flatMap_nil, List.append_nil, rswKid,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hLin _ (by simp)
    · exact hLin _ (by simp)

/-- **`ring_switch_weight`'s honest valuation**, on the chain `rs_eq_run` returns. -/
theorem rsw_hσ {rd : Reader} {bz bp bc count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64)
    (outs : List (List E × Main.Layout)) (hl : outs.length = 1)
    (ho : OutsOk (kidsAt [rswKid bz bp count zs ps] [] outs) outs)
    (hLin : MemL rd [(bz, zs), (bp, ps), (bc, cs)])
    (hLo : MemL rd (outsL (kidsAt [rswKid bz bp count zs ps] [] outs) outs)) :
    ∃ σ : Val, (Fn.params fn% «ring_switch_weight»).map σ =
        [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count] ∧
      (∀ s ∈ rswPre, DispOk σ s) ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ (Fn.body fn% «ring_switch_weight») False
        (fun r => r = [ringWeight zs (ps.map (1 + ·)) cs]) ∧
      (rswPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = [] ∧
      ((rswPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ = [] ∧
      CallsMatch σ ((rswPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (kidsAt [rswKid bz bp count zs ps] [] outs) outs ∧
      ∀ q ∈ rswPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
          addressOfIndex i ∧
        (RegionL [(bz, zs), (bp, ps), (bc, cs)] i ∨
          outRegion (kidsAt [rswKid bz bp count zs ps] [] outs) outs i) := by
  match outs, hl, ho, hLo with
  | [o], _, ho, hLo =>
  obtain ⟨ho1, -⟩ := ho
  obtain ⟨b, hr, hL⟩ := ho1 rfl
  have hch : ReadsAt rd (ofK (addressOfIndex b)) (rswChain zs ps count) := by
    refine hLo (b, rswChain zs ps count) ?_
    simp [outsL, kidsAt, rswKid, hL]
  have hcs : ReadsAt rd (ofK (addressOfIndex bc)) cs := hLin (bc, cs) (by simp)
  obtain ⟨σ, hat, e0, e1, e2, e3, e4, e260⟩ := rsw_block (bz := bz) (bp := bp) hcount hz hp hc hcs
    hch
  refine ⟨σ, ?_, ?_, ?_, by rw [rsw_allocs]; rfl, by rw [rsw_allocs]; rfl, ?_, ?_⟩
  · show [_, _, _, _].map _ = _
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3]
  · intro s hs
    have := List.all_eq_true.mp rsw_kinds s hs
    cases s <;> simp_all [DispOk, atomOrCall]
  · rw [rsw_body']
    refine Fwd.holdsList_straight _ _ _ _ (fun s hs ↦ ?_) (by simp [e260])
    have hnd := List.all_eq_true.mp rsw_kinds s hs
    cases s with
    | atom a => exact hat a (rsw_atom_mem hs)
    | call f args rets => trivial
    | _ => simp [atomOrCall] at hnd
  · rw [rsw_callSF]
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
    · show [_, _, _] = _
      simp only [rswKid, e0, e1, e3]
    · show [_] = o.1
      rw [hr, e4]
  · intro q hq
    obtain ⟨hoff, hp'⟩ := rsw_loads_ok hq
    rcases hp' with h | h <;> rw [h]
    · rw [e2, Main.addr_ofK]
      exact ⟨_, rfl, Or.inl ⟨(bc, cs), by simp, by simp [hc]; omega⟩⟩
    · rw [e4, rt_addr_mul]
      refine ⟨_, rfl, Or.inr (Or.inl ⟨rfl, ⟨(b, rswChain zs ps count), by simp [hL], ?_⟩⟩)⟩
      simp only [rswChain_length]; omega

/-- **`ring_switch_weight` is complete, placed**: on the coordinates, the point and the
coefficients, at every frame pointer, `rs_eq_run`'s chain at the bump allocator's position,
returning `ringWeight`. -/
theorem rsw_completeAt (κ : ℕ) {bz bp bc count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64) :
    CompleteAtD fs cert κ "ring_switch_weight" [(bz, zs), (bp, ps), (bc, cs)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
      (Returns [ringWeight zs (ps.map (1 + ·)) cs]) := by
  refine completeAt_flatDepR (fs := fs) (cert := cert) find_rsw rsw_not_loop κ _ _ _ rsw_body'
    rsw_flat rsw_addrs rsw_notIte [] (fun _ ↦ []) (fun _ ↦ List.Forall₂.nil)
    (fun _ ↦ [rswKid bz bp count zs ps]) ?_ (fun _ outs _ ↦ rsw_regions (fun i h ↦ Or.inl h) outs)
    (fun _ outs _ rd _ _ hLin _ ↦ rsw_lins hLin outs)
    (fun _ outs hl ho rd _ _ hLin hLo ↦ ?_)
  · intro fp k hk pv _
    rw [List.mem_singleton] at hk
    subst hk
    exact rs_completeAt κ hcount hz hp
  · obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := rsw_hσ hcount hz hp hc outs hl ho hLin hLo
    refine ⟨σ, h1, h2, h3, h4, h5, h6, fun q hq ↦ ?_⟩
    obtain ⟨i, hi, h | h⟩ := h7 q hq
    · exact ⟨i, hi, Or.inl h⟩
    · exact ⟨i, hi, Or.inr (Or.inr h)⟩

end
end LeanVM.Guest.B1.VerifySub
