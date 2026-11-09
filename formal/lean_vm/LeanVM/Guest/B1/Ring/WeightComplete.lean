/-
  LeanVM.Guest.B1.Ring.WeightComplete

  `ring_switch_weight` is complete in the uniform placed form (`CompleteAtD`): its chain at the
  bump allocator's position, row `0` its ones and row `⌈n/2⌉` `rs_eq_run`'s.
-/

module

public import LeanVM.Guest.B1.Ring.Weight
public import LeanVM.Guest.B1.Ring.TargetComplete
public import LeanVM.Guest.B1.Eq.RsEqRun

/-!
# `ring_switch_weight`, placed (TRIAGE G #66)

On the caller's words — `n < 64` coordinates `zs` at `g^bz`, `ps` (the point's `1 + r'`) at `g^bp`,
the 64 coefficients `cs` at `g^bc` — `ring_switch_weight` is complete at every frame pointer
(`rsw_completeAt`): its chain (`HeapBuf` of `64(n+1)` words, by `allocDyn`) holds the honest rows
`rswChain` (row `0` ones, row `h ≥ 1` `rs_eq_run`'s), `rs_eq_run` (pure, no range check) is
complete by `completeAt_of_rel_pureD` from its meaning (B1-a's `rs_eq_run_holds`), and it returns
`ringWeight zs (ps.map (1 + ·)) cs` (`ringWeight_eq`, `rwProd_eq_ringRow`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
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

/-- `rs_eq_run`'s callees: `__loop5` and `rs_eq_rows__L{n}`, `n ≤ 8`. -/
def rsPureNames : List String := ["rs_eq_run", "__loop5"] ++ rsEqRowsNames

theorem rs_pure : coreProgram.PureIn rsPureNames := by
  intro g hg fn hf
  simp only [rsPureNames, rsEqRowsNames, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Program.find?_of_indexOf? (j := 6) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 80) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 81) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 82) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 83) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 84) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 85) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 86) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 87) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 88) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 418) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel

/-- `rs_eq_run`'s words: the chain, the coordinates, the point. -/
def rsLin (bb bz bp count : ℕ) (zs ps : List E) : Main.Layout :=
  [(bb, rswChain zs ps count), (bz, zs), (bp, ps)]

theorem rs_rel {rd : Reader} {bb bz bp count : ℕ} {zs ps : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hL : MemL rd (rsLin bb bz bp count zs ps)) :
    coreProgram.Rel rd "rs_eq_run" [ofK (addressOfIndex bb), ofK (addressOfIndex bz), ofK
        (addressOfIndex bp), gen ^ count]
      [ofK (addressOfIndex bb) * gen ^ (64 * rswH count)] := by
  have hch : ReadsAt rd (ofK (addressOfIndex bb)) (rswChain zs ps count) :=
    hL (bb, rswChain zs ps count) (by simp [rsLin])
  have hzs : ReadsAt rd (ofK (addressOfIndex bz)) zs := hL (bz, zs) (by simp [rsLin])
  have hps : ReadsAt rd (ofK (addressOfIndex bp)) ps := hL (bp, ps) (by simp [rsLin])
  refine (rs_eq_run_holds rd _ _).2 ⟨count, hcount, rfl, zs, ps, List.replicate 64 1, hz, hp,
    by simp, hzs, hps, fun _ k hk ↦ ?_, fun h hh1 hh2 k hk ↦ ?_, rfl⟩
  · simp only [List.length_replicate] at hk
    have := rswChain_load hch (t := k) (by rw [rswH]; omega)
    simp only [List.getElem_replicate]
    rwa [ite_pos' (by omega : k / 64 = 0)] at this
  · have := rswChain_load hch (t := 64 * h + k) (by unfold rswH; omega)
    rw [ite_neg' (by omega : ¬ (64 * h + k) / 64 = 0), show (64 * h + k) / 64 = h by omega,
      show (64 * h + k) % 64 = k by omega] at this
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]
    exact this

/-! ## The body -/

theorem rsw_chk : chk 4 rswT = some 334 := by decide +kernel

theorem rsw_stores : storesOf 4 rswT =
    (List.range 64).map fun k => Atom.load (.n (13 + k)) (.n 12) k := by decide +kernel

/-- `ring_switch_weight`'s statements before its `ret`. -/
def rswPre : List Stmt :=
  [.atom (.const (.n 4) (word 2 0 0)), .atom (.mul (.n 5) (.n 3) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.hint (.allocDyn (.n 12) (.n 11)))] ++
  ((List.range 64).map rswInit).flatten ++ [.call "rs_eq_run" [.n 12, .n 0, .n 1, .n 3] [.n 77]] ++
  ((List.range 64).map rswTerm).flatten ++ [.atom (.copy (.n 333) (.n 332))]

theorem rswT_split : rswT = rswPre ++ [.ret [.n 333]] := by
  simp only [rswT, rswPre, List.append_assoc, List.cons_append, List.nil_append]

theorem rsw_body' : Fn.body Data.core14 = rswPre ++ [.ret [.n 333]] := by
  rw [show Fn.body Data.core14 = rswT from rsw_body, rswT_split]

theorem rsw_flat : rswPre.all Stmt.flat = true := by decide +kernel

theorem rsw_addrs : rswPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem rsw_allocs : rswPre.filterMap Main.Stmt.allocSz = [(.n 12, .inr (.n 11))] := by
  decide +kernel

theorem rsw_not_loop : coreProgram.loop "ring_switch_weight" = false := by decide +kernel

/-- The loads `ring_switch_weight` makes: the coefficients (`2`), the chain's last row (`77`), the
chain's first row (`12`, stores). -/
def rswLoadOk : Atom → Bool
  | .load _ p off => decide (off < 64) &&
      (decide (p = .n 2) || decide (p = .n 77) || decide (p = .n 12))
  | _ => true

theorem rsw_loadOk : (rswPre.filterMap fun s => match s with
    | .atom a => some a | _ => none).all rswLoadOk = true := by decide +kernel

theorem rsw_canon : canonChk [] ((rswPre.filterMap fun s => match s with
    | .atom a => some a | _ => none).filter (fun a => decide (a ∉ storesOf 4 rswT))) = true := by
  decide +kernel

theorem rsw_needs : (rswPre.filterMap fun s => match s with
    | .atom a => some a | _ => none).all (fun a => decide (a ∈ storesOf 4 rswT) || !needsSide a ||
      (match a with | .load _ p _ => decide (p = .n 2) || decide (p = .n 77) | _ => false)) = true := by
  decide +kernel

/-! ## The honest valuation -/

/-- The oracle of `ring_switch_weight`'s body: its chain's base, `rs_eq_run`'s return. -/
noncomputable def rswW (bb H : ℕ) : ℕ → E := fun i =>
  if i = 12 then ofK (addressOfIndex bb) else if i = 77 then ofK (addressOfIndex bb) * gen ^ (64 * H) else 0

/-- The evaluated valuation of `ring_switch_weight`'s body. -/
noncomputable def rswσ (rd : Reader) (args : List E) (bb H : ℕ) : Val :=
  B1.Val.ofArgs (ev rd (rswW bb H) args rswT)

/-- The atoms of `ring_switch_weight`'s statements. -/
def rswA : List Atom := rswPre.filterMap fun s => match s with | .atom a => some a | _ => none

theorem rsw_atom_mem {a : Atom} (h : Stmt.atom a ∈ rswPre) : a ∈ rswA :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem rsw_mem_atom {a : Atom} (h : a ∈ rswA) : Stmt.atom a ∈ rswPre := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem rswInit_mem {k : ℕ} (hk : k < 64) (s : Stmt) (hs : s ∈ rswInit k) : s ∈ rswPre := by
  simp only [rswPre, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨rswInit k, ⟨k, hk, rfl⟩, hs⟩)))

theorem rswTerm_mem {k : ℕ} (hk : k < 64) (s : Stmt) (hs : s ∈ rswTerm k) : s ∈ rswPre := by
  simp only [rswPre, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨rswTerm k, ⟨k, hk, rfl⟩, hs⟩)

/-- **`ring_switch_weight`'s statements hold** on their evaluated valuation, over the honest
chain, the coordinates, the point and the coefficients. -/
theorem rsw_block {rd : Reader} {bz bp bc bb count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64)
    (hzs : ReadsAt rd (ofK (addressOfIndex bz)) zs) (hps : ReadsAt rd (ofK (addressOfIndex bp)) ps)
    (hcs : ReadsAt rd (ofK (addressOfIndex bc)) cs) (hch : ReadsAt rd (ofK (addressOfIndex bb)) (rswChain zs ps count)) :
    (∀ a ∈ rswA, a.Holds rd (rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count] bb
      (rswH count))) ∧
    rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
        bb (rswH count) (.n 11) =
      ofK (addressOfIndex (64 * (count + 1))) ∧
    rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
        bb (rswH count) (.n 12) =
      ofK (addressOfIndex bb) ∧
    rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
        bb (rswH count) (.n 77) =
      ofK (addressOfIndex bb) * gen ^ (64 * rswH count) ∧
    rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
        bb (rswH count) (.n 333) =
      ringWeight zs (ps.map (1 + ·)) cs := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
      (addressOfIndex bc), gen ^ count] bb
      (rswH count) := ⟨_, rfl⟩
  rw [← hσdef]
  set S : List Atom := (List.range 64).map fun k => Atom.load (.n (13 + k)) (.n 12) k with hS
  obtain ⟨-, -, hgs⟩ := ev_spec rd (rswW bb (rswH count)) rswT
    [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count] rsw_chk
  rw [show [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^
      count].length = 4 from rfl,
    rsw_stores, ← hS, ← rswσ, ← hσdef] at hgs
  have hgS : ∀ s ∈ rswPre, GoodS rd S (rswW bb (rswH count)) σ s := fun s hs =>
    hgs s (by rw [rswT_split]; exact List.mem_append_left _ hs)
  have hg : ∀ a ∈ rswA, Good rd S (rswW bb (rswH count)) σ a := fun a ha => hgS _ (rsw_mem_atom ha)
  have e0 : σ (.n 0) = ofK (addressOfIndex bz) := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count]) rsw_chk
      (by simp)
  have e1 : σ (.n 1) = ofK (addressOfIndex bp) := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count]) rsw_chk
      (by simp)
  have e2 : σ (.n 2) = ofK (addressOfIndex bc) := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count]) rsw_chk
      (by simp)
  have e3 : σ (.n 3) = gen ^ count := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count]) rsw_chk
      (by simp)
  have mulE : ∀ d u v : ℕ, u < d → v < d → Stmt.atom (.mul (.n d) (.n u) (.n v)) ∈ rswPre →
      σ (.n d) = σ (.n u) * σ (.n v) := by
    intro d u v hu hv hm
    have := hg _ (rsw_atom_mem hm)
    simp only [Good] at this
    rwa [ite_pos' ⟨hu, hv⟩] at this
  have constE : ∀ d : ℕ, ∀ c : E, Stmt.atom (.const (.n d) c) ∈ rswPre → σ (.n d) = c :=
    fun d c h ↦ hg _ (rsw_atom_mem h)
  have hmem : ∀ a, Stmt.atom a ∈ [Stmt.atom (.const (.n 4) (word 2 0 0)),
      .atom (.mul (.n 5) (.n 3) (.n 4)), .atom (.mul (.n 6) (.n 5) (.n 5)),
      .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 7)),
      .atom (.mul (.n 9) (.n 8) (.n 8)), .atom (.mul (.n 10) (.n 9) (.n 9)),
      .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.hint (.allocDyn (.n 12) (.n 11)))] →
      Stmt.atom a ∈ rswPre := fun a h ↦ by
    simp only [rswPre, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  have e4 := constE 4 (word 2 0 0) (hmem _ (by simp))
  have e5 := mulE 5 3 4 (by omega) (by omega) (hmem _ (by simp))
  have e6 := mulE 6 5 5 (by omega) (by omega) (hmem _ (by simp))
  have e7 := mulE 7 6 6 (by omega) (by omega) (hmem _ (by simp))
  have e8 := mulE 8 7 7 (by omega) (by omega) (hmem _ (by simp))
  have e9 := mulE 9 8 8 (by omega) (by omega) (hmem _ (by simp))
  have e10 := mulE 10 9 9 (by omega) (by omega) (hmem _ (by simp))
  have e11 := mulE 11 10 10 (by omega) (by omega) (hmem _ (by simp))
  have e12 : σ (.n 12) = ofK (addressOfIndex bb) := by
    have := hg _ (rsw_atom_mem (hmem _ (by simp)) : Atom.hint (.allocDyn (.n 12) (.n 11)) ∈ rswA)
    simpa [Good, rswW] using this
  have e77 : σ (.n 77) = ofK (addressOfIndex bb) * gen ^ (64 * rswH count) := by
    have := hgS (.call "rs_eq_run" [.n 12, .n 0, .n 1, .n 3] [.n 77]) (by simp [rswPre])
    simpa [GoodS, rswW] using this
  have h11 : σ (.n 11) = ofK (addressOfIndex (64 * (count + 1))) := by
    rw [e11, e10, e9, e8, e7, e6, e5, e3, e4, word_gen, ← gen_pow_eq_ofK]
    ring
  -- the coefficients and the chain's last row
  have notS : ∀ d p off, p ≠ (.n 12 : V) → Atom.load d p off ∉ S := by
    intro d p off hp hm
    rw [hS] at hm
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hm
    simp only [Atom.load.injEq] at hk
    exact hp hk.2.1.symm
  have loadE : ∀ d p off, Stmt.atom (.load (.n d) p off) ∈ rswPre → p ≠ (.n 12 : V) →
      σ (.n d) = rdAt rd (σ p) off := by
    intro d p off hm hp
    rcases (hg _ (rsw_atom_mem hm) : Good rd S _ σ _) with h | h
    · exact absurd h (notS _ _ _ hp)
    · exact h
  have hrowH : ∀ k < 64, LoadHolds rd (σ (.n 77)) k (ringRow 1 zs ps k) := by
    intro k hk
    rw [e77, loadHolds_mul_gen_pow]
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
      (k ≠ 0 → σ (.n (4 * k + 80)) = σ (.n (4 * (k - 1) + 80)) + σ (.n (rswM k))) := by
    intro k hk
    have mem := rswTerm_mem hk
    have hne2 : (.n 2 : V) ≠ .n 12 := by decide
    have hne77 : (.n 77 : V) ≠ .n 12 := by decide
    unfold rswTerm at mem
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte] at mem
      have l1 := loadE 78 (.n 2) 0 (mem _ (by simp)) hne2
      have l2 := loadE 79 (.n 77) 0 (mem _ (by simp)) hne77
      have m := mulE 80 78 79 (by omega) (by omega) (mem _ (by simp))
      refine ⟨?_, ?_, m, fun h ↦ absurd rfl h⟩
      · rw [show rswC 0 = 78 from rfl, l1, rt_rdAt_of_load (hcsk 0 (by omega))]
      · rw [show rswP 0 = 79 from rfl, l2, rt_rdAt_of_load (hrowH 0 (by omega))]
    · simp only [hk0, ↓reduceIte] at mem
      have l1 := loadE (4 * k + 77) (.n 2) k (mem _ (by simp)) hne2
      have l2 := loadE (4 * k + 78) (.n 77) k (mem _ (by simp)) hne77
      have m := mulE (4 * k + 79) (4 * k + 77) (4 * k + 78) (by omega) (by omega) (mem _ (by simp))
      have a := (hg _ (rsw_atom_mem (mem (.atom (.add (.n (4 * k + 80)) (.n (4 * k + 76))
        (.n (4 * k + 79)))) (by simp))) : σ (.n (4 * k + 80)) = σ (.n (4 * k + 76)) +
          σ (.n (4 * k + 79)))
      simp only [rswC, rswP, rswM, hk0, ↓reduceIte]
      refine ⟨by rw [l1, rt_rdAt_of_load (hcsk k hk)], by rw [l2, rt_rdAt_of_load (hrowH k hk)], m,
        fun _ ↦ ?_⟩
      rw [a, show 4 * (k - 1) + 80 = 4 * k + 76 by omega]
  -- the atoms
  have hside : ∀ a ∈ rswA, a ∉ S → needsSide a = true → a.Holds rd σ ∨ Side rd S σ a := by
    intro a ha haS hns
    right
    have hok := List.all_eq_true.mp rsw_needs a ha
    have hld := List.all_eq_true.mp rsw_loadOk a ha
    rw [rsw_stores, ← hS] at hok
    simp only [hns, Bool.not_true, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with h | h
    · exact absurd h haS
    · cases a with
      | load d p off =>
        simp only [rswLoadOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hld h
        simp only [Side, ite_neg' haS]
        rcases h with rfl | rfl
        · exact rt_side_of_load (hcsk off hld.1)
        · exact rt_side_of_load (hrowH off hld.1)
      | _ => simp at h
  have hat : ∀ a ∈ rswA, a.Holds rd σ := by
    have hσv : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσdef]; rfl
    refine atoms_holds_stores (S := S) (w := rswW bb (rswH count)) (A := [])
      (dec := fun _ => inferInstance) hσv ?_ hg
      (fun i hi => absurd hi (by simp)) hside ?_
    · have := rsw_canon; rw [rsw_stores, ← hS] at this; exact this
    · intro _ a _ haS
      rw [hS] at haS
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp haS
      have hk' := List.mem_range.mp hk
      have hc1 := constE (13 + k) (word 1 0 0) (rswInit_mem hk' _ (by simp [rswInit]))
      show LoadHolds rd (σ (.n 12)) k (σ (.n (13 + k)))
      rw [e12, hc1, word_one]
      have := rswChain_load hch (t := k) (by unfold rswH; omega)
      rwa [ite_pos' (by omega : k / 64 = 0)] at this
  refine ⟨hat, h11, e12, e77, ?_⟩
  have hcopy : σ (.n 333) = σ (.n 332) :=
    hg _ (rsw_atom_mem (by simp [rswPre] : Stmt.atom (.copy (.n 333) (.n 332)) ∈ rswPre))
  rw [hcopy, show (332 : ℕ) = 4 * 63 + 80 from rfl,
    rsw_acc (fun k hk => (hterm k hk).2.2.2) 63 (by decide), ringWeight_eq, hc]
  refine gsum_congr fun k hk => ?_
  rw [(hterm k hk).2.2.1, (hterm k hk).1, (hterm k hk).2.1,
    rwProd_eq_ringRow k zs ps _ (by rw [hz, hp])]

/-! ## Placed -/

theorem rsw_noDisp : rswPre.all (fun s => match s with | .dispatch .. => false | _ => true) = true := by
  decide +kernel

/-- An atom or a call. -/
def atomOrCall : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | _ => false

theorem rsw_kinds : rswPre.all atomOrCall = true := by decide +kernel

theorem rsw_callS : rswPre.filterMap Main.Stmt.callS =
    [(none, "rs_eq_run", [.n 12, .n 0, .n 1, .n 3], [.n 77])] := by decide +kernel

theorem rsw_callSF (σ : Val) : rswPre.filterMap (Stmt.callSF σ) =
    [(none, "rs_eq_run", [.n 12, .n 0, .n 1, .n 3], [.n 77])] := by
  rw [← rsw_callS]
  refine List.filterMap_congr fun s hs => ?_
  have := List.all_eq_true.mp rsw_kinds s hs
  cases s <;> simp_all [Stmt.callSF, atomOrCall]

theorem rsw_loads_ok {q : V × ℕ} (hq : q ∈ rswPre.filterMap Stmt.loadS) :
    q.2 < 64 ∧ (q.1 = .n 2 ∨ q.1 = .n 77 ∨ q.1 = .n 12) := by
  obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
  cases s with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Stmt.loadS, Option.some.injEq] at hsq
      subst hsq
      have := List.all_eq_true.mp rsw_loadOk _ (rsw_atom_mem hs)
      simp only [rswLoadOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1, by tauto⟩
    | _ => simp [Stmt.loadS] at hsq
  | _ => simp [Stmt.loadS] at hsq

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`ring_switch_weight` is complete, placed**: on the coordinates, the point and the
coefficients, at every frame pointer, its chain at the bump allocator's position, returning
`ringWeight`. -/
theorem rsw_completeAt (κ : ℕ) {bz bp bc count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64) :
    CompleteAtD fs cert κ "ring_switch_weight" [(bz, zs), (bp, ps), (bc, cs)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
      (Returns [ringWeight zs (ps.map (1 + ·)) cs]) := by
  refine completeAt_flatD (fs := fs) (cert := cert) find_rsw rsw_not_loop κ _ _ _ rsw_body' rsw_flat
    rsw_addrs [64 * (count + 1)] (fun _ ↦ [rswChain zs ps count])
    (fun _ ↦ by simpa using rswChain_le zs ps count)
    (fun fp ↦ [⟨"rs_eq_run", true, [ofK (addressOfIndex (fp + fs "ring_switch_weight")), ofK
        (addressOfIndex bz),
      ofK (addressOfIndex bp), gen ^ count], rsLin (fp + fs "ring_switch_weight") bz bp count zs ps,
      Returns [ofK (addressOfIndex (fp + fs "ring_switch_weight")) * gen ^ (64 * rswH count)]⟩]) ?_
          ?_ ?_ ?_
  · intro fp k hk _
    rw [List.mem_singleton] at hk
    subst hk
    exact completeAt_of_rel_pureD rs_pure (by simp [rsPureNames]) (fun rd hL ↦ rs_rel hcount hz hp hL) κ
  · intro fp k hk _ i hi
    rw [List.mem_singleton] at hk
    subst hk
    obtain ⟨q, hq, hi⟩ := hi
    simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inr ⟨_, by simp [bufL, bases], hi⟩
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inl ⟨_, by simp, hi⟩
  · intro fp rd hB hLin k hk
    rw [List.mem_singleton] at hk
    subst hk
    intro q hq
    simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hB (fp + fs "ring_switch_weight", rswChain zs ps count) (by simp [bufL, bases])
    · exact hLin (bz, zs) (by simp)
    · exact hLin (bp, ps) (by simp)
  · intro fp outs ho rd _ hB hLin
    have hzs : ReadsAt rd (ofK (addressOfIndex bz)) zs := hLin (bz, zs) (by simp)
    have hps : ReadsAt rd (ofK (addressOfIndex bp)) ps := hLin (bp, ps) (by simp)
    have hcs : ReadsAt rd (ofK (addressOfIndex bc)) cs := hLin (bc, cs) (by simp)
    have hch : ReadsAt rd (ofK (addressOfIndex (fp + fs "ring_switch_weight"))) (rswChain zs ps
        count) :=
      hB (fp + fs "ring_switch_weight", rswChain zs ps count) (by simp [bufL, bases])
    rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
    · exact absurd ho (by simp [OutsOk])
    swap
    · exact absurd ho.2 (by simp [OutsOk])
    obtain ⟨ho', -⟩ := ho
    obtain ⟨ho1, -⟩ := ho' rfl
    obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count]
        (fp + fs "ring_switch_weight") (rswH count) := ⟨_, rfl⟩
    obtain ⟨hat, h11, e12, e77, e333⟩ := rsw_block hcount hz hp hc hzs hps hcs hch
    rw [← hσdef] at hat h11 e12 e77 e333
    have hpar : ∀ i (hi : i < 4), σ (.n i) =
        [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^
            count].getD i 0 := by
      intro i hi
      rw [hσdef]
      exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
          (addressOfIndex bc), gen ^ count]) rsw_chk
        (by simpa using hi)
    have e0 := hpar 0 (by omega)
    have e1 := hpar 1 (by omega)
    have e2 := hpar 2 (by omega)
    have e3 := hpar 3 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3
    refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show [Core.V.n 0, .n 1, .n 2, .n 3].map σ = _
      simp only [List.map_cons, List.map_nil, e0, e1, e2, e3]
    · intro s hs
      have := List.all_eq_true.mp rsw_noDisp s hs
      cases s <;> simp_all [DispOk]
    · rw [rsw_body']
      refine Fwd.holdsList_straight _ _ _ _ (fun s hs ↦ ?_) (by simp [e333])
      have hnd := List.all_eq_true.mp rsw_kinds s hs
      cases s with
      | atom a => exact hat a (rsw_atom_mem hs)
      | call f args rets =>
        have : Stmt.call f args rets = .call "rs_eq_run" [.n 12, .n 0, .n 1, .n 3] [.n 77] := by
          have h := rsw_callSF σ
          have hm : (Option.none, f, args, rets) ∈ rswPre.filterMap (Stmt.callSF σ) :=
            List.mem_filterMap.mpr ⟨_, hs, rfl⟩
          rw [h, List.mem_singleton] at hm
          simp only [Prod.mk.injEq] at hm
          obtain ⟨-, rfl, rfl, rfl⟩ := hm
          rfl
        rw [this]
        show coreProgram.Rel rd "rs_eq_run" [σ (.n 12), σ (.n 0), σ (.n 1), σ (.n 3)] [σ (.n 77)]
        rw [e12, e0, e1, e3, e77]
        exact rs_rel hcount hz hp (fun q hq ↦ by
          simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact hch
          · exact hzs
          · exact hps)
      | _ => simp [atomOrCall] at hnd
    · rw [rsw_allocs]
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, h11, List.cons.injEq, and_true]
      exact logG_spec (by omega)
    · rw [rsw_allocs]
      simp [bases, e12]
    · rw [rsw_callSF]
      refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 12), σ (.n 0), σ (.n 1), σ (.n 3)] = _
        rw [e12, e0, e1, e3]
      · show [σ (.n 77)] = o.1
        rw [ho1, e77]
    · intro q hq
      obtain ⟨hoff, hp'⟩ := rsw_loads_ok (filterMap_of_loadsEv (by decide +kernel) hq)
      rcases hp' with h | h | h <;> rw [h]
      · rw [e2, Main.addr_ofK]
        exact ⟨_, rfl, Or.inl ⟨(bc, cs), by simp, by simp [hc]; omega⟩⟩
      · rw [e77, rt_addr_mul]
        exact ⟨_, rfl, Or.inr ⟨(fp + fs "ring_switch_weight", rswChain zs ps count),
          by simp [bufL, bases], by simp only [rswChain_length]; omega⟩⟩
      · rw [e12, Main.addr_ofK]
        exact ⟨_, rfl, Or.inr ⟨(fp + fs "ring_switch_weight", rswChain zs ps count),
          by simp [bufL, bases], by simp only [rswChain_length]; omega⟩⟩

end
end LeanVM.Guest.B1.VerifySub
