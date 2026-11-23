/-
  LeanVM.Guest.B1.Ring.WeightComplete

  `ring_switch_weight` is complete in the uniform placed form (`CompleteAtD`): it reads the last
  row of the chain `rs_eq_run` returns.
-/

module

public import LeanVM.Guest.B1.Ring.Weight
public import LeanVM.Guest.B1.Ring.TargetComplete
public import LeanVM.Guest.B1.Eq.RsPlaced
public import LeanVM.Guest.B1.KeccakGkr.FlatG
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«ring_switch_weight»

/-!
# `ring_switch_weight`, placed (TRIAGE G #66)

On the caller's words, `n < 64` coordinates `zs` at `g^bz`, `ps` (the point's `1 + r'`) at `g^bp`,
the 64 coefficients `cs` at `g^bc`, `ring_switch_weight` is complete at every frame pointer
(`rsw_completeAt`): its one callee, `rs_eq_run`, is complete, placed, its chain returned
(`rs_completeAt`, `RsOut`), and `ring_switch_weight` reads that chain's last row
(`completeAt_flatG`, the callee's returned buffer), returning
`ringWeight zs (ps.map (1 + ·)) cs` (`ringWeight_eq`, `rwProd_eq_ringRow`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The body -/

theorem rsw_chk : chk 4 rswT = some 261 := by decide +kernel

theorem rsw_stores : storesOf 4 rswT = [] := by decide +kernel

/-- `ring_switch_weight`'s statements before its `ret`. -/
def rswPre : List Stmt :=
  [.call "rs_eq_run" [.n (val% «ring_switch_weight» "z_vals"), .n (val% «ring_switch_weight» "point1"), .n (val% «ring_switch_weight» "qkeccakv_g")] [.n (val% «ring_switch_weight» "prod_final")]] ++
  ((List.range 64).map rswTerm).flatten ++ [.atom (.copy (.n (val% «ring_switch_weight» "s3#0")) (.n (val% «ring_switch_weight» "rs_weight@64")))]

theorem rswT_split : rswT = rswPre ++ [.ret [.n (val% «ring_switch_weight» "s3#0")]] := by
  simp only [rswT, rswPre, List.append_assoc, List.cons_append, List.nil_append]

theorem rsw_body' : Fn.body fn% «ring_switch_weight» = rswPre ++ [.ret [.n (val% «ring_switch_weight» "s3#0")]] := by
  rw [show Fn.body fn% «ring_switch_weight» = rswT from rsw_body, rswT_split]

theorem rsw_flat : rswPre.all Stmt.flat = true := by decide +kernel

theorem rsw_addrs : rswPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem rsw_allocs : rswPre.filterMap Main.Stmt.allocSz = [] := by decide +kernel

theorem rsw_noLoadIte : rswPre.all noLoadIte = true := by decide +kernel

theorem rsw_not_loop : coreProgram.loop "ring_switch_weight" = false := by decide +kernel

/-- The loads `ring_switch_weight` makes: the coefficients, the chain's last row. -/
def rswLoadOk : Atom → Bool
  | .load _ p off => decide (off < 64) &&
      (decide (p = .n (val% «ring_switch_weight» "c_table")) || decide (p = .n (val% «ring_switch_weight» "prod_final")))
  | _ => true

theorem rsw_loadOk : (rswPre.filterMap fun s => match s with
    | .atom a => some a | _ => none).all rswLoadOk = true := by decide +kernel

theorem rsw_needs : (rswPre.filterMap fun s => match s with
    | .atom a => some a | _ => none).all (fun a => !needsSide a ||
      (match a with | .load _ p _ => decide (p = .n (val% «ring_switch_weight» "c_table")) || decide (p = .n (val% «ring_switch_weight» "prod_final")) | _ => false)) = true := by
  decide +kernel

theorem rsw_noDisp : rswPre.all (fun s => match s with | .dispatch .. => false | _ => true) = true := by
  decide +kernel

theorem rsw_kinds : rswPre.all atomOrCall = true := by decide +kernel

theorem rsw_callS : rswPre.filterMap Main.Stmt.callS =
    [(none, "rs_eq_run", [.n (val% «ring_switch_weight» "z_vals"), .n (val% «ring_switch_weight» "point1"), .n (val% «ring_switch_weight» "qkeccakv_g")], [.n (val% «ring_switch_weight» "prod_final")])] := by decide +kernel

theorem rsw_callSF (σ : Val) : rswPre.filterMap (Stmt.callSF σ) =
    [(none, "rs_eq_run", [.n (val% «ring_switch_weight» "z_vals"), .n (val% «ring_switch_weight» "point1"), .n (val% «ring_switch_weight» "qkeccakv_g")], [.n (val% «ring_switch_weight» "prod_final")])] := by
  rw [← rsw_callS]
  refine List.filterMap_congr fun s hs => ?_
  have := List.all_eq_true.mp rsw_kinds s hs
  cases s <;> simp_all [Stmt.callSF, atomOrCall]

theorem rsw_loads_ok {q : V × ℕ} (hq : q ∈ rswPre.filterMap Stmt.loadS) :
    q.2 < 64 ∧ (q.1 = .n (val% «ring_switch_weight» "c_table") ∨ q.1 = .n (val% «ring_switch_weight» "prod_final")) := by
  obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
  cases s with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Stmt.loadS, Option.some.injEq] at hsq
      subst hsq
      have := List.all_eq_true.mp rsw_loadOk _ (List.mem_filterMap.mpr ⟨_, hs, rfl⟩)
      simp only [rswLoadOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
      exact this
    | _ => simp [Stmt.loadS] at hsq
  | _ => simp [Stmt.loadS] at hsq

/-! ## The honest valuation -/

/-- The oracle of `ring_switch_weight`'s body: `rs_eq_run`'s return, the chain at `g^b`. -/
noncomputable def rswW (b H : ℕ) : ℕ → E := fun i =>
  if i = val% «ring_switch_weight» "prod_final" then ofK (addressOfIndex b) * gen ^ (64 * H) else 0

/-- The evaluated valuation of `ring_switch_weight`'s body. -/
noncomputable def rswσ (rd : Reader) (args : List E) (b H : ℕ) : Val :=
  B1.Val.ofArgs (ev rd (rswW b H) args rswT)

/-- The atoms of `ring_switch_weight`'s statements. -/
def rswA : List Atom := rswPre.filterMap fun s => match s with | .atom a => some a | _ => none

theorem rsw_atom_mem {a : Atom} (h : Stmt.atom a ∈ rswPre) : a ∈ rswA :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem rswTerm_mem {k : ℕ} (hk : k < 64) (s : Stmt) (hs : s ∈ rswTerm k) : s ∈ rswPre := by
  simp only [rswPre, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨rswTerm k, ⟨k, hk, rfl⟩, hs⟩)

/-- The chain's last row, read through `rs_eq_run`'s return. -/
theorem rsChain_last {rd : Reader} {zs ps : List E} {count b : ℕ} (hz : zs.length = count)
    (hp : ps.length = count) (hch : ReadsAt rd (ofK (addressOfIndex b)) (rsChain zs ps count)) :
    ∀ k < 64, LoadHolds rd (ofK (addressOfIndex b) * gen ^ (64 * ((count + 7) / 8))) k
      (ringRow 1 zs ps k) := by
  intro k hk
  obtain ⟨hone, hr⟩ := rsChain_rows hch
  rw [loadHolds_mul_gen_pow]
  rcases Nat.eq_zero_or_pos count with h0 | hpos
  · subst h0
    have hz0 : zs = [] := List.length_eq_zero_iff.mp hz
    have hp0 : ps = [] := List.length_eq_zero_iff.mp hp
    subst hz0 hp0
    simpa [ringRow] using hone k hk
  · have := hr ((count + 7) / 8) (by omega) le_rfl k hk
    rwa [show min (8 * ((count + 7) / 8)) count = count by omega, List.take_of_length_le (by omega),
      List.take_of_length_le (by omega)] at this

/-- **`ring_switch_weight`'s statements hold** on their evaluated valuation, over the coefficients
and the chain `rs_eq_run` returns. -/
theorem rsw_block {rd : Reader} {bz bp bc b count : ℕ} {zs ps cs : List E}
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64)
    (hcs : ReadsAt rd (ofK (addressOfIndex bc)) cs) (hch : ReadsAt rd (ofK (addressOfIndex b)) (rsChain zs ps count)) :
    (∀ a ∈ rswA, a.Holds rd (rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count] b ((count + 7) / 8))) ∧
    rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
        b ((count + 7) / 8) (.n (val% «ring_switch_weight» "prod_final")) =
      ofK (addressOfIndex b) * gen ^ (64 * ((count + 7) / 8)) ∧
    rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
        b ((count + 7) / 8) (.n (val% «ring_switch_weight» "s3#0")) =
      ringWeight zs (ps.map (1 + ·)) cs := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
      (addressOfIndex bc), gen ^ count] b ((count + 7) / 8) := ⟨_, rfl⟩
  rw [← hσdef]
  obtain ⟨-, -, hgs⟩ := ev_spec rd (rswW b ((count + 7) / 8)) rswT
    [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count] rsw_chk
  rw [show [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^
      count].length = 4 from rfl, rsw_stores, ← rswσ, ← hσdef] at hgs
  have hgS : ∀ s ∈ rswPre, GoodS rd [] (rswW b ((count + 7) / 8)) σ s := fun s hs =>
    hgs s (by rw [rswT_split]; exact List.mem_append_left _ hs)
  have hg : ∀ a ∈ rswA, Good rd [] (rswW b ((count + 7) / 8)) σ a := fun a ha => by
    obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp ha
    cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
    subst hsa
    exact hgS _ hs
  have e2 : σ (.n (val% «ring_switch_weight» "c_table")) = ofK (addressOfIndex bc) := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count]) rsw_chk (by simp)
  have mulE : ∀ d u v : ℕ, u < d → v < d → Stmt.atom (.mul (.n d) (.n u) (.n v)) ∈ rswPre →
      σ (.n d) = σ (.n u) * σ (.n v) := by
    intro d u v hu hv hm
    have := hg _ (rsw_atom_mem hm)
    simp only [Good] at this
    rwa [ite_pos' ⟨hu, hv⟩] at this
  have e4 : σ (.n (val% «ring_switch_weight» "prod_final")) = ofK (addressOfIndex b) * gen ^ (64 * ((count + 7) / 8)) := by
    have := hgS (.call "rs_eq_run" [.n (val% «ring_switch_weight» "z_vals"), .n (val% «ring_switch_weight» "point1"), .n (val% «ring_switch_weight» "qkeccakv_g")] [.n (val% «ring_switch_weight» "prod_final")]) (by simp [rswPre])
    simpa [GoodS, rswW] using this
  have loadE : ∀ d p off, Stmt.atom (.load (.n d) p off) ∈ rswPre → σ (.n d) = rdAt rd (σ p) off := by
    intro d p off hm
    rcases (hg _ (rsw_atom_mem hm) : Good rd [] _ σ _) with h | h
    · exact absurd h (List.not_mem_nil)
    · exact h
  have hrowH : ∀ k < 64, LoadHolds rd (σ (.n (val% «ring_switch_weight» "prod_final"))) k (ringRow 1 zs ps k) := by
    intro k hk
    rw [e4]
    exact rsChain_last hz hp hch k hk
  have hcsk : ∀ k < 64, LoadHolds rd (σ (.n (val% «ring_switch_weight» "c_table"))) k (cs.getD k 0) := by
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
      have l1 := loadE (val% «ring_switch_weight» "rs_weight@1~0") (.n (val% «ring_switch_weight» "c_table")) 0 (mem _ (by simp))
      have l2 := loadE (val% «ring_switch_weight» "rs_weight@1~1") (.n (val% «ring_switch_weight» "prod_final")) 0 (mem _ (by simp))
      have m := mulE (val% «ring_switch_weight» "rs_weight@1") (val% «ring_switch_weight» "rs_weight@1~0") (val% «ring_switch_weight» "rs_weight@1~1") (by decide) (by decide) (mem _ (by simp))
      refine ⟨?_, ?_, m, fun h ↦ absurd rfl h⟩
      · rw [show rswC 0 = val% «ring_switch_weight» "rs_weight@1~0" from rfl, l1, rt_rdAt_of_load (hcsk 0 (by omega))]
      · rw [show rswP 0 = val% «ring_switch_weight» "rs_weight@1~1" from rfl, l2, rt_rdAt_of_load (hrowH 0 (by omega))]
    · simp only [hk0, ↓reduceIte] at mem
      have l1 := loadE (4 * k + 4) (.n (val% «ring_switch_weight» "c_table")) k (mem _ (by simp))
      have l2 := loadE (4 * k + 5) (.n (val% «ring_switch_weight» "prod_final")) k (mem _ (by simp))
      have m := mulE (4 * k + 6) (4 * k + 4) (4 * k + 5) (by omega) (by omega) (mem _ (by simp))
      have a := (hg _ (rsw_atom_mem (mem (.atom (.add (.n (4 * k + 7)) (.n (4 * k + 3))
        (.n (4 * k + 6)))) (by simp))) : σ (.n (4 * k + 7)) = σ (.n (4 * k + 3)) +
          σ (.n (4 * k + 6)))
      simp only [rswC, rswP, rswM, hk0, ↓reduceIte]
      refine ⟨by rw [l1, rt_rdAt_of_load (hcsk k hk)], by rw [l2, rt_rdAt_of_load (hrowH k hk)], m,
        fun _ ↦ ?_⟩
      rw [a, show 4 * (k - 1) + 7 = 4 * k + 3 by omega]
  have hside : ∀ a ∈ rswA, a ∉ ([] : List Atom) → needsSide a = true → a.Holds rd σ ∨ Side rd [] σ a := by
    intro a ha _ hns
    right
    have hok := List.all_eq_true.mp rsw_needs a ha
    have hld := List.all_eq_true.mp rsw_loadOk a ha
    simp only [hns, Bool.not_true, Bool.false_or] at hok
    cases a with
    | load d p off =>
      simp only [rswLoadOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hld
      simp only [Side, ite_neg' (List.not_mem_nil)]
      rcases hld.2 with rfl | rfl
      · exact rt_side_of_load (hcsk off hld.1)
      · exact rt_side_of_load (hrowH off hld.1)
    | _ => simp at hok
  have hat : ∀ a ∈ rswA, a.Holds rd σ :=
    atoms_holds_stores (S := []) (w := rswW b ((count + 7) / 8)) hg hside
      (fun _ _ _ haS => absurd haS List.not_mem_nil)
  refine ⟨hat, e4, ?_⟩
  have hcopy : σ (.n (val% «ring_switch_weight» "s3#0")) = σ (.n (val% «ring_switch_weight» "rs_weight@64")) :=
    hg _ (rsw_atom_mem (by simp [rswPre] : Stmt.atom (.copy (.n (val% «ring_switch_weight» "s3#0")) (.n (val% «ring_switch_weight» "rs_weight@64"))) ∈ rswPre))
  rw [hcopy, show (val% «ring_switch_weight» "rs_weight@64") = 4 * 63 + 7 from rfl,
    rsw_acc (fun k hk => (hterm k hk).2.2.2) 63 (by decide), ringWeight_eq, hc]
  refine gsum_congr fun k hk => ?_
  rw [(hterm k hk).2.2.1, (hterm k hk).1, (hterm k hk).2.1,
    rwProd_eq_ringRow k zs ps _ (by rw [hz, hp])]

/-! ## Placed -/

/-- `ring_switch_weight`'s callee: `rs_eq_run` on the coordinates and the point, returning its
chain. -/
def rswKid (bz bp count : ℕ) (zs ps : List E) : KidG :=
  ⟨"rs_eq_run", true, fun _ ↦ [ofK (addressOfIndex bz), ofK (addressOfIndex bp), gen ^ count],
    fun _ ↦ [(bz, zs), (bp, ps)], fun _ ↦ RsOut zs ps count⟩

/-- **`ring_switch_weight`'s honest valuation, placed**: on a memory holding the caller's words and
the chain `rs_eq_run` returned, what `completeAt_flatG` asks. -/
theorem rsw_hσ {bz bp bc count : ℕ} {zs ps cs : List E} (hz : zs.length = count)
    (hp : ps.length = count) (hc : cs.length = 64) (fps : List ℕ) (outs : List (List E × Main.Layout))
    (hl : fps.length = 1) (ho : OutsOk (atAllG [] [rswKid bz bp count zs ps] fps) outs) (rd : Reader)
    (hLin : MemL rd [(bz, zs), (bp, ps), (bc, cs)])
    (hto : MemL rd (takenOuts (atAllG [] [rswKid bz bp count zs ps] fps) outs)) :
    MemL rd (Kid.lins (atAllG [] [rswKid bz bp count zs ps] fps)) ∧
    RegionsOk (fun i => RegionL [(bz, zs), (bp, ps), (bc, cs)] i) (fun _ => False)
      (atAllG [] [rswKid bz bp count zs ps] fps) outs ∧
    ∃ σ : Val, (Fn.params fn% «ring_switch_weight»).map σ =
        [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count] ∧
      (∀ s ∈ rswPre, DispOk σ s) ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ (Fn.body fn% «ring_switch_weight») False
        (fun r => r = [ringWeight zs (ps.map (1 + ·)) cs]) ∧
      CallsMatch σ ((rswPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (atAllG [] [rswKid bz bp count zs ps] fps) outs ∧
      ∀ q ∈ rswPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
        (RegionL [(bz, zs), (bp, ps), (bc, cs)] i ∨ outRegion (atAllG [] [rswKid bz bp count zs ps] fps) outs i) := by
  obtain ⟨p, rfl⟩ : ∃ p, fps = [p] := by
    match fps, hl with
    | [p], _ => exact ⟨p, rfl⟩
  rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
  · exact absurd ho (by simp [OutsOk, atAllG])
  swap
  · exact absurd ho (by simp [OutsOk, atAllG])
  obtain ⟨b, ho1, ho2⟩ := ho.1 rfl
  have hch : ReadsAt rd (ofK (addressOfIndex b)) (rsChain zs ps count) :=
    hto (b, rsChain zs ps count) (by simp [takenOuts, atAllG, rswKid, ho2])
  have hcs : ReadsAt rd (ofK (addressOfIndex bc)) cs := hLin (bc, cs) (by simp)
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
      (addressOfIndex bc), gen ^ count] b ((count + 7) / 8) := ⟨_, rfl⟩
  obtain ⟨hat, e4, e3⟩ := rsw_block (bz := bz) (bp := bp) hz hp hc hcs hch
  rw [← hσdef] at hat e4 e3
  have hpar : ∀ i (hi : i < 4), σ (.n i) =
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count].getD i 0 := by
    intro i hi
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count]) rsw_chk (by simpa using hi)
  have e0 := hpar 0 (by omega)
  have e1 := hpar 1 (by omega)
  have e2 := hpar 2 (by omega)
  have e3' := hpar 3 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3'
  have hlin : ∀ q ∈ Kid.lins (atAllG [] [rswKid bz bp count zs ps] [p]), q ∈ [(bz, zs), (bp, ps), (bc, cs)] := by
    intro q hq
    simp only [Kid.lins, atAllG, rswKid, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    tauto
  refine ⟨fun q hq ↦ hLin q (hlin q hq), ⟨fun _ i ⟨q, hq, hi⟩ ↦ Or.inl ⟨q, hlin q hq, hi⟩, trivial⟩,
    σ, ?_, ?_, ?_, ?_, ?_⟩
  · show [σ (.n (val% «ring_switch_weight» "z_vals")), σ (.n (val% «ring_switch_weight» "point1")),
      σ (.n (val% «ring_switch_weight» "c_table")), σ (.n (val% «ring_switch_weight» "qkeccakv_g"))] = _
    rw [e0, e1, e2, e3']
  · intro s hs
    have := List.all_eq_true.mp rsw_noDisp s hs
    cases s <;> simp_all [DispOk]
  · rw [rsw_body']
    refine Fwd.holdsList_straight _ _ _ _ (fun s hs ↦ ?_) (by simp [e3])
    have hnd := List.all_eq_true.mp rsw_kinds s hs
    cases s with
    | atom a => exact hat a (rsw_atom_mem hs)
    | call f args rets => trivial
    | _ => simp [atomOrCall] at hnd
  · rw [rsw_callSF]
    refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
    · show [σ (.n (val% «ring_switch_weight» "z_vals")), σ (.n (val% «ring_switch_weight» "point1")), σ (.n (val% «ring_switch_weight» "qkeccakv_g"))] = _
      rw [e0, e1, e3']
      rfl
    · show [σ (.n (val% «ring_switch_weight» "prod_final"))] = o.1
      rw [ho1, e4]
  · intro q hq
    obtain ⟨hoff, hp'⟩ := rsw_loads_ok hq
    rcases hp' with h | h <;> rw [h]
    · rw [e2, Main.addr_ofK]
      exact ⟨_, rfl, Or.inl ⟨(bc, cs), by simp, by simp [hc]; omega⟩⟩
    · rw [e4, rt_addr_mul]
      refine ⟨_, rfl, Or.inr (Or.inl ⟨rfl, (b, rsChain zs ps count), by rw [ho2]; simp, by omega, ?_⟩)⟩
      simp only [rsChain_length]
      omega

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`ring_switch_weight` is complete, placed**: on the coordinates, the point and the
coefficients, at every frame pointer, returning `ringWeight`, `rs_eq_run`'s chain its callee's
(`rs_completeAt`). -/
theorem rsw_completeAt (κ : ℕ) {bz bp bc count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64) :
    CompleteAtD fs cert κ "ring_switch_weight" [(bz, zs), (bp, ps), (bc, cs)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
      (Returns [ringWeight zs (ps.map (1 + ·)) cs]) := by
  refine completeAt_flatG (fs := fs) (cert := cert) find_rsw rsw_not_loop κ _ _ _ rsw_body' rsw_flat
    rsw_addrs rsw_noLoadIte [] (fun _ _ ↦ []) (fun _ _ ↦ .nil)
    (fun _ ↦ [rswKid bz bp count zs ps]) ?_ ?_
  · intro fp k hk _ ps'
    rw [List.mem_singleton] at hk
    subst hk
    exact (rs_completeAt κ hcount hz hp).toF
  · intro fp fps outs hl _ ho rd _ _ hLin hto
    obtain ⟨h1, h2, σ, h3, h4, h5, h6, h7⟩ := rsw_hσ hz hp hc fps outs hl ho rd hLin hto
    refine ⟨h1, regionsOk_mono (fun i h ↦ Or.inl h) h2, σ, h3, h4, h5, by rw [rsw_allocs]; rfl,
      by rw [rsw_allocs]; rfl, h6, fun q hq ↦ ?_⟩
    obtain ⟨i, hi, h | h⟩ := h7 q hq
    · exact ⟨i, hi, Or.inl h⟩
    · exact ⟨i, hi, Or.inr (Or.inr h)⟩

end
end LeanVM.Guest.B1.VerifySub
