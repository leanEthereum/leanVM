/-
  LeanVM.Guest.B1.Main.RawPushes

  On an honest run, `main_loop2`'s and `main_loop3`'s entries (`RawAtP`, `RawAtSP`) are `Hints.honestPushes`' raw leanXMSS and leanSPHINCS segments, stream by stream: each iteration's hinted raw index is `coveragePlan`'s direct slot.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsG
public import LeanVM.Guest.B1.Main.RawAtP
public import LeanVM.Guest.B1.Main.RawAtSP

/-!
# The raw loops' entries against the honest pushes

* `sameStreams_flatMap`: stream-by-stream equality, pointwise under a `flatMap`;
* `flatMap_range_getD`: a `flatMap` over a zip as one over the indices;
* `rawXD_slot`, `rawSD_slot`: raw signature `i`'s slot is `coveragePlan`'s `directSlots[i]`;
* `rawX_pops_sameStreams`: `main_loop2`'s entries from the counter `1` (`rawX_completeAtDP`) are `honestPushes`' segment `(rawX.zip xr.directSlots).flatMap …`, stream by stream;
* `rawS_pops_sameStreams`: `main_loop3`'s (`rawS_completeAtDP`) are `(rawS.zip sr.directSlots).flatMap …`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Coverage (coveragePlan)

@[expose] public section

theorem sameStreams_flatMap {α : Type} {f g : α → List Pop} :
    ∀ {l : List α}, (∀ x ∈ l, SameStreams (f x) (g x)) → SameStreams (l.flatMap f) (l.flatMap g)
  | [], _ => SameStreams.refl _
  | x :: l, h => by
      rw [List.flatMap_cons, List.flatMap_cons]
      exact (h x List.mem_cons_self).append (sameStreams_flatMap fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem flatMap_range_getD {α β γ : Type} (l : List α) (ds : List β) (a0 : α) (b0 : β) (G : α × β → List γ)
    (hd : l.length ≤ ds.length) :
    (l.zip ds).flatMap G = (List.range l.length).flatMap fun i => G (l.getD i a0, ds.getD i b0) := by
  have e : l.zip ds = (List.range l.length).map fun i => (l.getD i a0, ds.getD i b0) := by
    refine List.ext_getElem (by simp [hd]) fun k h1 h2 => ?_
    have hk : k < l.length := by simpa using h2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (lt_of_lt_of_le hk hd)]
  rw [e, List.flatMap_map]

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-- **Raw signature `i`'s slot is `coveragePlan`'s direct slot.** -/
theorem rawXD_slot {i : ℕ} (hi : i < (hRawX s w).length) :
    (slotsOf (xPlan s w)).getD i 0 = (xPlan s w).directSlots.getD i 0 := by
  obtain ⟨hk', hs, e, -⟩ := plan_raw s.claims.xmss ((hRawX s w).map (·.1))
    (w.children.map (·.statement.claims.xmss)) (k := i) (by simpa using hi)
  exact (List.getD_eq_getElem _ _ hs).trans (e.trans (List.getD_eq_getElem _ _ hk').symm)

/-- **`main_loop2`'s entries are the honest pushes' raw leanXMSS segment**, stream by stream. -/
theorem rawX_pops_sameStreams (fs : String → ℕ) (fp : ℕ) (hn : NodeRelation bytecode seed s w)
    (hl : GuestLimits s w) (d0 : LeanXmssClaim × LeanXmss.Signature) :
    SameStreams ((List.range' 0 ((hRawX s w).length - 0)).flatMap (l2Pops (rawXD fs fp hn d0)))
      ((w.xmssSignatures.zip (coveragePlan s.claims.xmss (w.xmssSignatures.map (·.1))
          (w.children.map (·.statement.claims.xmss))).directSlots).flatMap
        (fun (c, slot) ↦ ("raw_index", [Hints.count slot]) :: Hints.xmssHints c.1.1 c.1.2 c.2)) := by
  have hlen := plan_raw_length s.claims.xmss (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))
  rw [List.length_map] at hlen
  rw [flatMap_range_getD _ _ d0 0 _ hlen.ge, Nat.sub_zero, ← List.range_eq_range']
  refine sameStreams_flatMap fun i hi => ?_
  have hi : i < (hRawX s w).length := List.mem_range.mp hi
  have hb := regions_lt hl
  have hsl := xs_lt (s := s) (w := w) hi
  have hlt : (xPlan s w).directSlots.getD i 0 < 2 ^ 64 := by rw [← rawXD_slot hi]; omega
  have e : gen ^ (rawXD fs fp hn d0).slot i = Hints.count ((xPlan s w).directSlots.getD i 0) := by
    show gen ^ (slotsOf (xPlan s w)).getD i 0 = _
    rw [rawXD_slot hi, Sig.count_eq hlt, gen_pow_eq_ofK]
  rw [l2Pops, e]
  exact SameStreams.append (a := [_]) (SameStreams.refl _) (Sig.xSegPops_sameStreams _ _ _)

theorem rawSD_slot {i : ℕ} (hi : i < (hRawS s w).length) :
    (slotsOf (sPlan s w)).getD i 0 = (sPlan s w).directSlots.getD i 0 := by
  obtain ⟨hk', hs, e, -⟩ := plan_raw s.claims.sphincs ((hRawS s w).map (·.1))
    (w.children.map (·.statement.claims.sphincs)) (k := i) (by simpa using hi)
  exact (List.getD_eq_getElem _ _ hs).trans (e.trans (List.getD_eq_getElem _ _ hk').symm)

/-- **`main_loop3`'s entries are the honest pushes' raw leanSPHINCS segment**, stream by stream. -/
theorem rawS_pops_sameStreams (fs : String → ℕ) (fp : ℕ) (hn : NodeRelation bytecode seed s w)
    (hl : GuestLimits s w) (d0 : LeanSphincsClaim × Sphincs.Signature) :
    SameStreams ((List.range' 0 ((hRawS s w).length - 0)).flatMap (l4Pops (rawSD fs fp hn d0)))
      ((w.sphincsSignatures.zip (coveragePlan s.claims.sphincs (w.sphincsSignatures.map (·.1))
          (w.children.map (·.statement.claims.sphincs))).directSlots).flatMap
        (fun (c, slot) ↦ ("sp_raw_index", [Hints.count slot]) :: Hints.sphincsHints c.1.1 c.1.2 c.2)) := by
  have hlen := plan_raw_length s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs))
  rw [List.length_map] at hlen
  rw [flatMap_range_getD _ _ d0 0 _ hlen.ge, Nat.sub_zero, ← List.range_eq_range']
  refine sameStreams_flatMap fun i hi => ?_
  have hi : i < (hRawS s w).length := List.mem_range.mp hi
  have hb := regions_lt hl
  have hsl := ss_lt (s := s) (w := w) hi
  have hlt : (sPlan s w).directSlots.getD i 0 < 2 ^ 64 := by rw [← rawSD_slot hi]; omega
  have e : gen ^ (rawSD fs fp hn d0).slot i = Hints.count ((sPlan s w).directSlots.getD i 0) := by
    show gen ^ (slotsOf (sPlan s w)).getD i 0 = _
    rw [rawSD_slot hi, Sig.count_eq hlt, gen_pow_eq_ofK]
  rw [l4Pops, e]
  exact SameStreams.append (a := [_]) (SameStreams.refl _)
    (Sig.spSegPops_sameStreams _ _ _ (ss_verify hn d0 hi))

end
end LeanVM.Guest.B1.Main
