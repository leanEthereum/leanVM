/-
  LeanVM.Guest.B1.Da.CellPlaced

  The cell check placed on its completing valuation, its node holding the honest symbols, and the placement
  predicates of a callee with no words of its own (`PlacedF`) and of a loop from an iteration on (`PlacedLF`).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.CellPops
public import LeanVM.Guest.B1.Da.CellAtChk
public import LeanVM.Guest.B1.Da.AtTB
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_cell»

/-!
# The cell check, placed

* `PlacedF`, `PlacedLF`: placed at every frame pointer (a loop from an iteration on), no words of its own;
  `PlacedF.toDTB`: within the bound every valid tree of it meets; `placedLF_tail`: the rest of a loop.
* `cellNH syms`: a cell check's node holding `syms`; `cell_placedF`, `cellNH_pops`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Protocol.KeccakHash
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtDTB Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append iterK)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-! ## Placed without words of its own -/

/-- **`f` placed at every frame pointer, no words of its own**, by a tree of `T`. -/
def PlacedF (k : ℕ) (f : String) (Lin : Layout) (args rets : List E) (T : Tree → Prop) : Prop :=
  ∀ fp, ∃ n, ∀ rd, LowDef k rd → MemL rd Lin →
    RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp n f args rets T

/-- **A loop helper placed from an iteration on, no words of its own**: its frames, `B` words, at any `fp`, the rest of
its subtree at any `c` past them. -/
def PlacedLF (k : ℕ) (f : String) (Lin : Layout) (args : List E) (T : Tree → Prop) : Prop :=
  ∃ B, ∀ fp c, fp + B ≤ c → ∃ n, ∀ rd, LowDef k rd → MemL rd Lin →
    RelAtInCT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c B n f args [] T

variable {fs cert}

theorem PlacedLF.toF {k : ℕ} {f : String} {Lin : Layout} {args : List E} {T : Tree → Prop}
    (h : PlacedLF fs cert k f Lin args T) : PlacedF fs cert k f Lin args [] T := fun fp =>
  let ⟨B, hB⟩ := h
  let ⟨n, hn⟩ := hB fp (fp + B) le_rfl
  ⟨B + n, fun rd hl hm => (hn rd hl hm).relAtInT⟩

/-- **Within the bound every valid tree meets.** -/
theorem PlacedF.toDTB {k : ℕ} {f : String} {Lin : Layout} {args rets : List E} {T : Tree → Prop} {B : ℕ}
    (h : PlacedF fs cert k f Lin args rets T)
    (hB : ∀ (rd : Reader) (t : Tree) (rets' : List E), t.name = f → t.Valid coreProgram rd args rets' →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtDTB fs cert k f Lin args (Returns rets) T B := by
  intro fp
  classical
  obtain ⟨n, hn⟩ := h fp
  by_cases hex : ∃ rd, LowDef k rd ∧ MemL rd Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    obtain ⟨t, ⟨hnm, hv, hb, -, ht, -⟩, -⟩ := hn rd1 hl1 hL1
    exact ⟨n, [], rets, [], ht ▸ hB rd1 t rets hnm hv hb, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => hn rd hl (by simpa using hL)⟩
  · exact ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- **The rest of a loop**: the next iteration's `PlacedLF`, or after the last a phantom of one frame. -/
theorem placedLF_tail {k : ℕ} {f g : String} {Lin : Layout} {args : List E} {T : Tree → Prop} {last : Prop}
    [Decidable last] (h : ¬ last → PlacedLF fs cert k f Lin args T) :
    ∃ Bt, ∀ fp c, fp + Bt ≤ c → ∃ nt, (last → Bt = fs (tailKey g) ∧ nt = 0) ∧ ∀ rd, LowDef k rd → MemL rd Lin →
      if decide (¬ last) = true then
        RelAtInCT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c Bt nt f args [] T
      else Bt = fs (tailKey g) ∧ nt = 0 := by
  by_cases hl : last
  · exact ⟨fs (tailKey g), fun _ _ _ => ⟨0, fun _ => ⟨rfl, rfl⟩, fun _ _ _ => by simp [hl]⟩⟩
  · obtain ⟨B, hB⟩ := h hl
    refine ⟨B, fun fp c hc => ?_⟩
    obtain ⟨nt, hR⟩ := hB fp c hc
    refine ⟨nt, fun h' => absurd h' hl, fun rd hlw hm => ?_⟩
    simp only [hl, not_false_eq_true, decide_true, ↓reduceIte]
    exact hR rd hlw hm

/-! ## The cell check -/

/-- The symbols a cell check's valuation holds. -/
def cellQ (syms : List E) (σ : Val) : Prop := ∀ j < 128, σ (.n (j + 1)) = syms.getD j 0

/-- **A cell check's node holding `syms`.** -/
def cellNH (syms : List E) (t : Tree) : Prop := ∃ σ ks, t = .node "da_verify_cell" σ [] ks ∧ cellQ syms σ

/-- **A cell check holding `syms` pops them.** -/
theorem cellNH_pops {syms : List E} (hsl : syms.length = 128) {t : Tree} (ht : cellNH syms t) {rd : Reader}
    {args rets : List E} (hv : t.Valid coreProgram rd args rets) :
    t.pops coreProgram rd = [("da_symbols", syms)] := by
  obtain ⟨σ, ks, rfl, hq⟩ := ht
  rw [cell_pops hv, cellPop]
  refine congrArg (fun l => [(("da_symbols" : String), l)]) (List.ext_getElem (by simp [hsl]) fun j h1 h2 => ?_)
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  rw [hq j h1, List.getD_eq_getElem _ _ (by omega)]

/-- **The cell check placed on its completing valuation**: its weights `ws` at `g^b`, which `Lin` holds. -/
theorem cell_placedF {Lin : Layout} {b : ℕ} (syms : List E) (ws : List E) (hsl : syms.length = 128)
    (hwl : ws.length = 128) (hreads : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ b) ws)
    (hreg : ∀ e < 128, RegionL Lin (b + e)) :
    PlacedF fs cert 16 "da_verify_cell" Lin [gen ^ b] (cellRets syms ws) (cellNH syms) := by
  have hok := cellp_ok
  unfold cellPOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hbe, hflat⟩, hnd⟩, hni⟩, haddr⟩, halloc⟩, hcall⟩, hloads⟩ := hok
  have hb := stmtsEqb_sound hbe
  intro fp
  refine ⟨fs "da_verify_cell", fun rd _ hm => ?_⟩
  obtain ⟨σ, e0, hsym, hh⟩ := da_verify_cell_complete_vals rd (gen ^ b) syms ws hsl hwl (hreads rd hm)
  have hdo : ∀ s ∈ cellPre, B1.DispOk σ s := fun s hs => by
    have := List.all_eq_true.mp hnd s hs
    cases s with
    | dispatch => simp [noDispatch] at this
    | _ => trivial
  have hf := find_da_verify_cell
  have hpar := da_verify_cell_params
  have hmem : fn% «da_verify_cell» ∈ coreProgram := List.mem_of_find?_eq_some hf
  have hh1 := hh fun _ _ _ => True
  generalize fn% «da_verify_cell» = F at hf hpar hmem hh1 hb
  have hw := B1.walk_flat σ [.n (val% «da_verify_cell» "s6#0"), .n (val% «da_verify_cell» "s6#0[1]"), .n (val% «da_verify_cell» "s6#0[2]")] cellPre hflat hdo
  rw [← hb] at hw
  have hsat := walk_sat (P := coreProgram) _ (coreProgram_wf _ hmem) hh1
  rw [hw] at hsat
  obtain ⟨i1, i2, i3, i4, i5⟩ := B1.flat_parts σ cellPre hflat
  have hal : allocs σ (cellPre.flatMap (B1.flEvs σ)) = [] := by rw [i2, halloc]; rfl
  have hcs : calls (cellPre.flatMap (B1.flEvs σ)) = [] := by
    rw [i4, show cellPre.filterMap (Stmt.callSF σ) = [] by
      rw [← hcall]
      refine List.filterMap_congr fun s hs => ?_
      have := List.all_eq_true.mp hnd s hs
      cases s with
      | dispatch => simp [noDispatch] at this
      | _ => rfl]
    rfl
  have hrel := relAtInWT_of_walk (P := coreProgram) (fs := fs)
    (cert := cert) (σ := σ) (rd := rd) (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0)
    (fp := fp) (args := [gen ^ b]) (rets := cellRets syms ws) coreProgram_wf hf (Or.inr hcs)
    (by rw [hpar]; simp [e0]) hw hsat.2 (fun e he => (hsat.1 e he).1)
    (by rw [hal, i1, halloc]; rfl) (by rw [i3, haddr]; simp) [] (by rw [hcs, hal]; exact ⟨rfl, fun _ h => h⟩)
    (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · obtain ⟨t, ⟨hn', hv', hb', hp', htt, hl', hd'⟩, ks, he, -⟩ := hrel
    rw [hal] at he
    exact ⟨t, ⟨hn', hv', hb', hp', by rw [htt, hal, List.sum_nil, Nat.add_zero, Nat.add_zero], hl', hd'⟩,
      σ, ks, he, hsym⟩
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    have hq' := B1.filterMap_of_loadsEv hni hq
    rw [hloads] at hq'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq'
    have he' := List.mem_range.mp he
    exact ⟨b + e, by rw [e0, limb0_gen_pow_mul], Or.inr (Or.inl (hreg e he'))⟩

/-! ## The row loop -/

end
end LeanVM.Guest.B1.Da
