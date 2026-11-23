/-
  LeanVM.Guest.B1.Whir.CBlk

  Blocks of the template at values fixed before the memory and the callees: the form the body's
  completeness takes, so that one valuation serves every memory holding the caller's words.
-/

module

public import LeanVM.Guest.B1.Whir.CRounds
public import LeanVM.Guest.B1.Whir.Lam
public import LeanVM.Guest.B1.Whir.WinEx

/-!
# Blocks at fixed values

`BlkA M H σ k k' ss Out`: some values `f` on `[k, k')`, chosen before the call relation `C` and the
memory `rd`, make the block `ss` and `Out` hold of every valuation agreeing with `σ` below `k` and
holding `f` on `[k, k')`, for every `C`, `rd` with `H C rd`, and the block's loads hold on every
memory satisfying `M` (`LoadsIn`), so that each reads a word `M` fixes, and its window hints are
exact (`WinEx`): the inlined grind checks' (`gc_blk`). A block without range checks holds on `HM M H`
(`H`, or a memory satisfying `M` with the trivial call relation) and so gives its loads, and has no
window hints (`BlkA.ofHM`, `Stmt.noWin`, by `rfl` where the block's statements are listed). Blocks
compose (`BlkA.seq`), the second built on the valuation the first leaves, knowing its outcome under
`HM M H`.

`lstF k vs`: the values `vs` listed from `k`; `lstF_at` reads them back. `OsSt.Ok σ st`: the
running state's invariants between blocks.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A statement's load: its destination, pointer and offset. -/
def ldT : Stmt → Option (V × V × ℕ)
  | .atom (.load d p off) => some (d, p, off)
  | _ => none

/-- **The loads of `ss` hold on `rd`** at `σ`: each reads its destination's value. -/
def LoadsHold (rd : Reader) (σ : Val) (ss : List Stmt) : Prop :=
  ∀ q ∈ ss.filterMap ldT, LoadHolds rd (σ q.2.1) q.2.2 (σ q.1)

/-- **The loads of `ss` hold on every memory satisfying `M`** at `σ`. -/
def LoadsIn (M : Reader → Prop) (ss : List Stmt) (σ : Val) : Prop := ∀ rd, M rd → LoadsHold rd σ ss

theorem loadsHold_append {rd : Reader} {σ : Val} {ss ts : List Stmt} :
    LoadsHold rd σ (ss ++ ts) ↔ LoadsHold rd σ ss ∧ LoadsHold rd σ ts := by
  simp only [LoadsHold, List.filterMap_append, List.mem_append]
  exact ⟨fun h ↦ ⟨fun q hq ↦ h q (Or.inl hq), fun q hq ↦ h q (Or.inr hq)⟩,
    fun h q hq ↦ hq.elim (h.1 q) (h.2 q)⟩

theorem loadsIn_append {M : Reader → Prop} {σ : Val} {ss ts : List Stmt} :
    LoadsIn M (ss ++ ts) σ ↔ LoadsIn M ss σ ∧ LoadsIn M ts σ :=
  ⟨fun h ↦ ⟨fun rd hm ↦ (loadsHold_append.mp (h rd hm)).1, fun rd hm ↦ (loadsHold_append.mp (h rd hm)).2⟩,
    fun h rd hm ↦ loadsHold_append.mpr ⟨h.1 rd hm, h.2 rd hm⟩⟩

/-- The loads hold wherever the block does. -/
theorem loadsHold_of_allOk {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} (h : AllOk C rd σ ss) :
    LoadsHold rd σ ss := by
  intro q hq
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp hq
  match s, he with
  | .atom (.load d p off), he =>
    simp only [ldT, Option.some.injEq] at he
    subst he
    exact h _ hs

/-- **A block at fixed values**: some values `f` on `[k, k')`, independent of the call relation and
the memory, make `ss` and `Out` hold wherever `H` does, its loads holding on every memory
satisfying `M`, its window hints exact. -/
def BlkA (M : Reader → Prop) (H : CallRel → Reader → Prop) (σ : Val) (k k' : ℕ) (ss : List Stmt)
    (Out : Val → Prop) : Prop :=
  ∃ f : ℕ → E, ∀ C rd, H C rd → BlkF C rd σ k k' f ss (fun σ' ↦ (LoadsIn M ss σ' ∧ WinEx ss σ') ∧ Out σ')

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

/-- **`H`, or a memory satisfying `M` with the trivial call relation**, where `H` holds somewhere:
what a block without range checks holds on, so that its loads hold on every memory satisfying
`M` (`BlkA.ofHM`). -/
def HM (M : Reader → Prop) (H : CallRel → Reader → Prop) (C : CallRel) (rd : Reader) : Prop :=
  H C rd ∨ (M rd ∧ C = (fun _ _ _ ↦ True) ∧ ∃ C0 rd0, H C0 rd0)

theorem HM.ex {C : CallRel} {rd : Reader} (h : HM M H C rd) : ∃ C0 rd0, H C0 rd0 :=
  h.elim (fun h ↦ ⟨C, rd, h⟩) (·.2.2)

/-- A fact independent of the memory and the callees, from `H`. -/
theorem HM.indep {Q : Prop} (h : ∀ C rd, H C rd → Q) : ∀ C rd, HM M H C rd → Q :=
  fun _ _ hh ↦ let ⟨C0, rd0, h0⟩ := hh.ex; h C0 rd0 h0

/-- **A block without range checks**: holding on `HM M H`, its loads hold on `M`; without window hints. -/
theorem BlkA.ofHM {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out : Val → Prop} (f : ℕ → E)
    (h : ∀ C rd, HM M H C rd → BlkF C rd σ k k' f ss Out) (hw : ss.all Stmt.noWin = true := by rfl) :
    BlkA M H σ k k' ss Out :=
  ⟨f, fun C rd hH σ' ha hr ↦ ⟨(h C rd (.inl hH) σ' ha hr).1,
    ⟨fun rd' hm ↦ loadsHold_of_allOk (h _ rd' (.inr ⟨hm, rfl, C, rd, hH⟩) σ' ha hr).1, winEx_of_noWin hw⟩,
    (h C rd (.inl hH) σ' ha hr).2⟩⟩

/-- A block from its values, its loads and window hints given apart. -/
theorem BlkA.mk {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out : Val → Prop} (f : ℕ → E)
    (h : ∀ C rd, H C rd → BlkF C rd σ k k' f ss Out)
    (hL : ∀ C rd, H C rd → ∀ σ', AgreeBelow k σ σ' → RangeVals σ' k k' f → LoadsIn M ss σ')
    (hW : ∀ σ', AgreeBelow k σ σ' → RangeVals σ' k k' f → WinEx ss σ') :
    BlkA M H σ k k' ss Out :=
  ⟨f, fun C rd hH σ' ha hr ↦ ⟨(h C rd hH σ' ha hr).1, ⟨hL C rd hH σ' ha hr, hW σ' ha hr⟩,
    (h C rd hH σ' ha hr).2⟩⟩

/-- **Two blocks in sequence**, the second from the valuation the first leaves, its outcome known
under `H`. -/
theorem BlkA.seq {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA OutB : Val → Prop}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : BlkA M H σ k k1 A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → (∀ C rd, HM M H C rd → OutA σ1) → BlkA M H σ1 k1 k2 B OutB) :
    BlkA M H σ k k2 (A ++ B) (fun σ' ↦ OutA σ' ∧ OutB σ') := by
  obtain ⟨fA, hfA⟩ := hA
  set σ1 := fill σ k k1 fA with hσ1
  obtain ⟨fB, hfB⟩ := hB σ1 (agree_fill _ _ _ _) (HM.indep fun C rd hH ↦
    (hfA C rd hH σ1 (agree_fill _ _ _ _) (range_fill _ _ _ _)).2.2)
  refine ⟨fun i ↦ if i < k1 then fA i else fB i, fun C rd hH σ' ha hr ↦ ?_⟩
  have hrA : RangeVals σ' k k1 fA := fun i hi1 hi2 ↦ by
    rw [hr i hi1 (by omega)]; simp only [hi2, ↓reduceIte]
  have hrB : RangeVals σ' k1 k2 fB := fun i hi1 hi2 ↦ by
    rw [hr i (by omega) hi2]; simp only [show ¬ i < k1 by omega, ↓reduceIte]
  have hab : AgreeBelow k1 σ1 σ' := fun i hi ↦ by
    by_cases hk : i < k
    · rw [ha i hk, hσ1, fill_lt hk]
    · rw [hrA i (by omega) hi, hσ1, fill_in (by omega) hi]
  obtain ⟨okA, lA, oA⟩ := hfA C rd hH σ' ha hrA
  obtain ⟨okB, lB, oB⟩ := hfB C rd hH σ' hab hrB
  exact ⟨allOk_append.mpr ⟨okA, okB⟩, ⟨loadsIn_append.mpr ⟨lA.1, lB.1⟩, winEx_append.mpr ⟨lA.2, lB.2⟩⟩, oA, oB⟩

theorem BlkA.mono {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out Out' : Val → Prop}
    (h : BlkA M H σ k k' ss Out) (hO : ∀ σ', Out σ' → Out' σ') : BlkA M H σ k k' ss Out' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd hH ↦ (hf C rd hH).mono fun σ' o ↦ ⟨o.1, hO σ' o.2⟩⟩

/-- An outcome holding wherever `H` does. -/
theorem BlkA.monoH {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out Out' : Val → Prop}
    (h : BlkA M H σ k k' ss Out)
    (hO : ∀ C rd, HM M H C rd → ∀ σ', AgreeBelow k σ σ' → Out σ' → Out' σ') :
    BlkA M H σ k k' ss Out' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd hH σ' ha hr ↦ ⟨(hf C rd hH σ' ha hr).1, (hf C rd hH σ' ha hr).2.1,
    hO C rd (.inl hH) σ' ha (hf C rd hH σ' ha hr).2.2⟩⟩

/-- A block under a stronger hypothesis. -/
theorem BlkA.weaken {H' : CallRel → Reader → Prop} {σ : Val} {k k' : ℕ} {ss : List Stmt}
    {Out : Val → Prop} (h : BlkA M H σ k k' ss Out) (hH : ∀ C rd, H' C rd → H C rd) :
    BlkA M H' σ k k' ss Out := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd h' ↦ hf C rd (hH C rd h')⟩

theorem BlkA.nil {σ : Val} {k : ℕ} {Out : Val → Prop} (hO : ∀ σ', AgreeBelow k σ σ' → Out σ') :
    BlkA M H σ k k [] Out :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ BlkF.nil fun σ' ha ↦ ⟨⟨fun _ _ _ hq ↦ absurd hq List.not_mem_nil, winEx_nil⟩, hO σ' ha⟩⟩

/-- A block whose statements are another's. -/
theorem BlkA.congr {σ : Val} {k k' : ℕ} {ss ss' : List Stmt} {Out : Val → Prop}
    (h : BlkA M H σ k k' ss Out) (e : ss = ss') : BlkA M H σ k k' ss' Out := e ▸ h

/-- **A block is needed only where `H` holds somewhere.** -/
theorem BlkA.of_ne {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out : Val → Prop}
    (h : (∃ C rd, HM M H C rd) → BlkA M H σ k k' ss Out) : BlkA M H σ k k' ss Out := by
  by_cases hne : ∃ C rd, H C rd
  · obtain ⟨C, rd, hH⟩ := hne
    exact h ⟨C, rd, .inl hH⟩
  · exact ⟨fun _ ↦ 0, fun C rd hH ↦ absurd ⟨C, rd, hH⟩ hne⟩

/-- An outcome that keeps the agreement below `k`. -/
theorem BlkA.agree {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out : Val → Prop}
    (h : BlkA M H σ k k' ss Out) : BlkA M H σ k k' ss (fun σ' ↦ Out σ' ∧ AgreeBelow k σ σ') := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd hH σ' ha hr ↦ ⟨(hf C rd hH σ' ha hr).1, (hf C rd hH σ' ha hr).2.1,
    (hf C rd hH σ' ha hr).2.2, ha⟩⟩

/-! ## Without window hints -/

theorem osMatP_noWin (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    (osMatP plan mats base off k).1.all Stmt.noWin = true := by
  unfold osMatP; split <;> rfl

theorem osMat_noWin (base off k : ℕ) : (osMat base off k).1.all Stmt.noWin = true := by
  unfold osMat; split <;> rfl

theorem osRates_noWin (c : OsCfg) (lvl : ℕ) (s : OsSt) : (osRates c lvl s).1.all Stmt.noWin = true := by
  unfold osRates
  refine noWin_cons rfl (noWin_cons (noWin_match fun arm harm => ?_) rfl)
  obtain ⟨⟨lv, r⟩, -, rfl⟩ := List.mem_map.mp harm
  exact noWin_flatten_map fun ⟨_, _⟩ => rfl

/-! ## Listed values -/

/-- The values `vs` from `k`. -/
def lstF (k : ℕ) (vs : List E) : ℕ → E := fun i ↦ vs.getD (i - k) 0

theorem lstF_at {σ' : Val} {k k' : ℕ} {vs : List E} (hr : RangeVals σ' k k' (lstF k vs))
    (hk : k + vs.length ≤ k') (j : ℕ) (hj : j < vs.length) : σ' (.n (k + j)) = vs.getD j 0 := by
  rw [hr _ (by omega) (by omega)]
  simp [lstF]

/-- **A block at listed values**: each statement holding at them. -/
theorem blk_lst {σ : Val} {k k' : ℕ} {ss : List Stmt} (vs : List E) {Out : Val → Prop}
    (hk : k + vs.length ≤ k')
    (h : ∀ C rd, HM M H C rd → ∀ σ', AgreeBelow k σ σ' →
      (∀ j < vs.length, σ' (.n (k + j)) = vs.getD j 0) → AllOk C rd σ' ss ∧ Out σ')
    (hw : ss.all Stmt.noWin = true := by rfl) :
    BlkA M H σ k k' ss Out :=
  BlkA.ofHM (lstF k vs) (fun C rd hH σ' ha hr ↦ h C rd hH σ' ha (lstF_at hr hk)) hw

/-! ## A call -/

theorem osRun_map (σ : Val) (r n : ℕ) :
    (osRun r n).map σ = (List.range n).map fun j ↦ σ (.n (r + j)) := by
  simp [osRun]

/-- **A call at its returns**: the returns listed from `r`. -/
theorem call_blk {σ : Val} {r n : ℕ} {f : String} {args : List ℕ} (rets : List E)
    (hl : rets.length = n) (hargs : ∀ i ∈ args, i < r)
    (hC : ∀ C rd, HM M H C rd → C f (args.map fun i ↦ σ (.n i)) rets) :
    BlkA M H σ r (r + n) [.call f (args.map V.n) (osRun r n)]
      (fun σ' ↦ ∀ j < n, σ' (.n (r + j)) = rets.getD j 0) := by
  refine BlkA.ofHM (lstF r rets) fun C rd hH σ' ha hr ↦ ?_
  have hv : ∀ j < n, σ' (.n (r + j)) = rets.getD j 0 := fun j hj ↦
    lstF_at hr (by omega) j (by omega)
  refine ⟨?_, hv⟩
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call]
  have e1 : (args.map V.n).map σ' = args.map fun i ↦ σ (.n i) := by
    simp only [List.map_map]
    exact List.map_congr_left fun i hi ↦ ha i (hargs i hi)
  have e2 : (osRun r n).map σ' = rets := by
    rw [osRun_map]
    refine List.ext_getElem (by simp [hl]) fun j h1 h2 ↦ ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hv j h1, List.getD_eq_getElem _ _ h2]
  rw [e1, e2]
  exact hC C rd hH

/-! ## The running state -/

/-- **The running state's static facts**: five capacity cells, the carried values and
materializations below the next free value, the cursor's offset a word, the zero run below it,
the fixed buffers' values below it. -/
structure OsSt.Sf (st : OsSt) : Prop where
  fs : st.fs.length = 5
  below : st.Below
  co : st.co < u128Bound
  padB : ∀ p, st.pad = some p → p + 4 < st.k
  k : 43 ≤ st.k

/-- **The running state's invariants**: its static facts, the materializations holding, the zero
run's cells zero. -/
structure OsSt.Ok (σ : Val) (st : OsSt) : Prop where
  sf : st.Sf
  mats : MatsOk σ st.mats
  pad : PadOk σ st.pad

/-- The state's invariants on a valuation agreeing below its next free value. -/
theorem OsSt.Ok.agree {σ σ' : Val} {st : OsSt} (h : st.Ok σ) (ha : AgreeBelow st.k σ σ') :
    st.Ok σ' := by
  refine ⟨h.sf, matsOk_agree h.mats h.sf.below.mats fun i hi ↦ ha i hi, ?_⟩
  intro p hp
  have hb := h.sf.padB p hp
  obtain ⟨a, b, c, d⟩ := h.pad p hp
  rw [ha _ (by omega), ha _ (by omega), ha _ (by omega), ha _ (by omega)]
  exact ⟨a, b, c, d⟩

/-- The sponge, cursor and claim on a valuation agreeing below the next free value. -/
theorem OsSt.Sf.vals {σ σ' : Val} {st : OsSt} (h : st.Sf) (ha : AgreeBelow st.k σ σ') :
    st.F σ' = st.F σ ∧ st.cur σ' = st.cur σ ∧ σ' (.n st.claim) = σ (.n st.claim) := by
  obtain ⟨-, e2, e3, e4⟩ := OsSt.agree h.below ha
  exact ⟨e2, e4, e3⟩

end
end LeanVM.Guest.B1.Whir
