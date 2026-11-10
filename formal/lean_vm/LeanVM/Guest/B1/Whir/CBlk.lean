/-
  LeanVM.Guest.B1.Whir.CBlk

  Blocks of the template at values fixed before the memory and the callees: the form the body's
  completeness takes, so that one valuation serves every memory holding the caller's words.
-/

module

public import LeanVM.Guest.B1.Whir.CRounds
public import LeanVM.Guest.B1.Whir.Lam

/-!
# Blocks at fixed values

`BlkA H σ k k' ss Out`: some values `f` on `[k, k')`, chosen before the call relation `C` and the
memory `rd`, make the block `ss` and `Out` hold of every valuation agreeing with `σ` below `k` and
holding `f` on `[k, k')`, for every `C`, `rd` with `H C rd`. Blocks compose (`BlkA.seq`), the
second built on the valuation the first leaves, knowing its outcome under `H`.

`lstF k vs`: the values `vs` listed from `k`; `lstF_at` reads them back. `OsSt.Ok σ st`: the
running state's invariants between blocks.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A block at fixed values**: some values on `[k, k')`, independent of the call relation and
the memory, make `ss` and `Out` hold wherever `H` does. -/
def BlkA (H : CallRel → Reader → Prop) (σ : Val) (k k' : ℕ) (ss : List Stmt) (Out : Val → Prop) :
    Prop :=
  ∃ f : ℕ → E, ∀ C rd, H C rd → BlkF C rd σ k k' f ss Out

variable {H : CallRel → Reader → Prop}

theorem BlkA.ofF {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out : Val → Prop} (f : ℕ → E)
    (h : ∀ C rd, H C rd → BlkF C rd σ k k' f ss Out) : BlkA H σ k k' ss Out := ⟨f, h⟩

/-- **Two blocks in sequence**, the second from the valuation the first leaves, its outcome known
under `H`. -/
theorem BlkA.seq {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA OutB : Val → Prop}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : BlkA H σ k k1 A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → (∀ C rd, H C rd → OutA σ1) → BlkA H σ1 k1 k2 B OutB) :
    BlkA H σ k k2 (A ++ B) (fun σ' ↦ OutA σ' ∧ OutB σ') := by
  obtain ⟨fA, hfA⟩ := hA
  set σ1 := fill σ k k1 fA with hσ1
  obtain ⟨fB, hfB⟩ := hB σ1 (agree_fill _ _ _ _) fun C rd hH ↦
    (hfA C rd hH σ1 (agree_fill _ _ _ _) (range_fill _ _ _ _)).2
  refine ⟨fun i ↦ if i < k1 then fA i else fB i, fun C rd hH σ' ha hr ↦ ?_⟩
  have hrA : RangeVals σ' k k1 fA := fun i hi1 hi2 ↦ by
    rw [hr i hi1 (by omega)]; simp only [hi2, ↓reduceIte]
  have hrB : RangeVals σ' k1 k2 fB := fun i hi1 hi2 ↦ by
    rw [hr i (by omega) hi2]; simp only [show ¬ i < k1 by omega, ↓reduceIte]
  have hab : AgreeBelow k1 σ1 σ' := fun i hi ↦ by
    by_cases hk : i < k
    · rw [ha i hk, hσ1, fill_lt hk]
    · rw [hrA i (by omega) hi, hσ1, fill_in (by omega) hi]
  obtain ⟨okA, oA⟩ := hfA C rd hH σ' ha hrA
  obtain ⟨okB, oB⟩ := hfB C rd hH σ' hab hrB
  exact ⟨allOk_append.mpr ⟨okA, okB⟩, oA, oB⟩

theorem BlkA.mono {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out Out' : Val → Prop}
    (h : BlkA H σ k k' ss Out) (hO : ∀ σ', Out σ' → Out' σ') : BlkA H σ k k' ss Out' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd hH ↦ (hf C rd hH).mono hO⟩

/-- An outcome holding wherever `H` does. -/
theorem BlkA.monoH {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out Out' : Val → Prop}
    (h : BlkA H σ k k' ss Out) (hO : ∀ C rd, H C rd → ∀ σ', AgreeBelow k σ σ' → Out σ' → Out' σ') :
    BlkA H σ k k' ss Out' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd hH σ' ha hr ↦ ⟨(hf C rd hH σ' ha hr).1, hO C rd hH σ' ha (hf C rd hH σ' ha hr).2⟩⟩

/-- A block under a stronger hypothesis. -/
theorem BlkA.weaken {H' : CallRel → Reader → Prop} {σ : Val} {k k' : ℕ} {ss : List Stmt}
    {Out : Val → Prop} (h : BlkA H σ k k' ss Out) (hH : ∀ C rd, H' C rd → H C rd) :
    BlkA H' σ k k' ss Out := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd h' ↦ hf C rd (hH C rd h')⟩

theorem BlkA.nil {σ : Val} {k : ℕ} {Out : Val → Prop} (hO : ∀ σ', AgreeBelow k σ σ' → Out σ') :
    BlkA H σ k k [] Out :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ BlkF.nil hO⟩

/-- A block whose statements are another's. -/
theorem BlkA.congr {σ : Val} {k k' : ℕ} {ss ss' : List Stmt} {Out : Val → Prop}
    (h : BlkA H σ k k' ss Out) (e : ss = ss') : BlkA H σ k k' ss' Out := e ▸ h

/-- An outcome that keeps the agreement below `k`. -/
theorem BlkA.agree {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out : Val → Prop}
    (h : BlkA H σ k k' ss Out) : BlkA H σ k k' ss (fun σ' ↦ Out σ' ∧ AgreeBelow k σ σ') := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd hH σ' ha hr ↦ ⟨(hf C rd hH σ' ha hr).1, (hf C rd hH σ' ha hr).2, ha⟩⟩

/-! ## Listed values -/

/-- The values `vs` from `k`. -/
def lstF (k : ℕ) (vs : List E) : ℕ → E := fun i ↦ vs.getD (i - k) 0

theorem lstF_at {σ' : Val} {k k' : ℕ} {vs : List E} (hr : RangeVals σ' k k' (lstF k vs))
    (hk : k + vs.length ≤ k') (j : ℕ) (hj : j < vs.length) : σ' (.n (k + j)) = vs.getD j 0 := by
  rw [hr _ (by omega) (by omega)]
  simp [lstF]

/-! ## A call -/

theorem osRun_map (σ : Val) (r n : ℕ) :
    (osRun r n).map σ = (List.range n).map fun j ↦ σ (.n (r + j)) := by
  simp [osRun]

/-- **A call at its returns**: the returns listed from `r`. -/
theorem call_blk {σ : Val} {r n : ℕ} {f : String} {args : List ℕ} (rets : List E)
    (hl : rets.length = n) (hargs : ∀ i ∈ args, i < r)
    (hC : ∀ C rd, H C rd → C f (args.map fun i ↦ σ (.n i)) rets) :
    BlkA H σ r (r + n) [.call f (args.map V.n) (osRun r n)]
      (fun σ' ↦ ∀ j < n, σ' (.n (r + j)) = rets.getD j 0) := by
  refine ⟨lstF r rets, fun C rd hH σ' ha hr ↦ ?_⟩
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

/-- **The running state's invariants**: five capacity cells, the carried values and
materializations below the next free value and holding, the cursor's offset a word, the zero run's
cells zero, the fixed buffers' values below it. -/
structure OsSt.Ok (σ : Val) (st : OsSt) : Prop where
  fs : st.fs.length = 5
  below : st.Below
  mats : MatsOk σ st.mats
  co : st.co < u128Bound
  pad : PadOk σ st.pad
  padB : ∀ p, st.pad = some p → p + 4 < st.k
  k : 36 ≤ st.k

/-- The state's invariants on a valuation agreeing below its next free value. -/
theorem OsSt.Ok.agree {σ σ' : Val} {st : OsSt} (h : st.Ok σ) (ha : AgreeBelow st.k σ σ') :
    st.Ok σ' := by
  refine ⟨h.fs, h.below, matsOk_agree h.mats h.below.mats fun i hi ↦ ha i hi, h.co, ?_, h.padB, h.k⟩
  intro p hp
  have hb := h.padB p hp
  obtain ⟨a, b, c, d⟩ := h.pad p hp
  rw [ha _ (by omega), ha _ (by omega), ha _ (by omega), ha _ (by omega)]
  exact ⟨a, b, c, d⟩

/-- The sponge, cursor and claim on a valuation agreeing below the next free value. -/
theorem OsSt.Ok.vals {σ σ' : Val} {st : OsSt} (h : st.Ok σ) (ha : AgreeBelow st.k σ σ') :
    st.F σ' = st.F σ ∧ st.cur σ' = st.cur σ ∧ σ' (.n st.claim) = σ (.n st.claim) := by
  obtain ⟨-, e2, e3, e4⟩ := OsSt.agree h.below ha
  exact ⟨e2, e4, e3⟩

end
end LeanVM.Guest.B1.Whir
