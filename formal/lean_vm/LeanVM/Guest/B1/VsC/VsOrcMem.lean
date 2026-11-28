/-
  LeanVM.Guest.B1.VsC.VsOrcMem

  The honest memory's facts: defined everywhere, `Pre` from the witness, the own words held, `WordsInA`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcSpec

/-!
# The honest memory's facts

On an honest context (`x.Hon`): `x.rd0` is defined everywhere (`VsCtx.lowDef_rd0`), agrees with the witness
`x.rdP` below the cursor (`VsCtx.rd0_low`), so it satisfies `Pre` (`VsCtx.pre_rd0`); it holds the own words
(`VsCtx.holdsWords_rd0`), which lie in the cursor part, pairwise apart (`VsCtx.wordsInA_Wo`, by
`bases_zip_in` and `bases_zip_pairwise`: consecutive runs from increasing bases).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Readers -/

theorem addr_inj {i j : ℕ} (hi : i < 2 ^ 64 - 1) (hj : j < 2 ^ 64 - 1) (h : addressOfIndex i = addressOfIndex j) :
    i = j :=
  gpow_injOn (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) h

/-- The first cell of `cells` at an index, its keys distinct and below the order, is its word. -/
theorem rdSet_of_mem {rd : Reader} {cells : List (ℕ × E)} (hn : (cells.map Prod.fst).Nodup)
    (hb : ∀ q ∈ cells, q.1 < 2 ^ 64 - 1) {i : ℕ} {v : E} (hq' : (i, v) ∈ cells) : rdSet rd cells (addressOfIndex i) = some v := by
  suffices key : ∀ q ∈ cells, rdSet rd cells (addressOfIndex q.1) = some q.2 from key _ hq'
  intro q hq
  unfold rdSet
  have hs : (cells.find? fun r => decide (addressOfIndex r.1 = addressOfIndex q.1)).isSome := by
    rw [List.find?_isSome]; exact ⟨q, hq, by simp⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  have hrm := List.mem_of_find?_eq_some hr
  have hre : addressOfIndex r.1 = addressOfIndex q.1 := by simpa using List.find?_some hr
  have e1 : r.1 = q.1 := addr_inj (hb r hrm) (hb q hq) hre
  have e : r = q := by
    rcases r with ⟨r1, r2⟩; rcases q with ⟨q1, q2⟩
    simp only at e1; subst e1
    have := (List.inj_on_of_nodup_map hn) hrm hq rfl
    exact this
  rw [hr, e]; rfl

/-- An address no cell's index names is `rd`'s. -/
theorem rdSet_of_not {rd : Reader} {cells : List (ℕ × E)} {A : K} (h : ∀ q ∈ cells, addressOfIndex q.1 ≠ A) :
    rdSet rd cells A = rd A := by
  unfold rdSet
  rw [List.find?_eq_none.mpr (fun q hq => by simpa using h q hq)]
  rfl

theorem exAt_of_not {ex : List (ℕ × E)} {A : K} (h : ∀ q ∈ ex, addressOfIndex q.1 ≠ A) : exAt ex A = none := by
  unfold exAt
  rw [List.find?_eq_none.mpr (fun q hq => by simpa using h q hq)]
  rfl

theorem rdW_of_not {W : Words} {i : ℕ} (hi : i < 2 ^ 64 - 1) (h : ¬ InW W i) : rdW W (addressOfIndex i) = none := by
  unfold rdW
  split
  · rename_i hh
    obtain ⟨j, hj, he, hin⟩ := hh
    exact absurd (addr_inj hi hj he ▸ hin) h
  · rfl

theorem rdSet_isSome {rd : Reader} (cells : List (ℕ × E)) (h : ∀ A, (rd A).isSome) (A : K) :
    (rdSet rd cells A).isSome := by
  unfold rdSet
  cases (cells.find? fun q => decide (addressOfIndex q.1 = A)).map Prod.snd
  · exact h A
  · rfl

/-- A load through `ptrAt q` reads index `q + o`. -/
theorem loadHolds_tr {rd rd' : Reader} {q o : ℕ} {d : E}
    (h : ∀ v, rd (addressOfIndex (q + o)) = some v → rd' (addressOfIndex (q + o)) = some v)
    (hl : LoadHolds rd (ptrAt q) o d) : LoadHolds rd' (ptrAt q) o d := by
  refine ⟨hl.1, ?_⟩
  have h2 := hl.2
  rw [Main.addr_ofK] at h2 ⊢
  exact h _ h2

/-! ## Runs from a base -/

theorem bases_length : ∀ (b : ℕ) (L : List ℕ), (bases b L).length = L.length
  | _, [] => rfl
  | b, _ :: L => by simp [bases, bases_length _ L]

/-- Run `j` lies in `[b, b + Σ)`. -/
theorem bases_getD_in : ∀ (b : ℕ) (L : List ℕ) (j : ℕ), j < L.length →
    b ≤ (bases b L).getD j 0 ∧ (bases b L).getD j 0 + L.getD j 0 ≤ b + L.sum
  | _, [], _, h => absurd h (by simp)
  | b, n :: L, 0, _ => by simp [bases]
  | b, n :: L, j + 1, h => by
    have := bases_getD_in (b + n) L j (by simpa using h)
    simp only [bases, List.getD_cons_succ, List.sum_cons]
    omega

/-- Runs `j < i` are apart: run `j` ends before run `i` starts. -/
theorem bases_getD_lt : ∀ (b : ℕ) (L : List ℕ) (j i : ℕ), j < i → i < L.length →
    (bases b L).getD j 0 + L.getD j 0 ≤ (bases b L).getD i 0
  | _, [], _, _, _, h => absurd h (by simp)
  | b, n :: L, 0, i + 1, _, h => by
    have := (bases_getD_in (b + n) L i (by simpa using h)).1
    simp only [bases, List.getD_cons_succ, List.getD_cons_zero]
    omega
  | b, n :: L, j + 1, i + 1, hji, h => by
    have := bases_getD_lt (b + n) L j i (by omega) (by simpa using h)
    simpa [bases] using this

namespace VsCtx

variable {x : VsCtx}

theorem rd1_isSome (A : K) : (x.rd1 A).isSome := by
  show ((rdW (vsRuns x.cur x.bw) A).or ((exAt x.ex A).or (some ((x.rdP A).getD 0)))).isSome
  cases rdW (vsRuns x.cur x.bw) A <;> cases exAt x.ex A <;> rfl

/-- **The evaluation memory is defined everywhere.** -/
theorem lowDef_rd0 (k : ℕ) : LowDef k x.rd0 :=
  fun _ _ => rdSet_isSome x.cells19 rd1_isSome _

/-- The buffers' sizes sum. -/
theorem vsAllocSz_sum (p : ℕ) : (vsAllocSz p).sum = 982 + 256 * p := by
  have h0 : vsSz0.sum = 824 := rfl
  rw [vsAllocSz, List.sum_append, h0]
  simp only [List.sum_cons, List.sum_nil]
  omega

theorem p_le (h : x.Hon) : x.p ≤ 32 := by
  obtain ⟨_, _, _, _, hN⟩ := frontNum_of_child h.ok.child
  exact hN.hp

/-- Every index from the buffers on lies below `cur + 2^14`, so below the generator's order. -/
theorem top_lt (h : x.Hon) : x.cur + (vsAllocSz x.p).sum < 2 ^ 60 + 2 ^ 14 := by
  have := p_le h; have := h.ok.hcur; rw [vsAllocSz_sum]; omega

theorem vsAllocSz_length (p : ℕ) : (vsAllocSz p).length = 24 := rfl

theorem vsAllocSz_13 (p : ℕ) : (vsAllocSz p).getD 13 0 = 12 := rfl

/-- Own buffer `j`'s run lies in `[cur, cur + Σ)`. -/
theorem base_lt (_ : x.Hon) (j : ℕ) (hj : j < 24) :
    x.cur ≤ x.base j ∧ x.base j + (vsAllocSz x.p).getD j 0 ≤ x.cur + (vsAllocSz x.p).sum :=
  bases_getD_in x.cur (vsAllocSz x.p) j (by rw [vsAllocSz_length]; exact hj)

/-- **The evaluation memory below the cursor is the witness's.** -/
theorem rd0_low (h : x.Hon) {i : ℕ} (hi : i < x.cur) {v : E} (hv : x.rdP (addressOfIndex i) = some v) :
    x.rd0 (addressOfIndex i) = some v := by
  have ht := top_lt h
  have hc := h.ok.hcur
  have e0 : x.rd0 (addressOfIndex i) = x.rd1 (addressOfIndex i) := by
    refine rdSet_of_not fun q hq he => ?_
    simp only [cells19, vsCells19, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    simp only at he
    have hb := (base_lt h 13 (by omega))
    have := addr_inj (by omega) (by omega) he
    omega
  rw [e0]
  show (rdW (vsRuns x.cur x.bw) (addressOfIndex i)).or ((exAt x.ex (addressOfIndex i)).or
    (some ((x.rdP (addressOfIndex i)).getD 0))) = some v
  rw [rdW_of_not (by omega) ?_, exAt_of_not ?_, hv]
  · rfl
  · intro q hq he
    have := h.hex q hq
    have := addr_inj (by omega) (by omega) he
    omega
  · rintro ⟨q, hq, h1, h2⟩
    have := (bases_zip_in x.cur x.bw q hq).1
    omega

/-- **The evaluation memory satisfies `Pre`.** -/
theorem pre_rd0 (h : x.Hon) : x.Pre x.rd0 := by
  have hP := h.ok.pre
  have ht := h.ok.ht
  have ho := h.ok.ho
  have hf := h.ok.hfc
  have tr : ∀ q o, q + o < x.cur → ∀ d, LoadHolds x.rdP (ptrAt q) o d → LoadHolds x.rd0 (ptrAt q) o d :=
    fun q o hqo d => loadHolds_tr fun v hv => rd0_low h hqo hv
  have hP' : (ExpTables x.rdP (ptrAt x.qt) ∧ ExpWinTab x.rdP (ptrAt x.qt)) ∧
      ReadsAt x.rdP (ptrAt x.qo) x.c.freshClaim.cells := hP
  obtain ⟨⟨⟨hE1, hE2⟩, hW⟩, hC⟩ := hP'
  show (ExpTables x.rd0 (ptrAt x.qt) ∧ ExpWinTab x.rd0 (ptrAt x.qt)) ∧ ReadsAt x.rd0 (ptrAt x.qo) x.c.freshClaim.cells
  have hL : 178 ≤ expTabLen := by decide
  have hL2 : winTabAt + 2 ^ winTabBits ≤ expTabLen := le_rfl
  refine ⟨⟨⟨fun j hj => tr _ _ ?_ _ (hE1 j hj), fun j hj u hu => tr _ _ ?_ _ (hE2 j hj u hu)⟩,
    fun n hn => tr _ _ ?_ _ (hW n hn)⟩, fun k hk => tr _ _ ?_ _ (hC k hk)⟩
  · simp only [sizeBits] at hj; omega
  · simp only [sizeBits, selTabNibbles] at hj hu ⊢; omega
  · omega
  · omega

/-- The own words' lists: the buffers' words, `.n 19`'s the overlay's. -/
noncomputable def Lw (x : VsCtx) : List (List E) := x.bw.set 13 (x.cells19.map Prod.snd)

theorem cells19_length : x.cells19.length = 12 := by
  rw [cells19, vsCells19, List.length_map, List.length_range]

theorem Lw_sizes (h : x.Hon) : x.Lw.map List.length = vsAllocSz x.p := by
  rw [Lw, List.map_set, h.hbw, List.length_map, cells19_length]
  rfl

theorem Wo_eq (h : x.Hon) : x.Wo = (bases x.cur (x.Lw.map List.length)).zip x.Lw := by
  rw [Lw_sizes h]; rfl

/-- **The own words lie in the cursor part, pairwise apart.** -/
theorem wordsInA_Wo (h : x.Hon) (hall : allocs x.σ0 (vsEs x.σ0) = vsAllocSz x.p) (lo hi : ℕ) :
    WordsInA x.Wo lo hi x.cur (x.cur + (allocs x.σ0 (vsEs x.σ0)).sum) := by
  rw [hall, Wo_eq h]
  refine ⟨fun q hq => Or.inr ?_, bases_zip_pairwise _ _⟩
  have := bases_zip_in x.cur x.Lw q hq
  rw [Lw_sizes h] at this
  exact this

theorem bw_length (h : x.Hon) : x.bw.length = 24 := by
  rw [← List.length_map (f := List.length), h.hbw, vsAllocSz_length]

theorem Lw_getD (h : x.Hon) {j : ℕ} (hj : j < 24) :
    x.Lw.getD j [] = if j = 13 then x.cells19.map Prod.snd else x.bw.getD j [] := by
  have hl := bw_length h
  by_cases e : j = 13
  · subst e
    simp [Lw, List.getD_eq_getElem?_getD, hl]
  · simp only [e, ↓reduceIte]
    rw [Lw, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm e), ← List.getD_eq_getElem?_getD]

theorem vsCells19_mem (b : ℕ) (σ : Val) {k : ℕ} (hk : k < 12) :
    (b + k, σ (.n (vs19Src.getD k 0))) ∈ vsCells19 b σ := by
  simp only [vsCells19, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩

theorem vsCells19_nodup (b : ℕ) (σ : Val) : ((vsCells19 b σ).map Prod.fst).Nodup := by
  simp only [vsCells19, List.map_map, Function.comp_def]
  exact List.nodup_range.map (fun a c e => by simpa using e)

theorem vsCells19_lt {b : ℕ} {σ : Val} (hb : b + 12 < 2 ^ 64 - 1) : ∀ q ∈ vsCells19 b σ, q.1 < 2 ^ 64 - 1 := by
  intro q hq
  simp only [vsCells19, List.mem_map, List.mem_range] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only; omega

theorem vsCells19_getD (b : ℕ) (σ : Val) {k : ℕ} (hk : k < 12) :
    ((vsCells19 b σ).map Prod.snd).getD k 0 = σ (.n (vs19Src.getD k 0)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp only [vsCells19, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]

theorem rd1_of_rdW {A : K} {v : E} (h : rdW (vsRuns x.cur x.bw) A = some v) : x.rd1 A = some v := by
  unfold rd1 vsRd1; rw [h]; rfl

theorem rd0_of_mem {A : K} {v : E} (h : rdSet x.rd1 x.cells19 A = some v) : x.rd0 A = some v := h

/-- The overlay's run: word `k < 12` of `.n 19` is its stored value. -/
theorem rd0_run13 (h : x.Hon) {k : ℕ} (hk' : k < 12) :
    x.rd0 (addressOfIndex (x.base 13 + k)) = some ((x.cells19.map Prod.snd).getD k 0) := by
  have ht := top_lt h
  have h13 := vsAllocSz_13 x.p
  have hb13 := base_lt h 13 (by omega)
  have hb : ∀ q ∈ vsCells19 (x.base 13) (vsVal x.rd1 x.w x.args), q.1 < 2 ^ 64 - 1 :=
    vsCells19_lt (by omega)
  have hv := vsCells19_getD (x.base 13) (vsVal x.rd1 x.w x.args) hk'
  rw [cells19, hv]
  exact rdSet_of_mem (rd := x.rd1) (vsCells19_nodup _ _) hb (vsCells19_mem _ _ hk')

/-- A buffer run but the overlay's: word `k` is the buffers' words'. -/
theorem rd0_runNe (h : x.Hon) {j : ℕ} (hj : j < 24) (e13 : j ≠ 13) {k : ℕ} (hk : k < (vsAllocSz x.p).getD j 0) :
    x.rd0 (addressOfIndex (x.base j + k)) = some ((x.bw.getD j []).getD k 0) := by
  have ht := top_lt h
  have hl := bw_length h
  have h13 := vsAllocSz_13 x.p
  have hbj := base_lt h j hj
  have hb13 := base_lt h 13 (by omega)
  have hjl : j < (bases x.cur (vsAllocSz x.p)).length := by rw [bases_length, vsAllocSz_length]; exact hj
  have hmem : (x.base j, x.bw.getD j []) ∈ vsRuns x.cur x.bw := by
    rw [vsRuns, h.hbw]
    have := List.getElem_mem (l := (bases x.cur (vsAllocSz x.p)).zip x.bw)
      (by rw [List.length_zip, bases_length, vsAllocSz_length, hl]; omega : j < _)
    rw [List.getElem_zip] at this
    rwa [base, List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ (by omega)]
  have hsz : (x.bw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
    rw [← h.hbw, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by rw [List.length_map]; omega),
      List.getElem_map]
  have hW := holdsWords_rdW (bases_zip_pairwise x.cur x.bw) (fun q hq => by
    have := bases_zip_in x.cur x.bw q hq; rw [h.hbw] at this; omega) _ hmem k (by rw [hsz]; exact hk)
  have h2 := hW.2
  rw [Main.addr_ofK] at h2
  have e1 : x.rd1 (addressOfIndex (x.base j + k)) = some ((x.bw.getD j []).getD k 0) := by
    rw [List.getD_eq_getElem _ _ (by rw [hsz]; exact hk)]
    exact rd1_of_rdW h2
  rw [← e1]
  refine rdSet_of_not fun q hq he => ?_
  simp only [cells19, vsCells19, List.mem_map, List.mem_range] at hq
  obtain ⟨t, ht', rfl⟩ := hq
  simp only at he
  have := addr_inj (by omega) (by omega) he
  rcases Nat.lt_or_gt_of_ne e13 with hlt | hlt
  · have := bases_getD_lt x.cur (vsAllocSz x.p) j 13 hlt (by rw [vsAllocSz_length]; omega)
    simp only [base] at *
    omega
  · have := bases_getD_lt x.cur (vsAllocSz x.p) 13 j hlt (by rw [vsAllocSz_length]; omega)
    simp only [base] at *
    omega

/-- **The evaluation memory on own buffer `j`**: word `k` is the own words'. -/
theorem rd0_run (h : x.Hon) {j : ℕ} (hj : j < 24) {k : ℕ} (hk : k < (vsAllocSz x.p).getD j 0) :
    x.rd0 (addressOfIndex (x.base j + k)) = some ((x.Lw.getD j []).getD k 0) := by
  rw [Lw_getD h hj]
  by_cases e13 : j = 13
  · subst e13
    simp only [↓reduceIte]
    exact rd0_run13 h (by rw [vsAllocSz_13] at hk; exact hk)
  · simp only [e13, ↓reduceIte]
    exact rd0_runNe h hj e13 hk

theorem bases_cover : ∀ (b : ℕ) (L : List ℕ) (i : ℕ), b ≤ i → i < b + L.sum →
    ∃ q ∈ L.zip (bases b L), q.2 ≤ i ∧ i < q.2 + q.1
  | _, [], _, h1, h2 => by simp at h2; omega
  | b, n :: L, i, h1, h2 => by
    simp only [List.sum_cons] at h2
    by_cases hi : i < b + n
    · exact ⟨(n, b), by simp [bases], h1, by omega⟩
    · obtain ⟨q, hq, h⟩ := bases_cover (b + n) L i (by omega) (by omega)
      exact ⟨q, by simp only [bases, List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq, h⟩

/-- **The buffers' cells are `verify_sub`'s own**, its allocations the honest sizes. -/
theorem ownB_own (hall : allocs x.σ0 (vsEs x.σ0) = vsAllocSz x.p) : ∀ i, x.OwnB i → x.Own i := by
  intro i ⟨h1, h2⟩
  show ownData B2C.cert x.fp x.cur "verify_sub" (allocs x.σ0 (vsEs x.σ0)) (vsEs x.σ0) i
  rw [hall]
  exact Or.inl (bases_cover x.cur (vsAllocSz x.p) i h1 h2)

/-- **The evaluation memory holds the own words.** -/
theorem holdsWords_rd0 (h : x.Hon) : HoldsWords x.rd0 x.Wo := by
  have hbl : (bases x.cur (vsAllocSz x.p)).length = 24 := by rw [bases_length, vsAllocSz_length]
  have hLl : x.Lw.length = 24 := by rw [Lw, List.length_set, bw_length h]
  rintro ⟨b, l⟩ hq k hk
  have hWo : x.Wo = (bases x.cur (vsAllocSz x.p)).zip x.Lw := rfl
  rw [hWo, List.mem_iff_getElem] at hq
  obtain ⟨j, hj, hq⟩ := hq
  rw [List.getElem_zip, Prod.mk.injEq] at hq
  have hj' : j < 24 := by rw [List.length_zip, hbl, hLl] at hj; omega
  obtain ⟨e1, e2⟩ := hq
  have eb : b = x.base j := by rw [← e1, base, List.getD_eq_getElem _ _ (by omega)]
  have el : l = x.Lw.getD j [] := by rw [← e2, List.getD_eq_getElem _ _ (by omega)]
  subst eb el
  simp only at hk ⊢
  have hsz : (x.Lw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
    rw [← Lw_sizes h, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by rw [List.length_map]; omega),
      List.getElem_map]
  refine ⟨Value.ofK_isInK _, ?_⟩
  rw [Main.addr_ofK, rd0_run h hj' (by rw [← hsz]; exact hk), List.getD_eq_getElem _ _ hk]

end VsCtx

/-! ## The composition -/

/-- **The honest contexts exist**: at every placement (`Ok`), end cursors, buffers' words, extra cells and a
return rule making it honest (the helpers' conditions, the closed forms). -/
def VsHonEx (al : String → Bool) : Prop :=
  ∀ x : VsCtx, x.al = al → x.Ok → ∃ (ec : ℕ → ℕ) (bw : List (List E)) (ex : List (ℕ × E)) (ret : ℕ → (ℕ → E) → E),
    ({ x with ec := ec, bw := bw, ex := ex, ret := ret } : VsCtx).Hon

/-- **`verify_sub`'s allocations are the honest sizes** on an honest context whose body walks through. -/
def VsAllocsHyp : Prop :=
  ∀ x : VsCtx, x.Hon → (∃ es, walk x.σ0 vsSS = .fall es) → allocs x.σ0 (vsEs x.σ0) = vsAllocSz x.p

/-- **The windows' first state is the honest allocations' one** once the body allocates `vsAllocSz p`. -/
theorem VsCtx.st0_eq {x : VsCtx} (hall : allocs x.σ0 (vsEs x.σ0) = vsAllocSz x.p) : x.st0 = x.st0B := by
  simp only [VsCtx.st0, VsCtx.st0B, vsSt0, hall]

/-- **The honest oracle's statement from the phases' and the honest contexts**: the phases at `Own = True`
give the body's walk, so the allocations, so the phases at `verify_sub`'s own cells. -/
theorem vsOrcWFromCallees_of_specs {al : String → Bool} (hF : FrontS al) (h1 : Ph4to6S al) (h2 : Ph7to11S al)
    (h3 : Ph12toEndS al) (hH : VsHonEx al) (hA : VsAllocsHyp) : VsOrcWFromCallees al 17 := by
  intro _ hc seed c qt qo fp cur hcc ht ho hfc ⟨rdP, hP⟩ hcur
  obtain ⟨ec, bw, ex, ret, hx⟩ := hH ⟨al, seed, c, qt, qo, fp, cur, rdP, fun _ => 0, [], [], fun _ _ => 0⟩ rfl
    ⟨hcc, ht, ho, hfc, hP, hcur⟩
  have hT := vsPhases_of_specs hF h1 h2 h3 rfl hx hc (Own := fun _ => True) fun _ _ => trivial
  obtain ⟨es, _, _, hw, -⟩ := vs_seg (fp := fp) rfl (vsHyp_of_orc (by norm_num) rfl hT)
  have hall := hA _ hx ⟨es, hw⟩
  have H := vsPhases_of_specs hF h1 h2 h3 rfl hx hc (VsCtx.ownB_own hall)
  rw [← VsCtx.st0_eq hall] at H
  exact ⟨_, _, _, VsCtx.wordsInA_Wo hx hall _ _, H⟩

end
end LeanVM.Guest.B1.VsC
