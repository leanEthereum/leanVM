/-
  LeanVM.Prover.Complete.Link.TailRowCols

  The honest prover's pointer columns at the row point, in closed form: each column's
  coefficients are its row coefficients at the columns' extensions.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowFacts

/-!
# The pointer columns at the row point

`columnsAt_eq_map`: a bound table's pointer columns are `colSpec` of its pointers, the coefficient
tables read off by position replaced by their extensions. `rowCoefs_mem`: a memory pointer's row
coefficient, its word reads ungrouped (`sum_wordReads`). `mleA_coefTable_fst`, `..._snd`: each
coefficient table's extension is the row coefficient at the columns' extensions (`Affine`), the
successor forms and the word-read scales being of degree at most one.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open Finset

/-! ## The columns by position -/

section Columns

variable (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable) (chi : List E)

/-- Table `t`'s coefficient table of its pointer column `(pointer, k)`: `(c_ω, c_act)` per row. -/
def coefTable (k pointer : ℕ) : Array (E × E) :=
  Array.ofFn (n := 2 ^ W.layout.tableLogHeights.getD t 0) fun u ↦
    rowCoefs inp (tables.getD t default).links (inp.ch.mu.getD t []) k pointer (rowValue (W.tableCols t) u)

theorem rowPointerStep_AB (acc : Array (Array E) × Array (E × Array ℕ) × ℕ) (pk : ℕ × ℕ) :
    ∃ rest : List (Array E), (rowPointerStep W inp t q₀ acc pk).1.toList = acc.1.toList ++
      [(coefTable W inp t pk.2 pk.1).map (·.1), (coefTable W inp t pk.2 pk.1).map (·.2)] ++ rest := by
  obtain ⟨tabs, terms, pos⟩ := acc
  unfold rowPointerStep coefTable
  dsimp only
  simp only [Array.toList_append, List.append_assoc, List.cons_append, List.nil_append]
  exact ⟨_, rfl⟩

/-- The column at `(pointer, k)` whose coefficient tables read `cw` and `ca`. -/
def tailRowColAt (cw ca : E) (pointer k : ℕ) : ColumnAt :=
  let ch := inp.ch
  let d := W.chunks.d
  let links := (tables.getD t default).links
  let mu := ch.mu.getD t []
  let cols := W.tableCols t
  let point := chi.take rt.height
  let P := rt.prods
  let omega := P.at 0
  let slices := columnSlices (cols.getD pointer #[]) point
  let coef := omega * cw + P.at 1 * ca
  let shifts := (List.range inp.maxShift).map fun s ↦
    sumE ((accessesAt links mu pointer).map fun (a, m) ↦
      if a.shift = s + 1 then
        ch.etaMem * inp.yMem * m * omega * ((a.gate.map fun g ↦ P.at (3 + g)).getD 1)
      else 0)
  let certs := (List.range d).map fun i ↦
    omega * inp.cert * ch.eps.getD (q₀ + k) 0 * ch.nu.getD i 0
  let c := rt.corner
  ⟨c * coef, shifts.map (c * ·), inp.functionals.values W.chunks slices, certs.map (c * ·), slices⟩

theorem columnOf_eq_tailRowColAt (pos pointer k : ℕ) :
    columnOf W inp t q₀ rt chi pos pointer k =
      tailRowColAt W inp t q₀ rt chi (rt.prods.at pos) (rt.prods.at (pos + 1)) pointer k := rfl

/-- **The column at `(pointer, k)`**, its coefficient tables at the row point. -/
def colSpec (pointer k : ℕ) : ColumnAt :=
  tailRowColAt W inp t q₀ rt chi (mleA ((coefTable W inp t k pointer).map (·.1)) (chi.take rt.height))
    (mleA ((coefTable W inp t k pointer).map (·.2)) (chi.take rt.height)) pointer k

theorem foldl_columnStep_eq (T : Array (Array E))
    (hat : ∀ f, rt.prods.at f = mleA (T.getD f #[]) (chi.take rt.height)) :
    ∀ (L : List (ℕ × ℕ)) (racc : Array (Array E) × Array (E × Array ℕ) × ℕ)
      (cacc : List ColumnAt × ℕ), racc.2.2 = racc.1.size → cacc.2 = racc.2.2 →
      (L.foldl (rowPointerStep W inp t q₀) racc).1.toList <+: T.toList →
      (L.foldl (columnStep W inp t q₀ rt chi) cacc).1 =
        cacc.1 ++ L.map fun pk ↦ colSpec W inp t q₀ rt chi pk.1 pk.2
  | [], _, _, _, _, _ => by simp
  | pk :: L, racc, cacc, hpos, hc, hpre => by
    rw [List.foldl_cons] at hpre
    rw [List.foldl_cons, foldl_columnStep_eq T hat L (rowPointerStep W inp t q₀ racc pk)
      (columnStep W inp t q₀ rt chi cacc pk) (by rw [rowPointerStep_pos, rowPointerStep_size, hpos])
      (by rw [rowPointerStep_pos, ← hc]; rfl) hpre]
    have hpre1 := (foldl_rowPointerStep_prefix W inp t q₀ L _).trans hpre
    obtain ⟨rest, hst⟩ := rowPointerStep_AB W inp t q₀ racc pk
    rw [hst] at hpre1
    have hlen : racc.1.toList.length = racc.2.2 := by rw [hpos]; simp
    have hA : rt.prods.at racc.2.2 = mleA ((coefTable W inp t pk.2 pk.1).map (·.1)) (chi.take rt.height) := by
      rw [hat, Keccak.getD_toList T, getD_of_prefix hpre1 (by simp; omega),
        List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega), hlen,
        Nat.sub_self]
      rfl
    have hB : rt.prods.at (racc.2.2 + 1) = mleA ((coefTable W inp t pk.2 pk.1).map (·.2)) (chi.take rt.height) := by
      rw [hat, Keccak.getD_toList T, getD_of_prefix hpre1 (by simp; omega),
        List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega), hlen,
        Nat.add_sub_cancel_left]
      rfl
    show (cacc.1 ++ [columnOf W inp t q₀ rt chi cacc.2 pk.1 pk.2]) ++ _ = _
    rw [columnOf_eq_tailRowColAt, hc, hA, hB]
    simp [colSpec]

end Columns

/-! ## A memory pointer's word reads -/

/-- A read's word term at `pointer`, under `m`. -/
def wordAt (pointer : ℕ) (m : E) (col : ℕ → E) : Read → E
  | .word p scale => if p = pointer then m * scale.evaluate col else 0
  | _ => 0

/-- The forms at `pointer` among the word reads. -/
def wordVal (pointer : ℕ) (col : ℕ → E) (out : List (ℕ × Form)) : E :=
  (out.map fun pf ↦ if pf.1 = pointer then pf.2.evaluate col else 0).sum

theorem sum_ite_key_zero {β : Type} (f : β → E) (p : ℕ) :
    ∀ out : List (ℕ × β), (∀ x ∈ out, x.1 ≠ p) → (out.map fun x ↦ if x.1 = p then f x.2 else 0).sum = 0
  | [], _ => rfl
  | x :: out, h => by
    rw [List.map_cons, List.sum_cons, ite_eq_right (h x List.mem_cons_self),
      sum_ite_key_zero f p out fun y hy ↦ h y (List.mem_cons_of_mem _ hy), add_zero]

/-- Over distinct keys, the entry at a present key. -/
theorem sum_ite_key_one {β : Type} (c : E) (p : ℕ) :
    ∀ out : List (ℕ × β), (out.map (·.1)).Nodup → (∃ x ∈ out, x.1 = p) →
      (out.map fun x ↦ if x.1 = p then c else 0).sum = c
  | [], _, ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | x :: out, hnd, ⟨y, hy, hyp⟩ => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    by_cases hx : x.1 = p
    · rw [ite_eq_left hx, sum_ite_key_zero (fun _ ↦ c) p out fun z hz hzp ↦
        hnd.1 (List.mem_map.mpr ⟨z, hz, hzp.trans hx.symm⟩), add_zero]
    · rw [ite_eq_right hx, zero_add]
      rcases List.mem_cons.mp hy with rfl | hy
      · exact absurd hyp hx
      · exact sum_ite_key_one c p out hnd.2 ⟨y, hy, hyp⟩

/-- `wordReads`' step at one read. -/
def wrStep (w m : E) (out : List (ℕ × Form)) (read : Read) : List (ℕ × Form) :=
  match read with
  | .word p scale =>
    if out.any (·.1 = p) then out.map fun (p', f) ↦ (p', if p' = p then f.addScaled scale (w * m) else f)
    else out ++ [(p, ({} : Form).addScaled scale (w * m))]
  | _ => out

theorem wordVal_wrStep (pointer : ℕ) (col : ℕ → E) (w m : E) (out : List (ℕ × Form))
    (hnd : (out.map (·.1)).Nodup) (rd : Read) :
    wordVal pointer col (wrStep w m out rd) = wordVal pointer col out + w * wordAt pointer m col rd ∧
      ((wrStep w m out rd).map (·.1)).Nodup := by
  cases rd with
  | word p scale =>
    simp only [wrStep]
    split_ifs with hany
    · have hkeys : ((out.map fun pf : ℕ × Form ↦ (pf.1, if pf.1 = p then pf.2.addScaled scale (w * m)
          else pf.2)).map (·.1)) = out.map (·.1) := by simp
      refine ⟨?_, ?_⟩
      · have hex : ∃ x ∈ out, x.1 = p := by simpa using hany
        unfold wordVal
        rw [List.map_map]
        have e : ∀ x ∈ out, ((fun pf : ℕ × Form ↦ if pf.1 = pointer then pf.2.evaluate col else 0) ∘
            (fun pf : ℕ × Form ↦ (pf.1, if pf.1 = p then pf.2.addScaled scale (w * m) else pf.2))) x =
            (if x.1 = pointer then x.2.evaluate col else 0) +
              (if x.1 = p then (if p = pointer then w * (m * scale.evaluate col) else 0) else 0) := by
          intro x _
          simp only [Function.comp]
          by_cases h1 : x.1 = p
          · subst h1
            by_cases h2 : x.1 = pointer
            · simp [h2, evaluate_addScaled]; ring
            · simp [h2]
          · simp [h1]
        rw [List.map_congr_left e, List.sum_map_add, sum_ite_key_one _ p out hnd hex]
        simp [wordAt]
      · rw [hkeys]; exact hnd
    · have hno : ∀ x ∈ out, x.1 ≠ p := fun x hx hxp ↦
        hany (List.any_eq_true.mpr ⟨x, hx, by simp [hxp]⟩)
      refine ⟨?_, ?_⟩
      · unfold wordVal
        rw [List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wordAt,
          evaluate_addScaled, evaluate_empty, zero_add]
        split_ifs <;> ring
      · rw [List.map_append, List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact hno x hx
  | slot _ _ => exact ⟨by simp [wrStep, wordAt], hnd⟩
  | frame _ _ => exact ⟨by simp [wrStep, wordAt], hnd⟩
  | pc _ _ => exact ⟨by simp [wrStep, wordAt], hnd⟩

theorem wordVal_foldl_reads (pointer : ℕ) (col : ℕ → E) (w m : E) :
    ∀ (rs : List Read) (out : List (ℕ × Form)), (out.map (·.1)).Nodup →
      wordVal pointer col (rs.foldl (wrStep w m) out) =
        wordVal pointer col out + w * (rs.map (wordAt pointer m col)).sum ∧
      ((rs.foldl (wrStep w m) out).map (·.1)).Nodup
  | [], out, hnd => ⟨by simp, hnd⟩
  | rd :: rs, out, hnd => by
    obtain ⟨h1, h2⟩ := wordVal_wrStep pointer col w m out hnd rd
    obtain ⟨h3, h4⟩ := wordVal_foldl_reads pointer col w m rs _ h2
    rw [List.foldl_cons]
    refine ⟨?_, h4⟩
    rw [h3, h1, List.map_cons, List.sum_cons]
    ring

theorem wordVal_foldl_memory (pointer : ℕ) (col : ℕ → E) (w : E) :
    ∀ (L : List (Access × E)) (out : List (ℕ × Form)), (out.map (·.1)).Nodup →
      wordVal pointer col (L.foldl (fun out am ↦ am.1.reads.foldl (wrStep w am.2) out) out) =
        wordVal pointer col out + w * (L.map fun am ↦ (am.1.reads.map (wordAt pointer am.2 col)).sum).sum
  | [], out, _ => by simp
  | am :: L, out, hnd => by
    obtain ⟨h1, h2⟩ := wordVal_foldl_reads pointer col w am.2 am.1.reads out hnd
    rw [List.foldl_cons, wordVal_foldl_memory pointer col w L _ h2, h1, List.map_cons, List.sum_cons]
    ring

theorem wordReads_eq (links : Links) (mu : List E) (w : E) :
    wordReads links mu w = (links.memory.zip mu).foldl
      (fun out am ↦ am.1.reads.foldl (wrStep w am.2) out) [] := by
  unfold wordReads
  congr 1

/-- **The word reads, ungrouped.** -/
theorem sum_wordReads (links : Links) (mu : List E) (w : E) (pointer : ℕ) (col : ℕ → E) :
    ((wordReads links mu w).map fun pf ↦ if pf.1 = pointer then pf.2.evaluate col else 0).sum =
      w * ((links.memory.zip mu).map fun am ↦ (am.1.reads.map (wordAt pointer am.2 col)).sum).sum := by
  rw [wordReads_eq]
  have := wordVal_foldl_memory pointer col w (links.memory.zip mu) [] List.nodup_nil
  unfold wordVal at this
  rw [this]
  simp

/-- The unshifted accesses' part of a memory pointer's coefficient. -/
def directAt (links : Links) (mu : List E) (pointer : ℕ) (col : ℕ → E) : E :=
  ((accessesAt links mu pointer).map fun am ↦
    if am.1.shift = 0 then am.2 * (am.1.gate.map col).getD 1 else 0).sum

/-- The word reads' part of a memory pointer's coefficient. -/
def readsAt (links : Links) (mu : List E) (pointer : ℕ) (col : ℕ → E) : E :=
  ((links.memory.zip mu).map fun am ↦ (am.1.reads.map (wordAt pointer am.2 col)).sum).sum

/-- **A memory pointer's row coefficient.** -/
theorem rowCoefs_mem (inp : RowInputs) (links : Links) (mu : List E) (k pointer : ℕ) (col : ℕ → E) :
    rowCoefs inp links mu (k + 2) pointer col =
      (inp.ch.etaMem * inp.yMem * directAt links mu pointer col +
        inp.ch.etaMem * inp.ch.gammaMem.getD 1 0 * inp.m1 * readsAt links mu pointer col, 0) := by
  simp only [rowCoefs, sumE_eq_sum, directAt, readsAt]
  congr 1
  congr 1
  · rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun am _ ↦ ?_)
    obtain ⟨a, m⟩ := am
    split_ifs <;> simp; ring
  · have e : ∀ x ∈ wordReads links mu 1, (match x with
        | (p, scale) => if p = pointer then inp.ch.etaMem * inp.ch.gammaMem.getD 1 0 * inp.m1 *
            Form.evaluate scale col else 0) =
        inp.ch.etaMem * inp.ch.gammaMem.getD 1 0 * inp.m1 *
          (if x.1 = pointer then x.2.evaluate col else 0) := by
      intro x _
      obtain ⟨p, f⟩ := x
      by_cases hp : p = pointer <;> simp [hp]
    rw [List.map_congr_left e, List.sum_map_mul_left, sum_wordReads, one_mul]

/-! ## The coefficient tables' extensions -/

theorem affine_gate (g : Option ℕ) : Affine fun col ↦ (g.map col).getD 1 := by
  cases g with
  | none => exact (affine_const 1).congr fun _ ↦ rfl
  | some g => exact (affine_col g).congr fun _ ↦ rfl

theorem affine_directAt (links : Links) (mu : List E) (pointer : ℕ) :
    Affine (directAt links mu pointer) := by
  unfold directAt
  refine affine_sum _ _ fun am _ ↦ ?_
  by_cases h : am.1.shift = 0
  · exact ((affine_gate am.1.gate).mul_left am.2).congr fun _ ↦ by simp [h]
  · exact (affine_const 0).congr fun _ ↦ by simp [h]

theorem affine_readsAt (links : Links) (mu : List E) (pointer : ℕ)
    (h : ∀ a ∈ links.memory, ∀ p scale, Read.word p scale ∈ a.reads → ∀ m ∈ scale.terms, m.1.length ≤ 1) :
    Affine (readsAt links mu pointer) := by
  unfold readsAt
  refine affine_sum _ _ fun am ham ↦ affine_sum _ _ fun rd hrd ↦ ?_
  have ha := (List.of_mem_zip ham).1
  cases rd with
  | word p scale =>
    by_cases hp : p = pointer
    · exact ((affine_evaluate (h _ ha p scale hrd)).mul_left am.2).congr fun _ ↦ by simp [wordAt, hp]
    · exact (affine_const 0).congr fun _ ↦ by simp [wordAt, hp]
  | slot _ _ => exact (affine_const 0).congr fun _ ↦ rfl
  | frame _ _ => exact (affine_const 0).congr fun _ ↦ rfl
  | pc _ _ => exact (affine_const 0).congr fun _ ↦ rfl

/-- The row coefficients are affine in the row, for a table whose successor forms and word-read
scales have degree at most one. -/
theorem affine_rowCoefs (inp : RowInputs) (links : Links) (mu : List E) (k pointer : ℕ)
    (h1 : ∀ m ∈ links.stateLink.next.1.terms, m.1.length ≤ 1)
    (h2 : ∀ m ∈ links.stateLink.next.2.terms, m.1.length ≤ 1)
    (hr : ∀ a ∈ links.memory, ∀ p scale, Read.word p scale ∈ a.reads → ∀ m ∈ scale.terms, m.1.length ≤ 1) :
    Affine (fun col ↦ (rowCoefs inp links mu k pointer col).1) ∧
      Affine (fun col ↦ (rowCoefs inp links mu k pointer col).2) := by
  match k with
  | 0 =>
    refine ⟨(affine_const 0).congr fun _ ↦ rfl, ?_⟩
    have hs : Affine fun col ↦ 1 + inp.ch.gammaState.getD 0 0 * col links.stateLink.pc +
        inp.ch.gammaState.getD 1 0 * col links.stateLink.fp :=
      ((affine_const 1).add ((affine_col _).mul_left _)).add ((affine_col _).mul_left _)
    have hs' : Affine fun col ↦ 1 + inp.ch.gammaState.getD 0 0 * links.stateLink.next.1.evaluate col +
        inp.ch.gammaState.getD 1 0 * links.stateLink.next.2.evaluate col :=
      ((affine_const 1).add ((affine_evaluate h1).mul_left _)).add ((affine_evaluate h2).mul_left _)
    exact ((hs.mul_left inp.eqZeta).add (hs'.mul_left inp.shiftZeta)).congr fun _ ↦ rfl
  | 1 =>
    exact ⟨((affine_const inp.xBc).add ((affine_col _).mul_left inp.pFp)).congr fun _ ↦ rfl,
      (affine_const 0).congr fun _ ↦ rfl⟩
  | k + 2 =>
    refine ⟨?_, (affine_const 0).congr fun col ↦ by rw [rowCoefs_mem]⟩
    exact (((affine_directAt links mu pointer).mul_left _).add
      ((affine_readsAt links mu pointer hr).mul_left _)).congr fun col ↦ by rw [rowCoefs_mem]

theorem tableFacts_affine {t : ℕ} (hf : TableFacts t) :
    (∀ m ∈ (tables.getD t default).links.stateLink.next.1.terms, m.1.length ≤ 1) ∧
      (∀ m ∈ (tables.getD t default).links.stateLink.next.2.terms, m.1.length ≤ 1) ∧
      ∀ a ∈ (tables.getD t default).links.memory, ∀ p scale, Read.word p scale ∈ a.reads →
        ∀ m ∈ scale.terms, m.1.length ≤ 1 :=
  ⟨(formAff_spec hf.next1).1, (formAff_spec hf.next2).1,
    fun a ha _ _ hrd ↦ (formAff_spec (hf.reads a ha _ hrd)).1⟩

/-- **A coefficient table's extensions** are the row coefficients at the columns' extensions. -/
theorem mleA_coefTable (W : Witness) (inp : RowInputs) {t : ℕ} (hf : TableFacts t) (k pointer : ℕ)
    (pt : List E) (hpt : pt.length = W.layout.tableLogHeights.getD t 0) :
    mleA ((coefTable W inp t k pointer).map (·.1)) pt =
        (rowCoefs inp (tables.getD t default).links (inp.ch.mu.getD t []) k pointer
          (rowSum (W.tableCols t) pt)).1 ∧
      mleA ((coefTable W inp t k pointer).map (·.2)) pt =
        (rowCoefs inp (tables.getD t default).links (inp.ch.mu.getD t []) k pointer
          (rowSum (W.tableCols t) pt)).2 := by
  obtain ⟨h1, h2, hr⟩ := tableFacts_affine hf
  obtain ⟨a1, a2⟩ := affine_rowCoefs inp (tables.getD t default).links (inp.ch.mu.getD t []) k
    pointer h1 h2 hr
  unfold coefTable
  rw [← hpt, Array.map_ofFn, Array.map_ofFn]
  exact ⟨mleA_rows a1 _ _, mleA_rows a2 _ _⟩

end LeanVM.Prover.Complete

end
