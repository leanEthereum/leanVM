/-
  LeanVM.Guest.B1.Tables.VerifyTablesSpec

  Specification-side facts `verify_tables` relies on: the tables' weights (V:624-628) as products,
  and the bus blocks of the deployed layout (V:888-898), table by table.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Main.FreshWeight
public import LeanVM.Guest.B1.Tables.ColumnSelector

/-!
# The tables' weights and the bus blocks

* `tableWeights_eq`: at the point `rs.reverse` (the sumcheck's challenges in round order,
  reversed), a table of height `h` weighs the equality of its `h` coordinates times the product of
  the first `n - h` challenges.
* `layoutOf_blocks`: the deployed layout's blocks per side, by owner (`layoutPushOwners`,
  `layoutCountOwners`), each block at its owner's height and row count, the pull side shaped as
  the push side; `busLayout_pull_push`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The tables' weights -/

theorem prodE_eq_prod (l : List E) : prodE l = ∏ i ∈ Finset.range l.length, l.getD i 0 := by
  rw [prodE, ← Main.foldl_mul_eq_prod]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- The weights as products over the coordinates. -/
theorem tableWeights_prod (hts : List ℕ) (eqP : List E) : ∀ P : List E,
    tableWeights hts eqP P = hts.map fun h => ∏ v ∈ Finset.range P.length,
      (if v < h then 1 + eqP.getD v 0 + P.getD v 0 else P.getD v 0) := by
  intro P
  induction P using List.reverseRecOn with
  | nil => simp [tableWeights]
  | append_singleton P x ih =>
    have hz : (P ++ [x]).zipIdx = P.zipIdx ++ [(x, P.length)] := by
      simp [List.zipIdx_append]
    unfold tableWeights at ih ⊢
    rw [hz, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_singleton]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_zipWith, List.getElem_map, Finset.prod_range_succ]
    have hx : (P ++ [x]).getD P.length 0 = x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl
    simp only [hx]
    refine congrArg (· * _) (Finset.prod_congr rfl fun v hv => ?_)
    have hv' := Finset.mem_range.mp hv
    have hg : (P ++ [x]).getD v 0 = P.getD v 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hv']
    simp only [hg]

/-- **The tables' weights** (V:624-628) at the reversed challenges `rs.reverse`: the equality of
the table's `h` coordinates, times the first `n - h` challenges. -/
theorem tableWeights_eq (heights : List ℕ) (eqPoint rs : List E)
    (hh : ∀ h ∈ heights, h ≤ rs.length) (he : ∀ h ∈ heights, h ≤ eqPoint.length) :
    tableWeights heights eqPoint rs.reverse =
      heights.map fun h => prodE (rs.take (rs.length - h)) *
        eqEval (eqPoint.take h) (rs.reverse.take h) := by
  rw [tableWeights_prod heights eqPoint rs.reverse, List.length_reverse]
  refine List.map_congr_left fun h hm => ?_
  have h1 := hh h hm
  have h2 := he h hm
  rw [show Finset.range rs.length = Finset.range (h + (rs.length - h)) by
    rw [Nat.add_sub_cancel' h1], Finset.prod_range_add, mul_comm,
    eqEval_take _ _ h (by omega) (by simp; omega)]
  refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun v hv => ?_)
  · rw [prodE_eq_prod, List.length_take, show min (rs.length - h) rs.length = rs.length - h by
      omega, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    rw [ite_neg' (by omega), List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_take, ite_pos' (by omega)]
    congr 2
    omega
  · rw [ite_pos' (Finset.mem_range.mp hv)]

/-! ## The bus blocks -/

/-- The owners of the push side's blocks (and the pull side's). -/
def layoutPushOwners : List ℕ :=
  [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    5, 5]

/-- The owners of the count side's blocks. -/
def layoutCountOwners : List ℕ :=
  [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]

theorem tables_opcode : ∀ i (h : i < tables.length), (tables[i]'h).opcode = i := by decide +kernel

theorem tables_length' : tables.length = 6 := rfl

/-- A side's blocks over the zipped tables, projected, are the tables' own lists. -/
theorem flatMap_zip_map {α : Type} (G : Table × ℕ × ℕ → List BusBlock) (g : BusBlock → α)
    (S : Table → List α) (hG : ∀ t h n, (G (t, h, n)).map g = S t) :
    ∀ (ts : List Table) (hs ns : List ℕ), ts.length ≤ hs.length → ts.length ≤ ns.length →
      ((List.zip ts (List.zip hs ns)).flatMap G).map g = ts.flatMap S
  | [], _, _, _, _ => by simp
  | t :: ts, h :: hs, n :: ns, h1, h2 => by
    simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append, hG]
    rw [flatMap_zip_map G g S hG ts hs ns (by simpa using h1) (by simpa using h2)]
  | _ :: _, [], _, h1, _ => by simp at h1
  | _ :: _, _ :: _, [], _, h2 => by simp at h2

/-- Every block of a side sits at its owner's height and row count. -/
theorem blocks_fields (G : Table × ℕ × ℕ → List BusBlock)
    (hG : ∀ t h n b, b ∈ G (t, h, n) → b.logRows = h ∧ b.rows = n ∧ b.owner = t.opcode)
    (rows : List ℕ) (hr : rows.length = 6) :
    ∀ b ∈ (List.zip tables (List.zip (rows.map log2Ceil) rows)).flatMap G,
      b.logRows = log2Ceil (rows.getD b.owner 0) ∧ b.rows = rows.getD b.owner 0 := by
  intro b hb
  obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.mp hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi6 : i < 6 := by
    have := List.lt_length_left_of_zip hi; rwa [tables_length'] at this
  simp only [List.getElem_zip, List.getElem_map] at hbx
  obtain ⟨h1, h2, h3⟩ := hG _ _ _ b hbx
  have ho : b.owner = i := by rw [h3, tables_opcode]
  rw [ho, h1, h2, List.getD_eq_getElem _ _ (by omega)]
  exact ⟨rfl, rfl⟩

theorem map_fields (G : Table × ℕ × ℕ → List BusBlock)
    (hG : ∀ t h n b, b ∈ G (t, h, n) → b.logRows = h ∧ b.rows = n ∧ b.owner = t.opcode)
    (rows : List ℕ) (hr : rows.length = 6) {α : Type} (f : ℕ → ℕ → ℕ → α) :
    ((List.zip tables (List.zip (rows.map log2Ceil) rows)).flatMap G).map
        (fun b => f b.owner b.logRows b.rows) =
      (((List.zip tables (List.zip (rows.map log2Ceil) rows)).flatMap G).map (·.owner)).map
        fun t => f t (log2Ceil (rows.getD t 0)) (rows.getD t 0) := by
  rw [List.map_map]
  refine List.map_congr_left fun b hb => ?_
  obtain ⟨h1, h2⟩ := blocks_fields G hG rows hr b hb
  simp only [Function.comp_apply, h1, h2]

theorem push_owners :
    tables.flatMap (fun t => t.flushes.push.map fun _ => t.opcode) = layoutPushOwners := by
  decide +kernel

theorem pull_owners :
    tables.flatMap (fun t => t.flushes.pull.map fun _ => t.opcode) = layoutPushOwners := by
  decide +kernel

theorem tables_counts : tables.map (fun t => (t.countColumns, t.opcode)) =
    [([11, 12, 13, 14], 0), ([11, 12, 13, 14], 1), ([6, 7], 2), ([11, 12, 13, 14], 3),
      ([8, 9, 10, 11], 4), ([27, 28, 29, 30, 31, 32, 33, 34, 35, 36], 5)] := by
  simp [Table.countColumns, tables, arithColumns, setColumns, derefColumns, jumpColumns,
    blake2sColumns, opXor, opMul, opSet, opDeref, opJump, opBlake2s]

theorem count_owners :
    tables.flatMap (fun t => t.countColumns.map fun _ => t.opcode) = layoutCountOwners := by
  have e : tables.flatMap (fun t => t.countColumns.map fun _ => t.opcode) =
      (tables.map fun t => (t.countColumns, t.opcode)).flatMap
        (fun p => p.1.map fun _ => p.2) := by rw [List.flatMap_map]
  rw [e, tables_counts]
  rfl

/-- **The deployed layout's bus blocks** (V:888-898), side by side: each block at its owner's
height and row count, the coordinates the tables' flushes, the pull side shaped as the push
side. -/
theorem layoutOf_blocks (bytecode : List K) (hb : bytecode.length = 2 ^ 22) (logMem : ℕ)
    (rows : List ℕ) (hr : rows.length = 6) :
    let L := layoutOf bytecode logMem rows
    L.logBytecode = 18 ∧ L.tableLogHeights = rows.map log2Ceil ∧
    L.push.map (·.owner) = layoutPushOwners ∧ L.count.map (·.owner) = layoutCountOwners ∧
    L.push.map (·.logRows) = layoutPushOwners.map (fun t => log2Ceil (rows.getD t 0)) ∧
    L.push.map (·.rows) = layoutPushOwners.map (fun t => rows.getD t 0) ∧
    L.count.map (·.logRows) = layoutCountOwners.map (fun t => log2Ceil (rows.getD t 0)) ∧
    L.count.map (·.rows) = layoutCountOwners.map (fun t => rows.getD t 0) ∧
    L.push.map (·.coordinates) = tables.flatMap (·.flushes.push) ∧
    L.pull.map (·.coordinates) = tables.flatMap (·.flushes.pull) ∧
    L.count.map (·.coordinates) =
      tables.flatMap (fun t => t.countColumns.map fun l => [Form.col l]) ∧
    L.pull.map (fun b => (b.owner, b.logRows, b.rows)) =
      L.push.map (fun b => (b.owner, b.logRows, b.rows)) := by
  intro L
  have hlog : Nat.log2 bytecode.length = 22 := by rw [hb, Nat.log2_two_pow]
  have hl1 : tables.length ≤ (rows.map log2Ceil).length := by simp [hr, tables_length']
  have hl2 : tables.length ≤ rows.length := by simp [hr, tables_length']
  set Gp : Table × ℕ × ℕ → List BusBlock :=
    fun x => x.1.flushes.push.map fun c => ⟨x.2.1, x.2.2, c, x.1.opcode⟩ with hGpd
  set Gl : Table × ℕ × ℕ → List BusBlock :=
    fun x => x.1.flushes.pull.map fun c => ⟨x.2.1, x.2.2, c, x.1.opcode⟩ with hGld
  set Gc : Table × ℕ × ℕ → List BusBlock :=
    fun x => x.1.countColumns.map fun l => ⟨x.2.1, x.2.2, [Form.col l], x.1.opcode⟩ with hGcd
  have ep : L.push = (List.zip tables (List.zip (rows.map log2Ceil) rows)).flatMap Gp := rfl
  have el : L.pull = (List.zip tables (List.zip (rows.map log2Ceil) rows)).flatMap Gl := rfl
  have ec : L.count = (List.zip tables (List.zip (rows.map log2Ceil) rows)).flatMap Gc := rfl
  have hm : ∀ {β : Type} (l : List β) (f : β → BusBlock) (b : BusBlock) (h n o : ℕ),
      (∀ c, (f c).logRows = h ∧ (f c).rows = n ∧ (f c).owner = o) → b ∈ l.map f →
        b.logRows = h ∧ b.rows = n ∧ b.owner = o := by
    intro β l f b h n o hf hb; obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb; exact hf c
  have hGp : ∀ (t : Table) (h n : ℕ) (b : BusBlock), b ∈ Gp (t, h, n) →
      b.logRows = h ∧ b.rows = n ∧ b.owner = t.opcode :=
    fun t h n b => hm _ _ b h n _ fun _ => ⟨rfl, rfl, rfl⟩
  have hGl : ∀ (t : Table) (h n : ℕ) (b : BusBlock), b ∈ Gl (t, h, n) →
      b.logRows = h ∧ b.rows = n ∧ b.owner = t.opcode :=
    fun t h n b => hm _ _ b h n _ fun _ => ⟨rfl, rfl, rfl⟩
  have hGc : ∀ (t : Table) (h n : ℕ) (b : BusBlock), b ∈ Gc (t, h, n) →
      b.logRows = h ∧ b.rows = n ∧ b.owner = t.opcode :=
    fun t h n b => hm _ _ b h n _ fun _ => ⟨rfl, rfl, rfl⟩
  have po : L.push.map (·.owner) = layoutPushOwners := by
    rw [ep, flatMap_zip_map Gp (·.owner) (fun t => t.flushes.push.map fun _ => t.opcode)
      (fun t h n => by rw [hGpd, List.map_map]; rfl) _ _ _ hl1 hl2, push_owners]
  have lo : L.pull.map (·.owner) = layoutPushOwners := by
    rw [el, flatMap_zip_map Gl (·.owner) (fun t => t.flushes.pull.map fun _ => t.opcode)
      (fun t h n => by rw [hGld, List.map_map]; rfl) _ _ _ hl1 hl2, pull_owners]
  have co : L.count.map (·.owner) = layoutCountOwners := by
    rw [ec, flatMap_zip_map Gc (·.owner) (fun t => t.countColumns.map fun _ => t.opcode)
      (fun t h n => by rw [hGcd, List.map_map]; rfl) _ _ _ hl1 hl2, count_owners]
  have pf := fun {α : Type} (f : ℕ → ℕ → ℕ → α) => map_fields Gp hGp rows hr f
  have lf := fun {α : Type} (f : ℕ → ℕ → ℕ → α) => map_fields Gl hGl rows hr f
  have cf := fun {α : Type} (f : ℕ → ℕ → ℕ → α) => map_fields Gc hGc rows hr f
  refine ⟨by show Nat.log2 bytecode.length - busBits = 18; rw [hlog]; rfl, rfl, po, co, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have := pf (fun _ l _ => l); rw [← ep] at this; rw [this, po]
  · have := pf (fun _ _ n => n); rw [← ep] at this; rw [this, po]
  · have := cf (fun _ l _ => l); rw [← ec] at this; rw [this, co]
  · have := cf (fun _ _ n => n); rw [← ec] at this; rw [this, co]
  · rw [ep, flatMap_zip_map Gp (·.coordinates) (fun t => t.flushes.push)
      (fun t h n => by rw [hGpd, List.map_map]; exact List.map_id _) _ _ _ hl1 hl2]
  · rw [el, flatMap_zip_map Gl (·.coordinates) (fun t => t.flushes.pull)
      (fun t h n => by rw [hGld, List.map_map]; exact List.map_id _) _ _ _ hl1 hl2]
  · rw [ec, flatMap_zip_map Gc (·.coordinates) (fun t => t.countColumns.map fun l => [Form.col l])
      (fun t h n => by rw [hGcd, List.map_map]; rfl) _ _ _ hl1 hl2]
  · have h1 := lf (fun o l n => (o, l, n)); rw [← el] at h1
    have h2 := pf (fun o l n => (o, l, n)); rw [← ep] at h2
    rw [h1, h2, po, lo]

/-- The pull side's bus layout is the push side's. -/
theorem busLayout_pull_push (bytecode : List K) (hb : bytecode.length = 2 ^ 22) (logMem : ℕ)
    (rows : List ℕ) (hr : rows.length = 6) :
    busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).pull =
      busLayout [0, logMem, 18] (layoutOf bytecode logMem rows).push := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := layoutOf_blocks bytecode hb logMem rows hr
  have e : (layoutOf bytecode logMem rows).pull.map (·.logRows) =
      (layoutOf bytecode logMem rows).push.map (·.logRows) := by
    have := congrArg (List.map fun x : ℕ × ℕ × ℕ => x.2.1) h
    simpa [List.map_map, Function.comp_def] using this
  unfold busLayout
  rw [e]

end
end LeanVM.Guest.B1.VerifySub
