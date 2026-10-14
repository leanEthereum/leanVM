import WhirAeneas.Replay

/-! The composed replay: the generated `verify` returns `Ok` exactly when the model's
`nativeVerify` accepts the challenges and opening the transcript answered. -/
namespace WhirAeneas.Replay
open Aeneas Aeneas.Std ReplaySource Whir Whir.Concrete WhirAeneas.Fold WhirAeneas.Query

/-! ## Saved-context counts -/

section Counts
open AccumulatedTerminalRefinement WHIRNativeArithmetic

theorem foldModel_saved {E : Type} (encode : E → Concrete.E) (rounds : List (E × E × E)) (st : State) :
    (foldModel encode rounds st).source.saved = st.source.saved := by
  induction rounds generalizing st with
  | nil => rfl
  | cons x rounds ih =>
    simp only [foldModel, List.foldl_cons] at ih ⊢
    rw [ih]; rfl

theorem foldModel_ris {E : Type} (encode : E → Concrete.E) (rounds : List (E × E × E)) (st : State) :
    (foldModel encode rounds st).source.ris = st.source.ris ++ rounds.map fun x => encode x.1 := by
  induction rounds generalizing st with
  | nil => simp [foldModel]
  | cons x rounds ih =>
    simp only [foldModel, List.foldl_cons] at ih ⊢
    rw [ih]; simp [foldScalar, SourceState.step]

theorem foldModel_n {E : Type} (encode : E → Concrete.E) (rounds : List (E × E × E)) (st : State) :
    (foldModel encode rounds st).n = st.n - rounds.length := by
  induction rounds generalizing st with
  | nil => simp [foldModel]
  | cons x rounds ih =>
    simp only [foldModel, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih]; simp only [foldScalar]; omega

theorem oodFold_counts (lam : Concrete.E)
    (data : List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E)) (acc : State × Concrete.E) :
    ((Query.oodFold lam data acc).1.source.saved.filter Query.isOod).length =
        (acc.1.source.saved.filter Query.isOod).length + data.length ∧
      ((Query.oodFold lam data acc).1.source.saved.filter fun sv => !Query.isOod sv).length =
        (acc.1.source.saved.filter fun sv => !Query.isOod sv).length ∧
      (Query.oodFold lam data acc).1.source.ris = acc.1.source.ris ∧
      (Query.oodFold lam data acc).1.n = acc.1.n := by
  induction data generalizing acc with
  | nil => simp [Query.oodFold]
  | cons d data ih =>
    obtain ⟨st, b⟩ := acc
    obtain ⟨z, y, m⟩ := d
    obtain ⟨e1, e2, e3, e4⟩ := ih (batchScalar st (.ood z) y (b * lam) m, b * lam)
    have hsv : (batchScalar st (.ood z) y (b * lam) m).source.saved =
        st.source.saved ++ [⟨st.source.ris.length, .ood z, b * lam⟩] := rfl
    simp only [Query.oodFold]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, hsv, List.filter_append]
      simp only [List.filter_cons, Query.isOod_ood, List.filter_nil, ↓reduceIte, List.length_append,
        List.length_singleton, List.length_cons, List.length_nil]
      omega
    · rw [e2, hsv, List.filter_append]; simp
    · rw [e3]; rfl
    · rw [e4]; rfl

theorem batch_query_counts (s : State) (n : Nat) (qs : Array Nat) (lam value beta : Concrete.E)
    (m : Protocol.Message Concrete.E) :
    ((batchScalar s (.query n qs lam) value beta m).source.saved.filter Query.isOod).length =
        (s.source.saved.filter Query.isOod).length ∧
      ((batchScalar s (.query n qs lam) value beta m).source.saved.filter fun sv => !Query.isOod sv).length =
        (s.source.saved.filter fun sv => !Query.isOod sv).length + 1 := by
  simp [batchScalar, SourceState.step, List.filter_append]

end Counts

/-! ## The level-0 row reversal -/

theorem verify_loop3_eq {K : Type} (L0 : List (List K)) :
    ∀ (m : Nat) (r : Usize) (rows : alloc.vec.Vec (alloc.vec.Vec K)), L0.length - r.val = m →
      r.val ≤ L0.length → rows.val.map (·.val) = (L0.take r.val).map List.reverse ++ L0.drop r.val →
      ∃ rows', whir.verify.verify_loop3 rows r = .ok rows' ∧
        rows'.val.map (·.val) = L0.map List.reverse := by
  intro m
  induction m with
  | zero =>
    intro r rows hm hr hrows
    refine ⟨rows, ?_, ?_⟩
    · unfold whir.verify.verify_loop3
      apply loop_done
      have hlen : rows.val.length = L0.length := by
        have := congrArg List.length hrows; simp at this; omega
      have hle : L0.length ≤ r.val := by omega
      have : ¬ (r < alloc.vec.Vec.len rows) := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simp [hlen]; exact hle
      simp [whir.verify.verify_loop3.body, this]
    · rw [hrows, List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]; simp
  | succ m ih =>
    intro r rows hm hr hrows
    have hlen : rows.val.length = L0.length := by
      have := congrArg List.length hrows; simp at this; omega
    have hlt : r.val < L0.length := by omega
    have hsucc := succ_val r L0.length hlt (by have := rows.property; omega)
    let row := rows.val[r.val]'(by omega)
    have hrow : row.val = L0[r.val] := by
      have := congrArg (fun l => l[r.val]?) hrows
      simp only [List.getElem?_map] at this
      rw [List.getElem?_append_right (by simp <;> omega)] at this
      simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt), Nat.sub_self,
        List.getElem?_drop, Nat.add_zero] at this
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hlt] at this
      simpa [row] using this
    let rows1 := alloc.vec.Vec.set rows r (alloc.vec.Vec.mk (core.slice.Slice.reverse row.slice))
    have hbody : whir.verify.verify_loop3.body rows r =
        .ok (.cont (rows1, Std.Usize.wrapping_add r 1#usize)) := by
      have : r < alloc.vec.Vec.len rows := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simp [hlen, hlt]
      simp [whir.verify.verify_loop3.body, this, alloc.vec.Vec.index_mut_usize,
        vec_index_usize rows r (by omega), lift, alloc.vec.Vec.deref_mut, rows1, row]
    obtain ⟨rows', hloop, erows⟩ := ih (Std.Usize.wrapping_add r 1#usize) rows1 (by rw [hsucc]; omega)
      (by rw [hsucc]; omega) (by
        rw [hsucc]
        simp only [rows1, alloc.vec.Vec.set_val_eq]
        rw [List.map_set, hrows, List.set_append_right _ _ (by simp <;> omega)]
        simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt), Nat.sub_self]
        rw [List.drop_eq_getElem_cons hlt, List.set_cons_zero, List.take_add_one,
          List.getElem?_eq_getElem hlt]
        have hx : (alloc.vec.Vec.mk (core.slice.Slice.reverse row.slice)).val = L0[r.val].reverse := by
          rw [← hrow]; simp [core.slice.Slice.reverse, alloc.vec.Vec.val, Slice.from_val]
        rw [hx]
        simp only [List.map_append, List.append_assoc, Option.toList, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append])
    refine ⟨rows', ?_, erows⟩
    unfold whir.verify.verify_loop3
    rw [loop_cont hbody]
    unfold whir.verify.verify_loop3 at hloop
    exact hloop

/-! ## A level's model state -/

section LevelModel
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (encode : E → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)

/-- The interpreted out-of-domain claims of a level. -/
def oodList (oods : List (List E × E × E × E)) :
    List (Array Concrete.E × Concrete.E × Protocol.Message Concrete.E) :=
  oods.map fun o => ((o.1.map encode).toArray, encode o.2.1, ⟨encode o.2.2.1, encode o.2.2.2⟩)

theorem oodData_of_forall₂ (ws : List (whir.verify.Ood E)) (l : List (List E × E × E × E))
    (h : List.Forall₂ (OodIs encode) ws l) : Query.oodData encode ws = oodList encode l := by
  induction h with
  | nil => rfl
  | @cons o d _ _ hod _ ih =>
    obtain ⟨hz, hy, hc, ha, _⟩ := hod
    simp only [Query.oodData, oodList, List.map_cons] at ih ⊢
    rw [ih, hz, hy, hc, ha]

theorem oodBatch_level (l : SLevel E Q R K) (base : Bool) (st : State) :
    oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs base) st =
      Query.oodFold (encode l.lambda) (oodList encode l.oods) (st, 1) := by
  rw [oodBatch_eq (oodList encode l.oods) _ _ st (by simp [SLevel.chal, oodList])
    (by simp [SLevel.prf, oodList])]
  rfl

theorem foldBlock_level (l : SLevel E Q R K) (base : Bool) (st : State) :
    foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs base) st = foldModel encode l.folds st :=
  foldBlock_eq encode l.folds _ _ st rfl rfl

/-- A later level's batch, as `finish_query_eq` states it, is the model's `queryBatch`. -/
theorem level_model_eq (l : SLevel E Q R K) (st : State) (j : Nat) (hj : j ≠ 0)
    (b : whir.verify.PendingQuery Q E) (sum : E) (intro : whir.sumcheck.RoundQuad E)
    (oods : List (whir.verify.Ood E))
    (rowsV : List (alloc.vec.Vec E)) (hbq : b.queries.val = l.queries) (hbl : b.lambda = l.lambda)
    (hbw : b.weights.val.map encode = (Concrete.powers (encode l.lambda) l.queries.length).toList)
    (hoods : List.Forall₂ (OodIs encode) oods l.oods)
    (hsum : encode sum = Protocol.enforced (rowsV.map fun r => (r.val.map encode).toArray).toArray
      ((l.folds.map (·.1)).map encode).toArray (b.weights.val.map encode).toArray false)
    (hrowsV : rowsV.map (fun r => r.val.map encode) = l.rows.map (eRow encodeK ofLimbs))
    (hic : intro.c = l.intro.1) (hia : intro.a = l.intro.2) (n1 : Nat)
    (hn1 : n1 = (foldModel encode l.folds st).n) :
    batchScalar (Query.oodFold (encode b.lambda) (Query.oodData encode oods) (foldModel encode l.folds st, 1)).1
        (.query n1 (b.queries.val.map index).toArray (encode b.lambda)) (encode sum)
        ((Query.oodFold (encode b.lambda) (Query.oodData encode oods) (foldModel encode l.folds st, 1)).2 *
          encode b.lambda) ⟨encode intro.c, encode intro.a⟩ =
      queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j (l.chal encode)
        (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st)) := by
  rw [foldBlock_level, oodBatch_level, oodData_of_forall₂ encode oods l.oods hoods, hbl, hbq, hn1, hsum, hic, hia]
  have hw' : (b.weights.val.map encode).toArray = Concrete.powers (encode l.lambda) l.queries.length := by
    rw [hbw]
  have hrw : (rowsV.map fun r => (r.val.map encode).toArray) = (l.rows.map (eRow encodeK ofLimbs)).map
      List.toArray := by rw [← hrowsV]; simp
  have hj' : (j == 0) = false := by simpa using hj
  simp only [queryBatch, hw', hrw, hj', SLevel.prf, SLevel.chal, List.map_map, List.size_toArray,
    List.length_map, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Level 0's batch, as `finish_query_eq` states it over the reversed rows of words the
source sums, is the model's `queryBatch` on the base rows. -/
theorem base_model_eq (l : SLevel E Q R K) (st : State)
    (b : whir.verify.PendingQuery Q E) (sum : E) (intro : whir.sumcheck.RoundQuad E)
    (oods : List (whir.verify.Ood E))
    (hbq : b.queries.val = l.queries) (hbl : b.lambda = l.lambda)
    (hbw : b.weights.val.map encode = (Concrete.powers (encode l.lambda) l.queries.length).toList)
    (hoods : List.Forall₂ (OodIs encode) oods l.oods)
    (hsum : encode sum = Protocol.enforced
      ((l.rows.map List.reverse).map fun r => (r.map fun k => Concrete.E.ofK (encodeK k)).toArray).toArray
      ((l.folds.map (·.1)).map encode).toArray (b.weights.val.map encode).toArray false)
    (hic : intro.c = l.intro.1) (hia : intro.a = l.intro.2) (n1 : Nat)
    (hn1 : n1 = (foldModel encode l.folds st).n) :
    batchScalar (Query.oodFold (encode b.lambda) (Query.oodData encode oods) (foldModel encode l.folds st, 1)).1
        (.query n1 (b.queries.val.map index).toArray (encode b.lambda)) (encode sum)
        ((Query.oodFold (encode b.lambda) (Query.oodData encode oods) (foldModel encode l.folds st, 1)).2 *
          encode b.lambda) ⟨encode intro.c, encode intro.a⟩ =
      queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs true) st).n 0 (l.chal encode)
        (l.prf encode encodeK ofLimbs true) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs true)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs true) st)) := by
  rw [foldBlock_level, oodBatch_level, oodData_of_forall₂ encode oods l.oods hoods, hbl, hbq, hn1, hsum, hic, hia]
  have hw' : (b.weights.val.map encode).toArray = Concrete.powers (encode l.lambda) l.queries.length := by
    rw [hbw]
  simp only [queryBatch, SLevel.prf, SLevel.chal, beq_self_eq_true, ↓reduceIte, enforced_base, hw',
    List.size_toArray, List.length_map]
  congr 2 <;> simp [List.map_map, Function.comp_def, List.map_reverse]

/-- The last level has no out-of-domain claims; its batch is `lastState`. -/
theorem last_model_eq (l : SLevel E Q R K) (st : State) (j : Nat) (hj : j ≠ 0) (hoods : l.oods = []) :
    queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j (l.chal encode)
        (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st)) =
      lastState encode encodeK ofLimbs index (foldModel encode l.folds st) (foldModel encode l.folds st).n
        l.queries l.lambda l.rows (l.folds.map (·.1)) l.intro.1 l.intro.2 := by
  rw [foldBlock_level, oodBatch_level, hoods]
  have hj' : (j == 0) = false := by simpa using hj
  simp only [queryBatch, lastState, oodList, List.map_nil, Query.oodFold, hj', SLevel.prf, SLevel.chal,
    List.size_toArray, List.length_map, Bool.false_eq_true, ↓reduceIte, List.map_map]
  rfl

/-- What a level does to the model state's size, fit and saved-context counts. -/
theorem level_state_facts (l : SLevel E Q R K) (base : Bool) (st : State) (j : Nat) (qs : Array Nat)
    (hfits : ModelFits st) (hk : l.folds.length ≤ st.n) (h64 : st.n < 64)
    (hz : ∀ o ∈ l.oods, o.1.length = st.n - l.folds.length) :
    let s' := queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs base) st).n j (l.chal encode)
      (l.prf encode encodeK ofLimbs base) qs (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs base)
        (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs base) st))
    ModelFits s' ∧ s'.n = st.n - l.folds.length ∧
      (s'.source.saved.filter Query.isOod).length = (st.source.saved.filter Query.isOod).length + l.oods.length ∧
      (s'.source.saved.filter fun sv => !Query.isOod sv).length =
        (st.source.saved.filter fun sv => !Query.isOod sv).length + 1 := by
  intro s'
  have hf := ModelFits.ofFold encode l.folds st hfits hk
  have hn1 : (foldModel encode l.folds st).n = st.n - l.folds.length := foldModel_n encode l.folds st
  obtain ⟨hof, hon⟩ := ModelFits.ofOodFold (encode l.lambda) (oodList encode l.oods) (foldModel encode l.folds st, 1)
    hf (fun d hd => by
      simp only [oodList, List.mem_map] at hd
      obtain ⟨o, ho, rfl⟩ := hd
      simp [hz o ho, hn1]) (by rw [hn1]; omega)
  obtain ⟨c1, c2, -, c4⟩ := oodFold_counts (encode l.lambda) (oodList encode l.oods) (foldModel encode l.folds st, 1)
  have hs' : s' = batchScalar (Query.oodFold (encode l.lambda) (oodList encode l.oods) (foldModel encode l.folds st, 1)).1
      (.query (foldModel encode l.folds st).n qs (encode l.lambda))
      (Protocol.enforced (l.prf encode encodeK ofLimbs base).rows (l.chal encode).folds
        (Concrete.powers (encode l.lambda) qs.size) (j == 0))
      ((Query.oodFold (encode l.lambda) (oodList encode l.oods) (foldModel encode l.folds st, 1)).2 * encode l.lambda)
      (l.prf encode encodeK ofLimbs base).intro := by
    simp only [s', foldBlock_level, oodBatch_level, queryBatch]; rfl
  obtain ⟨b1, b2⟩ := batch_query_counts (Query.oodFold (encode l.lambda) (oodList encode l.oods)
    (foldModel encode l.folds st, 1)).1 (foldModel encode l.folds st).n qs (encode l.lambda) _ _ _
  rw [hs']
  refine ⟨ModelFits.batch _ hof _ (by simp [Basis.dimension, hon]) (by rw [hon, hn1]; omega) _ _ _, ?_, ?_, ?_⟩
  · simp only [batchScalar]; rw [hon, hn1]
  · rw [b1, c1, foldModel_saved]; simp [oodList]
  · rw [b2, c2, foldModel_saved]

end LevelModel

/-! ## A middle level of the replay loop -/

section Mid
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat) (tape : V → List (Event E Q R K) → Prop)

theorem mid_level_eq {T1 : Type}
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (ht : Transcript inst encode tape)
    (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (config : whir.config.Config) (oracle : whir.verify.Oracle R) (iter : core.ops.range.Range Usize)
    (w : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : Query.StateRel encode index w st)
    (v : V) (n : Usize) (hst : st.n = n.val)
    (l : SLevel E Q R K) (root : R) (hhead : l.head = .inl root) (rest : List (Event E Q R K))
    (horoot : oracle.root = l.root)
    (hodepth : (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate).val = l.depth)
    (howords : (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved).val = l.rowWords)
    (hleaf : l.leafWords = l.rowWords)
    (hv : tape v (levelTape l ++ rest))
    (hit : iter.start.val < iter.end.val) (hiend : iter.end = alloc.vec.Vec.len config.level_ks)
    (hmid : iter.start.val + 1 < config.level_ks.val.length)
    (hfl : l.folds.length = (config.level_ks.val[iter.start.val]'(by omega)).val)
    (hkn : l.folds.length ≤ n.val)
    (hol : iter.start.val + 2 < config.ood_samples.val.length)
    (hoodn : l.oods.length = (config.ood_samples.val[iter.start.val + 2]'hol).val)
    (hoodz : ∀ o ∈ l.oods, o.1.length = n.val - l.folds.length)
    (hgl : iter.start.val + 1 < config.grinding_bits.val.length)
    (hql : iter.start.val + 1 < config.queries.val.length)
    (hg : config.grinding_bits.val[iter.start.val + 1] ≤ U32.max)
    (hbits : (config.grinding_bits.val[iter.start.val + 1]).val = l.bits)
    (hcount : l.queries.length = (config.queries.val[iter.start.val + 1]).val)
    (hrows : l.rows.length = l.queries.length) (hne : l.rows ≠ [])
    (hwidth : ∀ r ∈ l.rows, r.length = 3 * 2 ^ l.folds.length) (hk64 : l.folds.length < 64)
    (hrl : iter.start.val + 2 < config.log_inv_rates.val.length)
    (hk2 : (config.level_ks.val[iter.start.val + 1]).val ≤ n.val - l.folds.length)
    (hcap : w.ris.val.length + l.folds.length ≤ Usize.max)
    (hcapo : w.oods.val.length + l.oods.length < Usize.max) (hcapl : w.levels.val.length < Usize.max)
    (j : Nat) (hj : j ≠ 0) :
    ∃ iter' v' w' n' oracle',
      whir.verify.verify_loop4.body inst W config weight_at iter v w n oracle =
        .ok (.cont (iter', v', w', n', oracle')) ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end ∧ tape v' rest ∧
      n'.val = n.val - l.folds.length ∧ w'.ris.val = w.ris.val ++ l.folds.map (·.1) ∧
      Query.StateRel encode index w'
        (queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j (l.chal encode)
          (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
          (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
            (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st))) ∧
      oracle'.root = root ∧
      oracle'.log_num_interleaved.val = (config.level_ks.val[iter.start.val + 1]'hmid).val ∧
      oracle'.log_msg_cols.val = n.val - l.folds.length - (config.level_ks.val[iter.start.val + 1]'hmid).val ∧
      oracle'.log_inv_rate.val = (config.log_inv_rates.val[iter.start.val + 2]'hrl).val := by
  have hlk := config.level_ks.property
  have hi1 := succ_val iter.start config.level_ks.val.length (by omega) (by omega)
  have hi2 : (Std.Usize.wrapping_add iter.start 2#usize).val = iter.start.val + 2 := by
    have := config.ood_samples.property
    rw [Std.Usize.wrapping_add_val_eq]
    have : iter.start.val + 2 < UScalar.size .Usize := by
      have := Usize.max_def; simp only [UScalar.size] at *; scalar_tac
    have h2 : (2#usize).val = 2 := by simp
    rw [h2]
    exact Nat.mod_eq_of_lt this
  obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some iter hit
  set k := config.level_ks.val[iter.start.val]'(by omega) with hkdef
  have hidx : Slice.index_usize (alloc.vec.Vec.deref config.level_ks) iter.start = .ok k := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; omega)]
    simp [alloc.vec.Vec.deref, hkdef]
  have hnk : ¬ (n.val < k.val) := by omega
  -- fold rounds
  obtain ⟨rs, w1, v1, hfold, hv1, ers, eris1, elev1, eoods1, hrel1, hn1⟩ :=
    fold_rounds_eq inst encode const index tape h ht w st hrel v k l.folds _ hfl
      (by simpa [levelTape, List.append_assoc] using hv) hcap
  -- root
  have hv1' : tape v1 (.root root :: (oodTape l.oods ++ (batchTape l ++ rest))) := by
    rw [hhead] at hv1; exact hv1
  obtain ⟨v2, hroot, hv2⟩ := ht.root v1 root _ hv1'
  -- out-of-domain claims
  have hsub : (Std.Usize.wrapping_sub n k).val = n.val - k.val := Fold.sub_val _ _ (by omega)
  obtain ⟨n1, hn1e⟩ : ∃ n1, Std.Usize.wrapping_sub n k = n1 := ⟨_, rfl⟩
  rw [hn1e] at hsub
  set cnt := config.ood_samples.val[iter.start.val + 2]'hol with hcnt
  have hidxo : Slice.index_usize (alloc.vec.Vec.deref config.ood_samples)
      (Std.Usize.wrapping_add iter.start 2#usize) = .ok cnt := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; omega)]
    simp [alloc.vec.Vec.deref, hcnt, hi2]
  obtain ⟨oodsV, v3, hrep, hv3, eoods⟩ := replay_all_eq inst encode const tape h ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v2 cnt n1 l.oods _ hoodn
    (fun d hd => by rw [hsub, hoodz d hd, hfl]) hv2
  -- query phase
  obtain ⟨ph, hph, hphc, hphg, hphd⟩ : ∃ ph, whir.verify.WhirReplay.phase inst config (Std.Usize.wrapping_add iter.start 1#usize)
      (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate) = .ok ph ∧
      ph.count = config.queries.val[(Std.Usize.wrapping_add iter.start 1#usize).val]'(by rw [hi1]; exact hql) ∧
      ph.grinding = UScalar.cast .U32 (config.grinding_bits.val[(Std.Usize.wrapping_add iter.start 1#usize).val]'(by
        rw [hi1]; exact hgl)) ∧
      ph.depth = Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate :=
    ⟨_, phase_eq inst config (Std.Usize.wrapping_add iter.start 1#usize)
      (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate) (by rw [hi1]; exact hgl)
      (by rw [hi1]; exact hql) (by simp only [hi1]; exact hg), rfl, rfl, rfl⟩
  have hgv : ph.grinding.val = l.bits := by
    rw [hphg, cast_u32_val _ (by simp only [hi1]; exact hg)]; simp only [hi1]; exact hbits
  obtain ⟨b, v4, hbq, hv4, ebq, ebl, ebw⟩ := begin_query_eq inst encode const tape h ht v3 ph l.queries l.lambda _
    (by rw [hphc]; simp only [hi1]; exact hcount) (by rw [hgv, hphd, hodepth]; exact hv3)
  have hv4' : tape v4 (.rows l.root l.depth l.queries l.rowWords l.rowWords l.rows ::
      .poly l.intro.1 l.intro.2 :: rest) := by
    rw [hleaf] at hv4; exact hv4
  obtain ⟨rowsV, v5, hopen, hv5, erows⟩ := open_e_rows_eq inst encode encodeK ofLimbs index tape hr ht oracle v4
    (alloc.vec.Vec.deref b.queries) l.root l.depth l.queries l.rowWords l.rows _
    (fun r hr' => by rw [hwidth r hr']; omega) horoot hodepth (by simpa [alloc.vec.Vec.deref] using ebq) howords hv4'
  have hlenrows : rowsV.val.length = l.rows.length := by simpa using congrArg List.length erows
  have hrows_ne : rowsV.val ≠ [] := by
    intro hnil; apply hne; rw [hnil] at hlenrows; exact List.eq_nil_of_length_eq_zero hlenrows.symm
  have hwidthV : ∀ r ∈ rowsV.val, r.val.length = 2 ^ rs.val.length := by
    intro r hr'
    have hmem : r.val.map encode ∈ l.rows.map (eRow encodeK ofLimbs) := by
      rw [← erows]; exact List.mem_map_of_mem hr'
    obtain ⟨wd, hwd, hwe⟩ := List.mem_map.mp hmem
    have := congrArg List.length hwe
    simp only [eRow, List.length_map, List.length_range] at this
    rw [hwidth wd hwd] at this
    rw [ers]; simp at this ⊢
    omega
  obtain ⟨sum, hsum, esum⟩ := Query.ext_enforced_eq inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
    inst encode const h v5 rowsV (alloc.vec.Vec.deref rs) (alloc.vec.Vec.deref b.weights) (2 ^ rs.val.length)
    hrows_ne (by simpa [alloc.vec.Vec.deref] using hwidthV) (by simp [alloc.vec.Vec.deref, ers] <;> omega)
    (by simp [alloc.vec.Vec.deref]) (by
      have := congrArg List.length ebw
      simp only [List.length_map, Array.length_toList, BatchingRefinement.size_powers] at this
      simp [alloc.vec.Vec.deref, this, hlenrows, hrows])
  obtain ⟨intro, v6, hrecv, hic, hia, hib, hv6⟩ := recv_eq inst encode const tape h ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v5 sum l.intro.1 l.intro.2 _ hv5
  have hoodsI : ∀ o ∈ oodsV.val, encode o.intro.b = encode o.y + encode o.intro.a := by
    intro o ho
    obtain ⟨d, _, hod⟩ := forall₂_mem eoods o ho
    obtain ⟨_, hy, _, ha, hb⟩ := hod
    rw [hb, hy, ha]
  have hcapo' : w1.oods.val.length + oodsV.val.length < Usize.max := by
    rw [eoods1, eoods.length_eq]; exact hcapo
  obtain ⟨w2, hfin, hris2, hrel2⟩ := Query.finish_query_eq inst encode const index h w1
    (foldModel encode l.folds st) hrel1 v5 v5 v6 b oodsV n1 sum intro (ht.end_scope v5) hrecv
    (by rw [hib, hia]) hoodsI (by rw [ebw, ebq, ebl]) hcapo' (by rw [elev1]; exact hcapl)
  -- next oracle
  obtain ⟨o', horacle, ho1, ho2, ho3, ho4⟩ := oracle_eq inst config root (Std.Usize.wrapping_add iter.start 1#usize) n1
    (by rw [hi1]; exact hmid) (by simp only [hi1, hsub]; omega) (by rw [hi1]; exact hrl)
  refine ⟨iter1, v6, w2, n1, o', ?_, hs1, he1, hv6, by rw [hsub, hfl], by rw [hris2, eris1, ers], ?_, ho1,
    by rw [ho2]; simp only [hi1], by rw [ho3, hsub, hfl]; simp only [hi1],
    by rw [ho4]; simp only [hi1, show iter.start.val + 1 + 1 = iter.start.val + 2 by omega]⟩
  · have hne1 : ¬ (Std.Usize.wrapping_add iter.start 1#usize = alloc.vec.Vec.len config.level_ks) := by
      intro he; have := congrArg UScalar.val he; rw [hi1] at this; simp at this; omega
    simp [whir.verify.verify_loop4.body, hnext, whir.config.Config.impl.level_ks, hidx, hnk, hfold,
      core.result.Result.Insts.CoreOpsTry.branch, lift, whir.config.Config.level_steps, hne1, hroot,
      whir.config.Config.impl.ood_samples, hidxo, hn1e, hrep, whir.verify.Oracle.depth, hph, hbq, hopen, hsum,
      hfin, horacle]
  · rw [← level_model_eq encode encodeK ofLimbs index l st j hj b sum intro oodsV.val rowsV.val ebq ebl
      (by rw [ebw]) eoods (by rw [esum, ← ers]; simp [alloc.vec.Vec.deref]) erows hic hia n1.val
      (by rw [hsub, hn1, hst])]
    exact hrel2

/-- The loop's last iteration replays the last level against the model's last level and
the closing rounds. -/
theorem last_iter_eq {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : whir.config.Config) (oracle : whir.verify.Oracle R) (iter : core.ops.range.Range Usize)
    (w : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : Query.StateRel encode index w st)
    (hfits : ModelFits st) (v : V) (n : Usize) (hst : st.n = n.val) (hn64 : n.val < 64)
    (l : SLevel E Q R K) (ys : List E) (hhead : l.head = .inr ys) (hoods : l.oods = [])
    (horoot : oracle.root = l.root)
    (hodepth : (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate).val = l.depth)
    (howords : (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved).val = l.rowWords)
    (hleaf : l.leafWords = l.rowWords)
    (tail : List E) (msgs : List (E × E)) (rest : List (Event E Q R K))
    (hv : tape v (levelTape l ++ (tailTape tail msgs ++ rest)))
    (hit : iter.start.val < iter.end.val) (hiend : iter.end = alloc.vec.Vec.len config.level_ks)
    (hlast : iter.start.val + 1 = config.level_ks.val.length)
    (hfl : l.folds.length = (config.level_ks.val[iter.start.val]'(by omega)).val)
    (hkn : l.folds.length ≤ n.val) (hys : ys.length = 2 ^ (n.val - l.folds.length))
    (hgl : config.level_ks.val.length < config.grinding_bits.val.length)
    (hql : config.level_ks.val.length < config.queries.val.length)
    (hg : config.grinding_bits.val[config.level_ks.val.length] ≤ U32.max)
    (hbits : (config.grinding_bits.val[config.level_ks.val.length]).val = l.bits)
    (hcount : l.queries.length = (config.queries.val[config.level_ks.val.length]).val)
    (hrows : l.rows.length = l.queries.length) (hne : l.rows ≠ [])
    (hwidth : ∀ r ∈ l.rows, r.length = 3 * 2 ^ l.folds.length)
    (htail : tail.length = n.val - l.folds.length) (hmsgs : msgs.length + 1 = tail.length)
    (hk : config.initial_k.val ≤ w.ris.val.length + l.folds.length + tail.length)
    (hcap : w.ris.val.length + l.folds.length + tail.length + 1 ≤ Usize.max)
    (hcapo : w.oods.val.length < Usize.max) (hcapl : w.levels.val.length < Usize.max)
    (ch : Protocol.Challenges) (pf : Protocol.Opening) (hch : ch.tail = (tail.map encode).toArray)
    (hpf : pf.tailMessages = (msgs.map fun m => (⟨encode m.1, encode m.2⟩ : Protocol.Message Concrete.E)).toArray)
    (j : Nat) (hj : j ≠ 0) :
    ∃ r v', whir.verify.verify_loop4.body inst W config weight_at iter v w n oracle =
        .ok (.done (r, v')) ∧
      let sF := queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j
        (l.chal encode) (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st))
      (r = .Ok () ↔ (closeTail ch pf sF).claim =
        sourceTerminal (callerAt (rotatePoint config.initial_k.val (sF.source.ris ++ tail.map encode).toArray))
          sF.source.saved sF.source.ris (tail.map encode) (ys.map encode).toArray) := by
  have hlk := config.level_ks.property
  have hi1 := succ_val iter.start config.level_ks.val.length (by omega) (by omega)
  obtain ⟨iter1, hnext, hs1, he1⟩ := range_next_some iter hit
  set k := config.level_ks.val[iter.start.val]'(by omega) with hkdef
  have hidx : Slice.index_usize (alloc.vec.Vec.deref config.level_ks) iter.start = .ok k := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; omega)]
    simp [alloc.vec.Vec.deref, hkdef]
  have hnk : ¬ (n.val < k.val) := by omega
  obtain ⟨rs, w1, v1, hfold, hv1, ers, eris1, elev1, eoods1, hrel1, hn1⟩ :=
    fold_rounds_eq inst encode const index tape h ht w st hrel v k l.folds _ hfl
      (by simpa [levelTape, List.append_assoc] using hv) (by omega)
  have hsub : (Std.Usize.wrapping_sub n k).val = n.val - k.val := Fold.sub_val _ _ (by omega)
  obtain ⟨n1, hn1e⟩ : ∃ n1, Std.Usize.wrapping_sub n k = n1 := ⟨_, rfl⟩
  rw [hn1e] at hsub
  have heq1 : Std.Usize.wrapping_add iter.start 1#usize = alloc.vec.Vec.len config.level_ks :=
    UScalar.eq_of_val_eq (by rw [hi1, alloc.vec.Vec.len_val]; simpa using hlast)
  have hv1' : tape v1 ([.scalars ys, .grind l.bits, .queries l.depth l.queries, .sample l.lambda,
      .rows l.root l.depth l.queries l.rowWords l.rowWords l.rows,
      .poly l.intro.1 l.intro.2] ++ (tailTape tail msgs ++ rest)) := by
    rw [hhead, hoods] at hv1; simpa [headTape, oodTape, batchTape, hleaf] using hv1
  have hlen : (alloc.vec.Vec.len config.level_ks).val = config.level_ks.val.length := by simp
  have hfits1 := ModelFits.ofFold encode l.folds st hfits (by omega)
  have hrsl : (alloc.vec.Vec.deref rs).val.length = l.folds.length := by simp [alloc.vec.Vec.deref, ers]
  obtain ⟨r, v', wF, hll, hrelF, hrisF, hiff⟩ := last_level_eq inst encode const encodeK ofLimbs index tape hw h hr hn
    ht hclone hens W weight_at callerAt hcall config oracle l.root l.depth l.rowWords l.bits horoot hodepth howords
    (alloc.vec.Vec.deref rs) w1 (foldModel encode l.folds st)
    hrel1 hfits1 v1 n1 (by rw [hn1, hst, hsub]) (by omega) ys l.queries l.lambda l.rows l.intro.1 l.intro.2
    tail msgs rest hv1' (by rw [hys, hsub, hfl]) (by rw [hlen]; exact hgl) (by rw [hlen]; exact hql)
    (by simp only [hlen]; exact hg) (by simp only [hlen]; exact hbits) (by simp only [hlen]; exact hcount) hrows hne
    (fun r hr' => by rw [hwidth r hr', hrsl]) (by omega) (by rw [htail, hsub, hfl])
    hmsgs (by rw [eris1, ers]; simp; omega) (by rw [eris1, ers]; simp; omega) (by rw [eoods1]; exact hcapo)
    (by rw [elev1]; exact hcapl) ch pf hch hpf
  refine ⟨r, v', ?_, ?_⟩
  · simp [whir.verify.verify_loop4.body, hnext, whir.config.Config.impl.level_ks, hidx, hnk, hfold,
      core.result.Result.Insts.CoreOpsTry.branch, lift, whir.config.Config.level_steps, heq1, hn1e, hll]
  · intro sF
    have hsF : sF = lastState encode encodeK ofLimbs index (foldModel encode l.folds st) n1.val l.queries l.lambda
        l.rows (alloc.vec.Vec.deref rs).val l.intro.1 l.intro.2 := by
      simp only [sF]
      rw [last_model_eq encode encodeK ofLimbs index l st j hj hoods, hn1, hst, hsub]
      simp [alloc.vec.Vec.deref, ers]
    rw [hsF, hiff, terminal_link encode index wF _ hrelF callerAt config.initial_k.val ys tail, eq_comm]

end Mid

/-! ## A script level in the model's checked replay -/

theorem before_add_le (c : Protocol.Config) (hc : c.valid = true) :
    ∀ j ≤ c.folds.size, WHIRNativeGuards.before c j + j ≤ c.logN := by
  intro j
  induction j with
  | zero => intro _; simp [WHIRNativeGuards.before]
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2, -⟩ := WHIRNativeGuards.config_level c hc j (by omega)
    have hs := WHIRNativeGuards.before_step c j (by omega)
    have hb : WHIRNativeGuards.before c (j + 1) = CausalGame.remaining c j := rfl
    have := ih (by omega)
    omega

theorem folds_size_le (c : Protocol.Config) (hc : c.valid = true) : c.folds.size ≤ c.logN := by
  have := before_add_le c hc c.folds.size le_rfl
  omega

section ScriptLevel
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {R K Q E : Type} (encode : E → Concrete.E) (encodeK : K → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E) (index : Q → Nat)

theorem residual_last (s : Script E Q R K) (hl : 0 < s.levels.length) (ys : List E)
    (hys : (s.levels[s.levels.length - 1]'(by omega)).head = .inr ys) :
    (s.prf encode encodeK ofLimbs).residual = (ys.map encode).toArray := by
  have : s.levels.getLast? = some (s.levels[s.levels.length - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem]
  simp [Script.prf, this, hys, residualOf]

/-- A level of a valid script passes the model's level check and returns the level's
query batch. -/
theorem script_level_any (c : Protocol.Config) (s : Script E Q R K) (lanes : Nat)
    (hch : (s.chal encode).valid c = true) (hS : ScriptShape index c s lanes) (init st : State) (j : Nat)
    (hj : j < c.folds.size)
    (hrun : Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) j 0 init = .ok st)
    (hst : st.n = WHIRNativeGuards.before c j) :
    let l := s.levels[j]'(by rw [hS.len]; exact hj)
    Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) (j + 1) 0 init =
      .ok (queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs (j == 0)) st).n j (l.chal encode)
        (l.prf encode encodeK ofLimbs (j == 0)) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs (j == 0))
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs (j == 0)) st))) := by
  intro l
  have hjl : j < s.levels.length := by rw [hS.len]; exact hj
  obtain ⟨hfl, hol, hoz, qsA, hqA, eqA, hql⟩ := level_facts encode index c s lanes hch hS j hj
  have hstep := WHIRNativeGuards.before_step c j hj
  have hfb : (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs (j == 0)) st).n =
      CausalGame.remaining c j := by
    rw [foldBlock_level, foldModel_n, hst, ← hstep, hfl]
  have hqs : qsA = (l.queries.map index).toArray := by
    rw [← eqA]
  have hc : (s.chal encode).levels[j]! = l.chal encode := chal_get encode s j hjl
  have hp : (s.prf encode encodeK ofLimbs).levels[j]! = l.prf encode encodeK ofLimbs (j == 0) :=
    prf_get encode encodeK ofLimbs s j hjl
  rw [runChecked_last, hrun]
  show verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs) (0 + j) st = _
  rw [Nat.zero_add]
  have hok := verifyLevel_ok c (s.chal encode) (s.prf encode encodeK ofLimbs) j st qsA
    (by rw [hc, hp]; simp [SLevel.prf, SLevel.chal])
    (by rw [hc, hp]; simp [SLevel.prf, SLevel.chal])
    (by
      rw [hc, hp]
      by_cases hm : j + 1 < c.folds.size
      · rw [if_pos hm]
        obtain ⟨r, hr⟩ := hS.head j (by rw [hS.len]; exact hm)
        simp [SLevel.prf, l, hr]
      · rw [if_neg hm]
        have hjL : j = s.levels.length - 1 := by rw [hS.len]; omega
        obtain ⟨ys, hys, hyl⟩ := hS.last (by omega)
        have hl : l = s.levels[s.levels.length - 1]'(by omega) := by simp only [l, hjL]
        refine ⟨by simp [SLevel.prf, hl, hys], ?_⟩
        rw [residual_last encode encodeK ofLimbs s (by omega) ys hys, hfb]
        simp [hyl, show c.folds.size - 1 = j by omega])
    (by rw [hc, hp, hfb]; simpa [SLevel.chal] using hqA)
    (by rw [hp, hqs]; cases j == 0 <;> simp [SLevel.prf, l, hS.rows j hjl])
  rw [hc, hp, hqs] at hok
  exact hok

/-- A later level of a valid script passes the model's level check and returns the
level's query batch. -/
theorem script_level_ok (c : Protocol.Config) (s : Script E Q R K) (lanes : Nat)
    (hch : (s.chal encode).valid c = true) (hS : ScriptShape index c s lanes) (init st : State) (j : Nat)
    (hj : j < c.folds.size) (hj0 : j ≠ 0)
    (hrun : Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) j 0 init = .ok st)
    (hst : st.n = WHIRNativeGuards.before c j) :
    let l := s.levels[j]'(by rw [hS.len]; exact hj)
    Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) (j + 1) 0 init =
      .ok (queryBatch (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st).n j (l.chal encode)
        (l.prf encode encodeK ofLimbs false) (l.queries.map index).toArray
        (oodBatch (l.chal encode) (l.prf encode encodeK ofLimbs false)
          (foldBlock (l.chal encode) (l.prf encode encodeK ofLimbs false) st))) := by
  have h := script_level_any encode encodeK ofLimbs index c s lanes hch hS init st j hj hrun hst
  have h0 : (j == 0) = false := by simpa using hj0
  rw [h0] at h
  exact h

end ScriptLevel

/-! ## The model's verifier around its checked level replay -/

section Native
open AccumulatedTerminalRefinement WHIRNativeArithmetic

theorem nativeVerify_ok_iff (c : Protocol.Config) (ch : Protocol.Challenges) (lanes : Nat) (initialClaim : Concrete.E)
    (callerAt : Array Concrete.E → Concrete.E) (pf : Protocol.Opening) (sL : State)
    (hch : ch.valid c = true) (hl0 : lanes ≠ 0) (hlm : lanes ≤ 2 ^ c.folds[0]!)
    (hsize : pf.levels.size = c.folds.size) (htm : pf.tailMessages.size + 1 = ch.tail.size)
    (hrun : Protocol.runChecked (verifyLevel c ch pf) c.folds.size 0
      ⟨c.logN, initialClaim, pf.initial, ⟨[], []⟩⟩ = .ok sL) :
    nativeVerify c ch lanes initialClaim callerAt pf = .ok () ↔
      (closeTail ch pf sL).claim = sourceTerminal (callerAt (rotatePoint c.folds[0]!
        (sL.source.ris ++ ch.tail.toList).toArray)) sL.source.saved sL.source.ris ch.tail.toList pf.residual := by
  have hlm' : ¬ (2 ^ c.folds[0]! < lanes) := by omega
  simp only [nativeVerify, hch, hl0, hlm', hsize, htm, hrun, Bool.not_true, Bool.false_or, beq_iff_eq,
    decide_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.or_self]
  rw [show ∀ f : State → Except String Unit, ((Except.ok sL : Except String State) >>= f) = f sL from
    fun _ => rfl]
  by_cases he : (closeTail ch pf sL).claim = sourceTerminal (callerAt (rotatePoint c.folds[0]!
      (sL.source.ris ++ ch.tail.toList).toArray)) sL.source.saved sL.source.ris ch.tail.toList pf.residual
  · simp [he]; rfl
  · have : ((!(closeTail ch pf sL).claim == sourceTerminal (callerAt (rotatePoint c.folds[0]!
        (sL.source.ris ++ ch.tail.toList).toArray)) sL.source.saved sL.source.ris ch.tail.toList pf.residual)) =
        true := by simpa using he
    simp only [this, ↓reduceIte, he, iff_false]
    intro h; cases h

theorem nativeVerify_lanes (c : Protocol.Config) (ch : Protocol.Challenges) (lanes : Nat) (initialClaim : Concrete.E)
    (callerAt : Array Concrete.E → Concrete.E) (pf : Protocol.Opening)
    (hl : lanes = 0 ∨ 2 ^ c.folds[0]! < lanes) :
    nativeVerify c ch lanes initialClaim callerAt pf ≠ .ok () := by
  intro h
  have : (!ch.valid c || lanes == 0 || decide (lanes > 2 ^ c.folds[0]!)) = true := by
    rcases hl with hl | hl <;> simp [hl]
  simp only [nativeVerify, this, ↓reduceIte] at h
  cases h

end Native

/-! ## The level loop -/

section Loop
open AccumulatedTerminalRefinement WHIRNativeArithmetic
variable {V R K Q E : Type} (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : K → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Q → Nat) (tape : V → List (Event E Q R K) → Prop)

/-- Each script level's proof-of-work bits are the configuration's grinding bits for it. -/
def GrindShape (config : whir.config.Config) (s : Script E Q R K) : Prop :=
  ∀ i (hi : i < s.levels.length) (hg : i < config.grinding_bits.val.length),
    (s.levels[i]).bits = (config.grinding_bits.val[i]).val

/-- The oracle the replay builds for level `j + 1` answers the rows read with that level's
depth and with three words per element of the level's fold as its leaf width. -/
theorem oracle_shape (hw : System.Platform.numBits = 64) {config : whir.config.Config} {c : Protocol.Config}
    {log_n : Usize} (hcfg : ConfigRel config c log_n) (hcv : c.valid = true) (o : whir.verify.Oracle R) (j : Nat)
    (hj : j + 1 < c.folds.size) (hk : o.log_num_interleaved.val = c.folds[j + 1]!)
    (hm : o.log_msg_cols.val = CausalGame.remaining c j - c.folds[j + 1]!)
    (hr : o.log_inv_rate.val = c.rates[j + 1]!) :
    (Std.Usize.wrapping_add o.log_msg_cols o.log_inv_rate).val = CausalGame.remaining c (j + 1) + c.rates[j + 1]! ∧
      (Std.Usize.wrapping_shl 3#usize o.log_num_interleaved).val = 3 * 2 ^ c.folds[j + 1]! := by
  have hstep := WHIRNativeGuards.before_step c (j + 1) hj
  have hb : WHIRNativeGuards.before c (j + 1) = CausalGame.remaining c j := rfl
  have h64 := (WHIRNativeGuards.config_level c hcv (j + 1) hj).2.2.2.2
  have hL := hcfg.folds_size
  have hks : c.folds[j + 1]! < 62 := by
    rw [hcfg.foldk j (by omega)]; exact hcfg.ks _ (List.getElem_mem _)
  refine ⟨?_, ?_⟩
  · rw [add_val_lt _ _ (by omega)]; omega
  · rw [shl_three_val hw _ (by omega), hk]

theorem verify_loop4_eq {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : whir.config.Config) (c : Protocol.Config) (log_n : Usize) (hcfg : ConfigRel config c log_n)
    (s : Script E Q R K) (lanes : Nat) (hch : (s.chal encode).valid c = true) (hS : ScriptShape index c s lanes)
    (hgs : GrindShape config s)
    (init : State) (rest : List (Event E Q R K)) :
    ∀ (m : Nat) (iter : core.ops.range.Range Usize) (v : V) (w : whir.verify.WhirReplay V R K Q E) (n : Usize)
      (oracle : whir.verify.Oracle R) (st : State),
      c.folds.size - 2 - iter.start.val = m → iter.start.val + 2 ≤ c.folds.size →
      iter.end = alloc.vec.Vec.len config.level_ks →
      Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) (iter.start.val + 1) 0
        init = .ok st →
      Query.StateRel encode index w st → ModelFits st → st.n = n.val →
      n.val = CausalGame.remaining c iter.start.val → w.ris.val.length + n.val = c.logN →
      w.oods.val.length + ((s.levels.drop (iter.start.val + 1)).map fun l => l.oods.length).sum < Usize.max →
      w.levels.val.length = iter.start.val + 1 →
      (∀ hjl : iter.start.val + 1 < s.levels.length, (s.levels[iter.start.val + 1]'hjl).root = oracle.root) →
      (Std.Usize.wrapping_add oracle.log_msg_cols oracle.log_inv_rate).val =
        CausalGame.remaining c (iter.start.val + 1) + c.rates[iter.start.val + 1]! →
      (Std.Usize.wrapping_shl 3#usize oracle.log_num_interleaved).val = 3 * 2 ^ c.folds[iter.start.val + 1]! →
      tape v ((s.levels.drop (iter.start.val + 1)).flatMap levelTape ++ (tailTape s.tail s.tailMsgs ++ rest)) →
      ∃ sL r v', Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) c.folds.size 0
          init = .ok sL ∧
        whir.verify.verify_loop4 inst W iter v config weight_at w n oracle = .ok (r, v') ∧
        (r = .Ok () ↔ (closeTail (s.chal encode) (s.prf encode encodeK ofLimbs) sL).claim =
          sourceTerminal (callerAt (rotatePoint c.folds[0]! (sL.source.ris ++ (s.chal encode).tail.toList).toArray))
            sL.source.saved sL.source.ris (s.chal encode).tail.toList (s.prf encode encodeK ofLimbs).residual) := by
  have hL := hcfg.folds_size
  have hcv := WHIRNativeGuards.challenges_config c _ hch
  obtain ⟨hrl, hqlen, holen⟩ := hcfg.lengths hcv
  have hgrl := hcfg.lengths' hcv
  have hsl := hS.len
  have hlog := hcfg.log64
  have hlogN := hcfg.logN
  intro m
  induction m with
  | zero =>
    intro iter v w n oracle st hm h2 hend hrun hrel hfits hst hnr hris hoods hlev hor hod how hv
    set i := iter.start.val with hidef
    have hiL : i + 2 = c.folds.size := by omega
    have hj : i + 1 < c.folds.size := by omega
    have hjl : i + 1 < s.levels.length := by omega
    obtain ⟨hfl, hol, hoz, qsA, hqA, eqA, hql⟩ := level_facts encode index c s lanes hch hS (i + 1) hj
    have hcl := WHIRNativeGuards.config_level c hcv (i + 1) hj
    have hbefore : WHIRNativeGuards.before c (i + 1) = CausalGame.remaining c i := rfl
    have hstep := WHIRNativeGuards.before_step c (i + 1) hj
    have hk : c.folds[i + 1]! = (config.level_ks.val[i]'(by omega)).val := hcfg.foldk i (by omega)
    obtain ⟨ys, hys, hyl⟩ := hS.last (by omega)
    have hlast : (s.levels[s.levels.length - 1]'(by omega)) = s.levels[i + 1]'hjl := by
      simp only [show s.levels.length - 1 = i + 1 by omega]
    rw [hlast] at hys
    have hrowsl := hS.rows (i + 1) hjl
    have hext := hS.ext (i + 1) hjl (by omega)
    obtain ⟨hrw, hlw⟩ := hS.extWords (i + 1) hjl (by omega)
    have hdep := hS.depth (i + 1) hjl
    have hor1 := hor hjl
    have hdrop : s.levels.drop (i + 1) = [s.levels[i + 1]'hjl] := by
      rw [List.drop_eq_getElem_cons hjl, List.drop_of_length_le (by omega)]
    have hfsz := folds_size_le c hcv
    set l := s.levels[i + 1]'hjl with hldef
    have hoods0 : l.oods = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [hol]; simp [CausalGame.oodCount]; omega
    have hrun' := script_level_ok encode encodeK ofLimbs index c s lanes hch hS init st (i + 1) hj (by omega)
      hrun (by rw [hst, hnr]; rfl)
    dsimp only at hrun'
    rw [show i + 1 + 1 = c.folds.size by omega] at hrun'
    have hkb : c.folds[i + 1]! < n.val := by have := hcl.2.1; rw [hbefore] at this; omega
    have hcl0 := WHIRNativeGuards.config_level c hcv 0 (by omega)
    have hb0 : WHIRNativeGuards.before c 0 = c.logN := by simp [WHIRNativeGuards.before]
    have hmax : 64 < Usize.max := by scalar_tac
    rw [hdrop] at hoods
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hoods0, List.length_nil] at hoods
    have htl := WHIRNativeGuards.challenges_tail c _ hch
    have htail : s.tail.length = n.val - l.folds.length := by
      have : (s.chal encode).tail.size = s.tail.length := by simp [Script.chal]
      rw [← this, htl, hnr, hfl, ← hbefore, hstep]
      simp only [CausalGame.remaining]
      congr 2
      rw [List.take_of_length_le (by simp; omega)]
    have hqpos : 0 < c.queries[i + 1]! := hcl.2.2.2.1
    obtain ⟨r, v', hbody, hiff⟩ := last_iter_eq inst encode const encodeK ofLimbs index tape hw h hr hn ht hclone
      hens W weight_at callerAt hcall config oracle iter w st hrel hfits v n hst (by omega) l ys hys hoods0
      hor1.symm (by rw [hod, hdep]) (by rw [how, hrw]) (by rw [hlw, hrw])
      s.tail s.tailMsgs rest (by rw [hdrop] at hv; simpa using hv) (by rw [hend]; simp; omega) hend (by omega)
      (by rw [hfl, hk]) (by rw [hfl]; omega)
      (by rw [hyl, hfl, hnr, ← hbefore, hstep]; congr 2; omega)
      (by omega) (by omega) (hcfg.grinding _ (List.getElem_mem _))
      (by have e := hgs (i + 1) hjl (by omega); simp only [show config.level_ks.val.length = i + 1 by omega]
          exact e.symm)
      (by rw [hql, hcfg.query (i + 1) (by omega)]; congr 2; omega) hrowsl
      (by intro hnil; have := congrArg List.length hnil; simp only [List.length_nil] at this; omega)
      (fun r hr' => by rw [hext r hr', hfl]) htail hS.tail
      (by have := hcfg.fold0; have := hcl0.2.1; rw [hb0] at this; omega) (by omega) (by omega) (by omega)
      (s.chal encode) (s.prf encode encodeK ofLimbs) rfl rfl (i + 1) (by omega)
    dsimp only at hiff
    refine ⟨_, r, v', hrun', ?_, ?_⟩
    · unfold whir.verify.verify_loop4
      apply loop_done
      exact hbody
    · rw [hiff, hcfg.fold0, residual_last encode encodeK ofLimbs s (by omega) ys (by rw [hlast]; exact hys)]
      simp only [Script.chal, List.toList_toArray]
      exact Iff.rfl
  | succ m ih =>
    intro iter v w n oracle st hm h2 hend hrun hrel hfits hst hnr hris hoods hlev hor hod how hv
    set i := iter.start.val with hidef
    have hj2 : i + 2 < c.folds.size := by omega
    have hj : i + 1 < c.folds.size := by omega
    have hjl : i + 1 < s.levels.length := by omega
    obtain ⟨hfl, hol, hoz, qsA, hqA, eqA, hql⟩ := level_facts encode index c s lanes hch hS (i + 1) hj
    have hcl := WHIRNativeGuards.config_level c hcv (i + 1) hj
    have hcl2 := WHIRNativeGuards.config_level c hcv (i + 2) hj2
    have hbefore : WHIRNativeGuards.before c (i + 1) = CausalGame.remaining c i := rfl
    have hbefore2 : WHIRNativeGuards.before c (i + 2) = CausalGame.remaining c (i + 1) := rfl
    have hstep := WHIRNativeGuards.before_step c (i + 1) hj
    have hk : c.folds[i + 1]! = (config.level_ks.val[i]'(by omega)).val := hcfg.foldk i (by omega)
    have hk2 : c.folds[i + 2]! = (config.level_ks.val[i + 1]'(by omega)).val := hcfg.foldk (i + 1) (by omega)
    have hroot := hS.roots (i + 1) (by omega)
    have hrowsl := hS.rows (i + 1) hjl
    have hext := hS.ext (i + 1) hjl (by omega)
    obtain ⟨hrw, hlw⟩ := hS.extWords (i + 1) hjl (by omega)
    have hdep := hS.depth (i + 1) hjl
    have hor1 := hor hjl
    have hdrop : s.levels.drop (i + 1) = (s.levels[i + 1]'hjl) :: s.levels.drop (i + 2) :=
      List.drop_eq_getElem_cons hjl
    have hfsz := folds_size_le c hcv
    have hoodc : CausalGame.oodCount c (i + 1) = (config.ood_samples.val[i + 2]'(by omega)).val := by
      simp only [CausalGame.oodCount, if_pos hj2]; exact hcfg.ood (i + 2) (by omega)
    have hrun' := script_level_ok encode encodeK ofLimbs index c s lanes hch hS init st (i + 1) hj (by omega)
      hrun (by rw [hst, hnr]; rfl)
    dsimp only at hrun'
    set l := s.levels[i + 1]'hjl with hldef
    have hkb : c.folds[i + 1]! < n.val := by have := hcl.2.1; rw [hbefore] at this; omega
    have hmax : 64 < Usize.max := by scalar_tac
    rw [hdrop] at hoods hv
    simp only [List.map_cons, List.sum_cons] at hoods
    have hqpos : 0 < c.queries[i + 1]! := hcl.2.2.2.1
    obtain ⟨iter', v', w', n', oracle', hbody, hs', he', hv', hn', hris', hrel', ho1, ho2, ho3, ho4⟩ :=
      mid_level_eq inst encode const
      encodeK ofLimbs index tape h hr ht W weight_at config oracle iter w st hrel v n hst l _ hroot
      ((s.levels.drop (i + 2)).flatMap levelTape ++ (tailTape s.tail s.tailMsgs ++ rest))
      hor1.symm (by rw [hod, hdep]) (by rw [how, hrw]) (by rw [hlw, hrw])
      (by simpa [List.flatMap_cons, List.append_assoc] using hv) (by rw [hend]; simp; omega) hend (by omega)
      (by rw [hfl, hk]) (by rw [hfl]; omega) (by omega) (by rw [hol, hoodc])
      (fun o ho => by rw [hoz o ho, hfl, hnr, ← hbefore, hstep]) (by omega) (by omega)
      (hcfg.grinding _ (List.getElem_mem _)) (hgs (i + 1) hjl (by omega)).symm
      (by rw [hql, hcfg.query (i + 1) (by omega)])
      hrowsl (by intro hnil; have := congrArg List.length hnil; simp only [List.length_nil] at this; omega)
      (fun r hr' => by rw [hext r hr', hfl]) (by omega) (by omega)
      (by rw [← hk2, hfl]; have := hcl2.2.1; rw [hbefore2, ← hstep, hbefore] at this; omega)
      (by omega) (by omega) (by omega) (i + 1) (by omega)
    obtain ⟨hfits', hn'', hco, hcl'⟩ := level_state_facts encode encodeK ofLimbs l false st (i + 1)
      (l.queries.map index).toArray hfits (by omega) (by omega)
      (fun o ho => by rw [hoz o ho, hfl, hst, hnr, ← hbefore, hstep])
    have hoodlen : w'.oods.val.length = w.oods.val.length + l.oods.length := by
      rw [hrel'.oods.length_eq, hco, ← hrel.oods.length_eq]
    have hlevlen : w'.levels.val.length = w.levels.val.length + 1 := by
      rw [hrel'.levels.length_eq, hcl', ← hrel.levels.length_eq]
    simp only [← hidef] at ho2 ho3 ho4
    have hstep2 := WHIRNativeGuards.before_step c (i + 2) hj2
    have hr2 : c.rates[i + 2]! = (config.log_inv_rates.val[i + 2]'(by omega)).val := hcfg.rate (i + 2) (by omega)
    have h64 := hcl2.2.2.2.2
    have hks2 : oracle'.log_num_interleaved.val < 62 := by rw [ho2]; exact hcfg.ks _ (List.getElem_mem _)
    obtain ⟨sL, r, v'', hL', hloop, hiff⟩ := ih iter' v' w' n' oracle' _ (by omega) (by omega) (by rw [he', hend])
      (by rw [hs']; exact hrun') hrel' hfits' (by rw [hn'', hn', hst])
      (by rw [hn', hs', hfl, hnr, ← hbefore, hstep]) (by rw [hris', hn']; simp; omega)
      (by rw [hoodlen, hs', show i + 1 + 1 = i + 2 by omega]; omega) (by rw [hlevlen, hs']; omega)
      (fun _ => by simp only [hs', ← hidef, ho1])
      (by
        rw [hs', show i + 1 + 1 = i + 2 by omega, add_val_lt _ _ (by omega)]
        omega)
      (by rw [hs', show i + 1 + 1 = i + 2 by omega, shl_three_val hw _ hks2, ho2, ← hk2])
      (by rw [hs']; exact hv')
    refine ⟨sL, r, v'', hL', ?_, hiff⟩
    unfold whir.verify.verify_loop4
    rw [loop_cont hbody]
    unfold whir.verify.verify_loop4 at hloop
    exact hloop

/-- The lane fold: `verify` reads `k - 1` rounds through `fold_rounds`, then the last round's
challenge through `fold_challenge` and its polynomial through `RoundQuad::read`, which together
fold exactly as `fold_rounds_eq` does over all `k` rounds. -/
theorem lane_fold_eq (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (ht : Transcript inst encode tape)
    (self : whir.verify.WhirReplay V R K Q E) (st : State) (hrel : Query.StateRel encode index self st)
    (v : V) (k : Usize) (rounds : List (E × E × E)) (rest : List (Event E Q R K))
    (hk : rounds.length = k.val) (hk1 : 0 < k.val) (hv : tape v (foldTape rounds ++ rest))
    (hcap : self.ris.val.length + rounds.length ≤ Usize.max) :
    ∃ (rs : alloc.vec.Vec E) (self1 : whir.verify.WhirReplay V R K Q E) (v1 : V) (t : E)
      (w1 : whir.verify.WhirReplay V R K Q E) (v2 : V) (rs1 : alloc.vec.Vec E) (q : whir.sumcheck.RoundQuad E)
      (v3 : V),
      whir.verify.WhirReplay.fold_rounds inst self v (Std.Usize.wrapping_sub k 1#usize) =
        .ok (.Ok rs, self1, v1) ∧
      whir.verify.WhirReplay.fold_challenge inst self1 v1 = .ok (t, w1, v2) ∧
      alloc.vec.Vec.push rs t = .ok rs1 ∧
      whir.sumcheck.RoundQuad.read inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst
        inst.fiat_shamirarithVerifierInst v2 w1.t_r = .ok (.Ok q, v3) ∧
      tape v3 rest ∧ rs1.val = rounds.map (·.1) ∧ w1.ris.val = self.ris.val ++ rs1.val ∧
      w1.levels = self.levels ∧ w1.oods = self.oods ∧
      Query.StateRel encode index ({ w1 with quad := q } : whir.verify.WhirReplay V R K Q E)
        (foldModel encode rounds st) ∧
      (foldModel encode rounds st).n = st.n - k.val := by
  obtain ⟨init, last, hsplit⟩ : ∃ init last, rounds = init ++ [last] :=
    ⟨rounds.dropLast, rounds.getLast (by intro he; rw [he] at hk; simp at hk; omega),
      (List.dropLast_append_getLast _).symm⟩
  obtain ⟨r, u0, u2⟩ := last
  subst hsplit
  simp only [List.length_append, List.length_singleton] at hk hcap
  have hkl : init.length = (Std.Usize.wrapping_sub k 1#usize).val := by
    rw [Fold.sub_val _ _ (by simp; omega)]; simp; omega
  have hv' : tape v (foldTape init ++ ([.sample r, .poly u0 u2] ++ rest)) := by
    simpa [foldTape, List.flatMap_append, List.append_assoc] using hv
  obtain ⟨rs, self1, v1, hfold, hv1, ers, eris1, elev1, eoods1, hrel1, hn1⟩ :=
    fold_rounds_eq inst encode const index tape h ht self st hrel v (Std.Usize.wrapping_sub k 1#usize) init _ hkl
      hv' (by omega)
  obtain ⟨v2, hsample, hv2⟩ := ht.sample v1 r (.poly u0 u2 :: rest) (by simpa using hv1)
  obtain ⟨t, het, et⟩ := quad_eval inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst inst
    encode const h self1.quad v2 r (foldModel encode init st).claim hrel1.linear
  have hrsl : rs.val.length = init.length := by rw [ers]; simp
  obtain ⟨ris1, hpris, eris1'⟩ := push_ok self1.ris r (by rw [eris1, List.length_append, hrsl]; omega)
  have hfc : whir.verify.WhirReplay.fold_challenge inst self1 v1 =
      .ok (r, { self1 with t_r := t, ris := ris1 }, v2) := by
    simp [whir.verify.WhirReplay.fold_challenge, hsample, het, hpris]
  obtain ⟨rs1, hpush, ers1⟩ := push_ok rs r (by rw [hrsl]; omega)
  obtain ⟨q, v3, hrecv, hqc, hqa, hqb, hv3⟩ := recv_eq inst encode const tape h ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v2 t u0 u2 rest hv2
  have hfm : foldModel encode (init ++ [(r, u0, u2)]) st =
      foldScalar (foldModel encode init st) (encode r) ⟨encode u0, encode u2⟩ := by
    simp [foldModel, List.foldl_append]
  refine ⟨rs, self1, v1, r, { self1 with t_r := t, ris := ris1 }, v2, rs1, q, v3, hfold, hfc, hpush, hrecv, hv3,
    by rw [ers1, ers]; simp, by simp only; rw [eris1', eris1, ers1]; simp, elev1, eoods1, ?_, ?_⟩
  · rw [hfm]
    refine ⟨by rw [et, hrel1.message]; rfl, by simp only [foldScalar, hqc, hqa],
      by rw [hqb, hqa, et, hrel1.message]; rfl, ?_, ?_, ?_⟩
    · simp only [eris1', foldScalar, SourceState.step, ← hrel1.ris]; simp
    · simpa [foldScalar, SourceState.step] using hrel1.oods
    · simpa [foldScalar, SourceState.step] using hrel1.levels
  · rw [foldModel_n]; simp; omega

set_option maxHeartbeats 400000 in
/-- With an accepted lane count, `verify` checks the configuration, replays level 0 (the lane
fold, the reveal branch not taken without padding), then the level loop, and returns `Ok`
exactly when the model's final terminal check holds after its checked level replay. -/
theorem replay_eq {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : whir.config.Config) (c : Protocol.Config) (log_n : Usize) (hcfg : ConfigRel config c log_n)
    (s : Script E Q R K) (n_lanes : Usize) (hch : (s.chal encode).valid c = true)
    (hS : ScriptShape index c s n_lanes.val) (hgs : GrindShape config s) (target : E) (root : R) (v : V)
    (rest : List (Event E Q R K))
    (hroot : ∀ (hl : 0 < s.levels.length), (s.levels[0]'hl).root = root)
    (hv : tape v (s.tape ++ rest)) (hl0 : n_lanes.val ≠ 0) (hlm : n_lanes.val ≤ 2 ^ config.initial_k.val) :
    ∃ sL r v', Protocol.runChecked (verifyLevel c (s.chal encode) (s.prf encode encodeK ofLimbs)) c.folds.size 0
        ⟨c.logN, encode target, (s.prf encode encodeK ofLimbs).initial, ⟨[], []⟩⟩ = .ok sL ∧
      whir.verify.verify inst W v config log_n n_lanes target root weight_at = .ok (r, v') ∧
      (r = .Ok () ↔ (closeTail (s.chal encode) (s.prf encode encodeK ofLimbs) sL).claim =
        sourceTerminal (callerAt (rotatePoint c.folds[0]! (sL.source.ris ++ (s.chal encode).tail.toList).toArray))
          sL.source.saved sL.source.ris (s.chal encode).tail.toList (s.prf encode encodeK ofLimbs).residual) := by
  have hL := hcfg.folds_size
  have hcv := WHIRNativeGuards.challenges_config c _ hch
  obtain ⟨hrl, hqlen, holen⟩ := hcfg.lengths hcv
  have hgrl := hcfg.lengths' hcv
  have hsl := hS.len
  have hlog := hcfg.log64
  have hlogN := hcfg.logN
  have hfsz := folds_size_le c hcv
  have hmax : 64 < Usize.max := by scalar_tac
  have hhdr := WHIRNativeGuards.config_header c hcv
  have h0L : 0 < c.folds.size := by omega
  have hjl0 : 0 < s.levels.length := by omega
  obtain ⟨hfl0, hol0, hoz0, qsA, hqA, eqA, hql0⟩ := level_facts encode index c s n_lanes.val hch hS 0 h0L
  have hcl0 := WHIRNativeGuards.config_level c hcv 0 h0L
  have hcl1 := WHIRNativeGuards.config_level c hcv 1 (by omega)
  have hb0 : WHIRNativeGuards.before c 0 = c.logN := by simp [WHIRNativeGuards.before]
  have hstep0 := WHIRNativeGuards.before_step c 0 h0L
  have hb1 : WHIRNativeGuards.before c 1 = CausalGame.remaining c 0 := rfl
  have hf0 := hcfg.fold0
  have hk1 : c.folds[1]! = (config.level_ks.val[0]'(by omega)).val := hcfg.foldk 0 (by omega)
  obtain ⟨root0, hroot0, hr1⟩ : ∃ r, (s.levels[0]'hjl0).head = .inl r ∧ (s.levels[1]'(by omega)).root = r :=
    ⟨_, hS.roots 0 (by omega), rfl⟩
  have hrows0 := hS.rows 0 hjl0
  have hbase := hS.base hjl0
  have hdrop0 : s.levels = (s.levels[0]'hjl0) :: s.levels.drop 1 := by
    rw [← List.drop_eq_getElem_cons hjl0]; simp
  have hoodc : CausalGame.oodCount c 0 = (config.ood_samples.val[1]'(by omega)).val := by
    simp only [CausalGame.oodCount, if_pos (show 0 + 1 < c.folds.size by omega)]; exact hcfg.ood 1 (by omega)
  have hsmall := hS.small
  rw [hdrop0] at hsmall
  simp only [List.map_cons, List.sum_cons] at hsmall
  set l0 := s.levels[0]'hjl0 with hl0def
  have hik : config.initial_k.val < 64 := by have := hcl0.2.1; rw [hb0] at this; omega
  have hshl := shl_one_val hw config.initial_k hik
  have hikl : config.initial_k.val < c.logN := by have := hcl0.2.1; rw [hb0, hf0] at this; exact this
  have hz : ¬ (n_lanes = 0#usize) := by intro he; rw [he] at hl0; simp at hl0
  have hgt : ¬ ((Std.Usize.wrapping_shl 1#usize config.initial_k).val < n_lanes.val) := by
    rw [hshl]; omega
  have hcheck := check_config_shape_ok hcfg hw hcv
  have hpad : config.padding = 0#usize := UScalar.eq_of_val_eq (by simpa using hcfg.padding)
  have hv' : tape v (.poly s.initial.1 s.initial.2 :: (foldTape l0.folds ++
      (headTape l0.head ++ (oodTape l0.oods ++ (batchTape l0 ++
        ((s.levels.drop 1).flatMap levelTape ++ (tailTape s.tail s.tailMsgs ++ rest))))))) := by
    have e : s.tape ++ rest = .poly s.initial.1 s.initial.2 :: (foldTape l0.folds ++
        (headTape l0.head ++ (oodTape l0.oods ++ (batchTape l0 ++
          ((s.levels.drop 1).flatMap levelTape ++ (tailTape s.tail s.tailMsgs ++ rest)))))) := by
      rw [Script.tape]
      conv_lhs => rw [hdrop0]
      simp [levelTape, List.append_assoc]
    rw [← e]; exact hv
  obtain ⟨q, v1, hrecv, hqc, hqa, hqb, hv1⟩ := recv_eq inst encode const tape h ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v target s.initial.1 s.initial.2 _ hv'
  obtain ⟨val1, hcs, hval1⟩ := checked_sub_some log_n config.initial_k (by
    have := hcl0.2.1; rw [hb0, hf0, hlogN] at this; omega)
  set init : State := ⟨c.logN, encode target, (s.prf encode encodeK ofLimbs).initial, ⟨[], []⟩⟩ with hinit
  let w0 : whir.verify.WhirReplay V R K Q E :=
    whir.verify.WhirReplay.mk target q (alloc.vec.Vec.new E) (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)
  have hrel0 : Query.StateRel encode index w0 init := by
    refine ⟨rfl, ?_, ?_, by simp [w0, init, alloc.vec.Vec.new], by simp [w0, init, alloc.vec.Vec.new],
      by simp [w0, init, alloc.vec.Vec.new]⟩
    · simp [w0, init, Script.prf, hqc, hqa]
    · simp only [w0, init]; rw [hqb, hqa]
  obtain ⟨rs, self1, v2a, t1, w1, v2b, rs1, q1, v2, hfold, hfc, hpush, hrecv1, hv2, ers, eris1, elev1, eoods1,
      hrel1, hn1⟩ :=
    lane_fold_eq inst encode const index tape h ht w0 init hrel0 v1 config.initial_k l0.folds _
      (by rw [hfl0, hf0]) (by rw [← hf0]; exact hcl0.1) hv1 (by simp [w0, alloc.vec.Vec.new, hfl0, hf0]; omega)
  have hv2' : tape v2 (.root root0 :: (oodTape l0.oods ++ (batchTape l0 ++
      ((s.levels.drop 1).flatMap levelTape ++ (tailTape s.tail s.tailMsgs ++ rest))))) := by
    rw [hroot0] at hv2; exact hv2
  obtain ⟨v3, hnroot, hv3⟩ := ht.root v2 root0 _ hv2'
  set cnt := config.ood_samples.val[1]'(by omega) with hcnt
  have hidxo : Slice.index_usize (alloc.vec.Vec.deref config.ood_samples) 1#usize = .ok cnt := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; simp; omega)]
    simp [alloc.vec.Vec.deref, hcnt]
  have hrem0 : CausalGame.remaining c 0 = val1.val := by
    rw [← hstep0, hb0, hf0, hval1, hlogN]
  obtain ⟨oodsV, v4, hrep, hv4, eoods⟩ := replay_all_eq inst encode const tape h ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v3 cnt val1 l0.oods _ (by rw [hol0, hoodc])
    (fun d hd => by rw [hoz0 d hd, hrem0]) hv3
  set rate0 := config.log_inv_rates.val[0]'(by omega) with hrate0
  have hidxr : Slice.index_usize (alloc.vec.Vec.deref config.log_inv_rates) 0#usize = .ok rate0 := by
    rw [slice_index _ _ (by simp only [alloc.vec.Vec.deref, Slice.from_val]; simp; omega)]
    simp [alloc.vec.Vec.deref, hrate0]
  obtain ⟨ph, hph, hphc, hphg, hphd⟩ : ∃ ph, whir.verify.WhirReplay.phase inst config 0#usize
      (Std.Usize.wrapping_add val1 rate0) = .ok ph ∧ ph.count = config.queries.val[0]'(by omega) ∧
      ph.grinding = UScalar.cast .U32 (config.grinding_bits.val[0]'(by omega)) ∧
      ph.depth = Std.Usize.wrapping_add val1 rate0 :=
    ⟨_, phase_eq inst config 0#usize (Std.Usize.wrapping_add val1 rate0) (by simp; omega) (by simp; omega)
      (hcfg.grinding _ (List.getElem_mem _)), rfl, rfl, rfl⟩
  have hdepth0 : ph.depth.val = l0.depth := by
    have hdep0 : l0.depth = CausalGame.remaining c 0 + c.rates[0]! := hS.depth 0 hjl0
    have hr0 : c.rates[0]! = rate0.val := hcfg.rate 0 (by omega)
    rw [hphd, add_val_lt _ _ (by rw [← hrem0, ← hr0]; exact hcl0.2.2.2.2), hdep0, hrem0, hr0]
  have hgv0 : ph.grinding.val = l0.bits := by
    rw [hphg, cast_u32_val _ (hcfg.grinding _ (List.getElem_mem _))]; exact (hgs 0 hjl0 (by omega)).symm
  obtain ⟨b, v5, hbq, hv5, ebq, ebl, ebw⟩ := begin_query_eq inst encode const tape h ht v4 ph l0.queries l0.lambda _
    (by rw [hphc, hql0, hcfg.query 0 (by omega)]) (by rw [hgv0, hdepth0]; exact hv4)
  have hv5' : tape v5 (.rows root ph.depth.val (alloc.vec.Vec.deref b.queries).val n_lanes.val
      (Std.Usize.wrapping_shl 1#usize config.initial_k).val l0.rows :: .poly l0.intro.1 l0.intro.2 ::
      ((s.levels.drop 1).flatMap levelTape ++ (tailTape s.tail s.tailMsgs ++ rest))) := by
    have hrw0 : l0.rowWords = n_lanes.val := (hS.baseWords hjl0).1
    have hlw0 : l0.leafWords = 2 ^ c.folds[0]! := (hS.baseWords hjl0).2
    have hroot0' : l0.root = root := hroot hjl0
    rw [hdepth0, ← hroot0', hshl, ← hf0, ← hlw0, ← hrw0,
      show (alloc.vec.Vec.deref b.queries).val = l0.queries by simp [alloc.vec.Vec.deref, ebq]]
    exact hv5
  obtain ⟨wR, v6, hopen, ewR, hv6⟩ := ht.rows v5 root ph.depth (alloc.vec.Vec.deref b.queries) n_lanes
    (Std.Usize.wrapping_shl 1#usize config.initial_k) l0.rows _ hv5'
  have hlenR : wR.val.length = l0.rows.length := by simpa using congrArg List.length ewR
  obtain ⟨rows1, hloop0, erows1⟩ := verify_loop3_eq l0.rows _ 0#usize wR rfl (by simp) (by simpa using ewR)
  have hlen1 : rows1.val.length = l0.rows.length := by simpa using congrArg List.length erows1
  have hqpos : 0 < c.queries[0]! := hcl0.2.2.2.1
  have hne1 : rows1.val ≠ [] := by
    intro hnil; rw [hnil] at hlen1; simp only [List.length_nil] at hlen1; omega
  have hw1 : ∀ r ∈ rows1.val, r.val.length = n_lanes.val := by
    intro r hr'
    have hmem : r.val ∈ l0.rows.map List.reverse := by rw [← erows1]; exact List.mem_map_of_mem hr'
    obtain ⟨wd, hwd, hwe⟩ := List.mem_map.mp hmem
    rw [← hwe, List.length_reverse, hbase wd hwd]
  obtain ⟨t, hsum, esum⟩ := Query.base_enforced_eq inst.coremarkerCopyInst1 inst encode const encodeK ofLimbs index h hr
    v6 rows1 (alloc.vec.Vec.deref rs1) (alloc.vec.Vec.deref b.weights) (alloc.vec.Vec.deref b.queries) n_lanes.val
    hne1 hw1 (by simp [alloc.vec.Vec.deref, ers, hfl0, hf0]; omega)
    (by simp [alloc.vec.Vec.deref, ers, hfl0, hf0]; omega) (by
      have := congrArg List.length ebw
      simp only [List.length_map, Array.length_toList, BatchingRefinement.size_powers] at this
      simp [alloc.vec.Vec.deref, this, hlen1, hrows0])
    (by simp [alloc.vec.Vec.deref, ebq, hlen1, hrows0])
  obtain ⟨intro, v7, hrecv2, hic, hia, hib, hv7⟩ := recv_eq inst encode const tape h ht
    inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst v6 t l0.intro.1 l0.intro.2 _ hv6
  have hoodsI : ∀ o ∈ oodsV.val, encode o.intro.b = encode o.y + encode o.intro.a := by
    intro o ho
    obtain ⟨d, _, hod⟩ := forall₂_mem eoods o ho
    obtain ⟨_, hy, _, ha, hb⟩ := hod
    rw [hb, hy, ha]
  obtain ⟨w2, hfin, hris2, hrel2⟩ := Query.finish_query_eq inst encode const index h { w1 with quad := q1 }
    (foldModel encode l0.folds init) hrel1 v6 v6 v7 b oodsV val1 t intro (ht.end_scope v6) hrecv2
    (by rw [hib, hia]) hoodsI (by rw [ebw, ebq, ebl])
    (by simp only; rw [eoods1, eoods.length_eq]; simp [w0, alloc.vec.Vec.new]; omega)
    (by simp only; rw [elev1]; simp [w0, alloc.vec.Vec.new]; omega)
  have hz0 : (0#usize : Usize).val = 0 := by simp
  obtain ⟨o', horacle, ho1, hod1, how1⟩ : ∃ o' : whir.verify.Oracle R,
      whir.verify.WhirReplay.oracle inst config root0 0#usize val1 = .ok (.Ok o') ∧ o'.root = root0 ∧
      (Std.Usize.wrapping_add o'.log_msg_cols o'.log_inv_rate).val = CausalGame.remaining c 1 + c.rates[1]! ∧
      (Std.Usize.wrapping_shl 3#usize o'.log_num_interleaved).val = 3 * 2 ^ c.folds[1]! := by
    obtain ⟨o', horacle, ho1, ho2, ho3, ho4⟩ := oracle_eq inst config root0 0#usize val1 (by rw [hz0]; omega)
      (by simp only [hz0]; rw [← hk1]; have := hcl1.2.1; rw [hb1, hrem0] at this; omega)
      (by rw [hz0]; omega)
    obtain ⟨hod1, how1⟩ := oracle_shape hw hcfg hcv o' 0 (by omega) (by simp only [ho2, hk1, hz0, Nat.zero_add])
      (by simp only [ho3, hk1, hz0, hrem0, Nat.zero_add])
      (by simp only [ho4, hcfg.rate 1 (by omega), hz0, Nat.zero_add])
    exact ⟨o', horacle, ho1, hod1, how1⟩
  -- the model's level 0
  have hrunA := script_level_any encode encodeK ofLimbs index c s n_lanes.val hch hS init init 0 h0L rfl
    (by simp [init, hb0])
  dsimp only at hrunA
  simp only [BEq.rfl] at hrunA
  set st0 := queryBatch (foldBlock (l0.chal encode) (l0.prf encode encodeK ofLimbs true) init).n 0 (l0.chal encode)
    (l0.prf encode encodeK ofLimbs true) (l0.queries.map index).toArray
    (oodBatch (l0.chal encode) (l0.prf encode encodeK ofLimbs true)
      (foldBlock (l0.chal encode) (l0.prf encode encodeK ofLimbs true) init)) with hst0
  have hrelS : Query.StateRel encode index w2 st0 := by
    rw [hst0, ← base_model_eq encode encodeK ofLimbs index l0 init b t intro oodsV.val ebq ebl (by rw [ebw]) eoods
      (by
        rw [esum]
        have : rows1.val.map (fun r => (r.val.map fun k => Concrete.E.ofK (encodeK k)).toArray) =
            (l0.rows.map List.reverse).map fun r => (r.map fun k => Concrete.E.ofK (encodeK k)).toArray := by
          rw [← erows1]; simp
        rw [this]; simp [alloc.vec.Vec.deref, ers])
      hic hia val1.val (by rw [hn1, hval1, ← hlogN])]
    exact hrel2
  have hfitsI : ModelFits init := by intro sv hsv; simp [init] at hsv
  obtain ⟨hfits0, hn0, hco0, hcl0'⟩ := level_state_facts encode encodeK ofLimbs l0 true init 0
    (l0.queries.map index).toArray hfitsI (by rw [hfl0]; simp only [init]; have := hcl0.2.1; omega)
    (by simp only [init]; omega) (fun o ho => by rw [hoz0 o ho, ← hstep0, hb0, hfl0])
  have hoodlen : w2.oods.val.length = l0.oods.length := by
    rw [hrelS.oods.length_eq, hco0]; simp [init]
  have hlevlen : w2.levels.val.length = 1 := by
    rw [hrelS.levels.length_eq, hcl0']; simp [init]
  obtain ⟨sL, r, v', hL', hloop, hiff⟩ := verify_loop4_eq inst encode const encodeK ofLimbs index tape hw h hr hn
    ht hclone hens W weight_at callerAt hcall config c log_n hcfg s n_lanes.val hch hS hgs init rest
    (c.folds.size - 2)
    { start := 0#usize, «end» := alloc.vec.Vec.len config.level_ks } v7 w2 val1 o' st0 (by simp) (by simp; omega)
    rfl (by simpa using hrunA) hrelS hfits0 (by rw [hn0]; simp only [init]; rw [hfl0, hf0, hval1, hlogN])
    (by simp; omega) (by rw [hris2]; simp only; rw [eris1, ers]; simp [w0, alloc.vec.Vec.new, hfl0, hf0]; omega)
    (by rw [hz0, Nat.zero_add]; omega) (by simp [hlevlen])
    (fun _ => by simp only [hz0, Nat.zero_add, ho1, hr1])
    (by simp only [hz0, Nat.zero_add]; exact hod1)
    (by simp only [hz0, Nat.zero_add]; exact how1)
    (by simpa using hv7)
  refine ⟨sL, r, v', hL', ?_, hiff⟩
  simp only [w0] at hfold
  simp [whir.verify.verify, hcheck, whir.config.Config.impl.initial_k, lift, hz, hgt, hrecv,
    core.result.Result.Insts.CoreOpsTry.branch, hcs, core.option.Option.ok_or_some, hfold, hfc, hpush,
    whir.config.Config.impl.padding, hpad, hrecv1, hnroot,
    whir.config.Config.impl.ood_samples, hidxo, hrep, whir.config.Config.impl.log_inv_rates, hidxr, hph, hbq,
    hopen, hloop0, core.option.Option.as_ref, hsum, hfin, horacle, whir.config.Config.level_steps, hloop]

/-- The composed replay theorem. For an opening verifier whose transcript answers the
script's reads in order, the generated `verify` returns `Ok` exactly when the model's
`nativeVerify` accepts the script's challenges and opening with the same lane count,
initial claim and caller weight. -/
theorem verify_eq {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel inst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    (ht : Transcript inst encode tape)
    (hclone : ∀ x, inst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x)
    (hens : EnsureModel inst encode) (W : whir.verify.WeightAt T1 E V R K Q) (weight_at : T1)
    (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : whir.config.Config) (c : Protocol.Config) (log_n : Usize) (hcfg : ConfigRel config c log_n)
    (s : Script E Q R K) (n_lanes : Usize) (hch : (s.chal encode).valid c = true)
    (hS : ScriptShape index c s n_lanes.val) (hgs : GrindShape config s) (target : E) (root : R) (v : V)
    (rest : List (Event E Q R K))
    (hroot : ∀ (hl : 0 < s.levels.length), (s.levels[0]'hl).root = root)
    (hv : tape v (s.tape ++ rest)) :
    ∃ r v', whir.verify.verify inst W v config log_n n_lanes target root weight_at = .ok (r, v') ∧
      (r = .Ok () ↔ nativeVerify c (s.chal encode) n_lanes.val (encode target) callerAt
        (s.prf encode encodeK ofLimbs) = .ok ()) := by
  have hcv := WHIRNativeGuards.challenges_config c _ hch
  have hcheck := check_config_shape_ok hcfg hw hcv
  have hf0 := hcfg.fold0
  by_cases hlanes : n_lanes.val = 0 ∨ 2 ^ config.initial_k.val < n_lanes.val
  · have hnat := nativeVerify_lanes c (s.chal encode) n_lanes.val (encode target) callerAt
      (s.prf encode encodeK ofLimbs) (by rw [hf0]; exact hlanes)
    have hik : config.initial_k.val < 64 := by
      have h0 := WHIRNativeGuards.config_level c hcv 0 (by have := hcfg.folds_size; omega)
      have hb0 : WHIRNativeGuards.before c 0 = c.logN := by simp [WHIRNativeGuards.before]
      have := h0.2.1; rw [hb0, hf0, hcfg.logN] at this; have := hcfg.log64; omega
    have hshl := shl_one_val hw config.initial_k hik
    rcases hlanes with h0 | hgt
    · have hz : n_lanes = 0#usize := UScalar.eq_of_val_eq (by simpa using h0)
      refine ⟨.Err (whir.verify.WhirError.LaneCount n_lanes (Std.Usize.wrapping_shl 1#usize config.initial_k)), v,
        ?_, ?_⟩
      · simp [whir.verify.verify, hcheck, core.result.Result.Insts.CoreOpsTry.branch,
          whir.config.Config.impl.initial_k, lift, hz]
      · simp only [reduceCtorEq, false_iff]; exact hnat
    · have hz : ¬ n_lanes = 0#usize := by intro he; rw [he] at hgt; simp at hgt
      have hgt' : (Std.Usize.wrapping_shl 1#usize config.initial_k).val < n_lanes.val := by rw [hshl]; exact hgt
      refine ⟨.Err (whir.verify.WhirError.LaneCount n_lanes (Std.Usize.wrapping_shl 1#usize config.initial_k)), v,
        ?_, ?_⟩
      · simp [whir.verify.verify, hcheck, core.result.Result.Insts.CoreOpsTry.branch,
          whir.config.Config.impl.initial_k, lift, hz, hgt']
      · simp only [reduceCtorEq, false_iff]; exact hnat
  · obtain ⟨hl0, hlm⟩ : n_lanes.val ≠ 0 ∧ n_lanes.val ≤ 2 ^ config.initial_k.val := by omega
    obtain ⟨sL, r, v', hrun, hrunEq, hiff⟩ := replay_eq inst encode const encodeK ofLimbs index tape hw h hr hn ht
      hclone
      hens W weight_at callerAt hcall config c log_n hcfg s n_lanes hch hS hgs target root v rest hroot hv hl0 hlm
    refine ⟨r, v', hrunEq, ?_⟩
    rw [hiff, nativeVerify_ok_iff c (s.chal encode) n_lanes.val (encode target) callerAt
      (s.prf encode encodeK ofLimbs) sL hch hl0 (by rw [hf0]; exact hlm)
      (by simp [Script.prf, hS.len]) (by simp [Script.prf, Script.chal, hS.tail]) hrun]

end Loop
end WhirAeneas.Replay
