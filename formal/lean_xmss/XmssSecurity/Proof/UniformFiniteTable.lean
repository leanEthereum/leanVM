module

public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import XmssSecurity.Proof.EvalDistEq

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

def finHeadTailEquiv (α : Type) (count : Nat) :
    (α × (Fin count → α)) ≃ (Fin (count + 1) → α) where
  toFun pair := Fin.cases pair.1 pair.2
  invFun values := (values 0, fun index => values index.succ)
  left_inv pair := by
    apply Prod.ext
    · simp
    · funext index
      simp
  right_inv values := by
    funext index
    cases index using Fin.cases <;> simp

theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] :
    (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) =ᵈ
    ($ᵗ (α × β)) := by
  rw [SampleableType.uniformSample_prod_eq_bind]

noncomputable def uniformSnocList
    (α : Type) [SampleableType α] : Nat → ProbComp (List α)
  | 0 => pure []
  | count + 1 => do
      let prior ← uniformSnocList α count
      let next ← $ᵗ α
      pure (prior ++ [next])

theorem uniformSnocList_append
    (α : Type) [SampleableType α] (firstLength secondLength : Nat) :
    (do
      let first ← uniformSnocList α firstLength
      let second ← uniformSnocList α secondLength
      pure (first ++ second)) =
    uniformSnocList α (firstLength + secondLength) := by
  induction secondLength with
  | zero => simp [uniformSnocList]
  | succ secondLength ih =>
      simp [uniformSnocList, bind_assoc, ← ih, List.append_assoc]

theorem evalDist_uniformSnocList_eq_reverse_drawList
    (α : Type) [SampleableType α] (count : Nat) :
    (uniformSnocList α count) =ᵈ
      (List.reverse <$>
        OracleComp.drawList ($ᵗ α) count) := by
  induction count with
  | zero => simp [uniformSnocList, OracleComp.drawList]
  | succ count ih =>
      rw [uniformSnocList]
      calc
        _ =ᵈ ((List.reverse <$>
              OracleComp.drawList ($ᵗ α) count) >>= fun prior =>
            ($ᵗ α) >>= fun next =>
            pure (prior ++ [next])) := by
          exact ih.bind_left _
        _ =ᵈ (OracleComp.drawList ($ᵗ α) count >>= fun prior =>
            ($ᵗ α) >>= fun next =>
            pure (prior.reverse ++ [next])) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ =ᵈ (($ᵗ α) >>= fun next =>
            OracleComp.drawList ($ᵗ α) count >>= fun prior =>
            pure (prior.reverse ++ [next])) :=
          OracleComp.EvalDistEq.bind_bind_swap
            (OracleComp.drawList ($ᵗ α) count) ($ᵗ α)
              (fun prior next => pure (prior.reverse ++ [next]))
        _ =ᵈ (List.reverse <$>
            OracleComp.drawList ($ᵗ α) (count + 1)) := by
          simp [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc]

def finInitLastEquiv (α : Type) (count : Nat) :
    ((Fin count → α) × α) ≃ (Fin (count + 1) → α) where
  toFun pair := Fin.lastCases pair.2 pair.1
  invFun values := (fun index => values index.castSucc, values (Fin.last count))
  left_inv pair := by
    apply Prod.ext
    · funext index
      simp
    · simp
  right_inv values := by
    funext index
    cases index using Fin.lastCases <;> simp

set_option maxRecDepth 100000 in
theorem evalDist_uniformSnocList_eq_uniformFunction
    (α : Type) [Fintype α] [SampleableType α] (count : Nat) :
    (uniformSnocList α count) =ᵈ
      (List.ofFn <$> ($ᵗ (Fin count → α))) := by
  induction count with
  | zero =>
      rw [uniformSnocList]
      symm
      rw [map_eq_bind_pure_comp]
      calc
        (($ᵗ (Fin 0 → α)) >>= fun values =>
            pure (List.ofFn values)) =ᵈ
            (($ᵗ (Fin 0 → α)) >>= fun _values => pure []) := by
          refine EvalDistEq.bind_right _ fun values => ?_
          have hnil : List.ofFn values = [] :=
            List.eq_nil_of_length_eq_zero (by simp)
          rw [hnil]
        _ =ᵈ (pure [] : ProbComp (List α)) :=
          OracleComp.EvalDistEq.bind_const ($ᵗ (Fin 0 → α)) (pure [])
  | succ count ih =>
      rw [uniformSnocList]
      calc
        _ =ᵈ ((List.ofFn <$> ($ᵗ (Fin count → α))) >>= fun prior =>
            ($ᵗ α) >>= fun next => pure (prior ++ [next])) := by
          exact ih.bind_left _
        _ =ᵈ (List.ofFn <$> (finInitLastEquiv α count <$> (do
              let prior ← $ᵗ (Fin count → α)
              let next ← $ᵗ α
              pure (prior, next)))) := by
          refine EvalDistEq.of_eq ?_
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]
          apply bind_congr
          intro prior
          apply bind_congr
          intro next
          congr 1
          rw [List.ofFn_succ']
          simp [finInitLastEquiv]
        _ =ᵈ (List.ofFn <$> (finInitLastEquiv α count <$>
              ($ᵗ ((Fin count → α) × α)))) :=
          (evalDist_independent_uniform_pair.map _).map _
        _ =ᵈ (List.ofFn <$> ($ᵗ (Fin (count + 1) → α))) :=
          (SampleableType.map_uniformSample_evalDistEq_of_bijective
            (finInitLastEquiv α count).bijective).map _

set_option maxRecDepth 100000 in
theorem evalDist_drawList_uniform_eq_uniformFunction
    (α : Type) [Fintype α] [SampleableType α] (count : Nat) :
    (OracleComp.drawList ($ᵗ α) count) =ᵈ
      (List.ofFn <$> ($ᵗ (Fin count → α))) := by
  induction count with
  | zero =>
      rw [OracleComp.drawList]
      symm
      rw [map_eq_bind_pure_comp]
      calc
        (($ᵗ (Fin 0 → α)) >>= fun values =>
            pure (List.ofFn values)) =ᵈ
            (($ᵗ (Fin 0 → α)) >>= fun _values => pure []) := by
          refine EvalDistEq.bind_right _ fun values => ?_
          have hnil : List.ofFn values = [] :=
            List.eq_nil_of_length_eq_zero (by simp)
          rw [hnil]
        _ =ᵈ (pure [] : ProbComp (List α)) :=
          OracleComp.EvalDistEq.bind_const ($ᵗ (Fin 0 → α)) (pure [])
  | succ count ih =>
      rw [OracleComp.drawList]
      calc
        _ =ᵈ (($ᵗ α) >>= fun first =>
              (List.ofFn <$> ($ᵗ (Fin count → α))) >>= fun rest =>
              pure (first :: rest)) := by
          apply EvalDistEq.bind_right
          intro first
          exact ih.bind_left _
        _ =ᵈ (List.ofFn <$> (finHeadTailEquiv α count <$> (do
              let first ← $ᵗ α
              let rest ← $ᵗ (Fin count → α)
              pure (first, rest)))) := by
          simp [finHeadTailEquiv, map_eq_bind_pure_comp, bind_assoc]
        _ =ᵈ (List.ofFn <$> (finHeadTailEquiv α count <$>
              ($ᵗ (α × (Fin count → α))))) :=
          (evalDist_independent_uniform_pair.map _).map _
        _ =ᵈ (List.ofFn <$> ($ᵗ (Fin (count + 1) → α))) :=
          (SampleableType.map_uniformSample_evalDistEq_of_bijective
            (finHeadTailEquiv α count).bijective).map _

noncomputable def finiteTableTapeEquiv
    {ι α : Type} [DecidableEq ι] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order) :
    (ι → α) ≃ (Fin order.length → α) :=
  (Equiv.piCongrLeft (fun _ : ι => α)
    (hnodup.getEquivOfForallMemList order hcover)).symm

theorem listOfFn_finiteTableTapeEquiv
    {ι α : Type} [DecidableEq ι] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order)
    (table : ι → α) :
    List.ofFn (finiteTableTapeEquiv order hnodup hcover table) =
      order.map table := by
  rw [← List.ofFn_get (order.map table)]
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp [finiteTableTapeEquiv]

noncomputable def finiteTableOfTape
    {ι α : Type} [DecidableEq ι] [Inhabited α] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order)
    (targets : List α) : ι → α :=
  if hlength : targets.length = order.length then
    (finiteTableTapeEquiv order hnodup hcover).symm fun index =>
      targets.get (Fin.cast hlength.symm index)
  else
    default

@[simp]
theorem finiteTableOfTape_map
    {ι α : Type} [DecidableEq ι] [Inhabited α] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order)
    (table : ι → α) :
    finiteTableOfTape order hnodup hcover (order.map table) = table := by
  unfold finiteTableOfTape
  split
  · rename_i hlength
    apply (finiteTableTapeEquiv order hnodup hcover).injective
    rw [(finiteTableTapeEquiv order hnodup hcover).apply_symm_apply]
    funext index
    simp [finiteTableTapeEquiv]
  · rename_i hlength
    exact (hlength (by simp)).elim

set_option maxRecDepth 100000 in
theorem evalDist_finiteTableOfTape_drawList_eq_uniform
    {ι α : Type} [DecidableEq ι] [Inhabited α] [Fintype α]
    [SampleableType α] [Fintype ι] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order) :
    (finiteTableOfTape order hnodup hcover <$>
      OracleComp.drawList ($ᵗ α) order.length) =ᵈ ($ᵗ (ι → α)) := by
  have htape : ((fun table : ι → α => order.map table) <$>
      ($ᵗ (ι → α))) =ᵈ
      (OracleComp.drawList ($ᵗ α) order.length) := by
    calc
      _ =ᵈ (List.ofFn <$>
          (finiteTableTapeEquiv order hnodup hcover <$>
            ($ᵗ (ι → α)))) := by
        simp only [Functor.map_map]
        refine EvalDistEq.of_eq ?_
        congr 1
        funext table
        exact (listOfFn_finiteTableTapeEquiv order hnodup hcover table).symm
      _ =ᵈ (List.ofFn <$>
          ($ᵗ (Fin order.length → α))) :=
        (SampleableType.map_uniformSample_evalDistEq_of_bijective
          (finiteTableTapeEquiv order hnodup hcover).bijective).map _
      _ =ᵈ _ := (evalDist_drawList_uniform_eq_uniformFunction α
        order.length).symm
  calc
    _ =ᵈ (finiteTableOfTape order hnodup hcover <$>
        ((fun table : ι → α => order.map table) <$>
          ($ᵗ (ι → α)))) :=
      (htape.symm.map _)
    _ =ᵈ ($ᵗ (ι → α)) := by
      simp [Functor.map_map]

theorem evalDist_finiteTableOfTape_uniformSnoc_eq_uniform
    {ι α : Type} [DecidableEq ι] [Inhabited α] [Fintype α]
    [SampleableType α] [Fintype ι] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order) :
    (finiteTableOfTape order hnodup hcover <$>
      uniformSnocList α order.length) =ᵈ ($ᵗ (ι → α)) := by
  calc
    _ =ᵈ (finiteTableOfTape order hnodup hcover <$>
        OracleComp.drawList ($ᵗ α) order.length) :=
      ((evalDist_uniformSnocList_eq_uniformFunction α order.length).trans
          (evalDist_drawList_uniform_eq_uniformFunction α order.length).symm).map _
    _ =ᵈ _ := evalDist_finiteTableOfTape_drawList_eq_uniform order hnodup hcover

end XmssSecurity
