import Whir.PCSBCSCallerGKRPolynomialBound

/-! Deterministic polynomial source-operation bounds for the concrete bus and
AIR receivers. Literal numeric configuration entries contribute additively to
size; these counters are not CPU timing bounds. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Whir.PCSBCSCallerParserCost
open Concrete WHIRCallerClaims

/-- Unary magnitude of the literal AIR configuration, including list cells. -/
def airLayoutSize (l : AirLayout) : Nat :=
  1+l.tau+l.columns+l.publicColumns+
    (l.fields.map (fun f => 1+f.column+f.width)).sum

private def tableStep (layout : AirLayout) (slices : List E) (c : Nat)
    (state : List E × List E) : Parser (ForInStep (List E × List E)) := do
  let found := fieldOf c layout.fields 0
  tick (found.work+2)
  match found.value with
  | some (f,start) =>
    let combined := combineBits ((slices.drop start).take f.width)
    tick (dropCost start slices+takeCost f.width (slices.drop start)+
      combined.work+appendCost state.2+1)
    pure (.yield (state.1,state.2++[combined.value]))
  | none =>
    tick 1
    match state.1 with
    | [] => do check false; pure (.yield state)
    | x :: xs => do
      tick (appendCost state.2+2)
      pure (.yield (xs,state.2++[x]))

private theorem tableStep_work_le (l : AirLayout) (slices : List E)
    (c : Nat) (state : List E × List E) (tokens : List CallerToken) :
    (tableStep l slices c state tokens).work ≤
      2*state.2.length+3*slices.length*slices.length+20*slices.length+
        5*l.fields.length+20 := by
  have search := fieldOf_work_le c l.fields 0
  unfold tableStep
  rw [tick_bind_work]
  cases found : (fieldOf c l.fields 0).value with
  | some pair =>
    rcases pair with ⟨f,start⟩
    dsimp only []
    rw [tick_bind_work]
    have combined := combineBits_work_le ((slices.drop start).take f.width)
    have short : ((slices.drop start).take f.width).length ≤ slices.length := by
      simp only [List.length_take,List.length_drop]
      omega
    simp only [pure,dropCost,takeCost,appendCost,List.length_drop]
    have h1 := Nat.min_le_right start slices.length
    have h2 := Nat.min_le_right f.width (slices.length-start)
    have square := Nat.mul_self_le_mul_self short
    nlinarith [Nat.sub_le slices.length start]
  | none =>
    dsimp only []
    rw [tick_bind_work]
    cases cursor : state.1 with
    | nil => simp [Bind.bind,check,bind,pure]; omega
    | cons x xs =>
      rw [tick_bind_work]
      simp only [pure,appendCost]
      omega

private theorem tableStep_success (l : AirLayout) (slices : List E)
    (c : Nat) (state : List E × List E) (tokens rest : List CallerToken)
    (step : ForInStep (List E × List E))
    (accepted : (tableStep l slices c state tokens).result = some (step,rest)) :
    ∃ next, step = .yield next ∧ next.2.length = state.2.length+1 := by
  unfold tableStep at accepted
  dsimp only [Bind.bind,bind,tick] at accepted
  cases found : (fieldOf c l.fields 0).value with
  | some pair =>
    rcases pair with ⟨f,start⟩
    simp only [found,bind,tick,pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    exact ⟨_,rfl,by simp⟩
  | none =>
    simp only [found] at accepted
    cases cursor : state.1 with
    | nil => simp [cursor,Bind.bind,bind,check,tick] at accepted
    | cons x xs =>
      simp only [cursor,bind,tick,pure,Option.some.injEq,Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl,rfl⟩
      exact ⟨_,rfl,by simp⟩

private theorem tableLoop_work_le (l : AirLayout) (slices sent : List E)
    (tokens : List CallerToken) :
    (forIn (List.range (l.columns-l.publicColumns)) (sent,[])
      (tableStep l slices) tokens).work ≤
    (l.columns-l.publicColumns) *
      (2*(l.columns-l.publicColumns)+3*slices.length*slices.length+
        20*slices.length+5*l.fields.length+20) := by
  have bounded := forIn_growth_work_le
    (List.range (l.columns-l.publicColumns)) (sent,[]) (tableStep l slices)
    (fun state => state.2.length) 2
    (3*slices.length*slices.length+20*slices.length+5*l.fields.length+20) 1
    (by intro c _ state ts; simpa [Nat.add_assoc] using tableStep_work_le l slices c state ts)
    (by
      intro c _ state ts step rest accepted
      obtain ⟨next,rfl,growth⟩ := tableStep_success l slices c state ts rest step accepted
      simp [iterationState,growth]) tokens
  simpa [List.length_range,Nat.add_assoc] using bounded

private theorem forIn_exact_growth {A B : Type} (xs : List A) (body : A → B → Parser (ForInStep B))
    (size : B → Nat)
    (grows : ∀ x state ts step rest, (body x state ts).result = some (step,rest) →
      ∃ next, step = .yield next ∧ size next = size state+1)
    (initial final : B) (tokens rest : List CallerToken)
    (accepted : (forIn xs initial body tokens).result = some (final,rest)) :
    size final = size initial+xs.length := by
  induction xs generalizing initial tokens with
  | nil =>
    simp only [List.forIn_nil] at accepted
    change some (initial,tokens) = some (final,rest) at accepted
    cases accepted
    simp
  | cons x xs ih =>
    rw [List.forIn_cons] at accepted
    change (bind (body x initial) _ tokens).result = some (final,rest) at accepted
    cases first : (body x initial tokens).result with
    | none => simp [bind,first] at accepted
    | some pair =>
      rcases pair with ⟨step,middle⟩
      obtain ⟨next,rfl,growth⟩ := grows x initial tokens step middle first
      simp only [bind,first] at accepted
      have tail := ih next middle accepted
      simp only [List.length_cons]
      omega

private theorem tableLoop_success (l : AirLayout) (slices sent : List E)
    (tokens rest : List CallerToken) (final : List E × List E)
    (accepted : (forIn (List.range (l.columns-l.publicColumns)) (sent,[])
      (tableStep l slices) tokens).result = some (final,rest)) :
    final.2.length = l.columns-l.publicColumns := by
  have exactLength := forIn_exact_growth
    (List.range (l.columns-l.publicColumns)) (tableStep l slices) (fun state => state.2.length)
    (fun c state ts step tail h => tableStep_success l slices c state ts tail step h)
    (sent,[]) final tokens rest accepted
  simpa using exactLength

private theorem tick_work_le (n : Nat) (tokens : List CallerToken) :
    (tick n tokens).work ≤ n := Nat.le_refl _

private theorem pure_work_le {A : Type} (value : A) (tokens : List CallerToken) :
    ((Pure.pure value : Parser A) tokens).work ≤ 0 := Nat.le_refl _

private theorem tableLoop_work_size (l : AirLayout) (slices sent : List E)
    (tokens : List CallerToken)
    (length : slices.length = (l.fields.map BitField.width).sum) :
    (forIn (List.range (l.columns-l.publicColumns)) (sent,[])
      (tableStep l slices) tokens).work ≤
    (l.columns-l.publicColumns) *
      (2*(l.columns-l.publicColumns)+3*(l.fields.map BitField.width).sum*
        (l.fields.map BitField.width).sum+
        20*(l.fields.map BitField.width).sum+5*l.fields.length+20) := by
  simpa [length] using tableLoop_work_le l slices sent tokens

/-- A literal polynomial, valid for every input, including every rejecting
guard, exhausted cursor, and malformed or truncated scalar stream. -/
def receiveTableWork (l : AirLayout) (p : List E) : Nat :=
  10*p.length+20*l.columns+30*l.fields.length+2*l.fields.length*l.fields.length+
    9*(l.fields.map BitField.width).sum+50+
    l.columns*(2*l.columns+3*(l.fields.map BitField.width).sum*
      (l.fields.map BitField.width).sum+20*(l.fields.map BitField.width).sum+
        5*l.fields.length+20)

private theorem eraseDups_length_le {A : Type} [BEq A] (xs : List A) :
    xs.eraseDups.length ≤ xs.length := by
  have loop (as seen : List A) :
      (List.eraseDupsBy.loop (fun a b => a == b) as seen).length ≤ as.length+seen.length := by
    induction as generalizing seen with
    | nil => simp [List.eraseDupsBy.loop]
    | cons a as ih =>
      simp only [List.eraseDupsBy.loop]
      split
      · have := ih seen; simp only [List.length_cons]; omega
      · have := ih (a::seen); simp only [List.length_cons] at *; omega
  exact loop xs []

syntax "table_cost" : tactic
macro_rules
| `(tactic| table_cost) => `(tactic|
  first
  | exact tick_work_le _ _
  | exact check_work_le _ _
  | exact readScalars_work_le _ _
  | exact pure_work_le _ _
  | exact tableLoop_work_size _ _ _ _ (readScalars_success_length _ _ _ _ (by assumption))
  | (apply bind_work_le
     · table_cost
     · intro value tail parsed; table_cost))

theorem receiveTable_work_le (l : AirLayout) (p : List E) (tokens : List CallerToken) :
    (receiveTable l p tokens).work ≤ receiveTableWork l p := by
  have scans := allCost_le
    (fun f : BitField => decide (f.column < l.columns-l.publicColumns) && decide (f.width ≤ 64))
    (fun f => if f.column < l.columns-l.publicColumns then 3 else 2)
    l.fields 3 (by intro f _; split <;> omega)
  have dups := eraseDupsCost_le 1 (l.fields.map BitField.column) []
  have short := eraseDups_length_le (l.fields.map BitField.column)
  have hn := Nat.sub_le l.columns l.publicColumns
  have loopMono :
      (l.columns-l.publicColumns) *
        (2*(l.columns-l.publicColumns)+3*(l.fields.map BitField.width).sum*
          (l.fields.map BitField.width).sum+20*(l.fields.map BitField.width).sum+
            5*l.fields.length+20) ≤
      l.columns*(2*l.columns+3*(l.fields.map BitField.width).sum*
        (l.fields.map BitField.width).sum+20*(l.fields.map BitField.width).sum+
          5*l.fields.length+20) :=
    Nat.mul_le_mul hn (by omega)
  apply Nat.le_trans
  · unfold receiveTable
    table_cost
  · simp only [receiveTableWork,lengthCost,takeCost,List.length_map,List.length_nil] at *
    split <;> nlinarith [Nat.min_le_right l.tau p.length,
      Nat.sub_le l.columns l.publicColumns,
      Nat.sub_le (l.columns-l.publicColumns) l.fields.length]

private theorem tick_bind_result {A : Type} (n : Nat) (next : Unit → Parser A)
    (tokens : List CallerToken) :
    ((tick n >>= next) tokens).result = (next () tokens).result := rfl

private theorem bind_success {A B : Type} (before : Parser A) (next : A → Parser B)
    (tokens rest : List CallerToken) (output : B)
    (accepted : ((before >>= next) tokens).result = some (output,rest)) :
    ∃ value middle, (before tokens).result = some (value,middle) ∧
      (next value middle).result = some (output,rest) := by
  change (bind before next tokens).result = _ at accepted
  cases first : (before tokens).result with
  | none => simp [bind,first] at accepted
  | some pair =>
    rcases pair with ⟨value,middle⟩
    exact ⟨value,middle,rfl,by simpa [bind,first] using accepted⟩

private theorem check_bind_success {A : Type} (ok : Bool) (next : Unit → Parser A)
    (tokens rest : List CallerToken) (output : A)
    (accepted : ((check ok >>= next) tokens).result = some (output,rest)) :
    ok = true ∧ (next () tokens).result = some (output,rest) := by
  cases ok
  · simp [Bind.bind,check,bind] at accepted
  · exact ⟨rfl,accepted⟩

/-- Actual returned cardinalities; no externally supplied claim-size certificate. -/
theorem receiveTable_success_lengths (l : AirLayout) (p : List E)
    (tokens rest : List CallerToken) (output : TableClaims)
    (accepted : (receiveTable l p tokens).result = some (output,rest)) :
    output.point.length = l.tau ∧
    output.evals.length = l.columns-l.publicColumns ∧
    output.slices.length = (l.fields.map BitField.width).sum := by
  unfold receiveTable at accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨valid,accepted⟩ := check_bind_success _ _ _ _ _ accepted
  have tauBound : l.tau ≤ p.length := by
    simp at valid
    exact valid.2
  simp only [tick_bind_result] at accepted
  obtain ⟨_,accepted⟩ := check_bind_success _ _ _ _ _ accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨_,accepted⟩ := check_bind_success _ _ _ _ _ accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨sent,middle,_,accepted⟩ := bind_success _ _ _ _ _ accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨slices,middle,slicesRead,accepted⟩ := bind_success _ _ _ _ _ accepted
  have slicesLength := readScalars_success_length _ _ _ _ slicesRead
  simp only [tick_bind_result] at accepted
  obtain ⟨final,middle,loopRead,accepted⟩ := bind_success _ _ _ _ _ accepted
  have evalsLength := tableLoop_success l slices sent _ _ final loopRead
  simp only [tick_bind_result] at accepted
  obtain ⟨_,accepted⟩ := check_bind_success _ _ _ _ _ accepted
  simp only [tick_bind_result,pure,Option.some.injEq,Prod.mk.injEq] at accepted
  rcases accepted with ⟨rfl,rfl⟩
  simp only [List.length_take,Nat.min_eq_left tauBound]
  exact ⟨True.intro,evalsLength,slicesLength⟩

private theorem fieldSize_components (fs : List BitField) :
    fs.length ≤ (fs.map (fun f => 1+f.column+f.width)).sum ∧
    (fs.map BitField.width).sum ≤ (fs.map (fun f => 1+f.column+f.width)).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem airLayoutSize_components (l : AirLayout) :
    l.columns ≤ airLayoutSize l ∧ l.tau ≤ airLayoutSize l ∧
    l.fields.length ≤ airLayoutSize l ∧
    (l.fields.map BitField.width).sum ≤ airLayoutSize l := by
  have := fieldSize_components l.fields
  unfold airLayoutSize
  omega

theorem receiveTable_success_caps (l : AirLayout) (p : List E)
    (tokens rest : List CallerToken) (output : TableClaims) (size : Nat)
    (configuration : airLayoutSize l ≤ size)
    (accepted : (receiveTable l p tokens).result = some (output,rest)) :
    output.point.length ≤ size ∧ output.evals.length ≤ size ∧ output.slices.length ≤ size := by
  have lengths := receiveTable_success_lengths l p tokens rest output accepted
  have components := airLayoutSize_components l
  omega

theorem receiveTable_work_polynomial (l : AirLayout) (p : List E)
    (tokens : List CallerToken) (size : Nat)
    (configuration : airLayoutSize l ≤ size) (point : p.length ≤ size) :
    (receiveTable l p tokens).work ≤ 100*(size+1)^3 := by
  have components := airLayoutSize_components l
  have columns : l.columns ≤ size := by omega
  have fields : l.fields.length ≤ size := by omega
  have widths : (l.fields.map BitField.width).sum ≤ size := by omega
  have squares := Nat.mul_self_le_mul_self widths
  have fieldSquares := Nat.mul_self_le_mul_self fields
  have inner :
      2*l.columns+3*(l.fields.map BitField.width).sum*(l.fields.map BitField.width).sum+
        20*(l.fields.map BitField.width).sum+5*l.fields.length+20 ≤
      3*size*size+27*size+20 := by nlinarith
  have loopBound := Nat.mul_le_mul columns inner
  apply (receiveTable_work_le l p tokens).trans
  unfold receiveTableWork
  nlinarith

/-- All literal AIR entries, with a cell charge for the outer list. -/
def airLayoutsSize (layouts : List AirLayout) : Nat :=
  1+(layouts.map (fun l => 1+airLayoutSize l)).sum

private theorem airLayouts_components (layouts : List AirLayout) :
    layouts.length ≤ (layouts.map (fun l => 1+airLayoutSize l)).sum ∧
    (∀ l ∈ layouts, airLayoutSize l ≤ (layouts.map (fun l => 1+airLayoutSize l)).sum) := by
  induction layouts with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,List.mem_cons]
    constructor
    · omega
    · intro next member
      rcases member with rfl | member
      · omega
      · have := ih.2 next member; omega

private theorem foldMax_le (xs : List Nat) (initial cap : Nat)
    (start : initial ≤ cap) (entries : ∀ x ∈ xs, x ≤ cap) :
    xs.foldl max initial ≤ cap := by
  induction xs generalizing initial with
  | nil => exact start
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact max_le start (entries x (by simp))
    · intro y member; exact entries y (by simp [member])

private theorem constraintRounds_work_le (n : Nat) (tokens : List CallerToken) :
    ((List.range n).mapM (fun _ => do
      tick 2
      let _ ← readScalars 3
      drawScalar) tokens).work ≤ 35*n := by
  simpa using mapM_work_le (List.range n) _ 35 (by
    intro i _ ts
    rw [tick_bind_work]
    have h := bind_work_le (readScalars 3) (fun _ => drawScalar) ts 29 4
      (readScalars_work_le 3 ts) (by intro _ tail _; exact drawScalar_work_le tail)
    omega) tokens

private theorem constraintTables_work_le (layouts : List AirLayout) (rounds : List E)
    (tokens : List CallerToken) (size : Nat)
    (configuration : airLayoutsSize layouts ≤ size) (point : rounds.length ≤ size) :
    (layouts.mapM (fun l => do
      tick (2*rounds.length+3)
      receiveTable l rounds.reverse) tokens).work ≤
      (100*(size+1)^3+2*size+3)*layouts.length := by
  apply mapM_work_le
  intro l member ts
  rw [tick_bind_work]
  have entry := (airLayouts_components layouts).2 l member
  have config : airLayoutSize l ≤ size := by
    unfold airLayoutsSize at configuration
    omega
  have work := receiveTable_work_polynomial l rounds.reverse ts size config (by simpa)
  omega

theorem constraintClaims_work_polynomial (layouts : List AirLayout) (p : List E)
    (tokens : List CallerToken) (size : Nat)
    (configuration : airLayoutsSize layouts ≤ size) (point : p.length ≤ size) :
    (constraintClaims layouts p tokens).work ≤
      100*(size+1)^3*size+2*size*size+50*size+20 := by
  have components := airLayouts_components layouts
  have length : layouts.length ≤ size := by unfold airLayoutsSize at configuration; omega
  have maxBound : (layouts.map AirLayout.tau).foldl max 0 ≤ size := by
    apply foldMax_le _ _ _ (Nat.zero_le _)
    intro tau member
    obtain ⟨l,sourceMember,equal⟩ := List.mem_map.mp member
    subst tau
    have entry := components.2 l sourceMember
    have tau := (airLayoutSize_components l).2.1
    unfold airLayoutsSize at configuration
    omega
  have mapBound := Nat.mul_le_mul_left (100*(size+1)^3+2*size+3) length
  unfold constraintClaims
  apply Nat.le_trans
  · apply bind_work_le
    · exact tick_work_le _ _
    · intro _ tail _
      apply bind_work_le
      · exact check_work_le _ _
      · intro _ tail _
        apply bind_work_le
        · exact tick_work_le _ _
        · intro _ tail _
          apply bind_work_le
          · exact constraintRounds_work_le _ _
          · intro rounds tail parsed
            have roundsLength := mapM_success_length _ _ _ _ _ parsed
            apply constraintTables_work_le _ _ _ size configuration
            simp only [List.length_range] at roundsLength
            exact roundsLength.trans_le maxBound
  · unfold lengthCost
    simp only [Nat.add_mul] at mapBound
    nlinarith

/-- Successful constraint traversal returns exactly one table per literal AIR. -/
theorem constraintClaims_success_length (layouts : List AirLayout) (p : List E)
    (tokens rest : List CallerToken) (output : List TableClaims)
    (accepted : (constraintClaims layouts p tokens).result = some (output,rest)) :
    output.length = layouts.length := by
  unfold constraintClaims at accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨_,accepted⟩ := check_bind_success _ _ _ _ _ accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨rounds,middle,_,accepted⟩ := bind_success _ _ _ _ _ accepted
  exact mapM_success_length _ _ _ _ _ accepted

private theorem forIn_success_growth {A B : Type} (xs : List A)
    (body : A → B → Parser (ForInStep B)) (size : B → Nat) (delta : Nat)
    (grows : ∀ x ∈ xs, ∀ state ts step rest, (body x state ts).result = some (step,rest) →
      ∃ next, step = .yield next ∧ size next ≤ size state+delta)
    (initial final : B) (tokens rest : List CallerToken)
    (accepted : (forIn xs initial body tokens).result = some (final,rest)) :
    size final ≤ size initial+delta*xs.length := by
  induction xs generalizing initial tokens with
  | nil =>
    simp only [List.forIn_nil] at accepted
    change some (initial,tokens) = some (final,rest) at accepted
    cases accepted
    simp
  | cons x xs ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨step,middle,first,accepted⟩ := bind_success _ _ _ _ _ accepted
    obtain ⟨next,rfl,growth⟩ := grows x (by simp) initial tokens step middle first
    have tail := ih
      (fun y member st ts outcome tail h => grows y (by simp [member]) st ts outcome tail h)
      next middle accepted
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

private abbrev BusState := List (Nat × Nat) × List ColumnClaim
private def busStateSize (state : BusState) : Nat := state.1.length+state.2.length

private def busCoordStep (point : List E) (block : BusBlock) (coord : BusCoord)
    (state : BusState) : Parser (ForInStep BusState) := do
  tick 2
  match coord with
  | .column col =>
    tick (memberCost (col,block.kappa) 2 state.1+1)
    if (col,block.kappa) ∉ state.1 then
      let value ← readScalar
      tick (appendCost state.1+appendCost state.2+takeCost block.kappa point+5)
      pure (.yield (state.1++[(col,block.kappa)],
        state.2++[⟨col,point.take block.kappa,value⟩]))
    else pure (.yield state)
  | .publicValue => pure (.yield state)
  | .tableExpression => do check false; pure (.yield state)

private theorem busCoord_work_le (point : List E) (block : BusBlock) (coord : BusCoord)
    (state : BusState) (tokens : List CallerToken) :
    (busCoordStep point block coord state tokens).work ≤
      5*busStateSize state+2*point.length+20 := by
  have memberBound := memberCost_le (match coord with | .column col => col | _ => 0,block.kappa)
    2 state.1
  unfold busCoordStep
  rw [tick_bind_work]
  cases coord with
  | column col =>
    rw [tick_bind_work]
    split
    · apply Nat.le_trans
      · apply Nat.add_le_add_left
        apply Nat.add_le_add_left
        apply bind_work_le
        · exact readScalar_work_le _
        · intro value tail _
          rw [tick_bind_work]
          exact Nat.le_refl _
      · simp only [busStateSize,appendCost,takeCost,pure] at *
        nlinarith [Nat.min_le_right block.kappa point.length]
    · simp only [pure,busStateSize] at *
      omega
  | publicValue => simp [pure,busStateSize]
  | tableExpression => simp [Bind.bind,bind,check,pure,busStateSize]

private theorem busCoord_success (point : List E) (block : BusBlock) (coord : BusCoord)
    (state : BusState) (tokens rest : List CallerToken) (step : ForInStep BusState)
    (accepted : (busCoordStep point block coord state tokens).result = some (step,rest)) :
    ∃ next, step = .yield next ∧ busStateSize next ≤ busStateSize state+2 := by
  unfold busCoordStep at accepted
  simp only [tick_bind_result] at accepted
  cases coord with
  | column col =>
    simp only [tick_bind_result] at accepted
    split at accepted
    · obtain ⟨value,middle,_,accepted⟩ := bind_success _ _ _ _ _ accepted
      simp only [tick_bind_result,pure,Option.some.injEq,Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl,rfl⟩
      exact ⟨_,rfl,by simp only [busStateSize,List.length_append,List.length_cons,List.length_nil]; omega⟩
    · simp only [pure,Option.some.injEq,Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl,rfl⟩
      exact ⟨_,rfl,by omega⟩
  | publicValue =>
    simp only [pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    exact ⟨_,rfl,by omega⟩
  | tableExpression => simp [Bind.bind,bind,check] at accepted

private def busBlockStep (point : List E) (block : BusBlock)
    (state : BusState) : Parser (ForInStep BusState) := do
  tick (lengthCost point+4)
  check (block.kappa ≤ point.length)
  if !block.tableOwned then
    let next ← forIn block.coords state (busCoordStep point block)
    pure (.yield next)
  else pure (.yield state)

private theorem busBlock_work_le (point : List E) (block : BusBlock)
    (state : BusState) (tokens : List CallerToken) (size : Nat)
    (coordinates : block.coords.length ≤ size) (pointBound : point.length ≤ size) :
    (busBlockStep point block state tokens).work ≤
      5*size*busStateSize state+20*size*size+21*size+28 := by
  have loop := forIn_growth_work_le block.coords state (busCoordStep point block)
    busStateSize 5 (2*point.length+20) 2
    (by intro c _ st ts; exact busCoord_work_le point block c st ts)
    (by
      intro c _ st ts step rest accepted
      obtain ⟨next,rfl,growth⟩ := busCoord_success point block c st ts rest step accepted
      exact growth) tokens
  have loopBound : block.coords.length*
      (5*(busStateSize state+2*block.coords.length)+(2*point.length+20)) ≤
      size*(5*busStateSize state+12*size+20) :=
    Nat.mul_le_mul coordinates (by omega)
  unfold busBlockStep
  rw [tick_bind_work]
  apply Nat.le_trans
  · apply Nat.add_le_add_left
    apply bind_work_le
    · exact check_work_le _ _
    · intro _ tail _
      split
      · apply bind_work_le
        · exact forIn_growth_work_le block.coords state (busCoordStep point block)
            busStateSize 5 (2*point.length+20) 2
            (by intro c _ st ts; exact busCoord_work_le point block c st ts)
            (by
              intro c _ st ts step rest accepted
              obtain ⟨next,rfl,growth⟩ := busCoord_success point block c st ts rest step accepted
              exact growth) tail
        · intro _ _ _; exact pure_work_le _ _
      · exact (pure_work_le _ _).trans (Nat.zero_le _)
  · unfold lengthCost
    nlinarith


private theorem busBlock_success (point : List E) (block : BusBlock)
    (state : BusState) (tokens rest : List CallerToken) (step : ForInStep BusState)
    (accepted : (busBlockStep point block state tokens).result = some (step,rest)) :
    ∃ next, step = .yield next ∧
      busStateSize next ≤ busStateSize state+2*block.coords.length := by
  unfold busBlockStep at accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨_,accepted⟩ := check_bind_success _ _ _ _ _ accepted
  split at accepted
  · obtain ⟨next,middle,loopRead,accepted⟩ := bind_success _ _ _ _ _ accepted
    have growth := forIn_success_growth block.coords (busCoordStep point block)
      busStateSize 2
      (fun c _ st ts outcome tail h => busCoord_success point block c st ts tail outcome h)
      state next tokens middle loopRead
    simp only [pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    exact ⟨next,rfl,growth⟩
  · simp only [pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    exact ⟨_,rfl,by omega⟩

/-- Every bus literal (including unused producer windows and coordinate indices)
is represented additively; powers of two are not counted as input magnitude. -/
def busCoordSize : BusCoord → Nat
  | .column col => 1+col
  | .publicValue => 1
  | .tableExpression => 1
def busBlockSize (block : BusBlock) : Nat :=
  2+block.kappa+(block.coords.map busCoordSize).sum
def busLayoutSize (l : BusLayout) : Nat :=
  3+l.grinding+(l.push.map busBlockSize).sum+(l.pull.map busBlockSize).sum+
    (l.producers.map (fun p => 1+p.kappa+p.bits+p.window)).sum

private theorem sum_bound {A : Type} (xs : List A) (weight : A → Nat)
    (positive : ∀ x, 1 ≤ weight x) :
    xs.length ≤ (xs.map weight).sum ∧ ∀ x ∈ xs, weight x ≤ (xs.map weight).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,List.mem_cons]
    constructor
    · have := positive x; omega
    · intro next member
      rcases member with rfl | member
      · omega
      · have := ih.2 next member; omega

private theorem blockSize_components (block : BusBlock) :
    block.coords.length ≤ busBlockSize block ∧ block.kappa ≤ busBlockSize block := by
  have coords := sum_bound block.coords busCoordSize (by intro c; cases c <;> simp [busCoordSize])
  unfold busBlockSize
  omega

theorem busLayoutSize_components (l : BusLayout) :
    (l.push++l.pull).length ≤ busLayoutSize l ∧
      ∀ block ∈ l.push++l.pull, block.coords.length ≤ busLayoutSize l := by
  have entries := sum_bound (l.push++l.pull) busBlockSize
    (by intro b; unfold busBlockSize; omega)
  simp only [List.map_append,List.sum_append] at entries
  unfold busLayoutSize
  constructor
  · omega
  · intro b member
    have entry := entries.2 b member
    have coords := (blockSize_components b).1
    omega

private theorem add_power_bound (a b x y : Nat) (left : x ≤ 2^a) (right : y ≤ 2^b) :
    x+y ≤ 2^(1+a+b) := by
  have l := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_right a b)
  have r := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_left b a)
  have equal : 2^(1+a+b) = 2^(a+b)*2 := by
    rw [show 1+a+b = (a+b)+1 by omega,Nat.pow_succ]
  rw [equal]
  omega

private theorem sum_power_bound {A : Type} (xs : List A) (value budget : A → Nat)
    (entries : ∀ x, value x ≤ 2^(budget x)) :
    (xs.map value).sum ≤ 2^((xs.map (fun x => 1+budget x)).sum) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_power_bound _ _ _ _ (entries x) ih

theorem bus_mu_le_size (l : BusLayout) : l.mu ≤ busLayoutSize l := by
  let pushSize := (l.push.map (fun b => 1+b.kappa)).sum
  let pullSize := (l.pull.map (fun b => 1+b.kappa)).sum
  let prodSize := (l.producers.map (fun p => 1+(p.bits+p.kappa))).sum
  have push := sum_power_bound l.push (fun b => 2^b.kappa) BusBlock.kappa (by intro b; rfl)
  have pull := sum_power_bound l.pull (fun b => 2^b.kappa) BusBlock.kappa (by intro b; rfl)
  have producers := sum_power_bound l.producers (fun p => p.bits*2^p.kappa)
    (fun p => p.bits+p.kappa) (by
      intro p
      rw [Nat.pow_add]
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self))
  have stacked := add_power_bound pushSize prodSize _ _ push producers
  have mass : max
      ((l.push.map (fun b => 2^b.kappa)).sum+
        (l.producers.map (fun p => p.bits*2^p.kappa)).sum)
      ((l.pull.map (fun b => 2^b.kappa)).sum) ≤ 2^(1+pushSize+prodSize+pullSize) := by
    apply max_le
    · exact stacked.trans (Nat.pow_le_pow_right (by decide) (by omega))
    · exact pull.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have pushBudget : pushSize ≤ (l.push.map busBlockSize).sum := by
    dsimp only [pushSize]
    apply List.sum_le_sum
    intro b member
    unfold busBlockSize
    omega
  have pullBudget : pullSize ≤ (l.pull.map busBlockSize).sum := by
    dsimp only [pullSize]
    apply List.sum_le_sum
    intro b member
    unfold busBlockSize
    omega
  have prodBudget : prodSize ≤
      (l.producers.map (fun p => 1+p.kappa+p.bits+p.window)).sum := by
    dsimp only [prodSize]
    apply List.sum_le_sum
    intro p member
    omega
  have exponential : max (max
      ((l.push.map (fun b => 2^b.kappa)).sum+
        (l.producers.map (fun p => p.bits*2^p.kappa)).sum)
      ((l.pull.map (fun b => 2^b.kappa)).sum)) 1 ≤ 2^(1+pushSize+prodSize+pullSize) :=
    max_le mass Nat.one_le_two_pow
  have logarithm : Nat.log2 (max (max
      ((l.push.map (fun b => 2^b.kappa)).sum+
        (l.producers.map (fun p => p.bits*2^p.kappa)).sum)
      ((l.pull.map (fun b => 2^b.kappa)).sum)) 1-1) ≤ 1+pushSize+prodSize+pullSize := by
    by_cases zero : max (max
      ((l.push.map (fun b => 2^b.kappa)).sum+
        (l.producers.map (fun p => p.bits*2^p.kappa)).sum)
      ((l.pull.map (fun b => 2^b.kappa)).sum)) 1-1 = 0
    · rw [zero,Nat.log2_zero]; omega
    · have less : max (max
        ((l.push.map (fun b => 2^b.kappa)).sum+
          (l.producers.map (fun p => p.bits*2^p.kappa)).sum)
        ((l.pull.map (fun b => 2^b.kappa)).sum)) 1-1 < 2^(1+pushSize+prodSize+pullSize) := by
        omega
      exact Nat.le_of_lt ((Nat.log2_lt zero).2 less)
  unfold BusLayout.mu busLayoutSize
  dsimp only []
  split <;> omega

private theorem sum_scaled_le {A : Type} (xs : List A) (value weight : A → Nat)
    (scale : Nat) (entries : ∀ x, value x ≤ scale*weight x) :
    (xs.map value).sum ≤ scale*(xs.map weight).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have entry := entries x
    simp only [List.map_cons,List.sum_cons]
    nlinarith

theorem bus_mu_work_le (l : BusLayout) :
    (mu l).work ≤ 11*busLayoutSize l+17 := by
  have push := sum_scaled_le l.push (fun b => 3*b.kappa+6) busBlockSize 7
    (by intro b; unfold busBlockSize; omega)
  have pull := sum_scaled_le l.pull (fun b => 3*b.kappa+6) busBlockSize 7
    (by intro b; unfold busBlockSize; omega)
  have producers := sum_scaled_le l.producers (fun p => 3*p.kappa+7)
    (fun p => 1+p.kappa+p.bits+p.window) 7 (by intro p; omega)
  have work := mu_work_le l
  have logarithm := bus_mu_le_size l
  unfold busLayoutSize at *
  omega

private theorem busLoop_work_le (l : BusLayout) (point : List E)
    (tokens : List CallerToken) (size : Nat)
    (configuration : busLayoutSize l ≤ size) (pointBound : point.length ≤ size) :
    (forIn (l.push++l.pull) ([],[]) (busBlockStep point) tokens).work ≤
      size*(10*size*size*size+20*size*size+21*size+28) := by
  have components := busLayoutSize_components l
  have blocks : (l.push++l.pull).length ≤ size := components.1.trans configuration
  have bounded := forIn_growth_work_le (l.push++l.pull) ([],[]) (busBlockStep point)
    busStateSize (5*size) (20*size*size+21*size+28) (2*size)
    (by
      intro b member state ts
      have coords := (components.2 b member).trans configuration
      simpa [Nat.add_assoc] using busBlock_work_le point b state ts size coords pointBound)
    (by
      intro b member state ts step rest accepted
      obtain ⟨next,rfl,growth⟩ := busBlock_success point b state ts rest step accepted
      have coords := (components.2 b member).trans configuration
      simp only [iterationState]
      omega) tokens
  have inner : 5*size*(busStateSize ([],[])+2*size*(l.push++l.pull).length)+
      (20*size*size+21*size+28) ≤
      10*size*size*size+20*size*size+21*size+28 := by
    have product := Nat.mul_le_mul_left (2*size) blocks
    have scaled := Nat.mul_le_mul_left (5*size) product
    simp only [busStateSize,List.length_nil] at *
    nlinarith
  exact bounded.trans (Nat.mul_le_mul blocks inner)

private theorem busLoop_success_size (l : BusLayout) (point : List E)
    (tokens rest : List CallerToken) (final : BusState) (size : Nat)
    (configuration : busLayoutSize l ≤ size)
    (accepted : (forIn (l.push++l.pull) ([],[]) (busBlockStep point) tokens).result =
      some (final,rest)) :
    final.2.length ≤ 2*size*size := by
  have components := busLayoutSize_components l
  have growth := forIn_success_growth (l.push++l.pull) (busBlockStep point)
    busStateSize (2*size) (by
      intro b member state ts step tail h
      obtain ⟨next,rfl,bound⟩ := busBlock_success point b state ts tail step h
      have coords := (components.2 b member).trans configuration
      exact ⟨next,rfl,by omega⟩) ([],[]) final tokens rest accepted
  have length := components.1.trans configuration
  simp only [busStateSize,List.length_nil] at growth
  nlinarith [Nat.mul_le_mul_left (2*size) length]

private theorem mapM_success_all {A B : Type} (xs : List A) (body : A → Parser B)
    (property : B → Prop)
    (each : ∀ x ∈ xs, ∀ ts value rest, (body x ts).result = some (value,rest) → property value)
    (tokens rest : List CallerToken) (output : List B)
    (accepted : (xs.mapM body tokens).result = some (output,rest)) :
    ∀ value ∈ output, property value := by
  induction xs generalizing tokens output with
  | nil =>
    simp only [List.mapM_nil] at accepted
    change some ([],tokens) = some (output,rest) at accepted
    cases accepted
    simp
  | cons x xs ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨value,middle,first,accepted⟩ := bind_success _ _ _ _ _ accepted
    obtain ⟨values,middle,last,accepted⟩ := bind_success _ _ _ _ _ accepted
    change some (value::values,middle) = some (output,rest) at accepted
    cases accepted
    have head := each x (by simp) tokens value middle first
    have tail := ih (fun y member ts v remaining h => each y (by simp [member]) ts v remaining h)
      _ _ last
    intro next member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact tail next member

theorem constraintClaims_success_caps (layouts : List AirLayout) (p : List E)
    (tokens rest : List CallerToken) (output : List TableClaims) (size : Nat)
    (configuration : airLayoutsSize layouts ≤ size)
    (accepted : (constraintClaims layouts p tokens).result = some (output,rest)) :
    output.length ≤ size ∧
    ∀ table ∈ output, table.point.length ≤ size ∧
      table.evals.length ≤ size ∧ table.slices.length ≤ size := by
  have cardinality := constraintClaims_success_length layouts p tokens rest output accepted
  have components := airLayouts_components layouts
  constructor
  · unfold airLayoutsSize at configuration
    omega
  · unfold constraintClaims at accepted
    simp only [tick_bind_result] at accepted
    obtain ⟨_,accepted⟩ := check_bind_success _ _ _ _ _ accepted
    simp only [tick_bind_result] at accepted
    obtain ⟨rounds,middle,_,accepted⟩ := bind_success _ _ _ _ _ accepted
    refine mapM_success_all _ _
      (fun table => table.point.length ≤ size ∧ table.evals.length ≤ size ∧ table.slices.length ≤ size)
      ?_ _ _ _ accepted
    intro l member ts table remaining h
    simp only [tick_bind_result] at h
    have lengths := receiveTable_success_lengths l rounds.reverse ts remaining table h
    have sourceSize := components.2 l member
    have config := airLayoutSize_components l
    unfold airLayoutsSize at configuration
    omega

private theorem forIn_success_invariant {A B : Type} (xs : List A)
    (body : A → B → Parser (ForInStep B)) (invariant : B → Prop)
    (preserves : ∀ x state ts step rest, invariant state →
      (body x state ts).result = some (step,rest) →
      ∃ next, step = .yield next ∧ invariant next)
    (initial final : B) (tokens rest : List CallerToken)
    (start : invariant initial)
    (accepted : (forIn xs initial body tokens).result = some (final,rest)) :
    invariant final := by
  induction xs generalizing initial tokens with
  | nil =>
    simp only [List.forIn_nil] at accepted
    change some (initial,tokens) = some (final,rest) at accepted
    cases accepted
    exact start
  | cons x xs ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨step,middle,first,accepted⟩ := bind_success _ _ _ _ _ accepted
    obtain ⟨next,rfl,retained⟩ := preserves x initial tokens step middle start first
    exact ih next middle retained accepted

private def busPointInvariant (point : List E) (state : BusState) : Prop :=
  ∀ claim ∈ state.2, claim.point.length ≤ point.length

private theorem busCoord_preserves (point : List E) (block : BusBlock) (coord : BusCoord)
    (state : BusState) (tokens rest : List CallerToken) (step : ForInStep BusState)
    (invariant : busPointInvariant point state)
    (accepted : (busCoordStep point block coord state tokens).result = some (step,rest)) :
    ∃ next, step = .yield next ∧ busPointInvariant point next := by
  unfold busCoordStep at accepted
  simp only [tick_bind_result] at accepted
  cases coord with
  | column col =>
    simp only [tick_bind_result] at accepted
    split at accepted
    · obtain ⟨value,middle,_,accepted⟩ := bind_success _ _ _ _ _ accepted
      simp only [tick_bind_result,pure,Option.some.injEq,Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl,rfl⟩
      refine ⟨_,rfl,?_⟩
      intro claim member
      rcases List.mem_append.mp member with member | member
      · exact invariant claim member
      · simp only [List.mem_singleton] at member
        subst claim
        simp only [List.length_take]
        exact Nat.min_le_right _ _
    · simp only [pure,Option.some.injEq,Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl,rfl⟩
      exact ⟨_,rfl,invariant⟩
  | publicValue =>
    simp only [pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    exact ⟨_,rfl,invariant⟩
  | tableExpression => simp [Bind.bind,bind,check] at accepted

private theorem busBlock_preserves (point : List E) (block : BusBlock)
    (state : BusState) (tokens rest : List CallerToken) (step : ForInStep BusState)
    (invariant : busPointInvariant point state)
    (accepted : (busBlockStep point block state tokens).result = some (step,rest)) :
    ∃ next, step = .yield next ∧ busPointInvariant point next := by
  unfold busBlockStep at accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨_,accepted⟩ := check_bind_success _ _ _ _ _ accepted
  split at accepted
  · obtain ⟨next,middle,loopRead,accepted⟩ := bind_success _ _ _ _ _ accepted
    have retained := forIn_success_invariant block.coords (busCoordStep point block)
      (busPointInvariant point)
      (fun c st ts outcome tail inv h => busCoord_preserves point block c st ts tail outcome inv h)
      state next tokens middle invariant loopRead
    simp only [pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    exact ⟨next,rfl,retained⟩
  · simp only [pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    exact ⟨_,rfl,invariant⟩

private def busTail (l : BusLayout) (point : List E) :
    Parser (List E × List ColumnClaim) := do
  tick (appendCost l.push+2)
  let final ← forIn (l.push++l.pull) ([],[]) (busBlockStep point)
  tick 3
  pure (point,final.2)

private def busPrefix (l : BusLayout) : Parser (List E × List ColumnClaim) := do
  let _ ← drawScalars 4
  let _ ← drawScalar
  tick (mu l).work
  let point ← gkrPoint (mu l).value
  busTail l point

private theorem busClaims_normalized (l : BusLayout) :
    busClaims l = (do
      tick 2
      if l.grinding > 0 then
        let _ ← nonce l.grinding
        busPrefix l
      else busPrefix l) := rfl

private theorem busTail_work_le (l : BusLayout) (point : List E)
    (tokens : List CallerToken) (size : Nat)
    (configuration : busLayoutSize l ≤ size) (pointBound : point.length ≤ size) :
    (busTail l point tokens).work ≤
      size*(10*size*size*size+20*size*size+21*size+28)+2*size+6 := by
  have blocks := (busLayoutSize_components l).1.trans configuration
  have push : l.push.length ≤ size := by simp only [List.length_append] at blocks; omega
  unfold busTail
  rw [tick_bind_work]
  apply Nat.le_trans
  · apply Nat.add_le_add_left
    apply bind_work_le
    · exact busLoop_work_le l point tokens size configuration pointBound
    · intro _ tail _
      rw [tick_bind_work]
      exact Nat.le_refl _
  · simp only [appendCost,pure]
    omega

private theorem busTail_success_caps (l : BusLayout) (point : List E)
    (tokens rest : List CallerToken) (output : List E × List ColumnClaim) (size : Nat)
    (configuration : busLayoutSize l ≤ size)
    (accepted : (busTail l point tokens).result = some (output,rest)) :
    output.1 = point ∧ output.2.length ≤ 2*size*size ∧
      ∀ claim ∈ output.2, claim.point.length ≤ point.length := by
  unfold busTail at accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨final,middle,loopRead,accepted⟩ := bind_success _ _ _ _ _ accepted
  have cardinality := busLoop_success_size l point tokens middle final size configuration loopRead
  have points := forIn_success_invariant (l.push++l.pull) (busBlockStep point)
    (busPointInvariant point)
    (fun b st ts step tail inv h => busBlock_preserves point b st ts tail step inv h)
    ([],[]) final tokens middle (by simp [busPointInvariant]) loopRead
  simp only [tick_bind_result,pure,Option.some.injEq,Prod.mk.injEq] at accepted
  rcases accepted with ⟨rfl,rfl⟩
  exact ⟨rfl,cardinality,points⟩

theorem receiveTable_work_canonical (l : AirLayout) (p : List E) (tokens : List CallerToken) :
    (receiveTable l p tokens).work ≤ 100*(airLayoutSize l+p.length+1)^3 :=
  receiveTable_work_polynomial l p tokens (airLayoutSize l+p.length)
    (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem constraintClaims_work_canonical (layouts : List AirLayout) (p : List E)
    (tokens : List CallerToken) :
    (constraintClaims layouts p tokens).work ≤
      100*(airLayoutsSize layouts+p.length+1)^3*(airLayoutsSize layouts+p.length)+
        2*(airLayoutsSize layouts+p.length)*(airLayoutsSize layouts+p.length)+
          50*(airLayoutsSize layouts+p.length)+20 :=
  constraintClaims_work_polynomial layouts p tokens (airLayoutsSize layouts+p.length)
    (Nat.le_add_right _ _) (Nat.le_add_left _ _)

private theorem busPrefix_success_decomposition (l : BusLayout)
    (tokens rest : List CallerToken) (output : List E × List ColumnClaim) (size : Nat)
    (configuration : busLayoutSize l ≤ size)
    (accepted : (busPrefix l tokens).result = some (output,rest)) :
    ∃ gkrTokens gkrRest, (gkrPoint (mu l).value gkrTokens).result = some (output.1,gkrRest) ∧
      output.2.length ≤ 2*size*size ∧
      ∀ claim ∈ output.2, claim.point.length ≤ output.1.length := by
  unfold busPrefix at accepted
  obtain ⟨_,middle,_,accepted⟩ := bind_success _ _ _ _ _ accepted
  obtain ⟨_,gkrTokens,_,accepted⟩ := bind_success _ _ _ _ _ accepted
  simp only [tick_bind_result] at accepted
  obtain ⟨point,gkrRest,gkrRead,accepted⟩ := bind_success _ _ _ _ _ accepted
  have caps := busTail_success_caps l point gkrRest rest output size configuration accepted
  rw [← caps.1] at gkrRead
  exact ⟨gkrTokens,gkrRest,gkrRead,caps.2.1,by simpa [caps.1] using caps.2.2⟩

theorem busClaims_success_decomposition (l : BusLayout)
    (tokens rest : List CallerToken) (output : List E × List ColumnClaim) (size : Nat)
    (configuration : busLayoutSize l ≤ size)
    (accepted : (busClaims l tokens).result = some (output,rest)) :
    ∃ gkrTokens gkrRest, (gkrPoint l.mu gkrTokens).result = some (output.1,gkrRest) ∧
      output.2.length ≤ 2*size*size ∧
      ∀ claim ∈ output.2, claim.point.length ≤ output.1.length := by
  rw [busClaims_normalized] at accepted
  simp only [tick_bind_result] at accepted
  split at accepted
  · obtain ⟨_,middle,_,accepted⟩ := bind_success _ _ _ _ _ accepted
    simpa only [mu_erasure] using
      busPrefix_success_decomposition l middle rest output size configuration accepted
  · simpa only [mu_erasure] using
      busPrefix_success_decomposition l tokens rest output size configuration accepted

/-- Conservative quartic obtained from the actual nested bus visits. -/
def busClaimsWork (size : Nat) : Nat :=
  size*(10*size*size*size+20*size*size+21*size+28)+
    94*size*size+155*size+134

private theorem busGKR_work_le (l : BusLayout) (tokens : List CallerToken) (size : Nat)
    (configuration : busLayoutSize l ≤ size) :
    (gkrPoint (mu l).value tokens).work ≤ 94*size*size+142*size+62 := by
  have bound := gkrPoint_work_le (mu l).value tokens
  have magnitude := (bus_mu_le_size l).trans configuration
  rw [mu_erasure] at bound ⊢
  have square := Nat.mul_self_le_mul_self magnitude
  nlinarith

private theorem busPrefix_work_le (l : BusLayout) (tokens : List CallerToken) (size : Nat)
    (configuration : busLayoutSize l ≤ size) :
    (busPrefix l tokens).work ≤
      size*(10*size*size*size+20*size*size+21*size+28)+
        94*size*size+155*size+127 := by
  have muCost := bus_mu_work_le l
  have magnitude := (bus_mu_le_size l).trans configuration
  unfold busPrefix
  apply Nat.le_trans
  · apply bind_work_le
    · exact drawScalars_work_le _ _
    · intro _ tail _
      apply bind_work_le
      · exact drawScalar_work_le _
      · intro _ tail _
        apply bind_work_le
        · exact tick_work_le _ _
        · intro _ tail _
          apply bind_work_le
          · exact busGKR_work_le l tail size configuration
          · intro point tail parsed
            have pointLength := gkrPoint_success_length (mu l).value _ point _ parsed
            rw [mu_erasure] at pointLength
            exact busTail_work_le l point tail size configuration
              (pointLength.trans_le magnitude)
  · omega

theorem busClaims_work_polynomial (l : BusLayout) (tokens : List CallerToken)
    (size : Nat) (configuration : busLayoutSize l ≤ size) :
    (busClaims l tokens).work ≤ busClaimsWork size := by
  rw [busClaims_normalized,tick_bind_work]
  split
  · apply Nat.le_trans
    · apply Nat.add_le_add_left
      apply bind_work_le
      · exact nonce_work_le _ _
      · intro _ tail _; exact busPrefix_work_le l tail size configuration
    · unfold busClaimsWork; omega
  · have bound := busPrefix_work_le l tokens size configuration
    unfold busClaimsWork
    omega

theorem busClaims_work_canonical (l : BusLayout) (tokens : List CallerToken) :
    (busClaims l tokens).work ≤ busClaimsWork (busLayoutSize l) :=
  busClaims_work_polynomial l tokens (busLayoutSize l) (Nat.le_refl _)

theorem busClaims_success_point_length (l : BusLayout)
    (tokens rest : List CallerToken) (output : List E × List ColumnClaim)
    (accepted : (busClaims l tokens).result = some (output,rest)) :
    output.1.length = l.mu := by
  obtain ⟨gkrTokens,gkrRest,gkrRead,_⟩ :=
    busClaims_success_decomposition l tokens rest output (busLayoutSize l) (Nat.le_refl _) accepted
  exact gkrPoint_success_length l.mu gkrTokens output.1 gkrRest gkrRead

theorem busClaims_success_caps (l : BusLayout)
    (tokens rest : List CallerToken) (output : List E × List ColumnClaim) (size : Nat)
    (configuration : busLayoutSize l ≤ size)
    (accepted : (busClaims l tokens).result = some (output,rest)) :
    output.1.length = l.mu ∧ output.1.length ≤ size ∧ output.2.length ≤ 2*size*size ∧
      ∀ claim ∈ output.2, claim.point.length ≤ size := by
  obtain ⟨gkrTokens,gkrRest,gkrRead,cardinality,points⟩ :=
    busClaims_success_decomposition l tokens rest output size configuration accepted
  have length := gkrPoint_success_length l.mu gkrTokens output.1 gkrRest gkrRead
  have pointBound := length.trans_le ((bus_mu_le_size l).trans configuration)
  exact ⟨length,pointBound,cardinality,fun claim member => (points claim member).trans pointBound⟩

#print axioms busClaims_work_polynomial
#print axioms busClaims_work_canonical
#print axioms busClaims_success_point_length
#print axioms busClaims_success_caps

#print axioms busClaims_success_decomposition

#print axioms bus_mu_le_size
#print axioms bus_mu_work_le
#print axioms constraintClaims_success_caps

#print axioms constraintClaims_work_polynomial
#print axioms constraintClaims_success_length

#print axioms receiveTable_work_le
#print axioms receiveTable_work_polynomial
#print axioms receiveTable_success_lengths
#print axioms receiveTable_success_caps
#print axioms receiveTable_work_canonical
#print axioms constraintClaims_work_canonical

end Whir.PCSBCSCallerParserCost
