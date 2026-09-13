import SphincsSecurity.Statement

open OracleComp OracleSpec

namespace DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {ι : Type} {base : OracleSpec ι} {Request Answer : Type}

/-- Every request is new, on every branch of the computation. -/
inductive FreshRequests {α : Type} :
    Set Request → OracleComp (base + (Request →ₒ Answer)) α → Prop
  | pure {used : Set Request} (value : α) : FreshRequests used (pure value)
  | base {used : Set Request} (input : base.Domain) (next : base.Range input → OracleComp (base + (Request →ₒ Answer)) α)
      (tail : ∀ answer, FreshRequests used (next answer)) :
      FreshRequests used (liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= next)
  | request {used : Set Request} (input : Request) (hnew : input ∉ used)
      (next : Answer → OracleComp (base + (Request →ₒ Answer)) α)
      (tail : ∀ answer, FreshRequests (insert input used) (next answer)) :
      FreshRequests used (liftM ((base + (Request →ₒ Answer)).query (.inr input)) >>= next)

theorem FreshRequests.map {α β : Type} {used : Set Request}
    {computation : OracleComp (base + (Request →ₒ Answer)) α}
    (h : FreshRequests used computation) (f : α → β) : FreshRequests used (f <$> computation) := by
  induction h with
  | pure value => simpa only [map_pure] using FreshRequests.pure (f value)
  | base input next _ ih =>
      rw [map_bind]
      apply FreshRequests.base
      exact ih
  | request input hnew next _ ih =>
      rw [map_bind]
      apply FreshRequests.request _ hnew
      exact ih

theorem FreshRequests.bind {α β : Type} {used : Set Request}
    {computation : OracleComp (base + (Request →ₒ Answer)) α}
    (h : FreshRequests used computation) (next : α → OracleComp (base + (Request →ₒ Answer)) β)
    (htail : ∀ value used', FreshRequests used' (next value)) :
    FreshRequests used (computation >>= next) := by
  induction h with
  | pure value => simpa only [pure_bind] using htail value _
  | base input tail _ ih =>
      rw [bind_assoc]
      exact .base input _ ih
  | request input hnew tail _ ih =>
      rw [bind_assoc]
      exact .request input hnew _ ih

def baseLift {α : Type} (computation : OracleComp base α) :
    OracleComp (base + (Request →ₒ Answer)) α :=
  simulateQ (fun input => (liftM ((base + (Request →ₒ Answer)).query (.inl input)) :
    OracleComp (base + (Request →ₒ Answer)) (base.Range input))) computation

theorem baseLift_eq_liftM {α : Type} (computation : OracleComp base α) :
    baseLift (Request := Request) (Answer := Answer) computation =
      (liftM computation : OracleComp (base + (Request →ₒ Answer)) α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [baseLift, simulateQ_bind, simulateQ_spec_query, liftM_bind]
      change (liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= _) =
        (liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= _)
      exact bind_congr ih

theorem simulateQ_baseLift {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (handler : QueryImpl base m) (other : QueryImpl (Request →ₒ Answer) m) (computation : OracleComp base α) :
    simulateQ (handler + other) (baseLift computation) = simulateQ handler computation := by
  rw [baseLift_eq_liftM, QueryImpl.simulateQ_add_liftM_left]

theorem freshRequests_base_bind {α β : Type} (used : Set Request) (first : OracleComp base α)
    (next : α → OracleComp (base + (Request →ₒ Answer)) β)
    (hnext : ∀ value, FreshRequests used (next value)) :
    FreshRequests used (baseLift first >>= next) := by
  rw [baseLift_eq_liftM]
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using hnext value
  | query_bind input tail ih =>
      simp only [liftM_bind, bind_assoc]
      change FreshRequests used (liftM ((base + (Request →ₒ Answer)).query (.inl input)) >>= _)
      exact .base input _ ih

variable {Tape State : Type} [DecidableEq Request]

noncomputable def tableRun {α : Type}
    (handler : QueryImpl base (StateT State ProbComp))
    (sign : Request → Tape → StateT State ProbComp Answer) (table : Request → Tape)
    (computation : OracleComp (base + (Request →ₒ Answer)) α) : StateT State ProbComp α :=
  simulateQ (handler + fun request => sign request (table request)) computation

theorem FreshRequests.tableRun_update {α : Type} {used : Set Request}
    {computation : OracleComp (base + (Request →ₒ Answer)) α}
    (h : FreshRequests used computation)
    (handler : QueryImpl base (StateT State ProbComp))
    (sign : Request → Tape → StateT State ProbComp Answer) (table : Request → Tape)
    (request : Request) (tape : Tape) (hused : request ∈ used) :
    tableRun handler sign (Function.update table request tape) computation =
      tableRun handler sign table computation := by
  induction h with
  | pure value => rfl
  | base input next _ ih =>
      change (handler input >>= fun answer => tableRun handler sign (Function.update table request tape) (next answer)) =
        (handler input >>= fun answer => tableRun handler sign table (next answer))
      exact congrArg (fun k : base.Range input → StateT State ProbComp α => handler input >>= k)
        (funext fun answer => ih answer hused)
  | request input hnew next _ ih =>
      have hne : input ≠ request := fun heq => hnew (heq ▸ hused)
      change (sign input (Function.update table request tape input) >>= fun answer =>
          tableRun handler sign (Function.update table request tape) (next answer)) =
        (sign input (table input) >>= fun answer => tableRun handler sign table (next answer))
      rw [Function.update_of_ne hne]
      exact congrArg (fun k : Answer → StateT State ProbComp α => sign input (table input) >>= k)
        (funext fun answer => ih answer (Set.mem_insert_of_mem _ hused))

variable [Finite Request] [Finite Tape] [Nonempty Tape]
    [SampleableType Tape] [SampleableType (Request → Tape)]

noncomputable def freshRun {α : Type}
    (handler : QueryImpl base (StateT State ProbComp))
    (sign : Request → Tape → StateT State ProbComp Answer)
    (computation : OracleComp (base + (Request →ₒ Answer)) α) : StateT State ProbComp α :=
  simulateQ (handler + fun request => do
    let tape ← liftM ($ᵗ Tape : ProbComp Tape)
    sign request tape) computation

omit [DecidableEq Request] [Finite Request] [Finite Tape] [Nonempty Tape]
    [SampleableType (Request → Tape)] in
theorem freshRun_request_bind {α : Type}
    (handler : QueryImpl base (StateT State ProbComp))
    (sign : Request → Tape → StateT State ProbComp Answer) (input : Request)
    (next : Answer → OracleComp (base + (Request →ₒ Answer)) α) :
    freshRun handler sign (liftM ((base + (Request →ₒ Answer)).query (.inr input)) >>= next) =
      (do
        let tape ← liftM ($ᵗ Tape : ProbComp Tape)
        let answer ← sign input tape
        freshRun handler sign (next answer)) := by
  simp only [freshRun, simulateQ_bind, simulateQ_spec_query]
  change ((do
    let tape ← liftM ($ᵗ Tape : ProbComp Tape)
    sign input tape) >>= _) = _
  simp only [bind_assoc]
  rfl

omit [DecidableEq Request] [Finite Request] [Finite Tape] [Nonempty Tape]
    [SampleableType (Request → Tape)] in
theorem freshRun_baseLift_bind {α β : Type}
    (handler : QueryImpl base (StateT State ProbComp))
    (sign : Request → Tape → StateT State ProbComp Answer) (first : OracleComp base α)
    (next : α → OracleComp (base + (Request →ₒ Answer)) β) :
    freshRun handler sign (baseLift first >>= next) =
      (simulateQ handler first >>= fun value => freshRun handler sign (next value)) := by
  simp only [freshRun, simulateQ_bind, simulateQ_baseLift]

theorem evalDist_table_refresh {α : Type} (request : Request)
    (next : (Request → Tape) → ProbComp α) :
    𝒟[do let table ← $ᵗ (Request → Tape); next table] =
      𝒟[do
        let tape ← $ᵗ Tape
        let table ← $ᵗ (Request → Tape)
        next (Function.update table request tape)] := by
  rw [evalDist_bind, ← evalDist_uniformSample_bind_update request, ← evalDist_bind]
  simp only [bind_assoc, pure_bind]

/-- Independent tapes may be sampled when a request first appears. The state can include query costs. -/
theorem FreshRequests.evalDist_tableRun {α : Type} {used : Set Request}
    {computation : OracleComp (base + (Request →ₒ Answer)) α}
    (h : FreshRequests used computation)
    (handler : QueryImpl base (StateT State ProbComp))
    (sign : Request → Tape → StateT State ProbComp Answer) (state : State) :
    𝒟[do
      let table ← $ᵗ (Request → Tape)
      (tableRun handler sign table computation).run state] =
      𝒟[(freshRun handler sign computation).run state] := by
  induction h generalizing state with
  | pure value =>
      apply evalDist_ext
      intro result
      simp [tableRun, freshRun]
  | base input next _ ih =>
      simp only [tableRun, freshRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change 𝒟[do
        let table ← $ᵗ (Request → Tape)
        let result ← (handler input).run state
        (tableRun handler sign table (next result.1)).run result.2] =
          𝒟[do
            let result ← (handler input).run state
            (freshRun handler sign (next result.1)).run result.2]
      rw [evalDist_bind_bind_swap]
      apply evalDist_bind_congr'
      intro result
      exact ih result.1 result.2
  | request input hnew next htail ih =>
      rw [evalDist_table_refresh input]
      simp only [tableRun, freshRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change 𝒟[do
        let tape ← $ᵗ Tape
        let table ← $ᵗ (Request → Tape)
        let result ← (sign input (Function.update table input tape input)).run state
        (tableRun handler sign (Function.update table input tape) (next result.1)).run result.2] =
          𝒟[do
            let result ← ((do
              let tape ← liftM ($ᵗ Tape : ProbComp Tape)
              sign input tape) : StateT State ProbComp Answer).run state
            (freshRun handler sign (next result.1)).run result.2]
      simp only [Function.update_self, StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
      apply evalDist_bind_congr'
      intro tape
      rw [evalDist_bind_bind_swap]
      apply evalDist_bind_congr'
      intro result
      have hsame : ∀ table : Request → Tape,
          tableRun handler sign (Function.update table input tape) (next result.1) =
            tableRun handler sign table (next result.1) := fun table =>
        (htail result.1).tableRun_update handler sign table input tape (Set.mem_insert _ _)
      simp_rw [hsame]
      exact ih result.1 result.2

end DeterministicSigning
