import Whir.PCSBCSCallerPayloadPolynomialBound

/-! Actual CPU producer and nested register source-operation bounds. Rejection
retains its executed prefix; delayed getters are not evaluated by construction. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace Whir.PCSBCSCallerPayloadCost
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec
open PCSBCSCallerParserCost hiding pure liftOption

abbrev CpuEarly := Option (List RingPCSGame.FamilyClaim × List ColumnClaim)
abbrev CpuSlices := CpuEarly × List E
abbrev CpuRings := CpuEarly × List RingPCSGame.FamilyClaim

def cpuSliceStep (summed : List TableClaims) (t : Nat) (state : CpuSlices) :
    Parser (ForInStep CpuSlices) := do
  tick (1 + indexWork summed t)
  match summed[t]? with
  | some claims =>
    tick (2 * state.2.length + 2)
    pure (.yield (none,state.2 ++ claims.slices))
  | _ =>
    let r ← PCSBCSCallerParserCost.liftOption 1 none
    pure (.done (some r,state.2))

def cpuProducerStep (pair : BusProducer × TableClaims) (rings : List RingPCSGame.FamilyClaim) :
    Parser (ForInStep (List RingPCSGame.FamilyClaim)) :=
  match pair with
  | (p,c) => do
    let ring := PCSBCSCallerParserCost.paddedRing p.window c.point c.evals
    tick (1 + ring.work)
    match ring.value with
    | some claim => tick (2*rings.length+2); pure (.yield (rings ++ [claim]))
    | none => PCSBCSCallerParserCost.check false; pure (.yield rings)

def cpuRegisterStep (summed : List TableClaims) (word : RegisterWord) (state : CpuRings) :
    Parser (ForInStep CpuRings) := do
  tick 2
  match word.tables.head? with
  | some first =>
    tick (indexWork summed first)
    match summed[first]? with
    | some firstClaims =>
      let slices ← forIn word.tables (none,[]) (cpuSliceStep summed)
      match slices.1 with
      | some r => pure (.done (some r,state.2))
      | none =>
        let ring := PCSBCSCallerParserCost.paddedRing word.offset firstClaims.point slices.2
        tick ring.work
        match ring.value with
        | some claim => tick (2*state.2.length+2); pure (.yield (none,state.2 ++ [claim]))
        | none => PCSBCSCallerParserCost.check false; pure (.yield (none,state.2))
    | _ =>
      let r ← PCSBCSCallerParserCost.liftOption 1 none
      pure (.done (some r,state.2))
  | _ =>
    let r ← PCSBCSCallerParserCost.liftOption 1 none
    pure (.done (some r,state.2))

private theorem loop_preserves {A B : Type} (xs : List A)
    (body : A → B → Parser (ForInStep B)) (P : B → Prop)
    (each : ∀ x ∈ xs, ∀ st ts step rest, P st →
      (body x st ts).result = some (step,rest) → P (iterationState step))
    (st : B) (ts : List CallerToken) (out : B) (rest : List CallerToken)
    (start : P st) (h : (forIn xs st body ts).result = some (out,rest)) : P out := by
  induction xs generalizing st ts with
  | nil => change some (st,ts) = some (out,rest) at h; cases h; exact start
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step,middle,first,last⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
    have retained := each x (by simp) st ts step middle start first
    cases step with
    | done value => change some (value,middle) = some (out,rest) at last; cases last; exact retained
    | yield value => exact ih (by intro y hy; exact each y (by simp [hy])) value middle retained last

private theorem loop_growth {A B : Type} (xs : List A)
    (body : A → B → Parser (ForInStep B)) (size : B → Nat) (delta : Nat)
    (each : ∀ x ∈ xs, ∀ st ts step rest,
      (body x st ts).result = some (step,rest) → size (iterationState step) ≤ size st+delta)
    (st : B) (ts : List CallerToken) (out : B) (rest : List CallerToken)
    (h : (forIn xs st body ts).result = some (out,rest)) : size out ≤ size st+delta*xs.length := by
  induction xs generalizing st ts with
  | nil => change some (st,ts) = some (out,rest) at h; cases h; simp
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step,middle,first,last⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
    have growth := each x (by simp) st ts step middle first
    cases step with
    | done value =>
      change some (value,middle) = some (out,rest) at last
      cases last
      simp only [iterationState,List.length_cons,Nat.mul_add,Nat.mul_one] at *
      omega
    | yield value =>
      have tail := ih (by intro y hy; exact each y (by simp [hy])) value middle last
      simp only [iterationState,List.length_cons,Nat.mul_add,Nat.mul_one] at *
      omega

private theorem sliceStep_work (summed : List TableClaims) (t : Nat) (state : CpuSlices)
    (ts : List CallerToken) :
    (cpuSliceStep summed t state ts).work ≤ 2*state.2.length+2*summed.length+5 := by
  have index := indexWork_le summed t
  unfold cpuSliceStep
  rw [tick_bind_work]
  cases summed[t]? <;> simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
    Pure.pure,PCSBCSCallerParserCost.pure,PCSBCSCallerParserCost.liftOption] <;> omega

private theorem sliceStep_success (summed : List TableClaims) (cap : Nat)
    (caps : ∀ c ∈ summed, c.slices.length ≤ cap)
    (t : Nat) (state : CpuSlices) (ts rest : List CallerToken) (step : ForInStep CpuSlices)
    (h : (cpuSliceStep summed t state ts).result = some (step,rest)) :
    (iterationState step).1 = none ∧ (iterationState step).2.length ≤ state.2.length+cap := by
  unfold cpuSliceStep at h
  cases lookup : summed[t]? with
  | none => simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,PCSBCSCallerParserCost.liftOption,lookup] at h
  | some claims =>
    have bound := caps claims (List.mem_of_getElem? lookup)
    simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      Pure.pure,PCSBCSCallerParserCost.pure,lookup] at h
    rcases h with ⟨rfl,rfl⟩
    simp [iterationState]
    exact bound

 theorem cpuSliceLoop_work (summed : List TableClaims) (tables : List Nat) (cap : Nat)
    (caps : ∀ c ∈ summed, c.slices.length ≤ cap) (ts : List CallerToken) :
    (forIn tables (none,[]) (cpuSliceStep summed) ts).work ≤
      tables.length*(2*(cap*tables.length)+2*summed.length+5) := by
  simpa [Nat.add_assoc] using forIn_growth_work_le tables (none,[]) (cpuSliceStep summed)
    (fun st => st.2.length) 2 (2*summed.length+5) cap
    (by intro t _ st tokens; exact sliceStep_work summed t st tokens)
    (by intro t _ st tokens step rest h; exact (sliceStep_success summed cap caps t st tokens rest step h).2) ts

 theorem cpuSliceLoop_success (summed : List TableClaims) (tables : List Nat) (cap : Nat)
    (caps : ∀ c ∈ summed, c.slices.length ≤ cap) (ts rest : List CallerToken) (out : CpuSlices)
    (h : (forIn tables (none,[]) (cpuSliceStep summed) ts).result = some (out,rest)) :
    out.1 = none ∧ out.2.length ≤ cap*tables.length := by
  constructor
  · exact loop_preserves tables (cpuSliceStep summed) (fun st => st.1 = none)
      (by intro t _ st tokens step tail _ parsed; exact (sliceStep_success summed cap caps t st tokens tail step parsed).1)
      (none,[]) ts out rest rfl h
  · simpa using loop_growth tables (cpuSliceStep summed) (fun st => st.2.length) cap
      (by intro t _ st tokens step tail parsed; exact (sliceStep_success summed cap caps t st tokens tail step parsed).2)
      (none,[]) ts out rest h

private theorem cpu_bind_bound {A B : Type} (p : Parser A) (f : A → Parser B)
    (ts : List CallerToken) (m n total : Nat) (sum : m+n ≤ total)
    (hp : (p ts).work ≤ m)
    (hf : ∀ a rest, (p ts).result = some (a,rest) → (f a rest).work ≤ n) :
    ((p >>= f) ts).work ≤ total := (bind_work_le p f ts m n hp hf).trans sum

local macro "cpu_bind " m:term "," n:term : tactic =>
  `(tactic| (apply cpu_bind_bound _ _ _ $m $n; · first | omega | nlinarith))

theorem cpuProducerStep_work (p : BusProducer × TableClaims)
    (rings : List RingPCSGame.FamilyClaim) (size : Nat)
    (point : p.2.point.length ≤ size) (evals : p.2.evals.length ≤ size)
    (ts : List CallerToken) :
    (cpuProducerStep p rings ts).work ≤ 2*rings.length+3*size+10 := by
  rcases p with ⟨p,c⟩
  dsimp only at point evals
  have pad := paddedRing_work_le p.window c.point c.evals
  unfold cpuProducerStep
  rw [tick_bind_work]
  cases (PCSBCSCallerParserCost.paddedRing p.window c.point c.evals).value <;>
    simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      PCSBCSCallerParserCost.check,Pure.pure,PCSBCSCallerParserCost.pure] <;> omega

private theorem cpuProducerStep_success (p : BusProducer × TableClaims)
    (rings : List RingPCSGame.FamilyClaim) (ts rest : List CallerToken)
    (step : ForInStep (List RingPCSGame.FamilyClaim))
    (h : (cpuProducerStep p rings ts).result = some (step,rest)) :
    ∃ ring, step = .yield (rings ++ [ring]) ∧ ring.point.size = p.2.point.length := by
  rcases p with ⟨p,c⟩
  unfold cpuProducerStep at h
  cases pad : (PCSBCSCallerParserCost.paddedRing p.window c.point c.evals).value with
  | none =>
    simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      pad,PCSBCSCallerParserCost.check,Bool.false_eq_true,↓reduceIte] at h
    cases h
  | some ring =>
    simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      pad,Pure.pure,PCSBCSCallerParserCost.pure,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact ⟨ring,rfl,paddedRing_success_point_size _ _ _ _ pad⟩

theorem cpuProducerLoop_work (pairs : List (BusProducer × TableClaims))
    (rings : List RingPCSGame.FamilyClaim) (size : Nat)
    (caps : ∀ p ∈ pairs, p.2.point.length ≤ size ∧ p.2.evals.length ≤ size)
    (ts : List CallerToken) :
    (forIn pairs rings cpuProducerStep ts).work ≤
      pairs.length*(2*(rings.length+pairs.length)+3*size+10) := by
  simpa [Nat.add_assoc] using forIn_growth_work_le pairs rings cpuProducerStep List.length
    2 (3*size+10) 1
    (by intro p hp st tokens; exact cpuProducerStep_work p st size (caps p hp).1 (caps p hp).2 tokens)
    (by
      intro p _ st tokens step rest h
      obtain ⟨ring,rfl,_⟩ := cpuProducerStep_success p st tokens rest step h
      simp [iterationState]) ts

theorem cpuProducerLoop_success (pairs : List (BusProducer × TableClaims))
    (rings : List RingPCSGame.FamilyClaim) (size : Nat)
    (caps : ∀ p ∈ pairs, p.2.point.length ≤ size)
    (initial : ∀ r ∈ rings, r.point.size ≤ size)
    (ts rest : List CallerToken) (out : List RingPCSGame.FamilyClaim)
    (h : (forIn pairs rings cpuProducerStep ts).result = some (out,rest)) :
    out.length ≤ rings.length+pairs.length ∧ ∀ r ∈ out, r.point.size ≤ size := by
  constructor
  · simpa using loop_growth pairs cpuProducerStep List.length 1
      (by
        intro p _ st tokens step tail parsed
        obtain ⟨ring,rfl,_⟩ := cpuProducerStep_success p st tokens tail step parsed
        simp [iterationState]) rings ts out rest h
  · apply loop_preserves pairs cpuProducerStep (fun st => ∀ r ∈ st, r.point.size ≤ size)
      _ rings ts out rest initial h
    intro p hp st tokens step tail inv parsed
    obtain ⟨ring,rfl,dimension⟩ := cpuProducerStep_success p st tokens tail step parsed
    simp only [iterationState,List.mem_append,List.mem_singleton]
    intro r member
    rcases member with member | rfl
    · exact inv r member
    · exact dimension.le.trans (caps p hp)

theorem cpuRegisterStep_work (summed : List TableClaims) (word : RegisterWord)
    (state : CpuRings) (size : Nat) (count : summed.length ≤ size)
    (tables : word.tables.length ≤ size)
    (caps : ∀ c ∈ summed, c.point.length ≤ size ∧ c.slices.length ≤ size)
    (ts : List CallerToken) :
    (cpuRegisterStep summed word state ts).work ≤
      2*state.2.length+2*size^3+3*size^2+9*size+14 := by
  unfold cpuRegisterStep
  rw [tick_bind_work]
  cases head : word.tables.head? with
  | none =>
    simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.liftOption]
  | some first =>
    rw [tick_bind_work]
    have index := indexWork_le summed first
    cases lookup : summed[first]? with
    | none =>
      simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.liftOption]
      omega
    | some claims =>
      have firstCaps := caps claims (List.mem_of_getElem? lookup)
      have slicesWork := cpuSliceLoop_work summed word.tables size (by intro c hc; exact (caps c hc).2) ts
      dsimp only
      apply Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_left
        (bind_work_le _ _ ts
          (word.tables.length*(2*(size*word.tables.length)+2*summed.length+5))
          (size*word.tables.length+2*size+2*state.2.length+9) slicesWork ?_) _) _)
      · nlinarith [Nat.mul_le_mul tables tables,
          Nat.mul_le_mul (Nat.mul_le_mul tables tables) (Nat.le_refl size),
          Nat.mul_le_mul tables count, Nat.mul_le_mul_left size tables]
      · intro slices rest parsed
        have geometry := cpuSliceLoop_success summed word.tables size
          (by intro c hc; exact (caps c hc).2) ts rest slices parsed
        rw [geometry.1]
        have pad := paddedRing_work_le word.offset claims.point slices.2
        rw [tick_bind_work]
        cases (PCSBCSCallerParserCost.paddedRing word.offset claims.point slices.2).value <;>
          simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
            PCSBCSCallerParserCost.check,Pure.pure,PCSBCSCallerParserCost.pure] <;> omega

private theorem cpuRegisterStep_success (summed : List TableClaims) (word : RegisterWord)
    (state : CpuRings) (size : Nat)
    (caps : ∀ c ∈ summed, c.point.length ≤ size ∧ c.slices.length ≤ size)
    (ts rest : List CallerToken) (step : ForInStep CpuRings)
    (h : (cpuRegisterStep summed word state ts).result = some (step,rest)) :
    ∃ ring, step = .yield (none,state.2 ++ [ring]) ∧ ring.point.size ≤ size := by
  unfold cpuRegisterStep at h
  cases head : word.tables.head? with
  | none =>
    simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      PCSBCSCallerParserCost.liftOption,head] at h
  | some first =>
    cases lookup : summed[first]? with
    | none =>
      simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
        PCSBCSCallerParserCost.liftOption,head,lookup] at h
    | some claims =>
      simp only [head,lookup] at h
      change ((forIn word.tables (none,[]) (cpuSliceStep summed) >>= _) ts).result = some (step,rest) at h
      obtain ⟨slices,middle,parsed,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
      have geometry := cpuSliceLoop_success summed word.tables size
        (by intro c hc; exact (caps c hc).2) ts middle slices parsed
      rw [geometry.1] at h
      cases pad : (PCSBCSCallerParserCost.paddedRing word.offset claims.point slices.2).value with
      | none =>
        simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
          pad,PCSBCSCallerParserCost.check,Bool.false_eq_true,↓reduceIte] at h
        cases h
      | some ring =>
        simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
          pad,Pure.pure,PCSBCSCallerParserCost.pure,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨ring,rfl,(paddedRing_success_point_size _ _ _ _ pad).le.trans
          (caps claims (List.mem_of_getElem? lookup)).1⟩

theorem cpuRegisterLoop_work (summed : List TableClaims) (words : List RegisterWord)
    (rings : List RingPCSGame.FamilyClaim) (size : Nat) (count : summed.length ≤ size)
    (tables : ∀ w ∈ words, w.tables.length ≤ size)
    (caps : ∀ c ∈ summed, c.point.length ≤ size ∧ c.slices.length ≤ size)
    (ts : List CallerToken) :
    (forIn words (none,rings) (cpuRegisterStep summed) ts).work ≤
      words.length*(2*(rings.length+words.length)+2*size^3+3*size^2+9*size+14) := by
  have bounded := forIn_growth_work_le words (none,rings) (cpuRegisterStep summed)
    (fun st => st.2.length) 2 (2*size^3+3*size^2+9*size+14) 1
    (by intro w hw st tokens; simpa [Nat.add_assoc] using cpuRegisterStep_work summed w st size count (tables w hw) caps tokens)
    (by
      intro w _ st tokens step rest parsed
      obtain ⟨ring,rfl,_⟩ := cpuRegisterStep_success summed w st size caps tokens rest step parsed
      simp [iterationState]) ts
  simpa only [Nat.one_mul,Nat.add_assoc] using bounded

theorem cpuRegisterLoop_success (summed : List TableClaims) (words : List RegisterWord)
    (rings : List RingPCSGame.FamilyClaim) (size : Nat)
    (caps : ∀ c ∈ summed, c.point.length ≤ size ∧ c.slices.length ≤ size)
    (initial : ∀ r ∈ rings, r.point.size ≤ size)
    (ts rest : List CallerToken) (out : CpuRings)
    (h : (forIn words (none,rings) (cpuRegisterStep summed) ts).result = some (out,rest)) :
    out.1 = none ∧ out.2.length ≤ rings.length+words.length ∧
      ∀ r ∈ out.2, r.point.size ≤ size := by
  constructor
  · exact loop_preserves words (cpuRegisterStep summed) (fun st => st.1 = none)
      (by
        intro w _ st tokens step tail _ parsed
        obtain ⟨ring,rfl,_⟩ := cpuRegisterStep_success summed w st size caps tokens tail step parsed
        rfl) (none,rings) ts out rest rfl h
  constructor
  · simpa using loop_growth words (cpuRegisterStep summed) (fun st => st.2.length) 1
      (by
        intro w _ st tokens step tail parsed
        obtain ⟨ring,rfl,_⟩ := cpuRegisterStep_success summed w st size caps tokens tail step parsed
        simp [iterationState]) (none,rings) ts out rest h
  · apply loop_preserves words (cpuRegisterStep summed) (fun st => ∀ r ∈ st.2, r.point.size ≤ size)
      _ (none,rings) ts out rest initial h
    intro w _ st tokens step tail inv parsed
    obtain ⟨ring,rfl,dimension⟩ := cpuRegisterStep_success summed w st size caps tokens tail step parsed
    simp only [iterationState,List.mem_append,List.mem_singleton]
    intro r member
    rcases member with member | rfl
    · exact inv r member
    · exact dimension


def cpuColumnsFinish (layout : CpuLayout) (bus : List ColumnClaim)
    (columns : List TableClaims) (rings : List RingPCSGame.FamilyClaim) :
    Parser (List RingPCSGame.FamilyClaim × List ColumnClaim) := do
  let paired := (layout.tables.map CpuTableLayout.base).zip columns
  let columnClaims ← charged (3*layout.tables.length+1+
    4*min layout.tables.length columns.length+1+columnsWork bus paired)
    (bus ++ paired.flatMap (fun (base,claims) => WHIRCallerClaims.tableColumns base claims))
  pure (rings,columnClaims)

def cpuAfterPacked (layout : CpuLayout) (bus : List ColumnClaim)
    (columns summed : List TableClaims) (packed : List RingPCSGame.FamilyClaim) :
    Parser (List RingPCSGame.FamilyClaim × List ColumnClaim) := do
  let producers ← charged (layout.tables.length+1+min layout.tables.length summed.length+1)
    (summed.drop layout.tables.length)
  tick (4*min layout.bus.producers.length producers.length+1)
  let rings ← forIn (layout.bus.producers.zip producers) packed cpuProducerStep
  let state ← forIn layout.registers (none,rings) (cpuRegisterStep summed)
  match state.1 with
  | some r => pure r
  | none => cpuColumnsFinish layout bus columns state.2

def cpuAfterSummed (layout : CpuLayout) (bus : List ColumnClaim)
    (settled summed : List TableClaims) :
    Parser (List RingPCSGame.FamilyClaim × List ColumnClaim) := do
  tick (settled.length+1+2*min settled.length layout.tables.length+1+
    allWork (·.settled) (fun _ => 1) (layout.tables.take settled.length))
  PCSBCSCallerParserCost.check (layout.tables.take settled.length |>.all (·.settled))
  tick (settled.length+1+min settled.length layout.tables.length+1+
    allWork (! ·.settled) (fun _ => 2) (layout.tables.drop settled.length))
  PCSBCSCallerParserCost.check (layout.tables.drop settled.length |>.all (! ·.settled))
  let columns ← charged (layout.tables.length+1+2*min layout.tables.length summed.length+1+
    settled.length+1+min settled.length (min layout.tables.length summed.length)+1+
    2*settled.length+1) (settled ++ (summed.take layout.tables.length).drop settled.length)
  let packed ← PCSBCSCallerParserCost.flockClaims layout.flock
  cpuAfterPacked layout bus columns summed packed

def cpuAfterBus (layout : CpuLayout) (point : List E) (bus : List ColumnClaim) :
    Parser (List RingPCSGame.FamilyClaim × List ColumnClaim) := do
  let settled ← settledClaims layout.tables point
  let _ ← PCSBCSCallerParserCost.drawScalar
  let producerAirs ← charged (7*layout.bus.producers.length+1)
    (layout.bus.producers.map (fun p => (⟨p.kappa,2*p.bits,p.bits,[]⟩ : AirLayout)))
  let airs ← charged (8*layout.tables.length+
    (layout.tables.map (fun t => t.summedColumns.length+1)).sum+2)
    (layout.tables.map CpuTableLayout.air ++ producerAirs)
  let summed ← PCSBCSCallerParserCost.constraintClaims airs point
  cpuAfterSummed layout bus settled summed

private theorem cpu_forIn_congr {A B : Type} (xs : List A) (st : B)
    (f g : A → B → Parser (ForInStep B))
    (h : ∀ x s, f x s = g x s) (ts : List CallerToken) :
    forIn xs st f ts = forIn xs st g ts :=
  congrArg (fun body : A → B → Parser (ForInStep B) => forIn xs st body ts)
    (funext fun x => funext fun s => h x s)

attribute [local irreducible] PCSBCSCallerParserCost.bind PCSBCSCallerParserCost.pure
  PCSBCSCallerParserCost.tick PCSBCSCallerParserCost.liftOption
  PCSBCSCallerParserCost.busClaims settledClaims PCSBCSCallerParserCost.drawScalar
  PCSBCSCallerParserCost.constraintClaims PCSBCSCallerParserCost.flockClaims
  PCSBCSCallerParserCost.paddedRing

theorem cpuPayloadBeforeExit_normalized (layout : CpuLayout) :
    cpuPayloadBeforeExit layout =
      (PCSBCSCallerParserCost.busClaims layout.bus >>= fun pair => cpuAfterBus layout pair.1 pair.2) := by
  unfold cpuPayloadBeforeExit
  apply congrArg (fun next : (List E × List ColumnClaim) →
    Parser (List RingPCSGame.FamilyClaim × List ColumnClaim) =>
      PCSBCSCallerParserCost.busClaims layout.bus >>= next)
  funext pair
  rcases pair with ⟨point,bus⟩
  unfold cpuAfterBus cpuAfterSummed cpuAfterPacked cpuColumnsFinish
    cpuProducerStep cpuRegisterStep cpuSliceStep
  dsimp only
  simp only [Bind.bind,Pure.pure]
  repeat' first
    | rfl
    | (apply cpu_forIn_congr; intro word state)
    | (congr 1 <;> funext x)
  all_goals
    rename_i carrier
    rcases carrier with ⟨early,values⟩
    cases early <;> rfl

attribute [local semireducible] PCSBCSCallerParserCost.bind PCSBCSCallerParserCost.pure
  PCSBCSCallerParserCost.tick PCSBCSCallerParserCost.liftOption
  PCSBCSCallerParserCost.busClaims settledClaims PCSBCSCallerParserCost.drawScalar
  PCSBCSCallerParserCost.constraintClaims PCSBCSCallerParserCost.flockClaims
  PCSBCSCallerParserCost.paddedRing

private theorem cpu_member_sum {A : Type} (xs : List A) (f : A → Nat) (x : A)
    (h : x ∈ xs) : f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.map_cons,List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem cpuLiteralCaps (layout : CpuLayout) (size : Nat) (volume : cpuLayoutVolume layout ≤ size) :
    layout.tables.length ≤ size ∧ layout.bus.producers.length ≤ size ∧
    layout.registers.length ≤ size ∧
    (∀ t ∈ layout.tables, cpuTableVolume t ≤ size) ∧
    (∀ w ∈ layout.registers, w.tables.length ≤ size) := by
  have components := cpuLayoutVolume_components layout
  have airLength (xs : List AirLayout) : xs.length ≤ airLayoutsSize xs := by
    unfold airLayoutsSize
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons] at *
      omega
  have length := airLength (cpuAirs layout)
  simp only [cpuAirs,List.length_append,List.length_map] at length
  change layout.tables.length+layout.bus.producers.length ≤ airLayoutsSize (cpuAirs layout) at length
  refine ⟨components.2.2.1.trans volume,by omega,components.2.2.2.2.2.trans volume,?_,?_⟩
  · intro t ht
    have entry := cpu_member_sum layout.tables cpuTableVolume t ht
    unfold cpuLayoutVolume at volume
    omega
  · intro w hw
    have entry := cpu_member_sum layout.registers registerVolume w hw
    unfold cpuLayoutVolume registerVolume at *
    omega

theorem cpuColumnsFinish_work (layout : CpuLayout) (bus : List ColumnClaim)
    (columns : List TableClaims) (rings : List RingPCSGame.FamilyClaim)
    (ts : List CallerToken) (size : Nat) (count : layout.tables.length ≤ size)
    (busCount : bus.length ≤ 2*size*size)
    (caps : ∀ t ∈ columns, t.evals.length ≤ size) :
    (cpuColumnsFinish layout bus columns rings ts).work ≤ 12*size^2+11*size+4 := by
  let paired := (layout.tables.map CpuTableLayout.base).zip columns
  have pairCount : paired.length ≤ size := by
    simp only [paired,List.length_zip,List.length_map]
    exact (Nat.min_le_left _ _).trans count
  have work := columnsWork_le bus paired size
    (by intro p hp; exact caps p.2 (List.of_mem_zip hp).2)
  unfold cpuColumnsFinish charged
  simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
    Pure.pure,PCSBCSCallerParserCost.pure]
  change 3*layout.tables.length+1+4*min layout.tables.length columns.length+1+
    columnsWork bus paired+0+0 ≤ _
  nlinarith [Nat.min_le_left layout.tables.length columns.length,
    Nat.mul_le_mul_left (8*size+4) pairCount]

theorem cpuColumnsFinish_success (layout : CpuLayout) (bus : List ColumnClaim)
    (columns : List TableClaims) (rings : List RingPCSGame.FamilyClaim)
    (ts rest : List CallerToken) (out : List RingPCSGame.FamilyClaim × List ColumnClaim)
    (size : Nat) (count : layout.tables.length ≤ size) (busCount : bus.length ≤ 2*size*size)
    (busPoints : ∀ c ∈ bus, c.point.length ≤ size)
    (caps : ∀ t ∈ columns, t.point.length ≤ size ∧ t.evals.length ≤ size)
    (h : (cpuColumnsFinish layout bus columns rings ts).result = some (out,rest)) :
    out.1 = rings ∧ out.2.length ≤ 3*size*size ∧ ∀ c ∈ out.2, c.point.length ≤ size := by
  let paired := (layout.tables.map CpuTableLayout.base).zip columns
  have pairCount : paired.length ≤ size := by
    simp only [paired,List.length_zip,List.length_map]
    exact (Nat.min_le_left _ _).trans count
  have geometry := column_geometry bus paired size busCount busPoints pairCount
    (by intro p hp; exact caps p.2 (List.of_mem_zip hp).2)
  unfold cpuColumnsFinish charged at h
  simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
    Pure.pure,PCSBCSCallerParserCost.pure,Option.some.injEq,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩
  exact ⟨rfl,geometry⟩

private theorem charged_bind_work {A B : Type} (n : Nat) (a : A) (f : A → Parser B)
    (ts : List CallerToken) : ((charged n a >>= f) ts).work = n+(f a ts).work := by
  simp only [charged,Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
    Pure.pure,PCSBCSCallerParserCost.pure,Nat.add_zero]

private theorem charged_bind_result {A B : Type} (n : Nat) (a : A) (f : A → Parser B)
    (ts : List CallerToken) : ((charged n a >>= f) ts).result = (f a ts).result := rfl

def cpuBeforeExitWork (size : Nat) : Nat :=
  busClaimsWork size+100*(size+1)^3*size+2*size^4+110*size^3+300*size^2+1300*size+1000

def CpuClaimCaps (size : Nat) (out : List RingPCSGame.FamilyClaim × List ColumnClaim) : Prop :=
  out.1.length ≤ 3*size ∧ (∀ r ∈ out.1, r.point.size ≤ size) ∧
  out.2.length ≤ 3*size*size ∧ (∀ c ∈ out.2, c.point.length ≤ size)

theorem cpuAfterPacked_work (layout : CpuLayout) (bus : List ColumnClaim)
    (columns summed : List TableClaims) (packed : List RingPCSGame.FamilyClaim)
    (ts : List CallerToken) (size : Nat) (volume : cpuLayoutVolume layout ≤ size)
    (busCount : bus.length ≤ 2*size*size) (summedCount : summed.length ≤ size)
    (summedCaps : ∀ t ∈ summed, t.point.length ≤ size ∧ t.evals.length ≤ size ∧ t.slices.length ≤ size)
    (columnCaps : ∀ t ∈ columns, t.evals.length ≤ size) (packedCount : packed.length ≤ size) :
    (cpuAfterPacked layout bus columns summed packed ts).work ≤
      2*size^4+3*size^3+40*size^2+60*size+30 := by
  have literals := cpuLiteralCaps layout size volume
  let pairs := layout.bus.producers.zip (summed.drop layout.tables.length)
  have pairCount : pairs.length ≤ size := by
    simp only [pairs,List.length_zip]
    exact (Nat.min_le_left _ _).trans literals.2.1
  have pairCaps : ∀ p ∈ pairs, p.2.point.length ≤ size ∧ p.2.evals.length ≤ size := by
    intro p hp
    have member := (List.of_mem_zip hp).2
    have source := List.mem_of_mem_drop member
    exact ⟨(summedCaps p.2 source).1,(summedCaps p.2 source).2.1⟩
  have producerWork := cpuProducerLoop_work pairs packed size pairCaps ts
  have producerCap : (forIn pairs packed cpuProducerStep ts).work ≤ size*(7*size+10) := by
    apply producerWork.trans
    exact Nat.mul_le_mul pairCount (by omega)
  unfold cpuAfterPacked
  rw [charged_bind_work,tick_bind_work]
  apply Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_left
    (bind_work_le _ _ ts (size*(7*size+10))
      (size*(2*size^3+3*size^2+15*size+14)+12*size^2+11*size+4) producerCap ?_) _) _)
  · have mn := Nat.min_le_left layout.tables.length summed.length
    have mp := Nat.min_le_left layout.bus.producers.length (summed.drop layout.tables.length).length
    nlinarith
  · intro rings rest parsed
    have grown := loop_growth pairs cpuProducerStep List.length 1
      (by
        intro p _ st tokens step tail accepted
        obtain ⟨ring,rfl,_⟩ := cpuProducerStep_success p st tokens tail step accepted
        simp [iterationState]) packed ts rings rest parsed
    simp only [Nat.one_mul] at grown
    have ringCount : rings.length ≤ 2*size := by omega
    have registerWork := cpuRegisterLoop_work summed layout.registers rings size summedCount
      literals.2.2.2.2 (by intro t ht; exact ⟨(summedCaps t ht).1,(summedCaps t ht).2.2⟩) rest
    have registerCap : (forIn layout.registers (none,rings) (cpuRegisterStep summed) rest).work ≤
        size*(2*size^3+3*size^2+15*size+14) := by
      apply registerWork.trans
      exact Nat.mul_le_mul literals.2.2.1 (by omega)
    cpu_bind (size*(2*size^3+3*size^2+15*size+14)), (12*size^2+11*size+4)
    · exact registerCap
    · intro state tail reached
      have clean := loop_preserves layout.registers (cpuRegisterStep summed) (fun st => st.1 = none)
        (by
          intro w _ st tokens step remaining _ accepted
          obtain ⟨ring,rfl,_⟩ := cpuRegisterStep_success summed w st size
            (by intro t ht; exact ⟨(summedCaps t ht).1,(summedCaps t ht).2.2⟩)
            tokens remaining step accepted
          rfl) (none,rings) rest state tail rfl reached
      rw [clean]
      exact cpuColumnsFinish_work layout bus columns state.2 tail size literals.1 busCount columnCaps

theorem cpuAfterPacked_success (layout : CpuLayout) (bus : List ColumnClaim)
    (columns summed : List TableClaims) (packed : List RingPCSGame.FamilyClaim)
    (ts rest : List CallerToken) (out : List RingPCSGame.FamilyClaim × List ColumnClaim)
    (size : Nat) (volume : cpuLayoutVolume layout ≤ size)
    (busCount : bus.length ≤ 2*size*size) (busPoints : ∀ c ∈ bus, c.point.length ≤ size)
    (summedCaps : ∀ t ∈ summed, t.point.length ≤ size ∧ t.slices.length ≤ size)
    (columnCaps : ∀ t ∈ columns, t.point.length ≤ size ∧ t.evals.length ≤ size)
    (packedCount : packed.length ≤ size) (packedPoints : ∀ r ∈ packed, r.point.size ≤ size)
    (h : (cpuAfterPacked layout bus columns summed packed ts).result = some (out,rest)) :
    CpuClaimCaps size out := by
  have literals := cpuLiteralCaps layout size volume
  let pairs := layout.bus.producers.zip (summed.drop layout.tables.length)
  have pairCount : pairs.length ≤ size := by
    simp only [pairs,List.length_zip]
    exact (Nat.min_le_left _ _).trans literals.2.1
  unfold cpuAfterPacked at h
  rw [charged_bind_result] at h
  change ((forIn pairs packed cpuProducerStep >>= _) ts).result = some (out,rest) at h
  obtain ⟨rings,middle,parsed,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have producers := cpuProducerLoop_success pairs packed size
    (by intro p hp; exact (summedCaps p.2 (List.mem_of_mem_drop (List.of_mem_zip hp).2)).1)
    packedPoints ts middle rings parsed
  obtain ⟨state,tail,reached,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have registers := cpuRegisterLoop_success summed layout.registers rings size summedCaps
    producers.2 middle tail state reached
  rw [registers.1] at h
  have columns := cpuColumnsFinish_success layout bus columns state.2 tail rest out size
    literals.1 busCount busPoints columnCaps h
  unfold CpuClaimCaps
  rw [columns.1]
  refine ⟨?_,registers.2.2,columns.2⟩
  omega

private theorem cpu_tick_bound {A : Type} (n : Nat) (p : Parser A) (ts : List CallerToken)
    (cap total : Nat) (sum : n+cap ≤ total) (hp : (p ts).work ≤ cap) :
    ((tick n >>= fun _ => p) ts).work ≤ total := by
  rw [tick_bind_work]
  exact (Nat.add_le_add_left hp n).trans sum

local macro "cpu_tick " cap:term : tactic =>
  `(tactic| (apply cpu_tick_bound _ _ _ $cap; · first | omega | nlinarith))

private theorem cpuMergedCaps (layout : CpuLayout) (settled summed : List TableClaims) (size : Nat)
    (settledCaps : ∀ t ∈ settled, t.point.length ≤ size ∧ t.evals.length ≤ size)
    (summedCaps : ∀ t ∈ summed, t.point.length ≤ size ∧ t.evals.length ≤ size ∧ t.slices.length ≤ size) :
    ∀ t ∈ settled ++ (summed.take layout.tables.length).drop settled.length,
      t.point.length ≤ size ∧ t.evals.length ≤ size := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact settledCaps t ht
  · have source := List.mem_of_mem_take (List.mem_of_mem_drop ht)
    exact ⟨(summedCaps t source).1,(summedCaps t source).2.1⟩

theorem cpuAfterSummed_work (layout : CpuLayout) (bus : List ColumnClaim)
    (settled summed : List TableClaims) (ts : List CallerToken) (size : Nat)
    (volume : cpuLayoutVolume layout ≤ size) (busCount : bus.length ≤ 2*size*size)
    (settledCount : settled.length ≤ size) (summedCount : summed.length ≤ size)
    (settledCaps : ∀ t ∈ settled, t.point.length ≤ size ∧ t.evals.length ≤ size)
    (summedCaps : ∀ t ∈ summed, t.point.length ≤ size ∧ t.evals.length ≤ size ∧ t.slices.length ≤ size) :
    (cpuAfterSummed layout bus settled summed ts).work ≤
      2*size^4+3*size^3+60*size^2+1000*size+800 := by
  have literals := cpuLiteralCaps layout size volume
  have components := cpuLayoutVolume_components layout
  have flockConfig := components.2.2.2.1.trans volume
  have allFirst := allWork_le (fun t : CpuTableLayout => t.settled) (fun _ => 1)
    (layout.tables.take settled.length) 1 (by intro t _; exact Nat.le_refl _)
  have allLast := allWork_le (fun t : CpuTableLayout => !t.settled) (fun _ => 2)
    (layout.tables.drop settled.length) 2 (by intro t _; exact Nat.le_refl _)
  have firstLen : (layout.tables.take settled.length).length ≤ size :=
    (List.length_take_le _ _).trans settledCount
  have lastLen : (layout.tables.drop settled.length).length ≤ size :=
    (by rw [List.length_drop]; omega)
  have merged := cpuMergedCaps layout settled summed size settledCaps summedCaps
  unfold cpuAfterSummed
  cpu_tick (2*size^4+3*size^3+60*size^2+994*size+797)
  cpu_bind 3, (2*size^4+3*size^3+60*size^2+994*size+794)
  · exact check_work_le _ _
  · intro _ rest _
    cpu_tick (2*size^4+3*size^3+60*size^2+987*size+791)
    cpu_bind 3, (2*size^4+3*size^3+60*size^2+987*size+788)
    · exact check_work_le _ _
    · intro _ tail _
      rw [charged_bind_work]
      apply Nat.le_trans (Nat.add_le_add_left
        (bind_work_le _ _ tail (20*size^2+800*size+700)
          (2*size^4+3*size^3+40*size^2+60*size+30) ?_ ?_) _)
      · nlinarith [Nat.min_le_left layout.tables.length summed.length,
          Nat.min_le_left settled.length layout.tables.length,
          Nat.min_le_left settled.length (min layout.tables.length summed.length)]
      · have work := flockClaims_work_le layout.flock tail
        have square := Nat.mul_self_le_mul_self flockConfig
        nlinarith
      · intro packed cursor accepted
        have shape := (flockClaims_resource layout.flock tail).2 packed cursor accepted
        have count := (FlockPolynomial.dimension_caps layout.flock).1.trans flockConfig
        exact cpuAfterPacked_work layout bus _ summed packed cursor size volume busCount summedCount
          summedCaps (by intro t ht; exact (merged t ht).2) (by omega)

theorem cpuAfterSummed_success (layout : CpuLayout) (bus : List ColumnClaim)
    (settled summed : List TableClaims) (ts rest : List CallerToken)
    (out : List RingPCSGame.FamilyClaim × List ColumnClaim) (size : Nat)
    (volume : cpuLayoutVolume layout ≤ size) (busCount : bus.length ≤ 2*size*size)
    (busPoints : ∀ c ∈ bus, c.point.length ≤ size)
    (settledCaps : ∀ t ∈ settled, t.point.length ≤ size ∧ t.evals.length ≤ size)
    (summedCaps : ∀ t ∈ summed, t.point.length ≤ size ∧ t.evals.length ≤ size ∧ t.slices.length ≤ size)
    (h : (cpuAfterSummed layout bus settled summed ts).result = some (out,rest)) :
    CpuClaimCaps size out := by
  have components := cpuLayoutVolume_components layout
  have flockConfig := components.2.2.2.1.trans volume
  unfold cpuAfterSummed at h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨columns,cursor,constructed,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have equal : columns = settled ++ (summed.take layout.tables.length).drop settled.length := by
    change some (_,_) = some (columns,cursor) at constructed
    exact (congrArg Prod.fst (Option.some.inj constructed)).symm
  subst columns
  obtain ⟨packed,tail,accepted,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have shape := (flockClaims_resource layout.flock cursor).2 packed tail accepted
  have count := (FlockPolynomial.dimension_caps layout.flock).1.trans flockConfig
  exact cpuAfterPacked_success layout bus _ summed packed tail rest out size volume
    busCount busPoints (by intro t ht; exact ⟨(summedCaps t ht).1,(summedCaps t ht).2.2⟩)
    (cpuMergedCaps layout settled summed size settledCaps summedCaps)
    (by omega) (by intro r hr; exact (shape.2 r hr).trans flockConfig) h

def cpuAfterBusWork (size : Nat) : Nat :=
  size*(2*size+100*(size+1)^2)+4+(7*size+1)+(8*size+size*(size+1)+2)+
  (100*(size+1)^3*size+2*size^2+50*size+20)+
  (2*size^4+3*size^3+60*size^2+1000*size+800)

theorem cpuAfterBus_work (layout : CpuLayout) (point : List E) (bus : List ColumnClaim)
    (ts : List CallerToken) (size : Nat) (volume : cpuLayoutVolume layout ≤ size)
    (pointCap : point.length ≤ size) (busCount : bus.length ≤ 2*size*size) :
    (cpuAfterBus layout point bus ts).work ≤ cpuAfterBusWork size := by
  have literals := cpuLiteralCaps layout size volume
  have components := cpuLayoutVolume_components layout
  have airConfig := components.2.1.trans volume
  have metadata := sumMap_le layout.tables (fun t => t.summedColumns.length+1) (size+1)
    (by intro t ht; have c := cpuTableVolume_components t; have v := literals.2.2.2.1 t ht; omega)
  have metadataCap : (layout.tables.map (fun t => t.summedColumns.length+1)).sum ≤ size*(size+1) :=
    metadata.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (size+1) literals.1)
  unfold cpuAfterBus cpuAfterBusWork
  cpu_bind (size*(2*size+100*(size+1)^2)),
    (4+(7*size+1)+(8*size+size*(size+1)+2)+
      (100*(size+1)^3*size+2*size^2+50*size+20)+
      (2*size^4+3*size^3+60*size^2+1000*size+800))
  · exact (settledClaims_work_polynomial layout.tables point ts size literals.1
      literals.2.2.2.1 pointCap).trans
      (Nat.mul_le_mul literals.1 (by omega))
  · intro settled rest accepted
    have settledCaps := settledClaims_success_caps layout.tables point ts rest settled size
      literals.1 literals.2.2.2.1 accepted
    cpu_bind 4, ((7*size+1)+(8*size+size*(size+1)+2)+
      (100*(size+1)^3*size+2*size^2+50*size+20)+
      (2*size^4+3*size^3+60*size^2+1000*size+800))
    · exact drawScalar_work_le rest
    · intro _ tail _
      rw [charged_bind_work,charged_bind_work]
      apply Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_left
        (bind_work_le _ _ tail (100*(size+1)^3*size+2*size^2+50*size+20)
          (2*size^4+3*size^3+60*size^2+1000*size+800) ?_ ?_) _) _)
      · omega
      · simpa only [cpuAirs,Nat.pow_two,Nat.mul_assoc] using
          constraintClaims_work_polynomial (cpuAirs layout) point tail size airConfig pointCap
      · intro summed cursor received
        have caps := constraintClaims_success_caps (cpuAirs layout) point tail cursor summed size airConfig received
        exact cpuAfterSummed_work layout bus settled summed cursor size volume busCount
          settledCaps.1 caps.1 settledCaps.2 caps.2

theorem cpuAfterBus_success (layout : CpuLayout) (point : List E) (bus : List ColumnClaim)
    (ts rest : List CallerToken) (out : List RingPCSGame.FamilyClaim × List ColumnClaim)
    (size : Nat) (volume : cpuLayoutVolume layout ≤ size) (busCount : bus.length ≤ 2*size*size)
    (busPoints : ∀ c ∈ bus, c.point.length ≤ size)
    (h : (cpuAfterBus layout point bus ts).result = some (out,rest)) : CpuClaimCaps size out := by
  have literals := cpuLiteralCaps layout size volume
  have airConfig := (cpuLayoutVolume_components layout).2.1.trans volume
  unfold cpuAfterBus at h
  obtain ⟨settled,middle,accepted,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have settledCaps := settledClaims_success_caps layout.tables point ts middle settled size
    literals.1 literals.2.2.2.1 accepted
  obtain ⟨_,tail,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  rw [charged_bind_result,charged_bind_result] at h
  obtain ⟨summed,cursor,received,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have summedCaps := constraintClaims_success_caps (cpuAirs layout) point tail cursor summed size airConfig received
  exact cpuAfterSummed_success layout bus settled summed cursor rest out size volume busCount
    busPoints settledCaps.2 summedCaps.2 h

theorem cpuPayloadBeforeExit_work_polynomial (layout : CpuLayout) (tokens : List CallerToken)
    (size : Nat) (volume : cpuLayoutVolume layout ≤ size) :
    (cpuPayloadBeforeExit layout tokens).work ≤ cpuBeforeExitWork size := by
  have busConfig := (cpuLayoutVolume_components layout).1.trans volume
  rw [cpuPayloadBeforeExit_normalized]
  unfold cpuBeforeExitWork
  apply cpu_bind_bound _ _ _ (busClaimsWork size) (cpuAfterBusWork size)
  · unfold cpuAfterBusWork; nlinarith
  · exact busClaims_work_polynomial layout.bus tokens size busConfig
  · intro pair rest accepted
    have caps := busClaims_success_caps layout.bus tokens rest pair size busConfig accepted
    exact cpuAfterBus_work layout pair.1 pair.2 rest size volume caps.2.1 caps.2.2.1

theorem cpuPayloadBeforeExit_success_caps (layout : CpuLayout) (tokens rest : List CallerToken)
    (out : List RingPCSGame.FamilyClaim × List ColumnClaim) (size : Nat)
    (volume : cpuLayoutVolume layout ≤ size)
    (h : (cpuPayloadBeforeExit layout tokens).result = some (out,rest)) : CpuClaimCaps size out := by
  have busConfig := (cpuLayoutVolume_components layout).1.trans volume
  rw [cpuPayloadBeforeExit_normalized] at h
  obtain ⟨pair,middle,accepted,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have caps := busClaims_success_caps layout.bus tokens middle pair size busConfig accepted
  exact cpuAfterBus_success layout pair.1 pair.2 middle rest out size volume caps.2.2.1 caps.2.2.2 h

def cpuPayloadWorkPolynomial (size : Nat) : Nat :=
  cpuBeforeExitWork size+(3*size*size+5)*(2*(size+6)+15)+6*size^2+300

theorem cpuExitColumns_caps (column : Nat) (output : Fin 4 → UInt64) (cost : OutputCosts) :
    ∀ c ∈ (exitClaims column output cost).value, c.point.length = 6 := by
  intro c hc
  simp only [exitClaims,WHIRCallerClaims.exitClaims,List.mem_cons,List.mem_ofFn] at hc
  rcases hc with rfl | ⟨i,rfl⟩ <;> simp

theorem cpuPayload_zero_work_polynomial (layout : CpuLayout) (cost : OutputCosts)
    (tokens : List CallerToken) (size : Nat) (volume : cpuLayoutVolume layout ≤ size) :
    (cpuPayload layout {cost with call := fun _ => 0} tokens).work ≤ cpuPayloadWorkPolynomial size := by
  unfold cpuPayload cpuPayloadWorkPolynomial
  cpu_bind (cpuBeforeExitWork size), ((3*size*size+5)*(2*(size+6)+15)+6*size^2+300)
  · exact cpuPayloadBeforeExit_work_polynomial layout tokens size volume
  · intro pair rest accepted
    have caps := cpuPayloadBeforeExit_success_caps layout tokens rest pair size volume accepted
    rcases pair with ⟨rings,columns⟩
    rw [charged_bind_work]
    have exits := exitClaims_length layout.finalRegisterColumn layout.output {cost with call := fun _ => 0}
    have columnCount : (columns ++ (exitClaims layout.finalRegisterColumn layout.output
        {cost with call := fun _ => 0}).value).length ≤ 3*size*size+5 := by
      simp only [List.length_append,exits]; exact Nat.add_le_add_right caps.2.2.1 5
    have pointCaps : ∀ c ∈ columns ++ (exitClaims layout.finalRegisterColumn layout.output
        {cost with call := fun _ => 0}).value, c.point.length ≤ size+6 := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact (caps.2.2.2 c hc).trans (Nat.le_add_right _ _)
      · rw [cpuExitColumns_caps _ _ _ c hc]; omega
    have placed := placeClaims_work_le layout.placements _ (size+6) pointCaps
    have placedCap := Nat.mul_le_mul_right (2*(size+6)+15) columnCount
    let allColumns := columns ++ (exitClaims layout.finalRegisterColumn layout.output {cost with call := fun _ => 0}).value
    change (PCSBCSCallerParserCost.placeClaims layout.placements allColumns).work ≤ _ at placed
    have finish : ((PCSBCSCallerParserCost.liftOption
        (PCSBCSCallerParserCost.placeClaims layout.placements allColumns).work
        (PCSBCSCallerParserCost.placeClaims layout.placements allColumns).value >>= fun points =>
          (Pure.pure (rings,points) : Parser _)) rest).work ≤
        (3*size*size+5)*(2*(size+6)+15)+6 := by
      simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.liftOption]
      cases (PCSBCSCallerParserCost.placeClaims layout.placements allColumns).value <;>
        simp only [Option.map_none,Option.map_some,Pure.pure,PCSBCSCallerParserCost.pure,Nat.add_zero]
        <;> omega
    have exitWork : (exitClaims layout.finalRegisterColumn layout.output {cost with call := fun _ => 0}).work = 281 := by
      simp [exitClaims_work,OutputCosts.total]
    rw [exitWork]
    nlinarith [caps.2.2.1]

/-- Every token stream, including early and late rejection, pays only reached
getters. Callback prices are arbitrary naturals and never absorbed in volume. -/
theorem cpuPayload_work_polynomial (layout : CpuLayout) (cost : OutputCosts)
    (tokens : List CallerToken) (size : Nat) (volume : cpuLayoutVolume layout ≤ size) :
    (cpuPayload layout cost tokens).work ≤ cpuPayloadWorkPolynomial size+
      (if (cpuPayloadBeforeExit layout tokens).result.isSome then cost.total else 0) := by
  rw [cpuPayload_output_work]
  exact Nat.add_le_add_right (cpuPayload_zero_work_polynomial layout cost tokens size volume) _

def cpuPointDimension : RingPCSGame.PointClaim → Nat
  | .point _ p _ => p.size
  | .strided _ _ _ p _ => p.size

private theorem cpuPlaceLoop_dimensions (placements : Array Placement)
    (columns : List ColumnClaim) (cap : Nat)
    (caps : ∀ c ∈ columns, c.point.length ≤ cap)
    (xs : List (Option RingPCSGame.PointClaim))
    (h : (PCSBCSCallerParserCost.placeClaimsLoop placements columns).value = some xs) :
    ∀ x ∈ xs, ∀ p, x = some p → cpuPointDimension p ≤ cap := by
  induction columns generalizing xs with
  | nil =>
    change some [] = some xs at h; cases h; simp
  | cons c cs ih =>
    simp only [PCSBCSCallerParserCost.placeClaimsLoop] at h
    cases lookup : placements[c.column]? with
    | none => simp only [lookup] at h; cases h
    | some place =>
      cases tail : (PCSBCSCallerParserCost.placeClaimsLoop placements cs).value with
      | none => simp only [lookup,tail,Option.map_none] at h; cases h
      | some ys =>
        simp only [lookup,tail,Option.map_some,Option.some.injEq] at h
        subst xs
        intro x hx p equal
        rcases List.mem_cons.mp hx with rfl | hx
        · cases place <;>
            simp only [PCSBCSCallerParserCost.placeClaim,Option.some.injEq,reduceCtorEq] at equal
          all_goals subst p; simpa [cpuPointDimension] using caps c (by simp)
        · exact ih (by intro d hd; exact caps d (by simp [hd])) ys tail x hx p equal

theorem cpuPlaceClaims_dimensions (placements : Array Placement) (columns : List ColumnClaim)
    (cap : Nat) (caps : ∀ c ∈ columns, c.point.length ≤ cap)
    (points : Array RingPCSGame.PointClaim)
    (h : (PCSBCSCallerParserCost.placeClaims placements columns).value = some points) :
    ∀ p ∈ points.toList, cpuPointDimension p ≤ cap := by
  unfold PCSBCSCallerParserCost.placeClaims at h
  cases loop : (PCSBCSCallerParserCost.placeClaimsLoop placements columns).value with
  | none => simp only [loop] at h; cases h
  | some xs =>
    simp only [loop,Option.some.injEq] at h
    subst points
    intro p hp
    simp only [List.mem_filterMap] at hp
    obtain ⟨x,hx,equal⟩ := hp
    exact cpuPlaceLoop_dimensions placements columns cap caps xs loop x hx p equal

theorem cpuPayload_success_caps (layout : CpuLayout) (cost : OutputCosts)
    (tokens rest : List CallerToken) (out : List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim)
    (size : Nat) (volume : cpuLayoutVolume layout ≤ size)
    (h : (cpuPayload layout cost tokens).result = some (out,rest)) :
    out.1.length ≤ 3*size ∧ (∀ r ∈ out.1, r.point.size ≤ size) ∧
      out.2.size ≤ 3*size*size+5 ∧ (∀ p ∈ out.2.toList, cpuPointDimension p ≤ size+6) := by
  unfold cpuPayload at h
  obtain ⟨pair,middle,accepted,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have caps := cpuPayloadBeforeExit_success_caps layout tokens middle pair size volume accepted
  rcases pair with ⟨rings,columns⟩
  rw [charged_bind_result] at h
  obtain ⟨points,tail,placed,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  change some ((rings,points),tail) = some (out,rest) at h
  cases h
  have placement : (PCSBCSCallerParserCost.placeClaims layout.placements
      (columns ++ (exitClaims layout.finalRegisterColumn layout.output cost).value)).value = some points := by
    change Option.map (fun x => (x,middle)) _ = some (points,rest) at placed
    cases hv : (PCSBCSCallerParserCost.placeClaims layout.placements
      (columns ++ (exitClaims layout.finalRegisterColumn layout.output cost).value)).value with
    | none => simp only [hv,Option.map_none] at placed; cases placed
    | some p =>
      simp only [hv,Option.map_some,Option.some.injEq,Prod.mk.injEq] at placed
      exact congrArg some placed.1
  have pointCaps : ∀ c ∈ columns ++ (exitClaims layout.finalRegisterColumn layout.output cost).value,
      c.point.length ≤ size+6 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (caps.2.2.2 c hc).trans (Nat.le_add_right _ _)
    · rw [cpuExitColumns_caps _ _ _ c hc]; omega
  refine ⟨caps.1,caps.2.1,?_,cpuPlaceClaims_dimensions _ _ _ pointCaps _ placement⟩
  have count := placeClaims_success_size _ _ _ placement
  rw [List.length_append,exitClaims_length] at count
  dsimp only [CpuClaimCaps] at caps ⊢
  omega

private theorem cpuLoop_exact {A B : Type} (xs : List A)
    (body : A → B → Parser (ForInStep B)) (size : B → Nat)
    (each : ∀ x ∈ xs, ∀ st ts step rest, (body x st ts).result = some (step,rest) →
      ∃ next, step = .yield next ∧ size next = size st+1)
    (st : B) (ts : List CallerToken) (out : B) (rest : List CallerToken)
    (h : (forIn xs st body ts).result = some (out,rest)) :
    size out = size st+xs.length := by
  induction xs generalizing st ts with
  | nil => change some (st,ts) = some (out,rest) at h; cases h; simp
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step,middle,first,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
    obtain ⟨next,rfl,growth⟩ := each x (by simp) st ts step middle first
    have last := ih (by intro y hy; exact each y (by simp [hy])) next middle h
    simp only [List.length_cons]
    omega

theorem cpuAfterPacked_family_count (layout : CpuLayout) (bus : List ColumnClaim)
    (columns summed : List TableClaims) (packed : List RingPCSGame.FamilyClaim)
    (ts rest : List CallerToken) (out : List RingPCSGame.FamilyClaim × List ColumnClaim)
    (size : Nat) (summedCaps : ∀ t ∈ summed, t.point.length ≤ size ∧ t.slices.length ≤ size)
    (h : (cpuAfterPacked layout bus columns summed packed ts).result = some (out,rest)) :
    out.1.length = packed.length+
      (layout.bus.producers.zip (summed.drop layout.tables.length)).length+layout.registers.length := by
  unfold cpuAfterPacked at h
  rw [charged_bind_result] at h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨rings,middle,accepted,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have producers := cpuLoop_exact _ cpuProducerStep List.length
    (by
      intro p _ st tokens step tail parsed
      obtain ⟨ring,rfl,_⟩ := cpuProducerStep_success p st tokens tail step parsed
      exact ⟨st ++ [ring],rfl,by simp⟩) packed cursor rings middle accepted
  obtain ⟨state,tail,reached,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have registers := cpuLoop_exact layout.registers (cpuRegisterStep summed) (fun st => st.2.length)
    (by
      intro w _ st tokens step remaining parsed
      obtain ⟨ring,rfl,_⟩ := cpuRegisterStep_success summed w st size summedCaps tokens remaining step parsed
      exact ⟨(none,st.2 ++ [ring]),rfl,by simp⟩) (none,rings) middle state tail reached
  have clean := loop_preserves layout.registers (cpuRegisterStep summed) (fun st => st.1 = none)
    (by
      intro w _ st tokens step remaining _ parsed
      obtain ⟨ring,rfl,_⟩ := cpuRegisterStep_success summed w st size summedCaps tokens remaining step parsed
      rfl) (none,rings) middle state tail rfl reached
  rw [clean] at h
  unfold cpuColumnsFinish charged at h
  simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
    Pure.pure,PCSBCSCallerParserCost.pure,Option.some.injEq,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩
  dsimp only at registers ⊢
  omega

/-- Exact family cardinality on actual success: every declared producer and
register contributes once, even though all rejection prefixes remain bounded. -/
theorem cpuPayloadBeforeExit_success_family_count (layout : CpuLayout)
    (tokens rest : List CallerToken) (out : List RingPCSGame.FamilyClaim × List ColumnClaim)
    (h : (cpuPayloadBeforeExit layout tokens).result = some (out,rest)) :
    out.1.length = layout.flock.length+layout.bus.producers.length+layout.registers.length := by
  rw [cpuPayloadBeforeExit_normalized] at h
  obtain ⟨pair,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  unfold cpuAfterBus at h
  obtain ⟨settled,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  rw [charged_bind_result,charged_bind_result] at h
  obtain ⟨summed,cursor,received,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have cardinality := constraintClaims_success_length (cpuAirs layout) pair.1 _ cursor summed received
  have caps := constraintClaims_success_caps (cpuAirs layout) pair.1 _ cursor summed
    (airLayoutsSize (cpuAirs layout)) (Nat.le_refl _) received
  unfold cpuAfterSummed at h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨_,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨columns,cursor,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  obtain ⟨packed,tail,accepted,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have packedCount := (flockClaims_success_layouts layout.flock cursor packed tail accepted).1
  have count := cpuAfterPacked_family_count layout pair.2 columns summed packed tail rest out
    (airLayoutsSize (cpuAirs layout)) (by intro t ht; exact ⟨(caps.2 t ht).1,(caps.2 t ht).2.2⟩) h
  simp only [cpuAirs,List.length_append,List.length_map] at cardinality
  simp only [List.length_zip,List.length_drop,packedCount] at count
  omega

theorem cpuPayload_success_family_count (layout : CpuLayout) (cost : OutputCosts)
    (tokens rest : List CallerToken) (out : List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim)
    (h : (cpuPayload layout cost tokens).result = some (out,rest)) :
    out.1.length = layout.flock.length+layout.bus.producers.length+layout.registers.length := by
  unfold cpuPayload at h
  obtain ⟨pair,cursor,accepted,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  have count := cpuPayloadBeforeExit_success_family_count layout tokens cursor pair accepted
  rcases pair with ⟨rings,columns⟩
  rw [charged_bind_result] at h
  obtain ⟨points,tail,_,h⟩ := FlockPolynomial.bind_success _ _ _ _ _ h
  change some ((rings,points),tail) = some (out,rest) at h
  cases h
  exact count

/-- Canonical literal-layout bound, with no external work or size certificate. -/
theorem cpuPayloadBeforeExit_work_literal_polynomial (layout : CpuLayout)
    (tokens : List CallerToken) :
    (cpuPayloadBeforeExit layout tokens).work ≤ cpuBeforeExitWork (cpuLayoutVolume layout) :=
  cpuPayloadBeforeExit_work_polynomial layout tokens _ (Nat.le_refl _)

/-- The mandatory surcharge is the sum of the four actually reached output
calls. Construction does not invoke the families' delayed slice closures. -/
theorem cpuPayload_work_literal_polynomial (layout : CpuLayout) (cost : OutputCosts)
    (tokens : List CallerToken) :
    (cpuPayload layout cost tokens).work ≤ cpuPayloadWorkPolynomial (cpuLayoutVolume layout)+
      ((outputGetterTrace layout tokens).map cost.call).sum := by
  rw [outputGetterTrace_cost]
  exact cpuPayload_work_polynomial layout cost tokens _ (Nat.le_refl _)

theorem cpuPayload_resource (layout : CpuLayout) (cost : OutputCosts) (tokens : List CallerToken) :
    (cpuPayload layout cost tokens).work ≤ cpuPayloadWorkPolynomial (cpuLayoutVolume layout)+
      ((outputGetterTrace layout tokens).map cost.call).sum ∧
    ∀ out rest, (cpuPayload layout cost tokens).result = some (out,rest) →
      out.1.length = layout.flock.length+layout.bus.producers.length+layout.registers.length ∧
      (∀ r ∈ out.1, r.point.size ≤ cpuLayoutVolume layout) ∧
      out.2.size ≤ 3*cpuLayoutVolume layout*cpuLayoutVolume layout+5 ∧
      (∀ p ∈ out.2.toList, cpuPointDimension p ≤ cpuLayoutVolume layout+6) := by
  refine ⟨cpuPayload_work_literal_polynomial layout cost tokens,?_⟩
  intro out rest accepted
  have caps := cpuPayload_success_caps layout cost tokens rest out _ (Nat.le_refl _) accepted
  exact ⟨cpuPayload_success_family_count layout cost tokens rest out accepted,caps.2⟩

#print axioms cpuPayloadBeforeExit_work_literal_polynomial
#print axioms cpuPayload_work_literal_polynomial
#print axioms cpuPayload_resource
#print axioms cpuPayloadBeforeExit_success_family_count
#print axioms cpuPayload_success_family_count
#print axioms cpuPayloadBeforeExit_normalized
#print axioms cpuSliceLoop_work
#print axioms cpuRegisterLoop_work
#print axioms cpuPayloadBeforeExit_work_polynomial
#print axioms cpuPayloadBeforeExit_success_caps
#print axioms cpuPayload_work_polynomial
#print axioms cpuPayload_success_caps
end Whir.PCSBCSCallerPayloadCost
