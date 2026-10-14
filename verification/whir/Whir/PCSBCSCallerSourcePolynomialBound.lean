import Whir.PCSBCSCallerPayloadPolynomialBound
import Whir.PCSBCSCallerSchedulePolynomialBound
import Whir.PCSBCSCallerCPUPolynomialBound

/-! Anchored source resource bounds in actual public metadata, placement word
volume, record coordinates and token lengths. Accessor prices stay explicit.
No theorem assumes the work of the parser it bounds. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace Whir.PCSBCSCallerPayloadCost
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec

/-- Public placement word volume is the source's sum of `2^dimension`, not a
reservation supplied by a caller. Including it accounts for the declared Nat
logarithm source-operation model in `shapeWork`. -/
def layoutPublicSize (layout : CallerLayout) : Nat :=
  1+layoutVolume layout+callerWords layout+callerMu layout

def recordPublicSize (saved : Record) : Nat :=
  1+saved.context.pendingBytes+saved.point.length

def freshPublicSize (layout : CallerLayout) (saved : Record) (tokens : List CallerToken) : Nat :=
  layoutVolume layout+recordPublicSize saved+tokens.length

private theorem summand_le {A : Type} (xs : List A) (f : A → Nat)
    (x : A) (member : x ∈ xs) : f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    simp only [List.mem_cons] at member
    simp only [List.map_cons,List.sum_cons]
    rcases member with rfl | member
    · omega
    · exact (ih member).trans (Nat.le_add_left _ _)

theorem placement_volume_le (layout : CallerLayout) :
    placementsVolume (callerPlacements layout) ≤ layoutVolume layout := by
  cases layout with
  | recursion l => exact (recLayoutVolume_components l).2.2.2.2
  | cpu l => exact (cpuLayoutVolume_components l).2.2.2.2.1

theorem shapeWork_polynomial (layout : CallerLayout) (size : Nat)
    (volume : layoutPublicSize layout ≤ size) :
    shapeWork layout ≤ 9*size^2+20*size+35 := by
  have placement := placement_volume_le layout
  have components : layoutVolume layout ≤ size ∧ callerWords layout ≤ size ∧ callerMu layout ≤ size := by
    unfold layoutPublicSize at volume
    omega
  have count : (callerPlacements layout).size ≤ size := by
    unfold placementsVolume at placement
    omega
  have dims : ∀ p ∈ (callerPlacements layout).toList, ∀ o d,
      p = .committed o d → d ≤ size := by
    intro p member o d equal
    subst p
    have memberVolume := summand_le (callerPlacements layout).toList placementVolume (.committed o d) member
    simp only [placementVolume] at memberVolume
    unfold placementsVolume at placement
    omega
  have words := wordsWork_le layout size dims
  have product := Nat.mul_le_mul_left (3*size+5) count
  have positive : 1 ≤ size := by
    unfold layoutPublicSize at volume
    omega
  unfold shapeWork
  nlinarith [Nat.sub_le (max (callerWords layout) 1) 1,
    Nat.sub_le (callerMu layout) 6,Nat.max_le.mpr ⟨components.2.1,positive⟩]

private theorem source_bind_bound {A B : Type} (p : PCSBCSCallerParserCost.Parser A)
    (f : A → PCSBCSCallerParserCost.Parser B) (ts : List CallerToken)
    (m n total : Nat) (sum : m+n ≤ total) (hp : (p ts).work ≤ m)
    (hf : ∀ a rest, (p ts).result = some (a,rest) → (f a rest).work ≤ n) :
    ((p >>= f) ts).work ≤ total :=
  (PCSBCSCallerParserCost.bind_work_le p f ts m n hp hf).trans sum

local macro "source_bind " m:term "," n:term : tactic =>
  `(tactic| (apply source_bind_bound _ _ _ $m $n; · first | omega | nlinarith))

private theorem source_tick_bound {A : Type} (n : Nat) (parser : PCSBCSCallerParserCost.Parser A)
    (ts : List CallerToken) (cap total : Nat) (sum : n+cap ≤ total)
    (bound : (parser ts).work ≤ cap) :
    ((PCSBCSCallerParserCost.tick n >>= fun _ => parser) ts).work ≤ total := by
  rw [PCSBCSCallerParserCost.tick_bind_work]
  exact (Nat.add_le_add_left bound n).trans sum

local macro "source_tick " n:term : tactic =>
  `(tactic| (apply source_tick_bound _ _ _ $n; · first | omega | nlinarith))

theorem readAnnouncements_work_le (heights : List Nat) (tokens : List CallerToken) :
    (readAnnouncements heights tokens).work ≤ 13*heights.length+1 := by
  induction heights generalizing tokens with
  | nil => simp [readAnnouncements,PCSBCSCallerParserCost.tick]
  | cons height heights ih =>
    simp only [List.length_cons]
    unfold readAnnouncements
    source_tick (13*heights.length+13)
    source_bind 4, (13*heights.length+9)
    · exact PCSBCSCallerParserCost.readScalar_work_le tokens
    · intro scalar rest read
      source_tick (13*heights.length+4)
      source_bind 3, (13*heights.length+1)
      · exact PCSBCSCallerParserCost.check_work_le _ _
      · intro unused tail checked
        exact ih tail

theorem prelude_work_polynomial (layout : CallerLayout) (tokens : List CallerToken)
    (size : Nat) (volume : layoutVolume layout ≤ size) :
    (prelude layout tokens).work ≤ 17*size+169 := by
  cases layout with
  | recursion l =>
    simp [prelude,PCSBCSCallerParserCost.tick]
  | cpu l =>
    have count := (cpuLayoutVolume_components l).2.2.1.trans volume
    have detailed : (prelude (.cpu l) tokens).work ≤ 17*l.tables.length+169 := by
      unfold prelude
      source_tick (16*l.tables.length+166)
      source_bind 3, (16*l.tables.length+163)
      · exact PCSBCSCallerParserCost.check_work_le _ _
      · intro unused rest checked
        unfold charged
        simp only [bind_assoc,pure_bind]
        source_tick (13*l.tables.length+161)
        source_bind (13*(l.tables.length+1)+1), 147
        · simpa only [List.length_append,List.length_map,List.length_cons,List.length_nil,
            Nat.add_zero] using readAnnouncements_work_le
              (l.tables.map CpuTableLayout.tau++[l.logInvRate]) rest
        · intro unused tail checked
          source_bind 4, 143
          · exact PCSBCSCallerParserCost.readScalar_work_le tail
          · intro clock suffix checked
            have clockCost : 3+(if clock.c1==0 then 3+
                (if clock.c2==0 then 125+(if clock.c0.toNat/2^40==1 then 4 else 0)
                 else 0) else 0) ≤ 135 := by
              repeat' first | split | omega
            source_tick 3
            exact PCSBCSCallerParserCost.check_work_le _ _
    nlinarith

theorem receive_work_local (layout : CallerLayout) (original : Context) (tokens : List CallerToken) :
    (receive layout original tokens).work ≤ 4*shapeWork layout+9*callerMu layout+156 := by
  have valid : shapeValidWork (AnchoredSourceCaller.shape layout) ≤ 42 := by
    simpa only [AnchoredSourceCaller.shape] using shapeValidWork_le (AnchoredSourceCaller.shape layout)
  unfold receive
  source_tick (3*shapeWork layout+9*callerMu layout+114)
  source_bind 3, (3*shapeWork layout+9*callerMu layout+111)
  · exact PCSBCSCallerParserCost.check_work_le _ _
  · intro unused rest checked
    source_bind 47, (3*shapeWork layout+9*callerMu layout+64)
    · exact PCSBCSCallerParserCost.readScalars_work_le 5 rest
    · intro header tail received
      have headerCost := headerWork_le (AnchoredSourceCaller.shape layout) header
      source_tick (2*shapeWork layout+9*callerMu layout+10)
      cases parsed : parseHeader (AnchoredSourceCaller.shape layout) header with
      | none =>
        simp [PCSBCSCallerParserCost.liftOption]
      | some root =>
        source_tick (shapeWork layout+9*callerMu layout+9)
        source_bind (9*callerMu layout+2), (shapeWork layout+7)
        · exact PCSBCSCallerParserCost.drawScalars_work_le _ _
        · intro point remaining sampled
          source_bind 4, (shapeWork layout+3)
          · exact PCSBCSCallerParserCost.readScalar_work_le remaining
          · intro value suffix read
            source_tick 0
            exact (PCSBCSCallerParserCost.pure_work _ _).le

theorem receive_work_polynomial (layout : CallerLayout) (original : Context)
    (tokens : List CallerToken) (size : Nat) (volume : layoutPublicSize layout ≤ size) :
    (receive layout original tokens).work ≤ 36*size^2+89*size+300 := by
  have work := receive_work_local layout original tokens
  have shape := shapeWork_polynomial layout size volume
  have dimension : callerMu layout ≤ size := by
    unfold layoutPublicSize at volume
    omega
  nlinarith

theorem receive_success_fields (layout : CallerLayout) (original : Context)
    (tokens rest : List CallerToken) (record : Record)
    (accepted : (receive layout original tokens).result = some (record,rest)) :
    record.context = original ∧ record.point.length = callerMu layout := by
  unfold receive at accepted
  by_cases valid : decide (AnchoredSourceCaller.shape layout).Valid = true
  · simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      PCSBCSCallerParserCost.check,valid,ite_true] at accepted
    cases headerRead : (PCSBCSCallerParserCost.readScalars 5 tokens).result with
    | none => simp [headerRead] at accepted
    | some pair =>
      rcases pair with ⟨header,tail⟩
      rw [headerRead] at accepted
      dsimp only at accepted
      cases parsed : parseHeader (AnchoredSourceCaller.shape layout) header with
      | none => simp [parsed,PCSBCSCallerParserCost.liftOption] at accepted
      | some root =>
        rw [parsed] at accepted
        dsimp only [PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick] at accepted
        cases draw : (PCSBCSCallerParserCost.drawScalars (AnchoredSourceCaller.shape layout).logN tail).result with
        | none => simp [draw] at accepted
        | some pair =>
          rcases pair with ⟨point,remaining⟩
          have pointLength := PCSBCSCallerParserCost.drawScalars_success_length _ _ _ _ draw
          rw [draw] at accepted
          dsimp only [PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick] at accepted
          cases read : (PCSBCSCallerParserCost.readScalar remaining).result with
          | none => simp [read] at accepted
          | some pair =>
            rcases pair with ⟨value,suffix⟩
            simp only [read,Pure.pure,PCSBCSCallerParserCost.pure,
              Option.some.injEq,Prod.mk.injEq] at accepted
            rcases accepted with ⟨rfl,rfl⟩
            exact ⟨rfl,pointLength⟩
  · simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
      PCSBCSCallerParserCost.check,valid] at accepted

theorem freshSourceClaims_work_local (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (tokens : List CallerToken) :
    (freshSourceClaims layout saved cost tokens).work ≤
      (payload layout cost tokens).work+108*recordPublicSize saved+1450+
        2*openingGetterWork saved cost := by
  unfold freshSourceClaims
  source_bind (payload layout cost tokens).work,
    (108*recordPublicSize saved+1450+2*openingGetterWork saved cost)
  · exact Nat.le_refl _
  · intro pair tail parsed
    rcases pair with ⟨families,points⟩
    source_bind (108*recordPublicSize saved+1447+2*openingGetterWork saved cost), 3
    · have bound := binding_polynomial saved cost tail
      unfold recordPublicSize
      omega
    · intro unused rest checked
      source_tick 0
      exact (PCSBCSCallerParserCost.pure_work _ _).le

theorem freshInterpret_work_local (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (tokens : List CallerToken) :
    (freshInterpret layout saved cost tokens).work ≤
      (payload layout cost tokens).work+(callerShape layout).work+
        8*(callerShape layout).value.length+875*tokens.length+
        159*recordPublicSize saved+2153+3*openingGetterWork saved cost := by
  have composite := freshInterpret_compositional_bound layout saved cost tokens
  have fresh := freshSourceClaims_work_local layout saved cost tokens
  have opening := openingWork_polynomial saved
  have length := openingScalars_length saved
  have packs : (saved.context.pendingBytes+23)/24 ≤ saved.context.pendingBytes+1 := by omega
  unfold recordPublicSize
  unfold recordPublicSize at fresh
  omega

#print axioms freshSourceClaims_work_local
#print axioms freshInterpret_work_local

theorem freshCallerShape_work_polynomial (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (size : Nat) (volume : layoutVolume layout ≤ size)
    (recordVolume : recordPublicSize saved ≤ size) :
    (freshCallerShape layout saved cost).work ≤
      30000*(size+1)^4+46*size+647+openingGetterWork saved cost := by
  have record : saved.context.pendingBytes+saved.point.length+1 ≤ size := by
    unfold recordPublicSize at recordVolume
    omega
  exact (freshCallerShape_resource_volume layout saved cost size volume record).1

/-- The fee of actual reached CPU getter applications, without evaluating an
output getter while constructing the trace. -/
def payloadGetterPrice (layout : CallerLayout) (cost : OutputCosts) (tokens : List CallerToken) : Nat :=
  (⟨freshOutputGetterTrace layout tokens,[],[],[]⟩ : GetterTrace).price cost

theorem payload_getter_work (layout : CallerLayout) (cost : OutputCosts) (tokens : List CallerToken) :
    (payload layout cost tokens).work = (payload layout OutputCosts.zero tokens).work+
      payloadGetterPrice layout cost tokens := by
  cases layout with
  | recursion l =>
    simp [payload,payloadGetterPrice,freshOutputGetterTrace,GetterTrace.price]
  | cpu l =>
    have work := cpuPayload_output_work l cost tokens
    have zero : cpuPayload l {cost with call := fun _ => 0} = cpuPayload l OutputCosts.zero := rfl
    rw [zero] at work
    have tracePrice : payloadGetterPrice (.cpu l) cost tokens =
        if (cpuPayloadBeforeExit l tokens).result.isSome then cost.total else 0 := by
      simp [payloadGetterPrice,GetterTrace.price,freshOutputGetterTrace,outputGetterTrace,
        OutputCosts.total,List.finRange]
      split <;> simp_all
    simpa only [payload,tracePrice] using work

private theorem payload_result_prices (layout : CallerLayout) (cost : OutputCosts)
    (tokens : List CallerToken) :
    (payload layout cost tokens).result = (payload layout OutputCosts.zero tokens).result := by
  have a := congrFun (payload_erasure layout cost) tokens
  have b := congrFun (payload_erasure layout OutputCosts.zero) tokens
  exact a.trans b.symm

private theorem binding_result_prices (saved : Record) (cost : OutputCosts) (tokens : List CallerToken) :
    (binding saved cost tokens).result = (binding saved OutputCosts.zero tokens).result := by
  have a := congrFun (binding_erasure saved cost) tokens
  have b := congrFun (binding_erasure saved OutputCosts.zero) tokens
  exact a.trans b.symm

theorem freshSourceClaims_getter_work (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (tokens : List CallerToken) :
    (freshSourceClaims layout saved cost tokens).work =
      (freshSourceClaims layout saved OutputCosts.zero tokens).work+
        (freshSourceClaimsGetterTrace layout saved tokens).price cost := by
  have payloadWork := payload_getter_work layout cost tokens
  have same := payload_result_prices layout cost tokens
  have cursor := payloadPendingCursor_erasure layout cost tokens
  cases parsed : (payload layout cost tokens).result with
  | none =>
    have base : (payload layout OutputCosts.zero tokens).result = none := same.symm.trans parsed
    have noCursor : payloadPendingCursor layout tokens = none := by simp [cursor,parsed]
    simp only [freshSourceClaims,Bind.bind,PCSBCSCallerParserCost.bind,parsed,base,
      freshSourceClaimsGetterTrace,noCursor]
    exact payloadWork
  | some pair =>
    rcases pair with ⟨⟨families,points⟩,tail⟩
    have base : (payload layout OutputCosts.zero tokens).result = some ((families,points),tail) :=
      same.symm.trans parsed
    have someCursor : payloadPendingCursor layout tokens = some tail := by simp [cursor,parsed]
    have bindingWork := binding_getter_work saved cost tail
    have bindingSame := binding_result_prices saved cost tail
    cases checked : (binding saved cost tail).result with
    | none =>
      have baseChecked : (binding saved OutputCosts.zero tail).result = none :=
        bindingSame.symm.trans checked
      simp only [freshSourceClaims,Bind.bind,PCSBCSCallerParserCost.bind,parsed,base,
        checked,baseChecked,freshSourceClaimsGetterTrace,someCursor,GetterTrace.price_append]
      unfold payloadGetterPrice at payloadWork
      omega
    | some pair =>
      rcases pair with ⟨unused,rest⟩
      have baseChecked : (binding saved OutputCosts.zero tail).result = some (unused,rest) :=
        bindingSame.symm.trans checked
      simp only [freshSourceClaims,Bind.bind,PCSBCSCallerParserCost.bind,parsed,base,
        checked,baseChecked,PCSBCSCallerParserCost.tick,
        freshSourceClaimsGetterTrace,someCursor,GetterTrace.price_append]
      unfold payloadGetterPrice at payloadWork
      omega

theorem freshCallerShape_getter_work (layout : CallerLayout) (saved : Record) (cost : OutputCosts) :
    (freshCallerShape layout saved cost).work =
      (freshCallerShape layout saved OutputCosts.zero).work+openingGetterWork saved cost := by
  have zero : openingGetterWork saved OutputCosts.zero = 0 := by
    rw [←openingGetterTrace_price]
    simp
  simp only [freshCallerShape,zero]
  omega

theorem freshInterpret_getter_work (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (tokens : List CallerToken) :
    (freshInterpret layout saved cost tokens).work =
      (freshInterpret layout saved OutputCosts.zero tokens).work+
        (freshInterpretGetterTrace layout saved tokens).price cost := by
  have expectedWork := freshCallerShape_getter_work layout saved cost
  have sourceWork := freshSourceClaims_getter_work layout saved cost tokens
  have same : (freshSourceClaims layout saved cost tokens).result =
      (freshSourceClaims layout saved OutputCosts.zero tokens).result := by
    have a := congrFun (freshSourceClaims_erasure layout saved cost) tokens
    have b := congrFun (freshSourceClaims_erasure layout saved OutputCosts.zero) tokens
    exact a.trans b.symm
  by_cases matched : WHIRCallerClaims.tokensShape tokens =
      AnchoredSourceFreshCaller.callerShape layout saved
  · cases parsed : (freshSourceClaims layout saved cost tokens).result with
    | none =>
      have base : (freshSourceClaims layout saved OutputCosts.zero tokens).result = none := same.symm.trans parsed
      simp [freshInterpret,matched,parsed,base,freshInterpretGetterTrace,
        freshShapeForTrace_erasure,openingGetterTrace_price] 
      omega
    | some pair =>
      rcases pair with ⟨claims,rest⟩
      have base : (freshSourceClaims layout saved OutputCosts.zero tokens).result = some (claims,rest) :=
        same.symm.trans parsed
      cases remaining : rest.isEmpty <;>
        simp [freshInterpret,matched,parsed,base,remaining,freshInterpretGetterTrace,
          freshShapeForTrace_erasure,openingGetterTrace_price] <;> omega
  · simp [freshInterpret,matched,freshInterpretGetterTrace,
      freshShapeForTrace_erasure,openingGetterTrace_price]
    omega

#print axioms freshCallerShape_getter_work
#print axioms freshInterpret_getter_work

private def sourcePrefix (layout : CallerLayout) (original : Context) :
    PCSBCSCallerParserCost.Parser Record := do
  prelude layout
  receive layout original

private theorem sourceClaims_normalized (layout : CallerLayout) (original : Context) (cost : OutputCosts) :
    sourceClaims layout original cost =
      (sourcePrefix layout original >>= fun record => freshSourceClaims layout record cost) := by
  simp only [sourceClaims,sourcePrefix,freshSourceClaims,bind_assoc]

/-- Prelude/header/point reception invokes no opaque accessor: returning the
immutable record is not evaluation of its byte or pending-word functions. -/
def sourceClaimsGetterTrace (layout : CallerLayout) (original : Context)
    (tokens : List CallerToken) : GetterTrace :=
  match (sourcePrefix layout original tokens).result with
  | none => .empty
  | some (record,rest) => freshSourceClaimsGetterTrace layout record rest

theorem sourceClaims_getter_work (layout : CallerLayout) (original : Context)
    (cost : OutputCosts) (tokens : List CallerToken) :
    (sourceClaims layout original cost tokens).work =
      (sourceClaims layout original OutputCosts.zero tokens).work+
        (sourceClaimsGetterTrace layout original tokens).price cost := by
  rw [sourceClaims_normalized,sourceClaims_normalized]
  cases parsed : (sourcePrefix layout original tokens).result with
  | none =>
    simp [Bind.bind,PCSBCSCallerParserCost.bind,parsed,
      sourceClaimsGetterTrace,GetterTrace.empty,GetterTrace.price]
  | some pair =>
    rcases pair with ⟨record,rest⟩
    have work := freshSourceClaims_getter_work layout record cost rest
    simp only [Bind.bind,PCSBCSCallerParserCost.bind,parsed,sourceClaimsGetterTrace]
    omega

#print axioms sourceClaims_getter_work

/-- Sum of the two proven concrete branch polynomials, not a parser reserve.
Each constituent is derived from actual successful-state geometry and failed
prefix work of the literal counted interpreter. -/
def payloadWorkPolynomial (size : Nat) : Nat :=
  cpuPayloadWorkPolynomial size+PCSBCSCallerParserCost.busClaimsWork size+
    100*(size+1)^3*size+6*size^3+79*size^2+874*size+738

def freshSourceWorkPolynomial (size : Nat) : Nat :=
  payloadWorkPolynomial size+108*size+1450

def freshInterpretWorkPolynomial (size : Nat) : Nat :=
  payloadWorkPolynomial size+90000*(size+1)^4+1034*size+2153

def sourceWorkPolynomial (size : Nat) : Nat :=
  payloadWorkPolynomial size+36*size^2+214*size+1919

theorem payload_zero_work_polynomial (layout : CallerLayout) (tokens : List CallerToken)
    (size : Nat) (volume : layoutVolume layout ≤ size) :
    (payload layout OutputCosts.zero tokens).work ≤ payloadWorkPolynomial size := by
  cases layout with
  | recursion l =>
    have bound := recPayload_work_polynomial l tokens size volume
    change (recPayload l tokens).work ≤ _
    unfold payloadWorkPolynomial
    omega
  | cpu l =>
    have bound := cpuPayload_work_polynomial l OutputCosts.zero tokens size volume
    have total : OutputCosts.zero.total = 0 := by
      simp [OutputCosts.total,OutputCosts.zero]
    simp only [total,ite_self,Nat.add_zero] at bound
    change (cpuPayload l OutputCosts.zero tokens).work ≤ _
    unfold payloadWorkPolynomial
    omega

theorem payload_work_polynomial (layout : CallerLayout) (cost : OutputCosts)
    (tokens : List CallerToken) (size : Nat) (volume : layoutVolume layout ≤ size) :
    (payload layout cost tokens).work ≤ payloadWorkPolynomial size+payloadGetterPrice layout cost tokens := by
  rw [payload_getter_work]
  exact Nat.add_le_add_right (payload_zero_work_polynomial layout tokens size volume) _

theorem freshSourceClaims_zero_work_polynomial (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) (size : Nat) (volume : layoutVolume layout ≤ size)
    (recordVolume : recordPublicSize saved ≤ size) :
    (freshSourceClaims layout saved OutputCosts.zero tokens).work ≤ freshSourceWorkPolynomial size := by
  have work := freshSourceClaims_work_local layout saved OutputCosts.zero tokens
  have payload := payload_zero_work_polynomial layout tokens size volume
  have zero : openingGetterWork saved OutputCosts.zero = 0 := by
    rw [←openingGetterTrace_price]
    simp
  rw [zero] at work
  unfold freshSourceWorkPolynomial
  omega

theorem freshSourceClaims_work_polynomial (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (tokens : List CallerToken) (size : Nat)
    (volume : layoutVolume layout ≤ size) (recordVolume : recordPublicSize saved ≤ size) :
    (freshSourceClaims layout saved cost tokens).work ≤ freshSourceWorkPolynomial size+
      (freshSourceClaimsGetterTrace layout saved tokens).price cost := by
  rw [freshSourceClaims_getter_work]
  exact Nat.add_le_add_right (freshSourceClaims_zero_work_polynomial layout saved tokens size volume recordVolume) _

theorem freshInterpret_zero_work_polynomial (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) (size : Nat) (volume : layoutVolume layout ≤ size)
    (recordVolume : recordPublicSize saved ≤ size) (tokenVolume : tokens.length ≤ size) :
    (freshInterpret layout saved OutputCosts.zero tokens).work ≤ freshInterpretWorkPolynomial size := by
  have work := freshInterpret_work_local layout saved OutputCosts.zero tokens
  have payload := payload_zero_work_polynomial layout tokens size volume
  have schedules := callerShape_resource layout size volume
  have zero : openingGetterWork saved OutputCosts.zero = 0 := by
    rw [←openingGetterTrace_price]
    simp
  rw [zero] at work
  unfold freshInterpretWorkPolynomial
  omega

/-- Fresh interpretation never runs `receive`/`shapeWork`. Its resource bound
therefore needs only literal layout metadata, immutable record/public token
lengths, and exact reached callback prices—not committed word volume. -/
theorem freshInterpret_work_polynomial (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (tokens : List CallerToken) (size : Nat)
    (volume : layoutVolume layout ≤ size) (recordVolume : recordPublicSize saved ≤ size)
    (tokenVolume : tokens.length ≤ size) :
    (freshInterpret layout saved cost tokens).work ≤ freshInterpretWorkPolynomial size+
      (freshInterpretGetterTrace layout saved tokens).price cost := by
  rw [freshInterpret_getter_work]
  exact Nat.add_le_add_right
    (freshInterpret_zero_work_polynomial layout saved tokens size volume recordVolume tokenVolume) _

/-- Original reception prices the source's literal committed-word volume in
`shapeWork`: this is not a polynomial claim in only compact dimension bits. -/
theorem sourceClaims_zero_work_polynomial (layout : CallerLayout) (original : Context)
    (tokens : List CallerToken) (size : Nat) (volume : layoutPublicSize layout ≤ size)
    (recordVolume : original.pendingBytes+callerMu layout+1 ≤ size) :
    (sourceClaims layout original OutputCosts.zero tokens).work ≤ sourceWorkPolynomial size := by
  have metadata : layoutVolume layout ≤ size := by
    unfold layoutPublicSize at volume
    omega
  unfold sourceClaims sourceWorkPolynomial
  source_bind (17*size+169), (payloadWorkPolynomial size+36*size^2+197*size+1750)
  · exact prelude_work_polynomial layout tokens size metadata
  · intro unused rest checked
    source_bind (36*size^2+89*size+300), (payloadWorkPolynomial size+108*size+1450)
    · exact receive_work_polynomial layout original rest size volume
    · intro record tail received
      have fields := receive_success_fields layout original rest tail record received
      have recordCap : recordPublicSize record ≤ size := by
        unfold recordPublicSize
        rw [fields.1,fields.2]
        omega
      exact freshSourceClaims_zero_work_polynomial layout record tail size metadata recordCap

theorem sourceClaims_work_polynomial (layout : CallerLayout) (original : Context)
    (cost : OutputCosts) (tokens : List CallerToken) (size : Nat)
    (volume : layoutPublicSize layout ≤ size)
    (recordVolume : original.pendingBytes+callerMu layout+1 ≤ size) :
    (sourceClaims layout original cost tokens).work ≤ sourceWorkPolynomial size+
      (sourceClaimsGetterTrace layout original tokens).price cost := by
  rw [sourceClaims_getter_work]
  exact Nat.add_le_add_right
    (sourceClaims_zero_work_polynomial layout original tokens size volume recordVolume) _

/-- Canonical closed bound on actual public input sizes: no caller-supplied
parser work bound, operation certificate, or reservation is a premise. -/
theorem freshInterpret_work_actual_sizes (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (tokens : List CallerToken) :
    (freshInterpret layout saved cost tokens).work ≤
      freshInterpretWorkPolynomial (freshPublicSize layout saved tokens)+
        (freshInterpretGetterTrace layout saved tokens).price cost := by
  apply freshInterpret_work_polynomial
  · unfold freshPublicSize; omega
  · unfold freshPublicSize; omega
  · unfold freshPublicSize; omega

#print axioms freshInterpret_work_actual_sizes

#print axioms payload_work_polynomial
#print axioms freshSourceClaims_work_polynomial
#print axioms freshInterpret_work_polynomial
#print axioms sourceClaims_work_polynomial

#print axioms payload_getter_work
#print axioms freshSourceClaims_getter_work

#print axioms receive_success_fields

#print axioms shapeWork_polynomial
#print axioms prelude_work_polynomial
#print axioms receive_work_polynomial

end Whir.PCSBCSCallerPayloadCost
