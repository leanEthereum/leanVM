import Whir.PCSBCSCallerPayloadCost
import Whir.PCSBCSCallerBusTablePolynomialBound
import Whir.PCSBCSCallerFlockPolynomialBound

/-! Literal public-layout volume and deterministic resource bounds. Numeric
metadata contributes by value. These are bounds on the declared reached source
operations, not machine timing; arbitrary accessor prices remain explicit. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace Whir.PCSBCSCallerPayloadCost
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec

private theorem bind_bound {A B : Type} (p : PCSBCSCallerParserCost.Parser A)
    (f : A → PCSBCSCallerParserCost.Parser B) (ts : List CallerToken)
    (m n total : Nat) (sum : m+n ≤ total) (hp : (p ts).work ≤ m)
    (hf : ∀ a rest, (p ts).result = some (a,rest) → (f a rest).work ≤ n) :
    ((p >>= f) ts).work ≤ total :=
  (PCSBCSCallerParserCost.bind_work_le p f ts m n hp hf).trans sum

private theorem tick_bound {A : Type} (n : Nat) (p : PCSBCSCallerParserCost.Parser A)
    (ts : List CallerToken) (cap total : Nat) (sum : n+cap ≤ total)
    (hp : (p ts).work ≤ cap) :
    ((PCSBCSCallerParserCost.tick n >>= fun _ => p) ts).work ≤ total := by
  rw [PCSBCSCallerParserCost.tick_bind_work]
  exact (Nat.add_le_add_left hp n).trans sum

local macro "payload_bind " m:term "," n:term : tactic =>
  `(tactic| (apply bind_bound _ _ _ $m $n; · first | omega | nlinarith))
local macro "payload_tick " n:term : tactic =>
  `(tactic| (apply tick_bound _ _ _ $n; · first | omega | nlinarith))

def placementVolume : Placement → Nat
  | .committed offset dimension => 1+offset+dimension
  | .port offset slot stride => 1+offset+slot+stride
  | .sliced => 1

def placementsVolume (placements : Array Placement) : Nat :=
  1+placements.size+(placements.toList.map placementVolume).sum

def cpuTableVolume (table : CpuTableLayout) : Nat :=
  1+table.base+table.tau+table.committedColumns+table.summedColumns.length+
    table.summedColumns.sum+(table.summedBits.map (fun f => 1+f.column+f.width)).sum

def registerVolume (word : RegisterWord) : Nat :=
  1+word.offset+word.tables.length+word.tables.sum

def recLayoutVolume (layout : RecLayout) : Nat :=
  1+PCSBCSCallerParserCost.busLayoutSize layout.bus+
    PCSBCSCallerParserCost.airLayoutsSize (layout.tables.map Prod.snd)+
    layout.tables.length+(layout.tables.map Prod.fst).sum+
    placementsVolume layout.placements+
    PCSBCSCallerParserCost.flockConfigurationSize [layout.hash]+layout.logInvRate

def cpuAirs (layout : CpuLayout) : List AirLayout :=
  layout.tables.map CpuTableLayout.air ++
    layout.bus.producers.map (fun p => (⟨p.kappa,2*p.bits,p.bits,[]⟩ : AirLayout))

def cpuLayoutVolume (layout : CpuLayout) : Nat :=
  1+PCSBCSCallerParserCost.busLayoutSize layout.bus+
    PCSBCSCallerParserCost.airLayoutsSize (cpuAirs layout)+
    layout.tables.length+(layout.tables.map cpuTableVolume).sum+
    placementsVolume layout.placements+
    PCSBCSCallerParserCost.flockConfigurationSize layout.flock+
    layout.registers.length+(layout.registers.map registerVolume).sum+
    layout.finalRegisterColumn+layout.logInvRate

def layoutVolume : CallerLayout → Nat
  | .recursion l => recLayoutVolume l
  | .cpu l => cpuLayoutVolume l

private theorem member_sum_le {A : Type} (xs : List A) (f : A → Nat)
    (x : A) (member : x ∈ xs) : f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    simp only [List.mem_cons] at member
    simp only [List.map_cons,List.sum_cons]
    rcases member with rfl | member
    · omega
    · exact (ih member).trans (Nat.le_add_left _ _)

theorem recLayoutVolume_components (l : RecLayout) :
    PCSBCSCallerParserCost.busLayoutSize l.bus ≤ recLayoutVolume l ∧
    PCSBCSCallerParserCost.airLayoutsSize (l.tables.map Prod.snd) ≤ recLayoutVolume l ∧
    l.tables.length ≤ recLayoutVolume l ∧
    PCSBCSCallerParserCost.flockConfigurationSize [l.hash] ≤ recLayoutVolume l ∧
    placementsVolume l.placements ≤ recLayoutVolume l := by
  unfold recLayoutVolume
  omega

theorem cpuLayoutVolume_components (l : CpuLayout) :
    PCSBCSCallerParserCost.busLayoutSize l.bus ≤ cpuLayoutVolume l ∧
    PCSBCSCallerParserCost.airLayoutsSize (cpuAirs l) ≤ cpuLayoutVolume l ∧
    l.tables.length ≤ cpuLayoutVolume l ∧
    PCSBCSCallerParserCost.flockConfigurationSize l.flock ≤ cpuLayoutVolume l ∧
    placementsVolume l.placements ≤ cpuLayoutVolume l ∧
    l.registers.length ≤ cpuLayoutVolume l := by
  unfold cpuLayoutVolume
  omega

theorem column_geometry (bus : List ColumnClaim) (paired : List (Nat × TableClaims))
    (size : Nat) (busLength : bus.length ≤ 2*size*size)
    (busPoints : ∀ c ∈ bus, c.point.length ≤ size)
    (pairedLength : paired.length ≤ size)
    (tables : ∀ p ∈ paired, p.2.point.length ≤ size ∧ p.2.evals.length ≤ size) :
    (bus ++ paired.flatMap (fun p => WHIRCallerClaims.tableColumns p.1 p.2)).length ≤ 3*size*size ∧
    ∀ c ∈ bus ++ paired.flatMap (fun p => WHIRCallerClaims.tableColumns p.1 p.2),
      c.point.length ≤ size := by
  constructor
  · have total := sumMap_le paired
      (fun p => (WHIRCallerClaims.tableColumns p.1 p.2).length) size (by
        intro p hp
        have count := PCSBCSCallerParserCost.tableColumns_length p.1 p.2
        rw [PCSBCSCallerParserCost.tableColumns_erasure] at count
        exact count.trans_le (tables p hp).2)
    simp only [List.length_append,List.length_flatMap]
    nlinarith
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact busPoints c hc
    · obtain ⟨p,hp,hc⟩ := List.mem_flatMap.mp hc
      have point := PCSBCSCallerParserCost.tableColumns_point p.1 p.2 c
      rw [PCSBCSCallerParserCost.tableColumns_erasure] at point
      rw [point hc]
      exact (tables p hp).1

private def recFinish (l : RecLayout) (bus : List ColumnClaim) (tables : List TableClaims)
    (rings : List RingPCSGame.FamilyClaim) :
    PCSBCSCallerParserCost.Parser (List RingPCSGame.FamilyClaim × Array RingPCSGame.PointClaim) := do
  let paired := (l.tables.map Prod.fst).zip tables
  let columns ← charged (3*l.tables.length+1+4*min l.tables.length tables.length+1+
    columnsWork bus paired)
    (bus ++ paired.flatMap (fun p => WHIRCallerClaims.tableColumns p.1 p.2))
  let placed := PCSBCSCallerParserCost.placeClaims l.placements columns
  let points ← PCSBCSCallerParserCost.liftOption placed.work placed.value
  pure (rings,points)

private theorem recFinish_work_le (l : RecLayout) (bus : List ColumnClaim)
    (tables : List TableClaims) (rings : List RingPCSGame.FamilyClaim)
    (tokens : List CallerToken) (size : Nat)
    (layout : l.tables.length ≤ size)
    (busLength : bus.length ≤ 2*size*size)
    (busPoints : ∀ c ∈ bus, c.point.length ≤ size)
    (tableCaps : ∀ c ∈ tables, c.point.length ≤ size ∧ c.evals.length ≤ size) :
    (recFinish l bus tables rings tokens).work ≤
      6*size^3+57*size^2+13*size+10 := by
  let paired := (l.tables.map Prod.fst).zip tables
  have length : paired.length ≤ size := by
    simp only [paired,List.length_zip,List.length_map]
    exact (Nat.min_le_left _ _).trans layout
  have caps : ∀ p ∈ paired, p.2.point.length ≤ size ∧ p.2.evals.length ≤ size := by
    intro p hp
    have ht := (List.of_mem_zip hp).2
    exact tableCaps p.2 ht
  have geometry := column_geometry bus paired size busLength busPoints length caps
  have construction := columnsWork_le bus paired size (fun p hp => (caps p hp).2)
  have placed := PCSBCSCallerParserCost.placeClaims_work_le l.placements
    (bus ++ paired.flatMap (fun p => WHIRCallerClaims.tableColumns p.1 p.2)) size geometry.2
  have placedProduct := Nat.mul_le_mul_right (2*size+15) geometry.1
  have constructionProduct := Nat.mul_le_mul_right (8*size+4) length
  dsimp only [paired] at construction geometry placed placedProduct constructionProduct
  unfold recFinish charged
  simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
    Pure.pure,PCSBCSCallerParserCost.pure,PCSBCSCallerParserCost.liftOption]
  cases (PCSBCSCallerParserCost.placeClaims l.placements
      (bus ++ paired.flatMap (fun p => WHIRCallerClaims.tableColumns p.1 p.2))).value <;>
    simp only [Option.map_none,Option.map_some,Nat.add_zero] <;>
    nlinarith [Nat.min_le_left l.tables.length tables.length]

theorem recPayload_work_polynomial (l : RecLayout) (tokens : List CallerToken)
    (size : Nat) (volume : recLayoutVolume l ≤ size) :
    (recPayload l tokens).work ≤
      PCSBCSCallerParserCost.busClaimsWork size+
      100*(size+1)^3*size+6*size^3+79*size^2+874*size+738 := by
  have components := recLayoutVolume_components l
  have busConfig := components.1.trans volume
  have airConfig := components.2.1.trans volume
  have count := components.2.2.1.trans volume
  have flockConfig := components.2.2.2.1.trans volume
  unfold recPayload
  change ((do
    let pair ← PCSBCSCallerParserCost.busClaims l.bus
    let _ ← PCSBCSCallerParserCost.drawScalar
    let airs ← charged (3*l.tables.length+1) (l.tables.map Prod.snd)
    let tables ← PCSBCSCallerParserCost.constraintClaims airs pair.1
    let rings ← PCSBCSCallerParserCost.flockClaims [l.hash]
    recFinish l pair.2 tables rings) tokens).work ≤ _
  payload_bind (PCSBCSCallerParserCost.busClaimsWork size),
    (100*(size+1)^3*size+6*size^3+79*size^2+874*size+738)
  · exact PCSBCSCallerParserCost.busClaims_work_polynomial l.bus tokens size busConfig
  · intro pair rest accepted
    have busCaps := PCSBCSCallerParserCost.busClaims_success_caps l.bus tokens rest pair size busConfig accepted
    payload_bind 4, (100*(size+1)^3*size+6*size^3+79*size^2+874*size+734)
    · exact PCSBCSCallerParserCost.drawScalar_work_le rest
    · intro unused tail accepted
      unfold charged
      simp only [bind_assoc,pure_bind]
      rw [PCSBCSCallerParserCost.tick_bind_work]
      have later : ((do
        let tables ← PCSBCSCallerParserCost.constraintClaims (l.tables.map Prod.snd) pair.1
        let rings ← PCSBCSCallerParserCost.flockClaims [l.hash]
        recFinish l pair.2 tables rings) tail).work ≤
          100*(size+1)^3*size+6*size^3+79*size^2+871*size+733 := by
        payload_bind (100*(size+1)^3*size+2*size^2+50*size+20),
          (6*size^3+77*size^2+821*size+713)
        · simpa only [pow_two,Nat.mul_assoc] using
            PCSBCSCallerParserCost.constraintClaims_work_polynomial _ _ tail size airConfig busCaps.2.1
        · intro tables tableRest received
          have tableCaps := PCSBCSCallerParserCost.constraintClaims_success_caps _ _ tail tableRest tables size airConfig received
          payload_bind (20*size^2+800*size+700),
            (6*size^3+57*size^2+13*size+10)
          · have hw := PCSBCSCallerParserCost.flockClaims_work_le [l.hash] tableRest
            nlinarith [Nat.mul_self_le_mul_self flockConfig]
          · intro rings final accepted
            exact recFinish_work_le l pair.2 tables rings final size count busCaps.2.2.1
              busCaps.2.2.2 (fun c hc => ⟨(tableCaps.2 c hc).1,(tableCaps.2 c hc).2.1⟩)
      nlinarith

private def settledColumnStep (table : CpuTableLayout) (c : Nat)
    (state : List E × List E) :
    PCSBCSCallerParserCost.Parser (ForInStep (List E × List E)) := do
  PCSBCSCallerParserCost.tick (1+containsWork c table.summedColumns+2*state.2.length+2)
  if c ∈ table.summedColumns then pure (.yield (state.1,state.2++[0]))
  else match state.1 with
  | [] => do PCSBCSCallerParserCost.check false; pure (.yield state)
  | x::xs => pure (.yield (xs,state.2++[x]))

private theorem settledColumnStep_work (table : CpuTableLayout) (c : Nat)
    (state : List E × List E) (tokens : List CallerToken) :
    (settledColumnStep table c state tokens).work ≤
      2*state.2.length+3*table.summedColumns.length+6 := by
  have search := containsWork_le c table.summedColumns
  unfold settledColumnStep
  rw [PCSBCSCallerParserCost.tick_bind_work]
  split
  · simp only [PCSBCSCallerParserCost.pure_work]; omega
  · cases state.1 with
    | nil => simp [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.check]; omega
    | cons x xs => simp only [PCSBCSCallerParserCost.pure_work]; omega

private theorem settledColumnStep_growth (table : CpuTableLayout) (c : Nat)
    (state : List E × List E) (tokens rest : List CallerToken)
    (step : ForInStep (List E × List E))
    (accepted : (settledColumnStep table c state tokens).result = some (step,rest)) :
    (PCSBCSCallerParserCost.iterationState step).2.length ≤ state.2.length+1 := by
  unfold settledColumnStep at accepted
  simp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick] at accepted
  split at accepted
  · simp only [Pure.pure,PCSBCSCallerParserCost.pure,Option.some.injEq,Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl,rfl⟩
    simp [PCSBCSCallerParserCost.iterationState]
  · cases remaining : state.1 with
    | nil => simp [remaining,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.check] at accepted
    | cons x xs =>
      rw [remaining] at accepted
      simp only [Pure.pure,PCSBCSCallerParserCost.pure,Option.some.injEq,Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl,rfl⟩
      simp [PCSBCSCallerParserCost.iterationState]

private theorem settledColumnLoop_work (table : CpuTableLayout) (sent : List E)
    (tokens : List CallerToken) :
    (forIn (List.range table.committedColumns) (sent,[]) (settledColumnStep table) tokens).work ≤
      table.committedColumns*(2*table.committedColumns+3*table.summedColumns.length+6) := by
  have growth := PCSBCSCallerParserCost.forIn_growth_work_le
    (List.range table.committedColumns) (sent,[]) (settledColumnStep table)
    (fun state => state.2.length) 2 (3*table.summedColumns.length+6) 1
    (fun c _ state ts => settledColumnStep_work table c state ts)
    (fun c _ state ts step rest h => settledColumnStep_growth table c state ts rest step h) tokens
  simpa [Nat.add_assoc] using growth

private def settledTableStep (point : List E) (table : CpuTableLayout)
    (claims : List TableClaims) : PCSBCSCallerParserCost.Parser (ForInStep (List TableClaims)) := do
  PCSBCSCallerParserCost.tick 2
  if table.settled then
    PCSBCSCallerParserCost.tick (allWork (· < table.committedColumns) (fun _ => 2) table.summedColumns)
    PCSBCSCallerParserCost.check (table.summedColumns.all (· < table.committedColumns))
    PCSBCSCallerParserCost.tick (dupsWork table.summedColumns []+table.summedColumns.eraseDups.length+1+
      table.summedColumns.length+1+1)
    PCSBCSCallerParserCost.check (table.summedColumns.eraseDups.length==table.summedColumns.length)
    PCSBCSCallerParserCost.tick (table.summedColumns.length+2)
    let sent ← PCSBCSCallerParserCost.readScalars (table.committedColumns-table.summedColumns.length)
    PCSBCSCallerParserCost.tick (3*table.committedColumns+1)
    let state ← forIn (List.range table.committedColumns) (sent,[]) (settledColumnStep table)
    PCSBCSCallerParserCost.tick (point.length+4)
    PCSBCSCallerParserCost.check (table.tau≤point.length && state.1.isEmpty)
    PCSBCSCallerParserCost.tick (2*min table.tau point.length+1+2*claims.length+3)
    pure (.yield (claims++[⟨point.take table.tau,state.2,[]⟩]))
  else pure (.yield claims)

private theorem settledClaims_normalized (tables : List CpuTableLayout) (point : List E) :
    settledClaims tables point =
      (forIn tables [] (settledTableStep point) >>= fun claims => pure claims) := rfl

private theorem dedup_length_le {A : Type} [BEq A] (xs : List A) :
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

private theorem settledTableStep_work (point : List E) (table : CpuTableLayout)
    (claims : List TableClaims) (tokens : List CallerToken) (size : Nat)
    (columns : table.committedColumns ≤ size) (summed : table.summedColumns.length ≤ size)
    (pointCap : point.length ≤ size) :
    (settledTableStep point table claims tokens).work ≤ 2*claims.length+100*(size+1)^2 := by
  have all := allWork_le (· < table.committedColumns) (fun _ => 2) table.summedColumns 2 (by simp)
  have distinct := dupsWork_le table.summedColumns []
  have erased := dedup_length_le table.summedColumns
  let c := table.committedColumns
  let u := table.summedColumns.length
  let p := point.length
  let loop := c*(2*c+3*u+6)
  have allCost : allWork (· < table.committedColumns) (fun _ => 2) table.summedColumns ≤ 4*u+1 := all
  have dupsCost : dupsWork table.summedColumns []+table.summedColumns.eraseDups.length+1+
      table.summedColumns.length+1+1 ≤ 3*(u+1)^2+2*u+3 := by
    dsimp only [u]
    simp only [List.length_nil] at distinct
    nlinarith
  have detailed : (settledTableStep point table claims tokens).work ≤
      2*claims.length+loop+3*(u+1)^2+7*u+12*c+3*p+40 := by
    unfold settledTableStep
    payload_tick (2*claims.length+loop+3*(u+1)^2+7*u+12*c+3*p+38)
    split
    · payload_tick (2*claims.length+loop+3*(u+1)^2+3*u+12*c+3*p+37)
      payload_bind 3, (2*claims.length+loop+3*(u+1)^2+3*u+12*c+3*p+34)
      · exact PCSBCSCallerParserCost.check_work_le _ _
      · intro unused rest checked
        payload_tick (2*claims.length+loop+u+12*c+3*p+31)
        payload_bind 3, (2*claims.length+loop+u+12*c+3*p+28)
        · exact PCSBCSCallerParserCost.check_work_le _ _
        · intro unused tail checked
          payload_tick (2*claims.length+loop+12*c+3*p+26)
          payload_bind (9*c+2), (2*claims.length+loop+3*c+3*p+24)
          · have read := PCSBCSCallerParserCost.readScalars_work_le
              (table.committedColumns-table.summedColumns.length) tail
            dsimp [c] at *; omega
          · intro sent remaining read
            payload_tick (2*claims.length+loop+3*p+23)
            payload_bind loop, (2*claims.length+3*p+23)
            · exact settledColumnLoop_work table sent remaining
            · intro state suffix stateRead
              payload_tick (2*claims.length+2*p+19)
              payload_bind 3, (2*claims.length+2*p+16)
              · exact PCSBCSCallerParserCost.check_work_le _ _
              · intro unused final checked
                rw [PCSBCSCallerParserCost.tick_bind_work]
                simp only [PCSBCSCallerParserCost.pure_work]
                dsimp [p] at *; omega
    · simp only [PCSBCSCallerParserCost.pure_work]
      omega
  dsimp [loop,c,u,p] at detailed
  have product : table.committedColumns*(2*table.committedColumns+3*table.summedColumns.length+6) ≤
      size*(5*size+6) := Nat.mul_le_mul columns (by omega)
  nlinarith [Nat.mul_self_le_mul_self summed]

private theorem settledTableStep_growth (point : List E) (table : CpuTableLayout)
    (claims : List TableClaims) (tokens rest : List CallerToken)
    (step : ForInStep (List TableClaims))
    (accepted : (settledTableStep point table claims tokens).result = some (step,rest)) :
    (PCSBCSCallerParserCost.iterationState step).length ≤ claims.length+1 := by
  unfold settledTableStep at accepted
  repeat' first
    | dsimp only [Bind.bind,PCSBCSCallerParserCost.bind,PCSBCSCallerParserCost.tick,
        Pure.pure,PCSBCSCallerParserCost.pure] at accepted
    | split at accepted
  all_goals simp only [Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at accepted
  all_goals rcases accepted with ⟨rfl,rfl⟩
  all_goals simp [PCSBCSCallerParserCost.iterationState]

theorem cpuTableVolume_components (table : CpuTableLayout) :
    table.committedColumns ≤ cpuTableVolume table ∧
    table.summedColumns.length ≤ cpuTableVolume table ∧
    table.tau ≤ cpuTableVolume table := by
  unfold cpuTableVolume
  omega

theorem settledClaims_work_polynomial (tables : List CpuTableLayout) (point : List E)
    (tokens : List CallerToken) (size : Nat) (_count : tables.length ≤ size)
    (volume : ∀ table ∈ tables, cpuTableVolume table ≤ size) (pointCap : point.length ≤ size) :
    (settledClaims tables point tokens).work ≤
      tables.length*(2*tables.length+100*(size+1)^2) := by
  rw [settledClaims_normalized]
  have growth := PCSBCSCallerParserCost.forIn_growth_work_le tables []
    (settledTableStep point) List.length 2 (100*(size+1)^2) 1
    (by
      intro table member claims ts
      have caps := cpuTableVolume_components table
      exact settledTableStep_work point table claims ts size
        (caps.1.trans (volume table member)) (caps.2.1.trans (volume table member)) pointCap)
    (fun table _ claims ts step rest h => settledTableStep_growth point table claims ts rest step h) tokens
  have bound : (forIn tables [] (settledTableStep point) tokens).work ≤
      tables.length*(2*tables.length+100*(size+1)^2) := by
    simpa using growth
  have final := PCSBCSCallerParserCost.bind_work_le
    (forIn tables [] (settledTableStep point)) (fun value => PCSBCSCallerParserCost.pure value)
    tokens _ 0 bound
    (by intro value rest accepted; exact (PCSBCSCallerParserCost.pure_work value rest).le)
  simpa only [Nat.add_zero,Pure.pure,PCSBCSCallerParserCost.pure] using final

theorem settledClaims_success_caps (tables : List CpuTableLayout) (point : List E)
    (tokens rest : List CallerToken) (claims : List TableClaims) (size : Nat)
    (count : tables.length ≤ size)
    (volume : ∀ table ∈ tables, cpuTableVolume table ≤ size)
    (accepted : (settledClaims tables point tokens).result = some (claims,rest)) :
    claims.length ≤ size ∧
      ∀ c ∈ claims, c.point.length ≤ size ∧ c.evals.length ≤ size := by
  constructor
  · rw [settledClaims_success_length tables point tokens rest claims accepted]
    exact (List.length_filter_le _ _).trans count
  · have geometry := settledClaims_success_geometry tables point tokens rest claims accepted
    have filtered : ∀ table ∈ tables.filter CpuTableLayout.settled, cpuTableVolume table ≤ size := by
      intro table member
      exact volume table (List.mem_filter.mp member).1
    clear accepted
    generalize tables.filter CpuTableLayout.settled = selected at geometry filtered
    induction geometry with
    | nil => simp
    | @cons table claim selected claims g relation ih =>
      intro c member
      rcases List.mem_cons.mp member with rfl | member
      · have v := filtered table (by simp)
        have dimensions := cpuTableVolume_components table
        exact ⟨g.1.trans (dimensions.2.2.trans v),g.2.trans (dimensions.1.trans v)⟩
      · exact ih (fun t ht => filtered t (List.mem_cons_of_mem _ ht)) c member

#print axioms recPayload_work_polynomial
#print axioms settledClaims_work_polynomial
#print axioms settledClaims_success_caps

end Whir.PCSBCSCallerPayloadCost
