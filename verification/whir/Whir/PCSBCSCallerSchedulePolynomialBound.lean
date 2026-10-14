import Whir.PCSBCSCallerPayloadPolynomialBound

/-! Bounds for the actual source schedule constructors. Literal numeric metadata
is charged by value; duplicate framework keys pay the actual dedup traversal.
These bounds do not require validity of the caller layout. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSCallerPayloadCost
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec

private theorem sum_member {A : Type} (xs : List A) (f : A → Nat)
    (x : A) (hx : x ∈ xs) : f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    simp only [List.map_cons,List.sum_cons]
    rcases hx with rfl | hx
    · omega
    · have := ih hx; omega

private theorem sum_count {A : Type} (xs : List A) (f : A → Nat)
    (hf : ∀ x ∈ xs, 1 ≤ f x) : xs.length ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht := ih (by intro x hx; exact hf x (by simp [hx]))
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

private theorem flat_resource {A : Type} (xs : List A)
    (f : A → PCSBCSCallerParserCost.Costed Schedule) (w n : Nat)
    (h : ∀ x ∈ xs, (f x).work ≤ w ∧ (f x).value.length ≤ n) :
    (scheduleFlatMap xs f).work ≤ xs.length+1+xs.length*(w+2*n+1) ∧
    (scheduleFlatMap xs f).value.length ≤ xs.length*n := by
  have hw := sumMap_le xs (fun x => (f x).work+2*(f x).value.length+1)
    (w+2*n+1) (by intro x hx; have := h x hx; omega)
  have hn := sumMap_le xs (fun x => (f x).value.length) n
    (by intro x hx; exact (h x hx).2)
  simp only [scheduleFlatMap,List.length_flatMap]
  simpa only [Nat.mul_comm] using (show
    xs.length+1+(xs.map (fun x => (f x).work+2*(f x).value.length+1)).sum ≤
      xs.length+1+(w+2*n+1)*xs.length ∧
    (xs.map (fun x => (f x).value.length)).sum ≤ n*xs.length from ⟨by omega,hn⟩)

private theorem repeat_resource (k : Nat) (a : PCSBCSCallerParserCost.Costed Schedule)
    (w n : Nat) (h : a.work ≤ w ∧ a.value.length ≤ n) :
    (scheduleRepeat k a).work ≤ w+3*k+2+k*(2*n+2) ∧
    (scheduleRepeat k a).value.length ≤ k*n := by
  have length : (List.replicate k a.value).flatten.length = k*a.value.length := by
    induction k with
    | zero => simp
    | succ k ih => simp [List.replicate_succ,ih,Nat.succ_mul,Nat.add_comm]
  simp only [scheduleRepeat,length]
  constructor <;> nlinarith [Nat.mul_le_mul_left k h.2]

@[simp] theorem gkrShape_value (mu : Nat) :
    (gkrShape mu).value = WHIRCallerClaims.gkrShape mu := rfl
@[simp] theorem frameworkKeys_value (layout : BusLayout) :
    (frameworkKeys layout).value = WHIRCallerClaims.frameworkKeys layout := rfl
@[simp] theorem busShape_value (layout : BusLayout) :
    (busShape layout).value = WHIRCallerClaims.busShape layout := rfl
@[simp] theorem constraintsShape_value (layouts : List AirLayout) :
    (constraintsShape layouts).value = WHIRCallerClaims.constraintsShape layouts := rfl
@[simp] theorem flockProgramShape_value (layouts : List FlockLayout) :
    (flockProgramShape layouts).value = WHIRCallerClaims.flockProgramShape layouts := rfl
@[simp] theorem callerShape_value (layout : CallerLayout) :
    (callerShape layout).value = WHIRCallerClaims.callerShape layout := by cases layout <;> rfl
@[simp] theorem freshCallerShape_value (layout : CallerLayout) (saved : Record) (cost : OutputCosts) :
    (freshCallerShape layout saved cost).value = AnchoredSourceFreshCaller.callerShape layout saved := rfl

private theorem gkr_assembled_value (mu : Nat) :
    (scheduleAppend (scheduleReads 1)
      (scheduleAppend (scheduleDraws 1)
        (scheduleAppend (if mu % 2 = 1 then scheduleAppend (scheduleReads 4) (scheduleDraws 2)
          else ⟨[],1⟩)
          (scheduleFlatMap (List.range (mu/2)) (fun i =>
            scheduleAppend (scheduleRepeat (mu%2+2*i)
              (scheduleAppend (scheduleReads 4) (scheduleDraws 1)))
              (scheduleAppend (scheduleReads 8) (scheduleDraws 3))))))).value =
      WHIRCallerClaims.gkrShape mu := by
  simp only [scheduleAppend,scheduleReads,scheduleDraws,scheduleRepeat,scheduleFlatMap,
    WHIRCallerClaims.gkrShape,List.append_assoc]
  split <;> rfl

 theorem gkrShape_resource (mu size : Nat) (bound : mu ≤ size) :
    (gkrShape mu).work ≤ 300*(size+1)^2 ∧
    (gkrShape mu).value.length ≤ 300*(size+1)^2 := by
  have odd : (if mu%2=1 then scheduleAppend (scheduleReads 4) (scheduleDraws 2)
      else (⟨[],1⟩ : PCSBCSCallerParserCost.Costed Schedule)).work ≤ 33 ∧
      (if mu%2=1 then scheduleAppend (scheduleReads 4) (scheduleDraws 2)
      else (⟨[],1⟩ : PCSBCSCallerParserCost.Costed Schedule)).value.length ≤ 6 := by
    split <;> simp [scheduleAppend,scheduleReads,scheduleDraws]
  have rows := flat_resource (List.range (mu/2)) (fun i =>
      scheduleAppend (scheduleRepeat (mu%2+2*i)
        (scheduleAppend (scheduleReads 4) (scheduleDraws 1)))
        (scheduleAppend (scheduleReads 8) (scheduleDraws 3))) (80*size+100) (10*size+11) (by
    intro i hi
    have index := List.mem_range.mp hi
    have rem := Nat.mod_lt mu (by decide : 0<2)
    have rep := repeat_resource (mu%2+2*i)
      (scheduleAppend (scheduleReads 4) (scheduleDraws 1)) 28 5
      (by simp [scheduleAppend,scheduleReads,scheduleDraws])
    simp only [scheduleAppend,scheduleReads,scheduleDraws,scheduleRepeat,List.length_append,
      List.length_replicate] at rep ⊢
    constructor <;> nlinarith [Nat.div_mul_le_self mu 2])
  simp only [List.length_range] at rows
  have count : mu/2 ≤ size := (Nat.div_le_self _ _).trans bound
  have rw := Nat.mul_le_mul_right (80*size+100+2*(10*size+11)+1) count
  have rn := Nat.mul_le_mul_right (10*size+11) count
  simp only [gkrShape]
  rw [← gkr_assembled_value mu]
  simp only [scheduleAppend,scheduleReads,scheduleDraws,
    List.length_append,List.length_replicate] at odd rows ⊢
  constructor <;> nlinarith [Nat.div_le_self mu 2]
private theorem dedup_length {A : Type} [BEq A] (xs : List A) :
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

theorem frameworkKeys_resource (l : BusLayout) (size : Nat)
    (volume : PCSBCSCallerParserCost.busLayoutSize l ≤ size) :
    (frameworkKeys l).work ≤ 30*(size+1)^4 ∧
    (frameworkKeys l).value.length ≤ size^2 := by
  let blocks := l.push++l.pull
  let keys := blocks.flatMap (fun b => if b.tableOwned then []
    else b.coords.filterMap (fun c => match c with | .column col => some (col,b.kappa) | _ => none))
  have caps := PCSBCSCallerParserCost.busLayoutSize_components l
  have count : blocks.length ≤ size := caps.1.trans volume
  have coords : ∀ b ∈ blocks, b.coords.length ≤ size := by
    intro b hb; exact (caps.2 b hb).trans volume
  have raw : keys.length ≤ size*size := by
    have hs := sumMap_le blocks (fun b =>
      (if b.tableOwned then [] else b.coords.filterMap (fun c =>
        match c with | .column col => some (col,b.kappa) | _ => none)).length) size (by
      intro b hb
      split
      · simp
      · exact (List.length_filterMap_le _ _).trans (coords b hb))
    simp only [keys,List.length_flatMap]
    exact hs.trans (Nat.mul_le_mul_left size count)
  have bw := sumMap_le blocks (fun b => 2+if b.tableOwned then 1 else
    1+(b.coords.map (fun c => match c with | .column _ => 5 | _ => 2)).sum)
    (3+5*size) (by
      intro b hb
      have hs := sumMap_le b.coords (fun c => match c with | .column _ => 5 | _ => 2)
        5 (by intro c _; cases c <;> simp)
      have hc := coords b hb
      split <;> nlinarith)
  have cost := PCSBCSCallerParserCost.eraseDupsCost_le 2 keys []
  have out := dedup_length keys
  have push : l.push.length ≤ size := by simp only [blocks,List.length_append] at count; omega
  have sumcap := Nat.mul_le_mul_left (3+5*size) count
  have square := Nat.mul_self_le_mul_self raw
  change (frameworkKeys l).work ≤ _ ∧ (WHIRCallerClaims.frameworkKeys l).length ≤ _
  change _ ∧ keys.eraseDups.length ≤ size^2
  simp only [frameworkKeys]
  change 2*l.push.length+1+blocks.length+1+
    (blocks.map (fun b => 2+if b.tableOwned then 1 else
      1+(b.coords.map (fun c => match c with | .column _ => 5 | _ => 2)).sum)).sum+
    2*keys.length+blocks.length+PCSBCSCallerParserCost.eraseDupsCost 2 keys [] ≤ _ ∧ _
  simp only [List.length_nil,Nat.add_zero] at cost
  constructor <;> nlinarith [out]

private theorem bus_assembled_value (l : BusLayout) :
    (scheduleAppend (if l.grinding>0 then ⟨[.nonce l.grinding],4⟩ else ⟨[],2⟩)
      (scheduleAppend (scheduleDraws 5)
        (scheduleAppend (gkrShape l.mu) (scheduleReads (frameworkKeys l).value.length)))).value =
      WHIRCallerClaims.busShape l := by
  simp only [scheduleAppend,scheduleDraws,scheduleReads,gkrShape_value,frameworkKeys_value,
    WHIRCallerClaims.busShape,List.append_assoc]
  split <;> rfl

theorem busShape_resource (l : BusLayout) (size : Nat)
    (volume : PCSBCSCallerParserCost.busLayoutSize l ≤ size) :
    (busShape l).work ≤ 1500*(size+1)^4 ∧
    (busShape l).value.length ≤ 1500*(size+1)^4 := by
  have keys := frameworkKeys_resource l size volume
  have gkr := gkrShape_resource l.mu size ((PCSBCSCallerParserCost.bus_mu_le_size l).trans volume)
  have muCost := PCSBCSCallerParserCost.bus_mu_work_le l
  have grinding : (if l.grinding>0 then
      (⟨[.nonce l.grinding],4⟩ : PCSBCSCallerParserCost.Costed Schedule) else ⟨[],2⟩).work ≤ 4 ∧
      (if l.grinding>0 then
      (⟨[.nonce l.grinding],4⟩ : PCSBCSCallerParserCost.Costed Schedule) else ⟨[],2⟩).value.length ≤ 1 := by
    split <;> simp
  simp only [busShape,PCSBCSCallerParserCost.mu_erasure]
  rw [← bus_assembled_value l]
  simp only [scheduleAppend,scheduleReads,scheduleDraws,List.length_append,List.length_replicate]
  constructor <;> nlinarith [Nat.zero_le ((size+1)^2)]

private theorem air_caps (ls : List AirLayout) (size : Nat)
    (volume : PCSBCSCallerParserCost.airLayoutsSize ls ≤ size) :
    ls.length ≤ size ∧ ∀ l ∈ ls,
      l.tau ≤ size ∧ l.columns ≤ size ∧ l.fields.length ≤ size ∧
      (l.fields.map BitField.width).sum ≤ size := by
  have count := sum_count ls (fun l => 1+PCSBCSCallerParserCost.airLayoutSize l)
    (by intro l _; omega)
  constructor
  · unfold PCSBCSCallerParserCost.airLayoutsSize at volume; omega
  · intro l hl
    have member := sum_member ls (fun l => 1+PCSBCSCallerParserCost.airLayoutSize l) l hl
    have fields := sum_count l.fields (fun f => 1+f.column+f.width) (by intro f _; omega)
    have widths : (l.fields.map BitField.width).sum ≤
        (l.fields.map (fun f => 1+f.column+f.width)).sum := by
      apply List.sum_le_sum; intro f _; omega
    unfold PCSBCSCallerParserCost.airLayoutsSize PCSBCSCallerParserCost.airLayoutSize at *
    omega

private theorem constraints_assembled_value (ls : List AirLayout) :
    (scheduleAppend (scheduleRepeat ((ls.map AirLayout.tau).foldl max 0)
      (scheduleAppend (scheduleReads 3) (scheduleDraws 1)))
      (scheduleFlatMap ls (fun l =>
        let a := scheduleAppend (scheduleReads (l.columns-l.publicColumns-l.fields.length))
          (scheduleReads (l.fields.map BitField.width).sum)
        ⟨a.value,a.work+5+l.fields.length+1+5*l.fields.length+2⟩))).value =
      WHIRCallerClaims.constraintsShape ls := by
  rfl

theorem constraintsShape_resource (ls : List AirLayout) (size : Nat)
    (volume : PCSBCSCallerParserCost.airLayoutsSize ls ≤ size) :
    (constraintsShape ls).work ≤ 200*(size+1)^2 ∧
    (constraintsShape ls).value.length ≤ 200*(size+1)^2 := by
  have caps := air_caps ls size volume
  have rounds : (ls.map AirLayout.tau).foldl max 0 ≤ size := by
    apply PCSBCSCallerParserCost.FlockPolynomial.max_fold_le _ _ _ (Nat.zero_le _)
    intro t ht
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp ht
    exact (caps.2 l hl).1
  have front := repeat_resource ((ls.map AirLayout.tau).foldl max 0)
    (scheduleAppend (scheduleReads 3) (scheduleDraws 1)) 23 4
    (by simp [scheduleAppend,scheduleReads,scheduleDraws])
  have tables := flat_resource ls (fun l =>
    let a := scheduleAppend (scheduleReads (l.columns-l.publicColumns-l.fields.length))
      (scheduleReads (l.fields.map BitField.width).sum)
    ⟨a.value,a.work+5+l.fields.length+1+5*l.fields.length+2⟩) (14*size+13) (2*size) (by
      intro l hl
      have hc := caps.2 l hl
      simp only [scheduleAppend,scheduleReads,List.length_append,List.length_replicate]
      constructor <;> omega)
  have pw := Nat.mul_le_mul_right (14*size+13+2*(2*size)+1) caps.1
  have pn := Nat.mul_le_mul_right (2*size) caps.1
  simp only [constraintsShape]
  rw [← constraints_assembled_value ls]
  simp only [scheduleAppend,List.length_append] at front tables ⊢
  constructor <;> nlinarith

private theorem flock_assembled_value (ls : List FlockLayout) :
    (scheduleAppend (scheduleDraws ((ls.map FlockLayout.logN).foldl max 0-13+1))
      (scheduleAppend (scheduleReads 64) (scheduleAppend (scheduleDraws 1)
      (scheduleAppend (scheduleRepeat ((ls.map FlockLayout.logN).foldl max 0-6)
        (scheduleAppend (scheduleReads 2) (scheduleDraws 1)))
      (scheduleAppend (scheduleReads (3*ls.length)) (scheduleAppend (scheduleDraws 1)
      (scheduleAppend (scheduleRepeat ((ls.map (fun l => l.kLog-6)).foldl max 0)
        (scheduleAppend (scheduleReads 2) (scheduleDraws 1)))
      (scheduleFlatMap ls (fun _ => scheduleAppend (scheduleReads 64) (scheduleReads 1)))))))))).value =
      WHIRCallerClaims.flockProgramShape ls := by
  simp only [scheduleAppend,scheduleReads,scheduleDraws,scheduleRepeat,scheduleFlatMap,
    WHIRCallerClaims.flockProgramShape,List.append_assoc]
  rfl

theorem flockProgramShape_resource (ls : List FlockLayout) (size : Nat)
    (volume : PCSBCSCallerParserCost.flockConfigurationSize ls ≤ size) :
    (flockProgramShape ls).work ≤ 2000*(size+1) ∧
    (flockProgramShape ls).value.length ≤ 2000*(size+1) := by
  have caps := PCSBCSCallerParserCost.FlockPolynomial.dimension_caps ls
  have count := caps.1.trans volume
  have m := caps.2.1.trans volume
  have r := caps.2.2.trans volume
  have first := repeat_resource ((ls.map FlockLayout.logN).foldl max 0-6)
    (scheduleAppend (scheduleReads 2) (scheduleDraws 1)) 18 3
    (by simp [scheduleAppend,scheduleReads,scheduleDraws])
  have last := repeat_resource ((ls.map (fun l => l.kLog-6)).foldl max 0)
    (scheduleAppend (scheduleReads 2) (scheduleDraws 1)) 18 3
    (by simp [scheduleAppend,scheduleReads,scheduleDraws])
  have tables := flat_resource ls (fun _ => scheduleAppend (scheduleReads 64) (scheduleReads 1))
    328 65 (by intro _ _; simp [scheduleAppend,scheduleReads])
  simp only [flockProgramShape]
  rw [← flock_assembled_value ls]
  simp only [scheduleAppend,scheduleDraws,scheduleReads,List.length_append,List.length_replicate]
    at first last tables ⊢
  constructor <;> omega

private theorem cpu_schedule_metadata (l : CpuLayout) (size : Nat)
    (volume : cpuLayoutVolume l ≤ size) :
    (∀ t ∈ l.tables, t.committedColumns ≤ size ∧ t.summedColumns.length ≤ size) ∧
    (l.tables.map (fun t => t.summedColumns.length+1)).sum ≤ size ∧
    l.bus.producers.length ≤ size := by
  have sumcap : (l.tables.map cpuTableVolume).sum ≤ size := by
    unfold cpuLayoutVolume at volume; omega
  have entries : ∀ t ∈ l.tables, t.committedColumns ≤ size ∧ t.summedColumns.length ≤ size := by
    intro t ht
    have member := sum_member l.tables cpuTableVolume t ht
    have localBudget := member.trans sumcap
    unfold cpuTableVolume at localBudget
    omega
  have summed : (l.tables.map (fun t => t.summedColumns.length+1)).sum ≤
      (l.tables.map cpuTableVolume).sum := by
    apply List.sum_le_sum
    intro t _
    unfold cpuTableVolume
    omega
  have producers := sum_count l.bus.producers (fun p => 1+p.kappa+p.bits+p.window)
    (by intro p _; omega)
  have bus := (cpuLayoutVolume_components l).1.trans volume
  unfold PCSBCSCallerParserCost.busLayoutSize at bus
  exact ⟨entries,summed.trans sumcap,by omega⟩

private theorem rec_assembled_value (l : RecLayout) :
    (scheduleAppend (scheduleReads 2) (scheduleAppend (busShape l.bus)
      (scheduleAppend (scheduleDraws 1)
        (scheduleAppend (constraintsShape (l.tables.map Prod.snd)) (flockProgramShape [l.hash]))))).value =
      WHIRCallerClaims.callerShape (.recursion l) := by
  simp only [scheduleAppend,scheduleReads,scheduleDraws,busShape_value,
    constraintsShape_value,flockProgramShape_value,WHIRCallerClaims.callerShape,List.append_assoc]
  rfl

private theorem cpu_assembled_value (l : CpuLayout) :
    (scheduleAppend (scheduleReads (l.tables.length+2))
      (scheduleAppend (scheduleReads 2) (scheduleAppend (busShape l.bus)
        (scheduleAppend (scheduleFlatMap l.tables (fun t =>
          if t.settled then
            let a := scheduleReads (t.committedColumns-t.summedColumns.length)
            ⟨a.value,a.work+t.summedColumns.length+3⟩
          else ⟨[],2⟩)) (scheduleAppend (scheduleDraws 1)
          (scheduleAppend (constraintsShape (cpuAirs l)) (flockProgramShape l.flock))))))).value =
      WHIRCallerClaims.callerShape (.cpu l) := by
  simp only [scheduleAppend,scheduleReads,scheduleDraws,busShape_value,
    constraintsShape_value,flockProgramShape_value,scheduleFlatMap,
    WHIRCallerClaims.callerShape,cpuAirs,List.append_assoc,apply_ite]
  rfl

/-- No validity or supplied work certificate: the actual constructors are
bounded for every literal CPU and recursive configuration. -/
theorem callerShape_resource (layout : CallerLayout) (size : Nat)
    (volume : layoutVolume layout ≤ size) :
    (callerShape layout).work ≤ 10000*(size+1)^4 ∧
    (callerShape layout).value.length ≤ 10000*(size+1)^4 := by
  cases layout with
  | recursion l =>
    change recLayoutVolume l ≤ size at volume
    have caps := recLayoutVolume_components l
    have bus := busShape_resource l.bus size (caps.1.trans volume)
    have airs := constraintsShape_resource (l.tables.map Prod.snd) size (caps.2.1.trans volume)
    have flock := flockProgramShape_resource [l.hash] size (caps.2.2.2.1.trans volume)
    have count := caps.2.2.1.trans volume
    simp only [callerShape]
    rw [← rec_assembled_value l]
    simp only [scheduleAppend,scheduleReads,scheduleDraws,List.length_append,List.length_replicate]
    constructor <;> nlinarith [Nat.zero_le (size^2),Nat.zero_le (size^3)]
  | cpu l =>
    change cpuLayoutVolume l ≤ size at volume
    have caps := cpuLayoutVolume_components l
    have bus := busShape_resource l.bus size (caps.1.trans volume)
    have airs := constraintsShape_resource (cpuAirs l) size (caps.2.1.trans volume)
    have flock := flockProgramShape_resource l.flock size (caps.2.2.2.1.trans volume)
    have count := caps.2.2.1.trans volume
    have metadata := cpu_schedule_metadata l size volume
    have settled := flat_resource l.tables (fun t =>
      if t.settled then
        let a := scheduleReads (t.committedColumns-t.summedColumns.length)
        ⟨a.value,a.work+t.summedColumns.length+3⟩
      else ⟨[],2⟩) (4*size+5) size (by
        intro t ht
        have localCap := metadata.1 t ht
        split <;> simp only [scheduleReads,List.length_replicate,List.length_nil] <;> omega)
    have sw := Nat.mul_le_mul_right (4*size+5+2*size+1) count
    have sn := Nat.mul_le_mul_right size count
    simp only [callerShape]
    change _ ∧ (WHIRCallerClaims.callerShape (.cpu l)).length ≤ _
    rw [← cpu_assembled_value l]
    change (scheduleAppend (scheduleReads (l.tables.length+2))
      (scheduleAppend (scheduleReads 2) (scheduleAppend (busShape l.bus)
        (scheduleAppend (scheduleFlatMap l.tables (fun t =>
          if t.settled then
            let a := scheduleReads (t.committedColumns-t.summedColumns.length)
            ⟨a.value,a.work+t.summedColumns.length+3⟩
          else ⟨[],2⟩)) (scheduleAppend (scheduleDraws 1)
          (scheduleAppend (constraintsShape (cpuAirs l)) (flockProgramShape l.flock))))))).work+
      9*l.tables.length+(l.tables.map (fun t => t.summedColumns.length+1)).sum+
      7*l.bus.producers.length+5 ≤ _ ∧ _
    simp only [scheduleAppend,scheduleReads,scheduleDraws,List.length_append,List.length_replicate]
      at settled ⊢
    constructor <;> nlinarith [Nat.zero_le (size^2),Nat.zero_le (size^3)]

/-- Mandatory opening serialization and pending/root/context accessor prices
remain explicit; none are hidden behind a free cost hypothesis. -/
theorem freshCallerShape_resource (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (size : Nat) (volume : layoutVolume layout ≤ size) :
    (freshCallerShape layout saved cost).work ≤
      30000*(size+1)^4+openingWork saved+openingGetterWork saved cost+
        4*(openingScalars saved).length+7 ∧
    (freshCallerShape layout saved cost).value.length ≤
      10000*(size+1)^4+(openingScalars saved).length := by
  have base := callerShape_resource layout size volume
  simp only [freshCallerShape,AnchoredSourceFreshCaller.callerShape,
    callerShape_value,AnchoredSourceCaller.reads,List.length_append,List.length_drop,
    List.length_replicate]
  simp only [callerShape_value] at base
  constructor <;> omega

theorem freshCallerShape_resource_volume (layout : CallerLayout) (saved : Record)
    (cost : OutputCosts) (size : Nat) (volume : layoutVolume layout ≤ size)
    (recordVolume : saved.context.pendingBytes+saved.point.length+1 ≤ size) :
    (freshCallerShape layout saved cost).work ≤
      30000*(size+1)^4+46*size+647+openingGetterWork saved cost ∧
    (freshCallerShape layout saved cost).value.length ≤ 10000*(size+1)^4+size+10 := by
  have schedule := freshCallerShape_resource layout saved cost size volume
  have opening := openingWork_polynomial saved
  have frame := openingScalars_length saved
  have packs : (saved.context.pendingBytes+23)/24 ≤ saved.context.pendingBytes+1 := by omega
  constructor <;> omega

#print axioms gkrShape_resource
#print axioms frameworkKeys_resource
#print axioms busShape_resource
#print axioms constraintsShape_resource
#print axioms flockProgramShape_resource
#print axioms callerShape_resource
#print axioms freshCallerShape_resource
#print axioms freshCallerShape_resource_volume

end Whir.PCSBCSCallerPayloadCost
