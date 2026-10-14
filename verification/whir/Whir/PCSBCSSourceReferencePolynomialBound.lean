import Whir.PCSBCSSourceReferenceParserCost

/-! Polynomial resource bounds for the literal scheduled-key reconstruction.
The volumes count scalar packets, framed payload bytes, and both ghost cursors;
the fresh-caller component remains its actual reached work. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSSourceReferencePolynomialBound
open Concrete Protocol FiatShamirGame DuplexRefinement WHIRHistory WHIRHistoryKey
open WHIRCallerClaims PCSBCSSourceRootReferences PCSBCSPublicLogParserCost
open PCSBCSSourceReferenceParserCost

 def configSize (c : Config) : Nat := c.folds.size+(schedule c).length+c.logN+1
 def pendingMass (ps : List Pending) : Nat := (ps.map (fun p => p.scalars.length+1)).sum

 theorem pendingMass_length (ps : List Pending) : ps.length ≤ pendingMass ps := by
  induction ps with
  | nil => simp [pendingMass]
  | cons p ps ih => simp only [pendingMass,List.map_cons,List.sum_cons,List.length_cons] at *; omega

 theorem pendingMass_scalars (ps : List Pending) :
    (ps.map (fun p => p.scalars.length)).sum ≤ pendingMass ps := by
  induction ps with
  | nil => simp [pendingMass]
  | cons p ps ih => simp only [pendingMass,List.map_cons,List.sum_cons] at *; omega

 theorem modelMass_le_wire (m : Model) : modelMass m ≤ modelWireSize m := by
  have h := framesSize_length m.history.frames
  unfold modelMass modelWireSize
  omega

 theorem absorb_wire (m : Model) (bs : List Byte) :
    modelWireSize (modelAbsorb m bs) ≤ modelWireSize m+bs.length := by
  unfold modelAbsorb
  split
  · omega
  · simp only [modelWireSize,List.length_append]
    split <;> omega

 theorem operation_squeeze_wire (m : Model) (n : Nat) :
    modelWireSize (operationCount m (.squeeze n)).1 ≤ modelWireSize m+n+1 := by
  have h := closeRun_wire m
  have cursor : (closeRun m).consumed = m.consumed := by unfold closeRun; split <;> rfl
  simp only [operationCount]
  split
  · dsimp only; omega
  · simp only [closeRunCount_value,modelWireSize] at *
    omega

 theorem operation_squeeze_work (m : Model) (n : Nat) :
    (operationCount m (.squeeze n)).2 ≤ modelWireSize m+6 := by
  have h := (closeRunCount_bound m).trans (Nat.add_le_add_right (modelMass_le_wire m) 3)
  simp only [operationCount]
  split <;> dsimp only <;> omega

 theorem operation_nonce_wire (m : Model) (bits : Nat) (nonce : Scalar24) :
    modelWireSize (operationCount m (.nonce bits nonce)).1 ≤ modelWireSize m+26 := by
  have h := closeRun_wire m
  simp only [operationCount,closeRunCount_value,modelWireSize,framesSize,List.map_append,
    List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,frameSize,List.length_nil] at *
  omega

 theorem operation_nonce_work (m : Model) (bits : Nat) (nonce : Scalar24) :
    (operationCount m (.nonce bits nonce)).2 ≤ 2*modelWireSize m+6 := by
  have h := (closeRunCount_bound m).trans (Nat.add_le_add_right (modelMass_le_wire m) 3)
  have closed := closeRun_mass m
  have wire := modelMass_le_wire m
  have frames : (closeRun m).history.frames.length ≤ modelWireSize m := by unfold modelMass at closed wire; omega
  simp only [operationCount,closeRunCount_value]
  omega

 theorem pendingModelCount_wire (m : Model) (p : Pending) :
    modelWireSize (pendingModelCount m p).1 ≤ modelWireSize m+26*(p.scalars.length+1) := by
  have absorb := absorb_wire m (scalarBytes p.scalars)
  simp only [scalarBytes_length] at absorb
  unfold pendingModelCount
  cases h : p.nonce with
  | none => simp only [operationCount]; omega
  | some pair =>
    rcases pair with ⟨bits,nonce⟩
    have ground := operation_nonce_wire (modelAbsorb m (scalarBytes p.scalars)) bits (ByteCodec.encodeE nonce)
    simp only [operationCount] at ground ⊢
    omega

 theorem pendingModelCount_work (m : Model) (p : Pending) :
    (pendingModelCount m p).2 ≤ 3*modelWireSize m+1000*(p.scalars.length+1) := by
  have run : m.run.length ≤ modelWireSize m := by unfold modelWireSize; omega
  have absorb := absorb_wire m (scalarBytes p.scalars)
  simp only [scalarBytes_length] at absorb
  unfold pendingModelCount
  cases h : p.nonce with
  | none => simp only [operationCount,scalarBytes_length]; omega
  | some pair =>
    rcases pair with ⟨bits,nonce⟩
    have ground := operation_nonce_work (modelAbsorb m (scalarBytes p.scalars)) bits (ByteCodec.encodeE nonce)
    simp only [operationCount,scalarBytes_length] at *
    omega

 theorem stackWidthCount_work (c : Config) (n : Nat) :
    (stackWidthCount c n).2 ≤ 65*configSize c+8 := by
  simp only [stackWidthCount,scheduleWork,scalarCountWork,configSize]
  have h := Nat.min_le_right n (schedule c).length
  omega

 theorem completedModelCount_wire (c : Config) (domain statement : Digest32)
    (ps : List Pending) (W : Nat) (width : ∀ n, stackWidth c n ≤ W) :
    modelWireSize (completedModelCount c domain statement ps).1 ≤ pendingMass ps*(W+27) := by
  induction ps with
  | nil => simp [completedModelCount,modelWireSize,framesSize,pendingMass]
  | cons p ps ih =>
    have pending := pendingModelCount_wire (completedModelCount c domain statement ps).1 p
    have squeezed := operation_squeeze_wire (pendingModelCount (completedModelCount c domain statement ps).1 p).1
      (stackWidth c ps.length)
    have w := width ps.length
    simp only [completedModelCount,stackWidthCount,pendingMass,List.map_cons,List.sum_cons] at *
    nlinarith

 def modelWorkPolynomial (c : Config) (W b : Nat) : Nat :=
  (b+1)*(b+1)*(8*(W+27)+65*configSize c+1200)

 theorem modelWorkPolynomial_step (c : Config) (W a b : Nat) (positive : 1 ≤ a) :
    modelWorkPolynomial c W b+5*b*(W+27)+1026*a+65*configSize c+18 ≤
      modelWorkPolynomial c W (a+b) := by
  let A := 8*(W+27)+65*configSize c+1200
  have coefficient : 5*(W+27) ≤ A := by unfold A; omega
  have fixed : 65*configSize c+18 ≤ A := by unfold A; omega
  have scalar : 1026 ≤ A := by unfold A; omega
  have hb := Nat.mul_le_mul_left b coefficient
  have ha := Nat.mul_le_mul_left a scalar
  have ab : b ≤ a*b := by simpa only [one_mul] using Nat.mul_le_mul_right b positive
  have aa : 1 ≤ a*a := by nlinarith only [positive]
  have factors : b+a+1 ≤ a*a+2*a*b+2*a := by nlinarith only [ab,aa,positive]
  have increment := Nat.mul_le_mul_right A factors
  have rest := Nat.add_le_add (Nat.add_le_add hb ha) fixed
  have restBound : 5*b*(W+27)+1026*a+65*configSize c+18 ≤ (b+a+1)*A := by
    convert rest using 1 <;> ring
  calc
    _ ≤ (b+1)*(b+1)*A+(b+a+1)*A := by
      convert Nat.add_le_add_left restBound ((b+1)*(b+1)*A) using 1
      dsimp only [modelWorkPolynomial,A]
      ring
    _ ≤ (b+1)*(b+1)*A+(a*a+2*a*b+2*a)*A := Nat.add_le_add_left increment _
    _ = _ := by unfold modelWorkPolynomial A; ring

 theorem completedModelCount_work (c : Config) (domain statement : Digest32)
    (ps : List Pending) (W : Nat) (width : ∀ n, stackWidth c n ≤ W) :
    (completedModelCount c domain statement ps).2 ≤ modelWorkPolynomial c W (pendingMass ps) := by
  induction ps with
  | nil => simp [completedModelCount,modelWorkPolynomial,pendingMass]
  | cons p ps ih =>
    have wire := completedModelCount_wire c domain statement ps W width
    have pending := pendingModelCount_work (completedModelCount c domain statement ps).1 p
    have pendingWire := pendingModelCount_wire (completedModelCount c domain statement ps).1 p
    have squeezed := operation_squeeze_work (pendingModelCount (completedModelCount c domain statement ps).1 p).1
      (stackWidth c ps.length)
    have stack := stackWidthCount_work c ps.length
    have len := pendingMass_length ps
    have lengthCharge : ps.length ≤ pendingMass ps*(W+27) := by nlinarith
    have step := modelWorkPolynomial_step c W (p.scalars.length+1) (pendingMass ps) (by omega)
    simp only [completedModelCount,stackWidthCount,pendingMass,List.map_cons,List.sum_cons,modelWorkPolynomial] at *
    nlinarith

 theorem beforeModelCount_wire (c : Config) (domain statement : Digest32)
    (ps : List Pending) (W : Nat) (width : ∀ n, stackWidth c n ≤ W) :
    modelWireSize (beforeModelCount c domain statement ps).1 ≤ pendingMass ps*(W+27) := by
  cases ps with
  | nil => simp [beforeModelCount,completedModelCount,modelWireSize,framesSize,pendingMass]
  | cons p ps =>
    have h := completedModelCount_wire c domain statement ps W width
    have k := pendingModelCount_wire (completedModelCount c domain statement ps).1 p
    simp only [beforeModelCount,pendingMass,List.map_cons,List.sum_cons] at *
    nlinarith

 theorem beforeModelCount_work (c : Config) (domain statement : Digest32)
    (ps : List Pending) (W : Nat) (width : ∀ n, stackWidth c n ≤ W) :
    (beforeModelCount c domain statement ps).2 ≤ modelWorkPolynomial c W (pendingMass ps) := by
  cases ps with
  | nil => exact completedModelCount_work c domain statement [] W width
  | cons p ps =>
    have h := completedModelCount_work c domain statement ps W width
    have wire := completedModelCount_wire c domain statement ps W width
    have k := pendingModelCount_work (completedModelCount c domain statement ps).1 p
    have step := modelWorkPolynomial_step c W (p.scalars.length+1) (pendingMass ps) (by omega)
    simp only [beforeModelCount,pendingMass,List.map_cons,List.sum_cons,modelWorkPolynomial] at *
    nlinarith

 theorem prepend_wire (frames : List Frame) (m : Model) :
    modelWireSize (WHIRCallerPrefix.prepend frames m) = framesSize frames+modelWireSize m := by
  simp only [WHIRCallerPrefix.prepend,modelWireSize,framesSize,List.map_append,List.sum_append]
  omega

 theorem outputKeyCount_wire (c : Config) (entry : FramedHistory) (ps : List Pending)
    (block W : Nat) (width : ∀ n, stackWidth c n ≤ W) :
    framesSize (outputKeyCount c entry ps block).1.history.frames ≤
      framesSize entry.frames+pendingMass ps*(W+27)+1 := by
  have before := beforeModelCount_wire c entry.domain entry.statement ps W width
  have close := closeRun_wire (WHIRCallerPrefix.prepend entry.frames (beforeModelCount c entry.domain entry.statement ps).1)
  rw [prepend_wire] at close
  simp only [outputKeyCount,closeRunCount_value]
  unfold modelWireSize at before close
  omega

 theorem outputKeyCount_work (c : Config) (entry : FramedHistory) (ps : List Pending)
    (block W : Nat) (width : ∀ n, stackWidth c n ≤ W) :
    (outputKeyCount c entry ps block).2 ≤ modelWorkPolynomial c W (pendingMass ps)+
      2*framesSize entry.frames+pendingMass ps*(W+27)+7 := by
  have before := beforeModelCount_work c entry.domain entry.statement ps W width
  have wire := beforeModelCount_wire c entry.domain entry.statement ps W width
  have close := closeRunCount_bound (WHIRCallerPrefix.prepend entry.frames (beforeModelCount c entry.domain entry.statement ps).1)
  have mass := modelMass_le_wire (WHIRCallerPrefix.prepend entry.frames (beforeModelCount c entry.domain entry.statement ps).1)
  rw [prepend_wire] at mass
  have len := framesSize_length entry.frames
  simp only [outputKeyCount]
  omega

 theorem scheduleGuardWork_bound (c : Config) (ps : List Pending) :
    scheduleGuardWork c ps ≤ pendingMass ps*(98*configSize c+37)+32*configSize c+8 := by
  have len := pendingMass_length ps
  have scalars := pendingMass_scalars ps
  unfold scheduleGuardWork scheduleWork scalarCountWork configSize
  nlinarith

 theorem phaseWork_bound (c : Config) (ps : List Pending) :
    phaseWork c ps ≤ pendingMass ps*(98*configSize c+4106)+8 := by
  have len := pendingMass_length ps
  have scalars := pendingMass_scalars ps
  unfold phaseWork scheduleWork scalarCountWork configSize
  nlinarith

 theorem framesSize_drop (fs : List Frame) (n : Nat) :
    framesSize (fs.drop n) ≤ framesSize fs := by
  induction fs generalizing n with
  | nil => simp [framesSize]
  | cons f fs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have h := ih n
      simp only [List.drop_succ_cons,framesSize,List.map_cons,List.sum_cons] at h ⊢
      omega

 theorem parseSteps_mass (fs : List Frame) (ps : List Pending)
    (parsed : parseSteps fs = some ps) : pendingMass ps ≤ framesSize fs := by
  induction fs using (measure List.length).wf.induction generalizing ps with
  | h fs ih =>
    cases fs with
    | nil => simp [parseSteps] at parsed; subst ps; simp [pendingMass,framesSize]
    | cons f rest =>
      have restIH := ih rest (by exact Nat.lt_succ_self _)
      cases f with
      | nonce consumed bits nonce => simp [parseSteps] at parsed
      | absorb consumed bytes =>
        cases rest with
        | nil =>
          simp only [parseSteps] at parsed
          cases hs : parseExact (bytes.length/24) bytes with
          | none => simp [hs] at parsed
          | some xs =>
            have hx := parseExact_length _ _ _ hs
            simp only [hs] at parsed
            cases parsed
            have hd := Nat.div_le_self bytes.length 24
            simp only [pendingMass,framesSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,frameSize]
            omega
        | cons next tail =>
          have tailIH := ih tail (by exact Nat.lt_add_of_pos_right (by decide : 0 < 2))
          cases next with
          | nonce nextConsumed bits nonce =>
            rw [parseSteps] at parsed
            cases hs : parseExact (bytes.length/24) bytes with
            | none => simp [hs] at parsed
            | some xs =>
              have hx := parseExact_length _ _ _ hs
              cases hm : parseSteps tail with
              | none => simp [hs,hm] at parsed
              | some ms =>
                simp only [hs,hm] at parsed
                cases parsed
                have cap := tailIH ms hm
                have hd := Nat.div_le_self bytes.length 24
                simp only [pendingMass,framesSize,List.map_cons,List.sum_cons,frameSize] at *
                omega
          | absorb nextConsumed nextBytes =>
            rw [parseSteps] at parsed
            case x_1 => simp
            cases hs : parseExact (bytes.length/24) bytes with
            | none => simp [hs] at parsed
            | some xs =>
              have hx := parseExact_length _ _ _ hs
              cases hm : parseSteps (.absorb nextConsumed nextBytes::tail) with
              | none => simp [hs,hm] at parsed
              | some ms =>
                simp only [hs,hm] at parsed
                cases parsed
                have cap := restIH ms hm
                have hd := Nat.div_le_self bytes.length 24
                simp only [pendingMass,framesSize,List.map_cons,List.sum_cons,frameSize] at *
                omega

 theorem pendingValidityCount_work (context : AnchoredHeaderCodec.Context)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) (indices : List (Fin 8)) :
    (pendingValidityCount context cost indices).2.2 ≤
      (indices.map cost.pending).sum+8*indices.length+1 := by
  induction indices with
  | nil => simp [pendingValidityCount]
  | cons i is ih =>
    simp only [pendingValidityCount]
    split <;> simp only [List.map_cons,List.sum_cons,List.length_cons] <;> omega

 theorem recordValidityCount_work (saved : AnchoredHeaderCodec.Record)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) :
    (recordValidityCount saved cost).2.2 ≤ (List.ofFn cost.pending).sum+
      saved.point.length+3*saved.shape.logBatch+97 := by
  have pending := pendingValidityCount_work saved.context cost (List.ofFn (fun i : Fin 8 => i))
  have shape := PCSBCSCallerPayloadCost.shapeValidWork_le saved.shape
  simp only [List.length_ofFn,List.map_ofFn,Function.comp_def] at pending
  change (pendingValidityCount saved.context cost (List.ofFn (fun i : Fin 8 => i))).2.2 ≤
    (List.ofFn cost.pending).sum+65 at pending
  unfold recordValidityCount
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

 theorem recordValidityCount_work_reached (saved : AnchoredHeaderCodec.Record)
    (cost : PCSBCSCallerPayloadCost.OutputCosts) :
    (recordValidityCount saved cost).2.2 ≤
      (((recordValidityCount saved cost).2.1).map cost.pending).sum+
      saved.point.length+3*saved.shape.logBatch+97 := by
  have zeroWork := pendingValidityCount_work saved.context
    PCSBCSCallerPayloadCost.OutputCosts.zero (List.ofFn (fun i : Fin 8 => i))
  have zeroCap : (pendingValidityCount saved.context PCSBCSCallerPayloadCost.OutputCosts.zero
      (List.ofFn (fun i : Fin 8 => i))).2.2 ≤ 65 := by
    simpa [PCSBCSCallerPayloadCost.OutputCosts.zero] using zeroWork
  have prices := pendingValidityCount_price_exact saved.context cost (List.ofFn (fun i : Fin 8 => i))
  have shape := PCSBCSCallerPayloadCost.shapeValidWork_le saved.shape
  unfold recordValidityCount
  split
  · split
    · dsimp only; omega
    · simp only [List.map_nil,List.sum_nil]; omega
  · simp only [List.map_nil,List.sum_nil]; omega

 def pendingKeyPolynomial (c : Config) (W P : Nat) : Nat :=
  (P+1)*(P+2050)+modelWorkPolynomial c W (P+1)+
    2*(P+1)*(W+27)+(P+1)*(98*configSize c+37)+32*configSize c+
    10*P+1050

 theorem parsePendingKeyCount_work (p : ParameterBounds.Profile) (entry : FramedHistory)
    (key : Coordinate) (W P : Nat)
    (width : ∀ n, stackWidth (ParameterBounds.config p) n ≤ W)
    (entryCap : framesSize entry.frames ≤ P) (keyCap : framesSize key.history.frames ≤ P) :
    (parsePendingKeyCount p entry key).2 ≤ pendingKeyPolynomial (ParameterBounds.config p) W P := by
  let fs := key.history.frames.drop entry.frames.length
  have fsCap := (framesSize_drop key.history.frames entry.frames.length).trans keyCap
  have steps := (parseStepsCount_bound fs).trans (stepsBudget_polynomial fs)
  have stepsCap : (parseStepsCount fs).2 ≤ (P+1)*(P+2050)+1 := by
    apply steps.trans
    gcongr
  have entryLen := (framesSize_length entry.frames).trans entryCap
  dsimp only [fs] at stepsCap
  have minCap : min entry.frames.length key.history.frames.length ≤ P :=
    (Nat.min_le_left _ _).trans entryLen
  unfold parsePendingKeyCount
  cases hs : (parseStepsCount fs).1 with
  | none => simp only [fs] at hs; simp only [hs]; unfold pendingKeyPolynomial; omega
  | some chronological =>
    have parsed : parseSteps fs = some chronological := by rw [← parseStepsCount_value,hs]
    have mass := (parseSteps_mass fs chronological parsed).trans fsCap
    let messages := chronological.reverse++[initialPending]
    have messagesMass : pendingMass messages ≤ P+1 := by
      simpa only [messages,pendingMass,List.map_append,List.sum_append,List.map_reverse,List.sum_reverse,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,initialPending,List.length_nil,
        Nat.zero_add,Nat.add_zero] using Nat.add_le_add_right mass 1
    have chronoLen := (pendingMass_length chronological).trans mass
    have guard := scheduleGuardWork_bound (ParameterBounds.config p) messages
    have modelCap : modelWorkPolynomial (ParameterBounds.config p) W (pendingMass messages) ≤
        modelWorkPolynomial (ParameterBounds.config p) W (P+1) := by unfold modelWorkPolynomial; gcongr
    have guardCap : scheduleGuardWork (ParameterBounds.config p) messages ≤
        (P+1)*(98*configSize (ParameterBounds.config p)+37)+32*configSize (ParameterBounds.config p)+8 := by
      apply guard.trans
      gcongr
    have cursorCap : pendingMass messages*(W+27) ≤ (P+1)*(W+27) := by gcongr
    simp only [fs] at hs
    simp only [hs]
    cases key.terminal <;> simp only []
    all_goals try (unfold pendingKeyPolynomial; omega)
    rename_i block
    have r := outputKeyCount_work (ParameterBounds.config p) entry messages block W width
    have wire := outputKeyCount_wire (ParameterBounds.config p) entry messages block W width
    unfold coordinateEqWork pendingKeyPolynomial
    change _ ≤ _
    dsimp only [messages] at r wire guardCap modelCap cursorCap
    nlinarith only [entryCap,keyCap,entryLen,minCap,stepsCap,chronoLen,r,wire,guardCap,modelCap,cursorCap]

 theorem parsePendingKeyCount_mass (p : ParameterBounds.Profile) (entry : FramedHistory)
    (key : Coordinate) (messages : List Pending)
    (returned : (parsePendingKeyCount p entry key).1 = some messages) :
    pendingMass messages ≤ framesSize key.history.frames+1 := by
  unfold parsePendingKeyCount at returned
  cases hs : (parseStepsCount (key.history.frames.drop entry.frames.length)).1 with
  | none => simp [hs] at returned
  | some chronological =>
    have parsed : parseSteps (key.history.frames.drop entry.frames.length) = some chronological := by
      rw [← parseStepsCount_value,hs]
    have h := (parseSteps_mass _ _ parsed).trans (framesSize_drop key.history.frames entry.frames.length)
    simp only [hs] at returned
    cases terminal : key.terminal with
    | commitment _ => simp [terminal] at returned
    | powBase _ _ => simp [terminal] at returned
    | output block =>
      simp only [terminal] at returned
      split at returned
      · have same := Option.some.inj returned
        subst messages
        simpa only [pendingMass,List.map_append,List.sum_append,List.map_reverse,List.sum_reverse,
          List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,initialPending,List.length_nil,
          Nat.zero_add,Nat.add_zero] using Nat.add_le_add_right h 1
      · contradiction

 /-- The exact caller work is exposed, not a source-work certificate. -/
 def reachedCallerWork (p : ParameterBounds.Profile) (layout : CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory)
    (answers : Coordinate → Digest32) (cost : PCSBCSCallerPayloadCost.OutputCosts) : Nat :=
  if (recordValidityCount saved cost).1 = true ∧ profileShape p saved.shape then
    match (entryTokensCount entry answers).1 with
    | none => 0
    | some ts => (PCSBCSCallerPayloadCost.freshInterpret layout saved cost ts).work
  else 0

 theorem parseReferencesCount_work_of_reached (p : ParameterBounds.Profile) (layout : CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (key : Coordinate) (cost : PCSBCSCallerPayloadCost.OutputCosts)
    (ts : List CallerToken) (messages : List Pending)
    (valid : (recordValidityCount saved cost).1 = true ∧ profileShape p saved.shape)
    (tokens : (entryTokensCount entry answers).1 = some ts)
    (caller : (PCSBCSCallerPayloadCost.freshInterpret layout saved cost ts).value.isSome = true)
    (pending : (parsePendingKeyCount p entry key).1 = some messages) :
    (parseReferencesCount p layout saved entry answers key cost).2.2 =
      (entryTokensCount entry answers).2.2+
      (PCSBCSCallerPayloadCost.freshInterpret layout saved cost ts).work+
      (parsePendingKeyCount p entry key).2+phaseWork (ParameterBounds.config p) messages+
      (recordValidityCount saved cost).2.2+128 := by
  cases hc : (PCSBCSCallerPayloadCost.freshInterpret layout saved cost ts).value with
  | none => simp [hc] at caller
  | some claims => simp only [parseReferencesCount,ite_eq_left valid,tokens,hc,pending]

 theorem parseReferencesCount_work (p : ParameterBounds.Profile) (layout : CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FramedHistory) (answers : Coordinate → Digest32)
    (key : Coordinate) (cost : PCSBCSCallerPayloadCost.OutputCosts) (W P : Nat)
    (width : ∀ n, stackWidth (ParameterBounds.config p) n ≤ W)
    (entryCap : framesSize entry.frames ≤ P) (keyCap : framesSize key.history.frames ≤ P)
    (pointCap : saved.point.length ≤ P) (batchCap : saved.shape.logBatch ≤ P) :
    (parseReferencesCount p layout saved entry answers key cost).2.2 ≤
      entryParserPolynomial P+reachedCallerWork p layout saved entry answers cost+
      pendingKeyPolynomial (ParameterBounds.config p) W P+
      (P+1)*(98*configSize (ParameterBounds.config p)+4106)+
      (List.ofFn cost.pending).sum+4*P+233 := by
  have valid := recordValidityCount_work saved cost
  have tokens := (entryTokensCount_bound entry answers P entryCap).2
  have pending := parsePendingKeyCount_work p entry key W P width entryCap keyCap
  by_cases gate : (recordValidityCount saved cost).1 = true ∧ profileShape p saved.shape
  · simp only [parseReferencesCount,reachedCallerWork,ite_eq_left gate]
    cases ht : (entryTokensCount entry answers).1 with
    | none => dsimp only; omega
    | some ts =>
      dsimp only
      cases hc : (PCSBCSCallerPayloadCost.freshInterpret layout saved cost ts).value with
      | none => dsimp only; omega
      | some claims =>
        dsimp only
        cases hp : (parsePendingKeyCount p entry key).1 with
        | none => dsimp only; omega
        | some messages =>
          dsimp only
          have mass := (parsePendingKeyCount_mass p entry key messages hp).trans (Nat.add_le_add_right keyCap 1)
          have phase := phaseWork_bound (ParameterBounds.config p) messages
          have phaseCap : phaseWork (ParameterBounds.config p) messages ≤
              (P+1)*(98*configSize (ParameterBounds.config p)+4106)+8 := by
            apply phase.trans
            gcongr
          omega
  · simp only [parseReferencesCount,reachedCallerWork,ite_eq_right gate]
    omega

#print axioms completedModelCount_work
#print axioms outputKeyCount_wire
#print axioms parseSteps_mass
#print axioms parsePendingKeyCount_work
#print axioms recordValidityCount_work
#print axioms recordValidityCount_work_reached
#print axioms parseReferencesCount_work_of_reached
#print axioms parseReferencesCount_work

end Whir.PCSBCSSourceReferencePolynomialBound
