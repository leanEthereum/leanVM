/-
  LeanVM.Protocol.EndToEnd.Sound.SkelFront

  The front phases' skeletons: the table sumcheck, the public input, the Keccak reduction, and
  the out-of-domain sample and ring switching around them, fixed by the layout.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelBus
import LeanVM.Protocol.EndToEnd.Complete.TableMath
public import LeanVM.Protocol.Verifier.Claims
import LeanVM.Protocol.Verifier.Phases
public import LeanVM.Protocol.EndToEnd.Sound.Assemble

/-!
# The front phases' skeletons

The table sumcheck reads each table's evaluations, one table per form the bus left
(`skel_tableSumcheckClaims`); its claims on the `KECCAK` output columns are at the `KECCAK`
table's point, of `kLen` coordinates (`KL`). The Keccak reduction's skeleton is fixed by that
length (`skel_verifyKeccak`), so the front program's is fixed by the layout (`skel_frontProg`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier

@[expose] public section

/-- The claims on `KECCAK` output columns are at points of `L` coordinates. -/
def KL (L : ℕ) (claims : List Verifier.ColumnClaim) : Prop :=
  ∀ c ∈ claims, c.column ∈ keccakOutputColumns → c.point.length = L

theorem KL.of_off {L : ℕ} {cl : List Verifier.ColumnClaim} (h : OffKeccak cl) : KL L cl :=
  fun c hc hk ↦ absurd hk (h c hc)

theorem KL.append {L : ℕ} {a b : List Verifier.ColumnClaim} (ha : KL L a) (hb : KL L b) :
    KL L (a ++ b) := fun c hc hk ↦ by
  rcases List.mem_append.mp hc with hc | hc
  · exact ha c hc hk
  · exact hb c hc hk

/-- Only the `KECCAK` table's columns are `KECCAK` output columns. -/
theorem table_columns_keccak : ∀ t ∈ tables, ∀ j < t.width,
    globalColumnBases.getD t.opcode 0 + j ∈ keccakOutputColumns → t.opcode = opKeccak := by
  decide +kernel

/-- A table's opcode is its index. -/
theorem tables_opcode : ∀ i (h : i < tables.length), tables[i].opcode = i := by
  decide +kernel

theorem map_comp_isSome_some (l : List E) :
    l.map (Option.isSome ∘ some) = List.replicate l.length true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.replicate_succ]

theorem map_fst_zip {α β : Type} : ∀ (a : List α) (b : List β),
    (List.zip a b).map Prod.fst = a.take b.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: a, y :: b => by simp [map_fst_zip a b]

/-! ## The table sumcheck -/

/-- The skeleton of the tables' reads. -/
def skTables (ts : List Table) : List Op := ts.flatMap fun t ↦ List.replicate t.width .read

theorem skel_tableTermsClaims (cp fp pt : List E) (L : ℕ) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim), KL L claims →
      (∀ r ∈ rows, r.1 ∈ tables ∧ (r.1.opcode = opKeccak → (pt.take r.2.1).length = L)) →
      SkelP (tableTermsClaims cp fp pt rows cursor final claims) (skTables (rows.map (·.1)))
        fun r ↦ KL L r.2
  | [], _, _, claims, hc, _ => SkelP.ret hc
  | (table, height, forms, weight) :: rest, cursor, final, claims, hc, hr => by
    unfold tableTermsClaims
    simp only [VerifierProgram.bind_eq]
    obtain ⟨hmem, hk⟩ := hr _ List.mem_cons_self
    refine ((skel_readScalars table.width).bind fun ev hev ↦
      skel_tableTermsClaims cp fp pt L rest _ _ _ (KL.append hc ?_)
        (fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr'))).mono (by simp [skTables]) fun _ h ↦ h
    intro c hc' hcol
    obtain ⟨⟨v, col⟩, hm, rfl⟩ := List.mem_map.mp hc'
    have hcol' : col < table.width := by
      have := (List.mem_zipIdx hm).2.1
      omega
    exact hk (table_columns_keccak _ hmem _ hcol' hcol)

/-- The `KECCAK` table's point's length: its log-height, at most the sumcheck's rounds. -/
def kLen (heights : List ℕ) : ℕ := min (heights.getD opKeccak 0) (heights.foldl max 0)

/-- The skeleton of the table sumcheck. -/
def skTableSumcheck (heights : List ℕ) : List Op :=
  skSum 4 (List.replicate (heights.foldl max 0) false) ++
    skTables (tables.take (min heights.length tables.length))

theorem skel_tableSumcheckClaims (heights : List ℕ) (forms : List (List Form))
    (cp fp eqp : List E) (target : E) (hforms : forms.length = tables.length) :
    SkelP (tableSumcheckClaims heights forms cp fp eqp target) (skTableSumcheck heights)
      fun cl ↦ KL (kLen heights) cl := by
  unfold tableSumcheckClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  have hk : ∀ r : List E × E, r.1.length = (List.replicate (heights.foldl max 0) (none : Option E)).length →
      SkelP ((tableTermsClaims cp fp r.1.reverse (List.zip tables (List.zip heights (List.zip forms
        (tableWeights heights eqp r.1.reverse)))) 0 0 []).bind fun x ↦
          (VerifierProgram.require (x.1 = r.2)).bind fun _ ↦ VerifierProgram.ret x.2)
        (skTables (tables.take (min heights.length tables.length)))
        fun cl ↦ KL (kLen heights) cl := by
    intro r hr
    have hrows : ∀ row ∈ List.zip tables (List.zip heights (List.zip forms
        (tableWeights heights eqp r.1.reverse))),
        row.1 ∈ tables ∧ (row.1.opcode = opKeccak → (r.1.reverse.take row.2.1).length =
          kLen heights) := by
      intro row hrow
      refine ⟨(List.of_mem_zip hrow).1, fun hop ↦ ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrow
      simp only [List.getElem_zip] at hop ⊢
      have hit : i < tables.length := by
        simp only [List.length_zip] at hi; omega
      rw [tables_opcode i hit] at hop
      subst hop
      have hih : opKeccak < heights.length := by simp only [List.length_zip] at hi; omega
      simp only [List.length_take, List.length_reverse, hr, List.length_replicate, kLen,
        List.getD_eq_getElem _ _ hih]
    have hsk : skTables ((List.zip tables (List.zip heights (List.zip forms
        (tableWeights heights eqp r.1.reverse)))).map Prod.fst) =
        skTables (tables.take (min heights.length tables.length)) := by
      rw [map_fst_zip]
      congr 2
      simp only [List.length_zip, EndToEnd.Complete.length_tableWeights, hforms]
      omega
    exact (((skel_tableTermsClaims cp fp _ (kLen heights) _ 0 0 [] (fun _ h ↦ by simp at h)
      hrows).mono hsk fun _ h ↦ h).bind fun r' hr' ↦ (skel_require (r'.1 = r.2)).bind fun _ _ ↦
        SkelP.ret (Q := fun cl ↦ KL (kLen heights) cl) hr').mono (by simp) fun _ h ↦ h
  exact ((skel_sumcheck 4 target _).bind fun r hr ↦ hk r hr).mono
    (by simp [skTableSumcheck, List.map_replicate]) fun _ h ↦ h

/-- The skeleton of the table phase. -/
def skTablePhase (heights : List ℕ) : List Op :=
  skGrind (grindingBits ((tables.map Table.nConstraints).sum + nTrees - 1)) ++ [.sample] ++
    skTableSumcheck heights

theorem skel_tablePhaseClaims (layout : Verifier.Layout) (bus : BusResult)
    (hbus : bus.forms.length = tables.length ∧ OffKeccak bus.claims) :
    SkelP (tablePhaseClaims layout bus) (skTablePhase layout.tableLogHeights)
      fun cl ↦ KL (kLen layout.tableLogHeights) cl := by
  unfold tablePhaseClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_grindProofOfWork _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    (skel_tableSumcheckClaims _ _ _ _ _ _ hbus.1).bind fun cl hcl ↦
      SkelP.ret (Q := fun cl ↦ KL (kLen layout.tableLogHeights) cl)
        (KL.append (KL.of_off hbus.2) hcl)).mono (by simp [skTablePhase, List.append_assoc])
    fun _ h ↦ h

/-! ## The public input -/

theorem skel_publicInputPhase (layout : Verifier.Layout) (publicInput : Digest) :
    SkelP (publicInputPhase layout publicInput) [.sample] OffKeccak := by
  rw [publicInputPhase_eq]
  refine (skel_sampleChallenge.bind fun c _ ↦ (skel_liftOption _).mono rfl fun cl hcl ↦ ?_).mono
    rfl fun _ h ↦ h
  rw [publicClaimsOf_spec hcl]
  obtain ⟨h0, h1, -, -⟩ := bus_columns_off
  intro c hc
  simp only [publicClaims, List.zipWith_cons_cons, List.zipWith_nil_left, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact h0
  · exact h1

/-! ## The Keccak reduction -/

/-- The skeleton of a Keccak layer at a point of `P` coordinates. -/
def skLayer (P : ℕ) : List Op :=
  List.replicate productBits .read ++ skGrind (grindingBits (productBits - 1)) ++ [.sample] ++
    skSum 3 (List.replicate P true) ++ skSum 4 (List.replicate keccakLocalBits false) ++
    List.replicate 3 .read ++ skGrind (grindingBits 2) ++ [.sample]

theorem skel_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    SkelP (verifyKeccakLayer logSteps step claim) (skLayer claim.point.length)
      fun c ↦ c.point.length = claim.point.length := by
  unfold verifyKeccakLayer
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_readScalars _).bind fun _ _ ↦ (skel_require _).bind fun _ _ ↦
    (skel_grindProofOfWork _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    (skel_sumcheck 3 _ (claim.point.map some)).bind fun r hr ↦ (skel_sumcheck 4 _ _).bind
      fun r' _ ↦ (skel_readScalars 3).bind fun _ _ ↦ (skel_require _).bind fun _ _ ↦
    (skel_grindProofOfWork _).bind fun _ _ ↦ skel_sampleChallenge.bind fun _ _ ↦
    SkelP.ret (Q := fun c : KeccakClaim ↦ c.point.length = claim.point.length)
      (by simpa using hr)).mono
    (by simp [skLayer, map_comp_isSome_some, List.append_assoc]) fun _ h ↦ h

theorem skel_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    SkelP (keccakLayers logSteps steps claim) (steps.flatMap fun _ ↦ skLayer claim.point.length)
      fun c ↦ c.point.length = claim.point.length
  | [], claim => SkelP.ret rfl
  | step :: steps, claim => by
    unfold keccakLayers
    simp only [VerifierProgram.bind_eq]
    exact ((skel_verifyKeccakLayer logSteps step claim).bind fun c hc ↦
      ((skel_keccakLayers logSteps steps c).mono (by rw [hc]) fun _ h ↦ h.trans hc)).mono
      (by simp) fun _ h ↦ h

/-- The skeleton of `open`. -/
def skOpen : List Op := skSum 3 (List.replicate qkeccakSlotBits false)

theorem skel_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    SkelP (keccakOpen logSteps claim first count value) skOpen fun _ ↦ True := by
  unfold keccakOpen
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_sumcheck 3 _ _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : List E × List E × E ↦ True) trivial).mono (by simp [skOpen])
    fun _ h ↦ h

/-- The skeleton of the Keccak reduction at an instance point of `L` coordinates. -/
def skKeccak (L : ℕ) : List Op :=
  skGrind (grindingBits (keccakSegmentBits + keccakLaneBits)) ++
    List.replicate keccakSegmentBits .sample ++ List.replicate keccakLaneBits .sample ++ [.read] ++
    (List.range keccakDepth).flatMap (fun _ ↦ skLayer (L - 4 + keccakSegmentBits)) ++
    skOpen ++ [.read] ++ skSum 3 (List.replicate 4 false) ++ skOpen ++ List.replicate kBits .read

theorem skel_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    SkelP (verifyKeccak logSteps inst output) (skKeccak inst.length) fun _ ↦ True := by
  have h1 : 1 < keccakSegments := by decide
  unfold verifyKeccak
  simp only [h1, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_grindProofOfWork _).bind fun _ _ ↦ (skel_sampleChallenges _).bind fun seg hseg ↦
    (skel_sampleChallenges _).bind fun _ _ ↦ skel_readScalar.bind fun _ _ ↦
    ((skel_keccakLayers logSteps (List.range keccakDepth) _).mono
      (sk' := (List.range keccakDepth).flatMap fun _ ↦ skLayer (inst.length - 4 + keccakSegmentBits))
      (by simp [keccakFirstClaim, hseg]) fun _ h ↦ h).bind fun claim _ ↦
    (skel_keccakOpen _ _ _ _ _).bind fun _ _ ↦ skel_readScalar.bind fun _ _ ↦
    (skel_require _).bind fun _ _ ↦ (skel_sumcheck 3 _ _).bind fun _ _ ↦
    (skel_keccakOpen _ _ _ _ _).bind fun _ _ ↦ (skel_readScalars kBits).bind fun _ _ ↦
    (skel_require _).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : List Verifier.ColumnClaim × List E × List E ↦ True) trivial).mono
    (by simp only [skKeccak, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil, List.map_replicate, Option.isSome_none]) fun _ h ↦ h

theorem skel_keccakPhaseClaims (layout : Verifier.Layout) (claims : List Verifier.ColumnClaim)
    {L : ℕ} (hc : KL L claims) :
    SkelP (keccakPhaseClaims layout claims) (skKeccak L) fun _ ↦ True := by
  unfold keccakPhaseClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_require _).bind fun _ hreq ↦
    ((skel_verifyKeccak _ _ _).mono (sk' := skKeccak L) (by
      have hlen : ((claims.filter fun c ↦ decide (c.column ∈ keccakOutputColumns)).headD
          default).point.length = L := by
        obtain ⟨hmap, -⟩ := hreq
        rcases hl : claims.filter (fun c ↦ decide (c.column ∈ keccakOutputColumns)) with
          _ | ⟨c, rest⟩
        · rw [hl] at hmap
          simp [keccakOutputColumns] at hmap
        · have hcm : c ∈ claims.filter (fun c ↦ decide (c.column ∈ keccakOutputColumns)) := by
            rw [hl]; exact List.mem_cons_self
          obtain ⟨hcm, hck⟩ := List.mem_filter.mp hcm
          rw [hl, List.headD_cons]
          exact hc c hcm (of_decide_eq_true hck)
      rw [hlen]) fun _ h ↦ h).bind fun _ _ ↦
    SkelP.ret (Q := fun _ : List Verifier.ColumnClaim × List E × List E ↦ True) trivial).mono
    (by simp) fun _ h ↦ h

/-! ## Around the front -/

/-- The skeleton of the out-of-domain sample. -/
def skOod (stackLog : ℕ) : List Op :=
  skGrind Whir.oodGrindingBits ++ List.replicate stackLog .sample ++ [.read]

theorem skel_readOod (stackLog : ℕ) : SkelP (readOod stackLog) (skOod stackLog) fun _ ↦ True := by
  unfold readOod
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact ((skel_grindProofOfWork _).bind fun _ _ ↦ (skel_sampleChallenges _).bind fun _ _ ↦
    skel_readScalar.bind fun _ _ ↦ SkelP.ret (Q := fun _ : StackClaim ↦ True) trivial).mono
    (by simp [skOod]) fun _ h ↦ h

/-- The skeleton of ring switching. -/
def skRing : List Op := skGrind Whir.batchGrindingBits ++ List.replicate (2 * ringMapWidth) .sample

theorem skel_ringSwitch (point s : List E) : SkelP (ringSwitch point s) skRing fun _ ↦ True := by
  rw [ringSwitch_eq]
  exact ((skel_grindProofOfWork _).bind fun _ _ ↦ (skel_sampleChallenges _).bind fun _ _ ↦
    (skel_liftOption _).weaken).mono (by simp [skRing]) fun _ h ↦ h

/-- The skeleton of the front phases. -/
def skFront (layout : Verifier.Layout) : List Op :=
  skBus (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth ++
    skTablePhase layout.tableLogHeights ++ [.sample] ++ skKeccak (kLen layout.tableLogHeights)

/-- **The front phases' skeleton**, fixed by the layout. -/
theorem skel_frontProg (layout : Verifier.Layout) (pd : Digest) :
    SkelP (frontProg computedBytecodeValue layout pd) (skFront layout) fun _ ↦ True := by
  unfold frontProg
  simp only [VerifierProgram.bind_eq]
  exact ((skel_verifyBusBalance layout).bind fun bus hbus ↦
    (skel_tablePhaseClaims layout bus hbus).bind fun cl hcl ↦
    (skel_publicInputPhase layout pd).bind fun pc hpc ↦
    skel_keccakPhaseClaims layout _ (KL.append hcl (KL.of_off hpc))).mono
    (by simp [skFront, List.append_assoc]) fun _ h ↦ h

end
end LeanVM.Protocol.EndToEnd.Sound
