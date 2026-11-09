module

public import VCVio.OracleComp.SimSemantics.StateT.Measure
public import XmssSecurity.Proof.EvalDistEq
public import XmssSecurity.Proof.Bridge.Naturality
public import XmssSecurity.Proof.Bridge.Program
public import XmssSecurity.Proof.Deterministic.FreshRequests
public import XmssSecurity.Proof.RandomOracle

@[expose] public section

/-!
# The top randomizer bases

Key generation reads the table of top randomizer bases once per top key, at the bottom root it has
just computed. A uniform table read that way is a uniform base per key: both are a fresh uniform
answer per request, the requests being distinct.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- Requests for the base of key `b` at root `r`. -/
abbrev TableReq := TopRndPos →ₒ Randomness
/-- Requests for the base of key `b`. -/
abbrev KeyReq := TopIndex →ₒ Randomness

/-- Hash queries in a world with requests. -/
@[reducible] def hashQueryIn {κ : Type} (Req : OracleSpec κ) : HasQuery HashSpec (OracleComp (OracleWorld + Req)) :=
  ⟨fun x => liftM ((OracleWorld + Req).query (.inl (.inr x)))⟩

/-- Hash queries answered by the random oracle. -/
@[reducible] noncomputable def hashQueryState : HasQuery HashSpec (StateT (QueryCache HashSpec) ProbComp) :=
  ⟨fun x => randomOracle x⟩

/-- A hash computation in a world with requests. -/
def liftHash {κ : Type} (Req : OracleSpec κ) : QueryImpl HashSpec (OracleComp (OracleWorld + Req)) :=
  fun x => liftM ((OracleWorld + Req).query (.inl (.inr x)))

/-- Key generation requesting the base of each key at its root. -/
def keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) :=
  @Concrete.honestKeygen (OracleComp (OracleWorld + TableReq)) _ (hashQueryIn TableReq) parameter secret
    topSecret fun key root => liftM ((OracleWorld + TableReq).query (.inr (key, root)))

/-- Key generation requesting the base of each key. -/
def keygenKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) :=
  @Concrete.honestKeygen (OracleComp (OracleWorld + KeyReq)) _ (hashQueryIn KeyReq) parameter secret
    topSecret fun key _ => liftM ((OracleWorld + KeyReq).query (.inr key))

/-- Key generation in the random oracle's state monad. -/
noncomputable def keygenState (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest)
    (topBase : TopIndex → Digest → StateT (QueryCache HashSpec) ProbComp Randomness) :=
  @Concrete.honestKeygen (StateT (QueryCache HashSpec) ProbComp) _ hashQueryState parameter secret topSecret
    topBase

/-! ## Naturality instances -/

theorem state_of_hash (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Digest → Randomness) :
    simulateQ randomOracle (Concrete.honestKeygen parameter secret topSecret
        fun key root => (pure (topBase key root) : OracleComp HashSpec Randomness)) =
      keygenState parameter secret topSecret fun key root => pure (topBase key root) := by
  have h := nat_honestKeygen (inst₁ := (inferInstance : HasQuery HashSpec (OracleComp HashSpec)))
    (inst₂ := hashQueryState) randomOracle (fun x => by
      change simulateQ randomOracle (liftM (HashSpec.query x) : OracleComp HashSpec _) = randomOracle x
      rw [simulateQ_spec_query]) parameter secret topSecret
    fun key root => (pure (topBase key root) : OracleComp HashSpec Randomness)
  simp only [simulateQ_pure] at h
  exact h

theorem state_of_req {κ : Type} {Req : OracleSpec κ} (reqImpl : QueryImpl Req (StateT (QueryCache HashSpec) ProbComp))
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest)
    (topBase : TopIndex → Digest → OracleComp (OracleWorld + Req) Randomness) :
    simulateQ (romImpl + reqImpl) (@Concrete.honestKeygen (OracleComp (OracleWorld + Req)) _ (hashQueryIn Req)
        parameter secret topSecret topBase) =
      keygenState parameter secret topSecret fun key root => simulateQ (romImpl + reqImpl) (topBase key root) :=
  nat_honestKeygen (inst₁ := hashQueryIn Req) (inst₂ := hashQueryState) (romImpl + reqImpl) (fun x => by
    change simulateQ (romImpl + reqImpl) (liftM ((OracleWorld + Req).query (.inl (.inr x))) :
      OracleComp (OracleWorld + Req) _) = randomOracle x
    rw [simulateQ_spec_query]
    rfl) parameter secret topSecret topBase

theorem liftHash_query {κ : Type} (Req : OracleSpec κ) (x : HashInput) :
    simulateQ (liftHash Req) (HasQuery.query (spec := HashSpec) (m := OracleComp HashSpec) x) =
      HasQuery.query (spec := HashSpec) (m := OracleComp (OracleWorld + Req)) (self := hashQueryIn Req) x := by
  change simulateQ (liftHash Req) (liftM (HashSpec.query x) : OracleComp HashSpec _) = _
  rw [simulateQ_spec_query]
  rfl


theorem treeNode_lift {κ : Type} (Req : OracleSpec κ) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    @Concrete.treeNode (OracleComp (OracleWorld + Req)) _ (hashQueryIn Req) parameter secret levels node =
      simulateQ (liftHash Req) (Concrete.treeNode parameter secret levels node) :=
  (nat_treeNode (inst₁ := inferInstance) (inst₂ := hashQueryIn Req) (liftHash Req) (liftHash_query Req)
    parameter secret levels node).symm

theorem topTreeNode_lift {κ : Type} (Req : OracleSpec κ) (parameter : PublicParameter)
    (topSecret : TopIndex → ChainIndex → Digest) (levels : Nat) (node : TopNode) :
    @Concrete.topTreeNode (OracleComp (OracleWorld + Req)) _ (hashQueryIn Req) parameter topSecret levels node =
      simulateQ (liftHash Req) (Concrete.topTreeNode parameter topSecret levels node) :=
  (nat_topTreeNode (inst₁ := inferInstance) (inst₂ := hashQueryIn Req) (liftHash Req) (liftHash_query Req)
    parameter topSecret levels node).symm

theorem topSignFrom_lift {κ : Type} (Req : OracleSpec κ) (parameter : PublicParameter) (key : TopIndex)
    (root : Digest) (base : Randomness) (attempts trial : Nat) :
    @Concrete.topSignFrom (OracleComp (OracleWorld + Req)) _ (hashQueryIn Req) parameter key root base attempts
        trial =
      simulateQ (liftHash Req) (Concrete.topSignFrom parameter key root base attempts trial) :=
  (nat_topSignFrom (inst₁ := inferInstance) (inst₂ := hashQueryIn Req) (liftHash Req) (liftHash_query Req)
    parameter key root base attempts trial).symm

/-! ## Distinct requests -/

theorem freshRequests_liftHash_bind {Request Answer α β : Type} (used : Set Request)
    (c : OracleComp HashSpec α) (k : α → OracleComp (OracleWorld + (Request →ₒ Answer)) β)
    (hk : ∀ a, FreshRequests used (k a)) :
    FreshRequests used (simulateQ (liftHash (Request →ₒ Answer)) c >>= k) := by
  induction c using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure, pure_bind] using hk a
  | query_bind x next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact FreshRequests.base (.inr x) _ fun a => ih a

theorem freshRequests_steps {Request Answer R γ β : Type} {n : Nat} (req : Fin n → R → Request)
    (hreq : ∀ i j r r', req i r = req j r' → i = j)
    (g : Fin n → OracleComp HashSpec R) (h : Fin n → R → Answer → OracleComp HashSpec γ)
    (k : (Fin n → γ) → OracleComp (OracleWorld + (Request →ₒ Answer)) β)
    (hk : ∀ v used', FreshRequests used' (k v)) (used : Set Request) (hused : ∀ i r, req i r ∉ used) :
    FreshRequests used (Concrete.sequenceFin (fun i => simulateQ (liftHash _) (g i) >>= fun r =>
      liftM ((OracleWorld + (Request →ₒ Answer)).query (.inr (req i r))) >>= fun x =>
        simulateQ (liftHash _) (h i r x)) >>= k) := by
  induction n generalizing used with
  | zero =>
      simp only [Concrete.sequenceFin, pure_bind]
      exact hk _ _
  | succ n ih =>
      simp only [Concrete.sequenceFin, bind_assoc]
      refine freshRequests_liftHash_bind _ _ _ fun r => ?_
      refine FreshRequests.request _ (hused 0 r) _ fun x => ?_
      refine freshRequests_liftHash_bind _ _ _ fun y => ?_
      have := ih (fun i => req i.succ) (fun i j r r' heq => Fin.succ_injective _ (hreq _ _ _ _ heq))
        (fun i => g i.succ) (fun i => h i.succ) (fun tail => k (Fin.cases y tail))
        (fun v used' => hk _ _) (insert (req 0 r) used) (fun i r' hmem => by
          rcases Set.mem_insert_iff.mp hmem with heq | hmem
          · exact Fin.succ_ne_zero i (hreq _ _ _ _ heq)
          · exact hused _ _ hmem)
      simpa only [bind_assoc, pure_bind] using this

theorem freshRequests_keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) :
    FreshRequests ∅ (keygenTable parameter secret topSecret) := by
  unfold keygenTable Concrete.honestKeygen
  simp only [treeNode_lift, topTreeNode_lift, topSignFrom_lift]
  exact freshRequests_steps (fun key root => (key, root)) (fun i j r r' h => (Prod.mk.inj h).1) _ _ _
    (fun v used' => freshRequests_liftHash_bind _ _ _ fun _ => .pure _) ∅ (fun _ _ h => h)

theorem freshRequests_keygenKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) :
    FreshRequests ∅ (keygenKey parameter secret topSecret) := by
  unfold keygenKey Concrete.honestKeygen
  simp only [treeNode_lift, topTreeNode_lift, topSignFrom_lift]
  exact freshRequests_steps (fun key _ => key) (fun i j r r' h => h) _ _ _
    (fun v used' => freshRequests_liftHash_bind _ _ _ fun _ => .pure _) ∅ (fun _ _ h => h)

/-! ## Table against fresh bases -/

/-- A table entry's first half is the base. -/
def signTable (_pos : TopRndPos) (tape : HashOutput) : StateT (QueryCache HashSpec) ProbComp Randomness :=
  pure (truncateHash tape)

def signKey (_key : TopIndex) (tape : Randomness) : StateT (QueryCache HashSpec) ProbComp Randomness :=
  pure tape

theorem tableRun_keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (table : TopRndPos → HashOutput) :
    tableRun romImpl signTable table (keygenTable parameter secret topSecret) =
      simulateQ randomOracle (Concrete.honestKeygen parameter secret topSecret
        fun key root => (pure (truncateHash (table (key, root))) : OracleComp HashSpec Randomness)) := by
  rw [state_of_hash]
  refine (state_of_req (Req := TableReq) (fun pos => signTable pos (table pos)) parameter secret topSecret
    fun key root => liftM ((OracleWorld + TableReq).query (.inr (key, root)))).trans ?_
  congr 1

theorem tableRun_keygenKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (table : TopIndex → Randomness) :
    tableRun romImpl signKey table (keygenKey parameter secret topSecret) =
      simulateQ randomOracle (Concrete.honestKeygen parameter secret topSecret
        fun key _ => (pure (table key) : OracleComp HashSpec Randomness)) := by
  rw [state_of_hash]
  refine (state_of_req (Req := KeyReq) (fun key => signKey key (table key)) parameter secret topSecret
    fun key _ => liftM ((OracleWorld + KeyReq).query (.inr key))).trans ?_
  congr 1

theorem keygenState_eq_table (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest)
    (topBase : TopIndex → Digest → StateT (QueryCache HashSpec) ProbComp Randomness) :
    keygenState parameter secret topSecret topBase =
      simulateQ (romImpl + fun (pos : TopRndPos) => topBase pos.1 pos.2)
        (keygenTable parameter secret topSecret) := by
  refine Eq.symm ((state_of_req (Req := TableReq) (fun (pos : TopRndPos) => topBase pos.1 pos.2) parameter
    secret topSecret fun key root => liftM ((OracleWorld + TableReq).query (.inr (key, root)))).trans ?_)
  congr 1
  funext key root
  rw [simulateQ_spec_query]
  rfl

theorem freshRun_keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) :
    freshRun romImpl signTable (keygenTable parameter secret topSecret) =
      keygenState parameter secret topSecret fun key root => (do
        let tape ← liftM ($ᵗ HashOutput : ProbComp HashOutput)
        signTable (key, root) tape) := by
  refine (state_of_req (Req := TableReq) (fun pos => do
    let tape ← liftM ($ᵗ HashOutput : ProbComp HashOutput)
    signTable pos tape) parameter secret topSecret
    fun key root => liftM ((OracleWorld + TableReq).query (.inr (key, root)))).trans ?_
  congr 1

theorem freshRun_keygenKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) :
    freshRun romImpl signKey (keygenKey parameter secret topSecret) =
      keygenState parameter secret topSecret fun key _ => (do
        let tape ← liftM ($ᵗ Randomness : ProbComp Randomness)
        signKey key tape) := by
  refine (state_of_req (Req := KeyReq) (fun key => do
    let tape ← liftM ($ᵗ Randomness : ProbComp Randomness)
    signKey key tape) parameter secret topSecret
    fun key _ => liftM ((OracleWorld + KeyReq).query (.inr key))).trans ?_
  congr 1

theorem evalDist_freshRun_table_key (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    ((freshRun romImpl signTable (keygenTable parameter secret topSecret)).run cache) =ᵈ
      ((freshRun romImpl signKey (keygenKey parameter secret topSecret)).run cache) := by
  rw [freshRun_keygenTable, freshRun_keygenKey, keygenState_eq_table, keygenState_eq_table]
  apply evalDistEq_simulateQ_run
  intro input state
  cases input with
  | inl input => rfl
  | inr pos =>
      change (((do
          let tape ← liftM ($ᵗ HashOutput : ProbComp HashOutput)
          pure (truncateHash tape)) : StateT (QueryCache HashSpec) ProbComp Randomness).run state) =ᵈ
        (((do
          let tape ← liftM ($ᵗ Randomness : ProbComp Randomness)
          pure tape) : StateT (QueryCache HashSpec) ProbComp Randomness).run state)
      simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind, StateT.run_pure]
      calc ((($ᵗ HashOutput : ProbComp HashOutput) >>= fun x => pure (truncateHash x, state) :
              ProbComp (Randomness × QueryCache HashSpec)))
          =ᵈ (((truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)) >>= fun d => pure (d, state) :
              ProbComp (Randomness × QueryCache HashSpec))) := by rw [bind_map_left]
        _ =ᵈ ((($ᵗ Digest : ProbComp Digest) >>= fun d => pure (d, state) :
              ProbComp (Randomness × QueryCache HashSpec))) :=
          Rom.evalDist_truncate_uniformHashOutput.bind_left _
        _ =ᵈ _ := (SampleableType.uniformSample_evalDistEq_of_inst (A := Digest) _ _).bind_left _

/-- Reading a uniform table at each key's own root is a uniform base per key. -/
theorem evalDist_topBase (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) {β : Type}
    (k : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryCache HashSpec → ProbComp β) :
    (sampleTopRnd >>= fun table => (simulateQ randomOracle (Concrete.honestKeygen parameter secret topSecret
        fun key root => (pure (truncateHash (table (key, root))) : OracleComp HashSpec Randomness))).run ∅ >>= k) =ᵈ
      (Concrete.sampleTopBase >>= fun topBase => (simulateQ randomOracle (Concrete.honestKeygen parameter secret
        topSecret fun key _ => (pure (topBase key) : OracleComp HashSpec Randomness))).run ∅ >>= k) := by
  simp_rw [← tableRun_keygenTable, ← tableRun_keygenKey]
  have h1 : (sampleTopRnd >>= fun table =>
      (tableRun romImpl signTable table (keygenTable parameter secret topSecret)).run ∅) =ᵈ
        ((freshRun romImpl signTable (keygenTable parameter secret topSecret)).run ∅) :=
    letI := topRndSampleable
    (freshRequests_keygenTable parameter secret topSecret).evalDist_tableRun romImpl signTable ∅
  have h2 : (Concrete.sampleTopBase >>= fun table =>
      (tableRun romImpl signKey table (keygenKey parameter secret topSecret)).run ∅) =ᵈ
        ((freshRun romImpl signKey (keygenKey parameter secret topSecret)).run ∅) := by
    let : SampleableType (TopIndex → Randomness) := SampleableType.ofFintype (TopIndex → Randomness)
    refine EvalDistEq.trans ?_
      ((freshRequests_keygenKey parameter secret topSecret).evalDist_tableRun romImpl signKey ∅)
    unfold Concrete.sampleTopBase
    exact (SampleableType.uniformSample_evalDistEq_of_inst _ _).bind_left _
  calc _ =ᵈ ((sampleTopRnd >>= fun table =>
          (tableRun romImpl signTable table (keygenTable parameter secret topSecret)).run ∅) >>= k) := by
        rw [bind_assoc]
    _ =ᵈ ((freshRun romImpl signTable (keygenTable parameter secret topSecret)).run ∅ >>= k) := by
        exact h1.bind_left _
    _ =ᵈ ((freshRun romImpl signKey (keygenKey parameter secret topSecret)).run ∅ >>= k) := by
        exact (evalDist_freshRun_table_key _ _ _ _).bind_left _
    _ =ᵈ ((Concrete.sampleTopBase >>= fun table =>
          (tableRun romImpl signKey table (keygenKey parameter secret topSecret)).run ∅) >>= k) := by
        exact h2.symm.bind_left _
    _ = _ := by rw [bind_assoc]

end XmssSecurity.Bridge
