import Whir.PublicMerkleLog

/-! Pointwise Merkle binding through the shared ordinary compression oracle.
The frozen table is the saturated domain reconstructed from the frozen public
log. No independent random whole-hash output or probability bound is assumed. -/
namespace Whir.PublicMerkleBinding
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicMerkleLog MerkleTransport MerkleTransport.Commitments

 theorem records_origin {log : PublicLog} {bytes : List Byte} {d : Digest32}
    (hm : (bytes,d) ∈ records log) :
    ∃ n, (n,d) ∈ log ∧ parse log n d = some bytes := by
  obtain ⟨⟨n,e⟩,hn,hp⟩ := List.mem_filterMap.mp hm
  cases he : parse log n e with
  | none => simp [he] at hp
  | some bs =>
    simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hp
    rcases hp with ⟨rfl,rfl⟩
    exact ⟨n,hn,he⟩

 theorem run_plan_present (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (bs : List (List Byte)) (cv : Digest32) (count : Nat)
    (d : Digest32) (done : run (PublicMerkleLog.lookup log) cv count bs = some d) :
    ∀ e ∈ planFrom C cv count bs, e ∈ log := by
  induction bs generalizing cv count with
  | nil => simp [run] at done
  | cons b rest ih =>
    cases rest with
    | nil =>
      intro e he
      have he' : e = (node cv count b true,C (node cv count b true)) :=
        List.mem_singleton.mp he
      have hm := PublicMerkleLog.lookup_mem done
      rw [he',auth _ _ hm]
      exact hm
    | cons next rest =>
      simp only [run,Option.bind_eq_bind] at done
      cases hq : PublicMerkleLog.lookup log (node cv count b false) with
      | none => simp [hq] at done
      | some value =>
        simp only [hq,Option.bind_some] at done
        have hm := PublicMerkleLog.lookup_mem hq
        have hv := auth _ _ hm
        intro e he
        simp only [planFrom,hv,List.mem_cons] at he
        rcases he with he | he
        · simpa only [he] using hm
        · exact ih value (count+b.length) done e he

 theorem parse_plan_present (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (n : Node) (d : Digest32) (bytes : List Byte)
    (parsed : parse log n d = some bytes) : ∀ e ∈ plan C bytes, e ∈ log := by
  unfold parse at parsed
  split at parsed
  · simp at parsed
  · cases hr : recover log (log.length+1)
        (n.tweak.toNat-finalLength n.tweak.toNat) n.cv with
    | none => simp [hr] at parsed
    | some pre =>
      simp only [hr,Option.bind_eq_bind,Option.bind_some] at parsed
      split at parsed
      next replay =>
        cases Option.some.inj parsed
        exact run_plan_present C log auth _ _ _ _ replay
      next => simp at parsed

 theorem record_length_bound {log : PublicLog} {bytes : List Byte} {d : Digest32}
    (hm : (bytes,d) ∈ records log) : bytes.length < 2^64 := by
  obtain ⟨n,_,hp⟩ := records_origin hm
  rw [parse_byte_count hp]
  exact n.tweak.toNat_lt

 theorem records_persist_or_collision (C : PrimitiveOracle) (oldLog newLog : PublicLog)
    (oldAuth : AuthenticLog C oldLog) (newAuth : AuthenticLog C newLog)
    (extension : ∀ e ∈ oldLog, e ∈ newLog) (bytes : List Byte) (d : Digest32)
    (hm : (bytes,d) ∈ records oldLog) :
    (bytes,d) ∈ records newLog ∨ OutputCollision newLog := by
  obtain ⟨n,_,hp⟩ := records_origin hm
  have present := parse_plan_present C oldLog oldAuth n d bytes hp
  have hd := records_authentic C oldLog oldAuth bytes d hm
  simpa only [hd] using plan_complete_or_public_collision C newLog newAuth bytes
    (record_length_bound hm) (fun e he => extension e (present e he))

 theorem records_persist (C : PrimitiveOracle) (oldLog newLog : PublicLog)
    (oldAuth : AuthenticLog C oldLog) (newAuth : AuthenticLog C newLog)
    (extension : ∀ e ∈ oldLog, e ∈ newLog) (noCollision : ¬ OutputCollision newLog) :
    ∀ e ∈ records oldLog, e ∈ records newLog := by
  rintro ⟨bytes,d⟩ hm
  exact (records_persist_or_collision C oldLog newLog oldAuth newAuth extension bytes d hm).resolve_right noCollision

/-- First-answer retention may change order and remove duplicates, but its
frozen domain must be saturated. Merely a subset is insufficient for FreshHit. -/
 theorem retained_domain_eq (retained current : Records)
    (covered : ∀ e ∈ retained, e ∈ current)
    (saturated : ∀ bytes d, (bytes,d) ∈ current → ∃ first, (bytes,first) ∈ retained) :
    recordDomain retained = recordDomain current := by
  apply Finset.Subset.antisymm
  · intro bytes hb
    obtain ⟨⟨x,d⟩,hm,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    dsimp only at he; subst x
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(bytes,d),covered _ hm,rfl⟩)
  · intro bytes hb
    obtain ⟨⟨x,d⟩,hm,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    dsimp only at he; subst x
    obtain ⟨first,hfirst⟩ := saturated bytes d hm
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(bytes,first),hfirst,rfl⟩)

 theorem reconstructed_collision (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log)
    (collision : MerkleBinding.Collision (hashing (hash C)) (recordDomain (records log))) :
    OutputCollision log := by
  obtain ⟨x,hx,y,hy,hne,he⟩ := collision
  obtain ⟨dx,hdx⟩ := recordLookup_exists (records log) x hx
  obtain ⟨dy,hdy⟩ := recordLookup_exists (records log) y hy
  have hxmem := recordLookup_mem _ _ _ hdx
  have hymem := recordLookup_mem _ _ _ hdy
  have hax := records_authentic C log auth x dx hxmem
  have hay := records_authentic C log auth y dy hymem
  have hd : dx = dy := hax.symm.trans (he.trans hay)
  rw [← hd] at hymem
  obtain ⟨nx,hnx,hpx⟩ := records_origin hxmem
  obtain ⟨ny,hny,hpy⟩ := records_origin hymem
  refine ⟨nx,ny,dx,hnx,hny,?_⟩
  intro hn
  subst ny
  exact hne (Option.some.inj (hpx.symm.trans hpy))

/-- The selected Merkle target is exactly the frozen root or a child of a
recorded pair input. The compression cut additionally permits an old CV. -/
def PrimitiveFreshHit (C : PrimitiveOracle) (oldLog : PublicLog) (root : Digest32)
    (queries : Finset (List Byte)) : Prop :=
  ∃ bytes ∈ queries,
    MerkleBinding.Target (hashing (hash C)) (recordDomain (records oldLog)) root (hash C bytes) ∧
    FreshTarget C oldLog (hash C bytes) (plan C bytes)

 theorem freshHit_primitive (C : PrimitiveOracle) (oldLog : PublicLog)
    (auth : AuthenticLog C oldLog) (root : Digest32) (queries : Finset (List Byte))
    (bounds : ∀ bytes ∈ queries, bytes.length < 2^64)
    (hit : MerkleBinding.FreshHit (hashing (hash C))
      (recordDomain (records oldLog)) root queries) :
    OutputCollision oldLog ∨ PrimitiveFreshHit C oldLog root queries := by
  obtain ⟨bytes,hq,absent,target⟩ := hit
  have notRecorded : (bytes,hash C bytes) ∉ records oldLog := by
    intro hm
    exact absent (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(bytes,hash C bytes),hm,rfl⟩))
  rcases frozen_target_alternative C oldLog auth bytes (hash C bytes) (bounds bytes hq) rfl with
    recorded | collision | fresh
  · exact False.elim (notRecorded recorded)
  · exact Or.inl collision
  · exact Or.inr ⟨bytes,hq,target,fresh⟩

def OpenPrimitiveBad (C : PrimitiveOracle) (oldLog : PublicLog) (root : Digest32)
    (output : List RawPath) : Prop :=
  OutputCollision oldLog ∨
    ∃ p ∈ output, PrimitiveFreshHit C oldLog root (p.opening.inputs (hashing (hash C)))

 theorem openBad_primitive (C : PrimitiveOracle) (oldLog : PublicLog)
    (auth : AuthenticLog C oldLog) (snapshot : Snapshot)
    (saturated : snapshot.table = recordDomain (records oldLog)) (root : Digest32)
    (output : List RawPath)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64)
    (bad : OpenBad (hash C) snapshot root output) :
    OpenPrimitiveBad C oldLog root output := by
  rcases bad with collision | ⟨p,hp,fresh⟩
  · exact Or.inl (reconstructed_collision C oldLog auth (by simpa only [saturated] using collision))
  · rcases freshHit_primitive C oldLog auth root _ (bounds p hp)
        (by simpa only [saturated] using fresh) with collision | hit
    · exact Or.inl collision
    · exact Or.inr ⟨p,hp,hit⟩

/-- Actual accepted pruned openings agree pointwise with the first frozen
oracle, or expose only ordinary shared-compression witnesses. No PCS cover
or probabilistic reduction is hidden in this transport theorem. -/
 theorem open_frozen_public (C : PrimitiveOracle) (oldLog : PublicLog)
    (auth : AuthenticLog C oldLog) (registry announcements : Registry)
    (root : Digest32) (snapshot : Snapshot)
    (saturated : snapshot.table = recordDomain (records oldLog))
    (committed : Commitments.lookup root registry = some snapshot)
    (proof : PrunedMerklePaths) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64)
    (accepted : proof.open (hash C) root numLeaves queries rowWords leafWords = some output) :
    Commitments.lookup root (registerMany registry announcements) = some snapshot ∧
      ((∀ p ∈ output, p.leafData = row (hash C) snapshot root numLeaves.log2 p.leafIndex) ∨
        OpenPrimitiveBad C oldLog root output) := by
  obtain ⟨stable,good | bad⟩ := open_frozen (hash C) registry announcements root snapshot committed
    proof numLeaves queries rowWords leafWords output accepted
  · exact ⟨stable,Or.inl good⟩
  · exact ⟨stable,Or.inr (openBad_primitive C oldLog auth snapshot saturated root output bounds bad)⟩

/-- Cumulative first records remain covered even when they were discovered
at different earlier public snapshots. Authenticity of those snapshots is
inherited from the actual current log, not supplied as a hash event. -/
 theorem historical_records_covered (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (noCollision : ¬ OutputCollision log)
    (retained : Records)
    (history : ∀ e ∈ retained, ∃ earlier : PublicLog,
      (∀ q ∈ earlier, q ∈ log) ∧ e ∈ records earlier) :
    ∀ e ∈ retained, e ∈ records log := by
  intro e he
  obtain ⟨earlier,extension,hm⟩ := history e he
  have earlierAuth : AuthenticLog C earlier := fun n d hn => auth n d (extension _ hn)
  exact records_persist C earlier log earlierAuth auth extension noCollision e hm

 theorem historical_domain_eq (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (noCollision : ¬ OutputCollision log)
    (retained : Records)
    (history : ∀ e ∈ retained, ∃ earlier : PublicLog,
      (∀ q ∈ earlier, q ∈ log) ∧ e ∈ records earlier)
    (saturated : ∀ bytes d, (bytes,d) ∈ records log → ∃ first, (bytes,first) ∈ retained) :
    recordDomain retained = recordDomain (records log) :=
  retained_domain_eq retained (records log)
    (historical_records_covered C log auth noCollision retained history) saturated

/-- Cumulative storage version. The interpreter supplies only provenance of
retained entries and saturation after its public observation; any failure of
collision-free persistence is returned as an observed primitive collision. -/
 theorem open_frozen_retained (C : PrimitiveOracle) (oldLog : PublicLog)
    (auth : AuthenticLog C oldLog) (retained : Records)
    (history : ∀ e ∈ retained, ∃ earlier : PublicLog,
      (∀ q ∈ earlier, q ∈ oldLog) ∧ e ∈ records earlier)
    (saturated : ∀ bytes d, (bytes,d) ∈ records oldLog → ∃ first, (bytes,first) ∈ retained)
    (registry announcements : Registry) (root : Digest32) (snapshot : Snapshot)
    (table : snapshot.table = recordDomain retained)
    (committed : Commitments.lookup root registry = some snapshot)
    (proof : PrunedMerklePaths) (numLeaves : Nat) (queries : List Nat)
    (rowWords leafWords : Nat) (output : List RawPath)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64)
    (accepted : proof.open (hash C) root numLeaves queries rowWords leafWords = some output) :
    Commitments.lookup root (registerMany registry announcements) = some snapshot ∧
      ((∀ p ∈ output, p.leafData = row (hash C) snapshot root numLeaves.log2 p.leafIndex) ∨
        OpenPrimitiveBad C oldLog root output) := by
  classical
  by_cases collision : OutputCollision oldLog
  · exact ⟨registerMany_preserves registry announcements root snapshot committed,
      Or.inr (Or.inl collision)⟩
  · have domains := historical_domain_eq C oldLog auth collision retained history saturated
    exact open_frozen_public C oldLog auth registry announcements root snapshot
      (table.trans domains) committed proof numLeaves queries rowWords leafWords output bounds accepted

/-- Reusable executable scenario: a real accepted pruned opening whose leaf
hash completes only after the frozen final compression record was public. -/
def smoke : IO Unit := do
  let leftWords : List Concrete.K := (List.range 9).map UInt64.ofNat
  let rightWords : List Concrete.K := (List.range 9).map fun n => UInt64.ofNat (n+9)
  let leftBytes := ByteCodec.wordsBytes leftWords
  let rightBytes := ByteCodec.wordsBytes rightWords
  let left := hashBlake2s leftBytes
  let right := hashBlake2s rightBytes
  let pairBytes := List.ofFn (ByteCodec.pairBytes (left,right))
  let root := hashBlake2s pairBytes
  let proof : PrunedMerklePaths := ⟨[leftWords],[right]⟩
  match proof.open hashBlake2s root 2 [0,0] 9 9 with
  | none => throw (IO.userError "actual two-leaf pruned opening was rejected")
  | some output =>
    unless output.map RawPath.leafData == [leftWords,leftWords] do
      throw (IO.userError "pruned opening did not preserve duplicate query rows")
  match plan blake2sOracle leftBytes with
  | [(first,a),(last,b)] =>
    let oldLog := (last,b) :: (plan blake2sOracle rightBytes ++ plan blake2sOracle pairBytes)
    let oldRecords := records oldLog
    unless recordLookup leftBytes oldRecords == none do
      throw (IO.userError "frozen table incorrectly contains incomplete leaf hash")
    unless recordLookup pairBytes oldRecords == some root do
      throw (IO.userError "frozen table lost the recorded pair target")
    unless PublicMerkleLog.lookup oldLog first == none && a == last.cv do
      throw (IO.userError "fresh leaf precursor does not hit old public CV")
    let (_,newRecords) := observe oldLog first a
    unless recordLookup leftBytes newRecords == some left do
      throw (IO.userError "late predecessor did not reconstruct accepted leaf")
    for (bytes,d) in oldRecords do
      unless recordLookup bytes newRecords == some d do
        throw (IO.userError "old reconstructed hash record failed to persist")
  | _ => throw (IO.userError "72-byte Merkle leaf did not use two compression nodes")
  IO.println "Accepted pruned opening: duplicate rows, frozen pair-child target, late leaf precursor, and record persistence OK"

end Whir.PublicMerkleBinding
