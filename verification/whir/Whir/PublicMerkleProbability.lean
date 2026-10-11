import Whir.PublicMerkleBinding
import Whir.PublicCompressionProgram

/-! Ordinary Merkle losses in the actual shared random compression game.
Every target is determined before the selected fresh compression answer.
Root announcements have their own cap: zero-cost bookkeeping is not charged
to the compression budget. No whole-hash random-oracle assumption is used. -/
namespace Whir.PublicMerkleProbability
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicMerkleLog PublicMerkleBinding PublicCompressionProgram
open MerkleTransport MerkleTransport.Commitments TypedOracleCompiler
open scoped BigOperators

private instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
private noncomputable instance : Fintype UInt64 := Fintype.ofFinite _
private def nodeFields (n : Node) : Digest32 × Block64 × UInt64 × Bool :=
  (n.cv,n.block,n.tweak,n.last)
private theorem nodeFields_injective : Function.Injective nodeFields := by
  intro a b h
  cases a; cases b
  simp_all [nodeFields]
private instance : Finite Node := Finite.of_injective nodeFields nodeFields_injective
private noncomputable instance : Fintype Node := Fintype.ofFinite _
private noncomputable instance oracleFintype : Fintype PrimitiveOracle := inferInstance

/-- The exact finite compression-oracle experiment used in the averages. -/
@[instance_reducible]
noncomputable def compressionOracleFintype : Fintype PrimitiveOracle := oracleFintype

abbrev RootPolicy := PublicLog → Finset Digest32

/-- This hash field is never used to decode pair children. The pair encoder is
exactly MerkleTransport.hashing's actual byte codec. -/
def pairCodec := hashing (fun _ => DuplexCompression.parameterIV)

noncomputable def pairChildren (log : PublicLog) : Finset Digest32 :=
  (recordDomain (records log)).biUnion (MerkleBinding.children pairCodec)

def cvTargets (log : PublicLog) : Finset Digest32 := (log.map fun e => e.1.cv).toFinset
def outputTargets (log : PublicLog) : Finset Digest32 := (log.map Prod.snd).toFinset

noncomputable def targets (roots : RootPolicy) (log : PublicLog) : Finset Digest32 :=
  roots log ∪ pairChildren log ∪ cvTargets log

noncomputable def badTargets (roots : RootPolicy) (log : PublicLog) : Finset Digest32 :=
  outputTargets log ∪ targets roots log

 theorem records_length (log : PublicLog) : (records log).length ≤ log.length :=
  List.length_filterMap_le _ _

 theorem recordDomain_card (rs : Records) : (recordDomain rs).card ≤ rs.length := by
  exact (List.toFinset_card_le _).trans_eq (List.length_map ..)

private theorem children_card {A B D : Type*} (H : MerkleBinding.Hashing A D B) (b : B) :
    (MerkleBinding.children H b).card ≤ 2 := by
  classical
  unfold MerkleBinding.children
  split
  · exact Finset.card_le_two
  · simp

 theorem pairChildren_card (log : PublicLog) : (pairChildren log).card ≤ 2*log.length := by
  classical
  have hc (bytes : List Byte) : (MerkleBinding.children pairCodec bytes).card ≤ 2 :=
    children_card pairCodec bytes
  calc
    _ ≤ ∑ bytes ∈ recordDomain (records log), (MerkleBinding.children pairCodec bytes).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _bytes ∈ recordDomain (records log), 2 := Finset.sum_le_sum fun _ _ => hc _
    _ = 2 * (recordDomain (records log)).card := by simp [Nat.mul_comm]
    _ ≤ 2 * log.length := Nat.mul_le_mul_left _ ((recordDomain_card _).trans (records_length log))

 theorem cvTargets_card (log : PublicLog) : (cvTargets log).card ≤ log.length := by
  exact (List.toFinset_card_le _).trans_eq (List.length_map ..)

 theorem outputTargets_card (log : PublicLog) : (outputTargets log).card ≤ log.length := by
  exact (List.toFinset_card_le _).trans_eq (List.length_map ..)

 theorem targets_card (roots : RootPolicy) (log : PublicLog) (R : Nat)
    (cap : (roots log).card ≤ R) : (targets roots log).card ≤ R+3*log.length := by
  have h1 := Finset.card_union_le (roots log) (pairChildren log)
  have h2 := Finset.card_union_le (roots log ∪ pairChildren log) (cvTargets log)
  have hp := pairChildren_card log
  have hc := cvTargets_card log
  change (roots log ∪ pairChildren log ∪ cvTargets log).card ≤ _
  omega

 theorem badTargets_card (roots : RootPolicy) (log : PublicLog) (R : Nat)
    (cap : (roots log).card ≤ R) :
    (badTargets roots log).card ≤ R+4*log.length := by
  have hu := Finset.card_union_le (outputTargets log) (targets roots log)
  have ho := outputTargets_card log
  have ht := targets_card roots log R cap
  change (outputTargets log ∪ targets roots log).card ≤ _
  omega

/-- Causal monitor: cache hits cannot trigger a fresh-answer event. Histories
are newest first, but contain every call, including repeated/internal calls. -/
noncomputable def alarm {T : Type} (roots : RootPolicy) (C : PrimitiveOracle) {Q : Nat} :
    Computation T Q → PublicLog → Bool
  | .ret _, _ => false
  | .draw n next, log =>
      (decide (PublicMerkleLog.lookup log n = none ∧ C n ∈ badTargets roots log)) ||
        alarm roots C (next (C n)) ((n,C n)::log)

noncomputable def risk {T : Type} (roots : RootPolicy) {Q : Nat} :
    Computation T Q → PublicLog → ℚ
  | .ret _, _ => 0
  | .draw n next, log =>
      match PublicMerkleLog.lookup log n with
      | some d => risk roots (next d) ((n,d)::log)
      | none => average (fun d => if d ∈ badTargets roots log then 1
          else risk roots (next d) ((n,d)::log))

/-- Sum the actual causal target counts: at call i there are at most R roots
and four targets per prior call, not three targets per final-budget call. -/
def bound (Q R : Nat) : ℚ :=
  ((Q : ℚ)*R + 2*Q*(Q-1)) / 2^256

private def remainingBound (R remaining previous : Nat) : ℚ :=
  ((remaining : ℚ)*(R+4*previous) + 2*remaining*(remaining-1)) / 2^256

private theorem remaining_nonneg (R n m : Nat) : 0 ≤ remainingBound R n m := by
  cases n with
  | zero => simp [remainingBound]
  | succ n =>
    unfold remainingBound
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    positivity

private theorem remaining_step (R n m : Nat) :
    remainingBound R (n+1) m =
      (R+4*m : ℚ)/2^256 + remainingBound R n (m+1) := by
  unfold remainingBound
  push_cast
  ring

 theorem uniform_target_probability (set : Finset Digest32) :
    average (fun d => if d ∈ set then (1 : ℚ) else 0) = set.card / (2^256 : ℚ) := by
  classical
  simp [average]; norm_num

 theorem risk_bound {T : Type} (roots : RootPolicy) (Q R : Nat)
    (rootCap : ∀ log, log.length ≤ Q → (roots log).card ≤ R)
    {n : Nat} (p : Computation T n) (log : PublicLog) (budget : log.length+n ≤ Q) :
    risk roots p log ≤ remainingBound R n log.length := by
  classical
  induction p generalizing log with
  | ret value => exact remaining_nonneg _ _ _
  | @draw n input next ih =>
    have hbudget : log.length ≤ Q := by omega
    have hcap := rootCap log hbudget
    have hcard := badTargets_card roots log R hcap
    have hstep := remaining_step R n log.length
    have hnon : (0 : ℚ) ≤ (R+4*log.length : ℚ)/2^256 := by positivity
    cases hit : PublicMerkleLog.lookup log input with
    | some d =>
      simp only [risk,hit]
      have htail := ih d ((input,d)::log) (by simp only [List.length_cons]; omega)
      simp only [List.length_cons] at htail
      rw [hstep]
      linarith
    | none =>
      simp only [risk,hit]
      calc
        _ ≤ average (fun d : Digest32 =>
            (if d ∈ badTargets roots log then (1:ℚ) else 0) +
              remainingBound R n (log.length+1)) := by
          apply average_mono
          intro d
          have hn := remaining_nonneg R n (log.length+1)
          have ht := ih d ((input,d)::log) (by simp only [List.length_cons]; omega)
          simp only [List.length_cons] at ht
          by_cases bad : d ∈ badTargets roots log
          · simp only [bad,↓reduceIte]
            linarith
          · simpa only [bad,↓reduceIte,zero_add] using ht
        _ = (badTargets roots log).card / (2^256 : ℚ) +
            remainingBound R n (log.length+1) := by
          rw [average_add,uniform_target_probability,average_const]
        _ ≤ (R+4*log.length : ℚ)/2^256 + remainingBound R n (log.length+1) := by
          apply add_le_add_left
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
        _ = _ := hstep.symm

 theorem lookup_cons (log : PublicLog) (n : Node) (d : Digest32) :
    PublicMerkleLog.lookup ((n,d)::log) =
      TypedFiatShamirGame.put (PublicMerkleLog.lookup log) n d := by
  funext m
  by_cases he : m = n
  · subst m; simp [PublicMerkleLog.lookup]
  · simp [PublicMerkleLog.lookup,TypedFiatShamirGame.put_other,he]

 theorem lookup_cons_hit (log : PublicLog) (n : Node) (d : Digest32)
    (hit : PublicMerkleLog.lookup log n = some d) :
    PublicMerkleLog.lookup ((n,d)::log) = PublicMerkleLog.lookup log := by
  funext m
  by_cases he : m = n
  · subst m; simp [PublicMerkleLog.lookup,hit]
  · simp [PublicMerkleLog.lookup,he]

/-- Exact adaptive finite-table/lazy-sampling identity. The fresh coordinate
split is the existing RawOracleCoupling proof; no answer independence axiom
or whole-hash table appears here. -/
 theorem table_alarm_eq_risk {T : Type} (roots : RootPolicy) {Q : Nat}
    (p : Computation T Q) (log : PublicLog) :
    average (fun C : PrimitiveOracle =>
      if alarm roots (RawOracleCoupling.overlay (PublicMerkleLog.lookup log) C) p log then 1 else 0) =
      risk roots p log := by
  classical
  induction p generalizing log with
  | ret value => simp [alarm,risk,average_const]
  | draw n next ih =>
    cases hit : PublicMerkleLog.lookup log n with
    | some d =>
      have cache := lookup_cons_hit log n d hit
      simp only [risk,hit]
      rw [← ih d ((n,d)::log),cache]
      apply congrArg average
      funext C
      simp [alarm,RawOracleCoupling.overlay,hit]
    | none =>
      rw [RawOracleCoupling.overlay_average (PublicMerkleLog.lookup log) n hit
        (fun oracle => if alarm roots oracle (.draw n next) log then (1:ℚ) else 0)]
      simp only [risk,hit]
      apply congrArg average
      funext d
      have cache := lookup_cons log n d
      by_cases bad : d ∈ badTargets roots log
      · simp [alarm,RawOracleCoupling.overlay,hit,bad,average_const]
      · rw [← ih d ((n,d)::log),cache]
        simp only [bad,↓reduceIte]
        apply congrArg average
        funext C
        simp [alarm,RawOracleCoupling.overlay,hit,bad]

 theorem random_compression_bound {T : Type} (roots : RootPolicy) (Q R : Nat)
    (rootCap : ∀ log, log.length ≤ Q → (roots log).card ≤ R) (p : Computation T Q) :
    average (fun C : PrimitiveOracle => if alarm roots C p [] then 1 else 0) ≤ bound Q R := by
  have he := table_alarm_eq_risk roots p []
  have hb := risk_bound roots Q R rootCap p [] (by simp)
  calc
    _ = risk roots p [] := he
    _ ≤ remainingBound R Q 0 := hb
    _ = bound Q R := by simp only [remainingBound,bound,Nat.cast_zero]; ring

/-- Actual mode specialization includes every internal construction node.
The independent R resource cap is not inferred from the mode C-call budget. -/
 theorem real_mode_bound {T : Type} (roots : RootPolicy) (Q R : Nat)
    (rootCap : ∀ log, log.length ≤ Q → (roots log).card ≤ R)
    (iv : Digest32) (p : Program T) (counts : Counts Q p) :
    average (fun C : PrimitiveOracle =>
      if alarm roots C (compile iv p Q counts) [] then 1 else 0) ≤ bound Q R :=
  random_compression_bound roots Q R rootCap (compile iv p Q counts)

noncomputable def traceAlarm (roots : RootPolicy) : PublicLog → PublicLog → Bool
  | _, [] => false
  | history, (n,d)::rest =>
      decide (PublicMerkleLog.lookup history n = none ∧ d ∈ badTargets roots history) ||
        traceAlarm roots ((n,d)::history) rest

 theorem alarm_trace {T : Type} (roots : RootPolicy) (C : PrimitiveOracle)
    {Q : Nat} (p : Computation T Q) (history : PublicLog) :
    alarm roots C p history = traceAlarm roots history (toLog (Sampling.execute C p).2) := by
  induction p generalizing history with
  | ret => rfl
  | draw n next ih => simp only [alarm,Sampling.execute,toLog,List.map_cons,traceAlarm,ih]

 theorem traceAlarm_append (roots : RootPolicy) (history before after : PublicLog) :
    traceAlarm roots history (before++after) =
      (traceAlarm roots history before || traceAlarm roots (before.reverse++history) after) := by
  induction before generalizing history with
  | nil => simp only [List.nil_append,List.reverse_nil,traceAlarm,Bool.false_or]
  | cons e rest ih =>
    rcases e with ⟨n,d⟩
    simp only [List.cons_append,traceAlarm,ih,List.reverse_cons,List.append_assoc,
      List.nil_append,Bool.or_assoc]

 theorem authentic_cons (C : PrimitiveOracle) (log : PublicLog) (auth : AuthenticLog C log)
    (n : Node) : AuthenticLog C ((n,C n)::log) := by
  intro m d hm
  rcases List.mem_cons.mp hm with he | hm
  · cases he; rfl
  · exact auth m d hm

 theorem collision_mono {small large : PublicLog}
    (sub : ∀ e ∈ small, e ∈ large) (h : OutputCollision small) : OutputCollision large := by
  obtain ⟨a,b,d,ha,hb,hne⟩ := h
  exact ⟨a,b,d,sub _ ha,sub _ hb,hne⟩

 theorem noCollision_cons (C : PrimitiveOracle) (roots : RootPolicy) (log : PublicLog)
    (auth : AuthenticLog C log) (clean : ¬ OutputCollision log) (n : Node)
    (safe : ¬ (PublicMerkleLog.lookup log n = none ∧ C n ∈ badTargets roots log)) :
    ¬ OutputCollision ((n,C n)::log) := by
  have oldOutput : ∀ m, (m,C n) ∈ log → m = n := by
    intro m hm
    cases hit : PublicMerkleLog.lookup log n with
    | none =>
      apply False.elim
      apply safe
      exact ⟨hit,Finset.mem_union_left _ (List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨(m,C n),hm,rfl⟩))⟩
    | some d =>
      have hn := PublicMerkleLog.lookup_mem hit
      have hd := auth n d hn
      rw [← hd] at hn
      by_contra ne
      exact clean ⟨m,n,C n,hm,hn,ne⟩
  rintro ⟨a,b,d,ha,hb,hne⟩
  rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
  · cases ha; cases hb; exact hne rfl
  · cases ha; exact hne (oldOutput b hb).symm
  · cases hb; exact hne (oldOutput a ha)
  · exact clean ⟨a,b,d,ha,hb,hne⟩

 theorem targets_mono (C : PrimitiveOracle) (roots : RootPolicy) (old new : PublicLog)
    (oldAuth : AuthenticLog C old) (newAuth : AuthenticLog C new)
    (sub : ∀ e ∈ old, e ∈ new) (clean : ¬ OutputCollision new)
    (rootSub : roots old ⊆ roots new) : targets roots old ⊆ targets roots new := by
  intro d hd
  rcases Finset.mem_union.mp hd with hp | hc
  · rcases Finset.mem_union.mp hp with hr | hp
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (rootSub hr))
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      obtain ⟨bytes,hb,hd⟩ := Finset.mem_biUnion.mp hp
      apply Finset.mem_biUnion.mpr
      refine ⟨bytes,?_,hd⟩
      obtain ⟨⟨x,a⟩,hm,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
      dsimp only at he; subst x
      exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨(bytes,a),records_persist C old new oldAuth newAuth sub clean _ hm,rfl⟩)
  · apply Finset.mem_union_right
    obtain ⟨⟨n,a⟩,hm,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(n,a),sub _ hm,he⟩)

 theorem traceAlarm_clean (C : PrimitiveOracle) (roots : RootPolicy)
    (history trace : PublicLog) (oldAuth : AuthenticLog C history)
    (auth : AuthenticLog C trace) (oldClean : ¬ OutputCollision history)
    (quiet : traceAlarm roots history trace = false) :
    ¬ OutputCollision (trace.reverse++history) := by
  induction trace generalizing history with
  | nil => exact oldClean
  | cons e rest ih =>
    rcases e with ⟨n,d⟩
    have hd := auth n d List.mem_cons_self
    subst d
    simp only [traceAlarm,Bool.or_eq_false_iff,decide_eq_false_iff_not] at quiet
    have clean := noCollision_cons C roots history oldAuth oldClean n quiet.1
    have ht := ih ((n,C n)::history) (authentic_cons C history oldAuth n)
      (fun m d hm => auth m d (List.mem_cons_of_mem _ hm)) clean quiet.2
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ht

/-- Roots persist across public-call boundaries. The cap R is independent:
announcing a root itself consumes no compression query. -/
def RootsGrow (roots : RootPolicy) : Prop :=
  ∀ history entry, roots history ⊆ roots (entry::history)

 theorem traceAlarm_avoids (C : PrimitiveOracle) (roots : RootPolicy) (grow : RootsGrow roots)
    (history trace : PublicLog) (oldAuth : AuthenticLog C history)
    (auth : AuthenticLog C trace) (oldClean : ¬ OutputCollision history)
    (quiet : traceAlarm roots history trace = false)
    (n : Node) (absent : ∀ d, (n,d) ∉ history)
    (present : (n,C n) ∈ trace.reverse++history) (target : C n ∈ targets roots history) : False := by
  induction trace generalizing history with
  | nil => exact absent _ present
  | cons e rest ih =>
    rcases e with ⟨m,d⟩
    have hd := auth m d List.mem_cons_self
    subst d
    simp only [traceAlarm,Bool.or_eq_false_iff,decide_eq_false_iff_not] at quiet
    by_cases eq : n = m
    · subst m
      have miss : PublicMerkleLog.lookup history n = none := by
        cases hit : PublicMerkleLog.lookup history n with
        | none => rfl
        | some a => exact False.elim (absent a (PublicMerkleLog.lookup_mem hit))
      exact quiet.1 ⟨miss,Finset.mem_union_right _ target⟩
    · have newAuth := authentic_cons C history oldAuth m
      have clean := noCollision_cons C roots history oldAuth oldClean m quiet.1
      apply ih ((m,C m)::history) newAuth (fun a d ha => auth a d (List.mem_cons_of_mem _ ha))
        clean quiet.2
      · intro a ha
        rcases List.mem_cons.mp ha with he | ha
        · exact eq (congrArg Prod.fst he)
        · exact absent a ha
      · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using present
      · exact targets_mono C roots history ((m,C m)::history) oldAuth newAuth
          (fun e he => List.mem_cons_of_mem _ he) clean (grow _ _) target

private theorem children_pair_mem {A B D : Type*} (H : MerkleBinding.Hashing A D B)
    (l r d : D) (hd : d = l ∨ d = r) : d ∈ MerkleBinding.children H (H.pair (l,r)) := by
  classical
  have hex : ∃ pair, H.pair pair = H.pair (l,r) := ⟨(l,r),rfl⟩
  have he := H.pair_injective hex.choose_spec
  simpa [MerkleBinding.children,dite_eq_left hex,he] using hd

 theorem snapshot_target_mem (C : PrimitiveOracle) (roots : RootPolicy) (old history : PublicLog)
    (oldAuth : AuthenticLog C old) (auth : AuthenticLog C history)
    (sub : ∀ e ∈ old, e ∈ history) (clean : ¬ OutputCollision history)
    (root selected d : Digest32) (registered : root ∈ roots history)
    (merkle : MerkleBinding.Target (hashing (hash C)) (recordDomain (records old)) root selected)
    (snapshot : SnapshotTarget old selected d) : d ∈ targets roots history := by
  rcases snapshot with rfl | ⟨n,a,hn,rfl⟩
  · rcases merkle with rfl | ⟨l,r,hpair,hd⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ registered)
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨List.ofFn (ByteCodec.pairBytes (l,r)),?_,children_pair_mem pairCodec l r _ hd⟩
      obtain ⟨a,ha⟩ := recordLookup_exists (records old) _ hpair
      have hp := records_persist C old history oldAuth auth sub clean _
        (recordLookup_mem _ _ _ ha)
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(_,a),hp,rfl⟩)
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(n,a),sub _ hn,rfl⟩))

/-- Concrete terminal event, not a free bad-event cover. A freeze is an actual
prefix of the complete compression trace. Hidden earlier calls may exist,
but any ordinary tag0 call at the freeze is in its public log. Verification
has actually evaluated every ordinary plan in the accepted opening inputs. -/
def FrozenOpeningBad (C : PrimitiveOracle) (roots : RootPolicy) (trace : PublicLog) : Prop :=
  ∃ before after oldLog root output,
    trace = before++after ∧
    (∀ e ∈ oldLog, e ∈ before) ∧
    (∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ oldLog) ∧
    root ∈ roots before.reverse ∧
    (∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^56) ∧
    (∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)),
      ∀ e ∈ PublicMerkleLog.plan C bytes, e ∈ trace) ∧
    OpenPrimitiveBad C oldLog root output

 theorem opening_alarm (C : PrimitiveOracle) (roots : RootPolicy) (grow : RootsGrow roots)
    (trace : PublicLog) (auth : AuthenticLog C trace)
    (bad : FrozenOpeningBad C roots trace) : traceAlarm roots [] trace = true := by
  classical
  by_contra hn
  have quiet : traceAlarm roots [] trace = false := Bool.eq_false_iff.mpr hn
  obtain ⟨before,after,oldLog,root,output,rfl,sub,ordinary,registered,bounds,plans,bad⟩ := bad
  rw [traceAlarm_append] at quiet
  simp only [List.append_nil,Bool.or_eq_false_iff] at quiet
  have beforeAuth : AuthenticLog C before := fun n d hm => auth n d (List.mem_append_left _ hm)
  have afterAuth : AuthenticLog C after := fun n d hm => auth n d (List.mem_append_right _ hm)
  have oldAuth : AuthenticLog C oldLog := fun n d hm => beforeAuth n d (sub _ hm)
  have historyAuth : AuthenticLog C before.reverse := fun n d hm =>
    beforeAuth n d (List.mem_reverse.mp hm)
  have emptyAuth : AuthenticLog C [] := by intro n d hm; cases hm
  have emptyClean : ¬ OutputCollision [] := by rintro ⟨a,b,d,ha,_⟩; cases ha
  have clean : ¬ OutputCollision before.reverse := by
    simpa only [List.append_nil] using traceAlarm_clean C roots [] before emptyAuth beforeAuth emptyClean quiet.1
  have oldSub : ∀ e ∈ oldLog, e ∈ before.reverse := fun e he => List.mem_reverse.mpr (sub e he)
  rcases bad with collision | ⟨p,hp,bytes,hbytes,merkle,n,hplan,absent,target⟩
  · exact clean (collision_mono oldSub collision)
  · have tag0 := PublicMerkleLog.plan_tag_zero C bytes (bounds p hp bytes hbytes) n (C n) hplan
    have absentBefore : ∀ d, (n,d) ∉ before.reverse := by
      intro d hd
      exact absent d (ordinary n d (List.mem_reverse.mp hd) tag0)
    have hmem := plans p hp bytes hbytes _ hplan
    have present : (n,C n) ∈ after.reverse++before.reverse := by
      rcases List.mem_append.mp hmem with hb | ha
      · exact List.mem_append_right _ (List.mem_reverse.mpr hb)
      · exact List.mem_append_left _ (List.mem_reverse.mpr ha)
    have targetMem := snapshot_target_mem C roots oldLog before.reverse oldAuth historyAuth
      oldSub clean root (hash C bytes) (C n) registered merkle target
    exact traceAlarm_avoids C roots grow before.reverse after historyAuth afterAuth clean quiet.2
      n absentBefore present targetMem

noncomputable def openingProbability {T : Type} (roots : RootPolicy) {Q : Nat}
    (p : Computation T Q) : ℚ := by
  classical
  exact average (fun C : PrimitiveOracle =>
    if FrozenOpeningBad C roots (toLog (Sampling.execute C p).2) then 1 else 0)

/-- Genuine adaptive random-compression bound for the public Merkle opening
event, with all collision/fresh-target cases discharged by the causal trace
monitor. Exact constants: QR + 2Q(Q-1), over 2^256. -/
 theorem opening_probability_bound {T : Type} (roots : RootPolicy) (Q R : Nat)
    (rootCap : ∀ log, log.length ≤ Q → (roots log).card ≤ R)
    (grow : RootsGrow roots) (p : Computation T Q) : openingProbability roots p ≤ bound Q R := by
  classical
  apply le_trans _ (random_compression_bound roots Q R rootCap p)
  apply average_mono
  intro C
  by_cases bad : FrozenOpeningBad C roots (toLog (Sampling.execute C p).2)
  · have ha := opening_alarm C roots grow _ (execute_authentic C p) bad
    rw [← alarm_trace] at ha
    simp only [bad,ha,↓reduceIte,le_refl]
  · simp only [bad,↓reduceIte]
    split <;> norm_num

 theorem real_mode_opening_bound {T : Type} (roots : RootPolicy) (Q R : Nat)
    (rootCap : ∀ log, log.length ≤ Q → (roots log).card ≤ R) (grow : RootsGrow roots)
    (iv : Digest32) (p : Program T) (counts : Counts Q p) :
    openingProbability roots (compile iv p Q counts) ≤ bound Q R :=
  opening_probability_bound roots Q R rootCap grow (compile iv p Q counts)

/-- The monitor is itself a bounded causal sampling program: it observes
only the selected compression answers. The outer existing memo interpreter
suppresses repeated-input draws, just as in the finite-table experiment. -/
noncomputable def audit {T : Type} (roots : RootPolicy) {Q : Nat} :
    Computation T Q → PublicLog → Computation Bool Q
  | .ret _, _ => .ret false
  | .draw n next, history =>
      .draw n (fun d => mapResult
        (fun later => decide (PublicMerkleLog.lookup history n = none ∧ d ∈ badTargets roots history) || later)
        (audit roots (next d) ((n,d)::history)))

 theorem audit_eval {T : Type} (roots : RootPolicy) (C : PrimitiveOracle)
    {Q : Nat} (p : Computation T Q) (history : PublicLog) :
    Sampling.eval C (audit roots p history) = alarm roots C p history := by
  induction p generalizing history with
  | ret => rfl
  | draw n next ih => simp only [audit,Sampling.eval,eval_mapResult,ih,alarm]

 theorem random_compression_lazy_bound {T : Type} (roots : RootPolicy) (Q R : Nat)
    (rootCap : ∀ log, log.length ≤ Q → (roots log).card ≤ R) (p : Computation T Q) :
    Sampling.expectation (fun result => if result.1 then 1 else 0)
      (RawOracleCoupling.memo (audit roots p []) (fun _ => none)) ≤ bound Q R := by
  rw [← RawOracleCoupling.empty_table_eq_memo (audit roots p []) (fun b => if b then (1:ℚ) else 0)]
  simpa only [audit_eval] using random_compression_bound roots Q R rootCap p

theorem four_calls_two_roots :
    bound 4 2 = (32 : ℚ) / 2^256 := by norm_num [bound]

end Whir.PublicMerkleProbability
