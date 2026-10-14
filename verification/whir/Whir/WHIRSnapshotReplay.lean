import Whir.StackWHIRROM
import Whir.WHIRROM

/-! Replay depends only on the original statement at its seed and on the
commitment references actually encoded at nonfinal last-fold positions.
Footprints inspect public pending messages, never future oracle answers. -/
namespace Whir.WHIRSnapshotReplay
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open FiatShamirGame (Digest32)
open WHIRHistory (Pending)

abbrev RootRef := Digest32 × Nat

/-- The exact possible lookup of the scalar parser. Invalid digest encodings,
other phases, and extra or missing scalars contribute no reference. -/
def replyFootprint {c : Config} (q : Coordinate c) (xs : List E) : List RootRef :=
  match q with
  | .fold i j => match xs with
    | _ :: _ :: rest =>
      if j.val + 1 = c.folds[i.val]! then
        if i.val + 1 < c.folds.size then
          match rest with
          | [r,s] => (ByteCodec.scalarsToHash (r,s)).toList.map (fun digest => (digest,i.val + 1))
          | _ => []
        else []
      else []
    | _ => []
  | _ => []

/-- Syntactic references in chronological order. Rejected histories may retain
references in unreachable older or newer messages; no unrelated root is added.
The initial commitment is obtained from the seed catalog, not this registry. -/
def historyFootprint (p : Profile) (s : Digest32) : List Pending → List RootRef
  | [] => []
  | [_] => []
  | m :: previous :: older =>
    historyFootprint p s (previous :: older) ++
      replyFootprint (WHIRReplay.query p (s,previous :: older)) m.scalars

/-- Local immutability, allowing every unmentioned digest and level to change. -/
def AgreeOn (refs : List RootRef) (old new : WHIRReplay.Roots) : Prop :=
  ∀ ref ∈ refs, old ref.1 ref.2 = new ref.1 ref.2

theorem AgreeOn.mono {refs more : List RootRef} {old new : WHIRReplay.Roots}
    (agree : AgreeOn more old new) (included : ∀ ref ∈ refs, ref ∈ more) :
    AgreeOn refs old new := fun ref member => agree ref (included ref member)

theorem decodeReplyScalars_congr {c : Config} (q : Coordinate c)
    (old new : WHIRReplay.Roots) (rows : Oracle) (xs : List E)
    (agree : AgreeOn (replyFootprint q xs) old new) :
    WHIRHistory.decodeReplyScalars q (fun digest => old digest (WHIRHistory.coordinateLevel q + 1)) rows xs =
      WHIRHistory.decodeReplyScalars q (fun digest => new digest (WHIRHistory.coordinateLevel q + 1)) rows xs := by
  cases q with
  | initial => rfl
  | ood i j => rfl
  | query i => rfl
  | tail j => rfl
  | fold i j =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b rest =>
        by_cases lastFold : j.val + 1 = c.folds[i.val]!
        · by_cases nonfinal : i.val + 1 < c.folds.size
          · cases rest with
            | nil => simp [WHIRHistory.decodeReplyScalars,lastFold,nonfinal]
            | cons r rest =>
              cases rest with
              | nil => simp [WHIRHistory.decodeReplyScalars,lastFold,nonfinal]
              | cons s rest =>
                cases rest with
                | cons extra rest => simp [WHIRHistory.decodeReplyScalars,lastFold,nonfinal]
                | nil =>
                  cases decoded : ByteCodec.scalarsToHash (r,s) with
                  | none => simp [WHIRHistory.decodeReplyScalars,lastFold,nonfinal,decoded]
                  | some digest =>
                    have same := agree (digest,i.val + 1) (by
                      simp [replyFootprint,lastFold,nonfinal,decoded])
                    simp only [WHIRHistory.decodeReplyScalars,lastFold,nonfinal,↓reduceIte,
                      decoded,Option.map_some,WHIRHistory.coordinateLevel]
                    rw [same]
          · simp [WHIRHistory.decodeReplyScalars,lastFold,nonfinal]
        · simp only [WHIRHistory.decodeReplyScalars,lastFold,↓reduceIte]

theorem reply_congr {p : Profile} (old new : WHIRReplay.Roots) (r : WHIRReplay.Replay p)
    (q : Coordinate (config p)) (x : Sample q) (m : Pending)
    (agree : AgreeOn (replyFootprint q m.scalars) old new) :
    WHIRReplay.reply old r q x m = WHIRReplay.reply new r q x m :=
  decodeReplyScalars_congr q old new _ m.scalars agree

theorem step_congr {p : Profile} (old new : WHIRReplay.Roots) (r : WHIRReplay.Replay p)
    (q : Coordinate (config p)) (x : Sample q) (m : Pending)
    (agree : AgreeOn (replyFootprint q m.scalars) old new) :
    WHIRReplay.step old r q x m = WHIRReplay.step new r q x m := by
  simp only [WHIRReplay.step,reply_congr old new r q x m agree]

theorem decodeHistory_congr (p : Profile) (oldCatalog newCatalog : WHIRReplay.Catalog p)
    (old new : WHIRReplay.Roots) (s : Digest32) (messages : List Pending)
    (ancestors : List (Pending × Sigma (@Sample (config p))))
    (catalog : oldCatalog s = newCatalog s)
    (agree : AgreeOn (historyFootprint p s messages) old new) :
    WHIRReplay.decodeHistory p oldCatalog old s messages ancestors =
      WHIRReplay.decodeHistory p newCatalog new s messages ancestors := by
  induction messages generalizing ancestors with
  | nil => rfl
  | cons m messages ih =>
    cases messages with
    | nil =>
      cases ancestors with
      | nil => simp only [WHIRReplay.decodeHistory,catalog]
      | cons a rest => rfl
    | cons previous older =>
      cases ancestors with
      | nil => rfl
      | cons a past =>
        rcases a with ⟨previous',q,x⟩
        have priorAgree : AgreeOn (historyFootprint p s (previous :: older)) old new :=
          agree.mono (fun ref member => List.mem_append_left _ member)
        have currentAgree : AgreeOn
            (replyFootprint (WHIRReplay.query p (s,previous :: older)) m.scalars) old new :=
          agree.mono (fun ref member => List.mem_append_right _ member)
        have prior := ih past priorAgree
        by_cases phase : q = WHIRReplay.query p (s,previous :: older)
        · have current : ∀ before : WHIRReplay.Replay p,
              WHIRReplay.step old before q x m = WHIRReplay.step new before q x m :=
            fun before => step_congr old new before q x m (by simpa only [phase] using currentAgree)
          simp only [WHIRReplay.decodeHistory,phase,↓reduceDIte]
          simp_rw [prior,current]
        · simp [WHIRReplay.decodeHistory,phase]

theorem decode_congr (p : Profile) (oldCatalog newCatalog : WHIRReplay.Catalog p)
    (old new : WHIRReplay.Roots) (key : WHIRReplay.Key p)
    (catalog : oldCatalog key.statement = newCatalog key.statement)
    (agree : AgreeOn (historyFootprint p key.statement key.messages) old new) :
    WHIRReplay.decode p oldCatalog old key = WHIRReplay.decode p newCatalog new key :=
  decodeHistory_congr p oldCatalog newCatalog old new key.statement key.messages key.ancestors catalog agree

theorem keyBad_congr (p : Profile) (oldCatalog newCatalog : WHIRReplay.Catalog p)
    (old new : WHIRReplay.Roots) (key : WHIRReplay.Key p) (x : WHIRReplay.Answer p key)
    (catalog : oldCatalog key.statement = newCatalog key.statement)
    (agree : AgreeOn (historyFootprint p key.statement key.messages) old new) :
    WHIRROM.keyBad p oldCatalog old key x ↔ WHIRROM.keyBad p newCatalog new key x := by
  simp only [WHIRROM.keyBad,decode_congr p oldCatalog newCatalog old new key catalog agree]

theorem stack_decodeInitial_congr (p : Profile) (cap : Nat)
    (oldCatalog newCatalog : StackWHIRReplay.Catalog p cap) (key : StackWHIRReplay.Key p)
    (catalog : oldCatalog key.statement = newCatalog key.statement) :
    StackWHIRReplay.decodeInitial p cap oldCatalog key =
      StackWHIRReplay.decodeInitial p cap newCatalog key := by
  simp only [StackWHIRReplay.decodeInitial,catalog]

theorem stack_decode_congr (p : Profile) (cap : Nat)
    (oldCatalog newCatalog : StackWHIRReplay.Catalog p cap) (old new : WHIRReplay.Roots)
    (key : StackWHIRReplay.Key p)
    (catalog : oldCatalog key.statement = newCatalog key.statement)
    (agree : AgreeOn (historyFootprint p key.statement key.messages) old new) :
    StackWHIRReplay.decode p cap oldCatalog old key = StackWHIRReplay.decode p cap newCatalog new key := by
  have decoded : ∀ (data : WHIRFiatShamir.StackInitial p cap) seed,
      WHIRReplay.decode p (StackWHIRReplay.localCatalog data seed) old (StackWHIRReplay.projectKey key) =
      WHIRReplay.decode p (StackWHIRReplay.localCatalog data seed) new (StackWHIRReplay.projectKey key) :=
    fun data seed => decode_congr p _ _ old new _ rfl agree
  simp only [StackWHIRReplay.decode,catalog]
  simp_rw [decoded]

theorem stack_keyBad_congr (p : Profile) (cap : Nat)
    (oldCatalog newCatalog : StackWHIRReplay.Catalog p cap) (old new : WHIRReplay.Roots)
    (key : StackWHIRReplay.Key p) (x : StackWHIRReplay.Answer p key)
    (catalog : oldCatalog key.statement = newCatalog key.statement)
    (agree : AgreeOn (historyFootprint p key.statement key.messages) old new) :
    StackWHIRROM.keyBad p cap oldCatalog old key x ↔ StackWHIRROM.keyBad p cap newCatalog new key x := by
  simp only [StackWHIRROM.keyBad,stack_decodeInitial_congr p cap oldCatalog newCatalog key catalog,
    stack_decode_congr p cap oldCatalog newCatalog old new key catalog agree]

theorem stack_historyFailure_congr (p : Profile) (cap : Nat)
    (oldCatalog newCatalog : StackWHIRReplay.Catalog p cap) (old new : WHIRReplay.Roots)
    (s : Digest32) (messages : List Pending)
    (history : List (Pending × Sigma (@StackWHIRReplay.Sample (config p))))
    (catalog : oldCatalog s = newCatalog s)
    (agree : AgreeOn (historyFootprint p s messages) old new) :
    StackWHIRROM.HistoryFailure p cap oldCatalog old s messages history ↔
      StackWHIRROM.HistoryFailure p cap newCatalog new s messages history := by
  have decoded : ∀ past, StackWHIRReplay.decode p cap oldCatalog old ⟨s,messages,past⟩ =
      StackWHIRReplay.decode p cap newCatalog new ⟨s,messages,past⟩ :=
    fun past => stack_decode_congr p cap oldCatalog newCatalog old new _ catalog agree
  simp only [StackWHIRROM.HistoryFailure,decoded]

theorem terminalFailure_congr (p : Profile) (oldCatalog newCatalog : WHIRReplay.Catalog p)
    (old new : WHIRReplay.Roots) {B : Nat} (result : WHIRROM.TerminalView p B)
    (catalog : oldCatalog result.request.statement = newCatalog result.request.statement)
    (agree : AgreeOn (historyFootprint p result.request.statement result.request.messages) old new) :
    WHIRROM.TerminalFailure p oldCatalog old result ↔ WHIRROM.TerminalFailure p newCatalog new result := by
  have decoded : ∀ past,
      WHIRReplay.decode p oldCatalog old ⟨result.request.statement,result.request.messages,past⟩ =
      WHIRReplay.decode p newCatalog new ⟨result.request.statement,result.request.messages,past⟩ :=
    fun past => decode_congr p oldCatalog newCatalog old new _ catalog agree
  simp only [WHIRROM.TerminalFailure,decoded]

/-- A frozen allocation needs no commitment first mentioned later in its branch. -/
theorem historyFootprint_drop (p : Profile) (s : Digest32) (messages : List Pending)
    (i : Nat) : ∀ ref ∈ historyFootprint p s (messages.drop i),
      ref ∈ historyFootprint p s messages := by
  induction i generalizing messages with
  | zero => simp
  | succ i ih =>
    cases messages with
    | nil => simp [historyFootprint]
    | cons m messages =>
      cases messages with
      | nil => simp [historyFootprint,List.drop]
      | cons previous older =>
        intro ref member
        exact List.mem_append_left _ (ih (previous :: older) ref member)

theorem AgreeOn.drop {p : Profile} {s : Digest32} {messages : List Pending}
    {old new : WHIRReplay.Roots} (agree : AgreeOn (historyFootprint p s messages) old new)
    (i : Nat) : AgreeOn (historyFootprint p s (messages.drop i)) old new :=
  agree.mono (historyFootprint_drop p s messages i)

end Whir.WHIRSnapshotReplay
