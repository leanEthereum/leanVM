import Whir.StackWHIRReplay

/-! Scalar-history reconstruction from actual counted Merkle opening rows. Query rows are supplied by the physical verifier, in sampled order, and are never synthesized by this decoder. Scalar, root, nonce, ancestor and position guards are the existing transport guards. Frozen root lookup reconstructs ghost next-oracle fields only; it is not native Merkle acceptance. Row dimensions and authentication belong to the physical opening checker. -/
namespace Whir.WHIRPhysicalHistory
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open FiatShamirGame (Digest32)
open WHIRHistory (Pending)

abbrev Rows := Nat → Oracle

def reply {p : Profile} (roots : WHIRReplay.Roots) (rows : Rows)
    (q : Coordinate (config p)) (pending : Pending) : Option Reply :=
  WHIRHistory.decodeReplyScalars q
    (fun digest => roots digest (WHIRHistory.coordinateLevel q + 1))
    (match q with | .query i => rows i.val | _ => #[]) pending.scalars

@[simp] theorem reply_query {p : Profile} (roots : WHIRReplay.Roots) (rows : Rows)
    (i : Fin (config p).folds.size) (pending : Pending) :
    reply roots rows (.query i) pending =
      (WHIRHistory.decodeMessage pending.scalars).map (Reply.query (rows i.val)) := rfl

theorem reply_fold_root {p : Profile} (roots : WHIRReplay.Roots) (rows : Rows)
    (i : Fin (config p).folds.size) (j : Fin (config p).folds[i.val]!)
    (last : j.val + 1 = (config p).folds[i.val]!) (next : i.val + 1 < (config p).folds.size)
    (a b r s : E) (nonce : Option (Nat × E)) :
    reply roots rows (.fold i j) ⟨[a,b,r,s],nonce⟩ =
      (ByteCodec.scalarsToHash (r,s)).map
        (fun digest => .fold ⟨a,b⟩ (some (roots digest (i.val+1))) #[]) := by
  simp [reply, WHIRHistory.decodeReplyScalars, WHIRHistory.coordinateLevel, last, next]

def step {p : Profile} (roots : WHIRReplay.Roots) (rows : Rows) (r : WHIRReplay.Replay p)
    (q : Coordinate (config p)) (x : Sample q) (pending : Pending) : Option (WHIRReplay.Replay p) :=
  (reply roots rows q pending).map (fun response =>
    ⟨r.statement,set q r.tape x,r.replies.push response⟩)

theorem step_eq {p : Profile} (roots : WHIRReplay.Roots) (rows : Rows) (r : WHIRReplay.Replay p)
    (q : Coordinate (config p)) (x : Sample q) (pending : Pending)
    (agrees : match q,x with | .query i,x => rows i.val = WHIRReplay.queryRows r i x | _,_ => True) :
    step roots rows r q x pending = WHIRReplay.step roots r q x pending := by
  cases q with
  | query i => simp only [step,WHIRReplay.step,reply,WHIRReplay.reply,agrees]
  | initial => rfl
  | fold i j => rfl
  | ood i j => rfl
  | tail j => rfl

/-- Exact existing history guards; only the query-row source differs. -/
def decodeHistory (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    (rows : Rows) (s : Digest32) :
    List Pending → List (Pending × Sigma (@Sample (config p))) → Option (WHIRReplay.Replay p)
  | [], _ => none
  | [m], [] => do
    if m.scalars.isEmpty && m.nonce.isNone then
      let statement ← catalog s
      pure ⟨statement,WHIRReplay.zeroTape p,#[]⟩
    else none
  | m :: previous :: older, (previous',⟨q,x⟩) :: past => do
    if previous' = previous then
      if q = WHIRReplay.query p (s,previous::older) then
        if position q = older.length then
          if position (WHIRReplay.query p (s,m::previous::older)) = older.length + 1 then
            if WHIRReplay.nonceShape (WHIRReplay.query p (s,m::previous::older)) m then
              let before ← decodeHistory p catalog roots rows s (previous::older) past
              step roots rows before q x m
            else none
          else none
        else none
      else none
    else none
  | _, _ => none

/-- Only recorded query answers and successfully parsed physical prefixes enter the agreement premise. This is literal equality of opened rows with frozen sampled rows, not an assumed decoder-correctness or soundness certificate. -/
def RowsAgree (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    (rows : Rows) (s : Digest32) (messages : List Pending)
    (ancestors : List (Pending × Sigma (@Sample (config p)))) : Prop :=
  ∀ (k : Nat) (previous : Pending) (i : Fin (config p).folds.size) (x : Sample (.query i))
    (before : WHIRReplay.Replay p),
    ancestors[k]? = some (previous,⟨.query i,x⟩) →
    decodeHistory p catalog roots rows s (messages.drop (k+1)) (ancestors.drop (k+1)) = some before →
    rows i.val = WHIRReplay.queryRows before i x

theorem RowsAgree_tail {p : Profile} {catalog : WHIRReplay.Catalog p} {roots : WHIRReplay.Roots}
    {rows : Rows} {s : Digest32} {m messages a ancestors}
    (agree : RowsAgree p catalog roots rows s (m::messages) (a::ancestors)) :
    RowsAgree p catalog roots rows s messages ancestors := by
  intro k previous i x before entry parsed
  apply agree (k+1) previous i x before
  · simpa using entry
  · simpa [Nat.add_assoc] using parsed

theorem decodeHistory_eq (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    (rows : Rows) (s : Digest32) (messages : List Pending)
    (ancestors : List (Pending × Sigma (@Sample (config p))))
    (agree : RowsAgree p catalog roots rows s messages ancestors) :
    decodeHistory p catalog roots rows s messages ancestors =
      WHIRReplay.decodeHistory p catalog roots s messages ancestors := by
  induction messages generalizing ancestors with
  | nil => rfl
  | cons m messages ih =>
    cases messages with
    | nil => cases ancestors <;> rfl
    | cons previous older =>
      cases ancestors with
      | nil => rfl
      | cons entry past =>
        rcases entry with ⟨previous',q,x⟩
        have priorEq := ih past (RowsAgree_tail agree)
        simp only [decodeHistory,WHIRReplay.decodeHistory]
        split
        · split
          · split
            · split
              · split
                · rw [← priorEq]
                  cases parsed : decodeHistory p catalog roots rows s (previous::older) past with
                  | none => rfl
                  | some before =>
                    apply step_eq
                    cases q with
                    | query i => exact agree 0 previous' i x before (by simp) (by simpa using parsed)
                    | initial => trivial
                    | fold i j => trivial
                    | ood i j => trivial
                    | tail j => trivial
                · rfl
              · rfl
            · rfl
          · rfl
        · rfl

def decode (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    (rows : Rows) (key : WHIRReplay.Key p) : Option (WHIRReplay.Replay p) :=
  decodeHistory p catalog roots rows key.statement key.messages key.ancestors

theorem decode_eq (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    (rows : Rows) (key : WHIRReplay.Key p)
    (agree : RowsAgree p catalog roots rows key.statement key.messages key.ancestors) :
    decode p catalog roots rows key = WHIRReplay.decode p catalog roots key :=
  decodeHistory_eq p catalog roots rows key.statement key.messages key.ancestors agree

theorem decodeHistory_success (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    (rows : Rows) (s : Digest32) (messages : List Pending)
    (ancestors : List (Pending × Sigma (@Sample (config p)))) (out : WHIRReplay.Replay p)
    (agree : RowsAgree p catalog roots rows s messages ancestors)
    (parsed : decodeHistory p catalog roots rows s messages ancestors = some out) :
    WHIRReplay.decodeHistory p catalog roots s messages ancestors = some out := by
  rwa [decodeHistory_eq p catalog roots rows s messages ancestors agree] at parsed

/-- Preserve the full initial eight-scalar stack answer, then project its WHIR lambda exactly as the existing stack decoder does. -/
def decodeStack (p : Profile) (cap : Nat) (catalog : StackWHIRReplay.Catalog p cap)
    (roots : WHIRReplay.Roots) (rows : Rows) (key : StackWHIRReplay.Key p) :
    Option (StackWHIRReplay.Replay p cap) := do
  let original ← catalog key.statement
  let initial ← StackWHIRReplay.initialSeed key.ancestors
  let whir ← decode p (StackWHIRReplay.localCatalog original initial) roots rows
    (StackWHIRReplay.projectKey key)
  pure ⟨original,initial,whir⟩

def StackRowsAgree (p : Profile) (cap : Nat) (catalog : StackWHIRReplay.Catalog p cap)
    (roots : WHIRReplay.Roots) (rows : Rows) (key : StackWHIRReplay.Key p) : Prop :=
  ∀ original initial, catalog key.statement = some original →
    StackWHIRReplay.initialSeed key.ancestors = some initial →
    RowsAgree p (StackWHIRReplay.localCatalog original initial) roots rows
      key.statement key.messages (key.ancestors.map StackWHIRReplay.projectEntry)

theorem decodeStack_eq (p : Profile) (cap : Nat) (catalog : StackWHIRReplay.Catalog p cap)
    (roots : WHIRReplay.Roots) (rows : Rows) (key : StackWHIRReplay.Key p)
    (agree : StackRowsAgree p cap catalog roots rows key) :
    decodeStack p cap catalog roots rows key = StackWHIRReplay.decode p cap catalog roots key := by
  unfold decodeStack StackWHIRReplay.decode
  cases found : catalog key.statement with
  | none => rfl
  | some original =>
    cases seed : StackWHIRReplay.initialSeed key.ancestors with
    | none => rfl
    | some initial =>
      change (decode p (StackWHIRReplay.localCatalog original initial) roots rows
        (StackWHIRReplay.projectKey key)).bind (fun whir => some (StackWHIRReplay.Replay.mk original initial whir)) =
        (WHIRReplay.decode p (StackWHIRReplay.localCatalog original initial) roots
          (StackWHIRReplay.projectKey key)).bind (fun whir => some (StackWHIRReplay.Replay.mk original initial whir))
      rw [decode_eq p (StackWHIRReplay.localCatalog original initial) roots rows
        (StackWHIRReplay.projectKey key) (agree original initial found seed)]

theorem decodeStack_success (p : Profile) (cap : Nat) (catalog : StackWHIRReplay.Catalog p cap)
    (roots : WHIRReplay.Roots) (rows : Rows) (key : StackWHIRReplay.Key p)
    (out : StackWHIRReplay.Replay p cap) (agree : StackRowsAgree p cap catalog roots rows key)
    (parsed : decodeStack p cap catalog roots rows key = some out) :
    StackWHIRReplay.decode p cap catalog roots key = some out := by
  rwa [decodeStack_eq p cap catalog roots rows key agree] at parsed

end Whir.WHIRPhysicalHistory
