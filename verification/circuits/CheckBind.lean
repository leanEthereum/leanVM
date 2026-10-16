import LeanVMCircuits.Rec.Dump
import LeanVMCircuits.Rec.Bind
import LeanVMCircuits.Rec.SideCert
import LeanVMCircuits.Rec.Flocked

/-!
`lake exe checkbind <dump>...`: replay each dump's builder calls through the model and check transcript binding
(`LeanVMCircuits.Rec.Bind`): every test reading a challenge reads only wires some transcript binds. The verdict is
`Bind.Cert.accepts` of the certificate the analysis records, which `Bind.checkbind_sound` proves sound. An accepted dump
also fails unless every WHIR sumcheck is certified from its opening's first claim and every hint a certified input
claim reads is the value of an `edge term` mark, a claim the node's reduction takes. It also fails unless every named table sumcheck has both bus sides certified call by call (`Bind.sidesOk`), their fingerprint weights and `β` the bus draw's `eq_table` and challenges (`Bind.DrawCert.ok`), and its child's flock reduction certified on its transcript (`Bind.FlockCert.ok`: the zerocheck, lincheck, ring switch and Lagrange weights, linked).

`--expect-unbound <dump>` checks a dump fails, the regression fixture of a circuit that did not bind.
-/

open LeanVMCircuits.Rec

def replay (path : System.FilePath) : IO (Option (Bind.Replay × Array String)) := do
  let text ← IO.FS.readFile path
  let (calls, _, _) ← match Dump.sections text with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let mut rp : Bind.Replay := {}
  -- Each call's line, for messages: marks are lines but not calls.
  let mut callLines : Array String := #[]
  for line in calls do
    match Dump.parseLine line with
    | .ok (.call call) =>
      unless call.args.all (· < rp.state.next) && call.ok do
        IO.eprintln s!"{path}: a call names a wire not yet made or has the wrong size: {line}"; return none
      rp := rp.step call
      callLines := callLines.push line
    | .ok mark =>
      match rp.mark mark with
      | .ok r => rp := r
      | .error e => IO.eprintln s!"{path}: {e}"; return none
    | .error e => IO.eprintln s!"{path}: {e}"; return none
  if rp.pending.isSome then
    IO.eprintln s!"{path}: a marked block without its end"; return none
  return some (rp, callLines)

/-- Check one dump; `true` when it binds. -/
def check (path : System.FilePath) : IO (Option Bool) := do
  let some (rp, lines) ← replay path | return none
  let probe := ((← IO.getEnv "CHECKBIND_PROBE").getD "").splitOn "," |>.filterMap String.toNat?
  let r := Bind.analyse rp probe
  for (w, ts) in r.probes do
    IO.println s!"  probe {w} (made at call {rp.maker.getD w 0 + 1}): {repr ts}"
  let line := fun (i : ℕ) => s!"call {i + 1}: {(lines.getD i "").take 120}"
  IO.println s!"{path}: {if r.accepted then "accepted" else "rejected"}: {r.transcripts} transcripts, {r.squeezes} squeezes, {r.products} union products, \
    {r.tests} tests reading a challenge, \
    {r.unbound.size} unbound, {r.late.size} bound only after their latest challenge, \
    {r.deferred.size} bound only with the statement's claims; \
    {r.exposed} statement words read a challenge, {r.exposedUnbound.size} unbound; \
    {r.sumchecks} tests close a certified sumcheck ({r.rounds} rounds, {r.residuals} of them by a residual, their \
    input claims reading {r.hints.length} hints, {r.tables} named as a table sumcheck, {r.gkrs} with their bus GKR \
    named from root to totals over {r.gkrLayers} layers past the first, {r.resids} with their residual certified \
    term by term), \
    {r.powTests} are the bits of {r.pows} certified proof-of-work checks, {r.odds} close a certified GKR odd layer, \
    {r.tops} a certified GKR radix-four top layer, {r.whirs} a certified WHIR sumcheck ({r.whirRounds} rounds, \
    {r.whirBatches} of them batching a level's claims, {r.whirPartial} sumchecks not from the opening's first claim), \
    {r.splits} a certified claim split"
  for f in r.unbound.toList.take 10 do
    IO.println s!"  unbound test at {line f.call}, per transcript {repr f.perTranscript}"
    for h in f.hints.eraseDups do
      IO.println s!"    hinted at {line h}"
  for i in r.others do
    IO.println s!"  other eq_e test at {line i}"
  for f in r.deferred do
    IO.println s!"  test bound only with the statement at {line f.call}"
  for f in r.late.toList.take 5 do
    IO.println s!"  late test at {line f.call}: bound at call {f.hints.headD 0 + 1}, latest challenge at call \
      {f.hints.getD 1 0 + 1}"
  if !r.chalsOk then
    IO.println s!"  the certified checks' challenges are not drawn in order from the oracle's words"
  if r.accepted != r.unbound.isEmpty && r.chalsOk then
    IO.println s!"  the certificate's verdict differs from the worklist's"
  if !r.accepted then return some false
  -- Every WHIR sumcheck is certified from its opening's first claim, its query batches included.
  if r.whirPartial != 0 then
    IO.eprintln s!"{path}: {r.whirPartial} WHIR sumchecks are not certified from their opening's first claim"
    return none
  -- Every residual sumcheck is a table sumcheck reading the bus totals and a GKR root (`Bind.TableCert`).
  if r.tables != r.residuals || !r.tablesOk then
    IO.eprintln s!"{path}: {r.tables} of {r.residuals} residual sumchecks named as table sumchecks, checks passing: \
      {r.tablesOk}"
    return none
  -- Every table sumcheck's bus GKR is named from its root to its totals (`Bind.GkrCert`).
  if r.gkrs != r.tables || !r.gkrsOk then
    IO.eprintln s!"{path}: {r.gkrs} of {r.tables} table sumchecks with their bus GKR named, checks passing: {r.gkrsOk}"
    return none
  -- Every table sumcheck's residual is named term by term (`Bind.ResidCert`).
  if r.resids != r.tables || !r.residsOk then
    IO.eprintln s!"{path}: {r.resids} of {r.tables} table sumchecks with their residual named, checks passing: \
      {r.residsOk}"
    return none
  -- Each table sumcheck's bus sides are `Side::decompose` over the marked blocks (`Bind.SideCert`, `Bind.sidesOk`), their
  -- fingerprint weights and `β` the bus draw's `eq_table` and challenges (`Bind.DrawCert`).
  let groups := Bind.busGroups (← IO.FS.readFile path)
  let mut sides := 0
  for (tc, g, rc) in r.named do
    let some (_, mu, push, pull) := (groups.filter (·.1 < tc.target)).getLast? | break
    let zeta := g.point r.scs r.topCerts r.oddCerts r.outs
    let some outs := Bind.LayerCert.chain r.scs rp.calls r.relax r.outs g.layers
      (g.start r.topCerts r.oddCerts r.outs).2.1 (g.start r.topCerts r.oddCerts r.outs).2.2 | break
    let pos := outs.foldl (fun p v => max p (rp.maker.getD v 0 + 1)) 0
    let some (w, beta) := Bind.weightsOf rp.calls r.outs rp.maker pos mu zeta (push.headD default) | break
    let some (s0, pos1) := Bind.sideOf rp.calls r.outs pos mu zeta w beta push none | break
    let some (s1, _) := Bind.sideOf rp.calls r.outs pos1 mu zeta w beta pull (some s0.formZero) | break
    unless Bind.sidesOk r.outs rp.calls r.relax r.scs r.topCerts r.oddCerts g rc s0 s1 do break
    let tr := (r.scs[tc.sc]?.map (·.transcript)).getD 0
    let some dc := Bind.drawOf rp r.ts tr s0.w s0.beta | break
    unless dc.ok r.outs rp.state rp.calls r.relax r.ts s0 do break
    sides := sides + 1
  IO.println s!"  {sides} of {r.named.length} table sumchecks with both bus sides certified call by call, their weights \
    and β the bus draw's"
  if sides != r.named.length then
    IO.eprintln s!"{path}: {sides} of {r.named.length} table sumchecks with their bus sides and draw certified"
    return none
  -- Each table sumcheck's child has flock's reduction over its hash rows named on its transcript (`Bind.FlockCert`), its
  -- lincheck of `Bind.hashRounds` rounds (`Bind.FlockCert.roundsOk`) and its zerocheck over the hash term's height
  -- (`Bind.FlockCert.heightOk`).
  let flocks := Bind.flocksOf rp r.scs r.outs r.relax
  let flocked := r.named.countP fun (tc, _, rc) =>
    flocks.any fun fc => (r.scs[fc.zero.sc]?.map (·.transcript)) == (r.scs[tc.sc]?.map (·.transcript)) &&
      fc.roundsOk r.scs && fc.heightOk r.scs rc
  IO.println s!"  {flocks.size} flock reductions certified (zerocheck, lincheck, ring switch, Lagrange weights), \
    {flocked} of {r.named.length} table sumchecks with their child's, its lincheck of {Bind.hashRounds} rounds and its \
    zerocheck over the hash term's height"
  if flocked != r.named.length then
    IO.eprintln s!"{path}: {flocked} of {r.named.length} table sumchecks with their child's flock reduction certified, \
      its lincheck of {Bind.hashRounds} rounds and its zerocheck over the hash term's height"
    return none
  -- Each named table sumcheck's residual is its own (`sc`, `ξ`) over its point, each owned table's term within its
  -- rounds (`Bind.ResidCert.tausOk`), and its last side a `zero` call's output (`Edges.ChildCerts.Ok`).
  let idx := Bind.outIndex rp
  let linked := r.named.countP fun (tc, _, rc) => rc.sc == tc.sc && rc.xi == tc.xi &&
    match r.scs[tc.sc]? with
    | some sc => decide (sc.rounds.length ≤ rc.zeta.length) && rc.tausOk sc.rounds.length &&
        (Bind.zeroAt rp idx sc.final).any fun j => Bind.callsOk rp.calls r.relax [(j, .zero)] && Bind.o r.outs j == sc.final
    | none => false
  IO.println s!"  {linked} of {r.named.length} table sumchecks with their residual linked, its terms within the rounds, \
    and tested against zero"
  if linked != r.named.length then
    IO.eprintln s!"{path}: {linked} of {r.named.length} table sumchecks with their residual linked, its terms within the \
      rounds, and tested against zero"
    return none
  -- Each hint a certified input claim reads is a claim the node's reduction takes: an `edge term`'s value.
  let terms : Std.HashSet ℕ := (Dump.edgeLines (← IO.FS.readFile path)).foldl (fun acc ws => match ws with
    | "term" :: _ :: _ :: _ :: _ :: v :: _ => match v.toNat? with
      | some w => acc.insert w
      | none => acc
    | _ => acc) {}
  if let some w := r.hints.find? (!terms.contains ·) then
    IO.eprintln s!"{path}: the hint at wire {w} a certified input claim reads is no claim the reduction takes"
    return none
  return some true

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  let mut expectUnbound := false
  for a in args do
    if a = "--expect-unbound" then expectUnbound := true
    else
      match ← check a with
      | none => ok := false
      | some binds =>
        if binds = expectUnbound then
          IO.eprintln s!"{a}: expected {if expectUnbound then "an unbound test" else "every test bound"}"
          ok := false
      expectUnbound := false
  return if ok then 0 else 1
