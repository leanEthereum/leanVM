import LeanVMCircuits.Rec.EdgeMarks
import LeanVMCircuits.Rec.DesignClaims
import LeanVMCircuits.Rec.DigestEdges

/-!
`lake exe checkedges <dump>...`: read each dump's edge marks (its statement's layout, each child's statement words, the claims its reduction takes), find the calls computing each child's scale from its kind word, the call reading its digest and the calls by which its verifier absorbs and reads its words (`Edges.InstCert`), and check the certificate (`Edges.EdgeCert.check`, which `Edges.EdgeCert.edge` and `Edges.InstCert.verifies` prove sound), and that each child's scale is computed in its tier's mode (`DesignClaims.modeOk`, under which `DesignClaims.tierMode_scale` makes it zero exactly at the first level). For a wrap and a node of a tree of outputs, find the calls by which its statement exposes its digest (`Edges.DigestCert`) and check them (`Edges.DigestCert.ok`, under which `Edges.DigestCert.wrap_states` and `Edges.DigestCert.node_states` prove the digest the wrap's child's or the tree digest of the node's children's). Dumps of one tree (the name up to `-first`, `-node` or `-circuit-`) must share a layout.
-/

open LeanVMCircuits.Rec Model Edges

/-- The calls whose outputs include each wire, with the output's position. -/
def outIndex (os : Array (List ℕ)) : Std.HashMap ℕ (Array (ℕ × ℕ)) := Id.run do
  let mut idx : Std.HashMap ℕ (Array (ℕ × ℕ)) := {}
  for j in [0:os.size] do
    let mut k := 0
    for w in os[j]! do
      idx := idx.insert w ((idx.getD w #[]).push (j, k))
      k := k + 1
  return idx

/-- The calls computing a child's scale wire `s` from its kind word `kw`, as `Design::kind_bits` makes them. -/
def scaleOf (cs : Array Call) (os : Array (List ℕ)) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (kw s : ℕ) :
    Option ScaleCert := do
  if s = kw then return .kind
  let makers := fun (w : ℕ) => (idx.getD w #[]).toList.filterMap fun (j, k) => if k = 0 then some j else none
  if let some c := (makers s).find? (cs[·]? == some Call.one) then return .one c
  let (last, f, one) ← (makers s).findSome? fun j => match (cs[j]? : Option Call) with
    | some (Call.add f one) => some (j, f, one)
    | _ => none
  let o ← (makers one).find? (cs[·]? == some Call.one)
  let e ← (List.range cs.size).find? (cs[·]? == some (Call.eToK kw))
  let sp ← (List.range cs.size).find? (cs[·]? == some (.split (out os e 0)))
  let mut acc := f
  let mut steps : List (ℕ × ℕ × ℕ) := []
  for _ in [0:65] do
    if acc = one then break
    let step := (makers acc).findSome? fun m => do
      let some (Call.mul a n) := (cs[m]? : Option Call) | none
      let (p, t) ← (makers n).findSome? fun p => match (cs[p]? : Option Call) with
        | some (Call.add t o') => if o' == one then some (p, t) else none
        | _ => none
      let k ← (makers t).find? fun k => match (cs[k]? : Option Call) with
        | some (Call.kToE1 _) => true
        | _ => false
      pure (a, k, p, m)
    let (a, k, p, m) ← step
    steps := (k, p, m) :: steps
    acc := a
  return .bits o e sp last steps

/-- The call whose output `k` is wire `w`, if one is. -/
def makerAt (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (w k : ℕ) : Option ℕ :=
  (idx.getD w #[]).toList.findSome? fun (j, k') => if k' = k then some j else none

/-- Where a statement exposes its digest (`Edges.DigestCert`): the `expose_e` calls at statement positions 1 and 2, the `k_to_e` halves they expose, the `d_to_k` and zero those read, and the digest's source: for a wrap the `halves_to_d` reading its child's words, else the `chain` over a header's `k_const`s and each child's `d_to_k` of a `halves_to_d`. -/
def digestOf (cs : Array Call) (os : Array (List ℕ)) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (wrap : Bool)
    (children : ℕ) : Option DigestCert := do
  let mut at1 : Option ℕ := none
  let mut at2 : Option ℕ := none
  for j in [0:cs.size] do
    if let some (.exposeE _) := (cs[j]? : Option Call) then
      if out os j 0 = 1 then at1 := some j
      if out os j 0 = 2 then at2 := some j
  let e1 ← at1
  let e2 ← at2
  let exposed := fun (j : ℕ) => match (cs[j]? : Option Call) with
    | some (.exposeE w) => makerAt idx w 0
    | _ => none
  let h0 ← exposed e1
  let h1 ← exposed e2
  let some (.kToE a _ zw) := (cs[h0]? : Option Call) | none
  let dk ← makerAt idx a 0
  let z ← makerAt idx zw 0
  let some (.dToK d) := (cs[dk]? : Option Call) | none
  let s ← makerAt idx d 0
  let src ← if wrap then pure (DigestSrc.wrap s) else do
    let some (.chain words) := (cs[s]? : Option Call) | none
    let header ← (words.take 8).mapM (makerAt idx · 0)
    let reads ← (List.range children).mapM fun i => do
      let r2 ← makerAt idx (words.getD (8 + 4 * i) 0) 0
      let some (.dToK hd) := (cs[r2]? : Option Call) | none
      pure ((← makerAt idx hd 0), r2)
    pure (DigestSrc.node s header reads)
  return { src, dk, z, h0, h1, e1, e2 }

/-- Where the child's verifier (`RecShape::verify`) reads its words `ws`: the first `leaf_block` absorbing the first word's limbs after a count, the blocks chained from it over the instance, each word's `e_to_k` call there, and every `mul_k_add` chain reading one limb of each word in order from a `zero`. -/
def instOf (cs : Array Call) (os : Array (List ℕ)) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (ws : List ℕ) :
    Option InstCert := do
  let n := ws.length
  let isE0 := fun (w : ℕ) => (idx.getD w #[]).toList.any fun (j, k) => k = 0 && cs[j]? == some (Call.eToK (ws.getD 0 0))
  -- Each `leaf_block` by the chaining value it reads, and each `mul_k_add` by the accumulator it adds to.
  let mut byH : Std.HashMap ℕ ℕ := {}
  let mut byD : Std.HashMap ℕ (Array ℕ) := {}
  let mut first : Option ℕ := none
  for j in [0:cs.size] do
    match (cs[j]? : Option Call) with
    | some (.leafBlock h m _ _) =>
      unless byH.contains h do byH := byH.insert h j
      if first.isNone && isE0 (m.getD 1 0) then first := some j
    | some (.mulKAdd _ _ d) => byD := byD.insert d ((byD.getD d #[]).push j)
    | _ => pure ()
  let b0 ← first
  let mut blocks := [b0]
  for _ in [1:(4 * n + 1 + 7) / 8] do
    blocks := blocks ++ [← byH[out os (blocks.getLast?.getD 0) 0]?]
  let msgAt := fun (i : ℕ) => match cs[blocks.getD (i / 8) 0]? with
    | some (.leafBlock _ m _ _) => m.getD (i % 8) 0
    | _ => 0
  let h0 ← match cs[b0]? with
    | some (.leafBlock h _ _ _) => some h
    | _ => none
  let ic : InstCert := {
    limbs := (List.range n).map fun z => (makerAt idx (msgAt (1 + 4 * z)) 0).getD 0
    count := (makerAt idx (msgAt 0) 0).getD 0
    zero := (makerAt idx (msgAt 4) 0).getD 0
    seed := (makerAt idx h0 0).getD 0
    blocks
    shares := [] }
  let isZero := fun (w : ℕ) => (idx.getD w #[]).toList.findSome? fun (j, k) =>
    if k = 0 && cs[j]? == some Call.zero then some j else none
  let mut shares := []
  for c in [0:4] do
    for (d, js) in byD.toList do
      let some z0 := isZero d | continue
      for j in js do
        let mut chain := [j]
        let mut ok := true
        for z in [0:n] do
          let cur := chain.getLast?.getD 0
          match cs[cur]? with
          | some (.mulKAdd _ k _) =>
            unless k == ic.limbWire os z c do ok := false; break
          | _ => ok := false; break
          if z + 1 < n then
            match (byD.getD (out os cur 0) #[]).toList.find? (fun j' => match (cs[j']? : Option Call) with
                | some (.mulKAdd _ k _) => k == ic.limbWire os (z + 1) c
                | _ => false) with
            | some j' => chain := chain ++ [j']
            | none => ok := false; break
        if ok then shares := shares ++ [(c, z0, chain)]
  return { ic with shares }

/-- The certificate of a dump's calls, outputs and marks. -/
def certOf (cs : Array Call) (os : Array (List ℕ)) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (m : Marks) (L : Layout) :
    Except String EdgeCert := do
  let claims : Claims ℕ := ⟨m.dense.toList, m.matrices.toList⟩
  let mut children := #[]
  for (i, (j, ws)) in m.children.toList.zipIdx.map (fun (x, i) => (i, x)) do
    unless i = j do .error s!"child {j} marked {i}th"
    let w := fun (n : ℕ) => ws.getD n 0
    -- The scale is the one on the fixed polynomial's claim at the child's words.
    let fixed := stmtDense L w 0 2
    let some s := claims.dense.findSome? fun d =>
        if d.poly = 2 ∧ d.low = fixed.low ∧ d.terms.map (·.value) = [w (L.dv + 2)] then
          d.terms.head?.bind (·.scale)
        else none
      | .error s!"child {j}: no claim on the fixed polynomial at its words"
    let some sc := scaleOf cs os idx (w 0) s | .error s!"child {j}: no calls computing its scale"
    let some dg := (List.range cs.size).find? (cs[·]? == some (.halvesToD (w 1) (w 2)))
      | .error s!"child {j}: its digest is not read"
    let some inst := instOf cs os idx ws | .error s!"child {j}: its verifier does not absorb its words"
    children := children.push { words := ws, scale := sc, digest := dg, inst }
  return { calls := cs, layout := L, claims, children := children.toList }

def modeName : Mode → String
  | .kind => "kind word"
  | .one => "one"
  | .bits b => s!"{b} kind bits"

/-- Check one dump; its layout when the certificate accepts. -/
def check (path : System.FilePath) : IO (Option Layout) := do
  let text ← IO.FS.readFile path
  let (lines, _, _) ← match Dump.sections text with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let mut calls : Array Call := #[]
  for line in lines do
    match Dump.parseLine line with
    | .ok (.call c) => calls := calls.push c
    | .ok _ => pure ()
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let marks ← match (Dump.edgeLines text).foldlM Marks.add {} with
    | .ok m => pure m
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let some L := marks.layout | do IO.eprintln s!"{path}: no layout mark"; return none
  let some (_, os) := replayR calls #[] 0 {} #[] | do IO.eprintln s!"{path}: the calls do not replay"; return none
  let idx := outIndex os
  let cert ← match certOf calls os idx marks L with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  -- Each child's scale is computed as its tier computes it (`DesignClaims.tierMode`), so it is zero exactly at the
  -- first level (`DesignClaims.tierMode_scale`).
  let some (sh, position) := DesignClaims.dumpShape (path.fileStem.getD "")
    | do IO.eprintln s!"{path}: not a tracked circuit's name"; return none
  let ct := ((sh.children position).map (·.2)).getD 0
  unless cert.children.all fun ch => DesignClaims.modeOk sh ct ch.scale.mode do
    IO.eprintln s!"{path}: a child's scale is not computed as tier {ct} computes it"; return none
  -- A wrap states its child's digest (`DigestCert.wrap_states`) and a node of a tree of outputs its children's tree
  -- digest (`DigestCert.node_states`), exposed at statement positions 1 and 2 (`DigestCert.exposed`).
  let wrap? : Option Bool := match (sh.placeAt position).level, sh.claims with
    | .wrap, _ => some true
    | .node _, none => some false
    | _, _ => none
  let words := cert.children.map (·.words)
  let digest ← match wrap? with
    | none => pure ""
    | some wrap => do
      unless (digestOf calls os idx wrap words.length).any (·.ok calls os words) do
        IO.eprintln s!"{path}: its statement does not expose {if wrap then "its child's digest" else "its children's tree digest"}"
        return none
      pure (if wrap then ", exposing its child's digest" else ", exposing its children's tree digest")
  let ok := cert.check
  unless ok do
    IO.eprintln s!"{path}: claims and digests {if cert.accepts os then "accepted" else "rejected"}, \
      verifiers' statements {if cert.verifies os then "accepted" else "rejected"}"
  let per := (stmtClaims L (fun _ => 0) 0 : Claims ℕ)
  let edges := if cert.children.isEmpty then "no child" else
    s!"children with scales from {", ".intercalate (cert.children.map fun ch => modeName ch.scale.mode)}, \
      each making {per.dense.length} dense and {per.matrices.length} matrix claims among them, \
      their verifiers absorbing their words in {", ".intercalate (cert.children.map fun ch => toString ch.inst.blocks.length)} \
      blocks and reading them in {", ".intercalate (cert.children.map fun ch => toString ch.inst.shares.length)} \
      statement shares"
  IO.println s!"{path}: {if ok then "accepted" else "rejected"}: a statement of {L.len} words, the reduction takes \
    {cert.claims.dense.length} dense and {cert.claims.matrices.length} matrix claims, {edges}{digest}"
  return if ok then some L else none

/-- The tree a dump is of: its name up to its position. -/
def treeOf (path : System.FilePath) : String :=
  let name := path.fileName.getD ""
  let cut := fun (s sep : String) => (s.splitOn sep).headD s
  cut (cut (cut name "-first") "-node") "-circuit-"

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  let mut layouts : Std.HashMap String Layout := {}
  for a in args do
    match ← check a with
    | none => ok := false
    | some L =>
      let t := treeOf a
      match layouts[t]? with
      | some L' =>
        if L ≠ L' then
          IO.eprintln s!"{a}: a layout other than its tree's"
          ok := false
      | none => layouts := layouts.insert t L
  return if ok then 0 else 1
