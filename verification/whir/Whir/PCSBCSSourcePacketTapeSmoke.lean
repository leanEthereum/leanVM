import Whir.PCSBCSSourcePacketTape

/-! Executable TOY functional fixture, not a production profile measurement or
an FS endpoint. Packets have a fixed literal toy Pending-history identifier;
the full block table is assigned before queries. Reading a child does not read
or disclose its parents. The actual grouped byte law and prefix/tape functions
are exercised, while source admission/caller/root provenance remain the explicit
SourcePacket obligations in the proof module (not asserted by this toy). -/
set_option autoImplicit false
namespace Whir.PCSBCSSourcePacketTapeSmoke
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame PCSBCSChallengeOracle PCSBCSSourcePacketTape

def toy : Config := ⟨3, #[1,1], #[2,2], #[16,8], #[0,1]⟩
def scalar (n : Nat) : E := ⟨UInt64.ofNat n,UInt64.ofNat (n+100),UInt64.ofNat (n+200)⟩

/-- A reverse-chronological history identifier, distinct for every packet. -/
def messages (q : Coordinate toy) : List Nat := (List.range (position q + 1)).reverse

def raw (q : Coordinate toy) : Raw q :=
  (rawVector q).symm (fun j => scalar (1000 * (position q + 1) + j.val))

/-- Includes every full 32-byte block, with nonzero unused bytes. -/
def full (q : Coordinate toy) : Fin (blocks (rawWidth q)) → Digest32 :=
  (packetEquiv (rawWidth q)).symm (rawVector q (raw q), fun i =>
    ⟨(197+i.val)%256, Nat.mod_lt _ (by decide)⟩)

abbrev FullTable := (q : Coordinate toy) → Fin (blocks (rawWidth q)) → Digest32

def assigned : FullTable := full

/-- Only the currently selected whole fiber changes, including all unused bytes. -/
def changed (current : Coordinate toy) : FullTable :=
  Function.update assigned current (fun block byte =>
    ⟨(block.val * 37 + byte.val + 211)%256, Nat.mod_lt _ (by decide)⟩)

def past (current : Coordinate toy) (table : FullTable) : RawPrefix current :=
  fun q _ => grouped q (table q)

def restored (current : Coordinate toy) (table : FullTable) : Tape toy :=
  tapeOfPrefix (projectedPrefix (past current table))

def payload (table : FullTable) (q : Coordinate toy) : List Byte :=
  (List.ofFn (fun b : Fin (blocks (rawWidth q)) => List.ofFn (table q b))).flatten

structure Disclosure where
  coord : Coordinate toy
  history : List Nat
  bytes : List Byte

/-- Operational read loop. Each requested full packet is disclosed in exactly
that order, with repeats preserved. No query is inserted for an ancestor. -/
def query (table : FullTable) (order : List (Coordinate toy)) : List Disclosure :=
  order.map (fun q => ⟨q,messages q,payload table q⟩)

/-- This functional query property holds for every order, not just the smoke's
child-before-parent ordering. -/
theorem query_at (table : FullTable) (order : List (Coordinate toy)) (n : Fin order.length) :
    (query table order)[n.val]'(by simp [query]) =
      ⟨order[n.val],messages order[n.val],payload table order[n.val]⟩ := by
  simp [query]

/-- Universal current-whole-packet independence of the toy strict raw prefix. -/
theorem past_update (current : Coordinate toy) : past current (changed current) =
    past current assigned := by
  funext q h
  have different : q ≠ current := by
    intro same
    subst q
    exact Nat.lt_irrefl _ h
  simp [past, changed, Function.update_of_ne different]

/-- Earlier disclosure contains exactly the bytes used by the reconstruction. -/
theorem earlier_bytes (current q : Coordinate toy) (h : position q < position current)
    (j : Fin (rawWidth q * 24)) :
    vectorBytes (rawWidth q) (rawVector q (past current assigned q h)) j =
      assigned q ⟨j.val/32, by
        have bound := packet_length (rawWidth q)
        have hj := j.isLt
        omega⟩ ⟨j.val%32, Nat.mod_lt _ (by decide)⟩ :=
  grouped_payload_bytes q _ j

def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def smoke : IO Unit := do
  let order := schedule toy
  let current : Coordinate toy := .tail ⟨0,by decide⟩
  let strict := order.filter (fun q => position q < position current)
  let childFirst := current :: strict.reverse ++ [current,.initial]
  let disclosures := query assigned childFirst
  check (disclosures.length == childFirst.length) "ancestor-warming query inserted"
  check (disclosures.head?.map (fun d => d.coord) == some current) "child was not queried first"
  check (disclosures.all (fun d => d.history == messages d.coord &&
    d.bytes == payload assigned d.coord)) "disclosed packet differed from assigned global table"
  for d in disclosures do
    if h : position d.coord < position current then
      let reconstructed := stackSampleScalars d.coord (past current assigned d.coord h)
      check (scalarBytes reconstructed == d.bytes.take (rawWidth d.coord * 24))
        "earlier disclosure payload differs from reconstructed strict prefix"
  let before := restored current assigned
  let after := restored current (changed current)
  for q in order do
    check (sampleScalars q (get q before) == sampleScalars q (get q after))
      "whole current replacement changed reconstructed tape"
    if h : position q < position current then
      check (sampleScalars q (get q before) == sampleScalars q (project q (raw q)))
        "strict earlier tape value differs from predecessor packet projection"
      check (stackSampleScalars q (past current assigned q h) == stackSampleScalars q (raw q))
        "strict earlier Raw value differs from earlier disclosed packet"
    else
      check (sampleScalars q (get q before) == sampleScalars q (inertSample q))
        "future/current coordinate was not inert"
  check (stackSampleScalars current (grouped current (assigned current)) !=
    stackSampleScalars current (grouped current ((changed current) current)))
    "full current packet replacement was vacuous"
  check (payload assigned current != payload (changed current) current)
    "full current bytes were not replaced"
  let ringBefore := ringOfPrefix (past current assigned)
  let ringAfter := ringOfPrefix (past current (changed current))
  check (ringBefore.1 == ringAfter.1 && List.ofFn ringBefore.2 == List.ofFn ringAfter.2)
    "whole current replacement changed reconstructed ring prefix"
  let parentFirst := query assigned order
  for d in parentFirst do
    check ((disclosures.find? (fun item => item.coord == d.coord)).map (fun item => item.bytes) ==
      some d.bytes) "query order changed a memoized disclosure"
  IO.println s!"TOY packet tape PASS: {order.length} coordinates; child-before-parent with repeats, no warming, full current block replacement, strict disclosed byte/Raw/projected tape match, inert suffix, ring prefix, order independence"

#print axioms query_at
#print axioms past_update
#print axioms earlier_bytes
end Whir.PCSBCSSourcePacketTapeSmoke

def main : IO Unit := Whir.PCSBCSSourcePacketTapeSmoke.smoke
