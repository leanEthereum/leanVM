import Whir.PCSBCSNativePacketCodec
import Whir.DuplexCompression

/-! Executable production logN=15/rate=3 native packet and codec smoke. A
syntactic prover history is admitted by the actual native ValidPacket predicate,
then its real completion is decoded from BLAKE2s duplex output blocks. This is
not an honest arithmetic opening fixture or a successful all-round reader. -/
set_option autoImplicit false
namespace Whir.PCSBCSNativePacketCodecSmoke
open Concrete Protocol CausalProbability CausalGame FiatShamirGame DuplexModeGame
open PCSBCSRounds PCSBCSChallengeOracle PCSBCSNativePacketBridge PCSBCSNativePacketCodec
open DuplexFraming DuplexRefinement

private def profile : ParameterBounds.Profile := (⟨0,by decide⟩,⟨2,by decide⟩)
private def frames : List Frame := [.absorb 0 [1,2,3,4,5]]
private def ctx : RawWHIRKeys.Context :=
  ⟨.stack, DuplexCompression.parameterIV, zeroDigest,
    fun _ => some profile, fun _ => frames.length, 0⟩

/-- Concrete prover strings of the production schedule's exact scalar widths.
Their syntactic admission does not assert arithmetic or Merkle acceptance. -/
private def pending (n : Fin (WHIRHistory.depth (ParameterBounds.config profile))) : WHIRHistory.Pending :=
  let c := ParameterBounds.config profile
  let qs := WHIRHistory.schedule c
  if n.val = 0 then WHIRHistoryKey.initialPending else
    let previous := qs[n.val-1]'(lt_of_le_of_lt (Nat.sub_le n.val 1) n.isLt)
    ⟨List.replicate (WHIRHistory.replyScalarCount previous) E.zero,
      match qs[n.val]'n.isLt with | .query _ => some (0,E.zero) | _ => none⟩

private def data : RawWHIRKeys.PacketData :=
  ⟨zeroDigest, profile, (List.ofFn pending).reverse, frames⟩
private def cap : Nat := pathCost (RawWHIRKeys.coordinate ctx data 0)

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Sharing the evaluated history is an executable optimization of the same
literal coordinate. It does not replace real primitive output by test data. -/
private def outputBytes (packet : RawWHIRKeys.Packet ctx cap) : Array (Array Byte) :=
  let h := (RawWHIRKeys.coordinate ctx packet.val 0).history
  let historyBytes := Array.ofFn (evalHistory DuplexCompression.compress ctx.iv h)
  let cv : Digest32 := fun i => historyBytes[i.val]!
  Array.ofFn fun b : Fin (RawWHIRKeys.blocks ctx packet.val) =>
    Array.ofFn (evalTerminal DuplexCompression.compress cv (.output b.val))

private theorem outputBytes_eq (packet : RawWHIRKeys.Packet ctx cap)
    (b : Fin (RawWHIRKeys.blocks ctx packet.val)) (i : Fin 32) :
    ((outputBytes packet)[b.val]!)[i.val]! =
      evalCoordinate DuplexCompression.compress ctx.iv
        (RawWHIRKeys.coordinate ctx packet.val b.val) i := by
  simp [outputBytes, evalCoordinate, evalTerminal, RawWHIRKeys.coordinate]

def smoke : IO Unit := do
  IO.println "native/groupcodec: checking production logN=15/rate=3"
  let c := ParameterBounds.config profile
  check (c.logN == 15 && c.rates[0]! == 3) "production geometry changed"
  if valid : RawWHIRKeys.ValidPacket ctx cap data then
    let final : RawWHIRKeys.Packet ctx cap := ⟨data,valid⟩
    let packets := RawOracleCoupling.Concrete.completion ctx cap final
    check (packets.length == (WHIRHistory.schedule c).length)
      "native completion did not cover the production schedule"
    check ((completionPackets ctx rfl cap final).length == packets.length)
      "canonical completion lost a native packet"
    IO.println s!"native/groupcodec: admitted {packets.length} production completion packets"
    let mut queries := 0
    let mut coordinates := 0
    for packet in packets do
      let pc := ParameterBounds.config packet.val.profile
      let q := query ctx cap packet
      let actual := outputBytes packet
      let raw : RawOracleCoupling.Concrete.GroupAnswer ctx cap (.inl packet) :=
        fun b i => (actual[b.val]!)[i.val]!
      let full := nativeFullBlocksEquiv ctx rfl cap packet raw
      let native := WHIRRawReplay.decodePacket ctx rfl cap packet raw
      let pcs := grouped q full
      check (List.ofFn (rawVector q native) == List.ofFn (rawVector q pcs))
        "literal native/grouped scheduled codec mismatch"
      check (List.ofFn ((nativeFullBlocksEquiv ctx rfl cap packet).symm full) == List.ofFn raw)
        "native full-block index cast dropped output bytes"
      check ((enteredPacket ctx rfl cap packet).1.val.frames == frames)
        "literal caller-entry frames changed"
      check (List.ofFn (vectorBytes (rawWidth q) (rawVector q pcs)) ==
        List.ofFn (fun i : Fin (rawWidth q*24) =>
          full ⟨i.val/32, by
            change i.val/32 < blocks (rawWidth q)
            have h := packet_length (rawWidth q)
            have := i.isLt
            omega⟩
            ⟨i.val%32,Nat.mod_lt _ (by decide)⟩)) "contiguous payload bytes differ"
      match hq : q with
      | .initial =>
        check (RawWHIRKeys.blocks ctx packet.val == 6) "initial is not six full blocks"
      | .query i =>
        let native : Raw (.query i) := hq ▸ native
        let pcs : Raw (.query i) := hq ▸ pcs
        check ((List.ofFn pcs.1).any (fun e => e.toNat / 2^128 != 0))
          "real full query scalar did not exercise its upper limb"
        check (Array.ofFn native.1 == Array.ofFn pcs.1 && native.2 == pcs.2)
          "full query high bits or lambda changed"
        check (deriveQueries (remaining pc i.val + pc.rates[i.val]!) pc.queries[i.val]!
          (Array.ofFn native.1) == deriveQueries (remaining pc i.val + pc.rates[i.val]!)
            pc.queries[i.val]! (Array.ofFn pcs.1)) "native query projection differs"
        queries := queries+1
      | _ => pure ()
      coordinates := coordinates+1
    check (queries > 0) "production query geometry was not exercised"
    IO.println s!"native/groupcodec PASS: production logN=15/rate=3; initial six full blocks; {coordinates} native completion packets, {queries} full-query/high-bit/lambda geometries"
  else
    throw (IO.userError "actual native production history failed admission")
end Whir.PCSBCSNativePacketCodecSmoke

def main : IO Unit := Whir.PCSBCSNativePacketCodecSmoke.smoke
