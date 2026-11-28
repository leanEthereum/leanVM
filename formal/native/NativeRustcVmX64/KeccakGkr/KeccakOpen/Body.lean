module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Known
public import NativeRustcVmX64.Sumcheck.Ctx

/-!
# `keccak_open`: the frame before the fold

The body invariant tracks the saved registers and exact caller-visible write footprint.
Its read regions, including the incoming stack arguments, round constants and raw GOT bytes, are preserved.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (off off_zero off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr DecArea tstateBytes TStateAt)

@[expose] public section

structure Body [Labels] (m0 : MachineData) (o : Nat) (d : MachineData) : Prop where
  fr : Frame m0 2208 slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0)

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 d d' : MachineData}

theorem context (h : PreOk a s c m0) :
    Sumcheck.Ctx m0 (tA m0) a keccakOpenStack 2208 := by
  refine ⟨h.st, h.rc, ⟨?_, ?_, ?_⟩, h.ts.footprint, by rw [stack_eq]; decide⟩
  · exact Areas.apart_stack h.areas (.tail _ (.head _))
  · exact Apart.symm' (Areas.stack_read h.areas (.head _))
  · exact Areas.apart_read h.areas (.tail _ (.head _)) (.tail _ (.tail _ (.tail _ (.head _))))

theorem slot_out (h : PreOk a s c m0) : OutOk m0 (tA m0) a (slA m0) 96 keccakOpenStack := by
  have hs : ewsRegion (slA m0) LeanVM.Protocol.Verifier.qkeccakSlotBits ∈ wsOf m0 :=
    .tail _ (.tail _ (.head _))
  have ho := Areas.ok h.areas (List.mem_append_left _ hs)
  have ha := Areas.apart_read h.areas hs (.head _)
  have hst := Areas.apart_stack h.areas hs
  have hrc := Areas.apart_read h.areas hs (.tail _ (.tail _ (.tail _ (.head _))))
  dsimp only [ewsRegion] at ho ha hst hrc
  rw [NativeVm.Math.Keccak.qkeccakSlotBits_eq] at ho ha hst hrc
  refine ⟨ho.1, ho.2, ?_, ha, hst, hrc⟩
  have ht := (nums h).ts
  change (slA m0).toNat + 96 ≤ (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ (slA m0).toNat
  omega

theorem read_kept (h : PreOk a s c m0)
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0)) {r : Region}
    (hr : r ∈ rsOf a c m0) {q : BitVec 64} (hq : r.Holds q) :
    d.dmem.get? q = m0.dmem.get? q := by
  have hrn := (Areas.ok h.areas (List.mem_append_right _ hr)).2
  refine hs q fun ⟨w, hw, hwq⟩ ↦ ?_
  rcases List.mem_cons.mp hw with rfl | hw
  · exact NativeRustcVm.Transcript.not_inRange_of_apart
      (Areas.stack_read h.areas hr) (noWrap_stackBelow h.st) hrn
      (inRange_mono hwq (show keccakOpenStack ≤ keccakOpenStack + 8 by omega)) hq
  · exact NativeRustcVm.Transcript.not_inRange_of_apart
      (h.areas.2.2 w (List.mem_cons_of_mem _ hw) r hr)
      (Areas.ok h.areas (List.mem_append_left _ hw)).2 hrn hwq hq

theorem Body.at (h : PreOk a s c m0) (hb : Body m0 0 d) : Sumcheck.At m0 2208 d := by
  refine Sumcheck.At.of_frame hb.fr fun i hi ↦ read_kept h hb.same
    (.tail _ (.tail _ (.tail _ (.head _)))) ?_
  change NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i)
  exact NativeRustcVm.Transcript.inRange_off_self hi (by have := (nums h).c; omega)

theorem body_match (h : PreOk a s c m0) (hb : Body m0 8 d) {ret : BitVec 64} :
    Match (E m0 d (fun _ ↦ 0) ret) (pS []) d := by
  apply Match.withKnownBytes
  · refine match_ofMachine ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨arg_alias 0, arg_alias 1, arg_alias 2, arg_alias 3, arg_alias 4, arg_alias 5, ?_,
        by simp [Sym.eval, RF, Env.base, gotAddr], trivial⟩
    show (E m0 d (fun _ ↦ 0) ret).load 3 32 8 = (E m0 d (fun _ ↦ 0) ret).base 1 + BitVec.ofInt 64 0
    rw [show (32 : Nat) = 8 * 4 from rfl, load_arg h hb.same (by decide), ofInt0, BitVec.add_zero]
    rfl
  · intro i hi
    simp only [Nat.zero_add]
    change d.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
      some (byteOf (Labels.label "memcpy").toBitVec i)
    exact got_byte h hb.same hi

theorem touch_frame_out (h : PreOk a s c m0) {q : BitVec 64} {W : Nat → Prop}
    (hW : ∀ j, W j → j < 2208) (hq : NativeRustcVm.Transcript.Touch (fbA m0) 2216 W q) :
    Out m0 q := by
  obtain ⟨j, _, hj, rfl⟩ := hq
  refine ⟨_, List.mem_cons_self, (context h).inRange_frame ?_⟩
  exact NativeRustcVm.Transcript.inRange_off_self (hW j hj)
    (by have := frame_noWrap h.st (F := 2208) (by rw [stack_eq]; decide)
        unfold NativeRustcVm.NoWrap at this; omega)

theorem body_block {o o' : Nat} (h : PreOk a s c m0) (hb : Body m0 o d)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (E m0 d vars ret) S d') (hmid : MidOk 2208 o' slots S = true)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 2208) : Body m0 o' d' := by
  have hwf := wf_fold h hb.fr.kept (vars := vars) (ret := ret)
  have hs := sameOutside_touch hwf hm (r := 0) (b := fbA m0) (N := 2216)
    (lo := 0) (hi := 2208) rfl (by decide) (fun w hw' ↦ by
      have := hw w hw'; exact ⟨this.1, by omega⟩)
  exact ⟨hb.fr.of_block hwf hm hmid slots_le', fun q hq ↦
    (hs q fun ht ↦ hq (touch_frame_out h (fun _ hj ↦ hj.2) ht)).trans (hb.same q hq)⟩

theorem body_unchanged {o o' : Nat} (h : PreOk a s c m0) (hb : Body m0 o d)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (E m0 d vars ret) S d') (hmid : MidOk 2208 o' slots S = true)
    (hw : S.mem = []) : Body m0 o' d' :=
  body_block h hb hm hmid (by rw [hw]; simp)

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
