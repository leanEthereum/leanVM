module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldBase

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps DecArea)

public section

@[expose] def storeRest (m0 : MachineData) (n : Nat) : List (BitVec 64 × Nat) :=
  [(off (rwA m0) (16 * n), 16), (argA m0, 48)]

@[expose] def storeEnv [Labels] (m0 d : MachineData) (n : Nat) : Env :=
  frameEnv m0 d 2208 (storeRest m0 n) (fun _ ↦ 0) 0

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 d : MachineData}

theorem row_off (h : PreOk a s c m0) {n : Nat} (hn : n < 4096) :
    (off (rwA m0) (16 * n)).toNat = (rwA m0).toNat + 16 * n := by
  have := (nums h).w
  exact toNat_off (by omega)

theorem store_wf (h : PreOk a s c m0) (hk : Kept m0.dmem d.dmem) {n : Nat}
    (hn : n < 4096) : (storeEnv m0 d n).WF := by
  have nh := nums h
  have := nh.r1; have := nh.r2; have := nh.w; have := nh.sw; have := nh.warg
  have hf : (stackBelow m0 2208).toNat = (rspOf m0).toNat - 2208 := fbA_toNat h
  have hg := argA_toNat h
  have hr := row_off h hn
  have mw : (⟨rwA m0, NativeRustcVm.KeccakGkr.rowsBytes⟩ : Region) ∈ wsOf m0 ++ rsOf a c m0 :=
    List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _))))
  have mg : argsRegion m0 6 ∈ wsOf m0 ++ rsOf a c m0 :=
    List.mem_append_right _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  refine frame_wf ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq]; decide)) hk,
    frame_noWrap h.st (by rw [stack_eq]; decide)⟩ (fun x hx ↦ ?_) ?_
  · simp only [storeRest, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨Mapped.keeps (mapped_off (Areas.ok h.areas mw).1 (by change 16 * n + 16 ≤ 65536; omega)) hk,
        by change (off (rwA m0) (16 * n)).toNat + 16 ≤ 2 ^ 64; omega⟩
    · exact ⟨Mapped.keeps (Areas.ok h.areas mg).1 hk,
        by change (argA m0).toNat + 48 ≤ 2 ^ 64; omega⟩
  · simp only [storeRest]
    refine List.pairwise_cons.mpr ⟨fun x hx ↦ ?_, List.pairwise_pair.mpr ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> unfold NativeRustcVm.Apart <;> dsimp only <;> omega
    · unfold NativeRustcVm.Apart
      dsimp only
      omega

theorem store_safe (h : PreOk a s c m0) {n : Nat} (hn : n < 4096) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (rwA m0) (16 * n)) 16 q) : Safe m0 q := by
  have hr := row_off h hn
  have := (nums h).w
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hr] at hq
  exact .inr (.inr ⟨by omega, by omega⟩)

theorem store_match {cx : Cx} {n so : Nat} {dr ib : Reg64}
    (hm : Mid cx m0 8 d)
    (ha : reg d dr + reg d ib = off (rwA m0) (16 * n) + BitVec.ofInt 64 (so : Int)) :
    Match (storeEnv m0 d n) (stS dr ib so) d := by
  have harg (i : Nat) : fbA m0 + BitVec.ofInt 64 ((2216 + 8 * i : Nat) : Int) =
      argA m0 + BitVec.ofInt 64 ((8 * i : Nat) : Int) :=
    arg_alias (m0 := m0) (st := d) (vars := fun _ ↦ 0) (ret := 0) i
  refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hm.fr.rsp_eval, trivial⟩ trivial trivial ?_
  change (fbA m0 + 2216#64 = argA m0 + 0#64) ∧
    (fbA m0 + 2224#64 = argA m0 + 8#64) ∧
    (fbA m0 + 2232#64 = argA m0 + 16#64) ∧
    (fbA m0 + 2240#64 = argA m0 + 24#64) ∧
    (fbA m0 + 2248#64 = argA m0 + 32#64) ∧
    (fbA m0 + 2256#64 = argA m0 + 40#64) ∧
    (reg d dr + reg d ib = off (rwA m0) (16 * n) + BitVec.ofInt 64 (so : Int)) ∧ True
  exact ⟨harg 0, harg 1, harg 2, harg 3, harg 4, harg 5, ha, trivial⟩

theorem store_match5 (h : PreOk a s c m0) {cx : Cx} {n : Nat}
    (hm : Mid cx m0 8 d) (hib : reg d .rbx = BitVec.ofNat 64 (16 * n)) :
    Match (storeEnv m0 d n) st5S d := by
  have harg (i : Nat) : fbA m0 + BitVec.ofInt 64 ((2216 + 8 * i : Nat) : Int) =
      argA m0 + BitVec.ofInt 64 ((8 * i : Nat) : Int) :=
    arg_alias (m0 := m0) (st := d) (vars := fun _ ↦ 0) (ret := 0) i
  have hl : (storeEnv m0 d n).load 2 40 8 = rwA m0 := by
    have hw := arg_word h hm.same (i := 5) (by decide)
    exact (load_of_wordAt hw).trans (UInt64.toBitVec_ofBitVec _)
  refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hm.fr.rsp_eval, trivial⟩ trivial trivial ?_
  change (fbA m0 + 2216#64 = argA m0 + 0#64) ∧
    (fbA m0 + 2224#64 = argA m0 + 8#64) ∧
    (fbA m0 + 2232#64 = argA m0 + 16#64) ∧
    (fbA m0 + 2240#64 = argA m0 + 24#64) ∧
    (fbA m0 + 2248#64 = argA m0 + 32#64) ∧
    (fbA m0 + 2256#64 = argA m0 + 40#64) ∧
    ((storeEnv m0 d n).load 2 40 8 + reg d .rbx = off (rwA m0) (16 * n) + 0#64) ∧ True
  refine ⟨harg 0, harg 1, harg 2, harg 3, harg 4, harg 5, ?_, trivial⟩
  rw [hl, hib, BitVec.add_zero]
