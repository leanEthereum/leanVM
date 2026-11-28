module

public import NativeRustcVmX64.Whir.FoldRound.Call

/-!
# `fold_round` on x86-64: the state's and the push's environments, the frame's words

`stEnv`: the frame and the state's head (24 bytes at `pA`), well formed (`st_wf`), `stS` matching
it (`st_match`). `pushEnv m0 d c`: also the `α`s' slot `c` and the output (`push_wf`,
`push_match`). `FW d m0 L`: the frame's words `L`; kept by a block missing them (`FW.block`) and a
call (`FW.call`).
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn miss_of_wr0)
open NativeRustcVm (WordAt EWAt EWsAt)

@[expose] public section

/-- The frame and the state's head. -/
abbrev stEnv [Labels] (m0 d : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) : Env :=
  frameEnv m0 d 176 [(pA m0, 24)] vars ret

/-- The frame, the state's head, the `α`s' slot `c`, the output. -/
abbrev pushEnv [Labels] (m0 d : MachineData) (c : Nat) : Env :=
  frameEnv m0 d 176 [(pA m0, 24), (off (pA m0) (24 + 16 * c), 16), (oA m0, 40)]

/-- The frame's words `L`. -/
def FW (d : Mem 64) (m0 : MachineData) (L : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ L, WordAt d (off (fb m0) p.1) p.2

end

public section

theorem shl4 (c : Nat) : BitVec.ofNat 64 c <<< 4 = BitVec.ofNat 64 (16 * c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem neg24 : BitVec.ofInt 64 (-24) = -(24#64) := by decide

theorem slot_alias (p : BitVec 64) (c : Nat) :
    p + BitVec.ofNat 64 c <<< 4 = p + BitVec.ofNat 64 (24 + 16 * c) + BitVec.ofInt 64 (-24) := by
  rw [shl4, neg24, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 24),
    BitVec.add_assoc, ← BitVec.sub_eq_add_neg, show BitVec.ofNat 64 24 = 24#64 from rfl,
    BitVec.sub_self, BitVec.add_zero]

theorem apart_sub {a a' b : BitVec 64} {n n' m : Nat} (h : NativeRustcVm.Apart a n b m)
    (h1 : a.toNat ≤ a'.toNat) (h2 : a'.toNat + n' ≤ a.toNat + n) :
    NativeRustcVm.Apart a' n' b m := by
  unfold NativeRustcVm.Apart at h ⊢
  omega

/-! ## The frame's words -/

theorem FW.get {d : Mem 64} {m0 : MachineData} {L : List (Nat × UInt64)} (h : FW d m0 L)
    {o : Nat} {v : UInt64} (hp : (o, v) ∈ L) : WordAt d (off (fb m0) o) v :=
  h (o, v) hp

theorem FW.call {d d' : Mem 64} {m0 : MachineData} {L : List (Nat × UInt64)}
    (hk : ∀ {o : Nat} {v : UInt64}, o + 8 ≤ 176 → WordAt d (off (fb m0) o) v →
      WordAt d' (off (fb m0) o) v) (hle : ∀ p ∈ L, p.1 + 8 ≤ 176) (h : FW d m0 L) : FW d' m0 L :=
  fun p hp ↦ hk (hle p hp) (h p hp)

theorem FW.append {d : Mem 64} {m0 : MachineData} {L L' : List (Nat × UInt64)} (h : FW d m0 L)
    (h' : FW d m0 L') : FW d m0 (L ++ L') := fun p hp ↦ by
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem FW.sub {d : Mem 64} {m0 : MachineData} {L L' : List (Nat × UInt64)} (h : FW d m0 L)
    (hs : ∀ p ∈ L', p ∈ L) : FW d m0 L' := fun p hp ↦ h p (hs p hp)

theorem FW.block [Labels] {m0 st st' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} {L : List (Nat × UInt64)}
    (hwf : (frameEnv m0 st 176 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 176 rest vars ret) S st') (hin : Transcript.writesIn S = true)
    (hmiss : ∀ p ∈ L, miss S p.1 = true) (hle : ∀ p ∈ L, p.1 + 8 ≤ 176)
    (h : FW st.dmem m0 L) : FW st'.dmem m0 L :=
  fun p hp ↦ loc_keep hwf hm hin (by have := hle p hp; omega) (hmiss p hp) (h p hp)

theorem miss_of_missL {S : SState} {os : List Nat} (h : missL S os = true)
    {L : List (Nat × UInt64)} (hs : ∀ p ∈ L, p.1 ∈ os) : ∀ p ∈ L, miss S p.1 = true :=
  fun p hp ↦ missL_spec h (hs p hp)

theorem miss_of_wr8 {S : SState} (h : wr0 S 8 = true) {L : List (Nat × UInt64)}
    (hs : ∀ p ∈ L, 8 ≤ p.1) : ∀ p ∈ L, miss S p.1 = true :=
  fun p hp ↦ miss_of_wr0 h (hs p hp)

/-- An element from its limbs' words. -/
theorem ew_of (x : EW) {u v : BitVec 64} (hu : u = x.c0.toBitVec) (hv : v = x.c1.toBitVec) :
    (⟨UInt64.ofBitVec u, UInt64.ofBitVec v⟩ : EW) = x := by
  subst hu hv
  rfl

/-! ## The environments -/

variable [Labels] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

theorem geo (h : FoldRoundPre a s0 w m0) :
    (pA m0).toNat + stateBytes ≤ 2 ^ 64 ∧ (oA m0).toNat + 40 ≤ 2 ^ 64 ∧
      NativeRustcVm.Apart (pA m0) stateBytes (fb m0) (176 + 8) ∧
      NativeRustcVm.Apart (oA m0) 40 (fb m0) (176 + 8) ∧
      NativeRustcVm.Apart (oA m0) 40 (pA m0) stateBytes ∧ (fb m0).toNat + (176 + 8) ≤ 2 ^ 64 := by
  have cx := ctx h
  exact ⟨(pre_p h).2.1, (pre_o h).2.1,
    Transcript.apart_frame (pre_p h).2.2.2.2.1 cx.hN F_le,
    Transcript.apart_frame (pre_o h).2.2.2.2.1 cx.hN F_le, pre_op h, cx.fnw⟩

theorem st_wf (h : FoldRoundPre a s0 w m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (stEnv m0 d vars ret).WF := by
  obtain ⟨g1, -, g3, -, -, g6⟩ := geo h
  have hS : stateBytes = 61152 := rfl
  refine Transcript.frame_wf ⟨Mapped.keeps (Transcript.frame_mapped (ctx h).stack F_le) hk, g6⟩
    (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps (fun i hi ↦ (pre_p h).1 i (by omega)) hk,
      show (pA m0).toNat + 24 ≤ 2 ^ 64 by omega⟩
  · exact Transcript.Apart.symm' (apart_sub (a' := pA m0) (n' := 24) g3 le_rfl (by omega))

theorem st_match {d : MachineData} (hw : Fr m0 d) (h14 : reg d .r14 = pA m0)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : Match (stEnv m0 d vars ret) stS d :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hw.fr.rsp_eval, Transcript.known_ptr rfl h14, trivial⟩
    trivial trivial trivial

theorem push_wf (h : FoldRoundPre a s0 w m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    {c : Nat} (hc : c < 30) : (pushEnv m0 d c).WF := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo h
  have hS : stateBytes = 61152 := rfl
  have hsl : (off (pA m0) (24 + 16 * c)).toNat = (pA m0).toNat + (24 + 16 * c) :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  unfold NativeRustcVm.Apart at g3 g4 g5
  refine Transcript.frame_wf ⟨Mapped.keeps (Transcript.frame_mapped (ctx h).stack F_le) hk, g6⟩
    (fun x hx ↦ ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨Mapped.keeps (fun i hi ↦ (pre_p h).1 i (by omega)) hk,
        show (pA m0).toNat + 24 ≤ 2 ^ 64 by omega⟩
    · refine ⟨Mapped.keeps (fun i hi ↦ ?_) hk,
        show (off (pA m0) (24 + 16 * c)).toNat + 16 ≤ 2 ^ 64 by omega⟩
      have := (pre_p h).1 (24 + 16 * c + i) (by omega)
      rwa [← NativeRustcVm.addr_add_add] at this
    · exact ⟨Mapped.keeps (pre_o h).1 hk, g2⟩
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.pairwise_singleton _ _)))
    all_goals
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    · rcases he with rfl | rfl | rfl
      · show (fb m0).toNat + (176 + 8) ≤ (pA m0).toNat ∨ (pA m0).toNat + 24 ≤ (fb m0).toNat
        omega
      · show (fb m0).toNat + (176 + 8) ≤ (off (pA m0) (24 + 16 * c)).toNat ∨
          (off (pA m0) (24 + 16 * c)).toNat + 16 ≤ (fb m0).toNat
        omega
      · show (fb m0).toNat + (176 + 8) ≤ (oA m0).toNat ∨ (oA m0).toNat + 40 ≤ (fb m0).toNat
        omega
    · rcases he with rfl | rfl
      · show (pA m0).toNat + 24 ≤ (off (pA m0) (24 + 16 * c)).toNat ∨ _
        omega
      · show (pA m0).toNat + 24 ≤ (oA m0).toNat ∨ (oA m0).toNat + 40 ≤ (pA m0).toNat
        omega
    · subst he
      show (off (pA m0) (24 + 16 * c)).toNat + 16 ≤ (oA m0).toNat ∨
        (oA m0).toNat + 40 ≤ (off (pA m0) (24 + 16 * c)).toNat
      omega

theorem push_match {d : MachineData} (hw : Fr m0 d) {c : Nat} (hbx : reg d .rbx = oA m0)
    (h14 : reg d .r14 = pA m0) (hax : reg d .rax = BitVec.ofNat 64 c) :
    Match (pushEnv m0 d c) pushS d := by
  refine match_ofMachine ⟨rfl, rfl, rfl, rfl, trivial⟩
    ⟨hw.fr.rsp_eval, Transcript.known_ptr rfl hbx, trivial⟩ trivial trivial ⟨?_, ?_, trivial⟩
  · show reg d .r14 = (Sym.ptr 1 0).eval (pushEnv m0 d c)
    rw [Transcript.eval_ptr rfl]
    exact h14
  · show BinOp.apply .add .W64 (reg d .r14)
      ((Sym.bin .shl .W64 (.reg .rax) (.lit 4)).eval (pushEnv m0 d c)) = _
    rw [NativeRustcVmX64.Arrays.eval_shl_lit _ (by omega)]
    simp only [BinOp.apply, low_W64, ext_W64, Env.base_ofMachine_eq]
    rw [h14, show (Sym.reg .rax).eval (pushEnv m0 d c) = BitVec.ofNat 64 c from hax]
    exact slot_alias _ c

end

end NativeRustcVmX64.Whir.FoldRound
