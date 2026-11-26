/-
  Rv64mc.Proof.Hash.KeccakFT

  `verifier::hash::keccak_f(state)` is total (`KeccakFSafeT`): from a state of `25` lanes at `a0`, 8-byte aligned,
  in the heap window up to the heap's end or in the stack window, apart from the stack below the stack pointer, it
  returns, writing at most the state (`Spec.Hash.KeccakF.Out`). It does not state the lanes it leaves, which is
  `Spec.Hash.KeccakF`'s partial contract, not yet proved; no caller's safety reads them.

  It copies the round constants out of the static data with `memcpy`, clears a stack array with `memset` each
  round, and reads the `π` and `ρ` tables in place. The three tables are an environment fact, `DataRef.InData env
  (tables L)`: with `env.Static` it puts each table in a window, aligned and below `NEXT` (`table_range`, from
  `data_static`: a word of `env.data` lies in `[staticLo, staticHi)`), and the `π` table's entries below `25`
  (`pi_lt`), which bounds the `π` loop's stores.

  The body is cut into parts at program counters (`p1_ok` to `p8_ok`, `mid_ok`, `mid2_ok`), each stepped by
  `rv_symT` from a state that keeps only `Inv`: the stack pointer, the state's pointer in `s0`, and `MemInv` (the
  frame writing at most the state, the static data, the code, and the saved registers' slots), with the round
  counter (`Head`: in `a3` at the round loop's head; `Body`: in its stack slot inside a round). The round loop is
  `Total.loop` with the rounds left (`loop_ok`), the `π` loop with the lanes left (`inner_ok`).

  ## Main definitions

  * `KeccakPreT`, `KeccakFSafeT`, `tables`

  ## Main results

  * `data_static`, `table_range`
  * `total`
-/

import Rv64mc.Spec.Hash.KeccakF
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.Hash.KeccakF

namespace Rv64mc.Proof.Hash.KeccakFT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Spec.Hash.KeccakF
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.MemsetT (MemsetSafeT)
open Rv64mc.Gen.Verifier.Hash.KeccakF

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

/-- **A word of `env.data` lies in the static data's range**: one outside it could be changed keeping
    `env.Static`, against `static_data`. -/
theorem data_static {m : MachineState} (hs : env.Static m) {q : Word × Word} (hq : q ∈ env.data) :
    env.staticLo.toNat ≤ q.1.toNat ∧ q.1.toNat < env.staticHi.toNat := by
  by_contra h
  have hs' := Tactic.static_store (a := q.1) (v := q.2 + 1) hs (by omega)
  have := env.static_data _ hs' q hq
  rw [MachineState.getMem_setMem_eq] at this
  exact absurd this (by bv_omega)

/-- A constant table of `n` words in `env.data`: in a window, 8-byte aligned, and below `NEXT`. -/
theorem table_range {top : Word} {m : MachineState} (hW : Windows env top m) (hs : env.Static m) {d : DataRef}
    {ws : List Word} (hd : ∀ k (hk : k < ws.length), (d.hi + d.lo + BitVec.ofNat 64 (8 * k), ws[k]) ∈ env.data)
    (hn : 0 < ws.length) (hn' : ws.length ≤ 64) :
    (d.hi + d.lo).toNat % 8 = 0 ∧ inWindow (d.hi + d.lo) (8 * ws.length) = true ∧
      (d.hi + d.lo).toNat + 8 * ws.length ≤ env.nextAddr.toNat := by
  have h0 := hd 0 hn
  have h1 := hd (ws.length - 1) (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at h0
  have w0 := hW.data_ok _ h0
  have w1 := hW.data_ok _ h1
  have s1 := data_static hs h1
  simp only [inWindow_iff] at w0 w1 ⊢
  have e : (d.hi + d.lo + BitVec.ofNat 64 (8 * (ws.length - 1))).toNat = (d.hi + d.lo).toNat + 8 * (ws.length - 1) :=
    toNat_add_ofNat (by omega)
  simp only [e] at w1 s1
  have := env.layout
  have := hW.nextAddr_aligned
  refine ⟨w0.2, by omega, by omega⟩

/-- `keccak_f`'s total precondition: the state's `200` bytes 8-byte aligned, in the heap window up to the heap's end
    or the stack window, apart from the stack below the stack pointer. -/
def KeccakPreT (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  (regs .x10).toNat % 8 = 0 ∧
    ((0x10000000 ≤ (regs .x10).toNat ∧ (regs .x10).toNat + stateBytes ≤ env.heapEnd.toNat) ∨
      (env.stackLimit.toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + stateBytes ≤ 0xc0000000)) ∧
    OffStack env (regs .x2) (regs .x10) stateBytes

/-- **The total contract of `keccak_f`**: it returns, writing at most the state. It does not say what it writes. -/
def KeccakFSafeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (KeccakPreT env) (fun _ _ _ _ => True) Out

/-- The round constants, the `π` table and the `ρ` table, at their data references. -/
abbrev tables (L : Link) : List (DataRef × List Word) :=
  [(L.d_c192_f8e6964a, d_c192_f8e6964a_words), (L.d_c200_f4afdee4, d_c200_f4afdee4_words),
    (L.d_c100_179d68cc, d_c100_179d68cc_words)]

/-- The three tables' ranges, as `table_range` gives them. -/
theorem tables_ok (hdata : DataRef.InData env (tables L)) {top : Word} {m : MachineState} (hW : Windows env top m)
    (hs : env.Static m) :
    ((L.d_c192_f8e6964a.hi + L.d_c192_f8e6964a.lo).toNat % 8 = 0 ∧
      inWindow (L.d_c192_f8e6964a.hi + L.d_c192_f8e6964a.lo) 192 = true ∧
      (L.d_c192_f8e6964a.hi + L.d_c192_f8e6964a.lo).toNat + 192 ≤ env.nextAddr.toNat) ∧
    ((L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo).toNat % 8 = 0 ∧
      inWindow (L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo) 200 = true ∧
      (L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo).toNat + 200 ≤ env.nextAddr.toNat) ∧
    ((L.d_c100_179d68cc.hi + L.d_c100_179d68cc.lo).toNat % 8 = 0 ∧
      inWindow (L.d_c100_179d68cc.hi + L.d_c100_179d68cc.lo) 104 = true ∧
      (L.d_c100_179d68cc.hi + L.d_c100_179d68cc.lo).toNat + 104 ≤ env.nextAddr.toNat) :=
  ⟨table_range (ws := d_c192_f8e6964a_words) hW hs
      (hdata (L.d_c192_f8e6964a, d_c192_f8e6964a_words) (List.mem_cons_self ..)) (by decide) (by decide),
    table_range (ws := d_c200_f4afdee4_words) hW hs (hdata (L.d_c200_f4afdee4, d_c200_f4afdee4_words)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (by decide) (by decide),
    table_range (ws := d_c100_179d68cc_words) hW hs (hdata (L.d_c100_179d68cc, d_c100_179d68cc_words)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (by decide) (by decide)⟩

/-- The memory after the prologue's saves of the return address and the callee-saved registers. -/
def saves (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((((((m.setMem (top + 0xfffffffffffffff8#64) ret).setMem (top + 0xfffffffffffffff0#64) (regs .x8)).setMem
    (top + 0xffffffffffffffe8#64) (regs .x9)).setMem (top + 0xffffffffffffffe0#64) (regs .x18)).setMem
    (top + 0xffffffffffffffd8#64) (regs .x19)).setMem (top + 0xffffffffffffffd0#64) (regs .x20)).setMem
    (top + 0xffffffffffffffc8#64) (regs .x21)).setMem (top + 0xffffffffffffffc0#64) (regs .x22)).setMem
    (top + 0xffffffffffffffb8#64) (regs .x23)).setMem (top + 0xffffffffffffffb0#64) (regs .x24)).setMem
    (top + 0xffffffffffffffa8#64) (regs .x25)).setMem (top + 0xffffffffffffffa0#64) (regs .x26)).setMem
    (top + 0xffffffffffffff98#64) (regs .x27)

/-- What every part of the body keeps of memory: the frame (writing at most the state), the static data, the code
    and the saved registers' slots. -/
def MemInv (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  env.Frame top (Out regs m) m M ∧ env.Static M ∧ M.code = m.code ∧
    ∀ a, top + 0xffffffffffffff98#64 ≤ a → a ≤ top + 0xfffffffffffffff8#64 →
      M.getMem a = (saves m top ret regs).getMem a

/-- What every part of the body keeps: the stack pointer, the state's pointer in `s0`, and `MemInv`. -/
def Inv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (r : Reg → Word) (M : MachineState) :
    Prop :=
  r .x2 = top + 0xfffffffffffffd70#64 ∧ r .x8 = regs .x10 ∧ MemInv env ret top regs m M

/-- What the entry gives every part: the windows, the stack room for the frame and `memcpy`'s or `memset`'s, the
    state's pointer, the tables. -/
structure Fx (env : Env) (L : Link) (needC : Nat) (top : Word) (regs : Reg → Word) (m : MachineState) : Prop where
  win : Windows env top m
  room : env.stackLimit.toNat + (0x290 + needC) ≤ top.toNat
  al : top.toNat % 16 = 0
  sal : (regs .x10).toNat % 8 = 0
  swin : (0x10000000 ≤ (regs .x10).toNat ∧ (regs .x10).toNat + stateBytes ≤ env.heapEnd.toNat) ∨
      (env.stackLimit.toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + stateBytes ≤ 0xc0000000)
  soff : OffStack env top (regs .x10) stateBytes
  static : env.Static m
  nx : (env.next m).toNat ≤ env.heapEnd.toNat
  tabs : DataRef.InData env (tables L)

/-- The saved slots' lowest address. -/
theorem lo_toNat {top : Word} (h : 0x68 ≤ top.toNat) : (top + 0xffffffffffffff98#64).toNat = top.toNat - 0x68 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

/-- A store into the stack below the saved registers keeps `MemInv`. -/
theorem MemInv.stack {ret top x v : Word} {regs : Reg → Word} {m M : MachineState}
    (h : MemInv env ret top regs m M) (hlo : env.stackLimit.toNat ≤ x.toNat) (hhi : x.toNat + 0x70 ≤ top.toNat) :
    MemInv env ret top regs m (M.setMem x v) := by
  obtain ⟨hF, hS, hc, hsv⟩ := h
  refine ⟨Tactic.frame_slot hF hlo (by omega), Env.static_setMem_stack hS hlo, by rw [MachineState.code_setMem, hc],
    fun a h1 h2 => ?_⟩
  rw [MachineState.getMem_setMem_ne (fun he => ?_)]
  · exact hsv a h1 h2
  · subst he
    have := BitVec.le_def.1 h1
    rw [lo_toNat (by omega)] at this
    omega

/-- A store into the state keeps `MemInv`. -/
theorem MemInv.state {L : Link} {needC : Nat} {ret top x v : Word} {regs : Reg → Word} {m M : MachineState}
    (F : Fx env L needC top regs m) (h : MemInv env ret top regs m M) (hx : InRange (regs .x10) stateBytes x) :
    MemInv env ret top regs m (M.setMem x v) := by
  obtain ⟨hF, hS, hc, hsv⟩ := h
  have hwin := F.swin
  have hoff := F.soff
  have hroom := F.room
  have := env.layout
  have := F.win.heapEnd_le
  unfold OffStack at hoff
  unfold InRange at hx
  refine ⟨Tactic.frame_out hF hx (fun he => ?_), Tactic.static_store hS (by omega),
    by rw [MachineState.code_setMem, hc], fun a h1 h2 => ?_⟩
  · subst he; omega
  rw [MachineState.getMem_setMem_ne (fun he => ?_)]
  · exact hsv a h1 h2
  · subst he
    have := BitVec.le_def.1 h1
    have := BitVec.le_def.1 h2
    rw [lo_toNat (by omega)] at *
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega

/-- A store into the state at an offset of its pointer keeps `MemInv`. -/
theorem MemInv.stateAt {L : Link} {needC : Nat} {ret top c v : Word} {regs : Reg → Word} {m M : MachineState}
    (F : Fx env L needC top regs m) (h : MemInv env ret top regs m M) (hc : c.toNat + 8 ≤ stateBytes) :
    MemInv env ret top regs m (M.setMem (regs .x10 + c) v) := by
  refine h.state F ?_
  have := F.swin
  unfold InRange
  rw [BitVec.toNat_add]
  omega

/-- A store into the state's first lane keeps `MemInv`. -/
theorem MemInv.state0 {L : Link} {needC : Nat} {ret top v : Word} {regs : Reg → Word} {m M : MachineState}
    (F : Fx env L needC top regs m) (h : MemInv env ret top regs m M) :
    MemInv env ret top regs m (M.setMem (regs .x10) v) :=
  h.state F ⟨Nat.le_refl _, by unfold stateBytes; omega⟩

/-- A call that writes at most the stack below the saved slots keeps `MemInv`. -/
theorem MemInv.call {L : Link} {needC : Nat} {ret top t : Word} {regs : Reg → Word} {m M M' : MachineState}
    {out : Word → Prop} (F : Fx env L needC top regs m) (h : MemInv env ret top regs m M)
    (hf : env.Frame t out M M') (ht : t.toNat + 0x68 ≤ top.toNat)
    (hout : ∀ a, out a → env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + 0x68 < top.toNat) (hs : env.Static M')
    (hc : M'.code = M.code) : MemInv env ret top regs m M' := by
  obtain ⟨hF, hS, hc0, hsv⟩ := h
  have hroom := F.room
  have := env.layout
  have hl := F.win.heapEnd_le
  refine ⟨hF.trans hf (by omega) fun a ha => Or.inl ⟨(hout a ha).1, by have := (hout a ha).2; omega⟩, hs,
    hc.trans hc0, fun a h1 h2 => ?_⟩
  have := BitVec.le_def.1 h1
  rw [lo_toNat (by omega)] at this
  rw [hf.2.2 a fun hw => ?_]
  · exact hsv a h1 h2
  have := hf.2.1
  rcases hw with hw | hw | hw | hw
  · omega
  · omega
  · subst hw; omega
  · have := hout a hw; omega

/-- The prologue's memory keeps `MemInv`. -/
theorem MemInv.prologue {L : Link} {needC : Nat} {ret top : Word} {regs : Reg → Word} {m : MachineState}
    (F : Fx env L needC top regs m) : MemInv env ret top regs m (saves m top ret regs) := by
  have hroom := F.room
  have hS := F.static
  refine ⟨?_, ?_, by simp only [saves, MachineState.code_setMem], fun _ _ _ => rfl⟩
  · unfold saves
    repeat refine Tactic.frame_slot ?_ ?_ ?_
    · exact Env.Frame.refl F.nx
    all_goals (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  · unfold saves
    repeat refine Env.static_setMem_stack ?_ ?_
    · exact hS
    all_goals (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

/-- The doublewords of an aligned range lie in it. -/
theorem dwords_bounds {d a : Word} {n : Nat} (h : DwordsOf d n a) (hd : d.toNat % 8 = 0) :
    d.toNat ≤ a.toNat ∧ a.toNat < d.toNat + n := by
  unfold DwordsOf InRange at h
  rw [toNat_alignToDword] at h
  omega

/-- What a copy into the frame at `top - o`, 8-byte aligned, writes lies in it. -/
theorem copyOut_frame {top c a : Word} {R : Reg → Word} {M : MachineState} {o : Nat}
    (hc : (top + c).toNat = top.toNat - o) (hal : (top.toNat - o) % 8 = 0) (h10 : R .x10 = top + c)
    (ha : CopyOut R M a) : top.toNat - o ≤ a.toNat ∧ a.toNat < top.toNat - o + (R .x12).toNat := by
  unfold CopyOut at ha
  rw [h10] at ha
  rw [← hc]
  exact dwords_bounds ha (by rw [hc]; exact hal)

/-- A callee's frame keeps a word of the stack at or above the callee's stack top and not in its `out`. -/
theorem frame_keep {t a : Word} {out : Word → Prop} {M M' : MachineState} (hf : env.Frame t out M M')
    (ht : t.toNat ≤ a.toNat) (hs : env.stackLimit.toNat ≤ a.toNat) (hout : ¬ out a) : M'.getMem a = M.getMem a := by
  have := env.layout
  have := hf.2.1
  refine hf.2.2 a fun hw => ?_
  rcases hw with hw | hw | hw | hw
  · omega
  · omega
  · subst hw; omega
  · exact hout hw

/-- The `π` table's entries are lane indices. -/
theorem pi_lt : ∀ j (h : j < 25), (d_c200_f4afdee4_words[j]'(by simpa [d_c200_f4afdee4_words] using h)).toNat < 25 := by
  decide

/-- The stack pointer lies below the saved slots. -/
theorem sp_room {top : Word} {n : Nat} (h : env.stackLimit.toNat + (0x290 + n) ≤ top.toNat) :
    (top + 0xfffffffffffffd70#64).toNat + 0x68 ≤ top.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- What `memset` may write, at `sp + 0x160` for `200` bytes, lies below the saved slots. -/
theorem memset_out {top a : Word} {R : Reg → Word} {M : MachineState} (h16 : top.toNat % 16 = 0)
    {n : Nat} (hroom : env.stackLimit.toNat + (0x290 + n) ≤ top.toNat) (h10 : R .x10 = top + 0xfffffffffffffed0#64)
    (h12 : R .x12 = 200#64) (ha : CopyOut R M a) :
    env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + 0x68 < top.toNat := by
  have := copyOut_frame (o := 0x130) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by omega) h10 ha
  rw [h12, show (200#64).toNat = 200 from rfl] at this
  omega

/-- The round counter's slot. -/
abbrev cnt (top : Word) : Word := top + 0xfffffffffffffde8#64

/-- The round counter's slot as a number. -/
theorem cnt_toNat {top : Word} (h : 0x218 ≤ top.toNat) : (cnt top).toNat = top.toNat - 0x218 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A store at another offset of the stack top keeps the counter. -/
theorem cnt_stack {top c v : Word} {M : MachineState} (hc : c ≠ 0xfffffffffffffde8#64) :
    (M.setMem (top + c) v).getMem (cnt top) = M.getMem (cnt top) :=
  MachineState.getMem_setMem_ne fun h => hc ((BitVec.add_right_inj _).1 h).symm

/-- A store into the state keeps the counter. -/
theorem cnt_state {L : Link} {needC : Nat} {top c v : Word} {regs : Reg → Word} {m M : MachineState}
    (F : Fx env L needC top regs m) (hc : c.toNat + 8 ≤ stateBytes) :
    (M.setMem (regs .x10 + c) v).getMem (cnt top) = M.getMem (cnt top) := by
  refine MachineState.getMem_setMem_ne fun h => ?_
  have hroom := F.room
  have hwin := F.swin
  have hoff := F.soff
  unfold OffStack at hoff
  have := congrArg BitVec.toNat h
  rw [cnt_toNat (by omega), BitVec.toNat_add] at this
  omega

theorem cnt_state0 {L : Link} {needC : Nat} {top v : Word} {regs : Reg → Word} {m M : MachineState}
    (F : Fx env L needC top regs m) : (M.setMem (regs .x10) v).getMem (cnt top) = M.getMem (cnt top) := by
  have := cnt_state (c := 0#64) (v := v) (M := M) F (by decide)
  rwa [BitVec.add_zero] at this

/-- `memset`'s frame keeps the counter. -/
theorem cnt_memset {top : Word} {R : Reg → Word} {M M' : MachineState} {n : Nat} (h16 : top.toNat % 16 = 0)
    (hroom : env.stackLimit.toNat + (0x290 + n) ≤ top.toNat)
    (hf : env.Frame (top + 0xfffffffffffffd70#64) (CopyOut R M) M M') (h10 : R .x10 = top + 0xfffffffffffffed0#64)
    (h12 : R .x12 = 200#64) : M'.getMem (cnt top) = M.getMem (cnt top) := by
  have e := cnt_toNat (top := top) (by omega)
  refine frame_keep hf ?_ (by omega) fun ha => ?_
  · rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · have := copyOut_frame (o := 0x130) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by omega) h10 ha
    rw [e, h12, show (200#64).toNat = 200 from rfl] at this
    omega

/-- A table index's step. -/
theorem off_succ (d : Word) (c j : Nat) :
    d + BitVec.ofNat 64 (c * j) + BitVec.ofNat 64 c = d + BitVec.ofNat 64 (c * (j + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-- The `π` loop's exit test: the next destination index past the table's `25` entries. -/
theorem idx_last {d : Word} {j : Nat} (hd : d.toNat + 200 < 2 ^ 64) (hj : j ≤ 24) :
    d + BitVec.ofNat 64 (8 * j) + 8#64 = d + 200#64 ↔ j = 24 := by
  rw [off_succ]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [toNat_add_ofNat (by omega), BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  · rintro rfl; rfl

/-- A store into the `π` loop's array keeps the counter. -/
theorem cnt_pi {top s v : Word} {M : MachineState} (hroom : 0x290 ≤ top.toNat) (hs : s.toNat < 200) :
    (M.setMem (top + 0xfffffffffffffed0#64 + s) v).getMem (cnt top) = M.getMem (cnt top) := by
  refine MachineState.getMem_setMem_ne fun h => ?_
  have := congrArg BitVec.toNat h
  rw [cnt_toNat (by omega), BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-- A store into the `π` loop's array keeps `MemInv`. -/
theorem MemInv.pi {ret top s v : Word} {regs : Reg → Word} {m M : MachineState} {n : Nat}
    (hroom : env.stackLimit.toNat + (0x290 + n) ≤ top.toNat) (h : MemInv env ret top regs m M) (hs : s.toNat ≤ 192) :
    MemInv env ret top regs m (M.setMem (top + 0xfffffffffffffed0#64 + s) v) := by
  refine h.stack ?_ ?_ <;> rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

/-- The saved slots' words. -/
theorem saves_get {m : MachineState} {top ret : Word} {regs : Reg → Word} :
    (saves m top ret regs).getMem (top + 0xfffffffffffffff8#64) = ret ∧
    (saves m top ret regs).getMem (top + 0xfffffffffffffff0#64) = regs .x8 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffe8#64) = regs .x9 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffe0#64) = regs .x18 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffd8#64) = regs .x19 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffd0#64) = regs .x20 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffc8#64) = regs .x21 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffc0#64) = regs .x22 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffb8#64) = regs .x23 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffb0#64) = regs .x24 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffa8#64) = regs .x25 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffffa0#64) = regs .x26 ∧
    (saves m top ret regs).getMem (top + 0xffffffffffffff98#64) = regs .x27 := by
  unfold saves
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne, BitVec.add_right_inj]

/-- What `memcpy` may write, the round constants' copy at `sp + 0xa0`, lies below the saved slots. -/
theorem memcpy_out {top a : Word} {R : Reg → Word} {M : MachineState} (h16 : top.toNat % 16 = 0)
    {n : Nat} (hroom : env.stackLimit.toNat + (0x290 + n) ≤ top.toNat) (h10 : R .x10 = top + 0xfffffffffffffe10#64)
    (h12 : R .x12 = 192#64) (ha : CopyOut R M a) :
    env.stackLimit.toNat ≤ a.toNat ∧ a.toNat + 0x68 < top.toNat := by
  have := copyOut_frame (o := 0x1f0) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by omega) h10 ha
  rw [h12, show (192#64).toNat = 192 from rfl] at this
  omega

/-- The continuation every part is proved against: the contract's, at the return. -/
abbrev Cont (env : Env) (p : Lprog (Op Reg) Reg) (Q : State rvIsa → Prop) (ret top : Word) (rest : List Frame)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  ∀ r' m', HoldsT.post env (fun _ _ _ _ => True) Out ret top regs m r' m' →
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩

/-- The fixed facts every part takes. -/
structure Ctx (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (needC : Nat) (Q : State rvIsa → Prop)
    (ret top : Word) (rest : List Frame) (regs : Reg → Word) (m : MachineState) : Prop where
  hp : p[i]? = some (tmpl L)
  hL : L.WF p
  hset : MemsetSafeT env p L.memset.idx needC
  F : Fx env L needC top regs m
  hk : Cont env p Q ret top rest regs m

variable {needC : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
  {m : MachineState}

/-- The return, from `MemInv` and the calling convention's registers. -/
theorem ret_of (hk : Cont env p Q ret top rest regs m) {r' : Reg → Word} {M : MachineState}
    (hM : MemInv env ret top regs m M) (ha : AbiRegs top regs r') : rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', M⟩ :=
  hk _ _ ⟨⟨ha, hM.1, hM.2.1, trivial⟩, hM.2.2.1⟩

set_option hygiene false in
/-- The fixed facts and a part's memory facts as hypotheses. -/
local macro "fx_facts " C:term:max hM:term:max : tactic => `(tactic| (
  have hp := ($C).hp; have hL := ($C).hL; have hset := ($C).hset; have F := ($C).F
  have hW := F.win; have hroom := F.room; have hal := F.sal; have hwin := F.swin
  have hoff := F.soff; unfold OffStack at hoff
  have hS := ($hM).2.1; have hcode := ($hM).2.2.1; have hsv := ($hM).2.2.2))

/-- `MemInv` through the stores of a part: into the state, or into the stack below the saved slots. -/
local macro "mem_close " F:term:max hM:term:max : tactic => `(tactic| (
  repeat (first
    | with_reducible refine MemInv.state0 $F ?_
    | with_reducible refine MemInv.stateAt $F ?_ (by decide)
    | with_reducible refine MemInv.stack ?_ ?_ ?_)
  · exact $hM
  all_goals (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)))

/-- The round counter through the stores of a part: into the state, or at other offsets of the stack top. -/
local macro "cnt_close " F:term:max h:term:max : tactic => `(tactic| (
  repeat (first | rw [cnt_state0 $F] | rw [cnt_state $F (by decide)] | rw [cnt_stack (by decide)])
  exact $h))

set_option hygiene false in
/-- A round's part from `Body` to the next part at `pc`, through stores into the state and the stack. -/
local macro "round_part " C:term:max hb:term:max hB:term:max pc:num next:ident : tactic => `(tactic| (
  obtain ⟨⟨h2, h8, hM⟩, h23, h13, hk0⟩ := $hB
  fx_facts $C hM
  have hR := And.intro h2 (And.intro h8 h23)
  rv_introT hR
  rv_symT hp stop [$pc]
  refine $next $C $hb ⟨⟨?_, ?_, ?mem⟩, ?_, ?cnt, hk0⟩
  case mem => mem_close F hM
  case cnt => cnt_close F h13
  all_goals rv_closeT))

/-- The round loop's head, `k` rounds left: the round counter in `a3`. -/
def Head (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Inv env ret top regs m r M ∧ r .x23 = top + 0xfffffffffffffed0#64 ∧ (r .x13).toNat + k = 24 ∧ 0 < k

/-- Inside a round, `k` rounds left: the round counter in its stack slot. -/
def Body (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Inv env ret top regs m r M ∧ r .x23 = top + 0xfffffffffffffed0#64 ∧
    (M.getMem (top + 0xfffffffffffffde8#64)).toNat + k = 24 ∧ 0 < k

/-- The round loop's back edge, from a round with `k` left. -/
abbrev Back (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (Q : State rvIsa → Prop) (ret top : Word)
    (rest : List Frame) (regs : Reg → Word) (m : MachineState) (k : Nat) : Prop :=
  ∀ r M, Head env ret top regs m (k - 1) r M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 116, ret, top⟩ :: rest, r, M⟩

/-- The `π` loop's head, `n` lanes left: `a1`, `a2`, `a3` the next rotation, lane and destination index. -/
def Inner (env : Env) (L : Link) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k n : Nat)
    (r : Reg → Word) (M : MachineState) : Prop :=
  Body env ret top regs m k r M ∧ r .x10 = L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo ∧
    r .x11 = L.d_c100_179d68cc.hi + L.d_c100_179d68cc.lo + BitVec.ofNat 64 (4 * (25 - n)) ∧
    r .x12 = regs .x10 + BitVec.ofNat 64 (8 * (25 - n)) ∧
    r .x13 = L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo + BitVec.ofNat 64 (8 * (25 - n)) ∧ 0 < n ∧ n ≤ 25

set_option rv_sym.heap true in
/-- The epilogue: the saved registers restored, the return. -/
theorem p8_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hI : Inv env ret top regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 752, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, hM⟩ := hI
  fx_facts C hM
  have hk := C.hk
  have hR := And.intro h2 h8
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := saves_get (m := m) (top := top) (ret := ret)
    (regs := regs)
  rv_introT hR
  rv_symT hp
  open Tactic in
    exact ret_of hk hM ⟨rf_get_x2 .., (rf_get_x8 ..).trans s2, (rf_get_x9 ..).trans s3, (rf_get_x18 ..).trans s4,
      (rf_get_x19 ..).trans s5, (rf_get_x20 ..).trans s6, (rf_get_x21 ..).trans s7, (rf_get_x22 ..).trans s8,
      (rf_get_x23 ..).trans s9, (rf_get_x24 ..).trans s10, (rf_get_x25 ..).trans s11, (rf_get_x26 ..).trans s12,
      (rf_get_x27 ..).trans s13⟩

set_option rv_sym.heap true in
/-- The round's end: the counter incremented, the back edge or the epilogue. -/
theorem p7_ok (C : Ctx env p i L needC Q ret top rest regs m) {k : Nat} (hb : Back env p i Q ret top rest regs m k)
    {r : Reg → Word} {M : MachineState} (hB : Body env ret top regs m k r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 740, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨⟨h2, h8, hM⟩, h23, h13, hk0⟩ := hB
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 h23)
  rv_introT hR
  rv_symT hp stop [752]
  · have hc' : (M.getMem (top + 0xfffffffffffffde8#64) + 1#64).toNat ≠ 24 := fun h => hc (BitVec.eq_of_toNat_eq h)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at hc'
    refine hb _ _ ⟨⟨?_, ?_, ?mem⟩, ?_, ?cnt, by omega⟩
    case mem => mem_close F hM
    case cnt =>
      show (M.getMem (top + 0xfffffffffffffde8#64) + 1#64).toNat + (k - 1) = 24
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    all_goals rv_closeT
  · refine p8_ok C ⟨?_, ?_, ?mem⟩
    case mem => mem_close F hM
    all_goals rv_closeT

set_option rv_sym.heap true in
/-- A round from label 330. -/
theorem p6_ok (C : Ctx env p i L needC Q ret top rest regs m) {k : Nat} (hb : Back env p i Q ret top rest regs m k)
    {r : Reg → Word} {M : MachineState} (hB : Body env ret top regs m k r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 660, ret, top⟩ :: rest, r, M⟩ := by
  round_part C hb hB 740 p7_ok

set_option rv_sym.heap true in
/-- A round from label 280. -/
theorem p5_ok (C : Ctx env p i L needC Q ret top rest regs m) {k : Nat} (hb : Back env p i Q ret top rest regs m k)
    {r : Reg → Word} {M : MachineState} (hB : Body env ret top regs m k r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 560, ret, top⟩ :: rest, r, M⟩ := by
  round_part C hb hB 660 p6_ok

set_option rv_sym.heap true in
/-- A round after the `π` loop. -/
theorem p4_ok (C : Ctx env p i L needC Q ret top rest regs m) {k : Nat} (hb : Back env p i Q ret top rest regs m k)
    {r : Reg → Word} {M : MachineState} (hB : Body env ret top regs m k r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 430, ret, top⟩ :: rest, r, M⟩ := by
  round_part C hb hB 560 p5_ok

set_option rv_sym.heap true in
/-- **The `π` loop**, by `Total.loop` with the lanes left as the measure. -/
theorem inner_ok (C : Ctx env p i L needC Q ret top rest regs m) {k : Nat}
    (hb : Back env p i Q ret top rest regs m k) :
    ∀ n r M, Inner env L ret top regs m k n r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 400, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (Inner env L ret top regs m k)
    fun n r M ⟨⟨⟨h2, h8, hM⟩, h23, h13, hk0⟩, h10, h11, h12, h13', hn0, hn25⟩ ih => ?_
  fx_facts C hM
  obtain ⟨⟨-, -, -⟩, ⟨pi1, pi2, pi3⟩, ⟨ro1, ro2, ro3⟩⟩ := tables_ok F.tabs hW F.static
  have hwd : DataRef.Words env L.d_c200_f4afdee4 d_c200_f4afdee4_words :=
    F.tabs.words (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hv := hwd.get hS (25 - n) (by simp [d_c200_f4afdee4_words]; omega)
  have hpi : (M.getMem (L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo + BitVec.ofNat 64 (8 * (25 - n)))).toNat < 25 := by
    rw [hv]; exact pi_lt _ (by omega)
  have hsh : (M.getMem (L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo + BitVec.ofNat 64 (8 * (25 - n))) <<< 3).toNat =
      8 * (M.getMem (L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo + BitVec.ofNat 64 (8 * (25 - n)))).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hl := hW.top_le
  have h16 := F.al
  have hly := env.layout
  have hna := hW.nextAddr_ge
  have hR := And.intro h2 (And.intro h8 (And.intro h23 (And.intro h10 (And.intro h11 (And.intro h12 h13')))))
  rw [inWindow_iff] at pi2 ro2
  have hsb : stateBytes = 200 := rfl
  have hhe := hW.heapEnd_le
  have hpi8 :
      (M.getMem (L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo + BitVec.ofNat 64 (8 * (25 - n))) <<< 3).toNat ≤ 192 := by
    omega
  have hlast := idx_last (d := L.d_c200_f4afdee4.hi + L.d_c200_f4afdee4.lo) (j := 25 - n) (by omega) (by omega)
  rv_introT hR
  rv_symT hp stop [430]
  all_goals try first
    | (rw [inWindow_iff, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    | (rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    | (rw [inWindow_iff, BitVec.toNat_add, BitVec.toNat_add, hsh, BitVec.toNat_ofNat]; omega)
    | (rw [BitVec.toNat_add, BitVec.toNat_add, hsh, BitVec.toNat_ofNat]; omega)
  · have hn1 : n ≠ 1 := fun h1 => hc (hlast.2 (by omega))
    have e := show 25 - (n - 1) = 25 - n + 1 by omega
    refine ih (n - 1) _ _ (by omega)
      ⟨⟨⟨?_, ?_, hM.pi hroom (by omega)⟩, ?_, ?cnt, hk0⟩, ?_, ?x11, ?x12, ?x13, by omega, by omega⟩
    case cnt => rw [cnt_pi (by omega) (by omega)]; exact h13
    case x11 => rw [e, ← off_succ]; rfl
    case x12 => rw [e, ← off_succ]; rfl
    case x13 => rw [e, ← off_succ]; rfl
    all_goals rv_closeT
  · have hn1 : n = 1 := by have := hlast.1 hc; omega
    refine p4_ok C hb ⟨⟨?_, ?_, hM.pi hroom (by omega)⟩, ?_, ?cnt, hk0⟩
    case cnt => rw [cnt_pi (by omega) (by omega)]; exact h13
    all_goals rv_closeT

set_option rv_sym.heap true in
/-- A round from label 170: the round constant read, the array cleared by `memset`, the `π` loop's entry. -/
theorem p3_ok (C : Ctx env p i L needC Q ret top rest regs m) {k : Nat} (hb : Back env p i Q ret top rest regs m k)
    {r : Reg → Word} {M : MachineState} (hB : Body env ret top regs m k r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 340, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨⟨h2, h8, hM⟩, h23, h13, hk0⟩ := hB
  fx_facts C hM
  have hsh : (M.getMem (top + 0xfffffffffffffde8#64) <<< 3).toNat =
      8 * (M.getMem (top + 0xfffffffffffffde8#64)).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hR := And.intro h2 (And.intro h8 h23)
  rv_introT hR
  have hl := hW.top_le
  have h16 := F.al
  have hly := env.layout
  have hna := hW.nextAddr_ge
  rv_symT hp stop [400] with [hL] using [hset]
  · rw [inWindow_iff, BitVec.toNat_add, BitVec.toNat_add, hsh]; simp only [BitVec.toNat_ofNat]; omega
  · rw [BitVec.toNat_add, BitVec.toNat_add, hsh]; simp only [BitVec.toNat_ofNat]; omega
  refine inner_ok C hb 25 _ _ ⟨⟨⟨?_, ?_, ?mem⟩, ?_, ?cnt, hk0⟩, ?_, ?e11, ?e12, ?e13, by decide, le_rfl⟩
  case e11 => exact (BitVec.add_zero _).symm
  case e12 => exact (BitVec.add_zero _).symm
  case e13 => exact (BitVec.add_zero _).symm
  case mem =>
    refine MemInv.call F ?_ hret1_14 (sp_room hroom) (fun a ha => memset_out h16 hroom rfl rfl ha) hret1_15
      hret1_17
    mem_close F hM
  case cnt =>
    rw [cnt_memset h16 hroom hret1_14 rfl rfl]
    cnt_close F h13
  all_goals rv_closeT

set_option rv_sym.heap true in
/-- A round from label 120. -/
theorem p2_ok (C : Ctx env p i L needC Q ret top rest regs m) {k : Nat} (hb : Back env p i Q ret top rest regs m k)
    {r : Reg → Word} {M : MachineState} (hB : Body env ret top regs m k r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 240, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨⟨h2, h8, hM⟩, h23, h13, hk0⟩ := hB
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 h23)
  rv_introT hR
  rv_symT hp stop [340]
  refine p3_ok C hb ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hk0⟩
  rotate_left 2
  · mem_close F hM
  all_goals rv_closeT

set_option rv_sym.heap true in
/-- A round from its head. -/
theorem p1_ok (C : Ctx env p i L needC Q ret top rest regs m) {k : Nat} (hb : Back env p i Q ret top rest regs m k)
    {r : Reg → Word} {M : MachineState} (hH : Head env ret top regs m k r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 116, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨⟨h2, h8, hM⟩, h23, h13, hk0⟩ := hH
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 h23)
  rv_introT hR
  rv_symT hp stop [240]
  refine p2_ok C hb ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hk0⟩
  rotate_left 2
  · mem_close F hM
  all_goals rv_closeT

/-- **The round loop**, by `Total.loop` with the rounds left as the measure. -/
theorem loop_ok (C : Ctx env p i L needC Q ret top rest regs m) :
    ∀ k r M, Head env ret top regs m k r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 116, ret, top⟩ :: rest, r, M⟩ :=
  Total.loop (I := rvIsa) (Head env ret top regs m) fun k _ _ hH ih =>
    p1_ok C (fun r' M' h => ih (k - 1) r' M' (by have := hH.2.2.2; omega) h) hH

set_option rv_sym.heap true in
/-- The rest of the state's lanes loaded, to the round loop's head. -/
theorem mid2_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hI : Inv env ret top regs m r M) (h13 : r .x13 = 0#64) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 80, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, hM⟩ := hI
  fx_facts C hM
  have hR := And.intro h2 (And.intro h8 h13)
  rv_introT hR
  rv_symT hp stop [116]
  refine loop_ok C 24 _ _ ⟨⟨?_, ?_, ?mem⟩, ?_, ?_, by decide⟩
  case mem => mem_close F hM
  all_goals rv_closeT

set_option rv_sym.heap true in
/-- From `memcpy`'s return: the state's first lanes loaded. -/
theorem mid_ok (C : Ctx env p i L needC Q ret top rest regs m) {r : Reg → Word} {M : MachineState}
    (hI : Inv env ret top regs m r M) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 42, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h2, h8, hM⟩ := hI
  fx_facts C hM
  have hR := And.intro h2 h8
  rv_introT hR
  rv_symT hp stop [80]
  refine mid2_ok C ⟨?_, ?_, ?mem⟩ ?_
  case mem => mem_close F hM
  all_goals rv_closeT

set_option rv_sym.heap true in
/-- **`keccak_f` is total**, with its `0x290`-byte frame and the stack `memcpy` and `memset` need. -/
theorem total (hp : p[i]? = some (tmpl L)) (hL : L.WF p) (hdata : DataRef.InData env (tables L)) {needC : Nat}
    (hcpy : MemcpySpecT env p L.memcpy.idx needC) (hset : MemsetSafeT env p L.memset.idx needC) :
    KeccakFSafeT env p i (0x290 + needC) := by
  rv_autoT hp stop [42] with [hL] using [hcpy, hset]
  all_goals
    obtain ⟨⟨rc1, rc2, rc3⟩, -, -⟩ := tables_ok hdata hpre_10 hpre_4
    have := env.layout
    have := hpre_10.top_le
    have := hpre_10.nextAddr_ge
    rw [inWindow_iff] at rc2
  · simp only [BitVec.toNat_ofNat]; omega
  all_goals
    have e1 : (top + 0xfffffffffffffe10#64).toNat = top.toNat - 0x1f0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e2 : (top + 0xfffffffffffffd70#64).toNat = top.toNat - 0x290 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e3 : (192#64).toNat = 192 := rfl
  · intro _ b h1 h2; unfold InRange at h1 h2; rw [e1, e3] at h1; rw [e3] at h2; omega
  · refine Or.inr ⟨Or.inr ⟨?_, ?_⟩, Or.inr ?_, ?_, Or.inl ?_⟩ <;> (try rw [inWindow_iff]) <;> (try rw [e3]) <;>
      (try rw [e1]) <;> (try rw [e2]) <;> omega
  · have F : Fx env L needC top regs m := ⟨hpre_10, by omega, hpre_9, hpre_6, hpre_7, by rw [← hpre_2]; exact hpre_8,
      hpre_4, hpre_5, hdata⟩
    refine mid_ok ⟨hp, hL, hset, F, hk⟩ ⟨?_, ?_, MemInv.call F (MemInv.prologue F) hret1_14 (sp_room F.room)
      (fun a ha => memcpy_out hpre_9 F.room rfl rfl ha) hret1_15 hret1_19⟩
    all_goals rv_closeT

end Rv64mc.Proof.Hash.KeccakFT

/-- info: 'Rv64mc.Proof.Hash.KeccakFT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Hash.KeccakFT.total
