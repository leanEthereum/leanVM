module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Mid

/-!
# `keccak_open`: the registers known around the fold

`KAt m0 vars ks st`: SP is the frame's base and each register of `ks` holds its value, a `stable`
symbolic value (no register, flag or memory in it) evaluated with the fold's regions (`envR`) and
`vars`. From it the symbolic state `pS ks` describes the machine (`match_pS`); after a block the
known registers `ks'` the block's result gives (`regsOk`, `KAt.after`); a callee keeps them
(`KAt.call`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)

@[expose] public section

/-- A value that reads no register, flag or memory. -/
def stable : Sym → Bool
  | .lit _ | .ptr _ _ | .var _ => true
  | .bin _ _ a b => stable a && stable b
  | .un _ _ a => stable a
  | _ => false

/-- Known registers: callee-saved, with stable values. -/
def wfK (ks : List (XReg × Sym)) : Bool := ks.all fun p ↦ calleeSaved p.1 && stable p.2

/-- **The known registers**: SP the frame's base, each register of `ks` its value. -/
def KAt [Labels] (m0 : MachineData) (vars : Nat → BitVec 64) (ks : List (XReg × Sym))
    (st : MachineData) : Prop :=
  st.regs.SP.toBitVec = fbA m0 ∧
    AllOf (fun p ↦ (st.regs.getXReg p.1).toBitVec = p.2.eval (Env.ofMachine m0 (envR m0) vars)) ks

/-- A register of `ks'` after a block: its value there, or a load the fold's memory gives (round
`t`'s challenge, the slot point's or the rows' address). -/
def ok1 (t : Nat) (S : SState) (p : XReg × Sym) : Bool :=
  stable p.2 && calleeSaved p.1 &&
    (S.reg p.1 == some p.2 ||
      (p.2 == .var 0 && S.reg p.1 == some (.load 1 (16 * t) 8)) ||
      (p.2 == .var 1 && S.reg p.1 == some (.load 1 (16 * t + 8) 8)) ||
      (p.2 == .ptr 1 0 && S.reg p.1 == some (.load 0 40 8)) ||
      (p.2 == .ptr 2 0 && S.reg p.1 == some (.load 0 48 8)))

/-- The known registers `ks'` after a block, SP the frame's base. -/
def regsOk (t : Nat) (S : SState) (ks : List (XReg × Sym)) : Bool :=
  ks.all (ok1 t S) && S.sp == .ptr 0 0

/-- `ks'` is part of `ks`. -/
def subK (ks' ks : List (XReg × Sym)) : Bool :=
  ks'.all fun p ↦ ks.any fun q ↦ q.1 == p.1 && decide (q.2 = p.2)

end

public section

variable [Labels]

theorem eval_stable : ∀ (v : Sym), stable v = true → ∀ {e e' : Env}, e.regions = e'.regions →
    e.vars = e'.vars → v.eval e = v.eval e'
  | .lit _, _, _, _, _, _ => rfl
  | .var i, _, e, e', _, hv => by simp only [Sym.eval, hv]
  | .ptr r o, _, e, e', hr, _ => by simp only [Sym.eval, Env.base, hr]
  | .bin op w a b, h, e, e', hr, hv => by
    simp only [stable, Bool.and_eq_true] at h
    simp only [Sym.eval]
    rw [eval_stable a h.1 hr hv, eval_stable b h.2 hr hv]
  | .un op w a, h, e, e', hr, hv => by
    simp only [stable] at h
    simp only [Sym.eval]
    rw [eval_stable a h hr hv]
  | .reg _, h, _, _, _, _ => nomatch h
  | .sp, h, _, _, _, _ => nomatch h
  | .label _, h, _, _, _, _ => nomatch h
  | .load _ _ _, h, _, _, _, _ => nomatch h
  | .loadx _ _ _ _, h, _, _, _, _ => nomatch h
  | .ite _ _ _, h, _, _, _, _ => nomatch h

variable {a : DecArea} {c : Cx} {m0 st st' : MachineData} {vars : Nat → BitVec 64}
  {ks ks' : List (XReg × Sym)}

theorem eval_of (m m' : MachineData) {v : Sym} (h : stable v = true) :
    v.eval (Env.ofMachine m (envR m0) vars) = v.eval (Env.ofMachine m' (envR m0) vars) :=
  eval_stable v h rfl rfl

theorem KAt.reg (hk : KAt m0 vars ks st) {r : XReg} {v : Sym} (h : (r, v) ∈ ks) :
    (st.regs.getXReg r).toBitVec = v.eval (Env.ofMachine m0 (envR m0) vars) :=
  mem_of_allOf (P := fun p : XReg × Sym ↦
    (st.regs.getXReg p.1).toBitVec = p.2.eval (Env.ofMachine m0 (envR m0) vars)) hk.2 h

theorem KAt.of_reg (hsp : st.regs.SP.toBitVec = fbA m0)
    (h : ∀ p ∈ ks, (st.regs.getXReg p.1).toBitVec = p.2.eval (Env.ofMachine m0 (envR m0) vars)) :
    KAt m0 vars ks st := by
  refine ⟨hsp, ?_⟩
  induction ks with
  | nil => trivial
  | cons p ks ih =>
    exact ⟨h p List.mem_cons_self, ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq)⟩

theorem KAt.sub (hk : KAt m0 vars ks st) (h : subK ks' ks = true) : KAt m0 vars ks' st :=
  KAt.of_reg hk.1 fun p hp ↦ by
    obtain ⟨q, hq, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    rw [← XReg.eq_of_beq he.1, ← he.2]
    exact hk.reg hq

/-- **A callee keeps the known registers.** -/
theorem KAt.call (hk : KAt m0 vars ks st) (hw : wfK ks = true) (hs : Saved st st') :
    KAt m0 vars ks st' :=
  KAt.of_reg (by rw [hs.2.1]; exact hk.1) fun p hp ↦ by
    have := List.all_eq_true.mp hw p hp
    simp only [Bool.and_eq_true] at this
    rw [hs.1 p.1 this.1]
    exact hk.reg hp

/-- The fold's regions are data memory, do not wrap and are apart. -/
theorem wf_fold (ok : Ok a m0) (hb : Body m0 st) : (Env.ofMachine st (envR m0) vars).WF := by
  have hn := ok.nums
  have hN := hn.hN
  obtain ⟨hfm, -, hfb⟩ := frame_ok ok.stack (show 2224 ≤ keccakOpenStack by decide)
  have hfb' : (fbA m0).toNat = spN m0 - 2224 := hfb
  have := hn.sW; have := hn.sS; have := hn.rW; have := hn.rS; have := hn.s_r
  refine Env.wf_of ⟨⟨Mapped.kept' hfm hb.kept,
      show (fbA m0).toNat + 2224 ≤ 2 ^ 64 by
        rw [hfb']; have := m0.regs.SP.toBitVec.isLt; unfold spN; omega⟩,
    ⟨Mapped.kept' ok.slotM hb.kept, show NoWrap (slA m0) 96 by unfold NoWrap; omega⟩,
    ⟨Mapped.kept' ok.rowsM hb.kept, show NoWrap (rwA m0) 65536 by unfold NoWrap; omega⟩,
    trivial⟩ ?_
  have hrn : (rwA m0).toNat + 65536 ≤ 2 ^ 64 := hn.rW
  have p01 : Apart (fbA m0) 2224 (slA m0) 96 := by unfold Apart; omega
  have p02 : Apart (fbA m0) 2224 (rwA m0) 65536 := by unfold Apart; omega
  have p12 : Apart (slA m0) 96 (rwA m0) 65536 := by unfold Apart; omega
  refine List.pairwise_cons.mpr ⟨fun e he ↦ ?_, List.pairwise_cons.mpr ⟨fun e he ↦ ?_,
    List.pairwise_singleton _ _⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    exacts [p01, p02]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; exact p12

omit [Labels] in
theorem allOf_imp {α : Type} {P Q : α → Prop} :
    ∀ {l : List α}, AllOf P l → (∀ x ∈ l, P x → Q x) → AllOf Q l
  | [], _, _ => trivial
  | x :: _, h, hq =>
    ⟨hq x List.mem_cons_self h.1, allOf_imp h.2 fun y hy ↦ hq y (List.mem_cons_of_mem _ hy)⟩

omit [Labels] in
theorem stable_of {p : XReg × Sym} (hw : wfK ks = true) (hp : p ∈ ks) : stable p.2 = true := by
  have := List.all_eq_true.mp hw p hp
  simp only [Bool.and_eq_true] at this
  exact this.2

/-- **The fold's symbolic state describes the machine** where the registers `ks` are known and
the frame's word `40` is the slot point's address. -/
theorem match_pS (ok : Ok a m0) (hk : KAt m0 vars ks st) (hw : wfK ks = true)
    (h40 : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 40)
      (UInt64.ofBitVec (slA m0))) :
    Match (Env.ofMachine st (envR m0) vars) (pS ks) st := by
  have hal : (fbA m0).toNat % 16 = 0 :=
    frame_aligned ok.stack (show 2224 ≤ keccakOpenStack by decide) rfl
  refine match_ofMachine ⟨rfl, fun _ ↦ hal, rfl, nofun, rfl, nofun, trivial⟩ ?_ ?_ trivial
    trivial ⟨?_, trivial⟩
  · rw [hk.1]
    show _ = fbA m0 + BitVec.ofInt 64 0
    rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, NativeRustcVm.addr_add_zero]
  · exact allOf_imp hk.2 fun p hp h ↦ h.trans (eval_of m0 st (stable_of hw hp))
  · show (Env.ofMachine st (envR m0) vars).load 0 40 8 = slA m0 + BitVec.ofInt 64 0
    rw [Sumcheck.load_word (env := Env.ofMachine st (envR m0) vars) (r := 0) h40,
      UInt64.toBitVec_ofBitVec, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
      NativeRustcVm.addr_add_zero]

/-- **The known registers after a block** from `pS ks`, by `regsOk`. -/
theorem KAt.after {S' : SState} (hm' : Match (Env.ofMachine st (envR m0) vars) S' st')
    {t : Nat} (ht : t < c.sl.size) (hv0 : vars 0 = (c.sl.getD t 0).c0.toBitVec)
    (hv1 : vars 1 = (c.sl.getD t 0).c1.toBitVec) (hmid : Mid c m0 st)
    (h : regsOk t S' ks' = true) : KAt m0 vars ks' st' := by
  simp only [regsOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hall, hsp⟩ := h
  refine KAt.of_reg ?_ fun ⟨r, v⟩ hp ↦ ?_
  · rw [hm'.sp, hsp]
    show fbA m0 + BitVec.ofInt 64 0 = _
    rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, NativeRustcVm.addr_add_zero]
  have h1 := List.all_eq_true.mp hall _ hp
  simp only [ok1, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨hs, -⟩, h1⟩ := h1
  have hew := ewsAt_getD hmid.slot ht
  obtain ⟨hl0, hl1⟩ := load_ew (env := Env.ofMachine st (envR m0) vars) (r := 1) (o := 16 * t)
    hew
  rcases h1 with (((h1 | ⟨rfl, h1⟩) | ⟨rfl, h1⟩) | ⟨rfl, h1⟩) | ⟨rfl, h1⟩
  · rw [hm'.regs _ _ h1]; exact eval_of st m0 hs
  · rw [hm'.regs _ _ h1]
    show (Env.ofMachine st (envR m0) vars).load 1 (16 * t) 8 = vars 0
    rw [hl0, hv0]
  · rw [hm'.regs _ _ h1]
    show (Env.ofMachine st (envR m0) vars).load 1 (16 * t + 8) 8 = vars 1
    rw [hl1, hv1]
  · rw [hm'.regs _ _ h1]
    show (Env.ofMachine st (envR m0) vars).load 0 40 8 = slA m0 + BitVec.ofInt 64 0
    rw [Sumcheck.load_word (env := Env.ofMachine st (envR m0) vars) (r := 0) hmid.sw,
      UInt64.toBitVec_ofBitVec, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
      NativeRustcVm.addr_add_zero]
  · rw [hm'.regs _ _ h1]
    show (Env.ofMachine st (envR m0) vars).load 0 48 8 = rwA m0 + BitVec.ofInt 64 0
    rw [Sumcheck.load_word (env := Env.ofMachine st (envR m0) vars) (r := 0) hmid.rw,
      UInt64.toBitVec_ofBitVec, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
      NativeRustcVm.addr_add_zero]

omit [Labels] in
theorem wfK_of_regsOk {t : Nat} {S : SState} (h : regsOk t S ks = true) : wfK ks = true := by
  simp only [regsOk, Bool.and_eq_true] at h
  refine List.all_eq_true.mpr fun p hp ↦ ?_
  have := List.all_eq_true.mp h.1 p hp
  simp only [ok1, Bool.and_eq_true] at this
  simp only [Bool.and_eq_true]
  exact ⟨this.1.2, this.1.1⟩

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
