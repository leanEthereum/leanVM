module

public import NativeRustcVmX64.Bus.AccumulateSide.Vals
public import NativeRustcVmX64.Ring.Stack
public import NativeRustcX64.Got

/-!
# `accumulate_side`: the blocks' environments (x86-64)

An input region (`In m0 a n`): mapped, not wrapping, apart from the forms and from the stack; a
part of one is one (`In.sub`). Its bytes are the entry's in the body (`St.bytes`, `St.word`).
The environments of the frame and one or two input regions are well formed (`wf1`, `wf2`); a
body state matches a template with RSP at offset `8` (`St.mt`). The stack arguments' aliases
(`argAliases_ok`). `eq_above`'s inlined head (`ev_sat`, `ev_shr`, `ev_above`) and its call
(`eqAbove_pre`, `eqAbove_ret`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- **An input region**: mapped, not wrapping, apart from the forms and the stack. -/
def In (m0 : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m0.dmem a n ∧ NativeRustcVm.NoWrap a n ∧ Apart a n (reg m0 .rsi) formsBytes ∧
    Apart a n (stackBelow m0 N) (N + 8)

end

public section

variable {m0 : MachineData}

theorem In.sub {a : BitVec 64} {n o k : Nat} (h : In m0 a n) (hk : o + k ≤ n) (hk0 : 0 < k) :
    In m0 (off a o) k := by
  obtain ⟨hm, hw, hf, hs⟩ := h
  have hw' := hw
  unfold NativeRustcVm.NoWrap at hw'
  have ho : (off a o).toNat = a.toNat + o := toNat_off (by omega)
  refine ⟨fun i hi ↦ by rw [off_add]; exact hm _ (by omega), ?_, ?_, ?_⟩
  · unfold NativeRustcVm.NoWrap; omega
  · unfold Apart at hf ⊢; rw [ho]; omega
  · unfold Apart at hs ⊢; rw [ho]; omega

theorem In.of_inOk {a : BitVec 64} {n : Nat} (hi : InOk m0 a n N) (hf : Apart a n (reg m0 .rsi) formsBytes) :
    In m0 a n :=
  ⟨hi.1.1, hi.1.2, hf, hi.2⟩

theorem allOf_of {α : Type} {P : α → Prop} : ∀ {l : List α}, (∀ a ∈ l, P a) → AllOf P l
  | [], _ => trivial
  | _ :: _, h => ⟨h _ List.mem_cons_self, allOf_of fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

section
variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- **The bytes of an input region** are the entry's in the body. -/
theorem St.bytes (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {o : Nat} {m : MachineData} (hst : St m0 O V D o m)
    (hO : ∀ q, O q → outs m0 q) {a : BitVec 64} {n : Nat} (hi : In m0 a n)
    {bs : List UInt8} (hb : NativeRustcVm.BytesAt m0.dmem a bs) (hn : bs.length ≤ n) :
    NativeRustcVm.BytesAt m.dmem a bs :=
  hb.of_sameOutside hst.same fun i hil hq ↦ hq.elim
    (fun hq ↦ NativeRustcVm.Apart.not_inRange_add hi.2.2.1 hi.2.1 h.forms_nw (by omega)
      (hO _ hq))
    fun hq ↦ NativeRustcVm.Apart.not_inRange_add hi.2.2.2 hi.2.1 (noWrap_stackBelow h.stack) (by omega)
      (Ring.inRange_le hq (by omega))

/-- **A word of an input region** is the entry's in the body. -/
theorem St.word (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {o : Nat} {m : MachineData} (hst : St m0 O V D o m)
    (hO : ∀ q, O q → outs m0 q) {a : BitVec 64} {n : Nat} (hi : In m0 a n) {j : Nat}
    (hj : j + 8 ≤ n) {w : UInt64} (hw : NativeRustcVm.WordAt m0.dmem (off a j) w) :
    NativeRustcVm.WordAt m.dmem (off a j) w :=
  St.bytes h hst hO (hi.sub hj (by omega)) hw (by rw [NativeRustcVm.length_wordBytes])

/-- The frame's environment with one input region is well formed. -/
theorem wf1 (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {a : BitVec 64} {n : Nat} (hi : In m0 a n) {vs : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 m F [(a, n)] vs ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped h.stack le_F) hk, h.frame_nw⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hi.1 hk, hi.2.1⟩)
    (List.pairwise_pair.mpr (Apart.symm' (apart_frame hi.2.2.2 h.spN le_F)))

/-- The frame's environment with two input regions apart is well formed. -/
theorem wf2 (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {a b : BitVec 64} {n n' : Nat} (ha : In m0 a n) (hb : In m0 b n') (hab : Apart a n b n')
    {vs : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 m F [(a, n), (b, n')] vs ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped h.stack le_F) hk, h.frame_nw⟩
    (rest2_ok ⟨ha.1, ha.2.1⟩ ⟨hb.1, hb.2.1⟩ hk)
    (pairwise3 (Apart.symm' (apart_frame ha.2.2.2 h.spN le_F))
      (Apart.symm' (apart_frame hb.2.2.2 h.spN le_F)) hab)

/-- The frame's environment alone is well formed. -/
theorem wf0 (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {vs : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 m F [] vs ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped h.stack le_F) hk, h.frame_nw⟩ (by simp)
    (List.pairwise_singleton _ _)

/-- The stack arguments are an input region. -/
theorem Pre.argsIn (h : Pre L rows bl Fm SL m0) : In m0 (rspOf m0 + 8#64) 88 :=
  ⟨h.args.1, (Ring.args_readable h.args (by decide)).2, Apart.symm' h.fArgs,
    Apart.symm' (Ring.args_apart (F := N) h.stack h.args (by decide) (Nat.le_refl _))⟩

/-- **The stack arguments' word `i`** in the body, loaded from region `1`. -/
theorem St.arg (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {o : Nat} {m : MachineData} (hst : St m0 O V D o m)
    (hO : ∀ q, O q → outs m0 q) {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {i : Nat} (hi : i < 11) :
    (frameEnv m0 m F ((rspOf m0 + 8#64, 88) :: rest) vs ret).load 1 (8 * i) 8 = stackArg m0 i := by
  have hw : NativeRustcVm.WordAt m0.dmem (off (rspOf m0 + 8#64) (8 * i))
      (UInt64.ofBitVec (stackArg m0 i)) := by
    rw [Ring.stackArg_eq]
    show NativeRustcVm.WordAt _ _ (UInt64.ofBitVec (UInt64.toBitVec _))
    rw [UInt64.ofBitVec_toBitVec]
    exact NativeRustcVm.wordAt_of_mapped (NativeRustcVm.Mapped.sub h.args.1 (by omega))
  rw [load_ofMachine (r := 1) (n := 88) rfl (St.word h hst hO h.argsIn (by omega) hw)]

/-- **A body state matches** a template with RSP at offset `8`. -/
theorem St.mt {O : BitVec 64 → Prop} {V : Nat → UInt64} {D : List (Sym × Nat)} {m : MachineData}
    (hst : St m0 O V D 8 m)
    {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64} {sizes : List Nat}
    {labels : List (Label × Nat)} {bounds : List (Sym × Nat)} {aliases : List (Sym × Nat × Int)}
    (hr : RegionsOk sizes ((fb m0, F + 8) :: rest))
    (hl : AllOf (fun p ↦ (frameEnv m0 m F rest vs ret).base p.2 = (Labels.label p.1).toBitVec)
      labels)
    (hb : AllOf (fun p ↦ (p.1.eval (frameEnv m0 m F rest vs ret)).toNat < p.2) bounds)
    (ha : AllOf (fun p ↦ p.1.eval (frameEnv m0 m F rest vs ret) =
      (frameEnv m0 m F rest vs ret).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Match (frameEnv m0 m F rest vs ret) (init sizes [(.rsp, .ptr 0 8)] labels bounds aliases) m :=
  match_ofMachine hr ⟨hst.fr.rsp_eval, trivial⟩ hl hb ha

/-- The copy slot is readable and protected by the existing forms/stack frame. -/
theorem Pre.gotIn (h : Pre L rows bl Fm SL m0) : In m0 (gotAddr "memcpy") 8 := by
  have hg := h.got.1 "memcpy" (by simp)
  exact ⟨h.got.mapped (by simp), hg.2.1,
    hg.2.2.2 (reg m0 .rsi, formsBytes) (by simp), hg.2.2.1⟩

/-- Match the raw copy call using preserved loader bytes, not a direct-call rewrite. -/
theorem St.mt_copy (h : Pre L rows bl Fm SL m0)
    {O : BitVec 64 → Prop} {V : Nat → UInt64} {D : List (Sym × Nat)} {m : MachineData}
    (hst : St m0 O V D 8 m) (hO : ∀ q, O q → outs m0 q)
    {vs : Nat → BitVec 64} {ret : BitVec 64} :
    Match (frameEnv m0 m F [(gotAddr "memcpy", 8)] vs ret) copyS m := by
  have hm := St.mt hst (rest := [(gotAddr "memcpy", 8)])
    (vs := vs) (ret := ret) (sizes := [12040, 8])
    (labels := []) (bounds := []) (aliases := [(.gotSlot "memcpy", 1, 0)])
    ⟨rfl, rfl, trivial⟩ trivial trivial ⟨(BitVec.add_zero _).symm, trivial⟩
  apply hm.withKnownBytes (r := 1) (off := 0) (n := 8) (v := .label "memcpy")
  intro i hi
  simp only [Env.ofMachine_mem0, Env.base_ofMachine_eq,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some, Nat.zero_add, Sym.eval]
  have hs := got_keep h.got h.stack
    (writes := [(reg m0 .rsi, formsBytes)])
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; simp)
    (by intro a ha; rcases List.mem_singleton.mp ha with rfl; exact h.forms_nw)
    (NativeRustcVm.SameOutside.mono hst.same (fun q hq => hq.elim
      (fun ho => Or.inl ⟨_, List.mem_singleton_self _, hO q ho⟩) Or.inr))
  rw [hs "memcpy" (by simp) i hi]
  exact h.got.byte (by simp) hi

/-- The stack arguments' aliases hold. -/
theorem argAliases_ok {m : MachineData} {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} :
    AllOf (fun p ↦ p.1.eval (frameEnv m0 m F ((rspOf m0 + 8#64, 88) :: rest) vs ret) =
      (frameEnv m0 m F ((rspOf m0 + 8#64, 88) :: rest) vs ret).base p.2.1 +
        BitVec.ofInt 64 p.2.2) argAliases := by
  refine allOf_of fun p hp ↦ ?_
  simp only [argAliases, List.mem_map, List.mem_range] at hp
  obtain ⟨i, -, rfl⟩ := hp
  exact NativeRustcVmX64.Bus.alias_arg (F := F) i

end

/-! ## `eq_above`'s head -/

section
variable [Labels] (env : Env)

/-- `sub; cmovb 0`: the saturating difference. -/
theorem ev_sat (a b z : Sym) (hz : z.eval env = 0#64) :
    ((Sym.ite (.cmp .ult .W64 a b) z (.bin .sub .W64 a b)).eval env).toNat =
      (a.eval env).toNat - (b.eval env).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc
  · rw [hz]; simp; omega
  · rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]

/-- `shr %cl; cmp $64; cmovae 0`: `shr`. -/
theorem ev_shr (x s z : Sym) (hz : z.eval env = 0#64) :
    ((Sym.ite (.not (.cmp .ult .W64 s (.lit 64))) z (.bin .shr .W64 x s)).eval env).toNat =
      (x.eval env).toNat >>> (s.eval env).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  have hr := (x.eval env).isLt
  split <;> rename_i hc <;> simp only [Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not] at hc
  · rw [hz, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega)
        (by rw [show (BitVec.ofNat 64 64).toNat = 64 from rfl] at hc; omega)))]
    rfl
  · rw [show (BitVec.ofNat 64 64).toNat = 64 from rfl] at hc
    have hs : shiftCount .W64 (s.eval env) = (s.eval env).toNat := by
      show ((s.eval env).setWidth 8).toNat &&& 63 = _
      rw [BitVec.toNat_setWidth, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [hs]
    exact BitVec.toNat_ushiftRight _ _

/-- `shl $4; add; cmovb 8`: the point's rest, or `8`. -/
theorem ev_above (n s p e : Sym) (he : e.eval env = 8#64) :
    (Sym.ite (.cmp .ult .W64 n s) e (.bin .add .W64 p (.bin .shl .W64 s (.lit 4)))).eval env =
      if (n.eval env).toNat < (s.eval env).toNat then 8#64
      else p.eval env + BitVec.ofNat 64 (16 * (s.eval env).toNat) := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.ult]
  by_cases hc : (n.eval env).toNat < (s.eval env).toNat
  · simp only [hc, decide_true, ↓reduceIte, he]
  · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    have h4 : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := rfl
    rw [h4]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 4 = 16 from rfl, Nat.mul_comm]

end

end

end NativeRustcVmX64.Bus.AccumulateSide
