/-
  LeanVM.Guest.Backend.Sound.Calls

  What the instructions of a call, of a loop helper's closing call and of a fused dispatch give:
  the callee's frame, entered with the caller's argument words, and the callee's relation.
-/

module

public import LeanVM.Guest.Backend.Sound.Lays

/-!
# Calls

The three placed statements that enter another frame, each read from its meaning
(`PStmt.Sem`) alone, the cells of its plumbing known:

* `call_node`: a call stores the arguments through the callee's frame pointer, a registered
  loop's own pointer past them, and the return registers (this frame's own for a tail call);
  so the callee's frame holds the argument words from cell `2`, its precondition holds
  (`PlaceEnv.pre`), it returns to the instruction after the jump (`retRegs`), and its
  postcondition gives the core call on the argument and return words (`PlaceEnv.post`);
* `loopNext_node`: a registered loop's closing call copies them into the next frame of the run,
  at `fp · g^S`, whose return registers are this frame's;
* `dispatch_node`: a fused `match` of calls on one shared frame jumps through the shared table
  at the selector, in range, to the callee the core relation names.

`enter_callee` is their common end: a frame holding the argument words, the callee's entry and
the return registers give the callee's relation and the continuation.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K}

/-! ## Runs of instructions -/

theorem segHolds_cons {o : LOp} {os : List LOp} {pos : ℕ} :
    SegHolds Γ fp (o :: os) pos ↔
      Holds Γ.L (Γ.pc0 + pos) fp (Γ.R o) ∧ SegHolds Γ fp os (pos + 1) := by
  constructor
  · intro h
    refine ⟨h 0 (Nat.zero_lt_succ _), fun i hi => ?_⟩
    have := h (i + 1) (Nat.succ_lt_succ hi)
    have e : Γ.pc0 + (pos + 1) + i = Γ.pc0 + pos + (i + 1) := by omega
    rw [e]
    exact this
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero => exact h0
    | succ i =>
        have := h1 i (Nat.lt_of_succ_lt_succ hi)
        have e : Γ.pc0 + (pos + 1) + i = Γ.pc0 + pos + (i + 1) := by omega
        rw [e] at this
        exact this

theorem segHolds_append {a b : List LOp} {pos : ℕ} :
    SegHolds Γ fp (a ++ b) pos ↔ SegHolds Γ fp a pos ∧ SegHolds Γ fp b (pos + a.length) := by
  induction a generalizing pos with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.add_zero, iff_and_self]
      exact fun _ _ h => absurd h (Nat.not_lt_zero _)
  | cons o os ih =>
      rw [List.cons_append, segHolds_cons, segHolds_cons, ih, List.length_cons, and_assoc]
      have : pos + 1 + os.length = pos + (os.length + 1) := by omega
      rw [this]

theorem segHolds_pos {ops : List LOp} {pos pos' : ℕ} (h : SegHolds Γ fp ops pos)
    (e : pos = pos') : SegHolds Γ fp ops pos' := e ▸ h

/-- Instruction `k` of a run made of a list, one instruction an element. -/
theorem segHolds_zipIdx {l : List ℕ} {f : ℕ × ℕ → LOp} {pos : ℕ}
    (h : SegHolds Γ fp (l.zipIdx.map f) pos) (k : ℕ) (hk : k < l.length) :
    Holds Γ.L (Γ.pc0 + pos + k) fp (Γ.R (f (l[k], k))) := by
  have := h k (by simpa using hk)
  simpa using this

/-! ## What the instructions of a frame's plumbing say -/

theorem holds_deref_read {pc p off o : ℕ} (h : Holds Γ.L pc fp (Γ.R (.deref p off o .cell))) :
    Γ.L.read ((wd Γ.L fp p).limb 0 * addressOfIndex off) = Γ.L.read (fp * addressOfIndex o) := by
  obtain ⟨pw, v, hp, _, ho, hr⟩ := h
  rw [wd_of_read hp, ho]
  exact hr

theorem holds_deref_pc {pc p off o : ℕ} (h : Holds Γ.L pc fp (Γ.R (.deref p off o .pc))) :
    Γ.L.read ((wd Γ.L fp p).limb 0 * addressOfIndex off) =
      some (ofK (addressOfIndex (pc + 2))) := by
  obtain ⟨pw, v, hp, _, ho, hr⟩ := h
  rw [wd_of_read hp, hr, derefSource_pc]

/-- A copy into the next frame: the cell there holds what this frame's cell does. -/
theorem holds_mulNext {pc a one c : ℕ} (h : Holds Γ.L pc fp (Γ.R (.mulNextFrame a one c)))
    (hone : wd Γ.L fp one = 1) :
    Γ.L.read (fp * addressOfIndex Γ.frame * addressOfIndex c) =
      Γ.L.read (fp * addressOfIndex a) := by
  obtain ⟨va, vb, ha, hb, hc⟩ := h
  have hb1 : vb = 1 := by rw [← wd_of_read hb]; exact hone
  rw [hb1, mul_one] at hc
  rw [ha, ← hc, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]

theorem holds_set_entry {pc o : ℕ} {f : String} (hpow : Γ.l.PowOk) (hlt : Γ.ent f < 2 ^ 128)
    (h : Holds Γ.L pc fp (Γ.R (.set o (.entry f)))) :
    wd Γ.L fp o = ofK (addressOfIndex (Γ.ent f)) :=
  (wd_of_read h).trans (Γ.l.immediateWord_pow hpow hlt)

theorem holds_set_local {pc o i : ℕ} (hpow : Γ.l.PowOk) (hlt : Γ.pc0 + i < 2 ^ 128)
    (h : Holds Γ.L pc fp (Γ.R (.set o (.local i)))) : wd Γ.L fp o = Γ.tgt i :=
  (wd_of_read h).trans (Γ.l.immediateWord_pow hpow hlt)

theorem holds_set_frame {pc o : ℕ} (hpow : Γ.l.PowOk) (hlt : Γ.frame < 2 ^ 128)
    (h : Holds Γ.L pc fp (Γ.R (.set o .frameSize))) :
    wd Γ.L fp o = ofK (addressOfIndex Γ.frame) :=
  (wd_of_read h).trans (Γ.l.immediateWord_pow hpow hlt)

/-- A table read: the cell holds the slot at the selector. -/
theorem holds_slot {pc x first dst : ℕ} (h : Holds Γ.L pc fp (Γ.R (.slot x first dst))) :
    IsInK (wd Γ.L fp x) ∧ Γ.L.read ((wd Γ.L fp x).limb 0 *
      addressOfIndex (Γ.l.tablesBase + first)) = some (wd Γ.L fp dst) :=
  holds_deref (pc := pc) (Γ := Γ) (p := x) (off := Γ.l.tablesBase + first) (o := dst) h

/-- A jump, in the words of its cells. -/
theorem jumpAt_wd {oc od of : ℕ} {fall : Prop} {taken : E → E → Prop}
    (h : JumpAt Γ fp oc od of fall taken) :
    IsInK (wd Γ.L fp oc) ∧ IsInK (wd Γ.L fp of) ∧ (wd Γ.L fp oc = 0 → fall) ∧
      (wd Γ.L fp oc ≠ 0 → taken (wd Γ.L fp od) (wd Γ.L fp of)) := by
  obtain ⟨c, d, f, hc, hd, hf, hcK, _, hfK, h0, h1⟩ := h
  rw [wd_of_read hc, wd_of_read hd, wd_of_read hf]
  exact ⟨hcK, hfK, h0, h1⟩

theorem wd_of_eq {κ' : ℕ} {L : MemoryImage κ'} {fp' : K} {o : ℕ} {a : K}
    (h : fp' * addressOfIndex o = a) : wd L fp' o = (L.read a).getD 0 := by
  rw [wd, h]

theorem frameWords_eq {L : MemoryImage κ} {fp' : K} {o n : ℕ} {ws : List E} (hlen : ws.length = n)
    (h : ∀ k (hk : k < ws.length), wd L fp' (o + k) = ws[k]) : frameWords L fp' o n = ws := by
  apply List.ext_getElem (by simp [frameWords, hlen])
  intro k h1 h2
  simp only [frameWords, List.getElem_map, List.getElem_range]
  exact h k h2

theorem isInK_limb {x : E} (h : IsInK x) : x = ofK (x.limb 0) := by
  rw [ofK_eq_ofLimbs, ofLimbs_of_isInK h]

/-! ## Entering a callee -/

section

variable {ctx : Ctx} {C : CallRel} {U : String → List E → Prop} {slots : Array KVal} {B : ℕ}

/-- **A frame holding the argument words, the callee's entry and the return registers**: the
callee's contract gives its relation on those words and the continuation. -/
theorem enter_callee (env : PlaceEnv Γ fp ctx C U slots B) {f : String} {n r : ℕ}
    (hcal : isCallee ctx.sigs n r f = true) {fp' : K} {argsW : List E}
    (hargs : frameWords Γ.L fp' 2 n = argsW)
    (hself : (ctx.loops[f]?).any (·.registered) = true → wd Γ.L fp' (2 + n) = ofK fp')
    (hU : U f argsW) {ret : Option (Registers K)} {k : Prop} {d fw : E}
    (hd : d = ofK (addressOfIndex (Γ.ent f))) (hfw : fw.limb 0 = fp')
    (hret : retRegs Γ.L fp' = ret) (hcs : CallSem Γ f ret k d fw) :
    C f argsW (frameWords Γ.L fp' (2 + n) r) ∧ k := by
  subst hfw hargs
  obtain ⟨hpost, hk⟩ := hcs hd (env.pre f n r _ hcal hself hU) hret
  exact ⟨env.post f n r _ hcal hpost, hk⟩

/-- **A call**: its condition is in `K`; at zero the code goes on, and at a nonzero condition,
the callee's precondition `U` holding of the argument words, the callee's relation holds on the
argument and return words and the code goes on after the returned words are read (or, for a tail
call, the frame has returned). -/
theorem call_node (env : PlaceEnv Γ fp ctx C U slots B) {hints : List LHint} {c : CallSite}
    {pos : ℕ} {N : Prop} {kj : E → E → Prop} {kretP : Prop} {khalt : E → E → Prop}
    (hcal : isCallee ctx.sigs c.args.length c.rets.length c.callee = true)
    (hloop : (ctx.loops[c.callee]?).any (·.registered) = true → c.loop.isSome = true)
    (htail : c.tail = true → c.rets = [])
    (hsem : PStmt.Sem Γ fp (.call hints c) pos N kj kretP khalt) :
    IsInK (wd Γ.L fp c.oc) ∧ (wd Γ.L fp c.oc = 0 → N) ∧
      (wd Γ.L fp c.oc ≠ 0 → U c.callee (c.args.map (wd Γ.L fp)) →
        C c.callee (c.args.map (wd Γ.L fp)) (c.rets.map (wd Γ.L fp)) ∧
          (if c.tail then kretP else N)) := by
  simp only [PStmt.Sem] at hsem
  obtain ⟨hpre, hj⟩ := hsem
  obtain ⟨hK, hfK, hfall, htaken⟩ := jumpAt_wd hj
  refine ⟨hK, fun h0 => (hfall h0).2, fun hne hU => ?_⟩
  unfold callPre at hpre
  obtain ⟨hset', hrest⟩ := segHolds_append.mp hpre
  obtain ⟨hAL, hrets₀⟩ := segHolds_append.mp hrest
  obtain ⟨hstores, hloopS⟩ := segHolds_append.mp hAL
  have hset := (segHolds_cons.mp hset').1
  have hrets : SegHolds Γ fp (if c.tail then [LOp.deref c.nfp 1 1 .cell, LOp.deref c.nfp 0 0 .cell]
      else [LOp.deref c.nfp 1 0 .fp, LOp.deref c.nfp 0 0 .pc])
      (pos + 1 + c.args.length + (if c.loop.isSome then 1 else 0)) := by
    refine segHolds_pos hrets₀ ?_
    simp only [List.length_append, List.length_map, List.length_zipIdx, List.length_cons,
      List.length_nil]
    cases c.loop.isSome <;> simp
    omega
  have hnfp := isInK_limb hfK
  have hargs : frameWords Γ.L ((wd Γ.L fp c.nfp).limb 0) 2 c.args.length =
      c.args.map (wd Γ.L fp) := by
    refine frameWords_eq (by simp) fun k hk => ?_
    have hk' : k < c.args.length := by simpa using hk
    have := holds_deref_read (segHolds_zipIdx hstores k hk')
    rw [List.getElem_map, wd, wd]
    exact congrArg (fun o => Option.getD o 0) this
  have hself : (ctx.loops[c.callee]?).any (·.registered) = true →
      wd Γ.L ((wd Γ.L fp c.nfp).limb 0) (2 + c.args.length) = ofK ((wd Γ.L fp c.nfp).limb 0) := by
    intro hreg
    rw [hloop hreg] at hloopS
    have := holds_deref_read (segHolds_cons.mp hloopS).1
    rw [wd, ← hnfp]
    exact congrArg (fun o => Option.getD o 0) this
  have hd := holds_set_entry env.pow (env.entLt _ _ _ hcal) hset
  have hgo := htaken hne
  cases ht : c.tail with
  | true =>
      rw [ht] at hgo hrets
      simp only [↓reduceIte] at hgo hrets ⊢
      obtain ⟨h1, hr⟩ := segHolds_cons.mp hrets
      obtain ⟨h0, -⟩ := segHolds_cons.mp hr
      have hret : retRegs Γ.L ((wd Γ.L fp c.nfp).limb 0) = retRegs Γ.L fp := by
        unfold retRegs
        rw [holds_deref_read h1, holds_deref_read h0]
      obtain ⟨hC, hk⟩ := enter_callee env hcal hargs hself hU hd rfl hret hgo
      refine ⟨?_, hk⟩
      rw [htail ht] at hC ⊢
      simpa [frameWords] using hC
  | false =>
      rw [ht] at hgo hrets
      simp only [Bool.false_eq_true, ↓reduceIte] at hgo hrets ⊢
      obtain ⟨h1, hr⟩ := segHolds_cons.mp hrets
      obtain ⟨h0, -⟩ := segHolds_cons.mp hr
      have hret : retRegs Γ.L ((wd Γ.L fp c.nfp).limb 0) =
          some ⟨addressOfIndex (Γ.pc0 + (pos + (callPre c).length + 1)), fp⟩ := by
        refine retRegs_of_ofK ?_ (holds_deref_fp h1).2
        rw [holds_deref_pc h0, callPre_length]
        congr 3
        omega
      obtain ⟨hC, hsegs, hN⟩ := enter_callee env hcal hargs hself hU hd rfl hret hgo
      refine ⟨?_, hN⟩
      have hrw : frameWords Γ.L ((wd Γ.L fp c.nfp).limb 0) (2 + c.args.length) c.rets.length =
          c.rets.map (wd Γ.L fp) := by
        refine frameWords_eq (by simp) fun k hk => ?_
        have hk' : k < c.rets.length := by simpa using hk
        have := holds_deref_read (segHolds_zipIdx hsegs k hk')
        rw [List.getElem_map, wd, wd]
        simp only [argBase] at this
        rw [show 2 + c.args.length + k = 2 + c.args.length + k from rfl]
        exact congrArg (fun o => Option.getD o 0) this
      rw [hrw] at hC
      exact hC

/-- **A registered loop's closing call**: the next frame of the run, at `fp · g^S`, holds the
argument words and its own pointer, and returns where this frame does. -/
theorem loopNext_node (env : PlaceEnv Γ fp ctx C U slots B) {hints : List LHint} {callee : String}
    {nfp entry oc one : Cell} {args : List Cell} {pos : ℕ} {N : Prop} {kj : E → E → Prop}
    {kretP : Prop} {khalt : E → E → Prop}
    (hcal : isCallee ctx.sigs args.length 0 callee = true) (hone : wd Γ.L fp one = 1)
    (hnfp : wd Γ.L fp nfp = ofK (fp * addressOfIndex Γ.frame))
    (hsem : PStmt.Sem Γ fp (.loopNext hints callee nfp entry oc one args) pos N kj kretP khalt) :
    IsInK (wd Γ.L fp oc) ∧ (wd Γ.L fp oc = 0 → N) ∧
      (wd Γ.L fp oc ≠ 0 → U callee (args.map (wd Γ.L fp)) →
        C callee (args.map (wd Γ.L fp)) [] ∧ kretP) := by
  simp only [PStmt.Sem] at hsem
  obtain ⟨hpre, hj⟩ := hsem
  obtain ⟨hK, -, hfall, htaken⟩ := jumpAt_wd hj
  refine ⟨hK, hfall, fun hne hU => ?_⟩
  unfold loopPre at hpre
  obtain ⟨hA, hT⟩ := segHolds_append.mp hpre
  obtain ⟨hset', hcopies⟩ := segHolds_append.mp hA
  have hset := (segHolds_cons.mp hset').1
  obtain ⟨hm1, hT1⟩ := segHolds_cons.mp hT
  obtain ⟨hm2, hT2⟩ := segHolds_cons.mp hT1
  obtain ⟨hm3, -⟩ := segHolds_cons.mp hT2
  have hlimb : (wd Γ.L fp nfp).limb 0 = fp * addressOfIndex Γ.frame := by rw [hnfp]; simp
  have hargs : frameWords Γ.L (fp * addressOfIndex Γ.frame) 2 args.length =
      args.map (wd Γ.L fp) := by
    refine frameWords_eq (by simp) fun k hk => ?_
    have hk' : k < args.length := by simpa using hk
    have := holds_mulNext (segHolds_zipIdx hcopies k hk') hone
    rw [List.getElem_map, wd, wd]
    exact congrArg (fun o => Option.getD o 0) this
  have hself : wd Γ.L (fp * addressOfIndex Γ.frame) (2 + args.length) =
      ofK (fp * addressOfIndex Γ.frame) := by
    have := holds_mulNext hm1 hone
    rw [← hnfp, wd, wd]
    exact congrArg (fun o => Option.getD o 0) this
  have hret : retRegs Γ.L (fp * addressOfIndex Γ.frame) = retRegs Γ.L fp := by
    unfold retRegs
    rw [holds_mulNext hm2 hone, holds_mulNext hm3 hone]
  have hd := holds_set_entry env.pow (env.entLt _ _ _ hcal) hset
  have := enter_callee (r := 0) env hcal hargs (fun _ => hself) hU hd hlimb hret (htaken hne)
  simpa [frameWords] using this

/-- **A fused `match` of calls**: at a selector in range, the table jump enters the callee the
selector names, on the shared frame. -/
theorem dispatch_node (env : PlaceEnv Γ fp ctx C U slots B) {hints : List LHint}
    {callees : List String} {nfp joinCell x entry one : Cell} {first : ℕ} {args rets : List Cell}
    {pos : ℕ} {N : Prop} {kj : E → E → Prop} {kretP : Prop} {khalt : E → E → Prop}
    (hB : pos + (args.length + 5 + rets.length) ≤ B)
    (hcal : ∀ f ∈ callees, isCallee ctx.sigs args.length rets.length f = true)
    (hnreg : ∀ f ∈ callees, (ctx.loops[f]?).any (·.registered) = false)
    (hone : wd Γ.L fp one = 1) {j : ℕ} (hj : j < callees.length)
    (hx : wd Γ.L fp x = ofK (addressOfIndex j))
    (hslot : slots[first + j]? = some (.entry callees[j]))
    (hU : U callees[j] (args.map (wd Γ.L fp)))
    (hsem : PStmt.Sem Γ fp (.dispatch hints callees nfp joinCell x entry one first args rets) pos N
      kj kretP khalt) :
    C callees[j] (args.map (wd Γ.L fp)) (rets.map (wd Γ.L fp)) ∧ N := by
  simp only [PStmt.Sem] at hsem
  obtain ⟨hpre, hjmp⟩ := hsem
  obtain ⟨-, hfK, -, htaken⟩ := jumpAt_wd hjmp
  have hmem : callees[j] ∈ callees := List.getElem_mem hj
  have hgo := htaken (by rw [hone]; exact one_ne_zero) callees[j] hmem
  unfold dispatchPre at hpre
  obtain ⟨hA, hT⟩ := segHolds_append.mp hpre
  obtain ⟨hstores, hfpS⟩ := segHolds_append.mp hA
  have hfps := (segHolds_cons.mp hfpS).1
  obtain ⟨hsetj, hT1⟩ := segHolds_cons.mp hT
  obtain ⟨hderj, hT2⟩ := segHolds_cons.mp hT1
  obtain ⟨hsl, -⟩ := segHolds_cons.mp hT2
  have hargs : frameWords Γ.L ((wd Γ.L fp nfp).limb 0) 2 args.length = args.map (wd Γ.L fp) := by
    refine frameWords_eq (by simp) fun k hk => ?_
    have hk' : k < args.length := by simpa using hk
    have := holds_deref_read (segHolds_zipIdx hstores k hk')
    rw [List.getElem_map, wd, wd]
    exact congrArg (fun o => Option.getD o 0) this
  have hd : wd Γ.L fp entry = ofK (addressOfIndex (Γ.ent callees[j])) := by
    have hread := (holds_slot hsl).2
    rw [hx] at hread
    have e : (ofK (addressOfIndex j)).limb 0 * addressOfIndex (Γ.l.tablesBase + first) =
        addressOfIndex (Γ.l.tablesBase + (first + j)) := by
      simp only [limb_ofK, Fin.val_zero, ↓reduceIte, addressOfIndex, ← pow_add]
      congr 1
      omega
    rw [e, env.jt (first + j) _ _ hslot rfl] at hread
    exact (Option.some.inj hread).symm.trans
      (Γ.l.immediateWord_pow env.pow (env.entLt _ _ _ (hcal _ hmem)))
  have hret : retRegs Γ.L ((wd Γ.L fp nfp).limb 0) =
      some ⟨addressOfIndex (Γ.pc0 + (pos + args.length + 5)), fp⟩ := by
    refine retRegs_of_ofK ?_ (holds_deref_fp hfps).2
    rw [holds_deref_read hderj]
    exact (show Γ.L.read (fp * addressOfIndex joinCell) = some _ from hsetj).trans
      (congrArg some (Γ.l.immediateWord_pow env.pow (by
        show _ < 2 ^ 128
        have := env.pcLt
        omega)))
  obtain ⟨hC, hsegs, hN⟩ := enter_callee env (hcal _ hmem) hargs
    (fun h => by rw [hnreg _ hmem] at h; cases h) hU hd rfl hret hgo
  refine ⟨?_, hN⟩
  have hrw : frameWords Γ.L ((wd Γ.L fp nfp).limb 0) (2 + args.length) rets.length =
      rets.map (wd Γ.L fp) := by
    refine frameWords_eq (by simp) fun k hk => ?_
    have hk' : k < rets.length := by simpa using hk
    have := holds_deref_read (segHolds_zipIdx hsegs k hk')
    rw [List.getElem_map, wd, wd]
    exact congrArg (fun o => Option.getD o 0) this
  rw [hrw] at hC
  exact hC

end

end
end LeanVM.Guest.Backend
