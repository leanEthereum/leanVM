module

public import NativeRustcVmArm.Bus.Common
public import NativeRustcVmArm.Sumcheck.Ctx
public import NativeRustcVm.Transcript.Update
public import NativeRustcVmArm.Spec.Sumcheck
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# The sumcheck loop: what its three instances share

`TState::sumcheck` (with `sumcheck_plain`'s, `gkr_step`'s or `verify_layer`'s closure) keeps a
frame of `F` bytes (`Ring.Fr`, outputs `outsOf`: the `Option<EW>` at `out`, the `n` slots at `sl`,
the `TState` at `t`), the message at `frame + 8` (80 bytes) and the `Option<EW>` `eq` at
`frame + 88` (24 bytes), the saved registers above `112` (`Geo`). A round: `sumcheck_round_poly`
(`Geo.roundPolyPre`, `Geo.afterRoundPoly`), `squeeze` (`Geo.squeezePre`, `Geo.afterSqueeze`),
the challenge into its slot, `poly_eval` (`Geo.polyEvalPre`, `Geo.afterPolyEval`). After `i`
rounds the model's run (`Rounds`).
-/

namespace NativeRustcVmArm.Sumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Sumcheck

@[expose] public section

/-- The outputs of a sumcheck: the `Option<EW>` at `out`, the `n` slots at `sl`, the
`TState` at `t`. -/
def outsOf (t out sl : BitVec 64) (n : Nat) (q : BitVec 64) : Prop :=
  InRange out 24 q ∨ InRange sl (16 * n) q ∨ InRange t tstateBytes q

/-- After `i` rounds of `sumcheckFn claim count E` from `s`: the claim `c`, the challenges in the
first `i` slots at `sl`, the `TState` at `t` the state. -/
def Rounds (d : Mem 64) (t : BitVec 64) (a : DecArea) (sl : BitVec 64) (claim : EW) (count : Nat)
    (E : Nat → Option EW) (s : TState) (i : Nat) (c : EW) : Prop :=
  ∃ xs si, (sumcheckFn claim count E i).run s = some ((xs, c), si) ∧ xs.size = i ∧
    NativeRustcVm.EWsAt d sl xs.toList ∧ TStateAt d t a si

/-- A sumcheck's frame: `F` bytes, the callees' stacks below it, the message and `eq` below the
saved registers' slots. -/
structure Geo [Labels] (a : DecArea) (s : TState) (m0 : MachineData) (t out sl : BitVec 64)
    (count n N F : Nat) (slots : List (Nat × XReg)) (outs : BitVec 64 → Prop) : Prop where
  ok : SumcheckOk a s m0 t out sl count n N
  osub : ∀ q, outs q → outsOf t out sl n q
  ot : ∀ q, InRange t tstateBytes q → outs q
  osl : ∀ q, InRange sl (16 * n) q → outs q
  le : F + sumcheckCallStack ≤ N
  al : F % 16 = 0
  f112 : 112 ≤ F
  sl : ∀ p ∈ slots, 112 ≤ p.1 ∧ p.1 + 8 ≤ F

end

public section

theorem sumcheckCallStack_eq : sumcheckCallStack = 720 := by decide

/-- **A call through the frame** that writes its stack, outputs among the frame's and `w` bytes
of the frame at `o`, below its slots. -/
theorem frCallLocal {m0 m m' : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} (h : Fr m0 F N slots keep outs m) {N' o w : Nat}
    {outs' : BitVec 64 → Prop} (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N) (how : o + w ≤ F)
    (hkeep : ∀ r ∈ keep, calleeSaved r = true) (hsl : ∀ p ∈ slots, o + w ≤ p.1 ∧ p.1 + 8 ≤ F)
    (houts : ∀ q, outs' q → outs q) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hS : Saved m m')
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (base m0 F + BitVec.ofNat 64 o) w q ∨
      outs' q ∨ InRange (stackBelow m N') N' q) :
    Fr m0 F N slots keep outs m' := by
  have hsb := stackBelow_eq h.sp (N' := N') (by omega)
  have hlt := m0.regs.SP.toNat_lt
  have hbF := base_toNat (m0 := m0) (F := F) (by omega)
  have hbN := base_toNat (m0 := m0) (F := N) hN
  have hbF' := base_toNat (m0 := m0) (F := F + N') (by omega)
  have hnwN := base_noWrap (m0 := m0) (F := N) hN
  have hnwF := base_noWrap (m0 := m0) (F := F) (by omega)
  have hnw' : NoWrap (base m0 (F + N')) N' := by unfold NoWrap; rw [hbF']; omega
  have hoff : (base m0 F + BitVec.ofNat 64 o).toNat = (base m0 F).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hnwo : NoWrap (base m0 F + BitVec.ofNat 64 o) w := by unfold NoWrap; rw [hoff]; omega
  refine h.step hS.2.1 (fun r hr ↦ hS.1 r (hkeep r hr)) hS.2.2 hs (fun q hq ↦ ?_) ?_
  · rcases hq with hq | hq | hq
    · left
      rw [Sym.inRange_iff hnwo, hoff] at hq
      rw [Sym.inRange_iff hnwN, hbN]
      omega
    · exact .inr (houts q hq)
    · left
      rw [hsb, Sym.inRange_iff hnw', hbF'] at hq
      rw [Sym.inRange_iff hnwN, hbN]
      omega
  · intro p hp i hi hq
    obtain ⟨hp1, hp8⟩ := hsl p hp
    have hq' : base m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
        base m0 F + BitVec.ofNat 64 (p.1 + i) := NativeRustcVm.addr_add_add _ _ _
    have hpi : (base m0 F + BitVec.ofNat 64 (p.1 + i)).toNat = (base m0 F).toNat + p.1 + i := by
      rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega
    rw [hq'] at hq
    rcases hq with hq | hq | hq
    · rw [Sym.inRange_iff hnwo, hoff, hpi] at hq
      omega
    · refine hfr _ (houts _ hq) ?_
      rw [Sym.inRange_iff hnwF, hpi]
      omega
    · rw [hsb, Sym.inRange_iff hnw', hbF', hpi] at hq
      omega


/-- **A block of the frame without writes**, run from `init [(F, true)] (.ptr 0 0)`: the frame
and the memory kept. -/
theorem frBlock [Labels] {m0 m m' : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} (h : Fr m0 F N slots keep outs m)
    (hS : StackOk m0 N) (hF : F ≤ N) (h16 : F % 16 = 0) {S' : SState}
    (hm' : Match (Env.ofMachine m [(base m0 F, F)]) S' m') (hmem : S'.mem = [])
    (hsp : S'.sp = .ptr 0 0)
    (hkeep0 : keep.all (fun r ↦ (init [(F, true)] (.ptr 0 0)).reg r == some (.reg r)) = true)
    (hkeep : keep.all (fun r ↦ S'.reg r == some (.reg r)) = true) :
    Fr m0 F N slots keep outs m' ∧ m'.dmem = m.dmem := by
  have hwf := Bus.wf_frame hS hF h.kept
  have hm := Bus.match_frame hS hF h16 h.sp
  exact ⟨Fr.ofBlock h hm hm' hwf rfl hmem (by rw [hsp]; rfl) fun r hr ↦
    ⟨.reg r, beq_iff_eq.mp (List.all_eq_true.mp hkeep0 r hr),
      beq_iff_eq.mp (List.all_eq_true.mp hkeep r hr)⟩, hm'.dmem_eq hwf hmem⟩

section
variable [Labels] {a : DecArea} {s : TState} {m0 m m' : MachineData} {t out sl : BitVec 64}
  {count n N F : Nat} {slots : List (Nat × XReg)} {keep : List XReg} {outs : BitVec 64 → Prop}

namespace Geo

variable (g : Geo a s m0 t out sl count n N F slots outs)
include g

theorem ctx : Ctx m0 t a N F :=
  ⟨g.ok.1, g.ok.2.1, g.ok.2.2.2.1, g.ok.2.2.1.footprint, by have := g.le; omega, g.al⟩

theorem hN : N ≤ m0.regs.SP.toNat := g.ok.1.2.1

theorem outOk : OutOk m0 t a out 24 N := g.ok.2.2.2.2.2.2.1

theorem slOk : OutOk m0 t a sl (16 * n) N := g.ok.2.2.2.2.2.2.2.1

theorem stack_noWrap : NoWrap (stackBelow m0 N) N := Bus.stack_noWrap g.ok.1

theorem outs_not_rc {q : BitVec 64} (hq : outsOf t out sl n q) : ¬InRange rcAddr 192 q := by
  have c := g.ctx
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange g.outOk.2.2.2.2.2 g.outOk.2.1 c.rc.2.1 hq
  · exact NativeRustcVm.Apart.not_inRange g.slOk.2.2.2.2.2 g.slOk.2.1 c.rc.2.1 hq
  · exact c.not_rc_tstate hq

theorem outs_not_frame {q : BitVec 64} (hq : outsOf t out sl n q) : ¬InRange (base m0 F) F q := by
  have c := g.ctx
  have hnw : NoWrap (base m0 F) F := base_noWrap (by have := c.spN; have := c.le; omega)
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange (apart_frame c.spN c.le g.outOk.2.2.2.2.1) g.outOk.2.1
      hnw hq
  · exact NativeRustcVm.Apart.not_inRange (apart_frame c.spN c.le g.slOk.2.2.2.2.1) g.slOk.2.1
      hnw hq
  · exact NativeRustcVm.Apart.not_inRange (apart_frame c.spN c.le c.tok.1) c.fp.1.2 hnw hq

theorem at_ (h : Fr m0 F N slots keep outs m) : At m0 F m :=
  ⟨h.sp, h.kept, fun q hq ↦ h.same q fun h' ↦
    h'.elim (fun hs ↦ g.ctx.not_rc_stack hs hq) (fun ho ↦ g.outs_not_rc (g.osub _ ho) hq)⟩

/-- A byte of the frame is in the stack. -/
theorem frame_stack {o w : Nat} (how : o + w ≤ F) {q : BitVec 64}
    (hq : InRange (base m0 F + BitVec.ofNat 64 o) w q) : InRange (stackBelow m0 N) N q := by
  have c := g.ctx
  have := c.spN; have := c.le
  have hl := m0.regs.SP.toNat_lt
  have hoff := c.frame_toNat (o := o) (by omega)
  have hnwo : NoWrap (base m0 F + BitVec.ofNat 64 o) w := by
    unfold NoWrap; rw [show base m0 F = frAt m0 F from rfl, hoff]; omega
  rw [Sym.inRange_iff hnwo, show base m0 F = frAt m0 F from rfl, hoff] at hq
  rw [Sym.inRange_iff g.stack_noWrap, c.stk]
  omega

/-- The slots are apart from the stack, the `TState` and the output. -/
theorem not_sl {q : BitVec 64}
    (hq : InRange (stackBelow m0 N) N q ∨ InRange t tstateBytes q ∨ InRange out 24 q) :
    ¬InRange sl (16 * n) q := by
  have ho := g.slOk
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange ho.2.2.2.2.1.symm g.stack_noWrap ho.2.1 hq
  · exact NativeRustcVm.Apart.not_inRange ho.2.2.1.symm g.ctx.fp.1.2 ho.2.1 hq
  · exact NativeRustcVm.Apart.not_inRange g.ok.2.2.2.2.2.2.2.2 g.outOk.2.1 ho.2.1 hq

/-- The `TState` and its area are apart from the stack, the slots and the output. -/
theorem not_t {q : BitVec 64}
    (hq : InRange (stackBelow m0 N) N q ∨ InRange sl (16 * n) q ∨ InRange out 24 q) :
    ¬InRange t tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have c := g.ctx
  rcases hq with hq | hq | hq
  · exact ⟨NativeRustcVm.Apart.not_inRange c.tok.1.symm g.stack_noWrap c.fp.1.2 hq,
      NativeRustcVm.Apart.not_inRange c.tok.2.1.symm g.stack_noWrap c.fp.2.1.2 hq⟩
  · exact ⟨NativeRustcVm.Apart.not_inRange g.slOk.2.2.1 g.slOk.2.1 c.fp.1.2 hq,
      NativeRustcVm.Apart.not_inRange g.slOk.2.2.2.1 g.slOk.2.1 c.fp.2.1.2 hq⟩
  · exact ⟨NativeRustcVm.Apart.not_inRange g.outOk.2.2.1 g.outOk.2.1 c.fp.1.2 hq,
      NativeRustcVm.Apart.not_inRange g.outOk.2.2.2.1 g.outOk.2.1 c.fp.2.1.2 hq⟩

/-- **Slots kept** where the memory changed in the stack, the `TState` and the output only. -/
theorem sl_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    (hR : ∀ q, R q → InRange (stackBelow m0 N) N q ∨ InRange t tstateBytes q ∨ InRange out 24 q)
    {xs : List EW} (hlen : xs.length ≤ n) (h : NativeRustcVm.EWsAt d sl xs) :
    NativeRustcVm.EWsAt d' sl xs := by
  have hnw := g.slOk.2.1
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hRq ↦ g.not_sl (hR _ hRq) ?_
  rw [NativeRustcVm.length_ewsBytes] at hi
  unfold NoWrap at hnw
  exact NativeRustcVm.inRange_add (by omega) (by omega)

/-- **The `TState` kept** where the memory changed in the stack, the slots and the output only. -/
theorem t_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    (hk : Kept d d')
    (hR : ∀ q, R q → InRange (stackBelow m0 N) N q ∨ InRange sl (16 * n) q ∨ InRange out 24 q)
    {s' : TState} (h : TStateAt d t a s') : TStateAt d' t a s' :=
  h.frame (fun p hp ↦ hk p hp) (fun q hq ↦ g.not_t (hR q hq)) hs

/-- **Bytes of the frame kept** across a call whose changes are outputs and its stack. -/
theorem local_keep (h : Fr m0 F N slots keep outs m) {N' : Nat}
    (hle : F + N' ≤ N) {R : BitVec 64 → Prop} (hR : ∀ q, R q → outs q)
    (hs : SameOutside m.dmem m'.dmem fun q ↦ R q ∨ InRange (stackBelow m N') N' q)
    {o : Nat} {bs : List UInt8} (hob : o + bs.length ≤ F)
    (hb : NativeRustcVm.BytesAt m.dmem (base m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m'.dmem (base m0 F + BitVec.ofNat 64 o) bs := by
  have c := g.ctx
  have hat := g.at_ h
  have := c.spN; have := c.le
  have hl := m0.regs.SP.toNat_lt
  refine NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ ?_
  have hin : InRange (base m0 F) F (base m0 F + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
    rw [NativeRustcVm.addr_add_add]
    have hnw := c.noWrap_fr
    unfold NoWrap at hnw
    exact NativeRustcVm.inRange_add (by omega) (by omega)
  rcases hq with hq | hq
  · exact g.outs_not_frame (g.osub _ (hR _ hq)) hin
  · have := c.apart_frame (o := 0) (n := F) hat hle (by omega)
    rw [NativeRustcVm.addr_add_zero] at this
    exact NativeRustcVm.Apart.not_inRange this c.noWrap_fr (by
      unfold NativeRustcVm.NoWrap; have hs' := c.spN' hat
      rw [toNat_stackBelow (by rw [hs']; omega)]; omega) hin hq

/-! ## The calls of a round -/

/-- `sumcheck_round_poly`'s precondition from the frame. -/
theorem roundPolyPre (h : Fr m0 F N slots keep outs m) {si : TState}
    {e : Option EW} (hts : TStateAt m.dmem t a si)
    (he : OptEWAt m.dmem (base m0 F + BitVec.ofNat 64 88) e)
    (hx0 : m.regs.X0.toBitVec = t) (hx1 : m.regs.X1.toNat = count)
    (hx4 : m.regs.X4.toBitVec = base m0 F + BitVec.ofNat 64 88)
    (hx5 : m.regs.X5.toBitVec = base m0 F + BitVec.ofNat 64 8) : RoundPolyPre a si e m := by
  have c := g.ctx
  have hat := g.at_ h
  have hle : F + roundPolyStack ≤ N := by
    have := g.le; rw [sumcheckCallStack_eq] at this; rw [roundPolyStack_eq]; omega
  have := g.f112
  unfold RoundPolyPre
  rw [hx0, hx1, hx4, hx5]
  exact ⟨c.stackOk hat hle, c.rcAt hat hle, hts, c.tstateOk hat hle, g.ok.2.2.2.2.1,
    g.ok.2.2.2.2.2.1, he, c.noWrap_frame (by omega), c.apart_frame hat hle (by omega),
    c.outOk hat hle (o := 8) (n := 16 * maxCount) (by unfold maxCount; omega)⟩
where
  roundPolyStack_eq : roundPolyStack = 720 := by decide

/-- **After `sumcheck_round_poly`**: the frame (the message changed), the message and the next
state on `some`, the slots kept. -/
theorem afterRoundPoly (h : Fr m0 F N slots keep outs m) {si : TState}
    {e : Option EW} (hpost : RoundPolyPost a si e m m') (hx0 : m.regs.X0.toBitVec = t)
    (hx5 : m.regs.X5.toBitVec = base m0 F + BitVec.ofNat 64 8)
    (hkeep : ∀ r ∈ keep, calleeSaved r = true) :
    Fr m0 F N slots keep outs m' ∧
      (∀ msg s1, (sumcheckRoundPoly m.regs.X1.toNat ⟨m.regs.X2, m.regs.X3⟩ e).run si =
        some (msg, s1) → NativeRustcVm.EWsAt m'.dmem (base m0 F + BitVec.ofNat 64 8) msg.toList ∧
          TStateAt m'.dmem t a s1) ∧
      (∀ xs : List EW, xs.length ≤ n → NativeRustcVm.EWsAt m.dmem sl xs →
        NativeRustcVm.EWsAt m'.dmem sl xs) := by
  obtain ⟨-, hmsg, hnext, hs, hsv⟩ := hpost
  have c := g.ctx
  have hat := g.at_ h
  have hle : F + roundPolyStack ≤ N := by
    have := g.le; rw [sumcheckCallStack_eq] at this; rw [roundPolyPre.roundPolyStack_eq]; omega
  have := g.f112
  rw [hx0, hx5] at hs
  rw [hx5] at hmsg
  rw [hx0] at hnext
  refine ⟨frCallLocal h g.hN hle (o := 8) (w := 16 * maxCount) (by unfold maxCount; omega) hkeep
      (fun p hp ↦ ⟨by have := g.sl p hp; unfold maxCount; omega, (g.sl p hp).2⟩)
      (outs' := fun q ↦ InRange t tstateBytes q) (fun q hq ↦ g.ot q hq)
      (fun q hq ↦ g.outs_not_frame (g.osub q hq)) hsv hs,
    fun msg s1 hr ↦ ⟨hmsg msg s1 hr, hnext msg s1 hr⟩, fun xs hlen hxs ↦ g.sl_keep hs ?_ hlen hxs⟩
  intro q hq
  rcases hq with hq | hq | hq
  · exact .inl (g.frame_stack (o := 8) (w := 16 * maxCount) (by unfold maxCount; omega) hq)
  · exact .inr (.inl hq)
  · exact .inl (c.inRange_stack hat hle hq)

/-- `squeeze`'s precondition from the frame. -/
theorem squeezePre (h : Fr m0 F N slots keep outs m) {si : TState}
    (hts : TStateAt m.dmem t a si) (hx0 : m.regs.X0.toBitVec = t) :
    SqueezePre si.sponge m := by
  have c := g.ctx
  have hat := g.at_ h
  have hle : F + squeezeStack ≤ N := by
    have := g.le; rw [sumcheckCallStack_eq] at this
    rw [show squeezeStack = 432 from by decide]; omega
  unfold SqueezePre
  rw [hx0]
  exact ⟨c.stackOk hat hle, c.rcAt hat hle, c.spongeOk hat hle, hts.sponge⟩

/-- **After `squeeze`**: the frame and its bytes, the challenge in X0, X1, the `TState` with the
sponge squeezed, the slots kept. -/
theorem afterSqueeze (h : Fr m0 F N slots keep outs m) {si : TState}
    (hts : TStateAt m.dmem t a si) (hpost : SqueezePost si.sponge m m')
    (hx0 : m.regs.X0.toBitVec = t) (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl8 : ∀ p ∈ slots, p.1 + 8 ≤ F) :
    Fr m0 F N slots keep outs m' ∧
      m'.regs.X0 = si.sponge.squeeze.1.c0 ∧ m'.regs.X1 = si.sponge.squeeze.1.c1 ∧
      TStateAt m'.dmem t a { si with sponge := si.sponge.squeeze.2 } ∧
      (∀ xs : List EW, xs.length ≤ n → NativeRustcVm.EWsAt m.dmem sl xs →
        NativeRustcVm.EWsAt m'.dmem sl xs) ∧
      (∀ (o : Nat) (bs : List UInt8), o + bs.length ≤ F →
        NativeRustcVm.BytesAt m.dmem (base m0 F + BitVec.ofNat 64 o) bs →
        NativeRustcVm.BytesAt m'.dmem (base m0 F + BitVec.ofNat 64 o) bs) := by
  obtain ⟨h0, h1, hsp, hs, hsv⟩ := hpost
  have c := g.ctx
  have hat := g.at_ h
  have hle : F + squeezeStack ≤ N := by
    have := g.le; rw [sumcheckCallStack_eq] at this
    rw [show squeezeStack = 432 from by decide]; omega
  have hfp := hts.footprint
  have hnwt : NoWrap t spongeBytes := NativeRustcVm.NoWrap.mono hfp.1.2 (by show spongeBytes ≤ tstateBytes; decide)
  rw [hx0] at hsp hs
  have hR : ∀ q, InRange t spongeBytes q → InRange t tstateBytes q := fun q hq ↦
    NativeRustcVm.InRange.mono hq hnwt hfp.1.2 (Nat.le_refl _)
      (by show t.toNat + spongeBytes ≤ t.toNat + tstateBytes; unfold spongeBytes tstateBytes; omega)
  have hs' : SameOutside m.dmem m'.dmem fun q ↦ InRange t tstateBytes q ∨
      InRange (stackBelow m squeezeStack) squeezeStack q :=
    NativeRustcVm.SameOutside.mono hs fun q hq ↦ hq.elim (fun h ↦ .inl (hR q h)) .inr
  refine ⟨h.call g.hN hle hkeep hsl8 (fun q hq ↦ g.ot q hq)
      (fun q hq ↦ g.outs_not_frame (g.osub q hq))
      hsv (NativeRustcVm.SameOutside.mono hs' fun q hq ↦ hq.elim .inr .inl),
    h0, h1, ?_, fun xs hlen hxs ↦ g.sl_keep hs' (fun q hq ↦ hq.elim (fun h ↦ .inr (.inl h))
      (fun h ↦ .inl (c.inRange_stack hat hle h))) hlen hxs,
    fun o bs hob hb ↦ g.local_keep h hle (R := fun q ↦ InRange t tstateBytes q)
      (fun q hq ↦ g.ot q hq) hs' hob hb⟩
  refine hts.with_sponge (R := fun q ↦ InRange (stackBelow m squeezeStack) squeezeStack q)
    hsv.2.2 (fun q hq ↦ g.not_t (.inl (c.inRange_stack hat hle hq)))
    (NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_) hsp
  rcases hq with hq | hq
  · left
    obtain ⟨i, hi, rfl⟩ := NativeRustcVm.InRange.exists hq
    exact ⟨i, by unfold spongeBytes tstateBytes at *; omega, hi, rfl⟩
  · exact .inr hq

/-- `poly_eval`'s precondition from the frame: the message at `frame + 8`. -/
theorem polyEvalPre (h : Fr m0 F N slots keep outs m)
    (hx0 : m.regs.X0.toBitVec = base m0 F + BitVec.ofNat 64 8) (hx1 : m.regs.X1.toNat = count) :
    PolyEvalPre m := by
  have c := g.ctx
  have hat := g.at_ h
  have hle : F + polyEvalStack ≤ N := by
    have := g.le; rw [sumcheckCallStack_eq] at this
    rw [show polyEvalStack = 656 from by decide]; omega
  have := g.f112
  have hc5 := g.ok.2.2.2.2.2.1
  unfold maxCount at hc5
  refine ⟨c.stackOk hat hle, by rw [hx1]; have := g.ok.2.2.2.2.1; omega, ?_⟩
  unfold SliceOk
  rw [hx0, hx1]
  obtain ⟨hr, ho⟩ := Bus.local_ok (o := 8) (n := 16 * count) g.ok.1
    (show F + polyEvalStack ≤ N from hle) (by omega) hat.kept h.sp
  exact ⟨hr, ho⟩

/-- **After `poly_eval`**: the frame, its bytes, the slots and the `TState` kept. -/
theorem afterPolyEval (h : Fr m0 F N slots keep outs m) (hpost : PolyEvalPost m m')
    (hkeep : ∀ r ∈ keep, calleeSaved r = true) (hsl8 : ∀ p ∈ slots, p.1 + 8 ≤ F) :
    Fr m0 F N slots keep outs m' ∧
      (∀ xs : List EW, xs.length ≤ n → NativeRustcVm.EWsAt m.dmem sl xs →
        NativeRustcVm.EWsAt m'.dmem sl xs) ∧
      (∀ s' : TState, TStateAt m.dmem t a s' → TStateAt m'.dmem t a s') := by
  obtain ⟨-, hs, hsv⟩ := hpost
  have c := g.ctx
  have hat := g.at_ h
  have hle : F + polyEvalStack ≤ N := by
    have := g.le; rw [sumcheckCallStack_eq] at this
    rw [show polyEvalStack = 656 from by decide]; omega
  have hs' : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m polyEvalStack)
      polyEvalStack q := NativeRustcVm.SameOutside.mono hs fun q hq ↦ hq.elim
        (fun h ↦ absurd h (by unfold InRange; simp)) id
  refine ⟨h.call g.hN hle hkeep hsl8 (outs' := fun _ ↦ False) (fun _ h ↦ h.elim)
      (fun q hq ↦ g.outs_not_frame (g.osub q hq)) hsv
      (NativeRustcVm.SameOutside.mono hs' fun q hq ↦ .inl hq),
    fun xs hlen hxs ↦ g.sl_keep hs' (fun q hq ↦ .inl (c.inRange_stack hat hle hq)) hlen hxs,
    fun s' hts ↦ g.t_keep hs' hsv.2.2 (fun q hq ↦ .inl (c.inRange_stack hat hle hq)) hts⟩


/-! ## The slots -/

/-- Slot `i`'s address as a number. -/
theorem slot_toNat {i : Nat} (hi : i < n) :
    (sl + BitVec.ofNat 64 (16 * i)).toNat = sl.toNat + 16 * i := by
  have hnw := g.slOk.2.1
  unfold NoWrap at hnw
  exact NativeRustcVm.toNat_add_ofNat (by omega)

/-- Slot `i`: readable and apart from the stack. -/
theorem slot_ok {i : Nat} (hi : i < n) :
    Readable m0 (sl + BitVec.ofNat 64 (16 * i)) 16 ∧
      OffStack m0 (sl + BitVec.ofNat 64 (16 * i)) 16 N := by
  have ho := g.slOk
  refine ⟨⟨NativeRustcVm.Mapped.sub ho.1 (by omega), NativeRustcVm.NoWrap.sub ho.2.1 (by omega)⟩,
    ?_⟩
  unfold OffStack
  exact NativeRustcVm.Apart.mono ho.2.2.2.2.1 (by rw [g.slot_toNat hi]; omega)
    (by rw [g.slot_toNat hi]; omega) (Nat.le_refl _) (Nat.le_refl _)

/-- A byte of slot `i` is one of the slots'. -/
theorem slot_in {i j : Nat} (hi : i < n) (hj : j < 16) :
    InRange sl (16 * n) (sl + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 j) := by
  have hnw := g.slOk.2.1
  unfold NoWrap at hnw
  rw [NativeRustcVm.addr_add_add]
  exact NativeRustcVm.inRange_add (by omega) (by omega)

/-- **The first `i` slots kept** where only slot `i` changed. -/
theorem prefix_keep {d d' : Mem 64} {i : Nat} (hi : i < n)
    (hs : SameOutside d d' (InRange (sl + BitVec.ofNat 64 (16 * i)) 16)) {xs : List EW}
    (hlen : xs.length = i) (h : NativeRustcVm.EWsAt d sl xs) : NativeRustcVm.EWsAt d' sl xs := by
  have hnw := g.slOk.2.1
  unfold NoWrap at hnw
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj hq ↦ ?_
  rw [NativeRustcVm.length_ewsBytes] at hj
  have hnw' : NoWrap (sl + BitVec.ofNat 64 (16 * i)) 16 := by
    unfold NoWrap; rw [g.slot_toNat hi]; omega
  rw [Sym.inRange_iff hnw', g.slot_toNat hi, NativeRustcVm.toNat_add_ofNat (by omega)] at hq
  omega

/-- Slot `i + 1`'s address is the end's exactly at the last. -/
theorem slot_eq_end {i : Nat} (hi : i < n) :
    (sl + BitVec.ofNat 64 (16 * (i + 1)) == sl + BitVec.ofNat 64 (16 * n)) = (i + 1 == n) := by
  have hnw := g.slOk.2.1
  unfold NoWrap at hnw
  by_cases h : i + 1 = n
  · rw [h]; simp
  · have hne : BitVec.ofNat 64 (16 * (i + 1)) ≠ BitVec.ofNat 64 (16 * n) := fun he ↦ by
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      omega
    have : sl + BitVec.ofNat 64 (16 * (i + 1)) ≠ sl + BitVec.ofNat 64 (16 * n) := fun he ↦
      hne (by simpa using congrArg (fun x ↦ x - sl) he)
    simp [this, h]

end Geo

end

/-! ## The model -/

theorem rounds_zero {d : Mem 64} {t : BitVec 64} {a : DecArea} {sl : BitVec 64} {claim : EW}
    {count : Nat} {E : Nat → Option EW} {s : TState} (h : TStateAt d t a s) :
    Rounds d t a sl claim count E s 0 claim :=
  ⟨#[], s, sumcheckFn_zero claim count E s, rfl, NativeRustcVm.ewsAt_nil d sl, h⟩

/-- `n` slots after `i` of them hold the first `i` challenges, and the challenge at slot `i`. -/
theorem ewsAt_push {d : Mem 64} {sl : BitVec 64} {xs : Array EW} {x : EW}
    (h : NativeRustcVm.EWsAt d sl xs.toList)
    (hx : NativeRustcVm.EWAt d (sl + BitVec.ofNat 64 (16 * xs.size)) x) :
    NativeRustcVm.EWsAt d sl (xs.push x).toList := by
  rw [Array.toList_push, NativeRustcVm.ewsAt_append_iff, NativeRustcVm.ewsAt_singleton_iff]
  exact ⟨h, by simpa using hx⟩

/-- What a sumcheck leaves on a rejection. -/
theorem sumcheckOut_none {d : Mem 64} {t : BitVec 64} {a : DecArea} {out sl : BitVec 64}
    (h : NativeRustcVm.WordAt d out 0) : SumcheckOut d t a out sl none :=
  ⟨h, ⟨fun _ _ _ h ↦ (nomatch h), fun _ _ h ↦ (nomatch h)⟩⟩

/-- What a sumcheck leaves on a success. -/
theorem sumcheckOut_some {d : Mem 64} {t : BitVec 64} {a : DecArea} {out sl : BitVec 64}
    {xs : Array EW} {c : EW} {s' : TState} (ho : OptEWAt d out (some c))
    (hxs : NativeRustcVm.EWsAt d sl xs.toList) (hts : TStateAt d t a s') :
    SumcheckOut d t a out sl (some ((xs, c), s')) :=
  ⟨ho, ⟨fun xs' c' s'' h ↦ by cases h; exact hxs, fun x s'' h ↦ by cases h; exact hts⟩⟩

end

end NativeRustcVmArm.Sumcheck
