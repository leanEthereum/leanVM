module

public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcVmX64.Transcript.Arith

/-!
# What `push_claim`, `ladder`, `commit_stack` and `read_ood` share (x86-64)

- A tail call's epilogue (`tail_restored`): the slots reloaded, RSP back at the entry's.
- The return address of a state with the entry's RSP and bytes there (`retOf_eq`).
- Writes a block's state holds as words (`WritesW`, `wordAt_writesW`): each pair `(o, v)`, the
  word `v` at offset `o` of a region.
- A region's pointer plus an offset (`eval_ptr_off`); AL's test of `TEST AL, AL` after a `bool`
  (`tag8_eval`); `stack_log > 30` (`big_false`); `sampleChallenges`' length.
-/

namespace NativeRustcVmX64.Layout.Stack

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript

@[expose] public section

/-- Each `(o, v)`: the eight bytes at offset `o` of region `r` are `v`'s, by the newest writes. -/
def WritesW (r : Nat) (l : List (Nat × Sym)) (S : SState) : Bool :=
  l.all fun p ↦ (List.range 8).all fun t ↦ findWrite r (p.1 + t) S.mem == some (p.2, t)

end

public section

variable {m0 d d' : MachineData} {F : Nat} {slots : Slots}

/-- **A tail call's epilogue** restores the registers: `Saved`, RSP the entry's. -/
theorem tail_restored [Labels] {o : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hf : Frame m0 F slots o d)
    (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hl : slotsLoaded slots S = true)
    (hk : keepsOthers slots S = true) (hsp : S.reg .rsp = some (.ptr 0 (F : Int))) :
    Saved m0 d' ∧ rspOf d' = rspOf m0 := by
  have hslot : ∀ p ∈ slots, reg d' p.2 = reg m0 p.2 := by
    intro p hp
    unfold slotsLoaded at hl
    rw [List.all_eq_true] at hl
    have := hm.regs p.2 _ (by simpa using hl p hp)
    rw [Sym.eval, load_ofMachine (o := p.1) rfl (hf.slot p hp)] at this
    exact this
  refine ⟨⟨fun r hr ↦ ?_, kept_trans hf.kept (hm.kept hwf)⟩, ?_⟩
  · cases hs : slots.any (·.2 == r)
    · have := hm.regs r _ (keepsOthers_spec hk hr hs)
      rw [Sym.eval, Env.ofMachine_regs] at this
      exact this.trans (hf.regs r hr hs)
    · obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp hs
      rw [← Reg64.eq_of_beq hpr]
      exact hslot p hp
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0, off_frame_F]

/-- The return address of a state with the entry's RSP whose bytes there are the frame's. -/
theorem retOf_eq {o : Nat} (hf : Frame m0 F slots o d) (hd : d'.dmem = d.dmem)
    (hsp : rspOf d' = rspOf m0) : retOf d' = retOf m0 :=
  Arrays.retOf_congr hsp fun j hj ↦ by
    rw [hd, ← frame_add F j]; exact hf.ret j hj

/-- **Words written**: each pair of `WritesW r l S`, a word at its offset of region `r`. -/
theorem wordAt_writesW [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz)) {l : List (Nat × Sym)}
    (hW : WritesW r l S = true) {o : Nat} {v : Sym} (hov : (o, v) ∈ l) (hle : o + 8 ≤ sz) :
    NativeRustcVm.WordAt m.dmem (off b o) (UInt64.ofBitVec (v.eval env)) := by
  unfold WritesW at hW
  rw [List.all_eq_true] at hW
  have h := hW _ hov
  rw [List.all_eq_true] at h
  exact wordAt_write hm hb hle fun t ht ↦ by simpa using h t (List.mem_range.mpr ht)

/-- A word given as a number. -/
theorem wordAt_nat {d : DataMem} {a : BitVec 64} {x : UInt64} {n : Nat}
    (h : NativeRustcVm.WordAt d a x) (hx : x.toNat = n) : NativeRustcVm.WordAt d a n.toUInt64 := by
  rw [← hx, show x.toNat.toUInt64 = x from UInt64.toNat.inj (by simp)]; exact h

/-- Region `i`'s base plus a nonnegative offset. -/
theorem eval_ptr_off [Labels] {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {i n : Nat} {b : BitVec 64}
    (hb : regions[i]? = some (b, n)) (o : Nat) :
    (Sym.ptr i (o : Int)).eval (Env.ofMachine m regions vars ret) = off b o := by
  rw [Sym.eval, Env.base_ofMachine m regions vars ret hb, BitVec.ofInt_natCast]

/-- `TEST CL, CL` of `MOV ECX, EAX`: AL is `0`. -/
theorem tag8_eval (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (UnOp.apply .trunc .W32 x) (UnOp.apply .trunc .W32 x))
      (BitVec.ofNat 64 0) = decide (x.toNat % 256 = 0) := by
  have h1 : (low .W8 (BinOp.apply .and .W8 (UnOp.apply .trunc .W32 x)
      (UnOp.apply .trunc .W32 x))).toNat = x.toNat % 256 := by
    simp only [BinOp.apply, BitVec.and_self, low_ext]
    rw [toNat_low]
    exact trunc32_mod x
  have h2 : (low .W8 (BitVec.ofNat 64 0)).toNat = 0 := by rw [toNat_low]; rfl
  rw [CmpOp.apply, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, h1, h2]

/-- `TEST AL, AL`: AL is `0`. -/
theorem and8_eval (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x x) (BitVec.ofNat 64 0) = decide (x.toNat % 256 = 0) := by
  have h1 : (low .W8 (BinOp.apply .and .W8 x x)).toNat = x.toNat % 256 := by
    simp only [BinOp.apply, BitVec.and_self, low_ext]
    rw [toNat_low]; rfl
  have h2 : (low .W8 (BitVec.ofNat 64 0)).toNat = 0 := by rw [toNat_low]; rfl
  rw [CmpOp.apply, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, h1, h2]

/-- `x > c` (`JA`) fails for `x ≤ c`. -/
theorem le_false (x : BitVec 64) (c : Nat) (hc : c < 2 ^ 64) (h : x.toNat ≤ c) :
    ((!CmpOp.apply .ult .W64 x (BitVec.ofNat 64 c)) &&
      !CmpOp.apply .eq .W64 x (BitVec.ofNat 64 c)) = false := by
  rcases Nat.lt_or_ge x.toNat c with h' | h'
  · have e : CmpOp.apply .ult .W64 x (BitVec.ofNat 64 c) = true := by
      simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt hc]; omega
    rw [e]; rfl
  · have e : x = BitVec.ofNat 64 c := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]; omega
    have e2 : CmpOp.apply .eq .W64 x (BitVec.ofNat 64 c) = true := by
      simp only [CmpOp.apply, low_W64, e, beq_self_eq_true]
    rw [e2, Bool.not_true, Bool.and_false]

/-- `stack_log > 30` fails for `stack_log ≤ 30`. -/
theorem big_false (x : BitVec 64) (h : x.toNat ≤ 30) :
    ((!CmpOp.apply .ult .W64 x (BitVec.ofNat 64 30)) &&
      !CmpOp.apply .eq .W64 x (BitVec.ofNat 64 30)) = false := by
  rcases Nat.lt_or_ge x.toNat 30 with h' | h'
  · have e : CmpOp.apply .ult .W64 x (BitVec.ofNat 64 30) = true := by
      simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    rw [e]; rfl
  · have e : x = BitVec.ofNat 64 30 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
    subst e; decide

/-- `sampleChallenges n` returns `n` challenges. -/
theorem sampleChallenges_size {n : Nat} {s s' : NativeVm.Model.TState}
    {xs : Array NativeVm.Model.EW}
    (h : (NativeVm.Model.sampleChallenges n).run s = some (xs, s')) : xs.size = n := by
  have key : ∀ (l : List Nat) (acc : Array NativeVm.Model.EW) (s s' : NativeVm.Model.TState)
      (xs : Array NativeVm.Model.EW),
      (l.foldlM (fun acc _ ↦ do pure (acc.push (← NativeVm.Model.sampleChallenge))) acc :
        NativeVm.Model.VM (Array NativeVm.Model.EW)).run s =
        some (xs, s') → xs.size = acc.size + l.length := by
    intro l
    induction l with
    | nil =>
      intro acc s s' xs h
      simp only [List.foldlM_nil, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; simp
    | cons x l ih =>
      intro acc s s' xs h
      simp only [List.foldlM_cons, StateT.run_bind] at h
      cases hr : (NativeVm.Model.sampleChallenge.run s) with
      | none =>
        simp only [bind, StateT.run] at h hr
        simp [hr] at h
      | some p =>
        obtain ⟨x, s1⟩ := p
        simp only [bind, StateT.run] at h hr
        simp only [hr, pure, StateT.pure, Option.bind_some] at h
        have := ih _ _ _ _ h
        simp at this
        simp; omega
  have := key (List.range n) #[] s s' xs h
  simpa using this

end

end NativeRustcVmX64.Layout.Stack
