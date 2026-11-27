module

public import NativeRustcX64.Sym.Operand

/-!
# Data instructions are sound

`OpOk` for `MOV`, `MOVZX`/`MOVSX`, `LEA`, `SETcc`, `CMOVcc`, the arithmetic and logical
instructions (`ADD`, `SUB`, `AND`, `OR`, `XOR`, `CMP`, `TEST`, `INC`, `DEC`, `NEG`, `NOT`, `IMUL`)
and `BSWAP`: the symbolic step's operands, value and flags are Kraken's.
-/

namespace NativeRustcX64.Sym

public section

variable [Labels] {env : Env} {w : Width}

omit [Labels] in
/-- The steps that end in a destination write and fall through. -/
theorem step_write {S' : SState} {x : Exit} {o : Option SState}
    (h : ∃ S₁, o = some S₁ ∧ fall S₁ = some (S', x)) : o = some S' ∧ x = .fall := by
  obtain ⟨S₁, h1, h2⟩ := h
  cases h2
  exact ⟨h1, rfl⟩
theorem ok_mov (dst : Dst w) (src : Operand w) : OpOk env (.mov dst src) := by
  intro S S' x m p hwf hm h _
  change Step.mov dst src S = some (S', x) at h
  simp only [Step.mov, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  exact hm.readOp hwf hv p <| hm.writeDst hwf hS (eval_truncTo env w v) p fun _ hm' => done_fall hm'

theorem movx_ok (op : UnOp) {w' : Width} (f : w'.type → w.type)
    (hf : ∀ y, op.apply w y = ext w (f (low w' y))) {dst : Dst w} {src : RegOrMem w'}
    {S S' : SState} {x : Exit} {m : MachineData} (hwf : env.WFRo) (hm : Match env S m)
    (h : Step.movx op dst src S = some (S', x)) (p : Std.Rco Int64) :
    (src.interp m p (fun val s => s.set dst (f val) p (fun m' => .done ⟨m', p.upper⟩))).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.movx, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  exact hm.readRM hwf hv p <|
    hm.writeDst hwf hS (by rw [eval_mkUn, hf]) p fun _ hm' => done_fall hm'

theorem ok_movzx {w' : Width} (dst : Dst w) (src : RegOrMem w') : OpOk env (.movzx dst src) :=
  fun _ _ _ _ p hwf hm h _ => movx_ok (.zext w') (·.zeroExtend _) (fun _ => rfl) hwf hm h p

theorem ok_movsx {w' : Width} (dst : Dst w) (src : RegOrMem w') : OpOk env (.movsx dst src) :=
  fun _ _ _ _ p hwf hm h _ => movx_ok (.sext w') (·.signExtend _) (fun _ => rfl) hwf hm h p

theorem ok_lea (dst : Reg w) (a : AddrExpr) : OpOk env (.lea dst a) := by
  intro S S' x m p hwf hm h _
  change Step.lea dst a S = some (S', x) at h
  simp only [Step.lea, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨xa, hxa, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  have hA := hm.addr hxa p
  refine done_fall (p := p) (hm.setR hS (x := ((a.interp m.regs p).zeroExtend _)) ?_)
  rw [eval_truncTo, ← hA]
  rfl

theorem ok_setcc (cc : CondCode) (dst : Dst w) : OpOk env (.setcc cc dst) := by
  intro S S' x m p hwf hm h _
  change Step.setcc cc dst S = some (S', x) at h
  simp only [Step.setcc, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  refine hm.writeDst hwf hS ?_ p fun _ hm' => done_fall hm'
  rw [eval_mkIte, eval_condSym env hm.flags hc]
  cases CondCode.interp cc m.status <;> cases w <;> rfl

theorem ok_cmovcc (cc : CondCode) (dst : Reg w) (src : RegOrMem w) :
    OpOk env (.cmovcc cc dst src) := by
  intro S S' x m p hwf hm h _
  change Step.cmovcc cc dst src S = some (S', x) at h
  simp only [Step.cmovcc, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, c, hc, old, hold, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  unfold Operation.interp
  refine hm.readRM hwf hv p ?_
  refine done_fall (hm.setR hS ?_)
  rw [eval_mkIte, eval_condSym env hm.flags hc, eval_truncTo, eval_truncTo, hm.getR hold]
  split <;> rfl

theorem ok_add (dst : Dst w) (src : Operand w) : OpOk env (.add dst src) := by
  intro S S' x m p hwf hm h _
  change Step.add dst src S = some (S', x) at h
  simp only [Step.add, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  exact hm.readOp hwf ha p <| hm.readRM hwf hb p <|
    (hm.setFlags _ (flagsOk_add env a b (rem := ⟨_, _, _⟩) rfl rfl)).writeDst hwf hS
      (by rw [eval_mkBin]; rfl) p fun _ hm' => done_fall hm'

theorem ok_sub (dst : Dst w) (src : Operand w) : OpOk env (.sub dst src) := by
  intro S S' x m p hwf hm h _
  change Step.sub dst src S = some (S', x) at h
  simp only [Step.sub, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  exact hm.readOp hwf ha p <| hm.readRM hwf hb p <|
    (hm.setFlags _ (flagsOk_sub env b a (rem := ⟨_, _, _⟩) rfl rfl)).writeDst hwf hS
      (by rw [eval_mkBin]; rfl) p fun _ hm' => done_fall hm'

theorem logic_ok (op : BinOp) (f : w.type → w.type → w.type)
    (hf : ∀ y z, op.apply w y z = ext w (f (low w y) (low w z))) {dst : Dst w} {src : Operand w}
    {S S' : SState} {x : Exit} {m : MachineData} (hwf : env.WFRo) (hm : Match env S m)
    (h : Step.logic op dst src S = some (S', x)) (p : Std.Rco Int64) :
    (dst.interp m p (fun a s => src.interp s p (fun b s =>
      undefined (fun af =>
        { s with status := StatusFlags.from_result (f a b) { cf := false, of := false, af } }.set
          dst (f a b) p (fun m' => .done ⟨m', p.upper⟩))))).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.logic, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  have hr : (mkBin op w a b).eval env = ext w (f (low w (a.eval env)) (low w (b.eval env))) := by
    rw [eval_mkBin, hf]
  exact hm.readRM hwf ha p <| hm.readOp hwf hb p fun af =>
    (hm.setFlags _ (flagsOk_logic env hr af)).writeDst hwf hS hr p fun _ hm' => done_fall hm'

theorem ok_and (dst : Dst w) (src : Operand w) : OpOk env (.and dst src) :=
  fun _ _ _ _ p hwf hm h _ => logic_ok .and (· &&& ·) (fun _ _ => rfl) hwf hm h p

theorem ok_or (dst : Dst w) (src : Operand w) : OpOk env (.or dst src) :=
  fun _ _ _ _ p hwf hm h _ => logic_ok .or (· ||| ·) (fun _ _ => rfl) hwf hm h p

theorem ok_xor (dst : Dst w) (src : Operand w) : OpOk env (.xor dst src) :=
  fun _ _ _ _ p hwf hm h _ => logic_ok .xor (· ^^^ ·) (fun _ _ => rfl) hwf hm h p

theorem ok_cmp (a : RegOrMem w) (b : Operand w) : OpOk env (.cmp a b) := by
  intro S S' x m p hwf hm h _
  change Step.cmp a b S = some (S', x) at h
  simp only [Step.cmp, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨u, hu, v, hv, rfl, rfl⟩ := h
  unfold Operation.interp
  refine hm.readRM hwf hu p ?_
  refine hm.readOp hwf hv p ?_
  exact done_fall (hm.setFlags _ (flagsOk_sub env u v (rem := ⟨_, _, _⟩) rfl rfl))

theorem ok_test (a : RegOrMem w) (b : Operand w) : OpOk env (.test a b) := by
  intro S S' x m p hwf hm h _
  change Step.test a b S = some (S', x) at h
  simp only [Step.test, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨u, hu, v, hv, rfl, rfl⟩ := h
  unfold Operation.interp
  refine hm.readRM hwf hu p ?_
  refine hm.readOp hwf hv p ?_
  exact fun af => done_fall (hm.setFlags _ (flagsOk_logic env (by rw [eval_mkBin]; rfl) af))

theorem ok_inc (dst : RegOrMem w) : OpOk env (.inc dst) := by
  intro S S' x m p hwf hm h _
  change Step.inc dst S = some (S', x) at h
  simp only [Step.inc, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  have hr : (mkBin .add w a (.lit 1)).eval env = ext w (low w (a.eval env) + 1) := by
    rw [eval_mkBin]
    simp only [BinOp.apply, Sym.eval, low_one]
    rfl
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  exact (hm.setFlags _ (flagsOk_result env hr (rem := ⟨_, _, _⟩) (fun c hc => hm.flags.1 c hc)
    (fun _ h => by cases h; rw [eval_mkCmp]; rfl))).writeDst hwf hS hr p
      fun _ hm' => done_fall hm'

theorem ok_dec (dst : RegOrMem w) : OpOk env (.dec dst) := by
  intro S S' x m p hwf hm h _
  change Step.dec dst S = some (S', x) at h
  simp only [Step.dec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  have hr : (mkBin .sub w a (.lit 1)).eval env = ext w (low w (a.eval env) - 1) := by
    rw [eval_mkBin]
    simp only [BinOp.apply, Sym.eval, low_one]
    rfl
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  exact (hm.setFlags _ (flagsOk_result env hr (rem := ⟨_, _, _⟩) (fun c hc => hm.flags.1 c hc)
    (fun _ h => by cases h; rw [eval_mkCmp]; rfl))).writeDst hwf hS hr p
      fun _ hm' => done_fall hm'

theorem ok_neg (dst : RegOrMem w) : OpOk env (.neg dst) := by
  intro S S' x m p hwf hm h _
  change Step.neg dst S = some (S', x) at h
  simp only [Step.neg, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  have hr : (mkUn .neg w a).eval env = ext w (-low w (a.eval env)) := by
    rw [eval_mkUn]
    rfl
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  exact (hm.setFlags _ (flagsOk_result env hr (rem := ⟨_, _, _⟩)
    (fun _ h => by
      cases h
      rw [eval_mkNot, eval_mkCmp]
      simp only [CmpOp.apply, Sym.eval, low_zero]
      rfl)
    (fun _ h => by cases h; rw [eval_mkCmp]; rfl))).writeDst hwf hS hr p
      fun _ hm' => done_fall hm'

theorem ok_not (dst : Dst w) : OpOk env (.not dst) := by
  intro S S' x m p hwf hm h _
  change Step.not dst S = some (S', x) at h
  simp only [Step.not, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨hS, rfl⟩ := step_write h
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  exact hm.writeDst hwf hS (by rw [eval_mkUn]; rfl) p fun _ hm' => done_fall hm'

theorem ok_imul (dst : Option (Dst w)) (src1 : RegOrMem w) (src2 : Operand w) :
    OpOk env (.imul dst src1 src2) := by
  intro S S' x m p hwf hm h _
  change Step.imul dst src1 src2 S = some (S', x) at h
  simp only [Step.imul, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, b, hb, S₁, hS, rfl, rfl⟩ := h
  unfold Operation.interp
  refine hm.readRM hwf ha p ?_
  refine hm.readOp hwf hb p ?_
  have hv : (mkBin .mul w a b).eval env = ext w (low w (a.eval env) * low w (b.eval env)) := by
    rw [eval_mkBin]
    rfl
  cases dst with
  | none =>
    exact hm.writeDst hwf hS hv p fun _ hm' _ _ _ _ =>
      done_fall (hm'.setFlags _ (flagsOk_unknown _))
  | some d =>
    exact hm.writeDst hwf hS hv p fun _ hm' _ _ _ _ =>
      done_fall (hm'.setFlags _ (flagsOk_unknown _))

theorem ok_bswap (dst : Reg w) : OpOk env (.bswap dst) := by
  intro S S' x m p hwf hm h _
  change Step.bswap dst S = some (S', x) at h
  cases w with
  | W32 =>
    simp only [Step.bswap, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨hS, rfl⟩ := step_write h
    refine done_fall (p := p) (hm.setR hS (x := bswap32 (m.regs.get dst)) ?_)
    rw [eval_mkUn, hm.getR ha]
    rfl
  | W64 =>
    simp only [Step.bswap, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨hS, rfl⟩ := step_write h
    refine done_fall (p := p) (hm.setR hS (x := bswap64 (m.regs.get dst)) ?_)
    rw [eval_mkUn, hm.getR ha]
    rfl
  | W8 => cases h
  | W16 => cases h

end

end NativeRustcX64.Sym
