module

public import NativeRustcX64.Sym.Smart

/-!
# Symbolic flags are sound

The symbolic flags of `ADD`, `SUB`/`CMP`, the logical instructions, `INC`, `DEC`, `NEG` and of a
result (`flagsOk_result`, `flagsOk_add`, `flagsOk_sub`) are Kraken's, with the carry of a
subtraction as an unsigned comparison and its zero flag as an equality; a symbolic condition is
Kraken's condition code on the flags (`eval_condSym`).
-/

namespace NativeRustcX64.Sym

public section

theorem sub_beq_zero {n : Nat} (x y : BitVec n) : ((x - y) == BitVec.zero n) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact bv_sub_eq_zero x y

theorem subs_carry {n : Nat} (x y : BitVec n) :
    ((x - y).unsigned == x.unsigned - y.unsigned) = !x.ult y := by
  simp only [BitVec.unsigned, BitVec.ult, BitVec.toNat_sub]
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : x.toNat < y.toNat
  · have h1 : ((2 ^ n - y.toNat + x.toNat) % 2 ^ n : Nat) = 2 ^ n - y.toNat + x.toNat := by
      apply Nat.mod_eq_of_lt
      omega
    simp only [h1, decide_eq_true h, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    omega
  · have h1 : ((2 ^ n - y.toNat + x.toNat) % 2 ^ n : Nat) = x.toNat - y.toNat := by
      rw [show 2 ^ n - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [h1, decide_eq_false h, Bool.not_false, beq_iff_eq]
    omega

theorem sub_carry {n : Nat} (x y : BitVec n) :
    ((x - y).unsigned != x.unsigned - y.unsigned) = x.ult y := by
  rw [bne, subs_carry, Bool.not_not]

variable [Labels] (env : Env)

/-- The flags of a result: ZF and SF of `v`, CF and OF as `cf` and `of` say. -/
theorem flagsOk_result {w : Width} {r : Sym} {v : w.type} (hr : r.eval env = ext w v)
    {cf of : Option SBool} {rem : StatusFlags.from_result.Remaining}
    (hcf : ∀ b, cf = some b → rem.cf = b.eval env) (hof : ∀ b, of = some b → rem.of = b.eval env) :
    FlagsOk env (resultFlags w r cf of) (StatusFlags.from_result v rem) := by
  refine ⟨hcf, fun b hb => ?_, fun b hb => ?_, hof⟩
  · cases hb
    rw [eval_mkCmp]
    simp only [CmpOp.apply, hr, low_ext, Sym.eval, low_zero]
    rfl
  · cases hb
    rw [eval_mkMsb, hr, low_ext]
    rfl

theorem flagsOk_add {w : Width} (a b : Sym) {rem : StatusFlags.from_result.Remaining}
    (hcf : rem.cf = ((low w (a.eval env) + low w (b.eval env)).unsigned !=
      (low w (a.eval env)).unsigned + (low w (b.eval env)).unsigned))
    (hof : rem.of = ((low w (a.eval env) + low w (b.eval env)).signed !=
      (low w (a.eval env)).signed + (low w (b.eval env)).signed)) :
    FlagsOk env (addFlags w a b)
      (StatusFlags.from_result (low w (a.eval env) + low w (b.eval env)) rem) :=
  flagsOk_result env (by rw [eval_mkBin]; rfl)
    (fun _ h => by cases h; rw [eval_mkCmp, hcf]; rfl)
    (fun _ h => by cases h; rw [eval_mkCmp, hof]; rfl)

theorem flagsOk_sub {w : Width} (a b : Sym) {rem : StatusFlags.from_result.Remaining}
    (hcf : rem.cf = ((low w (a.eval env) - low w (b.eval env)).unsigned !=
      (low w (a.eval env)).unsigned - (low w (b.eval env)).unsigned))
    (hof : rem.of = ((low w (a.eval env) - low w (b.eval env)).signed !=
      (low w (a.eval env)).signed - (low w (b.eval env)).signed)) :
    FlagsOk env (subFlags w a b)
      (StatusFlags.from_result (low w (a.eval env) - low w (b.eval env)) rem) := by
  refine ⟨fun c h => ?_, fun c h => ?_, fun c h => ?_, fun c h => ?_⟩
  · cases h
    rw [eval_mkCmp]
    show rem.cf = _
    rw [hcf, sub_carry]
    rfl
  · cases h
    rw [eval_mkCmp]
    show (_ == BitVec.zero _) = _
    rw [sub_beq_zero]
    rfl
  · cases h
    rw [eval_mkMsb, eval_mkBin]
    show _ = (low w (ext w _)).msb
    rw [low_ext]
    rfl
  · cases h
    rw [eval_mkCmp]
    show rem.of = _
    rw [hof]
    rfl

theorem flagsOk_logic {w : Width} {r : Sym} {v : w.type} (hr : r.eval env = ext w v) (af : Bool) :
    FlagsOk env (logicFlags w r) (StatusFlags.from_result v { cf := false, af, of := false }) :=
  flagsOk_result env hr (fun _ h => by cases h; rfl) (fun _ h => by cases h; rfl)

/-- **A symbolic condition is Kraken's condition code.** -/
theorem eval_condSym {cc : CondCode} {f : SFlags} {c : SBool} {st : StatusFlags}
    (hf : FlagsOk env f st) (h : condSym cc f = some c) : c.eval env = cc.interp st := by
  obtain ⟨hc, hz, hs, ho⟩ := hf
  cases cc with
  | o => exact (ho c h).symm
  | c => exact (hc c h).symm
  | z => exact (hz c h).symm
  | s => exact (hs c h).symm
  | no =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [eval_mkNot, ← ho b hb]
    rfl
  | nc =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [eval_mkNot, ← hc b hb]
    rfl
  | nz =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [eval_mkNot, ← hz b hb]
    rfl
  | ns =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [eval_mkNot, ← hs b hb]
    rfl
  | p => cases h
  | np => cases h
  | be =>
    simp only [condSym, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [eval_mkOr, ← hc x hx, ← hz y hy]
    rfl
  | a =>
    simp only [condSym, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [eval_mkAnd, eval_mkNot, eval_mkNot, ← hc x hx, ← hz y hy]
    rfl
  | l =>
    simp only [condSym, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [eval_mkNot, eval_mkBeq, ← hs x hx, ← ho y hy]
    rfl
  | ge =>
    simp only [condSym, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [eval_mkBeq, ← hs x hx, ← ho y hy]
    rfl
  | le =>
    simp only [condSym, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, z, hz', rfl⟩ := h
    rw [eval_mkOr, eval_mkNot, eval_mkBeq, ← hs x hx, ← ho y hy, ← hz z hz']
    rfl
  | g =>
    simp only [condSym, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, z, hz', rfl⟩ := h
    rw [eval_mkAnd, eval_mkNot, eval_mkBeq, ← hs x hx, ← ho y hy, ← hz z hz']
    rfl

end

end NativeRustcX64.Sym
