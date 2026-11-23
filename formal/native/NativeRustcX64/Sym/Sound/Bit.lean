module

public import NativeRustcX64.Sym.Operand

/-!
# Bit-test instructions are sound

`BT` and `BTS` use Kraken's modulo-width bit index, preserve ZF and retain only CF from the
new flags. Every choice of the undefined OF, SF, AF and PF is admitted. Eight-bit forms fail.
-/

namespace NativeRustcX64.Sym

public section

variable [Labels] {env : Env} {w : Width}

theorem flagsOk_bit {f : SFlags} {st : StatusFlags} (hf : FlagsOk env f st)
    (a b : Sym) (status : StatusFlags) :
    FlagsOk env ⟨some (mkCmp .bit w a b), f.zf, none, none⟩
      { status with
        cf := (low w (a.eval env)).getLsbD ((low w (b.eval env)).toNat % w.bits)
        zf := st.zf } := by
  refine ⟨?_, hf.2.1, nofun, nofun⟩
  intro c h
  cases h
  rw [eval_mkCmp]
  rfl

theorem ok_bt (base : Reg w) (offset : BitOffset w) : OpOk env (.bt base offset) := by
  intro S S' x m p _ hm h _
  change Step.bt base offset S = some (S', x) at h
  by_cases hw : (w == .W8) = true
  · rw [Step.bt, ite_pos hw] at h
    cases h
  · rw [Step.bt, ite_neg hw] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    dsimp only [Operation.interp]
    rw [ite_neg hw]
    refine hm.bitOffset hb p ?_
    rw [hm.getR ha]
    exact fun status => done_fall (hm.setFlags _ (flagsOk_bit hm.flags a b status))

theorem ok_bts (base : Reg w) (offset : BitOffset w) : OpOk env (.bts base offset) := by
  intro S S' x m p _ hm h _
  change Step.bts base offset S = some (S', x) at h
  by_cases hw : (w == .W8) = true
  · rw [Step.bts, ite_pos hw] at h
    cases h
  · rw [Step.bts, ite_neg hw] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨S₁, hS, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    dsimp only [Operation.interp]
    rw [ite_neg hw]
    refine hm.bitOffset hb p ?_
    rw [hm.getR ha]
    intro status
    refine done_fall ((hm.setFlags _ (flagsOk_bit hm.flags a b status)).setR hS ?_)
    rw [eval_mkBin]
    rfl

end

end NativeRustcX64.Sym
