module

public import NativeRustcX64.Sym
public import NativeRustcX64.Spec.Mem

/-!
# What `memcpy`'s and `memset`'s proofs share

The alignment test's meaning (`align_or`: where `testb $7` of an OR of 32-bit values with the
length is zero, so are the length's low three bits); `testq x, x` (`eval_test_self`); a loop
iteration extending the bytes written so far (`extend`); mapped bytes staying mapped
(`Mapped.of_kept`); a base-plus-index address (`ix`, `eval_ix`); and the final `retq`
(`ret_then`): from RSP at the entry's, with the return address's bytes as at entry, to the
entry's return address with RSP 8 above, memory and RAX unchanged.
-/

namespace NativeRustcX64.Mem

open NativeRustcX64.Sym

public section

theorem mod8_of_bits (x : BitVec 64) (h0 : x.getLsbD 0 = false) (h1 : x.getLsbD 1 = false)
    (h2 : x.getLsbD 2 = false) : x.toNat % 8 = 0 := by
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not] at h0 h1 h2
  omega

section
variable [Labels] {env : Env}

/-- The test `orl …, %e?x; testb $7, %?l` over the length `C`: where it is zero, so are `C`'s low
three bits. -/
theorem align_or {C X : Sym}
    (h : (SBool.cmp .eq .W8 (.bin .and .W8 (.bin .or .W32 (.un .trunc .W32 C) X) (.lit 7))
      (.lit 0)).eval env = true) :
    (C.eval env).toNat % 8 = 0 := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, UnOp.apply, low, ext,
    beq_iff_eq] at h
  apply mod8_of_bits
  · have := congrArg (fun x : BitVec 8 => x.getLsbD 0) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.1
  · have := congrArg (fun x : BitVec 8 => x.getLsbD 1) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.1
  · have := congrArg (fun x : BitVec 8 => x.getLsbD 2) h
    simp at this
    simpa [BitVec.getLsbD_eq_getElem] using this.1

/-- `testq x, x` sets ZF when `x` is zero. -/
theorem eval_test_self (x : Sym) :
    (SBool.cmp .eq .W64 (.bin .and .W64 x x) (.lit 0)).eval env = (x.eval env == 0#64) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]

end

/-- The address `(b,i)` (base plus index, scale 1), as the executor builds it. -/
@[expose] def ix (b i : Reg64) : Sym := .bin .add .W64 (.reg b) (.reg i)

theorem eval_ix [Labels] (env : Env) (b i : Reg64) :
    (ix b i).eval env = env.regs b + env.regs i := by
  simp [ix, Sym.eval, BinOp.apply]

theorem bytesAt_nil (d : DataMem) (a : BitVec 64) : BytesAt d a [] := fun _ h => absurd h (by simp)

theorem sameOutside_of_eq {d d' : DataMem} (h : d' = d) (R : BitVec 64 → Prop) :
    SameOutside d d' R := fun _ _ => by rw [h]

/-- Mapped bytes of a memory are mapped in one that keeps it. -/
theorem Mapped.of_kept {d d' : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n)
    (hk : Kept d d') : Mapped d' a n :=
  fun i hi => hk _ (h i hi)

theorem ofNat_toNat_eq {x : BitVec 64} {i : Nat} (h : x.toNat = i) : x = BitVec.ofNat 64 i := by
  subst h
  exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm

/-- **One iteration of a loop writing `f`'s bytes**: from the bytes `f 0 … f (i-1)` at `d` (memory
otherwise `m₀`'s), a step writing `f i … f (i+w-1)` after them and nothing else gives the bytes
`f 0 … f (i+w-1)` at `d`, memory otherwise `m₀`'s. -/
theorem extend {m₀ st st' : DataMem} {d : BitVec 64} {i w n : Nat} {f : Nat → UInt8}
    (hnw : NoWrap d n) (hle : i + w ≤ n)
    (hc : BytesAt st d ((List.range i).map f)) (hs : SameOutside m₀ st (InRange d i))
    (hw : ∀ j < w, st'.get? (d + BitVec.ofNat 64 (i + j)) = some (f (i + j)))
    (hout : ∀ a : BitVec 64, ¬(d.toNat + i ≤ a.toNat ∧ a.toNat < d.toNat + i + w) →
      st'.get? a = st.get? a) :
    BytesAt st' d ((List.range (i + w)).map f) ∧ SameOutside m₀ st' (InRange d (i + w)) := by
  unfold NoWrap at hnw
  constructor
  · intro j hj
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    by_cases hji : j < i
    · rw [hout _ (by rw [toNat_add_ofNat d j (by omega)]; omega)]
      have := hc j (by simp; omega)
      simpa using this
    · have := hw (j - i) (by omega)
      rw [show i + (j - i) = j by omega] at this
      exact this
  · intro a ha
    rw [inRange_iff (by omega)] at ha
    rw [hout a (by omega), hs a (by rw [inRange_iff (by omega)]; omega)]

/-! ## The final `retq` -/

/-- The symbolic state the `retq` block starts in: the 8 bytes at RSP, region 0. -/
@[expose] def sRet : SState := init [8] [(.rsp, .ptr 0 0)]

section
variable [Host]

/-- **The final `retq`**, from a state with RSP at the entry's and the return address's bytes as
at entry. -/
theorem ret_then {ds : List Directive} {k : Nat} {S' : SState} (hk : ds.IsInfixAt Host.prog k)
    (hx : exec ds sRet = some (S', .ret (.load 0 0 8))) (hrsp : S'.reg .rsp = some (.ptr 0 8))
    (hrax : S'.reg .rax = some (.reg .rax)) (hmem : S'.mem = []) (hkeeps : keeps sRet S' = true)
    {m : MachineData} {st : MachineState} (hpc : st.pc = Host.addrOf k) (hstk : StackOk m 0)
    (hsp : st.data.regs.get64 .rsp = rspOf m)
    (hslot : ∀ i < 8, st.data.dmem.get? (rspOf m + BitVec.ofNat 64 i) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 i)) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m ∧
      rspOf st'.data = rspOf m + 8#64 ∧ st'.data.dmem = st.data.dmem ∧
      reg st'.data .rax = reg st.data .rax ∧ Saved st.data st'.data) st := by
  obtain ⟨-, hnw, hmap⟩ := hstk
  rw [show rspOf m - BitVec.ofNat 64 0 = rspOf m from BitVec.sub_zero _] at hmap
  let env := Env.ofMachine st.data [(rspOf m, 8)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨fun i hi => by
        show (st.data.dmem.get? (rspOf m + _)).isSome = true
        rw [hslot i hi]
        exact hmap i (by omega), by unfold NoWrap; exact hnw⟩,
      trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env sRet st.data := match_ofMachine ⟨rfl, trivial⟩
    ⟨show st.data.regs.get64 .rsp = (Sym.ptr 0 0).eval env by
      simp [Sym.eval, env, hsp], trivial⟩ trivial trivial trivial
  have hread := hm.read hwf (r := 0) (o := 0) (n := 8) rfl (by decide) (by decide)
  refine exec_at hk hx hwf (fun _ h => nomatch h) hpc hm fun st' hm' hpc' =>
    .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    have hb : env.base 0 + BitVec.ofNat 64 0 = rspOf m := by simp [env]
    rw [hb] at hread
    rw [loadInt_congr hslot] at hread
    exact (retOf_of_loadInt hread).symm
  · have h := hm'.regs .rsp _ hrsp
    simp only [Sym.eval, env, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h
    exact h
  · exact (hm'.dmem_eq hwf hmem)
  · exact Match.reg_eq hm hm' rfl hrax
  · exact Match.saved hm hm' hwf rfl hkeeps

end

end

end NativeRustcX64.Mem
