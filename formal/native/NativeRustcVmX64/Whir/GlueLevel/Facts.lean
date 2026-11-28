module

public import NativeRustcVmX64.Whir.GlueLevel.Head

/-!
# `glue_level`'s facts across its steps (x86-64)

The precondition's parts (`pre_*`); the bytes of an input apart from the state and the stack kept
by every step (`keep_out`); a region of the state kept by a step not writing it (`keep_reg`); the
new glued claims' addresses as the blocks compute them (`k1_eval`, …, the templates' aliases
`t4_al`, `t7_al`, `t8_al`); a callee's view of an area apart from the stack (`offStack_call`).
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Vm.GlueLevel
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

public section

variable {s : WhirStateW} {m0 : MachineData}

/-! ## The precondition -/

theorem pre_pnw (hpre : GlueLevelPre s m0) : NoWrap (pOf m0) stateBytes := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨⟨-, h⟩, -⟩, -⟩ := hpre
  exact h

theorem pre_cap (hpre : GlueLevelPre s m0) : s.glued.size + 2 ≤ gluedCap := hpre.2.2.2.1

theorem pre_size (hpre : GlueLevelPre s m0) : s.glued.size ≤ 8 := by
  have := pre_cap hpre
  unfold gluedCap at this
  omega

theorem pre_st (hpre : GlueLevelPre s m0) : WhirStateAt m0.dmem (pOf m0) s := hpre.2.2.1

/-! ## The regions -/

theorem rs_0 : (rsOf s m0)[0]? = some (off (pOf m0) 0, 16) := by simp [rsOf, offs]
theorem rs_1 : (rsOf s m0)[1]? = some (off (pOf m0) 16, 488) := by simp [rsOf, offs]
theorem rs_2 : (rsOf s m0)[2]? = some (off (pOf m0) 504, 8) := by simp [rsOf, offs]
theorem rs_3 : (rsOf s m0)[3]? = some (off (pOf m0) (o1 s.glued.size), 40) := by
  simp [rsOf, offs]
theorem rs_4 : (rsOf s m0)[4]? = some (off (pOf m0) (o1 s.glued.size + 40), 488) := by
  simp [rsOf, offs]
theorem rs_5 : (rsOf s m0)[5]? = some (off (pOf m0) (o2 s.glued.size), 40) := by
  simp [rsOf, offs]
theorem rs_6 : (rsOf s m0)[6]? = some (off (pOf m0) (o2 s.glued.size + 528), 1848) := by
  simp [rsOf, offs]
theorem rs_7 : (rsOf s m0)[7]? = some (off (pOf m0) (o2 s.glued.size + 2376), 3688) := by
  simp [rsOf, offs]

/-- The regions of a list, writable in `wrAll` (not the `α`s). -/
theorem sub_of (l : List Nat) (h : (2 ∈ l) = False) :
    ∀ r, l.contains r = true → wrAll r = true := by
  intro r hr
  have hr' : r ∈ l := by simpa using hr
  simp only [wrAll, bne_iff_ne, ne_eq]
  rintro rfl
  exact (h ▸ hr' : False)

/-! ## Bytes kept -/

/-- **An input** apart from the state and the stack: its bytes kept by any step. -/
theorem keep_out (hpre : GlueLevelPre s m0) {wr : Nat → Bool} {d d' : DataMem}
    (hs : SameOutside d d' (fun q ↦ InRange (stackBelow m0 glueLevelStack) glueLevelStack q ∨
      outsOf (rsOf s m0) wr q))
    {a : BitVec 64} {n : Nat} (hnw : NoWrap a n)
    (hst : Apart a n (stackBelow m0 glueLevelStack) (glueLevelStack + 8))
    (hap : Apart (pOf m0) stateBytes a n) : Same d d' a n :=
  (lay hpre).keep hs hnw (by unfold Apart at hst ⊢; omega) fun i e _ he ↦ by
    obtain ⟨⟨o, sz⟩, ho, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? he)
    obtain ⟨hpos, hle⟩ := offs_le _ (pre_cap hpre) _ ho
    exact NativeRustcVm.Apart.symm (apart_off_of (pre_pnw hpre) hpos hle hap)

/-- **A region of the state** kept by a step not writing it. -/
theorem keep_reg (hpre : GlueLevelPre s m0) {wr : Nat → Bool} {d d' : DataMem}
    (hs : SameOutside d d' (fun q ↦ InRange (stackBelow m0 glueLevelStack) glueLevelStack q ∨
      outsOf (rsOf s m0) wr q))
    {i : Nat} {a : BitVec 64} {n : Nat} (he : (rsOf s m0)[i]? = some (a, n))
    (hw : wr (i + 1) = false) : Same d d' a n :=
  (lay hpre).keepArr hs he hw

theorem offs_cases (n : Nat) : ∀ e ∈ offs n, e.1 + e.2 ≤ 512 ∨ o1 n ≤ e.1 := by
  simp only [offs, o1, o2, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only <;> omega

theorem pre_offStack (hpre : GlueLevelPre s m0) :
    Apart (pOf m0) stateBytes (stackBelow m0 glueLevelStack) (glueLevelStack + 8) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, h⟩, -⟩ := hpre
  exact h

/-- **The glued claims so far**: their bytes kept by any step. -/
theorem keep_old (hpre : GlueLevelPre s m0) {wr : Nat → Bool} {d d' : DataMem}
    (hs : SameOutside d d' (fun q ↦ InRange (stackBelow m0 glueLevelStack) glueLevelStack q ∨
      outsOf (rsOf s m0) wr q)) :
    Same d d' (off (pOf m0) 512) (6064 * s.glued.size) := by
  have hpnw := pre_pnw hpre
  have hn := pre_size hpre
  rcases Nat.eq_zero_or_pos s.glued.size with h0 | hpos
  · intro j hj
    rw [h0] at hj
    omega
  have hle : 512 + 6064 * s.glued.size ≤ stateBytes := by unfold stateBytes; omega
  refine (lay hpre).keep hs (noWrap_off hpnw (by omega) hle)
    (by have := apart_off_of hpnw (by omega) hle (pre_offStack hpre); unfold Apart at this ⊢; omega)
    fun i e _ he ↦ ?_
  obtain ⟨⟨o, sz⟩, ho, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? he)
  obtain ⟨hpos', hle'⟩ := offs_le _ (pre_cap hpre) _ ho
  exact apart_offs hpnw (by omega) hpos' hle hle' ((offs_cases _ _ ho).elim .inr .inl)

/-! ## Values -/

section
variable {m : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64}

theorem vars_eq (i : Nat) : (envG s m0 m vals ret).vars i = vals i := rfl
theorem vA_19 : vA s m0 19 = BitVec.ofNat 64 s.glued.size := rfl
theorem vA_22 : vA s m0 22 = BitVec.ofNat 64 s.alphas.size := rfl
theorem vA_24 : vA s m0 24 = BitVec.ofNat 64 s.glued.size + BitVec.ofNat 64 1 := rfl
theorem vA_25 : vA s m0 25 =
    (BitVec.ofNat 64 s.glued.size + BitVec.ofNat 64 1) * BitVec.ofNat 64 6064 := rfl

end

/-- An address the blocks compute, as an offset of the state. -/
macro "addr_tac" : tactic => `(tactic| (
  simp only [key1, key2, key3, Sym.eval, BinOp.apply, low_W64, ext_W64, base_1, base_4, base_5,
    base_6, base_7, base_8, vars_eq, vA_19, vA_24, vA_25]
  apply BitVec.eq_of_toNat_eq
  simp only [NativeRustcVm.Transcript.off, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt, Width.bits, o1, o2]
  omega))

section
variable [Labels]

/-- A template whose aliases are the head's. -/
theorem headA_al {T : SState} (hT : T.aliases = headA) (m : MachineData)
    (vals : Nat → BitVec 64) (ret : BitVec 64) : AliasesOk T (envG s m0 m vals ret) :=
  aliasesOk_of fun _ _ _ hx ↦ headA_ok (hT ▸ hx)

theorem t4_al (m : MachineData) (ret : BitVec 64) : AliasesOk t4 (envG s m0 m (vA s m0) ret) :=
  aliasesOk_of fun x r o hx ↦ by
    rcases List.mem_append.mp hx with hx | hx
    · exact headA_ok hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> addr_tac

theorem t7_al (m : MachineData) (ret : BitVec 64) : AliasesOk t7 (envG s m0 m (vA s m0) ret) :=
  aliasesOk_of fun x r o hx ↦ by
    rcases List.mem_append.mp hx with hx | hx
    · exact headA_ok hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> addr_tac

theorem t8_al (m : MachineData) (ret : BitVec 64) : AliasesOk t8 (envG s m0 m (vA s m0) ret) :=
  aliasesOk_of fun x r o hx ↦ by
    rcases List.mem_append.mp hx with hx | hx
    · exact headA_ok hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl, rfl⟩
    addr_tac

end

/-- **An area apart from the stack**, from a callee using `S` bytes below the frame's base. -/
theorem offStack_call (hpre : GlueLevelPre s m0) {mc : MachineData}
    (hrsp : rspOf mc = stackBelow m0 96) {a : BitVec 64} {n : Nat}
    (hap : Apart a n (stackBelow m0 glueLevelStack) (glueLevelStack + 8)) {S : Nat}
    (hS : S ≤ 144) : OffStack mc a n S := by
  unfold OffStack
  unfold Apart at *
  have hok := hpre.1
  have hsp := hok.1
  have h1 : (stackBelow m0 glueLevelStack).toNat = (rspOf m0).toNat - 240 := stackBelow_glue hok
  have h2 : (stackBelow m0 96).toNat = (rspOf m0).toNat - 96 :=
    NativeRustcVmX64.Field.stackBelow_toNat' (by unfold glueLevelStack ewMulStack at hsp; omega)
  have h3 : (stackBelow mc S).toNat = (rspOf mc).toNat - S :=
    NativeRustcVmX64.Field.stackBelow_toNat' (by
      rw [hrsp, h2]; unfold glueLevelStack ewMulStack at hsp; omega)
  rw [h3, hrsp, h2]
  rw [h1] at hap
  unfold glueLevelStack ewMulStack at *
  omega

/-- A region's layout facts. -/
theorem reg_info (hpre : GlueLevelPre s m0) {i : Nat} {a : BitVec 64} {n : Nat}
    (he : (rsOf s m0)[i]? = some (a, n)) :
    Mapped m0.dmem a n ∧ NoWrap a n ∧
      Apart a n (stackBelow m0 glueLevelStack) (glueLevelStack + 8 + 64) :=
  mem_of_allOf (lay hpre).arr (List.mem_of_getElem? he)

end

end NativeRustcVmX64.Whir.GlueLevel
