module

public import NativeRustcArm.SphincsVerify.Parse.Glue

/-!
# Helpers for the parse's loops

`keepsRegs`, `writesIn`, `keepsRegs_regs`, `count_loop`, `alias_neg`, `bv_lin`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

public section

theorem add_ofNat_zero (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := by simp

/-- `S` keeps `S₀`'s SP and the registers `rs`, which `S₀` knows. -/
@[expose] def keepsRegs (rs : List XReg) (S₀ S : SState) : Bool :=
  S.sp == S₀.sp && rs.all fun x => (S₀.reg x).isSome && S.reg x == S₀.reg x

/-- The writes are in region 0, between `lo` and `hi`. -/
@[expose] def writesIn (S : SState) (lo hi : Nat) : Bool :=
  S.mem.all fun w => w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)

section
variable [Labels]

/-- What a block keeps of registers and SP. -/
theorem keepsRegs_regs {env : Env} {rs : List XReg} {S₀ S : SState} {m m' : MachineData}
    (hm : Match env S₀ m) (hm' : Match env S m') (h : keepsRegs rs S₀ S = true) :
    m'.regs.SP = m.regs.SP ∧ ∀ x ∈ rs, m'.regs.getXReg x = m.regs.getXReg x := by
  simp only [keepsRegs, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨Match.sp_eq hm hm' h.1, fun x hx => ?_⟩
  obtain ⟨hs, he⟩ := h.2 x hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact Match.reg_eq hm hm' hv (he.trans hv)

end

/-- **A counted loop**: from turn `j < N` in `P j`, each turn reaches the exit `Q` or turn
`j + 1 < N`. -/
theorem count_loop {σ : Type} {tr : σ → (σ → Prop) → Prop} {Q : σ → Prop} {P : Nat → σ → Prop}
    (N : Nat) (step : ∀ j s, j < N → P j s → Eventually tr (fun s' => Q s' ∨ (j + 1 < N ∧ P (j + 1) s')) s) :
    ∀ {j s}, j < N → P j s → Eventually tr Q s := by
  intro j s hj h
  refine loop (fun n s => ∃ j, j < N ∧ n = N - j ∧ P j s) (fun n s ⟨j, hj, hn, h⟩ => ?_)
    ⟨j, hj, rfl, h⟩
  refine eventually_weaken _ _ _ _ (fun s' h' => ?_) (step j s hj h)
  rcases h' with hq | ⟨hj', hp⟩
  · exact Or.inl hq
  · exact Or.inr ⟨N - (j + 1), by omega, j + 1, hj', rfl, hp⟩

/-- An address a negative constant below another. -/
theorem alias_neg {A B : BitVec 64} (k : Nat) (h : A + BitVec.ofNat 64 k = B) :
    A = B + BitVec.ofInt 64 (-(k : Int)) := by
  subst h
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.add_assoc]
  simp

/-- Linear arithmetic of addresses: the frame's and the inputs', with constants (`BitVec.ofNat`). -/
macro "bv_lin" : tactic => `(tactic| (
  try simp only [Run.off, Run.sigPtr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  try simp only [show MemWidth.W64.bits = 64 from rfl]
  omega))

end

end NativeRustcArm.SphincsVerifyProof.Parse
