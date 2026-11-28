/-
  LeanVM.Guest.Complete.MainWinCall

  A call window's and a guarded call window's hypotheses from a callee's `AtEvery`.
-/

module

public import LeanVM.Guest.Complete.MainWinGen
public import LeanVM.Guest.Complete.MainCalleesA
public import LeanVM.Guest.Complete.MainRunFacts

/-!
# Call windows from `MainCalleesAt`'s fields

`main`'s callees are stated at every frame past a floor and every cursor past their block (`AtEvery`,
`MainCalleesAt`), ending within `β` of their cursor below `Tc` (`AtEveryB`). `end_step`: then within
`2^52` of the callees' cursor below `2^57`, as `WinsHypT` asks. `winsHypT_call_of_atEvery`: a call
window's hypotheses from such a field, at the
aligned base of the callees' cursor, its region in the window's and its precondition the window's;
the rest at every end. `winsHypT_cif_of_atEvery`: a guarded call window, the guard `1 + g^n`
(`n < 2^34`): taken when `n ≠ 0`, from the field; skipped when `n = 0`, a phantom of a callee that
`Takes` the arguments, the cursor past its tail's frame. `memT_touch`, `memT_rc`, `pureT_rc`: a touch's
and a range check's facts on counts `g^n` from their words defined.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VsC LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {al : String → Bool} {k : ℕ} {σ0 : Val} {w : ℕ → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **A callee's end within `stepB` of the callees' cursor below `stepT`**, from its end within `β` of
its own cursor below `Tc`, its block and `β` within `2^51`. -/
theorem end_step {al : String → Bool} {g : String} {kc B β Tc e : ℕ} (hTc : 2 ^ 58 ≤ Tc)
    (hβ : B + β ≤ 2 ^ 51) (hb : allocBase (al g) kc + B < Tc → e ≤ allocBase (al g) kc + B + β) :
    kc < stepT → e ≤ kc + stepB := by
  intro hk
  have h0 := stepT_eq
  have h3 := stepB_ge
  have h1 := allocBase_le (al g) kc
  have h2 := hb (by omega)
  omega

/-- A frame and `2^40` within `2^51`. -/
theorem fs_add_le (g : String) : B2C.fs g + 2 ^ 40 ≤ 2 ^ 51 := by
  have := B2C.fs_lt g
  omega

/-- A loop helper's block over fewer than `2^19` iterations and `2^40` within `2^51`. -/
theorem loopBlock_add_le (L : String) {n : ℕ} (hn : n < 2 ^ 19) : loopBlock L n + 2 ^ 40 ≤ 2 ^ 51 := by
  unfold loopBlock
  have h1 := B2C.fs_lt L
  have h2 := B2C.fs_lt (tailKey L)
  have : n * B2C.fs L ≤ 2 ^ 19 * 2 ^ 30 := Nat.mul_le_mul hn.le h1.le
  omega

/-- **A call window from its callee's `AtEvery`.** -/
theorem winsHypT_call_of_atEvery {s : Stmt} {g : String} {ws : List W1} {st : St} {K : St → Prop}
    {args rets : List E} {Rg : ℕ → Prop} {Preg : Reader → Prop} {Post : Reader → Tree → Prop} {B lo Tc β : ℕ}
    (he : Enters σ0 g s) (ha : (argsOf s).map σ0 = args) (hr : (retsOf s).map σ0 = rets)
    (h : AtEveryB al k g args rets Rg Preg Post B lo Tc β) (hTc : 2 ^ 58 ≤ Tc)
    (hβ : B + β ≤ 2 ^ 51) (hlo : lo ≤ allocBase (al g) st.kc)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hrest : ∀ ec, WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
      ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False, st.Qs ++ [Post]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre (.call s :: ws) st K := by
  obtain ⟨e, hb, hc⟩ := h (allocBase (al g) st.kc) (allocBase (al g) st.kc + B) hlo le_rfl
  rw [WinsHypT]
  refine ⟨g, Post, B, e, Rg, fun _ => False, fun _ => True, he, hR, ?_, end_step hTc hβ hb, hrest e⟩
  rw [ha, hr]
  exact hc.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)

/-- **A guarded call window from its callee's `AtEvery`**: the guard `1 + g^n`, the callee entered on
`n ≠ 0`, a phantom on `n = 0`. -/
theorem winsHypT_cif_of_atEvery {c : V} {g : String} {as : List V} {ws : List W1} {st : St} {K : St → Prop}
    {n : ℕ} {args : List E} {Rg : ℕ → Prop} {Preg : Reader → Prop} {Post : Reader → Tree → Prop} {B lo Tc β : ℕ}
    (hn : n < 2 ^ 34) (hc : σ0 c = word 1 0 + gen ^ n) (ha : as.map σ0 = args)
    (htk : coreProgram.Takes g args.length = true)
    (h : n ≠ 0 → AtEveryB al k g args [] Rg Preg Post B lo Tc β)
    (hTc : 2 ^ 58 ≤ Tc) (hβ : B + β ≤ 2 ^ 51) (hlo : lo ≤ allocBase (al g) st.kc)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hT : n ≠ 0 → ∀ ec, WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
      ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False, st.Qs ++ [Post]⟩ K)
    (hZ : n = 0 → WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
      ⟨st.a, allocBase (al g) st.kc + B2C.fs (tailKey g), st.O, st.D, st.Qs ++ [fun _ _ => True]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre (.cif c g as :: ws) st K := by
  rw [WinsHypT]
  refine ⟨by rw [hc, word_one]; exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n), fun h0 => ?_, fun h0 => ?_⟩
  · have hn0 : n ≠ 0 := fun e => h0 (by rw [hc]; exact (guard_eq_zero_iff hn).mpr e)
    obtain ⟨e, hb, hcl⟩ := h hn0 (allocBase (al g) st.kc) (allocBase (al g) st.kc + B) hlo le_rfl
    refine ⟨Post, B, e, Rg, fun _ => False, fun _ => True, hR, ?_, end_step hTc hβ hb, hT hn0 e⟩
    rw [ha]
    exact hcl.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)
  · have hn0 : n = 0 := (guard_eq_zero_iff hn).mp (by rw [← hc]; exact h0)
    refine ⟨?_, lt_trans (B2C.fs_lt _) (by norm_num), hZ hn0⟩
    rw [ha]
    exact phantom_of_takes htk

/-- **A call window from its callee's `AtEveryB`, its end passed on**: `winsHypT_call_of_atEvery`
whose rest knows the callee's end bound. -/
theorem winsHypT_call_of_atEveryE {s : Stmt} {g : String} {ws : List W1} {st : St} {K : St → Prop}
    {args rets : List E} {Rg : ℕ → Prop} {Preg : Reader → Prop} {Post : Reader → Tree → Prop} {B lo Tc β : ℕ}
    (he : Enters σ0 g s) (ha : (argsOf s).map σ0 = args) (hr : (retsOf s).map σ0 = rets)
    (h : AtEveryB al k g args rets Rg Preg Post B lo Tc β) (hTc : 2 ^ 58 ≤ Tc)
    (hβ : B + β ≤ 2 ^ 51) (hlo : lo ≤ allocBase (al g) st.kc)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hrest : ∀ ec, (allocBase (al g) st.kc + B < Tc → ec ≤ allocBase (al g) st.kc + B + β) →
      WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
        ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False, st.Qs ++ [Post]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre (.call s :: ws) st K := by
  obtain ⟨e, hb, hc⟩ := h (allocBase (al g) st.kc) (allocBase (al g) st.kc + B) hlo le_rfl
  rw [WinsHypT]
  refine ⟨g, Post, B, e, Rg, fun _ => False, fun _ => True, he, hR, ?_, end_step hTc hβ hb, hrest e hb⟩
  rw [ha, hr]
  exact hc.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)

/-- **A guarded call window from its callee's `AtEveryB`, its end passed on.** -/
theorem winsHypT_cif_of_atEveryE {c : V} {g : String} {as : List V} {ws : List W1} {st : St} {K : St → Prop}
    {n : ℕ} {args : List E} {Rg : ℕ → Prop} {Preg : Reader → Prop} {Post : Reader → Tree → Prop} {B lo Tc β : ℕ}
    (hn : n < 2 ^ 34) (hc : σ0 c = word 1 0 + gen ^ n) (ha : as.map σ0 = args)
    (htk : coreProgram.Takes g args.length = true)
    (h : n ≠ 0 → AtEveryB al k g args [] Rg Preg Post B lo Tc β)
    (hTc : 2 ^ 58 ≤ Tc) (hβ : B + β ≤ 2 ^ 51) (hlo : lo ≤ allocBase (al g) st.kc)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hT : n ≠ 0 → ∀ ec, (allocBase (al g) st.kc + B < Tc → ec ≤ allocBase (al g) st.kc + B + β) →
      WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
        ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False, st.Qs ++ [Post]⟩ K)
    (hZ : n = 0 → WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre ws
      ⟨st.a, allocBase (al g) st.kc + B2C.fs (tailKey g), st.O, st.D, st.Qs ++ [fun _ _ => True]⟩ K) :
    WinsHypT B2C.fs al B2C.cert k σ0 w Own R Pre (.cif c g as :: ws) st K := by
  rw [WinsHypT]
  refine ⟨by rw [hc, word_one]; exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n), fun h0 => ?_, fun h0 => ?_⟩
  · have hn0 : n ≠ 0 := fun e => h0 (by rw [hc]; exact (guard_eq_zero_iff hn).mpr e)
    obtain ⟨e, hb, hcl⟩ := h hn0 (allocBase (al g) st.kc) (allocBase (al g) st.kc + B) hlo le_rfl
    refine ⟨Post, B, e, Rg, fun _ => False, fun _ => True, hR, ?_, end_step hTc hβ hb, hT hn0 e hb⟩
    rw [ha]
    exact hcl.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)
  · have hn0 : n = 0 := (guard_eq_zero_iff hn).mp (by rw [← hc]; exact h0)
    refine ⟨?_, lt_trans (B2C.fs_lt _) (by norm_num), hZ hn0⟩
    rw [ha]
    exact phantom_of_takes htk

/-! ## A run's memory facts on counts -/

theorem gen_pow_addr (m : ℕ) : (gen ^ m).limb 0 * addressOfIndex 0 = addressOfIndex m := by
  rw [Value.gen_pow_eq_ofK]; simp

/-- **A touch of a count's word** holds its memory fact where that word is defined. -/
theorem memT_touch {rd : Reader} {σ : Val} {t p : V} {n : ℕ} (hp : σ p = gen ^ n)
    (hd : (rd (addressOfIndex n)).isSome) : MemT rd σ (.touch t p) := by
  show (rd ((σ p).limb 0 * addressOfIndex 0)).isSome
  rw [hp, gen_pow_addr]; exact hd

/-- **A range check of two counts** holds its memory fact where their words are defined. -/
theorem memT_rc {rd : Reader} {σ : Val} {x y t1 t2 kk : V} {n m : ℕ} (hx : σ x = gen ^ n) (hy : σ y = gen ^ m)
    (hdx : (rd (addressOfIndex n)).isSome) (hdy : (rd (addressOfIndex m)).isSome) :
    MemT rd σ (.rangeCheck x y t1 t2 kk) := by
  show (rd ((σ x).limb 0 * addressOfIndex 0)).isSome ∧ (rd ((σ y).limb 0 * addressOfIndex 0)).isSome
  rw [hx, hy, gen_pow_addr, gen_pow_addr]; exact ⟨hdx, hdy⟩

/-- **A range check's pure facts** on two counts, the divisor's count positive when it divides. -/
theorem pureT_rc {σ : Val} {x y t1 t2 kk : V} {n m : ℕ} (hx : σ x = gen ^ n) (hy : σ y = gen ^ m) :
    PureT σ (.rangeCheck x y t1 t2 kk) :=
  ⟨by rw [hx]; exact gen_pow_isInK n, by rw [hy]; exact gen_pow_isInK m,
    fun _ => by rw [hx]; exact pow_ne_zero _ Value.gen_ne_zero⟩

end
end LeanVM.Guest.Complete
