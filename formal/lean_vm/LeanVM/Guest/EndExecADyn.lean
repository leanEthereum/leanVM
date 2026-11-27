/-
  LeanVM.Guest.EndExecADyn

  Every dynamic `HeapBuf`'s size is a power of `g`, at every honest instance (`DynPow`): the
  nonzero facts' check (`Res.carryNzG`) carried down the honest tree.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.EndExecAReady
public import LeanVM.Guest.Memory.Scope
public import LeanVM.Guest.Checked
public import LeanVM.Guest.B1.Placement.Common

/-!
# Dynamic sizes are powers of `g`

`g` generates `K^×` (`orderOf_g`), so a value of `K` is a power of `g` exactly when it is nonzero
(`exists_gpow`); `NZ x`: `x` in `K` and nonzero.

* `nzOf_sound`: a value the check pins (`Res.nzOf`) is `NZ`, given its listed values, the events of
  its context holding on a memory whose addresses are nonzero and whose range checks bound exponents
  (`MemNz`), and its context's calls' listed words (`Res.nzUp`).
* `tabNz_sound`, `armNzB_sound`, `selTabB_sound`: a table read at a range-checked index, and a body's own
  values (`Res.ownNz`), are `NZ`.
* `up_valid`: on a valid tree, each listed word of a node is `NZ` (`UpOk`), by its own body's check
  (`Res.upChk`) and its callees', by induction on the tree.
* `carryNzQ_all`: at every honest instance, its carried parameters (`Res.carriedNz`) are `NZ`
  (`CarryNzQ`), by `Res.insts_down`: a call site passes them (`Res.siteNz`), in the context of its
  statement on the path (`Memory.allB_body`), with the caller's carried values and loop counter.
* `dynPow_guest : DynPow`: a dynamic allocation on an honest instance's path has its size pinned.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Res (veq kvNz pinIn kIn upAt pinNz nzOf nzDepth siteNz nzStmt retNz upChk carryNzG
  carriedNz nzUp carryNz_all tabAt tabNz armNzB topSelsC selTabAt selTabB ownChk ownNz)

@[expose] public section

/-- `x` nonzero in `K`. -/
def NZ (x : E) : Prop := IsInK x ∧ x ≠ 0

/-- **What the nonzero facts' check needs of a memory**: its addresses are nonzero, and a range check
against `g^m`, `m < 2^28`, puts its value at `g^e`, `e ≤ m`. -/
def MemNz (rd : Reader) : Prop :=
  (∀ a w, rd a = some w → a ≠ 0) ∧ ∀ {x y t1 t2 : E} {m : ℕ}, m < 2 ^ 28 → LoadHolds rd x 0 t1 →
    ofK (addressOfIndex m) = x * y → LoadHolds rd y 0 t2 → ∃ e ≤ m, x = ofK (addressOfIndex e)

/-- **The listed words of a node** (`Res.nzUp`), among its arguments then its returns, are `NZ`. -/
def UpOk (f : String) (args rets : List E) : Prop :=
  ∀ c ∈ nzUp, c.1 = f → ∀ w, (args ++ rets)[c.2]? = some w → NZ w

/-- **The carried parameters of an instance** (`Res.carriedNz`) are `NZ`. -/
def CarryNzQ (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ c ∈ carriedNz,
    c.1 = f → ∀ v, fn.params[c.2]? = some v → NZ (σ v)

end

public section

/-! ## Powers of `g` -/

/-- **Every nonzero element of `K` is a power of `g`**, which generates `K^×`. -/
theorem exists_gpow {x : K} (hx : x ≠ 0) : ∃ n, x = addressOfIndex n := by
  let f : Fin (2 ^ 64 - 1) → Kˣ := fun i ↦ Units.mk0 (addressOfIndex i) (gpow_ne_zero i)
  have hf : Function.Injective f := fun i j h ↦
    Fin.ext (gpow_injOn i.2 j.2 (congrArg Units.val h))
  have hc : Nat.card Kˣ ≤ Nat.card (Fin (2 ^ 64 - 1)) := by
    rw [Nat.card_units, BF64.nat_card_bf64, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨i, hi⟩ := (hf.bijective_of_nat_card_le hc).2 (Units.mk0 x hx)
  exact ⟨i, (congrArg Units.val hi).symm⟩

theorem limb_zero : (0 : E).limb 0 = 0 := by
  rw [show (0 : E) = ofK 0 from (map_zero (algebraMap K E)).symm, limb_ofK]
  rfl

theorem limb0_ne_zero {x : E} (h : x ≠ 0) (hk : IsInK x) : x.limb 0 ≠ 0 := by
  intro h0
  apply h
  rw [Core.eq_ofK_limb hk, h0]
  exact map_zero (algebraMap K E)

/-- An `NZ` word is a power of `g`. -/
theorem NZ.pow {x : E} (h : NZ x) : ∃ n, x = ofK (addressOfIndex n) := by
  obtain ⟨n, hn⟩ := exists_gpow (limb0_ne_zero h.2 h.1)
  exact ⟨n, by rw [Core.eq_ofK_limb h.1, hn]⟩

theorem nz_gpow (n : ℕ) : NZ (ofK (addressOfIndex n)) :=
  ⟨B2C.isInK_ofK _, LeanVM.Guest.B1.Whir.ofK_ne_zero (gpow_ne_zero n)⟩

theorem NZ.mul {a b : E} (ha : NZ a) (hb : NZ b) : NZ (a * b) :=
  ⟨LeanVM.Guest.B1.isInK_mul ha.1 hb.1, mul_ne_zero ha.2 hb.2⟩

/-- A factor of an `NZ` product by a nonzero value of `K` is `NZ`. -/
theorem NZ.of_mul {a b : E} (hd : NZ (a * b)) (ha : IsInK a) : NZ b := by
  have ha0 : a ≠ 0 := fun h ↦ hd.2 (by rw [h, zero_mul])
  have hb0 : b ≠ 0 := fun h ↦ hd.2 (by rw [h, mul_zero])
  refine ⟨?_, hb0⟩
  obtain ⟨x, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨y, hy⟩ := (isInK_iff _).mp hd.1
  have hx : x ≠ 0 := fun h ↦ ha0 (by rw [h]; exact map_zero (algebraMap K E))
  have : b = ofK (x⁻¹ * y) := by
    rw [ofK_mul, ← hy, show ofK x⁻¹ = (ofK x)⁻¹ from map_inv₀ (algebraMap K E) x, inv_mul_cancel_left₀ ha0]
  rw [this]
  exact B2C.isInK_ofK _

/-! ## The checks' soundness -/

theorem veq_eq {a b : V} (h : veq a b = true) : a = b := by
  simp only [veq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- A loaded address is nonzero, on a memory whose addresses are. -/
theorem load_nz {rd : Reader} (hrd : ∀ a w, rd a = some w → a ≠ 0) {p d : E} {off : ℕ}
    (h : LoadHolds rd p off d) : NZ p := by
  refine ⟨h.1, fun h0 ↦ hrd _ _ h.2 ?_⟩
  rw [h0, limb_zero, zero_mul]

section

variable {rd : Reader} {σ : Val}

/-- A value equal to its square is `0` or `1`, in `K`. -/
theorem isInK_of_sq {x : E} (h : x = x * x) : IsInK x := by
  have h' : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h1
  · rw [h0, show (0 : E) = ofK 0 from (map_zero (algebraMap K E)).symm]; exact B2C.isInK_ofK _
  · rw [sub_eq_zero.mp h1, show (1 : E) = ofK 1 from (map_one (algebraMap K E)).symm]; exact B2C.isInK_ofK _

theorem pinIn_sound {v : V} {e : Ev} (hh : e.Holds rd σ) (hp : pinIn v e = true) : IsInK (σ v) := by
  rcases e with a | _ | _ | _
  all_goals try (simp [pinIn] at hp; done)
  cases a
  all_goals try (simp [pinIn] at hp; done)
  all_goals simp only [pinIn, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  all_goals simp only [Ev.Holds, Atom.Holds] at hh
  case mul d a b =>
    obtain ⟨⟨hd, ha⟩, hb⟩ := hp
    rw [veq_eq hd, veq_eq ha, veq_eq hb] at hh
    exact isInK_of_sq hh
  case const d w =>
    rw [veq_eq hp.1] at hh
    rw [hh]; exact hp.2
  case load d p off => rw [← veq_eq hp]; exact hh.1
  case rangeCheck x y t1 t2 k =>
    rcases hp with hp | hp <;> rw [← veq_eq hp]
    · exact hh.1.1
    · exact hh.2.2.1
  case assertInK a b =>
    rcases hp with hp | hp <;> rw [← veq_eq hp]
    · exact hh.1
    · exact hh.2
  case frameAddr p run => rw [← veq_eq hp]; exact hh.1
  case touch t p => rw [← veq_eq hp]; exact hh.1

theorem kIn0_sound {kv : List V} {sp : List Ev} (hkv : ∀ u ∈ kv, IsInK (σ u)) (hh : ∀ e ∈ sp, e.Holds rd σ)
    {v : V} (h : Res.kIn0 kv sp v = true) : IsInK (σ v) := by
  simp only [Res.kIn0, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨u, hu, he⟩ | ⟨e, he, hp⟩
  · rw [← veq_eq he]; exact hkv u hu
  · exact pinIn_sound (hh e he) hp

theorem kIn1_sound {kv : List V} {sp : List Ev} (hkv : ∀ u ∈ kv, IsInK (σ u)) (hh : ∀ e ∈ sp, e.Holds rd σ)
    {v : V} (h : Res.kIn1 kv sp v = true) : IsInK (σ v) := by
  simp only [Res.kIn1, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨e, he, hm⟩
  · exact kIn0_sound hkv hh h
  · cases e with
    | atom a =>
      have := hh _ he
      cases a <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at hm <;>
        simp only [Ev.Holds, Atom.Holds] at this
      · rename_i d x y
        obtain ⟨⟨hd, hx⟩, hy⟩ := hm
        rw [← veq_eq hd, this]
        exact B1.isInK_add (kIn0_sound hkv hh hx) (kIn0_sound hkv hh hy)
      · rename_i d x y
        obtain ⟨⟨hd, hx⟩, hy⟩ := hm
        rw [← veq_eq hd, this]
        exact LeanVM.Guest.B1.isInK_mul (kIn0_sound hkv hh hx) (kIn0_sound hkv hh hy)
    | _ => simp at hm

/-- **`kIn` puts its value in `K`.** -/
theorem kIn_sound {kv : List V} {sp : List Ev} (hkv : ∀ u ∈ kv, IsInK (σ u)) (hh : ∀ e ∈ sp, e.Holds rd σ) :
    ∀ n v, kIn kv sp n v = true → IsInK (σ v)
  | 0, v, h => kIn0_sound hkv hh h
  | n + 1, v, h => by
    rw [kIn, Bool.or_eq_true] at h
    rcases h with h | h
    · exact kIn0_sound hkv hh h
    · obtain ⟨e, he, hm⟩ := List.any_eq_true.mp h
      cases e with
      | atom a =>
        have := hh _ he
        cases a <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at hm <;>
          simp only [Ev.Holds, Atom.Holds] at this
        · rename_i d x y
          obtain ⟨⟨hd, hx⟩, hy⟩ := hm
          rw [← veq_eq hd, this]
          exact B1.isInK_add (kIn1_sound hkv hh hx) (kIn1_sound hkv hh hy)
        · rename_i d x y
          obtain ⟨⟨hd, hx⟩, hy⟩ := hm
          rw [← veq_eq hd, this]
          exact LeanVM.Guest.B1.isInK_mul (kIn_sound hkv hh n x hx) (kIn_sound hkv hh n y hy)
      | _ => simp at hm

/-- The listed words of a context's calls are `NZ`. -/
def UpCtx (σ : Val) (sp : List Ev) : Prop :=
  ∀ g args rets, Ev.call g args rets ∈ sp → UpOk g (args.map σ) (rets.map σ)

theorem pinNz_sound (hrd : ∀ a w, rd a = some w → a ≠ 0) {sp : List Ev} (hup : UpCtx σ sp) {v : V} {e : Ev}
    (he : e ∈ sp) (hh : e.Holds rd σ) (hp : pinNz v e = true) : NZ (σ v) := by
  rcases e with a | _ | ⟨g, args, rets⟩ | _
  all_goals try (simp [pinNz] at hp; done)
  · cases a
    all_goals try (simp [pinNz] at hp; done)
    all_goals simp only [pinNz, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hp
    all_goals simp only [Ev.Holds, Atom.Holds] at hh
    case const d w =>
      obtain ⟨⟨hd, h1⟩, h0⟩ := hp
      rw [veq_eq hd] at hh
      rw [hh]
      exact ⟨h1, fun h ↦ h0 (by rw [h, limb_zero])⟩
    case load d p off => rw [← veq_eq hp]; exact load_nz hrd hh
    case rangeCheck x y t1 t2 k =>
      rcases hp with hp | hp <;> rw [← veq_eq hp]
      · exact load_nz hrd hh.1
      · exact load_nz hrd hh.2.2
    case touch t p => rw [← veq_eq hp]; exact load_nz hrd hh
  · simp only [pinNz, upAt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨c, hc, hw, hg⟩ := hp
    split at hw
    · rename_i w hwv
      have hv := veq_eq hw
      subst hv
      exact hup g args rets he c hc hg (σ w) (by rw [← List.map_append, List.getElem?_map, hwv]; rfl)
    · cases hw

/-- A word the guest's powers name is that power of `g` (`Res.powOf`). -/
theorem tab_powOf {w : E} {e : ℕ} (h : Res.powOf w = some e) : w = ofK (addressOfIndex e) := by
  unfold Res.powOf at h
  split_ifs at h with h1
  have hk := Exec.PowTree.find_ok (Exec.PowTree.ok_of_okW Checked.powTree_ok) h
  rw [show K.ofBits (w.limb 0).toBitVec.toNat = w.limb 0 by
    simp [K.ofBits, BF64.ofBitVec, BitVec.ofNat_toNat]] at hk
  rw [eq_ofK_limb h1, hk]

/-- **A table read is `NZ`** (`tabAt`): its index `J` range checked against `g^m` is `g^e`, `e ≤ m`, so
the word at `T·J·g^off` is the one the context stores at `T·g^(e + off)`. -/
theorem tabAt_sound (hm : MemNz rd) {sp : List Ev} (hh : ∀ e ∈ sp, e.Holds rd σ) {nz : V → Bool}
    (hnz : ∀ w, nz w = true → NZ (σ w)) {T J : V} {off : ℕ} {d : E}
    (hld : LoadHolds rd (σ T * σ J) off d) (h : tabAt sp nz T J off = true) : NZ d := by
  unfold tabAt at h
  obtain ⟨e1, he1, h1⟩ := List.any_eq_true.mp h
  cases e1 with
  | atom a1 =>
    cases a1 <;> simp only [Bool.false_eq_true] at h1
    rename_i x y t1 t2 k
    simp only [Bool.and_eq_true] at h1
    obtain ⟨hxJ, h1⟩ := h1
    obtain ⟨e2, he2, h2⟩ := List.any_eq_true.mp h1
    have hrc := hh _ he1
    simp only [Ev.Holds, Atom.Holds] at hrc
    obtain ⟨r1, r2, r3⟩ := hrc
    cases e2 with
    | atom a2 =>
      cases a2 <;> simp only [Bool.false_eq_true] at h2
      rename_i kk c
      simp only [Bool.and_eq_true] at h2
      obtain ⟨hk, h2⟩ := h2
      have hc := hh _ he2
      simp only [Ev.Holds, Atom.Holds] at hc
      split at h2
      · rename_i m hpow
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h2
        obtain ⟨hm28, hall⟩ := h2
        rw [← veq_eq hk, hc, tab_powOf hpow, veq_eq hxJ] at r2
        rw [veq_eq hxJ] at r1
        obtain ⟨e, he, hJe⟩ := hm.2 hm28 r1 r2 r3
        obtain ⟨e3, he3, h3⟩ := List.any_eq_true.mp (hall e (by omega))
        cases e3 with
        | atom a3 =>
          cases a3 <;> simp only [Bool.false_eq_true] at h3
          rename_i w T' o
          simp only [Bool.and_eq_true, beq_iff_eq] at h3
          obtain ⟨⟨hT, ho⟩, hw⟩ := h3
          have hst := hh _ he3
          simp only [Ev.Holds, Atom.Holds] at hst
          rw [veq_eq hT, ho] at hst
          rw [hJe, ← Value.gen_pow_eq_ofK, LeanVM.Guest.B1.loadHolds_mul_gen_pow] at hld
          rw [LeanVM.Guest.B1.loadHolds_unique hld hst]
          exact hnz w hw
        | _ => simp at h3
      · simp at h2
    | _ => simp at h2
  | _ => simp at h1

/-- **A read at `p·g^off` of a table is `NZ`** (`tabNz`). -/
theorem tabNz_sound (hm : MemNz rd) {sp : List Ev} (hh : ∀ e ∈ sp, e.Holds rd σ) {nz : V → Bool}
    (hnz : ∀ w, nz w = true → NZ (σ w)) {p : V} {off : ℕ} {d : E}
    (hld : LoadHolds rd (σ p) off d) (h : tabNz sp nz p off = true) : NZ d := by
  unfold tabNz at h
  obtain ⟨e1, he1, h1⟩ := List.any_eq_true.mp h
  cases e1 with
  | atom a1 =>
    cases a1 <;> simp only [Bool.false_eq_true] at h1
    rename_i q a b
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
    obtain ⟨hq, h1 | h1⟩ := h1
    · have hmul := hh _ he1
      simp only [Ev.Holds, Atom.Holds] at hmul
      rw [← veq_eq hq, hmul] at hld
      exact tabAt_sound hm hh hnz hld h1
    · have hmul := hh _ he1
      simp only [Ev.Holds, Atom.Holds] at hmul
      rw [← veq_eq hq, hmul, mul_comm] at hld
      exact tabAt_sound hm hh hnz hld h1
  | _ => simp at h1

/-- **`nzOf` puts its value nonzero in `K`**, given its listed values, its context's events holding on
a memory as `MemNz` asks, and its context's calls' listed words. -/
theorem nzOf_sound (hM : MemNz rd) {kv : List V} {sp : List Ev}
    (hkv : ∀ u ∈ kv, NZ (σ u)) (hh : ∀ e ∈ sp, e.Holds rd σ) (hup : UpCtx σ sp) :
    ∀ n v, nzOf kv sp n v = true → NZ (σ v)
  | 0, v, h => by
    simp only [nzOf, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨u, hu, he⟩ | ⟨e, he, hp⟩
    · rw [← veq_eq he]; exact hkv u hu
    · exact pinNz_sound hM.1 hup he (hh e he) hp
  | n + 1, v, h => by
    have hk := kIn_sound (rd := rd) (σ := σ) (fun u hu ↦ (hkv u hu).1) hh
    simp only [nzOf, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with (⟨u, hu, he⟩ | ⟨e, he, hp⟩) | ⟨e, he, hm⟩
    · rw [← veq_eq he]; exact hkv u hu
    · exact pinNz_sound hM.1 hup he (hh e he) hp
    · cases e with
      | atom a =>
        have hhe := hh _ he
        cases a <;> simp only [Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hm <;>
          simp only [Ev.Holds, Atom.Holds] at hhe
        · rename_i d x y
          rcases hm with (⟨⟨hd, hx⟩, hy⟩ | ⟨⟨hd, hx⟩, hy⟩) | ⟨⟨hd, hx⟩, hy⟩
          · rw [← veq_eq hd, hhe]
            exact (nzOf_sound hM hkv hh hup n x hx).mul (nzOf_sound hM hkv hh hup n y hy)
          · rw [← veq_eq hd]
            have := nzOf_sound hM hkv hh hup n d hy
            rw [hhe] at this
            exact this.of_mul (hk _ x hx)
          · rw [← veq_eq hd]
            have := nzOf_sound hM hkv hh hup n d hy
            rw [hhe, mul_comm] at this
            exact this.of_mul (hk _ y hx)
        · rename_i d s
          rcases hm with ⟨hd, hs⟩ | ⟨hd, hs⟩
          · rw [← veq_eq hd, hhe]; exact nzOf_sound hM hkv hh hup n s hs
          · rw [← veq_eq hd, ← hhe]; exact nzOf_sound hM hkv hh hup n d hs
        · rename_i d p off
          obtain ⟨hd, ht⟩ := hm
          rw [← veq_eq hd]
          exact tabNz_sound hM hh (nzOf_sound hM hkv hh hup n) hhe ht
        · -- `a + b = 0`: `a = b`, in characteristic `2`
          rename_i d s
          have hds : σ d = σ s := Value.e_add_eq_zero_iff.mp hhe
          rcases hm with ⟨hd, hs⟩ | ⟨hd, hs⟩
          · rw [← veq_eq hd, hds]; exact nzOf_sound hM hkv hh hup n s hs
          · rw [← veq_eq hd, ← hds]; exact nzOf_sound hM hkv hh hup n d hs
      | _ => simp at hm

/-! ## What a body pins on every returning path -/

theorem seq_ret_sub {o k : Out} {es : List Ev} {vs : List V} (h : o.seq k = .ret es vs) : ∀ y ∈ o.evs, y ∈ es := by
  intro y hy
  rcases o with es1 | ⟨es1, vs1⟩ | _
  · rcases k with es2 | ⟨es2, vs2⟩ | _ <;> simp only [Out.seq, Out.pre, reduceCtorEq, Out.ret.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.mem_append_left _ hy
  · simp only [Out.seq, Out.ret.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hy
  · simp [Out.evs] at hy

/-- A statement free of `ret` on a returning path: its path falls through, the rest returns. -/
theorem seq_ret_next {s : Stmt} {ss : List Stmt} {es : List Ev} {vs : List V} (hn : Bridge.noRet [s] = true)
    (h : (walk1 σ s).seq (walk σ ss) = .ret es vs) : ∃ es1 es2, walk1 σ s = .fall es1 ∧ walk σ ss = .ret es2 vs ∧
      es = es1 ++ es2 := by
  rcases h1 : walk1 σ s with es1 | ⟨es1, vs1⟩ | _
  · rw [h1] at h
    rcases h2 : walk σ ss with es2 | ⟨es2, vs2⟩ | _ <;> rw [h2] at h <;>
      simp only [Out.seq, Out.pre, reduceCtorEq, Out.ret.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨es1, es2, rfl, rfl, rfl⟩
  · exact absurd h1 (Bridge.walk1_noRet s hn es1 vs1)
  · rw [h1] at h; simp [Out.seq] at h

/-- The arm a `match` that does not get stuck takes: arm `i`, at `x = g^(j + i)`. -/
theorem walkArms_arm {x : V} : ∀ (arms : List (List Stmt)) (j : ℕ), walkArms σ x j arms ≠ .stuck →
    ∃ i, ∃ h : i < arms.length, σ x = ofK (addressOfIndex (j + i)) ∧ walkArms σ x j arms = walk σ arms[i]
  | [], _, h => by simp [walkArms] at h
  | a :: as, j, h => by
    unfold walkArms at h ⊢
    split_ifs at h ⊢ with hx
    · exact ⟨0, by simp, by simpa using hx, rfl⟩
    · obtain ⟨i, hi, hxi, hw⟩ := walkArms_arm as (j + 1) h
      exact ⟨i + 1, by simpa using hi, by rw [hxi]; congr 2; omega, hw⟩

/-- **A value a top-level `match` pins in every arm is `NZ`** (`armNzB`), on a returning path whose events hold. -/
theorem armNzB_sound (hM : MemNz rd) {v : V} : ∀ {ss : List Stmt} {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → (∀ e ∈ es, e.Holds rd σ) → UpCtx σ es → armNzB v ss = true → NZ (σ v)
  | [], _, _, _, _, _, hv => by simp [armNzB] at hv
  | s :: ss, es, vs, hw, hh, hup, hv => by
    unfold armNzB at hv
    rw [walk] at hw
    rcases Bool.or_eq_true_iff.mp hv with hv | hv
    · rcases s with _ | _ | ⟨x, _ | ⟨a, as⟩⟩ | _ | _ | _ | _
      all_goals try (simp at hv; done)
      simp only at hv
      rw [List.all_eq_true] at hv
      have hst : walk1 σ (.match_ x (a :: as)) ≠ .stuck := by
        intro h0; rw [h0] at hw; simp [Out.seq] at hw
      simp only [walk1] at hst hw
      obtain ⟨i, hi, -, harm⟩ := walkArms_arm (a :: as) 0 hst
      have hsub := seq_ret_sub hw
      rw [harm] at hst hsub
      have hin : ∀ y ∈ spineE (a :: as)[i], y ∈ es := fun y hy ↦ hsub y (spineE_sub _ hst y hy)
      exact nzOf_sound hM (by simp) (fun e he ↦ hh e (hin e he)) (fun g a' r' hg ↦ hup g a' r' (hin _ hg)) _ _
        (hv _ (List.getElem_mem hi))
    · rw [Bool.and_eq_true] at hv
      obtain ⟨es1, es2, -, hw2, rfl⟩ := seq_ret_next hv.1 hw
      exact armNzB_sound hM hw2 (fun e he ↦ hh e (List.mem_append_right _ he))
        (fun g a' r' hg ↦ hup g a' r' (List.mem_append_right _ hg)) hv.2

/-- **A top-level selector of `m` arms is `g^e`, `e < m`**, on a returning path. -/
theorem topSelsC_sound : ∀ {ss : List Stmt} {es : List Ev} {vs : List V}, walk σ ss = .ret es vs →
    ∀ {x : V} {m : ℕ}, (x, m) ∈ topSelsC ss → ∃ e < m, σ x = ofK (addressOfIndex e)
  | [], _, _, _, _, _, h => by simp [topSelsC] at h
  | s :: ss, es, vs, hw, x, m, h => by
    unfold topSelsC at h
    rw [walk] at hw
    rcases List.mem_append.mp h with h | h
    · rcases s with _ | _ | ⟨y, arms⟩ | _ | _ | _ | _
      all_goals try (simp at h; done)
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hst : walk1 σ (.match_ x arms) ≠ .stuck := by
        intro h0; rw [h0] at hw; simp [Out.seq] at hw
      simp only [walk1] at hst
      obtain ⟨i, hi, hx, -⟩ := walkArms_arm arms 0 hst
      exact ⟨i, hi, by simpa using hx⟩
    · cases hn : Bridge.noRet [s]
      · simp [hn] at h
      · simp only [hn, Bool.cond_true] at h
        obtain ⟨es1, es2, -, hw2, -⟩ := seq_ret_next hn hw
        exact topSelsC_sound hw2 h

/-- **A table read at a selector is `NZ`** (`selTabAt`). -/
theorem selTabAt_sound (hM : MemNz rd) {sp : List Ev} (hh : ∀ e ∈ sp, e.Holds rd σ) (hup : UpCtx σ sp)
    {sels : List (V × ℕ)} (hsel : ∀ c ∈ sels, ∃ e < c.2, σ c.1 = ofK (addressOfIndex e)) {T J : V} {off : ℕ} {d : E}
    (hld : LoadHolds rd (σ T * σ J) off d) (h : selTabAt sp sels T J off = true) : NZ d := by
  unfold selTabAt at h
  obtain ⟨c, hc, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hcJ, hall⟩ := h
  obtain ⟨e, he, hJe⟩ := hsel c hc
  rw [veq_eq hcJ] at hJe
  obtain ⟨e3, he3, h3⟩ := List.any_eq_true.mp (hall e he)
  cases e3 with
  | atom a3 =>
    cases a3 <;> simp only [Bool.false_eq_true] at h3
    rename_i w T' o
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨⟨hT, ho⟩, hw⟩ := h3
    have hst := hh _ he3
    simp only [Ev.Holds, Atom.Holds] at hst
    rw [veq_eq hT, ho] at hst
    rw [hJe, ← Value.gen_pow_eq_ofK, LeanVM.Guest.B1.loadHolds_mul_gen_pow] at hld
    rw [LeanVM.Guest.B1.loadHolds_unique hld hst]
    exact nzOf_sound hM (by simp) hh hup _ _ hw
  | _ => simp at h3

/-- **A body's table read at a selector is `NZ`** (`selTabB`), on a returning path whose events hold. -/
theorem selTabB_sound (hM : MemNz rd) {body : List Stmt} {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs)
    (hh : ∀ e ∈ es, e.Holds rd σ) (hup : UpCtx σ es) {v : V} (hv : selTabB body v = true) : NZ (σ v) := by
  have hin : ∀ y ∈ spineE body, y ∈ es := by
    have := spineE_sub (σ := σ) body (by rw [hw]; simp)
    rwa [hw] at this
  have hh' : ∀ e ∈ spineE body, e.Holds rd σ := fun e he ↦ hh e (hin e he)
  have hup' : UpCtx σ (spineE body) := fun g a r hg ↦ hup g a r (hin _ hg)
  have hsel : ∀ c ∈ topSelsC body, ∃ e < c.2, σ c.1 = ofK (addressOfIndex e) := fun c hc ↦ topSelsC_sound hw hc
  unfold selTabB at hv
  obtain ⟨e1, he1, h1⟩ := List.any_eq_true.mp hv
  cases e1 with
  | atom a1 =>
    cases a1 <;> simp only [Bool.false_eq_true] at h1
    rename_i d p off
    simp only [Bool.and_eq_true] at h1
    obtain ⟨hd, hany⟩ := h1
    rw [← veq_eq hd]
    have hld := hh' _ he1
    simp only [Ev.Holds, Atom.Holds] at hld
    obtain ⟨e2, he2, h2⟩ := List.any_eq_true.mp hany
    cases e2 with
    | atom a2 =>
      cases a2 <;> simp only [Bool.false_eq_true] at h2
      rename_i q a b
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h2
      obtain ⟨hq, h2 | h2⟩ := h2
      · have hmul := hh' _ he2
        simp only [Ev.Holds, Atom.Holds] at hmul
        rw [← veq_eq hq, hmul] at hld
        exact selTabAt_sound hM hh' hup' hsel hld h2
      · have hmul := hh' _ he2
        simp only [Ev.Holds, Atom.Holds] at hmul
        rw [← veq_eq hq, hmul, mul_comm] at hld
        exact selTabAt_sound hM hh' hup' hsel hld h2
    | _ => simp at h2
  | _ => simp at h1

end

/-! ## The listed words of a valid tree -/

theorem call_mem_calls {es : List Ev} {g : String} {args rets : List V} (h : Ev.call g args rets ∈ es) :
    (⟨g, args, rets, true⟩ : Call) ∈ calls es := mem_calls_of_call h

theorem carryNzG_of {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) : carryNzG fn = true :=
  carryNz_all fn (List.mem_of_find?_eq_some hf)

section

variable {rd : Reader}

mutual
/-- **The listed words of a valid node are `NZ`.** -/
theorem up_valid (hrd : MemNz rd) :
    ∀ (t : Tree) {args rets : List E}, t.Valid coreProgram rd args rets → UpOk t.name args rets
  | .node f σ _ kids, args, rets, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩ => by
    have hname : fn.name = f := fn_name_of_find hf
    have hG := carryNzG_of hf
    simp only [carryNzG, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hG
    have hupc : ∀ ctx : List Ev, (∀ x ∈ ctx, x ∈ es) → UpCtx σ ctx := fun ctx hctx g a r hg ↦
      Tree.KidsValid.up hrd σ kids (calls es) hk _ (call_mem_calls (hctx _ hg)) rfl
    have hsp : ∀ x ∈ spineE fn.body, x ∈ es := by
      have := spineE_sub (σ := σ) fn.body (by rw [hw]; simp)
      rwa [hw] at this
    intro c hc hcf w hwc
    have hu := (hG.1.2 c hc).resolve_left (by rw [hname, hcf]; exact not_not.mpr rfl)
    have hlen : args.length = fn.params.length := by rw [← hp, List.length_map]
    unfold upChk at hu
    split at hu
    · rename_i p hpi
      have hlt : c.2 < fn.params.length := (List.getElem?_eq_some_iff.mp hpi).1
      rw [List.getElem?_append_left (by omega), ← hp, List.getElem?_map, hpi, Option.map_some,
        Option.some.injEq] at hwc
      subst hwc
      exact nzOf_sound hrd (by simp) (fun e he ↦ hes e (hsp e he)) (hupc _ hsp) _ _ hu
    · rename_i hpi
      have hge : fn.params.length ≤ c.2 := by
        by_contra h
        rw [List.getElem?_eq_none_iff] at hpi
        omega
      obtain ⟨ctx, hret, hctx⟩ := allB_body_ret (σ := σ) hu hw
      rw [List.getElem?_append_right (by omega), ← hr, hlen, List.getElem?_map] at hwc
      simp only [retNz] at hret
      split at hret
      · rename_i v hv
        rw [hv, Option.map_some, Option.some.injEq] at hwc
        subst hwc
        exact nzOf_sound hrd (by simp) (fun e he ↦ hes e (hctx e he)) (hupc _ hctx) _ _ hret
      · cases hret
  | .phantom .., _, _, h => h.elim

/-- `up_valid` for the callees: each call entered has its listed words `NZ`. -/
theorem Tree.KidsValid.up (hrd : MemNz rd) : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValid coreProgram rd σ cs ks → ∀ c ∈ cs, c.taken = true → UpOk c.f (c.args.map σ) (c.rets.map σ)
  | _, [], [], _, _, hc, _ => (List.not_mem_nil hc).elim
  | σ, k :: ks, c :: cs, ⟨hn, hk, hks⟩, c', hc', ht => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · rw [ite_eq_left ht] at hk
        rw [← hn]
        exact up_valid hrd k hk
      · exact Tree.KidsValid.up hrd σ ks cs hks c' hc' ht
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
end

end

/-! ## At the honest instances -/

section

variable {r : Ref}

theorem ref_rd (hr : r.Ok) : ∀ a w, r.img.read a = some w → a ≠ 0 := fun a w h ↦ by
  obtain ⟨i, -, rfl⟩ := read_pow h (logMemorySize_le_28 (e := r.exec) hr.size)
  exact gpow_ne_zero i

/-- **The reference memory is as the nonzero facts' check asks**: of at most `2^28` words, so a range
check bounds an exponent (`B1.Tables.tb_rc_sound'`). -/
theorem ref_memNz (hr : r.Ok) : MemNz r.img.read := by
  refine ⟨ref_rd hr, fun {x y t1 t2 m} hm h1 h2 h3 ↦ ?_⟩
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨e, he, hx⟩ := B1.Tables.tb_rc_sound' (by omega) r.img (K := m + 1) (k := ofK (addressOfIndex m))
    (by omega) (by omega) (by rw [Nat.add_sub_cancel]) h1 h2 h3
  exact ⟨e, by omega, by rw [hx, Value.gen_pow_eq_ofK]⟩

/-- The values `kvNz` lists of an honest instance are `NZ`, given its carried parameters. -/
theorem kvNz_sound (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hIt : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hQ : CarryNzQ I) : ∀ u ∈ kvNz fn, NZ (σ u) := by
  have hname : fn.name = f := fn_name_of_find hf
  intro u hu
  -- what its own body pins
  have hown : ∀ u, ownChk fn u = true → NZ (σ u) := by
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    obtain ⟨fn', hf', -, es, vs, hw, -, hh, hk⟩ := hv
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
    have hM := ref_memNz hr
    have hup : UpCtx σ es := fun g a' r' hg ↦ Tree.KidsValid.up hM σ kids (calls es) hk _ (call_mem_calls hg) rfl
    intro u hu
    rcases Bool.or_eq_true_iff.mp hu with hu | hu
    · exact armNzB_sound hM hw hh hup hu
    · exact selTabB_sound hM hw hh hup hu
  rcases List.mem_append.mp hu with hu | hu
  · rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨c, hc, hcu⟩ := List.mem_filterMap.mp hu
      split_ifs at hcu with hb
      exact hQ f σ bufs kids hIt fn hf c hc (by rw [← hname]; exact beq_iff_eq.mp hb) u hcu
    · split_ifs at hu with hl
      · obtain ⟨p0, prest, e', hps, hσ⟩ := inst_ctr hr hI hIt hf hl
        rw [hps] at hu
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hu
        rw [hu, hσ]
        exact nz_gpow e'
      · simp at hu
  · -- a listed own value, which its body pins (`ownChk`)
    obtain ⟨c, hc, hcu⟩ := List.mem_filterMap.mp hu
    split_ifs at hcu with hb
    obtain rfl := Option.some.inj hcu
    have hG := carryNzG_of hf
    simp only [carryNzG, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hG
    exact hown _ ((hG.2 c hc).resolve_left (not_not.mpr (beq_iff_eq.mp hb)))

/-- **The carried parameters pass down a call.** -/
theorem carryNzQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) CarryNzQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph hQI
    f σ bufs kids hJt fn hfn cc hcc hcf v hv
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn', hfn', hpar, -⟩ := hJv
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hfn')
  have hcf' : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  -- the call's event and the statement emitting it
  obtain ⟨e, he, hec⟩ := List.mem_filterMap.mp hc
  have hev : e = .call c.f c.args c.rets := by
    rcases e with _ | _ | ⟨g, a, r'⟩ | ⟨g, a⟩ <;> simp only [Ev.call?, reduceCtorEq] at hec
    · obtain rfl := Option.some.inj hec; rfl
    · obtain rfl := Option.some.inj hec; cases hct
  subst hev
  have hG := carryNzG_of hfI
  simp only [carryNzG, Bool.and_eq_true] at hG
  obtain ⟨ctx, s, hs, hem, hctx⟩ := allB_body hG.1.1 hw _ he
  have hrd := ref_memNz hr
  obtain ⟨args', rets', hvI⟩ := inst_valid' hr hI hIt
  obtain ⟨fnI', hfI', -, es', vs', hw', -, -, hkI⟩ := hvI
  obtain rfl : fnI = fnI' := Option.some.inj (hfI.symm.trans hfI')
  rw [hw] at hw'
  obtain ⟨rfl, rfl⟩ := Out.ret.inj hw'
  have hpin : ∀ a, nzOf (kvNz fnI) ctx nzDepth a = true → NZ (σI a) := fun a ha ↦
    nzOf_sound hrd (kvNz_sound hr hI hIt hfI hQI) (fun x hx ↦ hh x (hctx x hx))
      (fun g a' r' hg ↦ Tree.KidsValid.up hrd σI kidsI (calls es) hkI _ (call_mem_calls (hctx _ hg)) rfl) _ a ha
  have hsite : siteNz (kvNz fnI) ctx c.f c.args = true := by
    rcases s with a | _ | _ | ⟨g, a', r'⟩ | ⟨b, g, a'⟩ | ⟨x, gs, a', r'⟩ | _
    all_goals try (simp [Emits] at hem; done)
    · simp only [Emits, Ev.call.injEq] at hem
      obtain ⟨rfl, rfl, rfl⟩ := hem; exact hs
    · simp only [Emits, reduceCtorEq, Ev.call.injEq, false_or] at hem
      obtain ⟨rfl, rfl, -⟩ := hem; exact hs
    · simp only [Emits, Ev.call.injEq] at hem
      obtain ⟨g, hg, rfl, rfl, -⟩ := hem
      exact List.all_eq_true.mp hs _ hg
  have hs' := List.all_eq_true.mp hsite cc hcc
  rw [hcf', ← hcf] at hs'
  simp only [bne_self_eq_false, Bool.false_or] at hs'
  have hpv : (fn.params.map σ)[cc.2]? = some (σ v) := by simp [hv]
  rw [hpar] at hpv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hpv
  obtain ⟨a, ha, hav⟩ := hpv
  rw [ha] at hs'
  rw [← hav]
  exact hpin a hs'

/-- **The carried parameters at every honest instance.** -/
theorem carryNzQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, CarryNzQ J := by
  refine insts_all hr (carryNzQ_step hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt fn _ c hc hcf
  have hn := hm _ _ _ _ hJt
  subst hn
  have : ∀ c ∈ carriedNz, c.1 ≠ "main" := by decide
  exact absurd hcf (this c hc)

end

/-- **Every dynamic `HeapBuf`'s size is a power of `g`**, at every honest instance. -/
theorem dynPow_guest : DynPow := by
  intro r hr I hI f σ bufs kids hIt d s hev
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨fn, hf, -, es, vs, hw, -, hh, hk⟩ := hv
  rw [hIt, events_node hf hw] at hev
  have hG := carryNzG_of hf
  simp only [carryNzG, Bool.and_eq_true] at hG
  obtain ⟨ctx, st, hs, hem, hctx⟩ := allB_body hG.1.1 hw _ hev
  have hs' : nzOf (kvNz fn) ctx nzDepth s = true := by
    rcases st with a | _ | _ | _ | _ | _ | _
    all_goals try (simp [Emits] at hem; done)
    simp only [Emits, Ev.atom.injEq] at hem
    subst hem
    exact hs
  have hrd := ref_memNz hr
  have hnz := nzOf_sound hrd (kvNz_sound hr hI hIt hf (carryNzQ_all hr I hI)) (fun x hx ↦ hh x (hctx x hx))
    (fun g a' r' hg ↦ Tree.KidsValid.up hrd σ kids (calls es) hk _ (call_mem_calls (hctx _ hg)) rfl) _ _ hs'
  obtain ⟨n, hn⟩ := hnz.pow
  classical
  have hex : ∃ e, I.t.val s = ofK (addressOfIndex e) := ⟨n, by rw [hIt]; exact hn⟩
  unfold logG
  split
  · rename_i h; exact Nat.find_spec h
  · contradiction

end

end LeanVM.Guest.EndExec
