module

public import NativeVm.Code.Phase7.Rounds

/-!
# Facts of the area's words, and gadgets that store their result

`Dep env X D`: the memory fact `X` reads only the working area's words with index in `D`. Such a
fact survives the transcript's gadgets when `D` lies in the area (`Dep.mineOnly`) and a store to a
word outside `D` (`Dep.store`). `readTo k` / `sampleTo k`: a gadget, then its result stored at the
area's words `k`, `k + 1`, keeping every such fact that does not read them (`readTo_b`,
`sampleTo_b`) and every fact of the registers the gadgets and the stores keep (`RegOk`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wdisp Keeps clobbers wd_inj wd_zero eval_cw wp_load wp_store
  isSome_setMem ctxWork)

/-- Read a word through register updates and stores to the area's words. -/
macro "wsimp" : tactic => `(tactic|
  simp (disch := oomega) only [QState.setReg_mem, setMem_wd, QState.setReg_reg, QState.setMem_reg,
    reduceCtorEq, ↓reduceIte, ite_true, ite_false, ite_no, ite_yes])

/-! ## Facts of the area's words -/

/-- `X` reads only the working area's words with index in `D`. -/
def Dep (env : Env) (X : (UInt64 → Option UInt64) → Prop) (D : Nat → Prop) : Prop :=
  ∀ m m', (∀ k, D k → m' (wd env.work k) = m (wd env.work k)) → X m → X m'

namespace Dep

variable {env : Env} {X Y : (UInt64 → Option UInt64) → Prop} {D D' : Nat → Prop}

theorem mineOnly (h : Dep env X D) (hD : ∀ k, D k → mineLo ≤ k ∧ k < dataEnd) :
    MineOnly env X :=
  fun m m' hm hx ↦ h m m' (fun k hk ↦ hm _ (inMine_wd (hD k hk).1 (hD k hk).2)) hx

theorem store (h : Dep env X D) (hD : ∀ j, D j → j < 2 ^ 61) {k : Nat} (hk : ¬ D k)
    (hk' : k < 2 ^ 61) {m : UInt64 → Option UInt64} (v : UInt64) (hx : X m) :
    X (Function.update m (wd env.work k) (some v)) :=
  h m _ (fun j hj ↦ Function.update_of_ne (fun e ↦ hk ((wd_inj (hD j hj) hk').mp e ▸ hj)) _ _) hx

theorem and (h : Dep env X D) (h' : Dep env Y D') :
    Dep env (fun m ↦ X m ∧ Y m) (fun k ↦ D k ∨ D' k) :=
  fun m m' hm ⟨hx, hy⟩ ↦ ⟨h m m' (fun k hk ↦ hm k (.inl hk)) hx, h' m m' (fun k hk ↦ hm k (.inr hk)) hy⟩

theorem mono (h : Dep env X D) (hD : ∀ k, D k → D' k) : Dep env X D' :=
  fun m m' hm hx ↦ h m m' (fun k hk ↦ hm k (hD k hk)) hx

theorem true : Dep env (fun _ ↦ True) D := fun _ _ _ _ ↦ trivial

/-- A fact read through `Same` on a run of the area's words. -/
theorem of_same {o n : Nat} (h : ∀ m m', Same m m' (wd env.work o) n → X m → X m') :
    Dep env X (fun k ↦ o ≤ k ∧ k < o + n) :=
  fun m m' hm hx ↦ h m m' (fun j hj ↦ by rw [wd_wd]; exact hm _ ⟨by omega, by omega⟩) hx

end Dep

variable {env : Env}

theorem dep_ewat (j : Nat) (x : EW) :
    Dep env (fun m ↦ EWAt m (wd env.work j) x) (fun k ↦ j ≤ k ∧ k < j + 2) :=
  Dep.of_same fun _ _ h hx ↦ hx.congr h

theorem dep_natAt (j n : Nat) : Dep env (fun m ↦ NatAt m (wd env.work j) n) (fun k ↦ j ≤ k ∧ k < j + 1) :=
  Dep.of_same fun _ _ h hx ↦ hx.congr (h.base (by omega) rfl)

theorem dep_word (j : Nat) (v : Option UInt64) :
    Dep env (fun m ↦ m (wd env.work j) = v) (fun k ↦ j ≤ k ∧ k < j + 1) :=
  Dep.of_same fun _ _ h hx ↦ h.base (by omega) hx

theorem dep_whir (sW : WhirStateW) :
    Dep env (fun m ↦ WhirAt m (whirR.at env.work) sW) (fun k ↦ whirR.off ≤ k ∧ k < whirR.off + whirWords) :=
  Dep.of_same fun _ _ h hx ↦ hx.congr h

theorem dep_rounds (rs : Array FoldRoundW) :
    Dep env (fun m ↦ RoundsAt m (roundsR.at env.work) rs)
      (fun k ↦ roundsR.off ≤ k ∧ k < roundsR.off + roundsWords) :=
  Dep.of_same fun _ _ h hx ↦ hx.congr h

/-- `Only` reads the area's words outside the words written. -/
theorem dep_only (W : Nat → Prop) (m0 : UInt64 → Option UInt64) :
    Dep env (Only env W m0) (fun k ↦ mineLo ≤ k ∧ k < dataEnd ∧ ¬ W k) :=
  fun _ _ hm ho k h1 h2 hk ↦ (hm k ⟨h1, h2, hk⟩).trans (ho k h1 h2 hk)

/-- `Only` through a piece writing only the area's words in `W'`, a part of `W`. -/
theorem Only.frame {W W' : Nat → Prop} {m0 m1 m2 : UInt64 → Option UInt64} (h : Only env W m0 m1)
    (h2 : ∀ a, (∀ k, W' k → a ≠ wd env.work k) → m2 a = m1 a) (hW : ∀ k, W' k → W k)
    (hW' : ∀ k, W' k → k < 2 ^ 61) : Only env W m0 m2 := fun k h1 hk2 hk ↦ by
  rw [h2 _ fun j hj e ↦ hk (by
    have := hW' j hj
    rw [dataEnd_val] at hk2
    rw [(wd_inj (by omega) this).mp e]; exact hW j hj)]
  exact h k h1 hk2 hk

/-- A piece writing only the area's words in `W'` keeps the frame. -/
theorem frM_of {s s' : QState} {W' : Nat → Prop} (hrdi : s'.reg .rdi = s.reg .rdi)
    (hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome)
    (hm : ∀ a, (∀ k, W' k → a ≠ wd env.work k) → s'.mem a = s.mem a)
    (hW : ∀ k, W' k → mineLo ≤ k ∧ k < dataEnd) : FrM env s s' :=
  ⟨hrdi, hd, fun a ha ↦ hm a fun k hk e ↦ ha (e ▸ inMine_wd (hW k hk).1 (hW k hk).2)⟩

/-- The working area's words exist. -/
theorem Base.some {p : Par} {t : TState} {s : QState} (hb : Base p t s) {k : Nat}
    (_h1 : mineLo ≤ k) (h2 : k < dataEnd) : (s.mem (wd p.env.work k)).isSome :=
  hb.inp.workSome k (by have := workWords_ge p.inp.bytecode.size; rw [dataEnd_val] at h2; omega)

/-! ## Facts of the registers -/

/-- A fact of the registers the gadgets and the area's stores keep: all but `rbp` and `clobbers`. -/
def RegOk (Rg : (Reg64 → UInt64) → Prop) : Prop :=
  ∀ f g : Reg64 → UInt64, (∀ r, r ∉ Reg64.rbp :: clobbers → g r = f r) → Rg f → Rg g

theorem RegOk.true : RegOk fun _ ↦ True := fun _ _ _ _ ↦ trivial

theorem RegOk.eq {r : Reg64} (hr : r ∉ Reg64.rbp :: clobbers) (v : UInt64) :
    RegOk fun f ↦ f r = v := fun _ _ h hf ↦ (h r hr).trans hf

theorem RegOk.and {Rg Rg' : (Reg64 → UInt64) → Prop} (h : RegOk Rg) (h' : RegOk Rg') :
    RegOk fun f ↦ Rg f ∧ Rg' f := fun f g hfg ⟨a, b⟩ ↦ ⟨h f g hfg a, h' f g hfg b⟩

/-! ## A gadget, then its result stored -/

/-- `read`, its scalar stored at the area's words `k`, `k + 1`. -/
def readTo (k : Nat) : Stmt := blk [Transcript.readScalar, ldW, stw k .r9, stw (k + 1) .r10]

/-- `sample`, its challenge stored at the area's words `k`, `k + 1`. -/
def sampleTo (k : Nat) : Stmt := blk [Transcript.sampleChallenge, ldW, stw k .r9, stw (k + 1) .r10]

variable {p : Par} {X : (UInt64 → Option UInt64) → Prop} {D : Nat → Prop}
  {Rg : (Reg64 → UInt64) → Prop}

/-- The stores after a gadget. -/
theorem storeAfter {k : Nat} {x : EW} (hX : Dep p.env X D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd)
    (hk : ¬ D k ∧ ¬ D (k + 1)) (hka : mineLo ≤ k ∧ k + 1 < dataEnd) (hRg : RegOk Rg)
    {t : TState} {s : QState} (hb : Base p t s) (hx : X s.mem) (hr : Rg s.reg)
    (h9 : s.reg .r9 = x.c0) (h10 : s.reg .r10 = x.c1) :
    WP (blk [ldW, stw k .r9, stw (k + 1) .r10]) s
      (fun s' ↦ Base p t s' ∧ X s'.mem ∧ Rg s'.reg ∧ EWAt s'.mem (wd p.env.work k) x ∧
        s'.reg .rbp = p.env.work) fun _ ↦ False := by
  have hde := dataEnd_eq
  have hD' : ∀ j, D j → j < 2 ^ 61 := fun j hj ↦ by have := hD j hj; omega
  have hsome : ∀ (s : QState) j, Inputs p.env p.inp s.mem → mineLo ≤ j → j < dataEnd →
      (s.mem (wd p.env.work j)).isSome := fun s j hi h1 h2 ↦
    hi.workSome j (by have := workWords_ge p.inp.bytecode.size; omega)
  unfold ldW
  refine wp_load (eval_cw hb.rdi _) hb.workPtr ?_
  have b1 := hb.frM (frM_setReg (r := .rbp) (by decide) p.env.work)
  have hW1 : (s.setReg .rbp p.env.work).reg .rbp = p.env.work := by simp
  refine stw_wp hW1 (hsome _ _ b1.inp hka.1 (by omega)) ?_
  set s2 := (s.setReg .rbp p.env.work).setMem (wd p.env.work k) ((s.setReg .rbp p.env.work).reg .r9)
  have b2 : Base p t s2 := b1.frM (frM_store hka.1 (by omega) (hsome _ _ b1.inp hka.1 (by omega)) _)
  refine stw_wp (by simp [s2]) (hsome _ _ b2.inp (by omega) (by omega)) ?_
  have b3 := b2.frM (frM_store (k := k + 1) (by omega) (by omega) (hsome _ _ b2.inp (by omega) (by omega))
    (s2.reg .r10))
  refine WP.blk_nil ⟨b3, ?_, ?_, ?_, by simp [s2]⟩
  · exact hX.store hD' hk.2 (by omega) _ (hX.store hD' hk.1 (by omega) _ hx)
  · refine hRg _ _ (fun r hr ↦ ?_) hr
    have : r ≠ .rbp := fun e ↦ hr (by simp [e])
    simp [s2, this]
  · have hne : wd p.env.work (k + 1) ≠ wd p.env.work k :=
      fun e ↦ by have := (wd_inj (by omega) (by omega)).mp e; omega
    refine ⟨?_, ?_⟩
    · simp only [s2, QState.setMem_mem, QState.setReg_reg, ite_no hne.symm]
      simp [h9]
    · rw [wd_wd]
      simp [s2, QState.setMem_mem, h10]

theorem gok_of {hX : Dep p.env X D} (hD : ∀ k, D k → mineLo ≤ k ∧ k < dataEnd) (hRg : RegOk Rg) :
    GOk p.env p.inp fun s ↦ X s.mem ∧ Rg s.reg :=
  GOk.and (GOk.of_mine (hX.mineOnly hD)) fun _ _ hr _ hk _ ↦ hRg _ _ (fun r hr' ↦
    hk.regs r fun h ↦ hr' (List.mem_cons_of_mem _ h)) hr

/-- **`read`, stored**: every fact of the area's words not reading `k`, `k + 1`, and of the
registers the gadget keeps, kept. -/
theorem readTo_b {k : Nat} (hX : Dep p.env X D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd)
    (hk : ¬ D k ∧ ¬ D (k + 1)) (hka : mineLo ≤ k ∧ k + 1 < dataEnd) (hRg : RegOk Rg) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ Rg s.reg) (readTo k) Model.readScalar
      (fun x t s ↦ Base p t s ∧ X s.mem ∧ Rg s.reg ∧ EWAt s.mem (wd p.env.work k) x ∧
        s.reg .rbp = p.env.work) (Err p) := by
  refine Refines.of_run (m := Model.readScalar >>= pure) (fun t ↦ by rw [bind_pure]) ?_
  refine Refines.blk_cons (readScalar_b (gok_of (hX := hX) hD hRg) |>.mono
    (fun t s ⟨hb, hx, hr⟩ ↦ ⟨hb, hx, hr⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)) fun x ↦ ?_
  exact Refines.pure fun t s ⟨hb, ⟨hx, hr⟩, h9, h10⟩ ↦ storeAfter hX hD hk hka hRg hb hx hr h9 h10

/-- **`sample`, stored**, as `readTo_b`. -/
theorem sampleTo_b {k : Nat} (hX : Dep p.env X D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd)
    (hk : ¬ D k ∧ ¬ D (k + 1)) (hka : mineLo ≤ k ∧ k + 1 < dataEnd) (hRg : RegOk Rg) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ Rg s.reg) (sampleTo k) Model.sampleChallenge
      (fun x t s ↦ Base p t s ∧ X s.mem ∧ Rg s.reg ∧ EWAt s.mem (wd p.env.work k) x ∧
        s.reg .rbp = p.env.work) (Err p) := by
  refine Refines.of_run (m := Model.sampleChallenge >>= pure) (fun t ↦ by rw [bind_pure]) ?_
  refine Refines.blk_cons (sample_b (gok_of (hX := hX) hD hRg) |>.mono
    (fun t s ⟨hb, hx, hr⟩ ↦ ⟨hb, hx, hr⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)) fun x ↦ ?_
  exact Refines.pure fun t s ⟨hb, ⟨hx, hr⟩, h9, h10⟩ ↦ storeAfter hX hD hk hka hRg hb hx hr h9 h10

/-! ## Chains of gadgets -/

/-- `readTo k`, then the rest, which sees the scalar at `k`. -/
theorem readTo_then {β : Type} {k : Nat} (hX : Dep p.env X D)
    (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd) (hk : ¬ D k ∧ ¬ D (k + 1))
    (hka : mineLo ≤ k ∧ k + 1 < dataEnd) (hRg : RegOk Rg) {cs : List Stmt} {m₂ : EW → VM β}
    {Q : β → TState → QState → Prop}
    (h : ∀ x, Refines (fun t s ↦ Base p t s ∧ (X s.mem ∧ EWAt s.mem (wd p.env.work k) x) ∧ Rg s.reg)
      (blk cs) (m₂ x) Q (Err p)) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ Rg s.reg) (blk (readTo k :: cs))
      (Model.readScalar >>= m₂) Q (Err p) :=
  Refines.blk_cons (readTo_b hX hD hk hka hRg) fun x ↦ (h x).mono
    (fun _ _ ⟨hb, hx, hr, he, _⟩ ↦ ⟨hb, ⟨hx, he⟩, hr⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)

/-- `sampleTo k`, then the rest, which sees the challenge at `k`. -/
theorem sampleTo_then {β : Type} {k : Nat} (hX : Dep p.env X D)
    (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd) (hk : ¬ D k ∧ ¬ D (k + 1))
    (hka : mineLo ≤ k ∧ k + 1 < dataEnd) (hRg : RegOk Rg) {cs : List Stmt} {m₂ : EW → VM β}
    {Q : β → TState → QState → Prop}
    (h : ∀ x, Refines (fun t s ↦ Base p t s ∧ (X s.mem ∧ EWAt s.mem (wd p.env.work k) x) ∧ Rg s.reg)
      (blk cs) (m₂ x) Q (Err p)) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ Rg s.reg) (blk (sampleTo k :: cs))
      (Model.sampleChallenge >>= m₂) Q (Err p) :=
  Refines.blk_cons (sampleTo_b hX hD hk hka hRg) fun x ↦ (h x).mono
    (fun _ _ ⟨hb, hx, hr, he, _⟩ ↦ ⟨hb, ⟨hx, he⟩, hr⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)

/-- `grind bits` (`rsi := k` first), then the rest. -/
theorem grind_then {β : Type} {bits : Nat} {k : Int64} (hb0 : bits ≠ 0) (hb : bits < 2 ^ 64)
    (hk : k.toUInt64 = bits.toUInt64) (hX : Dep p.env X D)
    (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd) (hRg : RegOk Rg) {cs : List Stmt} {m₂ : Unit → VM β}
    {Q : β → TState → QState → Prop}
    (h : Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ Rg s.reg) (blk cs) (m₂ ()) Q (Err p)) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ Rg s.reg)
      (blk (I (.movi .rsi k) :: Transcript.grind :: cs)) (Model.grind bits >>= m₂) Q (Err p) := by
  refine Refines.pre_blk (P' := fun t s ↦ Base p t s ∧ (X s.mem ∧ Rg s.reg) ∧ s.reg .rsi = bits.toUInt64)
    (fun t s ⟨hb, hx, hr⟩ ↦ NativeVm.Transcript.wp_reg (s' := s.setReg .rsi k.toUInt64) rfl
      (WP.blk_nil ⟨hb.frM (frM_setReg (by decide) _), ⟨hx, hRg _ _ (fun r hr' ↦ by
        have : r ≠ .rsi := fun e ↦ hr' (by simp [e, clobbers])
        simp [this]) hr⟩, by simp [hk]⟩)) ?_
  refine Refines.blk_cons (grind_b hb0 hb (gok_of (hX := hX) hD hRg)) fun x ↦ ?_
  cases x
  exact h.mono (fun _ _ ⟨hb, hx, hr⟩ ↦ ⟨hb, hx, hr⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)

end NativeVm.Code.P7
