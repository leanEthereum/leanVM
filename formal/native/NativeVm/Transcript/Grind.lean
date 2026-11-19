module

public import NativeVm.Transcript.Sample

/-!
# `grind`

`grind_spec`: from a state that simulates `st`, with `bits` in `rsi`, `grind` ends in a state that
simulates `grindStep bits st`'s, or fails when it is `none` (a ground challenge waits, the stream is
consumed, or the proof of work fails). `nextAbsorb_then` is the next scalar read and absorbed, which
`grind` and `commit` share.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

variable {env : Env} {st : VerifierProgramState} {s : QState} {P Q : QState → Prop}

/-- **The next scalar, absorbed with `tag`**, no challenge waiting: the run continues from a state
that simulates the scalar absorbed and the stream advanced, the scalar's limbs in `r9`, `r10`; it
fails at the stream's end. -/
theorem nextAbsorb_then {tag : Nat} {rest : List Stmt} (h : SimState env st s)
    (hnil : st.stream = [] → ∀ s', Q s')
    (k : ∀ x xs s', st.stream = x :: xs →
      SimState env ⟨Id.run (Compile.absorb (m := Id) keccakF1600 st.sponge x tag), xs, st.openings,
        st.roots⟩ s' →
      s'.reg .r9 = (x.limb 0).lane → s'.reg .r10 = (x.limb 1).lane →
      (∀ k, k < workWords → k ≠ workCursor → s'.mem (wd env.work k) = s.mem (wd env.work k)) →
      Keeps [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] (Foot env) s s' → WP (blk rest) s' P Q) :
    WP (blk (nextScalar :: absorb tag :: rest)) s P Q := by
  obtain ⟨c, hc, hcw, hst⟩ := h.cursor
  refine wp_then' (WP.mono (nextScalar_spec h hc hcw) (fun s' h' ↦ h') ?_) ?_
  · intro _ hle
    exact hnil (by rw [hst, List.drop_eq_nil_of_le hle]) _
  rintro s₂ ⟨hlt, h9, h10, hm₂, hr₂⟩ d₂
  have hrdi₂ : s₂.reg .rdi = env.ctx := by rw [hr₂ _ (by simp)]; exact h.rdi
  have hsp₂ : SpongeAt s₂.mem env.ctx st.sponge := h.sponge.congr fun k _ _ ↦ by
    rw [hm₂, Function.update_of_ne (h.layout.work_ne_ctx (by lay_omega) (by lay_omega)).symm]
  refine wp_then' (absorb_spec (tag := tag) hrdi₂ hsp₂ ((h.layout.dom).of_isSome d₂) h9 h10) ?_
  rintro s₃ ⟨hsp₃, hk₃, hr₃⟩ d₃
  have hst' : st.stream = env.proof.stream[c] :: env.proof.stream.drop (c + 1) := by
    rw [hst, drop_eq_cons hlt]
  have hm₃ : ∀ k, k < workWords → s₃.mem (wd env.work k) = s₂.mem (wd env.work k) :=
    fun k hk ↦ hk₃ _ (h.layout.work_not_ctxIn (by lay_omega) hk)
  have hk : Keep (Foot env) s.mem s₃.mem := by
    intro a ha
    rw [hk₃ a (fun h' ↦ ha (foot_ctx h' le_rfl (by lay_omega))), hm₂,
      Function.update_of_ne (fun e ↦ ha (by rw [e]; exact foot_work (by lay_omega)))]
  have hw : ∀ k, k < workWords → k ≠ workCursor → s₃.mem (wd env.work k) = s.mem (wd env.work k) :=
    fun k hk hne ↦ by
      rw [hm₃ k hk, hm₂, Function.update_of_ne (by rw [Ne, wd_inj (by lay_omega) (by lay_omega)]; exact hne)]
  refine k _ _ s₃ hst' (SimState.mk' h ?_ ?_ hk hsp₃ ?_ ?_ ?_ h.rootsLen ?_ ?_) ?_ ?_ hw ?_
  · rw [hr₃ _ (by simp), hrdi₂]
  · intro a; rw [d₃, d₂]
  · refine ⟨c + 1, hlt, ?_, rfl⟩
    rw [hm₃ _ (by lay_omega), hm₂, Function.update_self]
  · obtain ⟨p, hp, h1, h2, h3⟩ := h.phase
    exact ⟨p, hp, (hw _ (by lay_omega) (by lay_omega)).trans h1,
      (hw _ (by lay_omega) (by lay_omega)).trans h2, h3⟩
  · exact (hw _ (by lay_omega) (by lay_omega)).trans h.phaseCount
  · exact (hw _ (by lay_omega) (by lay_omega)).trans h.rootCount
  · intro j hj
    obtain ⟨r1, r2, r3, r4, r5⟩ := h.roots j hj
    have hj8 : j < 8 := lt_of_lt_of_le hj h.rootsLen
    exact ⟨fun k hk ↦ (hw _ (by lay_omega) (by lay_omega)).trans (r1 k hk), r2, r3,
      (hw _ (by lay_omega) (by lay_omega)).trans r4, (hw _ (by lay_omega) (by lay_omega)).trans r5⟩
  · rw [hr₃ _ (by simp), h9]
  · rw [hr₃ _ (by simp), h10]
  · refine ⟨by rw [hr₃ _ (by simp), hrdi₂, h.rdi], fun r hr ↦ ?_, hk⟩
    rw [hr₃ r (by simp_all), hr₂ r (by simp_all)]

/-! ## The proof of work -/

theorem pow_mask_lt (x : UInt64) {bits : Nat} (hb : bits < 64) :
    (x &&& ((1 : UInt64) <<< (bits.toUInt64 &&& 63) - 1) = 0) ↔ x.toNat % 2 ^ bits = 0 := by
  have h63 : bits.toUInt64 &&& 63 = bits.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, toNat_toUInt64 (by omega)]
    show bits &&& 63 = bits
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hpos : 1 ≤ 2 ^ bits := Nat.one_le_two_pow
  have hlt : 2 ^ bits < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hb
  have hm : ((1 : UInt64) <<< (bits.toUInt64 &&& 63) - 1).toNat = 2 ^ bits - 1 := by
    rw [h63, UInt64.toNat_sub, UInt64.toNat_shiftLeft, toNat_toUInt64 (by omega)]
    simp only [UInt64.reduceToNat, Nat.mod_eq_of_lt hb, Nat.one_shiftLeft, Nat.mod_eq_of_lt hlt]
    omega
  rw [← UInt64.toNat_inj, UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem pow_mask_ge (x : UInt64) {bits : Nat} (hb : 64 ≤ bits) :
    (x &&& (-1 : Int64).toUInt64 = 0) ↔ x.toNat % 2 ^ bits = 0 := by
  have hx := x.toNat_lt
  have : 2 ^ 64 ≤ 2 ^ bits := Nat.pow_le_pow_right (by omega) hb
  rw [Nat.mod_eq_of_lt (by omega), show (-1 : Int64).toUInt64 = 0xFFFFFFFFFFFFFFFF from rfl]
  rw [← UInt64.toNat_inj, UInt64.toNat_and]
  simp only [UInt64.reduceToNat]
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hx]

/-- The mask the code computes: `bits` low ones. -/
def powMask (bits : Nat) : UInt64 :=
  if 64 ≤ bits then (-1 : Int64).toUInt64 else (1 : UInt64) <<< (bits.toUInt64 &&& 63) - 1

theorem powOk_iff (x : UInt64) (bits : Nat) : powOk bits x = true ↔ x &&& powMask bits = 0 := by
  unfold powOk powMask
  rw [decide_eq_true_iff]
  split
  · exact (pow_mask_ge x (by omega)).symm
  · exact (pow_mask_lt x (by omega)).symm

theorem absorbNonce_eq (sp : Sponge) (n : E) :
    Id.run (absorbNonce (m := Id) keccakF1600 sp n) =
      (Keccak.lane (keccakF1600 (duplexInput (Id.run (Compile.absorb (m := Id) keccakF1600 sp n
        dsPowNonce)))) 2,
       { Id.run (Compile.duplex (m := Id) keccakF1600 (Id.run (Compile.absorb (m := Id) keccakF1600 sp
          n dsPowNonce))) with
         ground := some (challengeOf (keccakF1600 (duplexInput (Id.run (Compile.absorb (m := Id)
          keccakF1600 sp n dsPowNonce))))) }) := (rfl)

/-- The ground challenge set. -/
theorem SpongeAt.setGround {ctx : UInt64} {sp : Sponge} {c : E} {m : UInt64 → Option UInt64}
    (h : SpongeAt m ctx sp) {m' : UInt64 → Option UInt64}
    (hm : ∀ k, laneW ≤ k → k < groundW → m' (wd ctx k) = m (wd ctx k))
    (h0 : m' (wd ctx groundW) = some 1) (h1 : m' (wd ctx (groundW + 1)) = some (c.limb 0).lane)
    (h2 : m' (wd ctx (groundW + 2)) = some (c.limb 1).lane) :
    SpongeAt m' ctx { sp with ground := some c } where
  lanes i hi := (hm _ (by lay_omega) (by lay_omega)).trans (h.lanes i hi)
  pendingLen := h.pendingLen
  count := (hm _ (by lay_omega) (by lay_omega)).trans h.count
  rate i hi := (hm _ (by lay_omega) (by lay_omega)).trans (h.rate i hi)
  ground := ⟨h0, h1, h2⟩

/-- The mask's last step: all ones from `64` bits on. -/
theorem mask_spec {bits : Nat} (hb : bits < 2 ^ 64) (hrsi : s.reg .rsi = bits.toUInt64)
    (hrdx : s.reg .rdx = (1 : UInt64) <<< (bits.toUInt64 &&& 63) - 1) :
    WP (.ite (.cmp .geu .rsi (.imm 64)) (I (.movi .rdx (-1))) .skip) s
      (fun s' ↦ s'.reg .rdx = powMask bits ∧ s'.mem = s.mem ∧ RegsFrame [.rdx] s s') Q := by
  by_cases h64 : 64 ≤ bits
  · refine wp_ite_true ?_ (WP.ins rfl ⟨?_, rfl, ?_⟩)
    · rw [cond_geu, rhs_imm]
      refine decide_eq_true ?_
      rw [hrsi, show Int64.toUInt64 64 = (64 : Nat).toUInt64 from rfl, toUInt64_le (by omega) hb]
      exact h64
    · reg_simp; simp [powMask, h64]
    · rf_tac
  · refine wp_ite_false ?_ (WP.skip ⟨?_, rfl, rf_refl _ _⟩)
    · rw [cond_geu, rhs_imm]
      refine decide_eq_false ?_
      rw [hrsi, show Int64.toUInt64 64 = (64 : Nat).toUInt64 from rfl, toUInt64_le (by omega) hb]
      exact h64
    · simp only [powMask, h64, ↓reduceIte]
      exact hrdx

/-- **`grind bits`**, `bits` in `rsi`. -/
theorem grind_spec {bits : Nat} (h : SimState env st s) (hb : bits < 2 ^ 64)
    (hrsi : s.reg .rsi = bits.toUInt64) :
    WP grind s (fun s' ↦ ∃ st', grindStep bits st = some st' ∧ SimState env st' s' ∧
      Keeps clobbers (Foot env) s s') (fun _ ↦ grindStep bits st = none) := by
  unfold grind
  refine wp_then (WP.mono (checkGround_spec h.rdi h.sponge.ground) (fun s' h' ↦ h') ?_) ?_
  · intro _ hg
    unfold grindStep
    obtain ⟨g, hg'⟩ := Option.isSome_iff_exists.mp hg
    rw [hg']
    cases st.stream <;> rfl
  rintro s₁ ⟨hg, rfl⟩
  have h₁ : SimState env st (s.setReg .rax 0) := ⟨by reg_simp; exact h.rdi, h.layout, h.decoded,
    h.sponge, h.cursor, h.phase, h.phaseCount, h.rootsLen, h.rootCount, h.roots⟩
  refine nextAbsorb_then h₁ (fun hn _ ↦ by unfold grindStep; rw [hn]) ?_
  intro n xs s₂ hst h₂ _ _ _ k₂
  set sp₁ := Id.run (Compile.absorb (m := Id) keccakF1600 st.sponge n dsPowNonce) with hsp₁
  have hdom₂ := h₂.layout.dom
  refine wp_then' (duplex_spec h₂.rdi h₂.sponge hdom₂) ?_
  rintro s₃ ⟨hsp₃, k₃, r₃⟩ d₃
  have hrdi₃ : s₃.reg .rdi = env.ctx := by rw [r₃ _ (by simp)]; exact h₂.rdi
  have hdom₃ := hdom₂.of_isSome d₃
  set A := keccakF1600 (duplexInput sp₁) with hA
  have l0 := hsp₃.lanes 0 (by omega)
  have l1 := hsp₃.lanes 1 (by omega)
  have l2 := hsp₃.lanes 2 (by omega)
  rw [duplex_eq'] at l0 l1 l2
  rw [Nat.add_zero] at l0
  have hrsi₃ : s₃.reg .rsi = bits.toUInt64 := by
    rw [r₃ _ (by simp), k₂.regs _ (by simp)]; reg_simp; exact hrsi
  refine wp_load (eval_cw hrdi₃ _) l0 ?_
  refine wp_store (eval_cw (by reg_simp; exact hrdi₃) _) (by some_tac) ?_
  refine wp_load (eval_cw (by reg_simp; exact hrdi₃) _) (by mem_simp; exact l1) ?_
  refine wp_store (eval_cw (by reg_simp; exact hrdi₃) _) (by some_tac) ?_
  refine wp_storei (eval_cw (by reg_simp; exact hrdi₃) _) (by some_tac) ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  refine wp_then (mask_spec hb (by reg_simp; exact hrsi₃) (by reg_simp; rw [hrsi₃])) ?_
  rintro s₅ ⟨m₅, hm₅, r₅⟩
  have hrdi₅ : s₅.reg .rdi = env.ctx := by rw [r₅ _ (by simp)]; reg_simp; exact hrdi₃
  refine wp_load (eval_cw hrdi₅ _) (by rw [hm₅]; mem_simp; exact l2) (wp_reg rfl ?_)
  set stF : VerifierProgramState := { st with sponge := { Id.run (Compile.duplex (m := Id)
    keccakF1600 sp₁) with ground := some (challengeOf A) }, stream := xs } with hstF
  have hgrind : grindStep bits st = if powOk bits (Keccak.lane A 2) then some stF else none := by
    unfold grindStep
    rw [hst, hg]
    simp only [absorbNonce_eq, ← hsp₁, ← hA, hstF]
  by_cases hok : powOk bits (Keccak.lane A 2) = true
  · refine wp_failIf ?_ (wp_done ⟨stF, by rw [hgrind]; simp only [hok, ↓reduceIte], ?_, ?_⟩)
    · simp only [Cond.eval, Rhs.eval]
      reg_simp
      rw [m₅, (powOk_iff _ _).mp hok]
      rfl
    · have hk₄ : Keep (CtxIn env.ctx scratchW (groundW + 3)) s₂.mem s₃.mem :=
        k₃.mono fun a ha ↦ ha.mono le_rfl (by lay_omega)
      refine SimState.withSponge h₂ (by reg_simp; exact hrdi₅) (fun a ↦ ?_) ?_ ?_
      · simp only [QState.setReg_mem, hm₅]
        isSome_tac
        exact d₃ a
      · simp only [QState.setReg_mem, hm₅]
        refine Keep.setMem (Keep.setMem (Keep.setReg (Keep.setMem (Keep.setReg hk₄ _ _)
          (CtxIn.word (by lay_omega) (by lay_omega)) _) _ _) (CtxIn.word (by lay_omega)
          (by lay_omega)) _) (CtxIn.word (by lay_omega) (by lay_omega)) _
      · simp only [QState.setReg_mem, hm₅]
        refine SpongeAt.setGround hsp₃ (fun k h1 h2 ↦ ?_) ?_ ?_ ?_
        · mem_simp
        · mem_simp
        · mem_simp; rw [challengeOf_limb0]
        · mem_simp; rw [challengeOf_limb1]
    · refine ⟨by reg_simp; rw [hrdi₅, h.rdi], fun r hr ↦ ?_, fun a ha ↦ ?_⟩
      · have hr' : r ∉ [Reg64.rax, .rcx, .rdx, .r8, .r9, .r10, .r11] := by simp_all [clobbers]
        reg_simp
        have : r ≠ .rax := by simp_all [clobbers]
        simp only [this, ↓reduceIte]
        rw [r₅ r (by simp_all [clobbers])]
        reg_simp
        have : r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r9 := by simp_all [clobbers]
        simp only [this.1, this.2.1, this.2.2, ↓reduceIte]
        rw [r₃ r (by simp_all [clobbers]), k₂.regs r hr']
        reg_simp
        simp_all [clobbers]
      · simp only [QState.setReg_mem, hm₅, QState.setMem_mem]
        have hne : ∀ k, scratchW ≤ k → k < ctxEnd → a ≠ wd env.ctx k := fun k h1 h2 e ↦
          ha (.inl ⟨k, h1, h2, e⟩)
        rw [ite_of_not (hne _ (by lay_omega) (by lay_omega)),
          ite_of_not (hne _ (by lay_omega) (by lay_omega)),
          ite_of_not (hne _ (by lay_omega) (by lay_omega)),
          k₃ a (fun h' ↦ ha (foot_ctx h' le_rfl (by lay_omega))), k₂.mem a ha]
        rfl
  · refine wp_failIf_fail ?_ (by rw [hgrind]; simp only [hok, ↓reduceIte, Bool.false_eq_true])
    simp only [Cond.eval, Rhs.eval]
    reg_simp
    rw [m₅]
    have := mt (powOk_iff (Keccak.lane A 2) bits).mpr hok
    simpa using this

end NativeVm.Transcript
