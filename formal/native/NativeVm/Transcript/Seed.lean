module

public import NativeVm.Transcript.SeedBytes

/-!
# The seed

`seed_spec`: from the context the decoder leaves (`SeedPre`: the areas, the decoded proof, the
bytecode's words and the public input's), `seed` ends in a state that simulates `runProof`'s initial
state, the sponge at `spongeSeedWith keccakF1600 bytecode publicInput`. It builds the hash input in
the working area (`seedBuffer_spec`, words `seedWords`), hashes it, permutes the IV and the public
input into the sponge (`seedState_spec`) and sets the cursors (`seedCursors_spec`).
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

variable {env : Env} {s : QState} {P Q : QState → Prop}

/-- The words of the seed's hash input in the working area. -/
def BufIn (env : Env) (n : Nat) (a : UInt64) : Prop := ∃ k < n + 2, a = wd env.work k

/-- **What `seed` needs**: the context as the decoder leaves it, the bytecode `bc` at `bcA` and the
public input `pub`, and room for the hash input (`bc.length + 2` words) in the working area. -/
structure SeedPre (env : Env) (bcA : UInt64) (bc : List K) (pub : Digest) (s : QState) : Prop where
  rdi : s.reg .rdi = env.ctx
  layout : Layout env s.mem
  decoded : Decoded s.mem env.dec env.L env.proof
  wireLen : s.mem (wd env.ctx ctxWireLen) = some env.L.toUInt64
  L64 : env.L < 2 ^ 64
  bcPtr : s.mem (wd env.ctx ctxBytecode) = some bcA
  bcLen : s.mem (wd env.ctx ctxBytecodeLen) = some bc.length.toUInt64
  bcWords : ∀ i (h : i < bc.length), s.mem (wd bcA i) = some bc[i].lane
  pubWords : ∀ i (h : i < 4), s.mem (wd env.ctx (ctxPublic + i)) = some pub[i]
  bcSmall : 8 * bc.length + 9 < 2 ^ 32
  fitBc : Fits bcA bc.length
  fitBuf : Fits env.work (bc.length + 2)
  bufSome : ∀ k < bc.length + 2, (s.mem (wd env.work k)).isSome
  disjBufCtx : Disj env.work (bc.length + 2) env.ctx ctxEnd
  disjBufDec : Disj env.work (bc.length + 2) env.dec (decodedWords env.L)
  disjBufBc : Disj env.work (bc.length + 2) bcA bc.length

theorem seedWords_getD_succ (bc : List K) (c : Nat) :
    (seedWords bc).getD (c + 1) 0 = (shiftWords 0x31 (bc.map K.lane)).getD c 0 := by
  simp [seedWords]

theorem lanes_getD (bc : List K) (c : Nat) (hc : c < bc.length) :
    (bc.map K.lane).getD c 0 = bc[c].lane := by
  simp [List.getD_eq_getElem?_getD, hc]

/-- **The shifting loop.** -/
theorem shiftLoop_spec {bcA : UInt64} {bc : List K}
    (hbcw : ∀ i (h : i < bc.length), s.mem (wd bcA i) = some bc[i].lane)
    (hsome : ∀ k < bc.length + 2, (s.mem (wd env.work k)).isSome) (hsmall : 8 * bc.length + 9 < 2 ^ 32)
    (hfitBc : Fits bcA bc.length) (hfitBuf : Fits env.work (bc.length + 2))
    (hdisj : Disj env.work (bc.length + 2) bcA bc.length)
    (hrcx : s.reg .rcx = 0) (hrdx : s.reg .rdx = 0x31) (hrsi : s.reg .rsi = bcA)
    (hr9 : s.reg .r9 = bc.length.toUInt64) (hr11 : s.reg .r11 = env.work) :
    WP shiftLoop s (fun s' ↦ s'.reg .rcx = bc.length.toUInt64 ∧
      s'.reg .rdx = shiftPrev 0x31 (bc.map K.lane) bc.length ∧
      (∀ i < bc.length, s'.mem (wd env.work (1 + i)) = some ((shiftWords 0x31 (bc.map K.lane)).getD i 0)) ∧
      (∀ a, (∀ i < bc.length, a ≠ wd env.work (1 + i)) → s'.mem a = s.mem a) ∧
      RegsFrame [.rax, .rcx, .rdx, .r8] s s') Q := by
  set n := bc.length with hn
  set lanes := bc.map K.lane with hlanes
  have hn32 := hsmall
  have hbuf : ∀ i, i < n → ∀ j, j < n → wd env.work (1 + i) ≠ wd bcA j := fun i hi j hj ↦
    wd_ne_of_disj hfitBuf hfitBc hdisj (by omega) hj
  refine WP.loop (fun s' ↦ ∃ c ≤ n, s'.reg .rcx = c.toUInt64 ∧
      s'.reg .rdx = shiftPrev 0x31 lanes c ∧
      (∀ i < c, s'.mem (wd env.work (1 + i)) = some ((shiftWords 0x31 lanes).getD i 0)) ∧
      (∀ a, (∀ i < c, a ≠ wd env.work (1 + i)) → s'.mem a = s.mem a) ∧
      RegsFrame [.rax, .rcx, .rdx, .r8] s s')
    (fun s' ↦ n - (s'.reg .rcx).toNat) ⟨0, by omega, hrcx, by rw [hrdx]; rfl,
      fun i hi ↦ absurd hi (by omega), fun _ _ ↦ rfl, rf_refl _ _⟩ ?_ ?_
  · rintro s' ⟨c, hc, h1, h2, h3, h4, h5⟩ hcond
    have hcn : c < n := by
      rw [cond_ltu, rhs_reg, decide_eq_true_eq, h1, h5 _ (by simp), hr9,
        toUInt64_lt (by omega) (by omega)] at hcond
      exact hcond
    have hrsi' : s'.reg .rsi = wd bcA 0 := by rw [h5 _ (by simp), hrsi, wd_zero]
    have hr11' : s'.reg .r11 = wd env.work 0 := by rw [h5 _ (by simp), hr11, wd_zero]
    have hbc : s'.mem (wd bcA (0 + c + 0)) = some (lanes.getD c 0) := by
      rw [h4 _ (fun i hi e ↦ hbuf i (by omega) c hcn (e.symm.trans (by simp))), Nat.zero_add,
        Nat.add_zero, hbcw c hcn, hlanes, lanes_getD bc c hcn]
    refine wp_load (eval_idx64' hrsi' h1 (k := 0) rfl) hbc ?_
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))
    refine wp_store ((eval_idx64' (k := 1) (by reg_simp; exact hr11') (by reg_simp; exact h1) rfl).trans
      (show wd env.work (0 + c + 1) = wd env.work (1 + c) by congr 1; omega)) (by
      rw [QState.setReg_mem, QState.setReg_mem, QState.setReg_mem, QState.setReg_mem,
        h4 _ (fun i hi e ↦ ?_)]
      · exact hsome _ (by omega)
      · rw [wd_inj (by omega) (by omega)] at e
        omega) ?_
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_done ⟨⟨c + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)))
    · reg_simp; rw [h1, toUInt64_succ]
    · reg_simp
      simp only [shiftPrev, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rfl
    · intro i hi
      reg_simp
      rw [QState.setMem_mem]
      by_cases e : i = c
      · subst e
        simp only [↓reduceIte]
        rw [shiftWords_getD _ _ _ (by simp [hlanes]; omega), h2]
        simp only [show i < lanes.length by simp [hlanes]; omega, ↓reduceIte]
        rfl
      · rw [ite_of_not (by rw [wd_inj (by omega) (by omega)]; omega)]
        exact h3 i (by omega)
    · intro a ha
      reg_simp
      rw [QState.setMem_mem, ite_of_not (ha c (by omega))]
      exact h4 a fun i hi ↦ ha i (by omega)
    · rf_tac
      exact h5
    · reg_simp
      rw [h1, toUInt64_succ, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro s' ⟨c, hc, h1, h2, h3, h4, h5⟩ hcond
    have hcn : c = n := by
      rw [cond_ltu, rhs_reg, decide_eq_false_iff_not, h1, h5 _ (by simp), hr9,
        toUInt64_lt (by omega) (by omega)] at hcond
      omega
    subst hcn
    exact ⟨h1, h2, h3, h4, h5⟩

/-- **The hash input**: `seedWords bc` in the working area's first `bc.length + 2` words. -/
theorem seedBuffer_spec {bcA : UInt64} {bc : List K} {pub : Digest} (h : SeedPre env bcA bc pub s) :
    WP seedBuffer s (fun s' ↦
      (∀ i < bc.length + 2, s'.mem (wd env.work i) = some ((seedWords bc).getD i 0)) ∧
      (∀ a, (∀ k < bc.length + 2, a ≠ wd env.work k) → s'.mem a = s.mem a) ∧
      s'.reg .r9 = bc.length.toUInt64 ∧ s'.reg .r11 = env.work ∧
      RegsFrame [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r11] s s') Q := by
  set n := bc.length with hn
  have hn32 := h.bcSmall
  unfold seedBuffer
  refine wp_load (eval_cw h.rdi _) h.layout.workPtr ?_
  refine wp_load (eval_cw (by reg_simp; exact h.rdi) _) h.bcPtr ?_
  refine wp_load (eval_cw (by reg_simp; exact h.rdi) _) h.bcLen (wp_reg rfl ?_)
  refine wp_store (x := wd env.work 0) (by rw [eval_at0]; reg_simp; exact (wd_zero _).symm)
    (h.bufSome 0 (by omega)) (wp_reg rfl (wp_reg rfl ?_))
  have hne0 : ∀ i, i < n → wd bcA i ≠ wd env.work 0 := fun i hi e ↦
    wd_ne_of_disj h.fitBuf h.fitBc h.disjBufBc (by omega) hi e.symm
  refine wp_then (shiftLoop_spec (bc := bc) (bcA := bcA) (fun i hi ↦ ?_) (fun k hk ↦ ?_) hn32 h.fitBc
    h.fitBuf h.disjBufBc (by reg_simp) (by reg_simp; rfl) (by reg_simp) (by reg_simp)
    (by reg_simp)) ?_
  · reg_simp
    rw [QState.setMem_mem, ite_of_not (hne0 i hi)]
    exact h.bcWords i hi
  · reg_simp
    rw [isSome_setMem _ _ (by reg_simp; exact h.bufSome 0 (by omega))]
    reg_simp
    exact h.bufSome k hk
  rintro s₁ ⟨h1, h2, h3, h4, h5⟩
  have hr11 : s₁.reg .r11 = wd env.work 0 := by rw [h5 .r11 (by simp)]; reg_simp; exact (wd_zero _).symm
  refine wp_store ((eval_idx64' (k := 1) hr11 h1 rfl).trans
      (show wd env.work (0 + n + 1) = wd env.work (1 + n) by congr 1; omega))
    (by
      rw [h4 _ (fun i hi e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega)]
      reg_simp
      rw [isSome_setMem _ _ (by reg_simp; exact h.bufSome 0 (by omega))]
      reg_simp
      exact h.bufSome _ (by omega))
    (wp_done ⟨fun i hi ↦ ?_, fun a ha ↦ ?_, ?_, ?_, ?_⟩)
  · rw [QState.setMem_mem]
    by_cases hin : i = 1 + n
    · subst hin
      simp only [↓reduceIte]
      rw [show 1 + n = n + 1 by omega, seedWords_getD_succ, shiftWords_getD _ _ _ (by simp; omega), h2]
      simp [hn]
    · rw [ite_of_not (by rw [wd_inj (by omega) (by omega)]; exact hin)]
      by_cases hi0 : i = 0
      · subst hi0
        rw [h4 _ (fun j hj e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega)]
        reg_simp
        rw [QState.setMem_mem]
        simp [seedWords]
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [show j + 1 = 1 + j by omega, h3 j (by omega), show 1 + j = j + 1 by omega,
          seedWords_getD_succ]
  · rw [QState.setMem_mem, ite_of_not (ha _ (by omega)), h4 a (fun i hi ↦ ha _ (by omega))]
    reg_simp
    rw [QState.setMem_mem, ite_of_not (ha _ (by omega))]
    rfl
  · rw [QState.setMem_reg, h5 .r9 (by simp)]; reg_simp; rfl
  · rw [QState.setMem_reg, h5 .r11 (by simp)]; reg_simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hr
    rw [QState.setMem_reg, h5 r (by simp [a1, a2, a3, a5])]
    reg_simp
    simp [a1, a2, a3, a4, a6, a7]

end NativeVm.Transcript
