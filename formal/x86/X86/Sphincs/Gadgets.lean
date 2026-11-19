module

public import X86.Sphincs.Words
public import X86.Bytes

/-!
# The verifier's gadgets

What `mv`, `mv2`, `be32`, `adrs`, `hashAt` and `tweak` do to the context's words.
-/

@[expose] public section

namespace X86.SphincsVerifier

open Keccak LeanVM.Protocol.KeccakHash

/-- What `be32` computes: the four low bytes of `x` in reverse order. -/
def bs (x : UInt64) : UInt64 :=
  (x &&& 255) <<< 24 ||| ((x >>> 8) &&& 255) <<< 16 ||| ((x >>> 16) &&& 255) <<< 8 |||
    ((x >>> 24) &&& 255)

/-- Address word `j`: fields `2 j` and `2 j + 1` of the record at `adrsRec`, big-endian. -/
def adrsW (V : Nat → UInt64) (j : Nat) : UInt64 :=
  bs (V (adrsRec + 2 * j)) ||| bs (V (adrsRec + 2 * j + 1)) <<< 32

/-- The four address words. -/
def adrsWords (V : Nat → UInt64) : List UInt64 := (List.range 4).map (adrsW V)

/-- `Trunc_16` of `keccak256` of the first `len` bytes of words. -/
def th (ws : List UInt64) (len : Nat) : BitVec 128 :=
  ofWords (keccak256 ((wordsBytes ws).take len))[0] (keccak256 ((wordsBytes ws).take len))[1]

variable {base : UInt64} {V : Nat → UInt64} {s : QState} {E : QState → Prop}

/-- Run one non-memory instruction at the head of a block. -/
macro "step" : tactic => `(tactic| (apply blk_ins; simp only [QInstr.step, QState.setReg_reg,
  QState.setReg_setReg_same, QState.setMem_reg, reduceCtorEq, ite_true, ite_false]))

theorem imm_ff : (0xff : Int64).toUInt64 = 255 := rfl

theorem be32_ok (s : QState) :
    WP be32 s (fun s' ↦ s'.mem = s.mem ∧ s'.reg .rax = bs (s.reg .rax) ∧
      RegsFrame [.rax, .rcx, .rdx] s s') E := by
  unfold be32
  iterate 18 step
  apply WP.blk_nil
  refine ⟨rfl, ?_, ?_⟩
  · simp [bs, imm_ff]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

theorem mv_ok (hI : Inv base V s) {src dst : Addr} {j k : Nat}
    (hs : src.eval s = base + (8 * j).toUInt64) (hj : j < Context.ctxWords)
    (hd : dst.eval (s.setReg .rax (V j)) = base + (8 * k).toUInt64) (hk : k < Context.ctxWords) :
    WP (mv src dst) s (fun s' ↦ Inv base (Function.update V k (V j)) s' ∧ RegsFrame [.rax] s s')
      E := by
  unfold mv
  refine blk_load hI hs hj ?_
  refine blk_store (hI.setReg (by decide) _) hd hk ?_
  apply WP.blk_nil
  refine ⟨?_, fun r hr ↦ ?_⟩
  · simpa using (hI.setReg (by decide) (V j)).setMem hk (V j)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [hr]

theorem mv2_ok (hI : Inv base V s) {src dst : Nat} (hs : src + 1 < Context.ctxWords)
    (hd : dst + 1 < Context.ctxWords) (hsd : src + 1 ≠ dst) :
    WP (mv2 src dst) s (fun s' ↦ Inv base (Function.update (Function.update V dst (V src))
      (dst + 1) (V (src + 1))) s' ∧ RegsFrame [.rax] s s') E := by
  unfold mv2
  apply WP.blk_cons
  refine WP.mono (mv_ok (j := src) (k := dst) hI (by rw [cw_eval, hI.rdi]) (by omega)
    (by rw [cw_eval]; simp [hI.rdi]) (by omega)) (fun s1 ⟨h1, f1⟩ ↦ ?_) (fun _ h ↦ h)
  refine WP.mono (mv_ok (j := src + 1) (k := dst + 1) h1 (by rw [cw_eval, h1.rdi]) (by omega)
    (by rw [cw_eval]; simp [h1.rdi]) (by omega)) (fun s2 ⟨h2, f2⟩ ↦ ⟨?_, ?_⟩) (fun _ h ↦ h)
  · rwa [Function.update_of_ne (by omega)] at h2
  · intro r hr; rw [f2 r hr, f1 r hr]


theorem RegsFrame.trans {rs : List Reg64} {s₁ s₂ s₃ : QState} (h₁ : RegsFrame rs s₁ s₂)
    (h₂ : RegsFrame rs s₂ s₃) : RegsFrame rs s₁ s₃ := fun r hr ↦ (h₂ r hr).trans (h₁ r hr)

theorem RegsFrame.mono {rs rs' : List Reg64} {s₁ s₂ : QState} (h : RegsFrame rs s₁ s₂)
    (hs : ∀ r ∈ rs, r ∈ rs') : RegsFrame rs' s₁ s₂ := fun r hr ↦ h r (fun h' ↦ hr (hs r h'))

theorem RegsFrame.setReg {rs : List Reg64} {s : QState} {r : Reg64} (hr : r ∈ rs) (v : UInt64) :
    RegsFrame rs s (s.setReg r v) := fun r' hr' ↦ by
  simp only [QState.setReg_reg]
  split
  · subst_vars; exact absurd hr hr'
  · rfl

theorem adrsWord_ok (hI : Inv base V s) {buf j : Nat} (hj : j < 4)
    (hb : buf + 6 ≤ Context.ctxWords) :
    WP (adrsWord buf j) s (fun s' ↦ Inv base (Function.update V (buf + 2 + j) (adrsW V j)) s' ∧
      RegsFrame [.rax, .rcx, .rdx, .r8] s s') E := by
  unfold adrsWord
  unfold Context.ctxWords at hb
  refine blk_load_cw hI (by unfold adrsRec Context.ctxWords; omega) ?_
  apply WP.blk_cons
  refine WP.mono (be32_ok _) (fun s1 ⟨m1, r1, f1⟩ ↦ ?_) (fun _ h ↦ h)
  have hI1 : Inv base V s1 :=
    (hI.setReg (by decide) _).frame m1 (f1 .rdi (by simp))
  step; step
  refine blk_load_cw ((hI1.setReg (by decide) _).setReg (by decide) _)
    (by unfold adrsRec Context.ctxWords; omega) ?_
  apply WP.blk_cons
  refine WP.mono (be32_ok _) (fun s2 ⟨m2, r2, f2⟩ ↦ ?_) (fun _ h ↦ h)
  have hI2 : Inv base V s2 :=
    ((((hI1.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _)).frame m2
      (f2 .rdi (by simp))
  step
  refine blk_store_cw (hI2.setReg (by decide) _) (by unfold Context.ctxWords; omega) ?_
  apply WP.blk_nil
  have hr8 : s2.reg .r8 = bs (V (adrsRec + 2 * j + 1)) <<< 32 := by
    rw [f2 .r8 (by simp)]; simp [r1]
  have hw : (s2.setReg .rax (s2.reg .rax ||| s2.reg .r8)).reg .rax = adrsW V j := by
    simp only [QState.setReg_reg, ite_true, r2, hr8, adrsW]
  refine ⟨?_, ?_⟩
  · rw [← hw]; exact (hI2.setReg (by decide) _).setMem (by unfold Context.ctxWords; omega) _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [QState.setMem_reg, QState.setReg_reg, hr.1, ite_false]
    rw [f2 r (by simp [hr.1, hr.2.1, hr.2.2.1])]
    simp only [QState.setReg_reg, hr.1, hr.2.2.2, ite_false]
    rw [f1 r (by simp [hr.1, hr.2.1, hr.2.2.1])]
    simp [hr.1]

theorem adrsW_update {k : Nat} (hk : k < adrsRec ∨ adrsRec + 8 ≤ k) (v : UInt64) {j : Nat}
    (hj : j < 4) : adrsW (Function.update V k v) j = adrsW V j := by
  unfold adrsRec at hk
  simp only [adrsW, adrsRec, Function.update_apply]
  rw [ite_no (by omega), ite_no (by omega)]

theorem adrs_ok (hI : Inv base V s) {buf : Nat} (hb : buf + 6 ≤ Context.ctxWords)
    (hd : buf + 6 ≤ adrsRec ∨ adrsRec + 8 ≤ buf + 2) :
    WP (adrs buf) s (fun s' ↦ ∃ V', Inv base V' s' ∧
      (∀ k, (k < buf + 2 ∨ buf + 6 ≤ k) → V' k = V k) ∧
      (∀ j < 4, V' (buf + 2 + j) = adrsW V j) ∧ RegsFrame [.rax, .rcx, .rdx, .r8] s s') E := by
  unfold adrs
  rw [show (List.range 4).map (adrsWord buf) =
    [adrsWord buf 0, adrsWord buf 1, adrsWord buf 2, adrsWord buf 3] from rfl]
  have hu : ∀ j < 4, buf + 2 + j < adrsRec ∨ adrsRec + 8 ≤ buf + 2 + j := by omega
  apply WP.blk_cons
  refine WP.mono (adrsWord_ok (j := 0) hI (by omega) hb) (fun s1 ⟨h1, f1⟩ ↦ ?_) (fun _ h ↦ h)
  apply WP.blk_cons
  refine WP.mono (adrsWord_ok (j := 1) h1 (by omega) hb) (fun s2 ⟨h2, f2⟩ ↦ ?_) (fun _ h ↦ h)
  rw [adrsW_update (hu 0 (by omega)) _ (by omega)] at h2
  apply WP.blk_cons
  refine WP.mono (adrsWord_ok (j := 2) h2 (by omega) hb) (fun s3 ⟨h3, f3⟩ ↦ ?_) (fun _ h ↦ h)
  rw [adrsW_update (hu 1 (by omega)) _ (by omega), adrsW_update (hu 0 (by omega)) _ (by omega)]
    at h3
  apply WP.blk_cons
  refine WP.mono (adrsWord_ok (j := 3) h3 (by omega) hb) (fun s4 ⟨h4, f4⟩ ↦ ?_) (fun _ h ↦ h)
  rw [adrsW_update (hu 2 (by omega)) _ (by omega), adrsW_update (hu 1 (by omega)) _ (by omega),
    adrsW_update (hu 0 (by omega)) _ (by omega)] at h4
  refine WP.blk_nil ⟨_, h4, fun k hk ↦ ?_, fun j hj ↦ ?_, RegsFrame.trans f1 (RegsFrame.trans f2 (RegsFrame.trans f3 f4))⟩
  · simp only [Function.update_apply]
    rw [ite_no (by omega), ite_no (by omega), ite_no (by omega), ite_no (by omega)]
  · simp only [Function.update_apply]
    interval_cases j <;> simp

theorem hashAt_ok (hb : Fits base) (hI : Inv base V s) {buf len : Nat} (hj : scratchWords ≤ buf)
    (hjn : buf + (len + 7) / 8 ≤ Context.ctxWords) (hlen0 : 0 < len) (hlen : len < 2 ^ 31)
    (hz : ∀ b ∈ (wordsBytes (words V buf ((len + 7) / 8))).drop len, b = 0) :
    WP (hashAt buf len) s (fun s' ↦ ∃ V', Inv base V' s' ∧ (∀ k, scratchWords ≤ k → V' k = V k) ∧
      (∀ k (hk : k < 4), V' k =
        (keccak256 ((wordsBytes (words V buf ((len + 7) / 8))).take len))[k]) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') E := by
  unfold hashAt
  step; step
  apply WP.blk_cons
  have hI' := (hI.setReg (d := .rsi) (by decide) ((cw buf).eval s)).setReg (d := .rbx) (by decide)
    (len.toInt64.toUInt64)
  refine WP.mono (hash_ok hb hI' (j := buf) (len := len) (by simp [cw_eval, hI.rdi])
    (by simp) hj hjn hlen0 (by omega) hz) (fun s' ⟨V', h1, h2, h3, h4⟩ ↦
      WP.blk_nil ⟨V', h1, h2, h3, ?_⟩) (fun _ h ↦ h)
  intro r hr
  rw [h4 r hr]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.2.1, hr.2.2.2.2.1]

/-- The words `tweak buf len` hashes: the buffer's first two, the address's four, the rest. -/
def tweakWords (V : Nat → UInt64) (buf len : Nat) : List UInt64 :=
  [V buf, V (buf + 1)] ++ adrsWords V ++ words V (buf + 6) ((len + 7) / 8 - 6)

theorem tweak_ok (hb : Fits base) (hI : Inv base V s) {buf len dst : Nat}
    (hj : scratchWords ≤ buf) (hjn : buf + (len + 7) / 8 ≤ Context.ctxWords) (hlen6 : 48 ≤ len)
    (hlen : len < 2 ^ 31) (hd : buf + 6 ≤ adrsRec ∨ adrsRec + 8 ≤ buf + 2)
    (hdst : scratchWords ≤ dst) (hdst' : dst + 1 < Context.ctxWords)
    (hz : ∀ b ∈ (wordsBytes (tweakWords V buf len)).drop len, b = 0) :
    WP (tweak buf len dst) s (fun s' ↦ ∃ V', Inv base V' s' ∧
      (∀ k, scratchWords ≤ k → (k < buf + 2 ∨ buf + 6 ≤ k) → k ≠ dst → k ≠ dst + 1 → V' k = V k) ∧
      V' dst = digestLo (th (tweakWords V buf len) len) ∧
      V' (dst + 1) = digestHi (th (tweakWords V buf len) len) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] s s') E := by
  unfold tweak
  have hsw : scratchWords = 84 := rfl
  apply WP.blk_cons
  refine WP.mono (adrs_ok hI (by omega) hd) (fun s1 ⟨V1, h1, e1, a1, f1⟩ ↦ ?_) (fun _ h ↦ h)
  have hw : words V1 buf ((len + 7) / 8) = tweakWords V buf len := by
    obtain ⟨n, hn⟩ : ∃ n, (len + 7) / 8 = n + 6 := ⟨(len + 7) / 8 - 6, by omega⟩
    unfold tweakWords adrsWords
    rw [hn, Nat.add_sub_cancel, Nat.add_comm n 6, words_add]
    congr 1
    · simp only [words, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl,
        show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, List.cons.injEq, and_true]
      exact ⟨e1 _ (by omega), e1 _ (by omega), a1 0 (by omega), a1 1 (by omega), a1 2 (by omega),
        a1 3 (by omega)⟩
    · exact words_congr fun i _ ↦ e1 _ (by omega)
  apply WP.blk_cons
  refine WP.mono (hashAt_ok hb h1 hj hjn (by omega) hlen (hw ▸ hz))
    (fun s2 ⟨V2, h2, e2, d2, f2⟩ ↦ ?_) (fun _ h ↦ h)
  rw [hw] at d2
  apply WP.blk_cons
  refine WP.mono (mv2_ok h2 (src := 0) (dst := dst) (by unfold Context.ctxWords; omega) hdst'
    (by omega)) (fun s3 ⟨h3, f3⟩ ↦ WP.blk_nil ⟨_, h3, fun k hk hk' h1 h2 ↦ ?_, ?_, ?_, ?_⟩)
    (fun _ h ↦ h)
  · simp only [Function.update_apply, ite_no h1, ite_no h2]
    rw [e2 k hk, e1 k hk']
  · rw [Function.update_of_ne (by omega), Function.update_self, d2 0 (by omega), th,
      digestLo_ofWords]
  · rw [Function.update_self, d2 1 (by omega), th, digestHi_ofWords]
  · intro r hr
    rw [f3 r (fun h ↦ hr (by simp_all)), f2 r hr, f1 r (fun h ↦ hr (by simp_all))]

end X86.SphincsVerifier
