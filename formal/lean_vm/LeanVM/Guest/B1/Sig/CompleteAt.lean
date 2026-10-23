/-
  LeanVM.Guest.B1.Sig.CompleteAt

  The signature verifiers complete in the uniform placed form (`CompleteRel`): the claim's words
  lie in the caller's words, the range checks read below `2^κ`, and the call tree is the one a
  single memory gives, transferred to every memory holding the caller's words.
-/

module

public import LeanVM.Guest.B1.Sig.Placed
public import LeanVM.Guest.B1.Sig.SphincsIff
public import LeanVM.Guest.B1.G1Placed
public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.B1.Da.RelIn

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Sig

@[expose] public section

namespace Sig

/-! ## Loads and calls of the verifiers' walks -/

theorem loads_claim {σ : Val} {D : List String} {es : List Ev} (h : ∀ e ∈ es, EvSigOk claimLoad D e) :
    ∀ A ∈ loadAddrs σ es, ∃ off < 4, A = (σ (.n 0)).limb 0 * gpow off := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      simp only [EvSigOk, claimLoad, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact ⟨off, hok.2, by rw [← hea, hok.1]⟩
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

theorem loads_none {σ : Val} {D : List String} {es : List Ev} (h : ∀ e ∈ es, EvSigOk noLoad D e) :
    ∀ A ∈ loadAddrs σ es, False := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load d p off => simp [EvSigOk, noLoad] at hok
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

theorem calls_in {lok : Atom → Bool} {D : List String} {es : List Ev} (h : ∀ e ∈ es, EvSigOk lok D e)
    {c : Call} (hc : c ∈ calls es) (ht : c.taken = true) : c.f ∈ D :=
  h _ (Digest.mem_calls_taken hc ht)

/-! ## The claim lies in the caller's words -/

theorem claimCells_canonical (r pa : BitVec 128) (m : BitVec 256) : ∀ k, IsCanonical128 (claimCells r pa m k) := by
  intro k
  fin_cases k <;> exact isCanonical128_cellOf _

/-- **The claim's words lie in `Lin`**, when every memory defined below `2^κ` and holding `Lin`
holds some claim at `p`: elsewhere a memory could hold a word no claim has. -/
theorem claim_region {κ : ℕ} {Lin : Layout} {p : E} {rd1 : Reader} (hl1 : LowDef κ rd1) (hL1 : MemL rd1 Lin)
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → ∃ (r pa : BitVec 128) (m : BitVec 256), ClaimAt rd p (claimCells r pa m)) :
    ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i := by
  intro k hk
  classical
  by_contra hn
  set A := p.limb 0 * gpow k
  set w : E := E.ofLimbs 0 0 1
  have hpk : LowDef κ (g1Poke rd1 A w) := fun i hi => by
    unfold g1Poke; split
    · rfl
    · exact hl1 i hi
  have hpm : MemL (g1Poke rd1 A w) Lin := fun q hq j hj => by
    refine ⟨(hL1 q hq j hj).1, ?_⟩
    have hne : (ofK (gpow q.1)).limb 0 * gpow j ≠ A := by
      rw [Main.addr_ofK]
      intro he
      exact hn ⟨q.1 + j, he.symm, q, hq, by omega, by omega⟩
    unfold g1Poke
    rw [ite_neg' hne]
    exact (hL1 q hq j hj).2
  obtain ⟨r, pa, m, hc⟩ := h _ hpk hpm
  have h2 := (hc ⟨k, hk⟩).2
  unfold g1Poke at h2
  rw [ite_pos' rfl, Option.some.injEq] at h2
  have := claimCells_canonical r pa m ⟨k, hk⟩
  rw [← h2] at this
  exact one_ne_zero (show (1 : K) = 0 from this)

/-! ## A memory below `2^κ` and the caller's words -/

/-- The memory `rd1` kept on the caller's words and below `2^κ`. -/
noncomputable def lowLin (rd1 : Reader) (κ : ℕ) (Lin : Layout) : Reader :=
  Main.restrict rd1 fun i => RegionL Lin i ∨ i < 2 ^ κ

theorem lowLin_memOK {rd1 : Reader} {κ K : ℕ} {Lin : Layout} (hl1 : LowDef κ rd1) (hK : K ≤ 2 ^ κ) :
    MemOK (lowLin rd1 κ Lin) K := fun i hi => by
  rw [lowLin, Main.restrict_of ⟨i, rfl, Or.inr (by omega)⟩]
  exact hl1 i (by omega)

theorem lowLin_claim {rd1 : Reader} {κ : ℕ} {Lin : Layout} {p : E} {cs : Fin 4 → E} (hc : ClaimAt rd1 p cs)
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i) : ClaimAt (lowLin rd1 κ Lin) p cs :=
  fun k => Main.loadHolds_restrict (hc k) (let ⟨i, h1, h2⟩ := hreg k.val k.isLt; ⟨i, h1, Or.inl h2⟩)

/-- **The relation on `lowLin` transfers** to every memory defined below `2^κ` and holding `Lin`,
placed at every frame pointer, when its loads read `Lin`. -/
theorem lowLin_relAtIn {fs : String → ℕ} {cert : String → V → ℕ} {S : List String} (hS : coreProgram.PureIn S)
    {g : String} (hg : g ∈ S) {rd1 : Reader} {κ : ℕ} {Lin : Layout} (hL1 : MemL rd1 Lin) {args rets : List E}
    (h : coreProgram.RelIn (lowLin rd1 κ Lin) (RegionL Lin) g args rets) :
    CompleteAt fs cert κ g Lin args (Returns rets) := by
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg h
  intro fp
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtIn_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [lowLin, Main.restrict_of ⟨i, rfl, Or.inl hi⟩, Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := Main.restrict_supp' rd1 _ _ _ hv
    · rw [Main.memL_agree hL' hL1 i hi, ← Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- **The relation on `lowLin` transfers** to every memory defined below `2^κ` and holding `Lin`,
placed at every frame pointer, when its loads read `Lin`. -/
theorem lowLin_relAtInD {fs : String → ℕ} {cert : String → V → ℕ} {S : List String} (hS : coreProgram.PureIn S)
    {g : String} (hg : g ∈ S) {rd1 : Reader} {κ : ℕ} {Lin : Layout} (hL1 : MemL rd1 Lin) {args rets : List E}
    (h : coreProgram.RelIn (lowLin rd1 κ Lin) (RegionL Lin) g args rets) :
    CompleteAtD fs cert κ g Lin args (Returns rets) := by
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg h
  intro fp
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtIn_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [lowLin, Main.restrict_of ⟨i, rfl, Or.inl hi⟩, Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := Main.restrict_supp' rd1 _ _ _ hv
    · rw [Main.memL_agree hL' hL1 i hi, ← Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-! ## The verifiers -/

/-- **The relation on `lowLin` transfers** to every memory defined below `2^κ` and holding `Lin`,
placed at every frame pointer, when its loads read `Lin`. -/
theorem lowLin_relAtInB {fs : String → ℕ} {cert : String → V → ℕ} {S : List String} (hS : coreProgram.PureIn S)
    {g : String} (hg : g ∈ S) {rd1 : Reader} {κ : ℕ} {Lin : Layout} (hL1 : MemL rd1 Lin) {args rets : List E}
    (h : coreProgram.RelIn (lowLin rd1 κ Lin) (RegionL Lin) g args rets) {B : ℕ}
    (hB : ∀ rd (t : Tree), t.name = g → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ B) :
    CompleteAtB fs cert κ g Lin args (Returns rets) B := by
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg h
  intro fp
  have hnB : n ≤ B := by
    obtain ⟨t, hname, hv, hbo, -, ht, -⟩ := hn fp (lowLin rd1 κ Lin) (fun _ _ => rfl) (fun _ h => h)
    rw [← ht]; exact hB _ t hname hv hbo
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, hnB, fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtIn_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [lowLin, Main.restrict_of ⟨i, rfl, Or.inl hi⟩, Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := Main.restrict_supp' rd1 _ _ _ hv
    · rw [Main.memL_agree hL' hL1 i hi, ← Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-! ## The verifiers -/

theorem xmss_relIn {rd : Reader} {R : ℕ → Prop} {p : E}
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ R i)
    (h : coreProgram.Rel rd "verify_lean_xmss" [p] []) : coreProgram.RelIn rd R "verify_lean_xmss" [p] [] := by
  refine Digest.relIn_of_inv (fun f args => f = "verify_lean_xmss" ∧ args = [p])
    (fun f args σ fn es vs hI hf hp hw _ => ?_) ⟨rfl, rfl⟩ h
  obtain ⟨rfl, rfl⟩ := hI
  rw [find_verify_lean_xmss, Option.some.injEq] at hf
  subst hf
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  have hsig : Stmt.sigOkList claimLoad [] xBody = true := xBody_eq ▸ xBody_sigOk
  have hw' : walk σ xBody = .ret es vs := hw
  generalize xBody = B at hsig hw'
  have hall := walk_sigOk (σ := σ) B hsig
  rw [hw'] at hall
  refine ⟨fun A hA => ?_, fun c hc ht => absurd (calls_in hall hc ht) List.not_mem_nil⟩
  obtain ⟨off, hoff, rfl⟩ := loads_claim hall A hA
  rw [hp]
  exact hreg off hoff

theorem sphincs_relIn {rd : Reader} {R : ℕ → Prop} {p : E}
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ R i)
    (h : coreProgram.Rel rd "verify_sig_lean_sphincs" [p] []) :
    coreProgram.RelIn rd R "verify_sig_lean_sphincs" [p] [] := by
  refine Digest.relIn_of_inv (fun f args => (f = "verify_sig_lean_sphincs" ∧ args = [p]) ∨ f ∈ fkNames)
    (fun f args σ fn es vs hI hf hp hw _ => ?_) (Or.inl ⟨rfl, rfl⟩) h
  rcases hI with ⟨rfl, rfl⟩ | hI
  · rw [find_verify_sig_lean_sphincs, Option.some.injEq] at hf
    subst hf
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
    have hsig : Stmt.sigOkList claimLoad fkNames sBody = true := sBody_eq ▸ sBody_sigOk
    have hw' : walk σ sBody = .ret es vs := hw
    generalize sBody = B at hsig hw'
    have hall := walk_sigOk (σ := σ) B hsig
    rw [hw'] at hall
    refine ⟨fun A hA => ?_, fun c hc ht => Or.inr (calls_in hall hc ht)⟩
    obtain ⟨off, hoff, rfl⟩ := loads_claim hall A hA
    rw [hp]
    exact hreg off hoff
  · obtain ⟨t, ht, rfl⟩ := mem_fkNames hI
    rw [find_fk ht, Option.some.injEq] at hf
    subst hf
    have hw' : walk σ (fkBody t) = .ret es vs := hw
    have hall := walk_sigOk (σ := σ) (fkBody t) (fkBody_sigOk t)
    rw [hw'] at hall
    exact ⟨fun A hA => (loads_none hall A hA).elim, fun c hc ht => absurd (calls_in hall hc ht) List.not_mem_nil⟩

end Sig

/-- **`verify_lean_xmss` is complete, uniformly placed**, on memories defined below `2^κ`, `κ ≥ 6`. -/
theorem verify_lean_xmss_completeRel (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 6 ≤ κ) :
    CompleteRel fs cert κ "verify_lean_xmss" Meaning_verify_lean_xmss := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, rfl, rfl, pk, m, hc1, sig, hv⟩ := hpre rd1 hl1 hL1
  have hreg := claim_region hl1 hL1 (p := p) fun rd hl hL => by
    obtain ⟨p', hp', -, pk', m', hc', -⟩ := hpre rd hl hL
    rw [List.cons.injEq] at hp'
    exact ⟨pk'.root, pk'.parameter, m', hp'.1 ▸ hc'⟩
  have h0 : coreProgram.Rel (lowLin rd1 κ Lin) "verify_lean_xmss" [p] [] :=
    (verify_lean_xmss_iff (lowLin_memOK hl1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)))).mpr
      ⟨p, rfl, rfl, pk, m, lowLin_claim hc1 hreg, sig, hv⟩
  exact lowLin_relAtIn xmss_pure (List.mem_singleton_self _) hL1
    (xmss_relIn (fun k hk => let ⟨i, h1, h2⟩ := hreg k hk; ⟨i, h1, h2⟩) h0) fp

/-- **`verify_lean_xmss` is complete, uniformly placed**, on memories defined below `2^κ`, `κ ≥ 6`. -/
theorem verify_lean_xmss_completeRelD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 6 ≤ κ) :
    CompleteRelD fs cert κ "verify_lean_xmss" Meaning_verify_lean_xmss := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, rfl, rfl, pk, m, hc1, sig, hv⟩ := hpre rd1 hl1 hL1
  have hreg := claim_region hl1 hL1 (p := p) fun rd hl hL => by
    obtain ⟨p', hp', -, pk', m', hc', -⟩ := hpre rd hl hL
    rw [List.cons.injEq] at hp'
    exact ⟨pk'.root, pk'.parameter, m', hp'.1 ▸ hc'⟩
  have h0 : coreProgram.Rel (lowLin rd1 κ Lin) "verify_lean_xmss" [p] [] :=
    (verify_lean_xmss_iff (lowLin_memOK hl1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)))).mpr
      ⟨p, rfl, rfl, pk, m, lowLin_claim hc1 hreg, sig, hv⟩
  exact lowLin_relAtInD xmss_pure (List.mem_singleton_self _) hL1
    (xmss_relIn (fun k hk => let ⟨i, h1, h2⟩ := hreg k hk; ⟨i, h1, h2⟩) h0) fp

/-- **`verify_lean_xmss` is complete, uniformly placed**, on memories defined below `2^κ`, `κ ≥ 6`. -/
theorem verify_lean_xmss_completeRelB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {B : ℕ}
    (hB : LeanVM.Guest.Memory.TotalLe coreProgram fs "verify_lean_xmss" fun _ => B) (hκ : 6 ≤ κ) :
    CompleteRelB fs cert κ "verify_lean_xmss" Meaning_verify_lean_xmss B := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, rfl, rfl, pk, m, hc1, sig, hv⟩ := hpre rd1 hl1 hL1
  have hreg := claim_region hl1 hL1 (p := p) fun rd hl hL => by
    obtain ⟨p', hp', -, pk', m', hc', -⟩ := hpre rd hl hL
    rw [List.cons.injEq] at hp'
    exact ⟨pk'.root, pk'.parameter, m', hp'.1 ▸ hc'⟩
  have h0 : coreProgram.Rel (lowLin rd1 κ Lin) "verify_lean_xmss" [p] [] :=
    (verify_lean_xmss_iff (lowLin_memOK hl1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)))).mpr
      ⟨p, rfl, rfl, pk, m, lowLin_claim hc1 hreg, sig, hv⟩
  exact lowLin_relAtInB xmss_pure (List.mem_singleton_self _) hL1
    (xmss_relIn (fun k hk => let ⟨i, h1, h2⟩ := hreg k hk; ⟨i, h1, h2⟩) h0) (fun rd t hn hv hbo => hB rd t _ _ hn hv hbo) fp

/-- **`verify_sig_lean_sphincs` is complete, uniformly placed**, on memories defined below `2^κ`,
`κ ≥ 8`. -/
theorem verify_sig_lean_sphincs_completeRel (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 8 ≤ κ) :
    CompleteRel fs cert κ "verify_sig_lean_sphincs" Meaning_verify_sig_lean_sphincs := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, rfl, rfl, pk, m, hc1, sig, hv⟩ := hpre rd1 hl1 hL1
  have hreg := claim_region hl1 hL1 (p := p) fun rd hl hL => by
    obtain ⟨p', hp', -, pk', m', hc', -⟩ := hpre rd hl hL
    rw [List.cons.injEq] at hp'
    exact ⟨pk'.root, pk'.parameter, m', hp'.1 ▸ hc'⟩
  have h0 : coreProgram.Rel (lowLin rd1 κ Lin) "verify_sig_lean_sphincs" [p] [] :=
    (verify_sig_lean_sphincs_iff (lowLin_memOK hl1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)))).mpr
      ⟨p, rfl, rfl, pk, m, lowLin_claim hc1 hreg, sig, hv⟩
  exact lowLin_relAtIn sphincs_pure (List.mem_cons_self ..) hL1
    (sphincs_relIn (fun k hk => let ⟨i, h1, h2⟩ := hreg k hk; ⟨i, h1, h2⟩) h0) fp

/-- **`verify_sig_lean_sphincs` is complete, uniformly placed**, on memories defined below `2^κ`,
`κ ≥ 8`. -/
theorem verify_sig_lean_sphincs_completeRelD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 8 ≤ κ) :
    CompleteRelD fs cert κ "verify_sig_lean_sphincs" Meaning_verify_sig_lean_sphincs := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, rfl, rfl, pk, m, hc1, sig, hv⟩ := hpre rd1 hl1 hL1
  have hreg := claim_region hl1 hL1 (p := p) fun rd hl hL => by
    obtain ⟨p', hp', -, pk', m', hc', -⟩ := hpre rd hl hL
    rw [List.cons.injEq] at hp'
    exact ⟨pk'.root, pk'.parameter, m', hp'.1 ▸ hc'⟩
  have h0 : coreProgram.Rel (lowLin rd1 κ Lin) "verify_sig_lean_sphincs" [p] [] :=
    (verify_sig_lean_sphincs_iff (lowLin_memOK hl1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)))).mpr
      ⟨p, rfl, rfl, pk, m, lowLin_claim hc1 hreg, sig, hv⟩
  exact lowLin_relAtInD sphincs_pure (List.mem_cons_self ..) hL1
    (sphincs_relIn (fun k hk => let ⟨i, h1, h2⟩ := hreg k hk; ⟨i, h1, h2⟩) h0) fp

/-- **`verify_sig_lean_sphincs` is complete, uniformly placed**, on memories defined below `2^κ`,
`κ ≥ 8`. -/
theorem verify_sig_lean_sphincs_completeRelB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {B : ℕ}
    (hB : LeanVM.Guest.Memory.TotalLe coreProgram fs "verify_sig_lean_sphincs" fun _ => B) (hκ : 8 ≤ κ) :
    CompleteRelB fs cert κ "verify_sig_lean_sphincs" Meaning_verify_sig_lean_sphincs B := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, rfl, rfl, pk, m, hc1, sig, hv⟩ := hpre rd1 hl1 hL1
  have hreg := claim_region hl1 hL1 (p := p) fun rd hl hL => by
    obtain ⟨p', hp', -, pk', m', hc', -⟩ := hpre rd hl hL
    rw [List.cons.injEq] at hp'
    exact ⟨pk'.root, pk'.parameter, m', hp'.1 ▸ hc'⟩
  have h0 : coreProgram.Rel (lowLin rd1 κ Lin) "verify_sig_lean_sphincs" [p] [] :=
    (verify_sig_lean_sphincs_iff (lowLin_memOK hl1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)))).mpr
      ⟨p, rfl, rfl, pk, m, lowLin_claim hc1 hreg, sig, hv⟩
  exact lowLin_relAtInB sphincs_pure (List.mem_cons_self ..) hL1
    (sphincs_relIn (fun k hk => let ⟨i, h1, h2⟩ := hreg k hk; ⟨i, h1, h2⟩) h0) (fun rd t hn hv hbo => hB rd t _ _ hn hv hbo) fp

end
end LeanVM.Guest.B1
