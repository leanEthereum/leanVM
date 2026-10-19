/-
  LeanVM.Guest.B1.VerifySub.CLog2c

  Group 1's `verify_log2_ceil` and `log2_ceil_in_the_exponent`, complete in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.VerifySub.CLog2b

/-!
# `verify_log2_ceil` and `log2_ceil_in_the_exponent`, placed

* `vl_completeAt`: `verify_log2_ceil` at the floor `fl`, on the bits of `N` at `g^bA` and the
  exponent tables in the caller's words, its prefix sums its one `HeapBuf`;
* `lc_completeAt`: `log2_ceil_in_the_exponent` on `g^N` and the exponent tables, its bits its one
  `HeapBuf`, from its callee's;
* `log2L0_completeAt`, `log2L15_completeAt`: the guest's two instances, on the exponent tables
  among the caller's words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The bits of `N`. -/
def bitsW (N : ℕ) : List E := (List.range 34).map fun j => bitE (N.testBit j)

/-- Its prefix sums. -/
def psW (N : ℕ) : List E := (List.range 35).map fun j => eOfNat (N % 2 ^ j)

theorem list1 {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp at h
  exact ⟨a, rfl⟩

theorem ptr_mul (a m : ℕ) : ofK (Parameters.gpow a) * gen ^ m = ofK (Parameters.gpow (a + m)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, Parameters.gpow, Parameters.gpow, Parameters.gpow, pow_add]

theorem regionL_of {L : Main.Layout} {b i : ℕ} {xs : List E} (h : (b, xs) ∈ L) (h1 : b ≤ i)
    (h2 : i < b + xs.length) : RegionL L i := ⟨_, h, h1, h2⟩

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 100000 in
/-- **`verify_log2_ceil`, placed.** -/
theorem vl_completeAt {name : String} {fn : Fn} (fl : ℕ) (hfl : fl < 34)
    (hf : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1, .n 2])
    (hbody : fn.body = vlBody fl) (hl : coreProgram.loop name = false) {k : ℕ} (hk : 6 ≤ k) {N : ℕ}
    (hN : N < 2 ^ 34) (hL : max fl (log2Ceil N) < 34) (bA lpA sqA : ℕ) (Lin : Main.Layout)
    (hLin : ∀ q ∈ expL lpA sqA ++ [(bA, bitsW N)], q ∈ Lin) :
    CompleteAtB fs cert k name Lin [ofK (Parameters.gpow bA), ofK (Parameters.gpow lpA),
      ofK (Parameters.gpow sqA)] (Returns [gen ^ max fl (log2Ceil N), gen ^ N]) (fs name + 35) := by
  refine completeAt_leafB hf hl k Lin _ _ [35] (fun _ => [psW N]) (fun _ => by simp [psW])
    fun fp rd hlow hL1 hL2 => ?_
  have hb := hLin (bA, bitsW N) (by simp)
  have hlp := hLin (lpA, (List.range sizeBits).map fun j => eOfNat (2 ^ j)) (by simp [expL])
  have hsq := hLin (sqA, (List.range sizeBits).map fun j => gen ^ 2 ^ j) (by simp [expL])
  have ht : ExpTables rd (ofK (Parameters.gpow lpA)) (ofK (Parameters.gpow sqA)) :=
    expTables_of fun q hq => hL2 q (hLin q (List.mem_append_left _ hq))
  have hps : ∀ j ≤ 34, LoadHolds rd (ofK (Parameters.gpow (fp + fs name))) j (eOfNat (N % 2 ^ j)) :=
    fun j hj => readsAt_map_range (m := 35) (f := fun j => eOfNat (N % 2 ^ j))
      (hL1 (fp + fs name, psW N) (by simp [bufL, bases])) j (by omega)
  have hbits : ∀ j < 34, LoadHolds rd (ofK (Parameters.gpow bA)) j (bitE (N.testBit j)) :=
    fun j hj => readsAt_map_range (m := 34) (f := fun j => bitE (N.testBit j)) (hL2 _ hb) j hj
  obtain ⟨τ, e0, e1, e2, e3, e409, e431, e433, e420, e425, e436, e440, hH⟩ :=
    vl_complete_low (C := coreProgram.Rel rd) fl hfl hk hlow ht hN hbits hL hps
  have hwf : Stmt.wfList coreProgram (vlBody fl) = true := by
    have := coreProgram_wf fn (List.mem_of_find?_eq_some hf); rwa [hbody] at this
  have hs := walk_sat _ hwf hH
  rw [vl_walk] at hs
  obtain ⟨p1, p2, p3, p4, p5⟩ := vl_parts fl τ
  set L := max fl (log2Ceil N)
  have own : ∀ i, fp + fs name ≤ i → i < fp + fs name + 35 →
      RegionL (bufL (fp + fs name) [35] [psW N]) i ∨ RegionL Lin i :=
    fun i h1 h2 => Or.inl (regionL_of (xs := psW N) (by simp [bufL, bases]) h1 (by simp [psW]; omega))
  refine ⟨τ, vlEvs fl τ, [.n 449, .n 450], by rw [hparams]; simp [e0, e1, e2],
    by rw [hbody]; exact vl_walk fl τ, hs.2, fun e he => (hs.1 e he).1, p4, p3, p2,
    by rw [p1]; simp [e3, bases], fun A hA => ?_⟩
  rcases p5 A hA with ⟨q, hq, rfl⟩ | ⟨-, h433, hA'⟩
  · rw [(vlPre_parts fl).2.2.2] at hq
    simp only [List.mem_cons, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range,
      List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | ⟨_, ⟨j, hj, rfl⟩, hq⟩ | rfl | rfl
    · exact ⟨fp + fs name + 0, by simp only [e3, Main.addr_ofK], own _ (by omega) (by omega)⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨bA + j, by simp only [e0, Main.addr_ofK],
          Or.inr (regionL_of hb (by omega) (by simp [bitsW]; omega))⟩
      · exact ⟨sqA + j, by simp only [e2, Main.addr_ofK],
          Or.inr (regionL_of hsq (by omega) (by simp [sizeBits]; omega))⟩
      · exact ⟨fp + fs name + (j + 1), by simp only [e3, Main.addr_ofK], own _ (by omega) (by omega)⟩
    · exact ⟨fp + fs name + L + 0, by simp only [e420, ptr_mul, Main.addr_ofK],
        own _ (by omega) (by omega)⟩
    · exact ⟨lpA + L + 0, by simp only [e425, ptr_mul, Main.addr_ofK],
        Or.inr (regionL_of hlp (by omega) (by simp [sizeBits]; omega))⟩
  · have hL0 : L ≠ 0 := fun h0 => h433 (by rw [e433, h0, pow_zero]; exact e_add_self _)
    have hinv : gen ^ L * invGenWord = gen ^ (L - 1) := by
      rw [show L = L - 1 + 1 by omega, gen_pow_mul_invGen, Nat.add_sub_cancel]
    rcases hA' with rfl | rfl
    · exact ⟨fp + fs name + (L - 1) + 0, by simp only [e436, hinv, ptr_mul, Main.addr_ofK],
        own _ (by omega) (by omega)⟩
    · exact ⟨lpA + (L - 1) + 0, by simp only [e440, hinv, ptr_mul, Main.addr_ofK],
        Or.inr (regionL_of hlp (by omega) (by simp [sizeBits]; omega))⟩

/-- `log2_ceil_in_the_exponent`'s statements before its `ret`. -/
def lcPre (callee : String) : List Stmt :=
  [.atom (.const (.n 3) (word (2 ^ 34) 0 0)), .atom (.hint (.allocDyn (.n 4) (.n 3))),
    .atom (.hint (.bitsExp (.n 0) 34 (.heap (.n 4) 0 34))),
    .call callee [.n 4, .n 1, .n 2] [.n 5, .n 6], .atom (.assertEq (.n 6) (.n 0)),
    .atom (.copy (.n 7) (.n 5))]

/-- **`log2_ceil_in_the_exponent`, placed**, from its callee's placed completeness. -/
theorem lc_completeAt {name callee : String} {fn : Fn} (fl : ℕ)
    (hf : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1, .n 2])
    (hbody : fn.body = lcBody callee) (hl : coreProgram.loop name = false) {k Bv : ℕ}
    (hcallee : ∀ (N : ℕ), N < 2 ^ 34 → max fl (log2Ceil N) < 34 → ∀ (bA lpA sqA : ℕ) (Lin : Main.Layout),
      (∀ q ∈ expL lpA sqA ++ [(bA, bitsW N)], q ∈ Lin) →
      CompleteAtB fs cert k callee Lin [ofK (Parameters.gpow bA), ofK (Parameters.gpow lpA),
        ofK (Parameters.gpow sqA)] (Returns [gen ^ max fl (log2Ceil N), gen ^ N]) Bv)
    {N : ℕ} (hN : N < 2 ^ 34) (hL : max fl (log2Ceil N) < 34) (lpA sqA : ℕ) (Lin : Main.Layout)
    (hLin : ∀ q ∈ expL lpA sqA, q ∈ Lin) :
    CompleteAtB fs cert k name Lin [gen ^ N, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA)]
      (Returns [gen ^ max fl (log2Ceil N)]) (fs name + 34 + Bv) := by
  intro fp
  set bA := fp + fs name
  set L := max fl (log2Ceil N)
  let kid : Kid := ⟨callee, true, [ofK (Parameters.gpow bA), ofK (Parameters.gpow lpA),
    ofK (Parameters.gpow sqA)], expL lpA sqA ++ [(bA, bitsW N)], Returns [gen ^ L, gen ^ N]⟩
  obtain ⟨N1, L1, outs, ho, hw, hd, hNb, -, hK⟩ := kidsFromIn_of_kidsB k (fun _ => Bv) [kid] (fun k' hk' _ => by
      rw [List.mem_singleton] at hk'; subst hk'
      exact hcallee N hN hL bA lpA sqA _ fun q hq => hq) (bA + 34)
  obtain ⟨o, rfl⟩ := list1 (ho.length.trans rfl)
  have hor : o.1 = [gen ^ L, gen ^ N] := by
    have := ho; simp only [OutsOk, Returns, forall_const, kid] at this; exact this.1.1
  have wb : Within [(bA, bitsW N)] bA 34 := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; simp [bitsW]
  refine ⟨fs name + 34 + N1, [(bA, bitsW N)] ++ L1, [gen ^ L], [], ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append (List.pairwise_singleton _ _) hd wb hw le_rfl,
    by simp only [kidsBound, kid, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      ↓reduceIte] at hNb; omega,
    fun rd hlow hM => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨wb.mono (by omega) (by omega), hw.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hM
  obtain ⟨hM1, hMin⟩ := Main.memL_append.mp hM
  obtain ⟨hMb, hML1⟩ := Main.memL_append.mp hM1
  set σ := upds (fun _ => 0) [(0, gen ^ N), (1, ofK (Parameters.gpow lpA)),
    (2, ofK (Parameters.gpow sqA)), (3, word (2 ^ 34) 0 0), (4, ofK (Parameters.gpow bA)),
    (5, gen ^ L), (6, gen ^ N), (7, gen ^ L)]
  have hw' : walk σ fn.body = .ret ((lcPre callee).flatMap (Main.slEvs σ)) [.n 7] := by
    rw [hbody, show lcBody callee = lcPre callee ++ [.ret [.n 7]] from rfl]
    exact Main.walk_straight σ _ _ rfl
  obtain ⟨a1, a2, a3, a4⟩ := Main.straight_parts σ (lcPre callee) rfl
  have l1 := loadAddrs_straight σ (lcPre callee) rfl
  have pa : (lcPre callee).filterMap Main.Stmt.allocSz = [(.n 4, .inr (.n 3))] := rfl
  have pd : (lcPre callee).filterMap Main.Stmt.addrS = [] := rfl
  have pc : (lcPre callee).filterMap Main.Stmt.callS =
      [(none, callee, [.n 4, .n 1, .n 2], [.n 5, .n 6])] := rfl
  have pl : (lcPre callee).filterMap Stmt.loadS = [] := rfl
  rw [pa] at a1 a2
  rw [pd] at a3
  rw [pc] at a4
  rw [pl] at l1
  have h34 : logG (σ (.n 3)) = 34 := by
    have e3 : σ (.n 3) = word (2 ^ 34) 0 0 := by simp [σ, upds_n]
    rw [e3, word_two_pow (a := 34) (by decide), gen_pow_eq_ofK]
    exact logG_spec (e := 34) (by decide)
  have hal : allocs σ ((lcPre callee).flatMap (Main.slEvs σ)) = [34] := by
    rw [a2]; simp [h34]
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (N := N1) (fp := fp) (rd := rd)
    (args := [gen ^ N, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA)]) (rets := [gen ^ L])
    coreProgram_wf hf (Or.inl hl) (by rw [hparams]; simp [σ, upds_n]) hw' (by simp [σ, upds_n])
    (fun e he => ?_) (by rw [a1, hal]; simp [σ, upds_n, bases, bA]) (by rw [a3]; simp) ?_
    (fun A hA => by rw [l1] at hA; simp at hA) (fun i ⟨q, hq, _⟩ => by simp at hq)
  · rw [hal] at h; simpa using h
  · simp only [lcPre, List.flatMap_cons, List.flatMap_nil, Main.slEvs, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Memory.Ev.Holds, Atom.Holds, σ, upds_n, e_add_self]
  · rw [hal, a4]
    simp only [List.map_cons, List.map_nil, Main.mkCall]
    refine kidsFromIn_dend _ _ _ _ (fun _ h => h.elim) (hK rd σ _ _ (fun _ => False) ?_ hlow hML1
      (memL_lins ?_) (regionsOk_of ?_))
    · simp only [CallsMatch, kid, hor, List.map_cons, List.map_nil, σ, upds_n]
      simp
    · intro k' hk'; rw [List.mem_singleton] at hk'; subst hk'
      exact Main.memL_append.mpr ⟨fun q hq => hMin q (hLin q hq), hMb⟩
    · intro k' hk' _ i hi; rw [List.mem_singleton] at hk'; subst hk'
      obtain ⟨q, hq, h1, h2⟩ := hi
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (Or.inl ⟨q, hLin q hq, h1, h2⟩)
      · simp only [List.mem_singleton] at hq; subst hq
        refine Or.inl (Or.inr (Or.inl ⟨(34, bA), by simp [bases, bA], h1, ?_⟩))
        simpa [bitsW] using h2

/-! ## The guest's instances -/

set_option maxRecDepth 100000 in
theorem find_lc0 : coreProgram.find? "log2_ceil_in_the_exponent__L0_L34" = some Data.core173 :=
  Program.find?_of_indexOf? (j := 173) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_lc15 : coreProgram.find? "log2_ceil_in_the_exponent__L15_L34" = some Data.core176 :=
  Program.find?_of_indexOf? (j := 176) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem lc0_not_loop : coreProgram.loop "log2_ceil_in_the_exponent__L0_L34" = false := by
  rw [Program.loop_of_find? find_lc0]; decide +kernel

set_option maxRecDepth 100000 in
theorem lc15_not_loop : coreProgram.loop "log2_ceil_in_the_exponent__L15_L34" = false := by
  rw [Program.loop_of_find? find_lc15]; decide +kernel

set_option maxRecDepth 100000 in
theorem vl0_not_loop : coreProgram.loop "verify_log2_ceil__L0_L34" = false := by
  rw [Program.loop_of_find? find_verify_log2_ceil_L0_L34]; decide +kernel

set_option maxRecDepth 100000 in
theorem vl15_not_loop : coreProgram.loop "verify_log2_ceil__L15_L34" = false := by
  rw [Program.loop_of_find? find_verify_log2_ceil_L15_L34]; decide +kernel

/-- The two instances' bounds: the frame, the bits' buffer, and the callee's frame and buffer. -/
def log2Bound0 (fs : String → ℕ) : ℕ :=
  fs "log2_ceil_in_the_exponent__L0_L34" + 34 + (fs "verify_log2_ceil__L0_L34" + 35)

def log2Bound15 (fs : String → ℕ) : ℕ :=
  fs "log2_ceil_in_the_exponent__L15_L34" + 34 + (fs "verify_log2_ceil__L15_L34" + 35)

/-- **`log2_ceil_in_the_exponent__L0_L34`, placed**: on `g^N`, `N < 2^34` with `log2Ceil N < 34`,
and the exponent tables at `g^lpA`, `g^sqA` among the caller's words, it returns `g^log2Ceil N`. -/
theorem log2L0_completeAt {k : ℕ} (hk : 6 ≤ k) {N : ℕ} (hN : N < 2 ^ 34) (hL : log2Ceil N < 34)
    (lpA sqA : ℕ) (Lin : Main.Layout) (hLin : ∀ q ∈ expL lpA sqA, q ∈ Lin) :
    CompleteAtB fs cert k "log2_ceil_in_the_exponent__L0_L34" Lin
      [gen ^ N, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA)] (Returns [gen ^ log2Ceil N])
      (log2Bound0 fs) := by
  have h := lc_completeAt (fs := fs) (cert := cert) (callee := "verify_log2_ceil__L0_L34") 0 find_lc0
    rfl rfl lc0_not_loop (fun N hN hL bA lpA sqA Lin h => vl_completeAt 0 (by decide)
      find_verify_log2_ceil_L0_L34 rfl core575_body vl0_not_loop hk hN hL bA lpA sqA Lin h)
    hN (by simpa using hL) lpA sqA Lin hLin
  simpa [log2Bound0] using h

/-- **`log2_ceil_in_the_exponent__L15_L34`, placed**: it returns `g^max 15 (log2Ceil N)`. -/
theorem log2L15_completeAt {k : ℕ} (hk : 6 ≤ k) {N : ℕ} (hN : N < 2 ^ 34)
    (hL : max 15 (log2Ceil N) < 34) (lpA sqA : ℕ) (Lin : Main.Layout)
    (hLin : ∀ q ∈ expL lpA sqA, q ∈ Lin) :
    CompleteAtB fs cert k "log2_ceil_in_the_exponent__L15_L34" Lin
      [gen ^ N, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA)]
      (Returns [gen ^ max 15 (log2Ceil N)]) (log2Bound15 fs) :=
  lc_completeAt (fs := fs) (cert := cert) (callee := "verify_log2_ceil__L15_L34") 15 find_lc15
    rfl rfl lc15_not_loop (fun N hN hL bA lpA sqA Lin h => vl_completeAt 15 (by decide)
      find_verify_log2_ceil_L15_L34 rfl core576_body vl15_not_loop hk hN hL bA lpA sqA Lin h)
    hN hL lpA sqA Lin hLin

end
end LeanVM.Guest.B1.VerifySub
