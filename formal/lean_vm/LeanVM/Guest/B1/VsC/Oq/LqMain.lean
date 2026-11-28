/-
  LeanVM.Guest.B1.VsC.Oq.LqMain

  `level_queries__L…` completes placed, every specialization.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.LqA

/-!
# `level_queries`, every specialization

`lqA_complete'`: one specialization, by `callAtA_node` on the forward evaluation of its straight
body (`lq_vals`, its path's parts `lq_parts`), its callees by `vmcA` and `oqA_all`; `lqA_all`:
every `lqTable` entry.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

set_option linter.unusedSimpArgs false

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem atomsAll_mem {p : Atom → Bool} : ∀ {ss : List Stmt} {a : Atom}, Stmt.atomsAll p ss = true →
    Stmt.atom a ∈ ss → p a = true
  | [], _, _, hm => by simp at hm
  | s :: ss, a, h, hm => by
    have h2 : Stmt.atomsAll p ss = true := by cases s <;> simp_all [Stmt.atomsAll]
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [Stmt.atomsAll, Bool.and_eq_true] at h; exact h.1
    · exact atomsAll_mem h2 hm

theorem pow_filterMap {β : Type} (f : Stmt → Option β) (hf : ∀ a, lpPure a = true → f (.atom a) = none)
    (x : ℕ) (ds : List Bool) (acc k : ℕ) : (osPowSteps x ds acc k).1.filterMap f = [] :=
  List.filterMap_eq_nil_iff.mpr fun s hs => by
    obtain ⟨a, rfl, ha⟩ := osPowSteps_pure x ds acc k s hs
    exact hf a ha

theorem pow_flatMap {β : Type} (f : Stmt → List β) (hf : ∀ a, lpPure a = true → f (.atom a) = [])
    (x : ℕ) (ds : List Bool) (acc k : ℕ) : (osPowSteps x ds acc k).1.flatMap f = [] :=
  List.flatMap_eq_nil_iff.mpr fun s hs => by
    obtain ⟨a, rfl, ha⟩ := osPowSteps_pure x ds acc k s hs
    exact hf a ha

theorem holds_indep {rd rd' : Reader} {σ : Val} {a : Atom} (h : needsSide a = false) :
    a.Holds rd σ → a.Holds rd' σ := by
  cases a <;> first | exact id | simp [needsSide] at h

theorem oqIn_ptr {R : ℕ → Prop} {a off : ℕ} (h : R (a + off)) :
    OqIn R ((ptrAt a).limb 0 * addressOfIndex off) := ⟨a + off, Main.addr_ofK a off, h⟩

/-- `level_queries`' body before its powers. -/
def lqHead (q base folds leaf d cd mu nhs hbits fin : ℕ) : List Stmt :=
  [osCst 6 (gw (4 * 2 ^ cd)), .atom (.hint (.allocDyn (.n 7) (.n 6))),
    .atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd)))),
    osCst 8 (gw (2 ^ cd)), .atom (.hint (.allocDyn (.n 9) (.n 8))),
    .atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd)))),
    .call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11],
    osCst 12 (gw (2 ^ (cd + 1))), osMul 13 7 12, osCst 14 (gw (2 ^ (cd - 1))), osMul 15 9 14,
    osCst 16 (gw (lqIters q base)), osCst 17 (gw (lqOdd q base)),
    .call (oqName base folds leaf (d - cd) mu nhs hbits fin)
      [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17] [.n 18],
    osCp 19 10, osCp 20 11, osCp 21 18]

theorem lqBodyA_eq (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    lqBodyA q base folds leaf d cd mu nhs hbits fin = lqHead q base folds leaf d cd mu nhs hbits fin ++
      (osPowSteps 0 (osPowDigits q) 0 22).1 ++ [osCp (22 + osPowLen q) (osPowSteps 0 (osPowDigits q) 0 22).2] := by
  simp only [lqBodyA, lqHead, osHeap, List.append_assoc, List.cons_append, List.nil_append]

/-- `level_queries`' words from its buffers and callees: the cap at `c`, the flags after it, the
root's halves `r0`, `r1`, the queries' return `m`. -/
def lqW (c cd : ℕ) (r0 r1 m : E) : ℕ → E := fun i =>
  if i = 7 then ptrAt c else if i = 9 then ptrAt (c + 4 * 2 ^ cd) else if i = 10 then r0
  else if i = 11 then r1 else if i = 18 then m else 0

section Body

variable {q base folds leaf d cd mu nhs hbits fin : ℕ}

theorem lqHead_sub {x : Stmt} (hx : x ∈ lqHead q base folds leaf d cd mu nhs hbits fin) :
    x ∈ lqBody q base folds leaf d cd mu nhs hbits fin := by
  rw [lqBody_split, lqBodyA_eq]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx))

theorem lqPow_sub {x : Stmt} (hx : x ∈ (osPowSteps 0 (osPowDigits q) 0 22).1) :
    x ∈ lqBody q base folds leaf d cd mu nhs hbits fin := by
  rw [lqBody_split, lqBodyA_eq]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))

theorem lqLast_sub : osCp (22 + osPowLen q) (osPowSteps 0 (osPowDigits q) 0 22).2 ∈
    lqBody q base folds leaf d cd mu nhs hbits fin := by
  rw [lqBody_split, lqBodyA_eq]
  exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

theorem lqA_sub {x : Stmt} (hx : x ∈ lqBodyA q base folds leaf d cd mu nhs hbits fin) :
    x ∈ lqBody q base folds leaf d cd mu nhs hbits fin := by
  rw [lqBody_split]; exact List.mem_append_left _ hx

theorem lq_noCallIf (c0 : V) (f0 : String) (a0 : List V) :
    Stmt.callIf c0 f0 a0 ∉ lqBodyA q base folds leaf d cd mu nhs hbits fin := by
  intro h
  rw [lqBodyA_eq] at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · simp [lqHead, osCst, osMul, osCp] at h
    · obtain ⟨b, hb, -⟩ := osPowSteps_pure 0 _ _ _ _ h
      cases hb
  · simp [osCp] at h

theorem two_pow_le8 (h : cd ≤ 8) : 2 ^ cd ≤ 256 :=
  calc 2 ^ cd ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) h
    _ = 256 := by norm_num

/-- Every atom of `level_queries`' body holds under forward evaluation, on every memory. -/
theorem lq_holds {c' : ℕ} {args : List E} {w : ℕ → E} {σ : Val}
    (hσ : σ = fwdVal (fun _ => none) w args (lqBody q base folds leaf d cd mu nhs hbits fin))
    (hc : chk args.length (lqBody q base folds leaf d cd mu nhs hbits fin) = some c')
    (hat : Stmt.atomsAll (fun a => !needsSide a && !isComputed a)
      (lqBody q base folds leaf d cd mu nhs hbits fin) = true)
    (rd : Reader) (a : Atom) (ha : Stmt.atom a ∈ lqBody q base folds leaf d cd mu nhs hbits fin) :
    a.Holds rd σ := by
  have h := atomsAll_mem hat ha
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  rw [hσ]
  exact holds_indep h.1 (fwd_holds_noSide (rd := fun _ => none) hc ha h.1)

/-- **`level_queries`' values under forward evaluation.** -/
theorem lq_vals {c' : ℕ} {args : List E} {w : ℕ → E} {σ : Val}
    (hσ : σ = fwdVal (fun _ => none) w args (lqBody q base folds leaf d cd mu nhs hbits fin))
    (hc : chk args.length (lqBody q base folds leaf d cd mu nhs hbits fin) = some c')
    (hat : Stmt.atomsAll (fun a => !needsSide a && !isComputed a)
      (lqBody q base folds leaf d cd mu nhs hbits fin) = true)
    (hcd : cd ≤ 8) (hq : q < 2 ^ 20) (hpow : digitsVal (osPowDigits q) 1 = q) :
    σ (.n 6) = gen ^ (4 * 2 ^ cd) ∧ σ (.n 7) = w 7 ∧ σ (.n 8) = gen ^ 2 ^ cd ∧ σ (.n 9) = w 9 ∧
      σ (.n 10) = w 10 ∧ σ (.n 11) = w 11 ∧ σ (.n 13) = w 7 * gen ^ 2 ^ (cd + 1) ∧
      σ (.n 15) = w 9 * gen ^ 2 ^ (cd - 1) ∧ σ (.n 16) = gen ^ lqIters q base ∧
      σ (.n 17) = gen ^ lqOdd q base ∧ σ (.n 18) = w 18 ∧ σ (.n 19) = w 10 ∧ σ (.n 20) = w 11 ∧
      σ (.n 21) = w 18 ∧ σ (.n (22 + osPowLen q)) = σ (.n 0) ^ q := by
  have hH := lq_holds hσ hc hat (fun _ => none)
  have hG : ∀ a, Stmt.atom a ∈ lqBody q base folds leaf d cd mu nhs hbits fin →
      Good (fun _ => none) (storesOf args.length (lqBody q base folds leaf d cd mu nhs hbits fin)) w σ a :=
    fun a ha => by rw [hσ]; exact fwd_good hc a ha
  have hR : ∀ f as rs, Stmt.call f as rs ∈ lqBody q base folds leaf d cd mu nhs hbits fin →
      ∀ v ∈ rs, σ v = w v.idx := fun f as rs h => by
    rw [hσ]; exact (ev_spec (fun _ => none) w _ args hc).2.2 _ h
  have h2 : 2 ^ cd ≤ 256 := two_pow_le8 hcd
  have h2' : 2 ^ (cd + 1) ≤ 512 := by rw [pow_succ]; omega
  have h2'' : 2 ^ (cd - 1) ≤ 2 ^ cd := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hb : ∀ n, n ≤ 2 ^ 20 → n < 2 ^ 64 := fun n hn => lt_of_le_of_lt hn (by norm_num)
  have hit : lqIters q base ≤ 2 ^ 20 := by unfold lqIters; split <;> omega
  have hod : lqOdd q base ≤ 2 ^ 20 := by unfold lqOdd; split <;> omega
  have c6 : σ (.n 6) = gw (4 * 2 ^ cd) :=
    hH (.const (.n 6) (gw (4 * 2 ^ cd))) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have c8 : σ (.n 8) = gw (2 ^ cd) :=
    hH (.const (.n 8) (gw (2 ^ cd))) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have c12 : σ (.n 12) = gw (2 ^ (cd + 1)) :=
    hH (.const (.n 12) (gw (2 ^ (cd + 1)))) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have c14 : σ (.n 14) = gw (2 ^ (cd - 1)) :=
    hH (.const (.n 14) (gw (2 ^ (cd - 1)))) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have c16 : σ (.n 16) = gw (lqIters q base) :=
    hH (.const (.n 16) (gw (lqIters q base))) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have c17 : σ (.n 17) = gw (lqOdd q base) :=
    hH (.const (.n 17) (gw (lqOdd q base))) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have m13 : σ (.n 13) = σ (.n 7) * σ (.n 12) :=
    hH (.mul (.n 13) (.n 7) (.n 12)) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have m15 : σ (.n 15) = σ (.n 9) * σ (.n 14) :=
    hH (.mul (.n 15) (.n 9) (.n 14)) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have p19 : σ (.n 19) = σ (.n 10) :=
    hH (.copy (.n 19) (.n 10)) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have p20 : σ (.n 20) = σ (.n 11) :=
    hH (.copy (.n 20) (.n 11)) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have p21 : σ (.n 21) = σ (.n 18) :=
    hH (.copy (.n 21) (.n 18)) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have a7 : σ (.n 7) = w 7 :=
    hG (.hint (.allocDyn (.n 7) (.n 6))) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have a9 : σ (.n 9) = w 9 :=
    hG (.hint (.allocDyn (.n 9) (.n 8))) (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have hcv := hR ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11]
    (lqHead_sub (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have hco := hR (oqName base folds leaf (d - cd) mu nhs hbits fin)
    [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17] [.n 18]
    (lqHead_sub (q := q) (by simp only [lqHead, List.mem_cons, true_or, or_true]))
  have r10 : σ (.n 10) = w 10 := hcv (.n 10) List.mem_cons_self
  have r11 : σ (.n 11) = w 11 := hcv (.n 11) (List.mem_cons_of_mem _ List.mem_cons_self)
  have r18 : σ (.n 18) = w 18 := hco (.n 18) List.mem_cons_self
  have hv := osPowSteps_val (C := fun _ _ _ => True) (rd := fun _ => none) (σ := σ) 0 (osPowDigits q) 0 22 1
    (by rw [pow_one]) (fun x hx => by
      obtain ⟨a, rfl, -⟩ := osPowSteps_pure 0 _ _ _ x hx
      exact hH a (lqPow_sub hx))
  have cp : σ (.n (22 + osPowLen q)) = σ (.n (osPowSteps 0 (osPowDigits q) 0 22).2) :=
    hH (.copy (.n (22 + osPowLen q)) (.n (osPowSteps 0 (osPowDigits q) 0 22).2)) lqLast_sub
  refine ⟨by rw [c6, gw_gen _ (hb _ (by omega))], a7, by rw [c8, gw_gen _ (hb _ (by omega))], a9, r10, r11,
    by rw [m13, a7, c12, gw_gen _ (hb _ (by omega))], by rw [m15, a9, c14, gw_gen _ (hb _ (by omega))],
    by rw [c16, gw_gen _ (hb _ hit)], by rw [c17, gw_gen _ (hb _ hod)], r18, by rw [p19, r10],
    by rw [p20, r11], by rw [p21, r18], by rw [cp, hv, hpow]⟩

/-- **`level_queries`' path**: its two `HeapBuf`s, no `frameAddr`, its two calls, no load, its
heap hints the cap's and the flags' words. -/
theorem lq_parts (σ : Val) {es : List Memory.Ev}
    (hes : es = (lqBodyA q base folds leaf d cd mu nhs hbits fin).flatMap (slEvs σ))
    (hstr : (lqBodyA q base folds leaf d cd mu nhs hbits fin).all Stmt.straight = true) (hcd : cd ≤ 8)
    (v6 : σ (.n 6) = gen ^ (4 * 2 ^ cd)) (v8 : σ (.n 8) = gen ^ 2 ^ cd) :
    allocDsts es = [.n 7, .n 9] ∧ allocs σ es = [4 * 2 ^ cd, 2 ^ cd] ∧ addrs es = [] ∧
      calls es = [⟨"verify_merkle_cap__L" ++ natStr cd, [.n 7, .n 9], [.n 10, .n 11], true⟩,
        ⟨oqName base folds leaf (d - cd) mu nhs hbits fin,
          [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17], [.n 18], true⟩] ∧
      loadAddrs σ es = [] ∧
      heapHintAddrs σ es = (List.range (4 * 2 ^ cd)).map (fun k => (σ (.n 7)).limb 0 * addressOfIndex (0 + k)) ++
        (List.range (2 ^ cd)).map (fun k => (σ (.n 9)).limb 0 * addressOfIndex (0 + k)) := by
  obtain ⟨i1, i2, i3, i4⟩ := straight_parts σ _ hstr
  rw [← hes] at i1 i2 i3 i4
  have h2 : 2 ^ cd ≤ 256 := two_pow_le8 hcd
  have hal : (lqBodyA q base folds leaf d cd mu nhs hbits fin).filterMap Stmt.allocSz =
      [(.n 7, .inr (.n 6)), (.n 9, .inr (.n 8))] := by
    rw [lqBodyA_eq, List.filterMap_append, List.filterMap_append,
      pow_filterMap Stmt.allocSz (fun a ha => by cases a <;> first | rfl | simp [lpPure] at ha)]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [i1, hal]; rfl
  · rw [i2, hal]
    show [logG (σ (.n 6)), logG (σ (.n 8))] = _
    rw [v6, v8, gen_pow_eq_ofK, gen_pow_eq_ofK, logG_spec (lt_of_le_of_lt (by omega : 4 * 2 ^ cd ≤ 1024)
      (by norm_num)), logG_spec (lt_of_le_of_lt (by omega : 2 ^ cd ≤ 1024) (by norm_num))]
  · rw [i3, lqBodyA_eq, List.filterMap_append, List.filterMap_append,
      pow_filterMap Stmt.addrS (fun a ha => by cases a <;> first | rfl | simp [lpPure] at ha)]
    rfl
  · rw [i4, lqBodyA_eq, List.filterMap_append, List.filterMap_append,
      pow_filterMap Stmt.callS (fun a _ => rfl)]
    rfl
  · rw [loadAddrs, hes, filterMap_slEvs (Ev.loadAddr? σ) σ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl),
      lqBodyA_eq, List.filterMap_append, List.filterMap_append,
      pow_filterMap _ (fun a ha => by cases a <;> first | rfl | simp [lpPure] at ha)]
    rfl
  · rw [heapHintAddrs, hes, flatMap_slEvs (Ev.hintAddrs σ) σ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl),
      lqBodyA_eq, List.flatMap_append, List.flatMap_append,
      pow_flatMap _ (fun a ha => by cases a <;> first | rfl | simp [lpPure] at ha)]
    rw [show (List.range (4 * 2 ^ cd)).map (fun k => (σ (.n 7)).limb 0 * addressOfIndex (0 + k)) ++
        (List.range (2 ^ cd)).map (fun k => (σ (.n 9)).limb 0 * addressOfIndex (0 + k)) =
        (((List.range (4 * 2 ^ cd)).map (fun k => (σ (.n 7)).limb 0 * addressOfIndex (0 + k)) ++
          ((List.range (2 ^ cd)).map (fun k => (σ (.n 9)).limb 0 * addressOfIndex (0 + k)) ++ [])) ++ []) ++ []
      by simp only [List.append_nil]]
    rfl

end Body

/-- The queries' memory from the cap's and flags' words and the caller's. -/
theorem lq_oqMem {l : LqCall} {q base cd c : ℕ} {s : Oq} {rd : Reader} {li : E} (hcd : 1 ≤ cd)
    (hst : l.Static q cd s) (hoQ : (l.oqG s q base cd c li).Q = q)
    (hc : ReadsAt rd (ptrAt c) l.capW) (hf : ReadsAt rd (ptrAt (c + 4 * 2 ^ cd)) l.flW)
    (hm : l.Mem q cd s rd) : (l.oqG s q base cd c li).Mem rd := by
  obtain ⟨hcl, hfl, -, -, -, hW⟩ := hst
  obtain ⟨hR1, hR2, hR3⟩ := hm
  refine ⟨hR1, hR2, fun k hk => ?_⟩
  rw [hoQ] at hk
  obtain ⟨hx, hb, hwin⟩ := hR3 k hk
  obtain ⟨hq, hrow, hsl, -, e0, e1, ef⟩ := hW k hk
  obtain ⟨b1, b2, -⟩ := cap_bounds hcd hq
  have hc2 : 2 ^ (cd + 1) = 2 * 2 ^ cd := by rw [pow_succ]; ring
  have hf2 : 2 ^ (cd - 1) * 2 = 2 ^ cd := by rw [← pow_succ]; congr 1; omega
  refine ⟨hx, hb, hwin, hrow, hsl, ?_, ?_, ?_⟩
  · show LoadHolds rd (ptrAt (c + 2 ^ (cd + 1))) (2 * ((l.ws k).1 / 2 ^ s.pd))
      (digestHalves (climbD (merkleLeafDigest (l.ws k).2.1) (l.ws k).1 (l.ws k).2.2)).1
    have hlt : 2 ^ (cd + 1) + 2 * ((l.ws k).1 / 2 ^ s.pd) < l.capW.length := by rw [hcl]; omega
    have h := hc _ hlt
    rw [← List.getD_eq_getElem _ 0 hlt, e0] at h
    exact loadHolds_ptrAt_add.mpr h
  · show LoadHolds rd (ptrAt (c + 2 ^ (cd + 1))) (2 * ((l.ws k).1 / 2 ^ s.pd) + 1)
      (digestHalves (climbD (merkleLeafDigest (l.ws k).2.1) (l.ws k).1 (l.ws k).2.2)).2
    have hlt : 2 ^ (cd + 1) + 2 * ((l.ws k).1 / 2 ^ s.pd) + 1 < l.capW.length := by rw [hcl]; omega
    have h := hc _ hlt
    rw [← List.getD_eq_getElem _ 0 hlt, e1, Nat.add_assoc] at h
    exact loadHolds_ptrAt_add.mpr h
  · show LoadHolds rd (ptrAt (c + 4 * 2 ^ cd + 2 ^ (cd - 1))) ((l.ws k).1 / 2 ^ (s.pd + 1)) 1
    have hlt : 2 ^ (cd - 1) + (l.ws k).1 / 2 ^ (s.pd + 1) < l.flW.length := by rw [hfl]; omega
    have h := hf _ hlt
    rw [← List.getD_eq_getElem _ 0 hlt, ef] at h
    exact loadHolds_ptrAt_add.mpr h

/-- `verify_merkle_cap`'s meaning from the cap's and flags' words. -/
theorem lq_vmcMeaning {cd c : ℕ} {capW flW : List E} {root : Digest} {rd : Reader} (hcd : 1 ≤ cd)
    (hcl : capW.length = 4 * 2 ^ cd) (hfl : flW.length = 2 ^ cd) (hcap : CapOk cd capW flW root)
    (hc : ReadsAt rd (ptrAt c) capW) (hf : ReadsAt rd (ptrAt (c + 4 * 2 ^ cd)) flW) :
    MeaningVerifyMerkleCap cd rd [ptrAt c, ptrAt (c + 4 * 2 ^ cd)]
      [(digestHalves root).1, (digestHalves root).2] := by
  obtain ⟨hK, hH, hZ, hr⟩ := hcap
  have h4 : 2 ^ (cd + 2) = 4 * 2 ^ cd := by rw [pow_add]; ring
  have hev : 2 ^ cd = 2 * 2 ^ (cd - 1) := by rw [← pow_succ']; congr 1; omega
  have lc : ∀ k, k < 2 ^ (cd + 2) → LoadHolds rd (ptrAt c) k (capW.getD k 0) := fun k hk => by
    have hk' : k < capW.length := by rw [hcl]; omega
    rw [List.getD_eq_getElem _ _ hk']
    exact hc _ hk'
  have lf : ∀ k, k < 2 ^ cd → LoadHolds rd (ptrAt (c + 4 * 2 ^ cd)) k (flW.getD k 0) := fun k hk => by
    have hk' : k < flW.length := by rw [hfl]; omega
    rw [List.getD_eq_getElem _ _ hk']
    exact hf _ hk'
  refine ⟨fun k => capW.getD k 0, fun k => flW.getD k 0, fun k _ hk => lc k hk,
    fun k _ hk => ⟨lf k hk, hK k (by omega) hk⟩, fun k h1 h2 h3 => hH k h1 h2 h3, fun k h1 h2 h3 => ?_, ?_⟩
  · obtain ⟨z1, z2⟩ := hZ k h1 h2 h3
    refine ⟨?_, ?_⟩
    · have := lf (2 * k) (by omega); rwa [z1] at this
    · have := lf (2 * k + 1) (by omega); rwa [z2] at this
  · rw [← hr]

/-- `level_queries`' cap and flag entries, from its buffers' words. -/
theorem lq_capPops {rd : Reader} {σ : Val} {c cd : ℕ} {capW flW : List E}
    (hcl : capW.length = 4 * 2 ^ cd) (hfl : flW.length = 2 ^ cd) (v7 : σ (.n 7) = ptrAt c)
    (v9 : σ (.n 9) = ptrAt (c + 4 * 2 ^ cd)) (hc : ReadsAt rd (ptrAt c) capW)
    (hf : ReadsAt rd (ptrAt (c + 4 * 2 ^ cd)) flW) :
    capPops rd σ cd = [("merkle_caps", capW), ("merkle_cap_active", flW)] := by
  have h1 := dest_words_eq v7 hc
  have h2 := dest_words_eq v9 hf
  rw [hcl] at h1
  rw [hfl] at h2
  simp only [capPops, h1, h2]

/-- `level_queries`' arguments at second argument `li`. -/
def LqCall.argsG (l : LqCall) (li : E) : List E :=
  [l.lam, li, ptrAt l.icf, ptrAt l.ihs, ptrAt l.ipos, ptrAt l.iptr]

/-- `level_queries`' end, from its pieces. -/
theorem lq_end_le {c q N cd F V O L T x : ℕ} (hN : N ≤ q) (hcd : 2 ^ cd ≤ 256) (hV : V ≤ F) (hO : O ≤ F)
    (hL : L ≤ F) (hT : T ≤ F) (hx : x ≤ c + (4 * 2 ^ cd + 2 ^ cd) + 15 + V + 15 + O + (N + 2) * (L + T + 32)) :
    x ≤ c + (q + 2) * (3 * F + 2048) := by
  have h1 : (N + 2) * (L + T + 32) ≤ (q + 2) * (F + F + 32) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (q + 2) * (F + F + 32) = q * F + q * F + 32 * q + 4 * F + 64 := by ring
  have h3 : (q + 2) * (3 * F + 2048) = 3 * (q * F) + 2048 * q + 6 * F + 4096 := by ring
  omega

set_option maxHeartbeats 1000000 in
/-- **`level_queries__L…` completes placed**, at any second argument, its end bounded. -/
theorem lqAGE_complete' {kd : ℕ} {name : String} {q base folds leaf d cd mu nhs hbits fin : ℕ} {fn : Fn}
    (hfn : coreProgram.find? name = some fn) (hpar : fn.params = osParams 6)
    (hbody : fn.body = lqBody q base folds leaf d cd mu nhs hbits fin)
    (hck : lqChecks q base folds leaf d cd mu nhs hbits fin = true) :
    LqAGE fs al cert kd name q base cd (oqShapeK (oqKey base folds leaf (d - cd) mu nhs hbits fin)).oq := by
  simp only [lqChecks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨hchk, hstr⟩, hat⟩, hpow⟩, hent⟩, hvmc⟩, hcdd, hq1, hq2, hb1⟩ := hck
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hchk
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hent
  have hp' : openingQueriesLoops.find? (fun e => e.2.2.key == oqKey base folds leaf (d - cd) mu nhs hbits fin) =
      some p := hp
  have hpm : p ∈ openingQueriesLoops := List.mem_of_find?_eq_some hp'
  have hpk : p.2.2.key = oqKey base folds leaf (d - cd) mu nhs hbits fin := by
    simpa using List.find?_some hp'
  have hpn : p.1 = oqName base folds leaf (d - cd) mu nhs hbits fin := by
    rw [oq_names p hpm, hpk, oqName_eq]
  have hsK : oqShapeK (oqKey base folds leaf (d - cd) mu nhs hbits fin) = p.2.2 := by
    unfold oqShapeK; rw [hp]; rfl
  rw [hsK]
  have hkb : p.2.2.base = base := by
    have := congrArg List.head? hpk; simpa [OqShape.key, oqKey] using this
  obtain ⟨hrs, hfin', -⟩ := oqSide_all p hpm
  have hcd : 2 ≤ cd ∧ cd ≤ 8 := by
    simp only [merkleCapNames, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hvmc
    omega
  obtain ⟨hcd1, hcd2⟩ := hcd
  set s := p.2.2.oq with hs
  have hsb : s.base = base := hkb
  intro l li R hst hR fp c hfc
  have hst' := hst
  obtain ⟨hcl, hfl, hcap, hrl, hnh, hW⟩ := hst
  set o := l.oqG s q base cd c li with ho
  have hoQ : o.Q = q := by
    show oqCount (lqOdd q base) s.base (lqIters q base) = q
    rw [hsb]; exact lq_count q base
  have hNlt : lqIters q base + 1 < ordG := by unfold lqIters ordG; split <;> omega
  have h2 : 2 ^ cd ≤ 256 := two_pow_le8 hcd2
  have h4 : 2 ^ (cd + 2) = 4 * 2 ^ cd := by rw [pow_add]; ring
  -- the queries' call's facts
  have hoS : o.Static := by
    refine ⟨hrs, hfin', by show 1 ≤ cd; omega, hrl, hnh, ?_, hNlt, fun k hk => ?_⟩
    · show lqOdd q base ≤ s.base
      rw [hsb]; unfold lqOdd; split <;> omega
    · rw [hoQ] at hk
      obtain ⟨h1, h2, h3, h4, -⟩ := hW k hk
      exact ⟨h1, h2, h3, h4⟩
  have hoR : o.Reg (fun i => R i ∨ (c ≤ i ∧ i < c + (4 * 2 ^ cd + 2 ^ cd))) := by
    obtain ⟨hco, hhs, hwin, hpp⟩ := hR
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hoQ] at hk
      obtain ⟨hq, -, -, -, -, -, -⟩ := hW k hk
      obtain ⟨b1, b2, b3⟩ := cap_bounds (by omega) hq
      show OqQReg _ s (ptrAt (c + 2 ^ (cd + 1))) (ptrAt (c + 4 * 2 ^ cd + 2 ^ (cd - 1))) (ptrAt l.icf)
        (ptrAt l.ihs) (ptrAt (l.wp k)) (l.ws k).1
      have h1 : 2 ^ (cd - 1) * 2 = 2 ^ cd := by rw [← pow_succ]; congr 1; omega
      have h2 : 2 ^ (cd + 1) = 2 * 2 ^ cd := by rw [pow_succ]; ring
      refine ⟨fun off ho' => oqIn_ptr (Or.inl (hco off ho')), fun hf off ho' => oqIn_ptr (Or.inl (hhs hf off ho')),
        fun off ho' => oqIn_ptr (Or.inl (hwin k hk off ho')), oqIn_addr (Or.inr ⟨by omega, by omega⟩),
        fun e he => oqIn_addr (Or.inr ⟨by omega, ?_⟩)⟩
      rw [b3]; omega
    · rw [hoQ] at hk
      exact ⟨Or.inl (hpp k hk).1, Or.inl (hpp k hk).2⟩
  -- the valuation
  have hlen : (l.argsG li).length = 6 := rfl
  have hc6 : chk (l.argsG li).length (lqBody q base folds leaf d cd mu nhs hbits fin) = some c' := by
    rw [hlen]; exact hc'
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = fwdVal (fun _ => none) (lqW c cd (digestHalves l.root).1 (digestHalves l.root).2 o.mret)
      (l.argsG li) (lqBody q base folds leaf d cd mu nhs hbits fin) := ⟨_, rfl⟩
  obtain ⟨v6, v7, v8, v9, v10, v11, v13, v15, v16, v17, v18, v19, v20, v21, vpow⟩ :=
    lq_vals hσ hc6 hat hcd2 hq2 hpow
  have w7 : lqW c cd (digestHalves l.root).1 (digestHalves l.root).2 o.mret 7 = ptrAt c := by simp [lqW]
  have w9 : lqW c cd (digestHalves l.root).1 (digestHalves l.root).2 o.mret 9 = ptrAt (c + 4 * 2 ^ cd) := by
    simp [lqW]
  have w10 : lqW c cd (digestHalves l.root).1 (digestHalves l.root).2 o.mret 10 = (digestHalves l.root).1 := by
    simp [lqW]
  have w11 : lqW c cd (digestHalves l.root).1 (digestHalves l.root).2 o.mret 11 = (digestHalves l.root).2 := by
    simp [lqW]
  have w18 : lqW c cd (digestHalves l.root).1 (digestHalves l.root).2 o.mret 18 = o.mret := by simp [lqW]
  rw [w7] at v7 v13
  rw [w9] at v9 v15
  rw [w10] at v10 v19
  rw [w11] at v11 v20
  rw [w18] at v18 v21
  have hpar' : ∀ i < 6, σ (.n i) = (l.argsG li).getD i 0 := fun i hi => by
    rw [hσ]; exact fwd_param hc6 (by rw [hlen]; exact hi)
  have v0 : σ (.n 0) = l.lam := hpar' 0 (by norm_num)
  rw [v0] at vpow
  -- the path
  obtain ⟨es, hes⟩ : ∃ es, es = (lqBodyA q base folds leaf d cd mu nhs hbits fin).flatMap (slEvs σ) := ⟨_, rfl⟩
  obtain ⟨i1, hallocs, i3, hcalls, hlA, hhA⟩ := lq_parts σ hes hstr hcd2 v6 v8
  have hbA : fn.body = lqBodyA q base folds leaf d cd mu nhs hbits fin ++
      [.ret [.n 19, .n 20, .n 21, .n (22 + osPowLen q)]] := by rw [hbody, lqBody_split]
  have hwk : walk σ fn.body = .ret es [.n 19, .n 20, .n 21, .n (22 + osPowLen q)] := by
    rw [hbA, hes]; exact walk_straight σ _ _ hstr
  have hsum : (allocs σ es).sum = 4 * 2 ^ cd + 2 ^ cd := by
    rw [hallocs]; simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  have hlo : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hfn, Fn.loop, hbA, List.reverse_append]; rfl
  have hnode : NodeAt cert (fp, c) name σ (allocs σ es) es := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [i1, hallocs]
      show [σ (.n 7), σ (.n 9)] = [ofK (addressOfIndex c), ofK (addressOfIndex (c + 4 * 2 ^ cd))]
      rw [v7, v9]
    · rw [i3] at hx; exact absurd hx List.not_mem_nil
  have hown : ∀ i, c ≤ i → i < c + (4 * 2 ^ cd + 2 ^ cd) → ownData cert fp c name (allocs σ es) es i := by
    intro i h1 h2
    rw [hallocs]
    by_cases hi : i < c + 4 * 2 ^ cd
    · exact ownData_buf (s := 4 * 2 ^ cd) (b := c) (by simp [bases]) h1 hi
    · exact ownData_buf (s := 2 ^ cd) (b := c + 4 * 2 ^ cd) (by simp [bases]) (by omega) (by omega)
  -- the own words
  let Wo : Words := [(c, l.capW), (c + 4 * 2 ^ cd, l.flW)]
  have hWo : ∀ rd, HoldsWords rd Wo → ReadsAt rd (ptrAt c) l.capW ∧ ReadsAt rd (ptrAt (c + 4 * 2 ^ cd)) l.flW :=
    fun rd h => ⟨h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hWoIn : WordsInA Wo (fp + 2) (fp + fs name) c (c + (allocs σ es).sum) := by
    rw [hsum]
    refine ⟨fun x hx => Or.inr ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · show c ≤ c ∧ c + l.capW.length ≤ c + (4 * 2 ^ cd + 2 ^ cd)
        rw [hcl]; omega
      · rw [List.mem_singleton] at hx
        subst hx
        show c ≤ c + 4 * 2 ^ cd ∧ c + 4 * 2 ^ cd + l.flW.length ≤ c + (4 * 2 ^ cd + 2 ^ cd)
        rw [hfl]; omega
    · refine List.pairwise_pair.mpr (Or.inl ?_)
      show c + l.capW.length ≤ c + 4 * 2 ^ cd
      rw [hcl]
  -- the callees
  have hcR : ∀ i < 2 ^ (cd + 2), c ≤ c + i ∧ c + i < c + (4 * 2 ^ cd + 2 ^ cd) := fun i hi =>
    ⟨Nat.le_add_right _ _, by rw [h4] at hi; omega⟩
  have hfR : ∀ i < 2 ^ cd, c ≤ c + 4 * 2 ^ cd + i ∧ c + 4 * 2 ^ cd + i < c + (4 * 2 ^ cd + 2 ^ cd) :=
    fun i hi => ⟨by omega, by omega⟩
  obtain ⟨eo, heoB, heo⟩ := oqAE_all (fs := fs) (al := al) (cert := cert) kd p hpm o _ rfl hoS hoR
    (allocBase (al (oqName base folds leaf (d - cd) mu nhs hbits fin))
      (allocBase (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd)) +
        fs ("verify_merkle_cap__L" ++ natStr cd)))
    (allocBase (al (oqName base folds leaf (d - cd) mu nhs hbits fin))
      (allocBase (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd)) +
        fs ("verify_merkle_cap__L" ++ natStr cd)) + fs p.1) le_rfl
  rw [hpn] at heo
  have hv : CallAtA fs al cert kd ("verify_merkle_cap__L" ++ natStr cd) ([V.n 7, .n 9].map σ)
      ([V.n 10, .n 11].map σ) (fun i => c ≤ i ∧ i < c + (4 * 2 ^ cd + 2 ^ cd)) (fun _ => False) (fun _ => True)
      (fun rd => l.Mem q cd s rd ∧ HoldsWords rd Wo) FreePost (fs ("verify_merkle_cap__L" ++ natStr cd))
      (allocBase (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd)))
      (allocBase (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd)) +
        fs ("verify_merkle_cap__L" ++ natStr cd))
      (allocBase (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd)) +
        fs ("verify_merkle_cap__L" ++ natStr cd)) := by
    have ea : ([V.n 7, .n 9] : List V).map σ = [ptrAt c, ptrAt (c + 4 * 2 ^ cd)] := by
      simp only [List.map_cons, List.map_nil, v7, v9]
    have er : ([V.n 10, .n 11] : List V).map σ = [(digestHalves l.root).1, (digestHalves l.root).2] := by
      simp only [List.map_cons, List.map_nil, v10, v11]
    rw [ea, er]
    exact (vmcA (fs := fs) (al := al) (cert := cert) kd ("verify_merkle_cap__L" ++ natStr cd, cd) hvmc c
      (c + 4 * 2 ^ cd) _ (fun i => c ≤ i ∧ i < c + (4 * 2 ^ cd + 2 ^ cd)) hcR hfR _ _).mono
      (fun _ h => h) (fun _ h => h) (fun _ h => h)
      (fun rd h => lq_vmcMeaning (by omega) hcl hfl hcap (hWo rd h.2).1 (hWo rd h.2).2) (fun _ _ _ h => h)
  have hq' : CallAtA fs al cert kd (oqName base folds leaf (d - cd) mu nhs hbits fin)
      ([V.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17].map σ) ([V.n 18].map σ)
      (fun i => R i ∨ (c ≤ i ∧ i < c + (4 * 2 ^ cd + 2 ^ cd))) (fun _ => False) (fun _ => True)
      (fun rd => l.Mem q cd s rd ∧ (HoldsWords rd Wo ∧ True))
      (fun rd t => t.pops coreProgram rd = o.pops ∧ t.Every (ExactAt coreProgram rd))
      (fs (oqName base folds leaf (d - cd) mu nhs hbits fin))
      (allocBase (al (oqName base folds leaf (d - cd) mu nhs hbits fin))
        (allocBase (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd)) +
          fs ("verify_merkle_cap__L" ++ natStr cd)))
      (allocBase (al (oqName base folds leaf (d - cd) mu nhs hbits fin))
        (allocBase (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd)) +
          fs ("verify_merkle_cap__L" ++ natStr cd)) + fs (oqName base folds leaf (d - cd) mu nhs hbits fin)) eo := by
    have ea : ([V.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17] : List V).map σ = o.margs := by
      simp only [List.map_cons, List.map_nil, v13, v15, v16, v17, hpar' 1 (by omega), hpar' 2 (by omega),
        hpar' 3 (by omega), hpar' 4 (by omega), hpar' 5 (by omega), ptrAt_mul_gen]
      rfl
    have er : ([V.n 18] : List V).map σ = [o.mret] := by simp only [List.map_cons, List.map_nil, v18]
    rw [ea, er]
    exact heo.mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
      (fun rd h => lq_oqMem (by omega) hst' hoQ (hWo rd h.2.1).1 (hWo rd h.2.1).2 h.1) (fun _ _ _ h => h)
  have hk : KidsAtF fs al cert kd σ (fun i => R i ∨ ownData cert fp c name (allocs σ es) es i) (l.Mem q cd s)
      (fun rd => HoldsWords rd Wo) (fun _ => False)
      [FreePost, fun rd t => t.pops coreProgram rd = o.pops ∧ t.Every (ExactAt coreProgram rd)]
      (calls es) (c + (allocs σ es).sum) eo (fun rd => (HoldsWords rd Wo ∧ True) ∧ True) (fun _ => False) := by
    rw [hcalls, hsum, KidsAtF]
    simp only [↓reduceIte]
    refine ⟨_, _, _, _, _, fun i hi => Or.inl (Or.inr (hown i hi.1 hi.2)), hv, ?_⟩
    rw [KidsAtF]
    simp only [↓reduceIte]
    refine ⟨_, _, _, _, _, fun i hi => ?_, hq', ?_⟩
    · rcases hi with hi | hi
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr (hown i hi.1 hi.2))
    · rw [KidsAtF]; exact ⟨rfl, fun _ h => h, fun _ h => h.elim⟩
  -- the loads and the heap hints
  have hloads : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c name (allocs σ es) es i ∨ R i ∨ False) := by
    intro A hA
    rw [hlA] at hA
    exact absurd hA List.not_mem_nil
  have hhints : ∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c name (allocs σ es) es i ∨ R i ∨ False) := by
    intro A hA
    rw [hhA, v7, v9] at hA
    rcases List.mem_append.mp hA with hA | hA
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hA
      have hk' := List.mem_range.mp hk
      simp only [Nat.zero_add, Main.addr_ofK]
      exact ⟨c + k, rfl, Or.inl (hown _ (by omega) (by omega))⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hA
      have hk' := List.mem_range.mp hk
      simp only [Nat.zero_add, Main.addr_ofK]
      exact ⟨c + 4 * 2 ^ cd + k, rfl, Or.inl (hown _ (by omega) (by omega))⟩
  -- the events
  have hev : ∀ rd, LowDef kd rd → l.Mem q cd s rd → (HoldsWords rd Wo ∧ True) ∧ True →
      ∀ ev ∈ es, ev.Holds rd σ := by
    intro rd _ _ _
    rw [hes]
    exact holds_slEvs _ (fun a ha => lq_holds hσ hc6 hat rd a (lqA_sub ha))
      (fun c0 f0 a0 h => absurd h (lq_noCallIf c0 f0 a0))
  -- the post
  have hop : o.pops = (List.range q).flatMap fun k => oqQE s (l.ws k) := by
    unfold OqCall.pops; rw [hoQ]; rfl
  have hpost : ∀ rd ts, LowDef kd rd → l.Mem q cd s rd → (HoldsWords rd Wo ∧ True) ∧ True →
      Tree.KidsValid coreProgram rd σ (calls es) ts →
      KidsPost rd [FreePost, fun rd t => t.pops coreProgram rd = o.pops ∧ t.Every (ExactAt coreProgram rd)]
        (calls es) ts →
      (Memory.Tree.node name σ (allocs σ es) ts).pops coreProgram rd = l.pops q s ∧
        (Memory.Tree.node name σ (allocs σ es) ts).Every (ExactAt coreProgram rd) := by
    intro rd ts _ _ hO hv' hq
    rw [hcalls] at hv' hq
    rcases ts with _ | ⟨tv, _ | ⟨tq, _ | ⟨t3, ts⟩⟩⟩
    · exact (hv' : False).elim
    · obtain ⟨-, -, h⟩ := hv'
      exact (h : False).elim
    · have hqv := (kidsPost_cons.mp hq).1 rfl
      have hqo := (kidsPost_cons.mp (kidsPost_cons.mp hq).2).1 rfl
      have hkk : Tree.popsKids coreProgram rd [tv, tq] = [[], o.pops] := by
        simp only [Tree.popsKids, hqv.1, hqo.1]
      obtain ⟨hc, hf⟩ := hWo rd hO.1.1
      refine ⟨?_, ?_⟩
      · rw [lq_node_pops hfn hbody σ _ hkk, lq_capPops hcl hfl v7 v9 hc hf, hop]
        rfl
      · rw [Tree.every_node]
        refine ⟨exactAt_of_walk hfn hwk fun ev hev => ?_,
          (⟨hqv.2, hqo.2, trivial⟩ : tv.Every (ExactAt coreProgram rd) ∧ tq.Every (ExactAt coreProgram rd) ∧ True)⟩
        cases ev with
        | atom a =>
          have := walk_atomsAll (by rw [hbody]; exact hat) hwk a hev
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
          exact exact_of_not_computed this.2
        | _ => trivial
    · obtain ⟨-, -, -, -, h⟩ := hv'
      exact (h : False).elim
  have hparams : fn.params.map σ = (l.argsG li) := by
    rw [hpar, hσ]; exact fwd_params hc6
  have hrets : ([.n 19, .n 20, .n 21, .n (22 + osPowLen q)] : List V).map σ =
      [(digestHalves l.root).1, (digestHalves l.root).2, (l.oqG s q base cd 0 li).mret, l.lam ^ q] := by
    simp only [List.map_cons, List.map_nil, v19, v20, v21, vpow]
    rfl
  have hoN : o.N ≤ q := by show lqIters q base ≤ q; unfold lqIters; split <;> omega
  refine ⟨eo, fun F hF => lq_end_le hoN h2 (hF ("verify_merkle_cap__L" ++ natStr cd)) (hF p.1) (hF p.2.1) (hF (tailKey p.2.1)) (by
    have := allocBase_le (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd))
    have := allocBase_le (al (oqName base folds leaf (d - cd) mu nhs hbits fin))
      (allocBase (al ("verify_merkle_cap__L" ++ natStr cd)) (c + (4 * 2 ^ cd + 2 ^ cd)) +
        fs ("verify_merkle_cap__L" ++ natStr cd))
    omega), ?_⟩
  exact callAtA_node hlo hfc ⟨σ, fn, es, [.n 19, .n 20, .n 21, .n (22 + osPowLen q)], Wo,
    [FreePost, fun rd t => t.pops coreProgram rd = o.pops ∧ t.Every (ExactAt coreProgram rd)],
    fun rd => (HoldsWords rd Wo ∧ True) ∧ True, fun _ => False,
    hfn, hparams, hwk, hrets, hnode, hWoIn, hloads, hhints, fun _ h => h.elim, hk, fun _ _ => trivial,
    hev, hpost⟩

/-- **`level_queries__L…` completes placed**, at any second argument. -/
theorem lqAG_complete' {kd : ℕ} {name : String} {q base folds leaf d cd mu nhs hbits fin : ℕ} {fn : Fn}
    (hfn : coreProgram.find? name = some fn) (hpar : fn.params = osParams 6)
    (hbody : fn.body = lqBody q base folds leaf d cd mu nhs hbits fin)
    (hck : lqChecks q base folds leaf d cd mu nhs hbits fin = true) :
    LqAG fs al cert kd name q base cd (oqShapeK (oqKey base folds leaf (d - cd) mu nhs hbits fin)).oq :=
  (lqAGE_complete' hfn hpar hbody hck).toG

/-- **`level_queries__L…` completes placed.** -/
theorem lqA_complete' {kd : ℕ} {name : String} {q base folds leaf d cd mu nhs hbits fin : ℕ} {fn : Fn}
    (hfn : coreProgram.find? name = some fn) (hpar : fn.params = osParams 6)
    (hbody : fn.body = lqBody q base folds leaf d cd mu nhs hbits fin)
    (hck : lqChecks q base folds leaf d cd mu nhs hbits fin = true) :
    LqA fs al cert kd name q base cd (oqShapeK (oqKey base folds leaf (d - cd) mu nhs hbits fin)).oq :=
  lqAG_of_lqA (lqAG_complete' hfn hpar hbody hck)

/-- **Every `level_queries__L…` completes placed.** -/
theorem lqA_all (kd : ℕ) : ∀ e ∈ lqTable, LqA fs al cert kd e.1 e.2.1 e.2.2.1 e.2.2.2.2.2.2.1
    (oqShapeK (oqKey e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 (e.2.2.2.2.2.1 - e.2.2.2.2.2.2.1) e.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2)).oq := by
  intro e he
  obtain ⟨fn, hfn, hpar, hbody⟩ := lqTable_ok e he
  exact lqA_complete' hfn hpar hbody (lq_checks e he)

/-- **Every `level_queries__L…` completes placed at any second argument**, by entry. -/
theorem lqAG_allT (kd : ℕ) : ∀ e ∈ lqTable, LqAG fs al cert kd e.1 e.2.1 e.2.2.1 e.2.2.2.2.2.2.1
    (oqShapeK (oqKey e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 (e.2.2.2.2.2.1 - e.2.2.2.2.2.2.1) e.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2)).oq := by
  intro e he
  obtain ⟨fn, hfn, hpar, hbody⟩ := lqTable_ok e he
  exact lqAG_complete' hfn hpar hbody (lq_checks e he)

/-- **Every `level_queries__L…` completes placed at any second argument, its end bounded**, by entry. -/
theorem lqAGE_allT (kd : ℕ) : ∀ e ∈ lqTable, LqAGE fs al cert kd e.1 e.2.1 e.2.2.1 e.2.2.2.2.2.2.1
    (oqShapeK (oqKey e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 (e.2.2.2.2.2.1 - e.2.2.2.2.2.2.1) e.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2)).oq := by
  intro e he
  obtain ⟨fn, hfn, hpar, hbody⟩ := lqTable_ok e he
  exact lqAGE_complete' hfn hpar hbody (lq_checks e he)

/-- **Every `level_queries__L…` completes placed at any second argument.** -/
theorem lqAG_all (kd : ℕ) : LqAllG fs al cert kd :=
  fun name q base folds leaf d cd mu nhs hbits fin he =>
    lqAG_allT kd (name, q, base, folds, leaf, d, cd, mu, nhs, hbits, fin) he

/-- **Every `level_queries__L…` completes placed at any second argument, its end bounded.** -/
theorem lqAGE_all (kd : ℕ) : LqAllGE fs al cert kd :=
  fun name q base folds leaf d cd mu nhs hbits fin he =>
    lqAGE_allT kd (name, q, base, folds, leaf, d, cd, mu, nhs, hbits, fin) he

end
end LeanVM.Guest.B1.VsC
