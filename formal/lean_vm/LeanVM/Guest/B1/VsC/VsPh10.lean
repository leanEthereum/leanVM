/-
  LeanVM.Guest.B1.VsC.VsPh10

  `wC`'s windows `17 ..< 20`: the eq tensor of the rows' point, `one_plus_suffixes__L{n}`, `packed_message__L144`.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh9

/-!
# `wC`'s windows `17 ..< 20`

`vsC_w17` (statements `970 ..< 1302`): the eq tensor of the rows' point (`.n 16`'s six words) into `.n 17` (`eqtreeAt`,
its stores by `eqtreeAt_complete` on the evaluation memory), then the range check `g^n ≤ g^40`; its `RunHyp` by
`winsHyp_run_bufs`. `vsC_w18` (statement `1302`): `one_plus_suffixes__L{n}`, a leaf. `vsC_w19` (statement `1303`):
`packed_message__L144`, a leaf. `vsPh10_wins` from numeric hypotheses.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Statements `970 ..< 1300`: the eq tensor of the rows' point into `.n 17`. -/
abbrev vsEq17 : List Stmt := eqtreeAt (.n 16) (.n 17) 0 0 1078 6

/-- Statements `1300 ..< 1302`: `n ≤ 40`. -/
def vsC17b : List Atom :=
  [.const (.n 1282) (word 1099511627776 0), .rangeCheck (.n 408) (.n 1283) (.n 1284) (.n 1285) (.n 1282)]

/-- Statement `1302`: `one_plus_suffixes__L{n}`. -/
def vsC18s : Stmt := .dispatch (.n 408) opsNames [.n 18, .n 15] [.n 1286]

/-- Statement `1303`: `packed_message__L144`. -/
def vsC19s : Stmt :=
  .call "packed_message__L144" [.n 1071, .n 1072, .n 1073, .n 1074, .n 1075, .n 1076]
    [.n 1287, .n 1288, .n 1289, .n 1290, .n 1291, .n 1292]

set_option maxRecDepth 200000 in
theorem vsC17_eq : (vsC.drop 542).take 332 = vsEq17 ++ vsC17b.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC18_eq : (vsC.drop 874).take 1 = [vsC18s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC19_eq : (vsC.drop 875).take 1 = [vsC19s] := stmtsEqb_sound (by decide +kernel)

theorem as17_eq : atomsOf ((vsC.drop 542).take 332) = atomsOf vsEq17 ++ vsC17b := by
  rw [vsC17_eq, atomsOf_append', atomsOf_map]

theorem vsC_w18_eq : vsC_w18 = .call vsC18s := by rw [vsC_w18, headD_of_take_one vsC18_eq]

theorem vsC_w19_eq : vsC_w19 = .call vsC19s := by rw [vsC_w19, headD_of_take_one vsC19_eq]

set_option maxRecDepth 200000 in
/-- The eq tensor's stores are the run's, its other atoms ask nothing, its reads are no stores. -/
theorem vsEq17_shape : stC17.all (fun a => (atomsOf vsEq17).contains a) = true ∧
    (atomsOf vsEq17).all (fun a => !pureAsks a && noFTB a) = true ∧
    (eqReadsAt (.n 16) (.n 17) 0 0 1078 6).all (fun a => !vsSL.contains a) = true := by decide +kernel

theorem opsNames_getElem! : ∀ j < 41, opsNames[j]! = opsNames.getD j "" := by decide +kernel

theorem opsNames_length : opsNames.length = 41 := rfl

theorem word_2_40 : word 1099511627776 0 = gen ^ 40 := wordG (j := 40) (by norm_num)

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `17 ..< 20`' hypotheses**: the rows' point buffer `.n 16` at `b16` (its words `xs16`, at least `6`,
word `t` the point's coordinate `rs[t]`), the eq buffer `.n 17` at `b17` (its words `xs17`, the point's eq tensor level
by level), each held on the evaluation memory and on every memory with `Pre` and the words held, own; `.n 408 = g^n`,
`n ≤ 40`; `one_plus_suffixes`' arrays (`n + 1` words at `.n 18`'s `b18`, `n` at `.n 15`'s `b15`; own), its precondition
and return; `packed_message`'s message `w 1076 = ptrAt bm` (`144` words in the region), its precondition and returns;
`K` past the two leaves. -/
theorem vsPh10_wins (hk : 6 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    {b15 b16 b17 b18 bm n : ℕ} {xs16 xs17 rs as15 xm : List E}
    (h16 : vsVal rd0 w args (.n 16) = ptrAt b16) (hl16 : 6 ≤ xs16.length) (r16 : ReadsAt rd0 (ptrAt b16) xs16)
    (hO16 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b16) xs16) (hOwn16 : ∀ j < 6, Own (b16 + j))
    (hrs : rs.length = 6) (hrs16 : ∀ t < 6, xs16[t]? = some (rs.getD t 0))
    (h17 : vsVal rd0 w args (.n 17) = ptrAt b17) (hl17 : 126 ≤ xs17.length) (r17 : ReadsAt rd0 (ptrAt b17) xs17)
    (hO17 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b17) xs17) (hOwn17 : ∀ j < 126, Own (b17 + j))
    (hlev : ∀ t, 1 ≤ t → t ≤ 6 → ∀ i < 2 ^ t, xs17[2 ^ t - 2 + i]? = some ((eqKernel (rs.take t)).getD i 0))
    (h408 : vsVal rd0 w args (.n 408) = gen ^ n) (hn : n ≤ 40)
    (h18 : vsVal rd0 w args (.n 18) = ptrAt b18) (h15 : vsVal rd0 w args (.n 15) = ptrAt b15)
    (hl15 : as15.length = n) (hO18 : ∀ j < n + 1, Own (b18 + j)) (hO15 : ∀ j < n, Own (b15 + j))
    (hPops : ∀ rd, Pre rd ∧ st.O rd →
      ReadsAt rd (ptrAt b15) as15 ∧ ReadsAt rd (ptrAt b18) ((List.range (n + 1)).map (belowE as15)))
    (hw1286 : w 1286 = 0)
    (hwm : w 1076 = ptrAt bm) (hxm : xm.length = 144) (hcm : ∀ j < 144, (R (bm + j) ∨ Own (bm + j)) ∨ st.D (bm + j))
    (hPpm : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt bm) xm)
    (hpm : [w 1287, w 1288, w 1289, w 1290, w 1291, w 1292] =
      (Fs.squeeze ⟨pkAbsorb 18 xm [w 1071, w 1072, w 1073, w 1074, w 1075], []⟩).1 ::
        (Fs.squeeze ⟨pkAbsorb 18 xm [w 1071, w 1072, w 1073, w 1074, w 1075], []⟩).2.cap)
    (hK : K ⟨st.a, leafEnd fs al "packed_message__L144" (leafEnd fs al (opsNames.getD n "") st.kc), st.O, st.D,
      st.Qs ++ [PostQuiet, PostQuiet]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w17, vsC_w18, vsC_w19] st K := by
  rw [vsC_w17, vsC_w18_eq, vsC_w19_eq]
  set σ := vsVal rd0 w args with hσ
  have hg17 : ∀ x ∈ atomsOf ((vsC.drop 542).take 332), Good rd0 vsSL w σ x := vsC_atoms_good ha 542 332
  have m17e : ∀ x ∈ atomsOf vsEq17, x ∈ atomsOf ((vsC.drop 542).take 332) := fun x h => by
    rw [as17_eq]; exact List.mem_append_left _ h
  have m17b : ∀ x ∈ vsC17b, x ∈ atomsOf ((vsC.drop 542).take 332) := fun x h => by
    rw [as17_eq]; exact List.mem_append_right _ h
  let bs : ℕ → ℕ := fun v => [b16, b17].getD (v - 16) 0
  let xs : ℕ → List E := fun v => [xs16, xs17].getD (v - 16) []
  have hsp : ∀ q ∈ spC17, q = (16, 6) ∨ q = (17, 126) := fun q hq => by simpa [spC17] using hq
  have hp : ∀ q ∈ spC17, σ (.n q.1) = ptrAt (bs q.1) := fun q hq => by
    rcases hsp q hq with rfl | rfl
    exacts [h16, h17]
  have hn' : ∀ q ∈ spC17, q.2 ≤ (xs q.1).length := fun q hq => by
    rcases hsp q hq with rfl | rfl
    exacts [hl16, hl17]
  have h0 : ∀ q ∈ spC17, ReadsAt rd0 (ptrAt (bs q.1)) (xs q.1) := fun q hq => by
    rcases hsp q hq with rfl | rfl
    exacts [r16, r17]
  have e1 : ∀ x ∈ stC17, x ∈ atomsOf vsEq17 := fun x hx => by
    simpa using List.all_eq_true.mp vsEq17_shape.1 x hx
  have e2 : ∀ x ∈ atomsOf vsEq17, pureAsks x = false ∧ noFTB x = true := fun x hx => by
    simpa using List.all_eq_true.mp vsEq17_shape.2.1 x hx
  have eqH : ∀ a, Stmt.atom a ∈ vsEq17 → a.Holds rd0 σ := by
    refine eqtreeAt_complete (by norm_num) (S := vsSL) (fun a h => storesOf_isLoad (by rw [vsSL_eq]; exact h))
      (fun a h hS => absurd (List.all_eq_true.mp vsEq17_shape.2.2 a h) (by simpa using hS))
      (fun a h hS => holds_bufs vsC_w17_bufs hg17 bs xs hp hn' h0 (m17e a (mem_atomsOf' h)) hS
        (e2 a (mem_atomsOf' h)).1 (e2 a (mem_atomsOf' h)).2)
      hrs (fun t ht => ?_) (fun t h1 h2 i hi => ?_)
    · rw [h16, Nat.zero_add]; exact loadHolds_of_get? r16 (hrs16 t ht)
    · rw [h17, Nat.zero_add]; exact loadHolds_of_get? r17 (hlev t h1 h2 i hi)
  have hst : ∀ x ∈ stC17, MemF rd0 σ x := fun x hx => by
    have := eqH x (mem_of_mem_atomsOf (e1 x hx))
    cases x with
    | load d p off => exact this
    | _ => trivial
  have h64 : 64 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  refine winsHyp_run_bufs vsC_w17_bufs hg17 bs xs hp hn' h0
    (fun q hq j hj => by
      rcases hsp q hq with rfl | rfl
      exacts [Or.inl (hOwn16 j hj), Or.inl (hOwn17 j hj)])
    (fun rd hpr ho q hq => by
      rcases hsp q hq with rfl | rfl
      exacts [hO16 rd hpr ho, hO17 rd hpr ho]) hst
    (fun x hx => by
      rw [vsC_w17_pure, pureC17, List.mem_singleton] at hx
      subst hx
      have hy := good_rcY (hg17 (.rangeCheck (.n 408) (.n 1283) (.n 1284) (.n 1285) (.n 1282))
        (m17b _ (by simp [vsC17b]))) (by omega)
      rw [show σ (.n 1282) = word 1099511627776 0 from hg17 (.const (.n 1282) (word 1099511627776 0))
        (m17b _ (by simp [vsC17b])), word_2_40, h408, gen_div hn] at hy
      exact ⟨by rw [h408]; exact lowW_pow (by omega), by rw [hy]; exact lowW_pow (by omega)⟩) ?_
  -- `one_plus_suffixes__L{n}`
  have r18 : ∀ v ∈ [V.n 1286], σ v = w v.idx := vsVal_retC (rd0 := rd0) (w := w) ha vsC18_eq
  have hargs18 : (argsOf vsC18s).map σ = [ptrAt b18, ptrAt b15] := by
    show [σ (.n 18), σ (.n 15)] = _
    rw [h18, h15]
  have hrets18 : (retsOf vsC18s).map σ = [0] := by
    show [σ (.n 1286)] = _
    rw [r18 (.n 1286) (by simp), hw1286]
  have L18 := one_plus_suffixes_leafA fs al cert k hn (ptrAt b18) (ptrAt b15) as15 hl15
    (R := fun i => (R i ∨ Own i) ∨ st.D i)
    (fun off hoff => ⟨b18 + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hO18 off hoff))⟩)
    (fun off hoff => ⟨b15 + off, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hO15 off hoff))⟩)
  rw [← hargs18, ← hrets18] at L18
  refine winsHyp_call_leaf (g := opsNames.getD n "")
    ⟨n, by rw [opsNames_length]; omega, by rw [h408, Value.gen_pow_eq_ofK], opsNames_getElem! _ (by omega)⟩ L18
    (fun _ h => h) (fun rd hp => hPops rd hp) ?_
  -- `packed_message__L144`
  have r19 : ∀ v ∈ [V.n 1287, .n 1288, .n 1289, .n 1290, .n 1291, .n 1292], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC19_eq
  have r16' : ∀ v ∈ [V.n 1071, .n 1072, .n 1073, .n 1074, .n 1075, .n 1076, .n 1077], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC16_eq
  have hargs19 : (argsOf vsC19s).map σ = [w 1071, w 1072, w 1073, w 1074, w 1075, ptrAt bm] := by
    show [σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075), σ (.n 1076)] = _
    rw [r16' (.n 1071) (by simp), r16' (.n 1072) (by simp), r16' (.n 1073) (by simp), r16' (.n 1074) (by simp),
      r16' (.n 1075) (by simp), r16' (.n 1076) (by simp), hwm]
  have hrets19 : (retsOf vsC19s).map σ = [w 1287, w 1288, w 1289, w 1290, w 1291, w 1292] := by
    show [σ (.n 1287), σ (.n 1288), σ (.n 1289), σ (.n 1290), σ (.n 1291), σ (.n 1292)] = _
    rw [r19 (.n 1287) (by simp), r19 (.n 1288) (by simp), r19 (.n 1289) (by simp), r19 (.n 1290) (by simp),
      r19 (.n 1291) (by simp), r19 (.n 1292) (by simp)]
  have L19 := packed_message_leafA fs al cert k (w 1071) (w 1072) (w 1073) (w 1074) (w 1075) (ptrAt bm) xm hxm
    (R := fun i => (R i ∨ Own i) ∨ (st.D i ∨ False))
    (fun off hoff => ⟨bm + off, by rw [ptrAt, B1.Main.addr_ofK], (hcm off hoff).imp_right Or.inl⟩)
  rw [← hpm, ← hrets19] at L19
  rw [show [w 1071, w 1072, w 1073, w 1074, w 1075, ptrAt bm] = (argsOf vsC19s).map σ from hargs19.symm] at L19
  refine winsHyp_call_leaf (g := "packed_message__L144") rfl L19 (fun _ h => h)
    (fun rd hp => hPpm rd ⟨hp.1, hp.2.1⟩) ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => by simp) (fun i => by simp) (by simp)

end

end
end LeanVM.Guest.B1.VsC
