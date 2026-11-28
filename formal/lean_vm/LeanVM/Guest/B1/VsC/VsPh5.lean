/-
  LeanVM.Guest.B1.VsC.VsPh5

  `wC`'s windows `3 ..< 7`: the stack's size selector, the out-of-domain grind, the out-of-domain point and its
  opening message.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh4
public import LeanVM.Guest.B1.VsC.GrindRun

/-!
# `wC`'s windows `3 ..< 7`

`vsC_w3` (statements `432 ..< 484`): the size selector `.n 489 = g^(stackLog - 16)` and its range check below
`g^14`, the stream's word `10` absorbed by one permutation, the out-of-domain grind
`gcInlineOT 15 512 178 (.n 500) (.n 4)` (`vsC3_eq`, by the kernel; its atoms by `GrindRun.lean`'s `gcO_atoms`).
`vsC_w4` (statement `484`): the `squeeze_point_from__L{stackLog}` dispatch, a leaf. `vsC_w5` (statements
`485 ..< 487`): the stream's cursor `g^11` past its base. `vsC_w6` (statement `487`): `opening_message__L1_L1`, a
leaf. `vsPh5_wins` from numeric hypotheses on the oracle and the evaluation memory.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Statements `432 ..< 442`: the size selector and its range check, the stream's word `10` absorbed. -/
def vsC3p : List Atom :=
  [.const (.n 488) (word 8198521646651277316 0), .mul (.n 489) (.n 485) (.n 488), .const (.n 490) (word 16384 0),
    .rangeCheck (.n 489) (.n 491) (.n 492) (.n 493) (.n 490), .load (.n 494) (.n 55) 10, .copy (.n 495) (.n 494),
    .const (.n 496) (word 0 4), .const (.n 497) (word 0 0), .const (.n 498) (word 0 0),
    .keccak [.n 135, .n 136, .n 138, .n 139, .n 495, .n 496, .n 497, .n 498, .n 129, .n 130, .n 131, .n 132, .n 133]
      [.n 499, .n 500, .n 501, .n 502, .n 503, .n 504, .n 505, .n 506, .n 507, .n 508, .n 509, .n 510, .n 511]
      false false]

/-- Statements `442 ..< 484`: the out-of-domain grind, `grind_check(.n 500, g_squares·g^178, 15)` from `.n 512`. -/
def vsOodG : List Stmt := gcInlineOT 15 512 178 (.n 500) (.n 4)

/-- `squeeze_point_from__L16` … `__L30`. -/
def spfNames16 : List String := (List.range 15).map fun j => spfName (j + 16)

/-- Statement `484`: the out-of-domain point. -/
def vsC4s : Stmt :=
  .dispatch (.n 489) spfNames16 [.n 507, .n 508, .n 509, .n 510, .n 511, .n 499, .n 22]
    [.n 566, .n 567, .n 568, .n 569, .n 570]

/-- Statements `485 ..< 487`: the stream's cursor. -/
def vsC5 : List Atom := [.const (.n 571) (word 2048 0), .mul (.n 572) (.n 55) (.n 571)]

/-- Statement `487`: the opening message. -/
def vsC6s : Stmt :=
  .call "opening_message__L1_L1" [.n 566, .n 567, .n 568, .n 569, .n 570, .n 572, .n 23]
    [.n 573, .n 574, .n 575, .n 576, .n 577, .n 578, .n 579, .n 580]

set_option maxRecDepth 200000 in
theorem vsC3_eq : (vsC.drop 4).take 52 = vsC3p.map Stmt.atom ++ vsOodG := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC4_eq : (vsC.drop 56).take 1 = [vsC4s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC5_eq : (vsC.drop 57).take 2 = vsC5.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC6_eq : (vsC.drop 59).take 1 = [vsC6s] := stmtsEqb_sound (by decide +kernel)

theorem atomsOf_append' (xs ys : List Stmt) : atomsOf (xs ++ ys) = atomsOf xs ++ atomsOf ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> first | exact congrArg (List.cons _) ih | exact ih

theorem vsC_w3_eq : vsC_w3 = .run (vsC3p ++ atomsOf vsOodG) := by
  rw [vsC_w3, vsC3_eq, atomsOf_append', atomsOf_map]

theorem vsC_w4_eq : vsC_w4 = .call vsC4s := by rw [vsC_w4, headD_of_take_one vsC4_eq]

theorem vsC_w5_eq : vsC_w5 = .run vsC5 := by rw [vsC_w5, vsC5_eq, atomsOf_map]

theorem vsC_w6_eq : vsC_w6 = .call vsC6s := by rw [vsC_w6, headD_of_take_one vsC6_eq]

theorem spfNames16_get : ∀ j < 15, spfNames16[j]! = spfName (j + 16) := by decide +kernel

theorem spfNames16_length : spfNames16.length = 15 := rfl

set_option maxRecDepth 200000 in
/-- No store into the grind's values. -/
theorem vsOod_noStore : (storesOf 482 vsC).all (fun a => !loadInto 512 (512 + (gcLen 15 - 2)) a) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- The stream's word `10` is first read here. -/
theorem vsC3_fresh : (storesOf 482 vsC).contains (.load (.n 494) (.n 55) 10) = false := by decide +kernel

theorem vsC3p_pure : vsC3p.filter pureAsks = [.rangeCheck (.n 489) (.n 491) (.n 492) (.n 493) (.n 490)] := by
  decide +kernel

theorem vsC3p_mem : vsC3p.filter memAsks = [.load (.n 494) (.n 55) 10] := by decide +kernel

theorem winv16_mul : word 8198521646651277316 0 * gen ^ 16 = 1 := by
  rw [show gen ^ 16 = ofK (K.ofBits 65536) by
      rw [← word_two_pow (a := 16) (by decide)]; exact word_eOfNat _,
    show word 8198521646651277316 0 = ofK (K.ofBits 8198521646651277316) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 8198521646651277316 * K.ofBits 65536 = 1 by decide +kernel]
  exact map_one (algebraMap K E)

theorem pow_mul_winv16 {s : ℕ} (h : 16 ≤ s) : gen ^ s * word 8198521646651277316 0 = gen ^ (s - 16) := by
  conv_lhs => rw [show s = (s - 16) + 16 by omega, pow_add, mul_assoc, mul_comm (gen ^ 16), winv16_mul, mul_one]

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `3 ..< 7`' hypotheses**: the stack's log `16 ≤ sl ≤ 30` (`certify_stack`'s return `g^sl`),
the stream at `s` (its words `10 ..< 13` own), the exponent table's window section at `qt` (on the evaluation memory,
defined low, and from `Pre`; its words in `R`), the out-of-domain grind's honest windows and its proof of work, the
point's buffer at `b22` and the opening's at `b23` (own), the two leaves' returns the oracle's and their
preconditions from `Pre` and the words held; `K` past the two leaves' ends. -/
theorem vsPh5_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    {sl s qt b22 b23 : ℕ} {ws xs : List E} {nn : E}
    (hsl16 : 16 ≤ sl) (hsl30 : sl ≤ 30) (hw485 : w 485 = gen ^ sl)
    (h55 : vsVal rd0 w args (.n 55) = ptrAt s) (hws : 10 < ws.length) (r0 : ReadsAt rd0 (ptrAt s) ws)
    (hOs : ∀ rd, st.O rd → ReadsAt rd (ptrAt s) ws) (hOwn : ∀ j < 3, Own (s + 10 + j))
    (h4 : vsVal rd0 w args (.n 4) = ptrAt qt) (hl0 : LowDef k rd0) (rt : ExpWinTab rd0 (ptrAt qt))
    (hPt : ∀ rd, Pre rd → ExpWinTab rd (ptrAt qt)) (hRq : ∀ j < 2 ^ 11, R (qt + (j + 178)))
    (hwin : ∀ j ≤ gcW 15, w (512 + j) = gcWin 15 (vsVal rd0 w args (.n 500)) j)
    (hlow : ((vsVal rd0 w args (.n 500)).limb 0).lane.toNat % 2 ^ 15 = 0)
    (h22 : vsVal rd0 w args (.n 22) = ptrAt b22) (hO22 : ∀ j < sl, Own (b22 + j))
    (hspf : [w 566, w 567, w 568, w 569, w 570] =
      ((⟨[vsVal rd0 w args (.n 507), vsVal rd0 w args (.n 508), vsVal rd0 w args (.n 509),
        vsVal rd0 w args (.n 510), vsVal rd0 w args (.n 511)], []⟩ : Fs).squeezeN (sl - 1)).2.cap)
    (hP22 : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt b22) (vsVal rd0 w args (.n 499) ::
      ((⟨[vsVal rd0 w args (.n 507), vsVal rd0 w args (.n 508), vsVal rd0 w args (.n 509),
        vsVal rd0 w args (.n 510), vsVal rd0 w args (.n 511)], []⟩ : Fs).squeezeN (sl - 1)).1))
    (h23 : vsVal rd0 w args (.n 23) = ptrAt b23) (hO23 : Own (b23 + 0)) (hxs : xs.length = 1)
    (hom : [w 573, w 574, w 575, w 576, w 577, w 578, w 579, w 580] =
      omRets (w 566) (w 567) (w 568) (w 569) (w 570) (ptrAt (s + 11)) xs nn)
    (hP23 : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (s + 11)) (xs ++ [nn]) ∧ ReadsAt rd (ptrAt b23) xs)
    (hK : K ⟨st.a, leafEnd fs al (omName (1, 1)) (leafEnd fs al (spfName sl) st.kc), st.O, st.D,
      st.Qs ++ [PostQuiet, PostQuiet]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w3, vsC_w4, vsC_w5, vsC_w6] st K := by
  rw [vsC_w3_eq, vsC_w4_eq, vsC_w5_eq, vsC_w6_eq, WinsHyp]
  set σ := vsVal rd0 w args with hσ
  have hgC := vsVal_goodC (rd := rd0) (w := w) ha
  have memC3 : ∀ x ∈ vsC3p.map Stmt.atom ++ vsOodG, x ∈ vsC := fun x hx =>
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [vsC3_eq]; exact hx))
  have hg3 : ∀ a ∈ vsC3p, Good rd0 (storesOf 482 vsC) w σ a := fun a h =>
    hgC (.atom a) (memC3 _ (List.mem_append_left _ (List.mem_map_of_mem h)))
  have hgG : ∀ x ∈ vsOodG, GoodS rd0 (storesOf 482 vsC) w σ x := fun x h =>
    hgC x (memC3 _ (List.mem_append_right _ h))
  -- the size selector
  have e485 : σ (.n 485) = gen ^ sl := ((vsVal_retC (rd0 := rd0) (w := w) ha vsC2_eq) (.n 485) (by simp)).trans hw485
  have e488 : σ (.n 488) = word 8198521646651277316 0 := hg3 (.const (.n 488) _) (by simp [vsC3p])
  have e489 : σ (.n 489) = gen ^ (sl - 16) := by
    rw [good_mulF (hg3 (.mul (.n 489) (.n 485) (.n 488)) (by simp [vsC3p])) (by omega) (by omega), e485, e488,
      pow_mul_winv16 hsl16]
  have e490 : σ (.n 490) = gen ^ 14 := (hg3 (.const (.n 490) _) (by simp [vsC3p])).trans (wordG (j := 14) (by norm_num))
  -- the stream's word
  have e494 : σ (.n 494) = ws[10] :=
    good_loadAt (by intro h; have := vsC3_fresh; rw [List.contains_iff_mem.mpr h] at this; exact absurd this (by decide))
      (hg3 _ (by simp [vsC3p])) h55 hws r0
  -- the grind
  have wt : ∀ rd, ExpWinTab rd (ptrAt qt) → WinTabs rd (σ (.n 4) * gen ^ 178) := fun rd h n hn => by
    rw [h4, loadHolds_mul_gen_pow]; exact h n hn
  have hS : ∀ a ∈ storesOf 482 vsC, loadInto 512 (512 + (gcLen 15 - 2)) a = false := fun a h => by
    have := List.all_eq_true.mp vsOod_noStore a h
    simpa using this
  have gG := gcO_atoms (k := k) (b := 15) (o := 512) (off := 178) (wv := .n 500) (tabs := .n 4) hk (by decide)
    (by show 500 < 512; omega) (by show 4 < 512; omega) hgG hS hl0 (wt rd0 rt) hwin hlow
  have hh3 : heapHintAddrs σ ((vsC3p ++ atomsOf vsOodG).map Ev.atom) = [] := rfl
  refine ⟨RunHyp.of_asks rfl ?_ (fun A hA => by rw [hh3] at hA; simp at hA) ?_ ?_, ?_⟩
  · intro A hA
    obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA
    rcases List.mem_append.mp hm with hm | hm
    · have hm' : Atom.load d p off ∈ vsC3p.filter memAsks := List.mem_filter.mpr ⟨hm, rfl⟩
      rw [vsC3p_mem] at hm'
      simp only [List.mem_cons, List.not_mem_nil, or_false, Atom.load.injEq] at hm'
      obtain ⟨-, rfl, rfl⟩ := hm'
      exact ⟨s + 10, by rw [h55, ptrAt, B1.Main.addr_ofK], Or.inl (by simpa using hOwn 0 (by norm_num))⟩
    · obtain ⟨rfl, e, he, hp⟩ := (gG _ hm).2.2 d p off rfl
      refine ⟨qt + (e + 178), ?_, Or.inr (Or.inl (hRq e he))⟩
      rw [hp, h4, ptrAt_add, ptrAt, B1.Main.addr_ofK, Nat.add_assoc]
  · intro x hx
    obtain ⟨hx, hpa⟩ := List.mem_filter.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · have hx' : x ∈ vsC3p.filter pureAsks := List.mem_filter.mpr ⟨hx, hpa⟩
      rw [vsC3p_pure, List.mem_singleton] at hx'
      subst hx'
      exact rc_pureF (by omega) (by norm_num) (show sl - 16 ≤ 14 by omega)
        (hg3 _ (by simp [vsC3p])) (by omega) e489 e490
    · exact (gG x hx).1
  · intro rd _ hp ho x hx
    obtain ⟨hx, hma⟩ := List.mem_filter.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · have hx' : x ∈ vsC3p.filter memAsks := List.mem_filter.mpr ⟨hx, hma⟩
      rw [vsC3p_mem, List.mem_singleton] at hx'
      subst hx'
      show LoadHolds rd (σ (.n 55)) 10 (σ (.n 494))
      rw [h55, e494]; exact hOs rd ho 10 hws
    · exact (gG x hx).2.1 rd (wt rd (hPt rd hp))
  rw [show allocs σ ((vsC3p ++ atomsOf vsOodG).map Ev.atom) = [] from rfl, List.sum_nil, Nat.add_zero]
  -- the out-of-domain point
  have r4 : ∀ v ∈ [V.n 566, .n 567, .n 568, .n 569, .n 570], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC4_eq
  have hrets4 : (retsOf vsC4s).map σ = [w 566, w 567, w 568, w 569, w 570] := by
    show [σ (.n 566), σ (.n 567), σ (.n 568), σ (.n 569), σ (.n 570)] = _
    rw [r4 (.n 566) (by simp), r4 (.n 567) (by simp), r4 (.n 568) (by simp),
      r4 (.n 569) (by simp), r4 (.n 570) (by simp)]
  have hn : sl ∈ spfDeployed := by
    simp only [spfDeployed, List.mem_map, List.mem_range]; exact ⟨sl - 6, by omega, by omega⟩
  have L4 : LeafAtA fs al cert k (spfName sl) ((argsOf vsC4s).map σ) ((retsOf vsC4s).map σ)
      (fun i => (R i ∨ Own i) ∨ st.D i) (fun _ => True)
      (fun rd ↦ ReadsAt rd (σ (.n 22)) (σ (.n 499) ::
        ((⟨[σ (.n 507), σ (.n 508), σ (.n 509), σ (.n 510), σ (.n 511)], []⟩ : Fs).squeezeN (sl - 1)).1))
      PostQuiet := by
    rw [hrets4, hspf]
    exact squeeze_point_from_leafA fs al cert k hn _ _ _ _ _ _ _ fun off hoff =>
      ⟨b22 + off, by rw [h22, ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr (hO22 off hoff))⟩
  refine winsHyp_call_leaf (g := spfName sl)
    ⟨sl - 16, by rw [spfNames16_length]; omega, by rw [e489, Value.gen_pow_eq_ofK],
      by rw [spfNames16_get _ (by omega), Nat.sub_add_cancel hsl16]⟩ L4 (fun _ h => h)
    (fun rd hp => by rw [h22]; exact hP22 rd hp) ?_
  -- the stream's cursor
  have hg5 : ∀ a ∈ vsC5, Good rd0 (storesOf 482 vsC) w σ a := vsC_run_good (rd0 := rd0) (w := w) ha vsC5_eq
  have e572 : σ (.n 572) = ptrAt (s + 11) := by
    rw [good_mulF (hg5 (.mul (.n 572) (.n 55) (.n 571)) (by simp [vsC5])) (by omega) (by omega), h55,
      show σ (.n 571) = word 2048 0 from hg5 (.const (.n 571) _) (by simp [vsC5]), show word 2048 0 = gen ^ 11 from wordG (j := 11) (by norm_num),
      ptrAt_add]
  rw [WinsHyp]
  refine ⟨RunHyp.of_asks rfl (fun A hA => by simp [loadAddrs, vsC5, Ev.loadAddr?] at hA)
    (fun A hA => by rw [show heapHintAddrs σ (vsC5.map Ev.atom) = [] from rfl] at hA; simp at hA)
    (fun x hx => by rw [show vsC5.filter pureAsks = [] by decide +kernel] at hx; simp at hx)
    (fun rd _ _ _ x hx => by rw [show vsC5.filter memAsks = [] by decide +kernel] at hx; simp at hx), ?_⟩
  rw [show allocs σ (vsC5.map Ev.atom) = [] from rfl, List.sum_nil, Nat.add_zero]
  -- the opening message
  have r6 : ∀ v ∈ [V.n 573, .n 574, .n 575, .n 576, .n 577, .n 578, .n 579, .n 580], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC6_eq
  have hargs6 : (argsOf vsC6s).map σ = [w 566, w 567, w 568, w 569, w 570, ptrAt (s + 11), ptrAt b23] := by
    show [σ (.n 566), σ (.n 567), σ (.n 568), σ (.n 569), σ (.n 570), σ (.n 572), σ (.n 23)] = _
    rw [r4 (.n 566) (by simp), r4 (.n 567) (by simp), r4 (.n 568) (by simp),
      r4 (.n 569) (by simp), r4 (.n 570) (by simp), e572, h23]
  have hrets6 : (retsOf vsC6s).map σ = [w 573, w 574, w 575, w 576, w 577, w 578, w 579, w 580] := by
    show [σ (.n 573), σ (.n 574), σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579), σ (.n 580)] = _
    rw [r6 (.n 573) (by simp), r6 (.n 574) (by simp), r6 (.n 575) (by simp),
      r6 (.n 576) (by simp), r6 (.n 577) (by simp), r6 (.n 578) (by simp),
      r6 (.n 579) (by simp), r6 (.n 580) (by simp)]
  have L6 : LeafAtA fs al cert k (omName (1, 1)) ((argsOf vsC6s).map σ) ((retsOf vsC6s).map σ)
      (fun i => (R i ∨ Own i) ∨ (st.D i ∨ False)) (fun _ => True)
      (fun rd ↦ ReadsAt rd (ptrAt (s + 11)) (xs ++ [nn]) ∧ ReadsAt rd (ptrAt b23) xs) PostQuiet := by
    rw [hargs6, hrets6, hom]
    refine opening_message_L1_leafA fs al cert k _ _ _ _ _ _ _ nn xs hxs (fun off hoff => ?_) (fun off hoff => ?_)
    · refine ⟨s + 10 + (off + 1), by rw [ptrAt, B1.Main.addr_ofK, show s + 11 + off = s + 10 + (off + 1) by omega], Or.inl (Or.inr (hOwn _ (by omega)))⟩
    · obtain rfl : off = 0 := by omega
      exact ⟨b23 + 0, by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inr hO23)⟩
  refine winsHyp_call_leaf (g := omName (1, 1)) rfl L6 (fun _ h => h)
    (fun rd hp => hP23 rd ⟨hp.1, hp.2.1⟩) ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => by simp) (fun i => by simp) (by simp)

end

end
end LeanVM.Guest.B1.VsC
