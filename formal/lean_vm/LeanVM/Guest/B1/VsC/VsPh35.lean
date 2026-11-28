/-
  LeanVM.Guest.B1.VsC.VsPh35

  `wC`'s windows `35 ..< 38`: `verify_keccak`, the ring switch's grind and buffers, `ring_switch_target`.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh10
public import LeanVM.Guest.B1.VsC.RingRun

/-!
# `wC`'s windows `35 ..< 38`

`vsC_w35` (statement `2928`): `verify_keccak`, at a given end. `vsC_w36` (statements `2929 ..< 3913`, one run cut into
parts, `vsC36_eq` by the kernel): the stream's word at `verify_keccak`'s cursor absorbed (`vsC36a`), the ring's grind
`gcInlineOT 13 2943 178 (.n 2931) (.n 4)` (`GrindRun.lean`'s `gcO_atoms`), two squeezes (`vsC36c`), then three
`HeapBuf`s at the cursor: the map challenges (`.n 3039`, sixteen words), `ring_coefficients(f, g)` (`.n 3040`,
sixty-four), the merged slices (`.n 3553`, sixty-four), each filled by straight code (`RingRun.lean`'s templates).
`vsC_w37` (statement `3913`): `ring_switch_target` on the slices and the challenges, at a given end. `vsPh35_wins`
from numeric hypotheses.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Statements `2922 ..< 2928`: `verify_keccak`'s cursor, its outputs' slice and its tables' window section. -/
def vsC34t : List Atom :=
  [.const (.n 2909) (word 21299200 0), .mul (.n 2910) (.n 1076) (.n 2909),
    .const (.n 2911) (word 36028797018963968 0), .mul (.n 2912) (.n 1076) (.n 2911),
    .const (.n 2913) (word 365917469723852800 0), .mul (.n 2914) (.n 4) (.n 2913)]

/-- Statement `2928`: `verify_keccak`. -/
def vsC35s : Stmt :=
  .call "verify_keccak" [.n 1288, .n 1289, .n 1290, .n 1291, .n 1292, .n 2910, .n 120, .n 15, .n 2912, .n 20, .n 21,
    .n 2914] [.n 2915, .n 2916, .n 2917, .n 2918, .n 2919, .n 2920, .n 2921]

/-- Statement `3913`: `ring_switch_target`. -/
def vsC37s : Stmt := .call "ring_switch_target" [.n 3553, .n 3039] [.n 3810]

/-- Statements `2938 ..< 2980`: the ring's grind. -/
abbrev vsRingG : List Stmt := gcInlineOT 13 2943 178 (.n 2931) (.n 4)

/-- Statements `2929 ..< 2938`: the stream's word absorbed. -/
noncomputable abbrev vsC36a : List Atom := atomsOf ((vsC.drop 2501).take 9)

/-- Statements `2980 ..< 2998`: two squeezes. -/
noncomputable abbrev vsC36c : List Atom := atomsOf ((vsC.drop 2552).take 18)

/-- Statements `2998 ..< 3913`: the three buffers. -/
def vsC36t : List Atom :=
  .hint (.alloc (.n 3039) 16) :: (vsMcS ++ (.hint (.alloc (.n 3040) 64) :: (vsRc ++ (.hint (.alloc (.n 3553) 64) :: vsRs))))

set_option maxRecDepth 200000 in
theorem vsC34_eq : (vsC.drop 2494).take 6 = vsC34t.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC35_eq : (vsC.drop 2500).take 1 = [vsC35s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC37_eq : (vsC.drop 3485).take 1 = [vsC37s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC36_eq : (vsC.drop 2501).take 984 =
    (vsC.drop 2501).take 9 ++ (vsRingG ++ ((vsC.drop 2552).take 18 ++ vsC36t.map Stmt.atom)) :=
  stmtsEqb_sound (by decide +kernel)

theorem vsC_w35_eq : vsC_w35 = .call vsC35s := by rw [vsC_w35, headD_of_take_one vsC35_eq]

theorem vsC_w37_eq : vsC_w37 = .call vsC37s := by rw [vsC_w37, headD_of_take_one vsC37_eq]

theorem as36_eq : atomsOf ((vsC.drop 2501).take 984) = vsC36a ++ (atomsOf vsRingG ++ (vsC36c ++ vsC36t)) := by
  rw [vsC36_eq, atomsOf_append', atomsOf_append', atomsOf_append', atomsOf_map]

set_option maxRecDepth 200000 in
/-- The first part: no allocation, no heap hint, no ask but its one load, a fresh read of the stream. -/
theorem vsC36a_shape : vsC36a.all noAllocB = true ∧ vsC36a.all noHeapB = true ∧ vsC36a.filter pureAsks = [] ∧
    vsC36a.filter memAsks = [.load (.n 2927) (.n 2920) 0] ∧ vsSL.contains (.load (.n 2927) (.n 2920) 0) = false := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- The squeezes: no allocation, no heap hint, no ask, no load. -/
theorem vsC36c_shape : vsC36c.all noAllocB = true ∧ vsC36c.all noHeapB = true ∧ vsC36c.filter pureAsks = [] ∧
    vsC36c.filter memAsks = [] := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- The grind: no allocation, no heap hint; no store into its values. -/
theorem vsRingG_shape : (atomsOf vsRingG).all noAllocB = true ∧ (atomsOf vsRingG).all noHeapB = true ∧
    vsSL.all (fun a => !loadInto 2943 (2943 + (gcLen 13 - 2)) a) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- The buffers' parts: read through known buffers, their fresh reads no stores. -/
theorem vsC36t_bufs : bufsOk [(3039, 16)] vsMcS vsSL vsMcS = true ∧ bufsOk [(3040, 64)] rcStores vsSL vsRc = true ∧
    bufsOk [(3553, 64), (21, 64), (1076, 144)] rsStores vsSL vsRs = true ∧ rsFreshB vsSL = true ∧
    vsMcS.filter pureAsks = [] ∧ vsRc.filter pureAsks = [] ∧ vsRs.filter pureAsks = [] := by
  decide +kernel

theorem mcRc_length (σ : Val) : (mcRc σ).length = 64 := rfl

theorem noAlloc_of_bufsOk {sp : List (ℕ × ℕ)} {sts S as : List Atom} (h : bufsOk sp sts S as = true) :
    as.all noAllocB = true :=
  List.all_eq_true.mpr fun x hx => by
    have := List.all_eq_true.mp h x hx
    simp only [Bool.and_eq_true] at this
    exact this.1.1.2

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `35 ..< 38`' hypotheses**, from the state `st` the windows before leave: `verify_keccak`'s
arguments (`.n 120 = g^τ`, the buffers `.n 15`, `.n 20`, `.n 21`, the tables at `qt`) and its `CallAtA` at a given end
`ev`, its returns the oracle's; the stream's word `nz` at its cursor `w 2920 = ptrAt cs` (own); the exponent tables'
window section (as `vsPh5_wins`), the ring grind's honest windows and proof of work on `.n 2931`; the three `HeapBuf`s at
the cursor `st.a` (`144` own words), holding the map challenges `mcW σ`, `mcRc σ = ring_coefficients(f, g)` and the
merged slices `rsW xs21 xsm (σ 3026)` on the evaluation memory and on every memory with `Pre` and the words held; the
slices buffer `.n 21` at `b21` (`xs21`, own) and the packed message `w 1076 = ptrAt bm` (`xsm`, in the region), held
alike; `ring_switch_target`'s `CallAtA` on the merged slices and the challenges at a given end `er`, its return the
oracle's; `K` past both, the cursor `144` words on. -/
theorem vsPh35_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    {qt b15 b20 b21 bm cs τ : ℕ} {nz : E} {xs21 xsm : List E}
    (h120 : vsVal rd0 w args (.n 120) = gen ^ τ) (h15 : vsVal rd0 w args (.n 15) = ptrAt b15)
    (h20 : vsVal rd0 w args (.n 20) = ptrAt b20) (h21 : vsVal rd0 w args (.n 21) = ptrAt b21)
    (h4 : vsVal rd0 w args (.n 4) = ptrAt qt)
    {Rv Dv : ℕ → Prop} {Ov Pv : Reader → Prop} {Qv : Reader → Tree → Prop} {Bv ev : ℕ}
    (hv : CallAtA fs al cert k "verify_keccak"
      [w 1288, w 1289, w 1290, w 1291, w 1292, w 1076 * word 21299200 0, gen ^ τ, ptrAt b15,
        w 1076 * word 36028797018963968 0, ptrAt b20, ptrAt b21, ptrAt qt * word 365917469723852800 0]
      [w 2915, w 2916, w 2917, w 2918, w 2919, w 2920, w 2921] Rv Dv Ov Pv Qv Bv
      (allocBase (al "verify_keccak") st.kc) (allocBase (al "verify_keccak") st.kc + Bv) ev)
    (hRv : ∀ i, Rv i → (R i ∨ Own i) ∨ st.D i) (hPv : ∀ rd, Pre rd ∧ st.O rd → Pv rd)
    (hw2920 : w 2920 = ptrAt cs) (r0cs : ReadsAt rd0 (ptrAt cs) [nz])
    (hOcs : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt cs) [nz]) (hOwncs : Own cs)
    (hl0 : LowDef k rd0) (rt : ExpWinTab rd0 (ptrAt qt)) (hPt : ∀ rd, Pre rd → ExpWinTab rd (ptrAt qt))
    (hRq : ∀ j < 2 ^ 11, R (qt + (j + 178)))
    (hwin : ∀ j ≤ gcW 13, w (2943 + j) = gcWin 13 (vsVal rd0 w args (.n 2931)) j)
    (hlow : ((vsVal rd0 w args (.n 2931)).limb 0).lane.toNat % 2 ^ 13 = 0)
    (hw3039 : w 3039 = ptrAt st.a) (hw3040 : w 3040 = ptrAt (st.a + 16)) (hw3553 : w 3553 = ptrAt (st.a + 80))
    (hOwn : ∀ j < 144, Own (st.a + j))
    (r39 : ReadsAt rd0 (ptrAt st.a) (mcW (vsVal rd0 w args)))
    (hO39 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt st.a) (mcW (vsVal rd0 w args)))
    (r40 : ReadsAt rd0 (ptrAt (st.a + 16)) (mcRc (vsVal rd0 w args)))
    (hO40 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt (st.a + 16)) (mcRc (vsVal rd0 w args)))
    (hl21 : 64 ≤ xs21.length) (r21 : ReadsAt rd0 (ptrAt b21) xs21)
    (hO21 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b21) xs21) (hOwn21 : ∀ j < 64, Own (b21 + j))
    (hwm : w 1076 = ptrAt bm) (hlm : 144 ≤ xsm.length) (rm : ReadsAt rd0 (ptrAt bm) xsm)
    (hOm : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt bm) xsm)
    (hcm : ∀ j < 144, (R (bm + j) ∨ Own (bm + j)) ∨ st.D (bm + j))
    (r53 : ReadsAt rd0 (ptrAt (st.a + 80)) (rsW xs21 xsm (vsVal rd0 w args (.n 3026))))
    (hO53 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt (st.a + 80)) (rsW xs21 xsm (vsVal rd0 w args (.n 3026))))
    {Rr Dr : ℕ → Prop} {Ort Pr : Reader → Prop} {Qr : Reader → Tree → Prop} {Br er : ℕ}
    (hr : CallAtA fs al cert k "ring_switch_target" [ptrAt (st.a + 80), ptrAt st.a] [w 3810] Rr Dr Ort Pr Qr Br
      (allocBase (al "ring_switch_target") ev) (allocBase (al "ring_switch_target") ev + Br) er)
    (hRr : ∀ i, Rr i → (R i ∨ Own i) ∨ (st.D i ∨ Dv i)) (hPr : ∀ rd, Pre rd ∧ (st.O rd ∧ Ov rd) → Pr rd)
    (hK : K ⟨st.a + 144, er, fun rd => (st.O rd ∧ Ov rd) ∧ Ort rd, fun i => (st.D i ∨ Dv i) ∨ Dr i,
      st.Qs ++ [Qv, Qr]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w35, vsC_w36, vsC_w37] st K := by
  rw [vsC_w35_eq, vsC_w36, vsC_w37_eq]
  set σ := vsVal rd0 w args with hσ
  -- `verify_keccak`
  have r19 : ∀ v ∈ [V.n 1287, .n 1288, .n 1289, .n 1290, .n 1291, .n 1292], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC19_eq
  have r16 : ∀ v ∈ [V.n 1071, .n 1072, .n 1073, .n 1074, .n 1075, .n 1076, .n 1077], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC16_eq
  have r35 : ∀ v ∈ [V.n 2915, .n 2916, .n 2917, .n 2918, .n 2919, .n 2920, .n 2921], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC35_eq
  have hg34 : ∀ a ∈ vsC34t, Good rd0 (storesOf 482 vsC) w σ a := vsC_run_good (rd0 := rd0) (w := w) ha vsC34_eq
  have e1076 : σ (.n 1076) = ptrAt bm := (r16 (.n 1076) (by simp)).trans hwm
  have e2910 : σ (.n 2910) = w 1076 * word 21299200 0 := by
    rw [good_mulF (hg34 (.mul (.n 2910) (.n 1076) (.n 2909)) (by simp [vsC34t])) (by omega) (by omega),
      r16 (.n 1076) (by simp),
      show σ (.n 2909) = word 21299200 0 from hg34 (.const (.n 2909) _) (by simp [vsC34t])]
  have e2912 : σ (.n 2912) = w 1076 * word 36028797018963968 0 := by
    rw [good_mulF (hg34 (.mul (.n 2912) (.n 1076) (.n 2911)) (by simp [vsC34t])) (by omega) (by omega),
      r16 (.n 1076) (by simp),
      show σ (.n 2911) = word 36028797018963968 0 from hg34 (.const (.n 2911) _) (by simp [vsC34t])]
  have e2914 : σ (.n 2914) = ptrAt qt * word 365917469723852800 0 := by
    rw [good_mulF (hg34 (.mul (.n 2914) (.n 4) (.n 2913)) (by simp [vsC34t])) (by omega) (by omega), h4,
      show σ (.n 2913) = word 365917469723852800 0 from hg34 (.const (.n 2913) _) (by simp [vsC34t])]
  have hargs35 : (argsOf vsC35s).map σ = [w 1288, w 1289, w 1290, w 1291, w 1292, w 1076 * word 21299200 0,
      gen ^ τ, ptrAt b15, w 1076 * word 36028797018963968 0, ptrAt b20, ptrAt b21,
      ptrAt qt * word 365917469723852800 0] := by
    show [σ (.n 1288), σ (.n 1289), σ (.n 1290), σ (.n 1291), σ (.n 1292), σ (.n 2910), σ (.n 120), σ (.n 15),
      σ (.n 2912), σ (.n 20), σ (.n 21), σ (.n 2914)] = _
    rw [r19 (.n 1288) (by simp), r19 (.n 1289) (by simp), r19 (.n 1290) (by simp), r19 (.n 1291) (by simp),
      r19 (.n 1292) (by simp), e2910, h120, h15, e2912, h20, h21, e2914]
  have hrets35 : (retsOf vsC35s).map σ = [w 2915, w 2916, w 2917, w 2918, w 2919, w 2920, w 2921] := by
    show [σ (.n 2915), σ (.n 2916), σ (.n 2917), σ (.n 2918), σ (.n 2919), σ (.n 2920), σ (.n 2921)] = _
    rw [r35 (.n 2915) (by simp), r35 (.n 2916) (by simp), r35 (.n 2917) (by simp), r35 (.n 2918) (by simp),
      r35 (.n 2919) (by simp), r35 (.n 2920) (by simp), r35 (.n 2921) (by simp)]
  rw [← hargs35, ← hrets35] at hv
  refine winsHyp_call_at (g := "verify_keccak") rfl hv hRv hPv ?_
  -- the run
  rw [WinsHyp, as36_eq]
  have hg36 : ∀ x ∈ vsC36a ++ (atomsOf vsRingG ++ (vsC36c ++ vsC36t)), Good rd0 vsSL w σ x := by
    rw [← as36_eq]; exact vsC_atoms_good ha 2501 984
  have memT : ∀ x ∈ vsC36t, x ∈ vsC36a ++ (atomsOf vsRingG ++ (vsC36c ++ vsC36t)) := fun x hx =>
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx))
  -- the stream's word
  obtain ⟨a1, a2, a3, a4, a5⟩ := vsC36a_shape
  have e2920 : σ (.n 2920) = ptrAt cs := (r35 (.n 2920) (by simp)).trans hw2920
  have hmA : Atom.load (.n 2927) (.n 2920) 0 ∈ vsC36a.filter memAsks := by rw [a4]; exact List.mem_singleton_self _
  have mA : Atom.load (.n 2927) (.n 2920) 0 ∈ vsC36a := (List.mem_filter.mp hmA).1
  have e2927 : σ (.n 2927) = nz :=
    good_loadAt (fun h => by have := List.contains_iff_mem.mpr h; rw [a5] at this; exact absurd this (by decide))
      (hg36 _ (List.mem_append_left _ mA)) e2920 (by simp) r0cs
  have hA : RunHyp k σ w st.a Own R (fun i => st.D i ∨ Dv i) Pre (fun rd => st.O rd ∧ Ov rd) vsC36a :=
    RunHyp.of_noAlloc a1 a2
      (fun d p off hm => by
        have h := List.mem_filter.mpr (⟨hm, rfl⟩ : Atom.load d p off ∈ vsC36a ∧ memAsks (.load d p off) = true)
        rw [a4, List.mem_singleton, Atom.load.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨cs + 0, by rw [e2920, ptrAt, B1.Main.addr_ofK], Or.inl (by simpa using hOwncs)⟩)
      (fun x hx => by rw [a3] at hx; simp at hx)
      (fun rd _ hp ho x hx => by
        rw [a4, List.mem_singleton] at hx
        subst hx
        show LoadHolds rd (σ (.n 2920)) 0 (σ (.n 2927))
        rw [e2920, e2927]
        exact hOcs rd hp ho.1 0 (by simp))
  -- the ring's grind
  obtain ⟨g1, g2, g3⟩ := vsRingG_shape
  have hgG : ∀ s ∈ vsRingG, GoodS rd0 vsSL w σ s := fun s hs => by
    have := vsVal_goodC (rd := rd0) (w := w) ha s (List.mem_of_mem_drop (List.mem_of_mem_take
      (by rw [vsC36_eq]; exact List.mem_append_right _ (List.mem_append_left _ hs))))
    rwa [vsSL_eq] at this
  have wt : ∀ rd, ExpWinTab rd (ptrAt qt) → WinTabs rd (σ (.n 4) * gen ^ 178) := fun rd h n hn => by
    rw [h4, loadHolds_mul_gen_pow]; exact h n hn
  have hS : ∀ a ∈ vsSL, loadInto 2943 (2943 + (gcLen 13 - 2)) a = false := fun a h => by
    simpa using List.all_eq_true.mp g3 a h
  have gG := gcO_atoms (k := k) (b := 13) (o := 2943) (off := 178) (wv := .n 2931) (tabs := .n 4) hk (by decide)
    (by show 2931 < 2943; omega) (by show 4 < 2943; omega) hgG hS hl0 (wt rd0 rt) hwin hlow
  have hG : RunHyp k σ w st.a Own R (fun i => st.D i ∨ Dv i) Pre (fun rd => st.O rd ∧ Ov rd) (atomsOf vsRingG) :=
    RunHyp.of_noAlloc g1 g2
      (fun d p off hm => by
        obtain ⟨rfl, e, he, hp⟩ := (gG _ hm).2.2 d p off rfl
        exact ⟨qt + (e + 178), by rw [hp, h4, ptrAt_add, ptrAt, B1.Main.addr_ofK, Nat.add_assoc],
          Or.inr (Or.inl (hRq e he))⟩)
      (fun x hx => (gG x (List.mem_filter.mp hx).1).1)
      (fun rd _ hp _ x hx => (gG x (List.mem_filter.mp hx).1).2.1 rd (wt rd (hPt rd hp)))
  -- the squeezes
  obtain ⟨c1, c2, c3, c4⟩ := vsC36c_shape
  have hC : RunHyp k σ w st.a Own R (fun i => st.D i ∨ Dv i) Pre (fun rd => st.O rd ∧ Ov rd) vsC36c :=
    RunHyp.of_noAlloc c1 c2
      (fun d p off hm => by
        have h := List.mem_filter.mpr (⟨hm, rfl⟩ : Atom.load d p off ∈ vsC36c ∧ memAsks (.load d p off) = true)
        rw [c4] at h; simp at h)
      (fun x hx => by rw [c3] at hx; simp at hx)
      (fun rd _ _ _ x hx => by rw [c4] at hx; simp at hx)
  -- the three buffers
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := vsC36t_bufs
  have mMc : ∀ x ∈ vsMcS, x ∈ vsC36t := fun x hx => List.mem_cons_of_mem _ (List.mem_append_left _ hx)
  have mRc : ∀ x ∈ vsRc, x ∈ vsC36t := fun x hx =>
    List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
  have mRs : ∀ x ∈ vsRs, x ∈ vsC36t := fun x hx =>
    List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_cons_of_mem _ hx))))
  have e3039 : σ (.n 3039) = ptrAt st.a := (hg36 _ (memT _ List.mem_cons_self)).trans hw3039
  have e3040 : σ (.n 3040) = ptrAt (st.a + 16) :=
    (hg36 _ (memT _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))).trans hw3040
  have e3553 : σ (.n 3553) = ptrAt (st.a + 80) :=
    (hg36 _ (memT _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self)))))).trans hw3553
  have hMc : RunHyp k σ w (st.a + 16) Own R (fun i => st.D i ∨ Dv i) Pre (fun rd => st.O rd ∧ Ov rd) vsMcS :=
    runHyp_bufs t1 (fun x hx => hg36 x (memT x (mMc x hx))) (fun _ => st.a) (fun _ => mcW σ)
      (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact e3039)
      (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact (mcW_length σ).symm.le)
      (fun q _ => r39)
      (fun q hq j hj => by
        rw [List.mem_singleton] at hq; subst hq
        exact Or.inl (hOwn j (by have : j < 16 := hj; omega)))
      (fun rd hp ho q _ => hO39 rd hp ho.1) (mcStores_mem e3039 r39)
      (fun x hx => by rw [t5] at hx; simp at hx)
  have hRc : RunHyp k σ w (st.a + 80) Own R (fun i => st.D i ∨ Dv i) Pre (fun rd => st.O rd ∧ Ov rd) vsRc :=
    runHyp_bufs t2 (fun x hx => hg36 x (memT x (mRc x hx))) (fun _ => st.a + 16) (fun _ => mcRc σ)
      (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact e3040)
      (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact (mcRc_length σ).symm.le)
      (fun q _ => r40)
      (fun q hq j hj => by
        rw [List.mem_singleton] at hq; subst hq
        show Own (st.a + 16 + j) ∨ _
        rw [Nat.add_assoc]
        exact Or.inl (hOwn _ (by have : j < 64 := hj; omega)))
      (fun rd hp ho q _ => hO40 rd hp ho.1)
      (rcStores_mem (fun x hx => hg36 x (memT x (mRc x hx))) e3040 r40)
      (fun x hx => by rw [t6] at hx; simp at hx)
  let bs : ℕ → ℕ := fun v => if v = 21 then b21 else if v = 1076 then bm else st.a + 80
  let xs : ℕ → List E := fun v => if v = 21 then xs21 else if v = 1076 then xsm else rsW xs21 xsm (σ (.n 3026))
  have hRs : RunHyp k σ w (st.a + 144) Own R (fun i => st.D i ∨ Dv i) Pre (fun rd => st.O rd ∧ Ov rd) vsRs :=
    runHyp_bufs t3 (fun x hx => hg36 x (memT x (mRs x hx))) bs xs
      (fun q hq => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact e3553
        · exact h21
        · exact e1076)
      (fun q hq => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact (rsW_length _ _ _).symm.le
        · exact hl21
        · exact hlm)
      (fun q hq => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact r53
        · exact r21
        · exact rm)
      (fun q hq j hj => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · show Own (st.a + 80 + j) ∨ _
          rw [Nat.add_assoc]
          exact Or.inl (hOwn _ (by have : j < 64 := hj; omega))
        · exact Or.inl (hOwn21 j hj)
        · show Own (bm + j) ∨ R (bm + j) ∨ (st.D (bm + j) ∨ Dv (bm + j))
          rcases hcm j hj with (h | h) | h
          exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inl h))])
      (fun rd hp ho q hq => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact hO53 rd hp ho.1
        · exact hO21 rd hp ho.1
        · exact hOm rd hp ho.1)
      (rsStores_mem (fun x hx => hg36 x (memT x (mRs x hx))) t4 h21 hl21 r21 e1076 hlm rm e3553 r53)
      (fun x hx => by rw [t7] at hx; simp at hx)
  have hT : RunHyp k σ w st.a Own R (fun i => st.D i ∨ Dv i) Pre (fun rd => st.O rd ∧ Ov rd) vsC36t :=
    runHyp_alloc_cons (d := .n 3039) (n := 16) hw3039 rfl (runHyp_append0 (noAlloc_of_bufsOk t1) hMc
      (runHyp_alloc_cons (d := .n 3040) (n := 64) hw3040 (by omega) (runHyp_append0 (noAlloc_of_bufsOk t2) hRc
        (runHyp_alloc_cons (d := .n 3553) (n := 64) hw3553 (by omega) hRs))))
  have hsum : (allocs σ ((vsC36a ++ (atomsOf vsRingG ++ (vsC36c ++ vsC36t))).map Ev.atom)).sum = 144 := by
    rw [allocs_append0 a1, allocs_append0 g1, allocs_append0 c1, vsC36t, allocs_alloc_cons,
      allocs_append0 (noAlloc_of_bufsOk t1), allocs_alloc_cons, allocs_append0 (noAlloc_of_bufsOk t2),
      allocs_alloc_cons, (noAlloc_fields (σ := σ) (noAlloc_of_bufsOk t3)).2]
    rfl
  refine ⟨runHyp_append0 a1 hA (runHyp_append0 g1 hG (runHyp_append0 c1 hC hT)), ?_⟩
  rw [hsum]
  -- `ring_switch_target`
  have r37 : ∀ v ∈ [V.n 3810], σ v = w v.idx := vsVal_retC (rd0 := rd0) (w := w) ha vsC37_eq
  have hargs37 : (argsOf vsC37s).map σ = [ptrAt (st.a + 80), ptrAt st.a] := by
    show [σ (.n 3553), σ (.n 3039)] = _
    rw [e3553, e3039]
  have hrets37 : (retsOf vsC37s).map σ = [w 3810] := by
    show [σ (.n 3810)] = _
    rw [r37 (.n 3810) (by simp)]
  rw [← hargs37, ← hrets37] at hr
  refine winsHyp_call_at (g := "ring_switch_target") rfl hr hRr hPr ?_
  rw [WinsHyp]
  exact st_congr hK rfl (fun rd => Iff.rfl) (fun i => Iff.rfl) (by simp)

end
end
end LeanVM.Guest.B1.VsC
