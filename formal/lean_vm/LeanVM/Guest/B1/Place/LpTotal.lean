/-
  LeanVM.Guest.B1.Place.LpTotal

  Every valid tree of a `level_positions` specialization takes at least its placed words, and one
  exists, on a memory built for it: so a words bound of its trees bounds its placed words.
-/

module

public import LeanVM.Guest.B1.Place.LpBodyAt

/-!
# `level_positions`' words, unplaced

`lpLoop_total_ge`: a valid tree of the loop entered at `g^j` of `g^sq` takes at least
`lpTot … sq j` words: its frame, its decoder's frame and its tail's (entered when `j + 1 < sq`,
the guard `g^(j+1) + g^sq` not zero, else a phantom). `lp_total_ge`: a valid tree of the
function with its `HeapBuf`s its path's takes at least `lpN` words: its frame, the squeeze run of
`(sq + 1)·5` words and the loop, entered behind `1 + g^sq ≠ 0`.

`lp_tree`: a valid tree exists, on a memory defined at small addresses (`lpRd`): the window
table at `0 .. 127`, then the positions, the window pointers (into one run nowhere defined, which
its `frameAddr` then reads nothing of) and the squeeze run; `lp_complete` relates it, its decoders
by `qw_complete`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

theorem lp_atom_mem {σ : Val} {pre : List Stmt} {a : Atom} (h : Stmt.atom a ∈ pre) :
    Ev.atom a ∈ pre.flatMap (Main.slEvs σ) :=
  List.mem_flatMap.mpr ⟨.atom a, h, by simp [Main.slEvs]⟩

/-- **A valid node of `level_positions`' loop from `g^j` of `g^sq`**: its callees are the decoder and
the tail, the tail valid from `g^(j+1)` when the guard is not zero. -/
theorem lpLoop_valid {d cd : ℕ} {loop : String} {fn : Fn}
    (hf : coreProgram.find? loop = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = lpLoopBody d cd loop) {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree}
    {args rets : List E} {j sq : ℕ} (hv : (Memory.Tree.node loop σ bufs kids).Valid coreProgram rd args rets)
    (hargs : args.take 2 = [gen ^ j, gen ^ sq]) :
    ∃ k1 k2, kids = [k1, k2] ∧ k1.name = qwDecName d cd ∧ k2.name = loop ∧
      (gen ^ j * gen + gen ^ sq ≠ 0 → ∃ args', k2.Valid coreProgram rd args' [] ∧
        args'.take 2 = [gen ^ (j + 1), gen ^ sq]) := by
  simp only [Tree.Valid] at hv
  obtain ⟨fn', hf', hp', es, vs, hw', -, hes, hkv⟩ := hv
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  have hst := lpLoopPre_straight d cd loop
  have hw : walk σ fn.body = .ret ((lpLoopPre d cd loop).flatMap (Main.slEvs σ)) [] := by
    rw [hb, lpLoopBody_pre]; exact Main.walk_straight σ [] _ hst
  rw [hw] at hw'
  obtain ⟨rfl, -⟩ := Out.ret.inj hw'
  obtain ⟨-, -, -, i4⟩ := Main.straight_parts σ _ hst
  rw [i4, lpLoopPre_calls] at hkv
  have hpar := congrArg (List.take 2) hp'
  rw [hp, hargs] at hpar
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.take_succ_cons, List.take_zero,
    List.cons.injEq, and_true] at hpar
  obtain ⟨g0, g1⟩ := hpar
  have hat : ∀ a, Stmt.atom a ∈ osLoopTailA (lpIterTail d) → a.Holds rd σ := fun a ha =>
    hes _ (lp_atom_mem (List.mem_append_left _ (List.mem_append_right _ ha)))
  have a0 : σ (.n (lpIterTail d)) = word 2 0 0 :=
    hat (.const (.n (lpIterTail d)) (word 2 0 0)) (by simp [osLoopTailA])
  have a1 : σ (.n (lpIterTail d + 1)) = σ (.n 0) * σ (.n (lpIterTail d)) :=
    hat (.mul (.n (lpIterTail d + 1)) (.n 0) (.n (lpIterTail d))) (by simp [osLoopTailA])
  have a2 : σ (.n (lpIterTail d + 2)) = σ (.n (lpIterTail d + 1)) + σ (.n 1) :=
    hat (.add (.n (lpIterTail d + 2)) (.n (lpIterTail d + 1)) (.n 1)) (by simp [osLoopTailA])
  have a3 : σ (.n (lpIterTail d + 3)) = word 2 0 0 :=
    hat (.const (.n (lpIterTail d + 3)) (word 2 0 0)) (by simp [osLoopTailA])
  have a4 : σ (.n (lpIterTail d + 4)) = σ (.n 0) * σ (.n (lpIterTail d + 3)) :=
    hat (.mul (.n (lpIterTail d + 4)) (.n 0) (.n (lpIterTail d + 3))) (by simp [osLoopTailA])
  have hg : σ (.n (lpIterTail d + 2)) = gen ^ j * gen + gen ^ sq := by
    rw [a2, a1, a0, g0, g1, word_gen]
  have ht0 : σ (.n (lpIterTail d + 4)) = gen ^ (j + 1) := by
    rw [a4, a3, g0, word_gen, gen_pow_mul_gen]
  match kids, hkv with
  | [k1, k2], hkv =>
    simp only [lpCallsS, List.map_cons, List.map_nil, Main.mkCall, Tree.KidsValid] at hkv
    obtain ⟨hk1, -, hk2, hk2v, -⟩ := hkv
    refine ⟨k1, k2, rfl, hk1, hk2, fun hne => ⟨(V.n (lpIterTail d + 4) ::
      (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ, ?_, ?_⟩⟩
    · rw [hg] at hk2v
      simpa [hne] using hk2v
    · simp [ht0, g1, List.range_succ]

/-- **A valid tree of `level_positions`' loop from `g^j` takes at least `lpTot … j` words.** -/
theorem lpLoop_total_ge (fs : String → ℕ) {d cd : ℕ} {loop : String} {fn : Fn}
    (hf : coreProgram.find? loop = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = lpLoopBody d cd loop) {sq : ℕ} (hsq : sq < 2 ^ 64 - 1) :
    ∀ t' j, j + t' + 1 = sq → ∀ (rd : Reader) (t : Tree) (args rets : List E),
      t.name = loop → t.Valid coreProgram rd args rets → args.take 2 = [gen ^ j, gen ^ sq] →
      lpTot fs loop (qwDecName d cd) sq j ≤ t.total fs := by
  intro t'
  induction t' with
  | zero => ?_
  | succ t' ih => ?_
  all_goals
    intro j hj rd t args rets hn hv hargs
    cases t with
    | phantom _ _ => simp [Tree.Valid] at hv
    | node f σ bufs kids => ?_
  all_goals
    simp only [Tree.name] at hn
    subst f
    obtain ⟨k1, k2, rfl, hk1, hk2, hk2v⟩ := lpLoop_valid hf hp hb hv hargs
    rw [total_node, totalKids_cons, totalKids_cons]
    have e1 := le_total (fs := fs) k1
    have e2 := le_total (fs := fs) k2
    rw [hk1] at e1
    rw [hk2] at e2
  · -- the last iteration
    rw [lpTot_step fs loop _ (by omega)]
    simp only [lpTailTot, show ¬ (j + 1 < sq) by omega, ↓reduceIte]
    omega
  · -- an iteration with a successor
    have hne : gen ^ j * gen + gen ^ sq ≠ 0 := by
      rw [ne_eq, gen_pow_add_eq_zero_iff]
      intro he
      have := gen_pow_inj (by omega) (by omega) he
      omega
    obtain ⟨args', hv', ha'⟩ := hk2v hne
    have := ih (j + 1) (by omega) rd k2 args' [] hk2 hv' ha'
    rw [lpTot_step fs loop _ (by omega)]
    simp only [lpTailTot, show j + 1 < sq by omega, ↓reduceIte]
    omega

/-- **A valid tree of `level_positions` takes at least `lpN` words.** -/
theorem lp_total_ge (fs : String → ℕ) {name loop : String} {sq d cd : ℕ}
    (hlp : FnIs name (osParams 8) (lpBody sq loop))
    (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop)) (hsq : 0 < sq)
    (hsq64 : (sq + 1) * 5 < 2 ^ 64 - 1) {rd : Reader} {t : Memory.Tree} {args rets : List E}
    (hn : t.name = name) (hv : t.Valid coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    lpN fs name loop d cd sq ≤ t.total fs := by
  obtain ⟨fnL, hfL, hpL, hbL⟩ := hl
  obtain ⟨fn, hf, hps, hb⟩ := hlp
  have hsq' : sq < u128Bound := by unfold u128Bound; omega
  cases t with
  | phantom _ _ => simp [Tree.Valid] at hv
  | node f σ bufs kids =>
  simp only [Tree.name] at hn
  subst f
  have hbo' := hbo
  simp only [Tree.Valid] at hv
  obtain ⟨fn', hf', -, es, vs, hw', -, hes, hkv⟩ := hv
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  have hst := lpPreB_straight sq loop
  have hw : walk σ fn.body = .ret ((lpPreB sq loop).flatMap (Main.slEvs σ))
      ((List.range 5).map fun i ↦ .n (22 + i)) := by
    rw [hb, lpBody_pre]; exact Main.walk_straight σ _ _ hst
  rw [hw] at hw'
  obtain ⟨rfl, -⟩ := Out.ret.inj hw'
  obtain ⟨-, i2, -, i4⟩ := Main.straight_parts σ _ hst
  have hat : ∀ a, Stmt.atom a ∈ lpPreB sq loop → a.Holds rd σ := fun a ha => hes _ (lp_atom_mem ha)
  have h8 : σ (.n 8) = gw ((sq + 1) * 5) :=
    hat (.const (.n 8) (gw ((sq + 1) * 5))) (by simp [lpPreB, osHeap])
  have h10 : σ (.n 10) = word 1 0 0 := hat (.const (.n 10) (word 1 0 0)) (by simp [lpPreB, osLoopCall])
  have h11 : σ (.n 11) = gw sq := hat (.const (.n 11) (gw sq)) (by simp [lpPreB, osLoopCall])
  have h12 : σ (.n 12) = σ (.n 10) + σ (.n 11) :=
    hat (.add (.n 12) (.n 10) (.n 11)) (by simp [lpPreB, osLoopCall])
  have h13 : σ (.n 13) = word 1 0 0 := hat (.const (.n 13) (word 1 0 0)) (by simp [lpPreB, osLoopCall])
  have h14 : σ (.n 14) = gw sq := hat (.const (.n 14) (gw sq)) (by simp [lpPreB, osLoopCall])
  have hbu : bufs = [(sq + 1) * 5] := by
    simp only [Tree.BufsOk] at hbo'
    rw [hbo'.1, events_node hf hw, i2, lpPreB_allocs]
    simp [h8, lp_logG_gw hsq64]
  rw [i4, lpPreB_calls] at hkv
  have hK : (1 : E) + gen ^ sq ≠ 0 := lp_one_add_ne hsq (by omega)
  have hg : σ (.n 12) = 1 + gen ^ sq := by rw [h12, h10, h11, word_one, Whir.gw_eq hsq']
  match kids, hkv with
  | [k], hkv =>
    simp only [List.map_cons, List.map_nil, Main.mkCall, Tree.KidsValid] at hkv
    obtain ⟨hk, hkv', -⟩ := hkv
    have hkv'' : k.Valid coreProgram rd
        [σ (.n 13), σ (.n 14), σ (.n 9), σ (.n 5), σ (.n 6), σ (.n 7)] [] := by
      rw [hg] at hkv'
      simpa [hK] using hkv'
    have := lpLoop_total_ge fs hfL hpL hbL (sq := sq) (by omega) (sq - 1) 0 (by omega) rd k _ []
      hk hkv'' (by simp [h13, h14, word_one, Whir.gw_eq hsq'])
    rw [total_node, totalKids_cons, hbu]
    simp only [Tree.totalKids, List.sum_cons, List.sum_nil, lpN]
    omega

/-! ## A valid tree, on a memory built for it -/

/-- The words of the built memory, by address exponent: the window table, the positions, the
window pointers into `run`, the squeeze run; nothing past them. -/
noncomputable def lpVal (d cd sq : ℕ) (cap : List E) (run : E) (i : ℕ) : Option E :=
  if i < 128 then some (eOfNat i)
  else if i < 128 + sq * (192 / d) then
    some (eOfNat (qwPosOf d (sqChal cap ((i - 128) / (192 / d))) ((i - 128) % (192 / d))))
  else if i < 128 + 2 * (sq * (192 / d)) then
    some (run * gen ^ ((i - (128 + sq * (192 / d))) % (192 / d) * qwN d cd))
  else if i < 128 + 2 * (sq * (192 / d)) + (sq + 1) * 5 then
    some ((sqCaps cap ((i - (128 + 2 * (sq * (192 / d)))) / 5)).getD
      ((i - (128 + 2 * (sq * (192 / d)))) % 5) 0)
  else none

/-- The built memory. -/
noncomputable def lpRd (d cd sq : ℕ) (cap : List E) (run : E) : Reader :=
  fun A ↦ lpVal d cd sq cap run (logG (ofK A))

theorem lpRd_at {d cd sq : ℕ} {cap : List E} {run : E} {i : ℕ} (hi : i < 2 ^ 64 - 1) :
    lpRd d cd sq cap run (addressOfIndex i) = lpVal d cd sq cap run i := by
  simp only [lpRd, logG_spec hi]

theorem lpRd_load {d cd sq : ℕ} {cap : List E} {run : E} {b k : ℕ} {v : E}
    (hi : b + k < 2 ^ 64 - 1) (h : lpVal d cd sq cap run (b + k) = some v) :
    LoadHolds (lpRd d cd sq cap run) (ofK (addressOfIndex b)) k v :=
  ⟨ofK_isInK _, by rw [Main.addr_ofK, lpRd_at hi, h]⟩

theorem lp_ite_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem lp_ite_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

/-- **A valid tree of `level_positions` exists**, on the built memory. -/
theorem lp_tree {name loop : String} {sq d cd : ℕ} (hlp : FnIs name (osParams 8) (lpBody sq loop))
    (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop)) (hsq : 0 < sq) (hsqB : sq ≤ 64)
    (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d) (hs : QwShape d cd)
    (hq : QwIs (qwDecName d cd) (qwBody d cd)) {cap : List E} (hcl : cap.length = 5)
    (hcan : AllCanonical cap) :
    ∃ (rd : Reader) (t : Memory.Tree) (args rets : List E), t.name = name ∧
      t.Valid coreProgram rd args rets ∧ t.BufsOk coreProgram := by
  have hQ0 : 0 < 192 / d := Nat.div_pos (by have := hs.2.1; omega) (by have := hs.1; omega)
  have hQle : 192 / d ≤ 192 := Nat.div_le_self _ _
  have hM : sq * (192 / d) ≤ 64 * 192 := Nat.mul_le_mul hsqB hQle
  have hW56 : 192 / d * qwN d cd ≤ 56 := hs.2.2.1
  have hQ : ∀ j < sq, ∀ t < 192 / d, j * (192 / d) + t < sq * (192 / d) := fun j hj t ht => by
    have := Nat.mul_le_mul_right (192 / d) (show j + 1 ≤ sq by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  set M := sq * (192 / d) with hMd
  set Q := 192 / d with hQd
  set run : E := ofK (addressOfIndex (128 + 2 * M + (sq + 1) * 5)) with hrun
  set rd := lpRd d cd sq cap run with hrd
  have hrows : ∀ j ≤ sq, ∀ i < 5, LoadHolds rd (ofK (addressOfIndex (128 + 2 * M))) (5 * j + i)
      ((sqCaps cap j).getD i 0) := fun j hj i hi => by
    refine lpRd_load (by omega) ?_
    simp only [lpVal]
    rw [lp_ite_neg (by omega), lp_ite_neg (by omega), lp_ite_neg (by omega), lp_ite_pos (by omega),
      show 128 + 2 * M + (5 * j + i) - (128 + 2 * M) = 5 * j + i by omega,
      show (5 * j + i) / 5 = j by omega, show (5 * j + i) % 5 = i by omega]
  have hdec : ∀ j < sq, coreProgram.Rel rd (qwDecName d cd)
      [sqChal cap j, ofK (addressOfIndex 128) * gen ^ (j * Q),
        ofK (addressOfIndex (128 + M)) * gen ^ (j * Q), ofK (addressOfIndex 0)] [] := by
    intro j hj
    have hdm : ∀ jj < Q, (j * Q + jj) / Q = j ∧ (j * Q + jj) % Q = jj := fun jj hjj => by
      rw [show j * Q + jj = jj + j * Q by ring, Nat.add_mul_div_right _ _ hQ0,
        Nat.div_eq_of_lt hjj, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjj]
      exact ⟨rfl, rfl⟩
    refine qw_complete hs hq rd _ _ _ _ run (fun i hi => ?_) (fun n hn => ?_) ⟨ofK_isInK _, ?_⟩
      (fun jj hjj => ⟨?_, ?_⟩)
    · rw [hrd, lpRd_at (by omega)]
      simp [lpVal, hi]
    · refine lpRd_load (by omega) ?_
      simp [lpVal, hn]
    · intro i hi v hv
      have hi56 : i < 56 := lt_of_lt_of_le hi hs.2.2.1
      rw [hrun, Main.addr_ofK, hrd, lpRd_at (by omega)] at hv
      simp only [lpVal] at hv
      rw [lp_ite_neg (by omega), lp_ite_neg (by omega), lp_ite_neg (by omega), lp_ite_neg (by omega)] at hv
      exact absurd hv (by simp)
    · rw [loadHolds_mul_gen_pow]
      refine lpRd_load (by have := hQ j hj jj hjj; omega) ?_
      have h1 := hQ j hj jj hjj
      simp only [lpVal]
      rw [lp_ite_neg (by omega), lp_ite_pos (by omega), show 128 + (j * Q + jj) - 128 = j * Q + jj by omega,
        (hdm jj hjj).1, (hdm jj hjj).2]
    · rw [loadHolds_mul_gen_pow]
      refine lpRd_load (by have := hQ j hj jj hjj; omega) ?_
      have h1 := hQ j hj jj hjj
      simp only [lpVal]
      rw [lp_ite_neg (by omega), lp_ite_neg (by omega), lp_ite_pos (by omega),
        show 128 + M + (j * Q + jj) - (128 + M) = j * Q + jj by omega, (hdm jj hjj).2]
  have hrel := lp_complete (rd := rd) hlp hl hsq (by unfold u128Bound; omega) hpw hcl hcan hrows hdec
  obtain ⟨t, hn, hv, hb⟩ := hrel.tree coreProgram_wf
  exact ⟨rd, t, _, _, hn, hv, hb⟩

/-- **A words bound of `level_positions`' trees bounds its placed words.** -/
theorem lp_bound {fs : String → ℕ} {name loop : String} {sq d cd : ℕ}
    (hlp : FnIs name (osParams 8) (lpBody sq loop))
    (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop)) (hsq : 0 < sq) (hsqB : sq ≤ 64)
    (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d) (hs : QwShape d cd)
    (hq : QwIs (qwDecName d cd) (qwBody d cd)) {cap : List E} (hcl : cap.length = 5)
    (hcan : AllCanonical cap) {B : ℕ} (hB : TotalLe coreProgram fs name (fun _ ↦ B)) :
    lpN fs name loop d cd sq ≤ B := by
  obtain ⟨rd, t, args, rets, hn, hv, hb⟩ := lp_tree hlp hl hsq hsqB hpw hs hq hcl hcan
  exact le_trans (lp_total_ge fs hlp hl hsq (by omega) hn hv hb) (hB rd t args rets hn hv hb)

end
end LeanVM.Guest.B1
