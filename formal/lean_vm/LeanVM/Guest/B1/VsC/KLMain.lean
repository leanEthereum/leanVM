/-
  LeanVM.Guest.B1.VsC.KLMain

  **`keccak_layer` completes placed** (`layer_placed`).
-/

module

public import LeanVM.Guest.B1.VsC.KLNode
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# `keccak_layer` completes placed

`layer_placed`: `callAtA_nodeRd` with `layerσ0` before the memory and `layerσ` on each, the own
words `layerWo`, the callees `layer_kids`; the events, returns and stored words by
`layer_body_complete`, the loads by `ldPs`/`gcPtrs`.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

theorem xs_length {D : LayerData} (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    (hlm : D.localMsgs.length = 11) : D.xs.length = 84 + 2 * D.y := by
  simp only [LayerData.xs, List.length_append, length_flatMap_pairs,
    flatMap_triples_length, hpl, hpm, hlm, List.length_cons, List.length_nil]
  omega

theorem xs_pack {D : LayerData} {rd : Reader} {cur : E} (hpl : D.product.length = 47)
    (h : ReadsAt rd cur D.xs) : ReadsAt rd (cur * gen ^ 48) (D.packMsgs.flatMap fun m ↦ [m.1, m.2]) := by
  simp only [LayerData.xs, List.append_assoc] at h
  rw [readsAt_append, readsAt_append, readsAt_append] at h
  have h3 := h.2.2.1
  rwa [hpl, List.length_singleton, mul_assoc, ← pow_add] at h3

theorem lAtoms_of_lPre {first j1 j2 : ℕ} {a : Atom} (h : Stmt.atom a ∈ lPre first j1 j2) :
    Stmt.atom a ∈ lAtoms first := by
  simp only [lPre, lAtoms, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h ⊢
  tauto

theorem klArrays_mem {claim cpt clp clc cfl cur out tb : E} {y nx : ℕ} :
    (claim, kcSize) ∈ VsC.klArrays claim cpt clp clc cfl cur out tb y nx ∧
    (cpt, y) ∈ VsC.klArrays claim cpt clp clc cfl cur out tb y nx ∧
    (clp, 25) ∈ VsC.klArrays claim cpt clp clc cfl cur out tb y nx ∧
    (clc, keccakLocalBits) ∈ VsC.klArrays claim cpt clp clc cfl cur out tb y nx ∧
    (cur, nx) ∈ VsC.klArrays claim cpt clp clc cfl cur out tb y nx ∧
    (out, kcSize) ∈ VsC.klArrays claim cpt clp clc cfl cur out tb y nx ∧
    (tb, 2 ^ winTabBits) ∈ VsC.klArrays claim cpt clp clc cfl cur out tb y nx := by
  simp [VsC.klArrays]

theorem ldPs_cases {first : ℕ} {p : V} {b : ℕ} (h : (p, b) ∈ ldPs first) :
    (p = .n (valf% «keccak_layer» "claim") ∧ b = kcSize) ∨
    (p = .n (valf% «keccak_layer» "cursor@1") ∧ b = 48) ∨
    (p = .n (valf% «keccak_layer» "out") ∧ b = kcSize) ∨ (p = .n (layOff first + 802) ∧ b = 36) ∨
    (p = .n (layOff first + 1240) ∧ b = 25) ∨ (p = .n (layOff first + 809) ∧ b = 11) ∨
    (p = .n (tW first + 25) ∧ b = 25) ∨ (p = .n (topV (tW first) + 3) ∧ b = 7) ∨
    (first ≠ 1 ∧ p = .n (layOff first + 1241) ∧ b = 11) := by
  unfold ldPs at h
  rw [List.mem_append] at h
  rcases h with h | h
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · split at h
    · simp at h
    · rename_i hf1
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hf1, h⟩)))))))

theorem r2_get5 {D : LayerData} {first : ℕ} {cur : E} :
    (D.r2 first cur).getD 5 0 = cur * gen ^ (48 + 2 * D.y) := by
  rw [LayerData.r2, List.getD_append_right _ _ _ _ (by rw [(LayerData.run2_state (D := D) (first := first)).2]),
    (LayerData.run2_state (D := D) (first := first)).2]
  exact cur_pack

/-- **The layer's loads**, from its pointers' values: through the caller's arrays, its own buffers,
or the window table. -/
theorem layer_loadsIn {first : ℕ} (hf : first < 2) {σ : Val} {T : ℕ → Prop}
    {claim cpt clp clc cfl cur out tb : E} {y nx cb j1 j2 : ℕ}
    (hreg : ∀ q ∈ VsC.klArrays claim cpt clp clc cfl cur out tb y nx, ∀ t < q.2,
      ∃ m, q.1.limb 0 * addressOfIndex t = addressOfIndex m ∧ T m)
    (hown : ∀ m, cb ≤ m → m < cb + (y + 43) → T m) (hnx : 84 + 2 * y ≤ nx)
    (e11 : σ (.n (valf% «keccak_layer» "claim")) = claim)
    (e7 : σ (.n (valf% «keccak_layer» "cursor@1")) = cur)
    (e12 : σ (.n (valf% «keccak_layer» "out")) = out)
    (e802 : σ (.n (layOff first + 802)) = cur * gen ^ (48 + 2 * y))
    (e1240 : σ (.n (layOff first + 1240)) = clp)
    (e809 : σ (.n (layOff first + 809)) = VsC.ptrAtV (cb + y))
    (e25 : σ (.n (tW first + 25)) = VsC.ptrAtV (cb + y + 11))
    (eF : σ (.n (topV (tW first) + 3)) = VsC.ptrAtV (cb + y + 36))
    (e1241 : first ≠ 1 → σ (.n (layOff first + 1241)) = clc)
    (egc : ∀ p ∈ gcPtrs 3 (preOff first + 544), ∃ e < 2 ^ 11, σ p = tb * gen ^ e) :
    ∀ A ∈ loadAddrs σ ((lPre first j1 j2).flatMap (slEvs σ)), ∃ i, A = addressOfIndex i ∧ T i := by
  have haoc := lPre_aoc hf j1 j2
  obtain ⟨mC, -, mL, mK, mX, mO, mT⟩ := klArrays_mem (claim := claim) (cpt := cpt) (clp := clp)
    (clc := clc) (cfl := cfl) (cur := cur) (out := out) (tb := tb) (y := y) (nx := nx)
  intro A hA
  rw [loadAddrs, List.mem_filterMap] at hA
  obtain ⟨ev, hev, hA⟩ := hA
  rcases VsC.mem_slEvs_aoc haoc hev with ⟨a, rfl, ha⟩ | ⟨g, a1, r1, rfl, -⟩
  · cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hA
      subst hA
      have hok := List.all_eq_true.mp (layer_atoms2 hf) _ (mem_atomsL.mpr (lAtoms_of_lPre ha))
      simp only [isLoad, Bool.not_true, Bool.false_or, ldOk, Bool.or_eq_true] at hok
      rcases hok with hok | hok
      · simp only [ldIn, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
        obtain ⟨⟨qp, qb⟩, hq, hqp, hoff⟩ := hok
        simp only at hqp hoff
        subst hqp
        rcases ldPs_cases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hf1, rfl, rfl⟩
        · rw [e11]; exact hreg _ mC off hoff
        · rw [e7]; exact hreg _ mX off (show off < nx by omega)
        · rw [e12]; exact hreg _ mO off hoff
        · rw [e802, addr_gen]; exact hreg _ mX (48 + 2 * y + off) (show 48 + 2 * y + off < nx by omega)
        · rw [e1240]; exact hreg _ mL off hoff
        · rw [e809, ptr_addr]; exact ⟨_, rfl, hown _ (by omega) (by omega)⟩
        · rw [e25, ptr_addr]; exact ⟨_, rfl, hown _ (by omega) (by omega)⟩
        · rw [eF, ptr_addr]; exact ⟨_, rfl, hown _ (by omega) (by omega)⟩
        · rw [e1241 hf1]; exact hreg _ mK off hoff
      · simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hok
        obtain ⟨hp, rfl⟩ := hok
        obtain ⟨e, he, hpe⟩ := egc p hp
        rw [hpe, addr_gen]
        exact hreg _ mT (e + 0) (show e + 0 < 2 ^ winTabBits by norm_num [winTabBits]; omega)
    | _ => simp [Ev.loadAddr?] at hA
  · simp [Ev.loadAddr?] at hA

set_option maxHeartbeats 1000000 in
theorem layer_e1240 {first : ℕ} (hf : first < 2) {rd : Reader} {w : ℕ → E} {args : List E}
    (hl : args.length = 15) {clp : E}
    {claim : E} (h11 : layerσ rd w args first (.n (valf% «keccak_layer» "claim")) = claim)
    (h : LoadHolds rd claim 3 clp) :
    layerσ rd w args first (.n (layOff first + 1240)) = clp := by
  have hmw : Stmt.atom (.load (.n (layOff first + 1240)) (.n (valf% «keccak_layer» "claim")) 3) ∈
      weightT first (layOff first) := by unfold weightT; split <;> simp
  have hG := layer_good (rd := rd) (w := w) (args := args) hf hl
  generalize layerσ rd w args first = σ at hG h11 ⊢
  have g := hG (Stmt.atom (.load (.n (layOff first + 1240)) (.n (valf% «keccak_layer» "claim")) 3))
    (by rw [layerT_sections]; simp only [List.mem_append]; tauto)
  rw [← h11] at h
  exact load_val (w := w) (S := layerSt first) g (not_mem_of_noStoreVia (layer_noStore hf) (by simp) _ _) h

set_option maxHeartbeats 1000000 in
theorem layer_e1241 {first : ℕ} (hf : first < 2) (hf1 : first ≠ 1) {rd : Reader} {w : ℕ → E}
    {args : List E} (hl : args.length = 15) {clc : E}
    {claim : E} (h11 : layerσ rd w args first (.n (valf% «keccak_layer» "claim")) = claim)
    (h : LoadHolds rd claim 4 clc) :
    layerσ rd w args first (.n (layOff first + 1241)) = clc := by
  have hmw : Stmt.atom (.load (.n (layOff first + 1241)) (.n (valf% «keccak_layer» "claim")) 4) ∈
      weightT first (layOff first) := by unfold weightT; simp [hf1]
  have hG := layer_good (rd := rd) (w := w) (args := args) hf hl
  generalize layerσ rd w args first = σ at hG h11 ⊢
  have g := hG (Stmt.atom (.load (.n (layOff first + 1241)) (.n (valf% «keccak_layer» "claim")) 4))
    (by rw [layerT_sections]; simp only [List.mem_append]; tauto)
  rw [← h11] at h
  exact load_val (w := w) (S := layerSt first) g (not_mem_of_noStoreVia (layer_noStore hf) (by simp) _ _) h

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`keccak_layer` completes placed** on a layer's honest data. -/
theorem layer_placed {k : ℕ} (hk : 11 ≤ k) {first : ℕ} (hf : first < 2) (D : LayerData)
    {p0 p1 cur claim out iota tb cpt clp clc cfl : E}
    (hcl : D.cap.length = 5) (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy32 : D.y < 32) (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hgrind : ((D.s0 first).absorbAll D.product dsObserve).GrindOk sGrindBits D.nonce)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs D.t)
    {R : ℕ → Prop} {fp : ℕ}
    (hR : VsC.InRegion (VsC.klArrays claim cpt clp clc cfl cur out tb D.y D.xs.length) R) :
    ∃ e, fp + fs (layerName first) + D.y + 43 ≤ e ∧
      ((∀ f, fs f < 2 ^ 16) → e ≤ fp + fs (layerName first) + 2 ^ 18) ∧
      CallAtA fs al cert k (layerName first) (layerArgs D p0 p1 cur claim out iota tb)
      (D.rets first cur) R (VsC.klOwn (fp + fs (layerName first)) D.y)
      (fun rd => ReadsAt rd out (VsC.klOutW (D.next first) (fp + fs (layerName first)) D.y) →
        ClaimRec rd false out (D.next first) D.y)
      (fun rd => WinTabs rd tb ∧ VsC.ClaimRecAt rd (first = 1) claim cpt clp clc cfl D.c D.y ∧
        ReadsAt rd cur D.xs ∧ ReadsAt rd out (VsC.klOutW (D.next first) (fp + fs (layerName first)) D.y))
      VsC.PostQuiet (fs (layerName first)) fp (fp + fs (layerName first)) e := by
  obtain ⟨fn, hfind, hbody, hparams⟩ := layer_fn hf
  have hlp : coreProgram.loop (layerName first) = false :=
    VsC.loop_false_of_ret (hfind := hfind) (by rw [hbody, layerT_split]) (by simp [lRet])
  set cb := fp + fs (layerName first) with hcb
  set w := layerW D first cur cb with hwd
  set args := layerArgs D p0 p1 cur claim out iota tb with hargs
  have hl15 : args.length = 15 := by simp [hargs, layerArgs, hcl]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (layer_chk hf)
  have hchk : chk args.length (layerT first) = some c' := by rw [hl15]; exact hc'
  set σr := layerσ (fun _ => none) w args first with hσr
  obtain ⟨-, r8, -, -, -, -, r14, r782, r784, r785, r797, r798, -, -, -⟩ :=
    layer_static (p0 := p0) (p1 := p1) (cur := cur) (claim := claim) (out := out) (iota := iota)
      (tb := tb) (cb := cb) hf hcl (fun _ => none)
  set σ0 := layerσ0 D first cpt σr with hσ0d
  obtain ⟨hA1, hR1, hA2, hR2⟩ := layer_σ0_calls (D := D) (first := first) (cpt := cpt) (cur := cur)
    (σr := σr) r784 r785 r782 r797 r798 r14
  have hj1 : D.y / krStep < 2 := by unfold krStep; omega
  have hj2 : D.y % krStep < 16 := by unfold krStep; omega
  have hn1 : D.n1 ≤ D.y := LayerData.n1_le
  have hn12 : D.n1 + D.y % krStep = D.y := by unfold LayerData.n1 krStep; omega
  have haoc := lPre_aoc hf (D.y / krStep) (D.y % krStep)
  set es := (lPre first (D.y / krStep) (D.y % krStep)).flatMap (slEvs σr) with hesd
  have hes : ∀ τ : Val, (lPre first (D.y / krStep) (D.y % krStep)).flatMap (slEvs τ) = es := fun τ =>
    List.flatMap_congr fun s hs => VsC.slEvs_atomOrCall τ σr s (List.all_eq_true.mp haoc s hs)
  have hstr := VsC.straight_of_atomOrCall _ haoc
  have hwalk : ∀ τ : Val, τ (.n 9) = gen ^ (D.y / krStep) → τ (.n 10) = gen ^ (D.y % krStep) →
      walk τ fn.body = .ret es (lRet first) := by
    intro τ h1 h2
    rw [hbody, layer_walk first hj1 hj2 (by rw [h1, gen_pow_eq_ofK]) (by rw [h2, gen_pow_eq_ofK]),
      walk_straight τ _ _ hstr, hes]
  obtain ⟨ha5, ha6, -⟩ := layer_atoms5 hf
  have hdst : allocDsts es = [.n (preOff first + 782), .n (preOff first + 810), .n (tW first + 25),
      .n (topV (tW first) + 3)] := by
    rw [hesd, (straight_parts σr _ hstr).1, lPre_filterMap (fun _ _ _ => rfl), ha5]; rfl
  have hal : ∀ τ : Val, τ (.n 8) = gen ^ D.y → allocs τ es = [D.y, 11, 25, 7] := by
    intro τ h8
    rw [← hes τ, (straight_parts τ _ hstr).2.1, lPre_filterMap (fun _ _ _ => rfl), ha5]
    simp [h8, gen_pow_eq_ofK, logG_spec (show D.y < 2 ^ 64 - 1 by omega)]
  have haddr : addrs es = [] := by
    rw [hesd, (straight_parts σr _ hstr).2.2.1, lPre_filterMap (fun _ _ _ => rfl), ha6]
  have hcalls : calls es = [⟨stepNames.getD (D.y / krStep) "", lA1 (preOff first), lR1 (preOff first), true⟩,
      ⟨remNames.getD (D.y % krStep) "", lA2 (preOff first), lR2 (preOff first), true⟩] := by
    rw [hesd, (straight_parts σr _ hstr).2.2.2, lPre_calls hf]; rfl
  have hal0 : allocs σ0 es = [D.y, 11, 25, 7] :=
    hal σ0 (by rw [hσ0d, σ0_other (by omega) (by omega) (by omega) (by omega)]; exact r8)
  -- own words
  obtain ⟨hchL, hlocL, hlanL, hflL⟩ := layerWo_lengths (first := first) hpm hlm
  set Wo := layerWo D first cb with hWod
  have hsum : [D.y, 11, 25, 7].sum = D.y + 43 := by simp
  have hown : ∀ i, cb ≤ i → i < cb + (D.y + 43) →
      ownData cert fp cb (layerName first) [D.y, 11, 25, 7] es i := by
    intro i h1 h2; left
    rcases (by omega : i < cb + D.y ∨ (cb + D.y ≤ i ∧ i < cb + D.y + 11) ∨
      (cb + D.y + 11 ≤ i ∧ i < cb + D.y + 11 + 25) ∨ cb + D.y + 11 + 25 ≤ i) with h | h | h | h
    · exact ⟨(D.y, cb), by simp [bases], by omega, by simp; omega⟩
    · exact ⟨(11, cb + D.y), by simp [bases], by simp; omega, by simp; omega⟩
    · exact ⟨(25, cb + D.y + 11), by simp [bases], by simp; omega, by simp; omega⟩
    · exact ⟨(7, cb + D.y + 11 + 25), by simp [bases], by simp; omega, by simp; omega⟩
  have hxsL := xs_length hpl hpm hlm
  set R' : ℕ → Prop := fun i => R i ∨ ownData cert fp cb (layerName first) (allocs σ0 es) es i with hR'
  have hreg : ∀ q ∈ VsC.klArrays claim cpt clp clc cfl cur out tb D.y D.xs.length, ∀ t < q.2,
      ∃ m, q.1.limb 0 * addressOfIndex t = addressOfIndex m ∧ R' m := fun q hq t ht => by
    obtain ⟨i, hi, hr⟩ := hR q hq t ht
    exact ⟨i, hi, Or.inl hr⟩
  have hownR : ∀ i, cb ≤ i → i < cb + (D.y + 43) → R' i := fun i h1 h2 => Or.inr (by
    rw [hal0]; exact hown i h1 h2)
  obtain ⟨mC, mP, mL, mK, mX, mO, mT⟩ := klArrays_mem (claim := claim) (cpt := cpt) (clp := clp)
    (clc := clc) (cfl := cfl) (cur := cur) (out := out) (tb := tb) (y := D.y) (nx := D.xs.length)
  have hn1' : krStep * (D.y / krStep) ≤ D.y := hn1
  have hK1 : VsC.KrRegion cpt (cur * gen ^ 48) (VsC.ptrAtV cb) (krStep * (D.y / krStep)) R' := by
    refine ⟨fun t ht => hreg _ mP t (by simp only; omega), fun t ht => ?_, fun t ht => ?_⟩
    · rw [addr_gen]; exact hreg _ mX _ (by simp only; omega)
    · exact ⟨cb + t, ptr_addr cb t, hownR _ (by omega) (by omega)⟩
  have hK2 : VsC.KrRegion (cpt * gen ^ D.n1) (cur * gen ^ 48 * gen ^ (2 * D.n1))
      (VsC.ptrAtV cb * gen ^ D.n1) (D.y % krStep) R' := by
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · rw [addr_gen]; exact hreg _ mP _ (by simp only; omega)
    · rw [mul_assoc, ← pow_add, addr_gen]; exact hreg _ mX _ (by simp only; omega)
    · rw [addr_gen, ptr_addr]; exact ⟨_, rfl, hownR _ (by omega) (by omega)⟩
  -- the callees' preconditions
  have hsq := sq_eq D first
  have hpk := LayerData.pack_split hpm hsq
  obtain ⟨hrs, hrl⟩ := LayerData.run1_state (D := D) (first := first)
  have hch : D.chs first = (D.run1 first).1.2 ++ (D.run2 first).1.2 := by
    rw [LayerData.chs, hpk]
  have hrun1L : (D.run1 first).1.2.length = D.n1 := by
    rw [LayerData.run1, packRunF_chs_length _ _ _ _ (by rw [List.length_take, List.length_take, hpm]; rfl),
      List.length_take]; exact Nat.min_eq_left hn1
  have hpre1 : ∀ rd, (WinTabs rd tb ∧ VsC.ClaimRecAt rd (first = 1) claim cpt clp clc cfl D.c D.y ∧
      ReadsAt rd cur D.xs ∧ ReadsAt rd out (VsC.klOutW (D.next first) cb D.y)) →
      ReadsAt rd cpt (D.c.point.take D.n1) ∧ ReadsAt rd (cpt * gen ^ D.n1) (D.c.point.drop D.n1) ∧
      ReadsAt rd (cur * gen ^ 48) ((D.packMsgs.take D.n1).flatMap fun m ↦ [m.1, m.2]) ∧
      ReadsAt rd (cur * gen ^ 48 * gen ^ (2 * D.n1)) ((D.packMsgs.drop D.n1).flatMap fun m ↦ [m.1, m.2]) := by
    intro rd hp
    have hpt := hp.2.1.2.2.2.2.2.2.1
    rw [← List.take_append_drop D.n1 D.c.point, readsAt_append] at hpt
    have hst := xs_pack hpl hp.2.2.1
    rw [← List.take_append_drop D.n1 D.packMsgs, List.flatMap_append, readsAt_append,
      length_flatMap_pairs, List.length_take, hpm, Nat.min_eq_left hn1] at hst
    rw [List.length_take, Nat.min_eq_left (show D.n1 ≤ D.c.point.length from hn1)] at hpt
    exact ⟨hpt.1, hpt.2, hst.1, hst.2⟩
  have hWr : ∀ rd, HoldsWords rd Wo → ReadsAt rd (VsC.ptrAtV cb) (D.chs first) ∧
      ReadsAt rd (VsC.ptrAtV (cb + D.y)) (D.locPt first) ∧
      ReadsAt rd (VsC.ptrAtV (cb + D.y + 11)) (lanesOut (D.locPt first) (D.beta first).1) ∧
      ReadsAt rd (VsC.ptrAtV (cb + D.y + 36)) (layerFl D first) := fun rd h =>
    ⟨h (cb, _) (by rw [hWod]; exact List.mem_cons_self),
      h (cb + D.y, _) (by rw [hWod]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      h (cb + D.y + 11, _) (by rw [hWod]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      h (cb + D.y + 36, _) (by
        rw [hWod]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  have hkids := layer_kids (fs := fs) (al := al) (cert := cert) (k := k) (first := first) D
    (cur := cur) (cpt := cpt) (tb := tb) (σ0 := σ0) (R' := R')
    (Pre := fun rd => WinTabs rd tb ∧ VsC.ClaimRecAt rd (first = 1) claim cpt clp clc cfl D.c D.y ∧
      ReadsAt rd cur D.xs ∧ ReadsAt rd out (VsC.klOutW (D.next first) cb D.y))
    (Wo := Wo) (cb := cb) (cur0 := cb + (D.y + 43)) hy32 hpm hA1 hR1 hA2 hR2 hK1 hK2
    (fun rd hp hW => by
      obtain ⟨a1, -, a3, -⟩ := hpre1 rd hp
      refine ⟨a1, a3, ?_⟩
      have := (hWr rd hW).1
      rw [hch] at this
      exact VsC.readsAt_prefix this)
    (fun rd hp hW => by
      obtain ⟨-, a2, -, a4⟩ := hpre1 rd hp
      refine ⟨a2, a4, ?_⟩
      have := (hWr rd hW).1
      rw [hch, readsAt_append, hrun1L] at this
      have h2 := this.2
      rwa [LayerData.run2, hrs] at h2)
  have hle : cb + D.y + 43 ≤ layerEnd fs al D (cb + (D.y + 43)) := by
    unfold layerEnd
    have h1 := le_allocBase (al (stepNames.getD (D.y / krStep) "")) (cb + (D.y + 43))
    have h2 := le_allocBase (al (remNames.getD (D.y % krStep) ""))
      (allocBase (al (stepNames.getD (D.y / krStep) "")) (cb + (D.y + 43)) + fs (stepNames.getD (D.y / krStep) ""))
    omega
  have hub : (∀ f, fs f < 2 ^ 16) → layerEnd fs al D (cb + (D.y + 43)) ≤ cb + 2 ^ 18 := by
    intro hfs
    unfold layerEnd
    have h1 := allocBase_le (al (stepNames.getD (D.y / krStep) "")) (cb + (D.y + 43))
    have h2 := allocBase_le (al (remNames.getD (D.y % krStep) ""))
      (allocBase (al (stepNames.getD (D.y / krStep) "")) (cb + (D.y + 43)) + fs (stepNames.getD (D.y / krStep) ""))
    have h3 := hfs (stepNames.getD (D.y / krStep) "")
    have h4 := hfs (remNames.getD (D.y % krStep) "")
    omega
  refine ⟨layerEnd fs al D (cb + (D.y + 43)), hle, hub, callAtA_nodeRd hlp le_rfl ⟨σ0, fn, es, lRet first, Wo,
    [VsC.PostQuiet, VsC.PostQuiet], fun rd => (HoldsWords rd Wo ∧ True) ∧ True, fun _ => False,
    hfind, ?_, ?_, ?_, fun rd h ho => layer_out hpm hlm h.1.1 ho, ?_⟩⟩
  · rw [hal0, hsum]
    refine ⟨fun q hq => Or.inr ?_, ?_⟩
    · simp only [hWod, layerWo, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [hchL, hlocL, hlanL, hflL] <;> omega
    · simp [hWod, layerWo, hchL, hlocL, hlanL, hflL]
  · intro i hi
    exact Or.inl (by rw [hal0]; exact hown i hi.1 (by have := hi.2; omega))
  · have hs : (allocs σ0 es).sum = D.y + 43 := by rw [hal0, hsum]
    rw [hcalls, hs]; exact hkids
  -- on a memory
  intro rd hl hpre hO
  obtain ⟨s7, s8, s9, s10, s11, s12, s14, s782, s784, s785, s797, s798, s810, s25, sF⟩ :=
    layer_static (p0 := p0) (p1 := p1) (cur := cur) (claim := claim) (out := out) (iota := iota)
      (tb := tb) (cb := cb) hf hcl rd
  set σ := layerσ rd w args first with hσd
  obtain ⟨htb, hcra, hxs, hout⟩ := hpre
  obtain ⟨cw, hcw, hcwl, -⟩ := cw_of_at hcra
  have hcpt : LoadHolds rd claim 2 cpt := hcra.2.2.2.2.2.1
  obtain ⟨w782, w810, w25, wF, w785, w798, wwin⟩ := layerW_vals (D := D) (cur := cur) (cb := cb) hf
  obtain ⟨hW0, hW1, hW2, hW3⟩ := hWr rd hO.1.1
  have hlo809 : layOff first + 809 = preOff first + 810 := by rw [layOff_eq]
  obtain ⟨⟨ecapS0, e7800, e7810, e7960, e5320⟩, HB⟩ := layer_body_complete (C := fun _ _ _ => True) hf D
    (p0 := p0) (p1 := p1) (cur := cur) (claim := claim) (out := out) (iota := iota) (tb := tb)
    (cpt := cpt) (w := w) hcl hw hy32 hpl hpm hlm hproj hgrind hfin (claimRec_of_at hcra) hcpt hcw hcwl
    hxs (by rw [hwd, hlo809, w810]; exact hW1) (by rw [hwd, w25]; exact hW2)
    (by rw [hwd, wF]; exact hW3)
    (by rw [hwd, hlo809, w782, w25, w810, wF]; exact hout)
    (VsC.hrc_of_lowDef hl hk) htb (fun j hj => wwin j hj) (fun k hk => w785 k hk)
    (fun k hk => w798 k hk) trivial trivial
  have ecapS : (cap5 (preOff first + 539)).map σ = D.capS first := ecapS0
  have e780 : σ (.n (preOff first + 780)) = polyEval D.product (D.sv first) := e7800
  have e781 : σ (.n (preOff first + 781)) = cpt := e7810
  have e796 : σ (.n (preOff first + 796)) = cpt * gen ^ D.n1 := e7960
  have e532 : σ (.n (preOff first + 532)) = D.gw first := e5320
  have hwf : Stmt.wfList coreProgram (layerT first) = true := by
    interval_cases first <;> decide +kernel
  have hsat : (walk σ (layerT first)).Sat (fun _ _ _ => True) rd σ False (fun r ↦ r = D.rets first cur) :=
    walk_sat (P := coreProgram) (layerT first) hwf HB
  rw [← hbody, hwalk σ s9 s10] at hsat
  obtain ⟨hevs, hret⟩ := hsat
  -- the calls' words on this memory
  have hA1σ : (lA1 (preOff first)).map σ = D.capS first ++
      [cur * gen ^ 48, polyEval D.product (D.sv first), cpt, VsC.ptrAtV cb, tb] := by
    simp only [lA1, List.map_append, List.map_cons, List.map_nil]
    rw [ecapS, s784, e780, e781, s782, s14]
  have hR1σ : (lR1 (preOff first)).map σ = D.r1 first cur := by
    apply List.ext_getElem (by simp [lR1, r1_length])
    intro k h1 h2
    simp only [lR1, List.getElem_map, List.getElem_range]
    rw [s785 k (by simpa [lR1] using h1), List.getD_eq_getElem _ _ h2]
  have hR2σ : (lR2 (preOff first)).map σ = D.r2 first cur := by
    apply List.ext_getElem (by simp [lR2, r2_length])
    intro k h1 h2
    simp only [lR2, List.getElem_map, List.getElem_range]
    rw [s798 k (by simpa [lR2] using h1), List.getD_eq_getElem _ _ h2]
  have hA2σ : (lA2 (preOff first)).map σ = D.r1 first cur ++
      [cpt * gen ^ D.n1, VsC.ptrAtV cb * gen ^ D.n1, tb] := by
    simp only [lA2, List.map_append, List.map_cons, List.map_nil, hR1σ]
    rw [e796, s797, s14]
  -- the grind's values and exactness
  have hgcv := gcInline_vals_of_good (rd := rd) (S := layerSt first) (wo := w) (σ := σ)
    (b := 3) (o := preOff first + 544) (by decide) (w := .n (preOff first + 532))
    (tabs := .n (valf% «keccak_layer» "tabs")) (by simp) (by simp)
    (fun s hs => layer_good (rd := rd) (w := w) hf hl15 s (gc_mem hf hs)) (layerSt_noGrind hf)
    (VsC.hrc_of_lowDef hl hk) (by rw [s14]; exact htb)
    (fun j hj => by rw [e532]; exact wwin j hj)
  have hgx := gcInline_exact_of_shape (σ := σ) (rd0 := rd) (b := 3) (o := preOff first + 544)
    ⟨by decide, by decide, by decide⟩ hgcv
  -- the loads' pointers
  have hpar7 : σ (.n 7) = cur := s7
  refine ⟨σ, by rw [hparams]; have := VsC.fwd_params (rd := rd) (w := w) hchk; rwa [hl15] at this,
    hwalk σ s9 s10, hret, by rw [hal σ s8, hal0], ⟨?_, by rw [haddr]; simp⟩, ?_, ?_, ?_,
    fun ev hev => (hevs ev hev).1, fun ts hv hp => ?_⟩
  · rw [hdst, hal0]
    simp only [List.map_cons, List.map_nil, bases, s782, s810, s25, sF, VsC.ptrAtV]
  · rw [hcalls]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨hA1.trans hA1σ.symm, hR1.trans hR1σ.symm⟩
    · exact ⟨hA2.trans hA2σ.symm, hR2.trans hR2σ.symm⟩
  · have cv : ∀ m, R' m → ownData cert fp cb (layerName first) (allocs σ0 es) es m ∨ R m ∨ False :=
      fun m h => h.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inl h)
    obtain ⟨-, -, -, -, -, -, -, lanes, hlp3, -, -, hrest⟩ := hcra
    have e1240 : σ (.n (layOff first + 1240)) = clp := layer_e1240 hf hl15 s11 hlp3
    have e1241 : first ≠ 1 → σ (.n (layOff first + 1241)) = clc := fun hf1 => by
      simp only [hf1, decide_false, Bool.false_eq_true, ↓reduceIte] at hrest
      obtain ⟨loc, h4, -⟩ := hrest
      exact layer_e1241 hf hf1 hl15 s11 h4
    have e802 : σ (.n (layOff first + 802)) = cur * gen ^ (48 + 2 * D.y) := by
      rw [show layOff first + 802 = preOff first + 798 + 5 by rw [layOff_eq], s798 5 (by norm_num), r2_get5]
    have e809 : σ (.n (layOff first + 809)) = VsC.ptrAtV (cb + D.y) := by
      rw [show layOff first + 809 = preOff first + 810 by rw [layOff_eq]]; exact s810
    have egc : ∀ p ∈ gcPtrs 3 (preOff first + 544), ∃ e < 2 ^ 11, σ p = tb * gen ^ e := by
      intro p hp
      obtain ⟨e, he, hpe⟩ := gcPtrs_of_good (rd := rd) (S := layerSt first) (wo := w) (σ := σ)
        (b := 3) (o := preOff first + 544) (by decide) (w := .n (preOff first + 532))
        (tabs := .n (valf% «keccak_layer» "tabs")) (by simp) (by simp)
        (fun s hs => layer_good (rd := rd) (w := w) hf hl15 s (gc_mem hf hs)) (layerSt_noGrind hf)
        (VsC.hrc_of_lowDef hl hk) (by rw [s14]; exact htb)
        (fun j hj => by rw [e532]; exact wwin j hj) p hp
      exact ⟨e, he, by rw [hpe, s14]⟩
    intro A hA
    rw [← hes σ] at hA
    exact layer_loadsIn hf (fun q hq t ht => by obtain ⟨m, hm, hr⟩ := hreg q hq t ht; exact ⟨m, hm, cv m hr⟩)
      (fun m h1 h2 => cv m (hownR m h1 h2)) (by omega) s11 s7 s12 e802 e1240 e809 s25 sF e1241 egc A hA
  · intro A hA
    rw [heapHintAddrs, List.mem_flatMap] at hA
    obtain ⟨ev, hev, hA⟩ := hA
    rw [← hes σ] at hev
    rcases VsC.mem_slEvs_aoc haoc hev with ⟨a, rfl, ha⟩ | ⟨g, a1, r1, rfl, -⟩
    · have := List.all_eq_true.mp (layer_atoms3 hf).1 a (mem_atomsL.mpr (lAtoms_of_lPre ha))
      cases a with
      | hint h =>
        simp only [noHeapHint, Option.isNone_iff_eq_none] at this
        simp [Ev.hintAddrs, this] at hA
      | _ => simp [Ev.hintAddrs] at hA
    · simp [Ev.hintAddrs] at hA
  · refine VsC.postQuiet_node hfind (hwalk σ s9 s10) (fun a ha => ?_) (fun ev hev => ?_) hv
      (by rw [hcalls] at hp ⊢; exact hp) _
    · rw [← hes σ] at ha
      rcases VsC.mem_slEvs_aoc haoc ha with ⟨b, hb, hb'⟩ | ⟨g, a1, r1, hb, -⟩
      · cases hb
        exact List.all_eq_true.mp (layer_atoms3 hf).2 a (mem_atomsL.mpr (lAtoms_of_lPre hb'))
      · cases hb
    · rw [← hes σ] at hev
      rcases VsC.mem_slEvs_aoc haoc hev with ⟨a, rfl, ha⟩ | ⟨g, a1, r1, rfl, -⟩
      · have h4 := List.all_eq_true.mp (layer_atoms4 hf) a (mem_atomsL.mpr (lAtoms_of_lPre ha))
        simp only [Bool.or_eq_true] at h4
        rcases h4 with h4 | h4
        · exact VsC.exact_of_trivExact h4
        · simp only [inGc, List.contains_iff_mem] at h4
          obtain ⟨a', ha', hx⟩ := hgx _ (mem_atomsL.mp h4)
          cases ha'
          exact hx rd
      · trivial

set_option maxRecDepth 20000 in
/-- **`keccak_layer` completes placed**, as `KeccakLayerCompleteA` states it. -/
theorem keccakLayerCompleteA {k : ℕ} (hk : 11 ≤ k) : VsC.KeccakLayerCompleteA fs al cert k := by
  intro first hf f0 f1 f2 f3 f4 p0 p1 cur claim out iota tabs w cpt clp clc cfl y step c product n packMsgs
    localMsgs t R fp _ hy32 hpl hpm hlm hgrind hproj hfin hw hiota hpt hR
  subst hpt hiota
  let D : LayerData := ⟨[f0, f1, f2, f3, f4], w, c, product, n, packMsgs, localMsgs, t⟩
  have hlen : (VsC.klXs product n packMsgs localMsgs t).length = 48 + 2 * c.point.length + 36 := by
    have := xs_length (D := D) hpl hpm hlm
    change D.xs.length = _
    rw [this]; show 84 + 2 * c.point.length = _; omega
  rw [hlen]
  exact layer_placed (fs := fs) (al := al) (cert := cert) hk hf D (p0 := p0) (p1 := p1) (cur := cur)
    (claim := claim) (out := out) (tb := tabs) (cpt := cpt) (clp := clp) (clc := clc) (cfl := cfl)
    rfl hw hy32 hpl hpm hlm hproj hgrind hfin hR

end
end LeanVM.Guest.B1.VerifySub.KL
