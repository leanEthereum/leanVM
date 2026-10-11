module

public import LeanVMCircuits.Xmss.Sound
public import LeanVMCircuits.Sphincs.Words
public import LeanVMCircuits.Sphincs.FieldFacts

@[expose] public section

/-!
# What the leanSPHINCS circuit's gadgets make their outputs

Contracts of the gadgets of `Sphincs.Circuit` in the style of `Xmss.SoundGadgets`, whose machinery (`Post`, the loop
rules, the statement count) and gadget contracts (`words`, `statementWords`, `digitProduct`, `indicators`) they
reuse: the tweak's second word from bits, a tweak hash, a tree level and a whole climb, a chain, the few-time key
and a layer.
-/

namespace LeanVMCircuits.Sphincs

open LeanVMCircuits.Rec (K E toE emb ofWord toWord words4 digest hashWords num root toE_injective)
open LeanVMCircuits.Rec.Model
open LeanVMCircuits.Xmss
open Xmss.Words (W Dig)

/-- A tweak's second word, `tau | j << 32`. -/
def tw1 (a b : ℕ) : W := BitVec.ofNat 64 (a % 2 ^ 32 + b % 2 ^ 32 * 2 ^ 32)

theorem tweak_eq (ty lay tau p j : ℕ) :
    Sphincs.Words.tweak ty lay tau p j = (BitVec.ofNat 64 (Sphincs.Circuit.tweak0 ty lay p), tw1 tau j) := rfl

theorem pure_good {α : Type} (a : α) :
    Good (fun _ => True) (pure a : M α) fun s r s' => s'.statement = s.statement ∧ r = a ∧ s' = s :=
  Good.pure' fun _ _ _ => ⟨rfl, rfl, rfl⟩

theorem spDig_th {val : Val} {r : ℕ} {tw : W × W} {P : Dig} {pl : List W}
    (h : words4 (val r) = digest (hashWords ([tw.1, tw.2, P.1, P.2] ++ pl))) :
    dig val r = Sphincs.Words.th tw P pl := by
  simp only [dig, Sphincs.Words.th, h]

theorem sp_climb_eq (ty lay tau e h : ℕ) (P : Dig) (path : ℕ → Dig) (leaf : Dig) :
    Sphincs.Words.climb ty lay tau e h P (fun l => path l.val) leaf =
      (List.range h).foldl (fun c l => Sphincs.Words.parent ty lay tau e l P c (path l)) leaf := by
  unfold Sphincs.Words.climb
  have : (List.finRange h).map Fin.val = List.range h := by
    apply List.ext_getElem <;> simp
  rw [← this, List.foldl_map]

theorem ofFn_flatMap' (n : ℕ) (F : ℕ → Dig) :
    (List.ofFn fun i : Fin n => F i.val).flatMap (fun d => [d.1, d.2]) =
      (List.range n).flatMap fun i => [(F i).1, (F i).2] := by
  have : (List.ofFn fun i : Fin n => F i.val) = (List.range n).map F := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, List.length_range]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  rw [this, List.flatMap_map]

/-! The tweak's second word. -/

theorem idx_getD (tau j : List ℕ) (z i : ℕ) (htau : tau.length ≤ 32) :
    (tau ++ List.replicate (32 - tau.length) z ++ j).getD i 0 =
      if i < tau.length then tau.getD i 0 else if i < 32 then z else j.getD (i - 32) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_append, List.length_replicate]
  by_cases h1 : i < tau.length
  · rw [if_pos (show i < tau.length + (32 - tau.length) by omega), if_pos h1, List.getElem?_append_left h1,
      List.getD_eq_getElem?_getD]
  · by_cases h2 : i < 32
    · rw [if_pos (show i < tau.length + (32 - tau.length) by omega), if_neg h1, if_pos h2,
        List.getElem?_append_right (show tau.length ≤ i by omega), List.getElem?_replicate,
        if_pos (show i - tau.length < 32 - tau.length by omega)]
      rfl
    · rw [if_neg (show ¬ i < tau.length + (32 - tau.length) by omega), if_neg h1, if_neg h2,
        List.getD_eq_getElem?_getD, show i - (tau.length + (32 - tau.length)) = i - 32 by omega]

/-- `indexWord`: the word `tau | j << 32` of the bits of `tau` and `j`. -/
theorem spIndexWord_good (tau j : List ℕ) (htau : tau.length ≤ 32) (hj : j.length ≤ 32) :
    Good (fun s => Wires tau s ∧ Wires j s) (Sphincs.Circuit.indexWord tau j) fun s r s' =>
      s'.statement = s.statement ∧ r < s'.next ∧ ∀ st val, Sat st s' val → ∀ a b : ℕ, a < 2 ^ tau.length →
        b < 2 ^ j.length → (∀ i < tau.length, (val (tau.getD i 0) 0 = 1 ↔ a.testBit i = true)) →
        (∀ i < j.length, (val (j.getD i 0) 0 = 1 ↔ b.testBit i = true)) → w64 val r = tw1 a b := by
  unfold Sphincs.Circuit.indexWord
  refine good_of_post fun s hs ⟨hwt, hwj⟩ => ?_
  refine ((kConst_good 0).pres (pres_kConst 0)).step hs trivial ?_
  rintro z s1 hi1 he1 ⟨hst1, hz, hzv⟩
  split
  · rename_i hemp
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hemp
    obtain ⟨rfl, rfl⟩ := hemp
    refine post_pure hi1 he1 ⟨hst1, hz, fun st val hsat a b ha hb _ _ => ?_⟩
    simp only [List.length_nil, pow_zero, Nat.lt_one_iff] at ha hb
    subst ha; subst hb
    rw [w64_const (hzv st val hsat)]
    rfl
  · refine ((pack_good _).pres (pres_pack _)).last hi1 ?_ he1 ?_
    · intro w hw
      simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · exact lt_mono (hwt w hw) he1
      · rw [List.eq_of_mem_replicate hw]; exact hz
      · exact lt_mono (hwj w hw) he1
    rintro r s2 he2 ⟨hst2, hr, hv⟩
    refine ⟨by omega, hr, fun st val hsat a b ha hb hta hjb => ?_⟩
    obtain ⟨-, hnum⟩ := hv st val hsat
    have hz0 : val z 0 = 0 := limb_zero (hzv st val (hsat.mono he2)) 0
    have ha32 : a < 2 ^ 32 := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) htau)
    have hb32 : b < 2 ^ 32 := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hj)
    have hL : (tau ++ List.replicate (32 - tau.length) z ++ j).length = 32 + j.length := by
      simp only [List.length_append, List.length_replicate]; omega
    rw [w64, hnum, tw1, Nat.mod_eq_of_lt ha32, Nat.mod_eq_of_lt hb32]
    apply congrArg (BitVec.ofNat 64)
    apply num_eq
    · generalize a = x at ha32 ⊢
      generalize b = y at hb32 ⊢
      omega
    intro i hi
    rw [ite_one, idx_getD tau j z i htau, hL, show a + b * 2 ^ 32 = 2 ^ 32 * b + a by ring,
      Nat.testBit_two_pow_mul_add _ ha32]
    by_cases h1 : i < tau.length
    · rw [if_pos h1, if_pos (show i < 32 by omega), hta i h1]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    · by_cases h2 : i < 32
      · rw [if_neg h1, if_pos h2, hz0, if_pos h2,
          Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))]
        exact ⟨fun h => absurd h.2 zero_ne_one, fun h => absurd h (by simp)⟩
      · rw [if_neg h1, if_neg h2, if_neg h2]
        by_cases h3 : i - 32 < j.length
        · rw [hjb _ h3]
          exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]
          exact ⟨fun h => absurd h.1 (by omega), fun h => absurd h (by simp)⟩

/-! A tweak hash and a level. -/

/-- `th`: the digest of `tw0 || tw1 || pp || payload`. -/
theorem th_good (tw0 tw1w : ℕ) (pp payload : List ℕ) (hlen : 8 * (2 + pp.length + payload.length) < 2 ^ 64) :
    Good (fun _ => True) (Sphincs.Circuit.th tw0 tw1w pp payload) fun s r s' => s'.statement = s.statement ∧
      r < s'.next ∧ ∀ st val, Sat st s' val →
        words4 (val r) = digest (hashWords ([BitVec.ofNat 64 tw0, w64 val tw1w] ++ (pp ++ payload).map (w64 val))) := by
  unfold Sphincs.Circuit.th
  refine good_of_post fun s hs _ => ?_
  refine ((kConst_good _).pres (pres_kConst _)).step hs trivial ?_
  rintro t s1 hi1 he1 ⟨hst1, -, htv⟩
  refine ((chain_good _ ?_).pres (pres_chain _)).last hi1 trivial he1 ?_
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rintro r s2 he2 ⟨hst2, hr, hv⟩
  refine ⟨by omega, hr, fun st val hsat => ?_⟩
  rw [hv st val hsat]
  simp only [List.map_append, List.map_cons, List.cons_append, List.nil_append,
    w64_const (htv st val (hsat.mono he2))]

/-- `level`: the hash of the current node and a sibling, on the side `bit` names. -/
theorem spLevel_good (tw0 tw1w bit node p0 p1 : ℕ) :
    Good (fun s => tw1w < s.next ∧ bit < s.next ∧ node < s.next ∧ p0 < s.next ∧ p1 < s.next)
      (Sphincs.Circuit.level tw0 tw1w bit node [p0, p1]) fun s r s' => s'.statement = s.statement ∧ r < s'.next ∧
        ∀ st val, Sat st s' val → ∃ sib : Dig, (val bit 0 = 0 ∨ val bit 0 = 1) →
          dig val r = if val bit 0 = 1 then
              Sphincs.Words.th (BitVec.ofNat 64 tw0, w64 val tw1w) (w64 val p0, w64 val p1)
                [sib.1, sib.2, (dig val node).1, (dig val node).2]
            else Sphincs.Words.th (BitVec.ofNat 64 tw0, w64 val tw1w) (w64 val p0, w64 val p1)
                [(dig val node).1, (dig val node).2, sib.1, sib.2] := by
  unfold Sphincs.Circuit.level
  refine good_of_post fun s hs ⟨htw, hbit, hnode, hp0, hp1⟩ => ?_
  refine ((dToEAndK_good node).pres (pres_dToEAndK node)).step hs (Wires.cons' hnode Wires.nil') ?_
  rintro ⟨cur, cur'⟩ s1 hi1 he1 ⟨hst1, hcur, -, hcurv⟩
  try dsimp only
  refine fresh_good'.step hi1 trivial ?_
  rintro sib s2 hi2 he2 ⟨hst2, hsib⟩
  refine ((add_good cur sib).pres (pres_add _ _)).step hi2
    (Wires.cons' (lt_mono hcur he2) (Wires.cons' hsib Wires.nil')) ?_
  rintro diff s3 hi3 he3 ⟨hst3, hdiff, hdiffv⟩
  refine ((mulKAdd_good diff bit cur).pres (pres_mulKAdd _ _ _)).step hi3
    (Wires.cons' hdiff (Wires.cons' (lt_mono hbit (by ext_chain))
      (Wires.cons' (lt_mono hcur (by ext_chain)) Wires.nil'))) ?_
  rintro left s4 hi4 he4 ⟨hst4, hleft, hleftv⟩
  refine ((add_good left diff).pres (pres_add _ _)).step hi4
    (Wires.cons' hleft (Wires.cons' (lt_mono hdiff he4) Wires.nil')) ?_
  rintro right s5 hi5 he5 ⟨hst5, hright, hrightv⟩
  refine (words_good left).step hi5 (Wires.cons' (lt_mono hleft he5) Wires.nil') ?_
  rintro ⟨l0, l1, l2⟩ s6 hi6 he6 ⟨hst6, hl0, hl1, -, hlv⟩
  try dsimp only
  refine (words_good right).step hi6 (Wires.cons' (lt_mono hright he6) Wires.nil') ?_
  rintro ⟨r0, r1, r2⟩ s7 hi7 he7 ⟨hst7, hr0, hr1, -, hrv⟩
  try dsimp only
  refine (th_good tw0 tw1w [p0, p1] [l0, l1, r0, r1] (by norm_num)).last hi7 trivial (by ext_chain) ?_
  rintro r s8 he8 ⟨hst8, hr, hrv8⟩
  refine ⟨by omega, hr, fun st val hsat => ⟨dig val sib, fun hb => ?_⟩⟩
  have hc : ∀ i : Fin 4, i.val < 3 → val cur i = val node i := (hcurv st val (hsat.mono (by ext_chain))).1
  have hcn : dig val cur = dig val node := dig_congr (hc 0 (by decide)) (hc 1 (by decide))
  obtain ⟨la0, la1, -, -⟩ := hlv st val (hsat.mono (by ext_chain))
  obtain ⟨ra0, ra1, -, -⟩ := hrv st val (hsat.mono he8)
  have hL : ev val left = ev val diff * emb (val bit 0) + ev val cur := hleftv st val (hsat.mono (by ext_chain))
  have hR : ev val right = ev val left + ev val diff := hrightv st val (hsat.mono (by ext_chain))
  have hD : ev val diff = ev val cur + ev val sib := hdiffv st val (hsat.mono (by ext_chain))
  have hw : ∀ (L R : ℕ), w64 val l0 = words4 (val L) 0 → w64 val l1 = words4 (val L) 1 →
      w64 val r0 = words4 (val R) 0 → w64 val r1 = words4 (val R) 1 →
      dig val r = Sphincs.Words.th (BitVec.ofNat 64 tw0, w64 val tw1w) (w64 val p0, w64 val p1)
        [(dig val L).1, (dig val L).2, (dig val R).1, (dig val R).2] := by
    intro L R h0 h1 h2 h3
    apply spDig_th
    rw [hrv8 st val hsat]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, h0, h1, h2, h3, dig]
  rcases hb with hb | hb
  · have hl : ev val left = ev val cur := by rw [hL, hb, Rec.emb_zero, mul_zero, zero_add]
    have hr' : ev val right = ev val sib := by rw [hR, hl, hD, ← add_assoc, add_self_E, zero_add]
    rw [if_neg (by rw [hb]; exact zero_ne_one), ← hcn, ← dig_of_ev hl, ← dig_of_ev hr']
    exact hw left right (w64_of la0) (w64_of la1) (w64_of ra0) (w64_of ra1)
  · have hl : ev val left = ev val sib := by
      rw [hL, hb, emb_one', mul_one, hD, add_assoc, add_comm (ev val sib), ← add_assoc, add_self_E, zero_add]
    have hr' : ev val right = ev val cur := by
      rw [hR, hl, hD, add_comm (ev val cur), ← add_assoc, add_self_E, zero_add]
    rw [if_pos hb, ← hcn, ← dig_of_ev hl, ← dig_of_ev hr']
    exact hw left right (w64_of la0) (w64_of la1) (w64_of ra0) (w64_of ra1)

/-- A level's hash is the specification's parent. -/
theorem parent_eq (ty lay tau e l : ℕ) (P N S : Dig) (b : K) (hbe : b = 1 ↔ e.testBit l = true) (T : W)
    (hT : T = tw1 tau (e / 2 ^ (l + 1))) :
    (if b = 1 then Sphincs.Words.th (BitVec.ofNat 64 (Sphincs.Circuit.tweak0 ty lay (l + 1)), T) P [S.1, S.2, N.1, N.2]
      else Sphincs.Words.th (BitVec.ofNat 64 (Sphincs.Circuit.tweak0 ty lay (l + 1)), T) P [N.1, N.2, S.1, S.2]) =
      Sphincs.Words.parent ty lay tau e l P N S := by
  subst hT
  simp only [Sphincs.Words.parent, tweak_eq]
  by_cases h : b = 1
  · rw [if_pos h, if_pos (hbe.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hbe.mpr h'))]

/-! A climb. -/

/-- `fold`: the leaf climbed to its tree's root, the leaf index's bits naming the sides. -/
theorem fold_good (ty lay : ℕ) (tauBits jBits : List ℕ) (top p0 p1 leaf : ℕ) (htau : tauBits.length ≤ 32)
    (hj : jBits.length ≤ 32) :
    Good (fun s => Wires tauBits s ∧ Wires jBits s ∧ top < s.next ∧ p0 < s.next ∧ p1 < s.next ∧ leaf < s.next)
      (Sphincs.Circuit.fold ty lay tauBits jBits top [p0, p1] leaf) fun s r s' => s'.statement = s.statement ∧
        r < s'.next ∧ ∀ st val, Sat st s' val → ∀ tau e : ℕ, tau < 2 ^ tauBits.length → e < 2 ^ jBits.length →
          (∀ i < tauBits.length, (val (tauBits.getD i 0) 0 = 1 ↔ tau.testBit i = true)) →
          (∀ i < jBits.length, (val (jBits.getD i 0) 0 = 1 ↔ e.testBit i = true)) →
          (∀ i < jBits.length, val (jBits.getD i 0) 0 = 0 ∨ val (jBits.getD i 0) 0 = 1) →
          w64 val top = tw1 tau 0 →
          ∃ path : ℕ → Dig, dig val r = (List.range jBits.length).foldl
            (fun c l => Sphincs.Words.parent ty lay tau e l (w64 val p0, w64 val p1) c (path l)) (dig val leaf) := by
  unfold Sphincs.Circuit.fold
  refine good_of_post fun s hs ⟨hwt, hwj, htop, hp0, hp1, hleaf⟩ => ?_
  refine post_bind (forIn_range_post jBits.length _ (fun k node s' => s'.statement = s.statement ∧
      node < s'.next ∧ ∀ st val, Sat st s' val → ∀ tau e : ℕ, tau < 2 ^ tauBits.length → e < 2 ^ jBits.length →
        (∀ i < tauBits.length, (val (tauBits.getD i 0) 0 = 1 ↔ tau.testBit i = true)) →
        (∀ i < jBits.length, (val (jBits.getD i 0) 0 = 1 ↔ e.testBit i = true)) →
        (∀ i < jBits.length, val (jBits.getD i 0) 0 = 0 ∨ val (jBits.getD i 0) 0 = 1) →
        w64 val top = tw1 tau 0 →
        ∃ path : ℕ → Dig, dig val node = (List.range k).foldl
          (fun c l => Sphincs.Words.parent ty lay tau e l (w64 val p0, w64 val p1) c (path l)) (dig val leaf)) hs
      ⟨rfl, hleaf, fun _ _ _ _ _ _ _ _ _ _ _ => ⟨fun _ => (0, 0), rfl⟩⟩ ?_) ?_
  · rintro l hl node s1 hi1 he1 ⟨hst1, hnode, hv1⟩
    -- The level, from a tweak word of the right value.
    have common : ∀ (tw : ℕ) (s2 : State), Rec.Model.Inv s2 → Ext s1 s2 → s2.statement = s1.statement →
        tw < s2.next → (∀ st val, Sat st s2 val → ∀ tau e : ℕ, tau < 2 ^ tauBits.length →
          e < 2 ^ jBits.length → (∀ i < tauBits.length, (val (tauBits.getD i 0) 0 = 1 ↔ tau.testBit i = true)) →
          (∀ i < jBits.length, (val (jBits.getD i 0) 0 = 1 ↔ e.testBit i = true)) → w64 val top = tw1 tau 0 →
          w64 val tw = tw1 tau (e / 2 ^ (l + 1))) →
        Post s1 (fun _ r s' => ∃ b', r = ForInStep.yield b' ∧ s'.statement = s.statement ∧ b' < s'.next ∧
          ∀ st val, Sat st s' val → ∀ tau e : ℕ, tau < 2 ^ tauBits.length → e < 2 ^ jBits.length →
            (∀ i < tauBits.length, (val (tauBits.getD i 0) 0 = 1 ↔ tau.testBit i = true)) →
            (∀ i < jBits.length, (val (jBits.getD i 0) 0 = 1 ↔ e.testBit i = true)) →
            (∀ i < jBits.length, val (jBits.getD i 0) 0 = 0 ∨ val (jBits.getD i 0) 0 = 1) →
            w64 val top = tw1 tau 0 →
            ∃ path : ℕ → Dig, dig val b' = (List.range (l + 1)).foldl
              (fun c l => Sphincs.Words.parent ty lay tau e l (w64 val p0, w64 val p1) c (path l)) (dig val leaf))
          (((Sphincs.Circuit.level (Sphincs.Circuit.tweak0 ty lay (l + 1)) tw (jBits.getD l 0) node [p0, p1] >>=
            fun node => pure (ForInStep.yield node)) : M (ForInStep ℕ)).run s2) := by
      intro tw s2 hi2 he2 hst2 htw htwv
      refine (spLevel_good _ tw _ node p0 p1).step hi2 ⟨htw, lt_mono (wires_getD' hwj hl) (by ext_chain),
        lt_mono hnode he2, lt_mono hp0 (by ext_chain), lt_mono hp1 (by ext_chain)⟩ ?_
      rintro node' s3 hi3 he3 ⟨hst3, hnode', hv3⟩
      refine post_pure hi3 (by ext_chain) ⟨node', rfl, by omega, hnode',
        fun st val hsat tau e hta hte htb heb hbb htop' => ?_⟩
      obtain ⟨path, hpath⟩ := hv1 st val (hsat.mono (by ext_chain)) tau e hta hte htb heb hbb htop'
      obtain ⟨sib, hsib⟩ := hv3 st val hsat
      have htw' := htwv st val (hsat.mono he3) tau e hta hte htb heb htop'
      refine ⟨fun j => if j = l then sib else path j, ?_⟩
      rw [hsib (hbb l hl), parent_eq ty lay tau e l _ _ _ _ (heb l hl) _ htw', List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      beta_reduce
      rw [if_pos rfl, hpath,
        foldl_range_congr (g := fun c j => Sphincs.Words.parent ty lay tau e j (w64 val p0, w64 val p1) c
          (if j = l then sib else path j)) fun c j hj => by rw [if_neg (show ¬ j = l by omega)]]
    try dsimp only
    split
    · rename_i hlt
      refine (spIndexWord_good tauBits (jBits.drop (l + 1)) htau (by simp only [List.length_drop]; omega)).step hi1
        ⟨hwt.mono he1, fun w hw => lt_mono (hwj w (List.mem_of_mem_drop hw)) he1⟩ ?_
      rintro tw s2 hi2 he2 ⟨hst2, htw, htwv⟩
      refine common tw s2 hi2 he2 hst2 htw fun st val hsat tau e hta hte htb heb _ => ?_
      apply htwv st val hsat tau (e / 2 ^ (l + 1)) hta
      · rw [List.length_drop, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
          show jBits.length - (l + 1) + (l + 1) = jBits.length by omega]
        exact hte
      · exact htb
      · intro i hi
        rw [List.length_drop] at hi
        rw [Nat.testBit_div_two_pow, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          show l + 1 + i = i + (l + 1) by omega]
        exact heb _ (by omega)
    · rename_i hlt
      refine (pure_good top).step hi1 trivial ?_
      rintro r s2 hi2 he2 ⟨hst2, hr, hs2⟩
      rw [hr, hs2]
      refine common top s1 hi1 (Ext.refl _) rfl (lt_mono htop he1) fun st val hsat tau e hta hte htb heb htop' => ?_
      rw [htop', Nat.div_eq_of_lt (lt_of_lt_of_le hte (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · rintro node s1 hi1 he1 ⟨hst1, hnode, hv1⟩
    exact post_pure hi1 he1 ⟨hst1, hnode, hv1⟩

/-! A chain. -/

/-- Chain `i` of layer `lay` at position `p`, from `T` at position `x`. -/
def spCpart (lay tau e i : ℕ) (P : Dig) (x : ℕ) (T : Dig) (p : ℕ) : Dig :=
  (List.range' x (p - x)).foldl (fun v s => Sphincs.Words.chainStep lay tau e i s P v) T

theorem spCpart_self (lay tau e i : ℕ) (P : Dig) (x : ℕ) (T : Dig) : spCpart lay tau e i P x T x = T := by
  simp [spCpart]

theorem spCpart_succ (lay tau e i : ℕ) (P : Dig) (x : ℕ) (T : Dig) (p : ℕ) (hx : x ≤ p) :
    spCpart lay tau e i P x T (p + 1) = Sphincs.Words.chainStep lay tau e i p P (spCpart lay tau e i P x T p) := by
  unfold spCpart
  rw [show p + 1 - x = p - x + 1 by omega, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    show x + 1 * (p - x) = p by omega]

/-- The digest of a chain step's hash. -/
theorem spStep_dig {val : Val} {d tw p0 p1 v0 v1 lay i s tau e : ℕ} {V : Dig}
    (hdv : words4 (val d) = digest (hashWords ([BitVec.ofNat 64 (Sphincs.Circuit.tweak0 1 lay (8 * i + s)), w64 val tw] ++
      ([p0, p1] ++ [v0, v1]).map (w64 val))))
    (htw : w64 val tw = tw1 tau e) (h0 : w64 val v0 = V.1) (h1 : w64 val v1 = V.2) :
    dig val d = Sphincs.Words.chainStep lay tau e i s (w64 val p0, w64 val p1) V := by
  apply spDig_th
  rw [hdv]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, htw, h0, h1, tweak_eq]

/-- `chainEnd`: chain `i` of layer `lay` from the element `tip` at the digit `x` to position 7. -/
theorem spChainEnd_good (lay i tw tip p0 p1 : ℕ) (ind : List ℕ) :
    Good (fun s => tw < s.next ∧ tip < s.next ∧ p0 < s.next ∧ p1 < s.next ∧ Wires ind s ∧ ind.length = 8)
      (Sphincs.Circuit.chainEnd lay i tw tip [p0, p1] ind) fun s r s' => s'.statement = s.statement ∧ r.1 < s'.next ∧
        r.2 < s'.next ∧ ∀ st val, Sat st s' val → ∀ x < 8, ∀ tau e : ℕ,
          (∀ v < 8, ev val (ind.getD v 0) = if v = x then 1 else 0) → w64 val tw = tw1 tau e →
            (w64 val r.1, w64 val r.2) = Sphincs.Words.chainFrom lay tau e i (w64 val p0, w64 val p1) x (dig val tip) := by
  unfold Sphincs.Circuit.chainEnd
  refine good_of_post fun s hs ⟨htwn, htip, hp0, hp1, hind, hlen⟩ => ?_
  refine (words_good tip).step hs (Wires.cons' htip Wires.nil') ?_
  rintro ⟨t0, t1, t2⟩ s1 hi1 he1 ⟨hst1, ht0, ht1, -, htv⟩
  try dsimp only
  refine (th_good (Sphincs.Circuit.tweak0 1 lay (8 * i)) tw [p0, p1] [t0, t1] (by norm_num)).step hi1 trivial ?_
  rintro d s2 hi2 he2 ⟨hst2, hd, hdv⟩
  refine ((dToEAndK_good d).pres (pres_dToEAndK d)).step hi2 (Wires.cons' hd Wires.nil') ?_
  rintro ⟨o, o'⟩ s3 hi3 he3 ⟨hst3, ho, -, hov⟩
  try dsimp only
  refine post_bind (forIn_range'_post 6 _ (fun k cur s' => s'.statement = s.statement ∧ cur < s'.next ∧
      ∀ st val, Sat st s' val → ∀ x < 8, ∀ tau e : ℕ, (∀ v < 8, ev val (ind.getD v 0) = if v = x then 1 else 0) →
        w64 val tw = tw1 tau e → x ≤ k →
          dig val cur = spCpart lay tau e i (w64 val p0, w64 val p1) x (dig val tip) (k + 1)) hi3
      ⟨by omega, ho, fun st val hsat x hx tau e hi he hxk => ?_⟩ ?_) ?_
  · obtain rfl : x = 0 := by omega
    have h0 : ∀ i : Fin 4, i.val < 3 → val o i = val d i := (hov st val hsat).1
    rw [dig_congr (h0 0 (by decide)) (h0 1 (by decide)), spCpart_succ _ _ _ _ _ _ _ _ le_rfl, spCpart_self]
    obtain ⟨a0, a1, -, -⟩ := htv st val (hsat.mono (by ext_chain))
    exact spStep_dig (s := 0) (V := dig val tip) (hdv st val (hsat.mono he3)) he (w64_of a0) (w64_of a1)
  · rintro k hk cur s4 hi4 he4 ⟨hst4, hcur, hv4⟩
    have hik : ind.getD (k + 1) 0 < s4.next := lt_mono (wires_getD' hind (by omega)) (by ext_chain)
    refine ((add_good tip cur).pres (pres_add _ _)).step hi4
      (Wires.cons' (lt_mono htip (by ext_chain)) (Wires.cons' hcur Wires.nil')) ?_
    rintro diff s5 hi5 he5 ⟨hst5, hdiff, hdiffv⟩
    refine ((mulAdd_good _ diff cur).pres (pres_mulAdd _ _ _)).step hi5
      (Wires.cons' (lt_mono hik he5) (Wires.cons' hdiff (Wires.cons' (lt_mono hcur he5) Wires.nil'))) ?_
    rintro m s6 hi6 he6 ⟨hst6, hm, hmv⟩
    refine (words_good m).step hi6 (Wires.cons' hm Wires.nil') ?_
    rintro ⟨v0, v1, v2⟩ s7 hi7 he7 ⟨hst7, hv0, hv1, -, hvv⟩
    try dsimp only
    refine (th_good (Sphincs.Circuit.tweak0 1 lay (8 * i + (k + 1))) tw [p0, p1] [v0, v1] (by norm_num)).step hi7 trivial ?_
    rintro d' s8 hi8 he8 ⟨hst8, hd', hdv'⟩
    refine ((dToEAndK_good d').pres (pres_dToEAndK d')).step hi8 (Wires.cons' hd' Wires.nil') ?_
    rintro ⟨o2, o2'⟩ s9 hi9 he9 ⟨hst9, ho2, -, hov2⟩
    try dsimp only
    refine post_pure hi9 (by ext_chain) ⟨o2, rfl, by omega, ho2, fun st val hsat x hx tau e hi he hxk => ?_⟩
    have h0 : ∀ i : Fin 4, i.val < 3 → val o2 i = val d' i := (hov2 st val hsat).1
    rw [dig_congr (h0 0 (by decide)) (h0 1 (by decide)), spCpart_succ _ _ _ _ _ _ _ _ hxk]
    obtain ⟨a0, a1, -, -⟩ := hvv st val (hsat.mono (by ext_chain))
    rw [spStep_dig (V := dig val m) (hdv' st val (hsat.mono he9)) he (w64_of a0) (w64_of a1)]
    apply congrArg (Sphincs.Words.chainStep lay tau e i (k + 1) _)
    have hmev : ev val m = if k + 1 = x then ev val tip else ev val cur := by
      rw [hmv st val (hsat.mono (by ext_chain)), hdiffv st val (hsat.mono (by ext_chain))]
      exact mux_ev _ _ _ _ (hi (k + 1) (by omega))
    split_ifs at hmev with hkx
    · rw [dig_of_ev hmev, ← hkx, spCpart_self]
    · rw [dig_of_ev hmev]
      exact hv4 st val (hsat.mono (by ext_chain)) x hx tau e hi he (by omega)
  · rintro cur s4 hi4 he4 ⟨hst4, hcur, hv4⟩
    have hik : ind.getD 7 0 < s4.next := lt_mono (wires_getD' hind (by omega)) (by ext_chain)
    refine ((add_good tip cur).pres (pres_add _ _)).step hi4
      (Wires.cons' (lt_mono htip (by ext_chain)) (Wires.cons' hcur Wires.nil')) ?_
    rintro diff s5 hi5 he5 ⟨hst5, hdiff, hdiffv⟩
    refine ((mulAdd_good _ diff cur).pres (pres_mulAdd _ _ _)).step hi5
      (Wires.cons' (lt_mono hik he5) (Wires.cons' hdiff (Wires.cons' (lt_mono hcur he5) Wires.nil'))) ?_
    rintro m s6 hi6 he6 ⟨hst6, hm, hmv⟩
    refine (words_good m).step hi6 (Wires.cons' hm Wires.nil') ?_
    rintro ⟨n0, n1, n2⟩ s7 hi7 he7 ⟨hst7, hn0, hn1, -, hnv⟩
    try dsimp only
    refine post_pure hi7 (by ext_chain) ⟨by omega, hn0, hn1, fun st val hsat x hx tau e hi he => ?_⟩
    obtain ⟨a0, a1, -, -⟩ := hnv st val hsat
    have a0' : val n0 0 = val m 0 := a0
    have a1' : val n1 0 = val m 1 := a1
    show (w64 val n0, w64 val n1) = spCpart lay tau e i (w64 val p0, w64 val p1) x (dig val tip) 7
    rw [w64_of a0', w64_of a1']
    show dig val m = spCpart lay tau e i (w64 val p0, w64 val p1) x (dig val tip) 7
    have hmev : ev val m = if 7 = x then ev val tip else ev val cur := by
      rw [hmv st val (hsat.mono he7), hdiffv st val (hsat.mono (by ext_chain))]
      exact mux_ev _ _ _ _ (hi 7 (by omega))
    split_ifs at hmev with hkx
    · rw [dig_of_ev hmev, ← hkx, spCpart_self]
    · rw [dig_of_ev hmev]
      exact hv4 st val (hsat.mono (by ext_chain)) x hx tau e hi he (by omega)

/-! The few-time key. -/

theorem getD_drop' (l : List ℕ) (s i : ℕ) : (l.drop s).getD i 0 = l.getD (s + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem getD_take' (l : List ℕ) (h i : ℕ) (hi : i < h) : (l.take h).getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD]

/-- `fts`: the few-time key of the fourteen trees' roots, each a secret's leaf climbed ten levels. -/
theorem fts_good (idxBits : List ℕ) (us : List (List ℕ)) (top p0 p1 : ℕ) (hidx : idxBits.length = 26)
    (hus : ∀ κ < 14, (us.getD κ []).length = 10) :
    Good (fun s => Wires idxBits s ∧ (∀ κ < 14, Wires (us.getD κ []) s) ∧ top < s.next ∧ p0 < s.next ∧ p1 < s.next)
      (Sphincs.Circuit.fts idxBits us top [p0, p1]) fun s r s' => s'.statement = s.statement ∧ r < s'.next ∧
        ∀ st val, Sat st s' val → ∀ (idx : ℕ) (u : ℕ → ℕ), idx < 2 ^ 26 →
          (∀ i < 26, (val (idxBits.getD i 0) 0 = 1 ↔ idx.testBit i = true)) →
          (∀ κ < 14, u κ < 2 ^ 10 ∧ (∀ i < 10, (val ((us.getD κ []).getD i 0) 0 = 1 ↔ (u κ).testBit i = true)) ∧
            ∀ i < 10, val ((us.getD κ []).getD i 0) 0 = 0 ∨ val ((us.getD κ []).getD i 0) 0 = 1) →
          w64 val top = tw1 idx 0 →
          ∃ (secrets : ℕ → Dig) (paths : ℕ → ℕ → Dig), dig val r =
            Sphincs.Words.th (Sphincs.Words.tweak 11 0 idx 0 0) (w64 val p0, w64 val p1)
              ((List.ofFn fun κ : Fin 14 => Sphincs.Words.ftsRoot idx κ (u κ) (w64 val p0, w64 val p1) (secrets κ)
                (fun l => paths κ l)).flatMap fun d => [d.1, d.2]) := by
  unfold Sphincs.Circuit.fts
  refine good_of_post fun s hs ⟨hwi, hwu, htop, hp0, hp1⟩ => ?_
  refine post_bind (forIn_range_post 14 _ (fun k (roots : List ℕ) s' => s'.statement = s.statement ∧
      roots.length = 2 * k ∧ Wires roots s' ∧ ∀ st val, Sat st s' val → ∀ (idx : ℕ) (u : ℕ → ℕ), idx < 2 ^ 26 →
        (∀ i < 26, (val (idxBits.getD i 0) 0 = 1 ↔ idx.testBit i = true)) →
        (∀ κ < 14, u κ < 2 ^ 10 ∧ (∀ i < 10, (val ((us.getD κ []).getD i 0) 0 = 1 ↔ (u κ).testBit i = true)) ∧
          ∀ i < 10, val ((us.getD κ []).getD i 0) 0 = 0 ∨ val ((us.getD κ []).getD i 0) 0 = 1) →
        w64 val top = tw1 idx 0 →
        ∃ (secrets : ℕ → Dig) (paths : ℕ → ℕ → Dig), roots.map (w64 val) = (List.range k).flatMap fun κ =>
          [(Sphincs.Words.ftsRoot idx κ (u κ) (w64 val p0, w64 val p1) (secrets κ) (fun l => paths κ l)).1,
           (Sphincs.Words.ftsRoot idx κ (u κ) (w64 val p0, w64 val p1) (secrets κ) (fun l => paths κ l)).2]) hs
      ⟨rfl, rfl, Wires.nil', fun _ _ _ _ _ _ _ _ _ => ⟨fun _ => (0, 0), fun _ _ => (0, 0), rfl⟩⟩ ?_) ?_
  · rintro κ hκ roots s1 hi1 he1 ⟨hst1, hlen1, hw1, hv1⟩
    refine fresh_good'.step hi1 trivial ?_
    rintro secret s2 hi2 he2 ⟨hst2, hsec⟩
    refine (words_good secret).step hi2 (Wires.cons' hsec Wires.nil') ?_
    rintro ⟨a0w, a1w, a2w⟩ s3 hi3 he3 ⟨hst3, ha0, ha1, -, hav⟩
    try dsimp only
    refine (spIndexWord_good idxBits (us.getD κ []) (by omega) (by rw [hus κ hκ]; omega)).step hi3
      ⟨hwi.mono (by ext_chain), (hwu κ hκ).mono (by ext_chain)⟩ ?_
    rintro tw s4 hi4 he4 ⟨hst4, htw, htwv⟩
    refine (th_good (Sphincs.Circuit.tweak0 9 κ 0) tw [p0, p1] [a0w, a1w] (by norm_num)).step hi4 trivial ?_
    rintro leaf s5 hi5 he5 ⟨hst5, hleaf, hleafv⟩
    refine (fold_good 10 κ idxBits (us.getD κ []) top p0 p1 leaf (by omega) (by rw [hus κ hκ]; omega)).step hi5
      ⟨hwi.mono (by ext_chain), (hwu κ hκ).mono (by ext_chain), lt_mono htop (by ext_chain),
        lt_mono hp0 (by ext_chain), lt_mono hp1 (by ext_chain), hleaf⟩ ?_
    rintro root s6 hi6 he6 ⟨hst6, hroot, hrootv⟩
    refine ((dToK_good root).pres (pres_dToK root)).step hi6 (Wires.cons' hroot Wires.nil') ?_
    rintro rs s7 hi7 he7 ⟨hst7, hrs, hrsv⟩
    refine post_pure hi7 (by ext_chain) ⟨roots ++ [rs.getD 0 0, rs.getD 1 0], rfl, by omega,
      by simp only [List.length_append, hlen1, List.length_cons, List.length_nil]; ring, fun w hw => ?_,
      fun st val hsat idx u hidx' hib hub htop' => ?_⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hw | rfl | rfl
      · exact lt_mono (hw1 w hw) (by ext_chain)
      · exact hrs 0 (by omega)
      · exact hrs 1 (by omega)
    · obtain ⟨secrets, paths, hroots⟩ := hv1 st val (hsat.mono (by ext_chain)) idx u hidx' hib hub htop'
      obtain ⟨hu, hubits, hubool⟩ := hub κ hκ
      have hlenu := hus κ hκ
      have htw' : w64 val tw = tw1 idx (u κ) :=
        htwv st val (hsat.mono (by ext_chain)) idx (u κ) (by rw [hidx]; exact hidx') (by rw [hlenu]; exact hu)
          (by rw [hidx]; exact hib) (by rw [hlenu]; exact hubits)
      obtain ⟨b0, b1, -, -⟩ := hav st val (hsat.mono (by ext_chain))
      have hleafd : dig val leaf = Sphincs.Words.th (Sphincs.Words.tweak 9 κ idx 0 (u κ)) (w64 val p0, w64 val p1)
          [(dig val secret).1, (dig val secret).2] := by
        apply spDig_th
        rw [hleafv st val (hsat.mono (by ext_chain)), htw']
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, tweak_eq, w64_of b0, w64_of b1, dig]
      obtain ⟨path, hpath⟩ := hrootv st val (hsat.mono (by ext_chain)) idx (u κ) (by rw [hidx]; exact hidx')
        (by rw [hlenu]; exact hu) (by rw [hidx]; exact hib) (by rw [hlenu]; exact hubits) (by rw [hlenu]; exact hubool)
        htop'
      rw [hlenu] at hpath
      have hfr : Sphincs.Words.ftsRoot idx κ (u κ) (w64 val p0, w64 val p1) (dig val secret) (fun l => path l) =
          dig val root := by
        unfold Sphincs.Words.ftsRoot
        rw [sp_climb_eq, ← hleafd, hpath]
      have h0 : val (rs.getD 0 0) 0 = val root 0 := hrsv st val hsat 0
      have h1 : val (rs.getD 1 0) 0 = val root 1 := hrsv st val hsat 1
      refine ⟨fun j => if j = κ then dig val secret else secrets j, fun j => if j = κ then path else paths j, ?_⟩
      rw [List.map_append, hroots, List.range_succ, List.flatMap_append,
        flatMap_range_congr (g := fun j =>
          [(Sphincs.Words.ftsRoot idx j (u j) (w64 val p0, w64 val p1) (if j = κ then dig val secret else secrets j)
            (fun l => (if j = κ then path else paths j) l)).1,
           (Sphincs.Words.ftsRoot idx j (u j) (w64 val p0, w64 val p1) (if j = κ then dig val secret else secrets j)
            (fun l => (if j = κ then path else paths j) l)).2])
          fun j hj => by rw [if_neg (show ¬ j = κ by omega), if_neg (show ¬ j = κ by omega)]]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, if_true]
      rw [hfr, w64_of h0, w64_of h1]
      rfl
  · rintro roots s1 hi1 he1 ⟨hst1, hlen1, hw1, hv1⟩
    have hb : 8 * (2 + [p0, p1].length + roots.length) < 2 ^ 64 := by
      simp only [hlen1, List.length_cons, List.length_nil]; norm_num
    refine (th_good (Sphincs.Circuit.tweak0 11 0 0) top [p0, p1] roots hb).last hi1 trivial he1 ?_
    rintro r s2 he2 ⟨hst2, hr, hrv⟩
    refine ⟨by omega, hr, fun st val hsat idx u hidx' hib hub htop' => ?_⟩
    obtain ⟨secrets, paths, hroots⟩ := hv1 st val (hsat.mono he2) idx u hidx' hib hub htop'
    refine ⟨secrets, paths, ?_⟩
    have hF := ofFn_flatMap' 14 (fun κ => Sphincs.Words.ftsRoot idx κ (u κ) (w64 val p0, w64 val p1) (secrets κ)
      (fun l => paths κ l))
    beta_reduce at hF
    apply spDig_th
    rw [hrv st val hsat, hF, ← hroots, tweak_eq, ← htop']
    simp only [List.map_cons, List.cons_append, List.nil_append]

/-! A layer. -/

theorem block8 (a b c d e f g : W) : Rec.block [a, b, c, d, e, f, g, 0] 0 = Rec.block [a, b, c, d, e, f, g] 0 := by
  apply Vector.ext
  intro r hr
  simp only [Rec.block, Vector.getElem_ofFn, Rec.wordAt]
  interval_cases r <;> rfl

theorem blake2s_one (ll : BitVec 64) (m : Vector (BitVec 32) 16) :
    Rec.blake2s256 ll m [] = Blake2s.Rfc7693.F Rec.paramIV m ll true := rfl

theorem layer_consts (lay : ℕ) (hlay : lay < 3) :
    Sphincs.Circuit.suffix (lay + 1) + Sphincs.Circuit.height lay = Sphincs.Circuit.suffix lay ∧
      Sphincs.Circuit.suffix lay ≤ 26 := by
  interval_cases lay <;> decide

/-- The bits of `idx >> s`. -/
theorem tau_bits (idxBits : List ℕ) (val : Val) (idx s : ℕ) (hs : s ≤ 26) (hidx : idxBits.length = 26)
    (hlt : idx < 2 ^ 26) (hib : ∀ i < 26, (val (idxBits.getD i 0) 0 = 1 ↔ idx.testBit i = true)) :
    idx / 2 ^ s < 2 ^ (idxBits.drop s).length ∧
      ∀ i < (idxBits.drop s).length, (val ((idxBits.drop s).getD i 0) 0 = 1 ↔ (idx / 2 ^ s).testBit i = true) := by
  rw [List.length_drop, hidx]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 26 - s + s = 26 by omega]
    exact hlt
  · rw [getD_drop', Nat.testBit_div_two_pow, show i + s = s + i by omega]
    exact hib _ (by omega)

/-- The bits of `(idx >> s) mod 2^h`. -/
theorem e_bits (idxBits : List ℕ) (val : Val) (idx s h : ℕ) (hsh : s + h ≤ 26) (hidx : idxBits.length = 26)
    (hib : ∀ i < 26, (val (idxBits.getD i 0) 0 = 1 ↔ idx.testBit i = true))
    (hbool : ∀ i < 26, val (idxBits.getD i 0) 0 = 0 ∨ val (idxBits.getD i 0) 0 = 1) :
    ((idxBits.drop s).take h).length = h ∧ idx / 2 ^ s % 2 ^ h < 2 ^ ((idxBits.drop s).take h).length ∧
      (∀ i < ((idxBits.drop s).take h).length,
        (val (((idxBits.drop s).take h).getD i 0) 0 = 1 ↔ (idx / 2 ^ s % 2 ^ h).testBit i = true)) ∧
      ∀ i < ((idxBits.drop s).take h).length,
        val (((idxBits.drop s).take h).getD i 0) 0 = 0 ∨ val (((idxBits.drop s).take h).getD i 0) 0 = 1 := by
  have hl : ((idxBits.drop s).take h).length = h := by
    simp only [List.length_take, List.length_drop, hidx]; omega
  rw [hl]
  refine ⟨rfl, Nat.mod_lt _ (by positivity), fun i hi => ?_, fun i hi => ?_⟩
  · rw [getD_take' _ _ _ hi, getD_drop', Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
      Nat.testBit_div_two_pow, show i + s = s + i by omega]
    exact hib _ (by omega)
  · rw [getD_take' _ _ _ hi, getD_drop']
    exact hbool _ (by omega)

theorem ctr_lt {val : Val} {ctr : ℕ} {cb : List ℕ} (hlen : cb.length = 64)
    (hnum : toWord (val ctr 0) = num (fun i => if val (cb.getD i 0) 0 = 1 then 1 else 0) 64)
    (hz : ∀ k ∈ cb.drop 32, val k = limbsOf [0, 0, 0, 0]) : (w64 val ctr).toNat < 2 ^ 32 := by
  rw [w64_toNat]
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases h64 : i < 64
  · have h0 : val (cb.getD i 0) 0 = 0 := limb_zero (hz _ (getD_mem_drop hlen hi h64)) 0
    cases hb : (toWord (val ctr 0)).testBit i
    · rfl
    · have := (testBit_split hnum i h64).mp hb; rw [h0] at this; exact absurd this zero_ne_one
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (toWord_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- `layer`: layer `lay`'s root from the message it signs, under the counter, chain elements and path read off
the assignment. -/
theorem layer_good (lay : ℕ) (hlay : lay < 3) (idxBits : List ℕ) (p0 p1 msg : ℕ) (hidx : idxBits.length = 26) :
    Good (fun s => Wires idxBits s ∧ p0 < s.next ∧ p1 < s.next ∧ msg < s.next)
      (Sphincs.Circuit.layer lay idxBits [p0, p1] msg) fun s r s' => s'.statement = s.statement ∧ r < s'.next ∧
        ∀ st val, Sat st s' val → ∀ idx : ℕ, idx < 2 ^ 26 →
          (∀ i < 26, (val (idxBits.getD i 0) 0 = 1 ↔ idx.testBit i = true)) →
          (∀ i < 26, val (idxBits.getD i 0) 0 = 0 ∨ val (idxBits.getD i 0) 0 = 1) →
          ∃ (ctr : W) (tips : ℕ → Dig) (path : ℕ → Dig), ∀ sig : Sphincs.Words.Sig,
            sig.counters ⟨lay, hlay⟩ = ctr → (∀ i : Fin 42, sig.tips ⟨lay, hlay⟩ i = tips i) →
            (∀ l (hl : l < Sphincs.Words.height ⟨lay, hlay⟩), sig.paths ⟨lay, hlay⟩ ⟨l, hl⟩ = path l) →
            Sphincs.Words.layerRoot (w64 val p0, w64 val p1) idx sig (dig val msg) ⟨lay, hlay⟩ =
              some (dig val r) := by
  obtain ⟨hsuf, hs26⟩ := layer_consts lay hlay
  have htBlen : (idxBits.drop (Sphincs.Circuit.suffix lay)).length = 26 - Sphincs.Circuit.suffix lay := by
    simp only [List.length_drop, hidx]
  have heBlen : ((idxBits.drop (Sphincs.Circuit.suffix (lay + 1))).take (Sphincs.Circuit.height lay)).length =
      Sphincs.Circuit.height lay := by
    simp only [List.length_take, List.length_drop, hidx]; omega
  unfold Sphincs.Circuit.layer
  refine good_of_post fun s hs ⟨hwi, hp0, hp1, hmsg⟩ => ?_
  have hwt : ∀ s', Ext s s' → Wires (idxBits.drop (Sphincs.Circuit.suffix lay)) s' :=
    fun s' he w hw => lt_mono (hwi w (List.mem_of_mem_drop hw)) he
  have hwe : ∀ s', Ext s s' →
      Wires ((idxBits.drop (Sphincs.Circuit.suffix (lay + 1))).take (Sphincs.Circuit.height lay)) s' :=
    fun s' he w hw => lt_mono (hwi w (List.mem_of_mem_drop (List.mem_of_mem_take hw))) he
  refine ((kConst_good 0).pres (pres_kConst 0)).step hs trivial ?_
  rintro z s1 hi1 he1 ⟨hst1, hz, hzv⟩
  refine (spIndexWord_good _ _ (by rw [htBlen]; omega) (by rw [heBlen]; omega)).step hi1 ⟨hwt s1 he1, hwe s1 he1⟩ ?_
  rintro key s2 hi2 he2 ⟨hst2, hkey, hkeyv⟩
  refine (spIndexWord_good _ [] (by rw [htBlen]; omega) (by simp)).step hi2 ⟨hwt s2 (by ext_chain), Wires.nil'⟩ ?_
  rintro top s3 hi3 he3 ⟨hst3, htop, htopv⟩
  refine ((dToK_good msg).pres (pres_dToK msg)).step hi3 (Wires.cons' (lt_mono hmsg (by ext_chain)) Wires.nil') ?_
  rintro ms s4 hi4 he4 ⟨hst4, hms, hmsv⟩
  refine fresh_good'.step hi4 trivial ?_
  rintro ctr s5 hi5 he5 ⟨hst5, hctr⟩
  refine ((split_good ctr).pres (pres_split ctr)).step hi5 trivial ?_
  rintro cb s6 hi6 he6 ⟨hst6, hcblen, hcbw, hcbv⟩
  refine (zeros_good _).step hi6 trivial ?_
  rintro _ s7 hi7 he7 ⟨hst7, hcbz⟩
  refine ((kConst_good _).pres (pres_kConst _)).step hi7 trivial ?_
  rintro tw0 s8 hi8 he8 ⟨hst8, htw0, htw0v⟩
  refine ((dConst_good _).pres (pres_constant _ _)).step hi8 trivial ?_
  rintro h s9 hi9 he9 ⟨hst9, hh, hhv⟩
  refine ((leafBlock_good h _ 52 true (by simp) (by norm_num)).pres (pres_leafBlock _ _ _ _)).step hi9 trivial ?_
  rintro d s10 hi10 he10 ⟨hst10, hd, hdv⟩
  refine ((dToK_good d).pres (pres_dToK d)).step hi10 (Wires.cons' hd Wires.nil') ?_
  rintro ks s11 hi11 he11 ⟨hst11, hks, hksv⟩
  refine ((split_good _).pres (pres_split _)).step hi11 trivial ?_
  rintro lo s12 hi12 he12 ⟨hst12, hlolen, hlow, hlov⟩
  refine ((split_good _).pres (pres_split _)).step hi12 trivial ?_
  rintro up s13 hi13 he13 ⟨hst13, huplen, hupw, hupv⟩
  refine ((eqConstK_good _ 0).pres (pres_eqConstK _ 0)).step hi13 trivial ?_
  rintro _ s14 hi14 he14 ⟨hst14, hlo63⟩
  refine ((eqConstK_good _ 0).pres (pres_eqConstK _ 0)).step hi14 trivial ?_
  rintro _ s15 hi15 he15 ⟨hst15, hup63⟩
  have hDBw : Wires (lo.take 63 ++ up.take 63) s15 :=
    wires_append_take (hlow.mono (by ext_chain)) (hupw.mono (by ext_chain))
  have hDBlen : (lo.take 63 ++ up.take 63).length = 126 := by simp [hlolen, huplen]
  refine (digitProduct_good _ (by omega)).step hi15 hDBw ?_
  rintro prod s16 hi16 he16 ⟨hst16, hprod, hprodv⟩
  refine ((eqConstE_good prod Sphincs.Circuit.targetWord 0 0).pres (pres_eqConstE _ _ _ _)).step hi16 trivial ?_
  rintro _ s17 hi17 he17 ⟨hst17, htarget⟩
  -- What every later assignment says of the digit bits and the tweak words.
  have hDBbool : ∀ st val, Sat st s17 val → ∀ j < 126, val ((lo.take 63 ++ up.take 63).getD j 0) 0 = 0 ∨
      val ((lo.take 63 ++ up.take 63).getD j 0) 0 = 1 := by
    intro st val hsat j hj
    rw [digitBits_getD _ _ hlolen j hj]
    split_ifs with h
    · exact (hlov st val (hsat.mono (by ext_chain))).1 j (by omega)
    · exact (hupv st val (hsat.mono (by ext_chain))).1 (j - 63) (by omega)
  have hkw : ∀ st val, Sat st s17 val → ∀ idx : ℕ, idx < 2 ^ 26 →
      (∀ i < 26, (val (idxBits.getD i 0) 0 = 1 ↔ idx.testBit i = true)) →
      (∀ i < 26, val (idxBits.getD i 0) 0 = 0 ∨ val (idxBits.getD i 0) 0 = 1) →
      w64 val key = tw1 (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩) ∧
      w64 val top = tw1 (Sphincs.Words.tau idx ⟨lay, hlay⟩) 0 := by
    intro st val hsat idx hlt hib hbool
    obtain ⟨ht1, ht2⟩ := tau_bits idxBits val idx _ hs26 hidx hlt hib
    obtain ⟨-, he2, he3, -⟩ := e_bits idxBits val idx (Sphincs.Circuit.suffix (lay + 1)) (Sphincs.Circuit.height lay)
      (by omega) hidx hib hbool
    exact ⟨hkeyv st val (hsat.mono (by ext_chain)) _ _ ht1 he2 ht2 he3,
      htopv st val (hsat.mono (by ext_chain)) _ 0 ht1 (by simp) ht2 (fun i hi => absurd hi (by simp))⟩
  -- The chains.
  refine post_bind (forIn_range_post 42 _ (fun k (ends : List ℕ) s' => s'.statement = s.statement ∧
      ends.length = 2 * k ∧ Wires ends s' ∧ ∀ st val, Sat st s' val → ∀ idx : ℕ, idx < 2 ^ 26 →
        (∀ i < 26, (val (idxBits.getD i 0) 0 = 1 ↔ idx.testBit i = true)) →
        (∀ i < 26, val (idxBits.getD i 0) 0 = 0 ∨ val (idxBits.getD i 0) 0 = 1) → ∃ tips : ℕ → Dig,
          ends.map (w64 val) = (List.range k).flatMap fun i =>
            [(Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
              i (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i) (tips i)).1,
             (Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
              i (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i) (tips i)).2]) hi17
      ⟨by omega, rfl, Wires.nil', fun _ _ _ _ _ _ _ => ⟨fun _ => (0, 0), rfl⟩⟩ ?_) ?_
  · rintro i hi ends s18 hi18 he18 ⟨hst18, hlen18, hw18, hv18⟩
    refine fresh_good'.step hi18 trivial ?_
    rintro tip s19 hi19 he19 ⟨hst19, htip⟩
    refine (indicators_good _ _ _).step hi19 (Wires.cons' (wires_getD' (hDBw.mono (by ext_chain)) (by omega))
      (Wires.cons' (wires_getD' (hDBw.mono (by ext_chain)) (by omega))
        (Wires.cons' (wires_getD' (hDBw.mono (by ext_chain)) (by omega)) Wires.nil'))) ?_
    rintro ind s20 hi20 he20 ⟨hst20, hindlen, hindw, hindv⟩
    refine (spChainEnd_good lay i key tip p0 p1 ind).step hi20 ⟨lt_mono hkey (by ext_chain), lt_mono htip he20,
      lt_mono hp0 (by ext_chain), lt_mono hp1 (by ext_chain), hindw, hindlen⟩ ?_
    rintro ⟨n0, n1⟩ s21 hi21 he21 ⟨hst21, hn0, hn1, hnv⟩
    try dsimp only
    refine post_pure hi21 (by ext_chain) ⟨ends ++ [n0, n1], rfl, by omega, by simp [hlen18]; ring,
      fun w hw => ?_, fun st val hsat idx hlt hib hbool => ?_⟩
    · rcases List.mem_append.mp hw with hw | hw
      · exact lt_mono (hw18 w hw) (by ext_chain)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hn0
        · exact hn1
    · have hDB := hDBbool st val (hsat.mono (by ext_chain))
      obtain ⟨hkey', -⟩ := hkw st val (hsat.mono (by ext_chain)) idx hlt hib hbool
      obtain ⟨tips, htips⟩ := hv18 st val (hsat.mono (by ext_chain)) idx hlt hib hbool
      have hind : ∀ v < 8, ev val (ind.getD v 0) =
          if v = dval val (lo.take 63 ++ up.take 63) i then 1 else 0 := by
        intro v hv
        rw [hindv st val (hsat.mono he21) v hv]
        exact indv_digit _ _ _ _ (hDB _ (by omega)) (hDB _ (by omega)) (hDB _ (by omega)) v hv
      have hend : (w64 val n0, w64 val n1) = Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩)
          (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩) i (w64 val p0, w64 val p1)
          (dval val (lo.take 63 ++ up.take 63) i) (dig val tip) :=
        hnv st val hsat _ (dval_lt _ _ i) _ _ hind hkey'
      refine ⟨fun j => if j = i then dig val tip else tips j, ?_⟩
      rw [List.map_append, htips, List.range_succ, List.flatMap_append,
        flatMap_range_congr (g := fun j =>
          [(Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
            j (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) j)
            (if j = i then dig val tip else tips j)).1,
           (Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
            j (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) j)
            (if j = i then dig val tip else tips j)).2])
          fun j hj => by rw [if_neg (show ¬ j = i by omega)]]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, if_true]
      rw [← hend]
  · rintro ends s18 hi18 he18 ⟨hst18, hlen18, hw18, hv18⟩
    have hb : 8 * (2 + [p0, p1].length + ends.length) < 2 ^ 64 := by
      simp only [hlen18, List.length_cons, List.length_nil]; norm_num
    refine (th_good (Sphincs.Circuit.tweak0 2 lay 0) key [p0, p1] ends hb).step hi18 trivial ?_
    rintro leaf s19 hi19 he19 ⟨hst19, hleaf, hleafv⟩
    refine (fold_good 3 lay _ _ top p0 p1 leaf (by rw [htBlen]; omega) (by rw [heBlen]; omega)).last hi19
      ⟨hwt s19 (by ext_chain), hwe s19 (by ext_chain), lt_mono htop (by ext_chain), lt_mono hp0 (by ext_chain),
        lt_mono hp1 (by ext_chain), hleaf⟩ (by ext_chain) ?_
    rintro r s20 he20 ⟨hst20, hr, hrv⟩
    refine ⟨by omega, hr, fun st val hsat idx hlt hib hbool => ?_⟩
    -- Read everything off the final assignment.
    have hsat17 : Sat st s17 val := hsat.mono (by ext_chain)
    have hDB := hDBbool st val hsat17
    obtain ⟨hkey', htop'⟩ := hkw st val hsat17 idx hlt hib hbool
    obtain ⟨tips, htips⟩ := hv18 st val (hsat.mono (by ext_chain)) idx hlt hib hbool
    obtain ⟨ht1, ht2⟩ := tau_bits idxBits val idx _ hs26 hidx hlt hib
    obtain ⟨-, he2, he3, he4⟩ := e_bits idxBits val idx (Sphincs.Circuit.suffix (lay + 1))
      (Sphincs.Circuit.height lay) (by omega) hidx hib hbool
    obtain ⟨path, hpath⟩ := hrv st val hsat _ _ ht1 he2 ht2 he3 he4 htop'
    rw [heBlen] at hpath
    -- The encoding's digest and digits.
    have hzw : w64 val z = 0 := w64_const (hzv st val (hsat.mono (by ext_chain)))
    have hms0 : val (ms.getD 0 0) 0 = val msg 0 := hmsv st val (hsat.mono (by ext_chain)) 0
    have hms1 : val (ms.getD 1 0) 0 = val msg 1 := hmsv st val (hsat.mono (by ext_chain)) 1
    have hh' : words4 (val h) = digest Rec.paramIV := by
      rw [hhv st val (hsat.mono (by ext_chain))]; exact words4_paramIV
    have hD : dig val d = Sphincs.Words.encDigest (Sphincs.Words.tweak 4 lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) 0
        (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)) (w64 val p0, w64 val p1) (dig val msg) (w64 val ctr) := by
      unfold Sphincs.Words.encDigest
      rw [blake2s_one]
      simp only [dig]
      rw [hdv st val (hsat.mono (by ext_chain)), hh', Rec.cvWords_digest]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        w64_const (htw0v st val (hsat.mono (by ext_chain))), hkey', w64_of hms0, w64_of hms1, hzw, tweak_eq, block8]
      rfl
    have hks0 : val (ks.getD 0 0) 0 = val d 0 := hksv st val (hsat.mono (by ext_chain)) 0
    have hks1 : val (ks.getD 1 0) 0 = val d 1 := hksv st val (hsat.mono (by ext_chain)) 1
    have hlonum : toWord (val d 0) = num (fun i => if val (lo.getD i 0) 0 = 1 then 1 else 0) 64 := by
      rw [← hks0]; exact (hlov st val (hsat.mono (by ext_chain))).2
    have hupnum : toWord (val d 1) = num (fun i => if val (up.getD i 0) 0 = 1 then 1 else 0) 64 := by
      rw [← hks1]; exact (hupv st val (hsat.mono (by ext_chain))).2
    have hlo' : ∀ j < 64, ((dig val d).1.toNat.testBit j = true ↔ val (lo.getD j 0) 0 = 1) := by
      intro j hj
      rw [show (dig val d).1 = words4 (val d) 0 from rfl, words4_toNat]
      exact testBit_split hlonum j hj
    have hup' : ∀ j < 64, ((dig val d).2.toNat.testBit j = true ↔ val (up.getD j 0) 0 = 1) := by
      intro j hj
      rw [show (dig val d).2 = words4 (val d) 1 from rfl, words4_toNat]
      exact testBit_split hupnum j hj
    have hsum : (Xmss.Words.digits (dig val d)).sum = 191 := by
      rw [digits_sum val d lo up hlolen hlo' hup']
      apply Sphincs.eq_191 _ (le_trans (dsum_le _ _ 42) (by norm_num))
      apply emb_injective
      rw [← hprodv st val (hsat.mono (by ext_chain)) hDB, htarget st val (hsat.mono (by ext_chain)),
        Rec.ofWord_zero, toE_emb, Sphincs.target_eq]
    have h63lo : (dig val d).1.getLsbD 63 = false := by
      cases hb : (dig val d).1.getLsbD 63
      · rfl
      · have := (hlo' 63 (by omega)).mp hb
        rw [limb_zero (hlo63 st val (hsat.mono (by ext_chain))) 0] at this
        exact absurd this zero_ne_one
    have h63up : (dig val d).2.getLsbD 63 = false := by
      cases hb : (dig val d).2.getLsbD 63
      · rfl
      · have := (hup' 63 (by omega)).mp hb
        rw [limb_zero (hup63 st val (hsat.mono (by ext_chain))) 0] at this
        exact absurd this zero_ne_one
    have hctr : (w64 val ctr).toNat < 2 ^ 32 := by
      obtain ⟨-, hnum⟩ := hcbv st val (hsat.mono (by ext_chain))
      exact ctr_lt hcblen hnum (hcbz st val (hsat.mono (by ext_chain)))
    have henc : Sphincs.Words.encode lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
        (w64 val p0, w64 val p1) (dig val msg) (w64 val ctr) = some (Xmss.Words.digits (dig val d)) := by
      simp only [Sphincs.Words.encode, ← hD, hctr, h63lo, h63up, hsum, and_self, if_true]
    -- The leaf.
    have hdig : ∀ j < 42, (Xmss.Words.digits (dig val d)).getD j 0 = dval val (lo.take 63 ++ up.take 63) j :=
      fun j hj => by rw [digits_getD _ j hj, digit_dval val d lo up hlolen hlo' hup' j hj]
    have hF := ofFn_flatMap' 42 (fun j => Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩)
      (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩) j (w64 val p0, w64 val p1)
      ((Xmss.Words.digits (dig val d)).getD j 0) (tips j))
    beta_reduce at hF
    have hcong : ((List.range 42).flatMap fun i =>
        [(Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
          i (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i) (tips i)).1,
         (Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
          i (w64 val p0, w64 val p1) (dval val (lo.take 63 ++ up.take 63) i) (tips i)).2]) =
        (List.range 42).flatMap fun i =>
        [(Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
          i (w64 val p0, w64 val p1) ((Xmss.Words.digits (dig val d)).getD i 0) (tips i)).1,
         (Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩) (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩)
          i (w64 val p0, w64 val p1) ((Xmss.Words.digits (dig val d)).getD i 0) (tips i)).2] :=
      flatMap_range_congr fun j hj => by rw [hdig j hj]
    have hleafd : dig val leaf = Sphincs.Words.otsLeaf lay (Sphincs.Words.tau idx ⟨lay, hlay⟩)
        (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩) (w64 val p0, w64 val p1)
        (List.ofFn fun i : Fin 42 => Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx ⟨lay, hlay⟩)
          (Sphincs.Words.leafIndex idx ⟨lay, hlay⟩) i (w64 val p0, w64 val p1)
          ((Xmss.Words.digits (dig val d)).getD i 0) (tips i)) := by
      unfold Sphincs.Words.otsLeaf
      apply spDig_th
      rw [hleafv st val (hsat.mono (by ext_chain)), hkey', hF, List.map_append, htips, hcong, tweak_eq]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    refine ⟨w64 val ctr, fun i => tips i, path, fun sig hc ht hp => ?_⟩
    have hpaths : sig.paths ⟨lay, hlay⟩ = fun l => path l.val := funext fun l => hp l.val l.isLt
    have htipsf : sig.tips ⟨lay, hlay⟩ = fun i => tips i.val := funext ht
    simp only [Sphincs.Words.layerRoot, hc, henc, hpaths, htipsf]
    rw [sp_climb_eq, ← hleafd]
    exact congrArg some hpath.symm

end LeanVMCircuits.Sphincs
