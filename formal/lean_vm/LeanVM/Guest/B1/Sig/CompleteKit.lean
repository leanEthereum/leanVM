/-
  LeanVM.Guest.B1.Sig.CompleteKit

  Combinators for straight-line completeness proofs, a checker for sequential blocks, and where a
  codeword's and a path's hints lie.
-/

module

public import LeanVM.Guest.B1.Sig.WotsCongr
public import LeanVM.Guest.B1.Sig.MerkleComplete

/-!
# A kit for completeness

* `Completes.nil'`, `Completes.checks`, `Completes.hint`, `Completes.seq`, `Completes.load`: a
  block of checks, a hint, a sequential block or a load, then the rest;
* `seqB`: a checker for `SeqOK`, `seqB_ok`;
* `cwPos_lt`, `cwBase_lt`, `mBase_lt`: a codeword's starts and digits and a path's children lie
  below the block's end.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem Completes.nil' {lo : Nat} {σ : Val} {Q : Val → Prop} (h : Q σ) : Completes C rd lo lo [] σ Q :=
  ⟨σ, Ext.refl _ _ _, h, fun _ _ hn => hn⟩

/-- Checks holding, then a block. -/
theorem Completes.checks {lo hi : Nat} {xs ys : List Stmt} {σ : Val} {Q : Val → Prop}
    (ha : atomsOnly xs = true) (hh : AtomsHold rd σ xs) (hn : NumBelow lo (Stmt.valsList xs))
    (hlh : lo ≤ hi) (h : Completes C rd lo hi ys σ Q) : Completes C rd lo hi (xs ++ ys) σ Q :=
  Completes.append le_rfl hlh hn
    (completes_atoms (Post := fun σ' => σ' = σ) ha (Ext.refl _ _ _) rfl hh)
    (fun _ _ e => e ▸ h)

/-- A hint keeping the valuation, then a block. -/
theorem Completes.hint {lo hi : Nat} {s : String} {vs : List V} {ys : List Stmt} {σ : Val}
    {Q : Val → Prop} (hn : NumBelow lo vs) (hlh : lo ≤ hi) (h : Completes C rd lo hi ys σ Q) :
    Completes C rd lo hi (hintW s vs :: ys) σ Q :=
  Completes.checks (xs := [hintW s vs]) rfl (fun a ha => by
    simp only [hintW, List.mem_singleton, Stmt.atom.injEq] at ha
    subst ha
    trivial) (by rw [valsList_hint]; exact hn) hlh h

/-- A sequential block, then a block. -/
theorem Completes.seq {lo m hi : Nat} {xs ys : List Stmt} {σ : Val} {Q : Val → Prop}
    (hs : SeqOK lo xs m) (hhi : m ≤ hi)
    (h : ∀ σ', Ext lo m σ σ' → AtomsHold rd σ' xs → Completes C rd m hi ys σ' Q) :
    Completes C rd lo hi (xs ++ ys) σ Q :=
  Completes.append hs.le hhi hs.numBelow (seq_completes hs σ) h

/-- A load into a fresh value, then a block. -/
theorem Completes.load {d hi : Nat} {p : V} {off : Nat} {w : E} {ys : List Stmt} {σ : Val}
    {Q : Val → Prop} (hp : NBv d p) (hl : LoadHolds rd (σ p) off w) (hhi : d + 1 ≤ hi)
    (h : ∀ σ', Ext d (d + 1) σ σ' → σ' (.n d) = w → Completes C rd (d + 1) hi ys σ' Q) :
    Completes C rd d hi (loadS (.n d) p off :: ys) σ Q :=
  Completes.append (xs := [loadS (.n d) p off]) (Nat.le_succ d) hhi
    (by
      simp only [loadS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
      exact .cons ⟨d, by omega, rfl⟩ (.cons (hp.mono' (by omega)) (.nil _)))
    (loadS_complete σ d hp hl) h

/-! ## A checker for sequential blocks -/

/-- `v` is a numbered value below `b`, decided. -/
def nbB (b : Nat) (v : V) : Bool := v == .n v.idx && decide (v.idx < b)

theorem nbB_ok {b : Nat} {v : V} (h : nbB b v = true) : NBv b v := by
  simp only [nbB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨v.idx, h.2, h.1⟩

/-- An atom defining value `b` from values below it, decided. -/
def aSeqB (b : Nat) : Atom → Bool
  | .const d _ => d == .n b
  | .add d x y | .mul d x y => d == .n b && nbB b x && nbB b y
  | .copy d x => d == .n b && nbB b x
  | _ => false

/-- A sequential block, decided. -/
def seqB : Nat → List Stmt → Nat → Bool
  | b, [], b' => b' == b
  | b, .atom a :: ss, b' => aSeqB b a && seqB (b + 1) ss b'
  | _, _ :: _, _ => false

theorem aSeqB_ok {b : Nat} {a : Atom} (h : aSeqB b a = true) : ASeq b a := by
  cases a with
  | const d c => simpa [aSeqB, ASeq] using h
  | add d x y =>
      simp only [aSeqB, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨h.1.1, nbB_ok h.1.2, nbB_ok h.2⟩
  | mul d x y =>
      simp only [aSeqB, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨h.1.1, nbB_ok h.1.2, nbB_ok h.2⟩
  | copy d x =>
      simp only [aSeqB, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨h.1, nbB_ok h.2⟩
  | _ => simp [aSeqB] at h

theorem seqB_ok : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, seqB b ss b' = true → SeqOK b ss b'
  | _, [], _, h => by simpa [seqB, SeqOK] using h
  | _, .atom a :: ss, _, h => by
      simp only [seqB, Bool.and_eq_true] at h
      exact ⟨aSeqB_ok h.1, seqB_ok h.2⟩
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => by simp [seqB] at h

/-! ## Where the hints lie -/

theorem cwBase_lt (W : WotsT) {G q : Nat} (target : E) (d0 : V) (b : Nat) (hq : q ≤ G) :
    (cwState W b q).2.2 < (codewordT W G target d0 b).2.1 := by
  have hle := cwState_le W b q (G - q)
  rw [show q + (G - q) = G by omega] at hle
  have hend := groupT_end W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2
  rw [codewordT_snd]
  rw [groupStart_eq] at hend
  simp only [Bool.false_eq_true, ↓reduceIte] at hend
  omega

theorem cwPos_lt (W : WotsT) {G : Nat} {K : Nat → Nat} (target : E) (d0 : V) (b : Nat) (hG : 0 < G)
    (hK : ∀ q ≤ G, K q < 4 ^ cwN G q) {i : Nat} (hi : i < 3 * G + 1) :
    ∃ j, cwPos W G b K i = .n j ∧ j < (codewordT W G target d0 b).2.1 := by
  rw [codewordT_snd]
  have hiq : i = 3 * (i / 3) + i % 3 := by omega
  rcases Nat.lt_or_ge (i / 3) G with hq | hq
  · have hn3 : cwN G (i / 3) = 3 := by simp [cwN, hq]
    rw [hiq, cwPos_eq W G b K (i / 3) (i % 3) (Nat.mod_lt _ (by norm_num))]
    obtain ⟨j, ej, -, hj, -⟩ := grpPos_spec W (3 * (i / 3)) (cwN G (i / 3)) (i / 3 == 0)
      (cwState W b (i / 3)).1 (cwState W b (i / 3)).2.1 (cwState W b (i / 3)).2.2 (K (i / 3)) (i % 3)
      (hK _ (by omega)) (by rw [hn3]; exact Nat.mod_lt _ (by norm_num))
    refine ⟨j, ej, ?_⟩
    have hle := cwState_le W b (i / 3 + 1) (G - (i / 3 + 1))
    rw [show i / 3 + 1 + (G - (i / 3 + 1)) = G by omega, cwState_succ, groupT_snd_eq] at hle
    rw [hn3] at hj
    have hend := groupT_end W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2
    rw [groupStart_eq] at hend
    simp only [Bool.false_eq_true, ↓reduceIte] at hend
    omega
  · have h1 : i / 3 = G := by omega
    have h2 : i % 3 = 0 := by omega
    rw [hiq, h1, h2, cwPos_eq W G b K G 0 (by omega)]
    obtain ⟨j, ej, -, hj, -⟩ := grpPos_spec W (3 * G) (cwN G G) (G == 0) (cwState W b G).1
      (cwState W b G).2.1 (cwState W b G).2.2 (K G) 0 (hK G le_rfl) (by simp [cwN])
    refine ⟨j, ej, ?_⟩
    have hnG : cwN G G = 1 := by simp [cwN]
    rw [groupT_snd_eq]
    rw [hnG] at hj
    have hfG : (G == 0) = false := by simp; omega
    rw [hfG] at hj
    omega

theorem mBase_lt (pad : Nat) (pp : V) (bitOf : Nat → V) (nodeOf : Nat → Option V) (addrOf : Nat → Nat) :
    ∀ (m l : Nat) (cur : V) (b j : Nat), j < m →
      mBase nodeOf l j b + 2 ≤ (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.1
  | 0, _, _, _, _, hj => absurd hj (by omega)
  | m + 1, l, cur, b, 0, _ => by
      simp only [mBase, merkleT]
      have h5 : b + 2 ≤ b + 5 + 2 := by omega
      have h6 : b + 2 ≤ b + 6 + 2 := by omega
      split
      · exact le_trans h5 (merkleT_snd_ge pad pp bitOf nodeOf addrOf m (l + 1) _ _)
      · exact le_trans h6 (merkleT_snd_ge pad pp bitOf nodeOf addrOf m (l + 1) _ _)
  | m + 1, l, cur, b, j + 1, hj => by
      simp only [mBase]
      cases hn : nodeOf l with
      | none =>
          have := mBase_lt pad pp bitOf nodeOf addrOf m (l + 1) (.n (b + 5 + 1)) (b + 5 + 2) j (by omega)
          simp only [merkleT, hn, mNext]
          exact this
      | some nd =>
          have := mBase_lt pad pp bitOf nodeOf addrOf m (l + 1) (.n (b + 6 + 1)) (b + 6 + 2) j (by omega)
          simp only [merkleT, hn, mNext]
          exact this

/-! ## The codeword's and the message's bounds -/

theorem codewordT_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {G : Nat} {target : E} {d0 : V}
    {b : Nat} (hb0 : 0 < b) (hB : B ≤ b) (hpw : ∀ j, NBv B (W.power j)) (hd0 : NBv b d0) :
    NumBelow (codewordT W G target d0 b).2.1 (Stmt.valsList (codewordT W G target d0 b).1) := by
  rw [codewordT_eq, codewordT_snd]
  have hbG := cwState_mono W b G
  obtain ⟨hpiG, heiG⟩ := cwState_in W hb0 G
  have hnbG := groupsT_numBelow hW hb0 hB hpw G 0
  simp only [Nat.zero_add] at hnbG
  have hnbL := groupT_numBelow (first := 3 * G) (n := 1) (fold := false) hW
    (show B ≤ (cwState W b G).2.2 by omega) hpiG heiG (fun j => (hpw j).mono' (by omega))
  have hendL := groupT_end W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2
  rw [groupStart_eq] at hendL
  simp only [Bool.false_eq_true, ↓reduceIte] at hendL
  rw [valsList_append, valsList_append]
  refine ((hnbG.mono (by omega)).append (hnbL.mono (by omega))).append ?_
  intro x hx
  simp only [copyS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨j, hj, rfl⟩ := hd0
    exact ⟨j, by omega, rfl⟩
  · exact ⟨_, by rw [groupStart_eq]; simp only [Bool.false_eq_true, ↓reduceIte]; omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩
  · exact ⟨_, by rw [groupStart_eq]; simp only [Bool.false_eq_true, ↓reduceIte]; omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩

theorem cwTip_lt (W : WotsT) {G : Nat} (target : E) (d0 : V) (b : Nat) (hG : 0 < G) {i : Nat}
    (hi : i < 3 * G + 1) : ∃ j, cwTip W b i = .n j ∧ j < (codewordT W G target d0 b).2.1 := by
  refine ⟨_, rfl, ?_⟩
  rw [codewordT_snd]
  have hs := (slot_bounds W (i / 3 == 0) (cwState W b (i / 3)).2.2 (i % 3) 2 (by norm_num)).2
  have hendL := groupT_end W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2
  rw [groupStart_eq] at hendL
  simp only [Bool.false_eq_true, ↓reduceIte] at hendL
  rcases Nat.lt_or_ge (i / 3) G with hq | hq
  · have hle := cwState_le W b (i / 3 + 1) (G - (i / 3 + 1))
    rw [show i / 3 + 1 + (G - (i / 3 + 1)) = G by omega] at hle
    have hend := groupT_end W (3 * (i / 3)) 3 (i / 3 == 0) (cwState W b (i / 3)).1
      (cwState W b (i / 3)).2.1 (cwState W b (i / 3)).2.2
    rw [← cwState_succ] at hend
    have : chainStride W * (i % 3 + 1) ≤ chainStride W * 3 := Nat.mul_le_mul_left _ (by omega)
    omega
  · have h1 : i / 3 = G := by omega
    have h2 : i % 3 = 0 := by omega
    have hfG : (G == 0) = false := by simp; omega
    rw [h1, h2, hfG] at hs ⊢
    rw [groupStart_eq] at hs
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    omega

theorem kBlocks_end (pad : Nat) (cs : List KC) (B : Nat) (tailRun : Bool) (n : Nat) :
    ∀ (m k : Nat) (st : Option (List V)) (b : Nat), 0 < m → k + m = B →
      (kBlocks pad cs B tailRun none n m k st b).2.2 + n ≤
        (kBlocks pad cs B tailRun none n m k st b).2.1
  | 0, _, _, _, h, _ => absurd h (by omega)
  | m + 1, k, st, b, _, hkm => by
      rw [kBlocks_none_eq]
      dsimp only
      by_cases hl : k + 1 = B
      · have hm : m = 0 := by omega
        subst hm
        simp [hl, kBlocks, kOutN]
      · have hne : (k + 1 == B) = false := by simp [hl]
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact kBlocks_end pad cs B tailRun n m (k + 1) _ _ (by omega) (by omega)

/-- **The message's output** lies below its end. -/
theorem kMsg_out (pad : Nat) (cells : List KC) (len : Nat) (tailRun : Bool) (b : Nat)
    (n : Nat := 1) :
    (kMsg pad cells len tailRun none b n).2.2 + n ≤ (kMsg pad cells len tailRun none b n).2.1 := by
  rw [kMsg_eq]
  dsimp only
  exact kBlocks_end _ _ _ _ _ (kBlocksOf len) 0 none _ (by unfold kBlocksOf; omega) (by simp)

/-- **The message ends above its base.** -/
theorem kMsg_le {pad : Nat} {cells : List KC} {len : Nat} {tailRun : Bool} {b : Nat}
    (hpb : pad + 5 ≤ b) (hc : ∀ c ∈ cells, KCb b c) (n : Nat := 1) :
    b ≤ (kMsg pad cells len tailRun none b n).2.1 := by
  rw [kMsg_eq]
  dsimp only
  set cs0 := cells ++ List.replicate (17 * (kBlocksOf len - 1) / 2 + 9 - cells.length) KC.zero with hcs0
  have hc0 : ∀ c ∈ cs0, KCb b c := by
    intro c hc'
    rcases List.mem_append.mp hc' with h | h
    · exact hc c h
    · rw [List.eq_of_mem_replicate h]
      trivial
  obtain ⟨a1, a2, a3⟩ := kXorByte_seq (cs := cs0) (pos := len) (v := 1) (b := b) hc0
  set x1 := kXorByte cs0 len 1 b with hx1
  obtain ⟨b1, b2, b3⟩ := kXorByte_seq (cs := x1.2.1) (pos := 136 * kBlocksOf len - 1) (v := 0x80)
    (b := x1.2.2) a2
  set x2 := kXorByte x1.2.1 (136 * kBlocksOf len - 1) 0x80 x1.2.2 with hx2
  have hs := SeqOK.append a1 b1
  have := hs.le
  obtain ⟨-, n2⟩ := kBlocks_nb (pad := pad) (cs := x2.2.1) (B := kBlocksOf len) (n := n)
    (tailRun := tailRun) (kBlocksOf len) 0 none x2.2.2 (by omega) (by omega) b2
    (fun s hs => by simp at hs)
  omega

theorem numBelow_of_all {hi : Nat} {vs : List V} (h : vs.all (nbB hi) = true) : NumBelow hi vs :=
  fun v hv => nbB_ok (List.all_eq_true.mp h v hv)

/-- **The message's values lie below its end.** -/
theorem kMsg_numBelow {pad : Nat} {cells : List KC} {len : Nat} {tailRun : Bool} {b : Nat}
    (hpb : pad + 5 ≤ b) (hc : ∀ c ∈ cells, KCb b c) (n : Nat := 1) :
    NumBelow (kMsg pad cells len tailRun none b n).2.1
      (Stmt.valsList (kMsg pad cells len tailRun none b n).1) := by
  rw [kMsg_eq]
  dsimp only
  set cs0 := cells ++ List.replicate (17 * (kBlocksOf len - 1) / 2 + 9 - cells.length) KC.zero with hcs0
  have hc0 : ∀ c ∈ cs0, KCb b c := by
    intro c hc'
    rcases List.mem_append.mp hc' with h | h
    · exact hc c h
    · rw [List.eq_of_mem_replicate h]
      trivial
  obtain ⟨a1, a2, a3⟩ := kXorByte_seq (cs := cs0) (pos := len) (v := 1) (b := b) hc0
  set x1 := kXorByte cs0 len 1 b with hx1
  obtain ⟨b1, b2, b3⟩ := kXorByte_seq (cs := x1.2.1) (pos := 136 * kBlocksOf len - 1) (v := 0x80)
    (b := x1.2.2) a2
  set x2 := kXorByte x1.2.1 (136 * kBlocksOf len - 1) 0x80 x1.2.2 with hx2
  have hs := SeqOK.append a1 b1
  have := hs.le
  obtain ⟨n1, n2⟩ := kBlocks_nb (pad := pad) (cs := x2.2.1) (B := kBlocksOf len) (n := n)
    (tailRun := tailRun) (kBlocksOf len) 0 none x2.2.2 (by omega) (by omega) b2
    (fun s hs => by simp at hs)
  rw [valsList_append]
  exact (hs.numBelow.mono n2).append n1

/-- **A path's values lie below its end.** -/
theorem merkleT_numBelow {pad : Nat} {pp : V} {bitOf : Nat → V} {nodeOf : Nat → Option V}
    {addrOf : Nat → Nat} :
    ∀ (m l : Nat) (cur : V) (b : Nat), pad + 5 ≤ b → NBv b pp → NBv b cur →
      (∀ j < m, NBv b (bitOf (l + j))) → (∀ l' nd, nodeOf l' = some nd → NBv b nd) →
      NumBelow (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.1
        (Stmt.valsList (merkleT pad pp bitOf nodeOf addrOf m l cur b).1)
  | 0, _, _, _, _, _, _, _, _ => NumBelow.nil _
  | m + 1, l, cur, b, hpb, hpp, hcur, hbits, hnodes => by
      have h0 := hbits 0 (by omega)
      rw [Nat.add_zero] at h0
      have hall : ∀ (c : Nat) (nodeL : List Stmt), b + 5 ≤ c →
          SeqOK (b + 4) ([cst (b + 4) (word (addrOf l) 0 0)] ++ nodeL) c →
          merkleT pad pp bitOf nodeOf addrOf (m + 1) l cur b =
            ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
              addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bitOf l) (.n (b + 3)),
              cst (b + 4) (word (addrOf l) 0 0)] ++ nodeL ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1) ++
              (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).1,
              (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).2.1,
              (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).2.2) →
          NumBelow (merkleT pad pp bitOf nodeOf addrOf (m + 1) l cur b).2.1
            (Stmt.valsList (merkleT pad pp bitOf nodeOf addrOf (m + 1) l cur b).1) := by
        intro c nodeL hc hseq heq
        rw [heq]
        have hl := level_numBelow hpb hpp h0 hcur hseq hc
        have hr := merkleT_numBelow (pad := pad) (pp := pp) (bitOf := bitOf) (nodeOf := nodeOf)
          (addrOf := addrOf) m (l + 1) (.n (c + 1)) (c + 2) (by omega) (hpp.mono' (by omega))
          ⟨c + 1, by omega, rfl⟩
          (fun j hj => by
            rw [show l + 1 + j = l + (j + 1) by omega]
            exact NBv.mono' (hbits (j + 1) (by omega)) (show b ≤ c + 2 by omega))
          (fun l' nd h => NBv.mono' (hnodes l' nd h) (show b ≤ c + 2 by omega))
        have hge := merkleT_snd_ge pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)
        dsimp only
        rw [valsList_append]
        exact (hl.mono hge).append hr
      cases hn : nodeOf l with
      | none => exact hall (b + 5) [] (by omega) ⟨rfl, rfl⟩ (by simp [merkleT, hn])
      | some nd =>
          exact hall (b + 6) [addS (.n (b + 5)) (.n (b + 4)) nd] (by omega)
            ⟨rfl, ⟨rfl, ⟨b + 4, by omega, rfl⟩, (hnodes l nd hn).mono' (by omega)⟩, rfl⟩
            (by simp [merkleT, hn])

end
end LeanVM.Guest.B1.Sig
