/-
  LeanVM.Guest.B1.Sig.KMsgComplete

  The lowered Keccak message (`kMsg`, `emit_keccak_message`) is complete: its statements hold of
  an extension of any valuation holding the padding run.
-/

module

public import LeanVM.Guest.B1.Sig.SeqComplete

/-!
# The Keccak message, complete

* `KCb`: a message cell's value numbered below a bound;
* `kCell_seq`, `kXor_seq`, `kRunFresh_seq`, `kRun_seq`, `kTailXor_seq`, `kIns_seq`, `kXorByte_seq`:
  the blocks between two `KECCAK`s are sequential (`SeqOK`);
* `kBlocks_complete`, `kMsg_complete`: the message completes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- A message cell's value is numbered below `b`. -/
def KCb (b : Nat) : KC → Prop
  | .cell o => NBv b o
  | _ => True

theorem KCb.mono {b b' : Nat} {k : KC} (h : KCb b k) (hle : b ≤ b') : KCb b' k := by
  cases k with
  | cell o => obtain ⟨j, hj, rfl⟩ := h; exact ⟨j, by omega, rfl⟩
  | _ => trivial

theorem NBv.mono {b b' : Nat} {v : V} (h : NBv b v) (hle : b ≤ b') : NBv b' v := by
  obtain ⟨j, hj, rfl⟩ := h; exact ⟨j, by omega, rfl⟩

theorem PadOK.congr {σ σ' : Val} {pad b : Nat} (h : PadOK σ pad) (hb : pad + 5 ≤ b)
    (hσ : AgreeBelow b σ σ') : PadOK σ' pad := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hσ pad (by omega)]; exact h0
  · rw [← hσ (pad + 1) (by omega)]; exact h1
  · rw [← hσ (pad + 2) (by omega)]; exact h2
  · rw [← hσ (pad + 3) (by omega)]; exact h3
  · rw [← hσ (pad + 4) (by omega)]; exact h4

/-! ## Sequential pieces -/

theorem kCell_seq {pad b : Nat} (hp : pad + 5 ≤ b) {k : KC} (hk : KCb b k) :
    SeqOK b (kCell pad k b).1 (kCell pad k b).2.2 ∧ NBv (kCell pad k b).2.2 (kCell pad k b).2.1 ∧
      b ≤ (kCell pad k b).2.2 := by
  cases k with
  | zero => exact ⟨rfl, ⟨pad + 1, by simp [kCell]; omega, rfl⟩, le_rfl⟩
  | const c =>
      rw [kCell_const]
      by_cases hc : isPadOne c = true
      · simp only [hc, ↓reduceIte]
        exact ⟨rfl, ⟨pad, by omega, rfl⟩, le_rfl⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ⟨⟨rfl, rfl⟩, ⟨b, by omega, rfl⟩, by omega⟩
  | cell o => exact ⟨rfl, hk, le_rfl⟩

theorem kXor_seq {pad b : Nat} (hp : pad + 5 ≤ b) {st : V} (hst : NBv b st) {k : KC} (hk : KCb b k) :
    SeqOK b (kXor pad st k b).1 (kXor pad st k b).2.2 ∧ NBv (kXor pad st k b).2.2 (kXor pad st k b).2.1 ∧
      b ≤ (kXor pad st k b).2.2 := by
  have key : ∀ k : KC, k.isZero = false → KCb b k →
      SeqOK b ((kCell pad k b).1 ++ [addS (.n (kCell pad k b).2.2) st (kCell pad k b).2.1])
        ((kCell pad k b).2.2 + 1) ∧ NBv ((kCell pad k b).2.2 + 1) (.n (kCell pad k b).2.2) ∧
        b ≤ (kCell pad k b).2.2 + 1 := by
    intro k _ hk
    obtain ⟨h1, h2, h3⟩ := kCell_seq (pad := pad) hp hk
    exact ⟨SeqOK.append h1 ⟨⟨rfl, hst.mono h3, h2⟩, rfl⟩, ⟨_, by omega, rfl⟩, by omega⟩
  cases k with
  | zero => exact ⟨rfl, hst, le_rfl⟩
  | const c => exact key (.const c) rfl hk
  | cell o => exact key (.cell o) rfl hk

theorem kRunFresh_seq : ∀ {ks : List KC} {b0 b : Nat}, (∀ k ∈ ks, KCb b0 k) → b0 ≤ b →
    SeqOK b (kRunFresh ks b) (b + ks.length)
  | [], _, _, _, _ => by simp [kRunFresh, SeqOK]
  | k :: ks, b0, b, h, hb => by
      have ih := kRunFresh_seq (ks := ks) (b := b + 1) (fun k hk => h k (by simp [hk])) (by omega)
      rw [show b + (k :: ks).length = b + 1 + ks.length by simp; omega]
      cases k with
      | zero => exact ⟨rfl, ih⟩
      | const c => exact ⟨rfl, ih⟩
      | cell o =>
          have := h (.cell o) (by simp)
          exact ⟨⟨rfl, (show NBv b0 o from this).mono hb⟩, ih⟩

theorem kVals_nb {b : Nat} : ∀ {ks : List KC}, (∀ k ∈ ks, KCb b k) → ∀ v ∈ kVals ks, NBv b v
  | [], _, _, hv => absurd hv (by simp [kVals])
  | .cell o :: ks, h, v, hv => by
      simp only [kVals, List.mem_cons] at hv
      rcases hv with h1 | hv
      · subst h1
        exact h (.cell v) (by simp)
      · exact kVals_nb (ks := ks) (fun k hk => h k (by simp [hk])) v hv
  | .zero :: ks, h, v, hv => kVals_nb (ks := ks) (fun k hk => h k (by simp [hk])) v hv
  | .const _ :: ks, h, v, hv => kVals_nb (ks := ks) (fun k hk => h k (by simp [hk])) v hv

theorem runV_nb {o n b : Nat} (h : o + n ≤ b) : ∀ v ∈ runV o n, NBv b v := by
  intro v hv
  simp only [runV, List.mem_map, List.mem_range] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  exact ⟨o + k, by omega, rfl⟩

theorem kRun_seq {pad b : Nat} (hp : pad + 5 ≤ b) {k0 k1 k2 k3 : KC} (tailRun : Bool)
    (hk : ∀ k ∈ [k0, k1, k2, k3], KCb b k) :
    SeqOK b (kRun pad [k0, k1, k2, k3] tailRun b).1 (kRun pad [k0, k1, k2, k3] tailRun b).2.2 ∧
      (∀ v ∈ (kRun pad [k0, k1, k2, k3] tailRun b).2.1, NBv (kRun pad [k0, k1, k2, k3] tailRun b).2.2 v) ∧
      b ≤ (kRun pad [k0, k1, k2, k3] tailRun b).2.2 := by
  rw [kRun_eq]
  split_ifs
  · exact ⟨rfl, kVals_nb hk, le_rfl⟩
  · dsimp only
    exact ⟨rfl, runV_nb (by omega), le_rfl⟩
  · dsimp only
    exact ⟨rfl, runV_nb (by omega), le_rfl⟩
  · dsimp only
    exact ⟨kRunFresh_seq hk le_rfl, runV_nb (by omega), by omega⟩

theorem kTailXor_seq {pad : Nat} : ∀ {sts : List V} {ks : List KC} {b : Nat}, pad + 5 ≤ b →
    (∀ v ∈ sts, NBv b v) → (∀ k ∈ ks, KCb b k) →
    SeqOK b (kTailXor pad sts ks b).1 (kTailXor pad sts ks b).2.2 ∧
      (∀ v ∈ (kTailXor pad sts ks b).2.1, NBv (kTailXor pad sts ks b).2.2 v) ∧
      b ≤ (kTailXor pad sts ks b).2.2
  | [], _, b, _, _, _ => ⟨rfl, by simp [kTailXor], le_rfl⟩
  | _ :: _, [], b, _, _, _ => ⟨rfl, by simp [kTailXor], le_rfl⟩
  | st :: sts, k :: ks, b, hp, hs, hk => by
      have hst := hs st (by simp)
      have hk0 := hk k (by simp)
      have step : ∀ (x : List Stmt × V × Nat), SeqOK b x.1 x.2.2 → NBv x.2.2 x.2.1 → b ≤ x.2.2 →
          SeqOK b (x.1 ++ (kTailXor pad sts ks x.2.2).1) (kTailXor pad sts ks x.2.2).2.2 ∧
          (∀ v ∈ x.2.1 :: (kTailXor pad sts ks x.2.2).2.1, NBv (kTailXor pad sts ks x.2.2).2.2 v) ∧
          b ≤ (kTailXor pad sts ks x.2.2).2.2 := by
        intro x h1 h2 h3
        obtain ⟨i1, i2, i3⟩ := kTailXor_seq (pad := pad) (sts := sts) (ks := ks) (b := x.2.2)
          (by omega) (fun v hv => (hs v (by simp [hv])).mono h3)
          (fun k hk' => (hk k (by simp [hk'])).mono h3)
        refine ⟨SeqOK.append h1 i1, fun v hv => ?_, by omega⟩
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h2.mono i3
        · exact i2 v hv
      cases k with
      | zero =>
          exact step ([copyS (.n b) st], .n b, b + 1) ⟨⟨rfl, hst⟩, rfl⟩
            (show NBv (b + 1) (.n b) from ⟨b, by omega, rfl⟩) (show b ≤ b + 1 by omega)
      | const c =>
          obtain ⟨h1, h2, h3⟩ := kXor_seq (pad := pad) hp hst (k := .const c) hk0
          exact step _ h1 h2 h3
      | cell o =>
          obtain ⟨h1, h2, h3⟩ := kXor_seq (pad := pad) hp hst (k := .cell o) hk0
          exact step _ h1 h2 h3

theorem kIns_seq {pad b : Nat} (hp : pad + 5 ≤ b) {blk : List KC} {tailRun : Bool}
    {st : Option (List V)} (hst : ∀ s, st = some s → ∀ v ∈ s, NBv b v)
    (hblk : ∀ k ∈ blk, KCb b k) :
    SeqOK b (kIns pad blk tailRun st b).1 (kIns pad blk tailRun st b).2.2 ∧
      (∀ v ∈ (kIns pad blk tailRun st b).2.1, NBv (kIns pad blk tailRun st b).2.2 v) ∧
      b ≤ (kIns pad blk tailRun st b).2.2 := by
  have hcell : ∀ i, KCb b (blk.getD i .zero) := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases h : blk[i]? with
    | none => trivial
    | some k => exact hblk k (List.mem_of_getElem? h)
  cases st with
  | none =>
      simp only [kIns]
      obtain ⟨a1, a2, a3⟩ := kCell_seq (pad := pad) hp (hcell 0)
      obtain ⟨b1, b2, b3⟩ := kCell_seq (pad := pad) (b := (kCell pad (blk.getD 0 .zero) b).2.2)
        (by omega) ((hcell 1).mono a3)
      obtain ⟨c1, c2, c3⟩ := kCell_seq (pad := pad)
        (b := (kCell pad (blk.getD 1 .zero) (kCell pad (blk.getD 0 .zero) b).2.2).2.2)
        (by omega) ((hcell 2).mono (by omega))
      obtain ⟨d1, d2, d3⟩ := kCell_seq (pad := pad)
        (b := (kCell pad (blk.getD 2 .zero) (kCell pad (blk.getD 1 .zero)
          (kCell pad (blk.getD 0 .zero) b).2.2).2.2).2.2) (by omega) ((hcell 3).mono (by omega))
      set B3 := (kCell pad (blk.getD 3 .zero) (kCell pad (blk.getD 2 .zero) (kCell pad (blk.getD 1 .zero)
          (kCell pad (blk.getD 0 .zero) b).2.2).2.2).2.2).2.2 with hB3
      obtain ⟨t1, t2, t3⟩ := kRun_seq (pad := pad) (b := B3) (by omega) tailRun
        (k0 := blk.getD 4 .zero) (k1 := blk.getD 5 .zero) (k2 := blk.getD 6 .zero) (k3 := blk.getD 7 .zero)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro k (rfl | rfl | rfl | rfl) <;> exact (hcell _).mono (by omega))
      set T := kRun pad [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero]
        tailRun B3 with hT
      obtain ⟨e1, e2, e3⟩ := kCell_seq (pad := pad) (b := T.2.2) (by omega) ((hcell 8).mono (by omega))
      refine ⟨SeqOK.append (SeqOK.append (SeqOK.append (SeqOK.append (SeqOK.append a1 b1) c1) d1) t1) e1,
        fun v hv => ?_, by omega⟩
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with (((((rfl | rfl | rfl | rfl) | hv) | rfl) | hv))
      · exact a2.mono (by omega)
      · exact b2.mono (by omega)
      · exact c2.mono (by omega)
      · exact d2.mono (by omega)
      · exact (t2 v hv).mono (by omega)
      · exact e2
      · exact runV_nb (by omega) v hv
  | some s =>
      have hs := hst s rfl
      have hsi : ∀ i, NBv b (s.getD i default) := fun i => by
        rw [List.getD_eq_getElem?_getD]
        cases h : s[i]? with
        | none => exact ⟨0, by omega, rfl⟩
        | some v => exact hs v (List.mem_of_getElem? h)
      simp only [kIns]
      obtain ⟨a1, a2, a3⟩ := kXor_seq (pad := pad) hp (hsi 0) (hcell 0)
      obtain ⟨b1, b2, b3⟩ := kXor_seq (pad := pad) (b := (kXor pad (s.getD 0 default) (blk.getD 0 .zero) b).2.2)
        (by omega) ((hsi 1).mono a3) ((hcell 1).mono a3)
      set B1 := (kXor pad (s.getD 1 default) (blk.getD 1 .zero)
        (kXor pad (s.getD 0 default) (blk.getD 0 .zero) b).2.2).2.2 with hB1
      obtain ⟨c1, c2, c3⟩ := kXor_seq (pad := pad) (b := B1) (by omega) ((hsi 2).mono (by omega))
        ((hcell 2).mono (by omega))
      set B2 := (kXor pad (s.getD 2 default) (blk.getD 2 .zero) B1).2.2 with hB2
      obtain ⟨d1, d2, d3⟩ := kXor_seq (pad := pad) (b := B2) (by omega) ((hsi 3).mono (by omega))
        ((hcell 3).mono (by omega))
      set B3 := (kXor pad (s.getD 3 default) (blk.getD 3 .zero) B2).2.2 with hB3
      have ht : SeqOK B3 (if [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero].all
            KC.isZero then (([], [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default], B3) :
              List Stmt × List V × Nat)
          else kTailXor pad [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default]
            [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero] B3).1
          (if [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero].all
            KC.isZero then (([], [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default], B3) :
              List Stmt × List V × Nat)
          else kTailXor pad [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default]
            [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero] B3).2.2 ∧
          (∀ v ∈ (if [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero].all
            KC.isZero then (([], [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default], B3) :
              List Stmt × List V × Nat)
          else kTailXor pad [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default]
            [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero] B3).2.1,
            NBv (if [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero].all
            KC.isZero then (([], [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default], B3) :
              List Stmt × List V × Nat)
          else kTailXor pad [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default]
            [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero] B3).2.2 v) ∧
          B3 ≤ (if [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero].all
            KC.isZero then (([], [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default], B3) :
              List Stmt × List V × Nat)
          else kTailXor pad [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default]
            [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero] B3).2.2 := by
        split
        · dsimp only
          refine ⟨rfl, fun v hv => ?_, le_rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> exact (hsi _).mono (by omega)
        · exact kTailXor_seq (by omega)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                rintro v (rfl | rfl | rfl | rfl) <;> exact (hsi _).mono (by omega))
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                rintro k (rfl | rfl | rfl | rfl) <;> exact (hcell _).mono (by omega))
      generalize hTdef : (if [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero].all
            KC.isZero then (([], [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default], B3) :
              List Stmt × List V × Nat)
          else kTailXor pad [s.getD 4 default, s.getD 5 default, s.getD 6 default, s.getD 7 default]
            [blk.getD 4 .zero, blk.getD 5 .zero, blk.getD 6 .zero, blk.getD 7 .zero] B3) = T at ht ⊢
      obtain ⟨t1, t2, t3⟩ := ht
      obtain ⟨e1, e2, e3⟩ := kXor_seq (pad := pad) (b := T.2.2) (st := s.getD 8 default)
        (k := blk.getD 8 .zero) (by omega) ((hsi 8).mono (by omega)) ((hcell 8).mono (by omega))
      refine ⟨SeqOK.append (SeqOK.append (SeqOK.append (SeqOK.append (SeqOK.append a1 b1) c1) d1) t1) e1,
        fun v hv => ?_, by omega⟩
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with ((((rfl | rfl | rfl | rfl) | hv) | (rfl | rfl | rfl | rfl | rfl)))
      · exact a2.mono (by omega)
      · exact b2.mono (by omega)
      · exact c2.mono (by omega)
      · exact d2.mono (by omega)
      · exact (t2 v hv).mono (by omega)
      · exact e2
      all_goals exact (hsi _).mono (by omega)

theorem kXorByte_seq {cs : List KC} {pos v b : Nat} (hc : ∀ k ∈ cs, KCb b k) :
    SeqOK b (kXorByte cs pos v b).1 (kXorByte cs pos v b).2.2 ∧
      (∀ k ∈ (kXorByte cs pos v b).2.1, KCb (kXorByte cs pos v b).2.2 k) ∧
      b ≤ (kXorByte cs pos v b).2.2 := by
  have hset : ∀ (l : List KC) (i : Nat) (x : KC) (bd : Nat), (∀ k ∈ l, KCb bd k) → KCb bd x →
      ∀ k ∈ l.set i x, KCb bd k := by
    intro l i x bd hl hx k hk
    rcases List.mem_or_eq_of_mem_set hk with h | h
    · exact hl k h
    · subst h; exact hx
  unfold kXorByte
  simp only
  split
  · exact ⟨rfl, hset _ _ _ _ hc trivial, le_rfl⟩
  · exact ⟨rfl, hset _ _ _ _ hc trivial, le_rfl⟩
  · rename_i o ho
    have hob : NBv b o := by
      have := hc (.cell o) (by
        rw [List.getD_eq_getElem?_getD] at ho
        cases h : cs[pos / 16]? with
        | none => rw [h] at ho; simp at ho
        | some k => rw [h] at ho; simp only [Option.getD_some] at ho; subst ho; exact List.mem_of_getElem? h)
      exact this
    dsimp only
    refine ⟨⟨rfl, ⟨rfl, hob.mono (by omega), ⟨b, by omega, rfl⟩⟩, rfl⟩,
      hset _ _ _ _ (fun k hk => (hc k hk).mono (by omega)) ⟨b + 1, by omega, rfl⟩, by omega⟩

/-! ## The blocks -/

theorem blockOf_mem {cs : List KC} {k : Nat} {c : KC} (h : c ∈ (cs.drop (17 * k / 2)).take 9) : c ∈ cs :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem kBlocks_none_eq (pad : Nat) (cs : List KC) (B : Nat) (tailRun : Bool) (n m k : Nat)
    (st : Option (List V)) (b : Nat) :
    kBlocks pad cs B tailRun none n (m + 1) k st b =
      ((kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).1 ++
        ([kecS (kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.1
          (runV (kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 (kOutN B n k))
          (k % 2 == 1) (!(k + 1 == B) && k % 2 == 0)] ++
        (kBlocks pad cs B tailRun none n m (k + 1)
          (some (runV (kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 13))
          ((kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 + kOutN B n k)).1),
        (kBlocks pad cs B tailRun none n m (k + 1)
          (some (runV (kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 13))
          ((kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 + kOutN B n k)).2.1,
        if k + 1 == B then (kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 else
          (kBlocks pad cs B tailRun none n m (k + 1)
            (some (runV (kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 13))
            ((kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 + kOutN B n k)).2.2) := by
  simp only [kBlocks, Option.getD_none, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, List.append_assoc]
  split <;> rfl

theorem kOutN_mid {B n k : Nat} (hk : k + 1 ≠ B) : kOutN B n k = 13 := by
  simp [kOutN, hk]

theorem kOutN_cellCount {B n k : Nat} (hn : n = 1 ∨ n = 2 ∨ n = 13) :
    kOutN B n k = 1 ∨ kOutN B n k = 2 ∨ kOutN B n k = 13 := by
  unfold kOutN; split
  · exact hn
  · exact .inr (.inr rfl)

theorem kBlocks_nb {pad : Nat} {cs : List KC} {B n : Nat} {tailRun : Bool} :
    ∀ (m k : Nat) (st : Option (List V)) (b : Nat), k + m ≤ B → pad + 5 ≤ b →
      (∀ c ∈ cs, KCb b c) → (∀ s, st = some s → ∀ v ∈ s, NBv b v) →
      NumBelow (kBlocks pad cs B tailRun none n m k st b).2.1
          (Stmt.valsList (kBlocks pad cs B tailRun none n m k st b).1) ∧
        b ≤ (kBlocks pad cs B tailRun none n m k st b).2.1
  | 0, _, _, b, _, _, _, _ => ⟨NumBelow.nil _, le_rfl⟩
  | m + 1, k, st, b, hkm, hpb, hcs, hst => by
      rw [kBlocks_none_eq]
      dsimp only
      obtain ⟨i1, i2, i3⟩ := kIns_seq (pad := pad) (tailRun := tailRun)
        (blk := (cs.drop (17 * k / 2)).take 9) hpb hst (fun c hc => hcs c (blockOf_mem hc))
      set o := (kIns pad ((cs.drop (17 * k / 2)).take 9) tailRun st b).2.2 with ho
      obtain ⟨r1, r2⟩ : NumBelow (kBlocks pad cs B tailRun none n m (k + 1) (some (runV o 13))
            (o + kOutN B n k)).2.1
          (Stmt.valsList (kBlocks pad cs B tailRun none n m (k + 1) (some (runV o 13))
            (o + kOutN B n k)).1) ∧
          o + kOutN B n k ≤ (kBlocks pad cs B tailRun none n m (k + 1) (some (runV o 13))
            (o + kOutN B n k)).2.1 := by
        by_cases hl : k + 1 = B
        · obtain rfl : m = 0 := by omega
          exact ⟨NumBelow.nil _, le_rfl⟩
        · rw [kOutN_mid hl]
          exact kBlocks_nb m (k + 1) (some (runV o 13)) (o + 13) (by omega) (by omega)
            (fun c hc => (hcs c hc).mono (by omega))
            (fun s hs v hv => by cases hs; exact runV_nb (by omega) v hv)
      refine ⟨?_, by omega⟩
      rw [valsList_append, valsList_append]
      refine (i1.numBelow.mono (by omega)).append (NumBelow.append ?_ r1)
      simp only [kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨j, hj, rfl⟩ := i2 v hv
        exact ⟨j, by omega, rfl⟩
      · exact runV_nb (by omega) v hv

/-- **The blocks complete**, the last writing `n` cells (one, two or thirteen). -/
theorem kBlocks_complete {pad : Nat} {cs : List KC} {B n : Nat} {tailRun : Bool}
    (hn : n = 1 ∨ n = 2 ∨ n = 13) :
    ∀ (m k : Nat) (st : Option (List V)) (b : Nat) (σ : Val), k + m ≤ B → PadOK σ pad →
      pad + 5 ≤ b → (∀ c ∈ cs, KCb b c) → (∀ s, st = some s → ∀ v ∈ s, NBv b v) →
      (st = none → tailRun = true → TailCells (blockOf cs k)) →
      Completes C rd b (kBlocks pad cs B tailRun none n m k st b).2.1
          (kBlocks pad cs B tailRun none n m k st b).1 σ (fun _ => True) ∧
        NumBelow (kBlocks pad cs B tailRun none n m k st b).2.1
          (Stmt.valsList (kBlocks pad cs B tailRun none n m k st b).1) ∧
        b ≤ (kBlocks pad cs B tailRun none n m k st b).2.1
  | 0, _, _, b, σ, _, _, _, _, _, _ =>
      ⟨⟨σ, Ext.refl _ _ _, trivial, fun _ _ hn => hn⟩, NumBelow.nil _, le_rfl⟩
  | m + 1, k, st, b, σ, hkm, hp, hpb, hcs, hst, htr => by
      obtain ⟨n1, n2⟩ := kBlocks_nb (pad := pad) (cs := cs) (B := B) (n := n) (tailRun := tailRun)
        (m + 1) k st b hkm hpb hcs hst
      rw [kBlocks_none_eq]
      dsimp only
      set blk := (cs.drop (17 * k / 2)).take 9 with hblk
      have hblkb : ∀ c ∈ blk, KCb b c := fun c hc => hcs c (blockOf_mem hc)
      obtain ⟨i1, i2, i3⟩ := kIns_seq (pad := pad) (tailRun := tailRun) (blk := blk) hpb hst hblkb
      have hlen : (kIns pad blk tailRun st b).2.1.length = 13 := kIns_length htr b
      set ins := kIns pad blk tailRun st b with hins
      rw [kBlocks_none_eq] at n1 n2
      dsimp only at n1 n2
      rw [← hblk, ← hins] at n1 n2
      refine ⟨?_, n1, n2⟩
      set w := kOutN B n k with hw
      have hr : ∀ σ2 : Val, PadOK σ2 pad →
          Completes C rd (ins.2.2 + w)
            (kBlocks pad cs B tailRun none n m (k + 1) (some (runV ins.2.2 13)) (ins.2.2 + w)).2.1
            (kBlocks pad cs B tailRun none n m (k + 1) (some (runV ins.2.2 13)) (ins.2.2 + w)).1
            σ2 (fun _ => True) ∧
          NumBelow (kBlocks pad cs B tailRun none n m (k + 1) (some (runV ins.2.2 13))
            (ins.2.2 + w)).2.1
            (Stmt.valsList (kBlocks pad cs B tailRun none n m (k + 1) (some (runV ins.2.2 13))
              (ins.2.2 + w)).1) ∧
          ins.2.2 + w ≤ (kBlocks pad cs B tailRun none n m (k + 1) (some (runV ins.2.2 13))
            (ins.2.2 + w)).2.1 := by
        intro σ2 hp2
        by_cases hl : k + 1 = B
        · obtain rfl : m = 0 := by omega
          exact ⟨⟨σ2, Ext.refl _ _ _, trivial, fun _ _ hn => hn⟩, NumBelow.nil _, le_rfl⟩
        · have hw13 : w = 13 := kOutN_mid hl
          rw [hw13]
          exact kBlocks_complete hn m (k + 1) (some (runV ins.2.2 13)) (ins.2.2 + 13) σ2
            (by omega) hp2 (by omega) (fun c hc => (hcs c hc).mono (by omega))
            (fun s hs v hv => by cases hs; exact runV_nb (by omega) v hv) (fun h => by simp at h)
      obtain ⟨r1, r2⟩ : NumBelow (kBlocks pad cs B tailRun none n m (k + 1)
            (some (runV ins.2.2 13)) (ins.2.2 + w)).2.1
          (Stmt.valsList (kBlocks pad cs B tailRun none n m (k + 1) (some (runV ins.2.2 13))
            (ins.2.2 + w)).1) ∧
          ins.2.2 + w ≤ (kBlocks pad cs B tailRun none n m (k + 1) (some (runV ins.2.2 13))
            (ins.2.2 + w)).2.1 := by
        by_cases hl : k + 1 = B
        · obtain rfl : m = 0 := by omega
          exact ⟨NumBelow.nil _, le_rfl⟩
        · rw [show w = 13 from kOutN_mid hl]
          exact kBlocks_nb m (k + 1) (some (runV ins.2.2 13)) (ins.2.2 + 13) (by omega) (by omega)
            (fun c hc => (hcs c hc).mono (by omega))
            (fun s hs v hv => by cases hs; exact runV_nb (by omega) v hv)
      refine Completes.append (m := ins.2.2) i3 (by omega) i1.numBelow (seq_completes i1 σ)
        (fun σ1 he1 hh1 => ?_)
      have hag1 : AgreeBelow b σ σ1 := he1.agree
      have hp1 := hp.congr hpb hag1
      refine Completes.append (m := ins.2.2 + w) (by omega) r2 ?_
        (kecS_complete σ1 ins.2.2 (kOutN_cellCount hn) hlen i2 _ _)
        (fun σ2 he2 hpost => ?_)
      · simp only [kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨j, hj, rfl⟩ := i2 v hv
          exact ⟨j, by omega, rfl⟩
        · exact runV_nb (by omega) v hv
      have hag2 : AgreeBelow ins.2.2 σ1 σ2 := he2.agree
      exact (hr σ2 (hp1.congr (by omega) hag2)).1

theorem kMsg_eq (pad : Nat) (cells : List KC) (len : Nat) (tailRun : Bool) (b n : Nat) :
    kMsg pad cells len tailRun none b n =
      let cs0 := cells ++ List.replicate (17 * (kBlocksOf len - 1) / 2 + 9 - cells.length) KC.zero
      let x1 := kXorByte cs0 len 1 b
      let x2 := kXorByte x1.2.1 (136 * kBlocksOf len - 1) 0x80 x1.2.2
      ((x1.1 ++ x2.1) ++
          (kBlocks pad x2.2.1 (kBlocksOf len) tailRun none n (kBlocksOf len) 0 none x2.2.2).1,
        (kBlocks pad x2.2.1 (kBlocksOf len) tailRun none n (kBlocksOf len) 0 none x2.2.2).2.1,
        (kBlocks pad x2.2.1 (kBlocksOf len) tailRun none n (kBlocksOf len) 0 none x2.2.2).2.2) :=
  rfl
/-- **The Keccak message completes**, its last block writing `n` cells (one, two or thirteen). -/
theorem kMsg_complete {pad : Nat} {cells : List KC} {len : Nat} {tailRun : Bool} {b : Nat}
    (σ : Val) (hp : PadOK σ pad) (hpb : pad + 5 ≤ b) (hc : ∀ c ∈ cells, KCb b c)
    (htr : tailRun = true → TailCells (blockOf (kMsgCells cells len b) 0)) (n : Nat := 1)
    (hn : n = 1 ∨ n = 2 ∨ n = 13 := by decide) :
    Completes C rd b (kMsg pad cells len tailRun none b n).2.1 (kMsg pad cells len tailRun none b n).1
        σ (fun _ => True) ∧
      NumBelow (kMsg pad cells len tailRun none b n).2.1
        (Stmt.valsList (kMsg pad cells len tailRun none b n).1) ∧
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
  obtain ⟨n1, n2⟩ := kBlocks_nb (pad := pad) (cs := x2.2.1) (B := kBlocksOf len) (n := n)
    (tailRun := tailRun) (kBlocksOf len) 0 none x2.2.2 (by omega) (by omega) b2
    (fun s hs => by simp at hs)
  refine ⟨?_, by rw [valsList_append]; exact (hs.numBelow.mono n2).append n1, by omega⟩
  refine Completes.append (m := x2.2.2) (by omega) n2 hs.numBelow (seq_completes hs σ)
    (fun σ1 he1 hh1 => ?_)
  have hag1 : AgreeBelow b σ σ1 := he1.agree
  exact (kBlocks_complete (pad := pad) (cs := x2.2.1) (B := kBlocksOf len) (tailRun := tailRun) hn
    (kBlocksOf len) 0 none x2.2.2 σ1 (by omega) (hp.congr hpb hag1) (by omega)
    b2 (fun s hs => by simp at hs) (fun _ h => htr h)).1

end
end LeanVM.Guest.B1.Sig
