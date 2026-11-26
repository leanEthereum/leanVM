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
* `kMsg_out`, `kMsg_le`, `kMsg_numBelow`: a Keccak message's output and its values lie below the
  block's end.
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

/-! ## The codeword's and the message's bounds -/

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

end
end LeanVM.Guest.B1.Sig
