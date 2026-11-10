import Rv64Verifier.Proofs.Walk.TailG
import Rv64Verifier.Proofs.Main.ParseBase

/-!
# `walk` R19, the public input's claims: the mirror and the loop's head

`publicInputRust` is a sample, then the three claims (`pubClaims`) when `log_memory > 0`, else a
failure (`publicInput_split`). The machine evaluates each memory limb's two words at the challenge
in a two-element `Vec`: `lo + (lo + hi) * c` (`mle_two`). `HeadR19`: at the claims loop's head
`0x80003b80`, `i` of the three claims pushed.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript

theorem mle_two (a b c : E) : multilinearEvalRust [a, b] [c] = some (a + (a + b) * c) := by
  simp [multilinearEvalRust, mlePass, mleStep]

/-- The public input's claims, the challenge `c` drawn. -/
def pubClaims (layout : LayoutMirror.LayoutRust) (pi : List (BitVec 8)) (c : E) :
    List ColumnClaim :=
  let h := halvesRust (digestWordsRust pi)
  let pt := c :: List.replicate (layout.logMemory - 1) 0
  [⟨memory0, pt, ofK (h.1.limb 0) + (ofK (h.1.limb 0) + ofK (h.2.limb 0)) * c⟩,
    ⟨memory1, pt, ofK (h.1.limb 1) + (ofK (h.1.limb 1) + ofK (h.2.limb 1)) * c⟩,
    ⟨memory2, pt, ofK (h.1.limb 2) + (ofK (h.1.limb 2) + ofK (h.2.limb 2)) * c⟩]

/-- After the sample: the claims, or a failure when `log_memory` is zero. -/
def pubRest (layout : LayoutMirror.LayoutRust) (pi : List (BitVec 8)) (c : E) :
    TM (List ColumnClaim) :=
  if 0 < layout.logMemory then pure (pubClaims layout pi c) else TM.fail

theorem publicInput_split (layout : LayoutMirror.LayoutRust) (pi : List (BitVec 8)) :
    publicInputRust layout pi = TM.sample >>= pubRest layout pi := by
  rcases Nat.eq_zero_or_pos layout.logMemory with h0 | h0
  · have e : pubRest layout pi = fun _ ↦ TM.fail := funext fun _ ↦ by simp [pubRest, h0]
    rw [e]
    simp only [publicInputRust, h0, setRust, List.replicate_zero, List.length_nil,
      Nat.lt_irrefl, ite_false, TM.ofOption]
    rfl
  · have e : pubRest layout pi = fun c ↦ pure (pubClaims layout pi c) :=
      funext fun _ ↦ by simp [pubRest, h0]
    rw [e]
    obtain ⟨n, hn⟩ : ∃ n, layout.logMemory = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
    simp only [publicInputRust, pubClaims, hn, mle_two, setRust, TM.ofOption,
      List.replicate_succ, List.length_cons, Nat.zero_lt_succ, ite_true, List.set_cons_zero,
      pure_bind, Nat.add_sub_cancel]

/-- `afterTables` past the sample. -/
theorem afterTables_sample (pi : List (BitVec 8)) (layout : LayoutMirror.LayoutRust)
    (rows : List (BitVec 64)) (lir : BitVec 64) (bus : BusResultRust)
    (evs : List (List E × List E)) :
    afterTables pi layout rows lir bus evs = TM.sample >>= fun c ↦ pubRest layout pi c >>=
      afterPublic layout rows lir bus evs (bus.claims ++ tableClaimsRust evs) := by
  rw [afterTables_stages, publicInput_split, bind_assoc]

theorem pubRest_pos {layout : LayoutMirror.LayoutRust} {pi : List (BitVec 8)} {c : E}
    {K : List ColumnClaim → TM SummaryRust} (h0 : 0 < layout.logMemory) :
    pubRest layout pi c >>= K = K (pubClaims layout pi c) := by
  simp only [pubRest, h0, ite_true, pure_bind]

/-- Limb `j` of the public input's first half, as a word: `w0`, `w1`, `0`. -/
def pubLo (s : MachineState) : Nat → Word
  | 0 => s.getMem (s.getReg .x12)
  | 1 => s.getMem (s.getReg .x12 + 8)
  | _ => 0

/-- Limb `j` of the second half: `w2`, `w3`, `0`. -/
def pubHi (s : MachineState) : Nat → Word
  | 0 => s.getMem (s.getReg .x12 + 16)
  | 1 => s.getMem (s.getReg .x12 + 24)
  | _ => 0

theorem pub_limbs {s : MachineState} (hpre : WalkPre s) (j : Fin 3) :
    (halvesRust (digestWordsRust (bytesAt s (s.getReg .x12) 32))).1.limb j =
      BF64.ofBitVec (pubLo s j) ∧
    (halvesRust (digestWordsRust (bytesAt s (s.getReg .x12) 32))).2.limb j =
      BF64.ofBitVec (pubHi s j) := by
  have ha : (s.getReg .x12).toNat % 8 = 0 := hpre.input.2
  have w (k : Nat) (hk : k < 4) := Proofs.Main.digestWords_at s ha hk
  simp only [halvesRust]
  rw [w 0 (by decide), w 1 (by decide), w 2 (by decide), w 3 (by decide)]
  fin_cases j <;> simp [pubLo, pubHi, E.ofLimbs, E.limb, CompPoly.Extension.Ext.coeff,
    CompPoly.Extension.Ext.ofVector]
  rfl

/-- At `0x80003b80`, `i` of the public input's three claims pushed (`L + i` claims): the point
`c, 0, ..`'s buffer at `S - 2520` (`n` = `log_memory` at `S - 2512`), the halves' limb words at
`S - 912 + 16 j`, the columns at `S - 848 + 8 j`, the challenge's words at `S - 2528` down. -/
structure HeadR19 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (i : Nat) (c : E) (pt : Word) : Prop
    extends CoreT OI s u₀ w t u layout lir evs P C (L.toNat + i)
      (bus.claims ++ tableClaimsRust evs ++
        (pubClaims layout (bytesAt s (s.getReg .x12) 32) c).take i)
      (afterPublic layout rows lir bus evs (bus.claims ++ tableClaimsRust evs)
        (pubClaims layout (bytesAt s (s.getReg .x12) 32) c)) where
  pc : u.pc = 0x80003b80
  hi : i < 3
  x12 : u.getReg .x12 = BitVec.ofNat 64 i
  x20 : u.getReg .x20 = (limbs c).1
  x21 : u.getReg .x21 = (limbs c).2.1
  x27 : u.getReg .x27 = (limbs c).2.2
  x24 : u.getReg .x24 = s.getReg .x2 - 512
  x25 : u.getReg .x25 = L + BitVec.ofNat 64 i
  lenSlot : u.getMem (s.getReg .x2 - 1616) = L + BitVec.ofNat 64 i
  ptr184 : u.getMem (s.getReg .x2 - 2472) = P
  c0 : u.getMem (s.getReg .x2 - 2528) = (limbs c).1
  c1 : u.getMem (s.getReg .x2 - 2536) = (limbs c).2.1
  c2 : u.getMem (s.getReg .x2 - 2544) = (limbs c).2.2
  ptSlot : u.getMem (s.getReg .x2 - 2520) = pt
  nSlot : (u.getMem (s.getReg .x2 - 2512)).toNat = layout.logMemory
  hn : 0 < layout.logMemory
  ptOld : Old s u pt (24 * layout.logMemory) ∧ heapNext t ≤ pt.toNat
  ptVal : eListAt u pt layout.logMemory = c :: List.replicate (layout.logMemory - 1) 0
  ptApart : Apart pt (24 * layout.logMemory) P (56 * C.toNat)
  pairs : ∀ j < 3, u.getMem (s.getReg .x2 - 912 + BitVec.ofNat 64 (16 * j)) = pubLo s j ∧
    u.getMem (s.getReg .x2 - 904 + BitVec.ofNat 64 (16 * j)) = pubHi s j
  cols : ∀ j < 3, u.getMem (s.getReg .x2 - 848 + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 j

/-- A step, then writes into what it allocated and into frame bytes `W'`: one step. -/
theorem StepW.thenW {s a b c : MachineState} (hpre : WalkPre s) {W W' : Word → Prop} {T : Prop}
    (ha : HeapOk a) (st : StepW s a b W T) (hW' : ∀ x, W' x → InF s x) {X : Word} {n : Nat}
    (fr : DFrame b c fun x ↦ W' x ∨ Within x X n) (h1 : heapNext a ≤ X.toNat)
    (h2 : X.toNat + n ≤ heapNext b) (sp : c.getReg .x2 = b.getReg .x2) :
    StepW s a c (fun x ↦ W x ∨ W' x) T := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hb := st.heap.hi
  have hm := st.mono
  have hl := ha.lo
  have hn : c.getMem nextAddr = b.getMem nextAddr := fr nextAddr fun i hi hw ↦ by
    simp only [heapNext, heapEnd, heapStart] at hb hm h1 h2 hl
    rcases hw with hw | hw
    · have := hW' _ hw; simp only [InF] at this; addr_omega [this, hi, hb1]
    · simp only [Within] at hw; addr_omega [hw, hi, h2, hb]
  have hn' : heapNext c = heapNext b := by simp only [heapNext, hn]
  refine ⟨(st.frame.mono fun x hx ↦ ?_).trans fr fun x hx ↦ ?_, ⟨hn' ▸ st.heap.lo, hn' ▸ st.heap.hi⟩,
    hn' ▸ st.mono, sp.trans st.sp⟩
  · simp only [Fresh] at hx ⊢
    rw [hn']
    rcases hx with hx | hx | hx | hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
  · simp only [Fresh]
    rw [hn']
    rcases hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · simp only [Within] at hx
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))

end Rv64Verifier.Proofs.Walk
