module

public import LeanVM.Guest.Complete.Claims.MonoBody
public import LeanVM.Guest.Complete.Claims.AnyLoops
import LeanVM.Guest.ValRef

/-!
# `child_claim_list_mono`'s callees, placed

`monoL_callAtA`: a frame loop of the gap walk (`child_claim_list_mono_loop0`, `_loop1`: params
`[x, N, chain, mark]`) entered at `1` completes placed from its blocks (`mono_core` at each counter,
the claims by `mRec_group`), its loads the chain buffer's records, the claims' coverage slots and
cells in the region. `mlc_callAtA`: `child_claim_list_mono_last__L{r}` a leaf placed from its
valuation per memory (`mlc_core`, `callAtA_leaf`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-! ## The frame loops -/

set_option maxRecDepth 100000 in
theorem monoLoop0_facts : coreProgram.loop name% «child_claim_list_mono_loop0» = true ∧
    loopShapeF (coreProgram.getD idx% «child_claim_list_mono_loop0» default) name% «child_claim_list_mono_loop0» = true ∧
    (coreProgram.getD idx% «child_claim_list_mono_loop0» default).params = [.n 0, .n 1, .n 2, .n 3] ∧
    (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop0» default)).all loopPlainHB = true ∧
    (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop0» default)).all noHeapHintC = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem monoLoop1_facts : coreProgram.loop name% «child_claim_list_mono_loop1» = true ∧
    loopShapeF (coreProgram.getD idx% «child_claim_list_mono_loop1» default) name% «child_claim_list_mono_loop1» = true ∧
    (coreProgram.getD idx% «child_claim_list_mono_loop1» default).params = [.n 0, .n 1, .n 2, .n 3] ∧
    (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop1» default)).all loopPlainHB = true ∧
    (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop1» default)).all noHeapHintC = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mono136_wits : (atomsIn (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop0» default))).flatMap
    atomWit = (List.range 136).map fun i => ("child_claim_gap", Dest.stack [V.n (13 + 10 * i)]) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mono17_wits : (atomsIn (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop1» default))).flatMap
    atomWit = (List.range 17).map fun i => ("child_claim_gap", Dest.stack [V.n (13 + 10 * i)]) := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **A frame loop of the gap walk entered at `1` completes placed**: `M` frames of `m` claims, the
records after each frame at `chain · g^(15q)`, the claims' coverage slots and cells in the region. -/
theorem monoL_callAtA {k : ℕ} {j : ℕ} {f : String} {m p0 st0 cw ew nb : ℕ}
    (hf : coreProgram.find? f = some (coreProgram.getD j default)) (hlp : coreProgram.loop f = true)
    (hshape : loopShapeF (coreProgram.getD j default) f = true)
    (hpl : (loopPre (coreProgram.getD j default)).all loopPlainHB = true)
    (hnh : (loopPre (coreProgram.getD j default)).all noHeapHintC = true)
    (hok : monoOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hc : mcOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hew : word ew 0 = gen ^ (4 * m))
    (hnb : (monoSpec m st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (hwit : (atomsIn (loopPre (coreProgram.getD j default))).flatMap atomWit =
      (List.range m).map fun i => ("child_claim_gap", Dest.stack [V.n (13 + 10 * i)]))
    (h64 : 64 * m = 136 * nb) (hm0 : 0 < m) {mark : E} {chP eP rg L M n0 s0 : ℕ} {pre0 : List UInt8}
    {o : ℕ → ℕ} {cells : List E} (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length)
    (hM : M < 2 ^ 34) (hM0 : M ≠ 0) (hinc : ∀ i < m * M, mStart o (s0 + i) ≤ o (s0 + i))
    {R : ℕ → Prop} {Pre : Reader → Prop}
    (hmem : ∀ rd, LowDef k rd → Pre rd → (∀ q ≤ M, MonoRecAt rd (gen ^ chP * gen ^ (15 * q)) (n0 + nb * q)
        (pre0 ++ cellsBytes (cells.take (4 * m * q))) (gen ^ rg) (gen ^ eP) (mStart o (s0 + m * q))) ∧
      MRec rd (gen ^ rg) L (gen ^ eP) mark (m * M) (fun i => o (s0 + i)) cells ∧ BoundMem rd L)
    (hR1 : ∀ q < M, ∀ c < 30, R (chP + 15 * q + c)) (hR2 : ∀ i < m * M, R (rg + o (s0 + i)))
    (hR3 : ∀ i < m * M, ∀ c < 4, R (eP + 4 * o (s0 + i) + c)) (fp c : ℕ) (hfc : fp + lpBlk fs f M ≤ c) :
    CallAtA fs al cert k f [1, gen ^ M, gen ^ chP, mark] [] R (fun _ => False)
      (fun _ => True) Pre (fun rd t => t.pops coreProgram rd = gapPops o s0 (m * M)) (lpBlk fs f M) fp c c := by
  have hpreA : ∀ s ∈ loopPre (coreProgram.getD j default), ∃ a, s = .atom a := by
    intro s hs
    have := List.all_eq_true.mp hpl s hs
    cases s with
    | atom a => exact ⟨a, rfl⟩
    | _ => simp [loopPlainHB] at this
  have h := loopFHP_callAtA (fs := fs) (al := al) (cert := cert) (k := k) hf hshape hlp hpl hM
    (ps := fun q => gapPops o (s0 + m * q) m)
    (rest := [gen ^ chP, mark]) (R := R) (Pre := Pre) (fun q hq rd hlow hp => ?_)
    0 (Nat.pos_of_ne_zero hM0) fp c (by simpa using hfc)
  · rw [pow_zero, Nat.sub_zero] at h
    exact h.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h) fun rd t _ ht => by
      rw [ht, loopPopsFrom, Nat.sub_zero, gapPops_flatMap]
  obtain ⟨hR, hrec, hbd⟩ := hmem rd hlow hp
  have hmq : m * q + m ≤ m * M := by nlinarith
  have h1 : 4 * m * q ≤ cells.length := le_trans (by nlinarith) hl
  have h2 : 4 * m * q + 4 * m ≤ cells.length := le_trans (by nlinarith) hl
  have hpre : (pre0 ++ cellsBytes (cells.take (4 * m * q))).length = rate * (n0 + nb * q) := by
    rw [List.length_append, length_cellsBytes, List.length_take, Nat.min_eq_left h1, hpre0]
    show 136 * n0 + 16 * (4 * m * q) = 136 * (n0 + nb * q)
    have : 16 * (4 * m * q) = (64 * m) * q := by ring
    rw [this, h64]; ring
  obtain ⟨hS0, h13, h14⟩ := hR q (by omega)
  obtain ⟨hS1, h28, h29⟩ := hR (q + 1) (by omega)
  rw [show 4 * m * (q + 1) = 4 * m * q + 4 * m by ring, List.take_add, cellsBytes_append,
    ← List.append_assoc, show nb * (q + 1) = nb * q + nb by ring, ← Nat.add_assoc] at hS1
  have hr := mRec_group hrec (s := m * q) (k := m) hmq
  rw [show 4 * (m * q) = 4 * m * q by ring] at hr
  have e15 : gen ^ chP * gen ^ (15 * (q + 1)) = gen ^ chP * (gen ^ q) ^ 15 * gen ^ 15 := by
    rw [gen_pow_pow, mul_assoc, ← pow_add]; ring_nf
  rw [e15, loadHolds_mul_gen_pow] at h28 h29
  rw [show s0 + m * (q + 1) = s0 + m * q + m by ring] at h28 h29
  obtain ⟨σ, hp', hat, hload, hg⟩ := mono_core hok hc hcw hew hnb hm0 (x := gen ^ q) (N := gen ^ M)
    (chain := gen ^ chP) (mark := mark) (s := s0 + m * q) (o := o) (L := L) rfl rfl rfl rfl hpre
    (by rw [gen_pow_pow]; exact hS0) (by rw [gen_pow_pow]; exact h13)
    (by rw [gen_pow_pow]; exact h14)
    (cells := (cells.drop (4 * m * q)).take (4 * m))
    (by simp only [List.length_take, List.length_drop]; omega)
    (fun i hi => by rw [Nat.add_assoc]; exact hinc (m * q + i) (by omega))
    (by intro i hi; have := hr i hi; simp only [Nat.add_assoc] at this ⊢; exact this)
    hbd
    (fun c => by
      have := hS1 c
      rw [e15, loadHolds_mul_gen_pow, show 15 + (0 + c.val) = 15 + c.val by ring] at this
      exact this) h28 h29
  refine ⟨σ, hp', fun s hs => ?_, fun q' hq' => ?_, fun A hA => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hpreA s hs
    exact hat a (cl_mem_atoms hs)
  · have hq'' : q' ∈ (loopPre (coreProgram.getD j default)).filterMap B1.Stmt.loadS := by
      obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp hq'
      exact List.mem_filterMap.mpr ⟨s, hs, by rw [loadS_eq_stmtLoad]; exact he⟩
    rcases hload q' hq'' with ⟨c, hc30, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, c, hc4, h⟩
    · exact ⟨_, h, hR1 q hq c hc30⟩
    · rw [Nat.add_assoc s0] at h
      exact ⟨_, h, hR2 (m * q + i) (by omega)⟩
    · rw [Nat.add_assoc s0] at h
      exact ⟨_, h, hR3 (m * q + i) (by omega) c hc4⟩
  · rw [heapHintAddrs_nil_of hnh] at hA
    exact absurd hA List.not_mem_nil
  · rw [blockPops_of_good hpreA hg hwit, gapPops]
    exact List.map_congr_left fun i _ => by rw [show (13 + 10 * i - 13) / 10 = i by omega]

/-! ## The last group -/

set_option maxRecDepth 100000 in
/-- `child_claim_list_mono_last__L{r}`'s witness hints: its claims' gaps. -/
theorem ml_wits_all : ∀ r < 17, decide ((mlAtoms r).flatMap atomWit =
    (List.range r).map fun i => ("child_claim_gap", Dest.stack [V.n (6 + 10 * i)])) = true := by
  decide +kernel

theorem ml_wits (r : ℕ) (hr : r < 17) : (mlAtoms r).flatMap atomWit =
    (List.range r).map fun i => ("child_claim_gap", Dest.stack [V.n (6 + 10 * i)]) :=
  of_decide_eq_true (ml_wits_all r hr)

set_option maxRecDepth 100000 in
theorem ml_noHeap : ∀ r < 17, (mlAtoms r).all (fun a => (atomHeapDest? a).isNone) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ml_noAddr : ∀ r < 17,
    (mlAtoms r).all (fun a => match a with | .frameAddr .. => false | _ => true) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
/-- **`child_claim_list_mono_last__L{r}` completes placed**, a leaf at any frame and cursor: the
record at `g^rP`, the claims' coverage slots and cells in the region, the walk ending at most at
`L`. -/
theorem mlc_callAtA {k r : ℕ} (hr : r < 17) {rP eP rg L n s : ℕ} {mark : E} {pre : List UInt8}
    {o : ℕ → ℕ} {cells : List E} (hpre : pre.length = rate * n) (hl : cells.length = 4 * r)
    (hinc : ∀ i < r, mStart o (s + i) ≤ o (s + i)) (hend : mStart o (s + r) ≤ L)
    {R : ℕ → Prop} {Pre : Reader → Prop}
    (hmem : ∀ rd, LowDef k rd → Pre rd → MonoRecAt rd (gen ^ rP) n pre (gen ^ rg) (gen ^ eP) (mStart o s) ∧
      MRec rd (gen ^ rg) L (gen ^ eP) mark r (fun i => o (s + i)) cells ∧ BoundMem rd (L + 1))
    (hR1 : ∀ c < 15, R (rP + c)) (hR2 : ∀ i < r, R (rg + o (s + i)))
    (hR3 : ∀ i < r, ∀ c < 4, R (eP + 4 * o (s + i) + c)) (fp c : ℕ) :
    CallAtA fs al cert k (mlNames.getD r "") [gen ^ rP, gen ^ rg, mark, gen ^ L]
      (digestCells (keccak256 (pre ++ cellsBytes cells))) R (fun _ => False) (fun _ => True) Pre
      (fun rd t => t.pops coreProgram rd = gapPops o s r) (fs (mlNames.getD r "")) fp c c := by
  have h := B1.VsC.callAtA_leaf (fs := fs) (al := al) (cert := cert) (k := k) (f := mlNames.getD r "")
    (args := [gen ^ rP, gen ^ rg, mark, gen ^ L]) (rets := digestCells (keccak256 (pre ++ cellsBytes cells)))
    (R := R) (D := fun _ => False) (Out := fun _ => True) (Pre := Pre)
    (Post := fun rd t => t.pops coreProgram rd = gapPops o s r) (fp := fp) (c := c)
    [] [] (ml_loop hr) ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial) (fun _ h => h.elim) (fun rd hlow _ hp => ?_)
  · simpa using h
  obtain ⟨hRa, hrec, hbd⟩ := hmem rd hlow hp
  obtain ⟨vs, σ, hb, hpar, hat, hret, hload, hg⟩ := mlc_core hr rfl rfl rfl rfl hpre hRa hl hinc hrec hend hbd
  have hw : walk σ (coreProgram.getD (idx% «child_claim_list_mono_last__L0» + r) default).body =
      .ret ((mlAtoms r).map Ev.atom) vs := by rw [hb, walk_atoms]
  refine ⟨σ, _, (mlAtoms r).map Ev.atom, vs, ml_name hr, hpar, hw, hret,
    calls_atoms _, Memory.allocs_atoms σ (ml_na hr), ⟨?_, fun q hq => ?_⟩, ?_, fun A hA => ?_, fun A hA => ?_, ?_⟩
  · rw [Memory.allocDsts_atoms (ml_na hr)]; rfl
  · rw [B1.VsC.addrs_atoms _ (ml_noAddr r hr)] at hq; exact absurd hq List.not_mem_nil
  · intro ev hev
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hev
    exact hat a ha
  · obtain ⟨d, p, off, ha, rfl⟩ := B1.VsC.mem_loadAddrs hA
    rcases hload (p, off) (List.mem_filterMap.mpr ⟨_, ha, rfl⟩) with ⟨c', hc, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, c', hc4, h⟩
    · exact ⟨_, h, Or.inr (hR1 c' hc)⟩
    · exact ⟨_, h, Or.inr (hR2 i hi)⟩
    · exact ⟨_, h, Or.inr (hR3 i hi c' hc4)⟩
  · rw [B1.VsC.heapHintAddrs_atoms _ (ml_noHeap r hr)] at hA; exact absurd hA List.not_mem_nil
  · rw [leaf_pops (ml_name hr) hw, atomsPops_of_good hg (ml_wits r hr), gapPops]
    exact List.map_congr_left fun i _ => by rw [show (6 + 10 * i - 6) / 10 = i by omega]

end
end LeanVM.Guest.Complete
