/-
  LeanVM.Guest.B1.Digest.ChildListComplete

  `child_claim_list_any`'s frame loops `__loop17` and `__loop18`, completely and placed: from the
  chain buffer's states and the honest records among the caller's words.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCLast
public import LeanVM.Guest.B1.Digest.ClaimListComplete
public import LeanVM.Guest.B1.Digest.LoopAtB

/-!
# The frames of child claims, placed

`recMem_group`: the records of claims `s, …, s + k - 1` of honest records are honest, the marks
`base · g^s`. `anyLoop_completeAt`: a frame loop of `m` claims a frame (`nb` blocks), run over
`M` frames from the counter `1`, is `CompleteAtD` (`anyLoop_completeAtB`: within `M + 1` frames)
given, at every frame `q ≤ M`, the sponge state
after whole blocks `pre0` and the first `4mq` cells at `chain · g^(13q)` (`any_core` at each
counter `g^q`, `loopA_completeAt`). `any136_completeAt`, `any17_completeAt`: `__loop17`,
`__loop18`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Memory (atomUnplaced)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {rd : Reader}

/-- The records of the claims `s, …, s + k - 1`. -/
theorem recMem_group {region limit entries base : E} {n : ℕ} {o : ℕ → ℕ} {cells : List E}
    (h : RecMem rd region limit entries base n o cells) {s k : ℕ} (hsk : s + k ≤ n) :
    RecMem rd region limit entries (base * gen ^ s) k (fun j => o (s + j))
      ((cells.drop (4 * s)).take (4 * k)) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h (s + j) (by omega)
  refine ⟨h1, by rwa [mul_assoc, ← pow_add], fun c hc => ?_⟩
  have e : ((cells.drop (4 * s)).take (4 * k)).getD (4 * j + c) 0 =
      cells.getD (4 * (s + j) + c) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ite_pos' (by omega), show 4 * s + (4 * j + c) = 4 * (s + j) + c by ring]
  rw [e]
  exact h3 c hc

theorem boundMem_of_low {κ : ℕ} (hl : LowDef κ rd) {L : ℕ} (hL : L ≤ 2 ^ κ) : BoundMem rd L :=
  fun i hi => ⟨_, by rw [gen_pow_eq_ofK]; exact B1.loadHolds_low hl (by omega)⟩

set_option maxRecDepth 100000 in
theorem any136_unplaced :
    (atomsIn (loopPre (coreProgram.getD 378 default))).all atomUnplaced = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem any17_unplaced :
    (atomsIn (loopPre (coreProgram.getD 379 default))).all atomUnplaced = true := by decide +kernel

set_option maxRecDepth 20000 in
/-- **A frame loop of child claims, its frames**: at every frame `q < M`, the block's valuation
holds its atoms and reads the chain buffer's states and the records among the caller's words. -/
theorem anyLoop_blocks {j : ℕ} {f : String} {m o0 p0 mk st0 nb : ℕ}
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hhd : anycHead (coreProgram.getD j default) f = true)
    (hcn : anycCanon (coreProgram.getD j default) m o0 st0 = true)
    (hedge : anycEdge (coreProgram.getD j default) m o0 p0 mk st0 = true)
    (hrecs : ∀ i < m,
      recW (ccOwn (loopAtoms (coreProgram.getD j default)) p0 i) (anyP mk) o0 i = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (h64 : 64 * m = 136 * nb) {κ : ℕ} {Lin : Main.Layout} {chain entries region base last : E}
    {chP eP rg L M n0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ} {cells : List E}
    (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length) (hc : AllCanonical cells)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre0 ++ cellsBytes (cells.take (4 * m * q))))) ∧
      RecMem rd region (gen ^ L) entries base (m * M) o cells)
    (hR1 : ∀ q < M, ∀ c < 26, RegionL Lin (chP + 13 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o i))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o i + c)) :
    ∀ q < M, LoopBlockIn κ (coreProgram.getD j default) Lin q (gen ^ M)
      [chain, entries, region, base, last] := by
  intro q hq rd hlow hLin
  obtain ⟨hS, hrec⟩ := hmem rd hLin
  have hmq : m * q + m ≤ m * M := by nlinarith
  have h1 : 4 * m * q ≤ cells.length := le_trans (by nlinarith) hl
  have h2 : 4 * m * q + 4 * m ≤ cells.length := le_trans (by nlinarith) hl
  have hpre : (pre0 ++ cellsBytes (cells.take (4 * m * q))).length = rate * (n0 + nb * q) := by
    rw [List.length_append, length_cellsBytes, List.length_take, Nat.min_eq_left h1, hpre0]
    show 136 * n0 + 16 * (4 * m * q) = 136 * (n0 + nb * q)
    have : 16 * (4 * m * q) = (64 * m) * q := by ring
    rw [this, h64]; ring
  have hS0 := hS q (by omega)
  have hS1 := hS (q + 1) (by omega)
  rw [show 4 * m * (q + 1) = 4 * m * q + 4 * m by ring, List.take_add, cellsBytes_append,
    ← List.append_assoc, show nb * (q + 1) = nb * q + nb by ring, ← Nat.add_assoc] at hS1
  have hr := recMem_group hrec (s := m * q) (k := m) hmq
  rw [show 4 * (m * q) = 4 * m * q by ring, show base * gen ^ (m * q) = base * (gen ^ q) ^ m by
    rw [gen_pow_pow]] at hr
  obtain ⟨σ, hp, hat, hload⟩ := any_core hok hhd hcn hedge hrecs hnb (x := gen ^ q) (N := gen ^ M)
    rfl hch hen hrg hpre (by rw [gen_pow_pow]; exact hS0)
    (cells := (cells.drop (4 * m * q)).take (4 * m))
    (by simp only [List.length_take, List.length_drop]; omega)
    (canon_take (canon_drop hc _) _) hr hlast hL33 (boundMem_of_low hlow hLκ) (fun c => by
      have := hS1 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow]
      rw [loadHolds_mul_gen_pow, show 13 * (q + 1) + (0 + c.val) = 13 * q + (13 + c.val) by ring]
        at this
      exact this)
  refine ⟨σ, hp, hat, fun q' hq' => ?_⟩
  rcases hload q' hq' with ⟨c, hc26, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, c, hc4, h⟩
  · exact ⟨_, h, hR1 q hq c hc26⟩
  · exact ⟨_, h, hR2 (m * q + i) (by omega)⟩
  · exact ⟨_, h, hR3 (m * q + i) (by omega) c hc4⟩

/-- **A frame loop of child claims is complete, placed, within its frames**: `M` frames of `m`
claims from the counter `1`, the chain buffer's states at `g^chP`, the records' marks and cells
among the caller's words; `M + 1` frames of words. -/
theorem anyLoop_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {j : ℕ} {f : String}
    {m o0 p0 mk st0 nb : ℕ} (hf : coreProgram.find? f = some (coreProgram.getD j default))
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hhd : anycHead (coreProgram.getD j default) f = true)
    (hcn : anycCanon (coreProgram.getD j default) m o0 st0 = true)
    (hedge : anycEdge (coreProgram.getD j default) m o0 p0 mk st0 = true)
    (hrecs : ∀ i < m,
      recW (ccOwn (loopAtoms (coreProgram.getD j default)) p0 i) (anyP mk) o0 i = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (hun : (atomsIn (loopPre (coreProgram.getD j default))).all atomUnplaced = true)
    (h64 : 64 * m = 136 * nb) {κ : ℕ} {Lin : Main.Layout} {chain entries region base last : E}
    {chP eP rg L M n0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ} {cells : List E}
    (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length) (hc : AllCanonical cells)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ) (hM : M < 2 ^ 34)
    (hM0 : 0 < M)
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre0 ++ cellsBytes (cells.take (4 * m * q))))) ∧
      RecMem rd region (gen ^ L) entries base (m * M) o cells)
    (hR1 : ∀ q < M, ∀ c < 26, RegionL Lin (chP + 13 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o i))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o i + c)) :
    CompleteAtDTB fs cert κ f Lin [1, gen ^ M, chain, entries, region, base, last] (Returns [])
      (fun _ => True) ((M + 1) * fs f) := by
  have hshape : loopShapeF (coreProgram.getD j default) f = true := by
    simp only [anycHead, Bool.and_eq_true] at hhd; exact hhd.1.1.1.1
  have hAS : (loopPre (coreProgram.getD j default)).all isAtomS = true := by
    simp only [anycHead, Bool.and_eq_true] at hhd; exact hhd.1.1.2
  have h := loopA_completeAtB fs cert hf hshape hAS hun (Lin := Lin) (κ := κ) (N := gen ^ M)
    (rest := [chain, entries, region, base, last]) (m := M) rfl hM
    (anyLoop_blocks hok hhd hcn hedge hrecs hnb h64 hch hen hrg hpre0 hl hc hlast hL33 hLκ hmem hR1
      hR2 hR3)
  have := h 0 hM0
  rwa [pow_zero, Nat.sub_zero] at this

/-- **A frame loop of child claims is complete, placed**: `M` frames of `m` claims from the
counter `1`, the chain buffer's states at `g^chP`, the records' marks and cells among the
caller's words. -/
theorem anyLoop_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {j : ℕ} {f : String}
    {m o0 p0 mk st0 nb : ℕ} (hf : coreProgram.find? f = some (coreProgram.getD j default))
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hhd : anycHead (coreProgram.getD j default) f = true)
    (hcn : anycCanon (coreProgram.getD j default) m o0 st0 = true)
    (hedge : anycEdge (coreProgram.getD j default) m o0 p0 mk st0 = true)
    (hrecs : ∀ i < m,
      recW (ccOwn (loopAtoms (coreProgram.getD j default)) p0 i) (anyP mk) o0 i = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (hun : (atomsIn (loopPre (coreProgram.getD j default))).all atomUnplaced = true)
    (h64 : 64 * m = 136 * nb) {κ : ℕ} {Lin : Main.Layout} {chain entries region base last : E}
    {chP eP rg L M n0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ} {cells : List E}
    (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length) (hc : AllCanonical cells)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ) (hM : M < 2 ^ 34)
    (hM0 : 0 < M)
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre0 ++ cellsBytes (cells.take (4 * m * q))))) ∧
      RecMem rd region (gen ^ L) entries base (m * M) o cells)
    (hR1 : ∀ q < M, ∀ c < 26, RegionL Lin (chP + 13 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o i))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o i + c)) :
    CompleteAtD fs cert κ f Lin [1, gen ^ M, chain, entries, region, base, last] (Returns []) :=
  (anyLoop_completeAtB fs cert hf hok hhd hcn hedge hrecs hnb hun h64 hch hen hrg hpre0 hl hc hlast
    hL33 hLκ hM hM0 hmem hR1 hR2 hR3).toDT.toD

end
end LeanVM.Guest.B1.Digest
