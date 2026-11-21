/-
  LeanVM.Guest.B1.Digest.ChildListAtP

  The walk by hinted indices' frame loops and last claims placed with their pops: each claim's hinted index, in
  order.
-/

module

public import LeanVM.Guest.B1.Digest.MonoAtNP

/-!
# The walk by hinted indices' helpers, with their pops

* `idxPops o s m`: claims `s ..< s + m`'s indices (`o`); `idxPops_append`, `idxPops_flatMap`, `idxPops_shift`;
* `anyLoop_blocksP`, `anyLoop_completeAtBP`, `ccl_completeAtBP`: `anyLoop_blocks`, `anyLoop_completeAtB`,
  `ccl_completeAtB` by trees popping their claims' indices (`any_core`'s, `ccl_core`'s oracle `slotW`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Memory (atomUnplaced)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB CompleteAtDTBR Returns LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

variable {rd : Reader}

/-- **Claims `s ..< s + m`'s indices.** -/
noncomputable def idxPops (o : ℕ → ℕ) (s m : ℕ) : List Pop :=
  (List.range m).map fun i => ("child_claim_index", [gen ^ o (s + i)])

theorem idxPops_append (o : ℕ → ℕ) (s A B : ℕ) : idxPops o s A ++ idxPops o (s + A) B = idxPops o s (A + B) := by
  simp only [idxPops, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Nat.add_assoc]

theorem idxPops_shift (o : ℕ → ℕ) (c s m : ℕ) : idxPops (fun i => o (c + i)) s m = idxPops o (c + s) m := by
  simp only [idxPops, Nat.add_assoc]

theorem idxPops_flatMap (o : ℕ → ℕ) (m : ℕ) : ∀ M : ℕ,
    (List.range' 0 M).flatMap (fun q => idxPops o (m * q) m) = idxPops o 0 (m * M)
  | 0 => by simp [idxPops]
  | M + 1 => by
    rw [← List.range'_append_1 (s := 0) (m := M) (n := 1), List.flatMap_append, idxPops_flatMap o m M]
    simp only [Nat.zero_add, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e := idxPops_append o 0 (m * M) m
    rw [Nat.zero_add] at e
    rw [e, Nat.mul_succ]

set_option maxRecDepth 100000 in
theorem any136_wits : (loopPre (coreProgram.getD idx% «child_claim_list_any_loop0» default)).filterMap
    Main.Stmt.popS = ((List.range 136).map fun i => ("child_claim_index", [V.n (ccOV 22 i)])).map
      fun x => some (x.1, .stack x.2) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any17_wits : (loopPre (coreProgram.getD idx% «child_claim_list_any_loop1» default)).filterMap
    Main.Stmt.popS = ((List.range 17).map fun i => ("child_claim_index", [V.n (ccOV 19 i)])).map
      fun x => some (x.1, .stack x.2) := by
  decide +kernel

/-- `child_claim_list_last__L{k}`'s witness hints: its claims' indices. -/
noncomputable def cclWitOk (k : ℕ) : Bool :=
  decide ((cclAtoms k).flatMap atomWit = ((List.range k).map fun i => ("child_claim_index", [V.n (ccOV 5 i)])).map
    fun x => (x.1, .stack x.2))

set_option maxRecDepth 100000 in
theorem ccl_wits_all : ∀ k < 17, cclWitOk k = true := by decide +kernel

theorem ccl_wits (k : ℕ) (hk : k < 17) : (cclAtoms k).flatMap atomWit =
    ((List.range k).map fun i => ("child_claim_index", [V.n (ccOV 5 i)])).map fun x => (x.1, .stack x.2) :=
  of_decide_eq_true (ccl_wits_all k hk)

set_option maxRecDepth 20000 in
/-- **A frame loop of child claims, its frames, with their pops**: `anyLoop_blocks`, frame `q` popping its claims'
indices. -/
theorem anyLoop_blocksP {j : ℕ} {f : String} {m o0 p0 mk st0 nb : ℕ}
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hhd : anycHead (coreProgram.getD j default) f = true)
    (hedge : anycEdge (coreProgram.getD j default) m o0 p0 mk st0 = true)
    (hrecs : ∀ i < m,
      recW (ccOwn (loopAtoms (coreProgram.getD j default)) p0 i) (anyP mk) o0 i = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (h64 : 64 * m = 136 * nb) {κ : ℕ} {Lin : Main.Layout} {chain entries region base last : E}
    {chP eP rg L M n0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ} {cells : List E}
    (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre0 ++ cellsBytes (cells.take (4 * m * q))))) ∧
      RecMem rd region (gen ^ L) entries base (m * M) o cells)
    (hR1 : ∀ q < M, ∀ c < 26, RegionL Lin (chP + 13 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o i))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o i + c))
    (hwit : (loopPre (coreProgram.getD j default)).filterMap Main.Stmt.popS =
      ((List.range m).map fun i => ("child_claim_index", [V.n (ccOV o0 i)])).map fun x => some (x.1, .stack x.2)) :
    ∀ q < M, LoopBlockInP κ (coreProgram.getD j default) Lin q (gen ^ M)
      [chain, entries, region, base, last] (idxPops o (m * q) m) := by
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
  obtain ⟨σ, hp, hat, hload, hg⟩ := any_core hok hhd hedge hrecs hnb (x := gen ^ q) (N := gen ^ M)
    rfl hch hen hrg hpre (by rw [gen_pow_pow]; exact hS0)
    (cells := (cells.drop (4 * m * q)).take (4 * m))
    (by simp only [List.length_take, List.length_drop]; omega)
    hr hlast hL33 (boundMem_of_low hlow hLκ) (fun c => by
      have := hS1 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow]
      rw [loadHolds_mul_gen_pow, show 13 * (q + 1) + (0 + c.val) = 13 * q + (13 + c.val) by ring]
        at this
      exact this)
  refine ⟨σ, hp, hat, fun q' hq' => ?_, ?_⟩
  · rcases hload q' hq' with ⟨c, hc26, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, c, hc4, h⟩
    · exact ⟨_, h, hR1 q hq c hc26⟩
    · exact ⟨_, h, hR2 (m * q + i) (by omega)⟩
    · exact ⟨_, h, hR3 (m * q + i) (by omega) c hc4⟩
  · rw [blockPops_wit hg hwit, idxPops, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, List.map_cons, List.map_nil, w_slot]

/-- **A frame loop of child claims is complete, placed, within its frames, popping its claims' indices.** -/
theorem anyLoop_completeAtBP (fs : String → ℕ) (cert : String → V → ℕ) {j : ℕ} {f : String}
    {m o0 p0 mk st0 nb : ℕ} (hf : coreProgram.find? f = some (coreProgram.getD j default))
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hhd : anycHead (coreProgram.getD j default) f = true)
    (hedge : anycEdge (coreProgram.getD j default) m o0 p0 mk st0 = true)
    (hrecs : ∀ i < m,
      recW (ccOwn (loopAtoms (coreProgram.getD j default)) p0 i) (anyP mk) o0 i = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (hun : (atomsIn (loopPre (coreProgram.getD j default))).all atomUnplaced = true)
    (h64 : 64 * m = 136 * nb) {κ : ℕ} {Lin : Main.Layout} {chain entries region base last : E}
    {chP eP rg L M n0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ} {cells : List E}
    (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ) (hM : M < 2 ^ 34)
    (hM0 : 0 < M)
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre0 ++ cellsBytes (cells.take (4 * m * q))))) ∧
      RecMem rd region (gen ^ L) entries base (m * M) o cells)
    (hR1 : ∀ q < M, ∀ c < 26, RegionL Lin (chP + 13 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o i))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o i + c))
    (hwit : (loopPre (coreProgram.getD j default)).filterMap Main.Stmt.popS =
      ((List.range m).map fun i => ("child_claim_index", [V.n (ccOV o0 i)])).map fun x => some (x.1, .stack x.2)) :
    CompleteAtDTBR fs cert κ f Lin [1, gen ^ M, chain, entries, region, base, last] (Returns [])
      (fun rd t => t.pops coreProgram rd = idxPops o 0 (m * M)) ((M + 1) * fs f) := by
  have hshape : loopShapeF (coreProgram.getD j default) f = true := by
    simp only [anycHead, Bool.and_eq_true] at hhd; exact hhd.1.1.1.1
  have hAS : (loopPre (coreProgram.getD j default)).all isAtomS = true := by
    simp only [anycHead, Bool.and_eq_true] at hhd; exact hhd.1.1.2
  have h := loopA_completeAtBP fs cert hf hshape hAS hun (Lin := Lin) (κ := κ) (N := gen ^ M)
    (rest := [chain, entries, region, base, last]) (m := M) rfl hM
    (anyLoop_blocksP hok hhd hedge hrecs hnb h64 hch hen hrg hpre0 hl hlast hL33 hLκ hmem hR1
      hR2 hR3 hwit)
  have := h 0 hM0
  rw [pow_zero, Nat.sub_zero, idxPops_flatMap] at this
  exact this

/-- **`child_claim_list_last__L{k}` is complete, placed, within its frame**: the state at
`sp = g^sP`, the records' marks at `region · g^(os j)` and their cells among the caller's words. -/
theorem ccl_completeAtBP (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ} (hk : k < 17) {κ : ℕ}
    {Lin : Main.Layout} {sp entries region marks last : E} {sP eP rg L n : ℕ}
    {pre : List UInt8} {os : ℕ → ℕ} {cells : List E}
    (hsp : sp = gen ^ sP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre : pre.length = rate * n) (hl : cells.length = 4 * k)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → StateAt rd sp 0 (absorbChunks n zeroState pre) ∧
      RecMem rd region (gen ^ L) entries marks k os cells)
    (hR1 : ∀ o < 13, RegionL Lin (sP + o)) (hR2 : ∀ j < k, RegionL Lin (rg + os j))
    (hR3 : ∀ j < k, ∀ c < 4, RegionL Lin (eP + 4 * os j + c)) :
    CompleteAtDTBR fs cert κ (cclNames.getD k "") Lin [sp, entries, region, marks, last]
      (Returns (digestCells (keccak256 (pre ++ cellsBytes cells))))
      (fun rd t => t.pops coreProgram rd = idxPops os 0 k) (fs (cclNames.getD k "")) := by
  intro fp
  refine ⟨fs (cclNames.getD k ""), [], _, [], le_rfl, ⟨rfl, rfl⟩, fun q hq => by simp at hq,
    B1.disj_nil, fun rd hlow hm => ?_⟩
  simp only [List.append_nil, List.nil_append] at hm
  obtain ⟨hS, hrec⟩ := hmem rd hm
  obtain ⟨vs, σ, hb, hp, hat, hr, hload, hg⟩ := ccl_core hk hsp hen hrg hpre hS hl hrec hlast hL33
    (boundMem_of_low hlow hLκ)
  refine relAtInP_atoms (ccl_name hk) hb (ccl_loop hk) (ccl_na hk) hp hat hr
    (fun q hq => by rw [ccl_addr hk] at hq; exact absurd hq List.not_mem_nil) (fun q hq => ?_)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq) ?_
  · rcases hload q hq with ⟨o, ho, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c, hc4, h⟩
    · exact ⟨_, h, Or.inl (hR1 o ho)⟩
    · exact ⟨_, h, Or.inl (hR2 j hj)⟩
    · exact ⟨_, h, Or.inl (hR3 j hj c hc4)⟩
  · rw [atomsPops_wit hg (ccl_wits k hk), idxPops, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, List.map_cons, List.map_nil, w_slot, Nat.zero_add]


end
end LeanVM.Guest.B1.Digest
