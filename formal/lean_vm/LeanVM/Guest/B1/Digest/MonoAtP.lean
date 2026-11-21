/-
  LeanVM.Guest.B1.Digest.MonoAtP

  The gap walk's frame loops and last claims placed with their pops: each claim's hinted gap, in order.
-/

module

public import LeanVM.Guest.B1.Digest.MonoAt
public import LeanVM.Guest.B1.Digest.LoopAtP
public import LeanVM.Guest.B1.Digest.ValidPops

/-!
# The gap walk's helpers, with their pops

* `atomsPops_wit`: on a valuation good for an oracle `w`, atoms whose witness hints are `L`'s stack hints pop their
  oracle's words; `relAtInP_atoms`: `relAtIn_atoms` by a tree popping its atoms' entries;
* `gapPops o s m`: claims `s ..< s + m`'s gaps (`mGap o`); `gapPops_append`, `gapPops_flatMap`;
* `monoLoop_blocksP`, `monoLoop_completeAtBP`, `mlc_completeAtBP`: `monoLoop_blocks`, `monoLoop_completeAtB`,
  `mlc_completeAtB` by trees popping their claims' gaps (`mono_core`'s, `mlc_core`'s oracle).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Memory (atomUnplaced)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB CompleteAtDTBR Returns LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (RunIn)

@[expose] public section

variable {rd : Reader}

/-- **Atoms good for an oracle**: atoms whose witness hints are `L`'s stack hints pop their oracle's words. -/
theorem atomsPops_wit {as : List Atom} {S : List Atom} {w : ℕ → E} {σ : Val} (hg : ∀ a ∈ as, Good rd S w σ a)
    {L : List (String × List V)} (hL : as.flatMap atomWit = L.map fun x => (x.1, .stack x.2)) :
    as.flatMap (Atom.pops rd σ) = L.map fun x => (x.1, x.2.map fun v => w v.idx) := by
  rw [flatMap_atom_pops, hL, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  have h1 : (x.1, Dest.stack x.2) ∈ as.flatMap atomWit := by rw [hL]; exact List.mem_map_of_mem hx
  obtain ⟨a, ha, hax⟩ := List.mem_flatMap.mp h1
  cases a with
  | hint hh =>
    cases hh with
    | witness s d =>
      simp only [atomWit, List.mem_singleton, Prod.mk.injEq] at hax
      obtain ⟨rfl, rfl⟩ := hax
      have hgx := hg _ ha
      simp only [Function.comp_apply, Dest.words, Prod.mk.injEq, true_and]
      exact List.map_congr_left hgx
    | _ => simp [atomWit] at hax
  | _ => simp [atomWit] at hax

/-- **`relAtIn_atoms` by a tree popping its atoms' entries.** -/
theorem relAtInP_atoms {fs : String → ℕ} {cert : String → V → ℕ} {f : String} {fn : Fn} {as : List Atom}
    {vs : List V} (hf : coreProgram.find? f = some fn) (hb : fn.body = as.map Stmt.atom ++ [.ret vs])
    (hl : coreProgram.loop f = false) (hna : as.all (fun a => !atomAllocB a) = true)
    {σ : Val} {args rets : List E} {fp : ℕ} {R D : ℕ → Prop}
    (hp : fn.params.map σ = args) (hh : ∀ a ∈ as, a.Holds rd σ) (hr : vs.map σ = rets)
    (haddr : ∀ q ∈ as.filterMap atomAddr?, σ q.1 = ofK (addressOfIndex (fp + cert f q.2)))
    (hload : ∀ q ∈ as.filterMap atomLoad?, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
        addressOfIndex i ∧ (R i ∨ RunIn cert fp f as i))
    (hD : ∀ i, D i → RunIn cert fp f as i) {ps : List Pop} (hps : as.flatMap (Atom.pops rd σ) = ps) :
    RelAtInP coreProgram fs cert rd R D fp (fs f) f args rets ps := by
  have hw := walk_atoms σ as vs
  rw [← hb] at hw
  have hown : ∀ i, RunIn cert fp f as i →
      ownData cert fp (fp + fs f) f (allocs σ (as.map Ev.atom)) (as.map Ev.atom) i := by
    rintro i ⟨q, hq, h1, h2⟩
    exact Or.inr ⟨q, by rw [runs_atoms]; exact hq, h1, h2⟩
  have h := relAtInP_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := R) (D := D)
    (Dk := fun _ => False) (N := 0) (fp := fp) (σ := σ) (rd := rd) (pss := []) (ps := ps) coreProgram_wf hf
    (Or.inl hl) hp hw hr (holds_atoms hh) (by rw [allocDsts_atoms hna, allocs_atoms σ hna]; rfl)
    (by rw [addrs_atoms]; exact haddr) (by rw [calls_atoms]; exact ⟨rfl, fun _ h => h⟩)
    (fun A hA => ?_) (fun i hi => Or.inl (hown i (hD i hi)))
    (by rw [splice_nil_of_calls _ (vp_calls_atoms as), vp_evPops_atoms, hps])
  · rw [allocs_atoms σ hna] at h
    simpa using h
  · rw [loadAddrs_atoms] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h⟩ := hload q hq
    exact ⟨i, hi, h.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl (hown i h)⟩

/-- **Claims `s ..< s + m`'s gaps.** -/
noncomputable def gapPops (o : ℕ → ℕ) (s m : ℕ) : List Pop :=
  (List.range m).map fun i => ("child_claim_gap", [gen ^ mGap o (s + i)])

theorem gapPops_append (o : ℕ → ℕ) (s A B : ℕ) : gapPops o s A ++ gapPops o (s + A) B = gapPops o s (A + B) := by
  simp only [gapPops, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Nat.add_assoc]

theorem gapPops_flatMap (o : ℕ → ℕ) (s0 m : ℕ) : ∀ M : ℕ,
    (List.range' 0 M).flatMap (fun q => gapPops o (s0 + m * q) m) = gapPops o s0 (m * M)
  | 0 => by simp [gapPops]
  | M + 1 => by
    rw [← List.range'_append_1 (s := 0) (m := M) (n := 1), List.flatMap_append, gapPops_flatMap o s0 m M]
    simp only [Nat.zero_add, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [gapPops_append, Nat.mul_succ]

set_option maxRecDepth 100000 in
theorem mono136_wits : (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop0» default)).filterMap
    Main.Stmt.popS = ((List.range 136).map fun i => ("child_claim_gap", [V.n (13 + 10 * i)])).map
      fun x => some (x.1, .stack x.2) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mono17_wits : (loopPre (coreProgram.getD idx% «child_claim_list_mono_loop1» default)).filterMap
    Main.Stmt.popS = ((List.range 17).map fun i => ("child_claim_gap", [V.n (13 + 10 * i)])).map
      fun x => some (x.1, .stack x.2) := by
  decide +kernel

/-- `child_claim_list_mono_last__L{k}`'s witness hints: its claims' gaps. -/
noncomputable def mlWitOk (k : ℕ) : Bool :=
  decide ((mlAtoms k).flatMap atomWit = ((List.range k).map fun i => ("child_claim_gap", [V.n (6 + 10 * i)])).map
    fun x => (x.1, .stack x.2))

set_option maxRecDepth 100000 in
theorem ml_wits_all : ∀ k < 17, mlWitOk k = true := by decide +kernel

theorem ml_wits (k : ℕ) (hk : k < 17) : (mlAtoms k).flatMap atomWit =
    ((List.range k).map fun i => ("child_claim_gap", [V.n (6 + 10 * i)])).map fun x => (x.1, .stack x.2) :=
  of_decide_eq_true (ml_wits_all k hk)

set_option maxRecDepth 20000 in
/-- **A frame loop of the gap walk, its frames, with their pops**: `monoLoop_blocks`, frame `q` popping its claims'
gaps. -/
theorem monoLoop_blocksP {j : ℕ} {f : String} {m p0 st0 cw ew nb : ℕ}
    (hok : monoOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hc : mcOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hew : word ew 0 = gen ^ (4 * m))
    (hnb : (monoSpec m st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (h64 : 64 * m = 136 * nb) (hm0 : 0 < m) {κ : ℕ} {Lin : Main.Layout}
    {chain entries region mark : E} {chP eP rg L M n0 s0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ}
    {cells : List E} (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length) (hLκ : L ≤ 2 ^ κ)
    (hinc : ∀ i < m * M, mStart o (s0 + i) ≤ o (s0 + i))
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, MonoRecAt rd (chain * gen ^ (15 * q)) (n0 + nb * q)
        (pre0 ++ cellsBytes (cells.take (4 * m * q))) region entries (mStart o (s0 + m * q))) ∧
      MRec rd region L entries mark (m * M) (fun i => o (s0 + i)) cells)
    (hR1 : ∀ q < M, ∀ c < 30, RegionL Lin (chP + 15 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o (s0 + i)))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o (s0 + i) + c))
    (hwit : (loopPre (coreProgram.getD j default)).filterMap Main.Stmt.popS =
      ((List.range m).map fun i => ("child_claim_gap", [V.n (13 + 10 * i)])).map fun x => some (x.1, .stack x.2)) :
    ∀ q < M, LoopBlockInP κ (coreProgram.getD j default) Lin q (gen ^ M) [chain, mark]
      (gapPops o (s0 + m * q) m) := by
  intro q hq rd hlow hLin
  obtain ⟨hR, hrec⟩ := hmem rd hLin
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
  have e15 : chain * gen ^ (15 * (q + 1)) = chain * (gen ^ q) ^ 15 * gen ^ 15 := by
    rw [gen_pow_pow, mul_assoc, ← pow_add]; ring_nf
  rw [e15, loadHolds_mul_gen_pow] at h28 h29
  rw [show s0 + m * (q + 1) = s0 + m * q + m by ring] at h28 h29
  obtain ⟨σ, hp, hat, hload, hg⟩ := mono_core hok hc hcw hew hnb hm0 (x := gen ^ q) (N := gen ^ M)
    (mark := mark) (s := s0 + m * q) (o := o) (L := L) rfl hch hen hrg hpre
    (by rw [gen_pow_pow]; exact hS0) (by rw [gen_pow_pow]; exact h13)
    (by rw [gen_pow_pow]; exact h14)
    (cells := (cells.drop (4 * m * q)).take (4 * m))
    (by simp only [List.length_take, List.length_drop]; omega)
    (fun i hi => by rw [Nat.add_assoc]; exact hinc (m * q + i) (by omega))
    (by intro i hi; have := hr i hi; simp only [Nat.add_assoc] at this ⊢; exact this)
    (boundMem_of_low hlow hLκ)
    (fun c => by
      have := hS1 c
      rw [e15, loadHolds_mul_gen_pow, show 15 + (0 + c.val) = 15 + c.val by ring] at this
      exact this) h28 h29
  refine ⟨σ, hp, hat, fun q' hq' => ?_, ?_⟩
  · rcases hload q' hq' with ⟨c, hc30, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, c, hc4, h⟩
    · exact ⟨_, h, hR1 q hq c hc30⟩
    · rw [Nat.add_assoc s0] at h
      exact ⟨_, h, hR2 (m * q + i) (by omega)⟩
    · rw [Nat.add_assoc s0] at h
      exact ⟨_, h, hR3 (m * q + i) (by omega) c hc4⟩
  · rw [blockPops_wit hg hwit, gapPops, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, List.map_cons, List.map_nil]
    rw [show (13 + 10 * i - 13) / 10 = i by omega]

/-- **A frame loop of the gap walk is complete, placed, within its frames, popping its claims' gaps.** -/
theorem monoLoop_completeAtBP (fs : String → ℕ) (cert : String → V → ℕ) {j : ℕ} {f : String}
    {m p0 st0 cw ew nb : ℕ} (hf : coreProgram.find? f = some (coreProgram.getD j default))
    (hok : monoOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hc : mcOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hew : word ew 0 = gen ^ (4 * m))
    (hnb : (monoSpec m st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (hun : (atomsIn (loopPre (coreProgram.getD j default))).all atomUnplaced = true)
    (h64 : 64 * m = 136 * nb) (hm0 : 0 < m) {κ : ℕ} {Lin : Main.Layout}
    {chain entries region mark : E} {chP eP rg L M n0 s0 : ℕ} {pre0 : List UInt8} {o : ℕ → ℕ}
    {cells : List E} (hch : chain = gen ^ chP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length) (hLκ : L ≤ 2 ^ κ)
    (hM : M < 2 ^ 34) (hM0 : 0 < M)
    (hinc : ∀ i < m * M, mStart o (s0 + i) ≤ o (s0 + i))
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ M, MonoRecAt rd (chain * gen ^ (15 * q)) (n0 + nb * q)
        (pre0 ++ cellsBytes (cells.take (4 * m * q))) region entries (mStart o (s0 + m * q))) ∧
      MRec rd region L entries mark (m * M) (fun i => o (s0 + i)) cells)
    (hR1 : ∀ q < M, ∀ c < 30, RegionL Lin (chP + 15 * q + c))
    (hR2 : ∀ i < m * M, RegionL Lin (rg + o (s0 + i)))
    (hR3 : ∀ i < m * M, ∀ c < 4, RegionL Lin (eP + 4 * o (s0 + i) + c))
    (hwit : (loopPre (coreProgram.getD j default)).filterMap Main.Stmt.popS =
      ((List.range m).map fun i => ("child_claim_gap", [V.n (13 + 10 * i)])).map fun x => some (x.1, .stack x.2)) :
    CompleteAtDTBR fs cert κ f Lin [1, gen ^ M, chain, mark] (Returns [])
      (fun rd t => t.pops coreProgram rd = gapPops o s0 (m * M)) ((M + 1) * fs f) := by
  have hshape : loopShapeF (coreProgram.getD j default) f = true := by
    simp only [mcOk, mcHead, Bool.and_eq_true] at hc; exact hc.1.1.1.1.1.1
  have hAS : (loopPre (coreProgram.getD j default)).all isAtomS = true := by
    simp only [mcOk, mcHead, Bool.and_eq_true] at hc; exact hc.1.1.1.1.2
  have h := loopA_completeAtBP fs cert hf hshape hAS hun (Lin := Lin) (κ := κ) (N := gen ^ M)
    (rest := [chain, mark]) (m := M) rfl hM
    (monoLoop_blocksP hok hc hcw hew hnb h64 hm0 hch hen hrg hpre0 hl hLκ hinc hmem hR1 hR2 hR3 hwit)
  have := h 0 hM0
  rw [pow_zero, Nat.sub_zero, gapPops_flatMap] at this
  exact this


/-- **`child_claim_list_mono_last__L{k}` is complete, placed, within its frame, popping its claims' gaps.** -/
theorem mlc_completeAtBP (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ} (hk : k < 17) {κ : ℕ}
    {Lin : Main.Layout} {rec region mark limit entries : E} {rP eP rg L s n : ℕ} {o : ℕ → ℕ}
    {pre : List UInt8} {cells : List E} (hrc : rec = gen ^ rP) (hen : entries = gen ^ eP)
    (hrg : region = gen ^ rg) (hlim : limit = gen ^ L) (hpre : pre.length = rate * n)
    (hl : cells.length = 4 * k) (hinc : ∀ i < k, mStart o (s + i) ≤ o (s + i))
    (hend : mStart o (s + k) ≤ L) (hLκ : L < 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → MonoRecAt rd rec n pre region entries (mStart o s) ∧
      MRec rd region L entries mark k (fun i => o (s + i)) cells)
    (hR1 : ∀ c < 15, RegionL Lin (rP + c)) (hR2 : ∀ j < k, RegionL Lin (rg + o (s + j)))
    (hR3 : ∀ j < k, ∀ c < 4, RegionL Lin (eP + 4 * o (s + j) + c)) :
    CompleteAtDTBR fs cert κ (mlNames.getD k "") Lin [rec, region, mark, limit]
      (Returns (digestCells (keccak256 (pre ++ cellsBytes cells))))
      (fun rd t => t.pops coreProgram rd = gapPops o s k) (fs (mlNames.getD k "")) := by
  intro fp
  refine ⟨fs (mlNames.getD k ""), [], _, [], le_rfl, ⟨rfl, rfl⟩, fun q hq => by simp at hq,
    B1.disj_nil, fun rd hlow hm => ?_⟩
  simp only [List.append_nil, List.nil_append] at hm
  obtain ⟨hR, hrec⟩ := hmem rd hm
  obtain ⟨vs, σ, hb, hp, hat, hr, hload, hg⟩ := mlc_core hk hrc hen hrg hlim hpre hR hl hinc hrec hend
    (boundMem_of_low hlow (by omega))
  refine relAtInP_atoms (ml_name hk) hb (ml_loop hk) (ml_na hk) hp hat hr
    (fun q hq => by rw [ml_addr hk] at hq; exact absurd hq List.not_mem_nil) (fun q hq => ?_)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq) ?_
  · rcases hload q hq with ⟨c, hc, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c, hc4, h⟩
    · exact ⟨_, h, Or.inl (hR1 c hc)⟩
    · exact ⟨_, h, Or.inl (hR2 j hj)⟩
    · exact ⟨_, h, Or.inl (hR3 j hj c hc4)⟩
  · rw [atomsPops_wit hg (ml_wits k hk), gapPops, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, List.map_cons, List.map_nil]
    rw [show (6 + 10 * i - 6) / 10 = i by omega]


end
end LeanVM.Guest.B1.Digest
