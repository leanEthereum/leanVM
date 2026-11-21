/-
  LeanVM.Guest.B1.Da.BlobAt

  `da_verify_blob` on its honest region, placed (G:4581-4596).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.CellLAt
public import LeanVM.Guest.B1.Da.PadAt
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_blob»

/-!
# A blob, placed

On a layout holding the weights at `g^bw` (`wtsCells q`, column `h`'s expansion at `g^(q h)`): blob `i`'s region at
`bb = fp + fs da_verify_blob` (`regionCells syms z i`), its cell loop (`cellL_completeAtTB`) and its tree
(`da_levels__L128_L7`). `blobNH`: its honest shape; `blob_completeAtB`: complete within its frame, its region and its
callees' static bounds, returning the blob's root.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Kid KidD kidsAt outsL KidsDepBP OutsOk RegionsOk CallsMatch
  Returns completeAt_flatDepRet flatCalls namedP)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)

@[expose] public section

/-- `da_verify_blob`'s body before its `ret`. -/
def blobPre : List Stmt := blobBody.dropLast

theorem blob_body : (fn% «da_verify_blob»).body = blobPre ++ [.ret [.n (val% «da_verify_blob» "s5#0"), .n (val% «da_verify_blob» "s5#0[1]")]] := by
  have hok := blob_ok
  unfold blobOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rw [stmtsEqb_sound hok.2]
  rfl

theorem blob_params : (fn% «da_verify_blob»).params = [.n (val% «da_verify_blob» "weights")] := by
  have hok := blob_ok
  unfold blobOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1

theorem blob_allocs : blobPre.filterMap Main.Stmt.allocSz = [(.n (val% «da_verify_blob» "base"), .inl 641)] := rfl

theorem blob_loads : blobPre.filterMap B1.Stmt.loadS = [(.n (val% «da_verify_blob» "base"), 512), (.n (val% «da_verify_blob» "base"), 640)] := rfl

theorem blob_flatCalls (σ : Val) : flatCalls blobPre σ =
    [Main.mkCall σ (none, name% «da_verify_blob_loop0», [.n (val% «da_verify_blob» "s2#0"), .n (val% «da_verify_blob» "weights"), .n (val% «da_verify_blob» "base")], []),
      Main.mkCall σ (none, "da_levels__L128_L7", [.n (val% «da_verify_blob» "base")], [.n (val% «da_verify_blob» "b0"), .n (val% «da_verify_blob» "b1")])] := rfl

/-- `da_verify_blob`'s callees, its region at `bb`. -/
noncomputable def blobKids (r : ℕ) (syms : ℕ → ℕ → List E) (z : E) (i bw : ℕ) (Lin : Layout) (bb : ℕ) :
    List KidD :=
  [fun _ => ⟨name% «da_verify_blob_loop0», true, [1, gen ^ bw, gen ^ bb],
      (bb, regionCells syms z i) :: Lin, Returns []⟩,
    fun _ => ⟨"da_levels__L128_L7", true, [gen ^ bb], [(bb, regionCells syms z i)],
      Returns (digestCells (blobLeaf r syms i))⟩]

/-- The predicates on `da_verify_blob`'s callees' trees: its cells holding `syms i k`. -/
def blobTs (syms : ℕ → ℕ → List E) (i : ℕ) : List (Tree → Prop) :=
  [cellLFrom (fun k => cellNH (syms i k)) 128 0, fun _ => True]

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`da_verify_blob`'s honest shape** on blob `i`'s cells. -/
def blobNH (SB SK : String → ℕ) (syms : ℕ → ℕ → List E) (i : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_verify_blob" (fun _ => True) (flatCalls blobPre) (fun _ => [641])
    (namedP fs [name% «da_verify_blob_loop0», "da_levels__L128_L7"]
      [cellB fs SK, SB "da_levels__L128_L7"] (blobTs syms i))

/-- **`da_verify_blob` is complete, placed, by a tree of its honest shape, within its frame, its region and its
callees' static bounds**: blob `i < r` of cells `syms i` orthogonal to the dual codeword of `z`, the weights at
`g^bw`; it returns the blob's root. -/
theorem blob_completeAtB {SB : String → ℕ}
    {SK : String → ℕ} (hcl : TotalLeOn coreProgram fs name% «da_verify_blob_loop0» (fun a => a.getD 0 0 = 1)
      (fun _ => cellB fs SK))
    (hdl : TotalLe coreProgram fs "da_levels__L128_L7" (fun _ => SB "da_levels__L128_L7"))
    {r i : ℕ} (hi : i < r) {syms : ℕ → ℕ → List E} (hsl : ∀ k, (syms i k).length = 128) {z : E}
    (hdot : ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 128,
      dualAt z (128 * h + e) * (syms i h).getD e 0 = 0) {bw : ℕ} {q : ℕ → ℕ} {Lin : Layout}
    (hWm : (bw, wtsCells q) ∈ Lin) (hCm : ∀ k < 128, (q k, colRun z k) ∈ Lin) :
    CompleteAtDTB fs cert 16 "da_verify_blob" Lin [gen ^ bw]
      (Returns (digestCells (blobLeaf r syms i))) (blobNH fs SB SK syms i)
      (fs "da_verify_blob" + 641 + (cellB fs SK + SB "da_levels__L128_L7")) := by
  have hlen := length_blobLeaves syms i
  have hroot : cellRoot 7 (blobLeaves syms i) = digestHalves (blobLeaf r syms i) := by
    rw [blobLeaf, ite_pos' hi, blobLeaves, ← cellRoot_mRoot]
    rfl
  refine ((completeAt_flatDepRet (fs := fs) (cert := cert) find_da_verify_blob
    (by rw [Program.loop_of_find? find_da_verify_blob]; decide +kernel) 16 Lin [gen ^ bw]
    (fun _ _ => digestCells (blobLeaf r syms i)) _ blob_body (by decide) (by decide) (by decide) [641]
    (fun _ => [regionCells syms z i]) (fun _ => .cons (by rw [length_regionCells]) .nil)
    (fun fp => blobKids r syms z i bw Lin (fp + fs "da_verify_blob"))
    [name% «da_verify_blob_loop0», "da_levels__L128_L7"]
    [cellB fs SK, SB "da_levels__L128_L7"] (blobTs syms i) (fun _ => True)
    (fun _ => .cons (fun _ => rfl) (.cons (fun _ => rfl) .nil))
    (fun fp => ⟨fun _ => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun _ => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩, trivial⟩)
    (fun _ _ _ _ => rfl) (fun fp outs ho => ?_) (fun fp outs ho rd _ hB hLin _ => ?_)
    (fun fp outs hlen ho rd _ hB _ _ => ?_)).mono ?_ (fun _ h => h))
  · -- the cell loop
    exact cellL_completeAtTB hcl hsl List.mem_cons_self (List.mem_cons_of_mem _ hWm)
      (fun k hk => List.mem_cons_of_mem _ (hCm k hk))
  · -- the blob's tree
    refine pureB_static daPure (List.mem_append_left _ (List.mem_append_right _ (by decide)))
      (fun rd hm => ?_) hdl
    have hregR := reads_of_memL hm List.mem_cons_self
    rw [regionCells, List.append_assoc, readsAt_append] at hregR
    have hc := da_levels_complete 7 (Or.inr rfl) rd _ (blobLeaves syms i) (by rw [hlen]; norm_num)
      (treeMem_of_reads (by rw [hlen]; norm_num) hregR.1)
    rw [hroot] at hc
    exact hc
  · -- the callees' regions
    have hown : ∀ j, RegionL [(fp + fs "da_verify_blob", regionCells syms z i)] j →
        RegionL (bufL (fp + fs "da_verify_blob") [641] [regionCells syms z i]) j := fun j hj => by
      simpa [bufL, bases] using hj
    match outs with
    | [] => trivial
    | o :: os =>
    refine ⟨fun _ j hj => ?_, ?_⟩
    · obtain ⟨p, hp, h1, h2⟩ := hj
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl (Or.inr (hown j ⟨_, List.mem_cons_self, h1, h2⟩))
      · exact Or.inl (Or.inl ⟨p, hp, h1, h2⟩)
    match os with
    | [] => trivial
    | o2 :: os => exact ⟨fun _ j hj => Or.inl (Or.inr (hown j hj)), by cases os <;> trivial⟩
  · -- what the callees read
    have hB' : MemL rd [(fp + fs "da_verify_blob", regionCells syms z i)] := by simpa [bufL, bases] using hB
    intro p hp
    match outs with
    | [] => simp [kidsAt, Kid.lins] at hp
    | [o] =>
      simp only [kidsAt, blobKids, Kid.lins, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hB' _ List.mem_cons_self
      · exact hLin _ hp
    | o :: o2 :: os =>
      simp only [kidsAt, blobKids, Kid.lins, List.flatMap_cons, List.mem_append, List.mem_cons] at hp
      rcases hp with (rfl | hp) | (rfl | hp) | hp
      · exact hB' _ List.mem_cons_self
      · exact hLin _ hp
      · exact hB' _ List.mem_cons_self
      · simp at hp
      · cases os <;> simp at hp
  · -- the valuation
    set bb := fp + fs "da_verify_blob"
    have hB' : ReadsAt rd (gen ^ bb) (regionCells syms z i) :=
      reads_of_memL (L := [(bb, regionCells syms z i)]) (by simpa [bufL, bases] using hB) List.mem_cons_self
    match outs, hlen with
    | [o1, o2], _ =>
    have h2 : o2.1 = digestCells (blobLeaf r syms i) := (show OutsOk [_, _] [o1, o2] from ho).2.1 rfl |>.1
    have h1 : o1.1 = [] := (show OutsOk [_, _] [o1, o2] from ho).1 rfl |>.1
    have l512 : LoadHolds rd (gen ^ bb) 512 (word 0 0) := loadHolds_of_reads hB'
      (by rw [length_regionCells]; norm_num) (by
        rw [word_zero, show (512 : ℕ) = 512 + 0 from rfl, regionCells_sum (by norm_num), runSum_zero])
    have l640 : LoadHolds rd (gen ^ bb) 640 (word 0 0) := loadHolds_of_reads hB'
      (by rw [length_regionCells]; norm_num) (by
        rw [word_zero, show (640 : ℕ) = 512 + 128 from rfl, regionCells_sum le_rfl, runSum_full hdot])
    refine ⟨Val.ofArgs [gen ^ bw, gen ^ bb, word 0 0, word 1 0, word 0 0, word 0 0,
      (digestHalves (blobLeaf r syms i)).1, (digestHalves (blobLeaf r syms i)).2,
      (digestHalves (blobLeaf r syms i)).1, (digestHalves (blobLeaf r syms i)).2],
      by rw [blob_params]; rfl, fun s hs => ?_, ?_, rfl, ?_, ?_, fun p hp => ?_, trivial⟩
    · simp only [blobPre, blobBody, List.dropLast, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro
    · rw [blob_body]
      refine holdsList_straight _ _ _ _ (fun s hs => ?_) (by simp [digestCells, ofArgs_n])
      simp only [blobPre, blobBody, List.dropLast, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [SHolds, Atom.Holds, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]
      exacts [l512, l640, by rw [word_zero, add_zero]]
    · rw [blob_allocs]
      simp [ofArgs_n, bases, gen_pow_eq_ofK]
    · rw [blob_flatCalls]
      simp only [List.map_cons, List.map_nil, Main.mkCall, kidsAt, blobKids, CallsMatch, ofArgs_n,
        List.getD_cons_succ, List.getD_cons_zero, h1, h2, digestCells, word_one]
      exact ⟨trivial, trivial, fun _ => ⟨trivial, trivial⟩, trivial, trivial, fun _ => ⟨trivial, trivial⟩,
        trivial⟩
    · rw [blob_loads] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      have hr : ∀ j, j < 641 → RegionL (bufL bb [641] [regionCells syms z i]) (bb + j) := fun j hj =>
        regionL_of_mem (xs := regionCells syms z i) (by simp [bufL, bases]) (by rw [length_regionCells]; exact hj)
      rcases hp with rfl | rfl
      · exact ⟨bb + 512, by simp only [ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]; rw [limb0_gen_pow_mul],
          Or.inr (Or.inl (hr _ (by norm_num)))⟩
      · exact ⟨bb + 640, by simp only [ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]; rw [limb0_gen_pow_mul],
          Or.inr (Or.inl (hr _ (by norm_num)))⟩
  · simp only [List.sum_cons, List.sum_nil]
    omega

end
end LeanVM.Guest.B1.Da
