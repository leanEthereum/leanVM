/-
  LeanVM.Guest.B1.Whir.OsKidsF

  `open_stacked`'s query-position loops, residual's value and residual chains, complete.
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsB
public import LeanVM.Guest.B1.Whir.OsKids
public import LeanVM.Guest.B1.Whir.ResIter

/-!
# The loops and the finish's callees (TRIAGE #36)

* `os_kid_sq`: a level's query-position loop, entered at `p`, on the caller's words and its
  decoders' pointers `W p`, returning its decoders' frame runs (`sqLoop_relAtIn`).
* `os_kid_ff`: `fold_final_msg` on the final message and the tail's challenges.
* `os_kid_res`: a level's residual chain loop, pure, on the words its iterations read.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

private theorem os_regionL_left {L L' : Main.Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_left _ hq, h1, h2⟩

/-- **A level's query-position loop**, entered at `p`. -/
theorem os_kid_sq {lv : OsLvl} (hpl : SqPlace lv) {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hb : fn.body = sqLoopOf lv)
    (hlp : coreProgram.loop lv.sqLoop = true) (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth)
    (hdec : OsDecodeAtD fs cert κ lv.depth lv.decode) {n : ℕ} (hn : 0 < n) (hn' : n + 1 < ordG)
    {sqz qpos qbp : E} {cv : Digest} {Lk : Main.Layout} {W : ℕ → Main.Layout}
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lk → ∀ j < n,
      LoadHolds rd sqz (2 * j) (digestScalars (sqAll j cv).2).1 ∧
        LoadHolds rd sqz (2 * j + 1) (digestScalars (sqAll j cv).2).2 ∧
        LoadHolds rd sqz (2 * j + 2) (digestScalars (sqCv (sqAll j cv).2)).1 ∧
        LoadHolds rd sqz (2 * j + 3) (digestScalars (sqCv (sqAll j cv).2)).2)
    (hdmem : ∀ p rd, LowDef κ rd → MemL rd (Lk ++ W p) → ∀ j < n, ∀ i < 192 / lv.depth,
      LoadHolds rd (qpos * gen ^ (lv.posOff + j * (192 / lv.depth))) i
          (eOfNat ((eToNat (sqW cv j) >>> (i * lv.depth)) % 2 ^ lv.depth)) ∧
        LoadHolds rd (qbp * gen ^ (lv.posOff + j * (192 / lv.depth))) i
          (ofK (Parameters.gpow (sqDecAt fs lv n p j + cert lv.decode (.n 3))) * gen ^ (i * lv.depth)))
    (hreg : ∀ j < n, ∀ t < 4, OqIn (RegionL Lk) (sqz.limb 0 * Parameters.gpow (2 * j + t))) :
    OsCompleteAtP fs cert κ lv.sqLoop (fun p => Lk ++ W p) [1, gen ^ n, sqz, qpos, qbp] []
      (fun p => sqRuns fs cert lv n p (sqW cv) 0) := by
  intro p
  obtain ⟨Lown, hW, hD, hrel⟩ := sqLoop_relAtIn fs cert κ hpl hfind hp hb hlp hpo hdig hdec hn hn' (sqz := sqz)
    (qpos := qpos) (qbp := qbp) (cv := cv) (Lin := Lk ++ W p) p
    (fun rd hl hm => hmem rd hl (Main.memL_append.mp hm).1) (hdmem p)
    (fun j hj t ht => oq_in_mono (fun _ h => os_regionL_left h) (hreg j hj t ht))
  exact ⟨sqTot fs lv n 0, Lown, hW, hD, hrel⟩

/-- **`fold_final_msg`** on the message at `msg` and the point at `point`. -/
theorem os_kid_ff {name : String} {n : ℕ} (hff : OsFoldFinalAtD fs cert κ name n) {Lk : Main.Layout} {msg point : E}
    {m ps : List E} (hm : m.length = 2 ^ n) (hps : ps.length = n)
    (hM : ∀ rd, MemL rd Lk → ReadsAt rd msg m ∧ ReadsAt rd point ps) :
    osKC fs cert κ Lk name [msg, point] [multilinearEval m ps] :=
  hff _ _ Lk fun rd hmm => ⟨m, ps, hm, hps, (hM rd hmm).1, (hM rd hmm).2, rfl⟩

/-- **A residual chain loop**, on the words its iterations read. -/
theorem os_kid_res {posOff row cols qo : ℕ} {vals : List ℕ} {loop : String} {fn : Fn}
    (hS : coreProgram.PureIn [loop]) (hfind : coreProgram.find? loop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) (hb : fn.body = resLoopBody posOff row cols qo vals loop)
    (hc : 1 ≤ cols) {n : ℕ} (hn : n < ordG) (hn0 : 0 < n) {qpos ba bb rc qw : E} {ch0 r wq A B : ℕ → E}
    {Lk : Main.Layout}
    (hM : ∀ rd, MemL rd Lk → (∀ i < n, LoadHolds rd (qpos * gen ^ i) posOff (ch0 i)) ∧
      (∀ t < cols, LoadHolds rd ba (row + t) (A t)) ∧ (∀ t < cols, LoadHolds rd bb (row + t) (B t)) ∧
      (∀ i < n, LoadHolds rd (rc * gen ^ i) 0 (r i)) ∧ (∀ i < n, LoadHolds rd (qw * gen ^ i) qo (wq i)) ∧
      (∀ i < n, LoadHolds rd (rc * gen ^ i) 1 (r i + wq i * resProd A B vals (ch0 i) cols))) :
    osKC fs cert κ Lk loop [1, gen ^ n, qpos, ba, bb, rc, qw] [] :=
  completeAt_of_rel_pureD hS (by simp) (fun rd hm => by
    obtain ⟨lp, la, lb, lr, lw, lr1⟩ := hM rd hm
    have := resLoop_rel hfind hp hb hc hn lp la lb lr lw lr1 0 hn0
    simpa using this) κ

end
end LeanVM.Guest.B1
