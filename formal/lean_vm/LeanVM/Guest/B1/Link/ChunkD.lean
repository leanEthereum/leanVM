/-
  LeanVM.Guest.B1.Link.ChunkD

  B1 for `chunk_d__L{w}`: `g^d`, `d` the chunk count of a `w`-bit pointer.
-/

module

public import LeanVM.Guest.B1.Link.Forms
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.CoreRef

/-!
# `chunk_d`

`chunk_d(w)` (G) returns `g^d` with `d = CHUNK_D[w]`, the chunk count of `Chunks.new w`
(`link::Chunks`). `chunk_d_sound`: at every deployed width `19 ≤ w ≤ 24`, its one return is
`g^d` for `Chunks.new w = some c`, `d = c.d`, the table checked against the Statement's chunking.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`chunk_d__L{w}`**: it returns `g^d`, `d` the chunk count of `Chunks.new w`. -/
def MeaningChunkD (w : ℕ) : List E → List E → Prop
  | [], rets => ∃ c : Chunks, Chunks.new w = some c ∧ rets = [gen ^ c.d]
  | _, _ => False

theorem chunkD_of {rd : Reader} {name : String} {f : Fn} {w k : ℕ} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = []) (hbody : f.body = [.atom (.const (.n 0) (word (2 ^ k) 0)), .ret [.n 0]])
    (hc : ((Chunks.new w).map Chunks.d) = some k) (hk : k < 64) (args rets : List E) :
    coreProgram.Rel rd name args rets → MeaningChunkD w args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  rintro ⟨σ, rfl, h0, hret⟩
  obtain ⟨c, hc1, rfl⟩ := Option.map_eq_some_iff.mp hc
  refine ⟨c, hc1, ?_⟩
  rw [← hret]
  simp only [Atom.Holds] at h0
  simp [h0, word_two_pow hk]

/-- **`chunk_d__L{w}`'s core IR implies its meaning**, at every deployed width. -/
theorem chunk_d_sound (rd : Reader) (args rets : List E) :
    (coreProgram.Rel rd "chunk_d__L19" args rets → MeaningChunkD 19 args rets) ∧
    (coreProgram.Rel rd "chunk_d__L20" args rets → MeaningChunkD 20 args rets) ∧
    (coreProgram.Rel rd "chunk_d__L21" args rets → MeaningChunkD 21 args rets) ∧
    (coreProgram.Rel rd "chunk_d__L22" args rets → MeaningChunkD 22 args rets) ∧
    (coreProgram.Rel rd "chunk_d__L23" args rets → MeaningChunkD 23 args rets) ∧
    (coreProgram.Rel rd "chunk_d__L24" args rets → MeaningChunkD 24 args rets) :=
  ⟨chunkD_of (k := 6) (coreProgram_find?_at (j := idx% «chunk_d__L19») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num) args rets,
    chunkD_of (k := 6) (coreProgram_find?_at (j := idx% «chunk_d__L20») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num) args rets,
    chunkD_of (k := 7) (coreProgram_find?_at (j := idx% «chunk_d__L21») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num) args rets,
    chunkD_of (k := 7) (coreProgram_find?_at (j := idx% «chunk_d__L22») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num) args rets,
    chunkD_of (k := 8) (coreProgram_find?_at (j := idx% «chunk_d__L23») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num) args rets,
    chunkD_of (k := 9) (coreProgram_find?_at (j := idx% «chunk_d__L24») rfl) rfl
      (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) (by norm_num) args rets⟩

end
end LeanVM.Guest.B1.Link
