/-
  LeanVM.Guest.B1.VsC.VsNatLt

  The link terminal's identity from the native terminal check, and `verify_keccak`'s start sponge carried.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatKr
public import LeanVM.Guest.B1.Link.Arith.Check

/-!
# The link terminal, natively

**`ltIdentity_of_tailLast`**: `linkTail`'s terminal check (`tailLast … = claim`, `LinkNat.Ok.terminal` natively) is
`link_terminal`'s identity `LtIdentity` at the row side's coefficient, shifts, base and certificate weight and
`tailLets`' `ν` and certificate, the pure part of `D3.Ok.hid`: what is left is that the guest's `.n 2846`,
`.n 2890`, `.n 2891`, `.n 19`'s cells, `.n 695`'s words and `w 1077` are those values (`linkSecStatement`'s
conclusions, at the honest context). **`VsCtx.hcar_nat`**: `D3.Ok.hcar`, from `vkStart_nat`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link.Arith (tailRowSide tailLets maxShift_tables)
open LeanVM.Guest.B1.VerifySub (tailLast tailNValues_tables)

@[expose] public section

/-- **The terminal check is `link_terminal`'s identity**, at the row side's and `tailLets`' values. -/
theorem ltIdentity_of_tailLast {layout : Layout} (htab : layout.tables = tables) {chunks : Chunks} {theta0 : E}
    {drawn r : List E} {m1 : E} {fresh : List E} {split : Split} {chi qPoint message : List E} {claim : E}
    (ht : tailLast layout chunks theta0 drawn r m1 fresh split chi qPoint message = claim) {σ : Val}
    (h2846 : σ (.n 2846) = (tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).coef)
    (h2891 : σ (.n 2891) = (tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).certWeight *
      (tailLets layout chunks theta0 drawn r m1 fresh split qPoint).cert)
    (h2890 : σ (.n 2890) = prodE (qPoint.map (1 + ·)) *
      (tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).base) :
    LtIdentity chunks σ claim r (message.drop 80)
      (tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).shifts
      (tailLets layout chunks theta0 drawn r m1 fresh split qPoint).nu := by
  set R := tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message with hR
  set L := tailLets layout chunks theta0 drawn r m1 fresh split qPoint with hL
  unfold LtIdentity
  rw [← ht, h2846, h2891, h2890]
  unfold tailLast
  dsimp only
  rw [tailNValues_tables htab, htab, maxShift_tables, ← hR, ← hL,
    show L.nu.map (fun n ↦ L.cert * R.certWeight * n) = L.nu.map ((R.certWeight * L.cert) * ·) from
      List.map_congr_left fun n _ ↦ by rw [mul_comm L.cert]]

section
variable {x : VsCtx} {L : LinkNat}

/-- **`D3.Ok.hcar`**: `verify_keccak`'s start sponge, `packed_message`'s returns, is carried. -/
theorem VsCtx.hcar_nat {rest : List E} (hret : CausalRule x.ret) (hb : L.bits x.lay ≠ 0)
    (hq : linkQVars x.lay ≠ 0) (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) (hm : L.msg.length = 144)
    (r1287 : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0) :
    ∃ sp, (⟨[x.w 1288, x.w 1289, x.w 1290, x.w 1291, x.w 1292], []⟩ : Fs).Carries sp := by
  refine ⟨⟨(L.F4 x.lay x.nF).perm, [], none⟩, ?_, rfl, rfl⟩
  rw [x.vkStart_nat hret hb hq hw hb18 hm r1287]
  rfl

end

end
end LeanVM.Guest.B1.VsC
