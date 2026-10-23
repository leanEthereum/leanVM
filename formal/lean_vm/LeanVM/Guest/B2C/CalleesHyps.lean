/-
  LeanVM.Guest.B2C.CalleesHyps

  `main`'s callees' hypotheses (`CalleesHyps`) at the deployed frame sizes and certificates.
-/

module

public import LeanVM.Guest.End
public import LeanVM.Guest.B2C.FsAgree
public import LeanVM.Guest.B2C.CertFacts
public import LeanVM.Guest.B1.Main.CalleesProved
public import LeanVM.Guest.B1.Whir.OsCalleesFsOf
public import LeanVM.Guest.B1.Tables.VerifyTablesCAtB

/-!
# `CalleesHyps` at `B2C.fs` and `B2C.cert`

The pure callees' tree bounds at `fsOf` transfer to `fs` (`fsAgree_fs`, `GuestBoundsAt`),
`da_verify`'s and group 1's certificate facts hold there (`CertFacts`), `verify_tables` is
complete (`verify_tables_completeAtB`) and `open_stacked` is complete at frame sizes agreeing with
`fsOf` (`open_stacked_completeAtB_of`): `calleesHyps_b2c`, nothing assumed.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.End (bytecode)

@[expose] public section

theorem ctNames_eq_ctList : Digest.ctNames = ctList := by decide

/-- **`main`'s callees' hypotheses at the deployed frame sizes and certificates.** -/
noncomputable def calleesHyps_b2c : Main.CalleesHyps fs cert bytecode where
  Bx := 1721
  xmss := verify_lean_xmss_totalLe_at fsAgree_fs
  Bsp := 3157
  sphincs := verify_sig_lean_sphincs_totalLe_at fsAgree_fs
  Bsd := 627
  sd := statement_digest_totalLe_at fsAgree_fs
  Bdl := fun _ => 134
  dl := da_list_digest_totalLe_at fsAgree_fs
  B86 := fun e => logG e * 482
  l86 := loop86_totalLeOn_at fsAgree_fs
  Bct := fun t => ctBound[t]!
  ct := fun t ht => by rw [ctNames_eq_ctList]; exact ct_totalLe_at fsAgree_fs t ht
  Bsl := 147
  sl11 := scaled_log_L11_totalLe_at fsAgree_fs
  Bsl6 := 147
  sl6 := scaled_log_L6_totalLe_at fsAgree_fs
  dvc20 := dvc20
  dvc4 := dvc4
  Btab := VerifySub.vtTablesBound fs
  tab := VerifySub.verify_tables_completeAtB fs cert (by norm_num) bytecode
  tabW := fun w => VerifySub.verify_tables_completeAtW fs cert w (by norm_num) bytecode
  Bop := osBop fs (osCalleesMaxOf fs fsAgree_fs cert 16 g1Certs) (osPureSizes fs)
  op := open_stacked_completeAtB_of fs fsAgree_fs cert 16 g1Certs osOqFits

end
end LeanVM.Guest.B2C
