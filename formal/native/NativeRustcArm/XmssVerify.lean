module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Common.Update.Names
public import NativeRustcArm.Code.Xmss.LayerRead.Names
public import NativeRustcArm.Code.Xmss.WotsLeaf.Names
public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.XmssVerify.HeadRun
public import NativeRustcArm.XmssVerify.ParseRun
public import NativeRustcArm.XmssVerify.Final

/-!
# `xmss_verify` meets its contract

`xmssVerify_spec`: `xmss_verify`, placed anywhere in a program whose callees meet their contracts,
meets `XmssVerifyPre`/`XmssVerifyPost` (`NativeRustcArm.Spec.XmssVerify`): the prologue (`head`),
the copy of the signature's words (`copy`), the parsing of the key and the layers (`parse`), the
bottom and top layers and the comparison with the key's root (`layers`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm

/-- **`xmss_verify` meets its contract.** -/
public theorem xmssVerify_spec [Host] {k : Nat} (hp : Placed code k) {w : Nat → UInt64}
    (hmemset : Spec (label NativeRustcArm.Common.Memset.entryLabel) MemsetPre MemsetPost)
    (hmemcpy : Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hupdate : Spec (label NativeRustcArm.Common.Update.entryLabel) UpdatePre UpdatePost)
    (hfinalize : Spec (label NativeRustcArm.Common.Finalize.entryLabel) FinalizePre
      FinalizePost)
    (hwots : Spec (label NativeRustcArm.Xmss.WotsLeaf.entryLabel) WotsLeafPre WotsLeafPost)
    (hfb : Spec (label NativeRustcArm.Xmss.LayerRead.entryLabel) LayerReadPre LayerReadPost) :
    Spec (label NativeRustcArm.Xmss.XmssVerify.entryLabel) (XmssVerifyPre w) (XmssVerifyPost w) := by
  intro m₀ hpre
  have P := pre_of hpre
  have Cs : Callees := ⟨hmemset, hmemcpy, hupdate, hfinalize, hwots, hfb⟩
  rw [hp.label NativeRustcArm.Xmss.XmssVerify.entry_at, NativeRustcArm.Xmss.XmssVerify.entryOffset, Nat.add_zero]
  exact head hp hmemset P fun st hpc h =>
    Eventually.bind (copy hp P hpc h) fun st' ⟨hpc', h'⟩ =>
      parse hp hfb P hpc' h' fun st'' hpc'' h'' =>
        Eventually.mono (layers hp Cs P hpc'' h'') fun s ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩

end NativeRustcArm.Xmss.XmssVerify
