import Sphincs.SecurityReferenceChoice
import Sphincs.SecuritySignatureWitness

/-! The reference WOTS word and counter chosen by the actual canonical encoding search at each
leaf, defined also for unsigned leaves and exhausted searches. -/

open OracleComp OracleSpec

namespace Sphincs.Security.SignatureWitness
open Concrete

attribute [local irreducible] messageDigest forestRecover otsLeaf treeFold
  Seeded.forestKey Seeded.treeRoot Seeded.treePath chainWalk encode

noncomputable def chosenWord (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : Encoding :=
  ReferenceChoice.word f parameter topLayer rootTree leaf (canonicalForest f parameter seed leaf)

noncomputable def chosenCounter (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : Option Counter :=
  (ReferenceChoice.selection f parameter topLayer rootTree leaf
    (canonicalForest f parameter seed leaf)).map Prod.fst

end Sphincs.Security.SignatureWitness
