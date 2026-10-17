import XmssSecurity.Proof.RandomOracle

namespace XmssSecurity

def hashOutputHigh (output : HashOutput) : Digest :=
  (Rom.hashOutputEquivDigestPair output).1

end XmssSecurity
