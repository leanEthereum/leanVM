import re,sys
root=sys.argv[1]
def blocks(path, names):
    src=open(path).read()
    out={}
    for n in names:
        i=src.index('\ndef '+n+' ')
        lines=src[i+1:].split('\n')
        body=[lines[0]]
        for l in lines[1:]:
            if l.startswith(('/--','def ','/-!','end ','abbrev ','theorem ')):
                break
            body.append(l)
        out[n]='\n'.join(body).rstrip()+'\n'
    return out
def gen(path, names, recursive, xmss, binders):
    b=blocks(path,names)
    res=[]
    for n in names:
        t=b[n].replace('def '+n+' ','def '+n+'Fast ',1)
        if n in recursive:
            t=re.sub(r'\| none => '+n+' ', '| none => '+n+'Fast ', t)
        res.append(t)
        if n in recursive:
            last='cases Codeword.decode result <;> simp [ih]' if xmss else 'cases result <;> simp [ih]'
            res.append(f'''@[csimp] theorem {n}_eq_fast : @{n} = @{n}Fast := by
  funext m _ π {binders} attempts start
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      simp only [{n}, {n}Fast]
      congr 1
      funext result
      {last}
''')
        else:
            res.append(f'@[csimp] theorem {n}_eq_fast : @{n} = @{n}Fast := rfl\n')
    return '\n'.join(res)
sph=gen(root+'/Statement/LeanSphincs.lean',
  ['otsSecrets','otsPublicLeaf','otsSignFrom','otsSign','treeLevels','forsOpen','keygenInternal',
   'keygenFromSeed','signLayer','signWithExpandedKey','sign'],{'otsSignFrom'},False,
  'key layer tree leaf message')
xm=gen(root+'/Statement/LeanXmss.lean',
  ['otsSecrets','oneTimePublicKey','otsSignFrom','otsSign','treeNode','treePath','keygenFromSeed','signLayer','signWithSchemeSeed','sign'],{'otsSignFrom'},True,
  'parameter layer a b c d')
fast='''/-!
# The signers, compiled fast

Speed only, as `Statement/Fast/Schemes.lean` does for the verifiers: compiled, `sequenceFin`'s
`Fin.cases` looks up an index at a cost exponential in it, so the key generation and signing
functions above it are restated here word for word, each equal to its definition (`rfl`, by
induction for the counter search), and swapped in by `@[csimp]`, which acts where code is compiled:
in this module. (`scripts/signature-kat-fast.py` writes this section from the statement.)
-/

namespace Sphincs.KeyGenerationAndSigning

open Verification HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

'''+sph+'''
end Sphincs.KeyGenerationAndSigning

namespace LeanXmss.KeyGenerationAndSigning

open Verification HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

'''+xm+'''
end LeanXmss.KeyGenerationAndSigning

'''
p=root+'/lean_sphincs/cli/SignatureKat.lean'
s=open(p).read()
a=s.index('/-!\n# The signers, compiled fast')
b=s.index('open HashSig\n\nnamespace SignatureKat')
s=s[:a]+fast+s[b:]
open(p,'w').write(s)
