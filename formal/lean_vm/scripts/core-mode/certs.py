"""Writes the core route's certificates and what they give of the end theorem's assembly
(`EndExec.CoreFacts`, `CoreMode/Assemble.lean`), from the core route's data alone:

* `CoreMode/Gen/<pack>/Cert.lean`: each routed function's certificate (`Fn.«k».modeCert`: its
  `envC`, `funC` and code), its callees' signatures (`modeSigs`), the pack's list (`CorePack.«p».certs`)
  and each one's static facts, frame interface (`fnSpec_core` of its `fnSpecC`), code, termination
  facts (`termOk_of` at its index) and residuals (`NzOnly CoreMode.coreNzs`);
* `CoreMode/Gen/Certs/List.lean`: the list `coreCerts`, pack by pack, and the core data `coreTable`;
* `CoreMode/Gen/Certs/Nodup.lean`: no entry twice;
* `CoreMode/Gen/Certs/In<k>.lean`: each certificate's membership in `coreCerts`;
* `CoreMode/Gen/Certs/Sig<k>.lean`: each certificate's callee signatures among `coreCerts`;
* `CoreMode/Gen/Certs.lean`: `coreFacts : CoreFacts …` and `main`'s start (`mainOk_core`).

Every function is on the route: a callee off it fails here.
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/certs.py [--check]"""
import sys, os, re, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import framelit as FL  # noqa: E402
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
CM = os.path.join(ROOT, 'CoreMode')
OUT = os.path.join(CM, 'Gen')
# packs per `In<k>` and `Sig<k>` module
SIGPACKS = 8


header = genfiles.header('core-mode/certs.py')


def imports(ms):
    # the certificates read the deployed guest's data, which `Statement/Data` does not expose
    return ''.join('public import %s\n' % m for m in sorted(ms)) + 'import all Statement.Data.Bytecode\nimport all Statement.Data.AdviceHints\n'


def fq(k): return 'Fn.«%s»' % k


def wrap(xs, ind=2, width=100):
    """A list literal of `xs`, its lines at most `width` wide where the items allow."""
    lines, cur = [], ''
    for x in xs:
        if cur and len(cur) + len(x) + 2 > width - ind: lines.append(cur + ','); cur = ''
        cur = cur + ', ' + x if cur else x
    lines.append(cur)
    return '[' + ('\n' + ' ' * (ind + 1)).join(lines) + ']'


def load():
    """Each pack's routed functions in its `coreFns` order; each one's callees and residuals, and its code's glue module."""
    packs = {}
    for f in sorted(glob.glob(os.path.join(OUT, '*', 'Core.lean'))):
        m = re.search(r'def coreFns : List CoreMode.CFun :=\n(.*?)\n\n', open(f, encoding='utf-8').read(), re.S)
        if m:
            ks = re.findall(r'Fn\.«([^»]+)»\.cfun', m.group(1))
            if ks: packs[f.split(os.sep)[-2]] = ks
    glue = {}
    for f in glob.glob(os.path.join(CM, 'GlueC', '*.lean')):
        t = open(f, encoding='utf-8').read()
        for k in re.findall(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', t, re.M) + re.findall(r'^theorem (?:Fn\.)?«([^»]+)»\.code_mem ', t, re.M):
            glue[k] = os.path.basename(f)[:-5]
    callees, nores = {}, set()
    for f in glob.glob(os.path.join(CM, 'Pack', '*', 'Frame*.lean')):
        t = open(f, encoding='utf-8').read()
        nss = [(m.start(), m.group(1)) for m in re.finditer(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', t, re.M)]
        def name(m):
            if m.group(1): return m.group(1)
            return [n for i, n in nss if i < m.start()][-1]
        for m in re.finditer(r'def (?:Fn\.«([^»]+)»\.)?envC : Mode\.Env\s*:=\s*CoreMode\.envOf\s*\[(.*?)\]', t, re.S):
            callees[name(m)] = re.findall(r'Fn\.«([^»]+)»\.csig', m.group(2))
        for m in re.finditer(r'def (?:Fn\.«([^»]+)»\.)?funC : Mode\.Fun\s*:=(.*?)⟩\n', t, re.S):
            if re.search(r'csig,\s+\.nil,\s+\.nil,\s+\.nil,\s+(false|true),\s+\.nil$', m.group(2)): nores.add(name(m))
        for k, d in FL.parse(t).items():
            callees[k] = d['callees']
            if 'fnz' not in d: nores.add(k)
    return packs, callees, nores, glue


def render():
    packs, callees, nores, glue = load()
    routed = {k for ks in packs.values() for k in ks}
    pk = sorted(packs)
    # each function's callees as its environment lists them (`envC`, by entry): the trie's order, which moves with the
    # entries' bits, never printed (`sigsIn_of_list`)
    sigs = {k: callees[k] for k in routed}
    off = sorted({m for k in routed for m in callees[k] if m not in routed})
    if off:
        sys.exit('certs: callees off the core route: ' + ', '.join(off))
    files = {}
    CE = 'EndExec.CertE CoreMode.hcTab CoreMode.coreNzs'
    # each pack's certificates
    for p in pk:
        ks = packs[p]
        mod = 'LeanVM.Guest.CoreMode.Gen.«%s».Cert' % p
        t = [header(mod, 'The core route\'s certificates of the pack\'s functions and their facts.')]
        t.append(imports({'LeanVM.Guest.CoreMode.Gen.«%s».Route' % p, 'LeanVM.Guest.CoreMode.Gen.HcTab',
                          'LeanVM.Guest.CoreMode.Nzs', 'LeanVM.Guest.CoreMode.CertLit'} | {'LeanVM.Guest.CoreMode.GlueC.«%s»' % glue[k] for k in ks}))
        t.append('meta import LeanVM.Guest.KernelLit\n\nset_option Elab.async false\nset_option linter.style.nameCheck false\n\n'
                 '/-! Each function\'s certificate (`modeCert`: its `envC`, `funC` and code), its callees\' signatures\n'
                 '(`modeSigs`), and the certificate with its facts (`ce`): `core_cert%`, `CoreMode/CertLit.lean`. -/\n\n'
                 'namespace LeanVM.Guest.Fn\n\nopen LeanVM.Guest LeanVM.Guest.EndExec\n\n@[expose] public section\n\n')
        for i, k in enumerate(ks):
            t.append('core_cert%% «%s» «%s» %d %s[%s]\n' % (
                k, p, i, '' if k in nores else 'nz ', ', '.join('«%s»' % m for m in sigs[k])))
        t.append('\nend\n\nend LeanVM.Guest.Fn\n\nnamespace LeanVM.Guest.CorePack.«%s»\n\n@[expose] public section\n\n'
                 '/-- The pack\'s certificates with their facts. -/\nnoncomputable def ces : List (%s) :=\n  %s\n\n'
                 'end\n\nend LeanVM.Guest.CorePack.«%s»\n' % (p, CE, wrap(['Fn.«%s».ce' % k for k in ks]), p))
        files[os.path.join(OUT, p, 'Cert.lean')] = ''.join(t)
    # the list
    mod = 'LeanVM.Guest.CoreMode.Gen.Certs.List'
    t = [header(mod, 'The core route\'s certificates and its core data.')]
    t.append(imports({'LeanVM.Guest.CoreMode.Gen.«%s».Cert' % p for p in pk}))
    t.append('\nset_option Elab.async false\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest.CoreMode\n\n'
             'open LeanVM.Guest LeanVM.Guest.Mode\n\n@[expose] public section\n\n')
    t.append('/-- The core route\'s certificates with their facts, by pack. -/\n'
             'noncomputable def corePacks : List (List (%s)) :=\n  %s\n\n' % (CE, wrap(['CorePack.«%s».ces' % p for p in pk])))
    t.append('/-- **The core route\'s certificates.** -/\nnoncomputable def coreCerts : List Mode.Cert := corePacks.flatten.map (·.K)\n\n')
    t.append('/-- **The core route\'s data**, pack by pack. -/\nnoncomputable def coreTable : List CoreMode.CFun := corePacks.flatten.map (·.cf)\n\n')
    t.append('end\n\nend LeanVM.Guest.CoreMode\n')
    files[os.path.join(OUT, 'Certs', 'List.lean')] = ''.join(t)
    mod = 'LeanVM.Guest.CoreMode.Gen.Certs.Nodup'
    t = [header(mod, 'The core route\'s certificates: no entry twice.')]
    t.append(imports({'LeanVM.Guest.CoreMode.Gen.Certs.List'}))
    t.append('\nset_option Elab.async false\n\nnamespace LeanVM.Guest.CoreMode\n\nopen LeanVM.Guest LeanVM.Guest.Mode\n\n'
             'public section\n\n')
    t.append('/-- No entry twice. -/\ntheorem coreCerts_nodup : nodupB (coreCerts.map (·.F.entry)) 0 = true := by decide +kernel\n\n')
    t.append('end\n\nend LeanVM.Guest.CoreMode\n')
    files[os.path.join(OUT, 'Certs', 'Nodup.lean')] = ''.join(t)
    # a fixed number of packs a module, so that a function added to or removed from a pack changes only its own
    chunks = [pk[i:i + SIGPACKS] for i in range(0, len(pk), SIGPACKS)]
    # each certificate's membership
    for c, ps in enumerate(chunks):
        mod = 'LeanVM.Guest.CoreMode.Gen.Certs.In%d' % c
        t = [header(mod, 'The core route\'s certificates, each among them (`modeCert_in`), pack by pack.')]
        t.append(imports({'LeanVM.Guest.CoreMode.Gen.Certs.List'}))
        t.append('\nset_option Elab.async false\nset_option linter.style.nameCheck false\n\n'
                 'namespace LeanVM.Guest.Fn\n\npublic section\n\n')
        for p in ps:
            j = pk.index(p)
            for i, f in enumerate(packs[p]):
                t.append('cert_in%% «%s» %d %d\n' % (f, j, i))
        t.append('\nend\n\nend LeanVM.Guest.Fn\n')
        files[os.path.join(OUT, 'Certs', 'In%d.lean' % c)] = ''.join(t)
    # the callee signatures
    for c, ps in enumerate(chunks):
        mod = 'LeanVM.Guest.CoreMode.Gen.Certs.Sig%d' % c
        t = [header(mod, 'The core route\'s certificates\' callee signatures, pack by pack.')]
        t.append(imports({'LeanVM.Guest.CoreMode.Gen.Certs.In%d' % d for d in range(len(chunks))}))
        t.append('\nset_option Elab.async false\n')
        for p in ps:
            sp = []
            for k in packs[p]:
                one = ['sig_in%% «%s»' % m for m in sigs[k]]
                sp.append('sigsIn_of_list %s.modeSigs fa%%%s' % (fq(k), wrap(one, 6, 118)))
            t.append('\nnamespace LeanVM.Guest.CorePack.«%s»\n\nopen LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.EndExec\n\n'
                     'public section\n\ntheorem certs_sigs : ∀ e ∈ ces, SigsIn CoreMode.coreCerts e.K := fa%%[\n  %s]\n\n'
                     'end\n\nend LeanVM.Guest.CorePack.«%s»\n' % (p, ',\n  '.join(sp), p))
        files[os.path.join(OUT, 'Certs', 'Sig%d.lean' % c)] = ''.join(t)
    mod = 'LeanVM.Guest.CoreMode.Gen.Certs'
    t = [header(mod, 'What the core route\'s data gives of the end theorem\'s assembly (`EndExec.CoreFacts`).')]
    t.append(imports({'LeanVM.Guest.CoreMode.Gen.Certs.Sig%d' % c for c in range(len(chunks))} |
                     {'LeanVM.Guest.CoreMode.Gen.Certs.Nodup', 'LeanVM.Guest.CoreMode.NzsOk'}))
    t.append('\nset_option Elab.async false\n\nnamespace LeanVM.Guest.CoreMode\n\nopen LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.EndExec\n\n'
             'public section\n\n')
    t.append('theorem coreCerts_sigs : ∀ K ∈ coreCerts, SigsIn coreCerts K :=\n  CertE.fa (ls := corePacks) fa%%%s\n\n' % (
        wrap(['CorePack.«%s».certs_sigs' % p for p in pk], 6)))
    t.append('/-- **What the core route gives of the end theorem\'s assembly.** -/\n'
             'theorem coreFacts : CoreFacts CoreMode.hcTab coreCerts coreTable coreNzs Fn.«main».modeCert :=\n'
             '  CoreFacts.of corePacks coreCerts_sigs coreNzs_ok coreCerts_nodup Fn.«main».modeCert_in rfl (by decide +kernel) rfl\n'
             '    (by decide +kernel)\n\n')
    t.append('/-- **`main`\'s certificate starts as the prologue leaves it.** -/\n'
             'theorem mainOk_core : MainOk Fn.«main».modeCert guestE0 := mainOk_guest rfl rfl\n\nend\n\nend LeanVM.Guest.CoreMode\n')
    files[os.path.join(OUT, 'Certs.lean')] = ''.join(t)
    return files


def main(argv):
    check = '--check' in argv
    files = render()
    have = glob.glob(os.path.join(OUT, '*', 'Cert.lean')) + glob.glob(os.path.join(OUT, 'Certs', '*.lean'))
    bad = genfiles.sync(files, have, check)
    genfiles.fail_if_stale(bad, check)
    print('core certificates: %d files, %s' % (
        len(files), 'unchanged' if not bad else ('stale' if check else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
