"""Writes the core route's certificates and the end theorem's assembly of them (`EndExec.assemble`,
`CoreMode/Assemble.lean`), from the core route's data alone:

* `CoreMode/Gen/<pack>/Cert.lean`: each routed function's certificate (`Fn.«k».modeCert`: its
  `envC`, `funC` and code), its callees' signatures (`modeSigs`), the pack's list (`CorePack.«p».ces`)
  and each one's static facts, frame interface (its `fnSpecC`, the contracts' table agreeing), code;
* `CoreMode/Gen/Certs/List.lean`: the routed certificates pack by pack (`corePacks`), and the
  functions off the route by signature (`offSigs`): every compiled function with a signature but none
  of a pack;
* `CoreMode/Gen/Certs/Nodup.lean`: no entry twice;
* `CoreMode/Gen/Certs/In<k>.lean`: each routed certificate's membership (`modeCert_in`);
* `CoreMode/Gen/Certs/Sig<k>.lean`: each routed certificate's callee signatures among the
  certificates, an off callee's by the hypothesis on the off functions (`EndExec.OffOk`);
* `CoreMode/Gen/Certs.lean`: `coreAssembled`, `ModeCerts`, each `FnSpec`, `main`'s start and its
  contract none, for any certificates of the off functions with their facts;
* `CoreMode/Gen/CertsTerm.lean`: `coreTermNodeA`, the termination facts at the entered instances,
  from the loops' check (`loopcheck.py`'s `Res.termAll`);
* `CoreMode/Gen/Certs/CfOk.lean`, once every pack's `Route.lean` is written (`core.py`): `tableOf_cfOk`, the core
  data table, each the deployed guest's (`CfOk`), the off functions' given.
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
# off functions per chunk of `offSigs`
OFFCH = 16


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
    """Each pack's routed functions in its `coreFns` order; each one's callees, and its code's glue module;
    every function's signature module."""
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
    sigmod = {}
    for f in glob.glob(os.path.join(CM, 'Sig', '*.lean')):
        for k in re.findall(r'^noncomputable def Fn\.«([^»]+)»\.csig : Mode\.Sig', open(f, encoding='utf-8').read(), re.M):
            sigmod[k] = os.path.basename(f)[:-5]
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
    return packs, callees, nores, glue, sigmod


def render():
    packs, callees, nores, glue, sigmod = load()
    routed = {k for ks in packs.values() for k in ks}
    pk = sorted(packs)
    # each function's callees as its environment lists them (`envC`, by entry): the trie's order, which moves with the
    # entries' bits, never printed (`sigsIn_of_list`)
    sigs = {k: callees[k] for k in routed}
    off = sorted(k for k in sigmod if k not in routed)
    offi = {k: i for i, k in enumerate(off)}
    missing = sorted({m for k in routed for m in callees[k] if m not in routed and m not in offi})
    if missing:
        sys.exit('certs: callees with no signature: ' + ', '.join(missing))
    if 'main' not in routed:
        sys.exit('certs: main is off the core route')
    files = {}
    CE = 'EndExec.CertE CoreMode.hcTab'
    mpack = [p for p in pk if 'main' in packs[p]][0]
    # each pack's certificates
    for p in pk:
        ks = packs[p]
        mod = 'LeanVM.Guest.CoreMode.Gen.«%s».Cert' % p
        t = [header(mod, 'The core route\'s certificates of the pack\'s functions and their facts.')]
        t.append(imports({'LeanVM.Guest.CoreMode.Gen.«%s».Core' % p, 'LeanVM.Guest.CoreMode.Gen.HcTab',
                          'LeanVM.Guest.CoreMode.Assemble', 'LeanVM.Guest.CoreMode.CertLit'} | {'LeanVM.Guest.CoreMode.GlueC.«%s»' % glue[k] for k in ks}))
        t.append('meta import LeanVM.Guest.KernelLit\n\nset_option Elab.async false\nset_option linter.style.nameCheck false\n\n'
                 '/-! Each function\'s certificate (`modeCert`: its `envC`, `funC` and code), its callees\' signatures\n'
                 '(`modeSigs`), and the certificate with its facts (`ce`): `core_cert%`, `CoreMode/CertLit.lean`. -/\n\n'
                 'namespace LeanVM.Guest.Fn\n\nopen LeanVM.Guest LeanVM.Guest.EndExec\n\n@[expose] public section\n\n')
        for k in ks:
            t.append('core_cert%% «%s» [%s]\n' % (k, ', '.join('«%s»' % m for m in sigs[k])))
        t.append('\nend\n\nend LeanVM.Guest.Fn\n\nnamespace LeanVM.Guest.CorePack.«%s»\n\n@[expose] public section\n\n'
                 '/-- The pack\'s certificates with their facts. -/\nnoncomputable def ces : List (%s) :=\n  %s\n\n'
                 'end\n\nend LeanVM.Guest.CorePack.«%s»\n' % (p, CE, wrap(['Fn.«%s».ce' % k for k in ks]), p))
        files[os.path.join(OUT, p, 'Cert.lean')] = ''.join(t)
    # the list
    mod = 'LeanVM.Guest.CoreMode.Gen.Certs.List'
    t = [header(mod, 'The core route\'s certificates and its core data.')]
    t.append(imports({'LeanVM.Guest.CoreMode.Gen.«%s».Cert' % p for p in pk} |
                     {'LeanVM.Guest.CoreMode.Sig.«%s»' % sigmod[k] for k in off}))
    t.append('\nset_option Elab.async false\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest.CoreMode\n\n'
             'open LeanVM.Guest LeanVM.Guest.Mode\n\n@[expose] public section\n\n')
    t.append('/-- The core route\'s certificates with their facts, by pack. -/\n'
             'noncomputable def corePacks : List (List (%s)) :=\n  %s\n\n' % (CE, wrap(['CorePack.«%s».ces' % p for p in pk])))
    och = [off[i:i + OFFCH] for i in range(0, len(off), OFFCH)]
    for c, ks in enumerate(och):
        t.append('/-- The functions off the core route, chunk %d. -/\nnoncomputable def offC%d : List Mode.Sig :=\n  %s\n\n'
                 % (c, c, wrap(['Fn.«%s».csig' % k for k in ks])))
    t.append('/-- **The functions off the core route**, by signature, chunk by chunk. -/\nnoncomputable def offSigs : List Mode.Sig :=\n  %s\n\n'
             % (''.join('offC%d ++ (' % c for c in range(len(och))) + '[]' + ')' * len(och)))
    t.append('end\n\nend LeanVM.Guest.CoreMode\n')
    files[os.path.join(OUT, 'Certs', 'List.lean')] = ''.join(t)
    mod = 'LeanVM.Guest.CoreMode.Gen.Certs.Nodup'
    t = [header(mod, 'The core route\'s certificates: no entry twice.')]
    t.append(imports({'LeanVM.Guest.CoreMode.Gen.Certs.List'}))
    t.append('\nset_option Elab.async false\n\nnamespace LeanVM.Guest.CoreMode\n\nopen LeanVM.Guest LeanVM.Guest.Mode\n\n'
             'public section\n\n')
    t.append('/-- No entry twice. -/\ntheorem coreCerts_nodup : nodupB (corePacks.flatten.map (·.K.F.entry) ++ offSigs.map (·.pc)) 0 = true := by\n  decide +kernel\n\n')
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
        t.append('\nset_option Elab.async false\nset_option linter.unusedVariables false\n')
        for p in ps:
            sp = []
            for k in packs[p]:
                one = [('sig_in%% «%s»' % m) if m in routed else ('off_in%% %d %d' % divmod(offi[m], OFFCH)) for m in sigs[k]]
                sp.append('sigsIn_of_list %s.modeSigs fa%%%s' % (fq(k), wrap(one, 6, 118)))
            t.append('\nnamespace LeanVM.Guest.CorePack.«%s»\n\nopen LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.EndExec\n\n'
                     'public section\n\ntheorem certs_sigs (offK : Mode.Sig → Mode.Cert) (Toff : List CoreMode.CFun)\n'
                     '    (hoff : OffOk CoreMode.corePacks CoreMode.offSigs offK Toff) :\n'
                     '    ∀ e ∈ ces, SigsIn (certsOf CoreMode.corePacks CoreMode.offSigs offK) e.K := fa%%[\n  %s]\n\n'
                     'end\n\nend LeanVM.Guest.CorePack.«%s»\n' % (p, ',\n  '.join(sp), p))
        files[os.path.join(OUT, 'Certs', 'Sig%d.lean' % c)] = ''.join(t)
    mod = 'LeanVM.Guest.CoreMode.Gen.Certs'
    t = [header(mod, 'The core route\'s certificates closed, the functions off it as a hypothesis (`EndExec.assemble`).')]
    t.append(imports({'LeanVM.Guest.CoreMode.Gen.Certs.Sig%d' % c for c in range(len(chunks))} |
                     {'LeanVM.Guest.CoreMode.Gen.Certs.Nodup'}))
    t.append('\nset_option Elab.async false\n\nnamespace LeanVM.Guest.CoreMode\n\nopen LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.EndExec\n\n'
             'public section\n\n')
    t.append('theorem coreCerts_sigs (offK : Mode.Sig → Mode.Cert) (Toff : List CoreMode.CFun)\n'
             '    (hoff : OffOk corePacks offSigs offK Toff) :\n'
             '    ∀ l ∈ corePacks, ∀ e ∈ l, SigsIn (certsOf corePacks offSigs offK) e.K :=\n  fa%%%s\n\n' % (
        wrap(['CorePack.«%s».certs_sigs offK Toff hoff' % p for p in pk], 2)))
    t.append('/-- **The core route\'s certificates closed**, for any certificates of the functions off it with their\n'
             'facts (`OffOk`): `ModeCerts`, each one\'s frame interface, `main`\'s start and its contract none, no entry `0`. -/\n'
             'theorem coreAssembled (offK : Mode.Sig → Mode.Cert) (Toff : List CoreMode.CFun)\n'
             '    (hoff : OffOk corePacks offSigs offK Toff) :\n'
             '    ModeCerts (certsOf corePacks offSigs offK) Fn.«main».modeCert guestE0 ∧\n'
             '      (∀ K ∈ certsOf corePacks offSigs offK, FnSpec hcTab (tableOf corePacks Toff) K) ∧\n'
             '      MainOk Fn.«main».modeCert guestE0 ∧ hcNone hcTab Fn.«main».modeCert.F.entry = true ∧\n'
             '      ∀ K ∈ certsOf corePacks offSigs offK, K.F.entry ≠ 0 :=\n'
             '  EndExec.assemble corePacks offSigs offK Toff hoff (coreCerts_sigs offK Toff hoff) coreCerts_nodup\n'
             '    (List.mem_map_of_mem (a := Fn.«main».ce) (List.mem_flatten.2 ⟨_, list_mem%% %d, list_mem%% %d⟩))\n'
             '    rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)\n\n'
             'end\n\nend LeanVM.Guest.CoreMode\n' % (pk.index(mpack), packs[mpack].index('main')))
    files[os.path.join(OUT, 'Certs.lean')] = ''.join(t)
    mod = 'LeanVM.Guest.CoreMode.Gen.CertsTerm'
    t = [header(mod, 'The termination facts at the entered instances, from the loops\' check (`EndExec.termNodeA_assembled`).')]
    t.append(imports({'LeanVM.Guest.CoreMode.Gen.Certs.List', 'LeanVM.Guest.CoreMode.Gen.LoopCheck',
                      'LeanVM.Guest.CoreMode.Fam.ResTA'}))
    t.append('\nnamespace LeanVM.Guest.CoreMode\n\nopen LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.EndExec\n\n'
             'public section\n\n'
             '/-- **The termination facts of the certificates carrying any**, for any certificates of the functions\n'
             'off the route with their facts (`OffOk`), at b2c\'s layout and an alignment entering each function at its\n'
             'compiled entry. -/\n'
             'theorem coreTermNodeA {al : String → Bool} {D : Ref → RefD} {A : String → Bridge.FnAl} {R : Ref → Prop}\n'
             '    (offK : Mode.Sig → Mode.Cert) (Toff : List CoreMode.CFun) (hoff : OffOk corePacks offSigs offK Toff)\n'
             '    (hE : EntIdx A) (hRH : ∀ r, R r → RefH (layB al) (D r) r) :\n'
             '    TermNodeA (layB al) D A R ((certsOf corePacks offSigs offK).filter hasTerm) :=\n'
             '  termNodeA_assembled hoff (progOk_of_termAll Res.termAll) hE hRH\n\n'
             'end\n\nend LeanVM.Guest.CoreMode\n')
    files[os.path.join(OUT, 'CertsTerm.lean')] = ''.join(t)
    # the routed core data, each the deployed guest's (`CfOk`), once every pack's `Route.lean` is written (`core.py`)
    if all(os.path.exists(os.path.join(OUT, p, 'Route.lean')) for p in pk):
        mod = 'LeanVM.Guest.CoreMode.Gen.Certs.CfOk'
        t = [header(mod, 'The core route\'s core data, each the deployed guest\'s (`CoreMode.CfOk`).')]
        t.append(imports({'LeanVM.Guest.CoreMode.Gen.Certs.List'} | {'LeanVM.Guest.CoreMode.Gen.«%s».Route' % p for p in pk}))
        t.append('\nset_option Elab.async false\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest.CoreMode\n\n'
                 'open LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.EndExec\n\npublic section\n\n')
        for p in pk:
            t.append('theorem cfOk_%s : ∀ e ∈ CorePack.«%s».ces, CfOk e.cf :=\n  fa%%%s\n\n'
                     % (p, p, wrap(['Fn.«%s».cfOk' % k for k in packs[p]], 2)))
        t.append('/-- **The routed core data, each the deployed guest\'s.** -/\n'
                 'theorem coreCfOk : ∀ l ∈ corePacks, ∀ e ∈ l, CfOk e.cf :=\n  fa%%%s\n\n' % wrap(['cfOk_%s' % p for p in pk], 2))
        t.append('/-- **The core data table, each the deployed guest\'s**, the off functions\' given. -/\n'
                 'theorem tableOf_cfOk {Toff : List CFun} (h : ∀ Cf ∈ Toff, CfOk Cf) :\n'
                 '    ∀ Cf ∈ tableOf corePacks Toff, CfOk Cf := by\n'
                 '  intro Cf hCf\n'
                 '  rcases List.mem_append.mp hCf with hCf | hCf\n'
                 '  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hCf\n'
                 '    obtain ⟨l, hl, he⟩ := List.mem_flatten.mp he\n'
                 '    exact coreCfOk l hl e he\n'
                 '  · exact h Cf hCf\n\n'
                 'end\n\nend LeanVM.Guest.CoreMode\n')
        files[os.path.join(OUT, 'Certs', 'CfOk.lean')] = ''.join(t)
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
