"""Deletes the mode walk's route once every function is on the core route (`formal/notes/core-mode.md`).

Preconditions (checked; `--force` skips them, for a dry run only): `Mode.offCerts` (`Mode/Certs/List.lean`'s
`offGroups`), `CoreMode.offSigs` (`CoreMode/Gen/Certs/List.lean`) and `Res.resExc` (`Res/ResGiven.lean`) are empty.

Then:
1. `EndExecFinal.lean`: the certificates are the core route's alone (`allCerts := CoreMode.coreCerts`), `assembled`
   from `OffFacts.nil CoreMode.coreCerts_nodup`; its imports of the functions off the route (`Res.Off`,
   `EndExecRCld`, `EndExecRCp`, `EndExecRGkrC`, `EndExecRLce`) go.
2. Every module the library's and the tests' roots then no longer reach is deleted (`git rm`): the mode walk's
   certificates (`Pack/*/Mode*`, `Mode/Certs*`), the residuals' certificates (`Res/*Certs*`, `Res/Off`, ...) and
   the hand modules only they import.
3. `scripts/mode-cert/`, `scripts/res-cert/` are deleted, and `scripts/regen-guest.sh` loses the `mode` step,
   the `res` step's `res-cert` parts and `MODE_CERT_CACHE`.
4. Reported, not done: the modules named for the old route that the end theorem still reaches (hand modules to
   move, `(b)`), and every script still naming `MODE_CERT_CACHE` or `mode-cert`.

Before it (found by a dry run with the functions off the route stubbed, `--force`):
* (done here) `Res/ResGiven.lean`, `res-cert/sel.py`'s, was read through `Res/SubDefs` only for its import: SubDefs
  drops it (`sub_defs`), and it goes with the rest.
* The modules named for the old route that the end theorem still reaches (reported in 4: `EndExecR*`, `Mode/*`,
  `Res/*Defs`, `Bridge/AlignWin` through the hint bridge) are hand modules to rename or move, `(b)`.
* `sigc.py`, `frame_gen.py`, `frame_data.py`, `frame_run.py`, `route.py` read `MODE_CERT_CACHE` only for functions off
  the route: with none left their branches are dead and go with it.

usage (from formal/lean_vm): python3 -I scripts/core-mode/drop-mode-route.py [--force] [--no-git] [--report-only]
"""
import os, re, sys, glob, shutil, subprocess, collections

LV = os.getcwd()
G = os.path.join(LV, 'LeanVM', 'Guest')
FORCE, NOGIT, REPORT = '--force' in sys.argv, '--no-git' in sys.argv, '--report-only' in sys.argv
RX = re.compile(r'^(?:public |meta |private )*import (?:all )?(\S+)', re.M)
OFF_IMPORTS = ['LeanVM.Guest.Res.Off', 'LeanVM.Guest.EndExecRCld', 'LeanVM.Guest.EndExecRCp',
               'LeanVM.Guest.EndExecRGkrC', 'LeanVM.Guest.EndExecRLce']
KEEP_IMPORTS = ['LeanVM.Guest.CoreMode.Gen.AnyLinkOk', 'LeanVM.Guest.CoreMode.Gen.MonoWalkOk']
OLD = re.compile(r'LeanVM\.Guest\.(Pack\.[^.]+\.Mode|Mode\.|Res\.|EndExecR|Bridge\.AlignWin)')


def text(p):
    return open(p, encoding='utf-8').read()


def empty_list(path, name):
    """`def name ... := []` (or a list of empty lists) in `path`."""
    t = text(path)
    m = re.search(r'def %s\b[^:]*:[^=]*:=\s*(.*?)\n\n' % name, t, re.S)
    return m is not None and re.fullmatch(r'[\[\]\s,]*', m.group(1)) is not None


def preconditions():
    out = {'Mode.offGroups': empty_list(os.path.join(G, 'Mode', 'Certs', 'List.lean'), 'offGroups'),
           'CoreMode.offSigs': empty_list(os.path.join(G, 'CoreMode', 'Gen', 'Certs', 'List.lean'), 'offSigs'),
           'Res.resExc': empty_list(os.path.join(G, 'Res', 'ResGiven.lean'), 'resExc')}
    return out


def graph():
    imp, files = {}, {}
    for base, strip in ((os.path.join(LV, 'LeanVM'), LV), (os.path.join(LV, 'tests'), os.path.join(LV, 'tests'))):
        for dp, _, fs in os.walk(base):
            for f in fs:
                if f.endswith('.lean'):
                    p = os.path.join(dp, f)
                    m = os.path.relpath(p, strip)[:-5].replace(os.sep, '.').replace('«', '').replace('»', '')
                    imp[m] = [x.replace('«', '').replace('»', '') for x in RX.findall(text(p))]
                    files[m] = p
    imp['LeanVM'] = RX.findall(text(os.path.join(LV, 'LeanVM.lean')))
    return imp, files


def reach(imp, cut):
    roots = ['LeanVM'] + [m for m in imp if m.startswith('LeanVMTests')]
    st, seen = list(roots), set(roots)
    while st:
        m = st.pop()
        for n in imp.get(m, []):
            if n not in seen and (m, n) not in cut:
                seen.add(n)
                st.append(n)
    return seen


def end_final():
    """`EndExecFinal.lean` with the core route's certificates alone."""
    p = os.path.join(G, 'EndExecFinal.lean')
    t = text(p)
    for m in OFF_IMPORTS:
        t = t.replace('public import %s\n' % m, '')
    # what it names that only those imports brought
    t = t.replace('public import LeanVM.Guest.CoreMode.Gen.Certs\n', 'public import LeanVM.Guest.CoreMode.Gen.Certs\n'
                  + ''.join('public import %s\n' % m for m in KEEP_IMPORTS))
    # no frame interface left unchecked: `OpenGaps` has no field
    t = re.sub(r'structure OpenGaps : Prop where\n.*?modeHyps : Mode.ModeHyps\n', 'structure OpenGaps : Prop\n', t, flags=re.S)
    t = t.replace('theorem openGaps : OpenGaps := ⟨⟨⟩⟩', 'theorem openGaps : OpenGaps := ⟨⟩')
    t = t.replace('have h := assembled O.modeHyps', 'have h := assembled')
    t = t.replace('theorem execGaps_of (O : OpenGaps) :', 'theorem execGaps_of (_O : OpenGaps) :')
    t = t.replace('noncomputable abbrev allCerts : List Mode.Cert := CoreMode.coreCerts ++ Mode.offCerts',
                  'noncomputable abbrev allCerts : List Mode.Cert := CoreMode.coreCerts')
    a = t.index('theorem assembled (h : Mode.ModeHyps)')
    b = t.index('/-- **`ExecGaps` from the open facts**')
    t = t[:a] + ('theorem assembled :\n'
                 '    ModeCerts allCerts Fn.«main».modeCert Mode.guestE0 ∧ (∀ K ∈ allCerts, K.F.entry ≠ 0) ∧\n'
                 '      ResTop allCerts alignA ∧ TermNode allCerts := by\n'
                 '  simpa only [List.append_nil] using\n'
                 '    assemble (A := alignA) CoreMode.coreFacts (OffFacts.nil CoreMode.coreCerts_nodup)\n\n') + t[b:]
    return p, t


def sub_defs():
    """`Res/SubDefs.lean` without `Res/ResGiven` (`res-cert/sel.py`'s, gone with it): its families take the list of
    certificates given whole as a parameter (`SubOk exc K`), and with none left nothing names it."""
    p = os.path.join(G, 'Res', 'SubDefs.lean')
    t = text(p).replace('public import LeanVM.Guest.Res.ResGiven\n', '')
    t = t.replace('`EndExec.resOpen_subOk` (`EndExecRSub`): given `SubOk resExc` of every certificate and the listed\n'
                  'certificates\' residuals, no `sub` residual outside the families is left open.\n', '')
    return p, t


def regen_script():
    p = os.path.join(LV, 'scripts', 'regen-guest.sh')
    t = text(p)
    t = re.sub(r'\npart_mode\(\) \{.*?\n\}\n', '\n', t, flags=re.S)
    t = t.replace(' mode bridge', ' bridge').replace('parts_mode=(mode) targets_mode=()\n', '')
    for s in ('term', 'sel', 'link', 'mono', 'sub'):
        t = re.sub(r'  step "res: [^\n]*\(scripts/res-cert/%s\.py\)"\n  python3 -I scripts/res-cert/%s\.py "\$\{check\[@\]\}"\n'
                   % (s, s), '', t)
    t = re.sub(r'  if \[ \$\{#check\[@\]\} -eq 0 \]; then\n    step "core-mode: the mode certificates.*?\n  fi\n', '', t,
               flags=re.S)
    t = re.sub(r'  if \[ ! -f "\$MODE_CERT_CACHE" \]; then.*?\n  \[ -f "\$MODE_CERT_CACHE" \] \|\| part_mode\n', '', t,
               flags=re.S)
    t = t.replace('export MODE_CERT_CACHE=$tmp/mode-cert.pkl CORE_MODE_CACHE=$tmp/core-mode.pkl',
                  'export CORE_MODE_CACHE=$tmp/core-mode.pkl')
    return p, t


def main():
    pre = preconditions()
    print('preconditions:', pre)
    if not all(pre.values()) and not FORCE:
        sys.exit('drop-mode-route: functions are still off the core route (--force for a dry run)')
    imp, files = graph()
    before = reach(imp, set())
    cut = {('LeanVM.Guest.EndExecFinal', m) for m in OFF_IMPORTS} | {('LeanVM.Guest.Res.SubDefs', 'LeanVM.Guest.Res.ResGiven')}
    imp['LeanVM.Guest.EndExecFinal'] = imp['LeanVM.Guest.EndExecFinal'] + KEEP_IMPORTS
    after = reach(imp, cut)
    gone = set(m for m in before - after if m in files)
    # modules no root reaches (built by the library's glob) that import a deleted one go too
    while True:
        more = {m for m in files if m not in after and m not in gone and any(n in gone for n in imp.get(m, []))}
        if not more:
            break
        print('  orphans importing deleted modules:', *sorted(more))
        gone |= more
    gone = sorted(gone)
    kept = sorted(m for m in after if OLD.match(m) and m in files)
    lines = lambda ms: sum(text(files[m]).count('\n') for m in ms)
    print('deleted: %d modules, %d lines' % (len(gone), lines(gone)))
    print('old-route modules still reached (to move): %d modules, %d lines' % (len(kept), lines(kept)))
    by = collections.Counter(re.sub(r'\d+', '#', m.split('.')[2] if not m.startswith('LeanVM.Guest.Pack') else 'Pack.*.' + m.split('.')[-1]) for m in kept)
    for k, v in by.most_common():
        print('  %-40s %d' % (k, v))
    scripts = sorted(os.path.relpath(p, LV) for p in glob.glob(os.path.join(LV, 'scripts', '**', '*.py'), recursive=True)
                     if not re.search(r'/(mode-cert|res-cert)/', p)
                     and re.search(r'MODE_CERT_CACHE|mode-cert|res-cert', text(p)))
    print('scripts still naming the mode walk:', *scripts, sep='\n  ')
    if REPORT:
        return
    p, t = end_final()
    open(p, 'w', encoding='utf-8').write(t)
    p, t = regen_script()
    open(p, 'w', encoding='utf-8').write(t)
    p, t = sub_defs()
    open(p, 'w', encoding='utf-8').write(t)
    paths = [files[m] for m in gone] + [os.path.join(LV, 'scripts', d) for d in ('mode-cert', 'res-cert')]
    if NOGIT:
        for q in paths:
            shutil.rmtree(q) if os.path.isdir(q) else os.remove(q)
    else:
        subprocess.run(['git', 'rm', '-rq', '--'] + paths, check=True)
    print('done: build LeanVM LeanVMTests, then scripts/regen-guest.sh --check')


if __name__ == '__main__':
    main()
