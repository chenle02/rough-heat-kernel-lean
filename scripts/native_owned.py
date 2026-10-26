"""Project adapter of the upstream owned collector and compiled escape controls.
Actual execution and independent readback are required for verification credit.
"""
from pathlib import Path
import gzip, hashlib, json, os, subprocess, tempfile, sys
if sys.flags.optimize: raise RuntimeError("Python assertion validation must not be optimized out")
root = Path(__file__).resolve().parents[1]
os.chdir(root)
out = Path(os.environ['LIBRARY_AUDIT_DIR']).resolve()
out.mkdir(parents=True, exist_ok=False)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
binary = root/'tools/axiom-audit/.lake/build/bin/axiom-audit'
subprocess.run(['lake','build'], cwd=binary.parents[3], check=True)
allowed = {'propext','Classical.choice','Quot.sound'}
controls = []
with tempfile.TemporaryDirectory(prefix='compiled-escape-') as td:
    t = Path(td)
    env = os.environ.copy()
    env['LEAN_PATH'] = str(t)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip()
    for module, expected in [('EscapePositive', set()), ('EscapeNegative', {'sorryAx','EscapeNegative.injected'}), ('EscapeNative', {'_private.EscapeNative.0.EscapeNative.nativeTrue._native.native_decide.ax_1_1'})]:
        source = root/'tests'/(module+'.lean')
        with (out/(module+'-build.log')).open('w') as log:
            subprocess.run(['lake','env','lean','-R',str(source.parent),str(source),'-o',str(t/(module+'.olean'))],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
        with (out/(module+'.json')).open('w') as log, (out/(module+'.stderr')).open('w') as err:
            rc = subprocess.run(['lake','env',str(binary),module],cwd=root,env=env,stdout=log,stderr=err,check=False).returncode
        data = json.loads((out/(module+'.json')).read_text())
        actual = {a for row in data['declarations'] for a in row['axioms']} - allowed
        if rc != bool(expected) or actual != expected or data['ok'] != (not expected):
            sys.exit('Compiled escape control failed: '+module)
        if module == 'EscapePositive':
            names={row['name'] for row in data['declarations']}
            if not {'EscapePositive.publicTrue','EscapePositive.retainedTrue'} <= names or not any(name.endswith('.privateTrue') for name in names) or data['owned_count']!=3:
                sys.exit('Incomplete positive control')
        if module == 'EscapeNegative':
            rows=data['declarations']
            for name, ax in [('privateFalse','sorryAx'),('retainedFalse','sorryAx'),('fromCustom','EscapeNegative.injected')]:
                if not any(row['name'].endswith('.'+name) and ax in row['axioms'] for row in rows):
                    sys.exit('Missing control coverage: '+name)
        controls.append({'module':module,'compile_exit':0,'audit_exit':rc,'forbidden_axioms':sorted(actual)})

import re

IMPORT_ONLY_ROOTS = {'RoughHeatKernel', 'RoughHeatKernelTest', 'Challenge', 'Solution'}
def import_only_source(source):
    # Same nested block/line-comment rules as the established strict fixture guard.
    # Strings are retained so a declaration or evaluator cannot masquerade as an import.
    text = source.read_text()
    code, depth, i = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: code.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i): depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i); i = len(text) if end < 0 else end
        elif text[i] == '"':
            # Import-only source needs no string tokens; refuse rather than interpret one.
            return False
        else: code.append(text[i]); i += 1
    if depth: return False
    lines = [line.strip() for line in ''.join(code).splitlines() if line.strip()]
    # Lean module system: an optional leading `module` header, then only (public) imports.
    if lines[:1] == ['module']: lines = lines[1:]
    return bool(lines) and all(re.fullmatch(r'(?:public )?import [A-Za-z_][A-Za-z0-9_.]*', line) for line in lines)

# Two cones deliberately define the same declaration names. Never import them into one environment.
prod = ['RoughHeatKernel', 'RoughHeatKernelTest', 'Solution']
cones = {'production': [], 'reference': []}
for cone, prefixes in [('production', prod), ('reference', ['Challenge'])]:
    for prefix in prefixes:
        paths = [root/(prefix+'.lean'), *sorted((root/prefix).rglob('*.lean'))]
        for source in paths:
            if source.is_file(): cones[cone].append(str(source.relative_to(root).with_suffix('')).replace('/', '.'))
    modules=sorted(set(cones[cone]))
    if not modules: raise RuntimeError('Empty cone')
    sources={m: sha(root/(m.replace('.','/')+'.lean')) for m in modules}
    lean_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip()
    def providers():
        bindings={}
        for m in modules:
            relative=Path(m.replace('.','/')).with_suffix('.olean')
            actual=next((Path(part)/relative for part in lean_path.split(os.pathsep) if (Path(part)/relative).is_file()),None)
            expected=root/'.lake/build/lib/lean'/relative
            assert actual is not None and actual.resolve()==expected.resolve(), (m,actual,expected)
            bindings[m]={'source_sha256':sources[m],'object':str(actual.resolve()),'object_sha256':sha(actual)}
        return bindings
    provider_pre=providers()
    (out/(cone+'-providers-pre.json')).write_text(json.dumps(provider_pre,sort_keys=True,indent=2)+'\n')
    raw=out/(cone+'.json')
    with raw.open('w') as log, (out/(cone+'.stderr')).open('w') as err:
        subprocess.run(['lake','env',str(binary),*modules],stdout=log,stderr=err,check=True)
    report=json.loads(raw.read_text()); rows=report['declarations']
    assert report['schema']=='lean-library-native-owned-audit/1' and report['ok'] is True and set(report['modules'])==set(modules)
    assert rows and report['owned_count']==len(rows)==len({r['name'] for r in rows})
    assert all(r['module'] in modules and r['type_expr'] and not(set(r['axioms'])-allowed) for r in rows)
    assert any(r['name'].startswith('_private.') for r in rows), 'Missing private ownership'
    if cone == 'production':
        expected_core=set((root/'EXPECTED-PRODUCTION-OWNERS.txt').read_text().splitlines())
        actual_core={r['name'] for r in rows if r['module']=='RoughHeatKernel' or r['module'].startswith('RoughHeatKernel.')}
        assert actual_core==expected_core, ('Production owner identity drift', sorted(expected_core-actual_core), sorted(actual_core-expected_core))
    records=[]
    skipped=[]
    for module in modules:
        if module in IMPORT_ONLY_ROOTS:
            owned=[row for row in rows if row['module']==module]
            assert not owned and import_only_source(root/(module.replace('.','/')+'.lean')), ('Nonempty or non-import-only umbrella', module)
            skipped.append({'module':module,'source_sha256':sources[module],'owned_count':0,'reason':'independently import-only source and zero actual compiler-owned rows'})
            continue
        prefixed=[name for name in modules if name==module or name.startswith(module+'.')]
        assert prefixed==[module], ('Unexpected non-leaf scientific selector requires review', module, prefixed)
        # Independent per-selector kernel replay, sequential and one Lean thread.
        path=out/(module+'.leanchecker.log')
        with path.open('w') as log:
            proc=subprocess.run(['lake','env','leanchecker','-v',module],stdout=log,stderr=subprocess.STDOUT,env=dict(os.environ,LEAN_NUM_THREADS='1'))
        selected=[line[len('replaying '):] for line in path.read_text().splitlines() if line.startswith('replaying ')]
        assert proc.returncode==0 and selected==[module], (module, proc.returncode, selected)
        records.append({'module':module,'exit':proc.returncode,'log_sha256':sha(path)})
    assert {r['module'] for r in records} | {r['module'] for r in skipped} == set(modules)
    assert not ({r['module'] for r in records} & {r['module'] for r in skipped})
    assert sources=={m:sha(root/(m.replace('.','/')+'.lean')) for m in modules}
    provider_post=providers()
    assert provider_pre==provider_post
    (out/(cone+'-providers-post.json')).write_text(json.dumps(provider_post,sort_keys=True,indent=2)+'\n')
    (out/(cone+'-inventory.json')).write_text(json.dumps({'modules':modules,'source_sha256':sources,'declarations':{r['name']:r['module'] for r in rows},'owned_count':len(rows),'replay':records,'import_only_skipped':skipped},sort_keys=True,indent=2)+'\n')
    with raw.open('rb') as src, (out/(cone+'.json.gz')).open('wb') as dst:
        with gzip.GzipFile(fileobj=dst,mode='wb',mtime=0,filename='') as gz:
            import shutil
            shutil.copyfileobj(src,gz)
    print('native-owned-cone:',cone,'modules:',len(modules),'owned:',len(rows),'sha256:',sha(raw),'gzip-sha256:',sha(out/(cone+'.json.gz')))
(out/'CONTROLS.json').write_text(json.dumps(controls,indent=2)+'\n')
print('native owned + actual compiled escape controls + exact module replay: PASS')
