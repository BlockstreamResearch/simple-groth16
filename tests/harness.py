"""Run generated programs through tools/harness `hand`, which parses, prunes, executes, serialises,
decodes and executes again, and reports the cost bound and the sizes."""
import json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
HAND = os.environ.get('HAND', os.path.join(ROOT, 'tools', 'harness', 'target', 'release', 'hand'))
WORK = os.environ.get('HAND_WORK', os.path.join(ROOT, 'build'))


def run(name, program_text, witness, multi=None, timeout=3600):
    """`hand`'s result for the program on the witness: {'ok': True, 'cost', 'program_bytes',
    'witness_bytes', 'cells', 'seconds', ...} or {'ok': False, 'stage', 'error'}.  With `multi` (more
    witnesses) the program is parsed once and a list is returned.  Files go to build/ (HAND_WORK)."""
    os.makedirs(WORK, exist_ok=True)
    prog = os.path.join(WORK, name + '.simpl')
    with open(prog, 'w') as f:
        f.write(program_text)
    files = []
    for i, w in enumerate([witness] + (multi or [])):
        files.append(os.path.join(WORK, f'{name}.w{i}.json'))
        with open(files[-1], 'w') as f:
            json.dump(w, f)
    t0 = time.time()
    out = subprocess.run([HAND, prog] + files, capture_output=True, text=True, timeout=timeout)
    results = [json.loads(line) for line in out.stdout.splitlines() if line.startswith('{')]
    if not results:
        results = [{'ok': False, 'stage': 'harness', 'error': (out.stdout + out.stderr)[-2000:]}]
    for r in results:
        r['seconds'] = time.time() - t0
    return results if multi is not None else results[0]


def expect_ok(res, label=''):
    if not res.get('ok'):
        print(f'FAIL {label}: {res}', file=sys.stderr)
        raise SystemExit(1)
    return res
