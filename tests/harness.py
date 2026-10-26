"""Run generated programs through tools/harness `hand`, which parses, prunes, executes, serialises,
decodes and executes again, and reports the cost bound and the sizes.  HAND overrides the path of hand
(default tools/harness/target/release/hand), HAND_WORK the directory for the files (default build/)."""

import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
HAND = os.environ.get('HAND', os.path.join(ROOT, 'tools', 'harness', 'target', 'release', 'hand'))
WORK = os.environ.get('HAND_WORK', os.path.join(ROOT, 'build'))


def run(name, program_text, witness, multi=None, timeout=3600):
    """`hand`'s result for the program on the witness: {'ok': True, 'cost', 'program_bytes',
    'witness_bytes', 'cells', 'seconds', ...} or {'ok': False, 'stage', 'error'}.  With `multi` (more
    witnesses) the program is parsed once and a list is returned.  Files go to build/ (HAND_WORK).  A crash
    of hand, or fewer results than witnesses, raises."""
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
    if out.returncode != 0 or len(results) != len(files):
        # a crash of hand is not a rejection: it must not pass for one, nor leave witnesses unchecked
        raise RuntimeError(
            f'hand failed on {name} (exit {out.returncode}, {len(results)} results for {len(files)} witnesses): '
            + (out.stdout + out.stderr)[-2000:]
        )
    for r in results:
        r['seconds'] = time.time() - t0
    return results if multi is not None else results[0]


def expect_ok(res, label=''):
    if not res.get('ok'):
        print(f'FAIL {label}: {res}', file=sys.stderr)
        raise SystemExit(1)
    return res


# the only failure an intended rejection may have: a jet failed (a `verify` of the program is false), when
# hand prunes the program (stage finalize, which runs it) or runs it (exec), not a type or decode error
JET_FAILED = 'Jet failed during execution'


def expect_rejected(res, label=''):
    if res.get('ok') or res.get('stage') not in ('exec', 'finalize') or JET_FAILED not in res.get('error', ''):
        print(f'FAIL {label}: expected a rejection by a failed jet, got {res}', file=sys.stderr)
        raise SystemExit(1)
    return res
