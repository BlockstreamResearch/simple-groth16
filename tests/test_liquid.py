#!/usr/bin/env python3
"""tools/liquid.py, with the chain and deploy replaced by fakes (no network, no node, no harness).

It refuses an outpoint that is malformed, spent, does not pay the verifier, is confidential or holds an
asset other than the policy asset; a fee rate below the minimum relay feerate, a negative fee, a fee that
takes the whole output, and any transaction whose fee is below its minimum relay fee; a --prove command
without {sighash}, a prover that fails or writes no witness, and a node on another chain or that refuses
the transaction.  It reads Esplora's and elements-cli's outputs, amounts in satoshis exactly, and passes
transactions to elements-cli on stdin (one is too long for an argument).  `prove` proves again only
while the measured size needs a higher fee, also when each proof is a few WU larger; the prover's output
stays off stdout, which carries only the transaction or the txid; nothing is sent without --broadcast.

    python3 tests/test_liquid.py
"""

import contextlib
import importlib.util
import io
import json
import math
import os
import sys
import tempfile
import types

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
spec = importlib.util.spec_from_file_location('liquid', os.path.join(ROOT, 'tools', 'liquid.py'))
L = importlib.util.module_from_spec(spec)
spec.loader.exec_module(L)
REAL_DEPLOY = L.deploy

TXID = 'ab' * 32
SPK = '5120' + '11' * 32
ASSET = L.LBTC['liquidtestnet']
DEST = 'tex1qexample'


def refused(f, *args, expect=''):
    try:
        with contextlib.redirect_stderr(io.StringIO()):
            f(*args)
    except SystemExit as e:
        assert expect in str(e), (expect, str(e))
        return
    raise AssertionError(f'not refused: {f.__name__}{args}')


def usage_error(argv):
    """argparse refuses the command line (exit status 2)."""
    try:
        with contextlib.redirect_stderr(io.StringIO()):
            L.main(argv)
    except SystemExit as e:
        assert e.code == 2, (argv, e.code)
        return
    raise AssertionError(f'accepted: {argv}')


class FakeChain:
    """An Esplora-like backend with one output and a record of what was sent."""

    def __init__(self, value=100_000, asset=ASSET, spk=SPK):
        self.out = {'script_pubkey': spk, 'value': value, 'asset': asset}
        self.sent = []

    def output(self, txid, vout):
        return self.out

    def policy_asset(self, network):
        return L.LBTC.get(network)

    def broadcast(self, hex_tx):
        self.sent.append(hex_tx)
        return 'cd' * 32

    def link(self, txid):
        return txid


class FakeDeploy:
    """deploy whose spends weigh the given weights in turn (the last one repeated); records the fees."""

    def __init__(self, *weights):
        self.weights, self.sighash_fees, self.spend_fees = list(weights), [], []

    def __call__(self, *args, log=False):
        cmd = args[0]
        if cmd == 'address':
            return json.dumps({'address': 'tex1pverifier', 'script_pubkey': SPK})
        # deploy sighash PROGRAM NETWORK TXID VOUT SATS ASSET DEST FEE; spend has WITNESS after PROGRAM
        if cmd == 'sighash':
            fee = int(args[8])
            self.sighash_fees.append(fee)
            return f'{fee:064x}'
        if cmd == 'spend':
            self.spend_fees.append(int(args[9]))
            w = self.weights.pop(0) if len(self.weights) > 1 else self.weights[0]
            return '00' * 10, f'program loaded\nnote: a note\ncost 1 mWU, tx weight {w} WU\n'
        if cmd == 'keyspend':
            assert log
            return 'ee' * 10, 'key path: internal key x, output key y, tx weight 721 WU\n'
        raise AssertionError(cmd)


def args(**kw):
    base = {
        'program': 'x.uprog',
        'network': 'liquidtestnet',
        'outpoint': f'{TXID}:0',
        'dest': DEST,
        'fee': None,
        'fee_rate': None,
        'vsize': None,
        'out': None,
        'broadcast': False,
        'genesis': None,
        'internal_key': None,
        'secret_file': None,
        'node': None,
        'esplora': None,
    }
    base.update(kw)
    return types.SimpleNamespace(**base)


def quiet(f, *a):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        f(*a)
    return out.getvalue(), err.getvalue()


def check_parsing():
    assert L.outpoint(f'{TXID.upper()}:7') == (TXID, 7)
    for bad in (TXID, f'{TXID}:', f'{TXID[:-1]}:0', f'{TXID}:-1', f'{TXID}:0:1'):
        refused(L.outpoint, bad, expect='TXID:VOUT')
    assert L.fee_for(13_328, '0.1') == math.ceil((13_328 + L.SLACK) / 10)
    assert L.fee_for(13_328, '1') == 13_338
    refused(L.fee_for, 1000, '0.05', expect='below the minimum relay feerate')
    assert L.vsize_of(53_311) == 13_328 and L.vsize_of(53_312) == 13_328
    print('parsing: outpoints, fees')


def check_backends():
    e = L.Esplora('https://example/api/')
    tx = {
        'vout': [
            {'scriptpubkey': SPK, 'value': 5, 'asset': ASSET},
            {'scriptpubkey': SPK, 'valuecommitment': '08' + '00' * 32},
        ]
    }
    e._get = lambda path: json.dumps({'spent': False} if '/outspend/' in path else tx)
    assert e.output(TXID, 0) == {'script_pubkey': SPK, 'value': 5, 'asset': ASSET}
    assert e.output(TXID, 1)['value'] is None
    refused(e.output, TXID, 2, expect='no output 2')
    e._get = lambda path: json.dumps({'spent': True, 'txid': 'ee'} if '/outspend/' in path else tx)
    refused(e.output, TXID, 0, expect='already spent, by ee')
    e._get = lambda path: json.dumps(
        [{'txid': TXID, 'vout': 1, 'value': 7, 'asset': ASSET, 'status': {'confirmed': False}}]
    )
    assert e.utxos('a') == [{'txid': TXID, 'vout': 1, 'value': 7, 'asset': ASSET, 'confirmed': False}]
    assert e.link('ff') == 'https://example/tx/ff' and e.policy_asset('liquid') == L.LBTC['liquid']

    calls = []

    def node(responses):
        n = L.Node('elements-cli -datadir=/x')

        def call(*a, stdin=None):
            calls.append((a, stdin))
            return responses[a[0]](a) if callable(responses[a[0]]) else responses[a[0]]

        n.call = call
        return n

    explicit = json.dumps({'scriptPubKey': {'hex': SPK}, 'asset': ASSET})[:-1] + ', "value": 0.00100001}'
    n = node({'gettxout': explicit})
    assert n.output(TXID, 0) == {'script_pubkey': SPK, 'value': 100_001, 'asset': ASSET}
    blinded = {'valuecommitment': '09' + '00' * 32, 'assetcommitment': '0a' + '00' * 32, 'scriptPubKey': {'hex': SPK}}
    n = node({'gettxout': json.dumps(blinded)})
    assert n.output(TXID, 0)['value'] is None and n.output(TXID, 0)['asset'] is None
    refused(node({'gettxout': ''}).output, TXID, 0, expect='not an unspent output')
    # scantxoutset sees confirmed outputs: one spent in the mempool (gettxout empty) is skipped
    scan = json.dumps({'unspents': [{'txid': TXID, 'vout': 0}, {'txid': 'cd' * 32, 'vout': 1}]})
    n = node({'scantxoutset': scan, 'gettxout': lambda a: explicit if a[1] == TXID else ''})
    assert [u['txid'] for u in n.utxos('a')] == [TXID]
    # the transaction goes through -stdin, never as an argument
    long_tx = 'ab' * 100_000
    calls.clear()
    n = node({'testmempoolaccept': json.dumps([{'allowed': True}]), 'sendrawtransaction': 'ff' * 32})
    assert n.broadcast(long_tx) == 'ff' * 32
    assert all(long_tx not in ' '.join(map(str, a)) for a, _ in calls) and calls[-1][1] == long_tx
    assert json.loads(calls[0][1]) == [long_tx]
    n = node(
        {'testmempoolaccept': json.dumps([{'allowed': False, 'reject-reason': 'mempool-script-verify-flag-failed'}])}
    )
    refused(n.broadcast, '00', expect='mempool-script-verify-flag-failed')
    print('backends: Esplora and elements-cli outputs read, amounts in satoshis exactly, transactions on stdin')


def check_backend_choice():
    refused(L.backend, args(network='elementsregtest'), expect='give --node')
    assert L.backend(args(network='liquid')).url == 'https://blockstream.info/liquid/api'
    refused(L.backend, args(node='elements-cli', esplora='https://x'), expect='not both')
    refused(L.backend, args(node='elements-cli', genesis='00' * 32), expect='--genesis is for an Esplora server')
    real = L.Node.genesis
    try:
        L.Node.genesis = lambda self: L.GENESIS['liquidtestnet']
        assert isinstance(L.backend(args(node='elements-cli')), L.Node)
        refused(L.backend, args(node='elements-cli', network='liquid'), expect='is not on liquid')
    finally:
        L.Node.genesis = real
    refused(L.chain_flags, args(network='elementsregtest', esplora='https://x'), FakeChain(), expect='--genesis')
    assert L.chain_flags(args(network='elementsregtest', genesis='aa'), FakeChain()) == ['--genesis', 'aa']
    assert L.chain_flags(args(), FakeChain()) == []
    print('backends chosen: one of --node and --esplora, the node on the chain of --network')


def check_funded():
    L.deploy = FakeDeploy(53_311)
    info = {'address': 'tex1pverifier', 'script_pubkey': SPK}
    assert L.funded(args(), FakeChain(), info) == (TXID, 0, 100_000, ASSET)
    refused(L.funded, args(), FakeChain(spk='0014' + '22' * 20), info, expect='does not pay the verifier')
    refused(L.funded, args(), FakeChain(value=None), info, expect='is confidential')
    refused(L.funded, args(), FakeChain(asset=None), info, expect='is confidential')
    refused(L.funded, args(), FakeChain(asset='ce' * 32), info, expect='not the policy asset')
    refused(L.spend_args, args(), FakeChain(), (TXID, 0, 1000, ASSET), 1000, expect='takes the whole output')
    print('the output: it must pay the verifier, be explicit, hold L-BTC and cover the fee')


def prover(tmp, extra=''):
    """A prover that records the sighash, prints to stdout, and writes the witness file."""
    log, witness = os.path.join(tmp, 'sighashes'), os.path.join(tmp, 'w.json')
    code = (
        'import sys; open(sys.argv[1], "a").write(sys.argv[3] + chr(10)); print("prover noise"); '
        f'open(sys.argv[2], "w").write(sys.argv[3]){extra}'
    )
    return f"{sys.executable} -c '{code}' {log} {witness} {{sighash}}", log, witness


def check_prove():
    with tempfile.TemporaryDirectory() as tmp:
        cmd, log, witness = prover(tmp)
        d = L.deploy = FakeDeploy(53_311)
        chain = FakeChain()
        out, err = quiet(L.cmd_prove, args(prove=cmd, witness=witness), chain)
        # a first guess, then the fee the measured size needs: two proofs, the second for the final fee
        need = L.fee_for(L.vsize_of(53_311), L.MIN_RATE)
        assert d.sighash_fees == [L.fee_for(1000, L.MIN_RATE), need], d.sighash_fees
        assert d.spend_fees == d.sighash_fees
        with open(log) as f:
            assert f.read().split() == [f'{x:064x}' for x in d.sighash_fees]
        # stdout carries only the transaction; the prover's output goes to stderr
        assert out.strip() == '00' * 10 and 'prover noise' in err, (out, err)
        assert not chain.sent and 'not sent' in err

        # each proof a few WU larger, at 1 sat/vB: the slack absorbs it, and the loop settles
        d = L.deploy = FakeDeploy(53_311, 53_315, 53_319, 53_323)
        quiet(L.cmd_prove, args(prove=cmd, witness=witness, fee_rate=L.feerate('1')), FakeChain())
        assert len(d.sighash_fees) == 2 and d.sighash_fees[-1] >= L.vsize_of(53_315), d.sighash_fees

        # the size known (--vsize): one proof; with --broadcast the txid is printed
        d = L.deploy = FakeDeploy(53_311)
        out, _ = quiet(L.cmd_prove, args(prove=cmd, witness=witness, vsize=13_328, broadcast=True), chain)
        assert d.sighash_fees == [need] and out.strip() == 'cd' * 32 and chain.sent == ['00' * 10]

        # a fixed --fee is kept if it can be relayed, refused if not
        d = L.deploy = FakeDeploy(53_311)
        quiet(L.cmd_prove, args(prove=cmd, witness=witness, fee=1500), FakeChain())
        assert d.sighash_fees == [1500]
        L.deploy = FakeDeploy(53_311)
        refused(
            L.cmd_prove, args(prove=cmd, witness=witness, fee=500), FakeChain(), expect='below the minimum relay fee'
        )

        # provers that cannot be used
        L.deploy = FakeDeploy(53_311)
        a = args(witness=witness, fee=1500)
        refused(
            L.cmd_prove,
            types.SimpleNamespace(**{**vars(a), 'prove': f'{sys.executable} -c pass'}),
            FakeChain(),
            expect='no {sighash}',
        )
        failing = f'{sys.executable} -c "raise SystemExit(3)" {{sighash}}'
        refused(
            L.cmd_prove, types.SimpleNamespace(**{**vars(a), 'prove': failing}), FakeChain(), expect='the prover failed'
        )
        silent = f'{sys.executable} -c "import sys" {{sighash}}'
        refused(L.cmd_prove, types.SimpleNamespace(**{**vars(a), 'prove': silent}), FakeChain(), expect='did not write')
        missing = f'{os.path.join(tmp, "no-such-prover")} {{sighash}}'
        refused(L.cmd_prove, types.SimpleNamespace(**{**vars(a), 'prove': missing}), FakeChain(), expect='the prover')
    print('prove: proves again only while the fee must rise; --vsize proves once; a low --fee is refused')


def check_spend():
    d = L.deploy = FakeDeploy(53_311)
    chain = FakeChain()
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'tx.hex')
        out, _ = quiet(L.cmd_spend, args(witness='w.json', vsize=13_328, out=path), chain)
        assert d.spend_fees == [L.fee_for(13_328, L.MIN_RATE)] and not out and not chain.sent
        with open(path) as f:
            assert f.read() == '00' * 10 + '\n'
        with open(path, 'w') as f:
            f.write('prover noise\n00\n')
        refused(L.cmd_broadcast, args(tx=path), chain, expect='does not hold one transaction')
    refused(L.cmd_spend, args(witness='w.json', fee=1000), FakeChain(), expect='below the minimum relay fee')
    refused(L.cmd_spend, args(witness='w.json'), FakeChain(), expect='give the fee')
    refused(L.cmd_spend, args(witness='w.json', fee=2000, vsize=10), FakeChain(), expect='not both')
    refused(L.cmd_spend, args(witness='w.json', fee=2000, fee_rate=L.feerate('2')), FakeChain(), expect='not both')
    refused(L.cmd_sighash, args(), FakeChain(), expect='the sighash covers the fee')
    out, _ = quiet(L.cmd_sighash, args(fee=1500), FakeChain())
    assert out.strip() == f'{1500:064x}'
    refused(L.cmd_keyspend, args(fee=100), FakeChain(), expect='--secret-file')
    refused(L.cmd_keyspend, args(secret_file='k', fee=1), FakeChain(), expect='below the minimum relay fee')
    out, _ = quiet(L.cmd_keyspend, args(secret_file='k', broadcast=True), chain)
    assert chain.sent[-1] == 'ee' * 10 and out.strip() == 'cd' * 32
    print('spend: every fee meets the minimum relay fee; nothing is sent without --broadcast')


def check_deploy():
    """deploy's notes reach stderr; its failure is reported with its message."""
    with tempfile.TemporaryDirectory() as tmp:
        fake = os.path.join(tmp, 'deploy')
        with open(fake, 'w') as f:
            f.write(
                f'#!{sys.executable}\nimport sys\nprint("note: dest is confidential", file=sys.stderr)\n'
                'print("out")\nsys.exit(1 if sys.argv[1] == "bad" else 0)\n'
            )
        os.chmod(fake, 0o755)
        L.DEPLOY = fake
        out, err = quiet(lambda: print(REAL_DEPLOY('sighash')))
        assert out.strip() == 'out' and 'note: dest is confidential' in err
        refused(REAL_DEPLOY, 'bad', expect='deploy bad: note: dest is confidential')
        L.DEPLOY = os.path.join(tmp, 'missing')
        refused(REAL_DEPLOY, 'sighash', expect='make harness')
    print('deploy: its notes are shown, its failures reported')


def check_cli():
    refused(
        L.main,
        ['address', 'x.uprog', '--network', 'liquid', '--internal-key', 'aa', '--secret-file', 'k'],
        expect='not both',
    )
    refused(L.main, ['faucet', 'ex1qmainnetaddress'], expect='Liquid testnet addresses')
    out = [f'{TXID}:0', DEST]
    usage_error(['spend', 'x.uprog', 'w.json', *out])  # --network is required
    for rate in ('abc', 'nan', 'inf', '0.01', '-1'):
        usage_error(['sighash', 'x.uprog', *out, '--network', 'liquid', '--vsize', '100', '--fee-rate', rate])
    usage_error(['sighash', 'x.uprog', *out, '--network', 'liquid', '--fee', '-5'])
    usage_error(['address', 'x.uprog', '--network', 'liquid', '--node', 'elements-cli'])  # address reads no chain
    print('the command line: one key flag, the faucet on testnet only, numbers checked, --network required')


def main():
    check_parsing()
    check_backends()
    check_backend_choice()
    check_funded()
    check_prove()
    check_spend()
    check_deploy()
    check_cli()
    print('all ok')


if __name__ == '__main__':
    main()
