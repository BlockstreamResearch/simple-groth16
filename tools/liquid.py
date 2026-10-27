#!/usr/bin/env python3
"""Spend a verifier's output on Liquid, Liquid testnet or an Elements regtest node.

    python3 tools/liquid.py address PROGRAM --network N
    python3 tools/liquid.py faucet ADDRESS                                     (Liquid testnet)
    python3 tools/liquid.py utxos PROGRAM --network N
    python3 tools/liquid.py sighash PROGRAM TXID:VOUT DEST --network N (--fee SAT | --vsize V)
    python3 tools/liquid.py spend PROGRAM WITNESS TXID:VOUT DEST --network N (--fee SAT | --vsize V) [--broadcast]
    python3 tools/liquid.py prove PROGRAM TXID:VOUT DEST --network N --prove CMD --witness FILE [--broadcast]
    python3 tools/liquid.py keyspend PROGRAM TXID:VOUT DEST --network N --secret-file F [--fee SAT] [--broadcast]
    python3 tools/liquid.py broadcast TX.hex --network N

PROGRAM is the verifier as `deploy compile` wrote it (x.uprog, with x.wnames beside it).  N is liquid,
liquidtestnet or elementsregtest.  The tool reads the chain through an Esplora server (--esplora, by
default Blockstream's for the two Liquid networks) or a node (--node "elements-cli -datadir=...", needed
on regtest), and builds every transaction with tools/harness's `deploy`.

The output.  `address` prints the verifier's address, and `utxos` the outputs that pay it.  Fund the
address with an explicit output: it is unconfidential, so a wallet that pays it writes the amount in the
clear, which the spend needs (the program's sighash covers the amount and the asset).  `faucet` asks
liquidtestnet.com's faucet for test coins, for example to the verifier's address itself.

The proof binds the spending transaction, fee included, so the fee is fixed before proving.  Either:
  - in two steps, for any prover: `sighash` prints the sighash of the transaction that pays the output to
    DEST minus the fee; prove for it; `spend` builds the transaction with the witness file;
  - in one: `prove` runs your prover itself (CMD, where {sighash} stands for the sighash; it writes the
    witness file), builds the transaction, and proves again if the fee must change.
The fee is --fee in satoshis, or --fee-rate (default 0.1 sat/vB, Liquid's minimum relay feerate) times a
virtual size: --vsize, or the size `prove` measures.  `spend` and `prove` report the transaction's vsize,
so the next spend of the same verifier can pass --vsize and prove once.

Every transaction is built and executed by `deploy`, which refuses one a node would not take (cost above
the budget, the cell cap, the standard weight), and is written to --out (default: printed).  Nothing is
sent without --broadcast; then the tool prints the txid.  With --node it is first tested with
testmempoolaccept.

The verifier's output may also have a key path: give its key with --internal-key (or --secret-file, the
secret, which `keyspend` signs with) to every command, as to `deploy`.
"""

import argparse
import json
import math
import os
import re
import shlex
import subprocess
import sys
import urllib.error
import urllib.request
from decimal import Decimal

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
DEPLOY = os.environ.get('DEPLOY', os.path.join(ROOT, 'tools', 'harness', 'target', 'release', 'deploy'))
NETWORKS = ('liquid', 'liquidtestnet', 'elementsregtest')
ESPLORA = {
    'liquid': 'https://blockstream.info/liquid/api',
    'liquidtestnet': 'https://blockstream.info/liquidtestnet/api',
}
# block 0 and the policy asset (L-BTC) of each Liquid network
GENESIS = {
    'liquid': '1466275836220db2944ca059a3a10ef6fd2ea684b0688d2c379296888a206003',
    'liquidtestnet': 'a771da8e52ee6ad581ed1e9a99825e5b3b7992225534eaa2ae23244fe26ab1c1',
}
LBTC = {
    'liquid': '6f0279e9ed041c3d710a9f57d0c02928416460c4b722ae3457a11eec381c526d',
    'liquidtestnet': '144c654344aa716d6f3abcc1ca90e5641e4e2a7f633bc09fe3baf64585819a49',
}
FAUCET = 'https://liquidtestnet.com/faucet'
MIN_RATE = Decimal('0.1')  # sat/vB: Elements' default minimum relay feerate, 100 sat/kvB
SLACK = 10  # vB added to a measured size: another proof's spend can weigh a few WU more
NOTED: set[str] = set()  # deploy's notes shown so far, each once


def fail(msg):
    sys.exit(f'liquid: {msg}')


def outpoint(s):
    """TXID:VOUT -> (txid, vout)."""
    m = re.fullmatch(r'([0-9a-fA-F]{64}):(\d+)', s)
    if not m:
        fail(f'{s!r} is not TXID:VOUT')
    return m.group(1).lower(), int(m.group(2))


def fee_for(vsize, rate):
    """The fee at rate sat/vB for vsize, with SLACK vB to spare."""
    if Decimal(rate) < MIN_RATE:
        fail(f'a fee rate of {rate} is below the minimum relay feerate {MIN_RATE} sat/vB')
    return math.ceil((vsize + SLACK) * Decimal(rate))


def vsize_of(weight):
    return (weight + 3) // 4


# the chain


class Esplora:
    """An Esplora server's REST API."""

    def __init__(self, url):
        self.url = url.rstrip('/')

    def _get(self, path):
        try:
            with urllib.request.urlopen(self.url + path, timeout=60) as r:
                return r.read().decode()
        except urllib.error.HTTPError as e:
            fail(f'{self.url}{path}: {e.code} {e.read().decode().strip()}')
        except urllib.error.URLError as e:
            fail(f'{self.url}{path}: {e.reason}')

    def output(self, txid, vout):
        """The output as {script_pubkey, value, asset} (value and asset None when confidential)."""
        tx = json.loads(self._get(f'/tx/{txid}'))
        if vout >= len(tx['vout']):
            fail(f'{txid} has {len(tx["vout"])} outputs, no output {vout}')
        spent = json.loads(self._get(f'/tx/{txid}/outspend/{vout}'))
        if spent.get('spent'):
            fail(f'{txid}:{vout} is already spent, by {spent.get("txid")}')
        o = tx['vout'][vout]
        return {'script_pubkey': o['scriptpubkey'], 'value': o.get('value'), 'asset': o.get('asset')}

    def utxos(self, address):
        out = []
        for u in json.loads(self._get(f'/address/{address}/utxo')):
            out.append(
                {
                    'txid': u['txid'],
                    'vout': u['vout'],
                    'value': u.get('value'),
                    'asset': u.get('asset'),
                    'confirmed': u['status']['confirmed'],
                }
            )
        return out

    def broadcast(self, hex_tx):
        req = urllib.request.Request(self.url + '/tx', data=hex_tx.strip().encode(), method='POST')
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read().decode().strip()
        except urllib.error.HTTPError as e:
            fail(f'the server refused the transaction: {e.read().decode().strip()}')
        except (urllib.error.URLError, OSError) as e:
            fail(f'{self.url}/tx: {e}; the transaction may have been sent: look at the output before sending again')

    def policy_asset(self, network):
        return LBTC.get(network)

    def link(self, txid):
        return f'{self.url.removesuffix("/api")}/tx/{txid}'


class Node:
    """An Elements node through elements-cli."""

    def __init__(self, cli):
        self.cli = shlex.split(cli)

    def call(self, *args, stdin=None):
        """A command; with stdin, its last argument goes through -stdin (a transaction is too long for one)."""
        cmd = self.cli + (['-stdin'] if stdin is not None else []) + [str(x) for x in args]
        try:
            r = subprocess.run(cmd, input=stdin, capture_output=True, text=True)
        except OSError as e:
            fail(f'{self.cli[0]}: {e}')
        if r.returncode:
            fail(f'{" ".join(self.cli)} {args[0]}: {r.stderr.strip() or r.stdout.strip()}')
        return r.stdout.strip()

    def _txout(self, txid, vout):
        out = self.call('gettxout', txid, vout, 'true')
        if not out:
            return None
        o = json.loads(out, parse_float=Decimal)
        value = o.get('value')
        return {
            'script_pubkey': o['scriptPubKey']['hex'],
            'value': None if value is None or 'valuecommitment' in o else int(value * 100_000_000),
            'asset': None if 'assetcommitment' in o else o.get('asset'),
        }

    def output(self, txid, vout):
        """The unspent output (gettxout: no -txindex needed), as Esplora.output."""
        o = self._txout(txid, vout)
        if o is None:
            fail(f'{txid}:{vout} is not an unspent output the node knows')
        return o

    def utxos(self, address):
        """The confirmed outputs (scantxoutset) that the mempool has not spent."""
        res = json.loads(self.call('scantxoutset', 'start', json.dumps([f'addr({address})'])), parse_float=Decimal)
        out = []
        for u in res.get('unspents', []):
            o = self._txout(u['txid'], u['vout'])
            if o is not None:
                out.append(
                    {'txid': u['txid'], 'vout': u['vout'], 'value': o['value'], 'asset': o['asset'], 'confirmed': True}
                )
        return out

    def test_accept(self, hex_tx):
        return json.loads(self.call('testmempoolaccept', stdin=json.dumps([hex_tx.strip()])))[0]

    def broadcast(self, hex_tx):
        r = self.test_accept(hex_tx)
        if not r['allowed']:
            fail(f'the node refuses the transaction: {r.get("reject-reason")}')
        return self.call('sendrawtransaction', stdin=hex_tx.strip())

    def genesis(self):
        return self.call('getblockhash', 0)

    def policy_asset(self, network):
        return json.loads(self.call('dumpassetlabels')).get('bitcoin')

    def link(self, txid):
        return txid


def backend(a):
    if a.node:
        if a.esplora:
            fail('--node or --esplora, not both')
        if a.genesis:
            fail('--genesis is for an Esplora server: the node gives its own')
        node = Node(a.node)
        if a.network in GENESIS and node.genesis() != GENESIS[a.network]:
            fail(f'the node is not on {a.network} (its block 0 is not {GENESIS[a.network]})')
        return node
    url = a.esplora or ESPLORA.get(a.network)
    if not url:
        fail(f'give --node (or --esplora) for {a.network}')
    return Esplora(url)


# deploy


def deploy(*args, log=False):
    """Run deploy and show its notes; its output, and with log=True its log too."""
    if not os.path.exists(DEPLOY):
        fail(f'{DEPLOY} not found: run `make harness` (or set DEPLOY)')
    r = subprocess.run([DEPLOY, *map(str, args)], capture_output=True, text=True)
    if r.returncode:
        fail(f'deploy {args[0]}: {r.stderr.strip()}')
    for line in r.stderr.splitlines():
        if line.startswith('note:') and line not in NOTED:
            NOTED.add(line)
            print(line, file=sys.stderr)
    return (r.stdout.strip(), r.stderr) if log else r.stdout.strip()


def weight_in(log, command):
    m = re.search(r'tx weight (\d+) WU', log)
    if not m:
        fail(f'deploy {command} did not report the weight:\n{log}')
    return int(m.group(1))


def key_flags(a):
    if a.internal_key:
        return ['--internal-key', a.internal_key]
    if a.secret_file:
        return ['--secret-file', a.secret_file]
    return []


def chain_flags(a, chain):
    """--genesis for regtest (deploy knows the Liquid networks')."""
    if a.network in GENESIS:
        return []
    g = a.genesis or (chain.genesis() if isinstance(chain, Node) else None)
    if not g:
        fail(f'give --genesis (elements-cli getblockhash 0) for {a.network}')
    return ['--genesis', g]


def verifier(a):
    """deploy address: {address, script_pubkey, ...}."""
    return json.loads(deploy('address', a.program, a.network, *key_flags(a)))


def funded(a, chain, info):
    """The output to spend: it must pay the verifier, be explicit and hold the policy asset (which pays the
    fee).  (txid, vout, sats, asset)"""
    txid, vout = outpoint(a.outpoint)
    o = chain.output(txid, vout)
    if o['script_pubkey'] != info['script_pubkey']:
        fail(f'{txid}:{vout} does not pay the verifier ({info["address"]})')
    if o['value'] is None or o['asset'] is None:
        fail(
            f'{txid}:{vout} is confidential: the spend needs its amount in the clear; fund the '
            'unconfidential address (or move the coins with deploy send)'
        )
    policy = chain.policy_asset(a.network)
    if policy and o['asset'] != policy:
        fail(f'{txid}:{vout} holds {o["asset"]}, not the policy asset {policy}, which the fee must be paid in')
    return txid, vout, o['value'], o['asset']


def spend_args(a, chain, out, fee):
    txid, vout, sats, asset = out
    if fee >= sats:
        fail(f'the fee ({fee} sat) takes the whole output ({sats} sat)')
    return [a.network, txid, vout, sats, asset, a.dest, fee, *chain_flags(a, chain), *key_flags(a)]


def sighash_for(a, chain, out, fee):
    return deploy('sighash', a.program, *spend_args(a, chain, out, fee))


def build(a, chain, out, fee, witness):
    """deploy spend: (hex, weight)."""
    hex_tx, log = deploy('spend', a.program, witness, *spend_args(a, chain, out, fee), log=True)
    weight = weight_in(log, 'spend')
    print(log.strip().splitlines()[-1], file=sys.stderr)
    return hex_tx, weight


def relayable(fee, weight):
    """Fail unless the fee meets the minimum relay fee of a transaction of this weight."""
    low = math.ceil(vsize_of(weight) * MIN_RATE)
    if fee < low:
        fail(
            f'a fee of {fee} sat is below the minimum relay fee of this {vsize_of(weight):,} vB transaction '
            f'({low} sat): prove again for --vsize {vsize_of(weight)}'
        )


def finish(a, chain, hex_tx, weight=None, fee=None):
    """Write or print the transaction, and broadcast it with --broadcast."""
    if weight is not None:
        print(
            f'vsize {vsize_of(weight):,} vB, fee {fee:,} sat (pass --vsize {vsize_of(weight)} next time)',
            file=sys.stderr,
        )
    if a.out:
        with open(a.out, 'w') as f:
            f.write(hex_tx + '\n')
        print(f'wrote {a.out}', file=sys.stderr)
    if a.broadcast:
        txid = chain.broadcast(hex_tx)
        print(f'sent: {chain.link(txid)}', file=sys.stderr)
        print(txid)
        return
    if isinstance(chain, Node):
        r = chain.test_accept(hex_tx)
        print(f'testmempoolaccept: {"allowed" if r["allowed"] else r.get("reject-reason")}', file=sys.stderr)
    if not a.out:
        print(hex_tx)
    print('not sent (--broadcast sends it)', file=sys.stderr)


def rate(a):
    return a.fee_rate if a.fee_rate is not None else MIN_RATE


def fee_arg(a):
    """The fee fixed by the arguments, or None."""
    if a.fee is not None:
        if a.vsize is not None or a.fee_rate is not None:
            fail('--fee, or --vsize with --fee-rate, not both')
        return a.fee
    if a.vsize is not None:
        return fee_for(a.vsize, rate(a))
    return None


def run_prover(command, sighash, witness):
    """Run the prover for the sighash; it must write the witness file anew.  Its output goes to stderr, so
    that stdout carries only the transaction (or the txid)."""
    cmd = [t.replace('{sighash}', sighash) for t in shlex.split(command)]
    if cmd == shlex.split(command):
        fail('--prove has no {sighash}')
    before = os.stat(witness).st_mtime_ns if os.path.exists(witness) else None
    try:
        sys.stderr.flush()
        target = sys.stderr.fileno()
    except (AttributeError, OSError, ValueError):
        target = None
    try:
        r = subprocess.run(cmd, stdout=target if target is not None else subprocess.PIPE, text=True)
    except OSError as e:
        fail(f'the prover {cmd[0]}: {e}')
    if target is None and r.stdout:
        print(r.stdout, end='', file=sys.stderr)
    if r.returncode:
        fail(f'the prover failed ({r.returncode}): {" ".join(cmd)}')
    if not os.path.exists(witness) or os.stat(witness).st_mtime_ns == before:
        fail(f'the prover did not write {witness}')


# commands


def cmd_address(a, chain):
    info = verifier(a)
    print(json.dumps(info, indent=2))
    print(f'Fund {info["address"]} with an explicit output (it is unconfidential).', file=sys.stderr)


def cmd_faucet(a, chain):
    if not re.fullmatch(r'tex1[0-9a-z]+|tlq1[0-9a-z]+', a.address):
        fail('the faucet pays Liquid testnet addresses (tex1... or tlq1...)')
    url = f'{FAUCET}?address={a.address}&action=lbtc'
    try:
        with urllib.request.urlopen(url, timeout=60) as r:
            page = r.read().decode()
    except (urllib.error.URLError, OSError) as e:
        fail(f'{FAUCET}: {e}')
    txids = re.findall(r'\b[0-9a-f]{64}\b', page)
    print(txids[0] if txids else 'requested (the page gave no txid: see `utxos` in a minute)')


def cmd_utxos(a, chain):
    info = verifier(a)
    for u in chain.utxos(info['address']):
        amount = (
            f'{u["value"]:,} sat of {u["asset"]}'
            if u['value'] is not None
            else 'confidential (cannot be spent by this tool)'
        )
        state = '' if u['confirmed'] else ', unconfirmed'
        print(f'{u["txid"]}:{u["vout"]}  {amount}{state}')


def cmd_sighash(a, chain):
    fee = fee_arg(a)
    if fee is None:
        fail('give --fee, or --vsize (with --fee-rate): the sighash covers the fee')
    out = funded(a, chain, verifier(a))
    print(f'output {a.outpoint}: {out[2]:,} sat; fee {fee:,} sat to {a.dest}', file=sys.stderr)
    print(sighash_for(a, chain, out, fee))


def cmd_spend(a, chain):
    fee = fee_arg(a)
    if fee is None:
        fail('give the fee the witness was proved for: --fee, or the --vsize (and --fee-rate) given to sighash')
    out = funded(a, chain, verifier(a))
    hex_tx, weight = build(a, chain, out, fee, a.witness)
    relayable(fee, weight)
    finish(a, chain, hex_tx, weight, fee)


def cmd_prove(a, chain):
    """Prove for a fee, build, and prove again while the measured size needs a higher fee: the next fee
    covers the measured size plus SLACK, so a proof a few WU larger still settles."""
    out = funded(a, chain, verifier(a))
    fixed = a.fee is not None
    fee = fee_arg(a)
    if fee is None:
        fee = fee_for(1000, rate(a))  # a first guess: the first build measures the size
    for _ in range(4):
        sighash = sighash_for(a, chain, out, fee)
        print(f'proving for sighash {sighash} (fee {fee:,} sat)', file=sys.stderr)
        run_prover(a.prove, sighash, a.witness)
        hex_tx, weight = build(a, chain, out, fee, a.witness)
        if fixed:
            relayable(fee, weight)
            return finish(a, chain, hex_tx, weight, fee)
        if fee >= math.ceil(vsize_of(weight) * Decimal(rate(a))):
            return finish(a, chain, hex_tx, weight, fee)
        fee = fee_for(vsize_of(weight), rate(a))
        print(f'{vsize_of(weight):,} vB needs more at {rate(a)} sat/vB: proving again for {fee:,} sat', file=sys.stderr)
    fail('the fee did not settle: give --fee')


def cmd_keyspend(a, chain):
    if not a.secret_file:
        fail('keyspend signs with --secret-file')
    fee = fee_arg(a)
    if fee is None:
        fee = fee_for(200, rate(a))  # about 181 vB
    out = funded(a, chain, verifier(a))
    hex_tx, log = deploy('keyspend', a.program, *spend_args(a, chain, out, fee), log=True)
    weight = weight_in(log, 'keyspend')
    relayable(fee, weight)
    finish(a, chain, hex_tx, weight, fee)


def cmd_broadcast(a, chain):
    with open(a.tx) as f:
        hex_tx = f.read().strip()
    if not re.fullmatch(r'[0-9a-fA-F]+', hex_tx):
        fail(f'{a.tx} does not hold one transaction in hex')
    a.out, a.broadcast = None, True
    finish(a, chain, hex_tx)


def satoshis(s):
    v = int(s)
    if v < 0:
        raise argparse.ArgumentTypeError('must not be negative')
    return v


def feerate(s):
    try:
        v = Decimal(s)
    except ArithmeticError:
        raise argparse.ArgumentTypeError(f'{s!r} is not a number') from None
    if not v.is_finite() or v < MIN_RATE:
        raise argparse.ArgumentTypeError(f'must be at least {MIN_RATE} sat/vB, the minimum relay feerate')
    return v


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='command', required=True)

    def command(name, *positional, chain=True, fee=False, out=False, keys=True):
        p = sub.add_parser(name)
        for arg in positional:
            p.add_argument(arg)
        if name != 'faucet':
            p.add_argument('--network', required=True, choices=NETWORKS)
        if chain:
            p.add_argument('--esplora', help="the Esplora API (default: Blockstream's, on the Liquid networks)")
            p.add_argument('--node', help='an Elements node instead: its elements-cli command line')
            p.add_argument('--genesis', help="the chain's `getblockhash 0` (regtest with --esplora)")
        if keys:
            p.add_argument('--internal-key', help="the output's taproot internal key (x-only hex)")
            p.add_argument('--secret-file', help="a file with the internal key's secret (hex)")
        if fee:
            p.add_argument('--fee', type=satoshis, help='the fee in satoshis')
            p.add_argument('--fee-rate', type=feerate, help='sat/vB, with --vsize or the measured size (default 0.1)')
            p.add_argument('--vsize', type=satoshis, help="the spend's virtual size, as an earlier spend reported it")
        if out:
            p.add_argument('--out', help='write the transaction to this file')
            p.add_argument('--broadcast', action='store_true', help='send it')
        return p

    command('address', 'program', chain=False)
    command('faucet', 'address', chain=False, keys=False)
    command('utxos', 'program')
    command('sighash', 'program', 'outpoint', 'dest', fee=True)
    command('spend', 'program', 'witness', 'outpoint', 'dest', fee=True, out=True)
    p = command('prove', 'program', 'outpoint', 'dest', fee=True, out=True)
    p.add_argument(
        '--prove',
        required=True,
        help="the prover's command line, with {sighash}; split like a shell's, but run without one (no &&, > or $VAR)",
    )
    p.add_argument('--witness', required=True, help='the witness file the prover writes')
    command('keyspend', 'program', 'outpoint', 'dest', fee=True, out=True)
    command('broadcast', 'tx', keys=False)
    a = ap.parse_args(argv)
    if getattr(a, 'internal_key', None) and getattr(a, 'secret_file', None):
        fail('--internal-key or --secret-file, not both')
    chain = backend(a) if hasattr(a, 'node') else None
    globals()[f'cmd_{a.command}'](a, chain)


if __name__ == '__main__':
    main()
